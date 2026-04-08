#!/usr/bin/env python3
"""
VORTHEX Reference Interpreter v1.0.0
=====================================
Concatenative + Stack-Based + Lambda Calculus Hybrid Language

Architecture:
  ┌──────────┐   ┌──────────┐   ┌─────────────────┐   ┌──────────────┐
  │  Lexer   │──▶│  Parser  │──▶│   Evaluator      │──▶│   Runtime    │
  └──────────┘   └──────────┘   └─────────────────┘   └──────────────┘
    tokens         AST nodes     two-pass + RTQ       Ω/Ψ stacks + ℒ

Usage:
  python3 vorthex.py <file.vx>
  python3 vorthex.py --compute-checksums <file.vx>
  python3 vorthex.py --debug <file.vx>
  python3 vorthex.py --dump-tokens <file.vx>
"""
from __future__ import annotations

import sys
import re
import os
import ast
import zlib
import math
import argparse
import traceback
from enum import Enum, auto
from dataclasses import dataclass, field
from typing import Any, Optional, Callable
from collections import defaultdict

__version__ = "1.0.0"

# ═══════════════════════════════════════════════════════════════════════════════
# CONSTANTS
# ═══════════════════════════════════════════════════════════════════════════════

MAX_STACK_SIZE     = 1024
FNV_OFFSET_BASIS   = 0x811c9dc5
FNV_PRIME          = 0x01000193
INITIAL_ENTROPY    = 0x811c9dc5
EPSILON            = 1e-9          # for ≈ operator

# ═══════════════════════════════════════════════════════════════════════════════
# OPERATOR TABLE  (40+ operators)
# Each entry: symbol → (category, ω_action, ψ_action, description)
# ω_action = primary meaning (most recently applied to Ω stack)
# ψ_action = secondary meaning (most recently applied to Ψ stack)
# Actual dispatch is further gated by entropy register value and column position
# ═══════════════════════════════════════════════════════════════════════════════

OPERATOR_TABLE: dict[str, tuple[str, str, str, str]] = {
    # ── Arithmetic ──────────────────────────────────────────────────────────
    '⊕': ('arith',   'add',           'type_union',
          'Ω: pop Ω and Ψ, push Ω+Ψ to Ω  | Ψ: push type-union of Ω/Ψ types'),
    '⊖': ('arith',   'sub',           'type_diff',
          'Ω: push Ω−Ψ to Ω              | Ψ: type difference'),
    '⊗': ('arith',   'mul',           'type_product',
          'Ω: push Ω×Ψ to Ω              | Ψ: Cartesian type product'),
    '⊙': ('arith',   'div',           'type_quotient',
          'Ω: push Ω÷Ψ to Ω              | Ψ: quotient type'),
    '⌁': ('arith',   'mod',           'type_residue',
          'Ω: push Ω mod Ψ to Ω          | Ψ: residue type'),
    # ── Bitwise ─────────────────────────────────────────────────────────────
    '⊻': ('bitwise', 'xor',           'entropy_fork',
          'Ω: bitwise XOR of Ω and Ψ    | Ψ: fork entropy register'),
    '⊼': ('bitwise', 'nand',          'type_complement',
          'Ω: bitwise NAND               | Ψ: type complement'),
    '⊽': ('bitwise', 'nor',           'type_inter_comp',
          'Ω: bitwise NOR                | Ψ: complement of type intersection'),
    '∿': ('bitwise', 'rotl',          'type_cast',
          'Ω: bit-rotate-left by Ψ top  | Ψ: cast Ω top to type on Ψ'),
    '∩': ('bitwise', 'bitand',        'type_intersection',
          'Ω: bitwise AND of top two Ω  | Ψ: type intersection'),
    '∪': ('bitwise', 'bitor',         'type_union2',
          'Ω: bitwise OR of top two Ω   | Ψ: type union (alt)'),
    # ── Stack manipulation ───────────────────────────────────────────────────
    '⥊': ('stack',   'swap_heads',    'swap_heads',
          'Swap tops of Ω and Ψ simultaneously (context-invariant)'),
    '⋄': ('stack',   'dup_omega',     'dup_psi',
          'Ω: duplicate Ω top           | Ψ: duplicate Ψ top'),
    '◇': ('stack',   'drop_omega',    'drop_psi',
          'Ω: discard Ω top             | Ψ: discard Ψ top'),
    '◈': ('stack',   'swap_omega',    'swap_psi',
          'Ω: swap top two of Ω         | Ψ: swap top two of Ψ'),
    '⧓': ('stack',   'over_omega',    'over_psi',
          'Ω: copy Ω[1] to Ω top        | Ψ: copy Ψ[1] to Ψ top'),
    '⟲': ('stack',   'rot_omega',     'rot_psi',
          'Ω: a b c → b c a on Ω        | Ψ: same on Ψ'),
    '⟳': ('stack',   'unrot_omega',   'unrot_psi',
          'Ω: a b c → c a b on Ω        | Ψ: same on Ψ'),
    '↑': ('stack',   'xfer_psi_to_omega', 'xfer_omega_to_psi',
          'Ω: copy Ψ top onto Ω         | Ψ: copy Ω top onto Ψ'),
    '↓': ('stack',   'drop_omega',    'drop_psi',
          'Ω: pop and discard Ω top     | Ψ: pop and discard Ψ top'),
    '⇑': ('stack',   'push_both',     'push_both',
          'Copy Ω top onto Ψ AND Ψ top onto Ω simultaneously'),
    '⇓': ('stack',   'pop_both',      'pop_both',
          'Discard tops of both Ω and Ψ'),
    '⊂': ('stack',   'copy_o_to_p',   'copy_p_to_o',
          'Ω: copy Ω top → Ψ (non-destructive) | Ψ: copy Ψ top → Ω'),
    '⊃': ('stack',   'move_o_to_p',   'move_p_to_o',
          'Ω: move Ω top → Ψ (destructive)     | Ψ: move Ψ top → Ω'),
    # ── Cross-stack ──────────────────────────────────────────────────────────
    '⊛': ('dual',    'cross_product', 'void_cascade',
          'Dual: push (Ω top × Ψ top) tuple to Ω | Single: trigger void cascade'),
    '⋈': ('dual',    'interleave',    'split',
          'Ω: interleave Ω and Ψ into Ω         | Ψ: split Ω alternately to Ω/Ψ'),
    '⋉': ('dual',    'left_merge',    'left_split',
          'Ω: left-biased merge of stacks        | Ψ: left split of Ω'),
    '⋊': ('dual',    'right_merge',   'right_split',
          'Ω: right-biased merge of stacks       | Ψ: right split of Ω'),
    # ── Logic ────────────────────────────────────────────────────────────────
    '∧': ('logic',   'and_op',        'type_and',
          'Ω: push (Ω∧Ψ) to Ω           | Ψ: type intersection'),
    '∨': ('logic',   'or_op',         'type_or',
          'Ω: push (Ω∨Ψ) to Ω           | Ψ: type union'),
    '¬': ('logic',   'not_omega',     'not_psi',
          'Ω: logical NOT of Ω top       | Ψ: logical NOT of Ψ top'),
    # ── Comparison ───────────────────────────────────────────────────────────
    '≡': ('cmp',     'eq',            'type_equiv',
          'Ω: push (Ω==Ψ) bool to Ω    | Ψ: type equivalence check'),
    '≠': ('cmp',     'neq',           'type_neq',
          'Ω: push (Ω!=Ψ) bool to Ω    | Ψ: type non-equivalence'),
    '≺': ('cmp',     'lt',            'subtype',
          'Ω: push (Ω<Ψ) bool to Ω     | Ψ: subtype check'),
    '≻': ('cmp',     'gt',            'supertype',
          'Ω: push (Ω>Ψ) bool to Ω     | Ψ: supertype check'),
    '≈': ('cmp',     'approx_eq',     'type_compat',
          'Ω: push (|Ω-Ψ|<ε) to Ω      | Ψ: type compatibility'),
    # ── Control flow ─────────────────────────────────────────────────────────
    '⟁': ('ctrl',    'branch_gt',     'rtq_defer',
          'Ω top > Ψ top: branch | else: push current expr to RTQ'),
    '⊜': ('ctrl',    'self_dispatch', 'tail_recurse',
          'Ω: dispatch fn whose FNV hash is on Ω | Ψ: tail-recurse current fn'),
    # ── I/O ──────────────────────────────────────────────────────────────────
    '⊞': ('io',      'write_stdout',  'write_stderr',
          'Ω: pop Ω top, print to stdout | Ψ: print to stderr'),
    '⊟': ('io',      'read_stdin_o',  'read_stdin_p',
          'Ω: read line → push to Ω     | Ψ: read line → push to Ψ'),
    # ── Lattice ──────────────────────────────────────────────────────────────
    '⊘': ('lattice', 'lat_write_ent', 'lat_read_ent',
          'Ω: write Ω to ℒ[Ω.x][Ψ.y][ε&0xFF] | Ψ: read that cell → Ω'),
    # ── Numeric ──────────────────────────────────────────────────────────────
    '⌊': ('num',     'floor_omega',   'floor_psi',
          'Ω: floor(Ω top)            | Ψ: floor(Ψ top)'),
    '⌈': ('num',     'ceil_omega',    'ceil_psi',
          'Ω: ceil(Ω top)             | Ψ: ceil(Ψ top)'),
    '∇': ('num',     'dec_omega',     'dec_psi',
          'Ω: Ω top − 1               | Ψ: Ψ top − 1'),
    'Δ': ('num',     'inc_omega',     'inc_psi',
          'Ω: Ω top + 1               | Ψ: Ψ top + 1'),
    # ── Literals ─────────────────────────────────────────────────────────────
    '∅': ('lit',     'push_zero_o',   'push_zero_p',
          'Ω: push 0 to Ω             | Ψ: push 0 to Ψ'),
    '∞': ('lit',     'push_inf_o',    'push_inf_p',
          'Ω: push float(inf) to Ω    | Ψ: push float(inf) to Ψ'),
    # ── Higher-order ─────────────────────────────────────────────────────────
    '∫': ('higher',  'fold_omega',    'fold_psi',
          'Ω: fold entire Ω stack with Ψ top as fn | Ψ: fold Ψ stack'),
    '∑': ('higher',  'sum_omega',     'sum_psi',
          'Ω: sum all of Ω, push result  | Ψ: sum all of Ψ'),
    '∏': ('higher',  'prod_omega',    'prod_psi',
          'Ω: product of all Ω           | Ψ: product of all Ψ'),
    '∀': ('higher',  'map_omega',     'map_psi',
          'Ω: map Ω top (fn) over remaining Ω items | Ψ: map over Ψ'),
    '∃': ('higher',  'any_omega',     'any_psi',
          'Ω: check any Ω item satisfies Ψ top predicate | Ψ: check Ψ'),
    # ── Sequence ─────────────────────────────────────────────────────────────
    '⋯': ('seq',     'range_o',       'range_p',
          'Ω: push integers [Ψ top..Ω top] onto Ω  | Ψ: push onto Ψ'),
}

# All operator symbols as a set (for fast lookup)
ALL_OPERATORS: set[str] = set(OPERATOR_TABLE.keys())

# Type primitive names
TYPE_NAMES = {'ℕ', 'ℤ', '𝔽', '𝔹', '⊤', '⊥'}

# ═══════════════════════════════════════════════════════════════════════════════
# EXCEPTIONS
# ═══════════════════════════════════════════════════════════════════════════════

class VorthexError(Exception):
    """Base class for all VORTHEX errors."""
    pass

class LexerError(VorthexError):
    def __init__(self, msg: str, line: int, col: int, filename: str = '<unknown>'):
        self.msg, self.line, self.col, self.filename = msg, line, col, filename
        super().__init__(f"{filename}:{line}:{col}: Lexer Error: {msg}")

class ParseError(VorthexError):
    def __init__(self, msg: str, line: int, col: int, filename: str = '<unknown>'):
        self.msg, self.line, self.col, self.filename = msg, line, col, filename
        super().__init__(f"{filename}:{line}:{col}: Parse Error: {msg}")

class ChecksumError(ParseError):
    pass

class RuntimeError_(VorthexError):
    """Runtime error with full machine state."""
    def __init__(self, msg: str, runtime: 'VorthexRuntime', line: int = 0, col: int = 0):
        self.vx_msg  = msg
        self.runtime = runtime
        self.line    = line
        self.col     = col
        state = (
            f"\n  Runtime state at error:"
            f"\n    Pass: {runtime.pass_number}"
            f"\n    Entropy register (ε): 0x{runtime.entropy:08X}"
            f"\n    Ω stack (top→bottom): {list(reversed(runtime.omega[-8:]))}"
            f"\n    Ψ stack (top→bottom): {list(reversed(runtime.psi[-8:]))}"
            f"\n    Degraded mode: {runtime.degraded}"
        )
        super().__init__(f"Runtime Error (line {line}, col {col}): {msg}{state}")

class VoidCascadeError(RuntimeError_):
    """Raised when reading an uninitialized lattice cell."""
    def __init__(self, coord: tuple[int,int,int], runtime: 'VorthexRuntime',
                 line: int = 0, col: int = 0):
        self.coord = coord
        super().__init__(
            f"Void cascade: read uninitialized lattice cell ℒ{coord}",
            runtime, line, col)

class EntropicCollapseWarning(VorthexError):
    """Non-fatal: both stacks XOR-merged, execution continues in degraded mode."""
    pass

class StackUnderflowError(RuntimeError_):
    pass

class DispatchError(RuntimeError_):
    pass

# ═══════════════════════════════════════════════════════════════════════════════
# TOKENS
# ═══════════════════════════════════════════════════════════════════════════════

class TT(Enum):
    INT         = auto()   # integer literal
    FLOAT       = auto()   # float literal
    STRING      = auto()   # «...» string
    BOOL        = auto()   # ⊤ / ⊥  (when used as literals, not type names)
    IDENT       = auto()   # function/identifier name
    OP          = auto()   # any operator from OPERATOR_TABLE
    TYPE        = auto()   # ℕ ℤ 𝔽 𝔹 ⊤ ⊥  (in type context)
    LAT_READ    = auto()   # ⟨ x , y , z ⟩  (entire expression)
    LAT_WRITE   = auto()   # ⟩ x , y , z ⟨  (entire expression)
    COMMENT     = auto()   # ⟦...⟧
    CHECKSUM    = auto()   # ⌸0xHEXHEX
    FUNC_DEF    = auto()   # ⦿
    FUNC_END    = auto()   # ⦾
    TYPESIG_BEGIN = auto() # [
    TYPESIG_END   = auto() # ]
    ARROW       = auto()   # →  (inside type sig)
    PIPE        = auto()   # |  (inside type sig)
    COMMA       = auto()   # ,  (inside lattice addresses)
    EOF         = auto()

@dataclass
class Token:
    type:         TT
    value:        Any
    line:         int
    col:          int
    indent:       int   # leading spaces on this line (0 = global scope)
    blank_before: int   # consecutive blank lines immediately before this line
    raw:          str   # exact source text (for checksum computation)

# ═══════════════════════════════════════════════════════════════════════════════
# FNV-1a AND CRC-32 HELPERS
# ═══════════════════════════════════════════════════════════════════════════════

def fnv1a_32(data: bytes) -> int:
    h = FNV_OFFSET_BASIS
    for byte in data:
        h ^= byte
        h = (h * FNV_PRIME) & 0xFFFFFFFF
    return h

def crc32(data: bytes) -> int:
    return zlib.crc32(data) & 0xFFFFFFFF

def compute_block_checksum(tokens: list[Token]) -> int:
    """CRC-32 of the UTF-8-encoded token stream (raw texts joined by spaces)."""
    stream = ' '.join(t.raw for t in tokens
                      if t.type not in (TT.CHECKSUM, TT.EOF))
    return crc32(stream.encode('utf-8'))

# ═══════════════════════════════════════════════════════════════════════════════
# LEXER
# ═══════════════════════════════════════════════════════════════════════════════

class Lexer:
    """
    Converts VORTHEX source text into a flat list of Tokens.

    Whitespace semantics are encoded into each token:
      token.indent       — leading-space count of the line (multiples of 2)
      token.blank_before — blank lines before this line
      token.col          — 1-based column of the token's first character
    """

    def __init__(self, source: str, filename: str = '<unknown>'):
        self.source   = source
        self.filename = filename
        self.pos      = 0
        self.line     = 1
        self.col      = 1
        self.tokens: list[Token] = []

    # ── helpers ───────────────────────────────────────────────────────────────

    def error(self, msg: str) -> LexerError:
        return LexerError(msg, self.line, self.col, self.filename)

    def peek(self, offset: int = 0) -> str:
        p = self.pos + offset
        return self.source[p] if p < len(self.source) else ''

    def peek_str(self, n: int) -> str:
        return self.source[self.pos:self.pos + n]

    def advance(self) -> str:
        ch = self.source[self.pos]
        self.pos += 1
        if ch == '\n':
            self.line += 1
            self.col = 1
        else:
            self.col += 1
        return ch

    def match(self, s: str) -> bool:
        if self.source[self.pos:self.pos + len(s)] == s:
            for _ in s:
                self.advance()
            return True
        return False

    def skip_spaces_and_tabs_on_line(self) -> int:
        """Skip horizontal whitespace; return count. Tabs raise an error."""
        count = 0
        while self.pos < len(self.source) and self.peek() in (' ', '\t'):
            if self.peek() == '\t':
                raise self.error(
                    "Tab character detected. VORTHEX uses spaces only. "
                    "Tabs are a fatal parse error."
                )
            self.advance()
            count += 1
        return count

    # ── line pre-analysis ─────────────────────────────────────────────────────

    def _scan_line_metadata(self) -> list[dict]:
        """
        Pre-scan all lines to collect indent and blank_before for each line.
        Returns a list indexed by line number (1-based, index 0 unused).
        """
        meta = [{'indent': 0, 'blank_before': 0}]  # index 0 placeholder
        lines = self.source.split('\n')
        blank_run = 0
        for raw_line in lines:
            is_blank = raw_line.strip() == ''
            if is_blank:
                blank_run += 1
                meta.append({'indent': 0, 'blank_before': blank_run, 'is_blank': True})
            else:
                indent = len(raw_line) - len(raw_line.lstrip(' '))
                if '\t' in raw_line[:indent]:
                    # will raise during actual tokenization
                    indent = 0
                meta.append({'indent': indent, 'blank_before': blank_run, 'is_blank': False})
                blank_run = 0
        return meta

    # ── main tokenize ─────────────────────────────────────────────────────────

    def tokenize(self) -> list[Token]:
        line_meta = self._scan_line_metadata()

        while self.pos < len(self.source):
            cur_line = self.line
            ch = self.peek()

            # Skip tabs (fatal) and spaces (indentation already captured)
            if ch == ' ':
                self.advance()
                continue
            if ch == '\t':
                raise self.error(
                    "Tab character detected. Tabs are a fatal parse error in VORTHEX.")
            if ch == '\n':
                self.advance()
                continue

            meta = line_meta[cur_line] if cur_line < len(line_meta) else {'indent': 0, 'blank_before': 0}
            indent       = meta.get('indent', 0)
            blank_before = meta.get('blank_before', 0)
            tok_col      = self.col

            tok = self._lex_one(indent, blank_before, tok_col, line_meta)
            if tok is not None:
                self.tokens.append(tok)

        meta = line_meta[self.line] if self.line < len(line_meta) else {'indent': 0, 'blank_before': 0}
        self.tokens.append(Token(TT.EOF, None, self.line, self.col,
                                 meta.get('indent', 0), meta.get('blank_before', 0), ''))
        return self.tokens

    def _lex_one(self, indent: int, blank_before: int, tok_col: int,
                 line_meta: list[dict]) -> Optional[Token]:
        """Lex a single token at the current position."""
        ch = self.peek()

        def tok(tt: TT, val: Any, raw: str) -> Token:
            return Token(tt, val, self.line, tok_col, indent, blank_before, raw)

        # ── Comment  ⟦...⟧ ──────────────────────────────────────────────────
        if ch == '⟦':
            return self._lex_comment(indent, blank_before, tok_col)

        # ── Function markers ─────────────────────────────────────────────────
        if ch == '⦿':
            self.advance()
            return tok(TT.FUNC_DEF, '⦿', '⦿')
        if ch == '⦾':
            self.advance()
            return tok(TT.FUNC_END, '⦾', '⦾')

        # ── Checksum  ⌸0xHEX ────────────────────────────────────────────────
        if ch == '⌸':
            return self._lex_checksum(indent, blank_before, tok_col)

        # ── Lattice read ⟨x,y,z⟩ ────────────────────────────────────────────
        if ch == '⟨':
            return self._lex_lattice(indent, blank_before, tok_col, is_read=True)

        # ── Lattice write ⟩x,y,z⟨ ───────────────────────────────────────────
        if ch == '⟩':
            return self._lex_lattice(indent, blank_before, tok_col, is_read=False)

        # ── Type sig brackets [ and ] ────────────────────────────────────────
        if ch == '[':
            self.advance()
            return tok(TT.TYPESIG_BEGIN, '[', '[')
        if ch == ']':
            self.advance()
            return tok(TT.TYPESIG_END, ']', ']')

        # ── Arrow → (inside type sig) ────────────────────────────────────────
        if ch == '→':
            self.advance()
            return tok(TT.ARROW, '→', '→')

        # ── Pipe | (inside type sig) ─────────────────────────────────────────
        if ch == '|':
            self.advance()
            return tok(TT.PIPE, '|', '|')

        # ── Comma ────────────────────────────────────────────────────────────
        if ch == ',':
            self.advance()
            return tok(TT.COMMA, ',', ',')

        # ── String literal «...» ─────────────────────────────────────────────
        if ch == '«':
            return self._lex_string(indent, blank_before, tok_col)

        # ── Numeric literal ──────────────────────────────────────────────────
        if ch.isdigit() or (ch == '-' and self.peek(1).isdigit()):
            return self._lex_number(indent, blank_before, tok_col)

        if ch == '0' and self.peek(1) in ('x', 'X'):
            return self._lex_number(indent, blank_before, tok_col)

        # ── Operator (check longest match first) ─────────────────────────────
        for op in sorted(ALL_OPERATORS, key=len, reverse=True):
            if self.source[self.pos:self.pos + len(op)] == op:
                for _ in op:
                    self.advance()
                return tok(TT.OP, op, op)

        # ── Type names (ℕ ℤ 𝔽 𝔹 ⊤ ⊥) ─────────────────────────────────────
        for tname in TYPE_NAMES:
            if self.source[self.pos:self.pos + len(tname)] == tname:
                for _ in tname:
                    self.advance()
                return tok(TT.TYPE, tname, tname)

        # ── Identifier (Unicode letters, digits, underscores, subscripts) ────
        if self._is_ident_start(ch):
            return self._lex_ident(indent, blank_before, tok_col)

        # Unknown character — skip with warning
        unknown = ch
        self.advance()
        if unknown.strip():
            print(f"  Warning: Unknown character U+{ord(unknown):04X} '{unknown}' "
                  f"at {self.filename}:{self.line}:{tok_col} — skipped",
                  file=sys.stderr)
        return None

    # ── sub-lexers ────────────────────────────────────────────────────────────

    def _lex_comment(self, indent: int, blank_before: int, tok_col: int) -> Token:
        # Comments support nesting: ⟦ ⟦ inner ⟧ outer still open ⟧
        start = self.pos
        self.advance()  # consume opening ⟦
        content_chars = []
        depth = 1
        while self.pos < len(self.source):
            if self.peek() == '⟦':
                depth += 1
                content_chars.append(self.advance())
            elif self.peek() == '⟧':
                depth -= 1
                if depth == 0:
                    self.advance()  # consume closing ⟧
                    break
                content_chars.append(self.advance())
            else:
                content_chars.append(self.advance())
        else:
            raise self.error("Unterminated comment ⟦ (expected ⟧)")
        content = ''.join(content_chars)
        raw = self.source[start:self.pos]
        return Token(TT.COMMENT, content, self.line, tok_col, indent, blank_before, raw)

    def _lex_checksum(self, indent: int, blank_before: int, tok_col: int) -> Token:
        self.advance()  # consume ⌸
        raw_start_pos = self.pos - len('⌸')
        if not self.peek_str(2).lower().startswith('0x'):
            raise self.error("Checksum must be in form ⌸0xHEXDIGITS")
        hex_chars = ['0', 'x'] if self.peek() == '0' else ['0', 'X']
        self.advance(); self.advance()  # consume 0x
        digits = []
        while self.peek() and self.peek() in '0123456789abcdefABCDEF':
            digits.append(self.advance())
        if not digits:
            raise self.error("Empty checksum hex value after ⌸0x")
        raw = '⌸0x' + ''.join(digits)
        value = int(''.join(digits), 16)
        return Token(TT.CHECKSUM, value, self.line, tok_col, indent, blank_before, raw)

    def _lex_lattice(self, indent: int, blank_before: int, tok_col: int,
                     is_read: bool) -> Token:
        """
        Parse ⟨expr,expr,expr⟩  (read)  or  ⟩expr,expr,expr⟨  (write).
        Coordinates are integer literals or arithmetic expressions.
        Returns Token whose value is a tuple of coordinate expressions.
        """
        open_ch  = '⟨' if is_read else '⟩'
        close_ch = '⟩' if is_read else '⟨'
        raw_start = self.pos
        self.advance()  # consume opening bracket

        coords_raw = []
        current = []
        depth = 1
        while self.pos < len(self.source):
            ch = self.peek()
            if ch == open_ch:
                depth += 1
                current.append(self.advance())
            elif ch == close_ch:
                depth -= 1
                if depth == 0:
                    self.advance()
                    coords_raw.append(''.join(current).strip())
                    break
                current.append(self.advance())
            elif ch == ',':
                coords_raw.append(''.join(current).strip())
                current = []
                self.advance()
            else:
                current.append(self.advance())
        else:
            kind = 'lattice read' if is_read else 'lattice write'
            raise self.error(f"Unterminated {kind} (expected {close_ch})")

        # Pad to 3 coordinates (default 0)
        while len(coords_raw) < 3:
            coords_raw.append('0')

        raw = self.source[raw_start:self.pos]
        tt = TT.LAT_READ if is_read else TT.LAT_WRITE
        return Token(tt, tuple(coords_raw[:3]), self.line, tok_col, indent, blank_before, raw)

    def _lex_string(self, indent: int, blank_before: int, tok_col: int) -> Token:
        self.advance()  # consume «
        chars = []
        while self.pos < len(self.source):
            ch = self.peek()
            if ch == '»':
                self.advance()
                break
            if ch == '\\':
                self.advance()
                esc = self.advance()
                chars.append({'n': '\n', 't': '\t', 'r': '\r',
                               '\\': '\\', '«': '«', '»': '»'}.get(esc, esc))
            else:
                chars.append(self.advance())
        else:
            raise self.error("Unterminated string literal (expected »)")
        s = ''.join(chars)
        raw = '«' + s + '»'
        return Token(TT.STRING, s, self.line, tok_col, indent, blank_before, raw)

    def _lex_number(self, indent: int, blank_before: int, tok_col: int) -> Token:
        start = self.pos
        sign = ''
        if self.peek() == '-':
            sign = self.advance()

        is_hex = self.peek() == '0' and self.peek(1) in ('x', 'X')
        chars = [sign] if sign else []

        if is_hex:
            chars.append(self.advance())  # 0
            chars.append(self.advance())  # x/X
            while self.peek() in '0123456789abcdefABCDEF_':
                c = self.advance()
                if c != '_':
                    chars.append(c)
            raw = ''.join(chars)
            return Token(TT.INT, int(raw, 16), self.line, tok_col, indent, blank_before, raw)

        while self.peek().isdigit():
            chars.append(self.advance())

        if self.peek() == '.' and self.peek(1).isdigit():
            chars.append(self.advance())  # dot
            while self.peek().isdigit():
                chars.append(self.advance())
            # optional exponent
            if self.peek() in ('e', 'E'):
                chars.append(self.advance())
                if self.peek() in ('+', '-'):
                    chars.append(self.advance())
                while self.peek().isdigit():
                    chars.append(self.advance())
            raw = ''.join(chars)
            return Token(TT.FLOAT, float(raw), self.line, tok_col, indent, blank_before, raw)

        raw = ''.join(chars)
        return Token(TT.INT, int(raw), self.line, tok_col, indent, blank_before, raw)

    def _lex_ident(self, indent: int, blank_before: int, tok_col: int) -> Token:
        chars = []
        while self.pos < len(self.source) and self._is_ident_cont(self.peek()):
            chars.append(self.advance())
        name = ''.join(chars)
        return Token(TT.IDENT, name, self.line, tok_col, indent, blank_before, name)

    @staticmethod
    def _is_ident_start(ch: str) -> bool:
        if not ch:
            return False
        return ch.isalpha() or ch == '_' or (ord(ch) > 127 and ch not in ALL_OPERATORS
                                              and ch not in TYPE_NAMES
                                              and ch not in '⦿⦾⌸⟨⟩⟦⟧«»[]→|,')

    @staticmethod
    def _is_ident_cont(ch: str) -> bool:
        if not ch:
            return False
        return (ch.isalnum() or ch in ('_', '\'', '`')
                or (ord(ch) > 127
                    and ch not in ALL_OPERATORS
                    and ch not in TYPE_NAMES
                    and ch not in '⦿⦾⌸⟨⟩⟦⟧«»[]→|,'))

# ═══════════════════════════════════════════════════════════════════════════════
# AST NODES
# ═══════════════════════════════════════════════════════════════════════════════

@dataclass
class Node:
    line: int
    col:  int
    indent: int
    blank_before: int

@dataclass
class IntLitNode(Node):
    value: int

@dataclass
class FloatLitNode(Node):
    value: float

@dataclass
class StringLitNode(Node):
    value: str

@dataclass
class OpNode(Node):
    op: str               # operator symbol

@dataclass
class IdentNode(Node):
    name: str             # function call or name reference

@dataclass
class TypeNode(Node):
    name: str             # ℕ ℤ 𝔽 𝔹 ⊤ ⊥

@dataclass
class CommentNode(Node):
    content: str          # raw comment text (affects entropy)

@dataclass
class LatticeReadNode(Node):
    coords: tuple         # (x_expr, y_expr, z_expr) as strings

@dataclass
class LatticeWriteNode(Node):
    coords: tuple

@dataclass
class ChecksumNode(Node):
    value: int            # expected CRC-32

@dataclass
class TypeSig:
    omega_in:  list[str]
    omega_out: list[str]
    psi_in:    list[str]
    psi_out:   list[str]

@dataclass
class FuncDefNode(Node):
    name:     str
    typesig:  Optional[TypeSig]
    body:     list[Node]
    checksum: int         # expected checksum for body

@dataclass
class ProgramNode:
    functions: dict[str, FuncDefNode]
    top_level: list[Node]
    filename:  str

# ═══════════════════════════════════════════════════════════════════════════════
# PARSER
# ═══════════════════════════════════════════════════════════════════════════════

class Parser:
    """
    Recursive descent parser.
    Validates block checksums during parse (fatal on mismatch).
    """

    def __init__(self, tokens: list[Token], filename: str = '<unknown>',
                 skip_checksum: bool = False):
        self.tokens         = tokens
        self.pos            = 0
        self.filename       = filename
        self.skip_checksum  = skip_checksum

    def error(self, msg: str) -> ParseError:
        t = self.current()
        return ParseError(msg, t.line, t.col, self.filename)

    def current(self) -> Token:
        return self.tokens[min(self.pos, len(self.tokens) - 1)]

    def peek_type(self) -> TT:
        return self.current().type

    def advance(self) -> Token:
        t = self.current()
        if t.type != TT.EOF:
            self.pos += 1
        return t

    def expect(self, tt: TT) -> Token:
        t = self.current()
        if t.type != tt:
            raise self.error(f"Expected {tt.name}, got {t.type.name} ({t.raw!r})")
        return self.advance()

    # ── entry point ──────────────────────────────────────────────────────────

    def parse(self) -> ProgramNode:
        functions: dict[str, FuncDefNode] = {}
        top_level: list[Node]             = []

        while self.peek_type() != TT.EOF:
            if self.peek_type() == TT.COMMENT:
                t = self.advance()
                top_level.append(CommentNode(t.line, t.col, t.indent, t.blank_before, t.value))
            elif self.peek_type() == TT.FUNC_DEF:
                fn = self._parse_func()
                functions[fn.name] = fn
            else:
                node = self._parse_stmt()
                if node is not None:
                    top_level.append(node)

        return ProgramNode(functions, top_level, self.filename)

    # ── function definition ───────────────────────────────────────────────────

    def _parse_func(self) -> FuncDefNode:
        t_def = self.expect(TT.FUNC_DEF)
        # next token should be IDENT (function name)
        if self.peek_type() not in (TT.IDENT, TT.OP, TT.TYPE):
            raise self.error("Expected function name after ⦿")
        t_name = self.advance()
        name   = t_name.raw

        typesig = None
        if self.peek_type() == TT.TYPESIG_BEGIN:
            typesig = self._parse_typesig()

        # Parse body until CHECKSUM + FUNC_END
        body_tokens: list[Token] = []
        body_nodes:  list[Node]  = []

        while self.peek_type() not in (TT.CHECKSUM, TT.FUNC_END, TT.EOF):
            t = self.current()
            body_tokens.append(t)
            node = self._parse_stmt()
            if node is not None:
                body_nodes.append(node)

        expected_checksum = 0
        if self.peek_type() == TT.CHECKSUM:
            t_cs = self.advance()
            expected_checksum = t_cs.value

        # Verify checksum
        if not self.skip_checksum and expected_checksum != 0:
            actual = compute_block_checksum(body_tokens)
            if actual != expected_checksum:
                t_fn = self.tokens[self.pos - 1]
                raise ChecksumError(
                    f"Checksum mismatch in function '{name}': "
                    f"expected 0x{expected_checksum:08X}, computed 0x{actual:08X}. "
                    f"Use --compute-checksums to get the correct value.",
                    t_def.line, t_def.col, self.filename)

        if self.peek_type() == TT.FUNC_END:
            self.advance()
        else:
            raise self.error(f"Expected ⦾ to close function '{name}'")

        return FuncDefNode(
            line=t_def.line, col=t_def.col,
            indent=t_def.indent, blank_before=t_def.blank_before,
            name=name, typesig=typesig,
            body=body_nodes, checksum=expected_checksum
        )

    def _parse_typesig(self) -> TypeSig:
        self.expect(TT.TYPESIG_BEGIN)
        omega_in, omega_out, psi_in, psi_out = [], [], [], []
        # grammar: [ ω_in → ω_out | ψ_in → ψ_out ]
        section = 0   # 0=ω_in, 1=ω_out, 2=ψ_in, 3=ψ_out
        targets = [omega_in, omega_out, psi_in, psi_out]
        while self.peek_type() not in (TT.TYPESIG_END, TT.EOF):
            t = self.current()
            if t.type == TT.ARROW:
                self.advance()
                section = min(section + 1, 3)
            elif t.type == TT.PIPE:
                self.advance()
                section = max(2, section)
            elif t.type == TT.TYPE:
                self.advance()
                targets[section].append(t.value)
            else:
                self.advance()  # skip unknown tokens inside typesig
        self.expect(TT.TYPESIG_END)
        return TypeSig(omega_in, omega_out, psi_in, psi_out)

    # ── statement ─────────────────────────────────────────────────────────────

    def _parse_stmt(self) -> Optional[Node]:
        t = self.current()
        if t.type == TT.EOF:
            return None

        if t.type == TT.COMMENT:
            self.advance()
            return CommentNode(t.line, t.col, t.indent, t.blank_before, t.value)
        if t.type == TT.INT:
            self.advance()
            return IntLitNode(t.line, t.col, t.indent, t.blank_before, t.value)
        if t.type == TT.FLOAT:
            self.advance()
            return FloatLitNode(t.line, t.col, t.indent, t.blank_before, t.value)
        if t.type == TT.STRING:
            self.advance()
            return StringLitNode(t.line, t.col, t.indent, t.blank_before, t.value)
        if t.type == TT.OP:
            self.advance()
            return OpNode(t.line, t.col, t.indent, t.blank_before, t.value)
        if t.type == TT.IDENT:
            self.advance()
            return IdentNode(t.line, t.col, t.indent, t.blank_before, t.value)
        if t.type == TT.TYPE:
            self.advance()
            return TypeNode(t.line, t.col, t.indent, t.blank_before, t.value)
        if t.type == TT.LAT_READ:
            self.advance()
            return LatticeReadNode(t.line, t.col, t.indent, t.blank_before, t.value)
        if t.type == TT.LAT_WRITE:
            self.advance()
            return LatticeWriteNode(t.line, t.col, t.indent, t.blank_before, t.value)
        if t.type == TT.CHECKSUM:
            self.advance()
            return ChecksumNode(t.line, t.col, t.indent, t.blank_before, t.value)
        if t.type in (TT.FUNC_DEF, TT.FUNC_END, TT.TYPESIG_BEGIN, TT.TYPESIG_END,
                      TT.ARROW, TT.PIPE, TT.COMMA):
            # These are structural; skip gracefully
            self.advance()
            return None

        self.advance()  # skip unknown
        return None

# ═══════════════════════════════════════════════════════════════════════════════
# RUNTIME
# ═══════════════════════════════════════════════════════════════════════════════

@dataclass
class CallFrame:
    """One entry in the inverse-scope call stack."""
    func_name:     str
    lattice_reads: list[tuple[int,int,int]]  # cells read in this frame (for void cascade)

class VorthexRuntime:
    """
    Manages all mutable interpreter state:
      Ω stack, Ψ stack, 3D lattice, entropy register,
      function table, call stack, RTQ, scope stack.
    """

    def __init__(self, debug: bool = False):
        self.omega:       list[Any]                         = []   # Ω stack
        self.psi:         list[Any]                         = []   # Ψ stack
        self.lattice:     dict[tuple[int,int,int], Any]     = {}   # ℒ[x][y][z]
        self.entropy:     int                               = INITIAL_ENTROPY
        self.functions:   dict[str, FuncDefNode]            = {}
        self.degraded:    bool                              = False
        self.pass_number: int                               = 1
        self.rtq:         list[Node]                        = []   # reverse-time queue
        self.call_stack:  list[CallFrame]                   = []
        self.last_op_stack: str                             = 'omega'  # context for operators
        self.debug:       bool                              = debug
        self.stdout:      Any                               = sys.stdout
        self.stdin:       Any                               = sys.stdin

    # ── entropy ───────────────────────────────────────────────────────────────

    def update_entropy(self, comment_content: str) -> None:
        """FNV-1a hash of comment content XOR'd into entropy register."""
        h = fnv1a_32(comment_content.encode('utf-8'))
        old = self.entropy
        self.entropy ^= h
        if self.debug:
            print(f"  [entropy] ε: 0x{old:08X} ^ fnv({comment_content!r})"
                  f"=0x{h:08X} → 0x{self.entropy:08X}", file=sys.stderr)

    # ── stack operations ──────────────────────────────────────────────────────

    def _check_overflow(self, stack_name: str, stack: list) -> None:
        if len(stack) > MAX_STACK_SIZE:
            self._entropic_collapse()

    def _entropic_collapse(self) -> None:
        """XOR-merge both stacks into Ω; enter degraded single-stack mode."""
        print("  [ENTROPIC COLLAPSE] Stack overflow. Merging Ω and Ψ via XOR. "
              "Execution continues in degraded mode.", file=sys.stderr)
        merged = []
        max_len = max(len(self.omega), len(self.psi))
        for i in range(max_len):
            a = self.omega[i] if i < len(self.omega) else 0
            b = self.psi[i]   if i < len(self.psi)   else 0
            try:
                merged.append(int(a) ^ int(b))
            except (TypeError, ValueError):
                merged.append(a)
        self.omega    = merged
        self.psi      = []
        self.degraded = True

    def push_omega(self, value: Any) -> None:
        self.omega.append(value)
        self.last_op_stack = 'omega'
        self._check_overflow('Ω', self.omega)

    def push_psi(self, value: Any) -> None:
        self.psi.append(value)
        self.last_op_stack = 'psi'
        self._check_overflow('Ψ', self.psi)

    def pop_omega(self, line: int = 0, col: int = 0) -> Any:
        if not self.omega:
            raise StackUnderflowError("Ω stack underflow", self, line, col)
        return self.omega.pop()

    def pop_psi(self, line: int = 0, col: int = 0) -> Any:
        if not self.psi:
            if self.degraded:
                raise StackUnderflowError("Ψ stack underflow (degraded mode)", self, line, col)
            raise StackUnderflowError("Ψ stack underflow", self, line, col)
        return self.psi.pop()

    def peek_omega(self, line: int = 0, col: int = 0) -> Any:
        if not self.omega:
            raise StackUnderflowError("Ω stack underflow (peek)", self, line, col)
        return self.omega[-1]

    def peek_psi(self, line: int = 0, col: int = 0) -> Any:
        if not self.psi:
            raise StackUnderflowError("Ψ stack underflow (peek)", self, line, col)
        return self.psi[-1]

    # ── lattice operations ────────────────────────────────────────────────────

    def lattice_read(self, x: int, y: int, z: int,
                     line: int = 0, col: int = 0) -> Any:
        coord = (int(x), int(y), int(z))
        # Record for void cascade tracking
        if self.call_stack:
            self.call_stack[-1].lattice_reads.append(coord)
        if coord not in self.lattice:
            self._void_cascade(coord, line, col)
        return self.lattice[coord]

    def lattice_write(self, x: int, y: int, z: int, value: Any) -> None:
        coord = (int(x), int(y), int(z))
        self.lattice[coord] = value
        # Inverse scoping: write propagates to ALL enclosing scopes
        # (All scopes share the same lattice dict, so this is automatic.)
        # However we record the write for debugging.
        if self.debug and self.call_stack:
            depth = len(self.call_stack)
            print(f"  [lattice] ℒ{coord} ← {value!r}  (scope depth {depth})",
                  file=sys.stderr)

    def _void_cascade(self, coord: tuple[int,int,int],
                      line: int, col: int) -> None:
        """
        Void cascade: reading an uninitialized cell.
        Sets every cell read in current frame to ⊥ (None),
        pushes None onto Ω, and continues execution (corrupted state).
        """
        print(f"  [VOID CASCADE] Read uninitialized ℒ{coord} at "
              f"line {line}, col {col}. "
              f"Setting all reads in current frame to ⊥. "
              f"Execution continues with corrupted state.",
              file=sys.stderr)
        if self.call_stack:
            for c in self.call_stack[-1].lattice_reads:
                self.lattice[c] = None  # set to ⊥
        self.lattice[coord] = None
        self.omega.append(None)   # push ⊥ to Ω and continue

    # ── context-shifted operator dispatch ────────────────────────────────────

    # Categories where entropy register actively flips the context
    _ENTROPY_SENSITIVE = frozenset({'dual', 'ctrl', 'bitwise', 'higher'})

    def get_op_mode(self, col: int, category: str = '') -> str:
        """
        Determine operator mode from:
          (a) last-used stack context (omega / psi)   [primary]
          (b) column position of token                [secondary]
          (c) entropy register (only for ε-sensitive categories)
        Returns 'omega', 'psi', or 'both'.
        """
        if col >= 81:
            return 'both'
        base = 'psi' if col >= 41 else 'omega'
        # Entropy flips mode only for control/dual/bitwise/higher ops
        if category in self._ENTROPY_SENSITIVE:
            entropy_bit = (self.entropy >> 16) & 1
            if entropy_bit:
                base = 'psi' if base == 'omega' else 'omega'
        return base

    # ── operator implementations ──────────────────────────────────────────────

    def exec_op(self, op: str, line: int, col: int) -> None:
        """Dispatch an operator symbol."""
        if op not in OPERATOR_TABLE:
            raise DispatchError(f"Unknown operator {op!r}", self, line, col)

        category, omega_action, psi_action, _ = OPERATOR_TABLE[op]
        mode = self.get_op_mode(col, category)
        action = omega_action if mode != 'psi' else psi_action

        if self.debug:
            print(f"  [op] {op} → {action} (mode={mode}, ε=0x{self.entropy:08X})",
                  file=sys.stderr)

        self.last_op_stack = 'omega' if mode != 'psi' else 'psi'
        handler = getattr(self, f'_op_{action}', None)
        if handler is None:
            # Fall back to generic omega action
            handler = getattr(self, f'_op_{omega_action}', None)
        if handler is None:
            print(f"  Warning: operator {op!r} action '{action}' not implemented, skipped",
                  file=sys.stderr)
            return
        handler(line, col)

    # ─── arithmetic ────────────────────────────────────────────────────────────
    # All binary arithmetic operators fall back to Ω-only (pop two from Ω)
    # when Ψ is empty.  When Ψ has values, the standard cross-stack mode
    # applies: a = pop_omega, b = pop_psi, result pushed to Ω.

    def _pop_binary(self, line: int, col: int) -> tuple[Any, Any]:
        """Pop operands for a binary op: cross-stack if Ψ has values, else Ω-only."""
        if self.psi:
            b = self.pop_psi(line, col)
            a = self.pop_omega(line, col)
        else:
            b = self.pop_omega(line, col)   # top
            a = self.pop_omega(line, col)   # second
        return a, b

    def _op_add(self, line: int, col: int) -> None:
        a, b = self._pop_binary(line, col)
        self.push_omega(self._numeric(a) + self._numeric(b))

    def _op_sub(self, line: int, col: int) -> None:
        a, b = self._pop_binary(line, col)
        self.push_omega(self._numeric(a) - self._numeric(b))

    def _op_mul(self, line: int, col: int) -> None:
        a, b = self._pop_binary(line, col)
        self.push_omega(self._numeric(a) * self._numeric(b))

    def _op_div(self, line: int, col: int) -> None:
        a, b = self._pop_binary(line, col)
        bv = self._numeric(b)
        if bv == 0:
            raise RuntimeError_(f"Division by zero at ℒ state: "
                                 f"Ω={self.omega[-4:]}, Ψ={self.psi[-4:]}",
                                 self, line, col)
        result = self._numeric(a) / bv
        self.push_omega(int(result) if isinstance(a, int) and isinstance(b, int)
                        and bv != 0 and int(a) % int(bv) == 0 else result)

    def _op_mod(self, line: int, col: int) -> None:
        a, b = self._pop_binary(line, col)
        bv = self._numeric(b)
        if bv == 0:
            raise RuntimeError_("Modulo by zero", self, line, col)
        self.push_omega(self._numeric(a) % bv)

    def _op_type_union(self, line: int, col: int) -> None:
        self._op_add(line, col)  # simplified: use add semantics

    def _op_type_diff(self, line: int, col: int) -> None:
        self._op_sub(line, col)

    def _op_type_product(self, line: int, col: int) -> None:
        self._op_mul(line, col)

    def _op_type_quotient(self, line: int, col: int) -> None:
        self._op_div(line, col)

    def _op_type_residue(self, line: int, col: int) -> None:
        self._op_mod(line, col)

    # ─── bitwise ───────────────────────────────────────────────────────────────

    def _op_xor(self, line: int, col: int) -> None:
        b = self.pop_psi(line, col)
        a = self.pop_omega(line, col)
        self.push_omega(int(a) ^ int(b))

    def _op_nand(self, line: int, col: int) -> None:
        b = self.pop_psi(line, col)
        a = self.pop_omega(line, col)
        self.push_omega(~(int(a) & int(b)) & 0xFFFFFFFF)

    def _op_nor(self, line: int, col: int) -> None:
        b = self.pop_psi(line, col)
        a = self.pop_omega(line, col)
        self.push_omega(~(int(a) | int(b)) & 0xFFFFFFFF)

    def _op_rotl(self, line: int, col: int) -> None:
        n  = int(self.pop_psi(line, col)) & 31
        a  = int(self.pop_omega(line, col)) & 0xFFFFFFFF
        self.push_omega(((a << n) | (a >> (32 - n))) & 0xFFFFFFFF)

    def _op_type_cast(self, line: int, col: int) -> None:
        tname = self.pop_psi(line, col)
        val   = self.pop_omega(line, col)
        self.push_omega(self._cast(val, tname))

    def _op_bitand(self, line: int, col: int) -> None:
        b = self.pop_omega(line, col)
        a = self.pop_omega(line, col)
        self.push_omega(int(a) & int(b))

    def _op_bitor(self, line: int, col: int) -> None:
        b = self.pop_omega(line, col)
        a = self.pop_omega(line, col)
        self.push_omega(int(a) | int(b))

    def _op_entropy_fork(self, line: int, col: int) -> None:
        """XOR top of Ψ into entropy and push current entropy to Ω."""
        v = self.pop_psi(line, col)
        self.entropy ^= (int(v) & 0xFFFFFFFF)
        self.push_omega(self.entropy)

    def _op_type_complement(self, line: int, col: int) -> None:
        a = self.pop_omega(line, col)
        self.push_omega(~int(a) & 0xFFFFFFFF)

    def _op_type_inter_comp(self, line: int, col: int) -> None:
        b = self.pop_psi(line, col)
        a = self.pop_omega(line, col)
        self.push_omega(~(int(a) & int(b)) & 0xFFFFFFFF)

    def _op_type_intersection(self, line: int, col: int) -> None:
        self._op_bitand(line, col)

    def _op_type_union2(self, line: int, col: int) -> None:
        self._op_bitor(line, col)

    # ─── stack manipulation ────────────────────────────────────────────────────

    def _op_swap_heads(self, line: int, col: int) -> None:
        a = self.pop_omega(line, col)
        b = self.pop_psi(line, col)
        self.push_omega(b)
        self.push_psi(a)

    def _op_dup_omega(self, line: int, col: int) -> None:
        v = self.peek_omega(line, col)
        self.push_omega(v)

    def _op_dup_psi(self, line: int, col: int) -> None:
        v = self.peek_psi(line, col)
        self.push_psi(v)

    def _op_drop_omega(self, line: int, col: int) -> None:
        self.pop_omega(line, col)

    def _op_drop_psi(self, line: int, col: int) -> None:
        if self.psi:
            self.pop_psi(line, col)

    def _op_swap_omega(self, line: int, col: int) -> None:
        b = self.pop_omega(line, col)
        a = self.pop_omega(line, col)
        self.push_omega(b)
        self.push_omega(a)

    def _op_swap_psi(self, line: int, col: int) -> None:
        b = self.pop_psi(line, col)
        a = self.pop_psi(line, col)
        self.push_psi(b)
        self.push_psi(a)

    def _op_over_omega(self, line: int, col: int) -> None:
        if len(self.omega) < 2:
            raise StackUnderflowError("⧓ requires ≥2 items on Ω", self, line, col)
        self.push_omega(self.omega[-2])

    def _op_over_psi(self, line: int, col: int) -> None:
        if len(self.psi) < 2:
            raise StackUnderflowError("⧓ requires ≥2 items on Ψ", self, line, col)
        self.push_psi(self.psi[-2])

    def _op_rot_omega(self, line: int, col: int) -> None:
        if len(self.omega) < 3:
            raise StackUnderflowError("⟲ requires ≥3 items on Ω", self, line, col)
        c = self.omega.pop(); b = self.omega.pop(); a = self.omega.pop()
        self.omega.extend([b, c, a])

    def _op_rot_psi(self, line: int, col: int) -> None:
        if len(self.psi) < 3:
            raise StackUnderflowError("⟲ requires ≥3 items on Ψ", self, line, col)
        c = self.psi.pop(); b = self.psi.pop(); a = self.psi.pop()
        self.psi.extend([b, c, a])

    def _op_unrot_omega(self, line: int, col: int) -> None:
        if len(self.omega) < 3:
            raise StackUnderflowError("⟳ requires ≥3 items on Ω", self, line, col)
        c = self.omega.pop(); b = self.omega.pop(); a = self.omega.pop()
        self.omega.extend([c, a, b])

    def _op_unrot_psi(self, line: int, col: int) -> None:
        if len(self.psi) < 3:
            raise StackUnderflowError("⟳ requires ≥3 items on Ψ", self, line, col)
        c = self.psi.pop(); b = self.psi.pop(); a = self.psi.pop()
        self.psi.extend([c, a, b])

    def _op_xfer_psi_to_omega(self, line: int, col: int) -> None:
        v = self.peek_psi(line, col)
        self.push_omega(v)

    def _op_xfer_omega_to_psi(self, line: int, col: int) -> None:
        v = self.peek_omega(line, col)
        self.push_psi(v)

    def _op_push_both(self, line: int, col: int) -> None:
        a = self.peek_omega(line, col) if self.omega else 0
        b = self.peek_psi(line, col)  if self.psi   else 0
        self.push_omega(b)
        self.push_psi(a)

    def _op_pop_both(self, line: int, col: int) -> None:
        if self.omega: self.omega.pop()
        if self.psi:   self.psi.pop()

    def _op_copy_o_to_p(self, line: int, col: int) -> None:
        v = self.peek_omega(line, col)
        self.push_psi(v)

    def _op_copy_p_to_o(self, line: int, col: int) -> None:
        v = self.peek_psi(line, col)
        self.push_omega(v)

    def _op_move_o_to_p(self, line: int, col: int) -> None:
        v = self.pop_omega(line, col)
        self.push_psi(v)

    def _op_move_p_to_o(self, line: int, col: int) -> None:
        v = self.pop_psi(line, col)
        self.push_omega(v)

    # ─── cross-stack ───────────────────────────────────────────────────────────

    def _op_cross_product(self, line: int, col: int) -> None:
        b = self.pop_psi(line, col)
        a = self.pop_omega(line, col)
        self.push_omega((a, b))

    def _op_void_cascade(self, line: int, col: int) -> None:
        """Single-stack ⊛: deliberately trigger void cascade semantics."""
        if self.call_stack:
            for c in self.call_stack[-1].lattice_reads:
                self.lattice[c] = None
        self.push_omega(None)

    def _op_interleave(self, line: int, col: int) -> None:
        merged = []
        lo, lp = len(self.omega), len(self.psi)
        for i in range(max(lo, lp)):
            if i < lo: merged.append(self.omega[i])
            if i < lp: merged.append(self.psi[i])
        self.omega = merged
        self.psi   = []

    def _op_split(self, line: int, col: int) -> None:
        evens = self.omega[0::2]
        odds  = self.omega[1::2]
        self.omega = evens
        self.psi   = odds

    def _op_left_merge(self, line: int, col: int) -> None:
        self.omega = self.omega + self.psi
        self.psi   = []

    def _op_right_merge(self, line: int, col: int) -> None:
        self.omega = self.psi + self.omega
        self.psi   = []

    def _op_left_split(self, line: int, col: int) -> None:
        half = len(self.omega) // 2
        self.psi   = self.omega[half:]
        self.omega = self.omega[:half]

    def _op_right_split(self, line: int, col: int) -> None:
        half = len(self.omega) // 2
        self.psi   = self.omega[:half]
        self.omega = self.omega[half:]

    # ─── logic ─────────────────────────────────────────────────────────────────

    def _op_and_op(self, line: int, col: int) -> None:
        b = self.pop_psi(line, col)
        a = self.pop_omega(line, col)
        self.push_omega(bool(a) and bool(b))

    def _op_or_op(self, line: int, col: int) -> None:
        b = self.pop_psi(line, col)
        a = self.pop_omega(line, col)
        self.push_omega(bool(a) or bool(b))

    def _op_not_omega(self, line: int, col: int) -> None:
        a = self.pop_omega(line, col)
        self.push_omega(not bool(a))

    def _op_not_psi(self, line: int, col: int) -> None:
        a = self.pop_psi(line, col)
        self.push_psi(not bool(a))

    def _op_type_and(self, line: int, col: int) -> None:
        self._op_and_op(line, col)

    def _op_type_or(self, line: int, col: int) -> None:
        self._op_or_op(line, col)

    # ─── comparison ────────────────────────────────────────────────────────────
    # Same Ω fallback: when Ψ is empty, compare top two on Ω.

    def _op_eq(self, line: int, col: int) -> None:
        a, b = self._pop_binary(line, col)
        self.push_omega(a == b)

    def _op_neq(self, line: int, col: int) -> None:
        a, b = self._pop_binary(line, col)
        self.push_omega(a != b)

    def _op_lt(self, line: int, col: int) -> None:
        a, b = self._pop_binary(line, col)
        try:
            self.push_omega(a < b)
        except TypeError:
            self.push_omega(False)

    def _op_gt(self, line: int, col: int) -> None:
        a, b = self._pop_binary(line, col)
        try:
            self.push_omega(a > b)
        except TypeError:
            self.push_omega(False)

    def _op_approx_eq(self, line: int, col: int) -> None:
        a, b = self._pop_binary(line, col)
        av, bv = self._numeric(a), self._numeric(b)
        self.push_omega(abs(av - bv) < EPSILON * max(abs(av), abs(bv), 1.0))

    def _op_type_equiv(self, line: int, col: int) -> None:
        self._op_eq(line, col)

    def _op_type_neq(self, line: int, col: int) -> None:
        self._op_neq(line, col)

    def _op_subtype(self, line: int, col: int) -> None:
        self._op_lt(line, col)

    def _op_supertype(self, line: int, col: int) -> None:
        self._op_gt(line, col)

    def _op_type_compat(self, line: int, col: int) -> None:
        self._op_approx_eq(line, col)

    # ─── control flow ──────────────────────────────────────────────────────────

    def _op_branch_gt(self, line: int, col: int) -> None:
        """
        ⟁ (standalone, no lookahead): if Ω top > Ψ top, call fn named by Ω next.
        The evaluator's exec_nodes handles the lookahead case ⟁ NAME.
        This fallback is invoked when ⟁ appears without a following identifier.
        """
        if self.psi:
            cond_b = self.pop_psi(line, col)
            cond_a = self.pop_omega(line, col)
            do_branch = self._numeric(cond_a) > self._numeric(cond_b)
        else:
            cond = self.pop_omega(line, col) if self.omega else False
            do_branch = bool(cond)
        # Without a following identifier, branch target must be on Ω
        if do_branch and self.omega:
            target = self.pop_omega(line, col)
            if isinstance(target, str) and target in self.functions:
                self._call_function(target, line, col)

    def _op_rtq_defer(self, line: int, col: int) -> None:
        """Ψ context for ⟁: no-op at runtime (deferral is handled by evaluator)."""
        pass

    def _op_self_dispatch(self, line: int, col: int) -> None:
        """⊜: pop Ω top (expected to be an FNV-1a hash), dispatch to matching fn."""
        if not self.omega:
            return
        target_hash = int(self.pop_omega(line, col))
        # Find function whose name hashes to target_hash
        for name, fn in self.functions.items():
            if fnv1a_32(name.encode('utf-8')) == target_hash:
                self._call_function(name, line, col)
                return
        raise DispatchError(
            f"⊜ self-dispatch: no function with FNV-1a hash 0x{target_hash:08X}",
            self, line, col)

    def _op_tail_recurse(self, line: int, col: int) -> None:
        """Ψ context for ⊜: tail-recurse the current function."""
        if self.call_stack:
            fname = self.call_stack[-1].func_name
            if fname in self.functions:
                self._call_function(fname, line, col)

    # ─── I/O ───────────────────────────────────────────────────────────────────
    # I/O operators ALWAYS consume/produce on Ω regardless of column context.
    # The mode (omega vs psi) only determines the OUTPUT DESTINATION:
    #   omega mode → stdout; psi mode → stderr.

    def _op_write_stdout(self, line: int, col: int) -> None:
        v = self.pop_omega(line, col)
        self.stdout.write(self._display(v))
        self.stdout.flush()

    def _op_write_stderr(self, line: int, col: int) -> None:
        # Ψ-mode ⊞: pop Ω top, write to stderr (not stdout)
        v = self.pop_omega(line, col)
        sys.stderr.write(self._display(v))
        sys.stderr.flush()

    def _op_read_stdin_o(self, line: int, col: int) -> None:
        try:
            line_s = self.stdin.readline().rstrip('\n')
        except EOFError:
            line_s = ''
        try:
            self.push_omega(int(line_s))
        except ValueError:
            try:
                self.push_omega(float(line_s))
            except ValueError:
                self.push_omega(line_s)

    def _op_read_stdin_p(self, line: int, col: int) -> None:
        # Ψ-mode ⊟: read and push to Ψ
        try:
            line_s = self.stdin.readline().rstrip('\n')
        except EOFError:
            line_s = ''
        try:
            self.push_psi(int(line_s))
        except ValueError:
            try:
                self.push_psi(float(line_s))
            except ValueError:
                self.push_psi(line_s)

    # ─── lattice entropy op ────────────────────────────────────────────────────

    def _op_lat_write_ent(self, line: int, col: int) -> None:
        """⊘ Ω-mode: write Ω top to ℒ[Ω[-2]][Ψ top][ε & 0xFF]."""
        v = self.pop_omega(line, col)
        if not self.omega:
            raise StackUnderflowError("⊘ requires ≥2 items on Ω", self, line, col)
        x = int(self.pop_omega(line, col))
        y = int(self.pop_psi(line, col))
        z = int(self.entropy & 0xFF)
        self.lattice_write(x, y, z, v)

    def _op_lat_read_ent(self, line: int, col: int) -> None:
        """⊘ Ψ-mode: read ℒ[Ω top][Ψ top][ε & 0xFF] → Ω."""
        x = int(self.pop_omega(line, col))
        y = int(self.pop_psi(line, col))
        z = int(self.entropy & 0xFF)
        v = self.lattice_read(x, y, z, line, col)
        self.push_omega(v)

    # ─── numeric ───────────────────────────────────────────────────────────────

    def _op_floor_omega(self, line: int, col: int) -> None:
        v = self.pop_omega(line, col)
        self.push_omega(int(math.floor(self._numeric(v))))

    def _op_floor_psi(self, line: int, col: int) -> None:
        v = self.pop_psi(line, col)
        self.push_psi(int(math.floor(self._numeric(v))))

    def _op_ceil_omega(self, line: int, col: int) -> None:
        v = self.pop_omega(line, col)
        self.push_omega(int(math.ceil(self._numeric(v))))

    def _op_ceil_psi(self, line: int, col: int) -> None:
        v = self.pop_psi(line, col)
        self.push_psi(int(math.ceil(self._numeric(v))))

    def _op_dec_omega(self, line: int, col: int) -> None:
        v = self.pop_omega(line, col)
        self.push_omega(self._numeric(v) - 1)

    def _op_dec_psi(self, line: int, col: int) -> None:
        v = self.pop_psi(line, col)
        self.push_psi(self._numeric(v) - 1)

    def _op_inc_omega(self, line: int, col: int) -> None:
        v = self.pop_omega(line, col)
        self.push_omega(self._numeric(v) + 1)

    def _op_inc_psi(self, line: int, col: int) -> None:
        v = self.pop_psi(line, col)
        self.push_psi(self._numeric(v) + 1)

    # ─── literals ──────────────────────────────────────────────────────────────

    def _op_push_zero_o(self, line: int, col: int) -> None:
        self.push_omega(0)

    def _op_push_zero_p(self, line: int, col: int) -> None:
        self.push_psi(0)

    def _op_push_inf_o(self, line: int, col: int) -> None:
        self.push_omega(float('inf'))

    def _op_push_inf_p(self, line: int, col: int) -> None:
        self.push_psi(float('inf'))

    # ─── higher-order ──────────────────────────────────────────────────────────

    def _op_fold_omega(self, line: int, col: int) -> None:
        """∫ Ω-mode: fold Ω stack using function named on Ψ top as accumulator fn."""
        if not self.psi:
            return
        fname = str(self.pop_psi(line, col))
        if not self.omega:
            self.push_omega(0)
            return
        acc = self.pop_omega(line, col)
        while self.omega:
            item = self.pop_omega(line, col)
            self.push_omega(acc)
            self.push_psi(item)
            if fname in self.functions:
                self._call_function(fname, line, col)
            acc = self.pop_omega(line, col) if self.omega else acc
        self.push_omega(acc)

    def _op_fold_psi(self, line: int, col: int) -> None:
        fname = str(self.pop_omega(line, col)) if self.omega else ''
        if not self.psi:
            self.push_psi(0)
            return
        acc = self.pop_psi(line, col)
        while self.psi:
            item = self.pop_psi(line, col)
            self.push_psi(acc)
            self.push_omega(item)
            if fname in self.functions:
                self._call_function(fname, line, col)
            acc = self.pop_psi(line, col) if self.psi else acc
        self.push_psi(acc)

    def _op_sum_omega(self, line: int, col: int) -> None:
        total = sum(self._numeric(x) for x in self.omega)
        self.omega = [total]

    def _op_sum_psi(self, line: int, col: int) -> None:
        total = sum(self._numeric(x) for x in self.psi)
        self.psi = [total]

    def _op_prod_omega(self, line: int, col: int) -> None:
        result = 1
        for x in self.omega:
            result *= self._numeric(x)
        self.omega = [result]

    def _op_prod_psi(self, line: int, col: int) -> None:
        result = 1
        for x in self.psi:
            result *= self._numeric(x)
        self.psi = [result]

    def _op_map_omega(self, line: int, col: int) -> None:
        if not self.omega:
            return
        fname = str(self.pop_omega(line, col))
        if fname not in self.functions:
            return
        items    = list(self.omega)
        self.omega = []
        for item in items:
            self.push_omega(item)
            self._call_function(fname, line, col)

    def _op_map_psi(self, line: int, col: int) -> None:
        if not self.psi:
            return
        fname = str(self.pop_psi(line, col))
        if fname not in self.functions:
            return
        items   = list(self.psi)
        self.psi = []
        for item in items:
            self.push_psi(item)
            self._call_function(fname, line, col)

    def _op_any_omega(self, line: int, col: int) -> None:
        pred = str(self.pop_psi(line, col)) if self.psi else ''
        if pred not in self.functions:
            self.push_omega(False)
            return
        found = False
        for item in list(self.omega):
            self.push_omega(item)
            self._call_function(pred, line, col)
            result = self.pop_omega(line, col) if self.omega else False
            if result:
                found = True
                break
        # Remove all items from omega, push result
        self.push_omega(found)

    def _op_any_psi(self, line: int, col: int) -> None:
        pred = str(self.pop_omega(line, col)) if self.omega else ''
        if pred not in self.functions:
            self.push_psi(False)
            return
        found = False
        for item in list(self.psi):
            self.push_psi(item)
            self._call_function(pred, line, col)
            result = self.pop_omega(line, col) if self.omega else False
            if result:
                found = True
                break
        self.push_psi(found)

    # ─── sequence ──────────────────────────────────────────────────────────────

    def _op_range_o(self, line: int, col: int) -> None:
        end   = int(self.pop_omega(line, col))
        start = int(self.pop_psi(line, col))
        for i in range(start, end + 1):
            self.push_omega(i)

    def _op_range_p(self, line: int, col: int) -> None:
        end   = int(self.pop_psi(line, col))
        start = int(self.pop_omega(line, col))
        for i in range(start, end + 1):
            self.push_psi(i)

    # ─── function call ─────────────────────────────────────────────────────────

    def _call_function(self, name: str, line: int, col: int,
                       evaluator: Optional['Evaluator'] = None) -> None:
        if name not in self.functions:
            raise DispatchError(f"Undefined function '{name}'", self, line, col)
        fn   = self.functions[name]
        frame = CallFrame(func_name=name, lattice_reads=[])
        self.call_stack.append(frame)
        try:
            if evaluator:
                evaluator.exec_nodes(fn.body, line, col)
            else:
                # Create a temporary evaluator
                ev = Evaluator(self)
                ev.exec_nodes(fn.body, line, col)
        finally:
            self.call_stack.pop()

    # ─── utilities ─────────────────────────────────────────────────────────────

    @staticmethod
    def _numeric(v: Any) -> Any:
        if v is None:
            return 0
        if isinstance(v, bool):
            return int(v)
        if isinstance(v, (int, float)):
            return v
        try:
            return int(v)
        except (TypeError, ValueError):
            try:
                return float(v)
            except (TypeError, ValueError):
                return 0

    @staticmethod
    def _cast(val: Any, tname: str) -> Any:
        if tname == 'ℕ':
            return max(0, int(VorthexRuntime._numeric(val)))
        if tname == 'ℤ':
            return int(VorthexRuntime._numeric(val))
        if tname == '𝔽':
            return float(VorthexRuntime._numeric(val))
        if tname == '𝔹':
            return bool(val)
        return val  # ⊤ or unknown → identity

    @staticmethod
    def _display(v: Any) -> str:
        if v is None:
            return '⊥'
        if isinstance(v, bool):
            return '⊤' if v else '⊥'
        if isinstance(v, float):
            if math.isinf(v):
                return '∞'
            if math.isnan(v):
                return 'NaN'
            # Print as int if it's a whole number
            if v == int(v):
                return str(int(v))
            return str(v)
        return str(v)

# ═══════════════════════════════════════════════════════════════════════════════
# EVALUATOR  (two-pass with RTQ)
# ═══════════════════════════════════════════════════════════════════════════════

class Evaluator:
    """
    Two-pass evaluator implementing reverse-time semantics.

    Pass 1 (forward):
      - Execute non-deferred statements sequentially
      - Statements with blank_before == 1 → added to RTQ (not executed)
      - Statements with blank_before >= 3 → spawn parallel entropy thread
        (simulated by saving/restoring entropy and executing in place)
      - Statements with blank_before == 2 → execute in reverse order
        relative to their local group

    Pass 2 (backward):
      - Execute RTQ in reverse order
    """

    def __init__(self, runtime: VorthexRuntime, debug: bool = False):
        self.rt    = runtime
        self.debug = debug

    # ── coordinate evaluation ─────────────────────────────────────────────────

    def _eval_coord(self, expr: str, line: int, col: int) -> int:
        """
        Evaluate a lattice coordinate expression.
        Supports: integer literals, Ω (top of Ω stack), Ψ (top of Ψ stack),
        and simple arithmetic using Python eval with restricted globals.
        """
        expr = expr.strip()
        if expr == '':
            return 0
        if expr == 'Ω':
            return int(self.rt.peek_omega(line, col)) if self.rt.omega else 0
        if expr == 'Ψ':
            return int(self.rt.peek_psi(line, col)) if self.rt.psi else 0
        if expr == 'ε':
            return int(self.rt.entropy)
        try:
            return int(expr, 0)
        except ValueError:
            pass
        try:
            return int(expr)
        except ValueError:
            pass
        # Try evaluating as a simple arithmetic expression using ast.literal_eval
        # or a restricted integer-only parser.  eval() is NOT used here.
        result = self._eval_coord_arith(expr)
        return int(result) if result is not None else 0

    _COORD_ARITH_OPS = {
        ast.Add:  lambda a, b: a + b,
        ast.Sub:  lambda a, b: a - b,
        ast.Mult: lambda a, b: a * b,
        ast.FloorDiv: lambda a, b: a // b if b else 0,
        ast.Mod:  lambda a, b: a % b if b else 0,
        ast.USub: lambda a: -a,
        ast.UAdd: lambda a: a,
    }

    def _eval_coord_arith(self, expr: str) -> Optional[int]:
        """Safely evaluate a coordinate arithmetic expression (integers only)."""
        try:
            tree = ast.parse(expr, mode='eval')
        except SyntaxError:
            return None

        def _eval(node: ast.expr) -> int:
            if isinstance(node, ast.Expression):
                return _eval(node.body)
            if isinstance(node, ast.Constant) and isinstance(node.value, int):
                return node.value
            if isinstance(node, ast.BinOp):
                op_type = type(node.op)
                fn = self._COORD_ARITH_OPS.get(op_type)
                if fn is None:
                    raise ValueError(f"Unsupported op {op_type}")
                return fn(_eval(node.left), _eval(node.right))
            if isinstance(node, ast.UnaryOp):
                op_type = type(node.op)
                fn = self._COORD_ARITH_OPS.get(op_type)
                if fn is None:
                    raise ValueError(f"Unsupported unary op {op_type}")
                return fn(_eval(node.operand))
            raise ValueError(f"Unsupported node type {type(node)}")

        try:
            return _eval(tree.body)
        except Exception:
            return None

    # ── node execution ────────────────────────────────────────────────────────

    def exec_node(self, node: Node) -> None:
        """Execute a single AST node."""
        line, col = node.line, node.col

        if isinstance(node, CommentNode):
            self.rt.update_entropy(node.content)

        elif isinstance(node, IntLitNode):
            if col >= 41:
                self.rt.push_psi(node.value)
            else:
                self.rt.push_omega(node.value)

        elif isinstance(node, FloatLitNode):
            if col >= 41:
                self.rt.push_psi(node.value)
            else:
                self.rt.push_omega(node.value)

        elif isinstance(node, StringLitNode):
            if col >= 41:
                self.rt.push_psi(node.value)
            else:
                self.rt.push_omega(node.value)

        elif isinstance(node, TypeNode):
            # Type names used as values push their string representation
            if node.name in ('⊤', '⊥'):
                val = True if node.name == '⊤' else False
                self.rt.push_omega(val)
            else:
                self.rt.push_omega(node.name)

        elif isinstance(node, OpNode):
            self.rt.exec_op(node.op, line, col)

        elif isinstance(node, IdentNode):
            name = node.name
            if name in self.rt.functions:
                self.rt._call_function(name, line, col, evaluator=self)
            else:
                # Unknown identifier: push FNV-1a hash (for self-dispatch)
                h = fnv1a_32(name.encode('utf-8'))
                self.rt.push_omega(h)
                if self.debug:
                    print(f"  [warn] Unknown identifier '{name}' → pushed FNV hash 0x{h:08X}",
                          file=sys.stderr)

        elif isinstance(node, LatticeReadNode):
            x = self._eval_coord(node.coords[0], line, col)
            y = self._eval_coord(node.coords[1], line, col)
            z = self._eval_coord(node.coords[2], line, col)
            v = self.rt.lattice_read(x, y, z, line, col)
            self.rt.push_omega(v)
            if self.debug:
                print(f"  [lattice] read ℒ({x},{y},{z}) → {v!r}", file=sys.stderr)

        elif isinstance(node, LatticeWriteNode):
            x = self._eval_coord(node.coords[0], line, col)
            y = self._eval_coord(node.coords[1], line, col)
            z = self._eval_coord(node.coords[2], line, col)
            v = self.rt.pop_omega(line, col)
            self.rt.lattice_write(x, y, z, v)
            if self.debug:
                print(f"  [lattice] write ℒ({x},{y},{z}) ← {v!r}", file=sys.stderr)

        elif isinstance(node, ChecksumNode):
            # Top-level checksum nodes are informational; only verified inside blocks
            pass

        elif isinstance(node, FuncDefNode):
            # Already registered; re-registration is no-op
            self.rt.functions[node.name] = node

    def exec_nodes(self, nodes: list[Node],
                   src_line: int = 0, src_col: int = 0) -> None:
        """
        Execute a list of nodes sequentially (used for function bodies).

        Special case: ⟁ consumes the NEXT IdentNode as its branch target.
        If the condition is true, the named function is called.
        If the condition is false, the identifier is skipped.
        In both cases execution then continues after the identifier.
        """
        i = 0
        while i < len(nodes):
            node = nodes[i]
            # ── ⟁ with lookahead ─────────────────────────────────────────
            if isinstance(node, OpNode) and node.op == '⟁':
                target_name: Optional[str] = None
                if (i + 1 < len(nodes) and
                        isinstance(nodes[i + 1], IdentNode)):
                    target_name = nodes[i + 1].name
                    i += 1  # consume the identifier regardless of branch
                # Evaluate condition
                if self.rt.psi:
                    cond_b = self.rt.pop_psi(node.line, node.col)
                    cond_a = self.rt.pop_omega(node.line, node.col)
                    do_branch = (self.rt._numeric(cond_a)
                                 > self.rt._numeric(cond_b))
                else:
                    cond = (self.rt.pop_omega(node.line, node.col)
                            if self.rt.omega else False)
                    do_branch = bool(cond)
                if do_branch and target_name:
                    if target_name in self.rt.functions:
                        self.rt._call_function(target_name,
                                               node.line, node.col,
                                               evaluator=self)
                    else:
                        # Unknown target: push FNV hash
                        h = fnv1a_32(target_name.encode('utf-8'))
                        self.rt.push_omega(h)
            else:
                self.exec_node(node)
            i += 1

    # ── two-pass evaluation ───────────────────────────────────────────────────

    def evaluate(self, program: ProgramNode) -> None:
        """
        Full two-pass evaluation of a parsed program.
        """
        # Register all functions first (hoisting, so line-10 can call line-40 fn)
        for fn in program.functions.values():
            self.rt.functions[fn.name] = fn

        # ── Pass 1 (forward) ──────────────────────────────────────────────────
        self.rt.pass_number = 1
        if self.debug:
            print("  [pass1] Forward pass begins", file=sys.stderr)

        rtq:                  list[Node] = []
        current_reverse_group: list[Node] = []

        # Separate nodes into groups by blank_before
        normal_seq:   list[tuple[int, Node]] = []  # (index, node)
        for idx, node in enumerate(program.top_level):
            bb = node.blank_before
            if bb >= 3:
                normal_seq.append(('parallel', node))
            elif bb == 2:
                normal_seq.append(('reverse', node))
            elif bb == 1:
                normal_seq.append(('defer', node))
            else:
                normal_seq.append(('seq', node))

        # Build groups for reverse-mode execution
        grouped: list[Any] = []
        cur_rev: list[Node] = []
        for tag, node in normal_seq:
            if tag == 'reverse':
                cur_rev.append(node)
            else:
                if cur_rev:
                    grouped.append(('rev_group', cur_rev))
                    cur_rev = []
                grouped.append((tag, node))
        if cur_rev:
            grouped.append(('rev_group', cur_rev))

        # Execute Pass 1
        rtq_nodes: list[Node] = []
        for tag, item in grouped:
            if tag == 'parallel':
                saved_entropy = self.rt.entropy
                saved_pass    = self.rt.pass_number
                if self.debug:
                    print(f"  [parallel] spawning entropy thread "
                          f"(saved ε=0x{saved_entropy:08X})", file=sys.stderr)
                self.exec_nodes([item])
                self.rt.entropy     = saved_entropy
                self.rt.pass_number = saved_pass
            elif tag == 'rev_group':
                self.exec_nodes(list(reversed(item)))
            elif tag == 'defer':
                rtq_nodes.append(item)
            else:  # 'seq'
                self.exec_nodes([item])

        # ── Pass 2 (backward / RTQ) ───────────────────────────────────────────
        self.rt.pass_number = 2
        if rtq_nodes:
            if self.debug:
                print(f"  [pass2] RTQ has {len(rtq_nodes)} items; "
                      f"executing in reverse", file=sys.stderr)
            self.exec_nodes(list(reversed(rtq_nodes)))

        if self.debug:
            print("  [eval] Evaluation complete", file=sys.stderr)
            print(f"  [state] Ω={self.rt.omega}", file=sys.stderr)
            print(f"  [state] Ψ={self.rt.psi}", file=sys.stderr)
            print(f"  [state] ε=0x{self.rt.entropy:08X}", file=sys.stderr)

# ═══════════════════════════════════════════════════════════════════════════════
# CHECKSUM PRINTER  (for --compute-checksums mode)
# ═══════════════════════════════════════════════════════════════════════════════

def print_checksums(tokens: list[Token], filename: str) -> None:
    """
    Walk token stream, find all function bodies, compute and print
    the correct ⌸0xXXXXXXXX checksum for each.
    """
    print(f"# VORTHEX checksum computation for: {filename}")
    print(f"# Insert these ⌸0x... lines before ⦾ in your source file.\n")

    i = 0
    while i < len(tokens):
        t = tokens[i]
        if t.type == TT.FUNC_DEF:
            # Next token should be the function name
            i += 1
            if i >= len(tokens):
                break
            name_tok = tokens[i]
            name = name_tok.raw
            i += 1
            # Skip optional type sig
            if i < len(tokens) and tokens[i].type == TT.TYPESIG_BEGIN:
                depth = 1
                i += 1
                while i < len(tokens) and depth > 0:
                    if tokens[i].type == TT.TYPESIG_BEGIN:
                        depth += 1
                    elif tokens[i].type == TT.TYPESIG_END:
                        depth -= 1
                    i += 1
            # Collect body tokens
            body_toks: list[Token] = []
            while i < len(tokens) and tokens[i].type not in (TT.CHECKSUM, TT.FUNC_END, TT.EOF):
                body_toks.append(tokens[i])
                i += 1
            cs = compute_block_checksum(body_toks)
            print(f"Function '{name}':  ⌸0x{cs:08X}")
            # Skip existing checksum token if present
            if i < len(tokens) and tokens[i].type == TT.CHECKSUM:
                i += 1
        else:
            i += 1

# ═══════════════════════════════════════════════════════════════════════════════
# MAIN ENTRY POINT
# ═══════════════════════════════════════════════════════════════════════════════

def main() -> int:
    ap = argparse.ArgumentParser(
        prog='vorthex',
        description='VORTHEX Reference Interpreter v' + __version__,
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  python3 vorthex.py hello.vx
  python3 vorthex.py --compute-checksums stdlib.vx
  python3 vorthex.py --debug fibonacci.vx
  python3 vorthex.py --dump-tokens hello.vx
""")
    ap.add_argument('file', nargs='?', help='VORTHEX source file (.vx)')
    ap.add_argument('--compute-checksums', action='store_true',
                    help='Print correct ⌸0x... checksums for all functions and exit')
    ap.add_argument('--debug', action='store_true',
                    help='Enable debug tracing (stack state, lattice ops, entropy)')
    ap.add_argument('--dump-tokens', action='store_true',
                    help='Dump lexer token stream and exit')
    ap.add_argument('--skip-checksums', action='store_true',
                    help='Skip checksum verification (useful for development)')
    ap.add_argument('--version', action='version', version=f'vorthex {__version__}')
    args = ap.parse_args()

    if args.file is None:
        ap.print_help()
        return 0

    try:
        with open(args.file, 'r', encoding='utf-8') as fh:
            source = fh.read()
    except FileNotFoundError:
        print(f"vorthex: error: file not found: {args.file}", file=sys.stderr)
        return 1
    except UnicodeDecodeError as e:
        print(f"vorthex: error: UTF-8 decode error in {args.file}: {e}", file=sys.stderr)
        return 1

    filename = os.path.basename(args.file)

    # ── Lex ──────────────────────────────────────────────────────────────────
    try:
        lexer  = Lexer(source, filename)
        tokens = lexer.tokenize()
    except LexerError as e:
        print(f"vorthex: {e}", file=sys.stderr)
        return 1

    if args.dump_tokens:
        for tok in tokens:
            print(f"  {tok.type.name:20s}  {tok.raw!r:30s}  "
                  f"line={tok.line:4d} col={tok.col:4d} "
                  f"indent={tok.indent:2d} blank={tok.blank_before}")
        return 0

    if args.compute_checksums:
        print_checksums(tokens, filename)
        return 0

    # ── Parse ─────────────────────────────────────────────────────────────────
    try:
        parser  = Parser(tokens, filename, skip_checksum=args.skip_checksums)
        program = parser.parse()
    except ChecksumError as e:
        print(f"vorthex: {e}", file=sys.stderr)
        print("  Hint: Run with --compute-checksums to get correct values.",
              file=sys.stderr)
        return 1
    except ParseError as e:
        print(f"vorthex: {e}", file=sys.stderr)
        return 1

    if args.debug:
        print(f"  [parse] {len(program.functions)} function(s) defined: "
              f"{list(program.functions.keys())}", file=sys.stderr)
        print(f"  [parse] {len(program.top_level)} top-level node(s)", file=sys.stderr)

    # ── Execute ───────────────────────────────────────────────────────────────
    try:
        runtime   = VorthexRuntime(debug=args.debug)
        evaluator = Evaluator(runtime, debug=args.debug)
        evaluator.evaluate(program)
    except (RuntimeError_, VorthexError) as e:
        print(f"vorthex: {e}", file=sys.stderr)
        return 1
    except RecursionError:
        print(f"vorthex: maximum recursion depth exceeded. "
              f"Consider using tail-call style with ⊜.", file=sys.stderr)
        return 1
    except KeyboardInterrupt:
        print("\nvorthex: interrupted", file=sys.stderr)
        return 130

    return 0


if __name__ == '__main__':
    sys.exit(main())
