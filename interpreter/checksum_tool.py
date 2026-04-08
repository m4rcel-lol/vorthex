#!/usr/bin/env python3
"""
VORTHEX Checksum Tool
=====================
Computes CRC-32 block checksums for VORTHEX source files.

The VORTHEX language requires every function body to end with a ⌸0xHEXHEX
checksum line whose value is the CRC-32 of the UTF-8-encoded token stream
of that body (tokens joined with single spaces, checksum line excluded).

Usage:
    python3 checksum_tool.py <file.vx>
        Print correct checksums for all function blocks.

    python3 checksum_tool.py --verify <file.vx>
        Verify that all existing checksums match.

    python3 checksum_tool.py --patch <file.vx>
        Write a new copy of the file with correct checksums inserted.

    python3 checksum_tool.py --raw <tokens...>
        Compute checksum of an ad-hoc token stream (space-separated on command line).
"""
from __future__ import annotations

import sys
import os
import re
import zlib
import argparse
from typing import Optional

# ── Import lexer from interpreter ────────────────────────────────────────────

_here = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, _here)

try:
    from vorthex import Lexer, TT, Token, compute_block_checksum, crc32
except ImportError:
    print("Error: cannot import vorthex.py. Make sure checksum_tool.py is in "
          "the same directory as vorthex.py.", file=sys.stderr)
    sys.exit(1)

# ═══════════════════════════════════════════════════════════════════════════════
# Core checksum computation
# ═══════════════════════════════════════════════════════════════════════════════

def compute_function_checksums(tokens: list[Token]) -> list[dict]:
    """
    Walk the token stream and return a list of dicts:
        {
            'name':     function name,
            'checksum': computed CRC-32 (int),
            'existing': existing checksum value or None,
            'cs_line':  line number of existing ⌸ token (or None),
            'body_tokens': [...],
        }
    """
    results = []
    i = 0
    while i < len(tokens):
        t = tokens[i]

        if t.type != TT.FUNC_DEF:
            i += 1
            continue

        # Function definition found
        i += 1
        if i >= len(tokens):
            break

        name_tok = tokens[i]
        name     = name_tok.raw
        i += 1

        # Skip optional type signature [...]
        if i < len(tokens) and tokens[i].type == TT.TYPESIG_BEGIN:
            depth = 1
            i += 1
            while i < len(tokens) and depth > 0:
                if tokens[i].type   == TT.TYPESIG_BEGIN:
                    depth += 1
                elif tokens[i].type == TT.TYPESIG_END:
                    depth -= 1
                i += 1

        # Collect body tokens (stop at CHECKSUM or FUNC_END)
        body_toks: list[Token] = []
        while i < len(tokens) and tokens[i].type not in (TT.CHECKSUM, TT.FUNC_END, TT.EOF):
            body_toks.append(tokens[i])
            i += 1

        # Check for existing checksum token
        existing_val  = None
        existing_line = None
        if i < len(tokens) and tokens[i].type == TT.CHECKSUM:
            existing_val  = tokens[i].value
            existing_line = tokens[i].line
            i += 1

        computed = compute_block_checksum(body_toks)
        results.append({
            'name':        name,
            'checksum':    computed,
            'existing':    existing_val,
            'cs_line':     existing_line,
            'body_tokens': body_toks,
        })

    return results


def patch_source(source: str, results: list[dict]) -> str:
    """
    Return a new copy of source with correct ⌸0x... checksums.
    If a checksum line already exists, replace it.
    If no checksum line exists, insert one before the ⦾ line.
    """
    lines = source.split('\n')

    # Sort results by cs_line descending so we patch from bottom to top
    # (avoids line-number shifting)
    patched_lines_set = set()

    for rec in sorted(results, key=lambda r: r['cs_line'] or 0, reverse=True):
        cs_val = rec['checksum']
        cs_str = f'⌸0x{cs_val:08X}'

        if rec['cs_line'] is not None:
            # Replace the existing ⌸ line
            lno = rec['cs_line'] - 1  # 0-based
            if 0 <= lno < len(lines):
                old_line = lines[lno]
                # Replace ⌸0x... in place, preserving indentation
                new_line = re.sub(r'⌸0x[0-9A-Fa-f]+', cs_str, old_line)
                lines[lno] = new_line
        else:
            # Find ⦾ after function and insert before it
            # Locate the ⦾ line after the function body tokens
            if rec['body_tokens']:
                last_body_line = rec['body_tokens'][-1].line
                # Search forward for ⦾
                for lno in range(last_body_line, len(lines)):
                    if '⦾' in lines[lno]:
                        indent = len(lines[lno]) - len(lines[lno].lstrip())
                        lines.insert(lno, ' ' * indent + cs_str)
                        break

    return '\n'.join(lines)


# ═══════════════════════════════════════════════════════════════════════════════
# CLI
# ═══════════════════════════════════════════════════════════════════════════════

def main() -> int:
    ap = argparse.ArgumentParser(
        prog='checksum_tool',
        description='VORTHEX CRC-32 block checksum utility',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  python3 checksum_tool.py stdlib.vx
  python3 checksum_tool.py --verify stdlib.vx
  python3 checksum_tool.py --patch stdlib.vx --out stdlib_fixed.vx
  python3 checksum_tool.py --raw '⊕ ⊖ ⊗'
""")
    ap.add_argument('file', nargs='?', help='VORTHEX source file')
    ap.add_argument('--verify', action='store_true',
                    help='Verify existing checksums (exit 1 on mismatch)')
    ap.add_argument('--patch', action='store_true',
                    help='Produce patched source with correct checksums')
    ap.add_argument('--out', metavar='FILE',
                    help='Output file for --patch (default: stdout)')
    ap.add_argument('--raw', metavar='TOKENS',
                    help='Compute checksum of raw token text (space-separated)')
    args = ap.parse_args()

    # ── --raw mode ────────────────────────────────────────────────────────────
    if args.raw:
        data = args.raw.encode('utf-8')
        cs   = crc32(data)
        print(f"CRC-32 of {args.raw!r}")
        print(f"  Hex:  0x{cs:08X}")
        print(f"  Dec:  {cs}")
        return 0

    if args.file is None:
        ap.print_help()
        return 0

    # ── Load source ───────────────────────────────────────────────────────────
    try:
        with open(args.file, 'r', encoding='utf-8') as fh:
            source = fh.read()
    except FileNotFoundError:
        print(f"checksum_tool: file not found: {args.file}", file=sys.stderr)
        return 1

    filename = os.path.basename(args.file)

    # ── Lex ───────────────────────────────────────────────────────────────────
    try:
        lexer  = Lexer(source, filename)
        tokens = lexer.tokenize()
    except Exception as e:
        print(f"checksum_tool: lex error: {e}", file=sys.stderr)
        return 1

    # ── Compute ───────────────────────────────────────────────────────────────
    results = compute_function_checksums(tokens)

    if not results:
        print(f"  No function definitions found in {filename}.")
        return 0

    # ── Default: print table ──────────────────────────────────────────────────
    if not args.verify and not args.patch:
        print(f"Checksums for {filename}:")
        print(f"  {'Function':<30} {'Computed':>12}  {'Existing':>12}  Status")
        print(f"  {'-'*30} {'-'*12}  {'-'*12}  ------")
        all_ok = True
        for rec in results:
            computed  = rec['checksum']
            existing  = rec['existing']
            if existing is None:
                status = 'MISSING'
                all_ok = False
            elif existing == computed:
                status = 'OK'
            else:
                status = 'MISMATCH'
                all_ok = False
            ex_str = f"0x{existing:08X}" if existing is not None else '(none)'
            print(f"  {rec['name']:<30} 0x{computed:08X}  {ex_str:>12}  {status}")
        print()
        if all_ok:
            print("  All checksums are correct.")
        else:
            print("  Some checksums are missing or incorrect.")
            print("  Use --patch to automatically fix them.")
        return 0 if all_ok else 1

    # ── --verify mode ─────────────────────────────────────────────────────────
    if args.verify:
        errors = 0
        for rec in results:
            computed = rec['checksum']
            existing = rec['existing']
            if existing is None:
                print(f"  MISSING checksum for function '{rec['name']}' "
                      f"(correct value: ⌸0x{computed:08X})")
                errors += 1
            elif existing != computed:
                print(f"  MISMATCH in function '{rec['name']}': "
                      f"source has 0x{existing:08X}, "
                      f"correct is 0x{computed:08X}")
                errors += 1
        if errors == 0:
            print(f"  All {len(results)} checksum(s) verified OK.")
            return 0
        else:
            print(f"  {errors} error(s) found.")
            return 1

    # ── --patch mode ──────────────────────────────────────────────────────────
    if args.patch:
        patched = patch_source(source, results)
        if args.out:
            with open(args.out, 'w', encoding='utf-8') as fh:
                fh.write(patched)
            print(f"  Wrote patched source to {args.out}")
        else:
            sys.stdout.write(patched)
        return 0

    return 0


if __name__ == '__main__':
    sys.exit(main())
