# VORTHEX Language Specification
**Version 1.0.0** · Canonical Reference

---

## Table of Contents

1. [Overview](#1-overview)
2. [Operator Table](#2-operator-table)
3. [Formal Grammar (EBNF)](#3-formal-grammar-ebnf)
4. [Whitespace Semantics](#4-whitespace-semantics)
5. [Dual-Stack Architecture](#5-dual-stack-architecture)
6. [3D Lattice Memory Model](#6-3d-lattice-memory-model)
7. [Void Cascade — Formal Specification](#7-void-cascade--formal-specification)
8. [Entropy Register State Machine](#8-entropy-register-state-machine)
9. [Reverse-Time Evaluation](#9-reverse-time-evaluation)
10. [Executable Comments](#10-executable-comments)
11. [Block Checksums](#11-block-checksums)
12. [Inverse Scoping](#12-inverse-scoping)
13. [Type System](#13-type-system)
14. [Function Syntax](#14-function-syntax)
15. [Operator Context-Shifting Rules](#15-operator-context-shifting-rules)
16. [Entropic Collapse](#16-entropic-collapse)
17. [Implementation Notes](#17-implementation-notes)

---

## 1. Overview

VORTHEX is a concatenative, stack-based, lambda-calculus hybrid programming
language designed for maximum expressive resistance. Its core properties:

| Property | Value |
|---|---|
| File extension | `.vx` |
| Paradigm | Concatenative + stack-based + lambda hybrid |
| Memory model | 3D integer-addressed lattice |
| Stack model | Dual: Ω (omega) and Ψ (psi) |
| Evaluation | Two-pass (forward + reverse-time queue) |
| Scoping | Inverse: inner writes propagate outward |
| Type system | Self-referential, runtime-only |
| Keywords | Zero. All operators are Unicode symbols. |

---

## 2. Operator Table

Every operator has a **primary meaning** (applied in Ω context)
and a **context-shifted secondary meaning** (applied in Ψ context).
The effective context is determined by: (a) column position of the
token, (b) entropy register state (for control/bitwise/dual operators),
and (c) which stack was most recently targeted.

Column rules:
- Columns 1–40: Ω target (primary meaning)
- Columns 41–80: Ψ target (secondary meaning)
- Column 81+: both stacks simultaneously

When Ψ is empty and a binary operator is invoked in Ω mode,
the operator falls back to consuming both operands from Ω
(top = b, second = a).

### 2.1 Complete Operator Table (45 symbols)

| Symbol | Category | Ω Context (Primary) | Ψ Context (Secondary) |
|--------|----------|--------------------|-----------------------|
| `⊕` | arith | Add: pop Ω, pop Ψ, push Ω+Ψ to Ω | Type union of Ω/Ψ types |
| `⊖` | arith | Subtract: push Ω−Ψ to Ω | Type difference |
| `⊗` | arith | Multiply: push Ω×Ψ to Ω | Cartesian type product |
| `⊙` | arith | Divide: push Ω÷Ψ to Ω | Quotient type |
| `⌁` | arith | Modulo: push Ω mod Ψ to Ω | Residue type |
| `⊻` | bitwise | Bitwise XOR of Ω and Ψ tops | Fork entropy register |
| `⊼` | bitwise | Bitwise NAND | Type complement |
| `⊽` | bitwise | Bitwise NOR | Complement of type intersection |
| `∿` | bitwise | Rotate-left Ω top by Ψ top bits | Cast Ω top to type on Ψ |
| `∩` | bitwise | Bitwise AND of top two Ω | Type intersection |
| `∪` | bitwise | Bitwise OR of top two Ω | Type union (alt) |
| `⥊` | stack | Swap tops of Ω and Ψ simultaneously | Same (context-invariant) |
| `⋄` | stack | Duplicate Ω top | Duplicate Ψ top |
| `◇` | stack | Discard Ω top | Discard Ψ top |
| `◈` | stack | Swap top two of Ω | Swap top two of Ψ |
| `⧓` | stack | Copy Ω[1] to Ω top (over) | Copy Ψ[1] to Ψ top |
| `⟲` | stack | Rotate Ω: a b c → b c a | Rotate Ψ: a b c → b c a |
| `⟳` | stack | Unrotate Ω: a b c → c a b | Unrotate Ψ: a b c → c a b |
| `↑` | stack | Copy Ψ top onto Ω | Copy Ω top onto Ψ |
| `↓` | stack | Pop and discard Ω top | Pop and discard Ψ top |
| `⇑` | stack | Copy Ω top → Ψ AND Ψ top → Ω | Same |
| `⇓` | stack | Discard tops of both Ω and Ψ | Same |
| `⊂` | stack | Copy Ω top → Ψ (non-destructive) | Copy Ψ top → Ω |
| `⊃` | stack | Move Ω top → Ψ (destructive) | Move Ψ top → Ω |
| `⊛` | dual | Push (Ω×Ψ) tuple to Ω | Trigger void cascade |
| `⋈` | dual | Interleave Ω and Ψ into Ω | Split Ω alternately to Ω/Ψ |
| `⋉` | dual | Left-biased merge of stacks | Left split of Ω |
| `⋊` | dual | Right-biased merge of stacks | Right split of Ω |
| `∧` | logic | Logical AND: (Ω∧Ψ) → Ω | Type intersection |
| `∨` | logic | Logical OR: (Ω∨Ψ) → Ω | Type union |
| `¬` | logic | Logical NOT of Ω top | Logical NOT of Ψ top |
| `≡` | cmp | Push (Ω==Ψ) bool to Ω | Type equivalence check |
| `≠` | cmp | Push (Ω!=Ψ) bool to Ω | Type non-equivalence |
| `≺` | cmp | Push (Ω<Ψ) bool to Ω | Subtype check |
| `≻` | cmp | Push (Ω>Ψ) bool to Ω | Supertype check |
| `≈` | cmp | Push (|Ω-Ψ|<ε) to Ω | Type compatibility |
| `⟁` | ctrl | Branch if Ω top > Ψ top | Defer to reverse-time queue |
| `⊜` | ctrl | Dispatch fn whose FNV hash is on Ω | Tail-recurse current fn |
| `⊞` | io | Pop Ω top, print to stdout | Pop Ω top, print to stderr |
| `⊟` | io | Read stdin line → push to Ω | Read stdin line → push to Ψ |
| `⊘` | lattice | Write Ω to ℒ[Ω.x][Ψ.y][ε&0xFF] | Read that cell → Ω |
| `⌊` | num | floor(Ω top) → Ω | floor(Ψ top) → Ψ |
| `⌈` | num | ceil(Ω top) → Ω | ceil(Ψ top) → Ψ |
| `∇` | num | Ω top − 1 | Ψ top − 1 |
| `Δ` | num | Ω top + 1 | Ψ top + 1 |
| `∅` | lit | Push 0 to Ω | Push 0 to Ψ |
| `∞` | lit | Push float(inf) to Ω | Push float(inf) to Ψ |
| `∫` | higher | Fold Ω stack with Ψ top as fn | Fold Ψ stack |
| `∑` | higher | Sum all of Ω, push result | Sum all of Ψ |
| `∏` | higher | Product of all Ω | Product of all Ψ |
| `∀` | higher | Map Ω top (fn) over remaining Ω | Map over Ψ |
| `∃` | higher | Check any Ω item satisfies predicate | Check Ψ |
| `⋯` | seq | Push integers [Ψ top .. Ω top] onto Ω | Push onto Ψ |

---

## 3. Formal Grammar (EBNF)

```ebnf
program         = { function-def | top-level-stmt } EOF ;

function-def    = "⦿" name [ type-sig ]
                    { function-stmt }
                  [ "⌸" hex-literal ]
                  "⦾" ;

type-sig        = "[" { type-name } "→" { type-name }
                      [ "|" { type-name } "→" { type-name } ]
                  "]" ;

type-name       = "ℕ" | "ℤ" | "𝔽" | "𝔹" | "⊤" | "⊥" ;

function-stmt   = comment | literal | operator | identifier
                | lattice-read | lattice-write | checksum ;

top-level-stmt  = function-def | function-stmt ;

literal         = integer-literal | float-literal | string-literal ;

integer-literal = [ "-" ] digit { digit }
                | "0x" hex-digit { hex-digit } ;

float-literal   = [ "-" ] digit { digit } "." digit { digit }
                  [ ("e"|"E") [ "+"|"-" ] digit { digit } ] ;

string-literal  = "«" { string-char } "»" ;
string-char     = any-unicode-except-» | "\" escape-char ;
escape-char     = "n" | "t" | "r" | "\" | "«" | "»" ;

operator        = (* any symbol from the operator table *) ;

identifier      = ident-start { ident-cont } ;
ident-start     = letter | "_" | unicode-above-127-non-reserved ;
ident-cont      = letter | digit | "_" | "'" | "`"
                | unicode-above-127-non-reserved ;

lattice-read    = "⟨" coord "," coord "," coord "⟩" ;
lattice-write   = "⟩" coord "," coord "," coord "⟨" ;
coord           = integer-literal | "Ω" | "Ψ" | "ε" | arithmetic-expr ;

comment         = "⟦" { nested-comment-content } "⟧" ;
nested-comment-content = any-char-except-⟦-⟧
                        | "⟦" { nested-comment-content } "⟧" ;

checksum        = "⌸" "0x" hex-digit { hex-digit } ;

name            = identifier | operator | type-name ;

hex-digit       = digit | "a"-"f" | "A"-"F" ;
digit           = "0"-"9" ;

(* Whitespace *)
blank-line      = line-of-only-spaces LF ;
indentation     = { SP } ;  (* no tabs *)
```

---

## 4. Whitespace Semantics

VORTHEX encodes program structure across three independent whitespace axes:

### 4.1 Indentation Axis (vertical depth)

| Leading spaces | Scope |
|---|---|
| 0 | Global lattice scope |
| 2 | Function body scope |
| 4 | Loop or branch body scope |
| 6 | Nested closure scope |
| 8 | Sub-interpreter scope (each +2 opens one sub-interpreter) |

**Tab characters are a fatal parse error.** There is no tab-to-space
conversion. The interpreter terminates immediately if a tab is detected.

### 4.2 Column Axis (horizontal position of first token)

| Column range | Target stack |
|---|---|
| 1 – 40 | Ω stack |
| 41 – 80 | Ψ stack |
| 81+ | Both stacks simultaneously |

Literals pushed at columns 41–80 go to Ψ. Operators at columns 41–80
invoke their Ψ-context (secondary) meaning. This is the primary mechanism
for targeting Ψ without explicit transfer operators.

### 4.3 Blank-Line Axis (execution timing)

| Blank lines before statement | Effect |
|---|---|
| 0 | Sequential execution (normal) |
| 1 | Deferred — added to reverse-time queue (RTQ) |
| 2 | Execute in reverse order relative to surrounding block |
| 3+ | Branch into a new parallel entropy thread |

A "blank line" is a line containing only whitespace followed by a newline.
The count is the number of consecutive blank lines immediately preceding
the non-blank line containing the statement's first token.

---

## 5. Dual-Stack Architecture

### 5.1 Properties

VORTHEX maintains two independent LIFO stacks at all times:

- **Ω (omega)**: primary stack, default target for most operations
- **Ψ (psi)**: secondary stack, used for cross-stack binary operations

Both stacks are unbounded (limited only by available memory) until they
reach `MAX_STACK_SIZE = 1024`, at which point an **entropic collapse**
occurs (see §16).

### 5.2 Cross-Stack Binary Operations

Most binary operators consume **one value from Ω and one from Ψ**:

```
Ω: [ … a ]       Ψ: [ … b ]
         ⊕
Ω: [ … a+b ]     Ψ: [ … ]
```

### 5.3 Ω Fallback

When Ψ is empty and a binary operator is invoked in Ω mode (column 1–40),
the operator consumes both operands from Ω (top = b, second = a):

```
Ω: [ … a b ]     Ψ: []
         ⊕
Ω: [ … a+b ]     Ψ: []
```

### 5.4 Silent Corruption

Pushing to the wrong stack or using a cross-stack operator when Ψ lacks the
expected value causes **silent data corruption**: the program continues with
bad data. There is no exception. There is no warning. The erroneous value
persists until deliberately overwritten.

---

## 6. 3D Lattice Memory Model

### 6.1 Structure

All storage is a three-dimensional integer-addressed grid **ℒ[x][y][z]**
where x, y, z ∈ ℤ. There are no named variables.

- **Read**: `⟨x,y,z⟩` — pushes `ℒ[x][y][z]` onto Ω stack.
- **Write**: `⟩x,y,z⟨` — pops Ω stack top and stores it at `ℒ[x][y][z]`.

Coordinate expressions may be:
- Integer literals: `⟨0,1,2⟩`
- Stack references: `⟨Ω,Ψ,0⟩` (read Ω top, Ψ top as coordinates)
- Entropy reference: `⟨0,0,ε⟩` (use entropy register as Z)
- Simple arithmetic expressions evaluated at read/write time

### 6.2 Uninitialized Cells

Reading an uninitialized cell does **not** return zero. It triggers a
**void cascade** (see §7).

### 6.3 Coordinate Indirection

Coordinates may themselves reference other lattice cells. Recursive
indirection is supported to arbitrary depth, subject to the Python
interpreter's recursion limit.

---

## 7. Void Cascade — Formal Specification

### 7.1 Trigger

A void cascade is triggered when `⟨x,y,z⟩` reads a cell that has never
been written.

### 7.2 Propagation Rules

Given a call stack `[frame₀, frame₁, …, frameₙ]` (frameₙ = innermost):

1. **Contamination**: Every lattice cell address that was read in frameₙ
   since the frame was pushed is set to `⊥` (bottom, represented as `None`
   in the reference interpreter).

2. **Continuation**: Execution does **not** halt. The value `⊥` is pushed
   onto Ω and execution continues from the instruction following the
   offending read.

3. **Propagation**: The cascade is noted in the interpreter's diagnostic
   output but does not propagate to enclosing frames automatically.
   However, any cell set to `⊥` in step 1 may trigger further cascades
   if those addresses are subsequently read by outer frames.

### 7.3 Formal Definition

```
void_cascade(addr):
  let frame = call_stack.top()
  for each addr' in frame.reads_since_push:
    lattice[addr'] := ⊥
  lattice[addr] := ⊥
  Ω.push(⊥)
  continue_execution()
```

### 7.4 Deliberate Cascade

The `⊛` operator in Ψ context deliberately triggers void cascade semantics
as an explicit language-level primitive.

---

## 8. Entropy Register State Machine

The entropy register **ε** is a 32-bit unsigned integer.

### 8.1 Initial Value

```
ε₀ = 0x811c9dc5    (FNV-1a offset basis)
```

### 8.2 State Transitions

```
  ┌─────────────────────────────────────────────────────────┐
  │                  Entropy Register ε                      │
  │                                                         │
  │  ε₀ = 0x811c9dc5                                       │
  │        │                                                 │
  │        ▼                                                 │
  │  ┌───────────────┐   comment ⟦…⟧    ┌─────────────┐    │
  │  │  INITIAL      │─────────────────▶│  UPDATED    │    │
  │  │  (any state)  │                  │  ε' = ε⊕H  │    │
  │  └───────────────┘                  └──────┬──────┘    │
  │                                            │            │
  │        ┌───────────────────────────────────┘            │
  │        ▼                                                 │
  │  ┌───────────────┐   ⊻ operator      ┌─────────────┐    │
  │  │  ACTIVE       │─────────────────▶│  XOR FORK   │    │
  │  │  (affects ops)│                  │  ε' = ε⊕Ψ  │    │
  │  └───────────────┘                  └─────────────┘    │
  │                                                         │
  │  H = FNV-1a(comment_content)                           │
  │  FNV-1a(data):                                          │
  │    h = 0x811c9dc5                                       │
  │    for each byte b in data:                             │
  │      h = (h XOR b) * 0x01000193 mod 2³²               │
  │    return h                                             │
  │                                                         │
  │  Usages of ε:                                           │
  │    1. Lattice Z-coordinate: ⊘ uses (ε & 0xFF) as Z    │
  │    2. Operator context flip: for ctrl/dual/bitwise ops │
  │       bit 16 of ε flips Ω↔Ψ context when set          │
  │    3. Branch direction modifier for ⟁                  │
  └─────────────────────────────────────────────────────────┘
```

### 8.3 Entropy-Sensitive Operator Categories

Only the following categories are affected by entropy's context-flipping
(bit 16):

| Category | Examples |
|---|---|
| `ctrl` | `⟁` `⊜` |
| `dual` | `⊛` `⋈` `⋉` `⋊` |
| `bitwise` | `⊻` `⊼` `⊽` `∿` |
| `higher` | `∫` `∀` `∃` |

Arithmetic, comparison, I/O, and stack operators are **not** entropy-shifted.

---

## 9. Reverse-Time Evaluation

### 9.1 Two-Pass Model

The interpreter performs two full passes over every source file:

**Pass 1 (Forward)**:
- Executes non-deferred statements sequentially in source order.
- Collects deferred statements (blank_before == 1) into the
  **Reverse-Time Queue (RTQ)**.
- Executes reversed-order groups (blank_before == 2) in reverse.
- Executes parallel-entropy statements (blank_before ≥ 3) with
  entropy save/restore.

**Pass 2 (Backward)**:
- Executes all RTQ entries in **reverse order** (last-deferred first).

### 9.2 RTQ Semantics

```
source:
  A           ← blank_before = 0 → execute immediately in Pass 1
              ← (1 blank line)
  B           ← blank_before = 1 → add to RTQ

  C           ← blank_before = 0 → execute immediately in Pass 1
              ← (1 blank line)
  D           ← blank_before = 1 → add to RTQ

execution order: A, C, D, B
```

### 9.3 Forward Reference Resolution

A function may be **called on line 10** and **defined on line 40**. This
is valid and intended. The interpreter hoists all function definitions
before executing any top-level code.

```vorthex
my_function          ⟦ line 10: call before definition ⟧
⦿ my_function [ → | → ]
  «called!» ⊞
⌸0x...
⦾
```

### 9.4 Programmer Mental Model

To reason about a VORTHEX program:
1. Identify all lines with exactly 1 preceding blank line → these are RTQ.
2. Mentally execute Pass 1 in source order (skipping RTQ entries).
3. Mentally execute Pass 2 in reverse RTQ order.
4. Combine the resulting state.

There is no tooling that shows pass-order execution. This is intentional.

---

## 10. Executable Comments

### 10.1 Syntax

```vorthex
⟦ This is a comment ⟧
⟦ Comments may ⟦ nest ⟧ arbitrarily deeply ⟧
⟦⟧   ⟦ empty comment — still updates entropy ⟧
```

### 10.2 Entropy Update

Every comment updates the entropy register:

```
ε' = ε XOR FNV-1a-32(UTF-8(comment_content))
```

Where `comment_content` is the raw text between the `⟦` and `⟧` delimiters
(not including the delimiters themselves; nested `⟦⟧` pairs are included
in the content of the outer comment).

### 10.3 Behavioral Consequences

Since ε affects operator context-shifting and lattice Z-coordinate
resolution:

- **Removing a comment** changes ε, potentially changing program behavior.
- **Editing a comment** changes ε, potentially changing program behavior.
- **Reordering comments** changes ε, potentially changing program behavior.
- An `⟦⟧` empty comment XORs `FNV-1a("")` = `0x811c9dc5` into ε.

Comments are **not documentation**. They are executable code.

### 10.4 Diagnostic Use

Programmers may use deliberately crafted comment content to achieve a
specific entropy state for a subsequent operator. This is a valid and
documented technique.

---

## 11. Block Checksums

### 11.1 Purpose

Every function body MUST end with a checksum line. This is a deliberate
friction point ensuring that any modification to a function body is
immediately detectable.

### 11.2 Syntax

```vorthex
⦿ my_function [ → | → ]
  ⊕ ⊖ ⊗
⌸0xDEADBEEF
⦾
```

The `⌸` prefix is followed by `0x` and exactly 8 hex digits (case-insensitive).

### 11.3 Computation Algorithm

```pseudocode
function compute_block_checksum(body_tokens):
    # body_tokens: all Token objects in the function body
    # excluding the ⌸ checksum token itself

    token_stream = JOIN(token.raw for token in body_tokens
                        WHERE token.type != CHECKSUM
                        AND   token.type != EOF)
                   WITH separator = " "

    return CRC-32(UTF-8-encode(token_stream))
```

Where `token.raw` is the exact source text of the token as it appears in
the file (preserving escape processing for strings: the raw includes the
processed content, e.g. `«Hello\n»` stores an actual newline in raw).

### 11.4 Verification

The interpreter verifies each block checksum **at parse time** (before
any execution). A checksum mismatch is a **fatal parse error**:

```
vorthex: filename.vx:10:1: Parse Error: Checksum mismatch in function 'foo':
    expected 0xDEADBEEF, computed 0xCAFEBABE.
    Use --compute-checksums to get the correct value.
```

### 11.5 Nested Blocks

When functions are defined inside functions (through closures at deeper
indentation), the outer block's token stream includes the inner block's
checksum line as a token. Therefore:

1. Compute and verify inner checksum first.
2. The inner checksum token's raw text (`⌸0xXXXXXXXX`) is included in the
   outer token stream.
3. Compute and verify outer checksum second.

Changing any inner block invalidates all outer block checksums.

### 11.6 Tooling

The `--compute-checksums` flag and `checksum_tool.py` utility compute
correct checksums for all functions in a source file. This is a pragmatic
concession to usability; the specification otherwise prohibits automatic
checksum derivation as a design friction point.

---

## 12. Inverse Scoping

### 12.1 Definition

VORTHEX uses **inverse scoping** for lattice writes:

> Any write to a lattice cell inside an inner scope also writes the same
> value to the same coordinates in **all enclosing outer scopes**.

### 12.2 Implementation

Since all scopes share the same lattice dictionary, writes are inherently
global. There is no mechanism to make a write local to a scope.

```vorthex
⦿ outer [ → | → ]
  ⟩0,0,0⟨           ⟦ writes to ℒ[0][0][0] ⟧
  inner
  ⟨0,0,0⟩           ⟦ reads the value written by inner ⟧
⌸...
⦾

⦿ inner [ → | → ]
  42
  ⟩0,0,0⟨           ⟦ writes 42 to ℒ[0][0][0] — visible in outer! ⟧
⌸...
⦾
```

### 12.3 Consequences

- Every function call is a potential global state mutation.
- Purity is impossible in VORTHEX.
- Side effects are the default and unavoidable.
- Reasoning about program state requires tracking all reachable lattice
  addresses across the entire call graph.

---

## 13. Type System

### 13.1 Primitive Types

| Symbol | Name | Description |
|---|---|---|
| `ℕ` | Natural | Non-negative integer (0, 1, 2, …) |
| `ℤ` | Integer | Any integer (…, -1, 0, 1, …) |
| `𝔽` | Float | IEEE 754 double-precision floating point |
| `𝔹` | Boolean | True (`⊤`) or false (`⊥`) |
| `⊤` | Top/Any | Any value; universal type |
| `⊥` | Bottom | Void/undefined; result of void cascade |

### 13.2 Compound Types

All compound types are **VORTHEX programs** that:
1. Accept a value on the Ω stack.
2. Leave a `𝔹` on the Ω stack (true = value belongs to type).

Type checking is performed by running a sandboxed sub-interpreter.

### 13.3 Type Checking Semantics

A type check may:
- Return `⊤` (true) — the value belongs to the type.
- Return `⊥` (false) — the value does not belong to the type.
- Trigger a void cascade — this is a **type error** at runtime.
- Fail its own checksum — this is a **type error** at runtime.
- Diverge (infinite loop) — the type check is killed after a timeout.

There is no static type checking. All type errors occur at runtime.

### 13.4 Type Signatures

Function type signatures are advisory (not enforced by the runtime):

```
[ ω_in_types → ω_out_types | ψ_in_types → ψ_out_types ]
```

Example: `[ ℤ ℤ → ℤ | → ]` means: consumes two integers from Ω,
produces one integer on Ω; Ψ is unchanged.

---

## 14. Function Syntax

### 14.1 Definition

```vorthex
⦿ FunctionName [ TypeSignature ]
  body-statement-1
  body-statement-2
  ...
⌸0xCHECKSUM
⦾
```

- `⦿` opens the definition.
- `FunctionName` may be any identifier, operator symbol, or type name.
- `[ TypeSignature ]` is optional.
- The body is one or more statements at indentation ≥ 2 spaces.
- `⌸0xCHECKSUM` is the CRC-32 checksum of the body token stream.
- `⦾` closes the definition.

### 14.2 Calling

Functions are called by writing their name at the call site:

```vorthex
5 my_function    ⟦ push 5 to Ω, then call my_function ⟧
```

### 14.3 Recursion

Direct recursion: write the function name in its own body.

```vorthex
⦿ fact [ ℕ → ℕ | → ]
  ⋄ 0 ≻ ⟁ fact_recurse
⌸0xD01445A9
⦾
```

Self-dispatch via FNV hash:

```vorthex
⦿ self_demo [ → | → ]
  ⟦ Push FNV-1a hash of "self_demo" to Ω ⟧
  2309492736    ⟦ = fnv1a_32(b"self_demo") ⟧
  ⊜             ⟦ dispatch to function with this hash ⟧
⌸0x...
⦾
```

### 14.4 Forward References

Functions may be called before they are defined in the source file.
All function definitions are hoisted to program start before any
top-level code executes.

---

## 15. Operator Context-Shifting Rules

The full context determination algorithm:

```pseudocode
function get_op_context(operator, column, entropy):
    category = operator.category

    if column >= 81:
        return BOTH

    if column >= 41:
        base = PSI
    else:
        base = OMEGA

    if category in {CTRL, DUAL, BITWISE, HIGHER}:
        entropy_bit = (entropy >> 16) & 1
        if entropy_bit == 1:
            base = flip(base)   ⟦ OMEGA↔PSI ⟧

    return base

function flip(mode):
    if mode == OMEGA: return PSI
    else: return OMEGA
```

The context determines:
1. Which action is dispatched (primary for Ω, secondary for Ψ).
2. Which stack serves as the source for binary operators.
3. Which stack receives the result of unary operators.

---

## 16. Entropic Collapse

### 16.1 Trigger

When either stack exceeds `MAX_STACK_SIZE = 1024` items.

### 16.2 Procedure

```pseudocode
entropic_collapse():
    print "ENTROPIC COLLAPSE: merging Ω and Ψ via XOR"
    merged = []
    N = max(len(Ω), len(Ψ))
    for i in 0..N-1:
        a = Ω[i] if i < len(Ω) else 0
        b = Ψ[i] if i < len(Ψ) else 0
        merged.append(int(a) XOR int(b))
    Ω = merged
    Ψ = []
    degraded = true
    ⟦ execution continues ⟧
```

### 16.3 Degraded Mode

In degraded mode:
- Only Ω exists (Ψ is permanently empty).
- Ψ-targeting operators attempt Ψ operations on an empty stack.
- This may trigger further runtime errors.
- There is no way to exit degraded mode programmatically.

---

## 17. Implementation Notes

### 17.1 Reference Interpreter

The reference interpreter is `interpreter/vorthex.py` (Python 3.11+).

Invocation:
```
python3 interpreter/vorthex.py <file.vx>
python3 interpreter/vorthex.py --compute-checksums <file.vx>
python3 interpreter/vorthex.py --debug <file.vx>
python3 interpreter/vorthex.py --dump-tokens <file.vx>
python3 interpreter/vorthex.py --skip-checksums <file.vx>
```

### 17.2 String Encoding

All source files MUST be UTF-8 encoded without BOM. The reference
interpreter will fail on non-UTF-8 input with a specific error message.

### 17.3 Integer Overflow

The reference interpreter uses Python's arbitrary-precision integers.
Bitwise operators mask results to 32 bits (`& 0xFFFFFFFF`) to simulate
32-bit overflow behavior. Arithmetic operators do not overflow.

### 17.4 Float Behavior

Floats follow IEEE 754 double precision. `∞` pushes Python's `float('inf')`.
Division by zero raises a runtime error (not IEEE 754 NaN/infinity).

### 17.5 Stack Display in Errors

Runtime error messages always include the full interpreter state:
```
Runtime Error (line L, col C): <message>
  Runtime state at error:
    Pass: 1 or 2
    Entropy register (ε): 0xXXXXXXXX
    Ω stack (top→bottom): [last 8 items]
    Ψ stack (top→bottom): [last 8 items]
    Degraded mode: True/False
```

---

*End of VORTHEX Language Specification v1.0.0*
