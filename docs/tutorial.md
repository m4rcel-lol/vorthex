# VORTHEX Tutorial
**Welcome. This language was not designed to be easy.**

---

## Table of Contents

1. [What Is VORTHEX?](#1-what-is-vorthex)
2. [Hello, World! — Annotated Line by Line](#2-hello-world--annotated-line-by-line)
3. [The Two Interpreter Passes — Worked Example](#3-the-two-interpreter-passes--worked-example)
4. [Why Comments Cannot Be Removed](#4-why-comments-cannot-be-removed)
5. [The 10 Most Frequent Errors](#5-the-10-most-frequent-errors)

---

## 1. What Is VORTHEX?

VORTHEX is a **concatenative, stack-based programming language** in the
tradition of Forth and Factor, with two additional layers of complexity
designed to maximize cognitive resistance:

1. **Dual stacks**: Ω (omega) and Ψ (psi) run concurrently.
2. **Reverse-time evaluation**: deferred statements execute in reverse.
3. **Executable comments**: comments hash into the entropy register, which
   changes operator behavior.
4. **3D lattice memory**: no variables, only a 3D grid of cells.
5. **Block checksums**: every function body must have a verified CRC-32.
6. **Inverse scoping**: all writes propagate outward to every enclosing scope.

There are **zero English keywords**. All operations are Unicode symbols.

---

## 2. Hello, World! — Annotated Line by Line

The simplest complete VORTHEX program:

```vorthex
⦿ hello [ → | → ]
  «Hello, World!\n» ⊞
⌸0x9B6900C4
⦾

hello
```

### Axis 1: Indentation (what scope is this?)

```
⦿ hello [ → | → ]     ← 0 spaces: global scope definition
  «Hello, World!\n» ⊞ ← 2 spaces: function body scope
⌸0x9B6900C4            ← 0 spaces: checksum (special syntax, not a stmt)
⦾                      ← 0 spaces: function end

hello                  ← 0 spaces: global scope call
```

The indentation depth tells the interpreter which scope level this code
operates in. 2 spaces = function body. If you use 4 spaces inside a
function body, you're opening a loop/branch scope. There are no braces.
Indentation **is** structure.

**Tabs are a fatal parse error.** Always use spaces.

### Axis 2: Column Position (which stack?)

```
  «Hello, World!\n» ⊞
  ^                  ^
  col 3              col 21
  (1-40 = Ω mode)    (1-40 = Ω mode)
```

`«Hello, World!\n»` at column 3 → pushes the string to **Ω** (omega stack).
`⊞` at column 21 → in Ω mode → pops from Ω and prints to stdout.

If `⊞` were at column 50 (Ψ mode), it would print to **stderr** instead.
The behavior of an operator depends on where it appears on the line.

### Axis 3: Blank Lines (when does it execute?)

```
⦿ hello [ → | → ]    ← no blank line before → sequential
  «Hello, World!\n» ⊞ ← no blank line before → sequential

hello                  ← no blank line before → sequential
```

No blank lines → everything runs in order, Pass 1 only, no RTQ. Clean.

If there were one blank line before `hello`:

```
⦿ hello [ → | → ]
  «Hello, World!\n» ⊞
⌸0x9B6900C4
⦾

hello   ← ONE blank line before → deferred to Pass 2 (RTQ)
```

Then `hello` would execute in Pass 2, AFTER everything else in the file.

### The Checksum

```
⌸0x9B6900C4
```

This is the CRC-32 of the token stream `«Hello, World!\n» ⊞`
(where the string raw value contains an actual newline character).

**If you change the function body, the checksum must change too.**
The interpreter verifies this at parse time. A mismatch is a fatal error.

To compute the correct checksum:
```
python3 interpreter/checksum_tool.py your_file.vx
```

### The Operators

| Token | What it is | What it does |
|---|---|---|
| `⦿` | `U+29BF` Function-open | Begins a function definition |
| `⦾` | `U+29BE` Function-close | Ends a function definition |
| `«…»` | String literal | Pushes a string value |
| `⊞` | `U+229E` Squared Plus | Ω mode: print Ω top to stdout |
| `⌸` | `U+2338` APL Quad Divide | Checksum marker |

### The Type Signature

```
[ → | → ]
```

Format: `[ Ω-inputs → Ω-outputs | Ψ-inputs → Ψ-outputs ]`

`→` separates inputs from outputs. `|` separates Ω and Ψ effects.

`[ → | → ]` means: **consumes nothing, produces nothing**. Side effects
only (printing).

---

## 3. The Two Interpreter Passes — Worked Example

Consider this file:

```vorthex
⟦ Example: reverse-time execution ⟧

⦿ print_n [ ℤ → | → ]
  ⊞ «\n» ⊞
⌸0x...
⦾

1 print_n
          ← 1 blank line →
2 print_n
3 print_n
          ← 1 blank line →
4 print_n
```

### Pass 1 (Forward)

The interpreter scans forward. When it finds a line preceded by exactly
1 blank line, it adds that statement to the **RTQ** (Reverse-Time Queue)
instead of executing it immediately.

```
Statement    blank_before    Action
---------    ------------    ------
1 print_n         0          Execute immediately → prints 1
2 print_n         1          → ADD TO RTQ [item 0]
3 print_n         0          Execute immediately → prints 3
4 print_n         1          → ADD TO RTQ [item 1]
```

After Pass 1 output: `1\n3\n`
RTQ state: `[2 print_n, 4 print_n]`

### Pass 2 (Backward)

The RTQ is executed in **reverse order**:

```
RTQ reversed: [4 print_n, 2 print_n]
Execute 4 print_n → prints 4
Execute 2 print_n → prints 2
```

### Final Output

```
1
3
4
2
```

Notice: `2` and `4` are printed, but in reverse order relative to their
source positions. **The programmer must mentally simulate both passes.**

### Forward Reference Example

```vorthex
⟦ forward_ref.vx ⟧

greet                    ← called on line 5, not yet defined

⦿ greet [ → | → ]       ← defined on line 7
  «Hello from greet!\n» ⊞
⌸0x...
⦾
```

This is **not an error**. All function definitions are hoisted before any
top-level code runs. `greet` on line 5 calls the function defined on line 7.

---

## 4. Why Comments Cannot Be Removed

Every comment `⟦…⟧` updates the **entropy register** ε:

```
ε' = ε XOR FNV-1a-32(comment_content)
```

The entropy register affects:
1. **Operator context-shifting**: for control and bitwise operators,
   bit 16 of ε can flip Ω↔Ψ mode.
2. **Lattice Z-coordinate**: the `⊘` operator uses `ε & 0xFF` as
   the Z dimension.
3. **Branch direction**: ε modifies `⟁` behavior.

### Concrete Example

```vorthex
⟦ This comment sets ε = fnv1a("This comment sets...") ⟧
⟁ my_function    ← ε bit 16 may or may not flip the branch direction
```

If you **delete the comment**, ε changes. The `⟁` branch may now go the
other direction. Your program produces different output.

If you **edit the comment text**, ε changes. Same consequence.

### The Empty Comment

```vorthex
⟦⟧    ← empty comment
```

This XORs `FNV-1a("")` = `0x811c9dc5` into ε. It is NOT a no-op.
It is a deliberate ε mutation with a specific 32-bit value.

### Safe Comment Strategies

1. **Never remove comments.** You can only add new ones or rewrite the
   program from scratch.
2. **Use the debug flag** to inspect ε before sensitive operators:
   ```
   python3 interpreter/vorthex.py --debug file.vx
   ```
3. **Comments that merely describe** are dangerous because they are also
   code. Annotate carefully.

---

## 5. The 10 Most Frequent Errors

### Error 1: Tab Characters

**Symptom:**
```
vorthex: Parse Error (file.vx:5:1): Tab character found in indentation.
  VORTHEX uses spaces only. Tabs are a fatal parse error.
  Found at: line 5, column 1
  Hint: convert all tabs to spaces (e.g. expand -t 2 file.vx)
```

**Cause:** You used a tab to indent.

**Fix:** Replace all tabs with spaces. VORTHEX requires exactly 0, 2, 4, 6,
or 8 spaces (multiples of 2). Use `expand -t 2 file.vx` on the command line.

---

### Error 2: Wrong Checksum

**Symptom:**
```
vorthex: Parse Error (file.vx:12:1): Checksum mismatch in function 'add_values':
  expected 0x89ABCDEF, computed 0x12345678.
  The function body has changed but the checksum was not updated.
  Use: python3 checksum_tool.py file.vx   to see correct values.
```

**Cause:** You modified the function body without updating `⌸0x...`.

**Fix:**
```
python3 interpreter/checksum_tool.py file.vx
```
Find your function in the output and copy the "Computed" value. Replace the
hex digits after `⌸0x` in your source.

**Important:** Changing ANY token in the body changes the checksum.
Even adding or removing a comment inside the function body will
change the checksum.

---

### Error 3: Ψ Stack Underflow

**Symptom:**
```
vorthex: Runtime Error (line 8, col 15): Ψ stack underflow
  Runtime state at error:
    Pass: 1
    Entropy register (ε): 0x6F9A9F2D
    Ω stack (top→bottom): [42]
    Ψ stack (top→bottom): []
    Degraded mode: False
```

**Cause:** A binary operator tried to consume a value from Ψ, but Ψ is empty.
Common causes:
- Using `⊕` when both values are on Ω (use Ω fallback or move one to Ψ first).
- Calling a function that expects a value on Ψ before putting one there.
- A token appearing at column > 40 causing Ψ-mode to be selected.

**Fix:**
Check which column your operator is at. If it's >= 41, it's in Ψ mode.
Move it to column 1-40, or explicitly move a value to Ψ first with `⊃`:
```
42 ⊃    ⟦ move 42 from Ω to Ψ ⟧
7 ⊕     ⟦ now: Ω=7, Ψ=42 → result=49 on Ω ⟧
```

When Ψ is empty, binary arithmetic and comparison operators fall back to
consuming both operands from Ω (Ω fallback mode).

---

### Error 4: Missing Checksum / Wrong Format

**Symptom:**
```
vorthex: Parse Error (file.vx:20:1): Expected checksum ⌸0x... before ⦾
  Function 'my_func' body ends without a checksum line.
```

**Cause:** You forgot the `⌸0xXXXXXXXX` line before `⦾`.

**Fix:** Every function MUST have exactly one checksum line immediately before
`⦾`. Use `checksum_tool.py` to compute it, then add it:
```vorthex
⦿ my_func [ → | → ]
  «Hello» ⊞
⌸0xABCD1234    ← add this line (use correct value from checksum_tool)
⦾
```

---

### Error 5: Void Cascade From Uninitialized Lattice Cell

**Symptom:**
```
vorthex: WARNING: Void cascade triggered at ℒ[0][0][0] (line 15, col 5)
  Every lattice cell read in the current frame has been set to ⊥.
  Ω stack now contains ⊥ (bottom). Execution continues with corrupted state.
```

**Cause:** You read a lattice cell before writing to it.
Uninitialized cells in VORTHEX do NOT return zero. Reading them triggers
a void cascade.

**Fix:** Always write to a lattice cell before reading it:
```vorthex
0 ⟩0,0,0⟨    ⟦ initialize ℒ[0][0][0] to 0 ⟧
⟨0,0,0⟩      ⟦ safe to read now ⟧
```

Or check if the program flow can reach the read before any write.
Remember: the void cascade does NOT crash the program; it silently corrupts
your state and execution continues.

---

### Error 6: Entropic Collapse (Stack Overflow)

**Symptom:**
```
ENTROPIC COLLAPSE: Ω stack size 1024 exceeded.
  Merging Ω and Ψ via XOR into a single flat array.
  Execution continues in DEGRADED MODE (single stack).
  Warning: All subsequent operations target only the merged Ω stack.
```

**Cause:** Unbounded recursion or an accidental infinite loop that keeps
pushing to Ω.

**Fix:** Check your recursive functions for a missing base case. Ensure
`⟁` branch conditions actually terminate the recursion:
```vorthex
⦿ count_bad [ ℕ → | → ]
  ⟦ BUG: no base case, ⊃ keeps moving to Ψ, n stays on Ω ⟧
  ⋄ print_int
  ∇ count_bad     ⟦ recurses forever ⟧
⌸...
⦾

⦿ count_good [ ℕ → | → ]
  ⋄ 0 ≻ ⟁ count_recurse    ⟦ base case: n <= 0 just returns ⟧
⌸...
⦾
```

---

### Error 7: Forward Reference to Undefined Function

**Symptom:**
```
vorthex: WARNING (line 5): Unknown identifier 'my_typo'. Pushing FNV hash.
  If this was intended to be a function call, check the function name.
```

**Cause:** You misspelled a function name. VORTHEX does NOT crash on unknown
identifiers — it pushes their FNV-1a hash as an integer to Ω. This is
deliberate (for self-dispatch). But it almost always means a typo.

**Fix:** Check spelling. Function names are case-sensitive.
Use `--debug` to see what's on the stack:
```
python3 interpreter/vorthex.py --debug file.vx
```

---

### Error 8: Unexpected Program Behavior Due to Comment Changes

**Symptom:** Program output changes after you add, remove, or edit a comment.

**Cause:** The entropy register ε is updated by every comment. If any
entropy-sensitive operator (`⟁`, `⊛`, `⋈`, `⊻`, `∿`) is used in your
program, its behavior depends on ε.

**Fix:**
1. Use `--debug` to print ε before each operator.
2. Design your program to NOT rely on ε for critical branching.
3. Or: explicitly set ε to a known value at the start of a function
   using `⊻`:
   ```vorthex
   0x00000000 ⊻    ⟦ XOR 0 into ε — minimal effect ⟧
   ```
4. Accept that comments are code. Treat them accordingly.

---

### Error 9: Wrong Execution Order (RTQ Confusion)

**Symptom:** Statements execute in a different order than their source order.
Usually: a value is used before it's defined, or a function is called
after you expected it to have already run.

**Cause:** A statement was preceded by exactly 1 blank line → it was
deferred to the RTQ and runs in Pass 2 in reverse order.

**Fix:** Count blank lines before each statement:
```vorthex
A         ← 0 blanks: runs in Pass 1 (first)

B         ← 1 blank: deferred to RTQ
C         ← 0 blanks: runs in Pass 1 (after A)

D         ← 1 blank: deferred to RTQ
```

Pass 1 order: A, C
Pass 2 order (RTQ reversed): D, B

Final execution: A → C → D → B

If you want A → B → C → D, use NO blank lines between any of them.

---

### Error 10: Inverse Scope Mutation (Unexpected Global Write)

**Symptom:** A lattice cell you thought was "local" has been overwritten
by a called function.

**Cause:** VORTHEX has **inverse scoping**: any write inside a called
function also writes to the same coordinates in ALL enclosing scopes.
There is no local storage.

**Fix:** Use different lattice coordinates for different purposes.
Establish a convention: e.g., `ℒ[0..9][0..9][0..9]` is reserved for
the top-level program; `ℒ[100+fn_id][…][…]` for function-local state.
Document your coordinate allocation in comments.

There is no `local` qualifier. There is no escape hatch. Every function
call is a potential global mutation. Design defensively.

---

*End of VORTHEX Tutorial*

---

## Quick Reference Card

| Want to... | Use... |
|---|---|
| Define a function | `⦿ name [ sig ] body ⌸0xHEX ⦾` |
| Push integer to Ω | Write the number at column 1-40 |
| Push integer to Ψ | Write the number at column 41-80 |
| Print to stdout | `⊞` at column 1-40 |
| Print to stderr | `⊞` at column 41-80 |
| Duplicate Ω top | `⋄` |
| Drop Ω top | `◇` |
| Swap top two Ω | `◈` |
| Copy Ω top to Ψ | `⊂` |
| Move Ω top to Ψ | `⊃` |
| Branch if n > 1 | `⋄ 1 ≻ ⟁ function_name` |
| Negate n | `0 ◈ ⊖` |
| Compute checksum | `python3 interpreter/checksum_tool.py file.vx` |
| Debug execution | `python3 interpreter/vorthex.py --debug file.vx` |
| Defer to RTQ | Put exactly 1 blank line before the statement |
