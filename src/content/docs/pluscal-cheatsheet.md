---
title: 'PlusCal Language Cheat Sheet'
description: 'Complete reference guide for PlusCal C-Syntax v1.8'
version: '1.8'
---

# PlusCal Language Cheat Sheet

**Version 1.8 (C-Syntax) Reference Guide**

> PlusCal is an algorithm language for writing and model-checking concurrent and
> distributed algorithms. It translates to TLA+ for verification with the TLC
> model checker.

---

## Quick Reference Card

| Construct               | Syntax                                    | Purpose                                                 |
| ----------------------- | ----------------------------------------- | ------------------------------------------------------- |
| **Algorithm**           | `--algorithm Name { ... }`                | Define algorithm                                        |
| **Fair Algorithm**      | `--fair algorithm Name { ... }`           | Conjoins WF of entire `Next` action (same as `-wfNext`) |
| **Variable**            | `variable x = 5;` or `variable x ∈ 1..N;` | Declare variable                                        |
| **Process Set**         | `process (Name ∈ Set) { ... }`            | Multiple processes                                      |
| **Single Process**      | `process (Name = id) { ... }`             | Single process                                          |
| **Label**               | `Lab: statement`                          | Mark atomic step boundary                               |
| **Assignment**          | `x := expr;`                              | Simple assignment                                       |
| **Multiple Assignment** | `x := 1 \|\| y := 2;`                     | Simultaneous assignments                                |
| **If**                  | `if (cond) { ... } else { ... }`          | Conditional                                             |
| **While**               | `while (cond) { ... }`                    | Loop (must be labeled)                                  |
| **Either**              | `either { ... } or { ... }`               | Nondeterministic choice                                 |
| **With**                | `with (x ∈ S) { ... }`                    | Bind variable                                           |
| **Await**               | `await expr;` or `when expr;`             | Wait for condition                                      |
| **Call**                | `call Proc(args);`                        | Call procedure                                          |
| **Return**              | `return;`                                 | Return from procedure                                   |
| **Goto**                | `goto Lab;`                               | Jump to label                                           |
| **Print**               | `print expr;`                             | Debug output                                            |
| **Assert**              | `assert expr;`                            | Check invariant                                         |

---

## Table of Contents

1. [Getting Started](#getting-started)
2. [Program Structure](#program-structure)
3. [Variables & Declarations](#variables--declarations)
4. [Statements](#statements)
5. [Control Flow](#control-flow)
6. [Processes & Concurrency](#processes--concurrency)
7. [Procedures](#procedures)
8. [Macros](#macros)
9. [Labels & Atomicity](#labels--atomicity)
10. [TLA+ Expressions](#tla-expressions)
11. [Temporal Properties](#temporal-properties)
12. [Fairness](#fairness)
13. [Translator Options](#translator-options)
14. [Translation to TLA+](#translation-to-tla)
15. [Algorithm Refinement](#algorithm-refinement)
16. [Common Patterns](#common-patterns)
17. [Troubleshooting](#troubleshooting)
18. [Best Practices](#best-practices)

---

## Getting Started

### Minimal Example

```tla
--algorithm HelloWorld {
    variables x = 0;
    {
        x := x + 1;
        print x;
    }
}
```

### Complete Module Template

```tla
---- MODULE Example ----
EXTENDS Naturals, TLC

CONSTANT N

(* --algorithm Example {
    variables x = 0;
    {
        a: x := x + 1;
        print x
    }
} *)

\* BEGIN TRANSLATION
\* END TRANSLATION
====
```

### Workflow

1. **Write** PlusCal algorithm in TLA+ module (in comment)
2. **Translate** with Ctrl+T (inserts TLA+ between BEGIN/END TRANSLATION)
3. **Create Model** and specify constants
4. **Run TLC** to check properties

### Translation Location

Algorithm must be in same file as TLA+ module, either:

1. **Inside module** (in comment) - RECOMMENDED
2. Before module declaration - not recommended
3. After module end - not recommended

BEGIN/END TRANSLATION comments can be placed manually if needed.

---

## Program Structure

### Algorithm Declaration

| Example                          | Explanation                                                                           |
| -------------------------------- | ------------------------------------------------------------------------------------- |
| `--algorithm Name { ... }`       | Basic algorithm                                                                       |
| `--fair algorithm Name { ... }`  | Conjoins WF of entire `Next` action (same as `-wfNext`; stronger than `fair process`) |
| `PlusCal options (-termination)` | Set translator options                                                                |

### Module Structure

```tla
---- MODULE ModuleName ----
EXTENDS Naturals, Sequences, TLC    \* Import modules
CONSTANT N                          \* Declare constants

(* --algorithm Name {
    \* Algorithm here
} *)

\* BEGIN TRANSLATION
\* TLA+ translation appears here
\* END TRANSLATION

\* Definitions after translation
Invariant == ...                     \* Properties to check
====
```

---

## Variables & Declarations

### Global Variables

| Example                       | Explanation                             |
| ----------------------------- | --------------------------------------- |
| `variable x;`                 | Uninitialized (gets `defaultInitValue`) |
| `variable x = 5;`             | Initialize with value                   |
| `variable x ∈ 1..N;`          | Nondeterministic from set               |
| `variables x = 1, y = 2;`     | Multiple variables                      |
| `variables x = 1; y ∈ {1,2};` | Semicolon separator                     |

### Process-Local Variables

```tla
process (Proc ∈ 1..N)
    variable localVar = 0;  \* Each process has its own copy
{
    a: localVar := self;     \* self = process identifier
}
```

### Procedure Variables

```tla
procedure P(param = defaultVal)
    variable localVar = 0;
{
    lab: localVar := param;
    return;
}
```

### Special Variables (Added by Translation)

| Variable | Type               | Purpose                          |
| -------- | ------------------ | -------------------------------- |
| `pc`     | Function or String | Program counter (current label)  |
| `stack`  | Sequence           | Call stack (if procedures exist) |
| `self`   | Value              | Current process identifier       |

---

## Statements

### Assignment

| Example                     | Explanation                        |
| --------------------------- | ---------------------------------- |
| `x := 5;`                   | Simple assignment                  |
| `x[i] := 5;`                | Array/function update              |
| `r.field := 5;`             | Record field update                |
| `x := 1 \|\| y := 2;`       | Multiple assignment (simultaneous) |
| `x[i] := 1 \|\| x[j] := 2;` | Multiple updates to same array     |

**Rules for same-variable updates:**

- **Allowed:** `x[i] := 1 || x[j] := 2` (single multiple assignment updating
  different components)
- **Not allowed:** Two _separate_ assignment statements to `x` in one step (must
  be separated by a label)
- Multiple assignments: all RHS evaluated first, then assignments performed
  left-to-right

### Skip

```tla
skip;  \* Do nothing (placeholder)
```

### Print & Assert

| Statement      | Purpose                        | Requires      |
| -------------- | ------------------------------ | ------------- |
| `print expr;`  | Print value during checking    | `EXTENDS TLC` |
| `assert expr;` | Check condition, fail if false | `EXTENDS TLC` |

**Example:**

```tla
print <<x, y>>;
assert x > 0;
```

---

## Control Flow

### If Statement

| Example                                 | Explanation              |
| --------------------------------------- | ------------------------ |
| `if (x > 0) { y := 1 }`                 | Simple if                |
| `if (x > 0) { y := 1 } else { y := 0 }` | If-else                  |
| `if (x > 0) { a: y := 1 }`              | Labeled statement inside |

**Rules:**

- If contains label/call/return/goto → must be followed by label
- Then clause cannot be empty

### While Loop

```tla
lab: while (condition) {
    \* body
};
```

**Rules:**

- **Must be labeled**
- The statement _after_ a `while` need not be labeled, even if the loop body
  contains labels

### Either (Nondeterministic Choice)

```tla
either { x := 1 }
or     { x := 2 }
or     { x := 3 }
```

**Equivalence:**

```tla
if (test) { body1 } else { body2 }
\* is equivalent to:
either { await test; body1 }
or     { await ~test; body2 }
```

### With (Bind Variables)

| Example                          | Explanation             |
| -------------------------------- | ----------------------- |
| `with (x ∈ S) { body }`          | Choose element from set |
| `with (x = expr) { body }`       | Bind to specific value  |
| `with (x ∈ S; y ∈ T) { ... }`    | Multiple bindings       |
| `with (x ∈ S, y = expr) { ... }` | Mixed bindings          |

**CRITICAL:** The bound identifier in `with (x ∈ S)` introduces a **new name**.
Do not reuse existing variable names:

```tla
\* BAD - if x is already a variable:
with (x ∈ 1..10) { ... }  \* ERROR: multiply-defined symbol

\* GOOD:
with (i ∈ 1..10) { ... }  \* Use a fresh identifier
```

**Restrictions:**

- The body may not contain labels.
- **Disallowed in the body:**
  - a `while` statement;
  - two separate assignments to the same variable (a single multiple assignment
    may update different components);
  - any statement following a `return`, or any statement other than a `return`
    following a `call`.
- **Effectively disallowed:** `goto` (it must be followed by a label, but labels
  are forbidden in a `with` body).

### Await (Synchronization)

```tla
await condition;  \* Block until condition true
when condition;   \* Synonym for await
```

**Note:** An `await` can appear anywhere within a step. A step with multiple
`await` statements is enabled iff **all** await conditions evaluate to `TRUE`.

**Example:**

```tla
a: await semaphore > 0;
   semaphore := semaphore - 1;
```

### Goto

```tla
goto labelName;
```

**Rules:**

- Must be immediately followed by label in control path
- Can jump into middle of if/while (but avoid)

---

## Processes & Concurrency

### Process Set

```tla
process (ProcName ∈ 1..N)
    variable local = 0;
{
    start: local := self;  \* self = process ID
    print local;
}
```

### Individual Process

```tla
process (MainProc = "main") {
    a: print "main process";
}
```

### Fair Processes

| Declaration             | Fairness                                           |
| ----------------------- | -------------------------------------------------- |
| `process (P ∈ S)`       | Unfair (no fairness)                               |
| `fair process (P ∈ S)`  | Adds WF constraints to all actions of that process |
| `fair+ process (P ∈ S)` | Adds SF constraints to all actions of that process |

### Label Modifiers for Fairness

```tla
fair process (P ∈ 1..N) {
    a:+  \* Strong fairness for this action
    b:-  \* No fairness for this action
    c:   \* Default (weak fairness from 'fair process')
}
```

### Execution Model

A multiprocess algorithm executes by:

1. Repeatedly choosing an arbitrary enabled process
2. Executing one atomic step of that process
3. Process cannot execute if at blocking `await` or `with (x ∈ {})`

---

## Procedures

**Requirements:** Using procedures requires `EXTENDS Sequences` in the module.

### Declaration

```tla
procedure ProcName(param1, param2 = defaultVal)
    variable localVar = 0;
{
    start: localVar := param1 + param2;
    return;
}
```

### Calling

```tla
call ProcName(arg1, arg2);
lab: \* Control returns here after return
```

### Returning Values

PlusCal procedures don't return values directly. Use global variables:

```tla
variables result = [i ∈ 1..N |-> 0];

procedure Compute(arg)
{
    lab: result[self] := arg * 2;
    return;
}

process (P ∈ 1..N) {
    a: call Compute(5);
    b: print result[self];  \* Use returned value
}
```

### Rules

- Parameters are variables (can be assigned)
- Call and return are assignments (count toward "one assignment per step" rule)
- Return must be followed by label (or another return)
- Call must be followed by label or return
- Requires `EXTENDS Sequences`

### Tail Recursion Optimization

When `call P` immediately precedes `return`, both returns execute in single
step:

```tla
procedure P() {
    lab: call P();    \* Tail recursive call
    return;           \* Both returns in one atomic step
}
```

This is standard tail recursion optimization.

---

## Macros

### Declaration

```tla
macro MacroName(param1, param2) {
    await param1 > 0;
    param1 := param1 - 1;
}
```

### Usage

```tla
MacroName(sem, 5);  \* No 'call' keyword
```

### Differences from Procedures

| Feature     | Macro               | Procedure           |
| ----------- | ------------------- | ------------------- |
| Expansion   | Compile-time inline | Runtime call        |
| Labels      | Not allowed         | Allowed             |
| While loops | Not allowed         | Allowed             |
| Call/return | Not allowed         | Allowed             |
| Goto        | Not allowed         | Allowed             |
| Overhead    | None (inlined)      | Call stack overhead |

**Caution:** Macro parameters are substituted textually. Avoid reusing parameter
names as bound variables:

```tla
macro Bad(x) {
    y := [x ∈ 1..N |-> x];  \* ERROR if called with x in scope
}
```

---

## Labels & Atomicity

### The Atomic Step Model

**A step** = execution from one label to the next label

```tla
a: x := 1;      \* Atomic: assign x and y
   y := 2;
b: z := x + y;  \* Atomic: read x,y and assign z
```

### When Labels are Required

| Situation                             | Rule                                                     |
| ------------------------------------- | -------------------------------------------------------- |
| **Beginning of body**                 | Algorithm, process, procedure body must start with label |
| **While statement**                   | Must be labeled                                          |
| **After call**                        | Next statement must be labeled (unless return/goto)      |
| **After return**                      | Next statement must be labeled                           |
| **After goto**                        | Next statement must be labeled                           |
| **After if/either with label inside** | Next statement must be labeled                           |
| **Multiple assignments to variable**  | Label must separate them                                 |

### When Labels Cannot Appear

- Inside `with` statement body
- Inside macro body

### Label Modifiers

```tla
a:+  statement  \* Strong fairness
b:-  statement  \* No fairness
c:   statement  \* Default fairness
```

### Automatic Labeling

```tla
PlusCal options (-label)
```

- Translator adds minimum required labels
- Default for uniprocess algorithms with no labels
- Use `-reportLabels` to see where labels were added

### Implicit Labels

- `Done`: Automatically added at end of each process/algorithm
- `Error`: Implicit label after each procedure body; execution halts if reached
- **These cannot be used as actual label names**

---

## TLA+ Expressions

PlusCal expressions are TLA+ expressions. Here are the most common:

### Numbers & Arithmetic

| Operator      | Meaning                     | Module   |
| ------------- | --------------------------- | -------- |
| `+`, `-`, `*` | Add, subtract, multiply     | Naturals |
| `^`           | Exponentiation              | Naturals |
| `÷`, `%`      | Integer division, modulus   | Naturals |
| `a..b`        | Set of integers from a to b | Naturals |
| `Nat`         | Set of all natural numbers  | Naturals |
| `Int`         | Set of all integers         | Integers |

### Boolean Logic

| Operator        | ASCII | Meaning           |
| --------------- | ----- | ----------------- |
| `∧`             | `/\`  | AND (conjunction) |
| `∨`             | `\/`  | OR (disjunction)  |
| `¬`             | `~`   | NOT (negation)    |
| `⇒`             | `=>`  | Implies           |
| `≡`             | `<=>` | Equivalence (iff) |
| `TRUE`, `FALSE` | -     | Boolean values    |

**Bulleted Lists (for readability):**

```tla
∧ A          \* Conjunction list
∧ ∨ B        \* Equivalent to: A ∧ (B ∨ C) ∧ D
  ∨ C
∧ D

\* Bullets must align exactly
```

### Strings

**String Escape Sequences:**

- `\"` → `"`
- `\\` → `\`
- `\t` → tab
- `\n` → newline
- `\r` → carriage return
- `\f` → form feed

### Sets

| Operator         | ASCII       | Meaning               |
| ---------------- | ----------- | --------------------- |
| `∈`              | `\in`       | Element of            |
| `∉`              | `\notin`    | Not element of        |
| `⊆`              | `\subseteq` | Subset                |
| `∪`              | `\cup`      | Union                 |
| `∩`              | `\cap`      | Intersection          |
| `\`              | `\`         | Set difference        |
| `{e1, e2}`       | -           | Set enumeration       |
| `{}`             | -           | Empty set             |
| `{x ∈ S : P(x)}` | -           | Set comprehension     |
| `{f(x) : x ∈ S}` | -           | Set mapping           |
| `SUBSET S`       | -           | Power set             |
| `UNION S`        | -           | Union of all elements |

**Examples:**

```tla
{1, 2, 3}                        \* Set with three elements
{x ∈ 1..10 : x % 2 = 0}         \* Even numbers 2,4,6,8,10
{x * x : x ∈ 1..5}              \* {1, 4, 9, 16, 25}
```

### Functions (Arrays)

| Syntax              | Meaning                          |
| ------------------- | -------------------------------- |
| `f[x]`              | Function application             |
| `[x ∈ S \|-> expr]` | Function constructor             |
| `[S -> T]`          | Set of all functions from S to T |
| `DOMAIN f`          | Domain of function f             |

**Examples:**

```tla
[i ∈ 1..N |-> 0]                \* Array of N zeros
[i ∈ 1..3 |-> i*i]              \* [1 |-> 1, 2 |-> 4, 3 |-> 9]
```

**TLC Module Operators (for reading stack traces):**

```tla
EXTENDS TLC
d :> e           \* Single-element function [d] = e
f1 @@ f2         \* Function merge (f2 overrides f1)
d1 :> e1 @@ d2 :> e2  \* Equivalent to [d1 |-> e1, d2 |-> e2]
```

### Records

| Syntax                                 | Meaning            |
| -------------------------------------- | ------------------ |
| `r.field`                              | Field access       |
| `[field1 \|-> val1, field2 \|-> val2]` | Record constructor |
| `[field1 : Set1, field2 : Set2]`       | Set of records     |

**Examples:**

```tla
[x |-> 5, y |-> 10]             \* Record with x and y fields
[x : 1..10, y : 1..10]          \* Set of all such records
point.x                          \* Access x field
```

### Tuples & Sequences

**Requires `EXTENDS Sequences`** for operators beyond basic tuple syntax.

| Syntax         | ASCII        | Meaning               |
| -------------- | ------------ | --------------------- |
| `⟨e1, e2⟩`     | `<<e1, e2>>` | Tuple/sequence        |
| `s[i]`         | -            | i-th element          |
| `S1 × S2`      | `S1 \X S2`   | Cartesian product     |
| `Seq(S)`       | -            | All sequences over S  |
| `Head(s)`      | -            | First element         |
| `Tail(s)`      | -            | All but first         |
| `Append(s, e)` | -            | Append element        |
| `s ◦ t`        | `s \o t`     | Concatenate sequences |
| `Len(s)`       | -            | Length                |

### Quantifiers

```tla
∀ x ∈ S : P(x)         \* For all (\A)
∃ x ∈ S : P(x)         \* Exists (\E)
∀ x, y ∈ S : P(x, y)   \* Multiple variables
```

### Control Expressions

```tla
IF condition THEN expr1 ELSE expr2
CASE p1 -> e1 [] p2 -> e2 [] OTHER -> e3
CHOOSE x ∈ S : P(x)    \* Arbitrary element satisfying P (deterministic!)
LET x == expr1 IN expr2
```

**Note on CHOOSE:** The expression `CHOOSE x ∈ S : P(x)` equals some arbitrarily
chosen value x in S satisfying P(x). **The same choice is returned each time**
from the same state—it cannot introduce nondeterminism. Use `with` for
nondeterministic choice.

### Except (Functional Update)

```tla
[f EXCEPT ![i] = newVal]           \* Update array/function
[r EXCEPT !.field = newVal]        \* Update record field
[f EXCEPT ![i][j] = val]           \* Nested update
[f EXCEPT ![i] = val1, ![j] = val2] \* Multiple updates
```

### Additional Standard Modules

**FiniteSets:**

```tla
EXTENDS FiniteSets
Cardinality(S)  \* Number of elements in finite set S
```

**Integers:**

```tla
EXTENDS Integers
Int             \* Set of all integers (positive and negative)
-x              \* Unary minus (negation)
```

**Reals:**

```tla
EXTENDS Reals
Real            \* Set of all real numbers
x / y           \* Real division
```

### Bound Variable Restrictions

**CRITICAL:** Cannot reuse identifiers that already have meaning

```tla
\* BAD - if j is a variable:
{x \in S : j > 0}           \* ERROR: j redefined
[j \in 1..N |-> j * 2]      \* ERROR: j redefined

\* GOOD:
{x \in S : j_local > 0}     \* Use different name
[k \in 1..N |-> k * 2]      \* Use different name
```

---

## Temporal Properties

### Temporal Operators

| Operator       | ASCII     | Meaning                               |
| -------------- | --------- | ------------------------------------- |
| $\Box F$       | `[]F`     | Always F (in all states)              |
| $\Diamond F$   | `<>F`     | Eventually F (in some state)          |
| $F \leadsto G$ | `F ~> G`  | F leads to G (F implies eventually G) |
| `WF_v(A)`      | `WF_v(A)` | Weak fairness of action A             |
| `SF_v(A)`      | `SF_v(A)` | Strong fairness of action A           |

### Common Patterns

| Property               | Formula          | Meaning                      |
| ---------------------- | ---------------- | ---------------------------- |
| **Invariant**          | $\Box P$         | P true in all states         |
| **Eventually**         | $\Diamond P$     | P true in some state         |
| **Infinitely often**   | $\Box\Diamond P$ | P true infinitely many times |
| **Eventually forever** | $\Diamond\Box P$ | P eventually stays true      |
| **Leads to**           | $P \leadsto Q$   | Whenever P, eventually Q     |

### Using in Properties

```tla
\* After translation, define properties:
TypeInvariant == x ∈ Nat ∧ y ∈ Nat
Mutex == ∀ i, j ∈ 1..N : i ≠ j ⇒ ~(pc[i] = "cs" ∧ pc[j] = "cs")
Progress == (∃ i ∈ 1..N : pc[i] = "trying") ↝ (∃ i ∈ 1..N : pc[i] = "cs")
```

---

## Fairness

### Types of Fairness

| Type            | Meaning                                              | When to Use                                      |
| --------------- | ---------------------------------------------------- | ------------------------------------------------ |
| **Weak Fair**   | If action stays enabled, it eventually executes      | Non-blocking actions, guaranteed progress        |
| **Strong Fair** | If action repeatedly enabled, it eventually executes | Blocking actions that may be disabled/re-enabled |

### Specifying Fairness

#### Algorithm Level

```tla
--fair algorithm Name { ... }  \* Conjoins WF of entire Next action
PlusCal options (-wfNext)      \* Same effect
```

**Note:** `--fair algorithm` ≡ `-wfNext` on `Spec` (stronger than
`fair process`).

#### Process Level

```tla
fair process (P ∈ S) { ... }    \* Adds WF constraints to all actions of that process
fair+ process (P ∈ S) { ... }   \* Adds SF constraints to all actions of that process
process (P ∈ S) { ... }         \* No fairness (unfair)
```

#### Action Level

```tla
fair process (P ∈ S) {
    a:   stmt1;  \* Weak fairness (default from 'fair process')
    b:+  stmt2;  \* Strong fairness
    c:-  stmt3;  \* No fairness
}
```

#### Translator Options

```tla
PlusCal options (-wf)          \* All processes weakly fair
PlusCal options (-sf)          \* All processes strongly fair
PlusCal options (-termination) \* Weak fairness + termination checking
```

### Fairness vs Blocking

```tla
\* Non-blocking (WF enough)
a: x := x + 1;

\* Blocking (may need SF)
b: await flag = TRUE;
   flag := FALSE;
```

---

## Translator Options

### Options in `PlusCal options ()` Statement

| Option            | Effect                                                              |
| ----------------- | ------------------------------------------------------------------- |
| `-wf`             | Change all unfair processes to weakly fair                          |
| `-sf`             | Change all unfair processes to strongly fair                        |
| `-wfNext`         | Weak fairness of algorithm's entire next-state action               |
| `-nof`            | No fairness assumptions                                             |
| `-termination`    | Implies `-wf` if no fairness selected; enables termination checking |
| `-noDoneDisjunct` | Suppress extra disjunct preventing deadlock on termination          |
| `-label`          | Add missing labels automatically (default for unlabeled uniprocess) |
| `-labelRoot name` | Use `name` as prefix for added labels (default: `Lbl`)              |
| `-reportLabels`   | Print names/locations of added labels                               |
| `-lineWidth n`    | Maximum line width for translation (default: 78, min: 60)           |

### Command-Line Only Options

| Option         | Effect                                                |
| -------------- | ----------------------------------------------------- |
| `-spec name`   | Use TLA+ spec for translation (e.g., `-spec PlusCal`) |
| `-myspec name` | Use local TLA+ spec from current directory            |
| `-writeAST`    | Write AST.tla without translation                     |
| `-unixEOL`     | Force Unix end-of-line convention                     |
| `-nocfg`       | Suppress .cfg file generation                         |
| `-help`        | Display help                                          |
| `-debug`       | Run in debugging mode                                 |

**Specifying via Toolbox:** Right-click specification in Spec Explorer →
Properties → "PlusCal call arguments" field

---

## Translation to TLA+

### What Gets Translated

**Variables declared:**

- All algorithm variables
- `pc` - program counter (label of next statement)
- `stack` - call stack (if procedures exist)
- Procedure parameters and locals

**Definitions created:**

- `ProcSet` - set of all process IDs (multiprocess)
- `Init` - initial predicate
- `Next` - next-state action
- `Spec` - complete specification
- Action for each label
- Action for each procedure/process

### Example Translation

**PlusCal:**

```tla
--algorithm Example {
    variables x = 0;
    {
        a: x := x + 1;
        b: x := x * 2;
    }
}
```

**Translated TLA+ (simplified):**

```tla
variables x, pc

Init == x = 0 ∧ pc = "a"

a == ∧ pc = "a"
     ∧ x' = x + 1
     ∧ pc' = "b"

b == ∧ pc = "b"
     ∧ x' = x * 2
     ∧ pc' = "Done"

Next == a ∨ b ∨ (pc = "Done" ∧ UNCHANGED <<x, pc>>)
Spec == Init ∧ □[Next]_<<x, pc>>
```

### Using `pc` in Algorithms

```tla
\* Check where other processes are
assert ∀ i ∈ 1..N : (i ≠ self) ⇒ (pc[i] ≠ "critical")

\* Define invariant after translation
Mutex == ∀ i, j ∈ 1..N : i ≠ j ⇒
         ~(pc[i] = "cs" ∧ pc[j] = "cs")
```

### Translation Details

**`defaultInitValue` constant:**

- Declared for uninitialized variables
- Default: model value in Toolbox
- Not type-correct; initialize variables explicitly

**Variable renaming:**

- Occurs when conflicts exist (same label and variable name)
- Check comment after "BEGIN TRANSLATION" for renames
- Warning issued by translator

**Expression transformations:**

- Expressions copied mostly as-is
- Local variables → functions: `j` becomes `j[self]`
- Component assignments use `EXCEPT`: `x[i] := v` → `[x EXCEPT ![i] = v]`
- Variables may be primed: `x'` in next-state actions

---

## Algorithm Refinement

### Implementing Higher-Level Specifications

**Approach 1: Implement TLA+ spec with PlusCal**

- Write high-level TLA+ specification
- Implement with PlusCal algorithm
- Prove refinement (typically interface refinement)

**Approach 2: Implement PlusCal with PlusCal**

- Write abstract PlusCal algorithm
- Refine with more detailed PlusCal
- Usually requires data refinement

**Key concepts:**

- Interface refinement: map low-level variables to high-level (Section 10.8,
  TLA+ book)
- Most common: data refinement (mapping concrete to abstract state)
- Beyond scope of this cheat sheet - see TLA+ book Chapter 10

**Checking refinement:**

- Define refinement mapping in TLA+ module
- Use TLC to check implementation satisfies specification

---

## Common Patterns

### Mutual Exclusion (Peterson's Algorithm)

```tla
--algorithm Peterson {
    variables flag = [i ∈ {0,1} |-> FALSE], turn = 0;

    fair process (P ∈ {0,1}) {
        ncs: while (TRUE) {
            skip;  \* Non-critical section
            entry: flag[self] := TRUE;
            e2:    turn := 1 - self;
            e3:    await ~flag[1-self] ∨ turn = self;
            cs:    skip;  \* Critical section
            exit:  flag[self] := FALSE;
        }
    }
}
```

### Producer-Consumer

```tla
--algorithm ProducerConsumer {
    variables buffer = <<>>, bufSize = 5;

    fair process (Producer = "p") {
        p: while (TRUE) {
            await Len(buffer) < bufSize;
            buffer := Append(buffer, "item");
        }
    }

    fair process (Consumer = "c") {
        c: while (TRUE) {
            await Len(buffer) > 0;
            buffer := Tail(buffer);
        }
    }
}
```

### Semaphore

```tla
macro P(s) {
    await s > 0;
    s := s - 1;
}

macro V(s) {
    s := s + 1;
}

--algorithm Semaphore {
    variables sem = 1;

    fair process (Proc ∈ 1..N) {
        a: P(sem);
        cs: skip;  \* Critical section
        b: V(sem);
    }
}
```

### Barrier Synchronization

```tla
--algorithm Barrier {
    variables count = 0;
    define { BarrierSize == 3 }

    fair process (P ∈ 1..BarrierSize) {
        work: skip;  \* Do work
        wait: count := count + 1;
        sync: await count = BarrierSize;
        continue: skip;
    }
}
```

### Work Queue

```tla
--algorithm WorkQueue {
    variables
        queue = 1..N,
        done = {};

    fair process (Worker ∈ 1..W)
        variable task;
    {
        w: while (queue ≠ {}) {
            with (t ∈ queue) {
                task := t;
                queue := queue \ {t};
            };
            process: skip;  \* Process task
            complete: done := done ∪ {task};
        }
    }
}
```

---

## Troubleshooting

### Common Translator Errors

| Error                                 | Cause                                     | Solution                                      |
| ------------------------------------- | ----------------------------------------- | --------------------------------------------- |
| "Expected ';' but found..."           | Missing semicolon                         | Add semicolon, check earlier in code          |
| "Missing label at..."                 | Label required but missing                | Add label per rules (Section 3.7)             |
| "multiply-defined symbol"             | Reused identifier                         | Don't reuse variable names, check translation |
| "multiply-defined in with/quantifier" | Bound variable reuses existing identifier | Use fresh identifier name                     |
| Can't parse expression                | Invalid TLA+                              | Check TLA+ syntax, operators                  |

### Common TLC Errors

| Error              | Cause                 | Solution                                |
| ------------------ | --------------------- | --------------------------------------- |
| "Deadlock reached" | All processes blocked | Check await conditions, ensure progress |
| "Assertion failed" | Assert false          | Debug with print statements             |
| "null" message     | Undefined expression  | Check record/array access, domain       |
| "Stack overflow"   | Infinite recursion    | Check procedure calls, termination      |

### Debugging Techniques

**Use Print Statements:**

```tla
print <<x, y, pc[self]>>;
```

**Use Print Operator in Invariants:**

```tla
Inv == Print(<<"x=", x>>, x > 0)  \* Prints and returns x > 0
```

**Check Stack in Procedures:**

```tla
procedure Debug() {
    a: print stack;
    return;
}
```

**Constrain State Space:**

```tla
\* In model's state constraint
x < 100 ∧ Len(queue) < 10
```

### Understanding Error Locations

**Key principle:** Errors often appear AFTER their actual source

- Missing semicolon on line 10 may report error on line 11
- Narrow down by commenting out code sections with `(* ... *)`

### Parsing Errors from SANY

**Multiply-defined symbol:**

- Reused identifier from translation (`pc`, `stack`, procedure parameters)
- Bound variable shadows existing identifier
- Solution: Use different names, check "BEGIN TRANSLATION" comment for renames

**Expression errors:**

- Translator doesn't parse expressions (SANY does)
- Click error → jumps to translation
- Use "Goto PCal Source" to find original code
- Variables may be primed (`x'`) or turned into functions (`j[self]`)

### TLC Error Messages

**"null" message:**

- Usually undefined expression
- Check: function domain, record field access, array bounds
- Add `Print(expr, TRUE)` around suspicious expressions

**Stack Trace Format:** When TLC prints procedure stack, format is:

```tla
  [param1 |-> val1, param2 |-> val2, pc |-> "returnLabel", procedure |-> "Name"],
  ...  \* Outer call frames
>>
```

---

## Best Practices

### General Guidelines

1. **Start Simple**: Begin with sequential version, add concurrency
   incrementally
2. **Use Invariants**: Check type correctness and safety properties
3. **Label Strategically**: Each label defines one atomic step
4. **Name Meaningfully**: Use descriptive names for labels, processes, variables
5. **Comment Intent**: Explain what algorithm achieves, not just syntax

### Common Gotchas

```tla
\* WRONG: Two separate assignments to x in one step
a: x := x + 1;
   x := x * 2;  \* ERROR: label required before this

\* RIGHT: Use multiple assignment or add label
a: x := (x + 1) * 2;

\* WRONG: Reusing variable name as bound identifier
variable i = 0;
with (i ∈ 1..N) { ... }  \* ERROR: multiply-defined

\* RIGHT: Use fresh name
with (j ∈ 1..N) { ... }

\* WRONG: CHOOSE for nondeterminism
x := CHOOSE i ∈ 1..10 : TRUE;  \* Always same value!

\* RIGHT: Use with for nondeterminism
with (i ∈ 1..10) { x := i; }
```

### Atomicity

```tla
\* BAD: Too fine-grained (race condition)
a: x := x + 1;
b: y := x;

\* GOOD: Atomic read-modify-write
a: x := x + 1;
   y := x;
```

### Variable Initialization

```tla
\* GOOD: Always initialize or specify type
variables
    counter = 0,
    flags = [i ∈ 1..N |-> FALSE],
    data ∈ DataType;

\* For type checking, initialize procedure parameters
procedure P(param = 0) { ... }
```

### State Space Management

```tla
\* Use constants to parameterize
CONSTANT N, MaxVal

\* Use constraints in model
StateConstraint ==
    ∧ counter < MaxVal
    ∧ Len(queue) < 10
```

### Fairness Usage

```tla
\* Use WF for non-blocking progress
fair process (P ∈ S) {
    a: x := x + 1;  \* Will eventually execute
}

\* Use SF for blocking waits
fair+ process (Q ∈ T) {
    b: await flag;  \* Will eventually proceed if flag keeps toggling
}
```

### Type Correctness

```tla
\* Define after translation
TypeInvariant ==
    ∧ counter ∈ Nat
    ∧ flags ∈ [1..N -> BOOLEAN]
    ∧ pc ∈ [1..N -> {"a", "b", "c", "Done"}]
```

### Comparable Process Identifiers

**All process identifiers must be "comparable":**

- Same general type (all numbers, all strings, all records)
- TLA+ semantics doesn't specify if string equals number
- For TLC: must be comparable values (see TLA+ book p.264)

**Good:**

```tla
process (P ∈ 1..N)        \* All integers
process (Q ∈ {"a", "b"})  \* All strings
```

**Avoid:**

```tla
process (P ∈ 1..3)
process (Q = "main")        \* Mixed integer and string - may cause issues
```

### Definition Placement Rules

**Before "BEGIN TRANSLATION":**

- Operators not using algorithm variables
- Must not reference `pc`, `stack`, or procedure variables

**In `define` statement:**

- Operators using global algorithm variables
- Can use `pc`, `stack` (if procedures exist)
- Cannot use process-local or procedure-local variables

**After "END TRANSLATION":**

- Properties checking translation artifacts
- Can use all declared variables

### Performance Tips

1. **Minimize State Space**:
   - Use smallest possible constants in model
   - Add state constraints
   - Use symmetry sets for model values

2. **Efficient Expressions**:
   - Prefer simple operations
   - Avoid expensive set operations in hot paths
   - Use definition override for complex computations

3. **Multiple Workers**:
   - Run TLC with multiple threads on multi-core
   - Set in model configuration

4. **Simulation Mode**:
   - For quick feedback on large state spaces
   - Trade completeness for speed

---

## Memory Model & Execution Semantics

### State and Transitions

**State**: Assignment of values to all variables at a point in time

**Step**: Atomic transition from one state to another

- Begins at a label
- Ends at next label
- Entire step executes atomically or not at all

**Execution**: Sequence of states connected by steps

```
Initial State → [Step] → State₁ → [Step] → State₂ → ...
```

### Atomicity Boundaries

Labels define where interleaving can occur:

```tla
process (P ∈ 1..2) {
    a: x := x + 1;     \* Process can be interrupted here
       y := x;         \* But not in middle of step
    b: z := y + 1;     \* Another atomic step
}
```

**With 2 processes, possible interleavings:**

- P1:a, P1:b, P2:a, P2:b
- P1:a, P2:a, P1:b, P2:b
- P1:a, P2:a, P2:b, P1:b
- etc.

### Variable Scope & Sharing

| Scope           | Shared?                  | Example                  |
| --------------- | ------------------------ | ------------------------ |
| Global          | Yes (all processes)      | `variables x = 0;`       |
| Process-local   | No (per-process copy)    | In process declaration   |
| Procedure-local | No (per-call activation) | In procedure declaration |

```tla
variables global = 0;  \* Shared by all

process (P ∈ 1..N)
    variable local = 0;  \* Each process has own copy (local[self])
{
    a: global := global + 1;  \* Shared access
       local := local + 1;     \* Private access
}
```

### Multiple Assignment Semantics

```tla
\* All RHS evaluated first, then assigned left-to-right
x := 1 || y := x || z := y;

\* If x=5, y=3 initially:
\* Step 1: Evaluate all RHS: (1, 5, 3)
\* Step 2: x := 1, y := 5, z := 3
\* Final: x=1, y=5, z=3
```

### Procedure Call Stack Semantics

**Stack representation (multiprocess):**

- `stack` is array: `stack[processId]` = sequence of call frames
- Each frame: record with parameter values, local values, return pc

**Example stack value:**

```tla
<<
  [qA |-> "Mn", qv1 |-> 9, qv2 |-> 2, pc |-> "LP2", procedure |-> "Q"],
  [pA |-> 11, pB |-> 12, pv |-> 0, pc |-> "LQ2", procedure |-> "P"]
>>
```

- First element: innermost (current) call
- `pc` field: where to return
- Parameters/locals: values to restore on return

---

## Examples Gallery

### 1. Euclid's GCD Algorithm

```tla
--algorithm Euclid {
    variables u = 24, v ∈ 1..N;
    {
        while (u ≠ 0) {
            if (u < v) {
                u := v || v := u  \* Swap
            };
            u := u - v
        };
        print <<"gcd =", v>>
    }
}
```

### 2. Dining Philosophers

```tla
--algorithm DiningPhilosophers {
    variables forks = [i ∈ 1..N |-> TRUE];  \* TRUE = available

    define {
        LeftFork(p) == p
        RightFork(p) == IF p = N THEN 1 ELSE p + 1
    }

    fair process (Phil ∈ 1..N) {
        think: while (TRUE) {
            skip;  \* Thinking
            pickLeft: await forks[LeftFork(self)];
                      forks[LeftFork(self)] := FALSE;
            pickRight: await forks[RightFork(self)];
                       forks[RightFork(self)] := FALSE;
            eat: skip;  \* Eating
            putLeft: forks[LeftFork(self)] := TRUE;
            putRight: forks[RightFork(self)] := TRUE;
        }
    }
}
```

### 3. Readers-Writers Lock

```tla
--algorithm ReadersWriters {
    variables readers = 0, writer = FALSE;

    fair process (Reader ∈ 1..NR) {
        r: while (TRUE) {
            startRead: await ~writer;
                       readers := readers + 1;
            read: skip;  \* Reading
            endRead: readers := readers - 1;
        }
    }

    fair process (Writer ∈ 1..NW) {
        w: while (TRUE) {
            startWrite: await ~writer ∧ readers = 0;
                        writer := TRUE;
            write: skip;  \* Writing
            endWrite: writer := FALSE;
        }
    }
}
```

### 4. Two-Phase Commit

```tla
--algorithm TwoPhaseCommit {
    variables
        rmState = [rm ∈ RM |-> "working"],
        tmState = "init",
        tmPrepared = {},
        msgs = {};

    macro Send(m) { msgs := msgs ∪ {m}; }

    fair process (ResourceManager ∈ RM) {
        rm: while (TRUE) {
            either {  \* Prepared to commit
                await rmState[self] = "working";
                rmState[self] := "prepared";
                Send([type |-> "Prepared", rm |-> self]);
            } or {  \* Abort
                await rmState[self] ∈ {"working", "prepared"};
                rmState[self] := "aborted";
            } or {  \* Receive commit
                await [type |-> "Commit"] ∈ msgs;
                rmState[self] := "committed";
            } or {  \* Receive abort
                await [type |-> "Abort"] ∈ msgs;
                rmState[self] := "aborted";
            }
        }
    }

    fair process (TransactionManager = "TM") {
        tm: while (TRUE) {
            either {  \* Receive prepared
                await tmState = "init";
                with (msg ∈ {m ∈ msgs : m.type = "Prepared"}) {
                    tmPrepared := tmPrepared ∪ {msg.rm};
                };
            } or {  \* Commit
                await tmState = "init" ∧ tmPrepared = RM;
                tmState := "committed";
                Send([type |-> "Commit"]);
            } or {  \* Abort
                await tmState = "init";
                tmState := "aborted";
                Send([type |-> "Abort"]);
            }
        }
    }
}
```

### 5. Bank Account Transfer

```tla
--algorithm BankTransfer {
    variables balance = [a ∈ Accounts |-> InitialBalance];

    fair process (Transfer ∈ Transfers)
        variables from, to, amount;
    {
        start: with (t ∈ TransferSpec) {
            from := t.from;
            to := t.to;
            amount := t.amount;
        };
        check: if (balance[from] ≥ amount) {
            withdraw: balance[from] := balance[from] - amount;
            deposit: balance[to] := balance[to] + amount;
        };
    }
}

\* Invariant: Total money unchanged
TotalMoney == balance[a1] + balance[a2] + ... = InitialBalance * Len(Accounts)
```

---

## PlusCal vs TLA+ vs Other Languages

### PlusCal vs TLA+

| Feature            | PlusCal                | TLA+                              |
| ------------------ | ---------------------- | --------------------------------- |
| **Style**          | Imperative (C-like)    | Declarative (mathematical)        |
| **Learning Curve** | Easier for programmers | Steeper, requires math background |
| **Abstraction**    | Higher-level algorithm | Low-level state machine           |
| **Use Case**       | Writing algorithms     | Specifying systems                |
| **Translation**    | Compiles to TLA+       | Direct specification              |
| **Modularity**     | Limited                | Excellent (parameterized modules) |
| **Refinement**     | Via translation        | Native support                    |

**When to use PlusCal:**

- You think imperatively
- Prototyping concurrent algorithms
- Learning formal methods

**When to use pure TLA+:**

- Complex system specifications
- Module composition
- Refinement proofs
- Maximum expressiveness

### PlusCal vs Other Specification Languages

| Language           | Paradigm    | Strengths                      | Weaknesses                      |
| ------------------ | ----------- | ------------------------------ | ------------------------------- |
| **PlusCal**        | Imperative  | Familiar syntax, TLA+ backend  | Limited modularity              |
| **TLA+**           | Declarative | Highly expressive, refinement  | Steep learning curve            |
| **Promela (SPIN)** | Imperative  | Efficient, LTL properties      | C-like only, limited data types |
| **Alloy**          | Declarative | SAT-based, great for structure | Not time-oriented               |
| **P**              | Imperative  | Async state machines           | Specific to distributed systems |
| **Dafny**          | Imperative  | Proof-carrying code            | Code-level, not algorithm       |

---

## Tooling

### VSCode Extension

**TLA+ extension by alygin** provides comprehensive TLA+ and PlusCal support in
Visual Studio Code.

**Installation:**

- Search for "TLA+" in VSCode Extensions (Ctrl+Shift+X)
- Or: `ext install alygin.vscode-tlaplus`

**Key Features:**

- Syntax highlighting for TLA+ and PlusCal
- PlusCal-to-TLA+ translation
- TLC model checker integration
- Model checking visualization
- Code snippets and completion
- Expression evaluation
- PDF/LaTeX export

**Documentation:** [Project Wiki](https://github.com/alygin/vscode-tlaplus/wiki)

### TLA+ Toolbox

**Installation:**

- Download from: https://lamport.azurewebsites.net/tla/toolbox.html
- Available for Windows, macOS, Linux

**Key Features:**

- PlusCal editor with syntax highlighting
- Automatic translation (Ctrl+T)
- Model creation and management
- TLC integration
- Error trace visualization

**Workflow:**

1. File → New Specification → Create .tla file
2. Write PlusCal in `(* ... *)`
3. Ctrl+T to translate
4. TLC Model Checker → New Model
5. Configure constants, invariants, properties
6. Run model checker

### TLC Model Checker

**Modes:**

- **Model-checking**: Explores all reachable states
- **Simulation**: Random exploration (faster, incomplete)

**Configuration:**

```
\* In model configuration:
CONSTANTS N = 3
INVARIANT TypeInvariant
INVARIANT SafetyProperty
PROPERTY LivenessProperty
```

**Options:**

- Number of worker threads (use # of CPU cores)
- State space constraints
- Deadlock checking
- Symmetry sets

### TLAPS (TLA+ Proof System)

**Purpose:** Machine-checked proofs of TLA+ specifications

**Note:** TLAPS works on TLA+ specs, not directly on PlusCal

- First translate PlusCal to TLA+
- Then write proofs about the TLA+ translation

---

## Syntax Comparison: C-Syntax vs P-Syntax

| Construct           | C-Syntax              | P-Syntax                        |
| ------------------- | --------------------- | ------------------------------- |
| **Block**           | `{ ... }`             | `begin ... end`                 |
| **If-Else**         | `if (x) { } else { }` | `if x then ... else ... end if` |
| **While**           | `while (x) { }`       | `while x do ... end while`      |
| **Assignment**      | `x := 1;`             | `x := 1;`                       |
| **Multiple Assign** | `x := 1 \|\| y := 2`  | `x := 1 \|\| y := 2`            |
| **Either**          | `either { } or { }`   | `either ... or ... end either`  |
| **Comment (line)**  | `\* comment`          | `\* comment`                    |
| **Comment (block)** | `(* comment *)`       | `(* comment *)`                 |

**This cheat sheet uses C-Syntax.** For P-Syntax, see the P-Syntax manual.

---

## Quick Reference: Translation Artifacts

After translation, these are available in TLA+ for properties:

| Symbol        | Type                 | Meaning                                                                   |
| ------------- | -------------------- | ------------------------------------------------------------------------- |
| `pc`          | String or Function   | Current label (uniprocess) or `[ProcessId -> Label]`                      |
| `stack`       | Sequence or Function | Call stack (if procedures)                                                |
| `vars`        | Tuple                | All variables (for UNCHANGED)                                             |
| `ProcSet`     | Set                  | All process identifiers (multiprocess)                                    |
| `Init`        | Formula              | Initial predicate                                                         |
| `Next`        | Action               | Next-state relation                                                       |
| `Spec`        | Formula              | Complete specification                                                    |
| `Termination` | Formula              | All processes reach "Done" (only defined when `-termination` option used) |

**Example Invariants:**

```tla
\* After translation:
TypeOK ==
    ∧ x ∈ Nat
    ∧ pc ∈ [ProcSet -> {"a", "b", "c", "Done"}]

Mutex ==
    ∀ i, j ∈ ProcSet : i ≠ j ⇒
        ~(pc[i] = "cs" ∧ pc[j] = "cs")
```

---

## Additional Resources

**Official Documentation:**

- TLA+ Website: https://lamport.azurewebsites.net/tla/tla.html
- PlusCal Manual: https://lamport.azurewebsites.net/tla/p-manual.pdf
- Specifying Systems Book: https://lamport.azurewebsites.net/tla/book.html

**Learning:**

- Learn TLA+: https://learntla.com
- TLA+ Video Course: https://lamport.azurewebsites.net/video/videos.html
- TLA+ Examples: https://github.com/tlaplus/Examples

**Community:**

- Google Group: https://groups.google.com/forum/#!forum/tlaplus
- GitHub: https://github.com/tlaplus

---

**End of PlusCal Cheat Sheet v1.8**

_Based on "A PlusCal User's Manual: C-Syntax Version 1.8" by Leslie Lamport_
