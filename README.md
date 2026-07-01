# JVM Formal Verification in Rocq

This is a coursework project I did for a formal methods module at the University of Southampton. The goal was to build a small but complete model of a JVM-like virtual machine in Rocq (formerly Coq), and then formally prove that a specific program running on it actually does what it's supposed to do.

I found this project genuinely interesting — it's one thing to write a program and test it, but it's another to *prove* it correct in the mathematical sense, where no amount of clever edge cases can slip past you.

---

## What's in here

The project is split into two main sections:

### Section 1 — JVM Model

I defined a minimal but functional virtual machine from scratch, including:

- **Memory** and **Stack** as lists of natural numbers
- A `read` / `write` interface for accessing local variables
- An **instruction set** covering `load`, `const`, `add`, `sub`, `mul`, `store`, `goto`, `ifeq`, and `halt`
- A `Machine` record holding the program counter, program, locals, and stack
- `execute_single_instruction` — steps the machine forward by one instruction
- `execute_n_instructions` — runs the machine for `n` steps

I also proved two general lemmas about execution:

- **`execute_instruction_succ`** — running `n` steps then one more equals running `n+1` steps
- **`execute_plus_instructions`** — running `a + b` steps equals running `b` steps followed by `a` steps

These might look simple, but they're the foundation that makes the program-level proofs possible.

### Section 2 — Exponential Program

I wrote a JVM program (`expt_program`) that computes `n ^ m` iteratively using a loop, then proved it correct.

The proof strategy was:

1. Define `expt_iter` — a tail-recursive Rocq function that mirrors what the JVM loop does
2. Prove **`expt_iter_helper`** — relating `expt_iter` at any accumulator value to `n ^ m`
3. Prove **`expt_iter_equivalent`** — showing `expt_iter n m 1 = n ^ m`
4. Prove **`expt_loop_correct`** — the JVM loop body produces the same result as `expt_iter`
5. Prove **`jvm_expt_correct`** — the full program computes the right answer
6. Prove **`jvm_expt_halts`** — the program always reaches the `halt` instruction

The last two theorems together mean: for any natural numbers `n` and `m`, the program terminates and returns `n ^ m`. No admitted lemmas, no shortcuts.

---

## How to run it

You'll need [Rocq](https://rocq-prover.org/) (version 8.x or later) installed.

```bash
# Check the whole file compiles cleanly
rocq compile jvm_verification.v

# Or open it interactively in RocqIDE / VS Code with the Rocq extension
# and step through the proofs line by line
```

If everything is set up correctly, the file should compile with no errors and no warnings about unfinished proofs.

---

## What I learned

Before this project, I'd used Rocq for simple exercises but never built anything end-to-end. A few things that surprised me:

- Structuring the induction carefully matters a lot. For `expt_loop_correct`, getting the right induction variable and accumulator took several attempts before the proof would go through.
- The `change` tactic was really useful for unfolding specific computation steps in the JVM loop without having to manually `simpl` everything.
- Writing the helper lemmas first (`execute_instruction_succ`, `execute_plus_instructions`) made the final proofs much cleaner — without them, the top-level theorems would have been a mess.

---

## Project context

- **Module**: COMP2313 — Formal Specification and Verification, University of Southampton
- **Language**: Rocq (Coq)
- **Topic**: Formal verification of a JVM-style virtual machine and an exponential program
