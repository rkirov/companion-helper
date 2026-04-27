# companion-helper

Tooling for authors of Lean 4 [textbook companions](https://terrytao.wordpress.com/2025/05/31/a-lean-companion-to-analysis-i/).

- **[design.md](design.md)** — what a companion is, why we're writing them, key design decisions.
- **[getting_started.md](getting_started.md)** — point your agent (or yourself) here when starting a new companion.
- **[guide.md](guide.md)** — translation idioms, style, anti-cheating tips.

The current source-of-truth for design discussion is the
[design doc draft](https://docs.google.com/document/d/1BFsOyxS2lHsyH3qv9RmH5MIJWg3La8OCEJxoVmX-r_g/);
the markdown files above are seeded from it and will diverge as the
project matures.

## What's here

### `@[avoiding …]`

An attribute that forbids the listed names from appearing in the proof term
of the attached declaration. After the proof elaborates, the proof term is
inspected; if any forbidden name appears in it, elaboration errors.

```lean
import CompanionHelper

@[avoiding Nat.mul_one]
theorem mul_one_ex (n : Nat) : n * 1 = n := by exact Nat.mul_one n
-- error: declaration 'mul_one_ex' uses forbidden lemma(s): [Nat.mul_one]
```

`exact?`, `simp [forbidden_lemma]`, and direct `apply`/`exact` of a forbidden
lemma all get caught — each materializes a proof term that references the
lemma directly.

The check is intentionally shallow (one level — direct constants in the proof
term). A user-defined wrapper defeats it. Per the design doc, the goal is to
catch *accidental* wins, not to be robust against adversarial cheating.

Stacks with other attributes:

```lean
@[simp, avoiding Nat.mul_one]
theorem foo (n : Nat) : n + 0 = n := by rfl
```

## Build

```
lake update mathlib && lake exe cache get   # first time only
lake build                                  # main library
lake build CompanionHelperTests             # tests (use #guard_msgs)
```

Toolchain: `leanprover/lean4:v4.29.0`. Mathlib pinned at `v4.29.0` (used in
tests; the core library itself only depends on `Lean`).
