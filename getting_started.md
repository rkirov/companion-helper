# Getting Started: Writing a New Companion

> **Audience.** A human or AI agent starting a new Lean companion for a
> specific math textbook. Read [design.md](design.md) first for *why*;
> [guide.md](guide.md) for *how* (style, idioms, tricks).

## Goal

Produce a Lean 4 project that mirrors a chosen textbook: every definition,
proof, example, and exercise from the text translated into Lean, with
exercises stubbed as `sorry` for readers to fill in. **No narrative** — the
prose stays in the original book.

## Pick a textbook

Choose from the list in [design.md](design.md#next-steps), or propose a new
one on the issue tracker. Confirm the textbook isn't already covered (or
in active development) elsewhere. License the companion under Apache-2.0
to keep upstreaming to mathlib friction-free.

## Project layout

A new companion is a fresh Lake project. Recommended skeleton:

```
my-companion/
├── README.md                ← what this is, build instructions
├── lakefile.toml
├── lean-toolchain           ← match mathlib's pin
├── MyCompanion.lean         ← root, imports each chapter
├── MyCompanion/
│   ├── Chapter01.lean
│   ├── Chapter02.lean
│   └── ...
└── .github/workflows/       ← lake build on CI
```

Dependencies:

```toml
[[require]]
name = "mathlib"
scope = "leanprover-community"
rev = "v4.29.0"            # match the latest mathlib release tag

[[require]]
name = "companion-helper"  # this repo, for @[avoiding ...]
git = "https://github.com/rkirov/companion-helper"
rev = "main"
```

After `lake update mathlib && lake exe cache get`, mathlib is ready
without recompilation.

For CI, copy `.github/workflows/build.yml` from this repo as a starting
point — it's a minimal `leanprover/lean-action@v1` workflow with the
mathlib cache enabled.

## Per-chapter workflow

For each chapter or section:

1. **Read the chapter.** Make a list of every definition, theorem,
   example, and exercise.
2. **Draft the Lean translation.** AI is fine at this stage — the draft
   doesn't have to be perfect.
   - For each *definition*: prefer the mathlib version
     (see [design.md](design.md#key-design-decision-use-mathlib-definitions)).
     Use `recall` to show that the textbook's axiom matches mathlib's.
   - For each *theorem with a proof in the text*: translate the proof.
     Aim to follow the textbook's structure rather than mathlib's terser
     style — companions are pedagogical.
   - For each *exercise*: state it, end with `sorry`. If a one-line
     mathlib lemma defeats the exercise, mark it with
     `@[avoiding mathlib_lemma_name]`. See [guide.md](guide.md) for the
     idiom.
3. **Build clean.** `lake build` must pass with no warnings beyond
   expected `sorry` warnings.
4. **Open a PR.** Describe which sections this covers and what's still
   open. Tag for review.
5. **Human review.** Someone who knows the material confirms the
   translations are faithful (no misformalizations).
6. **Playtest.** Someone clones the repo to a fork and works every
   exercise. Real proofs reveal ill-stated lemmas; fixes flow back as PRs.

The repo should make it visible per-chapter whether each step (review,
playtest) is complete.

## What "done" looks like for a chapter

- Every definition, theorem, example, and exercise from the chapter
  appears in the Lean file.
- Definitions match (or are bridged to) mathlib.
- Exercises are stubbed `sorry` and tagged `@[avoiding …]` where relevant.
- A separate fork or branch demonstrates that all exercises *are*
  solvable with the toolkit the text provides.
- CI builds green; mathlib linters pass.

## Chapter status table

The companion's top-level README should expose a per-chapter status
table so readers and contributors can see at a glance which chapters are
review-clean and which are playtested.

```markdown
| Chapter | Reviewed | Playtested |
|---|---|---|
| 1. Groups | ✓ | ✓ |
| 2. Subgroups | ✓ | — |
| 3. Quotients | — | — |
```

A row earns ✓ only after the corresponding step in the per-chapter
workflow above finishes.

## What to delegate to AI

- **First-pass translation** of definitions, theorems, exercises.
- **Drafting solutions** in the playtest fork.
- **Looking up mathlib names** for textbook concepts.

What humans still own:

- Confirming a translation is *faithful* (no misformalization).
- Spotting that an exercise is unsolvable / ill-stated as written.
- Style and pedagogical fidelity to the text.

## See also

- [design.md](design.md) — why companions, what's in scope.
- [guide.md](guide.md) — translation idioms, style, anti-cheating.
- [Tao's analysis companion][tao-repo] — the working precedent.

[tao-repo]: https://github.com/teorth/analysis
