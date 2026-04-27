# Companion Design Goals

> **Status: seed.** This file collects the overarching design goals for Lean
> companions to math textbooks. The current source of truth is the
> [design doc draft][doc] (which will continue to evolve); this file
> will diverge as the project matures.

[doc]: https://docs.google.com/document/d/1BFsOyxS2lHsyH3qv9RmH5MIJWg3La8OCEJxoVmX-r_g/

## What is a Lean companion?

A Lean project that mirrors a specific math textbook: a Lean translation of
all definitions, proofs, examples, and exercises (without solutions). It
contains **no narrative** — that stays in the original text — and is meant
to be:

1. read concurrently with the text;
2. cloned and worked through, replacing each `sorry` with a real proof.

The canonical existing example is Tao's *Real Analysis I* companion
([blog post][tao-blog], [repo][tao-repo]).

[tao-blog]: https://terrytao.wordpress.com/2025/05/31/a-lean-companion-to-analysis-i/
[tao-repo]: https://github.com/teorth/analysis

## Who are companions for?

1. People familiar with the math who want to practice Lean by formalizing
   it.
2. People familiar with Lean who want to learn a new field of math through
   formal methods.
3. Students learning math and Lean simultaneously — *studying math by
   coding in Lean*.

## Long-term vision

A curriculum of companions covering an undergraduate (and eventually
graduate) math program: Real Analysis (done) → Linear Algebra →
Abstract Algebra → Set Theory → Topology → Number Theory → Logic → …

There is far more math to learn than there is Lean. As Lean's mathematical
community grows, we expect demand for *learning new math through Lean* to
keep increasing — but the resources for it have to be written.

## Key design decision: use mathlib definitions

When the textbook introduces a concept already in mathlib (e.g., `Group`),
the companion **uses the mathlib definition directly** rather than
redefining it. The reasoning:

- Companions need to compose into a curriculum. If each rolls its own
  definitions, they'll drift into a worse parallel mathlib and require
  cross-imports between companions.
- Mathlib should be the dependency layer; companions should never import
  each other.
- Learners eventually need to know mathlib's way of doing things anyway —
  start there.

Tradeoffs accepted:
- **No cheating.** Mitigated by `@[avoiding …]` (see [guide.md](guide.md))
  to mark exercises whose one-liner solution would defeat the
  pedagogical point. Determined cheating is always possible; this is not
  optimizing for adversarial robustness.
- **Higher generality.** Mathlib's `Group` extends `DivInvMonoid`, which
  the textbook hasn't introduced. The companion can `recall` mathlib
  definitions to show that the textbook axioms match.
- **Conceptual divergence.** When mathlib's development of a concept
  differs significantly from the text (e.g., filters vs. ε-δ for
  convergence), fall back to a custom definition with an equational
  bridge — but this is the exception, not the rule.

## Process

Companions are developed in the open, one chapter at a time, via standard
GitHub PR review. Recommended workflow:

1. Per chapter or section, draft a Lean translation. AI may produce the
   draft.
2. Human review by someone who knows the material.
3. A "playtester" works all the exercises in a fork, upstreaming fixes
   for unprovable or ill-stated lemmas.

Companions follow [mathlib's style guide][style], build green on CI,
have linters enabled, and are kept on the latest mathlib + Lean toolchain.
Each chapter's review and playtest status should be visible in the repo.

[style]: https://leanprover-community.github.io/contribute/style.html

## Success looks like

High-quality, human-reviewed, human-playtested companions exist for every
proof-based topic in an average undergraduate math curriculum. Useful
proxy: cloned forks with solutions show that learners actually pick them
up.

## Frequently asked

**Why companions instead of just "open Lean and start formalizing"?**
Writing a companion is harder than solving the exercises and you'd learn
more — but the companion provides scaffolding for learners who need it.

**Why not write a new mathlib-aligned text instead?**
Existing texts have battle-tested pedagogy. The companion supplies the
formal layer that the original lacks; it doesn't have to re-do the
teaching.

**Why not bake Lean tutorials into the companion?**
Eventually there'll be many companions; embedding Lean intro in each
becomes annoying noise for readers on their n-th companion. Lean basics
belong in dedicated intros.

**Why not use Verbose Lean / NNG / other beginner scaffolding?**
The expected reader has intermediate Lean skills, matching the math
maturity these texts already demand.

## Next steps

In rough textbook-dependency order, candidate companions to write next
(once Real Analysis is "done enough" to anchor on):

- Linear algebra — Axler
- Abstract algebra — Aluffi
- Basic set theory — Halmos
- Point-set topology — Munkres or Armstrong
- Elementary number theory — Rosen
- Logic — TBD

Pre-analysis intros (e.g., *Book of Proof*) are lower priority; existing
Lean-based options like *Math 2001* already cover that space.
