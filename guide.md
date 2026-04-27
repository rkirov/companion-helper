# Companion Author's Guide

> **Status: seed.** Idioms and tricks for writing a Lean companion to a
> math textbook. This will grow as more companions are written and patterns
> emerge. Companion authors: PR your patterns here.

## Style

- Follow [mathlib's style guide][style] for naming, indentation, and
  proof structure.
- Enable mathlib's standard linters in CI.
- **Pedagogical fidelity over terseness.** Where mathlib would write a
  one-line `simp`, the companion may prefer a longer proof that mirrors
  the textbook's argument step-by-step. Companions exist for learners.

[style]: https://leanprover-community.github.io/contribute/style.html

## Reproving theorems from the text

Theorems that come with proofs in the textbook are not exercises — the
reader is not filling in `sorry`. But the *proof* is still the lesson, and
the Lean translation should mirror the textbook's argument so a reader can
follow both side-by-side, step for step.

**Preserve intermediate steps.** Where the text writes "first observe X,
then Y, then conclude Z", surface those as `have` statements (or named
sub-lemmas) instead of collapsing into one tactic.

If a mathlib version of the same theorem exists, make sure to mention that 
name with `recall`. If a shorter mathlib proof exists, ok to show it after
the text version.

## Use mathlib definitions, bridge when needed

Default: when the text introduces a concept already in mathlib (e.g.,
`Group`), use mathlib's definition directly. See
[design.md](design.md#key-design-decision-use-mathlib-definitions) for the
rationale.

### Showing the textbook axioms match mathlib

`recall` is useful for connecting the text's stated axioms to mathlib's
formalism without redefining anything:

```lean
import Mathlib.Tactic.Recall

recall mul_assoc {G : Type*} [Semigroup G] (a b c : G) :
    a * b * c = a * (b * c)
```

(See e.g. [napkin-lean's Chapter01_Groups][napkin-grp].)

[napkin-grp]: https://github.com/rkirov/napkin-lean/blob/main/NapkinLean/Part01_StartingOut/Chapter01_Groups.lean

### When to fall back to a custom definition

Two cases the rule of thumb breaks:

1. **The text and mathlib develop the concept differently.**
   E.g., real analysis convergence via ε-δ vs. mathlib's `Filter`-based
   `Tendsto`. Define the textbook's version yourself, then prove an
   equivalence bridge so later chapters can swap to mathlib.
2. **The concept isn't in mathlib yet.** Build it from scratch. If the
   work could plausibly go upstream, structure it so excerpting to a
   mathlib PR is cheap.

## Anti-cheating: `@[avoiding …]`

Many textbook exercises have a one-line mathlib solution that defeats the
pedagogical point. Mark these with the `@[avoiding …]` attribute from
`companion-helper`:

```lean
import CompanionHelper

@[avoiding mul_inv_rev]
theorem inv_of_product {G : Type*} [Group G] (a b : G) :
    (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  sorry  -- reader fills in
```

After the proof elaborates, the proof term is inspected; if it references
any name in the avoid list (directly or via tactics like `simp`, `aesop`,
`exact?`), the build fails.

Notes:

- The avoid list accepts unqualified names — `mul_one` matches any
  `Foo.mul_one` in scope (suffix matching). Qualify when you want to be
  more specific.
- Multiple lemmas: `@[avoiding mul_inv_rev, mul_one]`.
- Stacks with other attributes: `@[simp, avoiding …]`.
- Known limitations:
  - `grind` packages its proof inside an auto-generated helper, hiding
    the forbidden lemma one level deeper than our shallow check sees.
    Don't expect `@[avoiding …]` to constrain `grind`.
  - The check only looks one level deep into the proof term; a
    user-defined wrapper around the forbidden lemma defeats it. Per the
    design doc, we are not optimizing against adversarial cheating —
    only accidental cheating from `simp`, `aesop`, `exact?`, etc.

## Translating "prove or disprove" exercises

A textbook exercise of the form *"prove or disprove …"* or *"what happens
to theorem X if condition Y is removed"* turns into a `Decidable`
instance. Tao's analysis companion established the pattern:

```lean
example : Decidable (∀ n : ℕ, n + 0 = n) := by
  apply isTrue
  intro n
  rfl
```

(See the [analysis Section 9.2 example][tao-decide].)

[tao-decide]: https://github.com/teorth/analysis/blob/52ca2a255e856f69dd04bd441411afeb043a44f8/Analysis/Section_9_2.lean#L56-L70

## Publishing

Each companion should publish a Verso artifact (an HTML rendering of the
sources, like [analysis][tao-verso]) for slightly nicer reading outside
GitHub. Verso integration happens via a Lake target.

[tao-verso]: https://teorth.github.io/analysis/Analysis/

## License

Apache-2.0 is the friendliest choice for upstreaming useful pieces to
mathlib. Use it unless you have a reason not to.

## Add your tip here

This guide grows from real companion-writing experience. If you found a
pattern useful, send a PR adding it.
