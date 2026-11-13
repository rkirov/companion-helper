module

public meta import Lean

/-!
# `@[avoiding …]` attribute

Attach a list of forbidden lemma names to any declaration. After the proof
elaborates, the proof term is inspected and an error is raised if any
forbidden name appears in it.

```
@[avoiding Nat.mul_one]
theorem mul_one_ex (n : Nat) : n * 1 = n := by
  exact Nat.mul_one n
-- error: declaration 'mul_one_ex' uses forbidden lemma(s): [Nat.mul_one]
```

The check follows two paths into the proof term:
- *direct* — names that appear in the immediate proof term (catches a literal
  `exact <forbidden>` or `simp [<forbidden>]`);
- *helper* — bodies of auto-generated helpers under the declaration's own
  namespace (e.g., `<decl>._proof_*` that `grind` / `decide` / `omega`
  synthesize to bury their certificate).

User-defined wrappers in *other* namespaces are NOT followed; library
indirection through mathlib is NOT followed (it would explode and
false-positive via the algebra-hierarchy proof structure).

Forbidden names match by either suffix (so `mul_one` catches `Nat.mul_one`)
or prefix (so `Lean.Grind` catches `Lean.Grind.CommRing.…`, useful for
blocking entire decision-procedure namespaces).

Per the design doc, the goal is to catch *accidental* wins from `exact?`,
`simp`, default-tactic invocations like `grind`, etc. — not to be robust
against adversarial cheating. A user-defined wrapper in an unrelated
namespace still defeats it.

Stacks with other attributes (`@[simp, avoiding …]`), works on any kind of
declaration, and can be removed by deleting one line.
-/

public meta section

namespace CompanionHelper

open Lean

/-- Set of `Expr.const` names appearing in `e`, plus the bodies of any
auto-generated helper lemmas under `decl`'s own namespace (e.g.,
`decl._proof_1_1` that `grind`/`decide`/`omega` synthesize to hide their proof).
Library references are intentionally NOT followed — recursing through mathlib
would explode and would also false-positive (e.g., `add_assoc` transitively
mentions `eq_neg_of_add_eq_zero_*` via the AddGroup proof structure). -/
private partial def collectConstNamesDeep (env : Environment) (decl : Name) (e : Expr)
    (visited : NameSet := {}) : NameSet := Id.run do
  let mut acc := e.foldConsts {} fun n s => s.insert n
  let mut visited := visited
  for n in acc do
    if visited.contains n then continue
    visited := visited.insert n
    -- Only recurse into helpers under `decl`'s namespace. Catches `grind`'s
    -- `_proof_*` indirection without walking the rest of mathlib.
    -- Compare user-facing names: in a `module`, a public theorem's helpers are
    -- private (`_private.<Module>.0.decl._proof_1`) while `decl` is not.
    unless (privateToUserName decl).isPrefixOf (privateToUserName n) do continue
    let some info := env.find? n | continue
    let some body := info.value? (allowOpaque := true) | continue
    for m in collectConstNamesDeep env decl body visited do
      acc := acc.insert m
      visited := visited.insert m
  return acc

/-- Component path of a `Name`, innermost first. E.g. `Nat.mul_one` → `["mul_one", "Nat"]`. -/
private partial def Name.componentsRevS : Name → List String
  | .anonymous => []
  | .str pre s => s :: Name.componentsRevS pre
  | .num pre i => s!"{i}" :: Name.componentsRevS pre

/-- True iff `xs` is a prefix of `ys`. -/
private def isListPrefix : List String → List String → Bool
  | [],      _       => true
  | _,       []      => false
  | a :: as, b :: bs => a == b && isListPrefix as bs

/-- True iff `avoid`'s component path is a tail (right-suffix) of `used`'s.
E.g. `mul_one ⊑ Nat.mul_one`, `Group.mul_one ⊑ Foo.Group.mul_one`. -/
private def isNameSuffix (avoid used : Name) : Bool :=
  isListPrefix (Name.componentsRevS avoid) (Name.componentsRevS used)

/-- True iff `avoid`'s component path is a head (left-prefix) of `used`'s,
i.e. `avoid` is a strict-or-equal namespace of `used`. E.g.
`Lean.Grind ⊑ Lean.Grind.CommRing.Stepwise.unsat_eq`. Used to forbid every
constant inside an entire namespace — handy for blocking decision-procedure
machinery like `Lean.Grind.*` that `grind` injects into proof terms. -/
private def isNamePrefix (avoid used : Name) : Bool :=
  isListPrefix (Name.componentsRevS avoid).reverse (Name.componentsRevS used).reverse

/-- Attribute syntax: `@[avoiding Foo.bar, Baz.qux]`. -/
syntax (name := avoiding) "avoiding " ident,* : attr

initialize registerBuiltinAttribute {
  name := `avoiding
  descr :=
    "Error if the proof term of the attached declaration references any of \
     the listed names. Designed for textbook-companion exercises where some \
     lemmas would trivialize the problem."
  applicationTime := .afterTypeChecking
  add := fun decl stx kind => do
    unless kind == AttributeKind.global do
      throwError "`avoiding` only supports the global attribute kind"
    let avoidIdents := stx[1].getSepArgs
    -- Inside a `module`, the exported view of the environment hides theorem
    -- bodies (and `_proof_*` helpers); inspect the private view instead.
    let env := (← getEnv).setExporting false
    let some info := env.find? decl
      | throwError "avoiding: declaration `{decl}` not found"
    -- `allowOpaque := true` is required to get the body of theorems and
    -- opaque definitions; without it, `value?` returns `none` for them.
    let some value := info.value? (allowOpaque := true)
      | throwError "avoiding: declaration `{decl}` has no body to inspect"
    let used := collectConstNamesDeep env decl value
    let mut violations : Array Name := #[]
    for av in avoidIdents do
      let avName := av.getId
      for u in used do
        -- Match against the user-facing name: inside a `module`, non-`public`
        -- declarations carry a `_private.<Module>.0.` prefix.
        let u := privateToUserName u
        if isNameSuffix avName u || isNamePrefix avName u then
          violations := violations.push u
    unless violations.isEmpty do
      throwError "declaration '{privateToUserName decl}' uses forbidden lemma(s): {violations.toList}"
}

end CompanionHelper

end
