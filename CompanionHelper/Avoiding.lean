import Lean

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

The check is intentionally shallow — direct `Expr.const` references in the
proof term. A user-defined wrapper defeats it. Per the design doc, the goal
is to catch *accidental* wins from `exact?`, `simp`, or `apply`-ing a
forbidden lemma — not to be robust against adversarial cheating.

Stacks with other attributes (`@[simp, avoiding …]`), works on any kind of
declaration, and can be removed by deleting one line.
-/

namespace CompanionHelper

open Lean

/-- Set of `Expr.const` names appearing in `e`. -/
private def collectConstNames (e : Expr) : NameSet :=
  e.foldConsts {} fun n s => s.insert n

/-- Component path of a `Name`, innermost first. E.g. `Nat.mul_one` → `["mul_one", "Nat"]`. -/
private partial def Name.componentsRevS : Lean.Name → List String
  | .anonymous => []
  | .str pre s => s :: Name.componentsRevS pre
  | .num pre i => s!"{i}" :: Name.componentsRevS pre

/-- True iff `avoid`'s component path is a tail (right-suffix) of `used`'s.
E.g. `mul_one ⊑ Nat.mul_one`, `Group.mul_one ⊑ Foo.Group.mul_one`. -/
private def isNameSuffix (avoid used : Lean.Name) : Bool :=
  let rec go : List String → List String → Bool
    | [],     _      => true
    | _,      []     => false
    | a :: as, b :: bs => a == b && go as bs
  go (Name.componentsRevS avoid) (Name.componentsRevS used)

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
    let env ← getEnv
    let some info := env.find? decl
      | throwError "avoiding: declaration `{decl}` not found"
    -- `allowOpaque := true` is required to get the body of theorems and
    -- opaque definitions; without it, `value?` returns `none` for them.
    let some value := info.value? (allowOpaque := true)
      | throwError "avoiding: declaration `{decl}` has no body to inspect"
    let used := collectConstNames value
    let mut violations : Array Name := #[]
    for av in avoidIdents do
      let avName := av.getId
      for u in used do
        if isNameSuffix avName u then
          violations := violations.push u
    unless violations.isEmpty do
      throwError "declaration '{decl}' uses forbidden lemma(s): {violations.toList}"
}

end CompanionHelper
