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

The check follows three paths into the proof term:
- *direct* — names that appear in the immediate proof term (catches a literal
  `exact <forbidden>` or `simp [<forbidden>]`);
- *helper* — bodies of auto-generated helpers under the declaration's own
  namespace (e.g., `<decl>._proof_*` that `grind` / `decide` / `omega`
  synthesize to bury their certificate), followed to any depth;
- *one hop* — bodies (and helpers) of declarations under the same root
  namespace that the proof references directly. For a declaration
  `Foo.Bar.thm` this is everything under `Foo`, so a same-project wrapper
  `lemma helper := Nat.mul_one` is caught. Hops do not chain: a wrapper of a
  wrapper is not followed. Top-level declarations (no namespace) get no hop.

Library indirection (any other root namespace, e.g. mathlib) is NOT followed:
it would explode and false-positive via the algebra-hierarchy proof structure.

Forbidden names match by either suffix (so `mul_one` catches `Nat.mul_one`)
or prefix (so `Lean.Grind` catches `Lean.Grind.CommRing.…`, useful for
blocking entire decision-procedure namespaces).

Per the design doc, the goal is to catch *accidental* wins from `exact?`,
`simp`, default-tactic invocations like `grind`, etc. — not to be robust
against adversarial cheating. A wrapper in an unrelated namespace, or two
levels of wrappers, still defeats it.

Stacks with other attributes (`@[simp, avoiding …]`), works on any kind of
declaration, and can be removed by deleting one line.
-/

public meta section

namespace CompanionHelper

open Lean

/-- Set of `Expr.const` names appearing in `e`, plus (recursively) the bodies
of auto-generated helpers under `owner`'s own namespace — e.g. the
`owner._proof_1_1` that `grind`/`decide`/`omega` synthesize to hide their
proof. These are storage artifacts of the same declaration, so they are
walked unboundedly. Nothing else is followed. -/
private partial def collectWithHelpers (env : Environment) (owner : Name) (e : Expr)
    (visited : NameSet := {}) : NameSet := Id.run do
  let mut acc := e.foldConsts {} fun n s => s.insert n
  let mut visited := visited
  -- Compare user-facing names: in a `module`, a public theorem's helpers are
  -- private (`_private.<Module>.0.owner._proof_1`) while `owner` is not.
  let ownerU := privateToUserName owner
  for n in acc do
    if visited.contains n then continue
    visited := visited.insert n
    unless ownerU.isPrefixOf (privateToUserName n) do continue
    let some info := env.find? n | continue
    let some body := info.value? (allowOpaque := true) | continue
    for m in collectWithHelpers env owner body visited do
      acc := acc.insert m
      visited := visited.insert m
  return acc

/-- Names used by `decl`'s proof `value`:
- the constants of `value` and of `decl`'s own helpers (`collectWithHelpers`);
- when `userRoot? = some root`, additionally the constants (and helpers) of
  every declaration under `root` that `decl` references *directly* — one hop.
  This catches a same-project wrapper such as `lemma helper := Nat.mul_one`.
  Hops do not chain (a wrapper of a wrapper is not followed) and never enter
  other roots, so mathlib is not walked: that would explode and would
  false-positive via the algebra-hierarchy proof structure.

The hop targets are taken from the fixed set of direct references, so the
result does not depend on the order in which names are visited. -/
private def collectConstNamesDeep (env : Environment) (userRoot? : Option Name)
    (decl : Name) (value : Expr) : NameSet := Id.run do
  let direct := collectWithHelpers env decl value
  let some root := userRoot? | return direct
  let declU := privateToUserName decl
  let mut acc := direct
  for n in direct do
    let nU := privateToUserName n
    unless root.isPrefixOf nU && !declU.isPrefixOf nU do continue
    let some info := env.find? n | continue
    let some body := info.value? (allowOpaque := true) | continue
    for m in collectWithHelpers env n body do
      acc := acc.insert m
  return acc

/-- Component path of a `Name`, innermost first. E.g. `Nat.mul_one` → `["mul_one", "Nat"]`. -/
private partial def Name.componentsRevS : Name → List String
  | .anonymous => []
  | .str pre s => s :: Name.componentsRevS pre
  | .num pre i => s!"{i}" :: Name.componentsRevS pre

/-- Root namespace of `n`, i.e. its outermost `.str` component. `none` for
top-level names like `mul_one_ex` (no enclosing namespace). E.g.
`AvoidingTests.Foo.bar` → `some \`AvoidingTests`. -/
private def Name.root? (n : Name) : Option Name :=
  match (Name.componentsRevS (privateToUserName n)).reverse with
  | []     => none
  | [_]    => none
  | s :: _ => some (.str .anonymous s)

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
    let used := collectConstNamesDeep env (Name.root? decl) decl value
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
