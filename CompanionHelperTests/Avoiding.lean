module

public import CompanionHelper
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Tactic.Linter.Style
public import Mathlib.Basic.Complex.Basic
public import Aesop

/-!
Tests for `@[avoiding …]`. Uses `Nat.mul_one` as the stand-in forbidden lemma
for the simple cases; later tests pull in mathlib.
-/

namespace AvoidingTests

-- 1. Ordinary `theorem` without the attribute is unaffected.
theorem plain_no_attr (n : Nat) : n + 0 = n :=  by rfl

-- 2. Attribute attached, proof is clean → succeeds.
@[avoiding Nat.mul_one]
theorem clean_with_attr (n : Nat) : n + 0 = n := by rfl

-- 3. `exact` of forbidden lemma → error.
/--
error: declaration 'AvoidingTests.dirty_direct' uses forbidden lemma(s): [Nat.mul_one]
-/
#guard_msgs in
@[avoiding Nat.mul_one]
theorem dirty_direct (n : Nat) : n * 1 = n := by exact Nat.mul_one n

-- 4. `simp [forbidden]` reaches the lemma indirectly → error.
/--
error: declaration 'AvoidingTests.dirty_simp' uses forbidden lemma(s): [Nat.mul_one]
-/
#guard_msgs in
@[avoiding Nat.mul_one]
theorem dirty_simp (n : Nat) : n * 1 = n := by simp only [Nat.mul_one]

-- 5. Multiple listed, only one used → error names just the used one.
/--
error: declaration 'AvoidingTests.dirty_one_of_many' uses forbidden lemma(s): [Nat.mul_one]
-/
#guard_msgs in
@[avoiding Nat.mul_one, Nat.add_zero]
theorem dirty_one_of_many (n : Nat) : n * 1 = n := by exact Nat.mul_one n

-- 6. Stacks with other attributes.
@[simp, avoiding Nat.mul_one]
theorem stacks_clean (n : Nat) : n + 0 = n := by rfl

-- 7. Bare `simp` (no explicit lemma list) reaches the forbidden lemma through
-- its default simp set → caught. `Nat.mul_one` is `@[simp]` in core Lean.
/--
error: declaration 'AvoidingTests.dirty_simp_default' uses forbidden lemma(s): [mul_one]
-/
#guard_msgs in
@[avoiding mul_one]
theorem dirty_simp_default (n : Nat) : n * 1 = n := by simp

-- 8. Mathlib-flavored: `(a * b)⁻¹ = b⁻¹ * a⁻¹` in any group. The textbook
-- exercise; the "natural cheat" is to find `mul_inv_rev` in mathlib and
-- `exact` it. Forbidding it and closing with bare `simp` catches the
-- accidental cheat: simp picks `mul_inv_rev` from its default set and the
-- proof term references it directly.
/--
error: declaration 'AvoidingTests.simp_mathlib_dirty' uses forbidden lemma(s): [mul_inv_rev]
-/
#guard_msgs in
@[avoiding mul_inv_rev]
theorem simp_mathlib_dirty {G : Type*} [Group G] (a b : G) :
    (a * b)⁻¹ = b⁻¹ * a⁻¹ := by simp

-- 9. Same goal, closed with `aesop`. Aesop calls simp under the hood, so
-- the proof term still references `mul_inv_rev` and the check fires.
/--
error: declaration 'AvoidingTests.aesop_mathlib_dirty' uses forbidden lemma(s): [mul_inv_rev]
-/
#guard_msgs in
@[avoiding mul_inv_rev]
theorem aesop_mathlib_dirty {G : Type*} [Group G] (a b : G) :
    (a * b)⁻¹ = b⁻¹ * a⁻¹ := by aesop

-- 10. `grind` and `@[grind =]` lemmas. `min_def` is tagged `@[grind =]` and
-- grind genuinely uses it to close `min a b = a` from `a ≤ b`. The proof is
-- bundled inside an auto-generated helper `<thm>._proof_1_1`; the recursive
-- collector follows helpers under the declaration's namespace and finds the
-- buried `min_def` reference.
/--
error: declaration 'AvoidingTests.grind_min_def_caught' uses forbidden lemma(s): [min_def]
-/
#guard_msgs in
@[avoiding min_def]
theorem grind_min_def_caught {α : Type*} [LinearOrder α] (a b : α) (h : a ≤ b) :
    min a b = a := by grind

-- 11. The default state of a companion exercise: stubbed with `sorry`.
-- The proof term references only `sorryAx`, which is not in the avoid
-- list, so the check is silent. Compiles cleanly with the standard
-- "declaration uses 'sorry'" warning.
@[avoiding Nat.mul_one]
theorem sorry_is_silent (n : Nat) : n * 1 = n := by sorry

-- 12. `open Foo` + unqualified avoid name. Caught by suffix matching:
-- `helper`'s component path (["helper"]) is a tail of `OpenTestNs.helper`'s
-- (["helper", "OpenTestNs"]).
namespace OpenTestNs
theorem helper (n : Nat) : n + 0 = n := Nat.add_zero n
end OpenTestNs

/--
error: declaration 'AvoidingTests.open_caught' uses forbidden lemma(s): [AvoidingTests.OpenTestNs.helper]
-/
#guard_msgs in
open OpenTestNs in
@[avoiding helper]
theorem open_caught (n : Nat) : n + 0 = n := by exact helper n

-- 13. Namespace-prefix matching. `@[avoiding Foo]` rejects every constant
-- whose name starts with `Foo.…`. Useful for blocking entire decision-
-- procedure namespaces (e.g., `Lean.Grind` for `grind`'s polynomial-ring
-- machinery) without enumerating every internal lemma.
namespace PrefixTestNs
theorem inner (n : Nat) : n + 0 = n := Nat.add_zero n
end PrefixTestNs

/--
error: declaration 'AvoidingTests.prefix_match_caught' uses forbidden lemma(s): [AvoidingTests.PrefixTestNs.inner]
-/
#guard_msgs in
@[avoiding AvoidingTests.PrefixTestNs]
theorem prefix_match_caught (n : Nat) : n + 0 = n := PrefixTestNs.inner n

-- 14. Instance-specific banning. `add_comm` is polymorphic over any
-- `AddCommMonoid`, so banning the lemma name itself would forbid it on
-- every type. Banning a single `Complex.*` instance isn't enough either:
-- different proof paths thread through different algebraic-structure
-- instances. `ring` resolves `add_comm`'s typeclass arg through
-- `Complex.instCommSemiring`; a direct `exact add_comm` resolves through
-- the `Complex.instAddCommMonoid` shortcut instance. Listing these covers the realistic paths, while uses
-- on ℝ (which carry `Real.*` instances) remain unaffected.

/--
error: declaration 'AvoidingTests.complex_add_comm_ban_ring' uses forbidden lemma(s): [Complex.instCommSemiring]
-/
#guard_msgs in
@[avoiding Complex.instCommSemiring, Complex.commRing, Complex.instField, Complex.instAddCommMonoid]
theorem complex_add_comm_ban_ring (α β : ℂ) : α + β = β + α := by ring

/--
error: declaration 'AvoidingTests.complex_add_comm_ban_grind' uses forbidden lemma(s): [Complex.instField]
-/
#guard_msgs in
@[avoiding Complex.instCommSemiring, Complex.commRing, Complex.instField, Complex.instAddCommMonoid]
theorem complex_add_comm_ban_grind (α β : ℂ) : α + β = β + α := by grind

/--
error: declaration 'AvoidingTests.complex_add_comm_ban_direct' uses forbidden lemma(s): [Complex.instAddCommMonoid]
-/
#guard_msgs in
@[avoiding Complex.instCommSemiring, Complex.commRing, Complex.instField, Complex.instAddCommMonoid]
theorem complex_add_comm_ban_direct (a b : ℂ) : a + b = b + a := by
  exact add_comm a b

@[avoiding Complex.instCommSemiring, Complex.commRing, Complex.instField, Complex.instAddCommMonoid]
theorem complex_add_comm_allow (a b : ℂ) : a + b = b + a := by
  apply Complex.ext
  · simp [Complex.add_re]; ring
  · simp [Complex.add_im]; ring

@[avoiding Complex.instCommSemiring, Complex.commRing, Complex.instField, Complex.instAddCommMonoid]
theorem real_add_comm_allow (a b : ℝ) : a + b = b + a := by
  exact add_comm a b

-- 15. Module system: `public` theorems have their bodies hidden in the
-- exported environment view; the check must still see them (direct and via
-- `grind`'s `_proof_*` helpers).
public section

/--
error: declaration 'AvoidingTests.public_dirty' uses forbidden lemma(s): [Nat.mul_one]
-/
#guard_msgs in
@[avoiding Nat.mul_one]
theorem public_dirty (n : Nat) : n * 1 = n := by
  exact Nat.mul_one n

/--
error: declaration 'AvoidingTests.public_grind_caught' uses forbidden lemma(s): [min_def]
-/
#guard_msgs in
@[avoiding min_def]
theorem public_grind_caught {α : Type*} [LinearOrder α] (a b : α) (h : a ≤ b) :
    min a b = a := by grind

end

-- 16. One-level cross-decl walk into user-namespace siblings. The naïve
-- cheat is to hide the forbidden lemma behind a one-line wrapper in the
-- same file. The walker follows one hop into any decl under the
-- attributed decl's root namespace (here, `AvoidingTests`), so the
-- wrapper is caught.
theorem wrapper_for_mul_one (n : Nat) : n * 1 = n := Nat.mul_one n

/--
error: declaration 'AvoidingTests.cross_decl_caught' uses forbidden lemma(s): [Nat.mul_one]
-/
#guard_msgs in
@[avoiding Nat.mul_one]
theorem cross_decl_caught (n : Nat) : n * 1 = n := wrapper_for_mul_one n

-- 17. Cross-decl walk is one-level only: a wrapper that itself calls
-- another wrapper is NOT followed past the first hop. Keeps the walker
-- bounded — full transitive walking would explode through mathlib.
theorem wrapper_lvl_2 (n : Nat) : n * 1 = n := Nat.mul_one n
theorem wrapper_lvl_1 (n : Nat) : n * 1 = n := wrapper_lvl_2 n

@[avoiding Nat.mul_one]
theorem cross_decl_two_hops_silent (n : Nat) : n * 1 = n := wrapper_lvl_1 n

-- 18. The one-hop check does not depend on visiting order: the proof
-- mentions two wrappers, one of which also mentions the other. The inner
-- wrapper must still be walked. (Two mirrored pairs so that both name
-- orders are exercised.)
theorem ord_inner_a (n : Nat) : n * 1 = n := Nat.mul_one n
theorem ord_outer_a (n : Nat) : n * 1 = n ∧ True := ⟨ord_inner_a n, trivial⟩

/--
error: declaration 'AvoidingTests.ord_caught_a' uses forbidden lemma(s): [Nat.mul_one]
-/
#guard_msgs in
@[avoiding Nat.mul_one]
theorem ord_caught_a (n : Nat) : n * 1 = n := by
  have _h := ord_outer_a n
  exact ord_inner_a n

theorem ord_outer_b (n : Nat) : n * 1 = n := Nat.mul_one n
theorem ord_inner_b (n : Nat) : n * 1 = n ∧ True := ⟨ord_outer_b n, trivial⟩

/--
error: declaration 'AvoidingTests.ord_caught_b' uses forbidden lemma(s): [Nat.mul_one]
-/
#guard_msgs in
@[avoiding Nat.mul_one]
theorem ord_caught_b (n : Nat) : n * 1 = n := by
  have _h := ord_inner_b n
  exact ord_outer_b n

end AvoidingTests

