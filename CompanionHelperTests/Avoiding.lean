import CompanionHelper
import Mathlib.Algebra.Group.Basic
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Tactic.Linter.Style
import Aesop

/-!
Tests for `@[avoiding …]`. Uses `Nat.mul_one` as the stand-in forbidden lemma
for the simple cases; later tests pull in mathlib.
-/

namespace AvoidingTests

-- 1. Ordinary `theorem` without the attribute is unaffected.
theorem plain_no_attr (n : Nat) : n + 0 = n := by rfl

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
theorem dirty_simp (n : Nat) : n * 1 = n := by simp [Nat.mul_one]

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
error: declaration 'AvoidingTests.dirty_simp_default' uses forbidden lemma(s): [Nat.mul_one]
-/
#guard_msgs in
@[avoiding Nat.mul_one]
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

-- 10. KNOWN LIMITATION: `grind` and `@[grind =]` lemmas. `min_def` is
-- tagged `@[grind =]` and grind genuinely uses it to close `min a b = a`
-- from `a ≤ b`. But grind packages its proof inside an auto-generated
-- helper `<thm>._proof_1_1`, and our shallow check sees only the helper's
-- name in the top-level proof term. The forbidden `min_def` reference is
-- one level deeper. Expected to compile cleanly.
@[avoiding min_def]
theorem grind_min_def_not_caught {α : Type*} [LinearOrder α] (a b : α) (h : a ≤ b) :
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

end AvoidingTests
