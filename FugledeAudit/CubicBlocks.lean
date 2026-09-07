import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.NoncommRing

set_option autoImplicit false

/-!
# Exact noncommutative block identities at q = 3

The entries may themselves be operators in any ring. These are symbolic
identities for all such entries, not numerical tests of selected matrices.
This file checks the exceptional exponent-3 step, not the entire regular
decomposition for arbitrary primes.
-/

namespace FugledeAudit

open Matrix

def cyclicThreeBlock {R : Type*} [Ring R] (D S : Fin 3 → R) : Matrix (Fin 3) (Fin 3) R :=
  !![D 0, S 0, 0; 0, D 1, S 1; S 2, 0, D 2]

theorem cyclic_three_square_shift {R : Type*} [Ring R] (D S : Fin 3 → R) :
    (cyclicThreeBlock D S ^ 2) 0 1 = D 0 * S 0 + S 0 * D 1 := by
  simp [pow_succ, cyclicThreeBlock, Matrix.mul_apply, Fin.sum_univ_succ]

theorem cyclic_three_cube_shift {R : Type*} [Ring R] (D S : Fin 3 → R) :
    (cyclicThreeBlock D S ^ 3) 0 1 =
      D 0 ^ 2 * S 0 + D 0 * S 0 * D 1 + S 0 * D 1 ^ 2 := by
  simp [pow_succ, cyclicThreeBlock, Matrix.mul_apply, Fin.sum_univ_succ]
  noncomm_ring

theorem cyclic_three_cube_diagonal {R : Type*} [Ring R] (D S : Fin 3 → R) :
    (cyclicThreeBlock D S ^ 3) 0 0 = D 0 ^ 3 + S 0 * S 1 * S 2 := by
  simp [pow_succ, cyclicThreeBlock, Matrix.mul_apply, Fin.sum_univ_succ]

/-- At q = 3, the missing sparse-power assertion at exponent 3 is supplied
by U³ = I itself. No r < q hypothesis is smuggled into this step. -/
theorem cubic_identity_forces_shift_relation {R : Type*} [Ring R]
    (D S : Fin 3 → R) (hU : cyclicThreeBlock D S ^ 3 = 1) :
    D 0 ^ 2 * S 0 + D 0 * S 0 * D 1 + S 0 * D 1 ^ 2 = 0 := by
  rw [← cyclic_three_cube_shift, hU]
  simp

end FugledeAudit
