import FugledeAudit.BlockAlgebra
import FugledeAudit.Integrality
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.NormNum

set_option autoImplicit false

/-!
# Ambient-support boundary

This file both composes the verified invariant-compression and integrality
steps, and checks an explicit counterexample to dropping invariance.
The counterexample is NOT a counterexample to the manuscript's theorem:
it is a test that the verification has not erased an essential hypothesis.
-/

namespace FugledeAudit

open Matrix

/-- The conditional local-to-ambient arithmetic chain. Its hypotheses expose
exactly what the still-unformalized regular decomposition must provide. -/
theorem dvd_of_invariant_compressed_gram_eigenvector
    {n k : Type*} [Fintype n] [DecidableEq n] [Fintype k]
    (M : Matrix n k ℂ) (H : ℕ) (hH : 0 < H)
    (hM : ∀ i j, M i j ^ H = 1)
    (K : Submodule ℂ (n → ℂ)) (R : (n → ℂ) →ₗ[ℂ] (n → ℂ))
    (hR : ∀ w ∈ K, R w = w)
    (hK : ∀ w ∈ K, (M * M.conjTranspose).mulVec w ∈ K)
    (m q : ℕ) (hq : q ≠ 0)
    (v : n → ℂ) (hvK : v ∈ K) (hv : v ≠ 0)
    (he : R ((M * M.conjTranspose).mulVec v) = ((m : ℂ) / (q : ℂ)) • v) :
    q ∣ m := by
  have heAmbient : (M * M.conjTranspose).mulVec v = ((m : ℂ) / (q : ℂ)) • v :=
    ambient_eigenvector_of_invariant_compression K R (M * M.conjTranspose).toLin'
      hR hK hvK he
  exact dvd_of_root_of_unity_gram_eigenvector M H hH hM m q hq v hv heAmbient

noncomputable def firewallProjection : Matrix (Fin 3) (Fin 3) ℂ := fun _ _ => 1 / 3
def firewallOperator : Matrix (Fin 3) (Fin 3) ℂ := !![1, 0, 0; 0, 0, 0; 0, 0, 0]
def firewallVector : Fin 3 → ℂ := ![1, 1, 1]

/-- An orthogonal compression of an integer matrix can have eigenvalue 1/3
without the ambient matrix having that eigenvector. Orthogonality of the
projection alone does not justify the integrality argument. -/
theorem compression_without_invariance_counterexample :
    firewallProjection * firewallProjection = firewallProjection ∧
    firewallProjection.conjTranspose = firewallProjection ∧
    firewallProjection.mulVec firewallVector = firewallVector ∧
    firewallVector ≠ 0 ∧
    firewallProjection.mulVec (firewallOperator.mulVec firewallVector) =
      ((1 : ℂ) / 3) • firewallVector ∧
    firewallOperator.mulVec firewallVector ≠ ((1 : ℂ) / 3) • firewallVector ∧
    (∀ i j, IsIntegral ℤ (firewallOperator i j)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext i j
    norm_num [firewallProjection, Matrix.mul_apply, Fin.sum_univ_succ]
  · ext i j
    norm_num [firewallProjection, Matrix.conjTranspose_apply]
  · ext i
    fin_cases i <;>
      norm_num [firewallProjection, firewallVector, Matrix.mulVec, dotProduct,
        Fin.sum_univ_succ]
  · intro h
    have h₀ := congrArg (fun v : Fin 3 → ℂ => v 0) h
    norm_num [firewallVector] at h₀
  · ext i
    fin_cases i <;>
      norm_num [firewallProjection, firewallOperator, firewallVector, Matrix.mulVec,
        dotProduct, Fin.sum_univ_succ]
  · intro h
    have h₀ := congrArg (fun v : Fin 3 → ℂ => v 0) h
    norm_num [firewallOperator, firewallVector, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ] at h₀
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp [firewallOperator, isIntegral_one, isIntegral_zero]

end FugledeAudit
