import FugledeAudit.ActualResidualChain

set_option autoImplicit false

/-! # Actual averaged-power eigenvectors on the constructed residual spaces -/

namespace FugledeAudit

open Module

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

noncomputable def averagedPowers (U : End ℂ E) (q : ℕ) (c : Fin q → ℂ) : End ℂ E :=
  (q : ℂ)⁻¹ • ∑ r : Fin q, c r • U ^ r.val

theorem actual_residual_short_return_zero
    (U : E ≃ₗᵢ[ℂ] E) (q : ℕ) [NeZero q] (hq : 3 ≤ q)
    (ω : ℂ) (hω : IsPrimitiveRoot ω q) (hU : U.toLinearMap ^ q = 1)
    (L : ZMod q → Submodule ℂ E)
    (horth : Pairwise fun j k => (L j).IsOrtho (L k))
    (hsum : ∑ j, (L j).starProjection.toLinearMap = 1)
    (hsparse : ∀ r : ℕ, 1 ≤ r → r < q → ∀ j k : ZMod q,
      k ≠ j → k ≠ j + (r : ZMod q) →
      (L j).starProjection.toLinearMap * U.toLinearMap ^ r * (L k).starProjection.toLinearMap = 0)
    (n : ℕ) (hn : 0 < n) (hnq : n < q) (j : ZMod q)
    (v : localResidual U.toLinearMap (L j) ω q) :
    (L j).starProjection ((U.toLinearMap ^ n) (v : E)) = 0 := by
  let Q := fun j => (L j).starProjection.toLinearMap
  have hQ : ∀ j, Q j * Q j = Q j := by
    intro j; ext x
    exact (L j).starProjection_eq_self_iff.mpr ((L j).starProjection_apply_mem x)
  have hs : ∀ j k, k ≠ j → k ≠ j + 1 → Q j * U.toLinearMap * Q k = 0 := by
    intro j k h1 h2
    simpa only [pow_one] using hsparse 1 (by decide) (by omega) j k h1
      (by simpa only [Nat.cast_one] using h2)
  have h := actual_projection_short_diagonal q (by omega) Q hQ hsum U.toLinearMap hs n hn hnq j
  have hD := (actual_residual_diagonal_zero_and_unitary_shifts U q hq ω hω hU L horth hsum hsparse).1 j
  have hp := residual_diagonal_power_coe U L ω q (by omega) hU horth n j v
  rw [hD, zero_pow hn.ne'] at hp
  have hQv : Q j (v : E) = (v : E) := (L j).starProjection_eq_self_iff.mpr v.property.1
  have he := congrArg (fun f : End ℂ E => f (v : E)) h
  rw [← hp] at he
  change Q j ((U.toLinearMap ^ n) (v : E)) = 0
  simpa only [End.mul_apply, hQv, LinearMap.zero_apply, Submodule.coe_zero] using he

/-- This is an ambient equality for every actual residual vector, not merely
an eigenvalue of an abstract compression. The coefficient condition c(0)=1 is
the only condition on the spectral-projector coefficients used at this step. -/
theorem actual_residual_averaged_power_eigenvector
    (U : E ≃ₗᵢ[ℂ] E) (q : ℕ) [NeZero q] (hq : 3 ≤ q)
    (ω : ℂ) (hω : IsPrimitiveRoot ω q) (hU : U.toLinearMap ^ q = 1)
    (L : ZMod q → Submodule ℂ E)
    (horth : Pairwise fun j k => (L j).IsOrtho (L k))
    (hsum : ∑ j, (L j).starProjection.toLinearMap = 1)
    (hsparse : ∀ r : ℕ, 1 ≤ r → r < q → ∀ j k : ZMod q,
      k ≠ j → k ≠ j + (r : ZMod q) →
      (L j).starProjection.toLinearMap * U.toLinearMap ^ r * (L k).starProjection.toLinearMap = 0)
    (c : Fin q → ℂ) (hc : c 0 = 1) (j : ZMod q)
    (v : localResidual U.toLinearMap (L j) ω q) :
    (L j).starProjection (averagedPowers U.toLinearMap q c ((L j).starProjection (v : E))) =
      (q : ℂ)⁻¹ • (v : E) := by
  rw [(L j).starProjection_eq_self_iff.mpr v.property.1]
  simp only [averagedPowers, LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
  rw [Finset.sum_eq_single (0 : Fin q)]
  · simp only [Fin.val_zero, pow_zero, End.one_apply, hc, one_smul,
      (L j).starProjection_eq_self_iff.mpr v.property.1]
  · intro r _ hr
    have hrpos : 0 < r.val := by
      have hrne : r.val ≠ 0 := fun h => hr (Fin.ext h)
      omega
    rw [actual_residual_short_return_zero U q hq ω hω hU L horth hsum hsparse
      r.val hrpos r.isLt j v, smul_zero]
  · simp

end FugledeAudit
