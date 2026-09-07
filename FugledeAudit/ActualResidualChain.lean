import FugledeAudit.ResidualRestrictions

set_option autoImplicit false

/-!
# The residual-block chain from the actual sparse unitary

Unlike the earlier conditional chain, this theorem constructs its shift and
return maps, proves their identities, and derives their norm conditions. The
remaining external input is the sparse-power setup of Lemma 3.1.
-/

namespace FugledeAudit

open Module
open scoped InnerProductSpace

theorem actual_residual_diagonal_zero_and_unitary_shifts
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (U : E ≃ₗᵢ[ℂ] E) (q : ℕ) [NeZero q] (hq : 3 ≤ q)
    (ω : ℂ) (hω : IsPrimitiveRoot ω q) (hU : U.toLinearMap ^ q = 1)
    (L : ZMod q → Submodule ℂ E)
    (horth : Pairwise fun j k => (L j).IsOrtho (L k))
    (hsum : ∑ j, (L j).starProjection.toLinearMap = 1)
    (hsparse : ∀ r : ℕ, 1 ≤ r → r < q → ∀ j k : ZMod q,
      k ≠ j → k ≠ j + (r : ZMod q) →
      (L j).starProjection.toLinearMap * U.toLinearMap ^ r * (L k).starProjection.toLinearMap = 0) :
    (∀ j, unitaryCompression U (localResidual U.toLinearMap (L j) ω q) = 0) ∧
    (∀ j, Function.Bijective (residualPowerBlock U L ω q 1 j (j + 1)) ∧
      ∀ v, ‖residualPowerBlock U L ω q 1 j (j + 1) v‖ = ‖v‖) := by
  let Q : ZMod q → End ℂ E := fun j => (L j).starProjection.toLinearMap
  let D := fun j => unitaryCompression U (localResidual U.toLinearMap (L j) ω q)
  let S := fun j => residualPowerBlock U L ω q 1 j (j + 1)
  let T := fun j => residualPowerBlock U L ω q (q - 1) (j + 1) j
  have hqpos : 0 < q := by omega
  have hQ : ∀ j, Q j * Q j = Q j := by
    intro j; ext x
    exact (L j).starProjection_eq_self_iff.mpr ((L j).starProjection_apply_mem x)
  have hQo : ∀ j k, j ≠ k → Q j * Q k = 0 := by
    intro j k hjk; ext x
    exact (L j).starProjection_apply_eq_zero_iff.mpr
      ((horth (Ne.symm hjk)).le ((L k).starProjection_apply_mem x))
  have hrel := actual_projection_block_relations q hq Q hQ hQo hsum U.toLinearMap hU hsparse
  have hB := residual_power_block_coe_ambient U L ω q hqpos hU horth
  have hD (j : ZMod q) (v : localResidual U.toLinearMap (L j) ω q) :
      (D j v : E) = (Q j * U.toLinearMap * Q j) (v : E) := by
    change (unitaryCompression U _ v : E) = _
    rw [← residual_diagonal_eq_compression U L ω q j]
    simpa only [pow_one] using hB 1 j j v
  have hS (j : ZMod q) (v : localResidual U.toLinearMap (L (j + 1)) ω q) :
      (S j v : E) = (Q j * U.toLinearMap * Q (j + 1)) (v : E) := by
    simpa only [pow_one] using hB 1 j (j + 1) v
  refine constructed_residual_block_chain U q hq ω hω hU L S T ?_ ?_ ?_ ?_ ?_ ?_
  · intro j
    ext v
    change (T j (S j v) : E) = (v : E) - ((D (j + 1) ^ q) v : E)
    rw [hB (q - 1) (j + 1) j, hS,
      residual_diagonal_power_coe U L ω q hqpos hU horth q (j + 1)]
    have hr := congrArg (fun f : End ℂ E => f (v : E)) (hrel (j + 1)).1
    have hQv : Q (j + 1) (v : E) = (v : E) :=
      (L (j + 1)).starProjection_eq_self_iff.mpr v.property.1
    simp only [add_sub_cancel_right, LinearMap.add_apply, End.mul_apply, hQv] at hr
    apply eq_sub_iff_add_eq.mpr
    change (Q (j + 1) * U.toLinearMap ^ (q - 1) * Q j)
      ((Q j * U.toLinearMap * Q (j + 1)) (v : E)) +
      ((Q (j + 1) * U.toLinearMap * Q (j + 1)) ^ q) (v : E) = (v : E)
    simpa only [End.mul_apply, hQv, add_comm] using hr.symm
  · intro j
    ext v
    change (D j (S j v) : E) + (S j (D (j + 1) v) : E) = 0
    rw [hD, hS, hS, hD]
    simpa only [LinearMap.add_apply, End.mul_apply, LinearMap.zero_apply] using
      congrArg (fun f : End ℂ E => f (v : E)) (hrel j).2.1
  · intro j
    ext v
    change (D j (D j (S j v)) : E) + (D j (S j (D (j + 1) v)) : E) +
      (S j (D (j + 1) (D (j + 1) v)) : E) = 0
    simp only [hD, hS]
    simpa only [pow_two, LinearMap.add_apply, End.mul_apply, LinearMap.zero_apply] using
      congrArg (fun f : End ℂ E => f (v : E)) (hrel j).2.2
  · exact fun j v => residual_power_block_contraction U L ω q 1 j (j + 1) v
  · exact fun j v => residual_power_block_contraction U L ω q (q - 1) (j + 1) j v
  · intro j v
    change ‖v‖ ^ 2 = ‖(D (j + 1) v : E)‖ ^ 2 + ‖(S j v : E)‖ ^ 2
    have hQv : Q (j + 1) (v : E) = (v : E) :=
      (L (j + 1)).starProjection_eq_self_iff.mpr v.property.1
    have hsumv : ∑ k, Q k (U (v : E)) = U (v : E) := by
      have hsumQ : ∑ k, Q k = 1 := hsum
      simpa only [LinearMap.sum_apply, End.one_apply] using
        congrArg (fun f : End ℂ E => f (U (v : E))) hsumQ
    have hparts : ∑ k, Q k (U (v : E)) =
        Q (j + 1) (U (v : E)) + Q j (U (v : E)) := by
      apply Fintype.sum_eq_add (j + 1) j (cyclic_successor_ne q (by omega) j)
      intro k hk
      have hnext : j + 1 ≠ k + 1 := fun h => hk.2 (add_right_cancel h).symm
      have hz := hsparse 1 (by decide) (by omega) k (j + 1) (Ne.symm hk.1)
        (by simpa only [Nat.cast_one] using hnext)
      change Q k * U.toLinearMap ^ 1 * Q (j + 1) = 0 at hz
      change Q k (U.toLinearMap (v : E)) = 0
      simpa only [pow_one, End.mul_apply, hQv, LinearMap.zero_apply] using
        congrArg (fun f : End ℂ E => f (v : E)) hz
    have hDv : (D (j + 1) v : E) = Q (j + 1) (U (v : E)) := by
      rw [hD]; simp only [End.mul_apply, hQv]; rfl
    have hSv : (S j v : E) = Q j (U (v : E)) := by
      rw [hS]; simp only [End.mul_apply, hQv]; rfl
    have hsplit : U (v : E) = (D (j + 1) v : E) + (S j v : E) := by
      rw [hDv, hSv]
      exact hsumv.symm.trans hparts
    have hinner : ⟪(D (j + 1) v : E), (S j v : E)⟫_ℂ = 0 :=
      (horth (cyclic_successor_ne q (by omega) j)).inner_eq
        (D (j + 1) v).property.1 (S j v).property.1
    calc
      ‖v‖ ^ 2 = ‖U (v : E)‖ ^ 2 := by rw [U.norm_map]; rfl
      _ = ‖(D (j + 1) v : E) + (S j v : E)‖ ^ 2 := by rw [hsplit]
      _ = _ := by simpa only [pow_two] using
        norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ hinner

end FugledeAudit
