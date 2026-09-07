import FugledeAudit.ReducingSpaces
import FugledeAudit.SparseProjectionRelations
import FugledeAudit.ResidualBlockChain

set_option autoImplicit false

/-! # Actual operator blocks on the constructed residual spaces -/

namespace FugledeAudit

open Module

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

noncomputable def crossCompression (T : End ℂ E) (K L : Submodule ℂ E) : L →ₗ[ℂ] K :=
  K.orthogonalProjectionOnto.toLinearMap.comp (T.comp L.subtype)

noncomputable def residualPowerBlock
    {ι : Type*} (U : E ≃ₗᵢ[ℂ] E) (L : ι → Submodule ℂ E) (ω : ℂ) (q n : ℕ) (j k : ι) :
    localResidual U.toLinearMap (L k) ω q →ₗ[ℂ] localResidual U.toLinearMap (L j) ω q :=
  crossCompression (U.toLinearMap ^ n) (localResidual U.toLinearMap (L j) ω q)
    (localResidual U.toLinearMap (L k) ω q)

theorem residual_power_block_coe
    {ι : Type*} (U : E ≃ₗᵢ[ℂ] E) (L : ι → Submodule ℂ E) (ω : ℂ)
    (q : ℕ) (hq : 0 < q) (hU : U.toLinearMap ^ q = 1)
    (horth : Pairwise fun j k => (L j).IsOrtho (L k))
    (n : ℕ) (j k : ι) (v : localResidual U.toLinearMap (L k) ω q) :
    (residualPowerBlock U L ω q n j k v : E) =
      (L j).starProjection ((U.toLinearMap ^ n) (v : E)) := by
  change (localResidual U.toLinearMap (L j) ω q).starProjection
    ((U.toLinearMap ^ n) (v : E)) = _
  exact nested_projection_eq_of_mem _ (L j) inf_le_left _
    (projected_power_mem_local_residual U L ω q hq hU horth n j k v)

theorem residual_power_block_coe_ambient
    {ι : Type*} (U : E ≃ₗᵢ[ℂ] E) (L : ι → Submodule ℂ E) (ω : ℂ)
    (q : ℕ) (hq : 0 < q) (hU : U.toLinearMap ^ q = 1)
    (horth : Pairwise fun j k => (L j).IsOrtho (L k))
    (n : ℕ) (j k : ι) (v : localResidual U.toLinearMap (L k) ω q) :
    (residualPowerBlock U L ω q n j k v : E) =
      ((L j).starProjection.toLinearMap * U.toLinearMap ^ n *
        (L k).starProjection.toLinearMap) (v : E) := by
  rw [residual_power_block_coe U L ω q hq hU horth]
  change _ = (L j).starProjection ((U.toLinearMap ^ n) ((L k).starProjection (v : E)))
  rw [(L k).starProjection_eq_self_iff.mpr v.property.1]

theorem residual_diagonal_eq_compression
    {ι : Type*} (U : E ≃ₗᵢ[ℂ] E) (L : ι → Submodule ℂ E) (ω : ℂ) (q : ℕ) (j : ι) :
    residualPowerBlock U L ω q 1 j j =
      unitaryCompression U (localResidual U.toLinearMap (L j) ω q) := by
  simp only [residualPowerBlock, crossCompression, pow_one, unitaryCompression]

theorem residual_diagonal_power_coe
    {ι : Type*} (U : E ≃ₗᵢ[ℂ] E) (L : ι → Submodule ℂ E) (ω : ℂ)
    (q : ℕ) (hq : 0 < q) (hU : U.toLinearMap ^ q = 1)
    (horth : Pairwise fun j k => (L j).IsOrtho (L k))
    (n : ℕ) (j : ι) (v : localResidual U.toLinearMap (L j) ω q) :
    ((unitaryCompression U (localResidual U.toLinearMap (L j) ω q) ^ n) v : E) =
      (((L j).starProjection.toLinearMap * U.toLinearMap *
        (L j).starProjection.toLinearMap) ^ n) (v : E) := by
  have hD (w : localResidual U.toLinearMap (L j) ω q) :
      (unitaryCompression U (localResidual U.toLinearMap (L j) ω q) w : E) =
      ((L j).starProjection.toLinearMap * U.toLinearMap *
        (L j).starProjection.toLinearMap) (w : E) := by
    rw [← residual_diagonal_eq_compression U L ω q j]
    simpa only [pow_one] using residual_power_block_coe_ambient U L ω q hq hU horth 1 j j w
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [pow_succ', End.mul_apply, hD, ih]

omit [FiniteDimensional ℂ E] in
theorem unitary_power_preserves_norm (U : E ≃ₗᵢ[ℂ] E) (n : ℕ) (v : E) :
    ‖(U.toLinearMap ^ n) v‖ = ‖v‖ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ']
    exact (U.norm_map _).trans ih

theorem residual_power_block_contraction
    {ι : Type*} (U : E ≃ₗᵢ[ℂ] E) (L : ι → Submodule ℂ E) (ω : ℂ)
    (q n : ℕ) (j k : ι) (v : localResidual U.toLinearMap (L k) ω q) :
    ‖residualPowerBlock U L ω q n j k v‖ ≤ ‖v‖ := by
  calc
    _ ≤ ‖(U.toLinearMap ^ n) (v : E)‖ :=
      (localResidual U.toLinearMap (L j) ω q).norm_orthogonalProjectionOnto_apply_le _
    _ = _ := unitary_power_preserves_norm U n (v : E)

end FugledeAudit
