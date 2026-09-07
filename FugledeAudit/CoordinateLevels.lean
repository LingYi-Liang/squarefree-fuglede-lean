import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false

namespace FugledeAudit

open Module

variable {ι J : Type*} [Fintype ι] [DecidableEq J]

def coordinateLevel (label : ι → J) (j : J) : Submodule ℂ (EuclideanSpace ℂ ι) where
  carrier := {v | ∀ a, label a ≠ j → v a = 0}
  zero_mem' := by simp
  add_mem' := by intro x y hx hy a ha; simp [hx a ha, hy a ha]
  smul_mem' := by intro c x hx a ha; simp [hx a ha]

noncomputable def coordinateMask (label : ι → J) (j : J) : End ℂ (EuclideanSpace ℂ ι) where
  toFun v := WithLp.toLp 2 (fun a => if label a = j then v a else 0)
  map_add' x y := by ext a; by_cases h : label a = j <;> simp [h]
  map_smul' c x := by ext a; by_cases h : label a = j <;> simp [h]

omit [Fintype ι] in
theorem coordinate_mask_apply (label : ι → J) (j : J) (v : EuclideanSpace ℂ ι) (a : ι) :
    coordinateMask label j v a = if label a = j then v a else 0 := rfl

omit [Fintype ι] in
theorem coordinate_mask_mem (label : ι → J) (j : J) (v : EuclideanSpace ℂ ι) :
    coordinateMask label j v ∈ coordinateLevel label j := by
  intro a ha
  simp [coordinate_mask_apply, ha]

theorem coordinate_mask_sub_orthogonal (label : ι → J) (j : J) (v : EuclideanSpace ℂ ι) :
    v - coordinateMask label j v ∈ (coordinateLevel label j)ᗮ := by
  intro w hw
  rw [PiLp.inner_apply]
  apply Finset.sum_eq_zero
  intro a _
  by_cases ha : label a = j
  · simp [coordinate_mask_apply, ha]
  · simp [coordinate_mask_apply, ha, hw a ha]

theorem coordinate_mask_eq_projection (label : ι → J) (j : J) :
    (coordinateLevel label j).starProjection.toLinearMap = coordinateMask label j := by
  apply LinearMap.ext
  intro v
  exact Submodule.eq_starProjection_of_mem_orthogonal
    (coordinate_mask_mem label j v) (coordinate_mask_sub_orthogonal label j v)

theorem coordinate_levels_pairwise_orthogonal (label : ι → J) :
    Pairwise (fun j k => (coordinateLevel label j).IsOrtho (coordinateLevel label k)) := by
  intro j k hjk v hv w hw
  rw [PiLp.inner_apply]
  apply Finset.sum_eq_zero
  intro a _
  by_cases ha : label a = j
  · have hak : label a ≠ k := by simpa [ha] using hjk
    simp [hw a hak]
  · simp [hv a ha]

theorem coordinate_projections_sum [Fintype J] (label : ι → J) :
    ∑ j : J, (coordinateLevel label j).starProjection.toLinearMap = 1 := by
  classical
  simp_rw [coordinate_mask_eq_projection]
  ext v a
  simp [coordinate_mask_apply, eq_comm]

omit [Fintype ι] in
theorem coordinate_projection_idempotent (label : ι → J) (j : J) :
    coordinateMask label j * coordinateMask label j = coordinateMask label j := by
  ext v a
  by_cases ha : label a = j <;> simp [coordinate_mask_apply, ha]

omit [Fintype ι] in
theorem coordinate_projection_pairwise_zero (label : ι → J) (j k : J) (hjk : j ≠ k) :
    coordinateMask label j * coordinateMask label k = 0 := by
  ext v a
  by_cases ha : label a = j
  · simp [coordinate_mask_apply, ha, hjk]
  · simp [coordinate_mask_apply, ha]

end FugledeAudit
