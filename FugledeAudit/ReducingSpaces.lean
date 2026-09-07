import FugledeAudit.ResidualCompression

set_option autoImplicit false

/-!
# Constructed common reducing spaces

The spaces below are sums of actual level/eigenspace intersections. Their
invariance is proved from these definitions, not included as an input.
-/

namespace FugledeAudit

open Module
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def globalEigenSpace {ι : Type*} (U : End ℂ E) (L : ι → Submodule ℂ E)
    (ω : ℂ) (q : ℕ) : Submodule ℂ E := ⨆ j, localEigenSpace U (L j) ω q

theorem linear_map_preserves_iSup
    {ι : Type*} (T : End ℂ E) (L : ι → Submodule ℂ E)
    (hL : ∀ j x, x ∈ L j → T x ∈ L j) :
    ∀ x, x ∈ ⨆ j, L j → T x ∈ ⨆ j, L j := by
  intro x hx
  refine Submodule.iSup_induction L (motive := fun y => T y ∈ ⨆ j, L j) hx ?_ ?_ ?_
  · intro j y hy
    exact Submodule.mem_iSup_of_mem j (hL j y hy)
  · simpa only [map_zero] using (⨆ j, L j).zero_mem
  · intro y z hy hz
    simpa only [map_add] using (⨆ j, L j).add_mem hy hz

theorem linear_map_preserves_pow
    (T : End ℂ E) (W : Submodule ℂ E)
    (hW : ∀ x, x ∈ W → T x ∈ W) : ∀ n x, x ∈ W → (T ^ n) x ∈ W := by
  intro n
  induction n with
  | zero => intro x hx; simpa using hx
  | succ n ih =>
    intro x hx
    rw [pow_succ']
    exact hW ((T ^ n) x) (ih x hx)

theorem local_eigen_space_le_level
    (U : End ℂ E) (L : Submodule ℂ E) (ω : ℂ) (q : ℕ) :
    localEigenSpace U L ω q ≤ L := by
  exact iSup_le fun _ => inf_le_left

theorem local_eigen_space_invariant
    (U : End ℂ E) (L : Submodule ℂ E) (ω : ℂ) (q : ℕ) :
    ∀ x, x ∈ localEigenSpace U L ω q → U x ∈ localEigenSpace U L ω q := by
  apply linear_map_preserves_iSup
  intro i x hx
  have he := End.mem_eigenspace_iff.mp hx.2
  rw [he]
  exact (L ⊓ U.eigenspace (ω ^ i.val)).smul_mem _ hx

theorem global_eigen_space_invariant
    {ι : Type*} (U : End ℂ E) (L : ι → Submodule ℂ E) (ω : ℂ) (q : ℕ) :
    ∀ x, x ∈ globalEigenSpace U L ω q → U x ∈ globalEigenSpace U L ω q := by
  exact linear_map_preserves_iSup U _ (fun j => local_eigen_space_invariant U (L j) ω q)

theorem finite_order_unitary_inverse_apply
    (U : E ≃ₗᵢ[ℂ] E) (q : ℕ) (hq : 0 < q) (hU : U.toLinearMap ^ q = 1) (v : E) :
    U.symm v = (U.toLinearMap ^ (q - 1)) v := by
  apply U.injective
  rw [U.apply_symm_apply]
  symm
  calc
    _ = (U.toLinearMap ^ ((q - 1) + 1)) v := by rw [pow_succ']; rfl
    _ = v := by rw [Nat.sub_add_cancel (by omega : 1 ≤ q), hU]; rfl

theorem finite_order_invariant_orthogonal
    (U : E ≃ₗᵢ[ℂ] E) (q : ℕ) (hq : 0 < q) (hU : U.toLinearMap ^ q = 1)
    (W : Submodule ℂ E) (hW : ∀ x, x ∈ W → U x ∈ W) :
    ∀ x, x ∈ Wᗮ → U x ∈ Wᗮ := by
  intro x hx w hw
  have hwinv : U.symm w ∈ W := by
    rw [finite_order_unitary_inverse_apply U q hq hU]
    exact linear_map_preserves_pow U.toLinearMap W hW _ w hw
  calc
    ⟪w, U x⟫_ℂ = ⟪U (U.symm w), U x⟫_ℂ := by rw [U.apply_symm_apply]
    _ = ⟪U.symm w, x⟫_ℂ := U.inner_map_map _ _
    _ = 0 := hx _ hwinv

theorem global_residual_invariant
    {ι : Type*} (U : E ≃ₗᵢ[ℂ] E) (L : ι → Submodule ℂ E) (ω : ℂ)
    (q : ℕ) (hq : 0 < q) (hU : U.toLinearMap ^ q = 1) :
    ∀ x, x ∈ (globalEigenSpace U.toLinearMap L ω q)ᗮ →
      U x ∈ (globalEigenSpace U.toLinearMap L ω q)ᗮ := by
  exact finite_order_invariant_orthogonal U q hq hU _
    (global_eigen_space_invariant U.toLinearMap L ω q)

section Projections

variable [FiniteDimensional ℂ E]

theorem level_projection_preserves_global_eigen_space
    {ι : Type*} (U : End ℂ E) (L : ι → Submodule ℂ E) (ω : ℂ) (q : ℕ)
    (horth : Pairwise fun j k => (L j).IsOrtho (L k)) (j : ι) :
    ∀ x, x ∈ globalEigenSpace U L ω q →
      (L j).starProjection x ∈ globalEigenSpace U L ω q := by
  intro x hx
  refine Submodule.iSup_induction (fun k => localEigenSpace U (L k) ω q)
    (motive := fun y => (L j).starProjection y ∈ globalEigenSpace U L ω q) hx ?_ ?_ ?_
  · intro k y hy
    have hyL := local_eigen_space_le_level U (L k) ω q hy
    by_cases hjk : j = k
    · subst k
      rw [(L j).starProjection_eq_self_iff.mpr hyL]
      exact Submodule.mem_iSup_of_mem j hy
    · rw [(L j).starProjection_apply_eq_zero_iff.mpr ((horth (Ne.symm hjk)).le hyL)]
      exact (globalEigenSpace U L ω q).zero_mem
  · simpa only [map_zero] using (globalEigenSpace U L ω q).zero_mem
  · intro y z hy hz
    simpa only [map_add] using (globalEigenSpace U L ω q).add_mem hy hz

omit [FiniteDimensional ℂ E] in
theorem symmetric_map_preserves_orthogonal
    (T : End ℂ E) (hT : T.IsSymmetric) (W : Submodule ℂ E)
    (hW : ∀ x, x ∈ W → T x ∈ W) : ∀ x, x ∈ Wᗮ → T x ∈ Wᗮ := by
  intro x hx y hy
  rw [← hT y x]
  exact hx _ (hW y hy)

theorem level_projection_preserves_global_residual
    {ι : Type*} (U : End ℂ E) (L : ι → Submodule ℂ E) (ω : ℂ) (q : ℕ)
    (horth : Pairwise fun j k => (L j).IsOrtho (L k)) (j : ι) :
    ∀ x, x ∈ (globalEigenSpace U L ω q)ᗮ →
      (L j).starProjection x ∈ (globalEigenSpace U L ω q)ᗮ := by
  exact symmetric_map_preserves_orthogonal (L j).starProjection.toLinearMap
    (L j).starProjection_isSymmetric _
    (level_projection_preserves_global_eigen_space U L ω q horth j)

omit [FiniteDimensional ℂ E] in
/-- The locally defined residual space is exactly its level's part of the
global orthogonal complement. No level decomposition is asserted by fiat. -/
theorem local_residual_eq_level_inf_global
    {ι : Type*} (U : End ℂ E) (L : ι → Submodule ℂ E) (ω : ℂ) (q : ℕ)
    (horth : Pairwise fun j k => (L j).IsOrtho (L k)) (j : ι) :
    localResidual U (L j) ω q = L j ⊓ (globalEigenSpace U L ω q)ᗮ := by
  ext v
  constructor
  · intro hv
    refine ⟨hv.1, ?_⟩
    intro w hw
    refine Submodule.iSup_induction (fun k => localEigenSpace U (L k) ω q)
      (motive := fun z => ⟪z, v⟫_ℂ = 0) hw ?_ ?_ ?_
    · intro k z hz
      by_cases hkj : k = j
      · subst k; exact hv.2 z hz
      · exact (horth hkj).inner_eq (local_eigen_space_le_level U (L k) ω q hz) hv.1
    · simp
    · intro y z hy hz
      simp only [inner_add_left, hy, hz, add_zero]
  · intro hv
    exact ⟨hv.1, fun w hw => hv.2 w (Submodule.mem_iSup_of_mem j hw)⟩

theorem projected_power_mem_local_residual
    {ι : Type*} (U : E ≃ₗᵢ[ℂ] E) (L : ι → Submodule ℂ E) (ω : ℂ)
    (q : ℕ) (hq : 0 < q) (hU : U.toLinearMap ^ q = 1)
    (horth : Pairwise fun j k => (L j).IsOrtho (L k))
    (n : ℕ) (j k : ι) (v : localResidual U.toLinearMap (L k) ω q) :
    (L j).starProjection ((U.toLinearMap ^ n) (v : E)) ∈
      localResidual U.toLinearMap (L j) ω q := by
  rw [local_residual_eq_level_inf_global U.toLinearMap L ω q horth j]
  refine ⟨(L j).starProjection_apply_mem _, ?_⟩
  apply level_projection_preserves_global_residual U.toLinearMap L ω q horth j
  apply linear_map_preserves_pow U.toLinearMap _
    (global_residual_invariant U L ω q hq hU) n
  have hv := (le_of_eq (local_residual_eq_level_inf_global U.toLinearMap L ω q horth k)) v.property
  exact hv.2

theorem nested_projection_eq_of_mem
    (K L : Submodule ℂ E) (hKL : K ≤ L) (v : E) (hv : L.starProjection v ∈ K) :
    K.starProjection v = L.starProjection v := by
  apply K.eq_starProjection_of_mem_orthogonal hv
  exact Submodule.orthogonal_le hKL (L.sub_starProjection_mem_orthogonal v)

end Projections

end FugledeAudit
