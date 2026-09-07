import FugledeAudit.FourierUnitary
import FugledeAudit.CoordinateLevels

set_option autoImplicit false

namespace FugledeAudit

open Module

variable {ι : Type*} [Fintype ι] {q : ℕ} [NeZero q]

theorem standard_character_unit (x : ZMod q) :
    star (ZMod.stdAddChar x) * ZMod.stdAddChar x = 1 := by
  rw [std_character_star, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]

noncomputable def phaseMap (label : ι → ZMod q) : End ℂ (EuclideanSpace ℂ ι) where
  toFun v := WithLp.toLp 2 (fun a => ZMod.stdAddChar (label a) * v a)
  map_add' x y := by ext a; simp [mul_add]
  map_smul' c x := by ext a; simp [mul_left_comm]

omit [Fintype ι] in
theorem phase_map_apply (label : ι → ZMod q) (v : EuclideanSpace ℂ ι) (a : ι) :
    phaseMap label v a = ZMod.stdAddChar (label a) * v a := rfl

omit [Fintype ι] in
theorem phase_map_inverse (label : ι → ZMod q) (v : EuclideanSpace ℂ ι) :
    phaseMap (-label) (phaseMap label v) = v := by
  ext a
  simp only [phase_map_apply, Pi.neg_apply, ← std_character_star, ← mul_assoc,
    standard_character_unit, one_mul]

theorem phase_map_inner (label : ι → ZMod q) (x y : EuclideanSpace ℂ ι) :
    inner ℂ (phaseMap label x) (phaseMap label y) = inner ℂ x y := by
  simp only [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro a _
  change inner ℂ (ZMod.stdAddChar (label a) • x a) (ZMod.stdAddChar (label a) • y a) = _
  rw [inner_smul_left, inner_smul_right, ← mul_assoc]
  change (star (ZMod.stdAddChar (label a)) * ZMod.stdAddChar (label a)) * inner ℂ (x a) (y a) = _
  rw [standard_character_unit, one_mul]

noncomputable def phaseUnitary (label : ι → ZMod q) :
    EuclideanSpace ℂ ι ≃ₗᵢ[ℂ] EuclideanSpace ℂ ι :=
  let e : EuclideanSpace ℂ ι ≃ₗ[ℂ] EuclideanSpace ℂ ι :=
    { phaseMap label with
      invFun := phaseMap (-label)
      left_inv := phase_map_inverse label
      right_inv := fun v => by simpa using phase_map_inverse (-label) v }
  e.isometryOfInner (phase_map_inner label)

omit [Fintype ι] in
theorem phase_power_apply (label : ι → ZMod q) (n : ℕ) (v : EuclideanSpace ℂ ι) (a : ι) :
    (phaseMap label ^ n) v a = ZMod.stdAddChar (label a) ^ n * v a := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', End.mul_apply, phase_map_apply, ih, pow_succ']
    exact (mul_assoc _ _ _).symm

omit [Fintype ι] in
theorem phase_power_order (label : ι → ZMod q) : phaseMap label ^ q = 1 := by
  ext v a
  rw [phase_power_apply, ← AddChar.map_nsmul_eq_pow]
  simp

theorem standard_character_primitive_root : IsPrimitiveRoot (ZMod.stdAddChar (1 : ZMod q)) q := by
  refine ⟨by simp [← AddChar.map_nsmul_eq_pow], ?_⟩
  intro n hn
  have he : ZMod.stdAddChar (n : ZMod q) = ZMod.stdAddChar (0 : ZMod q) := by
    simpa [← AddChar.map_nsmul_eq_pow] using hn
  exact (ZMod.natCast_eq_zero_iff n q).mp (ZMod.injective_stdAddChar he)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

noncomputable def conjugatedPhase (F : EuclideanSpace ℂ ι ≃ₗᵢ[ℂ] E)
    (label : ι → ZMod q) : E ≃ₗᵢ[ℂ] E :=
  (F.symm.trans (phaseUnitary label)).trans F

theorem conjugated_phase_apply (F : EuclideanSpace ℂ ι ≃ₗᵢ[ℂ] E)
    (label : ι → ZMod q) (v : E) :
    conjugatedPhase F label v = F (phaseMap label (F.symm v)) := rfl

theorem conjugated_phase_power_apply (F : EuclideanSpace ℂ ι ≃ₗᵢ[ℂ] E)
    (label : ι → ZMod q) (n : ℕ) (v : E) :
    ((conjugatedPhase F label).toLinearMap ^ n) v = F ((phaseMap label ^ n) (F.symm v)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', End.mul_apply, ih]
    change conjugatedPhase F label (F ((phaseMap label ^ n) (F.symm v))) = _
    rw [conjugated_phase_apply, F.symm_apply_apply, pow_succ', End.mul_apply]

theorem conjugated_phase_order (F : EuclideanSpace ℂ ι ≃ₗᵢ[ℂ] E)
    (label : ι → ZMod q) : (conjugatedPhase F label).toLinearMap ^ q = 1 := by
  apply LinearMap.ext
  intro v
  rw [conjugated_phase_power_apply, phase_power_order]
  simp

end FugledeAudit
