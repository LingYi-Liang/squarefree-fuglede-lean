import FugledeAudit.SpectralResidualChain

set_option autoImplicit false

namespace FugledeAudit

open Module

theorem standard_character_average (q : ℕ) [NeZero q] (hq : q.Prime) (d : ZMod q) :
    (q : ℂ)⁻¹ * ∑ r : Fin q, ZMod.stdAddChar d ^ r.val = if d = 0 then 1 else 0 := by
  classical
  by_cases hd : d = 0
  · simp [hd, NeZero.ne q]
  · rw [if_neg hd]
    have hz : ∑ r : Fin q, ZMod.stdAddChar d ^ r.val = 0 := by
      simpa only [Fin.sum_univ_eq_sum_range] using
        (standard_character_nonzero_primitive q hq d hd).geom_sum_eq_zero hq.one_lt
    rw [hz, mul_zero]

theorem phase_average_eq_coordinate_mask
    {ι : Type*} [Fintype ι] (q : ℕ) [NeZero q] (hq : q.Prime)
    (label : ι → ZMod q) (i : ZMod q) :
    averagedPowers (phaseMap label) q (fun r => ZMod.stdAddChar (-i) ^ r.val) =
      coordinateMask label i := by
  classical
  ext v a
  simp only [averagedPowers, LinearMap.smul_apply, LinearMap.sum_apply,
    WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul,
    phase_power_apply, coordinate_mask_apply]
  have hs : (∑ r : Fin q, ZMod.stdAddChar (-i) ^ r.val *
      (ZMod.stdAddChar (label a) ^ r.val * v a)) =
      (∑ r : Fin q, ZMod.stdAddChar (label a - i) ^ r.val) * v a := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro r _
    rw [← mul_assoc, ← mul_pow, ← AddChar.map_add_eq_mul]
    rw [show -i + label a = label a - i by ring]
  rw [hs, ← mul_assoc, standard_character_average q hq]
  simp [sub_eq_zero, ite_mul]

theorem conjugated_average_apply
    {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E]
    (q : ℕ) [NeZero q] (F : EuclideanSpace ℂ ι ≃ₗᵢ[ℂ] E)
    (label : ι → ZMod q) (c : Fin q → ℂ) (v : E) :
    averagedPowers (conjugatedPhase F label).toLinearMap q c v =
      F (averagedPowers (phaseMap label) q c (F.symm v)) := by
  simp only [averagedPowers, LinearMap.smul_apply, LinearMap.sum_apply,
    map_smul, map_sum, conjugated_phase_power_apply]

noncomputable def spectralPhysicalProjection
    (q H : ℕ) [NeZero q] [NeZero H]
    (A Λ : Finset (ZMod (q * H))) (i : ZMod q) :
    End ℂ (EuclideanSpace ℂ Λ) :=
  (fourierForward A Λ).comp
    ((coordinateMask (fun a : A => (physicalCRT q H a.val).1) i).comp (fourierBackward A Λ))

/-- The averaged powers are identified with the original Fourier-conjugated
coordinate projector, including its actual normalization and indices. -/
theorem spectral_physical_projection_eq_average
    (q H : ℕ) [NeZero q] [NeZero H] (hq : q.Prime)
    (A Λ : Finset (ZMod (q * H))) (h : IsCyclicSpectralPair A Λ) (i : ZMod q) :
    spectralPhysicalProjection q H A Λ i =
      averagedPowers (spectralPrimeUnitary q H A Λ h).toLinearMap q
        (fun r => ZMod.stdAddChar (-i) ^ r.val) := by
  apply LinearMap.ext
  intro v
  rw [spectralPrimeUnitary, conjugated_average_apply, phase_average_eq_coordinate_mask q hq]
  rfl

theorem spectral_pair_residual_projector_eigenvector
    (q H : ℕ) [NeZero q] [NeZero H] (hq : q.Prime) (hq3 : 3 ≤ q)
    (hcop : Nat.Coprime q H)
    (A Λ : Finset (ZMod (q * H))) (h : IsCyclicSpectralPair A Λ) (i j : ZMod q)
    (v : localResidual (spectralPrimeUnitary q H A Λ h).toLinearMap
      (spectralPrimeLevels q H Λ j) (ZMod.stdAddChar (1 : ZMod q)) q) :
    (spectralPrimeLevels q H Λ j).starProjection
      (spectralPhysicalProjection q H A Λ i
        ((spectralPrimeLevels q H Λ j).starProjection (v : EuclideanSpace ℂ Λ))) =
      (q : ℂ)⁻¹ • (v : EuclideanSpace ℂ Λ) := by
  rw [spectral_physical_projection_eq_average q H hq A Λ h i]
  exact spectral_pair_residual_averaged_eigenvector q H hq hq3 hcop A Λ h _ (by simp) j v

end FugledeAudit
