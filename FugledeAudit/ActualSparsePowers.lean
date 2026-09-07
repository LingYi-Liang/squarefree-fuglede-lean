import FugledeAudit.ActualFourierZeros

set_option autoImplicit false

namespace FugledeAudit

open Matrix Module

noncomputable def spectralPrimeUnitary
    (q H : ℕ) [NeZero q] [NeZero H]
    (A Λ : Finset (ZMod (q * H))) (h : IsCyclicSpectralPair A Λ) :
    EuclideanSpace ℂ Λ ≃ₗᵢ[ℂ] EuclideanSpace ℂ Λ :=
  conjugatedPhase (spectralFourierUnitary A Λ h)
    (fun a : A => (physicalCRT q H a.val).1)

noncomputable def spectralPrimeLevels
    (q H : ℕ) [NeZero q] [NeZero H]
    (Λ : Finset (ZMod (q * H))) (j : ZMod q) :
    Submodule ℂ (EuclideanSpace ℂ Λ) :=
  coordinateLevel (fun ξ : Λ => (dualCRT q H ξ.val).1) j

noncomputable def spectralPhasePowerMatrix
    (q H : ℕ) [NeZero q] [NeZero H]
    (A Λ : Finset (ZMod (q * H))) (r : ℕ) : Matrix Λ Λ ℂ :=
  normalizedFourierMatrix A Λ *
    Matrix.diagonal (fun a : A => ZMod.stdAddChar (physicalCRT q H a.val).1 ^ r) *
    (normalizedFourierMatrix A Λ)ᴴ

theorem spectral_prime_power_matrix
    (q H : ℕ) [NeZero q] [NeZero H]
    (A Λ : Finset (ZMod (q * H))) (h : IsCyclicSpectralPair A Λ) (r : ℕ) :
    (spectralPrimeUnitary q H A Λ h).toLinearMap ^ r =
      (spectralPhasePowerMatrix q H A Λ r).toEuclideanLin := by
  classical
  apply LinearMap.ext
  intro v
  rw [spectralPrimeUnitary, conjugated_phase_power_apply]
  change fourierForward A Λ
    ((phaseMap (fun a : A => (physicalCRT q H a.val).1) ^ r) (fourierBackward A Λ v)) = _
  simp only [spectralPhasePowerMatrix, Matrix.toLpLin_mul_same, LinearMap.comp_apply]
  change fourierForward A Λ _ = fourierForward A Λ _
  congr 1
  ext a
  rw [phase_power_apply, Matrix.toLpLin_apply]
  simp [Matrix.mulVec_diagonal, fourierBackward, Matrix.toLpLin_apply]

theorem spectral_phase_power_entry
    (q H : ℕ) [NeZero q] [NeZero H]
    (A Λ : Finset (ZMod (q * H))) (r : ℕ) (ξ μ : Λ) :
    spectralPhasePowerMatrix q H A Λ r ξ μ =
      ((Real.sqrt (A.card : ℝ) : ℂ)⁻¹ * (Real.sqrt (A.card : ℝ) : ℂ)⁻¹) *
        ∑ a : A, ZMod.stdAddChar (physicalCRT q H a.val).1 ^ r *
          cyclicFourierEntry a.val (ξ.val - μ.val) := by
  classical
  rw [spectralPhasePowerMatrix, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal,
    Matrix.conjTranspose_apply, normalizedFourierMatrix, Matrix.smul_apply,
    restrictedFourierMatrix, smul_eq_mul, star_mul, star_inv₀,
    Complex.star_def, Complex.conj_ofReal]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [← fourier_entry_product_star]
  simp only [Complex.star_def]
  ring

theorem spectral_phase_power_entry_zero
    (q H : ℕ) [NeZero q] [NeZero H] (hq : q.Prime) (hcop : Nat.Coprime q H)
    (A Λ : Finset (ZMod (q * H))) (h : IsCyclicSpectralPair A Λ) (r : ℕ)
    (ξ μ : Λ)
    (hd : (dualCRT q H ξ.val).1 ≠ (dualCRT q H μ.val).1)
    (hr : (dualCRT q H μ.val).1 ≠ (dualCRT q H ξ.val).1 + (r : ZMod q)) :
    spectralPhasePowerMatrix q H A Λ r ξ μ = 0 := by
  rw [spectral_phase_power_entry,
    spectral_pair_weighted_fourier_zero q H hq hcop A Λ h ξ μ r hd hr, mul_zero]

theorem spectral_pair_sparse_powers
    (q H : ℕ) [NeZero q] [NeZero H] (hq : q.Prime) (hcop : Nat.Coprime q H)
    (A Λ : Finset (ZMod (q * H))) (h : IsCyclicSpectralPair A Λ)
    (r : ℕ) (j k : ZMod q) (hkj : k ≠ j) (hkr : k ≠ j + (r : ZMod q)) :
    (spectralPrimeLevels q H Λ j).starProjection.toLinearMap *
      (spectralPrimeUnitary q H A Λ h).toLinearMap ^ r *
      (spectralPrimeLevels q H Λ k).starProjection.toLinearMap = 0 := by
  classical
  rw [spectral_prime_power_matrix]
  simp only [spectralPrimeLevels, coordinate_mask_eq_projection]
  ext v ξ
  simp only [End.mul_apply, coordinate_mask_apply, LinearMap.zero_apply, PiLp.zero_apply]
  split_ifs with hξ
  · rw [Matrix.toLpLin_apply]
    change (∑ μ : Λ, spectralPhasePowerMatrix q H A Λ r ξ μ *
      (if (dualCRT q H μ.val).1 = k then v μ else 0)) = 0
    apply Finset.sum_eq_zero
    intro μ _
    split_ifs with hμ
    · rw [spectral_phase_power_entry_zero q H hq hcop A Λ h r ξ μ
        (by simpa [hξ, hμ] using hkj.symm) (by simpa [hξ, hμ] using hkr), zero_mul]
    · exact mul_zero _
  · rfl

end FugledeAudit
