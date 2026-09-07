import FugledeAudit.ActualCommutation

set_option autoImplicit false

namespace FugledeAudit

open Matrix

noncomputable def spectralPhysicalProjectionMatrix
    (q H : ℕ) [NeZero q] [NeZero H]
    (A Λ : Finset (ZMod (q * H))) (i : ZMod q) : Matrix Λ Λ ℂ :=
  normalizedFourierMatrix A Λ *
    coordinateMaskMatrix (fun a : A => (physicalCRT q H a.val).1) i *
    (normalizedFourierMatrix A Λ)ᴴ

theorem physical_projection_matrix_to_linear_map
    (q H : ℕ) [NeZero q] [NeZero H]
    (A Λ : Finset (ZMod (q * H))) (i : ZMod q) :
    (spectralPhysicalProjectionMatrix q H A Λ i).toEuclideanLin =
      spectralPhysicalProjection q H A Λ i := by
  classical
  simp only [spectralPhysicalProjectionMatrix, Matrix.toLpLin_mul_same,
    coordinate_mask_matrix_to_linear_map, spectralPhysicalProjection, fourierForward, fourierBackward]
  rfl

theorem physical_projection_matrix_entry
    (q H : ℕ) [NeZero q] [NeZero H]
    (A Λ : Finset (ZMod (q * H))) (i : ZMod q) (ξ μ : Λ) :
    spectralPhysicalProjectionMatrix q H A Λ i ξ μ =
      ((Real.sqrt (A.card : ℝ) : ℂ)⁻¹ * (Real.sqrt (A.card : ℝ) : ℂ)⁻¹) *
        ∑ a : A, if (physicalCRT q H a.val).1 = i then
          cyclicFourierEntry a.val (ξ.val - μ.val) else 0 := by
  classical
  rw [spectralPhysicalProjectionMatrix, Matrix.mul_apply]
  simp only [coordinateMaskMatrix, Matrix.mul_diagonal, Matrix.conjTranspose_apply,
    normalizedFourierMatrix, Matrix.smul_apply, restrictedFourierMatrix,
    smul_eq_mul, star_mul, star_inv₀, Complex.star_def, Complex.conj_ofReal]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs
  · rw [← fourier_entry_product_star]
    simp only [Complex.star_def]
    ring
  · simp

theorem spectral_pair_classwise_original_zero
    (q H : ℕ) [NeZero q] [NeZero H] (hq : q.Prime) (hq3 : 3 ≤ q)
    (hcop : Nat.Coprime q H)
    (A Λ : Finset (ZMod (q * H))) (h : IsCyclicSpectralPair A Λ)
    (hnd : ¬q ∣ A.card) (i : ZMod q) (ξ μ : Λ)
    (hξμ : (dualCRT q H ξ.val).1 ≠ (dualCRT q H μ.val).1) :
    (∑ a : A, if (physicalCRT q H a.val).1 = i then
      cyclicFourierEntry a.val (ξ.val - μ.val) else 0) = 0 := by
  classical
  let Q := coordinateMaskMatrix (fun ν : Λ => (dualCRT q H ν.val).1) (dualCRT q H ξ.val).1
  let P := spectralPhysicalProjectionMatrix q H A Λ i
  have hc : Q * P = P * Q := by
    apply (Matrix.toLpLin 2 2).injective
    simpa only [Module.End.mul_eq_comp, Matrix.toLpLin_mul_same, Q, P,
      coordinate_mask_matrix_to_linear_map, physical_projection_matrix_to_linear_map,
      spectralPrimeLevels, coordinate_mask_eq_projection]
      using spectral_pair_projections_commute q H hq hq3 hcop A Λ h hnd i
        (dualCRT q H ξ.val).1
  have he := congrArg (fun M : Matrix Λ Λ ℂ => M ξ μ) hc
  simp only [Q, P, coordinateMaskMatrix, Matrix.diagonal_mul, Matrix.mul_diagonal,
    if_true, if_neg hξμ.symm, one_mul, mul_zero] at he
  rw [physical_projection_matrix_entry] at he
  have hs : (Real.sqrt (A.card : ℝ) : ℂ) ≠ 0 := by
    have hp : 0 < (A.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr h.1
    exact_mod_cast (Real.sqrt_pos.mpr hp).ne'
  exact (mul_eq_zero.mp he).resolve_left (mul_ne_zero (inv_ne_zero hs) (inv_ne_zero hs))

theorem spectral_pair_classwise_cofactor_zero
    (q H : ℕ) [NeZero q] [NeZero H] (hq : q.Prime) (hq3 : 3 ≤ q)
    (hcop : Nat.Coprime q H)
    (A Λ : Finset (ZMod (q * H))) (h : IsCyclicSpectralPair A Λ)
    (hnd : ¬q ∣ A.card) (i : ZMod q) (ξ μ : Λ)
    (hξμ : (dualCRT q H ξ.val).1 ≠ (dualCRT q H μ.val).1) :
    (∑ a : A, if (physicalCRT q H a.val).1 = i then
      ZMod.stdAddChar ((physicalCRT q H a.val).2 *
        ((dualCRT q H ξ.val).2 - (dualCRT q H μ.val).2)) else 0) = 0 := by
  classical
  have hz := spectral_pair_classwise_original_zero q H hq hq3 hcop A Λ h hnd i ξ μ hξμ
  let z := ZMod.stdAddChar (i * ((dualCRT q H ξ.val).1 - (dualCRT q H μ.val).1))
  have he : (∑ a : A, if (physicalCRT q H a.val).1 = i then
      cyclicFourierEntry a.val (ξ.val - μ.val) else 0) =
      z * ∑ a : A, if (physicalCRT q H a.val).1 = i then
        ZMod.stdAddChar ((physicalCRT q H a.val).2 *
          ((dualCRT q H ξ.val).2 - (dualCRT q H μ.val).2)) else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    split_ifs with ha
    · rw [cyclic_fourier_crt_pairing q H hcop, dual_crt_sub]
      simp [ha, z]
    · exact (mul_zero z).symm
  rw [he] at hz
  apply (mul_eq_zero.mp hz).resolve_left
  intro hz0
  have hu := standard_character_unit (i * ((dualCRT q H ξ.val).1 - (dualCRT q H μ.val).1))
  change star z * z = 1 at hu
  simp [hz0] at hu

theorem spectral_pair_cofactor_zero
    (q H : ℕ) [NeZero q] [NeZero H] (hq : q.Prime) (hq3 : 3 ≤ q)
    (hcop : Nat.Coprime q H)
    (A Λ : Finset (ZMod (q * H))) (h : IsCyclicSpectralPair A Λ)
    (hnd : ¬q ∣ A.card) (ξ μ : Λ) (hξμ : ξ ≠ μ) :
    ∑ a : A, ZMod.stdAddChar ((physicalCRT q H a.val).2 *
      ((dualCRT q H ξ.val).2 - (dualCRT q H μ.val).2)) = 0 := by
  classical
  by_cases hd : (dualCRT q H ξ.val).1 = (dualCRT q H μ.val).1
  · have hv : ξ.val ≠ μ.val := fun he => hξμ (Subtype.ext he)
    have hz := h.2.2 ξ.val ξ.property μ.val μ.property hv
    rw [← Finset.sum_coe_sort] at hz
    simpa only [cyclic_fourier_crt_pairing q H hcop, dual_crt_sub,
      Prod.fst_sub, Prod.snd_sub, hd, sub_self, mul_zero,
      AddChar.map_zero_eq_one, one_mul] using hz
  · have hz : (∑ i : ZMod q, ∑ a : A, if (physicalCRT q H a.val).1 = i then
        ZMod.stdAddChar ((physicalCRT q H a.val).2 *
          ((dualCRT q H ξ.val).2 - (dualCRT q H μ.val).2)) else 0) = 0 :=
      Finset.sum_eq_zero fun i _ =>
        spectral_pair_classwise_cofactor_zero q H hq hq3 hcop A Λ h hnd i ξ μ hd
    rw [Finset.sum_comm] at hz
    simpa using hz

end FugledeAudit
