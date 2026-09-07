import FugledeAudit.ActualSpectralProjectors
import FugledeAudit.Integrality

set_option autoImplicit false

namespace FugledeAudit

open Matrix Module

noncomputable def coordinateMaskMatrix {ι J : Type*} (label : ι → J) (i : J) : Matrix ι ι ℂ := by
  classical
  exact Matrix.diagonal (fun a => if label a = i then 1 else 0)

theorem coordinate_mask_matrix_to_linear_map
    {ι J : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq J] (label : ι → J) (i : J) :
    (coordinateMaskMatrix label i).toEuclideanLin = coordinateMask label i := by
  ext v a
  rw [Matrix.toLpLin_apply, coordinate_mask_apply]
  simp [coordinateMaskMatrix, Matrix.mulVec_diagonal, ite_mul]

theorem coordinate_mask_matrix_star
    {ι J : Type*} (label : ι → J) (i : J) :
    (coordinateMaskMatrix label i)ᴴ = coordinateMaskMatrix label i := by
  classical
  ext a b
  by_cases hab : a = b
  · subst b
    simp [coordinateMaskMatrix]
  · simp [coordinateMaskMatrix, hab, Ne.symm hab]

theorem coordinate_mask_matrix_square
    {ι J : Type*} [Fintype ι] (label : ι → J) (i : J) :
    coordinateMaskMatrix label i * coordinateMaskMatrix label i = coordinateMaskMatrix label i := by
  classical
  simp only [coordinateMaskMatrix, Matrix.diagonal_mul_diagonal]
  congr 1
  funext a
  split_ifs <;> simp

theorem integral_matrix_product_entries
    {ι κ τ : Type*} [Fintype κ] (B : Matrix ι κ ℂ) (C : Matrix κ τ ℂ)
    (hB : ∀ i k, IsIntegral ℤ (B i k)) (hC : ∀ k j, IsIntegral ℤ (C k j)) :
    ∀ i j, IsIntegral ℤ ((B * C) i j) := by
  intro i j
  apply IsIntegral.sum
  intro k _
  exact (hB i k).mul (hC k j)

theorem integral_coordinate_mask_entries
    {ι J : Type*} (label : ι → J) (i : J) :
    ∀ a b, IsIntegral ℤ (coordinateMaskMatrix label i a b) := by
  classical
  intro a b
  simp only [coordinateMaskMatrix, Matrix.diagonal_apply]
  split_ifs <;> first | exact isIntegral_one | exact isIntegral_zero

theorem integral_restricted_fourier_entries
    {N : ℕ} [NeZero N] (A Λ : Finset (ZMod N)) :
    ∀ ξ a, IsIntegral ℤ (restrictedFourierMatrix A Λ ξ a) := by
  intro ξ a
  apply integral_of_root_of_unity _ N (Nat.pos_of_ne_zero (NeZero.ne N))
  simp [restrictedFourierMatrix, cyclicFourierEntry, ← AddChar.map_nsmul_eq_pow]

noncomputable def rawPrimeBlock
    (q H : ℕ) [NeZero q] [NeZero H]
    (A Λ : Finset (ZMod (q * H))) (i j : ZMod q) : Matrix Λ A ℂ :=
  coordinateMaskMatrix (fun ξ : Λ => (dualCRT q H ξ.val).1) j *
    restrictedFourierMatrix A Λ *
    coordinateMaskMatrix (fun a : A => (physicalCRT q H a.val).1) i

noncomputable def rawPrimeGram
    (q H : ℕ) [NeZero q] [NeZero H]
    (A Λ : Finset (ZMod (q * H))) (i j : ZMod q) : Matrix Λ Λ ℂ :=
  rawPrimeBlock q H A Λ i j * (rawPrimeBlock q H A Λ i j)ᴴ

theorem integral_raw_prime_gram_entries
    (q H : ℕ) [NeZero q] [NeZero H]
    (A Λ : Finset (ZMod (q * H))) (i j : ZMod q) :
    ∀ ξ μ, IsIntegral ℤ (rawPrimeGram q H A Λ i j ξ μ) := by
  apply integral_gram_entries
  apply integral_matrix_product_entries
  · exact integral_matrix_product_entries _ _ (integral_coordinate_mask_entries _ _)
      (integral_restricted_fourier_entries A Λ)
  · exact integral_coordinate_mask_entries _ _

theorem raw_prime_gram_sandwich
    (q H : ℕ) [NeZero q] [NeZero H]
    (A Λ : Finset (ZMod (q * H))) (i j : ZMod q) :
    rawPrimeGram q H A Λ i j =
      coordinateMaskMatrix (fun ξ : Λ => (dualCRT q H ξ.val).1) j *
        (restrictedFourierMatrix A Λ *
          coordinateMaskMatrix (fun a : A => (physicalCRT q H a.val).1) i *
          (restrictedFourierMatrix A Λ)ᴴ) *
        coordinateMaskMatrix (fun ξ : Λ => (dualCRT q H ξ.val).1) j := by
  classical
  simp only [rawPrimeGram, rawPrimeBlock, Matrix.conjTranspose_mul, coordinate_mask_matrix_star]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (coordinateMaskMatrix _ i), coordinate_mask_matrix_square]

/-- Equality in the original ambient coordinate basis. The Gram matrix is
unnormalized and no integrality property is asserted after a basis change. -/
theorem raw_prime_gram_to_linear_map
    (q H : ℕ) [NeZero q] [NeZero H]
    (A Λ : Finset (ZMod (q * H))) (h : IsCyclicSpectralPair A Λ) (i j : ZMod q) :
    (rawPrimeGram q H A Λ i j).toEuclideanLin =
      (A.card : ℂ) • ((spectralPrimeLevels q H Λ j).starProjection.toLinearMap *
        spectralPhysicalProjection q H A Λ i *
        (spectralPrimeLevels q H Λ j).starProjection.toLinearMap) := by
  classical
  have hmpos : 0 < (A.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr h.1
  have hsquare : (Real.sqrt (A.card : ℝ) : ℂ) ^ 2 = (A.card : ℂ) := by
    exact_mod_cast Real.sq_sqrt (le_of_lt hmpos)
  have hscalar : (A.card : ℂ) *
      ((Real.sqrt (A.card : ℝ) : ℂ)⁻¹ * (Real.sqrt (A.card : ℝ) : ℂ)⁻¹) = 1 := by
    rw [← hsquare, pow_two]
    have hs : (Real.sqrt (A.card : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.mpr hmpos).ne'
    field_simp
  let Q := coordinateMaskMatrix (fun ξ : Λ => (dualCRT q H ξ.val).1) j
  let E := coordinateMaskMatrix (fun a : A => (physicalCRT q H a.val).1) i
  have hm : (A.card : ℂ) • (Q * (normalizedFourierMatrix A Λ * E *
      (normalizedFourierMatrix A Λ)ᴴ) * Q) = rawPrimeGram q H A Λ i j := by
    simp only [normalizedFourierMatrix, Matrix.conjTranspose_smul, star_inv₀,
      Complex.star_def, Complex.conj_ofReal, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [hscalar, one_smul, raw_prime_gram_sandwich]
  rw [← hm]
  change Matrix.toLpLin 2 2 ((A.card : ℂ) • _) = _
  rw [map_smul]
  congr 1
  simp only [Matrix.toLpLin_mul_same, Q, E, coordinate_mask_matrix_to_linear_map,
    spectralPrimeLevels, coordinate_mask_eq_projection, spectralPhysicalProjection,
    fourierForward, fourierBackward]
  rfl

theorem spectral_pair_residual_raw_gram_eigenvector
    (q H : ℕ) [NeZero q] [NeZero H] (hq : q.Prime) (hq3 : 3 ≤ q)
    (hcop : Nat.Coprime q H)
    (A Λ : Finset (ZMod (q * H))) (h : IsCyclicSpectralPair A Λ) (i j : ZMod q)
    (v : localResidual (spectralPrimeUnitary q H A Λ h).toLinearMap
      (spectralPrimeLevels q H Λ j) (ZMod.stdAddChar (1 : ZMod q)) q) :
    (rawPrimeGram q H A Λ i j).toEuclideanLin (v : EuclideanSpace ℂ Λ) =
      ((A.card : ℂ) / (q : ℂ)) • (v : EuclideanSpace ℂ Λ) := by
  rw [raw_prime_gram_to_linear_map q H A Λ h i j]
  simp only [LinearMap.smul_apply, End.mul_apply]
  change (A.card : ℂ) • ((spectralPrimeLevels q H Λ j).starProjection
    (spectralPhysicalProjection q H A Λ i
      ((spectralPrimeLevels q H Λ j).starProjection (v : EuclideanSpace ℂ Λ)))) = _
  rw [spectral_pair_residual_projector_eigenvector q H hq hq3 hcop A Λ h i j v,
    smul_smul, div_eq_mul_inv]

theorem spectral_pair_residual_eq_bot
    (q H : ℕ) [NeZero q] [NeZero H] (hq : q.Prime) (hq3 : 3 ≤ q)
    (hcop : Nat.Coprime q H)
    (A Λ : Finset (ZMod (q * H))) (h : IsCyclicSpectralPair A Λ)
    (hnd : ¬q ∣ A.card) (j : ZMod q) :
    localResidual (spectralPrimeUnitary q H A Λ h).toLinearMap
      (spectralPrimeLevels q H Λ j) (ZMod.stdAddChar (1 : ZMod q)) q = ⊥ := by
  classical
  apply le_antisymm _ bot_le
  intro v hv
  change v = 0
  by_contra hv0
  let w : localResidual (spectralPrimeUnitary q H A Λ h).toLinearMap
      (spectralPrimeLevels q H Λ j) (ZMod.stdAddChar (1 : ZMod q)) q := ⟨v, hv⟩
  apply hnd
  apply dvd_of_integral_matrix_quotient_eigenvector (rawPrimeGram q H A Λ 0 j)
    (integral_raw_prime_gram_entries q H A Λ 0 j) A.card q (NeZero.ne q) v.ofLp
  · intro hz
    apply hv0
    ext ξ
    exact congrFun hz ξ
  · have he := spectral_pair_residual_raw_gram_eigenvector q H hq hq3 hcop A Λ h 0 j w
    exact congrArg WithLp.ofLp he

end FugledeAudit
