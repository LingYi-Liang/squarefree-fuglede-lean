import FugledeAudit.PaperStatements
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

set_option autoImplicit false

namespace FugledeAudit

open Matrix

theorem std_character_star {N : ℕ} [NeZero N] (x : ZMod N) :
    star (ZMod.stdAddChar x) = ZMod.stdAddChar (-x) := by
  change star ((ZMod.toCircle x : Circle) : ℂ) = ((ZMod.toCircle (-x) : Circle) : ℂ)
  rw [AddChar.map_neg_eq_inv, Circle.coe_inv_eq_conj]
  rfl

theorem fourier_entry_product_star {N : ℕ} [NeZero N] (a ξ μ : ZMod N) :
    cyclicFourierEntry a ξ * star (cyclicFourierEntry a μ) = cyclicFourierEntry a (ξ - μ) := by
  unfold cyclicFourierEntry
  rw [std_character_star, ← AddChar.map_add_eq_mul]
  congr 1
  ring

noncomputable def restrictedFourierMatrix {N : ℕ} [NeZero N]
    (A Λ : Finset (ZMod N)) : Matrix Λ A ℂ :=
  fun ξ a => cyclicFourierEntry a.val ξ.val

theorem spectral_pair_row_gram {N : ℕ} [NeZero N]
    (A Λ : Finset (ZMod N)) (h : IsCyclicSpectralPair A Λ) :
    restrictedFourierMatrix A Λ * (restrictedFourierMatrix A Λ)ᴴ = (A.card : ℂ) • 1 := by
  classical
  ext ξ μ
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, restrictedFourierMatrix,
    fourier_entry_product_star, Matrix.smul_apply, Matrix.one_apply]
  by_cases hξμ : ξ = μ
  · subst μ
    simp [cyclicFourierEntry]
  · rw [if_neg hξμ, smul_zero]
    have hv : ξ.val ≠ μ.val := fun hval => hξμ (Subtype.ext hval)
    exact (Finset.sum_coe_sort A (fun a => cyclicFourierEntry a (ξ.val - μ.val))).trans
      (h.2.2 ξ.val ξ.property μ.val μ.property hv)

noncomputable def normalizedFourierMatrix {N : ℕ} [NeZero N]
    (A Λ : Finset (ZMod N)) : Matrix Λ A ℂ :=
  (Real.sqrt (A.card : ℝ) : ℂ)⁻¹ • restrictedFourierMatrix A Λ

theorem spectral_pair_normalized_row_gram {N : ℕ} [NeZero N]
    (A Λ : Finset (ZMod N)) (h : IsCyclicSpectralPair A Λ) :
    normalizedFourierMatrix A Λ * (normalizedFourierMatrix A Λ)ᴴ = 1 := by
  classical
  have hmpos : 0 < (A.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr h.1
  have hspos : 0 < Real.sqrt (A.card : ℝ) := Real.sqrt_pos.mpr hmpos
  have hsne : (Real.sqrt (A.card : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hspos.ne'
  have hsquare : (Real.sqrt (A.card : ℝ) : ℂ) ^ 2 = (A.card : ℂ) := by
    exact_mod_cast Real.sq_sqrt (le_of_lt hmpos)
  have hscalar : (Real.sqrt (A.card : ℝ) : ℂ)⁻¹ *
      (Real.sqrt (A.card : ℝ) : ℂ)⁻¹ * (A.card : ℂ) = 1 := by
    rw [← hsquare, pow_two]
    field_simp
  simp only [normalizedFourierMatrix, Matrix.conjTranspose_smul, star_inv₀,
    Complex.star_def, Complex.conj_ofReal, Matrix.smul_mul, Matrix.mul_smul,
    spectral_pair_row_gram A Λ h, smul_smul, ← mul_assoc, hscalar, one_smul]

theorem spectral_pair_normalized_column_gram {N : ℕ} [NeZero N]
    (A Λ : Finset (ZMod N)) (h : IsCyclicSpectralPair A Λ) :
    (normalizedFourierMatrix A Λ)ᴴ * normalizedFourierMatrix A Λ = 1 := by
  classical
  let e : Λ ≃ A := Fintype.equivOfCardEq (by simpa only [Fintype.card_coe] using h.2.1.symm)
  exact (Matrix.mul_eq_one_comm_of_equiv e).mp (spectral_pair_normalized_row_gram A Λ h)

theorem spectral_pair_column_gram {N : ℕ} [NeZero N]
    (A Λ : Finset (ZMod N)) (h : IsCyclicSpectralPair A Λ) :
    (restrictedFourierMatrix A Λ)ᴴ * restrictedFourierMatrix A Λ = (A.card : ℂ) • 1 := by
  classical
  have hm : (A.card : ℂ) ≠ 0 := by exact_mod_cast (Finset.card_pos.mpr h.1).ne'
  let e : Λ ≃ A := Fintype.equivOfCardEq (by simpa only [Fintype.card_coe] using h.2.1.symm)
  have hr : restrictedFourierMatrix A Λ *
      ((A.card : ℂ)⁻¹ • (restrictedFourierMatrix A Λ)ᴴ) = 1 := by
    rw [Matrix.mul_smul, spectral_pair_row_gram A Λ h, smul_smul, inv_mul_cancel₀ hm, one_smul]
  have hc := (Matrix.mul_eq_one_comm_of_equiv e).mp hr
  have hc' := congrArg (fun M : Matrix A A ℂ => (A.card : ℂ) • M) hc
  simpa only [Matrix.smul_mul, smul_smul, mul_inv_cancel₀ hm, one_smul] using hc'

/-- Duality of the actual named spectral pair, including nonemptiness and
the precise Fourier convention. -/
theorem spectral_pair_swap {N : ℕ} [NeZero N]
    (A Λ : Finset (ZMod N)) (h : IsCyclicSpectralPair A Λ) :
    IsCyclicSpectralPair Λ A := by
  classical
  refine ⟨Finset.card_pos.mp (by rw [← h.2.1]; exact Finset.card_pos.mpr h.1),
    h.2.1.symm, ?_⟩
  intro a ha b hb hab
  let a' : A := ⟨a, ha⟩
  let b' : A := ⟨b, hb⟩
  have hba : b' ≠ a' := fun he => hab (congrArg Subtype.val he).symm
  have hg := congrArg (fun M : Matrix A A ℂ => M b' a') (spectral_pair_column_gram A Λ h)
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.smul_apply,
    Matrix.one_apply, if_neg hba, smul_zero, restrictedFourierMatrix] at hg
  have hterm : ∀ ξ : Λ,
      star (cyclicFourierEntry b ξ.val) * cyclicFourierEntry a ξ.val =
        cyclicFourierEntry ξ.val (a - b) := by
    intro ξ
    rw [mul_comm]
    simpa only [cyclicFourierEntry, mul_comm] using fourier_entry_product_star ξ.val a b
  change ∑ ξ : Λ, star (cyclicFourierEntry b ξ.val) * cyclicFourierEntry a ξ.val = 0 at hg
  simp_rw [hterm] at hg
  exact (Finset.sum_coe_sort Λ (fun ξ => cyclicFourierEntry ξ (a - b))).symm.trans hg

end FugledeAudit
