import FugledeAudit.FiniteFourierBasics
import Mathlib.Analysis.InnerProductSpace.Adjoint

set_option autoImplicit false

namespace FugledeAudit

open Matrix

noncomputable def fourierForward {N : ℕ} [NeZero N] (A Λ : Finset (ZMod N)) :
    EuclideanSpace ℂ A →ₗ[ℂ] EuclideanSpace ℂ Λ :=
  (normalizedFourierMatrix A Λ).toEuclideanLin

noncomputable def fourierBackward {N : ℕ} [NeZero N] (A Λ : Finset (ZMod N)) :
    EuclideanSpace ℂ Λ →ₗ[ℂ] EuclideanSpace ℂ A :=
  (normalizedFourierMatrix A Λ)ᴴ.toEuclideanLin

theorem fourier_forward_backward {N : ℕ} [NeZero N] (A Λ : Finset (ZMod N))
    (h : IsCyclicSpectralPair A Λ) :
    (fourierForward A Λ).comp (fourierBackward A Λ) = LinearMap.id := by
  classical
  change (Matrix.toLpLin 2 2 _).comp (Matrix.toLpLin 2 2 _) = _
  rw [← Matrix.toLpLin_mul_same, spectral_pair_normalized_row_gram A Λ h,
    Matrix.toLpLin_one]

theorem fourier_backward_forward {N : ℕ} [NeZero N] (A Λ : Finset (ZMod N))
    (h : IsCyclicSpectralPair A Λ) :
    (fourierBackward A Λ).comp (fourierForward A Λ) = LinearMap.id := by
  classical
  change (Matrix.toLpLin 2 2 _).comp (Matrix.toLpLin 2 2 _) = _
  rw [← Matrix.toLpLin_mul_same, spectral_pair_normalized_column_gram A Λ h,
    Matrix.toLpLin_one]

theorem fourier_backward_eq_adjoint {N : ℕ} [NeZero N] (A Λ : Finset (ZMod N)) :
    fourierBackward A Λ = (fourierForward A Λ).adjoint := by
  classical
  exact Matrix.toEuclideanLin_conjTranspose_eq_adjoint _

theorem fourier_forward_inner {N : ℕ} [NeZero N] (A Λ : Finset (ZMod N))
    (h : IsCyclicSpectralPair A Λ) (x y : EuclideanSpace ℂ A) :
    inner ℂ (fourierForward A Λ x) (fourierForward A Λ y) = inner ℂ x y := by
  rw [← LinearMap.adjoint_inner_right, ← fourier_backward_eq_adjoint]
  have hxy := LinearMap.congr_fun (fourier_backward_forward A Λ h) y
  change fourierBackward A Λ (fourierForward A Λ y) = y at hxy
  rw [hxy]

/-- The actual normalized Fourier matrix, with the manuscript's row and column
indices, as a unitary equivalence. No orthogonality hypothesis beyond the
literal spectral-pair definition is added. -/
noncomputable def spectralFourierUnitary {N : ℕ} [NeZero N]
    (A Λ : Finset (ZMod N)) (h : IsCyclicSpectralPair A Λ) :
    EuclideanSpace ℂ A ≃ₗᵢ[ℂ] EuclideanSpace ℂ Λ :=
  let e : EuclideanSpace ℂ A ≃ₗ[ℂ] EuclideanSpace ℂ Λ :=
    { fourierForward A Λ with
      invFun := fourierBackward A Λ
      left_inv := fun x => LinearMap.congr_fun (fourier_backward_forward A Λ h) x
      right_inv := fun x => LinearMap.congr_fun (fourier_forward_backward A Λ h) x }
  e.isometryOfInner (fourier_forward_inner A Λ h)

theorem spectral_fourier_unitary_to_linear_map {N : ℕ} [NeZero N]
    (A Λ : Finset (ZMod N)) (h : IsCyclicSpectralPair A Λ) :
    (spectralFourierUnitary A Λ h).toLinearMap = fourierForward A Λ := rfl

theorem spectral_fourier_unitary_inverse {N : ℕ} [NeZero N]
    (A Λ : Finset (ZMod N)) (h : IsCyclicSpectralPair A Λ) (y : EuclideanSpace ℂ Λ) :
    (spectralFourierUnitary A Λ h).symm y = fourierBackward A Λ y := rfl

end FugledeAudit
