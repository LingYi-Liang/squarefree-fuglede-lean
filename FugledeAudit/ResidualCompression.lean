import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.FieldTheory.IsAlgClosed.Spectrum
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Tactic.Linarith

set_option autoImplicit false

/-!
# The unit-circle exclusion in Lemma 3.2

The local residual space is constructed, not postulated to contain no
eigenvectors. It is the level space minus its intersections with the q
eigenspaces of the finite-order ambient unitary.

The compression defined here agrees with the manuscript's restricted block
once the common reducing-space and level-projection identifications are proved.
Those global identifications are not silently assumed to have been checked.
-/

namespace FugledeAudit

open Module

section Definitions

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def localEigenSpace (U : End ℂ E) (L : Submodule ℂ E) (ω : ℂ) (q : ℕ) :
    Submodule ℂ E := ⨆ i : Fin q, L ⊓ U.eigenspace (ω ^ i.val)

noncomputable def localResidual (U : End ℂ E) (L : Submodule ℂ E) (ω : ℂ) (q : ℕ) :
    Submodule ℂ E := L ⊓ (localEigenSpace U L ω q)ᗮ

/-- A residual vector that is also an ambient eigenvector must vanish.
The q-th-root enumeration follows from U^q = I and a primitive root. -/
theorem local_residual_eigenvector_eq_zero
    (U : End ℂ E) (L : Submodule ℂ E) (ω : ℂ) (q : ℕ) [NeZero q]
    (hω : IsPrimitiveRoot ω q) (hU : U ^ q = 1)
    {v : E} (hv : v ∈ localResidual U L ω q) {μ : ℂ}
    (he : U v = μ • v) : v = 0 := by
  by_contra hv0
  have hev : End.HasEigenvector U μ v := ⟨End.mem_eigenspace_iff.mpr he, hv0⟩
  have hp := hev.pow_apply q
  rw [hU] at hp
  have hpow : μ ^ q = 1 := by
    have hzero : (μ ^ q - 1) • v = 0 := by
      rw [sub_smul, one_smul, ← hp]
      simp
    exact sub_eq_zero.mp ((smul_eq_zero.mp hzero).resolve_right hv0)
  obtain ⟨i, hi, hroot⟩ := hω.eq_pow_of_pow_eq_one hpow
  have hvW : v ∈ localEigenSpace U L ω q := by
    apply (le_iSup (fun i : Fin q => L ⊓ U.eigenspace (ω ^ i.val)) ⟨i, hi⟩)
    exact ⟨hv.1, End.mem_eigenspace_iff.mpr (by simpa only [hroot] using he)⟩
  have hbot : v ∈ (⊥ : Submodule ℂ E) := by
    rw [← (localEigenSpace U L ω q).inf_orthogonal_eq_bot]
    exact ⟨hvW, hv.2⟩
  exact hv0 hbot

end Definitions

section Compression

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E]

noncomputable def unitaryCompression (U : E ≃ₗᵢ[ℂ] E) (K : Submodule ℂ E) : End ℂ K :=
  K.orthogonalProjectionOnto.toLinearMap.comp (U.toLinearMap.comp K.subtype)

theorem unitary_compression_contraction (U : E ≃ₗᵢ[ℂ] E) (K : Submodule ℂ E) (v : K) :
    ‖unitaryCompression U K v‖ ≤ ‖v‖ := by
  change ‖K.orthogonalProjectionOnto (U (v : E))‖ ≤ ‖v‖
  calc
    _ ≤ ‖U (v : E)‖ := K.norm_orthogonalProjectionOnto_apply_le _
    _ = ‖v‖ := U.norm_map _

/-- Equality of norms in the orthogonal compression forces all of Uv into K.
This is the Pythagorean equality argument used in the paper. -/
theorem unitary_compression_unit_eigenvector_lifts
    (U : E ≃ₗᵢ[ℂ] E) (K : Submodule ℂ E) (v : K) (μ : ℂ)
    (hμ : ‖μ‖ = 1) (he : unitaryCompression U K v = μ • v) :
    U (v : E) = μ • (v : E) := by
  have he' : K.starProjection (U (v : E)) = μ • (v : E) :=
    congrArg (fun w : K => (w : E)) he
  have hmem : U (v : E) ∈ K := by
    apply (K.mem_iff_norm_starProjection _).mpr
    rw [he', norm_smul, hμ, one_mul, U.norm_map]
  rw [← K.starProjection_eq_self_iff.mpr hmem]
  exact he'

theorem residual_compression_no_unit_eigenvalue
    (U : E ≃ₗᵢ[ℂ] E) (L : Submodule ℂ E) (ω : ℂ) (q : ℕ) [NeZero q]
    (hω : IsPrimitiveRoot ω q) (hU : U.toLinearMap ^ q = 1)
    (μ : ℂ) (hμ : ‖μ‖ = 1) :
    ¬ End.HasEigenvalue (unitaryCompression U (localResidual U.toLinearMap L ω q)) μ := by
  intro h
  obtain ⟨v, hv⟩ := h.exists_hasEigenvector
  have hlift := unitary_compression_unit_eigenvector_lifts U _ v μ hμ hv.apply_eq_smul
  have hz := local_residual_eigenvector_eq_zero U.toLinearMap L ω q hω hU v.property hlift
  exact hv.2 (Subtype.ext hz)

theorem residual_compression_eigenvalue_norm_lt_one
    (U : E ≃ₗᵢ[ℂ] E) (L : Submodule ℂ E) (ω : ℂ) (q : ℕ) [NeZero q]
    (hω : IsPrimitiveRoot ω q) (hU : U.toLinearMap ^ q = 1)
    (μ : ℂ)
    (he : End.HasEigenvalue (unitaryCompression U (localResidual U.toLinearMap L ω q)) μ) :
    ‖μ‖ < 1 := by
  obtain ⟨v, hv⟩ := he.exists_hasEigenvector
  have hnorm := unitary_compression_contraction U (localResidual U.toLinearMap L ω q) v
  rw [hv.apply_eq_smul, norm_smul] at hnorm
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv.2
  have hle : ‖μ‖ ≤ 1 := by nlinarith
  exact lt_of_le_of_ne hle (fun h => residual_compression_no_unit_eigenvalue U L ω q hω hU μ h he)

end Compression

/-- Finite-dimensional spectral mapping supplies the precise invertibility
consequence of excluding the unit circle, including zero-dimensional spaces. -/
theorem isUnit_one_sub_pow_of_no_unit_eigenvalue
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (D : End ℂ V) (q : ℕ) (hq : 0 < q)
    (hD : ∀ μ : ℂ, ‖μ‖ = 1 → ¬ End.HasEigenvalue D μ) :
    IsUnit (1 - D ^ q) := by
  by_contra h
  have hone : (1 : ℂ) ∈ spectrum ℂ (D ^ q) := by
    apply spectrum.mem_iff.mpr
    simpa using h
  rw [spectrum.map_pow_of_pos (𝕜 := ℂ) D hq] at hone
  obtain ⟨μ, hμ, hpow⟩ := hone
  change μ ^ q = 1 at hpow
  have hnorm : ‖μ‖ = 1 := by
    apply (pow_eq_one_iff_of_nonneg (norm_nonneg μ) hq.ne').mp
    rw [← norm_pow, hpow, norm_one]
  exact hD μ hnorm (End.HasEigenvalue.of_mem_spectrum hμ)

theorem residual_compression_one_sub_pow_bijective
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E]
    (U : E ≃ₗᵢ[ℂ] E) (L : Submodule ℂ E) (ω : ℂ) (q : ℕ) [NeZero q]
    (hω : IsPrimitiveRoot ω q) (hU : U.toLinearMap ^ q = 1) :
    Function.Bijective (1 - unitaryCompression U (localResidual U.toLinearMap L ω q) ^ q :
      End ℂ (localResidual U.toLinearMap L ω q)) := by
  apply (End.isUnit_iff _).mp
  apply isUnit_one_sub_pow_of_no_unit_eigenvalue _ q (NeZero.pos q)
  exact residual_compression_no_unit_eigenvalue U L ω q hω hU

end FugledeAudit
