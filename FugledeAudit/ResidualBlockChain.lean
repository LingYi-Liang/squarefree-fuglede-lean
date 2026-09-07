import FugledeAudit.ResidualCompression
import FugledeAudit.CyclicDimensions
import FugledeAudit.BlockAlgebra

set_option autoImplicit false

/-!
# Connected residual-block argument of Lemma 3.2

This module connects the algebraic block relations to vanishing diagonal
blocks and unitary shift blocks. The q-th, second and third block relations
remain explicit inputs here. SparseProjectionRelations derives their ambient
versions from sparse powers; ActualResidualChain proves the residual-subspace
restriction connecting the two modules. Injectivity and equal dimension are conclusions.
-/

namespace FugledeAudit

open Module

/-- A rightmost shift factor is injective because its full cyclic product is
I-D^q and the latter is invertible. V and W need not have equal dimension. -/
theorem shift_injective_of_return_identity
    {V W : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup W] [Module ℂ W]
    (D : End ℂ V) (S : V →ₗ[ℂ] W) (T : W →ₗ[ℂ] V)
    (q : ℕ) (hq : 0 < q)
    (hD : ∀ μ : ℂ, ‖μ‖ = 1 → ¬ End.HasEigenvalue D μ)
    (hreturn : T.comp S = 1 - D ^ q) : Function.Injective S := by
  have hunit := isUnit_one_sub_pow_of_no_unit_eigenvalue D q hq hD
  have hTS : Function.Injective (T.comp S) := by
    rw [hreturn]
    exact ((End.isUnit_iff _).mp hunit).1
  intro v w hvw
  exact hTS (congrArg T hvw)

/-- The full middle block argument, without assuming S injective or the
levels equidimensional. T_j denotes the return product after S_j. -/
theorem residual_block_chain
    {ι : Type*} [Fintype ι] (σ : Equiv.Perm ι)
    (V : ι → Type*) [∀ j, NormedAddCommGroup (V j)]
    [∀ j, NormedSpace ℂ (V j)] [∀ j, FiniteDimensional ℂ (V j)]
    (D : ∀ j, End ℂ (V j))
    (S : ∀ j, V (σ j) →ₗ[ℂ] V j) (T : ∀ j, V j →ₗ[ℂ] V (σ j))
    (q : ℕ) (hq : 3 ≤ q)
    (hD : ∀ j μ, ‖μ‖ = 1 → ¬ End.HasEigenvalue (D j) μ)
    (hreturn : ∀ j, (T j).comp (S j) = 1 - D (σ j) ^ q)
    (h₂ : ∀ j, (D j).comp (S j) + (S j).comp (D (σ j)) = 0)
    (h₃ : ∀ j, ((D j).comp (D j)).comp (S j) +
      ((D j).comp (S j)).comp (D (σ j)) + (S j).comp ((D (σ j)).comp (D (σ j))) = 0)
    (hS : ∀ j v, ‖S j v‖ ≤ ‖v‖) (hT : ∀ j v, ‖T j v‖ ≤ ‖v‖)
    (henergy : ∀ j v, ‖v‖ ^ 2 = ‖D (σ j) v‖ ^ 2 + ‖S j v‖ ^ 2) :
    (∀ j, D j = 0) ∧ (∀ j, Function.Bijective (S j) ∧ ∀ v, ‖S j v‖ = ‖v‖) := by
  have hqpos : 0 < q := lt_of_lt_of_le (by decide : 0 < 3) hq
  have hinj : ∀ j, Function.Injective (S j) := fun j =>
    shift_injective_of_return_identity (D (σ j)) (S j) (T j) q hqpos (hD (σ j)) (hreturn j)
  have hsquare : ∀ j, D (σ j) ^ 2 = 0 := by
    intro j
    simpa only [pow_two, End.mul_eq_comp] using
      shift_block_square_zero (D j) (D (σ j)) (S j) (hinj j) (h₂ j) (h₃ j)
  have hpower : ∀ j, D (σ j) ^ q = 0 := fun j =>
    pow_eq_zero_of_le (le_trans (by decide : 2 ≤ 3) hq) (hsquare j)
  have hleft : ∀ j, Function.LeftInverse (T j) (S j) := by
    intro j v
    have hid : (T j).comp (S j) = 1 := by rw [hreturn j, hpower j, sub_zero]
    exact congrArg (fun f : End ℂ (V (σ j)) => f v) hid
  have hnorm : ∀ j v, ‖S j v‖ = ‖v‖ := fun j v =>
    norm_eq_of_contraction_left_inverse (S j) (T j) (hS j) (hT j) (hleft j) v
  constructor
  · intro j
    obtain ⟨i, rfl⟩ := σ.surjective j
    ext v
    have he := henergy i v
    rw [hnorm i v] at he
    have hz : ‖D (σ i) v‖ = 0 := by nlinarith [norm_nonneg (D (σ i) v)]
    exact norm_eq_zero.mp hz
  · intro j
    exact ⟨permutation_blocks_bijective_of_injective σ V S hinj j, hnorm j⟩

/-- Specialization to residual spaces constructed from the actual finite-order
unitary. The exclusion of unit-circle eigenvalues is now a proved dependency,
not a hypothesis of this theorem. The remaining block identities stay explicit. -/
theorem constructed_residual_block_chain
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (U : E ≃ₗᵢ[ℂ] E) (q : ℕ) [NeZero q] (hq : 3 ≤ q)
    (ω : ℂ) (hω : IsPrimitiveRoot ω q) (hU : U.toLinearMap ^ q = 1)
    (L : ZMod q → Submodule ℂ E)
    (S : ∀ j, localResidual U.toLinearMap (L (j + 1)) ω q →ₗ[ℂ]
      localResidual U.toLinearMap (L j) ω q)
    (T : ∀ j, localResidual U.toLinearMap (L j) ω q →ₗ[ℂ]
      localResidual U.toLinearMap (L (j + 1)) ω q)
    (hreturn : ∀ j, (T j).comp (S j) =
      1 - unitaryCompression U (localResidual U.toLinearMap (L (j + 1)) ω q) ^ q)
    (h₂ : ∀ j,
      (unitaryCompression U (localResidual U.toLinearMap (L j) ω q)).comp (S j) +
      (S j).comp (unitaryCompression U (localResidual U.toLinearMap (L (j + 1)) ω q)) = 0)
    (h₃ : ∀ j,
      ((unitaryCompression U (localResidual U.toLinearMap (L j) ω q)).comp
        (unitaryCompression U (localResidual U.toLinearMap (L j) ω q))).comp (S j) +
      ((unitaryCompression U (localResidual U.toLinearMap (L j) ω q)).comp (S j)).comp
        (unitaryCompression U (localResidual U.toLinearMap (L (j + 1)) ω q)) +
      (S j).comp ((unitaryCompression U (localResidual U.toLinearMap (L (j + 1)) ω q)).comp
        (unitaryCompression U (localResidual U.toLinearMap (L (j + 1)) ω q))) = 0)
    (hS : ∀ j v, ‖S j v‖ ≤ ‖v‖) (hT : ∀ j v, ‖T j v‖ ≤ ‖v‖)
    (henergy : ∀ j v, ‖v‖ ^ 2 =
      ‖unitaryCompression U (localResidual U.toLinearMap (L (j + 1)) ω q) v‖ ^ 2 + ‖S j v‖ ^ 2) :
    (∀ j, unitaryCompression U (localResidual U.toLinearMap (L j) ω q) = 0) ∧
    (∀ j, Function.Bijective (S j) ∧ ∀ v, ‖S j v‖ = ‖v‖) := by
  apply residual_block_chain (Equiv.addRight (1 : ZMod q))
    (fun j => localResidual U.toLinearMap (L j) ω q)
    (fun j => unitaryCompression U (localResidual U.toLinearMap (L j) ω q)) S T q hq
    (fun j => residual_compression_no_unit_eigenvalue U (L j) ω q hω hU)
    hreturn h₂ h₃ hS hT henergy

end FugledeAudit
