import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false

/-!
# The finite cyclic dimension chain

The spaces are a genuinely dependent family and may initially have different
dimensions, including dimension zero. No equal-size identification is assumed.
-/

namespace FugledeAudit

open Module

theorem permutation_dimensions_equal_of_injective
    {ι : Type*} [Fintype ι] (σ : Equiv.Perm ι)
    {𝕜 : Type*} [DivisionRing 𝕜] (V : ι → Type*)
    [∀ j, AddCommGroup (V j)] [∀ j, Module 𝕜 (V j)]
    [∀ j, FiniteDimensional 𝕜 (V j)]
    (S : ∀ j, V (σ j) →ₗ[𝕜] V j) (hS : ∀ j, Function.Injective (S j)) :
    ∀ j, finrank 𝕜 (V (σ j)) = finrank 𝕜 (V j) := by
  have hle : ∀ j, finrank 𝕜 (V (σ j)) ≤ finrank 𝕜 (V j) :=
    fun j => LinearMap.finrank_le_finrank_of_injective (hS j)
  have hsum : ∑ j, finrank 𝕜 (V (σ j)) = ∑ j, finrank 𝕜 (V j) :=
    Equiv.sum_comp σ (fun j => finrank 𝕜 (V j))
  have heq := (Finset.sum_eq_sum_iff_of_le (fun j _ => hle j)).mp hsum
  exact fun j => heq j (Finset.mem_univ j)

theorem permutation_blocks_bijective_of_injective
    {ι : Type*} [Fintype ι] (σ : Equiv.Perm ι)
    {𝕜 : Type*} [DivisionRing 𝕜] (V : ι → Type*)
    [∀ j, AddCommGroup (V j)] [∀ j, Module 𝕜 (V j)]
    [∀ j, FiniteDimensional 𝕜 (V j)]
    (S : ∀ j, V (σ j) →ₗ[𝕜] V j) (hS : ∀ j, Function.Injective (S j)) :
    ∀ j, Function.Bijective (S j) := by
  intro j
  exact ⟨hS j, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (permutation_dimensions_equal_of_injective σ V S hS j)).mp (hS j)⟩

theorem zmod_function_constant_of_successor_eq
    (q : ℕ) [NeZero q] {α : Type*} (d : ZMod q → α)
    (hd : ∀ j, d (j + 1) = d j) : ∀ j, d j = d 0 := by
  have hnat : ∀ n : ℕ, d (n : ZMod q) = d 0 := by
    intro n
    induction n with
    | zero => simp only [Nat.cast_zero]
    | succ n ih => simpa only [Nat.cast_succ, hd] using ih
  intro j
  simpa only [ZMod.natCast_zmod_val] using hnat j.val

theorem cyclic_common_dimension_of_injective
    (q : ℕ) [NeZero q]
    {𝕜 : Type*} [DivisionRing 𝕜] (V : ZMod q → Type*)
    [∀ j, AddCommGroup (V j)] [∀ j, Module 𝕜 (V j)]
    [∀ j, FiniteDimensional 𝕜 (V j)]
    (S : ∀ j, V (j + 1) →ₗ[𝕜] V j) (hS : ∀ j, Function.Injective (S j)) :
    ∀ j, finrank 𝕜 (V j) = finrank 𝕜 (V 0) := by
  apply zmod_function_constant_of_successor_eq q
  exact permutation_dimensions_equal_of_injective (Equiv.addRight (1 : ZMod q)) V S hS

end FugledeAudit
