import FugledeAudit.ActualClasswiseZeros
import FugledeAudit.CyclotomicUnitTransfer

set_option autoImplicit false

namespace FugledeAudit

theorem spectral_pair_literal_projection_zero
    (q H : ℕ) [NeZero q] [NeZero H] (hq : q.Prime) (hq3 : 3 ≤ q)
    (hcop : Nat.Coprime q H)
    (A Λ : Finset (ZMod (q * H))) (h : IsCyclicSpectralPair A Λ)
    (hnd : ¬q ∣ A.card) (ξ μ : Λ) (hξμ : ξ ≠ μ) :
    ∑ a : A, cyclicFourierEntry (reducePrimeFactor q H a.val)
      (reducePrimeFactor q H ξ.val - reducePrimeFactor q H μ.val) = 0 := by
  have hz := spectral_pair_cofactor_zero q H hq hq3 hcop A Λ h hnd ξ μ hξμ
  have ht := standard_character_unit_sum_transfer H q hcop
    (fun a : A => (physicalCRT q H a.val).2 *
      ((dualCRT q H ξ.val).2 - (dualCRT q H μ.val).2)) hz
  convert ht using 1
  apply Finset.sum_congr rfl
  intro a _
  unfold cyclicFourierEntry
  congr 1
  change (physicalCRT q H a.val).2 *
    ((physicalCRT q H ξ.val).2 - (physicalCRT q H μ.val).2) = _
  calc
    _ = (physicalCRT q H a.val).2 *
        ((q : ZMod H) * (dualCRT q H ξ.val).2 -
          (q : ZMod H) * (dualCRT q H μ.val).2) := by
      rw [dual_cofactor_scaled_by_prime q H hcop, dual_cofactor_scaled_by_prime q H hcop]
    _ = _ := by ring

theorem spectral_pair_frequency_projection_injective
    (q H : ℕ) [NeZero q] [NeZero H] (hq : q.Prime) (hq3 : 3 ≤ q)
    (hcop : Nat.Coprime q H)
    (A Λ : Finset (ZMod (q * H))) (h : IsCyclicSpectralPair A Λ)
    (hnd : ¬q ∣ A.card) :
    Set.InjOn (reducePrimeFactor q H) (Λ : Set (ZMod (q * H))) := by
  intro ξ hξ μ hμ he
  by_contra hne
  have hz := spectral_pair_literal_projection_zero q H hq hq3 hcop A Λ h hnd
    ⟨ξ, hξ⟩ ⟨μ, hμ⟩ (fun hs => hne (congrArg Subtype.val hs))
  simp only [he, sub_self, cyclicFourierEntry, mul_zero, AddChar.map_zero_eq_one,
    Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul, mul_one] at hz
  have hc : A.card = 0 := by exact_mod_cast hz
  exact (Finset.card_pos.mpr h.1).ne' hc

theorem spectral_pair_physical_projection_injective
    (q H : ℕ) [NeZero q] [NeZero H] (hq : q.Prime) (hq3 : 3 ≤ q)
    (hcop : Nat.Coprime q H)
    (A Λ : Finset (ZMod (q * H))) (h : IsCyclicSpectralPair A Λ)
    (hnd : ¬q ∣ A.card) :
    Set.InjOn (reducePrimeFactor q H) (A : Set (ZMod (q * H))) := by
  exact spectral_pair_frequency_projection_injective q H hq hq3 hcop Λ A
    (spectral_pair_swap A Λ h) (by simpa only [← h.2.1] using hnd)

/-- Literal reduction of both finite sets is spectral, with injectivity proved
first so that no multiplicity is silently discarded by Finset.image. -/
theorem spectral_pair_reduction_is_spectral
    (q H : ℕ) [NeZero q] [NeZero H] (hq : q.Prime) (hq3 : 3 ≤ q)
    (hcop : Nat.Coprime q H)
    (A Λ : Finset (ZMod (q * H))) (h : IsCyclicSpectralPair A Λ)
    (hnd : ¬q ∣ A.card) :
    IsCyclicSpectralPair (A.image (reducePrimeFactor q H)) (Λ.image (reducePrimeFactor q H)) := by
  classical
  have hA := spectral_pair_physical_projection_injective q H hq hq3 hcop A Λ h hnd
  have hΛ := spectral_pair_frequency_projection_injective q H hq hq3 hcop A Λ h hnd
  refine ⟨h.1.image _, ?_, ?_⟩
  · rw [Finset.card_image_of_injOn hA, Finset.card_image_of_injOn hΛ]
    exact h.2.1
  · intro ξ hξ μ hμ hne
    obtain ⟨ξ, hxmem, rfl⟩ := Finset.mem_image.mp hξ
    obtain ⟨μ, hymem, rfl⟩ := Finset.mem_image.mp hμ
    rw [Finset.sum_image]
    · have hz := spectral_pair_literal_projection_zero q H hq hq3 hcop A Λ h hnd
        ⟨ξ, hxmem⟩ ⟨μ, hymem⟩ (fun he => hne (congrArg (fun ν : Λ => reducePrimeFactor q H ν.val) he))
      exact (Finset.sum_coe_sort A _).symm.trans hz
    · intro a ha b hb hab
      exact hA ha hb hab

end FugledeAudit
