import FugledeAudit.ActualTilingLift

set_option autoImplicit false

namespace FugledeAudit

theorem prime_root_zero_sum_card_divisible
    {ι : Type*} [Fintype ι] (q : ℕ) [NeZero q] (hq : q.Prime)
    (ω : ℂ) (hω : IsPrimitiveRoot ω q) (label : ι → Fin q)
    (hz : ∑ a, ω ^ (label a).val = 0) : q ∣ Fintype.card ι := by
  classical
  let η := ZMod.stdAddChar (1 : ZMod 1)
  let K := IntermediateField.adjoin ℚ {η}
  let n : Fin q → ℕ := fun i => ∑ a : ι, if label a = i then 1 else 0
  let c : Fin q → K := fun i => (n i : K)
  have hc : ∑ i : Fin q, (c i : ℂ) * ω ^ i.val = 0 := by
    change (∑ i : Fin q, (n i : ℂ) * ω ^ i.val) = 0
    simp only [n, Nat.cast_sum, Nat.cast_ite,
      Nat.cast_one, Nat.cast_zero, Finset.sum_mul, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_comm]
    simpa using hz
  have he := coprime_prime_coefficient_rigidity q 1 hq (by simp) ω η hω
    standard_character_primitive_root c hc
  have hn (i : Fin q) : n i = n 0 := by
    have hec : (n i : ℂ) = (n 0 : ℂ) := congrArg Subtype.val (he i 0)
    exact_mod_cast hec
  have hs : ∑ i : Fin q, n i = Fintype.card ι := by
    simp only [n]
    rw [Finset.sum_comm]
    simp
  refine ⟨n 0, ?_⟩
  rw [← hs]
  simp [hn]

/-- Collision exclusion needs primality and coprimality, but not q >= 3.
This supplies the order-two endpoint of the square-free induction. -/
theorem spectral_frequency_projection_injective_any_prime
    (q H : ℕ) [NeZero q] [NeZero H] (hq : q.Prime) (hcop : Nat.Coprime q H)
    (A Λ : Finset (ZMod (q * H))) (h : IsCyclicSpectralPair A Λ)
    (hnd : ¬q ∣ A.card) :
    Set.InjOn (reducePrimeFactor q H) (Λ : Set (ZMod (q * H))) := by
  classical
  intro ξ hξ μ hμ he
  by_contra hne
  let d := (dualCRT q H ξ).1 - (dualCRT q H μ).1
  have heH : (dualCRT q H ξ).2 - (dualCRT q H μ).2 = 0 := by
    change (Nat.gcdA q H : ZMod H) * reducePrimeFactor q H ξ -
      (Nat.gcdA q H : ZMod H) * reducePrimeFactor q H μ = 0
    rw [he, sub_self]
  have hz : ∑ a : A, ZMod.stdAddChar ((physicalCRT q H a.val).1 * d) = 0 := by
    have ho := h.2.2 ξ hξ μ hμ hne
    rw [← Finset.sum_coe_sort] at ho
    simpa only [cyclic_fourier_crt_pairing q H hcop, dual_crt_sub,
      Prod.fst_sub, Prod.snd_sub, heH, mul_zero, AddChar.map_zero_eq_one, mul_one] using ho
  have hd : d ≠ 0 := by
    intro hd
    simp only [hd, mul_zero, AddChar.map_zero_eq_one, Finset.sum_const,
      Finset.card_univ, Fintype.card_coe, nsmul_eq_mul, mul_one] at hz
    have hm : A.card = 0 := by exact_mod_cast hz
    exact (Finset.card_pos.mpr h.1).ne' hm
  apply hnd
  have hv := prime_root_zero_sum_card_divisible q hq (ZMod.stdAddChar d)
    (standard_character_nonzero_primitive q hq d hd)
    (fun a : A => ⟨(physicalCRT q H a.val).1.val, ZMod.val_lt _⟩)
    (by simpa only [standard_character_mul_power] using hz)
  simpa only [Fintype.card_coe] using hv

theorem spectral_physical_projection_injective_any_prime
    (q H : ℕ) [NeZero q] [NeZero H] (hq : q.Prime) (hcop : Nat.Coprime q H)
    (A Λ : Finset (ZMod (q * H))) (h : IsCyclicSpectralPair A Λ)
    (hnd : ¬q ∣ A.card) :
    Set.InjOn (reducePrimeFactor q H) (A : Set (ZMod (q * H))) :=
  spectral_frequency_projection_injective_any_prime q H hq hcop Λ A
    (spectral_pair_swap A Λ h) (by simpa only [← h.2.1] using hnd)

end FugledeAudit
