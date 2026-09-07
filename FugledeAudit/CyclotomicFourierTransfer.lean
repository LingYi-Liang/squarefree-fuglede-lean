import FugledeAudit.CoprimeCyclotomic
import FugledeAudit.PhaseUnitary

set_option autoImplicit false

namespace FugledeAudit

theorem standard_character_in_cyclotomic_field (H : ℕ) [NeZero H] (x : ZMod H) :
    ZMod.stdAddChar x ∈ IntermediateField.adjoin ℚ {ZMod.stdAddChar (1 : ZMod H)} := by
  have hx : ZMod.stdAddChar x = ZMod.stdAddChar (1 : ZMod H) ^ x.val := by
    rw [← AddChar.map_nsmul_eq_pow]
    simp
  rw [hx]
  exact pow_mem (IntermediateField.mem_adjoin_simple_self ℚ _) x.val

/-- A finite family is grouped by its actual prime-level label. Empty fibres
are allowed, and no independence or noncollision of the other labels is used. -/
theorem coprime_fibre_fourier_transfer
    {ι : Type*} [Fintype ι]
    (q H : ℕ) [NeZero q] [NeZero H] (hq : q.Prime) (hcop : Nat.Coprime q H)
    (ω Ω η : ℂ) (hω : IsPrimitiveRoot ω q) (hΩ : IsPrimitiveRoot Ω q)
    (hη : IsPrimitiveRoot η H) (label : ι → Fin q)
    (z : ι → IntermediateField.adjoin ℚ {η})
    (hzero : ∑ a : ι, (z a : ℂ) * ω ^ (label a).val = 0) :
    ∑ a : ι, (z a : ℂ) * Ω ^ (label a).val = 0 := by
  classical
  let K := IntermediateField.adjoin ℚ ({η} : Set ℂ)
  let c : Fin q → K := fun i => ∑ a : ι, if label a = i then z a else 0
  have hfibre (t : ℂ) :
      (∑ i : Fin q, (c i : ℂ) * t ^ i.val) = ∑ a : ι, (z a : ℂ) * t ^ (label a).val := by
    simp only [c, IntermediateField.coe_sum, apply_ite, IntermediateField.coe_zero,
      Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    simp [ite_mul]
  have hc := coprime_prime_coefficient_rigidity q H hq hcop ω η hω hη c
    ((hfibre ω).trans hzero)
  rw [← hfibre Ω]
  have heq : ∀ i : Fin q, (c i : ℂ) = (c 0 : ℂ) := fun i => congrArg Subtype.val (hc i 0)
  simp_rw [heq]
  rw [← Finset.mul_sum]
  have hsum : ∑ i : Fin q, Ω ^ i.val = 0 := by
    simpa only [Fin.sum_univ_eq_sum_range] using hΩ.geom_sum_eq_zero hq.one_lt
  rw [hsum, mul_zero]

end FugledeAudit
