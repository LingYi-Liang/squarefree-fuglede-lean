import FugledeAudit.ActualFourierZeros

set_option autoImplicit false

namespace FugledeAudit

open Polynomial

theorem primitive_root_power_sum_transfer
    {ι : Type*} [Fintype ι] (H : ℕ) [NeZero H]
    (ω Ω : ℂ) (hω : IsPrimitiveRoot ω H) (hΩ : IsPrimitiveRoot Ω H)
    (n : ι → ℕ) (hzero : ∑ a, ω ^ n a = 0) : ∑ a, Ω ^ n a = 0 := by
  classical
  let p : ℚ[X] := ∑ a : ι, X ^ n a
  have heval : aeval ω p = 0 := by simpa [p] using hzero
  have hmin : minpoly ℚ ω = cyclotomic H ℚ :=
    (hω.minpoly_eq_cyclotomic_of_irreducible (cyclotomic.irreducible_rat (NeZero.pos H))).symm
  have hd : cyclotomic H ℚ ∣ p := by
    rw [← hmin]
    exact minpoly.dvd ℚ ω heval
  obtain ⟨s, hs⟩ := hd
  have hc : aeval Ω (cyclotomic H ℚ) = 0 := by
    rw [aeval_def, ← eval_map, map_cyclotomic]
    exact hΩ.isRoot_cyclotomic (NeZero.pos H)
  have hp : aeval Ω p = 0 := by rw [hs, map_mul, hc, zero_mul]
  simpa [p] using hp

theorem standard_character_unit_sum_transfer
    {ι : Type*} [Fintype ι] (H u : ℕ) [NeZero H] (hcop : Nat.Coprime u H)
    (label : ι → ZMod H) (hzero : ∑ a, ZMod.stdAddChar (label a) = 0) :
    ∑ a, ZMod.stdAddChar ((u : ZMod H) * label a) = 0 := by
  have hω : IsPrimitiveRoot (ZMod.stdAddChar (1 : ZMod H)) H := standard_character_primitive_root
  have hΩ : IsPrimitiveRoot (ZMod.stdAddChar (u : ZMod H)) H := by
    have hp := hω.pow_of_coprime u hcop
    simpa [← AddChar.map_nsmul_eq_pow] using hp
  have h1 : ∑ a, ZMod.stdAddChar (1 : ZMod H) ^ (label a).val = 0 := by
    simpa only [standard_character_mul_power, mul_one] using hzero
  have ht := primitive_root_power_sum_transfer H _ _ hω hΩ (fun a => (label a).val) h1
  simpa only [standard_character_mul_power, mul_comm] using ht

theorem dual_cofactor_scaled_by_prime
    (q H : ℕ) [NeZero q] [NeZero H] (hcop : Nat.Coprime q H) (ξ : ZMod (q * H)) :
    (q : ZMod H) * (dualCRT q H ξ).2 = (physicalCRT q H ξ).2 := by
  have hb : (q : ZMod H) * (Nat.gcdA q H : ZMod H) = 1 := by
    have he := congrArg (fun z : ℤ => (z : ZMod H)) (crt_bezout q H hcop)
    simpa using he
  simp only [dualCRT, ← mul_assoc, hb, one_mul]

end FugledeAudit
