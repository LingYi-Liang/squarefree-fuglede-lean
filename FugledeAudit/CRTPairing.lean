import FugledeAudit.PaperStatements
import Mathlib.Data.Int.GCD
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false

namespace FugledeAudit

theorem standard_character_scaled (N n k : ℕ) [NeZero N] [NeZero n]
    (hN : N = n * k) (t : ℤ) :
    ZMod.stdAddChar ((k : ZMod N) * (t : ZMod N)) = ZMod.stdAddChar (t : ZMod n) := by
  have hk : k ≠ 0 := fun h => by simpa [h, hN] using NeZero.ne N
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne n
  have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast hk
  rw [show (k : ZMod N) = ((k : ℤ) : ZMod N) by simp, ← Int.cast_mul,
    ZMod.stdAddChar_coe, ZMod.stdAddChar_coe]
  congr 1
  push_cast
  rw [hN, Nat.cast_mul]
  field_simp

theorem crt_bezout (q H : ℕ) (hcop : Nat.Coprime q H) :
    (H : ℤ) * Nat.gcdB q H + (q : ℤ) * Nat.gcdA q H = 1 := by
  have hb := Nat.gcd_eq_gcd_ab q H
  rw [hcop.gcd_eq_one] at hb
  simpa only [Nat.cast_one, add_comm] using hb.symm

theorem standard_character_crt (q H : ℕ) [NeZero q] [NeZero H]
    (hcop : Nat.Coprime q H) (t : ℤ) :
    ZMod.stdAddChar (t : ZMod (q * H)) =
      ZMod.stdAddChar ((Nat.gcdB q H * t : ℤ) : ZMod q) *
        ZMod.stdAddChar ((Nat.gcdA q H * t : ℤ) : ZMod H) := by
  have hb := crt_bezout q H hcop
  have ht : t = (H : ℤ) * (Nat.gcdB q H * t) + (q : ℤ) * (Nat.gcdA q H * t) := by
    calc
      t = ((H : ℤ) * Nat.gcdB q H + (q : ℤ) * Nat.gcdA q H) * t := by rw [hb, one_mul]
      _ = _ := by ring
  calc
    _ = ZMod.stdAddChar
        (((H : ℤ) * (Nat.gcdB q H * t) + (q : ℤ) * (Nat.gcdA q H * t) : ℤ) :
          ZMod (q * H)) := congrArg (fun a : ℤ => ZMod.stdAddChar (a : ZMod (q * H))) ht
    _ = _ := by
      rw [Int.cast_add, AddChar.map_add_eq_mul]
      exact congrArg₂ (fun x y : ℂ => x * y)
        (by simpa only [Int.cast_mul, Int.cast_natCast] using
          standard_character_scaled (q * H) q H rfl (Nat.gcdB q H * t))
        (by simpa only [Int.cast_mul, Int.cast_natCast] using
          standard_character_scaled (q * H) H q (Nat.mul_comm q H) (Nat.gcdA q H * t))

def physicalCRT (q H : ℕ) (a : ZMod (q * H)) : ZMod q × ZMod H :=
  (ZMod.castHom (dvd_mul_right q H) (ZMod q) a,
    ZMod.castHom (dvd_mul_left H q) (ZMod H) a)

def dualCRT (q H : ℕ) (ξ : ZMod (q * H)) : ZMod q × ZMod H :=
  ((Nat.gcdB q H : ZMod q) * (physicalCRT q H ξ).1,
    (Nat.gcdA q H : ZMod H) * (physicalCRT q H ξ).2)

/-- The dual coordinates carry the inverse factors required by the original
Fourier pairing; the same unscaled CRT map is not used on both sides. -/
theorem cyclic_fourier_crt_pairing (q H : ℕ) [NeZero q] [NeZero H]
    (hcop : Nat.Coprime q H) (a ξ : ZMod (q * H)) :
    cyclicFourierEntry a ξ =
      ZMod.stdAddChar ((physicalCRT q H a).1 * (dualCRT q H ξ).1) *
        ZMod.stdAddChar ((physicalCRT q H a).2 * (dualCRT q H ξ).2) := by
  obtain ⟨a, rfl⟩ := ZMod.intCast_surjective a
  obtain ⟨ξ, rfl⟩ := ZMod.intCast_surjective ξ
  simp only [cyclicFourierEntry, physicalCRT, dualCRT, map_intCast]
  rw [← Int.cast_mul, standard_character_crt q H hcop]
  simp only [Int.cast_mul]
  congr 2 <;> ring

theorem physical_crt_eq_chinese_remainder (q H : ℕ) (hcop : Nat.Coprime q H)
    (a : ZMod (q * H)) : physicalCRT q H a = ZMod.chineseRemainder hcop a := by
  obtain ⟨a, rfl⟩ := ZMod.intCast_surjective a
  simp only [physicalCRT, map_intCast]
  rfl

end FugledeAudit
