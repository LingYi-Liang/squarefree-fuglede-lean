import Mathlib.Data.Matrix.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NoncommRing

set_option autoImplicit false

/-!
# General-q cyclic block expansions

The coefficient ring may be noncommutative, including an ambient operator
ring. No common dimension for level spaces is assumed by these identities.
ProjectionBlocks identifies them with actual ambient projection blocks.
Restriction to the constructed residual spaces is a separate obligation.
-/

namespace FugledeAudit

open Matrix

section

variable (q : ℕ) [NeZero q] {R : Type*} [Ring R]

def cyclicBand (D S : ZMod q → R) : Matrix (ZMod q) (ZMod q) R :=
  fun j k => if k = j then D j else if k = j + 1 then S j else 0

omit [NeZero q] in
theorem cyclic_successor_ne (hq : 2 ≤ q) (j : ZMod q) : j + 1 ≠ j := by
  intro h
  have h1 : (1 : ZMod q) = 0 := add_left_cancel (by simpa only [add_zero] using h)
  have hq1 := ZMod.one_eq_zero_iff.mp h1
  omega

omit [NeZero q] in
theorem cyclic_band_self (D S : ZMod q → R) (j : ZMod q) :
    cyclicBand q D S j j = D j := by simp [cyclicBand]

omit [NeZero q] in
theorem cyclic_band_next (D S : ZMod q → R) (hq : 2 ≤ q) (j : ZMod q) :
    cyclicBand q D S j (j + 1) = S j := by
  simp [cyclicBand, cyclic_successor_ne q hq j]

theorem cyclic_band_mul_row (D S : ZMod q → R) (hq : 2 ≤ q)
    (A : Matrix (ZMod q) (ZMod q) R) (j k : ZMod q) :
    (cyclicBand q D S * A) j k = D j * A j k + S j * A (j + 1) k := by
  rw [Matrix.mul_apply]
  rw [Fintype.sum_eq_add j (j + 1) (cyclic_successor_ne q hq j).symm]
  · rw [cyclic_band_self, cyclic_band_next q D S hq]
  · intro x hx
    simp [cyclicBand, hx.1, hx.2]

theorem cyclic_band_mul_column (D S : ZMod q → R) (hq : 2 ≤ q)
    (A : Matrix (ZMod q) (ZMod q) R) (j k : ZMod q) :
    (A * cyclicBand q D S) j k = A j k * D k + A j (k - 1) * S (k - 1) := by
  have hk : k ≠ k - 1 := by
    simpa only [sub_add_cancel] using cyclic_successor_ne q hq (k - 1)
  have hb : cyclicBand q D S (k - 1) k = S (k - 1) := by
    simpa only [sub_add_cancel] using cyclic_band_next q D S hq (k - 1)
  rw [Matrix.mul_apply, Fintype.sum_eq_add k (k - 1) hk]
  · rw [cyclic_band_self, hb]
  · intro x hx
    have h1 : k ≠ x := Ne.symm hx.1
    have h2 : k ≠ x + 1 := by
      intro h
      exact hx.2 (eq_sub_iff_add_eq.mpr h.symm)
    simp [cyclicBand, h1, h2]

/-- A nonzero length-n matrix entry has a path with between 0 and n shifts.
This is proved for all n; it is not a small-modulus enumeration. -/
theorem cyclic_band_power_support (D S : ZMod q → R) (hq : 2 ≤ q)
    (n : ℕ) (j k : ZMod q)
    (h : (cyclicBand q D S ^ n) j k ≠ 0) : ∃ s ≤ n, k = j + (s : ZMod q) := by
  induction n generalizing j k with
  | zero =>
    have hjk : k = j := by
      by_contra hne
      exact h (by simp [Ne.symm hne])
    exact ⟨0, Nat.zero_le _, by simpa only [Nat.cast_zero, add_zero] using hjk⟩
  | succ n ih =>
    rw [pow_succ', cyclic_band_mul_row q D S hq] at h
    by_cases hl : (cyclicBand q D S ^ n) j k = 0
    · have hr : (cyclicBand q D S ^ n) (j + 1) k ≠ 0 := by
        intro hr
        exact h (by rw [hl, hr, mul_zero, mul_zero, add_zero])
      obtain ⟨s, hs, he⟩ := ih (j + 1) k hr
      refine ⟨s + 1, Nat.succ_le_succ hs, ?_⟩
      simpa only [Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm] using he
    · obtain ⟨s, hs, he⟩ := ih j k hl
      exact ⟨s, Nat.le_succ_of_le hs, he⟩

/-- Before q steps, a path cannot complete a nontrivial circuit. -/
theorem cyclic_band_short_return_zero (D S : ZMod q → R) (hq : 2 ≤ q)
    (n : ℕ) (hn : n + 1 < q) (j : ZMod q) :
    (cyclicBand q D S ^ n) (j + 1) j = 0 := by
  by_contra h
  obtain ⟨s, hs, he⟩ := cyclic_band_power_support q D S hq n (j + 1) j h
  have hcast : ((s + 1 : ℕ) : ZMod q) = 0 := by
    apply add_left_cancel (a := j)
    simpa only [Nat.cast_add, Nat.cast_one, add_zero, add_assoc, add_comm, add_left_comm] using he.symm
  exact (Nat.not_dvd_of_pos_of_lt (Nat.succ_pos s)
    (lt_of_le_of_lt (Nat.succ_le_succ hs) hn)) ((ZMod.natCast_eq_zero_iff _ _).mp hcast)

theorem cyclic_band_power_diagonal_before_wrap (D S : ZMod q → R) (hq : 2 ≤ q)
    (n : ℕ) (hn : n < q) (j : ZMod q) : (cyclicBand q D S ^ n) j j = D j ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', cyclic_band_mul_row q D S hq,
      ih (Nat.lt_of_succ_lt hn), cyclic_band_short_return_zero q D S hq n hn j]
    simp only [mul_zero, add_zero, pow_succ']

/-- The q-th diagonal identity with the actual rightmost shift factor.
The return factor is the corresponding block of the (q-1)-st power. -/
theorem cyclic_band_qth_return_identity (D S : ZMod q → R) (hq : 2 ≤ q) (j : ZMod q) :
    (cyclicBand q D S ^ q) j j = D j ^ q +
      (cyclicBand q D S ^ (q - 1)) j (j - 1) * S (j - 1) := by
  have hq1 : 1 ≤ q := by omega
  have hn : q - 1 < q := by omega
  have h : (cyclicBand q D S ^ ((q - 1) + 1)) j j = D j ^ ((q - 1) + 1) +
      (cyclicBand q D S ^ (q - 1)) j (j - 1) * S (j - 1) := by
    rw [pow_succ, cyclic_band_mul_column q D S hq,
      cyclic_band_power_diagonal_before_wrap q D S hq (q - 1) hn j, pow_succ]
  simpa only [Nat.sub_add_cancel hq1] using h

theorem cyclic_band_square_shift (D S : ZMod q → R) (hq : 2 ≤ q) (j : ZMod q) :
    (cyclicBand q D S ^ 2) j (j + 1) = D j * S j + S j * D (j + 1) := by
  rw [pow_two, cyclic_band_mul_row q D S hq,
    cyclic_band_next q D S hq, cyclic_band_self]

theorem cyclic_band_cube_shift (D S : ZMod q → R) (hq : 3 ≤ q) (j : ZMod q) :
    (cyclicBand q D S ^ 3) j (j + 1) =
      D j ^ 2 * S j + D j * S j * D (j + 1) + S j * D (j + 1) ^ 2 := by
  have hq2 : 2 ≤ q := by omega
  have hn : 2 < q := by omega
  rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ', cyclic_band_mul_row q D S hq2,
    cyclic_band_square_shift q D S hq2,
    cyclic_band_power_diagonal_before_wrap q D S hq2 2 hn (j + 1)]
  noncomm_ring

end

end FugledeAudit
