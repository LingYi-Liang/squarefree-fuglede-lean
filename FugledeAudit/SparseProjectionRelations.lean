import FugledeAudit.ProjectionBlocks

set_option autoImplicit false

/-!
# Actual zero-block relations, including the q = 3 endpoint

The sparse-power hypothesis is still an input from Lemma 3.1, not a proved
consequence of a spectral pair in this module. Within that interface, the
second and third relations are derived, rather than separately assumed.
-/

namespace FugledeAudit

theorem cyclic_next_ne_later
    (q r : ℕ) (hr : 2 ≤ r) (hrq : r < q) (j : ZMod q) :
    j + 1 ≠ j + (r : ZMod q) := by
  intro h
  have hc : ((1 : ℕ) : ZMod q) = (r : ZMod q) := by
    simpa only [Nat.cast_one] using (add_left_cancel h : (1 : ZMod q) = (r : ZMod q))
  have hm := (ZMod.natCast_eq_natCast_iff' 1 r q).mp hc
  rw [Nat.mod_eq_of_lt (by omega : 1 < q), Nat.mod_eq_of_lt hrq] at hm
  omega

theorem sparse_powers_square_shift_zero
    (q : ℕ) [NeZero q] (hq : 3 ≤ q) {R : Type*} [Ring R]
    (Q : ZMod q → R) (U : R)
    (hsparse : ∀ r : ℕ, 1 ≤ r → r < q → ∀ j k,
      k ≠ j → k ≠ j + (r : ZMod q) → Q j * U ^ r * Q k = 0)
    (j : ZMod q) : Q j * U ^ 2 * Q (j + 1) = 0 := by
  exact hsparse 2 (by decide) (by omega) j (j + 1)
    (cyclic_successor_ne q (by omega) j) (cyclic_next_ne_later q 2 (by decide) (by omega) j)

theorem sparse_powers_cube_shift_zero
    (q : ℕ) [NeZero q] (hq : 3 ≤ q) {R : Type*} [Ring R]
    (Q : ZMod q → R) (horth : ∀ j k, j ≠ k → Q j * Q k = 0)
    (U : R) (hU : U ^ q = 1)
    (hsparse : ∀ r : ℕ, 1 ≤ r → r < q → ∀ j k,
      k ≠ j → k ≠ j + (r : ZMod q) → Q j * U ^ r * Q k = 0)
    (j : ZMod q) : Q j * U ^ 3 * Q (j + 1) = 0 := by
  by_cases hq3 : q = 3
  · have hcube : U ^ 3 = 1 := by simpa only [hq3] using hU
    rw [hcube, mul_one]
    exact horth j (j + 1) (cyclic_successor_ne q (by omega) j).symm
  · exact hsparse 3 (by decide) (by omega) j (j + 1)
      (cyclic_successor_ne q (by omega) j) (cyclic_next_ne_later q 3 (by decide) (by omega) j)

/-- All three ambient relations used by the residual-block argument follow
from one sparse-power interface and the projection identities. Restriction to
the constructed residual subspaces remains a separate, explicit task. -/
theorem actual_projection_block_relations
    (q : ℕ) [NeZero q] (hq : 3 ≤ q) {R : Type*} [Ring R]
    (Q : ZMod q → R) (hQ : ∀ j, Q j * Q j = Q j)
    (horth : ∀ j k, j ≠ k → Q j * Q k = 0) (hsum : ∑ j, Q j = 1)
    (U : R) (hU : U ^ q = 1)
    (hsparse : ∀ r : ℕ, 1 ≤ r → r < q → ∀ j k,
      k ≠ j → k ≠ j + (r : ZMod q) → Q j * U ^ r * Q k = 0) :
    ∀ j : ZMod q,
      Q j = (Q j * U * Q j) ^ q +
        (Q j * U ^ (q - 1) * Q (j - 1)) * (Q (j - 1) * U * Q j) ∧
      (Q j * U * Q j) * (Q j * U * Q (j + 1)) +
        (Q j * U * Q (j + 1)) * (Q (j + 1) * U * Q (j + 1)) = 0 ∧
      (Q j * U * Q j) ^ 2 * (Q j * U * Q (j + 1)) +
        (Q j * U * Q j) * (Q j * U * Q (j + 1)) * (Q (j + 1) * U * Q (j + 1)) +
        (Q j * U * Q (j + 1)) * (Q (j + 1) * U * Q (j + 1)) ^ 2 = 0 := by
  have hs : ∀ j k, k ≠ j → k ≠ j + 1 → Q j * U * Q k = 0 := by
    intro j k h1 h2
    simpa only [pow_one] using hsparse 1 (by decide) (by omega) j k h1
      (by simpa only [Nat.cast_one] using h2)
  intro j
  refine ⟨actual_projection_qth_return q hq Q hQ hsum U hU hs j, ?_, ?_⟩
  · rw [← actual_projection_square_shift q hq Q hQ hsum U hs j]
    exact sparse_powers_square_shift_zero q hq Q U hsparse j
  · rw [← actual_projection_cube_shift q hq Q hQ hsum U hs j]
    exact sparse_powers_cube_shift_zero q hq Q horth U hU hsparse j

end FugledeAudit
