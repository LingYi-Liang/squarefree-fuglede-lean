import FugledeAudit.SparseBlockPowers

set_option autoImplicit false

/-!
# From actual projection blocks to the general-q matrix identities

All entries live in a single ambient operator ring. This does not identify
the distinct level subspaces with each other. The projection-block map is
multiplicative but is deliberately not declared unital: its identity block
is Q_j, not the identity of the whole ambient space.
-/

namespace FugledeAudit

open Matrix

def projectionBlocks {ι R : Type*} [Ring R] (Q : ι → R) (U : R) : Matrix ι ι R :=
  fun j k => Q j * U * Q k

theorem projection_blocks_mul
    {ι R : Type*} [Fintype ι] [Ring R] (Q : ι → R)
    (hQ : ∀ j, Q j * Q j = Q j) (hsum : ∑ j, Q j = 1) (U V : R) :
    projectionBlocks Q U * projectionBlocks Q V = projectionBlocks Q (U * V) := by
  ext j k
  change (∑ i, (Q j * U * Q i) * (Q i * V * Q k)) = Q j * (U * V) * Q k
  calc
    _ = ∑ i, (Q j * U) * Q i * (V * Q k) := by
      apply Finset.sum_congr rfl
      intro i _
      calc
        _ = (Q j * U) * (Q i * Q i) * (V * Q k) := by noncomm_ring
        _ = _ := by rw [hQ i]
    _ = (Q j * U) * (∑ i, Q i) * (V * Q k) := by
      simp only [Finset.sum_mul, Finset.mul_sum]
    _ = _ := by rw [hsum]; noncomm_ring

/-- Only positive powers are asserted: matrix power zero has ambient I on
the diagonal, while the blockification of U^0 has Q_j on the diagonal. -/
theorem projection_blocks_positive_power
    {ι R : Type*} [Fintype ι] [DecidableEq ι] [Ring R] (Q : ι → R)
    (hQ : ∀ j, Q j * Q j = Q j) (hsum : ∑ j, Q j = 1) (U : R)
    (n : ℕ) (hn : 0 < n) : projectionBlocks Q U ^ n = projectionBlocks Q (U ^ n) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  clear hn
  induction n with
  | zero => simp only [pow_one]
  | succ n ih =>
    calc
      _ = (projectionBlocks Q U ^ n.succ) * projectionBlocks Q U := pow_succ _ _
      _ = projectionBlocks Q (U ^ n.succ) * projectionBlocks Q U := by rw [ih]
      _ = projectionBlocks Q (U ^ n.succ * U) := projection_blocks_mul Q hQ hsum _ _
      _ = _ := by rw [← pow_succ]

theorem projection_blocks_eq_cyclic_band
    (q : ℕ) [NeZero q] {R : Type*} [Ring R] (Q : ZMod q → R) (U : R)
    (hsparse : ∀ j k, k ≠ j → k ≠ j + 1 → Q j * U * Q k = 0) :
    projectionBlocks Q U = cyclicBand q
      (fun j => Q j * U * Q j) (fun j => Q j * U * Q (j + 1)) := by
  ext j k
  by_cases h1 : k = j
  · subst k; simp [projectionBlocks, cyclicBand]
  · by_cases h2 : k = j + 1
    · subst k; simp [projectionBlocks, cyclicBand, h1]
    · simp [projectionBlocks, cyclicBand, h1, h2, hsparse j k h1 h2]

theorem actual_projection_short_diagonal
    (q : ℕ) [NeZero q] (hq : 2 ≤ q) {R : Type*} [Ring R]
    (Q : ZMod q → R) (hQ : ∀ j, Q j * Q j = Q j) (hsum : ∑ j, Q j = 1)
    (U : R) (hsparse : ∀ j k, k ≠ j → k ≠ j + 1 → Q j * U * Q k = 0)
    (n : ℕ) (hn : 0 < n) (hnq : n < q) (j : ZMod q) :
    Q j * U ^ n * Q j = (Q j * U * Q j) ^ n := by
  have h := cyclic_band_power_diagonal_before_wrap q (fun j => Q j * U * Q j)
    (fun j => Q j * U * Q (j + 1)) hq n hnq j
  rw [← projection_blocks_eq_cyclic_band q Q U hsparse,
    projection_blocks_positive_power Q hQ hsum U n hn] at h
  exact h

/-- The q-th return identity for the actual ambient projection blocks. -/
theorem actual_projection_qth_return
    (q : ℕ) [NeZero q] (hq : 3 ≤ q) {R : Type*} [Ring R]
    (Q : ZMod q → R) (hQ : ∀ j, Q j * Q j = Q j) (hsum : ∑ j, Q j = 1)
    (U : R) (hU : U ^ q = 1)
    (hsparse : ∀ j k, k ≠ j → k ≠ j + 1 → Q j * U * Q k = 0)
    (j : ZMod q) :
    Q j = (Q j * U * Q j) ^ q +
      (Q j * U ^ (q - 1) * Q (j - 1)) * (Q (j - 1) * U * Q j) := by
  have hband := projection_blocks_eq_cyclic_band q Q U hsparse
  have hpow (n : ℕ) (hn : 0 < n) :
      cyclicBand q (fun j => Q j * U * Q j) (fun j => Q j * U * Q (j + 1)) ^ n =
      projectionBlocks Q (U ^ n) := by
    rw [← hband]
    exact projection_blocks_positive_power Q hQ hsum U n hn
  have h := cyclic_band_qth_return_identity q (fun j => Q j * U * Q j)
    (fun j => Q j * U * Q (j + 1)) (by omega) j
  rw [hpow q (by omega), hpow (q - 1) (by omega)] at h
  simpa only [projectionBlocks, hU, mul_one, hQ, sub_add_cancel] using h

theorem actual_projection_square_shift
    (q : ℕ) [NeZero q] (hq : 3 ≤ q) {R : Type*} [Ring R]
    (Q : ZMod q → R) (hQ : ∀ j, Q j * Q j = Q j) (hsum : ∑ j, Q j = 1)
    (U : R) (hsparse : ∀ j k, k ≠ j → k ≠ j + 1 → Q j * U * Q k = 0)
    (j : ZMod q) :
    Q j * U ^ 2 * Q (j + 1) =
      (Q j * U * Q j) * (Q j * U * Q (j + 1)) +
      (Q j * U * Q (j + 1)) * (Q (j + 1) * U * Q (j + 1)) := by
  have h := cyclic_band_square_shift q (fun j => Q j * U * Q j)
    (fun j => Q j * U * Q (j + 1)) (by omega) j
  rw [← projection_blocks_eq_cyclic_band q Q U hsparse,
    projection_blocks_positive_power Q hQ hsum U 2 (by decide)] at h
  exact h

theorem actual_projection_cube_shift
    (q : ℕ) [NeZero q] (hq : 3 ≤ q) {R : Type*} [Ring R]
    (Q : ZMod q → R) (hQ : ∀ j, Q j * Q j = Q j) (hsum : ∑ j, Q j = 1)
    (U : R) (hsparse : ∀ j k, k ≠ j → k ≠ j + 1 → Q j * U * Q k = 0)
    (j : ZMod q) :
    Q j * U ^ 3 * Q (j + 1) =
      (Q j * U * Q j) ^ 2 * (Q j * U * Q (j + 1)) +
      (Q j * U * Q j) * (Q j * U * Q (j + 1)) * (Q (j + 1) * U * Q (j + 1)) +
      (Q j * U * Q (j + 1)) * (Q (j + 1) * U * Q (j + 1)) ^ 2 := by
  have h := cyclic_band_cube_shift q (fun j => Q j * U * Q j)
    (fun j => Q j * U * Q (j + 1)) hq j
  rw [← projection_blocks_eq_cyclic_band q Q U hsparse,
    projection_blocks_positive_power Q hQ hsum U 3 (by decide)] at h
  exact h

end FugledeAudit
