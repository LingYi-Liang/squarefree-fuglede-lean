import FugledeAudit.PrimeCollision

set_option autoImplicit false

namespace FugledeAudit

theorem whole_group_tiles
    (G : Type*) [AddGroup G] [Fintype G] [DecidableEq G] :
    IsTranslationalTile (Finset.univ : Finset G) := by
  refine ⟨{0}, ?_⟩
  intro x
  refine ⟨(⟨x, Finset.mem_univ x⟩, ⟨0, Finset.mem_singleton_self 0⟩), by simp, ?_⟩
  intro v hv
  have ht : v.2.val = 0 := Finset.mem_singleton.mp v.2.property
  apply Prod.ext
  · apply Subtype.ext
    simpa only [ht, add_zero] using hv
  · exact Subtype.ext ht

theorem squarefree_dvd_twice_of_odd_primes_dvd
    (N m : ℕ) (hs : Squarefree N) (hm : 0 < m)
    (hp : ∀ q, q.Prime → 3 ≤ q → q ∣ N → q ∣ m) : N ∣ 2 * m := by
  have hm2 : 2 * m ≠ 0 := by omega
  have hd : (∏ q ∈ N.primeFactors, q) ∣ 2 * m := by
    apply (Nat.prod_primeFactors_dvd_iff hm2).mpr
    intro q hqN
    obtain ⟨hq, hqN, _⟩ := Nat.mem_primeFactors.mp hqN
    apply Nat.mem_primeFactors.mpr
    refine ⟨hq, ?_, hm2⟩
    by_cases hq2 : q = 2
    · subst q
      exact dvd_mul_right 2 m
    · exact dvd_mul_of_dvd_right (hp q hq (by have := hq.two_le; omega) hqN) 2
  simpa only [Nat.prod_primeFactors_of_squarefree hs] using hd

theorem size_eq_order_or_half
    (N m : ℕ) (hm : 0 < m) (hmN : m ≤ N) (hd : N ∣ 2 * m) :
    m = N ∨ N = 2 * m := by
  obtain ⟨k, hk⟩ := hd
  have hN : 0 < N := by omega
  have hkpos : 0 < k := by nlinarith
  have hkle : k ≤ 2 := by nlinarith
  interval_cases k <;> omega

theorem half_order_spectral_set_tiles
    (H : ℕ) [NeZero H] (hs : Squarefree (2 * H))
    (A Λ : Finset (ZMod (2 * H))) (h : IsCyclicSpectralPair A Λ) (hm : A.card = H) :
    IsTranslationalTile A := by
  classical
  have hcop := Nat.coprime_of_squarefree_mul hs
  have hnd : ¬2 ∣ A.card := by
    rw [hm]
    intro hd
    have hg : Nat.gcd 2 H = 2 := Nat.gcd_eq_left hd
    rw [hcop.gcd_eq_one] at hg
    omega
  have hi := spectral_physical_projection_injective_any_prime 2 H Nat.prime_two hcop A Λ h hnd
  have hfull : A.image (reducePrimeFactor 2 H) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_image_of_injOn hi, hm, ZMod.card]
  apply quotient_lifts_tiling (reducePrimeFactor 2 H).toAddMonoidHom A hi
  rw [show A.image (reducePrimeFactor 2 H).toAddMonoidHom = Finset.univ from hfull]
  exact whole_group_tiles (ZMod H)

/-- The manuscript's spectral-to-tiling main theorem with the literal finite
cyclic definitions. The order-two endpoint is not fed through the q >= 3
operator lemma. -/
theorem square_free_spectral_sets_tile : squareFreeMainStatement := by
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro inst hs A hA
    classical
    obtain ⟨Λ, h⟩ := hA
    by_cases hex : ∃ q, q.Prime ∧ 3 ≤ q ∧ q ∣ N ∧ ¬q ∣ A.card
    · obtain ⟨q, hq, hq3, hqN, hnd⟩ := hex
      obtain ⟨H, rfl⟩ := hqN
      let : NeZero q := ⟨hq.ne_zero⟩
      have hH : H ≠ 0 := by
        intro hz
        have hn := NeZero.ne (q * H)
        simp [hz] at hn
      let : NeZero H := ⟨hH⟩
      have hcop := Nat.coprime_of_squarefree_mul hs
      have hsH : Squarefree H := hs.of_mul_right
      have hlt : H < q * H := by nlinarith [Nat.pos_of_ne_zero hH]
      have hd := automatic_prime_step_descent q H hq hq3 hcop A Λ h hnd
      have ht : IsTranslationalTile (A.image (reducePrimeFactor q H)) :=
        ih H hlt hsH _ ⟨Λ.image (reducePrimeFactor q H), hd.2.2.1⟩
      exact hd.2.2.2.1 ht
    · have hp : ∀ q, q.Prime → 3 ≤ q → q ∣ N → q ∣ A.card := by
        intro q hq hq3 hqN
        by_contra hnd
        exact hex ⟨q, hq, hq3, hqN, hnd⟩
      have hmpos : 0 < A.card := Finset.card_pos.mpr h.1
      have hmle : A.card ≤ N := by simpa only [ZMod.card] using A.card_le_univ
      have hd := squarefree_dvd_twice_of_odd_primes_dvd N A.card hs hmpos hp
      rcases size_eq_order_or_half N A.card hmpos hmle hd with hfull | hhalf
      · have he : A = Finset.univ := Finset.eq_univ_of_card A (by simpa only [ZMod.card] using hfull)
        rw [he]
        exact whole_group_tiles (ZMod N)
      · have h2 : 2 ∣ N := ⟨A.card, hhalf⟩
        obtain ⟨H, rfl⟩ := h2
        have hH : H ≠ 0 := by
          intro hz
          have hn := NeZero.ne (2 * H)
          simp [hz] at hn
        let : NeZero H := ⟨hH⟩
        exact half_order_spectral_set_tiles H hs A Λ h (by omega)

end FugledeAudit
