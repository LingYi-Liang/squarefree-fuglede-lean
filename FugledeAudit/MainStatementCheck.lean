import FugledeAudit.SquarefreeClosure

set_option autoImplicit false

namespace FugledeAudit

/-- An expanded statement check: the assumptions contain the original
characters and finite sets, and the conclusion includes unique representation
in the original cyclic group. No intermediate operator conditions appear. -/
theorem checked_main_statement
    (N : ℕ) [NeZero N] (hN : Squarefree N) (A : Finset (ZMod N))
    (hA : ∃ Λ : Finset (ZMod N), A.Nonempty ∧ A.card = Λ.card ∧
      ∀ ξ ∈ Λ, ∀ μ ∈ Λ, ξ ≠ μ →
        ∑ a ∈ A, ZMod.stdAddChar (a * (ξ - μ)) = 0) :
    ∃ T : Finset (ZMod N), ∀ x : ZMod N,
      ∃! p : {a // a ∈ A} × {t // t ∈ T}, p.1.val + p.2.val = x := by
  exact square_free_spectral_sets_tile N hN A hA

end FugledeAudit
