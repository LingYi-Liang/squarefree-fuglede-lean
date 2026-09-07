import FugledeAudit.MainStatementCheck
import FugledeAudit.UnitInvariance
import FugledeAudit.HadamardConsequences

set_option autoImplicit false

example : FugledeAudit.squareFreeMainStatement := FugledeAudit.square_free_spectral_sets_tile
example : FugledeAudit.automaticPrimeStepDescentStatement := FugledeAudit.automatic_prime_step_descent

example (H : ℕ) [NeZero H] (u : (ZMod H)ˣ) (B L : Finset (ZMod H)) :
    FugledeAudit.IsCyclicSpectralPair B L ↔
      FugledeAudit.IsCyclicSpectralPair B (L.image (fun x => (u : ZMod H) * x)) :=
  FugledeAudit.spectral_pair_unit_invariance H u B L

example (H : ℕ) [NeZero H] (u : (ZMod H)ˣ) (B : Finset (ZMod H)) :
    FugledeAudit.IsTranslationalTile B ↔
      FugledeAudit.IsTranslationalTile (B.image (fun x => (u : ZMod H) * x)) :=
  FugledeAudit.tiling_unit_invariance H u B

example (N : ℕ) [NeZero N] (hN : Squarefree N) (A Λ : Finset (ZMod N))
    (hA : A.Nonempty) (hcard : A.card = Λ.card)
    (hgram : FugledeAudit.restrictedFourierMatrix A Λ *
      (FugledeAudit.restrictedFourierMatrix A Λ).conjTranspose = (A.card : ℂ) • 1) :
    FugledeAudit.IsTranslationalTile A ∧ FugledeAudit.IsTranslationalTile Λ ∧ A.card ∣ N :=
  FugledeAudit.squarefree_hadamard_rows_columns_tile N hN A Λ hA hcard hgram

#check FugledeAudit.checked_main_statement
#print axioms FugledeAudit.checked_main_statement
#print axioms FugledeAudit.automatic_prime_step_descent
