import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Finset.Card

set_option autoImplicit false

/-!
# Literal statement targets for the square-free manuscript

These definitions fix the mathematical goals. Defining a proposition is not
proving it. In particular, no result in this module establishes either of the
two main statement targets at the bottom of this file.
-/

namespace FugledeAudit

noncomputable def cyclicFourierEntry {N : ℕ} [NeZero N] (a ξ : ZMod N) : ℂ :=
  ZMod.stdAddChar (a * ξ)

/-- Nonempty, equal-cardinality sets with the actual Fourier zero conditions.
The convention uses positive characters; changing all signs is immaterial but
is not silently substituted in the definitions. -/
def IsCyclicSpectralPair {N : ℕ} [NeZero N] (A Λ : Finset (ZMod N)) : Prop :=
  A.Nonempty ∧ A.card = Λ.card ∧
    ∀ ξ ∈ Λ, ∀ μ ∈ Λ, ξ ≠ μ → ∑ a ∈ A, cyclicFourierEntry a (ξ - μ) = 0

def IsCyclicSpectralSet {N : ℕ} [NeZero N] (A : Finset (ZMod N)) : Prop :=
  ∃ Λ : Finset (ZMod N), IsCyclicSpectralPair A Λ

/-- Every group element has exactly one ordered pair of summands. -/
def IsExactTilingPair {G : Type*} [AddGroup G] (A T : Finset G) : Prop :=
  ∀ x : G, ∃! p : {a // a ∈ A} × {t // t ∈ T}, p.1.val + p.2.val = x

def IsTranslationalTile {G : Type*} [AddGroup G] (A : Finset G) : Prop :=
  ∃ T : Finset G, IsExactTilingPair A T

def squareFreeMainStatement : Prop :=
  ∀ (N : ℕ) [NeZero N], Squarefree N → ∀ A : Finset (ZMod N),
    IsCyclicSpectralSet A → IsTranslationalTile A

def squareFreeEquivalenceStatement : Prop :=
  ∀ (N : ℕ) [NeZero N], Squarefree N → ∀ A : Finset (ZMod N),
    IsCyclicSpectralSet A ↔ IsTranslationalTile A

def reducePrimeFactor (q H : ℕ) : ZMod (q * H) →+* ZMod H :=
  ZMod.castHom (dvd_mul_left H q) (ZMod H)

def automaticPrimeStepDescentStatement : Prop :=
  ∀ (q H : ℕ) [NeZero q] [NeZero H], q.Prime → 3 ≤ q → Nat.Coprime q H →
    ∀ A Λ : Finset (ZMod (q * H)), IsCyclicSpectralPair A Λ → ¬ q ∣ A.card →
      Set.InjOn (reducePrimeFactor q H) (A : Set (ZMod (q * H))) ∧
      Set.InjOn (reducePrimeFactor q H) (Λ : Set (ZMod (q * H))) ∧
      IsCyclicSpectralPair (A.image (reducePrimeFactor q H)) (Λ.image (reducePrimeFactor q H)) ∧
      (IsTranslationalTile (A.image (reducePrimeFactor q H)) → IsTranslationalTile A) ∧
      (IsTranslationalTile (Λ.image (reducePrimeFactor q H)) → IsTranslationalTile Λ)

end FugledeAudit
