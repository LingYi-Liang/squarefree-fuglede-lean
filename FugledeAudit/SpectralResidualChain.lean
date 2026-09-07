import FugledeAudit.ActualSparsePowers
import FugledeAudit.ResidualEigenvalue

set_option autoImplicit false

namespace FugledeAudit

theorem spectral_prime_unitary_order
    (q H : ℕ) [NeZero q] [NeZero H]
    (A Λ : Finset (ZMod (q * H))) (h : IsCyclicSpectralPair A Λ) :
    (spectralPrimeUnitary q H A Λ h).toLinearMap ^ q = 1 :=
  conjugated_phase_order _ _

theorem spectral_prime_levels_orthogonal
    (q H : ℕ) [NeZero q] [NeZero H] (Λ : Finset (ZMod (q * H))) :
    Pairwise fun j k => (spectralPrimeLevels q H Λ j).IsOrtho (spectralPrimeLevels q H Λ k) :=
  coordinate_levels_pairwise_orthogonal _

theorem spectral_prime_projections_sum
    (q H : ℕ) [NeZero q] [NeZero H] (Λ : Finset (ZMod (q * H))) :
    ∑ j, (spectralPrimeLevels q H Λ j).starProjection.toLinearMap = 1 :=
  coordinate_projections_sum _

/-- The residual-block conclusion now starts at a literal cyclic spectral pair.
In particular sparse powers, finite order, and the level decomposition are
derived rather than supplied as extra hypotheses. -/
theorem spectral_pair_residual_chain
    (q H : ℕ) [NeZero q] [NeZero H] (hq : q.Prime) (hq3 : 3 ≤ q)
    (hcop : Nat.Coprime q H)
    (A Λ : Finset (ZMod (q * H))) (h : IsCyclicSpectralPair A Λ) :
    let U := spectralPrimeUnitary q H A Λ h
    let L := spectralPrimeLevels q H Λ
    let ω := ZMod.stdAddChar (1 : ZMod q)
    (∀ j, unitaryCompression U (localResidual U.toLinearMap (L j) ω q) = 0) ∧
    (∀ j, Function.Bijective (residualPowerBlock U L ω q 1 j (j + 1)) ∧
      ∀ v, ‖residualPowerBlock U L ω q 1 j (j + 1) v‖ = ‖v‖) := by
  apply actual_residual_diagonal_zero_and_unitary_shifts
    (spectralPrimeUnitary q H A Λ h) q hq3 _ standard_character_primitive_root
    (spectral_prime_unitary_order q H A Λ h) (spectralPrimeLevels q H Λ)
    (spectral_prime_levels_orthogonal q H Λ) (spectral_prime_projections_sum q H Λ)
  intro r _ _ j k hkj hkr
  exact spectral_pair_sparse_powers q H hq hcop A Λ h r j k hkj hkr

theorem spectral_pair_residual_averaged_eigenvector
    (q H : ℕ) [NeZero q] [NeZero H] (hq : q.Prime) (hq3 : 3 ≤ q)
    (hcop : Nat.Coprime q H)
    (A Λ : Finset (ZMod (q * H))) (h : IsCyclicSpectralPair A Λ)
    (c : Fin q → ℂ) (hc : c 0 = 1) (j : ZMod q)
    (v : localResidual (spectralPrimeUnitary q H A Λ h).toLinearMap
      (spectralPrimeLevels q H Λ j) (ZMod.stdAddChar (1 : ZMod q)) q) :
    (spectralPrimeLevels q H Λ j).starProjection
      (averagedPowers (spectralPrimeUnitary q H A Λ h).toLinearMap q c
        ((spectralPrimeLevels q H Λ j).starProjection (v : EuclideanSpace ℂ Λ))) =
      (q : ℂ)⁻¹ • (v : EuclideanSpace ℂ Λ) := by
  apply actual_residual_averaged_power_eigenvector
    (spectralPrimeUnitary q H A Λ h) q hq3 _ standard_character_primitive_root
    (spectral_prime_unitary_order q H A Λ h) (spectralPrimeLevels q H Λ)
    (spectral_prime_levels_orthogonal q H Λ) (spectral_prime_projections_sum q H Λ)
    (fun r _ _ j k hkj hkr => spectral_pair_sparse_powers q H hq hcop A Λ h r j k hkj hkr)
    c hc j v

end FugledeAudit
