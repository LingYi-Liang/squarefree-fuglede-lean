import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

namespace FugledeAudit

open Polynomial IntermediateField

/-- The relative minimal-polynomial fact used in Lemma 3.1. The only
separation assumption is coprimality of the orders; no size inequality occurs. -/
theorem coprime_cyclotomic_minpoly
    (q H : ℕ) [NeZero q] [NeZero H] (hcop : Nat.Coprime q H)
    (ω η : ℂ) (hω : IsPrimitiveRoot ω q) (hη : IsPrimitiveRoot η H) :
    minpoly (IntermediateField.adjoin ℚ {η}) ω =
      cyclotomic q (IntermediateField.adjoin ℚ {η}) := by
  let K := IntermediateField.adjoin ℚ ({η} : Set ℂ)
  let L := IntermediateField.adjoin K ({ω} : Set ℂ)
  have hηint : IsIntegral ℚ η :=
    IsIntegral.of_pow (NeZero.pos H) (hη.pow_eq_one ▸ isIntegral_one)
  have hωint : IsIntegral K ω :=
    IsIntegral.of_pow (NeZero.pos q) (hω.pow_eq_one ▸ isIntegral_one)
  let : FiniteDimensional ℚ K := IntermediateField.adjoin.finiteDimensional hηint
  let : FiniteDimensional K L := IntermediateField.adjoin.finiteDimensional hωint
  let : FiniteDimensional ℚ L := FiniteDimensional.trans ℚ K L
  have hKcyc : IsCyclotomicExtension {H} ℚ K := by
    change IsCyclotomicExtension {H} ℚ (IntermediateField.adjoin ℚ {η}).toSubalgebra
    rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hηint.isAlgebraic]
    exact hη.adjoin_isCyclotomicExtension ℚ
  have hKdim : Module.finrank ℚ K = H.totient :=
    IsCyclotomicExtension.finrank K (cyclotomic.irreducible_rat (NeZero.pos H))
  have hLdim : Module.finrank K L = (minpoly K ω).natDegree :=
    IntermediateField.adjoin.finrank hωint
  let ηK : K := IntermediateField.AdjoinSimple.gen ℚ η
  let ωL : L := IntermediateField.AdjoinSimple.gen K ω
  have hηK : IsPrimitiveRoot ηK H := by
    apply IsPrimitiveRoot.coe_submonoidClass_iff.mp
    exact hη
  have hωL : IsPrimitiveRoot ωL q := by
    apply IsPrimitiveRoot.coe_submonoidClass_iff.mp
    exact hω
  have hηL : IsPrimitiveRoot (algebraMap K L ηK) H :=
    hηK.map_of_injective (algebraMap K L).injective
  have hlcm : 0 < Nat.lcm q H := by
    rw [hcop.lcm_eq_mul]
    exact Nat.mul_pos (NeZero.pos q) (NeZero.pos H)
  have hlower := hωL.lcm_totient_le_finrank (K := ℚ) hηL
    (cyclotomic.irreducible_rat hlcm)
  rw [hcop.lcm_eq_mul, Nat.totient_mul hcop,
    ← Module.finrank_mul_finrank ℚ K L, hKdim, hLdim] at hlower
  have hdegree : q.totient ≤ (minpoly K ω).natDegree := by
    have hHpos : 0 < H.totient := Nat.totient_pos.mpr (NeZero.pos H)
    nlinarith
  have heval : aeval ω (cyclotomic q K) = 0 := by
    rw [aeval_def, ← eval_map, map_cyclotomic]
    exact hω.isRoot_cyclotomic (NeZero.pos q)
  change minpoly K ω = cyclotomic q K
  symm
  exact eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hωint)
    (cyclotomic.monic q K) (minpoly.dvd K ω heval)
    (by simpa only [natDegree_cyclotomic] using hdegree)

/-- Coefficient rigidity at a prime root over the coprime cyclotomic field.
This includes zero coefficients and the degree-drop case. -/
theorem coprime_prime_coefficient_rigidity
    (q H : ℕ) [NeZero q] [NeZero H] (hq : q.Prime) (hcop : Nat.Coprime q H)
    (ω η : ℂ) (hω : IsPrimitiveRoot ω q) (hη : IsPrimitiveRoot η H)
    (c : Fin q → IntermediateField.adjoin ℚ {η})
    (hzero : ∑ i : Fin q, (c i : ℂ) * ω ^ i.val = 0) :
    ∀ i j : Fin q, c i = c j := by
  classical
  let K := IntermediateField.adjoin ℚ ({η} : Set ℂ)
  let p : K[X] := ∑ i : Fin q, monomial i.val (c i)
  have : Fact q.Prime := ⟨hq⟩
  have hpcoeff (i : Fin q) : p.coeff i.val = c i := by
    simp [p, finsetSum_coeff, coeff_monomial, Fin.val_inj]
  have hdegree : p.natDegree ≤ (cyclotomic q K).natDegree := by
    rw [natDegree_cyclotomic, Nat.totient_prime hq]
    apply natDegree_sum_le_of_forall_le
    intro i _
    exact (natDegree_monomial_le (c i)).trans (by omega)
  have heval : aeval ω p = 0 := by
    simpa [p, aeval_monomial] using hzero
  have hdiv : cyclotomic q K ∣ p := by
    rw [← coprime_cyclotomic_minpoly q H hcop ω η hω hη]
    exact minpoly.dvd K ω heval
  have hpform := eq_mul_leadingCoeff_of_monic_of_dvd_of_natDegree_le
    (cyclotomic.monic q K) hdiv hdegree
  have hcyccoeff (i : Fin q) : (cyclotomic q K).coeff i.val = 1 := by
    simp [cyclotomic_prime, finsetSum_coeff, coeff_X_pow, i.isLt]
  have hc (i : Fin q) : c i = p.leadingCoeff := by
    have he := congrArg (fun P : K[X] => P.coeff i.val) hpform
    rw [hpcoeff, coeff_mul_C, hcyccoeff, one_mul] at he
    exact he
  intro i j
  exact (hc i).trans (hc j).symm

end FugledeAudit
