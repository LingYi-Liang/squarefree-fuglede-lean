import FugledeAudit.CyclotomicUnitTransfer
import FugledeAudit.ActualTilingLift

set_option autoImplicit false

namespace FugledeAudit

theorem spectral_pair_unit_image
    (H : ℕ) [NeZero H] (u : (ZMod H)ˣ) (B L : Finset (ZMod H))
    (h : IsCyclicSpectralPair B L) :
    IsCyclicSpectralPair B (L.image (fun x => (u : ZMod H) * x)) := by
  classical
  have hinj : Function.Injective (fun x : ZMod H => (u : ZMod H) * x) := by
    intro x y he
    have ht := congrArg (fun z => (↑u⁻¹ : ZMod H) * z) he
    simpa only [← mul_assoc, Units.inv_mul, one_mul] using ht
  refine ⟨h.1, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hinj]
    exact h.2.1
  · intro ξ hξ μ hμ hne
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hξ
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hμ
    have hxy : x ≠ y := fun he => hne (congrArg _ he)
    have hz : ∑ a : B, ZMod.stdAddChar (a.val * (x - y)) = 0 := by
      exact (Finset.sum_coe_sort B (fun a => ZMod.stdAddChar (a * (x - y)))).trans
        (h.2.2 x hx y hy hxy)
    have ht := standard_character_unit_sum_transfer H (u : ZMod H).val
      (ZMod.val_coe_unit_coprime u) (fun a : B => a.val * (x - y)) hz
    simp only [ZMod.natCast_zmod_val] at ht
    rw [Finset.sum_coe_sort B (fun a => ZMod.stdAddChar ((u : ZMod H) * (a * (x - y))))] at ht
    simpa only [cyclicFourierEntry, ← mul_sub, mul_left_comm] using ht

/-- The two-sided assertion in Lemma 2.1, for the literal frequency set. -/
theorem spectral_pair_unit_invariance
    (H : ℕ) [NeZero H] (u : (ZMod H)ˣ) (B L : Finset (ZMod H)) :
    IsCyclicSpectralPair B L ↔
      IsCyclicSpectralPair B (L.image (fun x => (u : ZMod H) * x)) := by
  classical
  refine ⟨spectral_pair_unit_image H u B L, ?_⟩
  intro h
  have ht := spectral_pair_unit_image H u⁻¹ B _ h
  simpa only [Finset.image_image, Function.comp_def, ← mul_assoc, Units.inv_mul,
    one_mul, Finset.image_id'] using ht

theorem tiling_add_equiv_invariance
    {G H : Type*} [AddCommGroup G] [AddCommGroup H] [Fintype G] [Fintype H]
    [DecidableEq G] [DecidableEq H] (e : G ≃+ H) (A : Finset G) :
    IsTranslationalTile A ↔ IsTranslationalTile (A.image e) := by
  constructor
  · intro h
    apply quotient_lifts_tiling e.symm.toAddMonoidHom (A.image e) e.symm.injective.injOn
    simpa only [Finset.image_image, Function.comp_def, AddEquiv.coe_toAddMonoidHom, e.symm_apply_apply,
      Finset.image_id'] using h
  · exact quotient_lifts_tiling e.toAddMonoidHom A e.injective.injOn

def unitAddEquiv (H : ℕ) (u : (ZMod H)ˣ) : ZMod H ≃+ ZMod H where
  toFun x := (u : ZMod H) * x
  invFun x := (↑u⁻¹ : ZMod H) * x
  left_inv x := by simp only [← mul_assoc, Units.inv_mul, one_mul]
  right_inv x := by simp only [← mul_assoc, Units.mul_inv, one_mul]
  map_add' x y := mul_add _ _ _

theorem tiling_unit_invariance
    (H : ℕ) [NeZero H] (u : (ZMod H)ˣ) (B : Finset (ZMod H)) :
    IsTranslationalTile B ↔
      IsTranslationalTile (B.image (fun x => (u : ZMod H) * x)) :=
  tiling_add_equiv_invariance (unitAddEquiv H u) B

end FugledeAudit
