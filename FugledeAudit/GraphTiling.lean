import FugledeAudit.PaperStatements
import Mathlib.Data.Finset.Prod

set_option autoImplicit false

namespace FugledeAudit

variable {K H : Type*} [AddCommGroup K] [AddCommGroup H]
  [DecidableEq K] [DecidableEq H]

def graphSet (X : Finset H) (f : H → K) : Finset (K × H) :=
  X.image (fun x => (f x, x))

/-- The graph-lifting argument in the manuscript, with uniqueness of the
tiling decomposition included, not merely coverage. -/
theorem graph_lifts_exact_tiling [Fintype K] (X T : Finset H) (f : H → K)
    (h : IsExactTilingPair X T) :
    IsExactTilingPair (graphSet X f) (Finset.univ.product T) := by
  intro z
  obtain ⟨p, hp, hunique⟩ := h z.2
  let x : H := p.1.val
  let t : H := p.2.val
  have hx : (f x, x) ∈ graphSet X f := Finset.mem_image.mpr ⟨x, p.1.property, rfl⟩
  have ht : (z.1 - f x, t) ∈ Finset.univ.product T := by simp [t, p.2.property]
  let w : {a // a ∈ graphSet X f} × {b // b ∈ Finset.univ.product T} :=
    (⟨(f x, x), hx⟩, ⟨(z.1 - f x, t), ht⟩)
  refine ⟨w, ?_, ?_⟩
  · apply Prod.ext
    · change f x + (z.1 - f x) = z.1
      abel
    · exact hp
  · intro v hv
    obtain ⟨y, hy, hya⟩ := Finset.mem_image.mp v.1.property
    have hvT : v.2.val.2 ∈ T := (Finset.mem_product.mp v.2.property).2
    let p' : {a // a ∈ X} × {b // b ∈ T} := (⟨y, hy⟩, ⟨v.2.val.2, hvT⟩)
    have hp' : p'.1.val + p'.2.val = z.2 := by
      have he := congrArg Prod.snd hv
      change v.1.val.2 + v.2.val.2 = z.2 at he
      rw [← hya] at he
      exact he
    have heq := hunique p' hp'
    have hyx : y = x := congrArg (fun u => u.1.val) heq
    have hvt : v.2.val.2 = t := congrArg (fun u => u.2.val) heq
    apply Prod.ext
    · apply Subtype.ext
      change v.1.val = (f x, x)
      rw [← hya, hyx]
    · apply Subtype.ext
      apply Prod.ext
      · have he := congrArg Prod.fst hv
        change v.1.val.1 + v.2.val.1 = z.1 at he
        rw [← hya, hyx] at he
        change v.2.val.1 = z.1 - f x
        exact eq_sub_iff_add_eq.mpr (by simpa only [add_comm] using he)
      · exact hvt

theorem graph_lifts_tiling [Fintype K] (X : Finset H) (f : H → K)
    (h : IsTranslationalTile X) : IsTranslationalTile (graphSet X f) := by
  obtain ⟨T, hT⟩ := h
  exact ⟨Finset.univ.product T, graph_lifts_exact_tiling X T f hT⟩

end FugledeAudit
