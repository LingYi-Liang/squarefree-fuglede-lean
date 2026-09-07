import FugledeAudit.ActualSpectralDescent

set_option autoImplicit false

namespace FugledeAudit

/-- The graph lift written in the original group: the complement is the full
inverse image of the quotient complement. Injectivity is required on A only. -/
theorem quotient_lifts_exact_tiling
    {G H : Type*} [AddCommGroup G] [AddCommGroup H] [Fintype G]
    [DecidableEq G] [DecidableEq H]
    (π : G →+ H) (A : Finset G) (T : Finset H)
    (hinj : Set.InjOn π (A : Set G)) (h : IsExactTilingPair (A.image π) T) :
    IsExactTilingPair A (Finset.univ.filter (fun t => π t ∈ T)) := by
  intro x
  obtain ⟨p, hp, hu⟩ := h (π x)
  obtain ⟨a, ha, hap⟩ := Finset.mem_image.mp p.1.property
  have ht : x - a ∈ Finset.univ.filter (fun t => π t ∈ T) := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    have he : π (x - a) = p.2.val := by
      rw [map_sub, ← hp, hap]
      abel
    rw [he]
    exact p.2.property
  let w : {a // a ∈ A} × {t // t ∈ Finset.univ.filter (fun t => π t ∈ T)} :=
    (⟨a, ha⟩, ⟨x - a, ht⟩)
  refine ⟨w, by change a + (x - a) = x; abel, ?_⟩
  intro v hv
  let vp : {b // b ∈ A.image π} × {t // t ∈ T} :=
    (⟨π v.1.val, Finset.mem_image.mpr ⟨v.1.val, v.1.property, rfl⟩⟩,
      ⟨π v.2.val, (Finset.mem_filter.mp v.2.property).2⟩)
  have hvp : vp.1.val + vp.2.val = π x := by
    change π v.1.val + π v.2.val = π x
    rw [← map_add, hv]
  have he := hu vp hvp
  have hav : v.1.val = a := by
    apply hinj v.1.property ha
    exact (congrArg (fun z => z.1.val) he).trans hap.symm
  apply Prod.ext
  · exact Subtype.ext hav
  · apply Subtype.ext
    change v.2.val = x - a
    rw [hav] at hv
    exact eq_sub_iff_add_eq.mpr (by simpa only [add_comm] using hv)

theorem quotient_lifts_tiling
    {G H : Type*} [AddCommGroup G] [AddCommGroup H] [Fintype G]
    [DecidableEq G] [DecidableEq H]
    (π : G →+ H) (A : Finset G) (hinj : Set.InjOn π (A : Set G))
    (h : IsTranslationalTile (A.image π)) : IsTranslationalTile A := by
  obtain ⟨T, hT⟩ := h
  exact ⟨Finset.univ.filter (fun t => π t ∈ T), quotient_lifts_exact_tiling π A T hinj hT⟩

/-- The full literal prime-step statement, including both injections,
spectrality of the actual images, and both tiling lifts. -/
theorem automatic_prime_step_descent : automaticPrimeStepDescentStatement := by
  intro q H _ _ hq hq3 hcop A Λ h hnd
  classical
  have hA := spectral_pair_physical_projection_injective q H hq hq3 hcop A Λ h hnd
  have hΛ := spectral_pair_frequency_projection_injective q H hq hq3 hcop A Λ h hnd
  refine ⟨hA, hΛ, spectral_pair_reduction_is_spectral q H hq hq3 hcop A Λ h hnd, ?_, ?_⟩
  · exact quotient_lifts_tiling (reducePrimeFactor q H).toAddMonoidHom A hA
  · exact quotient_lifts_tiling (reducePrimeFactor q H).toAddMonoidHom Λ hΛ

end FugledeAudit
