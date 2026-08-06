import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.Certificates
import ACMaxConjecture.SmallCases.N18.Core

/-!
# Per-hub good-`C₄` share bound for the `n = 18`, `P₄`-cherry `|D| ∈ {9, 10}` hub-triangle corner

The `|D| ∈ {9, 10}` corner has non-uniform hub degrees (one degree-`5` hub for `|D| = 9`, two
degree-`5` or one degree-`6` for `|D| = 10`), so the global-degree-`4` hypothesis of
`nonadj_hubs_share_le_one_iso` (`TwinCert17Core`) does not apply.  This file restates that share
bound with **per-hub** degree hypotheses: its proof only ever uses the degrees of the two named
hubs, so requiring `G.degree h₁ = 4` and `G.degree h₂ = 4` (rather than `∀ w ∈ Dᶜ`) suffices.
-/

namespace ACMax

open scoped Classical

namespace N18

/-- **Per-hub good-`C₄` share bound.**  Two distinct non-adjacent degree-`4` hubs `h₁, h₂` share at
most one `M`-isolated twin: two shared twins `t₁, t₂` would form an induced `C₄` `h₁–t₁–h₂–t₂` with
`Σ deg = 4 + 4 + 3 + 3 = 14 ≤ 14`, excluded by `hC4`.  Unlike `nonadj_hubs_share_le_one_iso` this
needs only the two named hubs to have degree `4`, not all of `Dᶜ`. -/
theorem nonadj_deg4_hubs_share_le_one_iso_pointwise (G : SimpleGraph (Fin 18))
    (D Iso : Finset (Fin 18))
    (hC4 : ¬∃ a b c d : Fin 18, ({a, b, c, d} : Finset (Fin 18)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (hIsoD : Iso ⊆ D)
    (hIsoprop : ∀ v ∈ Iso, G.degree v = 3 ∧ (∀ w : Fin 18, G.Adj v w → G.degree w ≠ 3))
    (h₁ h₂ : Fin 18) (h1Dc : h₁ ∈ Dᶜ) (h2Dc : h₂ ∈ Dᶜ)
    (hd1 : G.degree h₁ = 4) (hd2 : G.degree h₂ = 4)
    (hne : h₁ ≠ h₂) (hnadj : ¬G.Adj h₁ h₂) :
    ((G.neighborFinset h₁ ∩ G.neighborFinset h₂) ∩ Iso).card ≤ 1 := by
  classical
  by_contra hgt
  rw [not_le] at hgt
  obtain ⟨t₁, ht1, t₂, ht2, h12⟩ := Finset.one_lt_card.mp hgt
  have unpack : ∀ t : Fin 18, t ∈ (G.neighborFinset h₁ ∩ G.neighborFinset h₂) ∩ Iso →
      G.Adj h₁ t ∧ G.Adj h₂ t ∧ t ∈ Iso := by
    intro t ht
    rw [Finset.mem_inter, Finset.mem_inter, G.mem_neighborFinset, G.mem_neighborFinset] at ht
    exact ⟨ht.1.1, ht.1.2, ht.2⟩
  obtain ⟨ha1, hb1, hI1⟩ := unpack t₁ ht1
  obtain ⟨ha2, hb2, hI2⟩ := unpack t₂ ht2
  have htw_nonadj : ¬G.Adj t₁ t₂ := fun hst => (hIsoprop t₁ hI1).2 t₂ hst ((hIsoprop t₂ hI2).1)
  have hti_ne : ∀ t : Fin 18, t ∈ Iso → h₁ ≠ t ∧ h₂ ≠ t := by
    intro t ht
    have htD : t ∈ D := hIsoD ht
    exact ⟨fun e => (Finset.mem_compl.mp h1Dc) (e ▸ htD),
      fun e => (Finset.mem_compl.mp h2Dc) (e ▸ htD)⟩
  obtain ⟨hh1t1, hh2t1⟩ := hti_ne t₁ hI1
  obtain ⟨hh1t2, hh2t2⟩ := hti_ne t₂ hI2
  apply hC4
  refine ⟨h₁, t₁, h₂, t₂, ?_, ha1, hb1.symm, hb2, ha2.symm, hnadj, htw_nonadj, ?_⟩
  · rw [Finset.card_insert_of_notMem (by simp [hh1t1, hne, hh1t2]),
      Finset.card_insert_of_notMem (by simp [Ne.symm hh2t1, h12]),
      Finset.card_insert_of_notMem (by simp [hh2t2]), Finset.card_singleton]
  · have e3 := (hIsoprop t₁ hI1).1
    have e4 := (hIsoprop t₂ hI2).1
    omega

end N18

end ACMax
