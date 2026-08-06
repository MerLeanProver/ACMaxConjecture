import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N17.Core
import ACMaxConjecture.SmallCases.N17.TwoHubSelect
import ACMaxConjecture.SmallCases.N17.TwoHubTight

/-!
# Deg-`5` two-hub corner selection for `n = 17` (deg-`5`-containing regimes)

This file supplies `two_hub_corner_select_deg5_seventeen`, the hub-pair *selection* lemma for the
`e(M) ≤ 1` two-hub corner regimes that contain a degree-`5` hub, i.e. `|Hub| ∈ {7, 8}`
(`#{deg-5 hubs} = 9 − |Hub| ∈ {1, 2}`).

The universal good-`C₄` share bound `nonadj_hubs_share_le_one_iso` **fails** for a non-adjacent
degree-`5`/degree-`4` hub pair (their `K₂,₂` exceeds the good-`C₄` `Σ ≤ 14` threshold).  But share
`≤ 1` **does** hold among the degree-`4` hubs.  We therefore route around the degree-`5` hubs: the
selection consumes only the **degree-`4`-restricted** share (`hshare`), exactly the hypothesis of the
shared `residual_arith` / `strong_deg4_count_le_two_deg5_seventeen` engine.

Of the four deg-`5`-containing profiles `(|Hub|, |Iso|, ∑deg) ∈ {(7,10,30), (7,8,30), (8,9,33),
(8,7,33)}`, the first three close by the unified `residual_arith` inequality `3·|Iso| > 29 − |Hub|`;
the tight `(8,7,33)` (`3·|Iso| = 29 − |Hub|`) is routed through the documented
`two_hub_select_eM1_tight_seventeen`. -/

namespace ACMax

open scoped Classical

namespace N17

/-- **Hub-pair selection for the `n = 17` deg-`5`-containing two-hub corner.**  Given the
deg-`5`-containing `e(M) ≤ 1` regimes `|Hub| ∈ {7, 8}`, with each `M`-isolated twin meeting exactly
three hubs (`hiso3`) and the good-`C₄` share bound holding **for degree-`4` hub pairs** (`hshare`),
there exist two non-adjacent degree-`4` hubs each retaining `≥ 2` private `M`-isolated twins.  Routes
around the degree-`5` hubs via the shared `residual_arith` engine. -/
theorem two_hub_corner_select_deg5_seventeen (G : SimpleGraph (Fin 17)) (Hub Iso : Finset (Fin 17))
    (hdeg : ∀ h ∈ Hub, 4 ≤ G.degree h) (hdeg5 : ∀ h ∈ Hub, G.degree h ≤ 5)
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hdisj : Disjoint Hub Iso)
    (hregime :
      (Hub.card = 7 ∧ Iso.card = 10 ∧ ∑ w ∈ Hub, G.degree w = 30) ∨
      (Hub.card = 7 ∧ Iso.card = 8 ∧ ∑ w ∈ Hub, G.degree w = 30) ∨
      (Hub.card = 8 ∧ Iso.card = 9 ∧ ∑ w ∈ Hub, G.degree w = 33) ∨
      (Hub.card = 8 ∧ Iso.card = 7 ∧ ∑ w ∈ Hub, G.degree w = 33)) :
    ∃ h₁ h₂ : Fin 17, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card := by
  classical
  set F : Finset (Fin 17) :=
    Hub.filter (fun h => G.degree h = 4 ∧ (G.neighborFinset h ∩ Iso).card = 4) with hFdef
  by_cases hk : 2 ≤ F.card
  · -- **Extremal case: two degree-`4` hubs of iso-degree `4`.**
    obtain ⟨h₁, hh1F, h₂, hh2F, hne⟩ := Finset.one_lt_card.mp hk
    obtain ⟨hh1, hd1, h1iso4⟩ := Finset.mem_filter.mp hh1F
    obtain ⟨hh2, hd2, h2iso4⟩ := Finset.mem_filter.mp hh2F
    have hsub : ∀ h : Fin 17, G.degree h = 4 → (G.neighborFinset h ∩ Iso).card = 4 →
        G.neighborFinset h ⊆ Iso := by
      intro h hdh hh4
      have hdc : (G.neighborFinset h).card = 4 := by rw [G.card_neighborFinset_eq_degree, hdh]
      have heq : G.neighborFinset h ∩ Iso = G.neighborFinset h :=
        Finset.eq_of_subset_of_card_le Finset.inter_subset_left (le_of_eq (by rw [hdc, hh4]))
      rw [← heq]; exact Finset.inter_subset_right
    have h1sub : G.neighborFinset h₁ ⊆ Iso := hsub h₁ hd1 h1iso4
    have hnadj : ¬G.Adj h₁ h₂ := by
      intro hadj
      exact Finset.disjoint_left.mp hdisj hh2 (h1sub ((G.mem_neighborFinset h₁ h₂).mpr hadj))
    have hsh : (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1 :=
      hshare h₁ hh1 hd1 h₂ hh2 hd2 hne hnadj
    have hsh' : (G.neighborFinset h₂ ∩ G.neighborFinset h₁ ∩ Iso).card ≤ 1 :=
      hshare h₂ hh2 hd2 h₁ hh1 hd1 (Ne.symm hne) (fun h => hnadj h.symm)
    have hfin := select_finish_seventeen G Iso h₁ h₂ (by omega) (by omega)
    exact ⟨h₁, h₂, hh1, hh2, hd1, hd2, hne, hnadj, hfin.1, hfin.2⟩
  · -- **Residual: at most one degree-`4` hub of iso-degree `4`.**
    have hdeg45 : ∀ h ∈ Hub, G.degree h = 4 ∨ G.degree h = 5 := by
      intro h hh; have := hdeg h hh; have := hdeg5 h hh; omega
    rcases hregime with hr | hr | hr | hr
    · obtain ⟨hHub, hIso, hdsum⟩ := hr
      by_contra hcon
      exact absurd (residual_arith G Hub Iso hdisj hshare hiso3 hdeg45 hcon) (by
        rw [hHub, hIso, hdsum]; omega)
    · obtain ⟨hHub, hIso, hdsum⟩ := hr
      by_contra hcon
      exact absurd (residual_arith G Hub Iso hdisj hshare hiso3 hdeg45 hcon) (by
        rw [hHub, hIso, hdsum]; omega)
    · obtain ⟨hHub, hIso, hdsum⟩ := hr
      by_contra hcon
      exact absurd (residual_arith G Hub Iso hdisj hshare hiso3 hdeg45 hcon) (by
        rw [hHub, hIso, hdsum]; omega)
    · -- (8, 7, 33): tight.
      obtain ⟨hHub, hIso, hdsum⟩ := hr
      exact two_hub_select_eM1_tight_seventeen G Hub Iso hdeg hdeg5 hiso3 hdisj hshare
        (Or.inl ⟨hHub, hIso, hdsum⟩)

end N17

end ACMax
