import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N18.Core
import ACMaxConjecture.SmallCases.N18.TwoHubSelect
import ACMaxConjecture.SmallCases.N18.TwoHubTight

/-!
# Deg-`5` two-hub corner selection for `n = 18` (deg-`5`-containing regimes)

This file is the `n = 18` port of `TwinCert17TwoHubDeg5`.  It supplies
`two_hub_corner_select_deg5_eighteen`, the hub-pair *selection* lemma for the `e(M) ≤ 1` two-hub
corner regimes that contain a degree-`5` hub, i.e. `|Hub| ∈ {7, 8, 9}` (`#{deg-5 hubs} = 10 − |Hub|
∈ {1, 2, 3}`).

The universal good-`C₄` share bound `nonadj_hubs_share_le_one_iso` **fails** for a non-adjacent
degree-`5`/degree-`4` hub pair (their `K₂,₂` exceeds the good-`C₄` `Σ ≤ 14` threshold).  But share
`≤ 1` **does** hold among the degree-`4` hubs.  We therefore route around the degree-`5` hubs: the
selection consumes only the **degree-`4`-restricted** share (`hshare`), exactly the hypothesis
of the shared `residual_arith_eighteen` / `strong_deg4_count_le_two_deg5_eighteen` engine.

Of the five deg-`5`-containing profiles `(|Hub|, |Iso|, ∑deg) ∈ {(7,9,31), (8,10,34), (9,9,37),
(8,8,34), (9,7,37)}`, the first three close by the unified `residual_arith_eighteen` inequality; the
two tight `e(M) = 1` profiles `(8,8,34)` and `(9,7,37)` are routed through the shared tight router
`two_hub_select_eM1_tight_eighteen` (documented `sorry` in `TwinCert18TwoHubSelect`). -/

namespace ACMax

open scoped Classical

namespace N18

/-- **Hub-pair selection for the `n = 18` deg-`5`-containing two-hub corner.**  Given the
deg-`5`-containing `e(M) ≤ 1` regimes `|Hub| ∈ {7, 8, 9}`, with each `M`-isolated twin meeting
exactly three hubs (`hiso3`) and the good-`C₄` share bound holding **for degree-`4` hub pairs**
(`hshare`), there exist two non-adjacent degree-`4` hubs each retaining `≥ 2` private `M`-isolated
twins.  Routes around the degree-`5` hubs via the shared `residual_arith_eighteen` engine. -/
theorem two_hub_corner_select_deg5_eighteen (G : SimpleGraph (Fin 18)) (Hub Iso : Finset (Fin 18))
    (hdeg : ∀ h ∈ Hub, 4 ≤ G.degree h) (hdeg5 : ∀ h ∈ Hub, G.degree h ≤ 5)
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hdisj : Disjoint Hub Iso)
    (hregime :
      (Hub.card = 7 ∧ Iso.card = 9 ∧ ∑ w ∈ Hub, G.degree w = 31) ∨
      (Hub.card = 8 ∧ Iso.card = 10 ∧ ∑ w ∈ Hub, G.degree w = 34) ∨
      (Hub.card = 9 ∧ Iso.card = 9 ∧ ∑ w ∈ Hub, G.degree w = 37) ∨
      (Hub.card = 8 ∧ Iso.card = 8 ∧ ∑ w ∈ Hub, G.degree w = 34) ∨
      (Hub.card = 9 ∧ Iso.card = 7 ∧ ∑ w ∈ Hub, G.degree w = 37 ∧
        (∀ v : Fin 18, 3 ≤ G.degree v) ∧ (∀ t ∈ Iso, G.degree t = 3) ∧
        ∑ h ∈ Hub, (G.neighborFinset h ∩ (Finset.univ \ (Hub ∪ Iso))).card ≤ 4 ∧
        ¬∃ x y z : Fin 18, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
          G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧
          G.degree x + G.degree y + G.degree z ≤ 11))
    (hC4 : ¬∃ a b c d : Fin 18, ({a, b, c, d} : Finset (Fin 18)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (hK23 : ¬∃ a b c d e : Fin 18, ({a, b, c, d, e} : Finset (Fin 18)).card = 5 ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
      G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 19) :
    (∃ h₁ h₂ : Fin 18, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card) ∨ StarTriangleConfig G := by
  classical
  set F : Finset (Fin 18) :=
    Hub.filter (fun h => G.degree h = 4 ∧ (G.neighborFinset h ∩ Iso).card = 4) with hFdef
  by_cases hk : 2 ≤ F.card
  · -- **Extremal case: two degree-`4` hubs of iso-degree `4`.**
    obtain ⟨h₁, hh1F, h₂, hh2F, hne⟩ := Finset.one_lt_card.mp hk
    obtain ⟨hh1, hd1, h1iso4⟩ := Finset.mem_filter.mp hh1F
    obtain ⟨hh2, hd2, h2iso4⟩ := Finset.mem_filter.mp hh2F
    have hsub : ∀ h : Fin 18, G.degree h = 4 → (G.neighborFinset h ∩ Iso).card = 4 →
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
    have hfin := select_finish_eighteen G Iso h₁ h₂ (by omega) (by omega)
    exact Or.inl ⟨h₁, h₂, hh1, hh2, hd1, hd2, hne, hnadj, hfin.1, hfin.2⟩
  · -- **Residual: at most one degree-`4` hub of iso-degree `4`.**
    have hdeg45 : ∀ h ∈ Hub, G.degree h = 4 ∨ G.degree h = 5 := by
      intro h hh; have := hdeg h hh; have := hdeg5 h hh; omega
    rcases hregime with hr | hr | hr | hr | hr
    · refine Or.inl ?_
      obtain ⟨hHub, hIso, hdsum⟩ := hr
      by_contra hcon
      exact absurd (residual_arith_eighteen G Hub Iso hdisj hshare hiso3 hdeg45 hcon) (by
        rw [hHub, hIso, hdsum]; omega)
    · refine Or.inl ?_
      obtain ⟨hHub, hIso, hdsum⟩ := hr
      by_contra hcon
      exact absurd (residual_arith_eighteen G Hub Iso hdisj hshare hiso3 hdeg45 hcon) (by
        rw [hHub, hIso, hdsum]; omega)
    · refine Or.inl ?_
      obtain ⟨hHub, hIso, hdsum⟩ := hr
      by_contra hcon
      exact absurd (residual_arith_eighteen G Hub Iso hdisj hshare hiso3 hdeg45 hcon) (by
        rw [hHub, hIso, hdsum]; omega)
    · -- (8, 8, 34): tight.
      exact two_hub_select_eM1_tight_eighteen G Hub Iso hdeg hdeg5 hiso3 hdisj hshare (Or.inl hr)
        hC4 hK23
    · -- (9, 7, 37): tight.
      exact two_hub_select_eM1_tight_eighteen G Hub Iso hdeg hdeg5 hiso3 hdisj hshare
        (Or.inr (Or.inl hr)) hC4 hK23

end N18

end ACMax
