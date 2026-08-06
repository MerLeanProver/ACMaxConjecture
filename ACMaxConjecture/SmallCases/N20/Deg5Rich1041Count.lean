import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N20.TwoHubCornerDeg5ZLeaf
import ACMaxConjecture.SmallCases.N20.TwoHubSelect
import ACMaxConjecture.SmallCases.N20.ZVertex
import ACMaxConjecture.SmallCases.N20.Deg5ZSlots
import ACMaxConjecture.SmallCases.N20.Deg5RichCap

/-! # The rich-count dichotomy for the (11,7,45) corner (`n = 20`) -/
namespace ACMax
open scoped Classical

namespace N20

set_option maxHeartbeats 1000000 in
/-- With a rich hub `g` (isoDeg ≥ 3), the `(11,7,45)` ledger + the iso-cap force either
at least `5` degree-`4` hubs of isoDeg `≥ 2`, or exactly `4` of them together with the
equality-forced structure: the single degree-`5` anchor is iso-saturated (isoDeg `= 5`)
and every non-rich degree-`4` hub has isoDeg exactly `1`. -/
theorem rich_count_1041_twenty (G : SimpleGraph (Fin 20)) (Hub Iso : Finset (Fin 20))
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdisj : Disjoint Hub Iso) (_hsum18 : Hub.card + Iso.card = 18)
    (_hdeg3 : ∀ v : Fin 20, 3 ≤ G.degree v) (_hisodeg3 : ∀ t ∈ Iso, G.degree t = 3)
    (_hleak : ∑ h ∈ Hub, (G.neighborFinset h ∩ (Finset.univ \ (Hub ∪ Iso))).card ≤ 4)
    (hdeg : ∀ h ∈ Hub, 4 ≤ G.degree h) (hdeg5 : ∀ h ∈ Hub, G.degree h ≤ 5)
    (hHub : Hub.card = 11) (hIso : Iso.card = 7) (hdsum : ∑ w ∈ Hub, G.degree w = 45)
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hno2hub : ¬∃ h₁ h₂ : Fin 20, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card)
    (g : Fin 20) (hg : g ∈ Hub) (hgd : G.degree g = 4)
    (hgiso : 3 ≤ (G.neighborFinset g ∩ Iso).card) :
    5 ≤ (Hub.filter (fun h => G.degree h = 4 ∧ 2 ≤ (G.neighborFinset h ∩ Iso).card)).card ∨
      ((Hub.filter (fun h => G.degree h = 4 ∧ 2 ≤ (G.neighborFinset h ∩ Iso).card)).card = 4 ∧
        (∃ f ∈ Hub, G.degree f = 5 ∧ (G.neighborFinset f ∩ Iso).card = 5) ∧
        (∀ h ∈ Hub, G.degree h = 4 →
          h ∉ Hub.filter (fun h => G.degree h = 4 ∧ 2 ≤ (G.neighborFinset h ∩ Iso).card) →
          (G.neighborFinset h ∩ Iso).card = 1)) := by
  classical
  -- === Degree partition: 10 deg-4 hubs, 1 deg-5 hub. ===
  have hdeg45 : ∀ h ∈ Hub, G.degree h = 4 ∨ G.degree h = 5 := by
    intro h hh; have h1 := hdeg h hh; have h2 := hdeg5 h hh; omega
  set D4 : Finset (Fin 20) := Hub.filter (fun h => G.degree h = 4) with hD4def
  set D5 : Finset (Fin 20) := Hub.filter (fun h => ¬ G.degree h = 4) with hD5def
  have hD4sub : D4 ⊆ Hub := by rw [hD4def]; exact Finset.filter_subset _ _
  have hD5sub : D5 ⊆ Hub := by rw [hD5def]; exact Finset.filter_subset _ _
  have hD4deg4 : ∀ h ∈ D4, G.degree h = 4 := by
    intro h hh; rw [hD4def, Finset.mem_filter] at hh; exact hh.2
  have hD5deg5 : ∀ h ∈ D5, G.degree h = 5 := by
    intro h hh; rw [hD5def, Finset.mem_filter] at hh
    rcases hdeg45 h hh.1 with h4 | h5
    · exact absurd h4 hh.2
    · exact h5
  have hcardpart : D4.card + D5.card = 11 := by
    rw [hD4def, hD5def, Finset.card_filter_add_card_filter_not]; exact hHub
  have hsumdeg : (∑ h ∈ D4, G.degree h) + (∑ h ∈ D5, G.degree h) = 45 := by
    rw [hD4def, hD5def, Finset.sum_filter_add_sum_filter_not]; exact hdsum
  have hsum4 : (∑ h ∈ D4, G.degree h) = 4 * D4.card := by
    calc (∑ h ∈ D4, G.degree h) = ∑ _h ∈ D4, 4 :=
          Finset.sum_congr rfl fun h hh => hD4deg4 h hh
      _ = 4 * D4.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have hsum5 : (∑ h ∈ D5, G.degree h) = 5 * D5.card := by
    calc (∑ h ∈ D5, G.degree h) = ∑ _h ∈ D5, 5 :=
          Finset.sum_congr rfl fun h hh => hD5deg5 h hh
      _ = 5 * D5.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  rw [hsum4, hsum5] at hsumdeg
  have hD4card : D4.card = 10 := by omega
  have hD5card : D5.card = 1 := by omega
  -- === Iso-degree ledger: ∑_Hub isoDeg = 21, and the anchor absorbs ≤ 5 of it. ===
  have hisosum21 : ∑ h ∈ Hub, (G.neighborFinset h ∩ Iso).card = 21 := by
    have h := hub_iso_sum_twenty G Hub Iso hiso3; rw [hIso] at h; omega
  have hisosplit : (∑ h ∈ D4, (G.neighborFinset h ∩ Iso).card)
      + (∑ h ∈ D5, (G.neighborFinset h ∩ Iso).card) = 21 := by
    rw [hD4def, hD5def, Finset.sum_filter_add_sum_filter_not]; exact hisosum21
  obtain ⟨f, hD5single⟩ := Finset.card_eq_one.mp hD5card
  have hfD5 : f ∈ D5 := by rw [hD5single]; exact Finset.mem_singleton_self f
  have hfdeg5 : G.degree f = 5 := hD5deg5 f hfD5
  have hisof5 : (G.neighborFinset f ∩ Iso).card ≤ 5 := by
    calc (G.neighborFinset f ∩ Iso).card ≤ (G.neighborFinset f).card :=
          Finset.card_le_card Finset.inter_subset_left
      _ = G.degree f := G.card_neighborFinset_eq_degree f
      _ = 5 := hfdeg5
  have hD5isosum : (∑ h ∈ D5, (G.neighborFinset h ∩ Iso).card)
      = (G.neighborFinset f ∩ Iso).card := by rw [hD5single, Finset.sum_singleton]
  -- === The rich set is `D4.filter (isoDeg ≥ 2)`; `g` belongs to it. ===
  have hgoaleq : (Hub.filter (fun h => G.degree h = 4 ∧ 2 ≤ (G.neighborFinset h ∩ Iso).card))
      = D4.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card) := by
    rw [hD4def, Finset.filter_filter]
  rw [hgoaleq]
  have hgD4 : g ∈ D4 := by rw [hD4def, Finset.mem_filter]; exact ⟨hg, hgd⟩
  have hgR : g ∈ D4.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card) := by
    rw [Finset.mem_filter]; exact ⟨hgD4, by omega⟩
  -- The rich set minus `g` is exactly the rich subset of `D4.erase g`.
  have hR'eq : (D4.erase g).filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)
      = (D4.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)).erase g := by
    ext x; simp only [Finset.mem_filter, Finset.mem_erase]; tauto
  have hRcard : (D4.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)).card
      = ((D4.erase g).filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)).card + 1 := by
    rw [hR'eq, Finset.card_erase_of_mem hgR]
    have hge1 : 1 ≤ (D4.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)).card :=
      Finset.card_pos.mpr ⟨g, hgR⟩
    omega
  -- === `isoDeg g + #(deg-4 hubs adjacent to g) ≤ 4` (rich `g` has ≤ 1 hub-neighbour). ===
  have hgsplit := nbr_split_three_twenty G Hub Iso hdisj g
  rw [hgd] at hgsplit
  have hA'sub : (D4.erase g).filter (fun h => G.Adj g h) ⊆ G.neighborFinset g ∩ Hub := by
    intro x hx
    rw [Finset.mem_filter, Finset.mem_erase] at hx
    obtain ⟨⟨_, hxD4⟩, hxadj⟩ := hx
    exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset g x).mpr hxadj, hD4sub hxD4⟩
  have hA'card : ((D4.erase g).filter (fun h => G.Adj g h)).card
      ≤ (G.neighborFinset g ∩ Hub).card := Finset.card_le_card hA'sub
  have hgA : ((D4.erase g).filter (fun h => G.Adj g h)).card
      + (G.neighborFinset g ∩ Iso).card ≤ 4 := by omega
  -- === The ledger split off `g`, and the per-hub upper bound over `D4.erase g`. ===
  have hsumerase : (∑ h ∈ D4, (G.neighborFinset h ∩ Iso).card)
      = (G.neighborFinset g ∩ Iso).card
        + ∑ h ∈ D4.erase g, (G.neighborFinset h ∩ Iso).card :=
    (Finset.add_sum_erase D4 (fun h => (G.neighborFinset h ∩ Iso).card) hgD4).symm
  have hpt : ∀ h ∈ D4.erase g, (G.neighborFinset h ∩ Iso).card
      ≤ 1 + (if 2 ≤ (G.neighborFinset h ∩ Iso).card then 1 else 0)
        + (if G.Adj g h then 1 else 0) := by
    intro h hh
    rw [Finset.mem_erase] at hh
    obtain ⟨hne, hhD4⟩ := hh
    have hhHub : h ∈ Hub := hD4sub hhD4
    have hhdeg : G.degree h = 4 := hD4deg4 h hhD4
    by_cases hadj : G.Adj g h
    · have hgN : g ∈ G.neighborFinset h ∩ Hub :=
        Finset.mem_inter.mpr ⟨(G.mem_neighborFinset h g).mpr hadj.symm, hg⟩
      have hbge1 : 1 ≤ (G.neighborFinset h ∩ Hub).card := Finset.card_pos.mpr ⟨g, hgN⟩
      have hsplit := nbr_split_three_twenty G Hub Iso hdisj h
      rw [hhdeg] at hsplit
      rw [if_pos hadj]
      by_cases hc : 2 ≤ (G.neighborFinset h ∩ Iso).card
      · rw [if_pos hc]; omega
      · rw [if_neg hc]; omega
    · have hcap := isoDeg_le_two_of_nonadj_rich_twenty G Hub Iso hshare hno2hub g h hg hhHub
        hgd hhdeg (Ne.symm hne) hadj hgiso
      rw [if_neg hadj]
      by_cases hc : 2 ≤ (G.neighborFinset h ∩ Iso).card
      · rw [if_pos hc]; omega
      · rw [if_neg hc]; omega
  have hH3 : ∑ h ∈ D4.erase g, (G.neighborFinset h ∩ Iso).card
      ≤ ∑ h ∈ D4.erase g,
          (1 + (if 2 ≤ (G.neighborFinset h ∩ Iso).card then 1 else 0)
             + (if G.Adj g h then 1 else 0)) :=
    Finset.sum_le_sum hpt
  have hRHS : ∑ h ∈ D4.erase g,
        (1 + (if 2 ≤ (G.neighborFinset h ∩ Iso).card then 1 else 0)
           + (if G.Adj g h then 1 else 0))
      = (D4.erase g).card
        + ((D4.erase g).filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)).card
        + ((D4.erase g).filter (fun h => G.Adj g h)).card := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one]
    congr 1
    · congr 1
      exact (Finset.card_filter _ _).symm
    · exact (Finset.card_filter _ _).symm
  have hEraseCard : (D4.erase g).card = 9 := by
    rw [Finset.card_erase_of_mem hgD4, hD4card]
  -- === Either the rich count reaches `5`, or `|R| = 4` forces every ledger step tight. ===
  by_cases h5 : 5 ≤ (D4.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)).card
  · exact Or.inl h5
  right
  -- `16 − isoDeg f ≤ 0 + 9 + R' + (4 − isoDeg g)` pins `R' = 3` and saturates the anchor.
  have hR'3 : ((D4.erase g).filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)).card = 3 := by
    omega
  have hisofeq : (G.neighborFinset f ∩ Iso).card = 5 := by omega
  refine ⟨by omega, ⟨f, hD5sub hfD5, hfdeg5, hisofeq⟩, ?_⟩
  -- === Tightness: every non-rich deg-4 hub has isoDeg exactly `1` (and avoids `g`). ===
  intro h₀ hh₀Hub hh₀deg hh₀notR
  have hh₀D4 : h₀ ∈ D4 := by rw [hD4def, Finset.mem_filter]; exact ⟨hh₀Hub, hh₀deg⟩
  have hh₀notrich : ¬ 2 ≤ (G.neighborFinset h₀ ∩ Iso).card := fun hc =>
    hh₀notR (Finset.mem_filter.mpr ⟨hh₀D4, hc⟩)
  have hh₀ne : h₀ ≠ g := by
    intro he; rw [he] at hh₀notrich; exact hh₀notrich (by omega)
  have hh₀mem : h₀ ∈ D4.erase g := Finset.mem_erase.mpr ⟨hh₀ne, hh₀D4⟩
  have hsplit0 : (∑ h ∈ D4.erase g, (G.neighborFinset h ∩ Iso).card)
      = (G.neighborFinset h₀ ∩ Iso).card
        + ∑ h ∈ (D4.erase g).erase h₀, (G.neighborFinset h ∩ Iso).card :=
    (Finset.add_sum_erase _ _ hh₀mem).symm
  have hsplit1 : (∑ h ∈ D4.erase g,
        (1 + (if 2 ≤ (G.neighborFinset h ∩ Iso).card then 1 else 0)
           + (if G.Adj g h then 1 else 0)))
      = (1 + (if 2 ≤ (G.neighborFinset h₀ ∩ Iso).card then 1 else 0)
           + (if G.Adj g h₀ then 1 else 0))
        + ∑ h ∈ (D4.erase g).erase h₀,
            (1 + (if 2 ≤ (G.neighborFinset h ∩ Iso).card then 1 else 0)
               + (if G.Adj g h then 1 else 0)) :=
    (Finset.add_sum_erase _ _ hh₀mem).symm
  have hH4 : ∑ h ∈ (D4.erase g).erase h₀, (G.neighborFinset h ∩ Iso).card
      ≤ ∑ h ∈ (D4.erase g).erase h₀,
          (1 + (if 2 ≤ (G.neighborFinset h ∩ Iso).card then 1 else 0)
             + (if G.Adj g h then 1 else 0)) :=
    Finset.sum_le_sum fun h hh => hpt h (Finset.mem_of_mem_erase hh)
  rw [if_neg hh₀notrich] at hsplit1
  by_cases hadj0 : G.Adj g h₀
  · -- an adjacent non-rich hub would be forced to isoDeg `2`: impossible.
    rw [if_pos hadj0] at hsplit1
    omega
  · rw [if_neg hadj0] at hsplit1
    omega

end N20

end ACMax
