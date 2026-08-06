import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N19.TwoHubCornerDeg5ZLeaf
import ACMaxConjecture.SmallCases.N19.TwoHubSelect
import ACMaxConjecture.SmallCases.N19.ZVertex
import ACMaxConjecture.SmallCases.N19.Deg5ZSlots
import ACMaxConjecture.SmallCases.N19.Deg5RichCap

/-! # The rich-count lower bound for the (10,7,41) corner (`n = 19`) -/
namespace ACMax
open scoped Classical

namespace N19

set_option maxHeartbeats 1000000 in
/-- With a rich hub `g` (isoDeg ≥ 3), the `(10,7,41)` ledger + the iso-cap force
at least `5` degree-`4` hubs of isoDeg `≥ 2`. -/
theorem rich_count_ge_five_1041_nineteen (G : SimpleGraph (Fin 19)) (Hub Iso : Finset (Fin 19))
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdisj : Disjoint Hub Iso) (_hsum17 : Hub.card + Iso.card = 17)
    (_hdeg3 : ∀ v : Fin 19, 3 ≤ G.degree v) (_hisodeg3 : ∀ t ∈ Iso, G.degree t = 3)
    (_hleak : ∑ h ∈ Hub, (G.neighborFinset h ∩ (Finset.univ \ (Hub ∪ Iso))).card ≤ 4)
    (hdeg : ∀ h ∈ Hub, 4 ≤ G.degree h) (hdeg5 : ∀ h ∈ Hub, G.degree h ≤ 5)
    (hHub : Hub.card = 10) (hIso : Iso.card = 7) (hdsum : ∑ w ∈ Hub, G.degree w = 41)
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hno2hub : ¬∃ h₁ h₂ : Fin 19, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card)
    (g : Fin 19) (hg : g ∈ Hub) (hgd : G.degree g = 4)
    (hgiso : 3 ≤ (G.neighborFinset g ∩ Iso).card) :
    5 ≤ (Hub.filter (fun h => G.degree h = 4 ∧ 2 ≤ (G.neighborFinset h ∩ Iso).card)).card := by
  classical
  -- === Degree partition: 9 deg-4 hubs, 1 deg-5 hub. ===
  have hdeg45 : ∀ h ∈ Hub, G.degree h = 4 ∨ G.degree h = 5 := by
    intro h hh; have h1 := hdeg h hh; have h2 := hdeg5 h hh; omega
  set D4 : Finset (Fin 19) := Hub.filter (fun h => G.degree h = 4) with hD4def
  set D5 : Finset (Fin 19) := Hub.filter (fun h => ¬ G.degree h = 4) with hD5def
  have hD4sub : D4 ⊆ Hub := by rw [hD4def]; exact Finset.filter_subset _ _
  have hD4deg4 : ∀ h ∈ D4, G.degree h = 4 := by
    intro h hh; rw [hD4def, Finset.mem_filter] at hh; exact hh.2
  have hD5deg5 : ∀ h ∈ D5, G.degree h = 5 := by
    intro h hh; rw [hD5def, Finset.mem_filter] at hh
    rcases hdeg45 h hh.1 with h4 | h5
    · exact absurd h4 hh.2
    · exact h5
  have hcardpart : D4.card + D5.card = 10 := by
    rw [hD4def, hD5def, Finset.card_filter_add_card_filter_not]; exact hHub
  have hsumdeg : (∑ h ∈ D4, G.degree h) + (∑ h ∈ D5, G.degree h) = 41 := by
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
  have hD4card : D4.card = 9 := by omega
  have hD5card : D5.card = 1 := by omega
  -- === Iso-degree ledger: ∑_Hub isoDeg = 21, so ∑_D4 isoDeg ≥ 16. ===
  have hisosum21 : ∑ h ∈ Hub, (G.neighborFinset h ∩ Iso).card = 21 := by
    have h := hub_iso_sum_nineteen G Hub Iso hiso3; rw [hIso] at h; omega
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
  have hD4isoge : 16 ≤ ∑ h ∈ D4, (G.neighborFinset h ∩ Iso).card := by
    rw [hD5isosum] at hisosplit; omega
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
  have hgsplit := nbr_split_three_nineteen G Hub Iso hdisj g
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
  have hH3 : ∑ h ∈ D4.erase g, (G.neighborFinset h ∩ Iso).card
      ≤ ∑ h ∈ D4.erase g,
          (1 + (if 2 ≤ (G.neighborFinset h ∩ Iso).card then 1 else 0)
             + (if G.Adj g h then 1 else 0)) := by
    apply Finset.sum_le_sum
    intro h hh
    rw [Finset.mem_erase] at hh
    obtain ⟨hne, hhD4⟩ := hh
    have hhHub : h ∈ Hub := hD4sub hhD4
    have hhdeg : G.degree h = 4 := hD4deg4 h hhD4
    by_cases hadj : G.Adj g h
    · have hgN : g ∈ G.neighborFinset h ∩ Hub :=
        Finset.mem_inter.mpr ⟨(G.mem_neighborFinset h g).mpr hadj.symm, hg⟩
      have hbge1 : 1 ≤ (G.neighborFinset h ∩ Hub).card := Finset.card_pos.mpr ⟨g, hgN⟩
      have hsplit := nbr_split_three_nineteen G Hub Iso hdisj h
      rw [hhdeg] at hsplit
      rw [if_pos hadj]
      by_cases hc : 2 ≤ (G.neighborFinset h ∩ Iso).card
      · rw [if_pos hc]; omega
      · rw [if_neg hc]; omega
    · have hcap := isoDeg_le_two_of_nonadj_rich_nineteen G Hub Iso hshare hno2hub g h hg hhHub
        hgd hhdeg (Ne.symm hne) hadj hgiso
      rw [if_neg hadj]
      by_cases hc : 2 ≤ (G.neighborFinset h ∩ Iso).card
      · rw [if_pos hc]; omega
      · rw [if_neg hc]; omega
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
  have hEraseCard : (D4.erase g).card = 8 := by
    rw [Finset.card_erase_of_mem hgD4, hD4card]
  rw [hRHS, hEraseCard] at hH3
  omega

end N19

end ACMax
