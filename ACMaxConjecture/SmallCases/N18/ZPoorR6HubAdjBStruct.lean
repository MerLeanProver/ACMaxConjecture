import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N18.Core
import ACMaxConjecture.SmallCases.N18.TwoHubSelect
import ACMaxConjecture.SmallCases.N18.StarTriangleStruct
import ACMaxConjecture.SmallCases.N18.RichCount
import ACMaxConjecture.SmallCases.N18.Align8Helpers
import ACMaxConjecture.SmallCases.N18.ZPoorN3
import ACMaxConjecture.SmallCases.N18.ZPoorR7
import ACMaxConjecture.SmallCases.N18.ZVertex
import ACMaxConjecture.SmallCases.N18.ZPoorSat
import ACMaxConjecture.SmallCases.N18.ZPoorR6Dist
import ACMaxConjecture.SmallCases.N18.ZPoorR6Sat
import ACMaxConjecture.SmallCases.N18.ZPoorR6Poor
import ACMaxConjecture.SmallCases.N18.ZPoorR6HubAdj

/-!
# Design B (`{3,3,2,2,2,2}`) `w`-structure for the `r = 6`, `S = 14` no-apex core (`n = 18`)

This file establishes the rigid skeleton of design `B` for the hub-adjacency core `G.Adj d₁ d₂` of
`apex_or_good_triangle_S14`: the rich iso-degree multiset is `{3,3,2,2,2,2}`, with two iso-degree-`3`
rich hubs `w₁, w₂` and four iso-degree-`2` rich hubs.

The two iso-degree-`3` rich hubs `w₁, w₂` are mutually adjacent (`rich3_clique_S14`), each spends
three of its four degree slots on twins, so has hub-degree `1` (only the edge `w₁ ~ w₂`) and
`Z`-degree `0`.  Since `w₁ ~ w₂`, the no-twin-cherry hypothesis forbids any twin meeting both, so the
six twins partition into the three `w₁`-twins and the three `w₂`-twins: every twin meets exactly one
of `w₁, w₂`.  Finally `d₁, d₂` (the two hub-neighbours of the `M`-partner `zp ∈ Z`) differ from
`w₁, w₂` because `w₁, w₂` have no `Z`-neighbour.
-/

namespace ACMax

open scoped Classical

namespace N18

/-- **Design B `w`-structure (the rigid skeleton).**  For the `r = 6`, `S = 14` profile with two
iso-degree-`3` rich hubs `w₁, w₂`, the hubs `w₁, w₂` are mutually adjacent, each has hub-degree `1`
and `Z`-degree `0`, every twin meets exactly one of them, and `d₁, d₂` (the hub-neighbours of the
`M`-partner `zp ∈ Z`) differ from `w₁, w₂`. -/
theorem designB_w_structure_S14 (G : SimpleGraph (Fin 18)) (Hub Iso : Finset (Fin 18))
    (hdisj : Disjoint Hub Iso) (hIso : Iso.card = 6)
    (hdeg4 : ∀ h ∈ Hub, G.degree h = 4)
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hno2hub : ¬∃ h₁ h₂ : Fin 18, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card)
    (hcherry : ¬∃ t ∈ Iso, ∃ a b : Fin 18, a ∈ G.neighborFinset t ∧ b ∈ G.neighborFinset t ∧
      a ≠ b ∧ G.Adj a b)
    (w1 w2 zp d1 d2 : Fin 18)
    (hw1Hub : w1 ∈ Hub) (hw2Hub : w2 ∈ Hub) (hw1w2ne : w1 ≠ w2)
    (hw13 : (G.neighborFinset w1 ∩ Iso).card = 3) (hw23 : (G.neighborFinset w2 ∩ Iso).card = 3)
    (hzpZ : zp ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 18)))
    (hd1zp : G.Adj d1 zp) (hd2zp : G.Adj d2 zp) :
    G.Adj w1 w2 ∧ (G.neighborFinset w1 ∩ Hub).card = 1 ∧ (G.neighborFinset w2 ∩ Hub).card = 1 ∧
    (G.neighborFinset w1 ∩ (Finset.univ \ (Hub ∪ Iso))).card = 0 ∧
    (G.neighborFinset w2 ∩ (Finset.univ \ (Hub ∪ Iso))).card = 0 ∧
    (∀ t ∈ Iso, (t ∈ G.neighborFinset w1 ∧ t ∉ G.neighborFinset w2) ∨
      (t ∉ G.neighborFinset w1 ∧ t ∈ G.neighborFinset w2)) ∧
    d1 ≠ w1 ∧ d1 ≠ w2 ∧ d2 ≠ w1 ∧ d2 ≠ w2 := by
  classical
  -- `w₁ ~ w₂` from the rich-`3` clique lemma.
  have hadjw : G.Adj w1 w2 :=
    rich3_clique_S14 G Hub Iso hdeg4 hshare hno2hub w1 w2 hw1Hub hw2Hub hw1w2ne hw13.ge hw23.ge
  -- Degree split: hub-degree + iso-degree + `Z`-degree = `4`.
  have hsp1 := nbr_split_three_eighteen G Hub Iso hdisj w1
  have hsp2 := nbr_split_three_eighteen G Hub Iso hdisj w2
  rw [hdeg4 w1 hw1Hub, hw13] at hsp1
  rw [hdeg4 w2 hw2Hub, hw23] at hsp2
  -- `w₂ ∈ N(w₁) ∩ Hub`, so `w₁` has hub-degree `≥ 1`; hence `= 1` and `Z`-degree `0`.
  have hw2mem : w2 ∈ G.neighborFinset w1 ∩ Hub :=
    Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hadjw, hw2Hub⟩
  have hw1mem : w1 ∈ G.neighborFinset w2 ∩ Hub :=
    Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hadjw.symm, hw1Hub⟩
  have hw1hubpos : 1 ≤ (G.neighborFinset w1 ∩ Hub).card := Finset.card_pos.mpr ⟨w2, hw2mem⟩
  have hw2hubpos : 1 ≤ (G.neighborFinset w2 ∩ Hub).card := Finset.card_pos.mpr ⟨w1, hw1mem⟩
  have hw1hub1 : (G.neighborFinset w1 ∩ Hub).card = 1 := by omega
  have hw2hub1 : (G.neighborFinset w2 ∩ Hub).card = 1 := by omega
  have hw1z0 : (G.neighborFinset w1 ∩ (Finset.univ \ (Hub ∪ Iso))).card = 0 := by omega
  have hw2z0 : (G.neighborFinset w2 ∩ (Finset.univ \ (Hub ∪ Iso))).card = 0 := by omega
  -- No twin meets both `w₁` and `w₂` (else a twin-cherry on the edge `w₁ ~ w₂`).
  have hno_both : ∀ t ∈ Iso, ¬(t ∈ G.neighborFinset w1 ∧ t ∈ G.neighborFinset w2) := by
    intro t ht ⟨ht1, ht2⟩
    have hw1t : w1 ∈ G.neighborFinset t :=
      (G.mem_neighborFinset _ _).mpr ((G.mem_neighborFinset _ _).mp ht1).symm
    have hw2t : w2 ∈ G.neighborFinset t :=
      (G.mem_neighborFinset _ _).mpr ((G.mem_neighborFinset _ _).mp ht2).symm
    exact hcherry ⟨t, ht, w1, w2, hw1t, hw2t, hw1w2ne, hadjw⟩
  -- The two twin-sets are disjoint and partition `Iso`.
  have hdisjIso : Disjoint (G.neighborFinset w1 ∩ Iso) (G.neighborFinset w2 ∩ Iso) := by
    rw [Finset.disjoint_left]
    intro t ht1 ht2
    exact hno_both t (Finset.mem_inter.mp ht1).2
      ⟨(Finset.mem_inter.mp ht1).1, (Finset.mem_inter.mp ht2).1⟩
  have hunionsub : (G.neighborFinset w1 ∩ Iso) ∪ (G.neighborFinset w2 ∩ Iso) ⊆ Iso := by
    intro t ht
    rcases Finset.mem_union.mp ht with h | h
    · exact (Finset.mem_inter.mp h).2
    · exact (Finset.mem_inter.mp h).2
  have hunioncard : ((G.neighborFinset w1 ∩ Iso) ∪ (G.neighborFinset w2 ∩ Iso)).card = 6 := by
    rw [Finset.card_union_of_disjoint hdisjIso, hw13, hw23]
  have hunioneq : (G.neighborFinset w1 ∩ Iso) ∪ (G.neighborFinset w2 ∩ Iso) = Iso :=
    Finset.eq_of_subset_of_card_le hunionsub (by rw [hunioncard, hIso])
  have hpart : ∀ t ∈ Iso, (t ∈ G.neighborFinset w1 ∧ t ∉ G.neighborFinset w2) ∨
      (t ∉ G.neighborFinset w1 ∧ t ∈ G.neighborFinset w2) := by
    intro t ht
    have htun : t ∈ (G.neighborFinset w1 ∩ Iso) ∪ (G.neighborFinset w2 ∩ Iso) := by
      rw [hunioneq]; exact ht
    rcases Finset.mem_union.mp htun with h | h
    · refine Or.inl ⟨(Finset.mem_inter.mp h).1, ?_⟩
      intro hc; exact hno_both t ht ⟨(Finset.mem_inter.mp h).1, hc⟩
    · refine Or.inr ⟨?_, (Finset.mem_inter.mp h).1⟩
      intro hc; exact hno_both t ht ⟨hc, (Finset.mem_inter.mp h).1⟩
  -- `d₁, d₂ ≠ w₁, w₂`: `w₁, w₂` have no `Z`-neighbour, but `d₁, d₂ ~ zp ∈ Z`.
  have hdwne : ∀ d : Fin 18, G.Adj d zp → d ≠ w1 ∧ d ≠ w2 := by
    intro d hdzp
    refine ⟨?_, ?_⟩
    · rintro rfl
      have : zp ∈ G.neighborFinset d ∩ (Finset.univ \ (Hub ∪ Iso)) :=
        Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hdzp, hzpZ⟩
      rw [Finset.card_eq_zero.mp hw1z0] at this
      exact absurd this (Finset.notMem_empty zp)
    · rintro rfl
      have : zp ∈ G.neighborFinset d ∩ (Finset.univ \ (Hub ∪ Iso)) :=
        Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hdzp, hzpZ⟩
      rw [Finset.card_eq_zero.mp hw2z0] at this
      exact absurd this (Finset.notMem_empty zp)
  exact ⟨hadjw, hw1hub1, hw2hub1, hw1z0, hw2z0, hpart,
    (hdwne d1 hd1zp).1, (hdwne d1 hd1zp).2, (hdwne d2 hd2zp).1, (hdwne d2 hd2zp).2⟩

end N18

end ACMax
