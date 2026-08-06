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

/-!
# Shared hub-adjacency identities for the `r = 6`, `S = 14` no-apex core (`n = 18`)

This file collects the structural counting identities shared by the two designs (`{4,2,2,2,2,2}`
and `{3,3,2,2,2,2}`) of the rich iso-degree multiset, used to close the hub-adjacency core
`G.Adj d₁ d₂` of `apex_or_good_triangle_S14` in the no-apex, no-twin-cherry branch.

`T = {hg₁, hg₂, d₁, d₂}` is the union of the two poor hubs met by the `M`-edge endpoint `z` and
the two hub-neighbours `d₁, d₂` of its `M`-partner `zp`.  In the no-apex, no-twin-cherry,
`¬Adj d₁ d₂` situation the four vertices of `T` are distinct and pairwise non-adjacent in the hub
graph; the `e(Hub, Hub) = 9` budget then forces the cut identities relating the off-diagonal
within `O = Hub \ T` and the cut `e(T, O)` to the iso-degrees of `d₁, d₂`.
-/

namespace ACMax

open scoped Classical

namespace N18

/-- **Forced hub-count identities for the no-apex core (LEAF).**  In the no-apex, no-twin-cherry,
`¬Adj d₁ d₂` situation, with `z` meeting the two poor hubs `hg₁, hg₂` (each iso-degree `1`) and the
`M`-partner `zp` meeting `d₁, d₂`, the four vertices of `T = {hg₁, hg₂, d₁, d₂}` are distinct and
pairwise non-adjacent in the hub graph.  At the `e(Hub, Hub) = 9` budget this forces the cut
identities relating the within-`O` off-diagonal (`O = Hub \ T`) and the `T`-`O` cut to the
iso-degrees of `d₁, d₂`. -/
theorem forced_hub_count_identities_S14 (G : SimpleGraph (Fin 18)) (Hub Iso : Finset (Fin 18))
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdisj : Disjoint Hub Iso) (hHub : Hub.card = 10) (hIso : Iso.card = 6)
    (hdsum : ∑ w ∈ Hub, G.degree w = 40)
    (hdeg3 : ∀ v : Fin 18, 3 ≤ G.degree v) (hisodeg3 : ∀ t ∈ Iso, G.degree t = 3)
    (hleak : ∑ h ∈ Hub, (G.neighborFinset h ∩ (Finset.univ \ (Hub ∪ Iso))).card ≤ 4)
    (hdeg4 : ∀ h ∈ Hub, G.degree h = 4)
    (z zp hg1 hg2 d1 d2 : Fin 18)
    (hzZ : z ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 18)))
    (hzpZ : zp ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 18)))
    (hg1Hub : hg1 ∈ Hub) (hg2Hub : hg2 ∈ Hub) (hd1Hub : d1 ∈ Hub) (hd2Hub : d2 ∈ Hub)
    (hg1z : G.Adj hg1 z) (hg2z : G.Adj hg2 z) (hd1zp : G.Adj d1 zp) (hd2zp : G.Adj d2 zp)
    (hg1zp : ¬G.Adj hg1 zp) (hg2zp : ¬G.Adj hg2 zp)
    (hg1g2 : hg1 ≠ hg2) (hd1d2 : d1 ≠ d2)
    (hnadj : ¬G.Adj hg1 hg2) (hd1d2nadj : ¬G.Adj d1 d2)
    (hapex : ¬∃ x : Fin 18, x ∈ Hub ∧ x ≠ hg1 ∧ x ≠ hg2 ∧ G.Adj zp x ∧ (G.Adj hg1 x ∨ G.Adj hg2 x))
    (hg1iso1 : (G.neighborFinset hg1 ∩ Iso).card = 1)
    (hg2iso1 : (G.neighborFinset hg2 ∩ Iso).card = 1) :
    d1 ≠ hg1 ∧ d1 ≠ hg2 ∧ d2 ≠ hg1 ∧ d2 ≠ hg2 ∧
    ¬G.Adj hg1 d1 ∧ ¬G.Adj hg2 d1 ∧ ¬G.Adj hg1 d2 ∧ ¬G.Adj hg2 d2 ∧
    (∑ v ∈ (Hub \ ({hg1, hg2, d1, d2} : Finset (Fin 18))),
        (G.neighborFinset v ∩ (Hub \ ({hg1, hg2, d1, d2} : Finset (Fin 18)))).card) + 2
      = 2 * ((G.neighborFinset d1 ∩ Iso).card + (G.neighborFinset d2 ∩ Iso).card) ∧
    (∑ v ∈ ({hg1, hg2, d1, d2} : Finset (Fin 18)),
        (G.neighborFinset v ∩ (Hub \ ({hg1, hg2, d1, d2} : Finset (Fin 18)))).card)
      + (G.neighborFinset d1 ∩ Iso).card + (G.neighborFinset d2 ∩ Iso).card = 10 := by
  classical
  -- Distinctness of the four `T`-vertices.
  have hd1g1 : d1 ≠ hg1 := by rintro rfl; exact hg1zp hd1zp
  have hd1g2 : d1 ≠ hg2 := by rintro rfl; exact hg2zp hd1zp
  have hd2g1 : d2 ≠ hg1 := by rintro rfl; exact hg1zp hd2zp
  have hd2g2 : d2 ≠ hg2 := by rintro rfl; exact hg2zp hd2zp
  -- The no-apex consequences: `dᵢ` is non-adjacent to both `hgⱼ`.
  have ha_d1g1 : ¬G.Adj hg1 d1 := fun h => hapex ⟨d1, hd1Hub, hd1g1, hd1g2, hd1zp.symm, Or.inl h⟩
  have ha_d1g2 : ¬G.Adj hg2 d1 := fun h => hapex ⟨d1, hd1Hub, hd1g1, hd1g2, hd1zp.symm, Or.inr h⟩
  have ha_d2g1 : ¬G.Adj hg1 d2 := fun h => hapex ⟨d2, hd2Hub, hd2g1, hd2g2, hd2zp.symm, Or.inl h⟩
  have ha_d2g2 : ¬G.Adj hg2 d2 := fun h => hapex ⟨d2, hd2Hub, hd2g1, hd2g2, hd2zp.symm, Or.inr h⟩
  set T : Finset (Fin 18) := ({hg1, hg2, d1, d2} : Finset (Fin 18)) with hTdef
  set O : Finset (Fin 18) := Hub \ T with hOdef
  -- Expansion of a sum over the four distinct `T`-vertices.
  have hsum4 : ∀ f : Fin 18 → ℕ,
      ∑ v ∈ T, f v = f hg1 + f hg2 + f d1 + f d2 := by
    intro f
    rw [hTdef, show ({hg1, hg2, d1, d2} : Finset (Fin 18))
        = insert hg1 (insert hg2 (insert d1 {d2})) from rfl,
      Finset.sum_insert (by
        simp only [Finset.mem_insert, Finset.mem_singleton]; push Not
        exact ⟨hg1g2, Ne.symm hd1g1, Ne.symm hd2g1⟩),
      Finset.sum_insert (by
        simp only [Finset.mem_insert, Finset.mem_singleton]; push Not
        exact ⟨Ne.symm hd1g2, Ne.symm hd2g2⟩),
      Finset.sum_insert (by simp only [Finset.mem_singleton]; exact hd1d2),
      Finset.sum_singleton]
    ring
  have hTsubHub : T ⊆ Hub := by
    rw [hTdef]; intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  -- Per-vertex three-way degree split, and the `Z`-incidence totals.
  have hpart : ∀ v : Fin 18, (G.neighborFinset v ∩ Hub).card + (G.neighborFinset v ∩ Iso).card
      + (G.neighborFinset v ∩ (Finset.univ \ (Hub ∪ Iso))).card = G.degree v := fun v =>
    nbr_split_three_eighteen G Hub Iso hdisj v
  have hzsum : ∑ h ∈ Hub, (G.neighborFinset h ∩ (Finset.univ \ (Hub ∪ Iso))).card = 4 :=
    zdeg_sum_four_eighteen G Hub Iso hiso3 hdisj hHub hIso hdsum hdeg3 hisodeg3 hleak
  -- Each `T`-vertex meets `Z` (`z` or `zp`), so its `Z`-incidence is `≥ 1`.
  have hz_hg1 : 1 ≤ (G.neighborFinset hg1 ∩ (Finset.univ \ (Hub ∪ Iso))).card :=
    Finset.card_pos.mpr ⟨z, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hg1z, hzZ⟩⟩
  have hz_hg2 : 1 ≤ (G.neighborFinset hg2 ∩ (Finset.univ \ (Hub ∪ Iso))).card :=
    Finset.card_pos.mpr ⟨z, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hg2z, hzZ⟩⟩
  have hz_d1 : 1 ≤ (G.neighborFinset d1 ∩ (Finset.univ \ (Hub ∪ Iso))).card :=
    Finset.card_pos.mpr ⟨zp, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hd1zp, hzpZ⟩⟩
  have hz_d2 : 1 ≤ (G.neighborFinset d2 ∩ (Finset.univ \ (Hub ∪ Iso))).card :=
    Finset.card_pos.mpr ⟨zp, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hd2zp, hzpZ⟩⟩
  -- Split `∑_Hub zDeg = ∑_O zDeg + ∑_T zDeg = 4`; force each `T` term to `1`, each `O` term to `0`.
  have hZsdiff := Finset.sum_sdiff (f := fun h => (G.neighborFinset h ∩
    (Finset.univ \ (Hub ∪ Iso))).card) hTsubHub
  rw [← hOdef, hzsum, hsum4 (fun h => (G.neighborFinset h ∩
    (Finset.univ \ (Hub ∪ Iso))).card)] at hZsdiff
  have hzd1 : (G.neighborFinset d1 ∩ (Finset.univ \ (Hub ∪ Iso))).card = 1 := by omega
  have hzd2 : (G.neighborFinset d2 ∩ (Finset.univ \ (Hub ∪ Iso))).card = 1 := by omega
  have hzg1 : (G.neighborFinset hg1 ∩ (Finset.univ \ (Hub ∪ Iso))).card = 1 := by omega
  have hzg2 : (G.neighborFinset hg2 ∩ (Finset.univ \ (Hub ∪ Iso))).card = 1 := by omega
  -- `N(v) ∩ T = ∅` for each `T`-vertex (the six internal pairs are non-edges).
  have hempT : ∀ v : Fin 18, (v = hg1 ∨ v = hg2 ∨ v = d1 ∨ v = d2) →
      G.neighborFinset v ∩ T = ∅ := by
    intro v hv
    rw [Finset.eq_empty_iff_forall_notMem]
    intro x hx
    rw [Finset.mem_inter, G.mem_neighborFinset, hTdef, Finset.mem_insert, Finset.mem_insert,
      Finset.mem_insert, Finset.mem_singleton] at hx
    obtain ⟨hadj, hmem⟩ := hx
    rcases hv with rfl | rfl | rfl | rfl <;> rcases hmem with rfl | rfl | rfl | rfl
    all_goals first
      | exact hadj.ne rfl
      | exact hnadj hadj | exact hnadj hadj.symm
      | exact hd1d2nadj hadj | exact hd1d2nadj hadj.symm
      | exact ha_d1g1 hadj | exact ha_d1g1 hadj.symm
      | exact ha_d1g2 hadj | exact ha_d1g2 hadj.symm
      | exact ha_d2g1 hadj | exact ha_d2g1 hadj.symm
      | exact ha_d2g2 hadj | exact ha_d2g2 hadj.symm
  -- For every vertex, `|N(v) ∩ Hub| = |N(v) ∩ T| + |N(v) ∩ O|`.
  have hHubTO : Hub = T ∪ O := by rw [hOdef, Finset.union_sdiff_of_subset hTsubHub]
  have hTOdisj : Disjoint T O := by
    rw [hOdef]; exact Finset.disjoint_sdiff
  have hHubsplit : ∀ v : Fin 18, (G.neighborFinset v ∩ Hub).card
      = (G.neighborFinset v ∩ T).card + (G.neighborFinset v ∩ O).card := by
    intro v
    rw [hHubTO, Finset.inter_union_distrib_left,
      Finset.card_union_of_disjoint (Finset.disjoint_of_subset_left Finset.inter_subset_right
        (Finset.disjoint_of_subset_right Finset.inter_subset_right hTOdisj))]
  -- The hub-degree of each `T`-vertex equals its within-`O` degree (since `N(v) ∩ T = ∅`).
  have hTvalO : ∀ v : Fin 18, (v = hg1 ∨ v = hg2 ∨ v = d1 ∨ v = d2) →
      (G.neighborFinset v ∩ Hub).card = (G.neighborFinset v ∩ O).card := by
    intro v hv
    rw [hHubsplit v, hempT v hv, Finset.card_empty, Nat.zero_add]
  -- Hub-degrees from the degree split: `hgᵢ` give `2`, `dᵢ` give `3 − isoDeg`.
  have hHg1 : (G.neighborFinset hg1 ∩ Hub).card = 2 := by
    have := hpart hg1; rw [hdeg4 hg1 hg1Hub, hg1iso1, hzg1] at this; omega
  have hHg2 : (G.neighborFinset hg2 ∩ Hub).card = 2 := by
    have := hpart hg2; rw [hdeg4 hg2 hg2Hub, hg2iso1, hzg2] at this; omega
  have hHd1 : (G.neighborFinset d1 ∩ Hub).card + (G.neighborFinset d1 ∩ Iso).card = 3 := by
    have := hpart d1; rw [hdeg4 d1 hd1Hub, hzd1] at this; omega
  have hHd2 : (G.neighborFinset d2 ∩ Hub).card + (G.neighborFinset d2 ∩ Iso).card = 3 := by
    have := hpart d2; rw [hdeg4 d2 hd2Hub, hzd2] at this; omega
  -- `St := ∑_T |N ∩ Hub|`, expanded.
  have hStHub : ∑ v ∈ T, (G.neighborFinset v ∩ Hub).card
      = (G.neighborFinset hg1 ∩ Hub).card + (G.neighborFinset hg2 ∩ Hub).card
        + (G.neighborFinset d1 ∩ Hub).card + (G.neighborFinset d2 ∩ Hub).card :=
    hsum4 (fun v => (G.neighborFinset v ∩ Hub).card)
  -- `∑_T |N ∩ O| = ∑_T |N ∩ Hub|`.
  have hStO : ∑ v ∈ T, (G.neighborFinset v ∩ O).card
      = ∑ v ∈ T, (G.neighborFinset v ∩ Hub).card := by
    refine (Finset.sum_congr rfl (fun v hv => ?_)).symm
    rw [hTdef, Finset.mem_insert, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hv
    exact hTvalO v hv
  -- Cut `e(T, O)` equals `e(O, T)` by bipartite double counting.
  have hcross : ∑ v ∈ T, (G.neighborFinset v ∩ O).card
      = ∑ o ∈ O, (G.neighborFinset o ∩ T).card := cross_count G T O
  -- Split `∑_Hub |N ∩ Hub| = ∑_O |N ∩ Hub| + ∑_T |N ∩ Hub| = 18`.
  have hHsdiff := Finset.sum_sdiff (f := fun h => (G.neighborFinset h ∩ Hub).card) hTsubHub
  rw [← hOdef] at hHsdiff
  have hHubedge : ∑ h ∈ Hub, (G.neighborFinset h ∩ Hub).card = 18 :=
    hub_hub_edge_count_eighteen G Hub Iso hiso3 hdisj hHub hIso hdsum hdeg3 hisodeg3 hleak
  -- `∑_O |N ∩ Hub| = ∑_O |N ∩ T| + ∑_O |N ∩ O|`.
  have hOsplit : ∑ o ∈ O, (G.neighborFinset o ∩ Hub).card
      = ∑ o ∈ O, (G.neighborFinset o ∩ T).card + ∑ o ∈ O, (G.neighborFinset o ∩ O).card := by
    rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl (fun o _ => hHubsplit o)
  refine ⟨hd1g1, hd1g2, hd2g1, hd2g2, ha_d1g1, ha_d1g2, ha_d2g1, ha_d2g2, ?_, ?_⟩
  · -- CUT2: `∑_O |N ∩ O| + 2 = 2 (isoD₁ + isoD₂)`.
    omega
  · -- CUT1: `∑_T |N ∩ O| + isoD₁ + isoD₂ = 10`.
    omega

end N18

end ACMax
