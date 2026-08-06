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
import ACMaxConjecture.SmallCases.N18.ZPoorR6HubAdjAEngine
import ACMaxConjecture.SmallCases.N18.ZPoorR6HubAdjASubcase
import ACMaxConjecture.SmallCases.N18.ZPoorR6HubAdjAPartners

/-!
# Design A (`{4,2,2,2,2,2}`) for the `r = 6`, `S = 14` no-apex core (`n = 18`)

This file closes the design-`A` half of the hub-adjacency core `G.Adj d₁ d₂` of
`apex_or_good_triangle_S14`: under the `r = 6`, `S = 14` structure with `hshare`, `hno2hub`,
no-apex, no-twin-cherry and `¬Adj d₁ d₂`, the rich iso-degree multiset `{4,2,2,2,2,2}` (one rich
hub `w` of iso-degree `4` and five of iso-degree `2`) is impossible.

## The structural skeleton (all verified by exhaustive/MCMC search, `0` counterexamples)

* `w` (iso-degree `4`) is **hub-isolated**: `|N(w) ∩ Hub| = 0`, since its four degree slots are all
  spent on its four twins.  In particular `w` is non-adjacent to every other hub.
* By `hno2hub` every iso-degree-`2` rich hub shares exactly one twin with `w` (so is a partner of a
  `w`-twin); by `hshare` the four `w`-twins have eight **distinct** partners, five of which are the
  rich hubs, three poor, leaving exactly one poor hub `u` off `w`'s twins.
* The two remaining (non-`w`) twins partition `{five rich hubs, u}` into two hub-independent
  triples (`twins_independent_of_no_cherry_S14`).
* `forced_hub_count_identities_S14` pins the within-`O` off-diagonal and the `T`-`O` cut
  (`T = {hg₁, hg₂, d₁, d₂}`, `O = Hub \ T`) to the iso-degrees of `d₁, d₂`.

The per-subcase contradiction (`isoDeg d₁ + isoDeg d₂ ∈ {2, 3, 4}`) then follows from these edge
identities together with the twin-independence forbidden pairs and `hno2hub`: at the
`e(Hub, Hub) = 9` no-slack budget the nine hub edges cannot realise the forced degree sequence
while avoiding every forbidden (twin-independent, `T`-internal, no-apex) pair.
-/

namespace ACMax

open scoped Classical

namespace N18

/-- **Design A (`{4,2,2,2,2,2}`) is impossible in the no-apex core.**  With the `r = 6`, `S = 14`
structure, `hshare`, `hno2hub`, no-apex (`hapex`), no-twin-cherry (`hcherry`) and `¬Adj d₁ d₂`, a
rich iso-degree distribution with one hub `w` of iso-degree `4` is contradictory.  `w` is
hub-isolated, its four twins have eight distinct partners forcing a single poor non-partner `u`, and
the two remaining twins partition `{rich, u}` into hub-independent triples; the `e(Hub, Hub) = 9`
cut identities (`forced_hub_count_identities_S14`) then collide with twin-independence and `hno2hub`
in each iso-degree subcase. -/
theorem forced_designA_false_S14 (G : SimpleGraph (Fin 18)) (Hub Iso : Finset (Fin 18))
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdisj : Disjoint Hub Iso) (hHub : Hub.card = 10) (hIso : Iso.card = 6)
    (hdsum : ∑ w ∈ Hub, G.degree w = 40)
    (hdeg3 : ∀ v : Fin 18, 3 ≤ G.degree v) (hisodeg3 : ∀ t ∈ Iso, G.degree t = 3)
    (hleak : ∑ h ∈ Hub, (G.neighborFinset h ∩ (Finset.univ \ (Hub ∪ Iso))).card ≤ 4)
    (hdeg4 : ∀ h ∈ Hub, G.degree h = 4)
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hno2hub : ¬∃ h₁ h₂ : Fin 18, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card)
    (hcherry : ¬∃ t ∈ Iso, ∃ a b : Fin 18, a ∈ G.neighborFinset t ∧ b ∈ G.neighborFinset t ∧
      a ≠ b ∧ G.Adj a b)
    (w z zp hg1 hg2 d1 d2 : Fin 18)
    (hwHub : w ∈ Hub) (hw4 : (G.neighborFinset w ∩ Iso).card = 4)
    (hother2 : ∀ r ∈ Hub, r ≠ w → 2 ≤ (G.neighborFinset r ∩ Iso).card →
      (G.neighborFinset r ∩ Iso).card = 2)
    (hr6 : (Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)).card = 6)
    (hzZ : z ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 18)))
    (hzpZ : zp ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 18)))
    (hg1Hub : hg1 ∈ Hub) (hg2Hub : hg2 ∈ Hub) (hd1Hub : d1 ∈ Hub) (hd2Hub : d2 ∈ Hub)
    (hg1z : G.Adj hg1 z) (hg2z : G.Adj hg2 z) (hd1zp : G.Adj d1 zp) (hd2zp : G.Adj d2 zp)
    (hg1zp : ¬G.Adj hg1 zp) (hg2zp : ¬G.Adj hg2 zp)
    (hg1g2 : hg1 ≠ hg2) (hd1d2 : d1 ≠ d2)
    (hnadj : ¬G.Adj hg1 hg2) (hd1d2nadj : ¬G.Adj d1 d2)
    (hcodeg0 : (G.neighborFinset hg1 ∩ G.neighborFinset hg2 ∩ Iso).card = 0)
    (hapex : ¬∃ x : Fin 18, x ∈ Hub ∧ x ≠ hg1 ∧ x ≠ hg2 ∧ G.Adj zp x ∧ (G.Adj hg1 x ∨ G.Adj hg2 x))
    (hg1iso1 : (G.neighborFinset hg1 ∩ Iso).card = 1)
    (hg2iso1 : (G.neighborFinset hg2 ∩ Iso).card = 1)
    (hd1iso : (G.neighborFinset d1 ∩ Iso).card = 1 ∨ (G.neighborFinset d1 ∩ Iso).card = 2)
    (hd2iso : (G.neighborFinset d2 ∩ Iso).card = 1 ∨ (G.neighborFinset d2 ∩ Iso).card = 2) :
    False := by
  classical
  -- The shared cut identities for `T = {hg₁, hg₂, d₁, d₂}`, `O = Hub \ T`.
  obtain ⟨hd1g1, hd1g2, hd2g1, hd2g2, ha_d1g1, ha_d1g2, ha_d2g1, ha_d2g2, hCUT2, hCUT1⟩ :=
    forced_hub_count_identities_S14 G Hub Iso hiso3 hdisj hHub hIso hdsum hdeg3 hisodeg3 hleak
      hdeg4 z zp hg1 hg2 d1 d2 hzZ hzpZ hg1Hub hg2Hub hd1Hub hd2Hub hg1z hg2z hd1zp hd2zp
      hg1zp hg2zp hg1g2 hd1d2 hnadj hd1d2nadj hapex hg1iso1 hg2iso1
  -- `w` is hub-isolated: all four degree slots are spent on its twins.
  have hwsplit := nbr_split_three_eighteen G Hub Iso hdisj w
  rw [hdeg4 w hwHub, hw4] at hwsplit
  have hwiso : (G.neighborFinset w ∩ Hub).card = 0 := by omega
  have hwz : (G.neighborFinset w ∩ (Finset.univ \ (Hub ∪ Iso))).card = 0 := by omega
  -- `w` is non-adjacent to every hub (its hub-neighbourhood is empty).
  have hwNoHub : ∀ h ∈ Hub, ¬G.Adj w h := by
    intro h hh hadj
    have : h ∈ G.neighborFinset w ∩ Hub :=
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hadj, hh⟩
    rw [Finset.card_eq_zero.mp hwiso] at this
    exact absurd this (Finset.notMem_empty h)
  -- The engine bound `E_RR ≥ 4` for the five iso-degree-`2` rich hubs.
  have hEngine := designA_rich_edges_ge_four_S14 G Hub Iso hiso3 hdisj hIso hdeg4 hshare hno2hub
    hcherry w hwHub hw4 hother2 hr6
  set Rich : Finset (Fin 18) := (Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)).erase w
    with hRichdef
  have hRichsubHub : Rich ⊆ Hub := by
    rw [hRichdef]; exact fun x hx => Finset.mem_of_mem_filter x (Finset.mem_of_mem_erase hx)
  have hbound := rich_internal_le_cut G Hub Rich ({hg1, hg2, d1, d2} : Finset (Fin 18)) hRichsubHub
  -- Poor hubs (iso-degree `1`) are never rich.
  have hnotRich : ∀ x : Fin 18, (G.neighborFinset x ∩ Iso).card = 1 → x ∉ Rich := by
    intro x hx hmem
    rw [hRichdef] at hmem
    have hxf := Finset.mem_of_mem_erase hmem
    rw [Finset.mem_filter] at hxf
    omega
  -- The iso-degree subcase split `isoDeg d₁ + isoDeg d₂ ∈ {2, 3, 4}`.
  rcases hd1iso with hd1a | hd1b <;> rcases hd2iso with hd2a | hd2b
  · -- Subcase `s = 2` (`isoDeg d₁ = isoDeg d₂ = 1`): both `d₁, d₂` poor; `T` is the four poor hubs,
    -- `O = {w} ∪ five rich`, so `e(O, O) = 1` and `e(T, O) = 8`.  The within-`O` edge cannot avoid
    -- the twin-independence forbidden pairs of the two non-`w` triples partitioning the rich hubs
    -- together with `w` hub-isolated — the rigid `e(Hub, Hub) = 9` no-slack collision.
    rw [hd1a, hd2a] at hCUT2 hCUT1
    have hRT : Rich ∩ ({hg1, hg2, d1, d2} : Finset (Fin 18)) = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro x hx
      rw [Finset.mem_inter] at hx
      have hxT := hx.2
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxT
      rcases hxT with h | h | h | h
      · exact hnotRich hg1 hg1iso1 (h ▸ hx.1)
      · exact hnotRich hg2 hg2iso1 (h ▸ hx.1)
      · exact hnotRich d1 hd1a (h ▸ hx.1)
      · exact hnotRich d2 hd2a (h ▸ hx.1)
    rw [hRT, Finset.sum_empty] at hbound
    omega
  · -- Subcase `s = 3` (`isoDeg d₁ = 1`, `isoDeg d₂ = 2`): `O = {w} ∪ four rich ∪ one poor`,
    -- `e(O, O) = 2`, `e(T, O) = 7`; same twin-independence collision at the no-slack budget.
    rw [hd1a, hd2b] at hCUT2 hCUT1
    have hRTsub : Rich ∩ ({hg1, hg2, d1, d2} : Finset (Fin 18)) ⊆ {d2} := by
      intro x hx
      rw [Finset.mem_inter] at hx
      have hxT := hx.2
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxT ⊢
      rcases hxT with h | h | h | h
      · exact absurd (h ▸ hx.1) (hnotRich hg1 hg1iso1)
      · exact absurd (h ▸ hx.1) (hnotRich hg2 hg2iso1)
      · exact absurd (h ▸ hx.1) (hnotRich d1 hd1a)
      · exact h
    have hsumle : ∑ d ∈ Rich ∩ ({hg1, hg2, d1, d2} : Finset (Fin 18)),
        (G.neighborFinset d ∩ Hub).card ≤ (G.neighborFinset d2 ∩ Hub).card := by
      calc _ ≤ ∑ d ∈ ({d2} : Finset (Fin 18)), (G.neighborFinset d ∩ Hub).card :=
            Finset.sum_le_sum_of_subset_of_nonneg hRTsub (fun _ _ _ => Nat.zero_le _)
        _ = (G.neighborFinset d2 ∩ Hub).card := Finset.sum_singleton _ _
    have hd2hub : (G.neighborFinset d2 ∩ Hub).card ≤ 1 := by
      have hsp := nbr_split_three_eighteen G Hub Iso hdisj d2
      rw [hdeg4 d2 hd2Hub, hd2b] at hsp
      have hzpos : 1 ≤ (G.neighborFinset d2 ∩ (Finset.univ \ (Hub ∪ Iso))).card :=
        Finset.card_pos.mpr ⟨zp, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hd2zp, hzpZ⟩⟩
      omega
    omega
  · -- Subcase `s = 3` (`isoDeg d₁ = 2`, `isoDeg d₂ = 1`), symmetric to the previous one.
    rw [hd1b, hd2a] at hCUT2 hCUT1
    have hRTsub : Rich ∩ ({hg1, hg2, d1, d2} : Finset (Fin 18)) ⊆ {d1} := by
      intro x hx
      rw [Finset.mem_inter] at hx
      have hxT := hx.2
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxT ⊢
      rcases hxT with h | h | h | h
      · exact absurd (h ▸ hx.1) (hnotRich hg1 hg1iso1)
      · exact absurd (h ▸ hx.1) (hnotRich hg2 hg2iso1)
      · exact h
      · exact absurd (h ▸ hx.1) (hnotRich d2 hd2a)
    have hsumle : ∑ d ∈ Rich ∩ ({hg1, hg2, d1, d2} : Finset (Fin 18)),
        (G.neighborFinset d ∩ Hub).card ≤ (G.neighborFinset d1 ∩ Hub).card := by
      calc _ ≤ ∑ d ∈ ({d1} : Finset (Fin 18)), (G.neighborFinset d ∩ Hub).card :=
            Finset.sum_le_sum_of_subset_of_nonneg hRTsub (fun _ _ _ => Nat.zero_le _)
        _ = (G.neighborFinset d1 ∩ Hub).card := Finset.sum_singleton _ _
    have hd1hub : (G.neighborFinset d1 ∩ Hub).card ≤ 1 := by
      have hsp := nbr_split_three_eighteen G Hub Iso hdisj d1
      rw [hdeg4 d1 hd1Hub, hd1b] at hsp
      have hzpos : 1 ≤ (G.neighborFinset d1 ∩ (Finset.univ \ (Hub ∪ Iso))).card :=
        Finset.card_pos.mpr ⟨zp, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hd1zp, hzpZ⟩⟩
      omega
    omega
  · -- Subcase `s = 4` (`isoDeg d₁ = isoDeg d₂ = 2`): `O = {w} ∪ three rich ∪ two poor`,
    -- `e(O, O) = 3`, `e(T, O) = 6`; the two poor `O`-hubs have hub-degree `3`, and the twin
    -- partition forbids enough rich-rich and rich-`u` pairs that the nine edges cannot be realised.
    exact designA_s4_false_S14 G Hub Iso hiso3 hdisj hHub hIso hdsum hdeg3 hisodeg3 hleak hdeg4
      hshare hno2hub hcherry w z zp hg1 hg2 d1 d2 hwHub hw4 hother2 hr6 hzZ hzpZ hg1Hub hg2Hub
      hd1Hub hd2Hub hg1z hg2z hd1zp hd2zp hg1zp hg2zp hg1g2 hd1d2 hnadj hd1d2nadj hapex hg1iso1
      hg2iso1 hcodeg0 hd1b hd2b

end N18

end ACMax
