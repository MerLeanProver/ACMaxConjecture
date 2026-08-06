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
import ACMaxConjecture.SmallCases.N18.ZPoorR6HubAdjBStruct
import ACMaxConjecture.SmallCases.N18.ZPoorR6CooccurB
import ACMaxConjecture.SmallCases.N18.ZPoorR6CodegCount
import ACMaxConjecture.SmallCases.N18.ZPoorR6BInfra

/-!
# Design B (`{3,3,2,2,2,2}`) `s = 4` co-occurrence kernel for the `r = 6`, `S = 14` core (`n = 18`)

The combinatorial heart of the `s = 4` subcase: when both hub-neighbours `d₁, d₂` of the `M`-partner
`zp` are iso-degree-`2` rich hubs, the two poor hubs `hg₁, hg₂` are forced onto a common twin, i.e.
`1 ≤ |N(hg₁) ∩ N(hg₂) ∩ Iso|`.  This is the unique fact whose negation (`hcodeg0`) is incompatible
with the rigid `s = 4` design (verified by direct enumeration: of all design-`B` `s = 4`
configurations realizable as hub graphs, **every** one has `hg₁, hg₂` co-occurring;
`scratchpad/searchB4graph.py`, `16` realizable designs, `0` with `codeg(hg₁, hg₂) = 0`).

## The mechanism (validated, `0` survivors)

Label the eight non-`w` hubs `D = {d₁, d₂, r₁, r₂}` (iso-degree `2`) and `P = {q₁, q₂, hg₁, hg₂}`
(iso-degree `1`), with hub-degrees `d₁, d₂ : 1`, `r₁, r₂ : 2`, `q₁, q₂ : 3`, `hg₁, hg₂ : 2`
(`w₁, w₂` have hub-degree `1`, joined only to each other).

* `d₁, d₂` non-adjacent ⟹ they co-occur on one twin `t* = {w_a, d₁, d₂}` (cooccur biconditional +
  `hshare`-codegree `≤ 1`).  Each has a second twin `tᵢ = {w_b, dᵢ, xᵢ}`.  As `dᵢ` has hub-degree
  `1` and the iso-`2` adjacency is governed by the cooccur biconditional, `xᵢ ∈ {r₁, r₂}` (else `dᵢ`
  would carry two forced iso-`2` edges), and `x₁ ≠ x₂` (an `rⱼ` occurs once per `w`-side).  Hence the
  four iso-`2` adjacencies among `D` are fully determined, `e(D) = 3`, and **`e(P, D) = 0`**: all of
  `P`'s hub-degree is internal.
* `P` then carries hub-degrees `[3, 3, 2, 2]` on four vertices, whose complement has exactly one
  edge: `P` is `K₄` minus the single non-edge `(hg₁, hg₂)` (forced by `hnadj`).
* The third `w_b`-twin `t₃` has two iso-`1` hubs (all iso-`2` hubs are used up); their pair is a
  `P`-non-edge (no-twin-cherry), hence equals the **only** `P`-non-edge `(hg₁, hg₂)`.  So
  `t₃ = {w_b, hg₁, hg₂}` and `hg₁, hg₂` co-occur.
-/

namespace ACMax

open scoped Classical

namespace N18

set_option maxHeartbeats 1600000 in
/-- **Design B, `s = 4` co-occurrence kernel.**  With both `d₁, d₂` iso-degree-`2` rich hubs in the
`r = 6`, `S = 14` design-`B` structure (no-apex, no-twin-cherry, `¬Adj d₁ d₂`), the two poor hubs
`hg₁, hg₂` share a common twin.  The rigid hub-degree pattern (`hg₁, hg₂` of hub-degree `2` with all
edges internal to the four iso-`1` hubs, forming `K₄` minus the single non-edge `hg₁ hg₂`) forces the
unique iso-`1`/iso-`1` twin onto `{hg₁, hg₂}`.  This is the fact that `hcodeg0` contradicts. -/
theorem designB_s4_dcooccur_S14 (G : SimpleGraph (Fin 18)) (Hub Iso : Finset (Fin 18))
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
    (w1 w2 z zp hg1 hg2 d1 d2 : Fin 18)
    (hw1Hub : w1 ∈ Hub) (hw2Hub : w2 ∈ Hub) (hw1w2ne : w1 ≠ w2)
    (hw13 : (G.neighborFinset w1 ∩ Iso).card = 3) (hw23 : (G.neighborFinset w2 ∩ Iso).card = 3)
    (hother2 : ∀ r ∈ Hub, r ≠ w1 → r ≠ w2 → 2 ≤ (G.neighborFinset r ∩ Iso).card →
      (G.neighborFinset r ∩ Iso).card = 2)
    (hzZ : z ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 18)))
    (hzpZ : zp ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 18)))
    (hg1Hub : hg1 ∈ Hub) (hg2Hub : hg2 ∈ Hub) (hd1Hub : d1 ∈ Hub) (hd2Hub : d2 ∈ Hub)
    (hg1z : G.Adj hg1 z) (hg2z : G.Adj hg2 z) (hd1zp : G.Adj d1 zp) (hd2zp : G.Adj d2 zp)
    (hg1zp : ¬G.Adj hg1 zp) (hg2zp : ¬G.Adj hg2 zp)
    (hg1g2 : hg1 ≠ hg2) (hd1d2 : d1 ≠ d2)
    (hnadj : ¬G.Adj hg1 hg2) (hd1d2nadj : ¬G.Adj d1 d2)
    (hapex : ¬∃ x : Fin 18, x ∈ Hub ∧ x ≠ hg1 ∧ x ≠ hg2 ∧ G.Adj zp x ∧ (G.Adj hg1 x ∨ G.Adj hg2 x))
    (hg1iso1 : (G.neighborFinset hg1 ∩ Iso).card = 1)
    (hg2iso1 : (G.neighborFinset hg2 ∩ Iso).card = 1)
    (hd1iso2 : (G.neighborFinset d1 ∩ Iso).card = 2)
    (hd2iso2 : (G.neighborFinset d2 ∩ Iso).card = 2) :
    1 ≤ (G.neighborFinset hg1 ∩ G.neighborFinset hg2 ∩ Iso).card := by
  classical
  set Z : Finset (Fin 18) := Finset.univ \ (Hub ∪ Iso) with hZdef
  -- Rigid skeleton + rich co-occurrence biconditional (shared with the other subcases).
  obtain ⟨hadjw, hw1hub1, hw2hub1, _hw1z0, _hw2z0, hpart, hd1w1, hd1w2, hd2w1, hd2w2⟩ :=
    designB_w_structure_S14 G Hub Iso hdisj hIso hdeg4 hshare hno2hub hcherry w1 w2 zp d1 d2
      hw1Hub hw2Hub hw1w2ne hw13 hw23 hzpZ hd1zp hd2zp
  obtain ⟨_hcoA, hcoB⟩ :=
    designB_rich_cooccur_S14 G Hub Iso hdeg4 hshare hno2hub hcherry w1 w2 hw1Hub hw2Hub hadjw
      hw1hub1 hw2hub1 hw13 hw23
  -- Distinctness from iso-degrees: `d`s are iso-`2`, `hg`s iso-`1`, `w`s iso-`3`.
  have hw1g1 : w1 ≠ hg1 := fun h => by rw [h, hg1iso1] at hw13; omega
  have hw1g2 : w1 ≠ hg2 := fun h => by rw [h, hg2iso1] at hw13; omega
  have hw2g1 : w2 ≠ hg1 := fun h => by rw [h, hg1iso1] at hw23; omega
  have hw2g2 : w2 ≠ hg2 := fun h => by rw [h, hg2iso1] at hw23; omega
  have hd1g1 : d1 ≠ hg1 := fun h => by rw [h, hg1iso1] at hd1iso2; omega
  have hd1g2 : d1 ≠ hg2 := fun h => by rw [h, hg2iso1] at hd1iso2; omega
  have hd2g1 : d2 ≠ hg1 := fun h => by rw [h, hg1iso1] at hd2iso2; omega
  have hd2g2 : d2 ≠ hg2 := fun h => by rw [h, hg2iso1] at hd2iso2; omega
  set OO : Finset (Fin 18) := Hub \ ({w1, w2} : Finset (Fin 18)) with hOOdef
  -- `N(w₁) ∩ Hub = {w₂}`, `N(w₂) ∩ Hub = {w₁}`, so no `OO`-hub is adjacent to a `w`.
  have hw2mem : w2 ∈ G.neighborFinset w1 ∩ Hub :=
    Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hadjw, hw2Hub⟩
  have hw1mem : w1 ∈ G.neighborFinset w2 ∩ Hub :=
    Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hadjw.symm, hw1Hub⟩
  have hw1set : G.neighborFinset w1 ∩ Hub = {w2} :=
    Finset.eq_singleton_iff_unique_mem.mpr ⟨hw2mem, fun x hx =>
      Finset.card_le_one.mp (le_of_eq hw1hub1) x hx w2 hw2mem⟩
  have hw2set : G.neighborFinset w2 ∩ Hub = {w1} :=
    Finset.eq_singleton_iff_unique_mem.mpr ⟨hw1mem, fun x hx =>
      Finset.card_le_one.mp (le_of_eq hw2hub1) x hx w1 hw1mem⟩
  have hOOsubHub : OO ⊆ Hub := by rw [hOOdef]; exact Finset.sdiff_subset
  have hOOmem : ∀ x, x ∈ OO ↔ x ∈ Hub ∧ x ≠ w1 ∧ x ≠ w2 := by
    intro x; rw [hOOdef, Finset.mem_sdiff]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
  have hwnadj : ∀ h, h ∈ OO → ¬G.Adj w1 h ∧ ¬G.Adj w2 h := by
    intro h hh
    obtain ⟨hhHub, hhw1, hhw2⟩ := (hOOmem h).mp hh
    refine ⟨fun hadj => ?_, fun hadj => ?_⟩
    · have : h ∈ G.neighborFinset w1 ∩ Hub :=
        Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hadj, hhHub⟩
      rw [hw1set, Finset.mem_singleton] at this; exact hhw2 this
    · have : h ∈ G.neighborFinset w2 ∩ Hub :=
        Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hadj, hhHub⟩
      rw [hw2set, Finset.mem_singleton] at this; exact hhw1 this
  -- The four named non-`w` hubs lie in `OO`.
  have hd1OO : d1 ∈ OO := (hOOmem d1).mpr ⟨hd1Hub, hd1w1, hd1w2⟩
  have hd2OO : d2 ∈ OO := (hOOmem d2).mpr ⟨hd2Hub, hd2w1, hd2w2⟩
  have hg1OO : hg1 ∈ OO := (hOOmem hg1).mpr ⟨hg1Hub, Ne.symm hw1g1, Ne.symm hw2g1⟩
  have hg2OO : hg2 ∈ OO := (hOOmem hg2).mpr ⟨hg2Hub, Ne.symm hw1g2, Ne.symm hw2g2⟩
  -- Each twin meets `OO` in exactly `2` vertices (it meets exactly one of `w₁, w₂`).
  have htwin2 : ∀ t ∈ Iso, (G.neighborFinset t ∩ OO).card = 2 := by
    intro t ht
    have hsub : G.neighborFinset t ∩ OO = (G.neighborFinset t ∩ Hub) \ {w1, w2} := by
      rw [hOOdef]; ext x
      simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
      tauto
    rw [hsub]
    have hflip : ∀ w : Fin 18, t ∈ G.neighborFinset w ↔ w ∈ G.neighborFinset t := by
      intro w; rw [G.mem_neighborFinset, G.mem_neighborFinset, G.adj_comm]
    rcases hpart t ht with ⟨hw1, hw2⟩ | ⟨hw1, hw2⟩
    · have hsing : (G.neighborFinset t ∩ Hub) ∩ ({w1, w2} : Finset (Fin 18)) = {w1} := by
        apply Finset.eq_singleton_iff_unique_mem.mpr
        refine ⟨Finset.mem_inter.mpr ⟨Finset.mem_inter.mpr ⟨(hflip w1).mp hw1, hw1Hub⟩,
          Finset.mem_insert_self w1 _⟩, ?_⟩
        intro x hx
        obtain ⟨hxNH, hx2⟩ := Finset.mem_inter.mp hx
        rcases Finset.mem_insert.mp hx2 with h | h
        · exact h
        · rw [Finset.mem_singleton] at h
          exact absurd ((hflip w2).mpr (h ▸ (Finset.mem_inter.mp hxNH).1)) hw2
      have := Finset.card_sdiff_add_card_inter (G.neighborFinset t ∩ Hub) ({w1, w2} : Finset (Fin 18))
      rw [hsing, Finset.card_singleton, hiso3 t ht] at this; omega
    · have hsing : (G.neighborFinset t ∩ Hub) ∩ ({w1, w2} : Finset (Fin 18)) = {w2} := by
        apply Finset.eq_singleton_iff_unique_mem.mpr
        refine ⟨Finset.mem_inter.mpr ⟨Finset.mem_inter.mpr ⟨(hflip w2).mp hw2, hw2Hub⟩,
          Finset.mem_insert_of_mem (Finset.mem_singleton_self w2)⟩, ?_⟩
        intro x hx
        obtain ⟨hxNH, hx2⟩ := Finset.mem_inter.mp hx
        rcases Finset.mem_insert.mp hx2 with h | h
        · exact absurd ((hflip w1).mpr (h ▸ (Finset.mem_inter.mp hxNH).1)) hw1
        · rw [Finset.mem_singleton] at h; exact h
      have := Finset.card_sdiff_add_card_inter (G.neighborFinset t ∩ Hub) ({w1, w2} : Finset (Fin 18))
      rw [hsing, Finset.card_singleton, hiso3 t ht] at this; omega
  -- Within-`OO` degree: `|N(h) ∩ OO| = |N(h) ∩ Hub|`, so `|N∩OO|+|N∩Iso|+|N∩Z| = 4`.
  have hNeq : ∀ h, h ∈ OO → G.neighborFinset h ∩ OO = G.neighborFinset h ∩ Hub := by
    intro h hh; ext x
    simp only [Finset.mem_inter]
    refine ⟨fun ⟨hx1, hx2⟩ => ⟨hx1, hOOsubHub hx2⟩, fun ⟨hx1, hx2⟩ => ⟨hx1, ?_⟩⟩
    have hxadj : G.Adj h x := (G.mem_neighborFinset _ _).mp hx1
    refine (hOOmem x).mpr ⟨hx2, fun hxw1 => ?_, fun hxw2 => ?_⟩
    · exact (hwnadj h hh).1 (hxw1 ▸ hxadj).symm
    · exact (hwnadj h hh).2 (hxw2 ▸ hxadj).symm
  have hdegsplit : ∀ h, h ∈ OO → (G.neighborFinset h ∩ OO).card + (G.neighborFinset h ∩ Iso).card
      + (G.neighborFinset h ∩ Z).card = 4 := by
    intro h hh
    have hsp := nbr_split_three_eighteen G Hub Iso hdisj h
    rw [hdeg4 h (hOOsubHub hh)] at hsp
    rw [← hZdef] at hsp; rw [hNeq h hh]; omega
  -- `Z`-exhaustion: the four `Z`-edges sit on `hg₁, hg₂, d₁, d₂`.
  have hZ4 : ∑ h ∈ Hub, (G.neighborFinset h ∩ Z).card = 4 := by
    rw [hZdef]
    exact zdeg_sum_four_eighteen G Hub Iso hiso3 hdisj hHub hIso hdsum hdeg3 hisodeg3 hleak
  set S4 : Finset (Fin 18) := ({hg1, hg2, d1, d2} : Finset (Fin 18)) with hS4def
  have hS4sub : S4 ⊆ Hub := by
    rw [hS4def]; intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  have hS4sum : ∀ f : Fin 18 → ℕ, ∑ v ∈ S4, f v = f hg1 + f hg2 + f d1 + f d2 := by
    intro f
    rw [hS4def, show ({hg1, hg2, d1, d2} : Finset (Fin 18))
        = insert hg1 (insert hg2 (insert d1 {d2})) from rfl,
      Finset.sum_insert (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hg1g2, Ne.symm hd1g1, Ne.symm hd2g1⟩),
      Finset.sum_insert (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨Ne.symm hd1g2, Ne.symm hd2g2⟩),
      Finset.sum_insert (by simp only [Finset.mem_singleton]; exact hd1d2),
      Finset.sum_singleton]
    ring
  have hZpos : ∀ p : Fin 18, ∀ q : Fin 18, G.Adj p q → q ∈ Z → 1 ≤ (G.neighborFinset p ∩ Z).card := by
    intro p q hpq hqZ
    apply Finset.card_pos.mpr
    exact ⟨q, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hpq, hqZ⟩⟩
  have hzZ' : z ∈ Z := by rw [hZdef]; exact hzZ
  have hzpZ' : zp ∈ Z := by rw [hZdef]; exact hzpZ
  have hS4le : ∑ v ∈ S4, (G.neighborFinset v ∩ Z).card ≤ 4 := by
    have := Finset.sum_le_sum_of_subset hS4sub (f := fun h => (G.neighborFinset h ∩ Z).card)
    omega
  have hS4exp := hS4sum (fun h => (G.neighborFinset h ∩ Z).card)
  have hz_g1 := hZpos hg1 z hg1z hzZ'
  have hz_g2 := hZpos hg2 z hg2z hzZ'
  have hz_d1 := hZpos d1 zp hd1zp hzpZ'
  have hz_d2 := hZpos d2 zp hd2zp hzpZ'
  have hZg1 : (G.neighborFinset hg1 ∩ Z).card = 1 := by omega
  have hZg2 : (G.neighborFinset hg2 ∩ Z).card = 1 := by omega
  have hZd1 : (G.neighborFinset d1 ∩ Z).card = 1 := by omega
  have hZd2 : (G.neighborFinset d2 ∩ Z).card = 1 := by omega
  -- Outside `S4`, the `Z`-degree is `0`.
  have hZout : ∀ h, h ∈ Hub → h ∉ S4 → (G.neighborFinset h ∩ Z).card = 0 := by
    have hsd := Finset.sum_sdiff (f := fun h => (G.neighborFinset h ∩ Z).card) hS4sub
    have hrest : ∑ h ∈ Hub \ S4, (G.neighborFinset h ∩ Z).card = 0 := by omega
    intro h hhHub hhS4
    exact (Finset.sum_eq_zero_iff.mp hrest) h (Finset.mem_sdiff.mpr ⟨hhHub, hhS4⟩)
  -- The iso-degree-`2` hubs `R2` and the poor hubs `Poor` partition `OO`.
  set R2 : Finset (Fin 18) := OO.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card) with hR2def
  set Poor : Finset (Fin 18) := OO \ R2 with hPoordef
  have hR2subOO : R2 ⊆ OO := by rw [hR2def]; exact Finset.filter_subset _ _
  have hR2iso2 : ∀ r, r ∈ R2 → (G.neighborFinset r ∩ Iso).card = 2 := by
    intro r hr; rw [hR2def, Finset.mem_filter] at hr
    obtain ⟨hrHub, hrne1, hrne2⟩ := (hOOmem r).mp hr.1
    exact hother2 r hrHub hrne1 hrne2 hr.2
  have hPoorle1 : ∀ p, p ∈ Poor → (G.neighborFinset p ∩ Iso).card ≤ 1 := by
    intro p hp; rw [hPoordef, Finset.mem_sdiff] at hp
    by_contra hc
    push Not at hc
    exact hp.2 (by rw [hR2def, Finset.mem_filter]; exact ⟨hp.1, by omega⟩)
  have hd1R2 : d1 ∈ R2 := by rw [hR2def, Finset.mem_filter]; exact ⟨hd1OO, by rw [hd1iso2]⟩
  have hd2R2 : d2 ∈ R2 := by rw [hR2def, Finset.mem_filter]; exact ⟨hd2OO, by rw [hd2iso2]⟩
  have hg1Poor : hg1 ∈ Poor := by
    rw [hPoordef, Finset.mem_sdiff]
    refine ⟨hg1OO, fun hr => ?_⟩
    rw [hR2def, Finset.mem_filter] at hr; rw [hg1iso1] at hr; omega
  have hg2Poor : hg2 ∈ Poor := by
    rw [hPoordef, Finset.mem_sdiff]
    refine ⟨hg2OO, fun hr => ?_⟩
    rw [hR2def, Finset.mem_filter] at hr; rw [hg2iso1] at hr; omega
  have hR2notg : ∀ r, r ∈ R2 → r ≠ hg1 ∧ r ≠ hg2 := by
    intro r hr
    have h2 := hR2iso2 r hr
    exact ⟨fun h => by rw [h, hg1iso1] at h2; omega, fun h => by rw [h, hg2iso1] at h2; omega⟩
  -- `|OO| = 8` and the iso-incidence sum on `OO` is `12`.
  have hw12subHub : ({w1, w2} : Finset (Fin 18)) ⊆ Hub := by
    intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  have hOOcard : OO.card = 8 := by
    have h := Finset.card_sdiff (s := ({w1, w2} : Finset (Fin 18))) (t := Hub)
    rw [Finset.inter_eq_left.mpr hw12subHub, Finset.card_pair hw1w2ne, hHub] at h
    rw [hOOdef]; omega
  have hHubIso : ∑ h ∈ Hub, (G.neighborFinset h ∩ Iso).card = 18 := by
    have h := hub_iso_sum_eighteen G Hub Iso hiso3; rw [hIso] at h; omega
  have hOOiso : ∑ h ∈ OO, (G.neighborFinset h ∩ Iso).card = 12 := by
    have hsd := Finset.sum_sdiff (f := fun h => (G.neighborFinset h ∩ Iso).card) hw12subHub
    rw [← hOOdef] at hsd
    rw [Finset.sum_pair hw1w2ne, hw13, hw23] at hsd
    omega
  -- `within-OO` degree of `d₁` is `1` (degree `4`, iso `2`, `Z` `1`).
  have hd1deg1 : (G.neighborFinset d1 ∩ OO).card = 1 := by
    have := hdegsplit d1 hd1OO; rw [hd1iso2, hZd1] at this; omega
  -- `∑_{r ∈ OO \ {d₁}} codeg(d₁, r) = 2`.
  have hd1cosum : ∑ r ∈ OO.erase d1,
      (G.neighborFinset d1 ∩ G.neighborFinset r ∩ Iso).card = 2 := by
    have hrw : ∀ r, (G.neighborFinset d1 ∩ G.neighborFinset r ∩ Iso).card
        = (G.neighborFinset r ∩ (G.neighborFinset d1 ∩ Iso)).card := by
      intro r; congr 1; ext x; simp only [Finset.mem_inter]; tauto
    rw [Finset.sum_congr rfl (fun r _ => hrw r),
      cross_count G (OO.erase d1) (G.neighborFinset d1 ∩ Iso)]
    have hterm : ∀ a, a ∈ G.neighborFinset d1 ∩ Iso →
        (G.neighborFinset a ∩ OO.erase d1).card = 1 := by
      intro a ha
      rw [Finset.mem_inter, G.mem_neighborFinset] at ha
      obtain ⟨had1, haIso⟩ := ha
      have hd1Na : d1 ∈ G.neighborFinset a := (G.mem_neighborFinset _ _).mpr had1.symm
      have heq : G.neighborFinset a ∩ OO.erase d1 = (G.neighborFinset a ∩ OO).erase d1 := by
        ext x; simp only [Finset.mem_inter, Finset.mem_erase]; tauto
      rw [heq, Finset.card_erase_of_mem (Finset.mem_inter.mpr ⟨hd1Na, hd1OO⟩), htwin2 a haIso]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, hd1iso2, smul_eq_mul, mul_one]
  -- Hence `|R2| ≤ 4`: `d₁` is adjacent to every `R2`-hub it does not co-occur with.
  have hAdjsub : (R2.erase d1).filter
        (fun r => (G.neighborFinset d1 ∩ G.neighborFinset r ∩ Iso).card = 0)
      ⊆ G.neighborFinset d1 ∩ OO := by
    intro r hr
    rw [Finset.mem_filter, Finset.mem_erase] at hr
    obtain ⟨⟨hrd1, hrR2⟩, hcodeg0r⟩ := hr
    obtain ⟨hrHub, hrw1, hrw2⟩ := (hOOmem r).mp (hR2subOO hrR2)
    have hbic := hcoB d1 hd1Hub r hrHub hd1w1 hd1w2 hrw1 hrw2 hd1iso2 (hR2iso2 r hrR2)
      (Ne.symm hrd1)
    have hadj : G.Adj d1 r := by
      by_contra hna
      have h1 := hbic.mp hna; rw [hcodeg0r] at h1; omega
    exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hadj, hR2subOO hrR2⟩
  have hAdjcard : ((R2.erase d1).filter
      (fun r => (G.neighborFinset d1 ∩ G.neighborFinset r ∩ Iso).card = 0)).card ≤ 1 := by
    calc _ ≤ (G.neighborFinset d1 ∩ OO).card := Finset.card_le_card hAdjsub
      _ = 1 := hd1deg1
  have hCocard : ((R2.erase d1).filter
      (fun r => ¬ (G.neighborFinset d1 ∩ G.neighborFinset r ∩ Iso).card = 0)).card ≤ 2 := by
    have hsub : (R2.erase d1).filter
        (fun r => ¬ (G.neighborFinset d1 ∩ G.neighborFinset r ∩ Iso).card = 0) ⊆ OO.erase d1 := by
      intro r hr
      rw [Finset.mem_filter, Finset.mem_erase] at hr
      exact Finset.mem_erase.mpr ⟨hr.1.1, hR2subOO hr.1.2⟩
    have hle1 : ((R2.erase d1).filter
        (fun r => ¬ (G.neighborFinset d1 ∩ G.neighborFinset r ∩ Iso).card = 0)).card
        ≤ ∑ r ∈ (R2.erase d1).filter
            (fun r => ¬ (G.neighborFinset d1 ∩ G.neighborFinset r ∩ Iso).card = 0),
          (G.neighborFinset d1 ∩ G.neighborFinset r ∩ Iso).card := by
      rw [Finset.card_eq_sum_ones]
      apply Finset.sum_le_sum
      intro r hr; rw [Finset.mem_filter] at hr; omega
    have hle2 : ∑ r ∈ (R2.erase d1).filter
            (fun r => ¬ (G.neighborFinset d1 ∩ G.neighborFinset r ∩ Iso).card = 0),
          (G.neighborFinset d1 ∩ G.neighborFinset r ∩ Iso).card
        ≤ ∑ r ∈ OO.erase d1, (G.neighborFinset d1 ∩ G.neighborFinset r ∩ Iso).card :=
      Finset.sum_le_sum_of_subset hsub
    omega
  have hR2erase : (R2.erase d1).card ≤ 3 := by
    have hpart := Finset.card_filter_add_card_filter_not
      (s := R2.erase d1)
      (p := fun r => (G.neighborFinset d1 ∩ G.neighborFinset r ∩ Iso).card = 0)
    omega
  have hR2card : R2.card = 4 := by
    have hk4 : (R2.erase d1).card = R2.card - 1 := Finset.card_erase_of_mem hd1R2
    -- lower bound `|R2| ≥ 4` from the iso-incidence sum.
    have hsplit := Finset.sum_sdiff (f := fun h => (G.neighborFinset h ∩ Iso).card) hR2subOO
    rw [← hPoordef] at hsplit
    have hR2sum : ∑ r ∈ R2, (G.neighborFinset r ∩ Iso).card = 2 * R2.card := by
      rw [Finset.sum_congr rfl (fun r hr => hR2iso2 r hr), Finset.sum_const, smul_eq_mul]; ring
    have hPoorsum : ∑ p ∈ Poor, (G.neighborFinset p ∩ Iso).card ≤ Poor.card := by
      calc _ ≤ ∑ _p ∈ Poor, 1 := Finset.sum_le_sum (fun p hp => hPoorle1 p hp)
        _ = Poor.card := by rw [Finset.sum_const, smul_eq_mul, mul_one]
    have hPoorcard : Poor.card = OO.card - R2.card := by
      have h := Finset.card_sdiff (s := R2) (t := OO)
      rw [Finset.inter_eq_left.mpr hR2subOO] at h
      rw [hPoordef]; omega
    have hR2le : R2.card ≤ 8 := by rw [← hOOcard]; exact Finset.card_le_card hR2subOO
    rw [hR2sum, hOOiso] at hsplit
    omega
  -- Partition sums over `OO = R2 ⊔ Poor`.
  have hpartsum : ∀ f : Fin 18 → ℕ,
      ∑ h ∈ OO, f h = (∑ r ∈ R2, f r) + ∑ p ∈ Poor, f p := by
    intro f
    have h := Finset.sum_sdiff (f := f) hR2subOO
    rw [← hPoordef] at h; omega
  have hPoorcard : Poor.card = 4 := by
    have h := Finset.card_sdiff (s := R2) (t := OO)
    rw [Finset.inter_eq_left.mpr hR2subOO, hOOcard, hR2card] at h
    rw [hPoordef]; omega
  have hR2isosum : ∑ r ∈ R2, (G.neighborFinset r ∩ Iso).card = 8 := by
    rw [Finset.sum_congr rfl (fun r hr => hR2iso2 r hr), Finset.sum_const, hR2card, smul_eq_mul]
  have hPoorisosum : ∑ p ∈ Poor, (G.neighborFinset p ∩ Iso).card = 4 := by
    have h := hpartsum (fun h => (G.neighborFinset h ∩ Iso).card)
    rw [hOOiso, hR2isosum] at h; omega
  have hPooriso1 : ∀ p, p ∈ Poor → (G.neighborFinset p ∩ Iso).card = 1 := by
    have hkey : ∑ p ∈ Poor, (1 - (G.neighborFinset p ∩ Iso).card) = 0 := by
      have h1 : ∑ p ∈ Poor, ((1 - (G.neighborFinset p ∩ Iso).card)
          + (G.neighborFinset p ∩ Iso).card) = ∑ _p ∈ Poor, 1 :=
        Finset.sum_congr rfl (fun p hp => by have := hPoorle1 p hp; omega)
      rw [Finset.sum_add_distrib, hPoorisosum, Finset.sum_const, hPoorcard, smul_eq_mul] at h1
      omega
    intro p hp
    have h0 := (Finset.sum_eq_zero_iff.mp hkey) p hp
    have := hPoorle1 p hp; omega
  -- `Z`-degree sub-sums: `∑_{R2} = 2`, `∑_{Poor} = 2`.
  have hd1d2subR2 : ({d1, d2} : Finset (Fin 18)) ⊆ R2 := by
    intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hd1R2
    · exact hd2R2
  have hg1g2subPoor : ({hg1, hg2} : Finset (Fin 18)) ⊆ Poor := by
    intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hg1Poor
    · exact hg2Poor
  have hR2Zsum : ∑ r ∈ R2, (G.neighborFinset r ∩ Z).card = 2 := by
    have hsd := Finset.sum_sdiff (f := fun h => (G.neighborFinset h ∩ Z).card) hd1d2subR2
    have hz0 : ∑ r ∈ R2 \ ({d1, d2} : Finset (Fin 18)), (G.neighborFinset r ∩ Z).card = 0 := by
      apply Finset.sum_eq_zero
      intro r hr
      rw [Finset.mem_sdiff] at hr
      obtain ⟨hrR2, hrne⟩ := hr
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hrne
      have hrHub : r ∈ Hub := hOOsubHub (hR2subOO hrR2)
      apply hZout r hrHub
      rw [hS4def]; simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨(hR2notg r hrR2).1, (hR2notg r hrR2).2, hrne.1, hrne.2⟩
    rw [Finset.sum_pair hd1d2, hZd1, hZd2] at hsd
    omega
  have hPoorZsum : ∑ p ∈ Poor, (G.neighborFinset p ∩ Z).card = 2 := by
    have hsd := Finset.sum_sdiff (f := fun h => (G.neighborFinset h ∩ Z).card) hg1g2subPoor
    have hz0 : ∑ p ∈ Poor \ ({hg1, hg2} : Finset (Fin 18)), (G.neighborFinset p ∩ Z).card = 0 := by
      apply Finset.sum_eq_zero
      intro p hp
      rw [Finset.mem_sdiff] at hp
      obtain ⟨hpPoor, hpne⟩ := hp
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hpne
      have hpOO : p ∈ OO := by rw [hPoordef] at hpPoor; exact (Finset.mem_sdiff.mp hpPoor).1
      have hpnotR2 : p ∉ R2 := by rw [hPoordef] at hpPoor; exact (Finset.mem_sdiff.mp hpPoor).2
      apply hZout p (hOOsubHub hpOO)
      rw [hS4def]; simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hpne.1, hpne.2, fun h => hpnotR2 (h ▸ hd1R2), fun h => hpnotR2 (h ▸ hd2R2)⟩
    rw [Finset.sum_pair hg1g2, hZg1, hZg2] at hsd
    omega
  -- Within-`OO` degree sums.
  have hP1 : ∑ r ∈ R2, (G.neighborFinset r ∩ OO).card = 6 := by
    have hconst : ∑ r ∈ R2, ((G.neighborFinset r ∩ OO).card + (G.neighborFinset r ∩ Iso).card
        + (G.neighborFinset r ∩ Z).card) = ∑ _r ∈ R2, 4 :=
      Finset.sum_congr rfl (fun r hr => hdegsplit r (hR2subOO hr))
    rw [Finset.sum_const, hR2card, smul_eq_mul, Finset.sum_add_distrib, Finset.sum_add_distrib,
      hR2isosum, hR2Zsum] at hconst
    omega
  have hP2 : ∑ p ∈ Poor, (G.neighborFinset p ∩ OO).card = 10 := by
    have hPoorsubOO : Poor ⊆ OO := by rw [hPoordef]; exact Finset.sdiff_subset
    have hconst : ∑ p ∈ Poor, ((G.neighborFinset p ∩ OO).card + (G.neighborFinset p ∩ Iso).card
        + (G.neighborFinset p ∩ Z).card) = ∑ _p ∈ Poor, 4 :=
      Finset.sum_congr rfl (fun p hp => hdegsplit p (hPoorsubOO hp))
    rw [Finset.sum_const, hPoorcard, smul_eq_mul, Finset.sum_add_distrib, Finset.sum_add_distrib,
      hPoorisosum, hPoorZsum] at hconst
    omega
  -- Per-neighbourhood split `|N x ∩ OO| = |N x ∩ R2| + |N x ∩ Poor|`.
  have hR2subHub : R2 ⊆ Hub := fun x hx => hOOsubHub (hR2subOO hx)
  have hPoorsubHub : Poor ⊆ Hub := fun x hx => by
    rw [hPoordef] at hx; exact hOOsubHub (Finset.mem_sdiff.mp hx).1
  have hsplitNbr : ∀ x : Fin 18, (G.neighborFinset x ∩ OO).card
      = (G.neighborFinset x ∩ R2).card + (G.neighborFinset x ∩ Poor).card := by
    intro x
    have hi := Finset.card_inter_add_card_sdiff (G.neighborFinset x ∩ OO) R2
    have e1 : (G.neighborFinset x ∩ OO) ∩ R2 = G.neighborFinset x ∩ R2 := by
      ext y; simp only [Finset.mem_inter]
      exact ⟨fun ⟨⟨h1, _⟩, h3⟩ => ⟨h1, h3⟩, fun ⟨h1, h3⟩ => ⟨⟨h1, hR2subOO h3⟩, h3⟩⟩
    have e2 : (G.neighborFinset x ∩ OO) \ R2 = G.neighborFinset x ∩ Poor := by
      rw [hPoordef]; ext y; simp only [Finset.mem_inter, Finset.mem_sdiff]; tauto
    rw [e1, e2] at hi; omega
  -- Within-`R2`, within-`Poor` edge counts; the cross count.
  have hwR2 := within_sum_eq_two_mul_S14 G R2
  have hwPoor := within_sum_eq_two_mul_S14 G Poor
  set a := (R2.offDiag.filter (fun p => p.1 < p.2 ∧ G.Adj p.1 p.2)).card with hadef
  set b := (Poor.offDiag.filter (fun p => p.1 < p.2 ∧ G.Adj p.1 p.2)).card with hbdef
  have hX := cross_count G R2 Poor
  have hP1split : ∑ r ∈ R2, (G.neighborFinset r ∩ OO).card
      = (∑ r ∈ R2, (G.neighborFinset r ∩ R2).card)
        + ∑ r ∈ R2, (G.neighborFinset r ∩ Poor).card := by
    rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl (fun r _ => hsplitNbr r)
  have hP2split : ∑ p ∈ Poor, (G.neighborFinset p ∩ OO).card
      = (∑ p ∈ Poor, (G.neighborFinset p ∩ Poor).card)
        + ∑ p ∈ Poor, (G.neighborFinset p ∩ R2).card := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun p _ => by have := hsplitNbr p; omega)
  have e6 : (6 : ℕ) = 2 * a + ∑ r ∈ R2, (G.neighborFinset r ∩ Poor).card := by
    rw [← hP1, hP1split, hwR2]
  have e10 : (10 : ℕ) = 2 * b + ∑ p ∈ Poor, (G.neighborFinset p ∩ R2).card := by
    rw [← hP2, hP2split, hwPoor]
  have hba : b = a + 2 := by omega
  -- The rich engine and the `cR2 = cP + 2` transfer identity.
  have hEngine := designB_rich4_edge_eq_S14 G Hub Iso R2 hdeg4 hshare hno2hub hcherry
    hR2subHub hR2card hR2iso2
  set cR2 := ∑ t ∈ Iso, ((G.neighborFinset t ∩ R2).card).choose 2 with hcR2def
  set cP := ∑ t ∈ Iso, ((G.neighborFinset t ∩ Poor).card).choose 2 with hcPdef
  have htwinR2le : ∀ t, t ∈ Iso → (G.neighborFinset t ∩ R2).card ≤ 2 := by
    intro t ht
    calc (G.neighborFinset t ∩ R2).card ≤ (G.neighborFinset t ∩ OO).card :=
          Finset.card_le_card (Finset.inter_subset_inter subset_rfl hR2subOO)
      _ = 2 := htwin2 t ht
  have htwinsplit : ∀ t, t ∈ Iso →
      (G.neighborFinset t ∩ R2).card + (G.neighborFinset t ∩ Poor).card = 2 := by
    intro t ht; rw [← hsplitNbr t, htwin2 t ht]
  have hcr2cp : cR2 = cP + 2 := by
    have hid : ∀ t, t ∈ Iso → ((G.neighborFinset t ∩ R2).card).choose 2 + 1
        = ((G.neighborFinset t ∩ Poor).card).choose 2 + (G.neighborFinset t ∩ R2).card := by
      intro t ht
      have hle := htwinR2le t ht
      have hs := htwinsplit t ht
      rcases (by omega : (G.neighborFinset t ∩ R2).card = 0 ∨ (G.neighborFinset t ∩ R2).card = 1
          ∨ (G.neighborFinset t ∩ R2).card = 2) with h | h | h
      · rw [h, show (G.neighborFinset t ∩ Poor).card = 2 from by omega]; decide
      · rw [h, show (G.neighborFinset t ∩ Poor).card = 1 from by omega]
      · rw [h, show (G.neighborFinset t ∩ Poor).card = 0 from by omega]; decide
    have hsum : ∑ t ∈ Iso, (((G.neighborFinset t ∩ R2).card).choose 2 + 1)
        = ∑ t ∈ Iso, (((G.neighborFinset t ∩ Poor).card).choose 2
          + (G.neighborFinset t ∩ R2).card) := Finset.sum_congr rfl hid
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, hIso, smul_eq_mul,
      mul_one, ← hcR2def, ← hcPdef] at hsum
    have htR2sum : ∑ t ∈ Iso, (G.neighborFinset t ∩ R2).card = 8 := by
      rw [cross_count G Iso R2]; exact hR2isosum
    rw [htR2sum] at hsum; omega
  -- The poor non-edge / co-occurrence count balance.
  have hltcard : (Poor.offDiag.filter (fun p => p.1 < p.2)).card = 6 := by
    rw [card_offDiag_filter_lt, hPoorcard]; decide
  have hNEsplit := Finset.card_filter_add_card_filter_not
    (s := Poor.offDiag.filter (fun p => p.1 < p.2)) (p := fun p => G.Adj p.1 p.2)
  have hfilteqAdj : (Poor.offDiag.filter (fun p => p.1 < p.2)).filter (fun p => G.Adj p.1 p.2)
      = Poor.offDiag.filter (fun p => p.1 < p.2 ∧ G.Adj p.1 p.2) := Finset.filter_filter _ _ _
  rw [hfilteqAdj, ← hbdef, hltcard] at hNEsplit
  have hcPeq := codeg_pair_sum_eq_twin_choose2 G Iso Poor
  rw [← hcPdef] at hcPeq
  have hcodeg_le1 : ∀ p ∈ Poor.offDiag.filter (fun p => p.1 < p.2),
      (G.neighborFinset p.1 ∩ G.neighborFinset p.2 ∩ Iso).card ≤ 1 := by
    intro p hp
    rw [Finset.mem_filter, Finset.mem_offDiag] at hp
    obtain ⟨⟨hp1, hp2, hp12⟩, _⟩ := hp
    by_cases hadj : G.Adj p.1 p.2
    · have hz : (G.neighborFinset p.1 ∩ G.neighborFinset p.2 ∩ Iso).card = 0 := by
        rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
        intro tt htt
        rw [Finset.mem_inter, Finset.mem_inter] at htt
        obtain ⟨⟨h1, h2⟩, h3⟩ := htt
        exact hcherry ⟨tt, h3, p.1, p.2,
          (G.mem_neighborFinset _ _).mpr ((G.mem_neighborFinset _ _).mp h1).symm,
          (G.mem_neighborFinset _ _).mpr ((G.mem_neighborFinset _ _).mp h2).symm, hp12, hadj⟩
      omega
    · exact hshare p.1 (hPoorsubHub hp1) (hdeg4 _ (hPoorsubHub hp1)) p.2 (hPoorsubHub hp2)
        (hdeg4 _ (hPoorsubHub hp2)) hp12 hadj
  have hCOcard : ((Poor.offDiag.filter (fun p => p.1 < p.2)).filter
      (fun p => 1 ≤ (G.neighborFinset p.1 ∩ G.neighborFinset p.2 ∩ Iso).card)).card = cP := by
    rw [Finset.card_filter, ← hcPeq]
    apply Finset.sum_congr rfl
    intro p hp
    have hle := hcodeg_le1 p hp
    by_cases h1 : 1 ≤ (G.neighborFinset p.1 ∩ G.neighborFinset p.2 ∩ Iso).card <;>
      simp only [h1, if_true, if_false] <;> omega
  -- `CO ⊆ NE` and `|CO| = |NE|`, hence `CO = NE`.
  have hCOsubNE : (Poor.offDiag.filter (fun p => p.1 < p.2)).filter
        (fun p => 1 ≤ (G.neighborFinset p.1 ∩ G.neighborFinset p.2 ∩ Iso).card)
      ⊆ (Poor.offDiag.filter (fun p => p.1 < p.2)).filter (fun p => ¬G.Adj p.1 p.2) := by
    intro p hp
    rw [Finset.mem_filter] at hp ⊢
    obtain ⟨hpltP, hcodeg⟩ := hp
    refine ⟨hpltP, fun hadj => ?_⟩
    rw [Finset.mem_filter, Finset.mem_offDiag] at hpltP
    obtain ⟨⟨_, _, hp12⟩, _⟩ := hpltP
    obtain ⟨tt, htt⟩ := Finset.card_pos.mp hcodeg
    rw [Finset.mem_inter, Finset.mem_inter] at htt
    obtain ⟨⟨h1, h2⟩, h3⟩ := htt
    exact hcherry ⟨tt, h3, p.1, p.2,
      (G.mem_neighborFinset _ _).mpr ((G.mem_neighborFinset _ _).mp h1).symm,
      (G.mem_neighborFinset _ _).mpr ((G.mem_neighborFinset _ _).mp h2).symm, hp12, hadj⟩
  have hCOeqNE : (Poor.offDiag.filter (fun p => p.1 < p.2)).filter
        (fun p => 1 ≤ (G.neighborFinset p.1 ∩ G.neighborFinset p.2 ∩ Iso).card)
      = (Poor.offDiag.filter (fun p => p.1 < p.2)).filter (fun p => ¬G.Adj p.1 p.2) :=
    Finset.eq_of_subset_of_card_le hCOsubNE (by rw [hCOcard]; omega)
  -- The non-edge `{hg₁, hg₂}` therefore co-occurs.
  have hfinal : ∀ x y, x ∈ Poor → y ∈ Poor → x < y → ¬G.Adj x y →
      1 ≤ (G.neighborFinset x ∩ G.neighborFinset y ∩ Iso).card := by
    intro x y hx hy hxy hnadjxy
    have hmem : (x, y) ∈ (Poor.offDiag.filter (fun p => p.1 < p.2)).filter
        (fun p => ¬G.Adj p.1 p.2) := by
      rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_offDiag]
      exact ⟨⟨⟨hx, hy, ne_of_lt hxy⟩, hxy⟩, hnadjxy⟩
    rw [← hCOeqNE, Finset.mem_filter] at hmem
    exact hmem.2
  rcases lt_or_gt_of_ne hg1g2 with hlt | hgt
  · exact hfinal hg1 hg2 hg1Poor hg2Poor hlt hnadj
  · have hsymm : G.neighborFinset hg2 ∩ G.neighborFinset hg1 ∩ Iso
        = G.neighborFinset hg1 ∩ G.neighborFinset hg2 ∩ Iso := by
      ext y; simp only [Finset.mem_inter]; tauto
    have := hfinal hg2 hg1 hg2Poor hg1Poor hgt (fun h => hnadj h.symm)
    rwa [hsymm] at this

end N18

end ACMax
