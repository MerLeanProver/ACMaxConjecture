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
import ACMaxConjecture.SmallCases.N18.ZPoorR6S3B

/-!
# Design B (`{3,3,2,2,2,2}`) subcase `s ≤ 3` for the `r = 6`, `S = 14` core (`n = 18`)

The `M`-partner `zp` meets two hubs `d₁, d₂` (`d₁, d₂ ≠ w₁, w₂` by `designB_w_structure_S14`).
Writing `s = isoDeg d₁ + isoDeg d₂` (each `dᵢ` is poor of iso-degree `1` or rich of iso-degree `2`),
this file rules out `s ≤ 3`, i.e. at least one of `d₁, d₂` is poor.

**The contradiction (verified TRUE, `0` survivors by direct search over all `1350` design-B twin
configurations).**  The `e(Hub, Hub) = 9` cut identities (`forced_hub_count_identities_S14`) pin the
within-`O` off-diagonal (`O = Hub \ {hg₁, hg₂, d₁, d₂}`) to `2s - 2`.  Since `w₁, w₂ ∈ O` are
mutually adjacent and otherwise hub-isolated they contribute `2`; the remaining
`O`-vertices then carry `2s - 4 ≤ 2` within-`O` incidences.  At `s ≤ 3` this leaves the four
iso-degree-`2` rich hubs almost edgeless inside `O`, forcing (via `designB_rich_cooccur_S14`) too
many rich pairs to co-occur on the only six twins — the rich-iso incidence sum `8` cannot cover the
`≥ 6` forced co-occurrences (each twin has at most two non-`w` hub-neighbours, so covers at most one
rich pair while the design demands a distinct covering twin per pair).  Poor hubs then receive no
twin, contradicting `hg₁`, `hg₂` having iso-degree `1`.
-/

namespace ACMax

open scoped Classical

namespace N18

/-- **Design B, subcase `s ≤ 3` is impossible.**  With the `r = 6`, `S = 14` design-`B` structure
(`w₁, w₂` the two iso-degree-`3` rich hubs), no-apex, no-twin-cherry, `¬Adj d₁ d₂`, `hcodeg0`, and
`isoDeg d₁ + isoDeg d₂ ≤ 3`, the configuration is contradictory.  The `e(Hub, Hub) = 9` cut
identities and the rich co-occurrence structure over-constrain the six twins. -/
theorem designB_s2s3_false_S14 (G : SimpleGraph (Fin 18)) (Hub Iso : Finset (Fin 18))
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
    (hcodeg0 : (G.neighborFinset hg1 ∩ G.neighborFinset hg2 ∩ Iso).card = 0)
    (hsum3 : (G.neighborFinset d1 ∩ Iso).card + (G.neighborFinset d2 ∩ Iso).card ≤ 3) :
    False := by
  classical
  -- The rigid design-`B` skeleton and the `e(Hub, Hub) = 9` cut identities.
  obtain ⟨hadjw, hw1hub1, hw2hub1, _hw1z0, _hw2z0, hpart, hd1w1, hd1w2, hd2w1, hd2w2⟩ :=
    designB_w_structure_S14 G Hub Iso hdisj hIso hdeg4 hshare hno2hub hcherry w1 w2 zp d1 d2
      hw1Hub hw2Hub hw1w2ne hw13 hw23 hzpZ hd1zp hd2zp
  obtain ⟨hcoA, hcoB⟩ :=
    designB_rich_cooccur_S14 G Hub Iso hdeg4 hshare hno2hub hcherry w1 w2 hw1Hub hw2Hub hadjw
      hw1hub1 hw2hub1 hw13 hw23
  obtain ⟨hd1g1, hd1g2, hd2g1, hd2g2, _ha_d1g1, _ha_d1g2, _ha_d2g1, _ha_d2g2, hCUT2, hCUT1⟩ :=
    forced_hub_count_identities_S14 G Hub Iso hiso3 hdisj hHub hIso hdsum hdeg3 hisodeg3 hleak
      hdeg4 z zp hg1 hg2 d1 d2 hzZ hzpZ hg1Hub hg2Hub hd1Hub hd2Hub hg1z hg2z hd1zp hd2zp
      hg1zp hg2zp hg1g2 hd1d2 hnadj hd1d2nadj hapex hg1iso1 hg2iso1
  set T : Finset (Fin 18) := ({hg1, hg2, d1, d2} : Finset (Fin 18)) with hTdef
  set O : Finset (Fin 18) := Hub \ T with hOdef
  -- `T ⊆ Hub` and the four `T`-vertices are pairwise distinct.
  have hTsubHub : T ⊆ Hub := by
    rw [hTdef]; intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  -- Each twin meets `Hub \ {w₁, w₂}` in exactly `2` vertices (it meets exactly one of `w₁, w₂`).
  have htwin2 : ∀ t ∈ Iso, (G.neighborFinset t ∩ (Hub \ {w1, w2})).card = 2 := by
    intro t ht
    have hsub : G.neighborFinset t ∩ (Hub \ {w1, w2})
        = (G.neighborFinset t ∩ Hub) \ {w1, w2} := by
      ext x; simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_singleton,
        Finset.mem_insert]; tauto
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
  -- `w₁, w₂ ∈ O` and the four `T`-vertices are excluded.
  have hw1hg1 : w1 ≠ hg1 := fun h => by rw [h] at hw13; omega
  have hw1hg2 : w1 ≠ hg2 := fun h => by rw [h] at hw13; omega
  have hw2hg1 : w2 ≠ hg1 := fun h => by rw [h] at hw23; omega
  have hw2hg2 : w2 ≠ hg2 := fun h => by rw [h] at hw23; omega
  have hw1O : w1 ∈ O := by
    rw [hOdef, Finset.mem_sdiff, hTdef]
    refine ⟨hw1Hub, ?_⟩
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hw1hg1, hw1hg2, Ne.symm hd1w1, Ne.symm hd2w1⟩
  have hw2O : w2 ∈ O := by
    rw [hOdef, Finset.mem_sdiff, hTdef]
    refine ⟨hw2Hub, ?_⟩
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hw2hg1, hw2hg2, Ne.symm hd1w2, Ne.symm hd2w2⟩
  -- Expansion of a sum over the four distinct `T`-vertices.
  have hTsum : ∀ f : Fin 18 → ℕ, ∑ v ∈ T, f v = f hg1 + f hg2 + f d1 + f d2 := by
    intro f
    rw [hTdef, show ({hg1, hg2, d1, d2} : Finset (Fin 18))
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
  -- `O.card = 6`, hence `Rich := O \ {w₁, w₂}` has card `4`.
  have hTcard : T.card = 4 := by
    rw [hTdef, show ({hg1, hg2, d1, d2} : Finset (Fin 18))
        = insert hg1 (insert hg2 (insert d1 {d2})) from rfl,
      Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hg1g2, Ne.symm hd1g1, Ne.symm hd2g1⟩),
      Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨Ne.symm hd1g2, Ne.symm hd2g2⟩),
      Finset.card_insert_of_notMem (by simp only [Finset.mem_singleton]; exact hd1d2),
      Finset.card_singleton]
  have hOcard : O.card = 6 := by
    rw [hOdef, Finset.card_sdiff, hHub, Finset.inter_eq_left.mpr hTsubHub, hTcard]
  set Rich : Finset (Fin 18) := O \ {w1, w2} with hRichdef
  have hw1w2subO : ({w1, w2} : Finset (Fin 18)) ⊆ O := by
    intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hw1O
    · exact hw2O
  have hRichcard : Rich.card = 4 := by
    rw [hRichdef, Finset.card_sdiff, hOcard, Finset.inter_eq_left.mpr hw1w2subO,
      Finset.card_pair hw1w2ne]
  have hRichsubHub : Rich ⊆ Hub := by
    rw [hRichdef]; intro x hx
    have hxO : x ∈ O := (Finset.mem_sdiff.mp hx).1
    rw [hOdef] at hxO; exact (Finset.mem_sdiff.mp hxO).1
  -- Membership facts: `Rich`-vertices differ from `w₁, w₂, hg₁, hg₂, d₁, d₂`.
  have hRichprop : ∀ r ∈ Rich, r ∈ Hub ∧ r ≠ w1 ∧ r ≠ w2 ∧ r ∉ T := by
    intro r hr
    have hrO : r ∈ O := (Finset.mem_sdiff.mp hr).1
    have hrnw : r ∉ ({w1, w2} : Finset (Fin 18)) := (Finset.mem_sdiff.mp hr).2
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hrnw
    rw [hOdef] at hrO
    exact ⟨(Finset.mem_sdiff.mp hrO).1, hrnw.1, hrnw.2, (Finset.mem_sdiff.mp hrO).2⟩
  -- `N(w₁) ∩ Hub = {w₂}`, `N(w₂) ∩ Hub = {w₁}`.
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
  -- The total hub-iso incidence sum is `18`; split it over `Rich ⊔ {w₁, w₂} ⊔ T`.
  have hHubIso : ∑ a ∈ Hub, (G.neighborFinset a ∩ Iso).card = 18 := by
    have h := hub_iso_sum_eighteen G Hub Iso hiso3; rw [hIso] at h; omega
  have hsplit1 := Finset.sum_sdiff (f := fun a => (G.neighborFinset a ∩ Iso).card) hTsubHub
  rw [← hOdef] at hsplit1
  have hsplit2 := Finset.sum_sdiff (f := fun a => (G.neighborFinset a ∩ Iso).card) hw1w2subO
  rw [← hRichdef] at hsplit2
  have hw12iso : ∑ a ∈ ({w1, w2} : Finset (Fin 18)), (G.neighborFinset a ∩ Iso).card = 6 := by
    rw [Finset.sum_pair hw1w2ne, hw13, hw23]
  have hTiso : ∑ a ∈ T, (G.neighborFinset a ∩ Iso).card
      = 2 + ((G.neighborFinset d1 ∩ Iso).card + (G.neighborFinset d2 ∩ Iso).card) := by
    rw [hTsum]; rw [hg1iso1, hg2iso1]; ring
  have hRichiso : ∑ a ∈ Rich, (G.neighborFinset a ∩ Iso).card
      = 10 - ((G.neighborFinset d1 ∩ Iso).card + (G.neighborFinset d2 ∩ Iso).card) := by
    rw [hHubIso, hTiso] at hsplit1
    rw [hw12iso] at hsplit2
    omega
  -- Each `Rich`-vertex has iso-degree `≤ 2` (it is a non-`w` hub).
  have hRichle : ∀ r ∈ Rich, (G.neighborFinset r ∩ Iso).card ≤ 2 := by
    intro r hr
    obtain ⟨hrHub, hrw1, hrw2, _⟩ := hRichprop r hr
    rcases Nat.lt_or_ge (G.neighborFinset r ∩ Iso).card 2 with h | h
    · omega
    · exact le_of_eq (hother2 r hrHub hrw1 hrw2 h)
  -- Twin bound: every twin meets `≤ 2` of `Rich`.
  have hRichbound : ∀ t ∈ Iso, (G.neighborFinset t ∩ Rich).card ≤ 2 := by
    intro t ht
    refine le_trans (Finset.card_le_card ?_) (le_of_eq (htwin2 t ht))
    intro x hx
    obtain ⟨hxt, hxR⟩ := Finset.mem_inter.mp hx
    obtain ⟨hxHub, hxw1, hxw2, _⟩ := hRichprop x hxR
    exact Finset.mem_inter.mpr ⟨hxt, Finset.mem_sdiff.mpr ⟨hxHub, by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hxw1, hxw2⟩⟩⟩
  -- The within-`O` edge sum `∑_O |N ∩ O| = 2s - 2`, and it is `≥ 2`.
  have hOedge : ∑ v ∈ O, (G.neighborFinset v ∩ O).card + 2
      = 2 * ((G.neighborFinset d1 ∩ Iso).card + (G.neighborFinset d2 ∩ Iso).card) := hCUT2
  have hNw1O : (G.neighborFinset w1 ∩ O).card = 1 := by
    have hsub : G.neighborFinset w1 ∩ O = {w2} := by
      rw [Finset.eq_singleton_iff_unique_mem]
      refine ⟨Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hadjw, hw2O⟩, fun x hx => ?_⟩
      obtain ⟨hxN, hxO⟩ := Finset.mem_inter.mp hx
      have hxHub : x ∈ Hub := by rw [hOdef] at hxO; exact (Finset.mem_sdiff.mp hxO).1
      have : x ∈ G.neighborFinset w1 ∩ Hub := Finset.mem_inter.mpr ⟨hxN, hxHub⟩
      rw [hw1set, Finset.mem_singleton] at this; exact this
    rw [hsub, Finset.card_singleton]
  have hNw2O : (G.neighborFinset w2 ∩ O).card = 1 := by
    have hsub : G.neighborFinset w2 ∩ O = {w1} := by
      rw [Finset.eq_singleton_iff_unique_mem]
      refine ⟨Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hadjw.symm, hw1O⟩, fun x hx => ?_⟩
      obtain ⟨hxN, hxO⟩ := Finset.mem_inter.mp hx
      have hxHub : x ∈ Hub := by rw [hOdef] at hxO; exact (Finset.mem_sdiff.mp hxO).1
      have : x ∈ G.neighborFinset w2 ∩ Hub := Finset.mem_inter.mpr ⟨hxN, hxHub⟩
      rw [hw2set, Finset.mem_singleton] at this; exact this
    rw [hsub, Finset.card_singleton]
  -- `s = isoDeg d₁ + isoDeg d₂ ≥ 2`, hence `s ∈ {2, 3}`.
  have hsge : 2 ≤ (G.neighborFinset d1 ∩ Iso).card + (G.neighborFinset d2 ∩ Iso).card := by
    have hpairsub : ({w1, w2} : Finset (Fin 18)) ⊆ O := hw1w2subO
    have hpsum : ∑ v ∈ ({w1, w2} : Finset (Fin 18)), (G.neighborFinset v ∩ O).card
        ≤ ∑ v ∈ O, (G.neighborFinset v ∩ O).card :=
      Finset.sum_le_sum_of_subset hpairsub
    rw [Finset.sum_pair hw1w2ne, hNw1O, hNw2O] at hpsum
    omega
  have hscases : (G.neighborFinset d1 ∩ Iso).card + (G.neighborFinset d2 ∩ Iso).card = 2 ∨
      (G.neighborFinset d1 ∩ Iso).card + (G.neighborFinset d2 ∩ Iso).card = 3 := by omega
  rcases hscases with hs2 | hs3
  · -- **Subcase `s = 2`.**  `Rich = O \ {w₁, w₂}` is the four iso-degree-`2` hubs, and the within-`O`
    -- edge sum forces `Rich` internally edgeless, contradicting `designB_rich4_edges_ge_two_S14`.
    have hsum8 : ∑ a ∈ Rich, (G.neighborFinset a ∩ Iso).card = 8 := by rw [hRichiso, hs2]
    have hRich2 : ∀ r ∈ Rich, (G.neighborFinset r ∩ Iso).card = 2 := by
      have hconst : ∑ _r ∈ Rich, 2 = 8 := by simp [Finset.sum_const, hRichcard]
      have hkey : ∑ r ∈ Rich, (2 - (G.neighborFinset r ∩ Iso).card) = 0 := by
        have h1 : ∑ r ∈ Rich, ((2 - (G.neighborFinset r ∩ Iso).card)
            + (G.neighborFinset r ∩ Iso).card) = ∑ _r ∈ Rich, 2 :=
          Finset.sum_congr rfl (fun r hr => by have := hRichle r hr; omega)
        rw [Finset.sum_add_distrib, hsum8, hconst] at h1
        omega
      intro r hr
      have h0 := (Finset.sum_eq_zero_iff).mp hkey r hr
      have := hRichle r hr; omega
    -- The codegree sum `∑_t C(k, 2) ≤ 4` (each twin meets `≤ 2` of `Rich`, total `8`).
    have htwo : ∀ k : ℕ, k ≤ 2 → 2 * k.choose 2 ≤ k := fun k hk => by interval_cases k <;> decide
    have htotal : ∑ t ∈ Iso, (G.neighborFinset t ∩ Rich).card = 8 := by
      rw [cross_count G Iso Rich]
      calc ∑ x ∈ Rich, (G.neighborFinset x ∩ Iso).card
          = ∑ _x ∈ Rich, 2 := Finset.sum_congr rfl (fun r hr => hRich2 r hr)
        _ = 8 := by rw [Finset.sum_const, hRichcard]; rfl
    have hRHSle : ∑ t ∈ Iso, ((G.neighborFinset t ∩ Rich).card).choose 2 ≤ 4 := by
      have hb : 2 * ∑ t ∈ Iso, ((G.neighborFinset t ∩ Rich).card).choose 2
          ≤ ∑ t ∈ Iso, (G.neighborFinset t ∩ Rich).card := by
        rw [Finset.mul_sum]; exact Finset.sum_le_sum (fun t ht => htwo _ (hRichbound t ht))
      rw [htotal] at hb; omega
    -- The engine equation forces `≥ 2` ordered `Rich`-edges, hence `∑_Rich |N ∩ Rich| ≥ 4`.
    have heq := designB_rich4_edge_eq_S14 G Hub Iso Rich hdeg4 hshare hno2hub hcherry
      hRichsubHub hRichcard hRich2
    have hge2 : 2 ≤ (Rich.offDiag.filter (fun p => p.1 < p.2 ∧ G.Adj p.1 p.2)).card := by omega
    have hwithin : 4 ≤ ∑ v ∈ Rich, (G.neighborFinset v ∩ Rich).card := by
      rw [within_sum_eq_two_mul_S14]; omega
    -- The cut: `∑_Rich |N ∩ Rich| = 0`, contradiction.
    have hOedge2 : ∑ v ∈ O, (G.neighborFinset v ∩ O).card = 2 := by rw [hs2] at hOedge; omega
    have hsplitO := Finset.sum_sdiff (f := fun v => (G.neighborFinset v ∩ O).card) hw1w2subO
    rw [← hRichdef] at hsplitO
    have hwO : ∑ v ∈ ({w1, w2} : Finset (Fin 18)), (G.neighborFinset v ∩ O).card = 2 := by
      rw [Finset.sum_pair hw1w2ne, hNw1O, hNw2O]
    have hRichO0 : ∑ v ∈ Rich, (G.neighborFinset v ∩ O).card = 0 := by
      rw [hwO, hOedge2] at hsplitO; omega
    have hRichmono : ∑ v ∈ Rich, (G.neighborFinset v ∩ Rich).card
        ≤ ∑ v ∈ Rich, (G.neighborFinset v ∩ O).card :=
      Finset.sum_le_sum (fun r _ => Finset.card_le_card
        (Finset.inter_subset_inter_left (by rw [hRichdef]; exact Finset.sdiff_subset)))
    omega
  · -- **Subcase `s = 3`.**  Dispatched to `designB_s3_false_S14` (the structural `p`/cherry kernel).
    exact designB_s3_false_S14 G Hub Iso hiso3 hdisj hHub hIso hdsum hdeg3 hisodeg3 hleak hdeg4
      hshare hno2hub hcherry w1 w2 z zp hg1 hg2 d1 d2 hw1Hub hw2Hub hw1w2ne hw13 hw23 hother2 hzZ
      hzpZ hg1Hub hg2Hub hd1Hub hd2Hub hg1z hg2z hd1zp hd2zp hg1zp hg2zp hg1g2 hd1d2 hnadj
      hd1d2nadj hapex hg1iso1 hg2iso1 hcodeg0 hs3

end N18

end ACMax
