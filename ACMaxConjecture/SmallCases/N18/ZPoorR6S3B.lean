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
# Design B (`{3,3,2,2,2,2}`) subcase `s = 3` for the `r = 6`, `S = 14` core (`n = 18`)

Rules out `s = isoDeg d₁ + isoDeg d₂ = 3`: exactly one of `d₁, d₂` is an iso-degree-`2` rich hub
`d_rich`, the other an iso-degree-`1` poor hub `d_poor`.  `Rich = O \ {w₁, w₂}` has iso-degree sum
`7`, so it is three iso-degree-`2` hubs `R₃` plus one iso-degree-`1` hub `p`; the four global
iso-degree-`2` hubs are `Rich4 = R₃ ∪ {d_rich}`.  Counting forces `p` non-adjacent to every rich hub,
hence (hub-degree `3`, `Z`-degree `0`) adjacent to all three poor hubs; its unique twin then meets
exactly one of `Rich4`, contradicting the parity `∑ C(k, 2) = 4` (which forces every twin to meet
`0` or `2` of `Rich4`).
-/

namespace ACMax

open scoped Classical

namespace N18

set_option maxHeartbeats 1600000 in
/-- **Design B, subcase `s = 3` is impossible.** -/
theorem designB_s3_false_S14 (G : SimpleGraph (Fin 18)) (Hub Iso : Finset (Fin 18))
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
    (hs3 : (G.neighborFinset d1 ∩ Iso).card + (G.neighborFinset d2 ∩ Iso).card = 3) :
    False := by
  classical
  -- ===== Common design-B setup (mirrors the `s = 2` branch) =====
  obtain ⟨hadjw, hw1hub1, hw2hub1, _hw1z0, _hw2z0, hpart, hd1w1, hd1w2, hd2w1, hd2w2⟩ :=
    designB_w_structure_S14 G Hub Iso hdisj hIso hdeg4 hshare hno2hub hcherry w1 w2 zp d1 d2
      hw1Hub hw2Hub hw1w2ne hw13 hw23 hzpZ hd1zp hd2zp
  obtain ⟨hd1g1, hd1g2, hd2g1, hd2g2, _ha_d1g1, _ha_d1g2, _ha_d2g1, _ha_d2g2, hCUT2, _hCUT1⟩ :=
    forced_hub_count_identities_S14 G Hub Iso hiso3 hdisj hHub hIso hdsum hdeg3 hisodeg3 hleak
      hdeg4 z zp hg1 hg2 d1 d2 hzZ hzpZ hg1Hub hg2Hub hd1Hub hd2Hub hg1z hg2z hd1zp hd2zp
      hg1zp hg2zp hg1g2 hd1d2 hnadj hd1d2nadj hapex hg1iso1 hg2iso1
  set T : Finset (Fin 18) := ({hg1, hg2, d1, d2} : Finset (Fin 18)) with hTdef
  set O : Finset (Fin 18) := Hub \ T with hOdef
  have hTsubHub : T ⊆ Hub := by
    rw [hTdef]; intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  have htwin2 : ∀ t ∈ Iso, (G.neighborFinset t ∩ (Hub \ {w1, w2})).card = 2 := by
    intro t ht
    have hsub : G.neighborFinset t ∩ (Hub \ {w1, w2})
        = (G.neighborFinset t ∩ Hub) \ {w1, w2} := by
      exact (Finset.inter_sdiff_assoc _ _ _).symm
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
  have hRichprop : ∀ r ∈ Rich, r ∈ Hub ∧ r ≠ w1 ∧ r ≠ w2 ∧ r ∉ T := by
    intro r hr
    have hrO : r ∈ O := (Finset.mem_sdiff.mp hr).1
    have hrnw : r ∉ ({w1, w2} : Finset (Fin 18)) := (Finset.mem_sdiff.mp hr).2
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hrnw
    rw [hOdef] at hrO
    exact ⟨(Finset.mem_sdiff.mp hrO).1, hrnw.1, hrnw.2, (Finset.mem_sdiff.mp hrO).2⟩
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
  have hRichle : ∀ r ∈ Rich, (G.neighborFinset r ∩ Iso).card ≤ 2 := by
    intro r hr
    obtain ⟨hrHub, hrw1, hrw2, _⟩ := hRichprop r hr
    rcases Nat.lt_or_ge (G.neighborFinset r ∩ Iso).card 2 with h | h
    · omega
    · exact le_of_eq (hother2 r hrHub hrw1 hrw2 h)
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
  -- `Rich`-vertices are non-adjacent to `w₁, w₂`.
  have hRnadjw : ∀ r ∈ Rich, ¬G.Adj r w1 ∧ ¬G.Adj r w2 := by
    intro r hr
    obtain ⟨hrHub, hrw1, hrw2, _⟩ := hRichprop r hr
    refine ⟨fun hadj => ?_, fun hadj => ?_⟩
    · have : r ∈ G.neighborFinset w1 ∩ Hub :=
        Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hadj.symm, hrHub⟩
      rw [hw1set, Finset.mem_singleton] at this; exact hrw2 this
    · have : r ∈ G.neighborFinset w2 ∩ Hub :=
        Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hadj.symm, hrHub⟩
      rw [hw2set, Finset.mem_singleton] at this; exact hrw1 this
  -- ===== Subcase `s = 3` =====
  -- (A) `∑_Rich isoDeg = 7`, within-`O` cut gives `∑_Rich |N ∩ Rich| = 2`.
  have hRichiso7 : ∑ a ∈ Rich, (G.neighborFinset a ∩ Iso).card = 7 := by rw [hRichiso]; omega
  have hOedge4 : ∑ v ∈ O, (G.neighborFinset v ∩ O).card = 4 := by
    have := hOedge; omega
  have hsplitO := Finset.sum_sdiff (f := fun v => (G.neighborFinset v ∩ O).card) hw1w2subO
  rw [← hRichdef] at hsplitO
  have hwO : ∑ v ∈ ({w1, w2} : Finset (Fin 18)), (G.neighborFinset v ∩ O).card = 2 := by
    rw [Finset.sum_pair hw1w2ne, hNw1O, hNw2O]
  have hRichO2 : ∑ v ∈ Rich, (G.neighborFinset v ∩ O).card = 2 := by
    rw [hwO, hOedge4] at hsplitO; omega
  have hNrO_eq : ∀ r ∈ Rich, G.neighborFinset r ∩ O = G.neighborFinset r ∩ Rich := by
    intro r hr
    obtain ⟨hr1, hr2⟩ := hRnadjw r hr
    ext x
    simp only [Finset.mem_inter, hRichdef, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hxN, hxO⟩
      refine ⟨hxN, hxO, ?_⟩
      rintro (rfl | rfl)
      · exact hr1 ((G.mem_neighborFinset _ _).mp hxN)
      · exact hr2 ((G.mem_neighborFinset _ _).mp hxN)
    · rintro ⟨hxN, hxO, _⟩; exact ⟨hxN, hxO⟩
  have hRichRich2 : ∑ v ∈ Rich, (G.neighborFinset v ∩ Rich).card = 2 := by
    have heq : ∑ v ∈ Rich, (G.neighborFinset v ∩ Rich).card
        = ∑ v ∈ Rich, (G.neighborFinset v ∩ O).card :=
      Finset.sum_congr rfl (fun r hr => by rw [hNrO_eq r hr])
    rw [heq, hRichO2]
  -- (B) Identify the iso-degree-`1` hub `p` and `R₃ = Rich \ {p}` (three iso-degree-`2` hubs).
  have hsumsplit : ∑ r ∈ Rich, (2 - (G.neighborFinset r ∩ Iso).card) = 1 := by
    have h1 : ∑ r ∈ Rich, ((2 - (G.neighborFinset r ∩ Iso).card) + (G.neighborFinset r ∩ Iso).card)
        = ∑ r ∈ Rich, 2 := Finset.sum_congr rfl (fun r hr => by have := hRichle r hr; omega)
    rw [Finset.sum_add_distrib, hRichiso7] at h1
    have h2 : ∑ _r ∈ Rich, 2 = 8 := by rw [Finset.sum_const, hRichcard]; rfl
    omega
  obtain ⟨p, hpRich, hpne⟩ :=
    Finset.exists_ne_zero_of_sum_ne_zero (s := Rich)
      (f := fun r => 2 - (G.neighborFinset r ∩ Iso).card) (by rw [hsumsplit]; exact one_ne_zero)
  have hpterm : 2 - (G.neighborFinset p ∩ Iso).card = 1 := by
    have hle := Finset.single_le_sum
      (f := fun r => 2 - (G.neighborFinset r ∩ Iso).card) (fun i _ => Nat.zero_le _) hpRich
    rw [hsumsplit] at hle; omega
  have hp_iso1 : (G.neighborFinset p ∩ Iso).card = 1 := by have := hRichle p hpRich; omega
  have hR3_iso2 : ∀ r ∈ Rich, r ≠ p → (G.neighborFinset r ∩ Iso).card = 2 := by
    intro r hr hrp
    have hsub : ({p} : Finset (Fin 18)) ⊆ Rich := Finset.singleton_subset_iff.mpr hpRich
    have hh := Finset.sum_sdiff (f := fun x => 2 - (G.neighborFinset x ∩ Iso).card) hsub
    rw [Finset.sum_singleton, hpterm, hsumsplit] at hh
    have hrmem : r ∈ Rich \ {p} := Finset.mem_sdiff.mpr ⟨hr, Finset.notMem_singleton.mpr hrp⟩
    have hz := (Finset.sum_eq_zero_iff).mp (by omega : ∑ x ∈ Rich \ {p},
        (2 - (G.neighborFinset x ∩ Iso).card) = 0) r hrmem
    have := hRichle r hr; omega
  set R3 : Finset (Fin 18) := Rich.erase p with hR3def
  have hpR3 : p ∉ R3 := Finset.notMem_erase p Rich
  have hRichins : insert p R3 = Rich := by rw [hR3def]; exact Finset.insert_erase hpRich
  have hR3sub : R3 ⊆ Rich := by rw [hR3def]; exact Finset.erase_subset p Rich
  have hR3subHub : R3 ⊆ Hub := fun x hx => hRichsubHub (hR3sub hx)
  have hR3card : R3.card = 3 := by rw [hR3def, Finset.card_erase_of_mem hpRich, hRichcard]
  have hpHub : p ∈ Hub := hRichsubHub hpRich
  have hpO : p ∈ O := by
    have := hRichdef ▸ hpRich; exact (Finset.mem_sdiff.mp this).1
  -- (C) Identify `d_rich` (iso `2`) and `d_poor` (iso `1`) among `d₁, d₂`.
  have hd1le2 : (G.neighborFinset d1 ∩ Iso).card ≤ 2 := by
    rcases Nat.lt_or_ge (G.neighborFinset d1 ∩ Iso).card 2 with h | h
    · omega
    · exact le_of_eq (hother2 d1 hd1Hub hd1w1 hd1w2 h)
  have hd2le2 : (G.neighborFinset d2 ∩ Iso).card ≤ 2 := by
    rcases Nat.lt_or_ge (G.neighborFinset d2 ∩ Iso).card 2 with h | h
    · omega
    · exact le_of_eq (hother2 d2 hd2Hub hd2w1 hd2w2 h)
  obtain ⟨dr, dp, hdrHub, hdpHub, hdr_zp, hdp_zp, hdr_iso2, hdp_iso1, hdr_w1, hdr_w2,
      hdp_w1, hdp_w2, hdr_g1ne, hdr_g2ne, hdp_g1ne, hdp_g2ne, hTeq⟩ :
      ∃ dr dp, dr ∈ Hub ∧ dp ∈ Hub ∧ G.Adj dr zp ∧ G.Adj dp zp ∧
        (G.neighborFinset dr ∩ Iso).card = 2 ∧ (G.neighborFinset dp ∩ Iso).card = 1 ∧
        dr ≠ w1 ∧ dr ≠ w2 ∧ dp ≠ w1 ∧ dp ≠ w2 ∧
        dr ≠ hg1 ∧ dr ≠ hg2 ∧ dp ≠ hg1 ∧ dp ≠ hg2 ∧
        T = ({hg1, hg2, dr, dp} : Finset (Fin 18)) := by
    rcases (show (G.neighborFinset d1 ∩ Iso).card = 2 ∧ (G.neighborFinset d2 ∩ Iso).card = 1
        ∨ (G.neighborFinset d1 ∩ Iso).card = 1 ∧ (G.neighborFinset d2 ∩ Iso).card = 2 from by omega)
      with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact ⟨d1, d2, hd1Hub, hd2Hub, hd1zp, hd2zp, ha, hb, hd1w1, hd1w2, hd2w1, hd2w2,
        hd1g1, hd1g2, hd2g1, hd2g2, hTdef⟩
    · refine ⟨d2, d1, hd2Hub, hd1Hub, hd2zp, hd1zp, hb, ha, hd2w1, hd2w2, hd1w1, hd1w2,
        hd2g1, hd2g2, hd1g1, hd1g2, ?_⟩
      rw [hTdef, show ({hg1, hg2, d1, d2} : Finset (Fin 18))
          = insert hg1 (insert hg2 {d1, d2}) from rfl, Finset.pair_comm d1 d2]
  have hdrT : dr ∈ T := by
    rw [hTeq]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  have hdr_notRich : dr ∉ Rich := by
    intro hh
    have hdrO : dr ∈ O := (Finset.mem_sdiff.mp (hRichdef ▸ hh)).1
    rw [hOdef] at hdrO; exact (Finset.mem_sdiff.mp hdrO).2 hdrT
  have hdrR3 : dr ∉ R3 := fun h => hdr_notRich (hR3sub h)
  have hp_ne_dr : p ≠ dr := fun h => hdr_notRich (h ▸ hpRich)
  set Rich4 : Finset (Fin 18) := insert dr R3 with hRich4def
  have hRich4card : Rich4.card = 4 := by
    rw [hRich4def, Finset.card_insert_of_notMem hdrR3, hR3card]
  have hRich4sub : Rich4 ⊆ Hub := by
    rw [hRich4def]; intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hxR3
    · exact hdrHub
    · exact hR3subHub hxR3
  have hRich4iso2 : ∀ r ∈ Rich4, (G.neighborFinset r ∩ Iso).card = 2 := by
    intro r hr
    rcases Finset.mem_insert.mp (hRich4def ▸ hr) with rfl | hxR3
    · exact hdr_iso2
    · have hrRich := hR3sub hxR3
      exact hR3_iso2 r hrRich (by
        intro h; exact hpR3 (h ▸ hxR3))
  -- (D) Counting: `∑_Rich4 |N ∩ Rich4|`, `∑_Rich |N ∩ Rich|`, and bridges to the edge equation.
  have hR3within := within_sum_eq_two_mul_S14 G R3
  -- Bridge: for `r`, `|N(r) ∩ insert a R3| = |N(r) ∩ R3| + |N(r) ∩ {a}|` when `a ∉ R3`.
  have hdecomp : ∀ (a : Fin 18), a ∉ R3 → ∀ r,
      (G.neighborFinset r ∩ insert a R3).card
        = (G.neighborFinset r ∩ R3).card + (G.neighborFinset r ∩ {a}).card := by
    intro a ha r
    rw [show insert a R3 = R3 ∪ {a} from by rw [Finset.insert_eq, Finset.union_comm],
      Finset.inter_union_distrib_left, Finset.card_union_of_disjoint]
    apply Finset.disjoint_left.mpr
    intro x hx1 hx2
    simp only [Finset.mem_inter, Finset.mem_singleton] at hx1 hx2
    exact ha (hx2.2 ▸ hx1.2)
  have hself : ∀ (a : Fin 18), G.neighborFinset a ∩ insert a R3 = G.neighborFinset a ∩ R3 := by
    intro a; ext x
    simp only [Finset.mem_inter, Finset.mem_insert]
    constructor
    · rintro ⟨hx, rfl | hxR3⟩
      · exact absurd ((G.mem_neighborFinset _ _).mp hx) (G.irrefl)
      · exact ⟨hx, hxR3⟩
    · rintro ⟨hx, hxR3⟩; exact ⟨hx, Or.inr hxR3⟩
  -- Rich-side equation: `2 = 2·sR3 + 2·aR3p`, where `aR3p = |N(p) ∩ R3|`.
  have key1 : ∑ v ∈ Rich, (G.neighborFinset v ∩ Rich).card
      = (G.neighborFinset p ∩ Rich).card + ∑ v ∈ R3, (G.neighborFinset v ∩ Rich).card := by
    rw [← hRichins, Finset.sum_insert hpR3]
  have hNpRichCard : (G.neighborFinset p ∩ Rich).card = (G.neighborFinset p ∩ R3).card := by
    rw [← hRichins, hself]
  have hcrossp : ∑ r ∈ R3, (G.neighborFinset r ∩ {p}).card = (G.neighborFinset p ∩ R3).card := by
    rw [cross_count G R3 {p}, Finset.sum_singleton]
  have hsumR3Rich : ∑ r ∈ R3, (G.neighborFinset r ∩ Rich).card
      = (∑ r ∈ R3, (G.neighborFinset r ∩ R3).card) + (G.neighborFinset p ∩ R3).card := by
    have hbody : ∀ r ∈ R3, (G.neighborFinset r ∩ Rich).card
        = (G.neighborFinset r ∩ R3).card + (G.neighborFinset r ∩ {p}).card := by
      intro r _; rw [← hRichins, hdecomp p hpR3 r]
    rw [Finset.sum_congr rfl hbody, Finset.sum_add_distrib, hcrossp]
  -- Rich4-side equation: `Rich4Sum = 2·sR3 + 2·aDr`, where `aDr = |N(dr) ∩ R3|`.
  have hRich4within := within_sum_eq_two_mul_S14 G Rich4
  have key4 : ∑ v ∈ Rich4, (G.neighborFinset v ∩ Rich4).card
      = (G.neighborFinset dr ∩ Rich4).card + ∑ v ∈ R3, (G.neighborFinset v ∩ Rich4).card := by
    rw [hRich4def, Finset.sum_insert hdrR3]
  have hNdrRich4Card : (G.neighborFinset dr ∩ Rich4).card = (G.neighborFinset dr ∩ R3).card := by
    rw [hRich4def, hself]
  have hcrossdr : ∑ r ∈ R3, (G.neighborFinset r ∩ {dr}).card = (G.neighborFinset dr ∩ R3).card := by
    rw [cross_count G R3 {dr}, Finset.sum_singleton]
  have hsumR3Rich4 : ∑ r ∈ R3, (G.neighborFinset r ∩ Rich4).card
      = (∑ r ∈ R3, (G.neighborFinset r ∩ R3).card) + (G.neighborFinset dr ∩ R3).card := by
    have hbody : ∀ r ∈ R3, (G.neighborFinset r ∩ Rich4).card
        = (G.neighborFinset r ∩ R3).card + (G.neighborFinset r ∩ {dr}).card := by
      intro r _; rw [hRich4def, hdecomp dr hdrR3 r]
    rw [Finset.sum_congr rfl hbody, Finset.sum_add_distrib, hcrossdr]
  -- `aDr ≤ 1` (`hubDeg dr ≤ 1`).
  have hsp_dr := nbr_split_three_eighteen G Hub Iso hdisj dr
  have hzdr1 : 1 ≤ (G.neighborFinset dr ∩ (Finset.univ \ (Hub ∪ Iso))).card :=
    Finset.card_pos.mpr ⟨zp, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hdr_zp, hzpZ⟩⟩
  have hdrHubDeg_le : (G.neighborFinset dr ∩ Hub).card ≤ 1 := by
    rw [hdeg4 dr hdrHub, hdr_iso2] at hsp_dr; omega
  have haDr_le : (G.neighborFinset dr ∩ R3).card ≤ 1 :=
    le_trans (Finset.card_le_card (Finset.inter_subset_inter_left hR3subHub)) hdrHubDeg_le
  -- (E) Edge equation + codegree bound force `aR3p = 0`, `∑ C(k,2) = 4`, `aDr = 1`.
  have hRich4bound : ∀ t ∈ Iso, (G.neighborFinset t ∩ Rich4).card ≤ 2 := by
    intro t ht
    refine le_trans (Finset.card_le_card ?_) (le_of_eq (htwin2 t ht))
    intro x hx
    obtain ⟨hxt, hxR4⟩ := Finset.mem_inter.mp hx
    rcases Finset.mem_insert.mp (hRich4def ▸ hxR4) with rfl | hxR3
    · exact Finset.mem_inter.mpr ⟨hxt, Finset.mem_sdiff.mpr ⟨hdrHub, by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hdr_w1, hdr_w2⟩⟩⟩
    · have hxRich := hR3sub hxR3
      obtain ⟨hxHub, hxw1, hxw2, _⟩ := hRichprop x hxRich
      exact Finset.mem_inter.mpr ⟨hxt, Finset.mem_sdiff.mpr ⟨hxHub, by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hxw1, hxw2⟩⟩⟩
  have htotal : ∑ t ∈ Iso, (G.neighborFinset t ∩ Rich4).card = 8 := by
    rw [cross_count G Iso Rich4]
    calc ∑ r ∈ Rich4, (G.neighborFinset r ∩ Iso).card
        = ∑ _r ∈ Rich4, 2 := Finset.sum_congr rfl (fun r hr => hRich4iso2 r hr)
      _ = 8 := by rw [Finset.sum_const, hRich4card]; rfl
  have htwo : ∀ k : ℕ, k ≤ 2 → 2 * k.choose 2 ≤ k := fun k hk => by interval_cases k <;> decide
  have hSCle : ∑ t ∈ Iso, ((G.neighborFinset t ∩ Rich4).card).choose 2 ≤ 4 := by
    have hb : 2 * ∑ t ∈ Iso, ((G.neighborFinset t ∩ Rich4).card).choose 2
        ≤ ∑ t ∈ Iso, (G.neighborFinset t ∩ Rich4).card := by
      rw [Finset.mul_sum]; exact Finset.sum_le_sum (fun t ht => htwo _ (hRich4bound t ht))
    rw [htotal] at hb; omega
  have hedgeeq := designB_rich4_edge_eq_S14 G Hub Iso Rich4 hdeg4 hshare hno2hub hcherry
    hRich4sub hRich4card hRich4iso2
  have haR3p0 : (G.neighborFinset p ∩ R3).card = 0 := by
    omega
  have hSC4 : ∑ t ∈ Iso, ((G.neighborFinset t ∩ Rich4).card).choose 2 = 4 := by
    omega
  have haDr1 : (G.neighborFinset dr ∩ R3).card = 1 := by
    omega
  -- (F) `p ⁄~` every rich hub.
  have hpR3nadj : ∀ r ∈ R3, ¬G.Adj p r := by
    intro r hr hadj
    have : r ∈ G.neighborFinset p ∩ R3 :=
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hadj, hr⟩
    rw [Finset.card_eq_zero.mp haR3p0] at this; exact absurd this (Finset.notMem_empty r)
  have hNdrHub_eq : G.neighborFinset dr ∩ R3 = G.neighborFinset dr ∩ Hub :=
    Finset.eq_of_subset_of_card_le (Finset.inter_subset_inter_left hR3subHub) (by
      rw [haDr1]; exact hdrHubDeg_le)
  have hp_ndr : ¬G.Adj p dr := by
    intro hadj
    have hpmem : p ∈ G.neighborFinset dr ∩ Hub :=
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hadj.symm, hpHub⟩
    rw [← hNdrHub_eq] at hpmem; exact hpR3 (Finset.mem_inter.mp hpmem).2
  have hp_nw : ¬G.Adj p w1 ∧ ¬G.Adj p w2 := hRnadjw p hpRich
  -- (G) `p` has hub-degree `3` and `Z`-degree `0`, hence is adjacent to `hg₁, hg₂, d_poor`.
  have hzsum4 := zdeg_sum_four_eighteen G Hub Iso hiso3 hdisj hHub hIso hdsum hdeg3 hisodeg3 hleak
  have hZT := hTsum (fun v => (G.neighborFinset v ∩ (Finset.univ \ (Hub ∪ Iso))).card)
  have hzg1 : 1 ≤ (G.neighborFinset hg1 ∩ (Finset.univ \ (Hub ∪ Iso))).card :=
    Finset.card_pos.mpr ⟨z, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hg1z, hzZ⟩⟩
  have hzg2 : 1 ≤ (G.neighborFinset hg2 ∩ (Finset.univ \ (Hub ∪ Iso))).card :=
    Finset.card_pos.mpr ⟨z, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hg2z, hzZ⟩⟩
  have hzd1 : 1 ≤ (G.neighborFinset d1 ∩ (Finset.univ \ (Hub ∪ Iso))).card :=
    Finset.card_pos.mpr ⟨zp, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hd1zp, hzpZ⟩⟩
  have hzd2 : 1 ≤ (G.neighborFinset d2 ∩ (Finset.univ \ (Hub ∪ Iso))).card :=
    Finset.card_pos.mpr ⟨zp, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hd2zp, hzpZ⟩⟩
  have hZsdiff := Finset.sum_sdiff
    (f := fun h => (G.neighborFinset h ∩ (Finset.univ \ (Hub ∪ Iso))).card) hTsubHub
  rw [← hOdef, hzsum4] at hZsdiff
  have hOZ0 : ∑ v ∈ O, (G.neighborFinset v ∩ (Finset.univ \ (Hub ∪ Iso))).card = 0 := by
    rw [hZT] at hZsdiff; omega
  have hzp0 : (G.neighborFinset p ∩ (Finset.univ \ (Hub ∪ Iso))).card = 0 := by
    have hle := Finset.single_le_sum
      (f := fun v => (G.neighborFinset v ∩ (Finset.univ \ (Hub ∪ Iso))).card)
      (fun i _ => Nat.zero_le _) hpO
    rw [hOZ0] at hle; omega
  have hsp_p := nbr_split_three_eighteen G Hub Iso hdisj p
  have hpHubDeg3 : (G.neighborFinset p ∩ Hub).card = 3 := by
    rw [hdeg4 p hpHub, hp_iso1, hzp0] at hsp_p; omega
  -- `N(p) ∩ Hub ⊆ {hg₁, hg₂, d_poor}`.
  have hpsub : G.neighborFinset p ∩ Hub ⊆ ({hg1, hg2, dp} : Finset (Fin 18)) := by
    intro x hx
    obtain ⟨hxN, hxHub⟩ := Finset.mem_inter.mp hx
    have hadjpx : G.Adj p x := (G.mem_neighborFinset _ _).mp hxN
    simp only [Finset.mem_insert, Finset.mem_singleton]
    have hxHubTO : x ∈ T ∨ x ∈ O := by
      by_cases hxT : x ∈ T
      · exact Or.inl hxT
      · exact Or.inr (by rw [hOdef]; exact Finset.mem_sdiff.mpr ⟨hxHub, hxT⟩)
    rcases hxHubTO with hxT | hxO
    · rw [hTeq] at hxT
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxT
      rcases hxT with rfl | rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact absurd hadjpx hp_ndr
      · exact Or.inr (Or.inr rfl)
    · by_cases hxw1 : x = w1
      · exact absurd (hxw1 ▸ hadjpx) hp_nw.1
      · by_cases hxw2 : x = w2
        · exact absurd (hxw2 ▸ hadjpx) hp_nw.2
        · have hxRich : x ∈ Rich := by
            rw [hRichdef]; exact Finset.mem_sdiff.mpr ⟨hxO, by
              simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hxw1, hxw2⟩⟩
          rcases Finset.mem_insert.mp (hRichins ▸ hxRich) with rfl | hxR3
          · exact absurd ((G.mem_neighborFinset _ _).mp hxN) (G.irrefl)
          · exact absurd hadjpx (hpR3nadj x hxR3)
  have hpset : G.neighborFinset p ∩ Hub = ({hg1, hg2, dp} : Finset (Fin 18)) := by
    apply Finset.eq_of_subset_of_card_le hpsub
    rw [hpHubDeg3]
    have hc : ({hg1, hg2, dp} : Finset (Fin 18)).card = 3 := by
      rw [show ({hg1, hg2, dp} : Finset (Fin 18)) = insert hg1 (insert hg2 {dp}) from rfl,
        Finset.card_insert_of_notMem (by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨hg1g2, Ne.symm hdp_g1ne⟩),
        Finset.card_insert_of_notMem (by
          simp only [Finset.mem_singleton]; exact Ne.symm hdp_g2ne),
        Finset.card_singleton]
    rw [hc]
  have hpadj_g1 : G.Adj p hg1 := by
    have hm : hg1 ∈ G.neighborFinset p ∩ Hub := by
      rw [hpset]; exact Finset.mem_insert_self _ _
    exact (G.mem_neighborFinset _ _).mp (Finset.mem_inter.mp hm).1
  have hpadj_g2 : G.Adj p hg2 := by
    have hm : hg2 ∈ G.neighborFinset p ∩ Hub := by
      rw [hpset]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    exact (G.mem_neighborFinset _ _).mp (Finset.mem_inter.mp hm).1
  have hpadj_dp : G.Adj p dp := by
    have hm : dp ∈ G.neighborFinset p ∩ Hub := by
      rw [hpset]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    exact (G.mem_neighborFinset _ _).mp (Finset.mem_inter.mp hm).1
  -- (H) The parity: `∑ C(k,2) = 4` ⟹ no twin meets exactly one of `Rich4`.
  have hparity : (Iso.filter (fun t => (G.neighborFinset t ∩ Rich4).card = 1)).card = 0 := by
    have hid : ∀ t ∈ Iso, (G.neighborFinset t ∩ Rich4).card
        = 2 * ((G.neighborFinset t ∩ Rich4).card).choose 2
          + (if (G.neighborFinset t ∩ Rich4).card = 1 then 1 else 0) := by
      intro t ht
      have hb := hRich4bound t ht
      interval_cases hk : (G.neighborFinset t ∩ Rich4).card <;> simp
    have hsum := Finset.sum_congr rfl hid
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, htotal, hSC4] at hsum
    have hind : ∑ t ∈ Iso, (if (G.neighborFinset t ∩ Rich4).card = 1 then 1 else 0)
        = (Iso.filter (fun t => (G.neighborFinset t ∩ Rich4).card = 1)).card := by
      rw [Finset.card_filter]
    rw [hind] at hsum; omega
  -- (I) `p`'s unique twin `tp` meets exactly one of `Rich4` — contradiction.
  obtain ⟨tp, htpmem⟩ := Finset.card_pos.mp (by rw [hp_iso1]; exact one_pos :
    0 < (G.neighborFinset p ∩ Iso).card)
  have htpIso : tp ∈ Iso := (Finset.mem_inter.mp htpmem).2
  have hp_tp : p ∈ G.neighborFinset tp :=
    (G.mem_neighborFinset _ _).mpr
      ((G.mem_neighborFinset _ _).mp (Finset.mem_inter.mp htpmem).1).symm
  have hp_ne_w1 : p ≠ w1 := (hRichprop p hpRich).2.1
  have hp_ne_w2 : p ≠ w2 := (hRichprop p hpRich).2.2.1
  have hp_notRich4 : p ∉ Rich4 := by
    rw [hRich4def]; simp only [Finset.mem_insert, not_or]
    exact ⟨hp_ne_dr, hpR3⟩
  have hp_notT : p ∉ T := (hRichprop p hpRich).2.2.2
  have hg1T : hg1 ∈ T := by rw [hTdef]; exact Finset.mem_insert_self _ _
  have hg2T : hg2 ∈ T := by
    rw [hTdef]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hdpT : dp ∈ T := by
    rw [hTeq]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_singleton_self _)))
  have hp_ne_g1 : p ≠ hg1 := fun h => hp_notT (h ▸ hg1T)
  have hp_ne_g2 : p ≠ hg2 := fun h => hp_notT (h ▸ hg2T)
  have hp_ne_dp : p ≠ dp := fun h => hp_notT (h ▸ hdpT)
  have hdrRich4 : dr ∈ Rich4 := by rw [hRich4def]; exact Finset.mem_insert_self _ _
  -- `N(tp) ∩ (Hub \ {w₁, w₂}) = N(tp) ∩ insert p Rich4`.
  have htpset : G.neighborFinset tp ∩ (Hub \ {w1, w2})
      = G.neighborFinset tp ∩ insert p Rich4 := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hxN, hxHub, hxnw⟩
      simp only [not_or] at hxnw
      refine ⟨hxN, ?_⟩
      have hxtp : x ∈ G.neighborFinset tp := hxN
      have hxHubTO : x ∈ T ∨ x ∈ O := by
        by_cases hxT : x ∈ T
        · exact Or.inl hxT
        · exact Or.inr (by rw [hOdef]; exact Finset.mem_sdiff.mpr ⟨hxHub, hxT⟩)
      rcases hxHubTO with hxT | hxO
      · rw [hTeq] at hxT
        simp only [Finset.mem_insert, Finset.mem_singleton] at hxT
        rcases hxT with rfl | rfl | rfl | rfl
        · exact absurd ⟨tp, htpIso, p, x, hp_tp, hxtp, hp_ne_g1, hpadj_g1⟩ hcherry
        · exact absurd ⟨tp, htpIso, p, x, hp_tp, hxtp, hp_ne_g2, hpadj_g2⟩ hcherry
        · exact Or.inr hdrRich4
        · exact absurd ⟨tp, htpIso, p, x, hp_tp, hxtp, hp_ne_dp, hpadj_dp⟩ hcherry
      · have hxRich : x ∈ Rich := by
          rw [hRichdef]; exact Finset.mem_sdiff.mpr ⟨hxO, by
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hxnw.1, hxnw.2⟩⟩
        rcases Finset.mem_insert.mp (hRichins ▸ hxRich) with rfl | hxR3
        · exact Or.inl rfl
        · exact Or.inr (by rw [hRich4def]; exact Finset.mem_insert_of_mem hxR3)
    · rintro ⟨hxN, hxp | hxRich4⟩
      · subst hxp
        exact ⟨hxN, hpHub, by simp only [not_or]; exact ⟨hp_ne_w1, hp_ne_w2⟩⟩
      · refine ⟨hxN, hRich4sub hxRich4, ?_⟩
        rcases Finset.mem_insert.mp (hRich4def ▸ hxRich4) with rfl | hxR3
        · simp only [not_or]; exact ⟨hdr_w1, hdr_w2⟩
        · obtain ⟨_, hxw1, hxw2, _⟩ := hRichprop x (hR3sub hxR3)
          simp only [not_or]; exact ⟨hxw1, hxw2⟩
  -- `|N(tp) ∩ Rich4| = 1`, contradicting the parity.
  have htwin2tp : (G.neighborFinset tp ∩ (Hub \ {w1, w2})).card = 2 := htwin2 tp htpIso
  have hNtpp1 : (G.neighborFinset tp ∩ {p}).card = 1 := by
    have hpp : G.neighborFinset tp ∩ {p} = {p} := by
      rw [Finset.inter_eq_right]; exact Finset.singleton_subset_iff.mpr hp_tp
    rw [hpp, Finset.card_singleton]
  have hcard_ins : (G.neighborFinset tp ∩ insert p Rich4).card
      = (G.neighborFinset tp ∩ {p}).card + (G.neighborFinset tp ∩ Rich4).card := by
    rw [show insert p Rich4 = {p} ∪ Rich4 from by rw [Finset.insert_eq],
      Finset.inter_union_distrib_left, Finset.card_union_of_disjoint]
    apply Finset.disjoint_left.mpr
    intro y hy1 hy2
    simp only [Finset.mem_inter, Finset.mem_singleton] at hy1 hy2
    exact hp_notRich4 (hy1.2 ▸ hy2.2)
  have hktp1 : (G.neighborFinset tp ∩ Rich4).card = 1 := by
    rw [htpset, hcard_ins, hNtpp1] at htwin2tp; omega
  have hcontra : 0 < (Iso.filter (fun t => (G.neighborFinset t ∩ Rich4).card = 1)).card :=
    Finset.card_pos.mpr ⟨tp, Finset.mem_filter.mpr ⟨htpIso, hktp1⟩⟩
  omega

end N18

end ACMax
