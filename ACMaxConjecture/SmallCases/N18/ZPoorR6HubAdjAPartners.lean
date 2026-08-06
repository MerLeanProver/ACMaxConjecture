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
import ACMaxConjecture.SmallCases.N18.ZPoorR6CodegCount
import ACMaxConjecture.SmallCases.N18.ZPoorR6HubAdjAEngine
import ACMaxConjecture.SmallCases.N18.ZPoorR6HubAdjASubcase
import ACMaxConjecture.SmallCases.N18.ZPoorR6HubAdjATight

/-!
# Design A (`{4,2,2,2,2,2}`) subcase `s = 4` for the `r = 6`, `S = 14` core (`n = 18`)

The hardest design-`A` subcase: both `M`-partner hub-neighbours `d₁, d₂` are iso-degree-`2` rich
hubs (`s = isoDeg d₁ + isoDeg d₂ = 4`).  Here the within-`O` cut leaves enough slack that the
engine bound `E_RR ≥ 4` does not by itself contradict; the rigid co-occurrence pattern together with
`hcodeg0` (`hg₁, hg₂` share no twin) is needed to close it.
-/

namespace ACMax

open scoped Classical

namespace N18

/-- **Design A, subcase `s = 4` is impossible.**  With the `r = 6`, `S = 14` design-`A` structure
(`w` the iso-degree-`4` rich hub), no-apex, no-twin-cherry, `¬Adj d₁ d₂`, both `d₁, d₂`
iso-degree-`2`, and `hcodeg0`, the configuration is contradictory. -/
theorem designA_s4_false_S14 (G : SimpleGraph (Fin 18)) (Hub Iso : Finset (Fin 18))
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
    (hapex : ¬∃ x : Fin 18, x ∈ Hub ∧ x ≠ hg1 ∧ x ≠ hg2 ∧ G.Adj zp x ∧ (G.Adj hg1 x ∨ G.Adj hg2 x))
    (hg1iso1 : (G.neighborFinset hg1 ∩ Iso).card = 1)
    (hg2iso1 : (G.neighborFinset hg2 ∩ Iso).card = 1)
    (hcodeg0 : (G.neighborFinset hg1 ∩ G.neighborFinset hg2 ∩ Iso).card = 0)
    (hd1iso2 : (G.neighborFinset d1 ∩ Iso).card = 2)
    (hd2iso2 : (G.neighborFinset d2 ∩ Iso).card = 2) :
    False := by
  classical
  set RichAll : Finset (Fin 18) := Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)
    with hRichAlldef
  set Rich : Finset (Fin 18) := RichAll.erase w with hRichdef
  set Poor : Finset (Fin 18) := Hub \ RichAll with hPoordef
  -- The two engine-tightness outputs: a `w`-twin meeting no rich hub, and rich-internal-closed.
  have hzd1 : 1 ≤ (G.neighborFinset d1 ∩ (Finset.univ \ (Hub ∪ Iso))).card :=
    Finset.card_pos.mpr ⟨zp, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hd1zp, hzpZ⟩⟩
  have hzd2 : 1 ≤ (G.neighborFinset d2 ∩ (Finset.univ \ (Hub ∪ Iso))).card :=
    Finset.card_pos.mpr ⟨zp, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hd2zp, hzpZ⟩⟩
  obtain ⟨htwin, hRIC⟩ := designA_both_poor_wtwin_S14 G Hub Iso hiso3 hdisj hIso hdeg4 hshare
    hno2hub hcherry w hwHub hw4 hother2 hr6 d1 d2 hd1Hub hd2Hub hd1d2 hd1iso2 hd2iso2 hzd1 hzd2
  rw [← hRichAlldef, ← hRichdef] at htwin hRIC
  -- `w` is hub-isolated.
  have hwsplit := nbr_split_three_eighteen G Hub Iso hdisj w
  rw [hdeg4 w hwHub, hw4] at hwsplit
  have hwiso : (G.neighborFinset w ∩ Hub).card = 0 := by omega
  have hwNoHub : ∀ h ∈ Hub, ¬G.Adj w h := by
    intro h hh hadj
    have hmem : h ∈ G.neighborFinset w ∩ Hub :=
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hadj, hh⟩
    rw [Finset.card_eq_zero.mp hwiso] at hmem
    exact absurd hmem (Finset.notMem_empty h)
  -- Set bookkeeping for the rich / poor split.
  have hRichAllsub : RichAll ⊆ Hub := by rw [hRichAlldef]; exact Finset.filter_subset _ _
  have hRichAllcard : RichAll.card = 6 := by rw [hRichAlldef]; exact hr6
  have hPoorsub : Poor ⊆ Hub := by rw [hPoordef]; exact Finset.sdiff_subset
  have hPoorcard : Poor.card = 4 := by
    have hadd : Poor.card + RichAll.card = Hub.card := by
      rw [hPoordef]; exact Finset.card_sdiff_add_card_eq_card hRichAllsub
    rw [hRichAllcard, hHub] at hadd; omega
  have hmemRichAll : ∀ p : Fin 18, p ∈ Hub → (G.neighborFinset p ∩ Iso).card = 1 → p ∈ Poor := by
    intro p hp hp1
    rw [hPoordef, Finset.mem_sdiff, hRichAlldef, Finset.mem_filter]
    exact ⟨hp, fun h => by have := h.2; omega⟩
  have hg1Poor : hg1 ∈ Poor := hmemRichAll hg1 hg1Hub hg1iso1
  have hg2Poor : hg2 ∈ Poor := hmemRichAll hg2 hg2Hub hg2iso1
  have hd1RichAll : d1 ∈ RichAll := by
    rw [hRichAlldef, Finset.mem_filter]; exact ⟨hd1Hub, hd1iso2.ge⟩
  have hd2RichAll : d2 ∈ RichAll := by
    rw [hRichAlldef, Finset.mem_filter]; exact ⟨hd2Hub, hd2iso2.ge⟩
  -- `z`-degree accounting: only `hg₁, hg₂, d₁, d₂` carry a `Z`-incidence.
  have hzsum := zdeg_sum_four_eighteen G Hub Iso hiso3 hdisj hHub hIso hdsum hdeg3 hisodeg3 hleak
  set T : Finset (Fin 18) := ({hg1, hg2, d1, d2} : Finset (Fin 18)) with hTdef
  have hd1g1 : d1 ≠ hg1 := fun h => by rw [h, hg1iso1] at hd1iso2; omega
  have hd1g2 : d1 ≠ hg2 := fun h => by rw [h, hg2iso1] at hd1iso2; omega
  have hd2g1 : d2 ≠ hg1 := fun h => by rw [h, hg1iso1] at hd2iso2; omega
  have hd2g2 : d2 ≠ hg2 := fun h => by rw [h, hg2iso1] at hd2iso2; omega
  have hTsubHub : T ⊆ Hub := by
    rw [hTdef]; intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  have hsum4T : ∀ f : Fin 18 → ℕ, ∑ v ∈ T, f v = f hg1 + f hg2 + f d1 + f d2 := by
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
  have hzg1 : 1 ≤ (G.neighborFinset hg1 ∩ (Finset.univ \ (Hub ∪ Iso))).card :=
    Finset.card_pos.mpr ⟨z, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hg1z, hzZ⟩⟩
  have hzg2 : 1 ≤ (G.neighborFinset hg2 ∩ (Finset.univ \ (Hub ∪ Iso))).card :=
    Finset.card_pos.mpr ⟨z, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hg2z, hzZ⟩⟩
  have hZsdiff := Finset.sum_sdiff
    (f := fun h => (G.neighborFinset h ∩ (Finset.univ \ (Hub ∪ Iso))).card) hTsubHub
  rw [hzsum, hsum4T] at hZsdiff
  have hZrest0 : ∑ h ∈ Hub \ T, (G.neighborFinset h ∩ (Finset.univ \ (Hub ∪ Iso))).card = 0 := by
    omega
  have hzPoor0 : ∀ p ∈ Poor, p ≠ hg1 → p ≠ hg2 →
      (G.neighborFinset p ∩ (Finset.univ \ (Hub ∪ Iso))).card = 0 := by
    intro p hp hpg1 hpg2
    have hpHubT : p ∈ Hub \ T := by
      rw [Finset.mem_sdiff, hTdef]
      refine ⟨hPoorsub hp, ?_⟩
      simp only [Finset.mem_insert, Finset.mem_singleton]
      push Not
      refine ⟨hpg1, hpg2, ?_, ?_⟩
      · rintro rfl; exact absurd hd1RichAll (by rw [hPoordef, Finset.mem_sdiff] at hp; exact hp.2)
      · rintro rfl; exact absurd hd2RichAll (by rw [hPoordef, Finset.mem_sdiff] at hp; exact hp.2)
    exact Nat.le_zero.mp (hZrest0 ▸ Finset.single_le_sum (f := fun h =>
      (G.neighborFinset h ∩ (Finset.univ \ (Hub ∪ Iso))).card) (fun _ _ => Nat.zero_le _) hpHubT)
  -- Poor hubs only connect to poor hubs (`E_RP = 0`, via `RIC` and `w` isolated).
  have hPoorNbr : ∀ p ∈ Poor, G.neighborFinset p ∩ Hub ⊆ Poor := by
    intro p hp x hx
    rw [Finset.mem_inter, G.mem_neighborFinset] at hx
    obtain ⟨hadj, hxHub⟩ := hx
    rw [hPoordef, Finset.mem_sdiff]
    refine ⟨hxHub, ?_⟩
    intro hxRichAll
    by_cases hxw : x = w
    · exact hwNoHub p (hPoorsub hp) (hxw ▸ hadj).symm
    · have hxRich : x ∈ Rich := by rw [hRichdef, Finset.mem_erase]; exact ⟨hxw, hxRichAll⟩
      have hpRich : p ∈ Rich := hRIC x hxRich
        (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hadj.symm, hPoorsub hp⟩)
      have : p ∈ RichAll := Finset.mem_of_mem_erase (hRichdef ▸ hpRich)
      rw [hPoordef, Finset.mem_sdiff] at hp
      exact hp.2 this
  -- A poor hub other than `hg₁, hg₂` has hub-degree `3`, hence is adjacent to every other poor hub.
  have hPoorDeg3 : ∀ p ∈ Poor, p ≠ hg1 → p ≠ hg2 → ∀ q ∈ Poor, q ≠ p → G.Adj p q := by
    intro p hp hpg1 hpg2 q hq hqp
    have hsp := nbr_split_three_eighteen G Hub Iso hdisj p
    rw [hdeg4 p (hPoorsub hp), hzPoor0 p hp hpg1 hpg2] at hsp
    have hisop : (G.neighborFinset p ∩ Iso).card ≤ 1 := by
      by_contra hc
      have : p ∈ RichAll := by
        rw [hRichAlldef, Finset.mem_filter]; exact ⟨hPoorsub hp, by omega⟩
      rw [hPoordef, Finset.mem_sdiff] at hp; exact hp.2 this
    have hsubPe : G.neighborFinset p ∩ Hub ⊆ Poor.erase p := by
      intro x hx
      rw [Finset.mem_erase]
      refine ⟨?_, hPoorNbr p hp hx⟩
      rintro rfl
      exact ((G.mem_neighborFinset _ _).mp (Finset.mem_inter.mp hx).1).ne rfl
    have hcardle : (G.neighborFinset p ∩ Hub).card ≤ 3 := by
      calc (G.neighborFinset p ∩ Hub).card ≤ (Poor.erase p).card := Finset.card_le_card hsubPe
        _ = 3 := by rw [Finset.card_erase_of_mem hp, hPoorcard]
    have heqset : G.neighborFinset p ∩ Hub = Poor.erase p :=
      Finset.eq_of_subset_of_card_le hsubPe (by
        rw [Finset.card_erase_of_mem hp, hPoorcard]; omega)
    have hqmem : q ∈ G.neighborFinset p ∩ Hub := by
      rw [heqset, Finset.mem_erase]; exact ⟨hqp, hq⟩
    exact (G.mem_neighborFinset _ _).mp (Finset.mem_inter.mp hqmem).1
  -- The non-adjacent poor pair is exactly `{hg₁, hg₂}`.
  have hPoorPair : ∀ a ∈ Poor, ∀ b ∈ Poor, a ≠ b → ¬G.Adj a b →
      (a = hg1 ∧ b = hg2) ∨ (a = hg2 ∧ b = hg1) := by
    intro a ha b hb hab hnadjab
    have haIn : a = hg1 ∨ a = hg2 := by
      by_contra hc
      push Not at hc
      exact hnadjab (hPoorDeg3 a ha hc.1 hc.2 b hb (Ne.symm hab))
    have hbIn : b = hg1 ∨ b = hg2 := by
      by_contra hc
      push Not at hc
      exact hnadjab ((hPoorDeg3 b hb hc.1 hc.2 a ha hab).symm)
    rcases haIn with rfl | rfl <;> rcases hbIn with rfl | rfl
    · exact absurd rfl hab
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩
    · exact absurd rfl hab
  -- Unpack the both-poor `w`-twin and reach the `hcodeg0` contradiction.
  obtain ⟨t, htIso, hwt, htRich0⟩ := htwin
  have htHub3 : (G.neighborFinset t ∩ Hub).card = 3 := hiso3 t htIso
  have htRich0' : G.neighborFinset t ∩ Rich = ∅ := Finset.card_eq_zero.mp htRich0
  have hwmem : w ∈ G.neighborFinset t ∩ Hub :=
    Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hwt.symm, hwHub⟩
  set S : Finset (Fin 18) := (G.neighborFinset t ∩ Hub).erase w with hSdef
  have hScard : S.card = 2 := by rw [hSdef, Finset.card_erase_of_mem hwmem, htHub3]
  have hSsubPoor : S ⊆ Poor := by
    intro x hx
    rw [hSdef, Finset.mem_erase, Finset.mem_inter] at hx
    obtain ⟨hxw, hxN, hxHub⟩ := hx
    rw [hPoordef, Finset.mem_sdiff]
    refine ⟨hxHub, ?_⟩
    intro hxRichAll
    have hxRich : x ∈ Rich := by rw [hRichdef, Finset.mem_erase]; exact ⟨hxw, hxRichAll⟩
    have : x ∈ G.neighborFinset t ∩ Rich := Finset.mem_inter.mpr ⟨hxN, hxRich⟩
    rw [htRich0'] at this
    exact absurd this (Finset.notMem_empty x)
  obtain ⟨a, b, hab, hSeq⟩ := Finset.card_eq_two.mp hScard
  have haS : a ∈ S := by rw [hSeq]; exact Finset.mem_insert_self a {b}
  have hbS : b ∈ S := by rw [hSeq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self b)
  have haN : a ∈ G.neighborFinset t := (Finset.mem_inter.mp (Finset.mem_of_mem_erase
    (hSdef ▸ haS))).1
  have hbN : b ∈ G.neighborFinset t := (Finset.mem_inter.mp (Finset.mem_of_mem_erase
    (hSdef ▸ hbS))).1
  have hnadjab : ¬G.Adj a b := by
    intro hadj
    exact hcherry ⟨t, htIso, a, b, haN, hbN, hab, hadj⟩
  -- Both `hg₁` and `hg₂` are neighbours of the twin `t`.
  have hpair := hPoorPair a (hSsubPoor haS) b (hSsubPoor hbS) hab hnadjab
  have hg1N : hg1 ∈ G.neighborFinset t := by
    rcases hpair with ⟨rfl, _⟩ | ⟨_, rfl⟩ <;> assumption
  have hg2N : hg2 ∈ G.neighborFinset t := by
    rcases hpair with ⟨_, rfl⟩ | ⟨rfl, _⟩ <;> assumption
  have htcodeg : t ∈ G.neighborFinset hg1 ∩ G.neighborFinset hg2 ∩ Iso :=
    Finset.mem_inter.mpr ⟨Finset.mem_inter.mpr
      ⟨(G.mem_neighborFinset _ _).mpr ((G.mem_neighborFinset _ _).mp hg1N).symm,
       (G.mem_neighborFinset _ _).mpr ((G.mem_neighborFinset _ _).mp hg2N).symm⟩, htIso⟩
  rw [Finset.card_eq_zero.mp hcodeg0] at htcodeg
  exact absurd htcodeg (Finset.notMem_empty t)

end N18

end ACMax
