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

/-!
# Design A (`{4,2,2,2,2,2}`) engine tightness for the `r = 6`, `S = 14` core (`n = 18`)

The design-`A` engine (`designA_rich_edges_ge_four_S14`) shows the five iso-degree-`2` rich hubs carry
`≥ 4` internal hub-edges.  In the `s = 4` subcase the two `M`-partner hubs `d₁, d₂` are themselves
rich (iso-degree `2`) and each spend one degree-slot on the `M`-vertex `zp`, so the within-rich
hub-mass is at most `8`; combined with the engine bound `≥ 8` this is an *equality*, which forces the
codegree double-count to be tight.  The tight `(2, 3)` split on the two non-`w` twins together with
the `(2, 2, 1, 0)` split on the four `w`-twins produces a `w`-twin meeting **no** rich hub, i.e. a
`w`-twin whose two non-`w` partners are both poor.
-/

namespace ACMax

open scoped Classical

namespace N18

set_option maxHeartbeats 1600000 in
/-- **Design A, `s = 4`: a `w`-twin meets no rich hub.**  With the `r = 6`, `S = 14` design-`A`
structure and both `M`-partners `d₁, d₂` iso-degree-`2` rich hubs (each adjacent to a `Z`-vertex
`zp`), the within-rich hub-mass is exactly `8`, forcing the codegree count tight; hence some twin
`t ∈ N(w) ∩ Iso` has `|N(t) ∩ Rich| = 0`. -/
theorem designA_both_poor_wtwin_S14 (G : SimpleGraph (Fin 18)) (Hub Iso : Finset (Fin 18))
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
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
    (w : Fin 18) (hwHub : w ∈ Hub) (hw4 : (G.neighborFinset w ∩ Iso).card = 4)
    (hother2 : ∀ r ∈ Hub, r ≠ w → 2 ≤ (G.neighborFinset r ∩ Iso).card →
      (G.neighborFinset r ∩ Iso).card = 2)
    (hr6 : (Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)).card = 6)
    (d1 d2 : Fin 18) (hd1Hub : d1 ∈ Hub) (hd2Hub : d2 ∈ Hub) (hd1d2 : d1 ≠ d2)
    (hd1iso2 : (G.neighborFinset d1 ∩ Iso).card = 2)
    (hd2iso2 : (G.neighborFinset d2 ∩ Iso).card = 2)
    (hzd1 : 1 ≤ (G.neighborFinset d1 ∩ (Finset.univ \ (Hub ∪ Iso))).card)
    (hzd2 : 1 ≤ (G.neighborFinset d2 ∩ (Finset.univ \ (Hub ∪ Iso))).card) :
    (∃ t : Fin 18, t ∈ Iso ∧ G.Adj w t ∧
      (G.neighborFinset t ∩
        ((Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)).erase w)).card = 0)
    ∧ (∀ r ∈ (Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)).erase w,
        G.neighborFinset r ∩ Hub ⊆
          (Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)).erase w) := by
  classical
  set RichAll : Finset (Fin 18) := Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)
    with hRichAlldef
  set Rich : Finset (Fin 18) := RichAll.erase w with hRichdef
  set Wtw : Finset (Fin 18) := G.neighborFinset w ∩ Iso with hWtwdef
  have hwRichAll : w ∈ RichAll := by
    rw [hRichAlldef, Finset.mem_filter]; exact ⟨hwHub, by rw [← hWtwdef]; omega⟩
  have hRichcard : Rich.card = 5 := by
    rw [hRichdef, Finset.card_erase_of_mem hwRichAll, hr6]
  have hRichsubHub : Rich ⊆ Hub := by
    rw [hRichdef]; intro x hx
    exact Finset.mem_of_mem_filter x (Finset.mem_of_mem_erase hx)
  have hwnotRich : w ∉ Rich := by rw [hRichdef]; exact Finset.notMem_erase w RichAll
  have hrmem : ∀ r ∈ Rich, r ∈ Hub ∧ r ≠ w ∧ (G.neighborFinset r ∩ Iso).card = 2 := by
    intro r hr
    rw [hRichdef] at hr
    have hrRA : r ∈ RichAll := Finset.mem_of_mem_erase hr
    have hrne : r ≠ w := Finset.ne_of_mem_erase hr
    rw [hRichAlldef, Finset.mem_filter] at hrRA
    exact ⟨hrRA.1, hrne, hother2 r hrRA.1 hrne hrRA.2⟩
  -- `d₁, d₂ ∈ Rich`.
  have hd1ne : d1 ≠ w := fun h => by rw [h, hw4] at hd1iso2; omega
  have hd2ne : d2 ≠ w := fun h => by rw [h, hw4] at hd2iso2; omega
  have hd1Rich : d1 ∈ Rich := by
    rw [hRichdef, Finset.mem_erase]
    exact ⟨hd1ne, by rw [hRichAlldef, Finset.mem_filter]; exact ⟨hd1Hub, by rw [hd1iso2]⟩⟩
  have hd2Rich : d2 ∈ Rich := by
    rw [hRichdef, Finset.mem_erase]
    exact ⟨hd2ne, by rw [hRichAlldef, Finset.mem_filter]; exact ⟨hd2Hub, by rw [hd2iso2]⟩⟩
  -- `w` is hub-isolated.
  have hwsplit := nbr_split_three_eighteen G Hub Iso hdisj w
  rw [hdeg4 w hwHub, hw4] at hwsplit
  have hwiso : (G.neighborFinset w ∩ Hub).card = 0 := by omega
  have hwnadj : ∀ r ∈ Hub, ¬G.Adj w r := by
    intro r hr hadj
    have hmem : r ∈ G.neighborFinset w ∩ Hub :=
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hadj, hr⟩
    rw [Finset.card_eq_zero.mp hwiso] at hmem
    exact absurd hmem (Finset.notMem_empty r)
  -- Each rich hub shares exactly one twin with `w`.
  have hcodegwr : ∀ r ∈ Rich,
      (G.neighborFinset w ∩ G.neighborFinset r ∩ Iso).card = 1 := by
    intro r hr
    obtain ⟨hrHub, hrne, hriso2⟩ := hrmem r hr
    have hwr : ¬G.Adj w r := hwnadj r hrHub
    have hle1 := hshare w hwHub (hdeg4 w hwHub) r hrHub (hdeg4 r hrHub) (Ne.symm hrne) hwr
    rcases Nat.lt_or_ge (G.neighborFinset w ∩ G.neighborFinset r ∩ Iso).card 1 with h0 | h1
    · exfalso
      have hcard0 : (G.neighborFinset w ∩ G.neighborFinset r ∩ Iso).card = 0 := by omega
      apply hno2hub
      have heqA : (G.neighborFinset w ∩ Iso) ∩ G.neighborFinset r
          = G.neighborFinset w ∩ G.neighborFinset r ∩ Iso := by
        ext x; simp only [Finset.mem_inter]; tauto
      have heqB : (G.neighborFinset r ∩ Iso) ∩ G.neighborFinset w
          = G.neighborFinset w ∩ G.neighborFinset r ∩ Iso := by
        ext x; simp only [Finset.mem_inter]; tauto
      refine ⟨w, r, hwHub, hrHub, hdeg4 w hwHub, hdeg4 r hrHub, Ne.symm hrne, hwr, ?_, ?_⟩
      · have hh := Finset.card_inter_add_card_sdiff (G.neighborFinset w ∩ Iso) (G.neighborFinset r)
        rw [heqA, hcard0, hw4] at hh
        omega
      · have hh := Finset.card_inter_add_card_sdiff (G.neighborFinset r ∩ Iso) (G.neighborFinset w)
        rw [heqB, hcard0, hriso2] at hh
        omega
    · omega
  -- The total / `w`-twin / non-`w`-twin rich-incidence sums.
  have htotal : ∑ t ∈ Iso, (G.neighborFinset t ∩ Rich).card = 10 := by
    rw [cross_count G Iso Rich]
    calc ∑ x ∈ Rich, (G.neighborFinset x ∩ Iso).card
        = ∑ x ∈ Rich, 2 := Finset.sum_congr rfl (fun r hr => (hrmem r hr).2.2)
      _ = 10 := by simp [Finset.sum_const, hRichcard]
  have hWtwsubIso : Wtw ⊆ Iso := by rw [hWtwdef]; exact Finset.inter_subset_right
  have hWtwcard : Wtw.card = 4 := by rw [hWtwdef, ← hw4]
  have hWtwsum : ∑ t ∈ Wtw, (G.neighborFinset t ∩ Rich).card = 5 := by
    rw [cross_count G Wtw Rich]
    calc ∑ x ∈ Rich, (G.neighborFinset x ∩ Wtw).card
        = ∑ x ∈ Rich, 1 := by
          apply Finset.sum_congr rfl
          intro r hr
          have heq : G.neighborFinset r ∩ Wtw = G.neighborFinset w ∩ G.neighborFinset r ∩ Iso := by
            rw [hWtwdef]; ext y; simp only [Finset.mem_inter]; tauto
          rw [heq]; exact hcodegwr r hr
      _ = 5 := by simp [Finset.sum_const, hRichcard]
  have hrestsum : ∑ t ∈ Iso \ Wtw, (G.neighborFinset t ∩ Rich).card = 5 := by
    have hh := Finset.sum_sdiff (f := fun t => (G.neighborFinset t ∩ Rich).card) hWtwsubIso
    rw [hWtwsum, htotal] at hh
    omega
  have hrestcard : (Iso \ Wtw).card = 2 := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hWtwsubIso]; omega
  -- Per-twin rich-degree bounds.
  have hWtwbound : ∀ t ∈ Wtw, (G.neighborFinset t ∩ Rich).card ≤ 2 := by
    intro t ht
    have htIso : t ∈ Iso := hWtwsubIso ht
    have htw : w ∈ G.neighborFinset t := by
      rw [hWtwdef] at ht
      have htadjw := (Finset.mem_inter.mp ht).1
      exact (G.mem_neighborFinset _ _).mpr ((G.mem_neighborFinset _ _).mp htadjw).symm
    have hsub : G.neighborFinset t ∩ Rich ⊆ (G.neighborFinset t ∩ Hub).erase w := by
      intro x hx
      rw [Finset.mem_inter] at hx
      rw [Finset.mem_erase, Finset.mem_inter]
      exact ⟨fun hxw => hwnotRich (hxw ▸ hx.2), hx.1, hRichsubHub hx.2⟩
    calc (G.neighborFinset t ∩ Rich).card
        ≤ ((G.neighborFinset t ∩ Hub).erase w).card := Finset.card_le_card hsub
      _ = (G.neighborFinset t ∩ Hub).card - 1 :=
          Finset.card_erase_of_mem (Finset.mem_inter.mpr ⟨htw, hwHub⟩)
      _ = 2 := by rw [hiso3 t htIso]
  have hrestbound : ∀ t ∈ Iso \ Wtw, (G.neighborFinset t ∩ Rich).card ≤ 3 := by
    intro t ht
    have htIso : t ∈ Iso := (Finset.mem_sdiff.mp ht).1
    calc (G.neighborFinset t ∩ Rich).card
        ≤ (G.neighborFinset t ∩ Hub).card := Finset.card_le_card (fun x hx => by
            rw [Finset.mem_inter] at hx ⊢; exact ⟨hx.1, hRichsubHub hx.2⟩)
      _ = 3 := hiso3 t htIso
  -- The codegree right-hand side split.
  have hRHSsplit : ∑ t ∈ Iso, ((G.neighborFinset t ∩ Rich).card).choose 2
      = ∑ t ∈ Wtw, ((G.neighborFinset t ∩ Rich).card).choose 2
        + ∑ t ∈ Iso \ Wtw, ((G.neighborFinset t ∩ Rich).card).choose 2 := by
    rw [← Finset.sum_sdiff hWtwsubIso]; exact Nat.add_comm _ _
  have hWtwchoose : ∑ t ∈ Wtw, ((G.neighborFinset t ∩ Rich).card).choose 2 ≤ 2 := by
    have hb : 2 * ∑ t ∈ Wtw, ((G.neighborFinset t ∩ Rich).card).choose 2
        ≤ ∑ t ∈ Wtw, (G.neighborFinset t ∩ Rich).card := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun t ht => two_mul_choose_two_le_self _ (hWtwbound t ht))
    rw [hWtwsum] at hb
    omega
  have hrestchoose : ∑ t ∈ Iso \ Wtw, ((G.neighborFinset t ∩ Rich).card).choose 2 ≤ 4 := by
    obtain ⟨a, b, hab, heq2⟩ := Finset.card_eq_two.mp hrestcard
    have ha_mem : a ∈ Iso \ Wtw := by rw [heq2]; exact Finset.mem_insert_self a {b}
    have hb_mem : b ∈ Iso \ Wtw := by
      rw [heq2]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self b)
    have hsum : (G.neighborFinset a ∩ Rich).card + (G.neighborFinset b ∩ Rich).card = 5 := by
      have hh := hrestsum; rw [heq2, Finset.sum_pair hab] at hh; exact hh
    rw [heq2, Finset.sum_pair hab]
    exact choose_two_pair_sum_five_le_four _ _ (hrestbound a ha_mem) (hrestbound b hb_mem) hsum
  -- The rich-pair dichotomy: codegree is `1` on non-edges, `0` on edges.
  have hdich : ∀ p ∈ Rich.offDiag.filter (fun p => p.1 < p.2),
      (G.neighborFinset p.1 ∩ G.neighborFinset p.2 ∩ Iso).card
        = if G.Adj p.1 p.2 then 0 else 1 := by
    intro p hp
    rw [Finset.mem_filter, Finset.mem_offDiag] at hp
    obtain ⟨⟨hp1, hp2, hp12⟩, _hlt⟩ := hp
    by_cases hadj : G.Adj p.1 p.2
    · rw [if_pos hadj, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro t ht
      rw [Finset.mem_inter, Finset.mem_inter] at ht
      obtain ⟨⟨ht1, ht2⟩, htIso⟩ := ht
      exact hcherry ⟨t, htIso, p.1, p.2,
        (G.mem_neighborFinset _ _).mpr ((G.mem_neighborFinset _ _).mp ht1).symm,
        (G.mem_neighborFinset _ _).mpr ((G.mem_neighborFinset _ _).mp ht2).symm, hp12, hadj⟩
    · rw [if_neg hadj]
      obtain ⟨hp1Hub, _, hp1iso2⟩ := hrmem p.1 hp1
      obtain ⟨hp2Hub, _, hp2iso2⟩ := hrmem p.2 hp2
      have hle1 := hshare p.1 hp1Hub (hdeg4 p.1 hp1Hub) p.2 hp2Hub (hdeg4 p.2 hp2Hub) hp12 hadj
      rcases Nat.lt_or_ge (G.neighborFinset p.1 ∩ G.neighborFinset p.2 ∩ Iso).card 1 with h0 | h1
      · exfalso
        have hcard0 : (G.neighborFinset p.1 ∩ G.neighborFinset p.2 ∩ Iso).card = 0 := by omega
        apply hno2hub
        have heqA : (G.neighborFinset p.1 ∩ Iso) ∩ G.neighborFinset p.2
            = G.neighborFinset p.1 ∩ G.neighborFinset p.2 ∩ Iso := by
          ext x; simp only [Finset.mem_inter]; tauto
        have heqB : (G.neighborFinset p.2 ∩ Iso) ∩ G.neighborFinset p.1
            = G.neighborFinset p.1 ∩ G.neighborFinset p.2 ∩ Iso := by
          ext x; simp only [Finset.mem_inter]; tauto
        refine ⟨p.1, p.2, hp1Hub, hp2Hub, hdeg4 p.1 hp1Hub, hdeg4 p.2 hp2Hub, hp12, hadj, ?_, ?_⟩
        · have hh := Finset.card_inter_add_card_sdiff (G.neighborFinset p.1 ∩ Iso)
            (G.neighborFinset p.2)
          rw [heqA, hcard0, hp1iso2] at hh
          omega
        · have hh := Finset.card_inter_add_card_sdiff (G.neighborFinset p.2 ∩ Iso)
            (G.neighborFinset p.1)
          rw [heqB, hcard0, hp2iso2] at hh
          omega
      · omega
  -- Translate the codegree sum into the count of non-adjacent rich pairs.
  have hcodegsum : ∑ p ∈ Rich.offDiag.filter (fun p => p.1 < p.2),
      (G.neighborFinset p.1 ∩ G.neighborFinset p.2 ∩ Iso).card
      = ((Rich.offDiag.filter (fun p => p.1 < p.2)).filter (fun p => ¬G.Adj p.1 p.2)).card := by
    have hstep : ∑ p ∈ Rich.offDiag.filter (fun p => p.1 < p.2),
        (G.neighborFinset p.1 ∩ G.neighborFinset p.2 ∩ Iso).card
        = ∑ p ∈ Rich.offDiag.filter (fun p => p.1 < p.2),
            (if G.Adj p.1 p.2 then 0 else 1) := Finset.sum_congr rfl hdich
    rw [hstep, Finset.card_filter]
    exact Finset.sum_congr rfl (fun p _ => by by_cases h : G.Adj p.1 p.2 <;> simp [h])
  have hLtcard : (Rich.offDiag.filter (fun p => p.1 < p.2)).card = 10 := by
    rw [card_offDiag_filter_lt, hRichcard]; decide
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := Rich.offDiag.filter (fun p => p.1 < p.2)) (p := fun p => G.Adj p.1 p.2)
  have hfilteq : (Rich.offDiag.filter (fun p => p.1 < p.2)).filter (fun p => G.Adj p.1 p.2)
      = Rich.offDiag.filter (fun p => p.1 < p.2 ∧ G.Adj p.1 p.2) := Finset.filter_filter _ _ _
  -- Handshake: the within-`Rich` degree sum counts ordered adjacent pairs.
  have hH1 : ∑ r ∈ Rich, (G.neighborFinset r ∩ Rich).card
      = (Rich.offDiag.filter (fun p => G.Adj p.1 p.2)).card := by
    have hoff : Rich.offDiag.filter (fun p => G.Adj p.1 p.2)
        = (Rich ×ˢ Rich).filter (fun p => G.Adj p.1 p.2) := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_offDiag, Finset.mem_product]
      constructor
      · rintro ⟨⟨h1, h2, _⟩, hadj⟩; exact ⟨⟨h1, h2⟩, hadj⟩
      · rintro ⟨⟨h1, h2⟩, hadj⟩; exact ⟨⟨h1, h2, hadj.ne⟩, hadj⟩
    rw [hoff, Finset.card_filter, Finset.sum_product]
    apply Finset.sum_congr rfl
    intro r _
    have heq : G.neighborFinset r ∩ Rich = Rich.filter (fun y => G.Adj r y) := by
      ext b
      simp only [Finset.mem_inter, Finset.mem_filter, SimpleGraph.mem_neighborFinset]; tauto
    rw [heq, Finset.card_filter]
  -- The within-rich hub-mass is at most `8` (each rich hub spends `2` slots; `d₁, d₂` give one each
  -- to `Z`).
  have hperHub : ∀ r ∈ Rich, (G.neighborFinset r ∩ Hub).card
      + (G.neighborFinset r ∩ (Finset.univ \ (Hub ∪ Iso))).card = 2 := by
    intro r hr
    obtain ⟨hrHub, _, hriso2⟩ := hrmem r hr
    have hsp := nbr_split_three_eighteen G Hub Iso hdisj r
    rw [hdeg4 r hrHub, hriso2] at hsp; omega
  have hHubmassZ : (∑ r ∈ Rich, (G.neighborFinset r ∩ Hub).card)
      + ∑ r ∈ Rich, (G.neighborFinset r ∩ (Finset.univ \ (Hub ∪ Iso))).card = 10 := by
    rw [← Finset.sum_add_distrib]
    calc ∑ r ∈ Rich, ((G.neighborFinset r ∩ Hub).card
            + (G.neighborFinset r ∩ (Finset.univ \ (Hub ∪ Iso))).card)
        = ∑ r ∈ Rich, 2 := Finset.sum_congr rfl hperHub
      _ = 10 := by simp [Finset.sum_const, hRichcard]
  have hZdd : 2 ≤ ∑ r ∈ Rich, (G.neighborFinset r ∩ (Finset.univ \ (Hub ∪ Iso))).card := by
    have hsub : ({d1, d2} : Finset (Fin 18)) ⊆ Rich := by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
    have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (f := fun r => (G.neighborFinset r ∩ (Finset.univ \ (Hub ∪ Iso))).card)
      (fun _ _ _ => Nat.zero_le _)
    rw [Finset.sum_pair hd1d2] at hle
    omega
  have hERRle : ∑ r ∈ Rich, (G.neighborFinset r ∩ Rich).card ≤ 8 := by
    have hstep : ∑ r ∈ Rich, (G.neighborFinset r ∩ Rich).card
        ≤ ∑ r ∈ Rich, (G.neighborFinset r ∩ Hub).card :=
      Finset.sum_le_sum (fun r _ => Finset.card_le_card
        (Finset.inter_subset_inter subset_rfl hRichsubHub))
    omega
  -- The engine lower bound `≥ 8`, hence `E_RR = 8` and the adjacent-pair count is `4`.
  have hEngine := designA_rich_edges_ge_four_S14 G Hub Iso hiso3 hdisj hIso hdeg4 hshare hno2hub
    hcherry w hwHub hw4 hother2 hr6
  rw [← hRichAlldef, ← hRichdef] at hEngine
  have hERR8 : ∑ r ∈ Rich, (G.neighborFinset r ∩ Rich).card = 8 := le_antisymm hERRle hEngine
  -- The within-rich hub-mass is also exactly `8`, so each rich hub keeps all its hub-edges inside
  -- `Rich`: the rich-internal-closed structure (`RIC`).
  have hHubmass8 : ∑ r ∈ Rich, (G.neighborFinset r ∩ Hub).card = 8 := by
    have hge : 8 ≤ ∑ r ∈ Rich, (G.neighborFinset r ∩ Hub).card := by
      have hstep : ∑ r ∈ Rich, (G.neighborFinset r ∩ Rich).card
          ≤ ∑ r ∈ Rich, (G.neighborFinset r ∩ Hub).card :=
        Finset.sum_le_sum (fun r _ => Finset.card_le_card
          (Finset.inter_subset_inter subset_rfl hRichsubHub))
      omega
    omega
  have hper0 : ∀ r ∈ Rich, (G.neighborFinset r ∩ Rich).card = (G.neighborFinset r ∩ Hub).card := by
    have hle : ∀ r ∈ Rich, (G.neighborFinset r ∩ Rich).card ≤ (G.neighborFinset r ∩ Hub).card :=
      fun r _ => Finset.card_le_card (Finset.inter_subset_inter subset_rfl hRichsubHub)
    exact (Finset.sum_eq_sum_iff_of_le hle).mp (by rw [hERR8, hHubmass8])
  have hRIC : ∀ r ∈ Rich, G.neighborFinset r ∩ Hub ⊆ Rich := by
    intro r hr
    have heq : G.neighborFinset r ∩ Rich = G.neighborFinset r ∩ Hub :=
      Finset.eq_of_subset_of_card_le (Finset.inter_subset_inter subset_rfl hRichsubHub)
        (le_of_eq (hper0 r hr).symm)
    intro x hx
    rw [← heq] at hx
    exact (Finset.mem_inter.mp hx).2
  -- Extract a `w`-twin with rich-incidence `0`.
  have htwin : ∃ t : Fin 18, t ∈ Iso ∧ G.Adj w t ∧
      (G.neighborFinset t ∩ Rich).card = 0 := by
    have htwomul := card_offDiag_filter_adj_eq_two_mul G Rich
    rw [← hfilteq] at htwomul
    have hERRadj : ∑ r ∈ Rich, (G.neighborFinset r ∩ Rich).card
        = 2 * ((Rich.offDiag.filter (fun p => p.1 < p.2)).filter (fun p => G.Adj p.1 p.2)).card := by
      rw [hH1, htwomul]
    have hadj4 : ((Rich.offDiag.filter (fun p => p.1 < p.2)).filter
        (fun p => G.Adj p.1 p.2)).card = 4 := by omega
    have hnonadj6 :
        ((Rich.offDiag.filter (fun p => p.1 < p.2)).filter (fun p => ¬G.Adj p.1 p.2)).card = 6 := by
      omega
    have hIsoC : ∑ t ∈ Iso, ((G.neighborFinset t ∩ Rich).card).choose 2 = 6 := by
      rw [← codeg_pair_sum_eq_twin_choose2 G Iso Rich, hcodegsum, hnonadj6]
    have hWtwC2 : ∑ t ∈ Wtw, ((G.neighborFinset t ∩ Rich).card).choose 2 = 2 := by
      rw [hRHSsplit] at hIsoC; omega
    by_contra hcon
    push Not at hcon
    have hge1 : ∀ t ∈ Wtw, 1 ≤ (G.neighborFinset t ∩ Rich).card := by
      intro t ht
      have htIso : t ∈ Iso := hWtwsubIso ht
      have htadjw : G.Adj w t := by
        rw [hWtwdef, Finset.mem_inter] at ht
        exact ((G.mem_neighborFinset _ _).mp ht.1)
      have := hcon t htIso htadjw
      omega
    have hkey : ∀ t ∈ Wtw, (G.neighborFinset t ∩ Rich).card
        = ((G.neighborFinset t ∩ Rich).card).choose 2 + 1 := by
      intro t ht
      have h1 := hge1 t ht
      have h2 := hWtwbound t ht
      have hv : (G.neighborFinset t ∩ Rich).card = 1 ∨ (G.neighborFinset t ∩ Rich).card = 2 := by
        omega
      rcases hv with h | h <;> rw [h] <;> decide
    have hsum6 : ∑ t ∈ Wtw, (G.neighborFinset t ∩ Rich).card
        = (∑ t ∈ Wtw, ((G.neighborFinset t ∩ Rich).card).choose 2) + Wtw.card := by
      rw [Finset.card_eq_sum_ones Wtw, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl hkey
    rw [hWtwsum, hWtwC2, hWtwcard] at hsum6
    omega
  exact ⟨htwin, hRIC⟩

end N18

end ACMax
