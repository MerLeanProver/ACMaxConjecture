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

/-!
# Design A (`{4,2,2,2,2,2}`) rich-edge engine for the `r = 6`, `S = 14` core (`n = 18`)

The combinatorial heart of the design-`A` half: the five iso-degree-`2` rich hubs
`Rich = RichAll.erase w` (with `RichAll` the six rich hubs and `w` the iso-degree-`4` hub) carry at
least `4` internal hub-edges, i.e. `∑_{r ∈ Rich} |N(r) ∩ Rich| ≥ 8`.

The proof is the codegree double-count `codeg_pair_sum_eq_twin_choose2` (with `S := Rich`): the
codegree sum over rich pairs equals `∑_{t ∈ Iso} C(|N(t) ∩ Rich|, 2)`, bounded by `6` (the four
`w`-twins each meet `≤ 2` rich hubs with total `5`, contributing `≤ 2`; the two non-`w` twins split
the remaining `5` rich incidences as `(2, 3)`, contributing `≤ 4`).  The rich-pair dichotomy
(`¬Adj ↔ codeg = 1`, from `hshare`/`hno2hub`; `Adj ↔ codeg = 0`, from no-twin-cherry) then turns the
codegree sum into the count of non-adjacent rich pairs, `≤ 6` of the `C(5, 2) = 10`, so `≥ 4` are
adjacent.
-/

namespace ACMax

open scoped Classical

namespace N18

/-- For `k ≤ 2`, twice the binomial `C(k, 2)` is at most `k`. -/
theorem two_mul_choose_two_le_self (k : ℕ) (hk : k ≤ 2) : 2 * k.choose 2 ≤ k := by
  interval_cases k <;> decide

/-- Two binomials `C(a, 2) + C(b, 2)` with `a, b ≤ 3` and `a + b = 5` sum to at most `4`. -/
theorem choose_two_pair_sum_five_le_four (a b : ℕ) (ha : a ≤ 3) (hb : b ≤ 3)
    (hab : a + b = 5) : a.choose 2 + b.choose 2 ≤ 4 := by
  interval_cases a <;> interval_cases b <;> simp_all

/-- **Symmetric adjacency-pair count is twice the strictly-ordered count.**  For any finset `s`, the
number of ordered adjacent pairs `(a, b) ∈ s × s` is twice the number with `a < b`. -/
theorem card_offDiag_filter_adj_eq_two_mul (G : SimpleGraph (Fin 18)) (s : Finset (Fin 18)) :
    (s.offDiag.filter (fun p => G.Adj p.1 p.2)).card
      = 2 * (s.offDiag.filter (fun p => p.1 < p.2 ∧ G.Adj p.1 p.2)).card := by
  classical
  have hswap : (s.offDiag.filter (fun p : Fin 18 × Fin 18 => ¬ p.1 < p.2 ∧ G.Adj p.1 p.2)).card
      = (s.offDiag.filter (fun p : Fin 18 × Fin 18 => p.1 < p.2 ∧ G.Adj p.1 p.2)).card := by
    rw [← Finset.card_image_of_injective
        (s.offDiag.filter (fun p : Fin 18 × Fin 18 => p.1 < p.2 ∧ G.Adj p.1 p.2))
        Prod.swap_injective]
    congr 1
    ext ⟨a, b⟩
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_offDiag, Prod.swap_prod_mk,
      Prod.mk.injEq, Prod.exists]
    constructor
    · rintro ⟨⟨ha, hb, hab⟩, hlt, hadj⟩
      exact ⟨b, a, ⟨⟨hb, ha, fun h => hab h.symm⟩,
        lt_of_le_of_ne (not_lt.1 hlt) (fun h => hab h.symm), G.adj_symm hadj⟩, rfl, rfl⟩
    · rintro ⟨c, d, ⟨⟨hc, hd, hcd⟩, hlt, hadj⟩, rfl, rfl⟩
      exact ⟨⟨hd, hc, fun h => hcd h.symm⟩, not_lt.2 hlt.le, G.adj_symm hadj⟩
  have hpart := Finset.card_filter_add_card_filter_not (s := s.offDiag)
    (p := fun p : Fin 18 × Fin 18 => p.1 < p.2 ∧ G.Adj p.1 p.2)
  have hadjfilt : s.offDiag.filter (fun p => G.Adj p.1 p.2)
      = s.offDiag.filter (fun p : Fin 18 × Fin 18 => p.1 < p.2 ∧ G.Adj p.1 p.2)
        ∪ s.offDiag.filter (fun p : Fin 18 × Fin 18 => ¬ p.1 < p.2 ∧ G.Adj p.1 p.2) := by
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, Finset.mem_union]
    tauto
  have hdisj : Disjoint
      (s.offDiag.filter (fun p : Fin 18 × Fin 18 => p.1 < p.2 ∧ G.Adj p.1 p.2))
      (s.offDiag.filter (fun p : Fin 18 × Fin 18 => ¬ p.1 < p.2 ∧ G.Adj p.1 p.2)) := by
    rw [Finset.disjoint_left]
    rintro ⟨a, b⟩ h1 h2
    simp only [Finset.mem_filter] at h1 h2
    exact h2.2.1 h1.2.1
  rw [hadjfilt, Finset.card_union_of_disjoint hdisj, hswap]
  ring

/-- **Design A: the five rich hubs carry at least four internal hub-edges.**  With the `r = 6`,
`S = 14` design-`A` structure (`w` the iso-degree-`4` rich hub, `Rich = RichAll.erase w` the five
iso-degree-`2` rich hubs), `hshare`, `hno2hub`, no-twin-cherry, the within-`Rich` ordered hub-degree
sum is at least `8`. -/
theorem designA_rich_edges_ge_four_S14 (G : SimpleGraph (Fin 18)) (Hub Iso : Finset (Fin 18))
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
    (hr6 : (Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)).card = 6) :
    8 ≤ ∑ r ∈ (Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)).erase w,
        (G.neighborFinset r ∩
          ((Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)).erase w)).card := by
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
  -- The codegree right-hand side is at most `6`.
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
  have hRHSle : ∑ t ∈ Iso, ((G.neighborFinset t ∩ Rich).card).choose 2 ≤ 6 := by
    rw [hRHSsplit]; omega
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
  have hnonadj_le :
      ((Rich.offDiag.filter (fun p => p.1 < p.2)).filter (fun p => ¬G.Adj p.1 p.2)).card ≤ 6 := by
    rw [← hcodegsum, codeg_pair_sum_eq_twin_choose2 G Iso Rich]; exact hRHSle
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := Rich.offDiag.filter (fun p => p.1 < p.2)) (p := fun p => G.Adj p.1 p.2)
  have hadjpair_ge :
      4 ≤ ((Rich.offDiag.filter (fun p => p.1 < p.2)).filter (fun p => G.Adj p.1 p.2)).card := by
    omega
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
  rw [hH1, card_offDiag_filter_adj_eq_two_mul, ← hfilteq]
  omega

end N18

end ACMax
