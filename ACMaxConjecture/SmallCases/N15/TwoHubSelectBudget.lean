import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N15.TwoHubSelect

/-!
# Budget leaf for the `n = 15` two-hub `|Hub| = 7` corner

This file supplies the **share-budget** machinery feeding the `|Hub| = 7` branch of
`two_hub_corner_select_fifteen`.  The core is `budget_card_bound`: assuming **no good pair** (no
non-adjacent hub pair whose shared isolated twins fall `≥ 2` short of both iso-degrees), the exact
off-diagonal share sum `6·|Iso| = 36` forces `u(u−1) + m(m−1) ≤ 48`, where `u = #{iso-deg ≥ 2}`
and `m = #{iso-deg ≥ 3}`.  This holds for any iso-degrees (the lower bound only uses
`share ≥ min − 1` on usable non-adjacent pairs, and `min ≥ 2`, `min ≥ 3` for usable, strong pairs
respectively).

`two_hub_corner_select_fifteen_noFour` applies this when `F.card = 0` (no degree-`4` hub of
iso-degree `4`): the seven degree-`4` hubs then have iso-degrees `≤ 3` summing to `18`, so the
profile is one of `(3,3,3,3,3,3,0)`, `(3,3,3,3,3,2,1)`, `(3,3,3,3,2,2,2)`, all of which give
`u(u−1) + m(m−1) ∈ {60, 50, 54} > 48`, a contradiction.
-/

namespace ACMax

open scoped Classical

namespace N15

/-- **Share-budget cardinality bound.**  In a hub set with `≤ 6` ordered adjacent pairs and every
isolated twin meeting exactly three hubs (`|Iso| = 6`), if every non-adjacent hub pair satisfies
`min(iso-deg) ≤ share + 1` (the **no good pair** hypothesis), then
`|U.offDiag| + |M3.offDiag| ≤ 48` for `U = {iso-deg ≥ 2}`, `M3 = {iso-deg ≥ 3}`. -/
theorem budget_card_bound (G : SimpleGraph (Fin 15)) (Hub Iso : Finset (Fin 15))
    (hHubsum : ∑ w ∈ Hub, (G.neighborFinset w ∩ Hub).card ≤ 6)
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hIso6 : Iso.card = 6)
    (hnogood : ∀ a ∈ Hub, ∀ b ∈ Hub, a ≠ b → ¬G.Adj a b →
      min ((G.neighborFinset a ∩ Iso).card) ((G.neighborFinset b ∩ Iso).card)
        ≤ (G.neighborFinset a ∩ G.neighborFinset b ∩ Iso).card + 1) :
    (Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)).offDiag.card
      + (Hub.filter (fun h => 3 ≤ (G.neighborFinset h ∩ Iso).card)).offDiag.card ≤ 48 := by
  classical
  set U : Finset (Fin 15) := Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card) with hU
  set M3 : Finset (Fin 15) := Hub.filter (fun h => 3 ≤ (G.neighborFinset h ∩ Iso).card) with hM3
  have hUsub : U ⊆ Hub := by rw [hU]; exact Finset.filter_subset _ _
  have hM3sub : M3 ⊆ Hub := by rw [hM3]; exact Finset.filter_subset _ _
  have hM3U : M3 ⊆ U := by
    intro x hx
    rw [hM3, Finset.mem_filter] at hx
    rw [hU, Finset.mem_filter]
    exact ⟨hx.1, by omega⟩
  have hUoffsub : U.offDiag ⊆ Hub.offDiag := by
    intro p hp
    rw [Finset.mem_offDiag] at hp ⊢
    exact ⟨hUsub hp.1, hUsub hp.2.1, hp.2.2⟩
  have hglob : ∑ p ∈ Hub.offDiag,
      (G.neighborFinset p.1 ∩ G.neighborFinset p.2 ∩ Iso).card = 36 := by
    rw [hub_offDiag_share_sum G Hub Iso hiso3, hIso6]
  have hsumUle : ∑ p ∈ U.offDiag,
      (G.neighborFinset p.1 ∩ G.neighborFinset p.2 ∩ Iso).card ≤ 36 := by
    rw [← hglob]
    exact Finset.sum_le_sum_of_subset_of_nonneg hUoffsub (fun _ _ _ => Nat.zero_le _)
  have hgbound : ∀ p ∈ U.offDiag,
      (if ¬G.Adj p.1 p.2 then 1 else 0)
        + (if (¬G.Adj p.1 p.2 ∧ 3 ≤ (G.neighborFinset p.1 ∩ Iso).card
              ∧ 3 ≤ (G.neighborFinset p.2 ∩ Iso).card) then 1 else 0)
        ≤ (G.neighborFinset p.1 ∩ G.neighborFinset p.2 ∩ Iso).card := by
    intro p hp
    rw [Finset.mem_offDiag] at hp
    obtain ⟨hp1, hp2, hp12⟩ := hp
    have hp1U := hp1
    have hp2U := hp2
    rw [hU, Finset.mem_filter] at hp1U hp2U
    have hd1 : 2 ≤ (G.neighborFinset p.1 ∩ Iso).card := hp1U.2
    have hd2 : 2 ≤ (G.neighborFinset p.2 ∩ Iso).card := hp2U.2
    by_cases hadj : G.Adj p.1 p.2
    · simp [hadj]
    · have hk := hnogood p.1 hp1U.1 p.2 hp2U.1 hp12 hadj
      rw [if_pos hadj]
      by_cases hboth : 3 ≤ (G.neighborFinset p.1 ∩ Iso).card
          ∧ 3 ≤ (G.neighborFinset p.2 ∩ Iso).card
      · rw [if_pos ⟨hadj, hboth.1, hboth.2⟩]; omega
      · rw [if_neg (fun h => hboth ⟨h.2.1, h.2.2⟩)]; omega
  have hg_sum : (U.offDiag.filter (fun p => ¬G.Adj p.1 p.2)).card
      + (U.offDiag.filter (fun p => ¬G.Adj p.1 p.2
            ∧ 3 ≤ (G.neighborFinset p.1 ∩ Iso).card
            ∧ 3 ≤ (G.neighborFinset p.2 ∩ Iso).card)).card ≤ 36 := by
    have hle := le_trans (Finset.sum_le_sum hgbound) hsumUle
    rw [Finset.sum_add_distrib, ← Finset.card_filter, ← Finset.card_filter] at hle
    exact hle
  have hN1 : U.offDiag.card ≤ (U.offDiag.filter (fun p => ¬G.Adj p.1 p.2)).card + 6 := by
    have hpart := Finset.card_filter_add_card_filter_not (s := U.offDiag)
      (fun p => G.Adj p.1 p.2)
    have hadjU : (U.offDiag.filter (fun p => G.Adj p.1 p.2)).card ≤ 6 := by
      refine le_trans (Finset.card_le_card ?_) (hub_offDiag_adj_le G Hub 6 hHubsum)
      exact Finset.filter_subset_filter _ hUoffsub
    omega
  have hN2 : M3.offDiag.card
      ≤ (U.offDiag.filter (fun p => ¬G.Adj p.1 p.2
            ∧ 3 ≤ (G.neighborFinset p.1 ∩ Iso).card
            ∧ 3 ≤ (G.neighborFinset p.2 ∩ Iso).card)).card + 6 := by
    have hpart := Finset.card_filter_add_card_filter_not (s := M3.offDiag)
      (fun p => G.Adj p.1 p.2)
    have hadjM : (M3.offDiag.filter (fun p => G.Adj p.1 p.2)).card ≤ 6 := by
      refine le_trans (Finset.card_le_card ?_) (hub_offDiag_adj_le G Hub 6 hHubsum)
      apply Finset.filter_subset_filter
      intro p hp
      rw [Finset.mem_offDiag] at hp ⊢
      exact ⟨hM3sub hp.1, hM3sub hp.2.1, hp.2.2⟩
    have hsubset : M3.offDiag.filter (fun p => ¬G.Adj p.1 p.2)
        ⊆ U.offDiag.filter (fun p => ¬G.Adj p.1 p.2
            ∧ 3 ≤ (G.neighborFinset p.1 ∩ Iso).card
            ∧ 3 ≤ (G.neighborFinset p.2 ∩ Iso).card) := by
      intro p hp
      rw [Finset.mem_filter, Finset.mem_offDiag] at hp
      obtain ⟨⟨hp1, hp2, hp12⟩, hnadj⟩ := hp
      have hp1M := hp1
      have hp2M := hp2
      rw [hM3, Finset.mem_filter] at hp1M hp2M
      rw [Finset.mem_filter, Finset.mem_offDiag]
      exact ⟨⟨hM3U hp1, hM3U hp2, hp12⟩, hnadj, hp1M.2, hp2M.2⟩
    have hle := Finset.card_le_card hsubset
    omega
  omega

/-- **No good pair from a refuted selection.**  Packages `select_finish` into the
`min(iso-deg) ≤ share + 1` form on non-adjacent degree-`4` hub pairs, given a refutation `hcon` of
the selection goal. -/
theorem nogood_of_not_select (G : SimpleGraph (Fin 15)) (Hub Iso : Finset (Fin 15))
    (hdeg4 : ∀ h ∈ Hub, G.degree h = 4)
    (hcon : ¬ ∃ h₁ h₂ : Fin 15, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card) :
    ∀ a ∈ Hub, ∀ b ∈ Hub, a ≠ b → ¬G.Adj a b →
      min ((G.neighborFinset a ∩ Iso).card) ((G.neighborFinset b ∩ Iso).card)
        ≤ (G.neighborFinset a ∩ G.neighborFinset b ∩ Iso).card + 1 := by
  intro a ha b hb hne hnadj
  by_contra hlt
  push Not at hlt
  have hsa : (G.neighborFinset a ∩ G.neighborFinset b ∩ Iso).card + 2
      ≤ (G.neighborFinset a ∩ Iso).card := by omega
  have hcomm : (G.neighborFinset b ∩ G.neighborFinset a ∩ Iso).card
      = (G.neighborFinset a ∩ G.neighborFinset b ∩ Iso).card := by
    rw [Finset.inter_comm (G.neighborFinset b) (G.neighborFinset a)]
  have hsb : (G.neighborFinset b ∩ G.neighborFinset a ∩ Iso).card + 2
      ≤ (G.neighborFinset b ∩ Iso).card := by rw [hcomm]; omega
  have hfin := select_finish G Iso a b hsa hsb
  exact hcon ⟨a, b, ha, hb, hdeg4 a ha, hdeg4 b hb, hne, hnadj, hfin.1, hfin.2⟩

/-- **Total iso-degree is `18`.**  Each of the six isolated twins meets exactly three hubs. -/
theorem hub_iso_degree_sum (G : SimpleGraph (Fin 15)) (Hub Iso : Finset (Fin 15))
    (hIso6 : Iso.card = 6) (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3) :
    ∑ a ∈ Hub, (G.neighborFinset a ∩ Iso).card = 18 := by
  rw [cross_count G Hub Iso]
  calc ∑ t ∈ Iso, (G.neighborFinset t ∩ Hub).card
      = ∑ _t ∈ Iso, 3 := Finset.sum_congr rfl (fun t ht => hiso3 t ht)
    _ = 18 := by rw [Finset.sum_const, hIso6, smul_eq_mul]

/-- **Budget leaf, `|Hub| = 7`, no iso-degree-`4` hub.**  Seven degree-`4` hubs, every isolated
twin meeting exactly three hubs, at most `6` ordered adjacent hub pairs, and no hub of iso-degree
`4`.  Then there exist two non-adjacent degree-`4` hubs each retaining `≥ 2` private isolated
twins. -/
theorem two_hub_corner_select_fifteen_noFour
    (G : SimpleGraph (Fin 15)) (Hub Iso : Finset (Fin 15))
    (hHub7 : Hub.card = 7) (hIso6 : Iso.card = 6)
    (hdeg4 : ∀ h ∈ Hub, G.degree h = 4)
    (hHubsum : ∑ w ∈ Hub, (G.neighborFinset w ∩ Hub).card ≤ 6)
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hnoFour : ∀ h ∈ Hub, (G.neighborFinset h ∩ Iso).card ≠ 4) :
    ∃ h₁ h₂ : Fin 15, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card := by
  classical
  by_contra hcon
  have key := nogood_of_not_select G Hub Iso hdeg4 hcon
  have hbig := budget_card_bound G Hub Iso hHubsum hiso3 hIso6 key
  -- Iso-degrees are `≤ 3` (bounded by degree `4`, and never equal to `4`).
  have hdle3 : ∀ a ∈ Hub, (G.neighborFinset a ∩ Iso).card ≤ 3 := by
    intro a ha
    have h1 : (G.neighborFinset a ∩ Iso).card ≤ G.degree a := by
      rw [← G.card_neighborFinset_eq_degree]
      exact Finset.card_le_card Finset.inter_subset_left
    have h2 := hdeg4 a ha
    have h3 := hnoFour a ha
    omega
  set U : Finset (Fin 15) := Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card) with hU
  set M3 : Finset (Fin 15) := Hub.filter (fun h => 3 ≤ (G.neighborFinset h ∩ Iso).card) with hM3
  have hUsub : U ⊆ Hub := by rw [hU]; exact Finset.filter_subset _ _
  have hM3U : M3 ⊆ U := by
    intro x hx
    rw [hM3, Finset.mem_filter] at hx
    rw [hU, Finset.mem_filter]
    exact ⟨hx.1, by omega⟩
  -- Threshold decomposition `d = [d ≥ 1] + [d ≥ 2] + [d ≥ 3]`.
  have hdecomp : ∀ a ∈ Hub, (G.neighborFinset a ∩ Iso).card
      = (if 1 ≤ (G.neighborFinset a ∩ Iso).card then 1 else 0)
        + (if 2 ≤ (G.neighborFinset a ∩ Iso).card then 1 else 0)
        + (if 3 ≤ (G.neighborFinset a ∩ Iso).card then 1 else 0) := by
    intro a ha
    have h3 := hdle3 a ha
    split_ifs <;> omega
  set n1 : ℕ := (Hub.filter (fun h => 1 ≤ (G.neighborFinset h ∩ Iso).card)).card with hn1
  have hsumeq : n1 + U.card + M3.card = 18 := by
    have hcong : ∑ a ∈ Hub, (G.neighborFinset a ∩ Iso).card
        = ∑ a ∈ Hub, ((if 1 ≤ (G.neighborFinset a ∩ Iso).card then 1 else 0)
          + (if 2 ≤ (G.neighborFinset a ∩ Iso).card then 1 else 0)
          + (if 3 ≤ (G.neighborFinset a ∩ Iso).card then 1 else 0)) :=
      Finset.sum_congr rfl hdecomp
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.card_filter, ← Finset.card_filter, ← Finset.card_filter,
      hub_iso_degree_sum G Hub Iso hIso6 hiso3] at hcong
    rw [hn1, hU, hM3]
    omega
  have hn1le : n1 ≤ 7 := by
    rw [hn1, ← hHub7]; exact Finset.card_le_card (Finset.filter_subset _ _)
  have hun1 : U.card ≤ n1 := by
    rw [hn1, hU]
    apply Finset.card_le_card
    intro x hx
    rw [Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, by omega⟩
  have hu7 : U.card ≤ 7 := by rw [← hHub7]; exact Finset.card_le_card hUsub
  have hmu : M3.card ≤ U.card := Finset.card_le_card hM3U
  set u := U.card with hu_def
  set m := M3.card with hm_def
  have hcU : U.offDiag.card = u * u - u := by rw [Finset.offDiag_card, hu_def]
  have hcM : M3.offDiag.card = m * m - m := by rw [Finset.offDiag_card, hm_def]
  have hu6 : 6 ≤ u := by omega
  interval_cases u <;> interval_cases m <;> omega

end N15

end ACMax
