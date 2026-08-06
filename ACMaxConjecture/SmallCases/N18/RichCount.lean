import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N18.Core
import ACMaxConjecture.SmallCases.N18.TwoHubSelect
import ACMaxConjecture.SmallCases.N18.StarTriangleStruct

/-!
# Abstract rich-hub count bounds for the rigid `n = 18` no-two-hub partition

For the tight `e(M) = 1`, all-degree-`4` profile `(|Hub|, |Iso|) = (10, 6)`, the *rich* hubs are
those meeting `≥ 2` `M`-isolated twins.  This file pins the rich count `r := |R|` between `6` and
`7` using only abstract counting (`N1` = `rich_nonadj_share_eq_one`, `N2` =
`rich_a3_count_le_two_eighteen`, the all-degree-`4` fact, and the no-two-hub hypothesis).

* `rich_count_le_seven_eighteen` (`r ≤ 7`): every non-adjacent rich pair has a **unique** common
  `M`-isolated twin (`N1`); the ordered non-adjacent rich pairs therefore embed into
  `⋃_{t} (N(t) ∩ R)²ᵒᶠᶠ`, bounded by `6·(3² − 3) = 36`; but `r = 8` would force `≥ 8² − 3·8 = 40`
  such pairs.
* `rich_count_ge_six_eighteen` (`r ≥ 6`): `r ≤ 5` forces `∑_R isoDeg ≥ 8 + r` while `N2` caps it at
  `2r + 4`, giving `r ∈ {4, 5}`; either value yields an iso-degree-`4` hub and a second iso-rich
  hub, non-adjacent with `≥ 2` private twins each — a two-hub pair, contradiction.
-/

namespace ACMax

open scoped Classical

namespace N18

/-- `k ≤ 3 ⟹ k² − k ≤ 6` (the off-diagonal cardinality of a `≤ 3`-element twin trace). -/
theorem offdiag_trace_le_six (k : ℕ) (hk : k ≤ 3) : k * k - k ≤ 6 := by
  interval_cases k <;> decide

/-- **`r ≤ 7` — abstract rich-count upper bound.**  With all hubs degree `4` and each `M`-isolated
twin meeting exactly three hubs, the rich hubs `R = {h : 2 ≤ |N(h) ∩ Iso|}` satisfy `|R| ≤ 7`. -/
theorem rich_count_le_seven_eighteen (G : SimpleGraph (Fin 18)) (Hub Iso : Finset (Fin 18))
    (hdeg4 : ∀ h ∈ Hub, G.degree h = 4)
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdisj : Disjoint Hub Iso) (hHub : Hub.card = 10) (hIso : Iso.card = 6)
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hno2hub : ¬∃ h₁ h₂ : Fin 18, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card) :
    (Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)).card ≤ 7 := by
  classical
  set R : Finset (Fin 18) := Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card) with hRdef
  set r : ℕ := R.card with hrdef
  have hRsubHub : R ⊆ Hub := Finset.filter_subset _ _
  have hr10 : r ≤ 10 := by rw [hrdef, ← hHub]; exact Finset.card_le_card hRsubHub
  -- Membership facts for `R`.
  have hRmem : ∀ a, a ∈ R ↔ a ∈ Hub ∧ 2 ≤ (G.neighborFinset a ∩ Iso).card := by
    intro a; rw [hRdef, Finset.mem_filter]
  -- Each rich hub has `≤ 2` hub-neighbours inside `R`.
  have hRnbr : ∀ a ∈ R, (G.neighborFinset a ∩ R).card ≤ 2 := by
    intro a ha
    obtain ⟨haHub, hae⟩ := (hRmem a).mp ha
    have hd4 : (G.neighborFinset a).card = 4 := by
      rw [G.card_neighborFinset_eq_degree, hdeg4 a haHub]
    have hdisjNR : Disjoint (G.neighborFinset a ∩ R) (G.neighborFinset a ∩ Iso) := by
      apply Finset.disjoint_left.mpr
      intro x hx1 hx2
      exact Finset.disjoint_left.mp hdisj (hRsubHub (Finset.mem_inter.mp hx1).2)
        (Finset.mem_inter.mp hx2).2
    have hun : (G.neighborFinset a ∩ R) ∪ (G.neighborFinset a ∩ Iso) ⊆ G.neighborFinset a := by
      rw [← Finset.inter_union_distrib_left]; exact Finset.inter_subset_left
    have hle := Finset.card_le_card hun
    rw [Finset.card_union_of_disjoint hdisjNR, hd4] at hle
    omega
  -- Off-diagonal of `R`.
  set Off : Finset (Fin 18 × Fin 18) := R.offDiag with hOffdef
  have hOffcard : Off.card = r * r - r := by rw [hOffdef, Finset.offDiag_card]
  set Dadj : Finset (Fin 18 × Fin 18) := Off.filter (fun p => G.Adj p.1 p.2) with hDadjdef
  set D : Finset (Fin 18 × Fin 18) := Off.filter (fun p => ¬G.Adj p.1 p.2) with hDdef
  have hDsplit : D.card + Dadj.card = Off.card := by
    rw [hDdef, hDadjdef, add_comm]
    exact Finset.card_filter_add_card_filter_not _
  -- Upper bound on `Dadj`: `≤ 2r` via fibering on the first coordinate.
  have hDadjle : Dadj.card ≤ 2 * r := by
    have hmaps : (Dadj : Set (Fin 18 × Fin 18)).MapsTo Prod.fst R := by
      intro p hp
      rw [hDadjdef, Finset.coe_filter] at hp
      have hpoff : p ∈ Off := hp.1
      rw [hOffdef, Finset.mem_offDiag] at hpoff
      exact hpoff.1
    rw [Finset.card_eq_sum_card_fiberwise hmaps]
    calc ∑ a ∈ R, (Dadj.filter (fun p => p.1 = a)).card
        ≤ ∑ _a ∈ R, 2 := by
          apply Finset.sum_le_sum
          intro a ha
          have hsub : Dadj.filter (fun p => p.1 = a) ⊆ (G.neighborFinset a ∩ R).map
              ⟨fun b => (a, b), fun b₁ b₂ h => by simpa using h⟩ := by
            intro p hp
            rw [Finset.mem_filter, hDadjdef, Finset.mem_filter, hOffdef,
              Finset.mem_offDiag] at hp
            obtain ⟨⟨⟨hp1R, hp2R, _⟩, hadj⟩, hfst⟩ := hp
            rw [Finset.mem_map]
            refine ⟨p.2, ?_, ?_⟩
            · rw [Finset.mem_inter, G.mem_neighborFinset]
              exact ⟨hfst ▸ hadj, hp2R⟩
            · rw [← hfst]
              exact Prod.eta p
          calc (Dadj.filter (fun p => p.1 = a)).card
              ≤ ((G.neighborFinset a ∩ R).map _).card := Finset.card_le_card hsub
            _ = (G.neighborFinset a ∩ R).card := Finset.card_map _
            _ ≤ 2 := hRnbr a ha
      _ = 2 * r := by rw [Finset.sum_const, smul_eq_mul, hrdef, mul_comm]
  -- Upper bound on `D`: each non-adjacent rich pair lies in a twin's off-diagonal trace.
  have hDbiU : D ⊆ Iso.biUnion (fun t => (G.neighborFinset t ∩ R).offDiag) := by
    intro p hp
    rw [hDdef, Finset.mem_filter, hOffdef, Finset.mem_offDiag] at hp
    obtain ⟨⟨hp1R, hp2R, hne⟩, hnadj⟩ := hp
    obtain ⟨hp1Hub, hp1e⟩ := (hRmem p.1).mp hp1R
    obtain ⟨hp2Hub, hp2e⟩ := (hRmem p.2).mp hp2R
    have hsh1 := rich_nonadj_share_eq_one G Hub Iso hshare hno2hub p.1 p.2 hp1Hub hp2Hub
      (hdeg4 p.1 hp1Hub) (hdeg4 p.2 hp2Hub) hne hnadj hp1e hp2e
    obtain ⟨t, ht⟩ := Finset.card_pos.mp (by rw [hsh1]; norm_num)
    rw [Finset.mem_inter, Finset.mem_inter, G.mem_neighborFinset, G.mem_neighborFinset] at ht
    obtain ⟨⟨ht1, ht2⟩, htIso⟩ := ht
    rw [Finset.mem_biUnion]
    refine ⟨t, htIso, ?_⟩
    rw [Finset.mem_offDiag]
    refine ⟨?_, ?_, hne⟩
    · rw [Finset.mem_inter, G.mem_neighborFinset]; exact ⟨ht1.symm, hp1R⟩
    · rw [Finset.mem_inter, G.mem_neighborFinset]; exact ⟨ht2.symm, hp2R⟩
  have hDle : D.card ≤ 36 := by
    calc D.card ≤ (Iso.biUnion (fun t => (G.neighborFinset t ∩ R).offDiag)).card :=
          Finset.card_le_card hDbiU
      _ ≤ ∑ t ∈ Iso, ((G.neighborFinset t ∩ R).offDiag).card := Finset.card_biUnion_le
      _ ≤ ∑ _t ∈ Iso, 6 := by
          apply Finset.sum_le_sum
          intro t ht
          rw [Finset.offDiag_card]
          have hk3 : (G.neighborFinset t ∩ R).card ≤ 3 := by
            calc (G.neighborFinset t ∩ R).card
                ≤ (G.neighborFinset t ∩ Hub).card :=
                  Finset.card_le_card (Finset.inter_subset_inter (Finset.Subset.refl _) hRsubHub)
              _ = 3 := hiso3 t ht
          exact offdiag_trace_le_six _ hk3
      _ = 36 := by rw [Finset.sum_const, hIso, smul_eq_mul]
  -- Combine: `r*r - r = D + Dadj ≤ 36 + 2r`, ruling out `r ≥ 8`.
  interval_cases r <;> omega

/-- **`r ≥ 6` — abstract rich-count lower bound.**  With all hubs degree `4`, each `M`-isolated twin
meeting exactly three hubs, the degree-`4` share bound (`hshare`) and no good two-hub pair
(`hno2hub`), the rich hubs `R = {h : 2 ≤ |N(h) ∩ Iso|}` satisfy `6 ≤ |R|`.  If `|R| ≤ 5` then
`∑_R isoDeg ≥ 8 + |R|` while `N2` caps it at `2|R| + 4`, so `|R| ∈ {4, 5}`; either value yields an
iso-degree-`4` hub `a` and a second iso-degree-`≥ 3` hub `b`, non-adjacent (`a` has all neighbours in
`Iso`) and each keeping `≥ 2` private twins (share `≤ 1`), a two-hub pair contradicting
`hno2hub`. -/
theorem rich_count_ge_six_eighteen (G : SimpleGraph (Fin 18)) (Hub Iso : Finset (Fin 18))
    (hdeg4 : ∀ h ∈ Hub, G.degree h = 4)
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdisj : Disjoint Hub Iso) (hHub : Hub.card = 10) (hIso : Iso.card = 6)
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hno2hub : ¬∃ h₁ h₂ : Fin 18, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card) :
    6 ≤ (Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)).card := by
  classical
  set R : Finset (Fin 18) := Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card) with hRdef
  have hRsubHub : R ⊆ Hub := Finset.filter_subset _ _
  have hRmem : ∀ a, a ∈ R ↔ a ∈ Hub ∧ 2 ≤ (G.neighborFinset a ∩ Iso).card := by
    intro a; rw [hRdef, Finset.mem_filter]
  -- iso-degree bounded by `4` everywhere on `Hub`.
  have hisole4 : ∀ a ∈ Hub, (G.neighborFinset a ∩ Iso).card ≤ 4 := by
    intro a ha
    calc (G.neighborFinset a ∩ Iso).card ≤ (G.neighborFinset a).card :=
          Finset.card_le_card Finset.inter_subset_left
      _ = 4 := by rw [G.card_neighborFinset_eq_degree, hdeg4 a ha]
  by_contra hlt
  push Not at hlt
  set r : ℕ := R.card with hrdef
  have hr5 : r ≤ 5 := by omega
  -- Total iso-incidences = 18.
  have hsum18 : ∑ a ∈ Hub, (G.neighborFinset a ∩ Iso).card = 18 := by
    have := hub_iso_sum_eighteen G Hub Iso hiso3; rw [hIso] at this; omega
  -- Split over `R` and its complement in `Hub`.
  have hsplit : ∑ a ∈ R, (G.neighborFinset a ∩ Iso).card
      + ∑ a ∈ Hub.filter (fun h => ¬ 2 ≤ (G.neighborFinset h ∩ Iso).card),
          (G.neighborFinset a ∩ Iso).card
      = ∑ a ∈ Hub, (G.neighborFinset a ∩ Iso).card := by
    rw [hRdef]
    exact Finset.sum_filter_add_sum_filter_not Hub _ _
  -- Poor hubs carry iso-degree `≤ 1`, so `≤ |Hub \ R| = 10 - r`.
  have hpoorle : ∑ a ∈ Hub.filter (fun h => ¬ 2 ≤ (G.neighborFinset h ∩ Iso).card),
      (G.neighborFinset a ∩ Iso).card ≤ 10 - r := by
    have hcardP : (Hub.filter (fun h => ¬ 2 ≤ (G.neighborFinset h ∩ Iso).card)).card = 10 - r := by
      have := Finset.card_filter_add_card_filter_not (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)
        (s := Hub)
      rw [← hRdef] at this; rw [hHub] at this; omega
    calc ∑ a ∈ Hub.filter (fun h => ¬ 2 ≤ (G.neighborFinset h ∩ Iso).card),
          (G.neighborFinset a ∩ Iso).card
        ≤ ∑ _a ∈ Hub.filter (fun h => ¬ 2 ≤ (G.neighborFinset h ∩ Iso).card), 1 := by
          apply Finset.sum_le_sum
          intro a ha; rw [Finset.mem_filter] at ha; omega
      _ = 10 - r := by rw [Finset.sum_const, smul_eq_mul, mul_one, hcardP]
  have hRlower : 8 + r ≤ ∑ a ∈ R, (G.neighborFinset a ∩ Iso).card := by omega
  -- `N2`: at most two rich hubs have iso-degree `≥ 3`.
  have hN2 : (R.filter (fun h => 3 ≤ (G.neighborFinset h ∩ Iso).card)).card ≤ 2 := by
    have heq : R.filter (fun h => 3 ≤ (G.neighborFinset h ∩ Iso).card)
        = Hub.filter (fun h => G.degree h = 4 ∧ 3 ≤ (G.neighborFinset h ∩ Iso).card) := by
      rw [hRdef, Finset.filter_filter]; apply Finset.filter_congr
      intro a ha; constructor
      · rintro ⟨_, h3⟩; exact ⟨hdeg4 a ha, h3⟩
      · rintro ⟨_, h3⟩; exact ⟨by omega, h3⟩
    rw [heq]
    exact rich_a3_count_le_two_eighteen G Hub Iso hdisj hshare hno2hub
  -- Extract an iso-degree-`4` rich hub `a`.
  obtain ⟨a, haR, ha4⟩ : ∃ a ∈ R, (G.neighborFinset a ∩ Iso).card = 4 := by
    by_contra hcon
    push Not at hcon
    have hbound : ∑ a ∈ R, (G.neighborFinset a ∩ Iso).card
        ≤ ∑ a ∈ R, (2 + if 3 ≤ (G.neighborFinset a ∩ Iso).card then 1 else 0) := by
      apply Finset.sum_le_sum
      intro a ha
      have h2 := ((hRmem a).mp ha).2
      have h4 : (G.neighborFinset a ∩ Iso).card ≤ 4 := hisole4 a (hRsubHub ha)
      have hne4 := hcon a ha
      split_ifs with h3 <;> omega
    rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, ← Finset.card_filter] at hbound
    omega
  obtain ⟨haHub, _⟩ := (hRmem a).mp haR
  -- `N(a) ⊆ Iso`.
  have haIso : G.neighborFinset a ⊆ Iso := by
    have hd4 : (G.neighborFinset a).card = 4 := by
      rw [G.card_neighborFinset_eq_degree, hdeg4 a haHub]
    have heq : G.neighborFinset a ∩ Iso = G.neighborFinset a :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by rw [hd4, ha4])
    rw [← heq]; exact Finset.inter_subset_right
  -- Extract a second iso-degree-`≥ 3` rich hub `b ≠ a`.
  obtain ⟨b, hbR, hbne, hb3⟩ : ∃ b ∈ R, b ≠ a ∧ 3 ≤ (G.neighborFinset b ∩ Iso).card := by
    by_contra hcon
    push Not at hcon
    have hbound : ∑ x ∈ R, (G.neighborFinset x ∩ Iso).card
        ≤ ∑ x ∈ R, (2 + if x = a then 2 else 0) := by
      apply Finset.sum_le_sum
      intro x hx
      by_cases hxa : x = a
      · subst hxa; rw [if_pos rfl]; have := hisole4 x (hRsubHub hx); omega
      · rw [if_neg hxa]; have := hcon x hx hxa; omega
    have hif : ∑ x ∈ R, (if x = a then (2 : ℕ) else 0) = 2 := by
      rw [Finset.sum_ite_eq' R a (fun _ => (2 : ℕ)), if_pos haR]
    rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, hif] at hbound
    omega
  obtain ⟨hbHub, _⟩ := (hRmem b).mp hbR
  -- `a` is non-adjacent to `b`.
  have hnadj : ¬G.Adj a b := by
    intro hadj
    have hbN : b ∈ G.neighborFinset a := (G.mem_neighborFinset a b).mpr hadj
    exact Finset.disjoint_left.mp hdisj hbHub (haIso hbN)
  -- Share `≤ 1`; private twins on each side.
  have hsh : (G.neighborFinset a ∩ G.neighborFinset b ∩ Iso).card ≤ 1 :=
    hshare a haHub (hdeg4 a haHub) b hbHub (hdeg4 b hbHub) hbne.symm hnadj
  have hpa : 2 ≤ ((G.neighborFinset a ∩ Iso) \ G.neighborFinset b).card := by
    have hk := Finset.card_sdiff_add_card_inter (G.neighborFinset a ∩ Iso) (G.neighborFinset b)
    have hi : (G.neighborFinset a ∩ Iso) ∩ G.neighborFinset b
        = G.neighborFinset a ∩ G.neighborFinset b ∩ Iso := Finset.inter_right_comm _ _ _
    rw [hi] at hk; rw [ha4] at hk; omega
  have hpb : 2 ≤ ((G.neighborFinset b ∩ Iso) \ G.neighborFinset a).card := by
    have hk := Finset.card_sdiff_add_card_inter (G.neighborFinset b ∩ Iso) (G.neighborFinset a)
    have hi : (G.neighborFinset b ∩ Iso) ∩ G.neighborFinset a
        = G.neighborFinset a ∩ G.neighborFinset b ∩ Iso := by
      rw [Finset.inter_right_comm, Finset.inter_comm (G.neighborFinset b) (G.neighborFinset a)]
    rw [hi] at hk; omega
  exact hno2hub ⟨a, b, haHub, hbHub, hdeg4 a haHub, hdeg4 b hbHub, Ne.symm hbne, hnadj, hpa, hpb⟩

end N18

end ACMax
