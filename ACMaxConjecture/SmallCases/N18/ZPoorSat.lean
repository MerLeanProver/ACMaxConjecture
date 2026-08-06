import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N18.Core
import ACMaxConjecture.SmallCases.N18.TwoHubSelect
import ACMaxConjecture.SmallCases.N18.StarTriangleStruct
import ACMaxConjecture.SmallCases.N18.RichCount
import ACMaxConjecture.SmallCases.N18.Align8Helpers
import ACMaxConjecture.SmallCases.N18.ZPoorN3
import ACMaxConjecture.SmallCases.N18.ZPoorR7
import ACMaxConjecture.SmallCases.N18.ZVertex

/-!
# The `r = 7`, `S = 15` saturation chain closing the main residual (`n = 18`)

For the tight `e(M) = 1`, all-degree-`4`, `(|Hub|, |Iso|) = (10, 6)` profile with seven rich hubs
and rich iso-incidence sum `S = 15`, the poor incidences concentrate as `(3,3,3,3,3,0)`
(`poor_incidence_concentrates_eighteen`).  This file carries the saturation chain that turns that
design into the good `C₄` kill.
-/

namespace ACMax

open scoped Classical

namespace N18

/-- **The ordered adjacent off-diagonal count equals the within-set degree sum.** -/
theorem dadj_eq_sum_eighteen (G : SimpleGraph (Fin 18)) (R : Finset (Fin 18)) :
    (R.offDiag.filter (fun p => G.Adj p.1 p.2)).card
      = ∑ a ∈ R, (G.neighborFinset a ∩ R).card := by
  classical
  set Dadj : Finset (Fin 18 × Fin 18) := R.offDiag.filter (fun p => G.Adj p.1 p.2) with hDdef
  have hmaps : (Dadj : Set (Fin 18 × Fin 18)).MapsTo Prod.fst R := by
    intro p hp
    rw [hDdef, Finset.coe_filter] at hp
    have hpoff : p ∈ R.offDiag := hp.1
    rw [Finset.mem_offDiag] at hpoff
    exact hpoff.1
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.card_bij (fun p _ => p.2)
  · intro p hp
    rw [Finset.mem_filter, hDdef, Finset.mem_filter, Finset.mem_offDiag] at hp
    obtain ⟨⟨⟨_, hp2R, _⟩, hadj⟩, hfst⟩ := hp
    rw [Finset.mem_inter, G.mem_neighborFinset]
    exact ⟨hfst ▸ hadj, hp2R⟩
  · intro p hp q hq hpq
    rw [Finset.mem_filter, hDdef, Finset.mem_filter] at hp hq
    have hp1 : p.1 = a := hp.2
    have hq1 : q.1 = a := hq.2
    exact Prod.ext (hp1.trans hq1.symm) hpq
  · intro b hb
    rw [Finset.mem_inter, G.mem_neighborFinset] at hb
    refine ⟨(a, b), ?_, rfl⟩
    rw [Finset.mem_filter, hDdef, Finset.mem_filter, Finset.mem_offDiag]
    have hne : a ≠ b := fun he => G.irrefl (he ▸ hb.1)
    exact ⟨⟨⟨ha, hb.2, hne⟩, hb.1⟩, rfl⟩

/-- **The ordered adjacent off-diagonal count is even** (closed under coordinate swap with no
fixed points on the off-diagonal). -/
theorem even_dadj_eighteen (G : SimpleGraph (Fin 18)) (R : Finset (Fin 18)) :
    Even (R.offDiag.filter (fun p => G.Adj p.1 p.2)).card := by
  classical
  set S : Finset (Fin 18 × Fin 18) := R.offDiag.filter (fun p => G.Adj p.1 p.2) with hSdef
  set Lt : Finset (Fin 18 × Fin 18) := S.filter (fun p => p.1 < p.2) with hLtdef
  set Gt : Finset (Fin 18 × Fin 18) := S.filter (fun p => ¬ p.1 < p.2) with hGtdef
  have hsplit : Lt.card + Gt.card = S.card := by
    rw [hLtdef, hGtdef]
    exact Finset.card_filter_add_card_filter_not (s := S) (fun p => p.1 < p.2)
  have hcardeq : Gt.card = Lt.card := by
    apply Finset.card_bij (fun p _ => Prod.swap p)
    · intro p hp
      rw [hGtdef, Finset.mem_filter, hSdef, Finset.mem_filter, Finset.mem_offDiag] at hp
      obtain ⟨⟨⟨hp1, hp2, hne⟩, hadj⟩, hnlt⟩ := hp
      rw [hLtdef, Finset.mem_filter, hSdef, Finset.mem_filter, Finset.mem_offDiag]
      refine ⟨⟨⟨hp2, hp1, fun he => hne he.symm⟩, hadj.symm⟩, ?_⟩
      simp only [Prod.fst_swap, Prod.snd_swap]
      omega
    · intro p hp q hq hpq
      have := congrArg Prod.swap hpq
      simpa using this
    · intro b hb
      rw [hLtdef, Finset.mem_filter, hSdef, Finset.mem_filter, Finset.mem_offDiag] at hb
      obtain ⟨⟨⟨hb1, hb2, hne⟩, hadj⟩, hlt⟩ := hb
      refine ⟨Prod.swap b, ?_, by simp⟩
      rw [hGtdef, Finset.mem_filter, hSdef, Finset.mem_filter, Finset.mem_offDiag]
      refine ⟨⟨⟨hb2, hb1, fun he => hne he.symm⟩, hadj.symm⟩, ?_⟩
      simp only [Prod.fst_swap, Prod.snd_swap]
      omega
  rw [← hsplit, hcardeq]
  exact ⟨Lt.card, by ring⟩

/-- **The non-adjacent rich off-diagonal lies in the twins' traces** (share-`1`). -/
theorem rich_nonadj_biUnion_eighteen (G : SimpleGraph (Fin 18)) (Hub Iso R : Finset (Fin 18))
    (hdeg4 : ∀ h ∈ Hub, G.degree h = 4)
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hno2hub : ¬∃ h₁ h₂ : Fin 18, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card)
    (hRHub : R ⊆ Hub) (hRrich : ∀ a ∈ R, 2 ≤ (G.neighborFinset a ∩ Iso).card) :
    (R.offDiag.filter (fun p => ¬G.Adj p.1 p.2))
      ⊆ Iso.biUnion (fun t => (G.neighborFinset t ∩ R).offDiag) := by
  classical
  intro p hp
  rw [Finset.mem_filter, Finset.mem_offDiag] at hp
  obtain ⟨⟨hp1R, hp2R, hne⟩, hnadj⟩ := hp
  have hp1Hub := hRHub hp1R
  have hp2Hub := hRHub hp2R
  have hsh1 := rich_nonadj_share_eq_one G Hub Iso hshare hno2hub p.1 p.2 hp1Hub hp2Hub
    (hdeg4 p.1 hp1Hub) (hdeg4 p.2 hp2Hub) hne hnadj (hRrich p.1 hp1R) (hRrich p.2 hp2R)
  obtain ⟨t, ht⟩ := Finset.card_pos.mp (by rw [hsh1]; norm_num)
  rw [Finset.mem_inter, Finset.mem_inter, G.mem_neighborFinset, G.mem_neighborFinset] at ht
  obtain ⟨⟨ht1, ht2⟩, htIso⟩ := ht
  rw [Finset.mem_biUnion]
  refine ⟨t, htIso, ?_⟩
  rw [Finset.mem_offDiag]
  refine ⟨?_, ?_, hne⟩
  · rw [Finset.mem_inter, G.mem_neighborFinset]; exact ⟨ht1.symm, hp1R⟩
  · rw [Finset.mem_inter, G.mem_neighborFinset]; exact ⟨ht2.symm, hp2R⟩

/-- **The non-adjacent rich off-diagonal count is exactly `30` (`e_RR = 6`, `D_adj = 12`).**
The within-`R` degree of the unique iso-degree-`3` hub `w` is `≤ 1`, the others `≤ 2`, so
`D_adj = ∑ ≤ 13`; the share-`1` design caps `D ≤ 30` hence `D_adj ≥ 12`; parity pins `D_adj = 12`,
`D = 30`. -/
theorem rich_D_eq_thirty_eighteen (G : SimpleGraph (Fin 18)) (Hub Iso R : Finset (Fin 18))
    (hdeg4 : ∀ h ∈ Hub, G.degree h = 4)
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdisj : Disjoint Hub Iso) (hIso : Iso.card = 6)
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hno2hub : ¬∃ h₁ h₂ : Fin 18, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card)
    (hRHub : R ⊆ Hub) (hRrich : ∀ a ∈ R, 2 ≤ (G.neighborFinset a ∩ Iso).card)
    (hr7 : R.card = 7) (hS15 : ∑ r ∈ R, (G.neighborFinset r ∩ Iso).card = 15) :
    (R.offDiag.filter (fun p => ¬G.Adj p.1 p.2)).card = 30 := by
  classical
  -- The all-poor twin `t6` and the design `(3,3,3,3,3,0)`.
  obtain ⟨t6, ht6Iso, ht6c0, htdesign⟩ := poor_incidence_concentrates_eighteen G Hub Iso R
    hdeg4 hiso3 hdisj hIso hshare hno2hub hRHub hRrich hr7 hS15
  -- The unique iso-degree-`3` rich hub `w`.
  obtain ⟨w, hwR, hw3, hwoth⟩ := rich_isodeg_seq_eighteen G Iso R hRrich hr7 hS15
  -- `D_adj = ∑_{a∈R} |N(a)∩R|`.
  have hDadjsum := dadj_eq_sum_eighteen G R
  -- Termwise bound: `|N(a)∩R| ≤ 4 - |N(a)∩Iso|`.
  have hterm : ∀ a ∈ R, (G.neighborFinset a ∩ R).card + (G.neighborFinset a ∩ Iso).card ≤ 4 := by
    intro a ha
    have hdisjRI : Disjoint (G.neighborFinset a ∩ R) (G.neighborFinset a ∩ Iso) := by
      apply Finset.disjoint_left.mpr
      intro x hx1 hx2
      exact Finset.disjoint_left.mp hdisj (hRHub (Finset.mem_inter.mp hx1).2)
        (Finset.mem_inter.mp hx2).2
    have hun : (G.neighborFinset a ∩ R) ∪ (G.neighborFinset a ∩ Iso) ⊆ G.neighborFinset a := by
      rw [← Finset.inter_union_distrib_left]; exact Finset.inter_subset_left
    have hle := Finset.card_le_card hun
    rw [Finset.card_union_of_disjoint hdisjRI, G.card_neighborFinset_eq_degree,
      hdeg4 a (hRHub ha)] at hle
    exact hle
  -- `D_adj ≤ 13`.
  have hDadjle : (R.offDiag.filter (fun p => G.Adj p.1 p.2)).card ≤ 13 := by
    have hwbound : (G.neighborFinset w ∩ R).card ≤ 1 := by
      have := hterm w hwR; rw [hw3] at this; omega
    have hobound : ∀ a ∈ R.erase w, (G.neighborFinset a ∩ R).card ≤ 2 := by
      intro a ha; obtain ⟨hne, haR⟩ := Finset.mem_erase.mp ha
      have := hterm a haR; rw [hwoth a haR hne] at this; omega
    have hsumerase : ∑ a ∈ R.erase w, (G.neighborFinset a ∩ R).card ≤ 12 := by
      calc ∑ a ∈ R.erase w, (G.neighborFinset a ∩ R).card ≤ ∑ _a ∈ R.erase w, 2 :=
            Finset.sum_le_sum hobound
        _ = 12 := by
            rw [Finset.sum_const, Finset.card_erase_of_mem hwR, hr7, smul_eq_mul]
    have hae := Finset.add_sum_erase R (fun a => (G.neighborFinset a ∩ R).card) hwR
    rw [hDadjsum, ← hae]; omega
  -- `D ⊆ biUnion`; `card biUnion ≤ 30` via the design.
  have hsub := rich_nonadj_biUnion_eighteen G Hub Iso R hdeg4 hshare hno2hub hRHub hRrich
  have hbiUle : (Iso.biUnion (fun t => (G.neighborFinset t ∩ R).offDiag)).card ≤ 30 := by
    calc (Iso.biUnion (fun t => (G.neighborFinset t ∩ R).offDiag)).card
        ≤ ∑ t ∈ Iso, ((G.neighborFinset t ∩ R).offDiag).card := Finset.card_biUnion_le
      _ = ∑ t ∈ Iso, ((G.neighborFinset t ∩ R).card * (G.neighborFinset t ∩ R).card
            - (G.neighborFinset t ∩ R).card) := by
          apply Finset.sum_congr rfl; intro t _; rw [Finset.offDiag_card]
      _ = 30 := by
          rw [← Finset.add_sum_erase Iso _ ht6Iso, ht6c0]
          have herase : ∑ t ∈ Iso.erase t6, ((G.neighborFinset t ∩ R).card
              * (G.neighborFinset t ∩ R).card - (G.neighborFinset t ∩ R).card)
              = ∑ _t ∈ Iso.erase t6, 6 := by
            apply Finset.sum_congr rfl
            intro t ht
            obtain ⟨htne, htIso⟩ := Finset.mem_erase.mp ht
            rw [htdesign t htIso htne]
          rw [herase, Finset.sum_const, Finset.card_erase_of_mem ht6Iso, hIso, smul_eq_mul]
  have hDle : (R.offDiag.filter (fun p => ¬G.Adj p.1 p.2)).card ≤ 30 :=
    le_trans (Finset.card_le_card hsub) hbiUle
  -- `D + D_adj = 42`.
  have hsplit := offdiag_eq_eighteen G R
  rw [hr7] at hsplit
  -- Parity of `D_adj`.
  obtain ⟨k, hk⟩ := even_dadj_eighteen G R
  omega

/-- **The twins' rich-trace off-diagonals total `≤ 30`** (the `(3,3,3,3,3,0)` design). -/
theorem rich_biUnion_le_thirty_eighteen (G : SimpleGraph (Fin 18)) (Hub Iso R : Finset (Fin 18))
    (hdeg4 : ∀ h ∈ Hub, G.degree h = 4)
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdisj : Disjoint Hub Iso) (hIso : Iso.card = 6)
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hno2hub : ¬∃ h₁ h₂ : Fin 18, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card)
    (hRHub : R ⊆ Hub) (hRrich : ∀ a ∈ R, 2 ≤ (G.neighborFinset a ∩ Iso).card)
    (hr7 : R.card = 7) (hS15 : ∑ r ∈ R, (G.neighborFinset r ∩ Iso).card = 15) :
    (Iso.biUnion (fun t => (G.neighborFinset t ∩ R).offDiag)).card ≤ 30 := by
  classical
  obtain ⟨t6, ht6Iso, ht6c0, htdesign⟩ := poor_incidence_concentrates_eighteen G Hub Iso R
    hdeg4 hiso3 hdisj hIso hshare hno2hub hRHub hRrich hr7 hS15
  calc (Iso.biUnion (fun t => (G.neighborFinset t ∩ R).offDiag)).card
      ≤ ∑ t ∈ Iso, ((G.neighborFinset t ∩ R).offDiag).card := Finset.card_biUnion_le
    _ = ∑ t ∈ Iso, ((G.neighborFinset t ∩ R).card * (G.neighborFinset t ∩ R).card
          - (G.neighborFinset t ∩ R).card) := by
        apply Finset.sum_congr rfl; intro t _; rw [Finset.offDiag_card]
    _ = 30 := by
        rw [← Finset.add_sum_erase Iso _ ht6Iso, ht6c0]
        have herase : ∑ t ∈ Iso.erase t6, ((G.neighborFinset t ∩ R).card
            * (G.neighborFinset t ∩ R).card - (G.neighborFinset t ∩ R).card)
            = ∑ _t ∈ Iso.erase t6, 6 := by
          apply Finset.sum_congr rfl
          intro t ht
          obtain ⟨htne, htIso⟩ := Finset.mem_erase.mp ht
          rw [htdesign t htIso htne]
        rw [herase, Finset.sum_const, Finset.card_erase_of_mem ht6Iso, hIso, smul_eq_mul]

/-- **NODE 1 — the rich triples are pairwise independent.**  For the `r = 7`, `S = 15` design, the
non-adjacent rich off-diagonal has exactly `30` ordered pairs (`rich_D_eq_thirty`), which is the
`biUnion` upper bound; equality forces every rich pair sharing a twin to be a *non-edge*.  Hence the
three rich hubs of any `M`-isolated twin are pairwise non-adjacent. -/
theorem rich_triples_partition_eighteen (G : SimpleGraph (Fin 18)) (Hub Iso R : Finset (Fin 18))
    (hdeg4 : ∀ h ∈ Hub, G.degree h = 4)
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdisj : Disjoint Hub Iso) (hIso : Iso.card = 6)
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hno2hub : ¬∃ h₁ h₂ : Fin 18, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card)
    (hRHub : R ⊆ Hub) (hRrich : ∀ a ∈ R, 2 ≤ (G.neighborFinset a ∩ Iso).card)
    (hr7 : R.card = 7) (hS15 : ∑ r ∈ R, (G.neighborFinset r ∩ Iso).card = 15) :
    ∀ t ∈ Iso, ∀ x ∈ G.neighborFinset t ∩ R, ∀ y ∈ G.neighborFinset t ∩ R, x ≠ y →
      ¬G.Adj x y := by
  classical
  have hD30 := rich_D_eq_thirty_eighteen G Hub Iso R hdeg4 hiso3 hdisj hIso hshare hno2hub
    hRHub hRrich hr7 hS15
  have hsub := rich_nonadj_biUnion_eighteen G Hub Iso R hdeg4 hshare hno2hub hRHub hRrich
  have hbiUle := rich_biUnion_le_thirty_eighteen G Hub Iso R hdeg4 hiso3 hdisj hIso hshare hno2hub
    hRHub hRrich hr7 hS15
  have hDeq : (R.offDiag.filter (fun p => ¬G.Adj p.1 p.2))
      = Iso.biUnion (fun t => (G.neighborFinset t ∩ R).offDiag) :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hD30]; exact hbiUle)
  intro t ht x hx y hy hxy
  have hpair : (x, y) ∈ Iso.biUnion (fun t => (G.neighborFinset t ∩ R).offDiag) := by
    rw [Finset.mem_biUnion]
    exact ⟨t, ht, by rw [Finset.mem_offDiag]; exact ⟨hx, hy, hxy⟩⟩
  rw [← hDeq, Finset.mem_filter] at hpair
  exact hpair.2

/-- **The iso-degree-`3` rich hub `w` has no rich neighbour.**  The three `M`-isolated twins through
`w` carry triples `N(t) ∩ R` that pairwise meet only in `w` (share-`1`); deleting `w` gives three
disjoint pairs that exhaust `R \ {w}`.  Any rich neighbour of `w` would therefore sit in some triple
of `w`, forcing it non-adjacent to `w` (NODE 1) — a contradiction. -/
theorem rich_w_no_rich_nbr_eighteen (G : SimpleGraph (Fin 18)) (Hub Iso R : Finset (Fin 18))
    (hdeg4 : ∀ h ∈ Hub, G.degree h = 4)
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdisj : Disjoint Hub Iso) (hIso : Iso.card = 6)
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hno2hub : ¬∃ h₁ h₂ : Fin 18, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card)
    (hRHub : R ⊆ Hub) (hRrich : ∀ a ∈ R, 2 ≤ (G.neighborFinset a ∩ Iso).card)
    (hr7 : R.card = 7) (hS15 : ∑ r ∈ R, (G.neighborFinset r ∩ Iso).card = 15) :
    ∃ w ∈ R, (G.neighborFinset w ∩ Iso).card = 3 ∧ (G.neighborFinset w ∩ R).card = 0 ∧
      ∀ r ∈ R, r ≠ w → (G.neighborFinset r ∩ Iso).card = 2 := by
  classical
  obtain ⟨t6, ht6Iso, ht6c0, htdesign⟩ := poor_incidence_concentrates_eighteen G Hub Iso R
    hdeg4 hiso3 hdisj hIso hshare hno2hub hRHub hRrich hr7 hS15
  obtain ⟨w, hwR, hw3, hwoth⟩ := rich_isodeg_seq_eighteen G Iso R hRrich hr7 hS15
  have hpw := rich_triples_partition_eighteen G Hub Iso R hdeg4 hiso3 hdisj hIso hshare hno2hub
    hRHub hRrich hr7 hS15
  refine ⟨w, hwR, hw3, ?_, hwoth⟩
  -- Every twin through `w` is all-rich (`|N(t) ∩ R| = 3`).
  have htw3 : ∀ t ∈ G.neighborFinset w ∩ Iso, (G.neighborFinset t ∩ R).card = 3 := by
    intro t ht
    rw [Finset.mem_inter, G.mem_neighborFinset] at ht
    obtain ⟨hwt, htIso⟩ := ht
    have htne : t ≠ t6 := by
      intro he
      have hmem : w ∈ G.neighborFinset t6 ∩ R := by
        rw [Finset.mem_inter, G.mem_neighborFinset]; exact ⟨he ▸ hwt.symm, hwR⟩
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem] at ht6c0
      exact ht6c0 w hmem
    exact htdesign t htIso htne
  -- `w ∈ N(t) ∩ R` for each twin `t` through `w`.
  have hwInTriple : ∀ t ∈ G.neighborFinset w ∩ Iso, w ∈ G.neighborFinset t ∩ R := by
    intro t ht
    rw [Finset.mem_inter, G.mem_neighborFinset] at ht
    rw [Finset.mem_inter, G.mem_neighborFinset]
    exact ⟨ht.1.symm, hwR⟩
  -- The three deleted triples are pairwise disjoint.
  set U : Finset (Fin 18) := (G.neighborFinset w ∩ Iso).biUnion
    (fun t => (G.neighborFinset t ∩ R).erase w) with hUdef
  have hdisjU : ∀ t ∈ G.neighborFinset w ∩ Iso, ∀ t' ∈ G.neighborFinset w ∩ Iso, t ≠ t' →
      Disjoint ((G.neighborFinset t ∩ R).erase w) ((G.neighborFinset t' ∩ R).erase w) := by
    intro t ht t' ht' htt'
    apply Finset.disjoint_left.mpr
    intro y hy hy'
    obtain ⟨hyw, hyt⟩ := Finset.mem_erase.mp hy
    obtain ⟨_, hyt'⟩ := Finset.mem_erase.mp hy'
    -- `y, w` non-adjacent and share both `t, t'`, contradicting share-`1`.
    have hyR : y ∈ R := (Finset.mem_inter.mp hyt).2
    have hnadj : ¬G.Adj y w := hpw t (Finset.mem_inter.mp ht).2 y hyt w (hwInTriple t ht) hyw
    have hyHub := hRHub hyR
    have hsh1 := rich_nonadj_share_eq_one G Hub Iso hshare hno2hub y w hyHub (hRHub hwR)
      (hdeg4 y hyHub) (hdeg4 w (hRHub hwR)) hyw hnadj (hRrich y hyR) (hRrich w hwR)
    -- But `t, t'` are two distinct common twins.
    have htmem : t ∈ G.neighborFinset y ∩ G.neighborFinset w ∩ Iso := by
      rw [Finset.mem_inter, Finset.mem_inter, G.mem_neighborFinset, G.mem_neighborFinset]
      exact ⟨⟨((G.mem_neighborFinset _ _).mp (Finset.mem_inter.mp hyt).1).symm,
        (G.mem_neighborFinset _ _).mp (Finset.mem_inter.mp ht).1⟩,
        (Finset.mem_inter.mp ht).2⟩
    have ht'mem : t' ∈ G.neighborFinset y ∩ G.neighborFinset w ∩ Iso := by
      rw [Finset.mem_inter, Finset.mem_inter, G.mem_neighborFinset, G.mem_neighborFinset]
      exact ⟨⟨((G.mem_neighborFinset _ _).mp (Finset.mem_inter.mp hyt').1).symm,
        (G.mem_neighborFinset _ _).mp (Finset.mem_inter.mp ht').1⟩,
        (Finset.mem_inter.mp ht').2⟩
    have h2le : 2 ≤ (G.neighborFinset y ∩ G.neighborFinset w ∩ Iso).card := by
      have hsub2 : ({t, t'} : Finset (Fin 18)) ⊆ G.neighborFinset y ∩ G.neighborFinset w ∩ Iso := by
        intro z hz
        rw [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl
        · exact htmem
        · exact ht'mem
      calc 2 = ({t, t'} : Finset (Fin 18)).card := by
            rw [Finset.card_insert_of_notMem (by simp [htt']), Finset.card_singleton]
        _ ≤ _ := Finset.card_le_card hsub2
    omega
  -- `|U| = 6`.
  have hUcard : U.card = 6 := by
    rw [hUdef, Finset.card_biUnion hdisjU]
    have : ∑ t ∈ G.neighborFinset w ∩ Iso, ((G.neighborFinset t ∩ R).erase w).card
        = ∑ _t ∈ G.neighborFinset w ∩ Iso, 2 := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [Finset.card_erase_of_mem (hwInTriple t ht), htw3 t ht]
    rw [this, Finset.sum_const, hw3, smul_eq_mul]
  -- `U ⊆ R.erase w`.
  have hUsub : U ⊆ R.erase w := by
    intro y hy
    rw [hUdef, Finset.mem_biUnion] at hy
    obtain ⟨t, _, hyt⟩ := hy
    obtain ⟨hyw, hytR⟩ := Finset.mem_erase.mp hyt
    exact Finset.mem_erase.mpr ⟨hyw, (Finset.mem_inter.mp hytR).2⟩
  have hUeq : U = R.erase w := by
    apply Finset.eq_of_subset_of_card_le hUsub
    rw [Finset.card_erase_of_mem hwR, hr7, hUcard]
  -- Conclude `N(w) ∩ R = ∅`.
  rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro x hx
  rw [Finset.mem_inter, G.mem_neighborFinset] at hx
  obtain ⟨hwx, hxR⟩ := hx
  have hxw : x ≠ w := fun he => G.irrefl (he ▸ hwx)
  have hxU : x ∈ U := by rw [hUeq]; exact Finset.mem_erase.mpr ⟨hxw, hxR⟩
  rw [hUdef, Finset.mem_biUnion] at hxU
  obtain ⟨t, ht, hxt⟩ := hxU
  obtain ⟨_, hxtR⟩ := Finset.mem_erase.mp hxt
  have hnadj : ¬G.Adj x w := hpw t (Finset.mem_inter.mp ht).2 x hxtR w (hwInTriple t ht) hxw
  exact hnadj hwx.symm

/-- **NODE 2 — the six iso-degree-`2` rich hubs are saturated.**  With `e_RR = 6` (`D = 30`) and the
iso-degree-`3` hub `w` carrying no rich edge, the within-`R` degree mass `12` is split evenly among
the other six rich hubs (`2` each).  Each then has `|N ∩ Iso| + |N ∩ R| = 4 = deg`, so its whole
neighbourhood lies in `Iso ∪ R`: it meets no `M`-edge endpoint and only rich hubs. -/
theorem rich_saturated_eighteen (G : SimpleGraph (Fin 18)) (Hub Iso R : Finset (Fin 18))
    (hdeg4 : ∀ h ∈ Hub, G.degree h = 4)
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdisj : Disjoint Hub Iso) (hIso : Iso.card = 6)
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hno2hub : ¬∃ h₁ h₂ : Fin 18, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card)
    (hRHub : R ⊆ Hub) (hRrich : ∀ a ∈ R, 2 ≤ (G.neighborFinset a ∩ Iso).card)
    (hr7 : R.card = 7) (hS15 : ∑ r ∈ R, (G.neighborFinset r ∩ Iso).card = 15) :
    ∃ w ∈ R, (G.neighborFinset w ∩ Iso).card = 3 ∧ (G.neighborFinset w ∩ R).card = 0 ∧
      ∀ r ∈ R, r ≠ w → G.neighborFinset r ⊆ Iso ∪ R := by
  classical
  obtain ⟨w, hwR, hw3, hw0, hwoth⟩ := rich_w_no_rich_nbr_eighteen G Hub Iso R hdeg4 hiso3 hdisj
    hIso hshare hno2hub hRHub hRrich hr7 hS15
  refine ⟨w, hwR, hw3, hw0, ?_⟩
  -- The degree split `|N(a)∩R| + |N(a)∩Iso| ≤ 4`.
  have hterm : ∀ a ∈ R, (G.neighborFinset a ∩ R).card + (G.neighborFinset a ∩ Iso).card = 4 ∨
      (G.neighborFinset a ∩ R).card + (G.neighborFinset a ∩ Iso).card ≤ 4 := by
    intro a ha; right
    have hdisjRI : Disjoint (G.neighborFinset a ∩ R) (G.neighborFinset a ∩ Iso) := by
      apply Finset.disjoint_left.mpr
      intro x hx1 hx2
      exact Finset.disjoint_left.mp hdisj (hRHub (Finset.mem_inter.mp hx1).2)
        (Finset.mem_inter.mp hx2).2
    have hun : (G.neighborFinset a ∩ R) ∪ (G.neighborFinset a ∩ Iso) ⊆ G.neighborFinset a := by
      rw [← Finset.inter_union_distrib_left]; exact Finset.inter_subset_left
    have hle := Finset.card_le_card hun
    rw [Finset.card_union_of_disjoint hdisjRI, G.card_neighborFinset_eq_degree,
      hdeg4 a (hRHub ha)] at hle
    exact hle
  have htermle : ∀ a ∈ R, (G.neighborFinset a ∩ R).card ≤ 2 := by
    intro a ha
    rcases hterm a ha with h | h <;> · have := hRrich a ha; omega
  -- `D_adj = 12` and `D_adj = ∑_{a∈R} |N(a)∩R|`.
  have hD30 := rich_D_eq_thirty_eighteen G Hub Iso R hdeg4 hiso3 hdisj hIso hshare hno2hub
    hRHub hRrich hr7 hS15
  have hsplit := offdiag_eq_eighteen G R
  rw [hr7] at hsplit
  have hDadjsum := dadj_eq_sum_eighteen G R
  have hRsum12 : ∑ a ∈ R, (G.neighborFinset a ∩ R).card = 12 := by
    rw [← hDadjsum]; omega
  -- The other six rich hubs each have within-`R` degree exactly `2`.
  have heach : ∀ r ∈ R, r ≠ w → (G.neighborFinset r ∩ R).card = 2 := by
    intro r hrR hrw
    have hrerase : r ∈ R.erase w := Finset.mem_erase.mpr ⟨hrw, hrR⟩
    -- `∑_{R.erase w} = 12`.
    have hae := Finset.add_sum_erase R (fun a => (G.neighborFinset a ∩ R).card) hwR
    rw [hw0] at hae
    have hsumE : ∑ a ∈ R.erase w, (G.neighborFinset a ∩ R).card = 12 := by omega
    -- Peel `r`.
    have hae2 := Finset.add_sum_erase (R.erase w) (fun a => (G.neighborFinset a ∩ R).card) hrerase
    have hrest : ∑ a ∈ (R.erase w).erase r, (G.neighborFinset a ∩ R).card ≤ 10 := by
      have hcardE : ((R.erase w).erase r).card = 5 := by
        rw [Finset.card_erase_of_mem hrerase, Finset.card_erase_of_mem hwR, hr7]
      calc ∑ a ∈ (R.erase w).erase r, (G.neighborFinset a ∩ R).card
          ≤ ∑ _a ∈ (R.erase w).erase r, 2 := by
            apply Finset.sum_le_sum
            intro a ha
            exact htermle a (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase ha))
        _ = 10 := by rw [Finset.sum_const, hcardE, smul_eq_mul]
    have hrge : 2 ≤ (G.neighborFinset r ∩ R).card := by omega
    have := htermle r hrR
    omega
  -- Saturation: `N(r) ⊆ Iso ∪ R`.
  intro r hrR hrw x hx
  have hr2 : (G.neighborFinset r ∩ R).card = 2 := heach r hrR hrw
  have hi2 : (G.neighborFinset r ∩ Iso).card = 2 := hwoth r hrR hrw
  have hdisjRI : Disjoint (G.neighborFinset r ∩ R) (G.neighborFinset r ∩ Iso) := by
    apply Finset.disjoint_left.mpr
    intro y hy1 hy2
    exact Finset.disjoint_left.mp hdisj (hRHub (Finset.mem_inter.mp hy1).2)
      (Finset.mem_inter.mp hy2).2
  have hun : (G.neighborFinset r ∩ R) ∪ (G.neighborFinset r ∩ Iso) ⊆ G.neighborFinset r := by
    rw [← Finset.inter_union_distrib_left]; exact Finset.inter_subset_left
  have hcardun : ((G.neighborFinset r ∩ R) ∪ (G.neighborFinset r ∩ Iso)).card = 4 := by
    rw [Finset.card_union_of_disjoint hdisjRI, hr2, hi2]
  have hNcard : (G.neighborFinset r).card = 4 := by
    rw [G.card_neighborFinset_eq_degree, hdeg4 r (hRHub hrR)]
  have heqN : (G.neighborFinset r ∩ R) ∪ (G.neighborFinset r ∩ Iso) = G.neighborFinset r :=
    Finset.eq_of_subset_of_card_le hun (by rw [hNcard, hcardun])
  rw [← heqN, Finset.mem_union, Finset.mem_inter, Finset.mem_inter] at hx
  rw [Finset.mem_union]
  tauto

/-- **NODE 3 — the `M`-partner kill (`r = 7`, `S = 15`).**  An `M`-edge endpoint `z` meeting two
poor hubs `hg₁, hg₂` (residual regime `hres`).  Saturation (NODE 2) forces the `M`-partner `z'` to
meet exactly the iso-degree-`3` rich hub `w` and the third poor hub `g₃ = N(t₆) ∖ {hg₁, hg₂}`; the
three poor hubs form a triangle, and `hg₁ – g₃ – z' – z` is a good `C₄` of degree sum
`4 + 4 + 3 + 3 = 14`, excluded by `hC4`. -/
theorem mpartner_meets_poor_eighteen (G : SimpleGraph (Fin 18)) (Hub Iso : Finset (Fin 18))
    (hdeg4 : ∀ h ∈ Hub, G.degree h = 4)
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdisj : Disjoint Hub Iso) (hHub : Hub.card = 10) (hIso : Iso.card = 6)
    (hdeg3 : ∀ v : Fin 18, 3 ≤ G.degree v) (hisodeg3 : ∀ t ∈ Iso, G.degree t = 3)
    (hdsum : ∑ w ∈ Hub, G.degree w = 40)
    (hleak : ∑ h ∈ Hub, (G.neighborFinset h ∩ (Finset.univ \ (Hub ∪ Iso))).card ≤ 4)
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hno2hub : ¬∃ h₁ h₂ : Fin 18, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card)
    (hC4 : ¬∃ a b c d : Fin 18, ({a, b, c, d} : Finset (Fin 18)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (_hK23 : ¬∃ a b c d e : Fin 18, ({a, b, c, d, e} : Finset (Fin 18)).card = 5 ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
      G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 19)
    (hT : ¬∃ x y z : Fin 18, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧
      G.degree x + G.degree y + G.degree z ≤ 10)
    (z : Fin 18) (hz : z ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 18)))
    (hg1 : Fin 18) (hg2 : Fin 18) (hg1ne : hg1 ≠ hg2)
    (hg1mem : hg1 ∈ G.neighborFinset z ∩ Hub) (hg2mem : hg2 ∈ G.neighborFinset z ∩ Hub)
    (hg1poor : (G.neighborFinset hg1 ∩ Iso).card ≤ 1)
    (hg2poor : (G.neighborFinset hg2 ∩ Iso).card ≤ 1)
    (hres : G.Adj hg1 hg2 ∨ (G.neighborFinset hg1 ∩ G.neighborFinset hg2 ∩ Iso).card = 0)
    (hr7 : (Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)).card = 7)
    (hS15 : ∑ r ∈ Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card),
        (G.neighborFinset r ∩ Iso).card = 15) :
    False := by
  classical
  set Z : Finset (Fin 18) := Finset.univ \ (Hub ∪ Iso) with hZdef
  set R : Finset (Fin 18) := Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card) with hRdef
  have hRHub : R ⊆ Hub := Finset.filter_subset _ _
  have hRrich : ∀ a ∈ R, 2 ≤ (G.neighborFinset a ∩ Iso).card := by
    intro a ha; rw [hRdef, Finset.mem_filter] at ha; exact ha.2
  -- Saturation (NODE 2).
  obtain ⟨w, hwR, hw3, hw0, hsat⟩ := rich_saturated_eighteen G Hub Iso R hdeg4 hiso3 hdisj hIso
    hshare hno2hub hRHub hRrich hr7 hS15
  have hwHub : w ∈ Hub := hRHub hwR
  -- The all-poor twin `t6` and design.
  obtain ⟨t6, ht6Iso, ht6c0, _⟩ := poor_incidence_concentrates_eighteen G Hub Iso R
    hdeg4 hiso3 hdisj hIso hshare hno2hub hRHub hRrich hr7 hS15
  -- `Z = {z, z'}` with `z'` the `M`-partner.
  have hZcard : Z.card = 2 := z_card_two_eighteen Hub Iso hdisj hHub hIso
  have hzerase : (Z.erase z).card = 1 := by rw [Finset.card_erase_of_mem hz, hZcard]
  obtain ⟨zp, hzp⟩ := Finset.card_eq_one.mp hzerase
  have hzpZe : zp ∈ Z.erase z := by rw [hzp]; exact Finset.mem_singleton_self _
  have hzpZ : zp ∈ Z := Finset.mem_of_mem_erase hzpZe
  have hzpz : zp ≠ z := (Finset.mem_erase.mp hzpZe).1
  have hZpair : Z = {z, zp} := by
    refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hz
      · rw [Finset.mem_singleton] at hx; subst hx; exact hzpZ
    · rw [hZcard, Finset.card_insert_of_notMem (by simp [Ne.symm hzpz]), Finset.card_singleton]
  -- Basic `Z`-vertex facts for `z` and `zp`.
  obtain ⟨hziso0, hzhub2, hzdeg3⟩ := z_two_hub_nbrs_eighteen G Hub Iso hiso3 hdisj hHub hIso hdsum
    hdeg3 hisodeg3 hleak z hz
  obtain ⟨hzpiso0, hzphub2, hzpdeg3⟩ := z_two_hub_nbrs_eighteen G Hub Iso hiso3 hdisj hHub hIso
    hdsum hdeg3 hisodeg3 hleak zp hzpZ
  have hznotHub : z ∉ Hub := by
    rw [hZdef, Finset.mem_sdiff, Finset.mem_union, not_or] at hz; exact hz.2.1
  have hznotIso : z ∉ Iso := by
    rw [hZdef, Finset.mem_sdiff, Finset.mem_union, not_or] at hz; exact hz.2.2
  have hzpnotHub : zp ∉ Hub := by
    rw [hZdef, Finset.mem_sdiff, Finset.mem_union, not_or] at hzpZ; exact hzpZ.2.1
  have hzpnotIso : zp ∉ Iso := by
    rw [hZdef, Finset.mem_sdiff, Finset.mem_union, not_or] at hzpZ; exact hzpZ.2.2
  -- `z ~ zp` (the `M`-edge): `z` has exactly one `Z`-neighbour.
  have hzZ1 : (G.neighborFinset z ∩ Z).card = 1 := by
    have hsp := nbr_split_three_eighteen G Hub Iso hdisj z
    rw [← hZdef] at hsp; omega
  have hzzp : G.Adj z zp := by
    obtain ⟨u, hu⟩ := Finset.card_eq_one.mp hzZ1
    have humem : u ∈ G.neighborFinset z ∩ Z := by rw [hu]; exact Finset.mem_singleton_self _
    have huZ : u ∈ Z := (Finset.mem_inter.mp humem).2
    have huN : u ∈ G.neighborFinset z := (Finset.mem_inter.mp humem).1
    have huz : u ≠ z := fun he => G.irrefl (by rw [he] at huN; exact (G.mem_neighborFinset z z).mp huN)
    rw [hZpair, Finset.mem_insert, Finset.mem_singleton] at huZ
    rcases huZ with rfl | rfl
    · exact absurd rfl huz
    · exact (G.mem_neighborFinset z u).mp huN
  -- Poor hub set `P = N(t6) = {hg1, hg2, g3}`.
  set P : Finset (Fin 18) := Hub.filter (fun h => ¬ 2 ≤ (G.neighborFinset h ∩ Iso).card) with hPdef
  have hPcard : P.card = 3 := by
    have := Finset.card_filter_add_card_filter_not (s := Hub)
      (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)
    rw [← hRdef, ← hPdef, hHub, hr7] at this; omega
  have hg1Hub : hg1 ∈ Hub := (Finset.mem_inter.mp hg1mem).2
  have hg2Hub : hg2 ∈ Hub := (Finset.mem_inter.mp hg2mem).2
  have hg1P : hg1 ∈ P := by rw [hPdef, Finset.mem_filter]; exact ⟨hg1Hub, by omega⟩
  have hg2P : hg2 ∈ P := by rw [hPdef, Finset.mem_filter]; exact ⟨hg2Hub, by omega⟩
  -- `N(t6) ⊆ Hub`, all poor, `|N(t6)| = 3`, so `N(t6) = P`.
  have ht6sub : G.neighborFinset t6 ⊆ Hub := by
    have hcard3 : (G.neighborFinset t6 ∩ Hub).card = 3 := hiso3 t6 ht6Iso
    have hdt : (G.neighborFinset t6).card = 3 := by
      rw [G.card_neighborFinset_eq_degree]; exact hisodeg3 t6 ht6Iso
    have heq : G.neighborFinset t6 ∩ Hub = G.neighborFinset t6 :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by rw [hcard3, hdt])
    rw [← heq]; exact Finset.inter_subset_right
  have ht6P : G.neighborFinset t6 ⊆ P := by
    intro x hx
    have hxHub := ht6sub hx
    rw [hPdef, Finset.mem_filter]
    refine ⟨hxHub, ?_⟩
    intro hxrich
    have hxR : x ∈ R := by rw [hRdef, Finset.mem_filter]; exact ⟨hxHub, hxrich⟩
    have : x ∈ G.neighborFinset t6 ∩ R := Finset.mem_inter.mpr ⟨hx, hxR⟩
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem] at ht6c0
    exact ht6c0 x this
  have ht6eqP : G.neighborFinset t6 = P := by
    apply Finset.eq_of_subset_of_card_le ht6P
    have hdt : (G.neighborFinset t6).card = 3 := by
      rw [G.card_neighborFinset_eq_degree]; exact hisodeg3 t6 ht6Iso
    rw [hPcard, hdt]
  -- `g3` the third poor hub.
  have hsub12 : ({hg1, hg2} : Finset (Fin 18)) ⊆ P := by
    intro x hx
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hg1P
    · exact hg2P
  have hg3ex : (P \ {hg1, hg2}).card = 1 := by
    have h2 : ({hg1, hg2} : Finset (Fin 18)).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simp [hg1ne]), Finset.card_singleton]
    have hadd := Finset.card_sdiff_add_card_inter P ({hg1, hg2} : Finset (Fin 18))
    have hPinter : P ∩ ({hg1, hg2} : Finset (Fin 18)) = {hg1, hg2} :=
      Finset.inter_eq_right.mpr hsub12
    rw [hPinter, hPcard, h2] at hadd
    omega
  obtain ⟨g3, hg3⟩ := Finset.card_eq_one.mp hg3ex
  have hg3mem : g3 ∈ P \ {hg1, hg2} := by rw [hg3]; exact Finset.mem_singleton_self _
  have hg3P : g3 ∈ P := (Finset.mem_sdiff.mp hg3mem).1
  have hg3not : g3 ∉ ({hg1, hg2} : Finset (Fin 18)) := (Finset.mem_sdiff.mp hg3mem).2
  have hg3hg1 : g3 ≠ hg1 := by
    intro he; exact hg3not (by rw [he]; exact Finset.mem_insert_self _ _)
  have hg3hg2 : g3 ≠ hg2 := by
    intro he
    exact hg3not (by rw [he]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have hg3Hub : g3 ∈ Hub := by rw [hPdef, Finset.mem_filter] at hg3P; exact hg3P.1
  have hg3poor : (G.neighborFinset g3 ∩ Iso).card ≤ 1 := by
    rw [hPdef, Finset.mem_filter] at hg3P; omega
  -- `P = {hg1, hg2, g3}`.
  have hPset : P = {hg1, hg2, g3} := by
    refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
    · intro x hx
      rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      exacts [hg1P, hg2P, hg3P]
    · rw [hPcard, Finset.card_insert_of_notMem (by simp [hg1ne, Ne.symm hg3hg1]),
        Finset.card_insert_of_notMem (by simp [Ne.symm hg3hg2]), Finset.card_singleton]
  -- Each poor hub meets `t6` (since `N(t6) = P`).
  have hpoorMeetT6 : ∀ p ∈ P, G.Adj p t6 := by
    intro p hp
    rw [← ht6eqP] at hp
    exact ((G.mem_neighborFinset t6 p).mp hp).symm
  -- `zp`'s two hub-neighbours are exactly `{w, g3}`.  Saturation excludes the iso-degree-`2` rich
  -- hubs (no `Z`-slot); `no_hub_adj_both` excludes `hg1, hg2` (they meet `z`); only `w`, `g3` remain.
  have hzpHubsub : G.neighborFinset zp ∩ Hub ⊆ ({w, g3} : Finset (Fin 18)) := by
    intro g hg
    have hgHub : g ∈ Hub := (Finset.mem_inter.mp hg).2
    have hzpg : G.Adj zp g := (G.mem_neighborFinset _ _).mp (Finset.mem_inter.mp hg).1
    by_cases hgrich : 2 ≤ (G.neighborFinset g ∩ Iso).card
    · have hgR : g ∈ R := by rw [hRdef, Finset.mem_filter]; exact ⟨hgHub, hgrich⟩
      have hgw : g = w := by
        by_contra hne
        have hzping : zp ∈ G.neighborFinset g := (G.mem_neighborFinset g zp).mpr hzpg.symm
        have hmem := hsat g hgR hne hzping
        rw [Finset.mem_union] at hmem
        rcases hmem with h | h
        · exact hzpnotIso h
        · exact hzpnotHub (hRHub h)
      rw [Finset.mem_insert, Finset.mem_singleton]; exact Or.inl hgw
    · have hgP : g ∈ P := by rw [hPdef, Finset.mem_filter]; exact ⟨hgHub, hgrich⟩
      rw [hPset, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hgP
      rw [Finset.mem_insert, Finset.mem_singleton]
      rcases hgP with h | h | h
      · exfalso
        have hzg : G.Adj z hg1 := (G.mem_neighborFinset z hg1).mp (Finset.mem_inter.mp hg1mem).1
        rw [h] at hzpg
        exact no_hub_adj_both_mends_eighteen G Hub Iso hdeg4 hiso3 hdisj hHub hIso hdsum hdeg3
          hisodeg3 hleak hT hg1 hg1Hub z hz zp hzpZ (Ne.symm hzpz) ⟨hzg.symm, hzpg.symm⟩
      · exfalso
        have hzg : G.Adj z hg2 := (G.mem_neighborFinset z hg2).mp (Finset.mem_inter.mp hg2mem).1
        rw [h] at hzpg
        exact no_hub_adj_both_mends_eighteen G Hub Iso hdeg4 hiso3 hdisj hHub hIso hdsum hdeg3
          hisodeg3 hleak hT hg2 hg2Hub z hz zp hzpZ (Ne.symm hzpz) ⟨hzg.symm, hzpg.symm⟩
      · exact Or.inr h
  have hwg3ne : w ≠ g3 := by intro he; rw [he] at hw3; omega
  have hwg3card : ({w, g3} : Finset (Fin 18)).card = 2 := by
    rw [Finset.card_insert_of_notMem (by rw [Finset.mem_singleton]; exact hwg3ne),
      Finset.card_singleton]
  have hzpHubeq : G.neighborFinset zp ∩ Hub = ({w, g3} : Finset (Fin 18)) :=
    Finset.eq_of_subset_of_card_le hzpHubsub (le_of_eq (by rw [hwg3card, hzphub2]))
  have hzpw : G.Adj zp w := by
    have hmem : w ∈ G.neighborFinset zp ∩ Hub := by
      rw [hzpHubeq, Finset.mem_insert]; exact Or.inl rfl
    exact (G.mem_neighborFinset zp w).mp (Finset.mem_inter.mp hmem).1
  have hg3second : G.Adj zp g3 := by
    have hmem : g3 ∈ G.neighborFinset zp ∩ Hub := by
      rw [hzpHubeq, Finset.mem_insert, Finset.mem_singleton]; exact Or.inr rfl
    exact (G.mem_neighborFinset zp g3).mp (Finset.mem_inter.mp hmem).1
  -- `N(w) \ Iso = {zp}`: `w`'s only non-twin neighbour is `zp`.
  have hwN : ∀ p, p ∈ G.neighborFinset w → p ∉ Iso → p = zp := by
    have hwsdiff : (G.neighborFinset w \ Iso).card = 1 := by
      have hcs := Finset.card_inter_add_card_sdiff (G.neighborFinset w) Iso
      have hwd : (G.neighborFinset w).card = 4 := by
        rw [G.card_neighborFinset_eq_degree, hdeg4 w hwHub]
      rw [hwd] at hcs; omega
    have hzpinw : zp ∈ G.neighborFinset w \ Iso :=
      Finset.mem_sdiff.mpr ⟨(G.mem_neighborFinset w zp).mpr hzpw.symm, hzpnotIso⟩
    intro p hp hpIso
    have hpw : p ∈ G.neighborFinset w \ Iso := Finset.mem_sdiff.mpr ⟨hp, hpIso⟩
    exact Finset.card_le_one.mp (le_of_eq hwsdiff) p hpw zp hzpinw
  -- `Adj hg1 g3`: count `hg1`'s three non-`t6` neighbours.
  have hg1t6 : G.Adj hg1 t6 := hpoorMeetT6 hg1 hg1P
  have hg1iso1 : (G.neighborFinset hg1 ∩ Iso).card = 1 := by
    have ht6in : t6 ∈ G.neighborFinset hg1 ∩ Iso :=
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset hg1 t6).mpr hg1t6, ht6Iso⟩
    have h1 : 1 ≤ (G.neighborFinset hg1 ∩ Iso).card := Finset.card_pos.mpr ⟨t6, ht6in⟩
    omega
  have hg1sdiff : (G.neighborFinset hg1 \ Iso).card = 3 := by
    have hcs := Finset.card_inter_add_card_sdiff (G.neighborFinset hg1) Iso
    have hd : (G.neighborFinset hg1).card = 4 := by
      rw [G.card_neighborFinset_eq_degree, hdeg4 hg1 hg1Hub]
    rw [hd, hg1iso1] at hcs; omega
  have hsubset : G.neighborFinset hg1 \ Iso ⊆ ({hg2, g3, z} : Finset (Fin 18)) := by
    intro x hx
    rw [Finset.mem_sdiff] at hx
    obtain ⟨hxN, hxIso⟩ := hx
    have hadjx : G.Adj hg1 x := (G.mem_neighborFinset hg1 x).mp hxN
    by_cases hxHub : x ∈ Hub
    · by_cases hxrich : 2 ≤ (G.neighborFinset x ∩ Iso).card
      · have hxR : x ∈ R := by rw [hRdef, Finset.mem_filter]; exact ⟨hxHub, hxrich⟩
        have hg1inx : hg1 ∈ G.neighborFinset x := (G.mem_neighborFinset x hg1).mpr hadjx.symm
        by_cases hxw : x = w
        · exfalso
          have heq : hg1 = zp :=
            hwN hg1 (by rw [← hxw]; exact hg1inx)
              (fun hh => Finset.disjoint_left.mp hdisj hg1Hub hh)
          exact hzpnotHub (heq ▸ hg1Hub)
        · exfalso
          have hmem := hsat x hxR hxw hg1inx
          rw [Finset.mem_union] at hmem
          rcases hmem with h | h
          · exact Finset.disjoint_left.mp hdisj hg1Hub h
          · rw [hRdef, Finset.mem_filter] at h; have := h.2; omega
      · have hxP : x ∈ P := by rw [hPdef, Finset.mem_filter]; exact ⟨hxHub, hxrich⟩
        rw [hPset, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hxP
        have hxne1 : x ≠ hg1 := fun he => G.irrefl (by rw [he] at hadjx; exact hadjx)
        rcases hxP with h | h | h
        · exact absurd h hxne1
        · rw [Finset.mem_insert]; exact Or.inl h
        · rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton]; exact Or.inr (Or.inl h)
    · have hxZ : x ∈ Z := by
        rw [hZdef, Finset.mem_sdiff, Finset.mem_union, not_or]
        exact ⟨Finset.mem_univ _, hxHub, hxIso⟩
      rw [hZpair, Finset.mem_insert, Finset.mem_singleton] at hxZ
      rcases hxZ with hxe | hxe
      · rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton]; exact Or.inr (Or.inr hxe)
      · exfalso
        rw [hxe] at hadjx
        have hzg1 : G.Adj z hg1 := (G.mem_neighborFinset z hg1).mp (Finset.mem_inter.mp hg1mem).1
        exact no_hub_adj_both_mends_eighteen G Hub Iso hdeg4 hiso3 hdisj hHub hIso hdsum hdeg3
          hisodeg3 hleak hT hg1 hg1Hub z hz zp hzpZ (Ne.symm hzpz) ⟨hzg1.symm, hadjx⟩
  have hcard3 : ({hg2, g3, z} : Finset (Fin 18)).card = 3 := by
    have hne1 : hg2 ∉ ({g3, z} : Finset (Fin 18)) := by
      rw [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun he => hg3hg2 he.symm, fun he => hznotHub (he ▸ hg2Hub)⟩
    have hne2 : g3 ∉ ({z} : Finset (Fin 18)) := by
      rw [Finset.mem_singleton]; exact fun he => hznotHub (he ▸ hg3Hub)
    rw [Finset.card_insert_of_notMem hne1, Finset.card_insert_of_notMem hne2, Finset.card_singleton]
  have hsetEq : G.neighborFinset hg1 \ Iso = ({hg2, g3, z} : Finset (Fin 18)) :=
    Finset.eq_of_subset_of_card_le hsubset (le_of_eq (by rw [hcard3, hg1sdiff]))
  have he1 : G.Adj hg1 g3 := by
    have hg3in : g3 ∈ G.neighborFinset hg1 \ Iso := by
      rw [hsetEq, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton]
      exact Or.inr (Or.inl rfl)
    exact (G.mem_neighborFinset hg1 g3).mp (Finset.mem_sdiff.mp hg3in).1
  -- Diagonals via `no_hub_adj_both_mends`.
  have hd1 : ¬G.Adj hg1 zp := by
    intro hadj
    have hzg1 : G.Adj z hg1 := (G.mem_neighborFinset z hg1).mp (Finset.mem_inter.mp hg1mem).1
    exact no_hub_adj_both_mends_eighteen G Hub Iso hdeg4 hiso3 hdisj hHub hIso hdsum hdeg3
      hisodeg3 hleak hT hg1 hg1Hub z hz zp hzpZ (Ne.symm hzpz) ⟨hzg1.symm, hadj⟩
  have hd2 : ¬G.Adj g3 z := by
    intro hadj
    exact no_hub_adj_both_mends_eighteen G Hub Iso hdeg4 hiso3 hdisj hHub hIso hdsum hdeg3
      hisodeg3 hleak hT g3 hg3Hub z hz zp hzpZ (Ne.symm hzpz) ⟨hadj, hg3second.symm⟩
  -- Assemble the good `C₄`  `hg1 – g3 – zp – z`.
  have hcard4 : ({hg1, g3, zp, z} : Finset (Fin 18)).card = 4 := by
    rw [Finset.card_eq_four]
    exact ⟨hg1, g3, zp, z, Ne.symm hg3hg1, fun he => hzpnotHub (he ▸ hg1Hub),
      fun he => hznotHub (he ▸ hg1Hub), fun he => hzpnotHub (he ▸ hg3Hub),
      fun he => hznotHub (he ▸ hg3Hub), hzpz, rfl⟩
  have he4 : G.Adj z hg1 := (G.mem_neighborFinset z hg1).mp (Finset.mem_inter.mp hg1mem).1
  exact low_rich_c4_assemble_eighteen G hg1 g3 zp z (hdeg4 hg1 hg1Hub) (hdeg4 g3 hg3Hub)
    hzpdeg3 hzdeg3 hcard4 he1 hg3second.symm hzzp.symm he4 hd1 hd2 hC4

end N18

end ACMax
