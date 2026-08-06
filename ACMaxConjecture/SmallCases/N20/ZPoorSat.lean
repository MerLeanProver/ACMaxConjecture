import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N20.Core
import ACMaxConjecture.SmallCases.N20.TwoHubSelect
import ACMaxConjecture.SmallCases.N20.StarTriangleStruct
import ACMaxConjecture.SmallCases.N20.RichCount
import ACMaxConjecture.SmallCases.N20.Align8Helpers
import ACMaxConjecture.SmallCases.N20.ZPoorN3
import ACMaxConjecture.SmallCases.N20.ZPoorR7
import ACMaxConjecture.SmallCases.N20.ZVertex
import ACMaxConjecture.SmallCases.N20.ZPoorCut

/-!
# The `r = 7`, `S = 15` saturation chain closing the main residual (`n = 20`)

For the tight `e(M) = 1`, all-degree-`4`, `(|Hub|, |Iso|) = (12, 6)` profile with seven rich hubs
and rich iso-incidence sum `S = 15`, the poor incidences concentrate as `(3,3,3,3,3,0)`
(`poor_incidence_concentrates_twenty`).  This file carries the saturation chain that turns that
design into the good `C₄`/`K₂,₃` kill.  At `n = 20` the poor side has `|P| = 5` (vs `4` for
`n = 19`), so two poor hubs may be iso-degree-`0`; the `M`-partner node handles that new residual
via a good triangle / `K₂,₃` dichotomy.
-/

namespace ACMax

open scoped Classical

namespace N20

/-- **The ordered adjacent off-diagonal count equals the within-set degree sum.** -/
theorem dadj_eq_sum_twenty (G : SimpleGraph (Fin 20)) (R : Finset (Fin 20)) :
    (R.offDiag.filter (fun p => G.Adj p.1 p.2)).card
      = ∑ a ∈ R, (G.neighborFinset a ∩ R).card := by
  classical
  set Dadj : Finset (Fin 20 × Fin 20) := R.offDiag.filter (fun p => G.Adj p.1 p.2) with hDdef
  have hmaps : (Dadj : Set (Fin 20 × Fin 20)).MapsTo Prod.fst R := by
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
theorem even_dadj_twenty (G : SimpleGraph (Fin 20)) (R : Finset (Fin 20)) :
    Even (R.offDiag.filter (fun p => G.Adj p.1 p.2)).card := by
  classical
  set S : Finset (Fin 20 × Fin 20) := R.offDiag.filter (fun p => G.Adj p.1 p.2) with hSdef
  set Lt : Finset (Fin 20 × Fin 20) := S.filter (fun p => p.1 < p.2) with hLtdef
  set Gt : Finset (Fin 20 × Fin 20) := S.filter (fun p => ¬ p.1 < p.2) with hGtdef
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
theorem rich_nonadj_biUnion_twenty (G : SimpleGraph (Fin 20)) (Hub Iso R : Finset (Fin 20))
    (hdeg4 : ∀ h ∈ Hub, G.degree h = 4)
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hno2hub : ¬∃ h₁ h₂ : Fin 20, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
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
  have hsh1 := rich_nonadj_share_eq_one_twenty G Hub Iso hshare hno2hub p.1 p.2 hp1Hub hp2Hub
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
theorem rich_D_eq_thirty_twenty (G : SimpleGraph (Fin 20)) (Hub Iso R : Finset (Fin 20))
    (hdeg4 : ∀ h ∈ Hub, G.degree h = 4)
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdisj : Disjoint Hub Iso) (hIso : Iso.card = 6)
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hno2hub : ¬∃ h₁ h₂ : Fin 20, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card)
    (hRHub : R ⊆ Hub) (hRrich : ∀ a ∈ R, 2 ≤ (G.neighborFinset a ∩ Iso).card)
    (hr7 : R.card = 7) (hS15 : ∑ r ∈ R, (G.neighborFinset r ∩ Iso).card = 15) :
    (R.offDiag.filter (fun p => ¬G.Adj p.1 p.2)).card = 30 := by
  classical
  -- The all-poor twin `t6` and the design `(3,3,3,3,3,0)`.
  obtain ⟨t6, ht6Iso, ht6c0, htdesign⟩ := poor_incidence_concentrates_twenty G Hub Iso R
    hdeg4 hiso3 hdisj hIso hshare hno2hub hRHub hRrich hr7 hS15
  -- The unique iso-degree-`3` rich hub `w`.
  obtain ⟨w, hwR, hw3, hwoth⟩ := rich_isodeg_seq_twenty G Iso R hRrich hr7 hS15
  -- `D_adj = ∑_{a∈R} |N(a)∩R|`.
  have hDadjsum := dadj_eq_sum_twenty G R
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
  have hsub := rich_nonadj_biUnion_twenty G Hub Iso R hdeg4 hshare hno2hub hRHub hRrich
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
  have hsplit := offdiag_eq_twenty G R
  rw [hr7] at hsplit
  -- Parity of `D_adj`.
  obtain ⟨k, hk⟩ := even_dadj_twenty G R
  omega

/-- **The twins' rich-trace off-diagonals total `≤ 30`** (the `(3,3,3,3,3,0)` design). -/
theorem rich_biUnion_le_thirty_twenty (G : SimpleGraph (Fin 20)) (Hub Iso R : Finset (Fin 20))
    (hdeg4 : ∀ h ∈ Hub, G.degree h = 4)
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdisj : Disjoint Hub Iso) (hIso : Iso.card = 6)
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hno2hub : ¬∃ h₁ h₂ : Fin 20, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card)
    (hRHub : R ⊆ Hub) (hRrich : ∀ a ∈ R, 2 ≤ (G.neighborFinset a ∩ Iso).card)
    (hr7 : R.card = 7) (hS15 : ∑ r ∈ R, (G.neighborFinset r ∩ Iso).card = 15) :
    (Iso.biUnion (fun t => (G.neighborFinset t ∩ R).offDiag)).card ≤ 30 := by
  classical
  obtain ⟨t6, ht6Iso, ht6c0, htdesign⟩ := poor_incidence_concentrates_twenty G Hub Iso R
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
theorem rich_triples_partition_twenty (G : SimpleGraph (Fin 20)) (Hub Iso R : Finset (Fin 20))
    (hdeg4 : ∀ h ∈ Hub, G.degree h = 4)
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdisj : Disjoint Hub Iso) (hIso : Iso.card = 6)
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hno2hub : ¬∃ h₁ h₂ : Fin 20, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card)
    (hRHub : R ⊆ Hub) (hRrich : ∀ a ∈ R, 2 ≤ (G.neighborFinset a ∩ Iso).card)
    (hr7 : R.card = 7) (hS15 : ∑ r ∈ R, (G.neighborFinset r ∩ Iso).card = 15) :
    ∀ t ∈ Iso, ∀ x ∈ G.neighborFinset t ∩ R, ∀ y ∈ G.neighborFinset t ∩ R, x ≠ y →
      ¬G.Adj x y := by
  classical
  have hD30 := rich_D_eq_thirty_twenty G Hub Iso R hdeg4 hiso3 hdisj hIso hshare hno2hub
    hRHub hRrich hr7 hS15
  have hsub := rich_nonadj_biUnion_twenty G Hub Iso R hdeg4 hshare hno2hub hRHub hRrich
  have hbiUle := rich_biUnion_le_thirty_twenty G Hub Iso R hdeg4 hiso3 hdisj hIso hshare hno2hub
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
theorem rich_w_no_rich_nbr_twenty (G : SimpleGraph (Fin 20)) (Hub Iso R : Finset (Fin 20))
    (hdeg4 : ∀ h ∈ Hub, G.degree h = 4)
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdisj : Disjoint Hub Iso) (hIso : Iso.card = 6)
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hno2hub : ¬∃ h₁ h₂ : Fin 20, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card)
    (hRHub : R ⊆ Hub) (hRrich : ∀ a ∈ R, 2 ≤ (G.neighborFinset a ∩ Iso).card)
    (hr7 : R.card = 7) (hS15 : ∑ r ∈ R, (G.neighborFinset r ∩ Iso).card = 15) :
    ∃ w ∈ R, (G.neighborFinset w ∩ Iso).card = 3 ∧ (G.neighborFinset w ∩ R).card = 0 ∧
      ∀ r ∈ R, r ≠ w → (G.neighborFinset r ∩ Iso).card = 2 := by
  classical
  obtain ⟨t6, ht6Iso, ht6c0, htdesign⟩ := poor_incidence_concentrates_twenty G Hub Iso R
    hdeg4 hiso3 hdisj hIso hshare hno2hub hRHub hRrich hr7 hS15
  obtain ⟨w, hwR, hw3, hwoth⟩ := rich_isodeg_seq_twenty G Iso R hRrich hr7 hS15
  have hpw := rich_triples_partition_twenty G Hub Iso R hdeg4 hiso3 hdisj hIso hshare hno2hub
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
  set U : Finset (Fin 20) := (G.neighborFinset w ∩ Iso).biUnion
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
    have hsh1 := rich_nonadj_share_eq_one_twenty G Hub Iso hshare hno2hub y w hyHub (hRHub hwR)
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
      have hsub2 : ({t, t'} : Finset (Fin 20)) ⊆ G.neighborFinset y ∩ G.neighborFinset w ∩ Iso := by
        intro z hz
        rw [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl
        · exact htmem
        · exact ht'mem
      calc 2 = ({t, t'} : Finset (Fin 20)).card := by
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
theorem rich_saturated_twenty (G : SimpleGraph (Fin 20)) (Hub Iso R : Finset (Fin 20))
    (hdeg4 : ∀ h ∈ Hub, G.degree h = 4)
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdisj : Disjoint Hub Iso) (hIso : Iso.card = 6)
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hno2hub : ¬∃ h₁ h₂ : Fin 20, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card)
    (hRHub : R ⊆ Hub) (hRrich : ∀ a ∈ R, 2 ≤ (G.neighborFinset a ∩ Iso).card)
    (hr7 : R.card = 7) (hS15 : ∑ r ∈ R, (G.neighborFinset r ∩ Iso).card = 15) :
    ∃ w ∈ R, (G.neighborFinset w ∩ Iso).card = 3 ∧ (G.neighborFinset w ∩ R).card = 0 ∧
      ∀ r ∈ R, r ≠ w → G.neighborFinset r ⊆ Iso ∪ R := by
  classical
  obtain ⟨w, hwR, hw3, hw0, hwoth⟩ := rich_w_no_rich_nbr_twenty G Hub Iso R hdeg4 hiso3 hdisj
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
  have hD30 := rich_D_eq_thirty_twenty G Hub Iso R hdeg4 hiso3 hdisj hIso hshare hno2hub
    hRHub hRrich hr7 hS15
  have hsplit := offdiag_eq_twenty G R
  rw [hr7] at hsplit
  have hDadjsum := dadj_eq_sum_twenty G R
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
poor hubs `hg₁, hg₂`.  At `n = 20` the poor side `P = Hub ∖ R` has `|P| = 12 − 7 = 5` hubs carrying
iso-incidence `18 − 15 = 3`, so exactly two poor hubs are iso-degree-`0`.  If either `z`-side hub
carries a twin, the reusable `Z`-leaf cut `two_poor_zleaf_pigeonhole_twenty` fires.  The residual
(both iso-degree-`0`, absent for `n ≤ 19` where `|P| ≤ 4`) is killed directly: if `hg₁ ~ hg₂` then
`{z, hg₁, hg₂}` is a good triangle (`3 + 4 + 4 = 11`); otherwise both meet `3` hubs in
`{w} ∪ N(t₆)` (saturation NODE 2), sharing `≥ 2` neighbours `x, x'` in `N(t₆)`, and
`{hg₁, hg₂ | z, x, x'}` is a good `K₂,₃` of degree sum `4 + 4 + 3 + 4 + 4 = 19`, excluded by
`hK23`. -/
theorem mpartner_meets_poor_twenty (G : SimpleGraph (Fin 20)) (Hub Iso : Finset (Fin 20))
    (hdeg4 : ∀ h ∈ Hub, G.degree h = 4)
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdisj : Disjoint Hub Iso) (hHub : Hub.card = 12) (hIso : Iso.card = 6)
    (hdeg3 : ∀ v : Fin 20, 3 ≤ G.degree v) (hisodeg3 : ∀ t ∈ Iso, G.degree t = 3)
    (hdsum : ∑ w ∈ Hub, G.degree w = 48)
    (hleak : ∑ h ∈ Hub, (G.neighborFinset h ∩ (Finset.univ \ (Hub ∪ Iso))).card ≤ 4)
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hno2hub : ¬∃ h₁ h₂ : Fin 20, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card)
    (_hC4 : ¬∃ a b c d : Fin 20, ({a, b, c, d} : Finset (Fin 20)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (hK23 : ¬∃ a b c d e : Fin 20, ({a, b, c, d, e} : Finset (Fin 20)).card = 5 ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
      G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 19)
    (hT : ¬∃ x y z : Fin 20, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧
      G.degree x + G.degree y + G.degree z ≤ 11)
    (hnocut : ¬ ZPoorCutConfig G)
    (z : Fin 20) (hz : z ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 20)))
    (hg1 : Fin 20) (hg2 : Fin 20) (hg1ne : hg1 ≠ hg2)
    (hg1mem : hg1 ∈ G.neighborFinset z ∩ Hub) (hg2mem : hg2 ∈ G.neighborFinset z ∩ Hub)
    (hg1poor : (G.neighborFinset hg1 ∩ Iso).card ≤ 1)
    (hg2poor : (G.neighborFinset hg2 ∩ Iso).card ≤ 1)
    (_hres : G.Adj hg1 hg2 ∨ (G.neighborFinset hg1 ∩ G.neighborFinset hg2 ∩ Iso).card = 0)
    (hr7 : (Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)).card = 7)
    (hS15 : ∑ r ∈ Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card),
        (G.neighborFinset r ∩ Iso).card = 15) :
    False := by
  -- The poor side `P = Hub \ R` has `|P| = 12 − 7 = 5` hubs carrying iso-incidence `18 − 15 = 3`.
  -- With `|P| = 5` the `n ≤ 19` pigeonhole fails (the extra poor hub absorbs the slack), so `hg1,
  -- hg2` CAN both be iso-degree-`0`.  We split: a `z`-side twin fires the reusable `Z`-leaf cut;
  -- the both-iso-`0` residual is killed by a good triangle (adjacent) or a good `K₂,₃` via the
  -- saturation design (non-adjacent).
  classical
  set R : Finset (Fin 20) := Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card) with hRdef
  have hRsub : R ⊆ Hub := Finset.filter_subset _ _
  set P : Finset (Fin 20) := Hub.filter (fun h => ¬ 2 ≤ (G.neighborFinset h ∩ Iso).card) with hPdef
  -- `|P| = 4` and `∑_P iso = 3`.
  have hsum18 : ∑ a ∈ Hub, (G.neighborFinset a ∩ Iso).card = 18 := by
    have := hub_iso_sum_twenty G Hub Iso hiso3; rw [hIso] at this; omega
  have hPcard : P.card = 5 := by
    have := Finset.card_filter_add_card_filter_not (s := Hub)
      (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)
    rw [← hRdef, ← hPdef, hHub, hr7] at this; omega
  have hPsum : ∑ g ∈ P, (G.neighborFinset g ∩ Iso).card = 3 := by
    have hsp : (∑ r ∈ R, (G.neighborFinset r ∩ Iso).card)
        + ∑ g ∈ P, (G.neighborFinset g ∩ Iso).card = 18 := by
      rw [hRdef, hPdef, Finset.sum_filter_add_sum_filter_not Hub _]; exact hsum18
    rw [hS15] at hsp; omega
  have hPle1 : ∀ g ∈ P, (G.neighborFinset g ∩ Iso).card ≤ 1 := by
    intro g hg; rw [hPdef, Finset.mem_filter] at hg; omega
  -- Hub memberships and poorness of `hg1, hg2`.
  have hg1Hub : hg1 ∈ Hub := (Finset.mem_inter.mp hg1mem).2
  have hg2Hub : hg2 ∈ Hub := (Finset.mem_inter.mp hg2mem).2
  have hg1P : hg1 ∈ P := by rw [hPdef, Finset.mem_filter]; exact ⟨hg1Hub, by omega⟩
  have hg2P : hg2 ∈ P := by rw [hPdef, Finset.mem_filter]; exact ⟨hg2Hub, by omega⟩
  have hg1notR : hg1 ∉ R := by rw [hRdef, Finset.mem_filter]; rintro ⟨_, h2⟩; omega
  have hg2notR : hg2 ∉ R := by rw [hRdef, Finset.mem_filter]; rintro ⟨_, h2⟩; omega
  -- `N(z) ∩ Hub = {hg1, hg2}` (both poor); record `z` has degree `3`.
  obtain ⟨_, hzhub2, hzdeg3⟩ :=
    z_two_hub_nbrs_twenty G Hub Iso hiso3 hdisj hHub hIso hdsum hdeg3 hisodeg3 hleak z hz
  have hNz : G.neighborFinset z ∩ Hub = {hg1, hg2} := by
    refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
    · intro x hx; rw [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hg1mem
      · exact hg2mem
    · rw [hzhub2, Finset.card_insert_of_notMem (by simp [hg1ne]), Finset.card_singleton]
  have hzpoor : ∀ h ∈ G.neighborFinset z ∩ Hub, h ∉ R := by
    intro h hh; rw [hNz, Finset.mem_insert, Finset.mem_singleton] at hh
    rcases hh with rfl | rfl
    · exact hg1notR
    · exact hg2notR
  -- **If either `z`-side poor hub carries a twin, the reusable `Z`-leaf cut fires.**
  by_cases h1 : 1 ≤ (G.neighborFinset hg1 ∩ Iso).card
  · have h1eq : (G.neighborFinset hg1 ∩ Iso).card = 1 := by omega
    obtain ⟨cstar, hcs⟩ := Finset.card_eq_one.mp h1eq
    exact hnocut (Or.inl (two_poor_zleaf_pigeonhole_twenty G Hub Iso hdeg4 hiso3 hdisj hHub hIso
      hdsum hdeg3 hisodeg3 hleak R hRdef hg1 z cstar hg1Hub hz
      ((G.mem_neighborFinset z hg1).mp (Finset.mem_inter.mp hg1mem).1) hcs hzpoor (by omega)))
  by_cases h2 : 1 ≤ (G.neighborFinset hg2 ∩ Iso).card
  · have h2eq : (G.neighborFinset hg2 ∩ Iso).card = 1 := by omega
    obtain ⟨cstar, hcs⟩ := Finset.card_eq_one.mp h2eq
    exact hnocut (Or.inl (two_poor_zleaf_pigeonhole_twenty G Hub Iso hdeg4 hiso3 hdisj hHub hIso
      hdsum hdeg3 hisodeg3 hleak R hRdef hg2 z cstar hg2Hub hz
      ((G.mem_neighborFinset z hg2).mp (Finset.mem_inter.mp hg2mem).1) hcs hzpoor (by omega)))
  -- **Both `z`-side poor hubs are iso-degree `0`.**  (Empty for `n ≤ 19`; the genuine `n = 20`
  -- residual: `|P| = 5` carries only `3` twin-incidences, so two poor hubs miss every twin — and
  -- the `n ≤ 19` pigeonhole `hone` becomes false with the extra poor hub absorbing the slack.)
  push Not at h1 h2
  have h1z : (G.neighborFinset hg1 ∩ Iso).card = 0 := by omega
  have h2z : (G.neighborFinset hg2 ∩ Iso).card = 0 := by omega
  have hznotHub : z ∉ Hub := by
    rw [Finset.mem_sdiff, Finset.mem_union, not_or] at hz; exact hz.2.1
  -- The adjacent sub-case is the good triangle `{z, hg1, hg2}` (degree sum `3 + 4 + 4 = 11`).
  by_cases hadj12 : G.Adj hg1 hg2
  · refine hT ⟨z, hg1, hg2, fun he => hznotHub (he ▸ hg1Hub), hg1ne,
      fun he => hznotHub (he ▸ hg2Hub),
      (G.mem_neighborFinset z hg1).mp (Finset.mem_inter.mp hg1mem).1, hadj12,
      (G.mem_neighborFinset z hg2).mp (Finset.mem_inter.mp hg2mem).1, ?_⟩
    have := hdeg4 hg1 hg1Hub; have := hdeg4 hg2 hg2Hub; omega
  -- **The non-adjacent sub-case: the good `K₂,₃` `{hg1, hg2 | z, x, x'}` (degree sum `19`).**
  have hRrich : ∀ a ∈ R, 2 ≤ (G.neighborFinset a ∩ Iso).card := by
    intro a ha; rw [hRdef, Finset.mem_filter] at ha; exact ha.2
  -- The `M`-partner `zp` (`z ~ zp`, `Z = {z, zp}`).
  set Z : Finset (Fin 20) := Finset.univ \ (Hub ∪ Iso) with hZdef
  have hZcard : Z.card = 2 := z_card_two_twenty Hub Iso hdisj hHub hIso
  have hzZ : z ∈ Z := hz
  have hzerase : (Z.erase z).card = 1 := by rw [Finset.card_erase_of_mem hzZ, hZcard]
  obtain ⟨zp, hzp⟩ := Finset.card_eq_one.mp hzerase
  have hzpZe : zp ∈ Z.erase z := by rw [hzp]; exact Finset.mem_singleton_self _
  have hzpZ : zp ∈ Z := Finset.mem_of_mem_erase hzpZe
  have hzpz : zp ≠ z := (Finset.mem_erase.mp hzpZe).1
  have hZpair : Z = {z, zp} := by
    refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hzZ
      · rw [Finset.mem_singleton] at hx; subst hx; exact hzpZ
    · rw [hZcard, Finset.card_insert_of_notMem (by simp [Ne.symm hzpz]), Finset.card_singleton]
  -- The all-poor twin `t6` (design) and the saturation hub `w`.
  obtain ⟨t6, ht6Iso, ht6c0, htdesign⟩ := poor_incidence_concentrates_twenty G Hub Iso R
    hdeg4 hiso3 hdisj hIso hshare hno2hub hRsub hRrich hr7 hS15
  obtain ⟨w, hwR, hw3, hw0, hsat⟩ := rich_saturated_twenty G Hub Iso R hdeg4 hiso3 hdisj hIso
    hshare hno2hub hRsub hRrich hr7 hS15
  have ht6subHub : G.neighborFinset t6 ⊆ Hub := by
    have hcard3 : (G.neighborFinset t6 ∩ Hub).card = 3 := hiso3 t6 ht6Iso
    have hdt : (G.neighborFinset t6).card = 3 := by
      rw [G.card_neighborFinset_eq_degree]; exact hisodeg3 t6 ht6Iso
    have heq : G.neighborFinset t6 ∩ Hub = G.neighborFinset t6 :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by rw [hcard3, hdt])
    rw [← heq]; exact Finset.inter_subset_right
  -- Only `hg1, hg2` are the iso-degree-`0` poor hubs (else `∑_P` would fall below `3`).
  have hiso0only : ∀ g ∈ P, (G.neighborFinset g ∩ Iso).card = 0 → g = hg1 ∨ g = hg2 := by
    intro g hgP hg0
    by_contra hcon
    push Not at hcon
    obtain ⟨hgne1, hgne2⟩ := hcon
    have e1 := Finset.add_sum_erase P (fun a => (G.neighborFinset a ∩ Iso).card) hg1P
    have hg2er : hg2 ∈ P.erase hg1 := Finset.mem_erase.mpr ⟨Ne.symm hg1ne, hg2P⟩
    have e2 := Finset.add_sum_erase (P.erase hg1) (fun a => (G.neighborFinset a ∩ Iso).card) hg2er
    have hger : g ∈ (P.erase hg1).erase hg2 :=
      Finset.mem_erase.mpr ⟨hgne2, Finset.mem_erase.mpr ⟨hgne1, hgP⟩⟩
    have e3 := Finset.add_sum_erase ((P.erase hg1).erase hg2)
      (fun a => (G.neighborFinset a ∩ Iso).card) hger
    have hrest : ∑ a ∈ ((P.erase hg1).erase hg2).erase g, (G.neighborFinset a ∩ Iso).card ≤ 2 := by
      have hcardE : (((P.erase hg1).erase hg2).erase g).card = 2 := by
        rw [Finset.card_erase_of_mem hger, Finset.card_erase_of_mem hg2er,
          Finset.card_erase_of_mem hg1P, hPcard]
      calc ∑ a ∈ ((P.erase hg1).erase hg2).erase g, (G.neighborFinset a ∩ Iso).card
          ≤ ∑ _a ∈ ((P.erase hg1).erase hg2).erase g, 1 := Finset.sum_le_sum (fun a ha =>
            hPle1 a (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase ha))))
        _ = 2 := by rw [Finset.sum_const, hcardE, smul_eq_mul, mul_one]
    rw [hPsum] at e1
    omega
  -- A poor iso-degree-`1` hub meets `t6` (the other twins have all-rich neighbourhoods).
  have hpoorT6 : ∀ g ∈ Hub, (G.neighborFinset g ∩ Iso).card = 1 → G.Adj g t6 := by
    intro g hgHub hgcard
    obtain ⟨tg, htg⟩ := Finset.card_eq_one.mp hgcard
    have htgmem : tg ∈ G.neighborFinset g ∩ Iso := by rw [htg]; exact Finset.mem_singleton_self _
    have htgIso : tg ∈ Iso := (Finset.mem_inter.mp htgmem).2
    have hgtg : G.Adj g tg := (G.mem_neighborFinset g tg).mp (Finset.mem_inter.mp htgmem).1
    by_cases htgt6 : tg = t6
    · rw [← htgt6]; exact hgtg
    · exfalso
      have hd3 := htdesign tg htgIso htgt6
      have htgdeg : (G.neighborFinset tg).card = 3 := by
        rw [G.card_neighborFinset_eq_degree]; exact hisodeg3 tg htgIso
      have heqR : G.neighborFinset tg ∩ R = G.neighborFinset tg :=
        Finset.eq_of_subset_of_card_le Finset.inter_subset_left (le_of_eq (by rw [htgdeg, hd3]))
      have hgin : g ∈ G.neighborFinset tg := (G.mem_neighborFinset tg g).mpr hgtg.symm
      have hgR : g ∈ R := by
        have hmem : g ∈ G.neighborFinset tg ∩ R := by rw [heqR]; exact hgin
        exact (Finset.mem_inter.mp hmem).2
      have := hRrich g hgR
      omega
  -- Every hub-neighbour of an iso-`0` poor hub is `w` or a `t6`-twin.
  have hAinK : ∀ g, (g = hg1 ∨ g = hg2) → ∀ x, x ∈ G.neighborFinset g ∩ Hub →
      x ∈ insert w (G.neighborFinset t6) := by
    intro g hg x hx
    have hxHub : x ∈ Hub := (Finset.mem_inter.mp hx).2
    have hgHub : g ∈ Hub := by rcases hg with rfl | rfl; exacts [hg1Hub, hg2Hub]
    have hgx : G.Adj g x := (G.mem_neighborFinset g x).mp (Finset.mem_inter.mp hx).1
    by_cases hxR : x ∈ R
    · rw [Finset.mem_insert]; left
      by_contra hxw
      have hmem := hsat x hxR hxw
      have hgin : g ∈ G.neighborFinset x := (G.mem_neighborFinset x g).mpr hgx.symm
      have hgmem := hmem hgin
      rw [Finset.mem_union] at hgmem
      rcases hgmem with h | h
      · exact Finset.disjoint_left.mp hdisj hgHub h
      · have hge2 := hRrich g h
        rcases hg with rfl | rfl
        · rw [h1z] at hge2; omega
        · rw [h2z] at hge2; omega
    · have hxne_g : x ≠ g := fun he => G.irrefl (by rw [he] at hgx; exact hgx)
      have hxiso1 : (G.neighborFinset x ∩ Iso).card = 1 := by
        have hxpoor : (G.neighborFinset x ∩ Iso).card ≤ 1 := by
          by_contra hc; push Not at hc
          exact hxR (by rw [hRdef, Finset.mem_filter]; exact ⟨hxHub, hc⟩)
        rcases Nat.eq_zero_or_pos (G.neighborFinset x ∩ Iso).card with hx0 | hxpos
        · exfalso
          have hxP : x ∈ P := by rw [hPdef, Finset.mem_filter]; exact ⟨hxHub, by omega⟩
          rcases hiso0only x hxP hx0 with rfl | rfl
          · rcases hg with rfl | rfl
            · exact hxne_g rfl
            · exact hadj12 hgx.symm
          · rcases hg with rfl | rfl
            · exact hadj12 hgx
            · exact hxne_g rfl
        · omega
      have hxt6 : G.Adj x t6 := hpoorT6 x hxHub hxiso1
      rw [Finset.mem_insert]; right
      exact (G.mem_neighborFinset t6 x).mpr hxt6.symm
  -- `|N(g) ∩ Hub| = 3` for `g ∈ {hg1, hg2}` (iso-`0`, meets only `z` in `Z`).
  have hAcard : ∀ g, (g = hg1 ∨ g = hg2) → (G.neighborFinset g ∩ Hub).card = 3 := by
    intro g hg
    have hgHub : g ∈ Hub := by rcases hg with rfl | rfl; exacts [hg1Hub, hg2Hub]
    have hgiso0 : (G.neighborFinset g ∩ Iso).card = 0 := by
      rcases hg with rfl | rfl; exacts [h1z, h2z]
    have hgz : G.Adj g z := by
      rcases hg with rfl | rfl
      · exact ((G.mem_neighborFinset z g).mp (Finset.mem_inter.mp hg1mem).1).symm
      · exact ((G.mem_neighborFinset z g).mp (Finset.mem_inter.mp hg2mem).1).symm
    have hgzp : ¬ G.Adj g zp := by
      intro hadj
      exact no_hub_adj_both_mends_twenty G Hub Iso hdeg4 hiso3 hdisj hHub hIso hdsum hdeg3
        hisodeg3 hleak hT g hgHub z hz zp hzpZ (Ne.symm hzpz) ⟨hgz, hadj⟩
    have hgZeq : (G.neighborFinset g ∩ Z).card = 1 := by
      have hzin : z ∈ G.neighborFinset g ∩ Z :=
        Finset.mem_inter.mpr ⟨(G.mem_neighborFinset g z).mpr hgz, hzZ⟩
      have hsub : G.neighborFinset g ∩ Z ⊆ {z} := by
        intro x hx
        obtain ⟨hxN, hxZ⟩ := Finset.mem_inter.mp hx
        rw [hZpair, Finset.mem_insert, Finset.mem_singleton] at hxZ
        rcases hxZ with rfl | rfl
        · exact Finset.mem_singleton_self _
        · exact absurd ((G.mem_neighborFinset g x).mp hxN) hgzp
      have heq : G.neighborFinset g ∩ Z = {z} :=
        Finset.eq_of_subset_of_card_le hsub
          (by rw [Finset.card_singleton]; exact Finset.card_pos.mpr ⟨z, hzin⟩)
      rw [heq, Finset.card_singleton]
    have hsp := nbr_split_three_twenty G Hub Iso hdisj g
    rw [← hZdef, hgiso0, hgZeq, hdeg4 g hgHub] at hsp
    omega
  set K : Finset (Fin 20) := insert w (G.neighborFinset t6) with hKdef
  have hwnotT6 : w ∉ G.neighborFinset t6 := by
    intro hw
    have hmem : w ∈ G.neighborFinset t6 ∩ R := Finset.mem_inter.mpr ⟨hw, hwR⟩
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem] at ht6c0
    exact ht6c0 w hmem
  have hKcard : K.card = 4 := by
    have hd : (G.neighborFinset t6).card = 3 := by
      rw [G.card_neighborFinset_eq_degree]; exact hisodeg3 t6 ht6Iso
    rw [hKdef, Finset.card_insert_of_notMem hwnotT6, hd]
  have hA1sub : G.neighborFinset hg1 ∩ Hub ⊆ K := fun x hx => hAinK hg1 (Or.inl rfl) x hx
  have hA2sub : G.neighborFinset hg2 ∩ Hub ⊆ K := fun x hx => hAinK hg2 (Or.inr rfl) x hx
  have hA1card : (G.neighborFinset hg1 ∩ Hub).card = 3 := hAcard hg1 (Or.inl rfl)
  have hA2card : (G.neighborFinset hg2 ∩ Hub).card = 3 := hAcard hg2 (Or.inr rfl)
  -- `≥ 2` common hub-neighbours, all in `N(t6)`.
  have hunionle : (G.neighborFinset hg1 ∩ Hub ∪ G.neighborFinset hg2 ∩ Hub).card ≤ 4 :=
    le_trans (Finset.card_le_card (Finset.union_subset hA1sub hA2sub)) (le_of_eq hKcard)
  have hincl := Finset.card_union_add_card_inter (G.neighborFinset hg1 ∩ Hub)
    (G.neighborFinset hg2 ∩ Hub)
  rw [hA1card, hA2card] at hincl
  have hcommon : 2 ≤ (G.neighborFinset hg1 ∩ Hub ∩ (G.neighborFinset hg2 ∩ Hub)).card := by omega
  have hCsubT6 : G.neighborFinset hg1 ∩ Hub ∩ (G.neighborFinset hg2 ∩ Hub)
      ⊆ G.neighborFinset t6 := by
    intro x hx
    obtain ⟨hxA1, hxA2⟩ := Finset.mem_inter.mp hx
    have hxK : x ∈ K := hA1sub hxA1
    rw [hKdef, Finset.mem_insert] at hxK
    rcases hxK with rfl | hxT6
    · exfalso
      have hg1inw : hg1 ∈ G.neighborFinset x :=
        (G.mem_neighborFinset x hg1).mpr ((G.mem_neighborFinset hg1 x).mp
          (Finset.mem_inter.mp hxA1).1).symm
      have hg2inw : hg2 ∈ G.neighborFinset x :=
        (G.mem_neighborFinset x hg2).mpr ((G.mem_neighborFinset hg2 x).mp
          (Finset.mem_inter.mp hxA2).1).symm
      have hsub2 : ({hg1, hg2} : Finset (Fin 20)) ⊆ G.neighborFinset x \ Iso := by
        intro y hy
        rw [Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with rfl | rfl
        · exact Finset.mem_sdiff.mpr ⟨hg1inw, fun h => Finset.disjoint_left.mp hdisj hg1Hub h⟩
        · exact Finset.mem_sdiff.mpr ⟨hg2inw, fun h => Finset.disjoint_left.mp hdisj hg2Hub h⟩
      have hge2 : 2 ≤ (G.neighborFinset x \ Iso).card :=
        le_trans (le_of_eq (by
          rw [Finset.card_insert_of_notMem (by simp [hg1ne]), Finset.card_singleton]))
          (Finset.card_le_card hsub2)
      have hwsdiff : (G.neighborFinset x \ Iso).card = 1 := by
        have hcs := Finset.card_inter_add_card_sdiff (G.neighborFinset x) Iso
        have hwd : (G.neighborFinset x).card = 4 := by
          rw [G.card_neighborFinset_eq_degree, hdeg4 x (hRsub hwR)]
        rw [hwd, hw3] at hcs; omega
      omega
    · exact hxT6
  obtain ⟨x, hxC, x', hx'C, hxx'⟩ :=
    Finset.one_lt_card.mp (lt_of_lt_of_le one_lt_two hcommon)
  -- Adjacencies and non-adjacencies for the `K₂,₃`.
  have hxHub : x ∈ Hub := (Finset.mem_inter.mp (Finset.mem_inter.mp hxC).1).2
  have hx'Hub : x' ∈ Hub := (Finset.mem_inter.mp (Finset.mem_inter.mp hx'C).1).2
  have hhg1x : G.Adj hg1 x :=
    (G.mem_neighborFinset hg1 x).mp (Finset.mem_inter.mp (Finset.mem_inter.mp hxC).1).1
  have hhg2x : G.Adj hg2 x :=
    (G.mem_neighborFinset hg2 x).mp (Finset.mem_inter.mp (Finset.mem_inter.mp hxC).2).1
  have hhg1x' : G.Adj hg1 x' :=
    (G.mem_neighborFinset hg1 x').mp (Finset.mem_inter.mp (Finset.mem_inter.mp hx'C).1).1
  have hhg2x' : G.Adj hg2 x' :=
    (G.mem_neighborFinset hg2 x').mp (Finset.mem_inter.mp (Finset.mem_inter.mp hx'C).2).1
  have hxt6 : x ∈ G.neighborFinset t6 := hCsubT6 hxC
  have hx't6 : x' ∈ G.neighborFinset t6 := hCsubT6 hx'C
  have hhg1z : G.Adj hg1 z := ((G.mem_neighborFinset z hg1).mp (Finset.mem_inter.mp hg1mem).1).symm
  have hhg2z : G.Adj hg2 z := ((G.mem_neighborFinset z hg2).mp (Finset.mem_inter.mp hg2mem).1).symm
  have hzNadjT6 : ∀ y, y ∈ G.neighborFinset t6 → ¬ G.Adj z y := by
    intro y hy hadj
    have hyHub : y ∈ Hub := ht6subHub hy
    have hyinNz : y ∈ G.neighborFinset z ∩ Hub :=
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset z y).mpr hadj, hyHub⟩
    rw [hNz, Finset.mem_insert, Finset.mem_singleton] at hyinNz
    rcases hyinNz with rfl | rfl
    · have hmem : t6 ∈ G.neighborFinset y ∩ Iso :=
        Finset.mem_inter.mpr ⟨(G.mem_neighborFinset y t6).mpr
          ((G.mem_neighborFinset t6 y).mp hy).symm, ht6Iso⟩
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem] at h1z
      exact h1z t6 hmem
    · have hmem : t6 ∈ G.neighborFinset y ∩ Iso :=
        Finset.mem_inter.mpr ⟨(G.mem_neighborFinset y t6).mpr
          ((G.mem_neighborFinset t6 y).mp hy).symm, ht6Iso⟩
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem] at h2z
      exact h2z t6 hmem
  have hxx'nadj : ¬ G.Adj x x' := by
    intro hadj
    have hxt6adj : G.Adj x t6 := ((G.mem_neighborFinset t6 x).mp hxt6).symm
    have hx't6adj : G.Adj x' t6 := ((G.mem_neighborFinset t6 x').mp hx't6).symm
    refine hT ⟨x, x', t6, hxx', ?_, ?_, hadj, hx't6adj, hxt6adj, ?_⟩
    · exact fun he => Finset.disjoint_left.mp hdisj hx'Hub (he ▸ ht6Iso)
    · exact fun he => Finset.disjoint_left.mp hdisj hxHub (he ▸ ht6Iso)
    · have := hdeg4 x hxHub; have := hdeg4 x' hx'Hub; have := hisodeg3 t6 ht6Iso; omega
  -- Distinctness of the five `K₂,₃` vertices.
  have hxne1 : x ≠ hg1 := fun he => G.irrefl (he ▸ hhg1x)
  have hxne2 : x ≠ hg2 := fun he => G.irrefl (he ▸ hhg2x)
  have hx'ne1 : x' ≠ hg1 := fun he => G.irrefl (he ▸ hhg1x')
  have hx'ne2 : x' ≠ hg2 := fun he => G.irrefl (he ▸ hhg2x')
  have hzne1 : z ≠ hg1 := fun he => hznotHub (by rw [he]; exact hg1Hub)
  have hzne2 : z ≠ hg2 := fun he => hznotHub (by rw [he]; exact hg2Hub)
  have hznex : z ≠ x := fun he => hznotHub (by rw [he]; exact hxHub)
  have hznex' : z ≠ x' := fun he => hznotHub (by rw [he]; exact hx'Hub)
  have hcard5 : ({hg1, hg2, z, x, x'} : Finset (Fin 20)).card = 5 := by
    rw [Finset.card_insert_of_notMem (by
          simp only [Finset.mem_insert, Finset.mem_singleton]; push Not
          exact ⟨hg1ne, hzne1.symm, hxne1.symm, hx'ne1.symm⟩),
        Finset.card_insert_of_notMem (by
          simp only [Finset.mem_insert, Finset.mem_singleton]; push Not
          exact ⟨hzne2.symm, hxne2.symm, hx'ne2.symm⟩),
        Finset.card_insert_of_notMem (by
          simp only [Finset.mem_insert, Finset.mem_singleton]; push Not
          exact ⟨hznex, hznex'⟩),
        Finset.card_insert_of_notMem (by simp only [Finset.mem_singleton]; exact hxx'),
        Finset.card_singleton]
  exact hK23 ⟨hg1, hg2, z, x, x', hcard5, hhg1z, hhg1x, hhg1x', hhg2z, hhg2x, hhg2x',
    hadj12, hzNadjT6 x hxt6, hzNadjT6 x' hx't6, hxx'nadj, by
      have := hdeg4 hg1 hg1Hub; have := hdeg4 hg2 hg2Hub; have := hdeg4 x hxHub
      have := hdeg4 x' hx'Hub; omega⟩

end N20

end ACMax
