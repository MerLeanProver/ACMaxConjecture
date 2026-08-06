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

/-!
# The `r = 7`, `S = 16` saturation chain closing the second residual (`n = 18`)

For the tight `e(M) = 1`, all-degree-`4`, `(|Hub|, |Iso|) = (10, 6)` profile with seven rich hubs
and rich iso-incidence sum `S = 16`, the poor incidences (mass `18 - 16 = 2`) sit on two
iso-degree-`1` poor hubs and one iso-degree-`0` poor hub.  The rich iso-incidence sum forces the
twin design `(3, 3, 3, 3, 3, 1)`: a unique twin `t*` meeting exactly one rich hub and five all-rich
twins.  Crucially the within-`R` degree mass is exactly `12` (`Dadj = 12`), so every rich hub has
`|N ∩ R| + |N ∩ Iso| = 4 = deg`: **all** rich hubs are saturated (`N ⊆ Iso ∪ R`).  The `M`-partner
`z'` then has two hub-neighbours, all poor (rich hubs are closed) and none of which can be the two
poor hubs `z` already meets (`no_hub_adj_both`); only one poor hub remains — a counting
contradiction.  No good `C₄` is needed: the residual dies by saturation counting.
-/

namespace ACMax

open scoped Classical

namespace N18

/-- **Poor-incidence concentration at `r = 7`, `S = 16`.**  With `c_t := |N(t) ∩ R| ≤ 3` and
`∑_t c_t = 16`, the within-`R` degree mass is `Dadj ≤ 12` (each rich hub spends `≥ 2` of its four
slots on twins), so the non-adjacent count `D = 42 - Dadj ≥ 30`.  The share-`1` design bound
`D ≤ ∑_t (c_t² - c_t)` then forces the unique solution `(n₀,n₁,n₂,n₃) = (0,1,0,5)`: five all-rich
twins (`c = 3`) and a unique twin `t*` meeting exactly one rich hub. -/
theorem poor_incidence_concentrates_S16 (G : SimpleGraph (Fin 18))
    (Hub Iso R : Finset (Fin 18))
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
    (hr7 : R.card = 7) (hS16 : ∑ r ∈ R, (G.neighborFinset r ∩ Iso).card = 16) :
    ∃ tstar ∈ Iso, (G.neighborFinset tstar ∩ R).card = 1 ∧
      ∀ t ∈ Iso, t ≠ tstar → (G.neighborFinset t ∩ R).card = 3 := by
  classical
  have hc3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ R).card ≤ 3 := by
    intro t ht
    calc (G.neighborFinset t ∩ R).card
        ≤ (G.neighborFinset t ∩ Hub).card :=
          Finset.card_le_card (Finset.inter_subset_inter (Finset.Subset.refl _) hRHub)
      _ = 3 := hiso3 t ht
  have hcsum : ∑ t ∈ Iso, (G.neighborFinset t ∩ R).card = 16 := by
    rw [cross_count G Iso R]; exact hS16
  have hsplit := offdiag_eq_eighteen G R
  rw [hr7] at hsplit
  -- `Dadj ≤ 12` (each rich hub spends `≥ 2` slots on twins).
  have hDadj12 : (R.offDiag.filter (fun p => G.Adj p.1 p.2)).card ≤ 12 := by
    have hsum := dadj_eq_sum_eighteen G R
    have hterm : ∀ a ∈ R,
        (G.neighborFinset a ∩ R).card + (G.neighborFinset a ∩ Iso).card ≤ 4 := by
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
    have hsumle : ∑ a ∈ R,
        ((G.neighborFinset a ∩ R).card + (G.neighborFinset a ∩ Iso).card) ≤ 28 := by
      calc ∑ a ∈ R, ((G.neighborFinset a ∩ R).card + (G.neighborFinset a ∩ Iso).card)
          ≤ ∑ _a ∈ R, 4 := Finset.sum_le_sum hterm
        _ = 28 := by rw [Finset.sum_const, hr7, smul_eq_mul]
    rw [Finset.sum_add_distrib, hS16] at hsumle
    rw [hsum]; omega
  have hDge : 30 ≤ (R.offDiag.filter (fun p => ¬G.Adj p.1 p.2)).card := by omega
  -- Each non-adjacent rich pair lies in a unique twin's off-diagonal trace (share-`1`).
  have hDbiU : (R.offDiag.filter (fun p => ¬G.Adj p.1 p.2))
      ⊆ Iso.biUnion (fun t => (G.neighborFinset t ∩ R).offDiag) :=
    rich_nonadj_biUnion_eighteen G Hub Iso R hdeg4 hshare hno2hub hRHub hRrich
  have hDle : (R.offDiag.filter (fun p => ¬G.Adj p.1 p.2)).card
      ≤ ∑ t ∈ Iso, ((G.neighborFinset t ∩ R).card * (G.neighborFinset t ∩ R).card
        - (G.neighborFinset t ∩ R).card) := by
    calc (R.offDiag.filter (fun p => ¬G.Adj p.1 p.2)).card
        ≤ (Iso.biUnion (fun t => (G.neighborFinset t ∩ R).offDiag)).card :=
          Finset.card_le_card hDbiU
      _ ≤ ∑ t ∈ Iso, ((G.neighborFinset t ∩ R).offDiag).card := Finset.card_biUnion_le
      _ = ∑ t ∈ Iso, ((G.neighborFinset t ∩ R).card * (G.neighborFinset t ∩ R).card
            - (G.neighborFinset t ∩ R).card) := by
          apply Finset.sum_congr rfl; intro t _; rw [Finset.offDiag_card]
  set N0 : ℕ := (Iso.filter (fun t => (G.neighborFinset t ∩ R).card = 0)).card with hN0def
  set N1 : ℕ := (Iso.filter (fun t => (G.neighborFinset t ∩ R).card = 1)).card with hN1def
  set N2 : ℕ := (Iso.filter (fun t => (G.neighborFinset t ∩ R).card = 2)).card with hN2def
  set N3 : ℕ := (Iso.filter (fun t => (G.neighborFinset t ∩ R).card = 3)).card with hN3def
  have eq_part : N0 + N1 + N2 + N3 = 6 := by
    rw [hN0def, hN1def, hN2def, hN3def]
    simp only [Finset.card_filter]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← hIso, Finset.card_eq_sum_ones]
    apply Finset.sum_congr rfl
    intro t ht
    have h3 := hc3 t ht
    set k := (G.neighborFinset t ∩ R).card with hk
    interval_cases k <;> decide
  have eq_csum : N1 + 2 * N2 + 3 * N3 = 16 := by
    rw [hN1def, hN2def, hN3def, ← hcsum]
    simp only [Finset.card_filter, Finset.mul_sum]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t ht
    have h3 := hc3 t ht
    set k := (G.neighborFinset t ∩ R).card with hk
    interval_cases k <;> decide
  have eq_sqsum : 2 * N2 + 6 * N3 = ∑ t ∈ Iso, ((G.neighborFinset t ∩ R).card
        * (G.neighborFinset t ∩ R).card - (G.neighborFinset t ∩ R).card) := by
    rw [hN2def, hN3def]
    simp only [Finset.card_filter, Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t ht
    have h3 := hc3 t ht
    set k := (G.neighborFinset t ∩ R).card with hk
    interval_cases k <;> decide
  have hsq30 : 30 ≤ 2 * N2 + 6 * N3 := by rw [eq_sqsum]; omega
  have hN0eq : N0 = 0 := by omega
  have hN1eq : N1 = 1 := by omega
  have hN2eq : N2 = 0 := by omega
  have hN3eq : N3 = 5 := by omega
  rw [hN1def] at hN1eq
  obtain ⟨tstar, htstareq⟩ := Finset.card_eq_one.mp hN1eq
  have htstarmem : tstar ∈ Iso.filter (fun t => (G.neighborFinset t ∩ R).card = 1) := by
    rw [htstareq]; exact Finset.mem_singleton_self tstar
  rw [Finset.mem_filter] at htstarmem
  obtain ⟨htstarIso, htstarc1⟩ := htstarmem
  refine ⟨tstar, htstarIso, htstarc1, ?_⟩
  intro t htIso htne
  have h3 := hc3 t htIso
  have hf0 : Iso.filter (fun t => (G.neighborFinset t ∩ R).card = 0) = ∅ :=
    Finset.card_eq_zero.mp (by rw [← hN0def]; exact hN0eq)
  have hf2 : Iso.filter (fun t => (G.neighborFinset t ∩ R).card = 2) = ∅ :=
    Finset.card_eq_zero.mp (by rw [← hN2def]; exact hN2eq)
  have hne0 : (G.neighborFinset t ∩ R).card ≠ 0 := by
    intro hc
    have hmem : t ∈ Iso.filter (fun t => (G.neighborFinset t ∩ R).card = 0) :=
      Finset.mem_filter.mpr ⟨htIso, hc⟩
    rw [hf0] at hmem; exact absurd hmem (Finset.notMem_empty t)
  have hne2 : (G.neighborFinset t ∩ R).card ≠ 2 := by
    intro hc
    have hmem : t ∈ Iso.filter (fun t => (G.neighborFinset t ∩ R).card = 2) :=
      Finset.mem_filter.mpr ⟨htIso, hc⟩
    rw [hf2] at hmem; exact absurd hmem (Finset.notMem_empty t)
  have hne1 : (G.neighborFinset t ∩ R).card ≠ 1 := by
    intro hc
    have hmem : t ∈ Iso.filter (fun t => (G.neighborFinset t ∩ R).card = 1) :=
      Finset.mem_filter.mpr ⟨htIso, hc⟩
    rw [htstareq, Finset.mem_singleton] at hmem; exact htne hmem
  omega

/-- **All rich hubs are saturated at `r = 7`, `S = 16`.**  The unique `(0,1,0,5)` design gives
`D = 30` exactly (`D ≤ 30` from the design, `D ≥ 30` from `Dadj ≤ 12`), hence `Dadj = 12`.  Since
`∑_R |N ∩ R| = 12` and `∑_R |N ∩ Iso| = 16` sum to `28 = 4·7 = ∑_R deg`, every rich hub spends all
four slots inside `Iso ∪ R`: its neighbourhood is closed in `Iso ∪ R`. -/
theorem rich_saturated_S16 (G : SimpleGraph (Fin 18)) (Hub Iso R : Finset (Fin 18))
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
    (hr7 : R.card = 7) (hS16 : ∑ r ∈ R, (G.neighborFinset r ∩ Iso).card = 16) :
    ∀ r ∈ R, G.neighborFinset r ⊆ Iso ∪ R := by
  classical
  obtain ⟨tstar, htstarIso, htstar1, htstaroth⟩ := poor_incidence_concentrates_S16 G Hub Iso R
    hdeg4 hiso3 hdisj hIso hshare hno2hub hRHub hRrich hr7 hS16
  -- The design bound `D ≤ 30`.
  have hbiUle : (Iso.biUnion (fun t => (G.neighborFinset t ∩ R).offDiag)).card ≤ 30 := by
    calc (Iso.biUnion (fun t => (G.neighborFinset t ∩ R).offDiag)).card
        ≤ ∑ t ∈ Iso, ((G.neighborFinset t ∩ R).offDiag).card := Finset.card_biUnion_le
      _ = ∑ t ∈ Iso, ((G.neighborFinset t ∩ R).card * (G.neighborFinset t ∩ R).card
            - (G.neighborFinset t ∩ R).card) := by
          apply Finset.sum_congr rfl; intro t _; rw [Finset.offDiag_card]
      _ = 30 := by
          rw [← Finset.add_sum_erase Iso _ htstarIso, htstar1]
          have herase : ∑ t ∈ Iso.erase tstar, ((G.neighborFinset t ∩ R).card
              * (G.neighborFinset t ∩ R).card - (G.neighborFinset t ∩ R).card)
              = ∑ _t ∈ Iso.erase tstar, 6 := by
            apply Finset.sum_congr rfl
            intro t ht
            obtain ⟨htne, htIso⟩ := Finset.mem_erase.mp ht
            rw [htstaroth t htIso htne]
          rw [herase, Finset.sum_const, Finset.card_erase_of_mem htstarIso, hIso, smul_eq_mul]
  have hsub := rich_nonadj_biUnion_eighteen G Hub Iso R hdeg4 hshare hno2hub hRHub hRrich
  have hDle30 : (R.offDiag.filter (fun p => ¬G.Adj p.1 p.2)).card ≤ 30 :=
    le_trans (Finset.card_le_card hsub) hbiUle
  -- `Dadj ≤ 12`, so `D = 30` and `Dadj = 12`.
  have hsum := dadj_eq_sum_eighteen G R
  have hterm : ∀ a ∈ R,
      (G.neighborFinset a ∩ R).card + (G.neighborFinset a ∩ Iso).card ≤ 4 := by
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
  have hDadj12 : (R.offDiag.filter (fun p => G.Adj p.1 p.2)).card ≤ 12 := by
    have hsumle : ∑ a ∈ R,
        ((G.neighborFinset a ∩ R).card + (G.neighborFinset a ∩ Iso).card) ≤ 28 := by
      calc ∑ a ∈ R, ((G.neighborFinset a ∩ R).card + (G.neighborFinset a ∩ Iso).card)
          ≤ ∑ _a ∈ R, 4 := Finset.sum_le_sum hterm
        _ = 28 := by rw [Finset.sum_const, hr7, smul_eq_mul]
    rw [Finset.sum_add_distrib, hS16] at hsumle
    rw [hsum]; omega
  have hsplit := offdiag_eq_eighteen G R
  rw [hr7] at hsplit
  have hDadjeq : (R.offDiag.filter (fun p => G.Adj p.1 p.2)).card = 12 := by omega
  have hsumR : ∑ a ∈ R, (G.neighborFinset a ∩ R).card = 12 := by rw [← hsum]; exact hDadjeq
  -- Each rich hub spends all four slots inside `Iso ∪ R`.
  have heach : ∀ a ∈ R,
      (G.neighborFinset a ∩ R).card + (G.neighborFinset a ∩ Iso).card = 4 := by
    have hsumf : ∑ a ∈ R, ((G.neighborFinset a ∩ R).card + (G.neighborFinset a ∩ Iso).card)
        = ∑ _a ∈ R, 4 := by
      rw [Finset.sum_add_distrib, hsumR, hS16, Finset.sum_const, hr7, smul_eq_mul]
    exact (Finset.sum_eq_sum_iff_of_le hterm).mp hsumf
  intro r hrR x hx
  have h4 := heach r hrR
  have hdisjRI : Disjoint (G.neighborFinset r ∩ R) (G.neighborFinset r ∩ Iso) := by
    apply Finset.disjoint_left.mpr
    intro y hy1 hy2
    exact Finset.disjoint_left.mp hdisj (hRHub (Finset.mem_inter.mp hy1).2)
      (Finset.mem_inter.mp hy2).2
  have hun : (G.neighborFinset r ∩ R) ∪ (G.neighborFinset r ∩ Iso) ⊆ G.neighborFinset r := by
    rw [← Finset.inter_union_distrib_left]; exact Finset.inter_subset_left
  have hcardun : ((G.neighborFinset r ∩ R) ∪ (G.neighborFinset r ∩ Iso)).card = 4 := by
    rw [Finset.card_union_of_disjoint hdisjRI]; exact h4
  have hNcard : (G.neighborFinset r).card = 4 := by
    rw [G.card_neighborFinset_eq_degree, hdeg4 r (hRHub hrR)]
  have heqN : (G.neighborFinset r ∩ R) ∪ (G.neighborFinset r ∩ Iso) = G.neighborFinset r :=
    Finset.eq_of_subset_of_card_le hun (by rw [hNcard, hcardun])
  rw [← heqN, Finset.mem_union, Finset.mem_inter, Finset.mem_inter] at hx
  rw [Finset.mem_union]
  tauto

/-- **NODE 3 — the `r = 7`, `S = 16` kill (saturation counting, no `C₄`).**  An `M`-edge endpoint
`z` meeting two poor hubs `hg₁, hg₂`.  All rich hubs are saturated (`rich_saturated_S16`), so the
`M`-partner `z'`'s two hub-neighbours are **all poor**.  But neither can be `hg₁` nor `hg₂` (a hub
adjacent to both `M`-endpoints would yield a good triangle, `no_hub_adj_both`), leaving only the
single third poor hub — `z'` cannot have two hub-neighbours.  The `C₄`/`K₂₃`/regime hypotheses are
not needed: the residual dies by this counting contradiction. -/
theorem rich_seven_S16_two_poor_false_eighteen (G : SimpleGraph (Fin 18))
    (Hub Iso : Finset (Fin 18))
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
    (_hC4 : ¬∃ a b c d : Fin 18, ({a, b, c, d} : Finset (Fin 18)).card = 4 ∧
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
    (_hres : G.Adj hg1 hg2 ∨ (G.neighborFinset hg1 ∩ G.neighborFinset hg2 ∩ Iso).card = 0)
    (hr7 : (Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)).card = 7)
    (hS16 : ∑ r ∈ Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card),
        (G.neighborFinset r ∩ Iso).card = 16) :
    False := by
  classical
  set Z : Finset (Fin 18) := Finset.univ \ (Hub ∪ Iso) with hZdef
  set R : Finset (Fin 18) := Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card) with hRdef
  have hRHub : R ⊆ Hub := Finset.filter_subset _ _
  have hRrich : ∀ a ∈ R, 2 ≤ (G.neighborFinset a ∩ Iso).card := by
    intro a ha; rw [hRdef, Finset.mem_filter] at ha; exact ha.2
  have hsat := rich_saturated_S16 G Hub Iso R hdeg4 hiso3 hdisj hIso hshare hno2hub hRHub hRrich
    hr7 hS16
  -- The `M`-partner `zp`.
  have hZcard : Z.card = 2 := z_card_two_eighteen Hub Iso hdisj hHub hIso
  have hzerase : (Z.erase z).card = 1 := by rw [Finset.card_erase_of_mem hz, hZcard]
  obtain ⟨zp, hzp⟩ := Finset.card_eq_one.mp hzerase
  have hzpZe : zp ∈ Z.erase z := by rw [hzp]; exact Finset.mem_singleton_self _
  have hzpZ : zp ∈ Z := Finset.mem_of_mem_erase hzpZe
  have hzpz : zp ≠ z := (Finset.mem_erase.mp hzpZe).1
  obtain ⟨_, hzphub2, _⟩ := z_two_hub_nbrs_eighteen G Hub Iso hiso3 hdisj hHub hIso hdsum
    hdeg3 hisodeg3 hleak zp hzpZ
  have hzpnotHub : zp ∉ Hub := by
    rw [hZdef, Finset.mem_sdiff, Finset.mem_union, not_or] at hzpZ; exact hzpZ.2.1
  have hzpnotIso : zp ∉ Iso := by
    rw [hZdef, Finset.mem_sdiff, Finset.mem_union, not_or] at hzpZ; exact hzpZ.2.2
  -- The poor hub set `P` has card `3`.
  set P : Finset (Fin 18) := Hub.filter (fun h => ¬ 2 ≤ (G.neighborFinset h ∩ Iso).card) with hPdef
  have hPcard : P.card = 3 := by
    have := Finset.card_filter_add_card_filter_not (s := Hub)
      (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)
    rw [← hRdef, ← hPdef, hHub, hr7] at this; omega
  have hg1Hub : hg1 ∈ Hub := (Finset.mem_inter.mp hg1mem).2
  have hg2Hub : hg2 ∈ Hub := (Finset.mem_inter.mp hg2mem).2
  have hg1P : hg1 ∈ P := by rw [hPdef, Finset.mem_filter]; exact ⟨hg1Hub, by omega⟩
  have hg2P : hg2 ∈ P := by rw [hPdef, Finset.mem_filter]; exact ⟨hg2Hub, by omega⟩
  -- `zp`'s two hub-neighbours are all poor and avoid `hg1, hg2`.
  have hzpsub : G.neighborFinset zp ∩ Hub ⊆ P \ ({hg1, hg2} : Finset (Fin 18)) := by
    intro g hg
    have hgHub : g ∈ Hub := (Finset.mem_inter.mp hg).2
    have hzpg : G.Adj zp g := (G.mem_neighborFinset _ _).mp (Finset.mem_inter.mp hg).1
    have hgP : g ∈ P := by
      rw [hPdef, Finset.mem_filter]
      refine ⟨hgHub, ?_⟩
      intro hgrich
      have hgR : g ∈ R := by rw [hRdef, Finset.mem_filter]; exact ⟨hgHub, hgrich⟩
      have hzping : zp ∈ G.neighborFinset g := (G.mem_neighborFinset g zp).mpr hzpg.symm
      have hmem := hsat g hgR hzping
      rw [Finset.mem_union] at hmem
      rcases hmem with h | h
      · exact hzpnotIso h
      · exact hzpnotHub (hRHub h)
    rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or]
    refine ⟨hgP, ?_, ?_⟩
    · intro he
      subst he
      have hzg : G.Adj g z :=
        ((G.mem_neighborFinset z g).mp (Finset.mem_inter.mp hg1mem).1).symm
      exact no_hub_adj_both_mends_eighteen G Hub Iso hdeg4 hiso3 hdisj hHub hIso hdsum hdeg3
        hisodeg3 hleak hT g hg1Hub z hz zp hzpZ (Ne.symm hzpz) ⟨hzg, hzpg.symm⟩
    · intro he
      subst he
      have hzg : G.Adj g z :=
        ((G.mem_neighborFinset z g).mp (Finset.mem_inter.mp hg2mem).1).symm
      exact no_hub_adj_both_mends_eighteen G Hub Iso hdeg4 hiso3 hdisj hHub hIso hdsum hdeg3
        hisodeg3 hleak hT g hg2Hub z hz zp hzpZ (Ne.symm hzpz) ⟨hzg, hzpg.symm⟩
  -- `P \ {hg1, hg2}` has card `1`, contradicting `|N(zp) ∩ Hub| = 2`.
  have hsub12 : ({hg1, hg2} : Finset (Fin 18)) ⊆ P := by
    intro x hx
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hg1P
    · exact hg2P
  have h2 : ({hg1, hg2} : Finset (Fin 18)).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simp [hg1ne]), Finset.card_singleton]
  have hsdiffcard : (P \ ({hg1, hg2} : Finset (Fin 18))).card = 1 := by
    have hadd := Finset.card_sdiff_add_card_inter P ({hg1, hg2} : Finset (Fin 18))
    rw [Finset.inter_eq_right.mpr hsub12, hPcard, h2] at hadd
    omega
  have hle := Finset.card_le_card hzpsub
  rw [hzphub2, hsdiffcard] at hle
  omega

end N18

end ACMax
