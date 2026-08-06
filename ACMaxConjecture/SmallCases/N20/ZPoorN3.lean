import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N20.Core
import ACMaxConjecture.SmallCases.N20.RichCount
import ACMaxConjecture.SmallCases.N20.StarTriangleStruct

/-!
# The `r = 7`, `S = 15` rich iso-degree sequence and poor-incidence concentration (`n = 18`)

For the tight `e(M) = 1`, all-degree-`4`, `(|Hub|, |Iso|) = (11, 6)` profile with seven rich hubs
(`R = {h : 2 ≤ |N(h) ∩ Iso|}`, `|R| = 7`) and iso-incidence sum `S = ∑_R |N ∩ Iso| = 15`, the
six remaining iso-incidences live on the three poor hubs.  Two structural facts are extracted here:

* `rich_isodeg_seq_twenty` (LEAF): the rich iso-degrees are `(3, 2, 2, 2, 2, 2, 2)` — a unique
  rich hub `w` of iso-degree `3`, the other six of iso-degree `2` (pure arithmetic on the excess).
-/

namespace ACMax

open scoped Classical

namespace N20

/-- **The `r = 7`, `S = 15` rich iso-degree sequence.**  Seven rich hubs, each meeting `≥ 2`
`M`-isolated twins, with total iso-incidence `15 = 2·7 + 1`, are forced into the degree sequence
`(3, 2, 2, 2, 2, 2, 2)`: a unique rich hub `w` of iso-degree `3` and six of iso-degree exactly `2`.
The excess over the baseline `2` is `1`, which a single hub must carry (any iso-degree `≥ 3` hub
already exhausts it, and an iso-degree-`4` hub is impossible). -/
theorem rich_isodeg_seq_twenty (G : SimpleGraph (Fin 20)) (Iso : Finset (Fin 20))
    (R : Finset (Fin 20)) (hRge : ∀ a ∈ R, 2 ≤ (G.neighborFinset a ∩ Iso).card)
    (hr7 : R.card = 7) (hS15 : ∑ r ∈ R, (G.neighborFinset r ∩ Iso).card = 15) :
    ∃ w ∈ R, (G.neighborFinset w ∩ Iso).card = 3 ∧
      ∀ r ∈ R, r ≠ w → (G.neighborFinset r ∩ Iso).card = 2 := by
  classical
  -- The excess sum `∑ (isoDeg - 2) = 1`.
  have hkey : ∑ r ∈ R, ((G.neighborFinset r ∩ Iso).card - 2) = 1 := by
    have hback : ∑ r ∈ R, (((G.neighborFinset r ∩ Iso).card - 2) + 2)
        = ∑ r ∈ R, (G.neighborFinset r ∩ Iso).card := by
      apply Finset.sum_congr rfl
      intro r hr; have := hRge r hr; omega
    rw [Finset.sum_add_distrib, Finset.sum_const, hr7, smul_eq_mul] at hback
    omega
  -- A hub carrying positive excess.
  have hpos : ∃ w ∈ R, 1 ≤ (G.neighborFinset w ∩ Iso).card - 2 := by
    by_contra hcon
    push Not at hcon
    have hzero : ∑ r ∈ R, ((G.neighborFinset r ∩ Iso).card - 2) = 0 := by
      apply Finset.sum_eq_zero
      intro r hr; have := hcon r hr; omega
    omega
  obtain ⟨w, hwR, hwpos⟩ := hpos
  refine ⟨w, hwR, ?_, ?_⟩
  · -- `isoDeg w = 3`: the excess at `w` is exactly `1`.
    have hsplit := Finset.add_sum_erase R
      (fun r => (G.neighborFinset r ∩ Iso).card - 2) hwR
    have hrest : 0 ≤ ∑ r ∈ R.erase w, ((G.neighborFinset r ∩ Iso).card - 2) := Nat.zero_le _
    have hwle : (G.neighborFinset w ∩ Iso).card - 2 ≤ 1 := by omega
    have hwge := hRge w hwR
    omega
  · -- The other rich hubs have iso-degree exactly `2`.
    intro r hrR hrw
    have hsplit := Finset.add_sum_erase R
      (fun x => (G.neighborFinset x ∩ Iso).card - 2) hwR
    have hrest0 : ∑ x ∈ R.erase w, ((G.neighborFinset x ∩ Iso).card - 2) = 0 := by omega
    have hrmem : r ∈ R.erase w := Finset.mem_erase.mpr ⟨hrw, hrR⟩
    have hr0 : (G.neighborFinset r ∩ Iso).card - 2 = 0 :=
      (Finset.sum_eq_zero_iff.mp hrest0) r hrmem
    have := hRge r hrR; omega

/-- **Off-diagonal split of the rich pairs (LEAF).**  The ordered off-diagonal pairs of `R` split
into the non-adjacent (`D`) and adjacent (`Dadj`) parts, and their cardinalities sum to the
off-diagonal count `|R|² − |R|`.  This is the counting identity factored out of
`rich_count_le_seven_twenty`. -/
theorem offdiag_eq_twenty (G : SimpleGraph (Fin 20)) (R : Finset (Fin 20)) :
    (R.offDiag.filter (fun p => ¬G.Adj p.1 p.2)).card
      + (R.offDiag.filter (fun p => G.Adj p.1 p.2)).card
      = R.card * R.card - R.card := by
  classical
  rw [add_comm, Finset.card_filter_add_card_filter_not, Finset.offDiag_card]

/-- **`e_RR ≤ 7` — rich-internal edges (LEAF).**  Each rich hub (degree `4`, meeting `≥ 2`
`M`-isolated twins) has at most `2` rich neighbours (the other two degree slots go to its iso-twins),
so the ordered adjacent rich pairs number `≤ 2·|R| = 14`.  Equivalently `e_RR ≤ 7`. -/
theorem eRR_le_seven_twenty (G : SimpleGraph (Fin 20)) (Hub Iso R : Finset (Fin 20))
    (hdeg4 : ∀ h ∈ Hub, G.degree h = 4) (hdisj : Disjoint Hub Iso) (hRHub : R ⊆ Hub)
    (hRrich : ∀ a ∈ R, 2 ≤ (G.neighborFinset a ∩ Iso).card) (hr7 : R.card = 7) :
    (R.offDiag.filter (fun p => G.Adj p.1 p.2)).card ≤ 14 := by
  classical
  -- Each rich hub has `≤ 2` hub-neighbours inside `R`.
  have hRnbr : ∀ a ∈ R, (G.neighborFinset a ∩ R).card ≤ 2 := by
    intro a ha
    have haHub := hRHub ha
    have hae := hRrich a ha
    have hd4 : (G.neighborFinset a).card = 4 := by
      rw [G.card_neighborFinset_eq_degree, hdeg4 a haHub]
    have hdisjNR : Disjoint (G.neighborFinset a ∩ R) (G.neighborFinset a ∩ Iso) := by
      apply Finset.disjoint_left.mpr
      intro x hx1 hx2
      exact Finset.disjoint_left.mp hdisj (hRHub (Finset.mem_inter.mp hx1).2)
        (Finset.mem_inter.mp hx2).2
    have hun : (G.neighborFinset a ∩ R) ∪ (G.neighborFinset a ∩ Iso) ⊆ G.neighborFinset a := by
      rw [← Finset.inter_union_distrib_left]; exact Finset.inter_subset_left
    have hle := Finset.card_le_card hun
    rw [Finset.card_union_of_disjoint hdisjNR, hd4] at hle
    omega
  set Off : Finset (Fin 20 × Fin 20) := R.offDiag with hOffdef
  set Dadj : Finset (Fin 20 × Fin 20) := Off.filter (fun p => G.Adj p.1 p.2) with hDadjdef
  have hDadjle : Dadj.card ≤ 2 * R.card := by
    have hmaps : (Dadj : Set (Fin 20 × Fin 20)).MapsTo Prod.fst R := by
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
      _ = 2 * R.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  rw [hr7] at hDadjle; omega

/-- **Poor-incidence concentration (HARD KERNEL).**  At `r = 7`, rich iso-incidence sum `S = 15`,
the six `M`-isolated twins distribute their rich-hub incidences as `(3, 3, 3, 3, 3, 0)`: five
*all-rich* twins (each meeting three rich hubs) and a unique *all-poor* twin `t₆` (meeting no rich
hub).  Arithmetic: with `c_t := |N(t) ∩ R| ≤ 3` and `∑_t c_t = 15`, the off-diagonal count
`r² − r = 42 = D + Dadj`, `Dadj ≤ 2·e_RR ≤ 14` forces `D ≥ 28`, while the share-`1` bound gives
`D ≤ ∑_t (c_t² − c_t) = 2·n₂ + 6·n₃` (`n_k = #{t : c_t = k}`).  The system
`n₀+n₁+n₂+n₃ = 6`, `n₁+2n₂+3n₃ = 15`, `2n₂+6n₃ ≥ 28` has the unique solution
`(n₀,n₁,n₂,n₃) = (1,0,0,5)`. -/
theorem poor_incidence_concentrates_twenty (G : SimpleGraph (Fin 20))
    (Hub Iso R : Finset (Fin 20))
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
    ∃ t6 ∈ Iso, (G.neighborFinset t6 ∩ R).card = 0 ∧
      ∀ t ∈ Iso, t ≠ t6 → (G.neighborFinset t ∩ R).card = 3 := by
  classical
  -- `c t := |N(t) ∩ R|` is at most `3` (a twin meets exactly three hubs).
  have hc3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ R).card ≤ 3 := by
    intro t ht
    calc (G.neighborFinset t ∩ R).card
        ≤ (G.neighborFinset t ∩ Hub).card :=
          Finset.card_le_card (Finset.inter_subset_inter (Finset.Subset.refl _) hRHub)
      _ = 3 := hiso3 t ht
  -- Rich-incidence sum: `∑_{t∈Iso} c t = ∑_{r∈R} |N(r)∩Iso| = 15`.
  have hcsum : ∑ t ∈ Iso, (G.neighborFinset t ∩ R).card = 15 := by
    rw [cross_count_twenty G Iso R]; exact hS15
  -- Off-diagonal split and the `D ≥ 28` bound.
  have hsplit := offdiag_eq_twenty G R
  rw [hr7] at hsplit
  have hDadj := eRR_le_seven_twenty G Hub Iso R hdeg4 hdisj hRHub hRrich hr7
  have hDge : 28 ≤ (R.offDiag.filter (fun p => ¬G.Adj p.1 p.2)).card := by omega
  -- Each non-adjacent rich pair lies in a unique twin's off-diagonal trace (share-`1`).
  have hDbiU : (R.offDiag.filter (fun p => ¬G.Adj p.1 p.2))
      ⊆ Iso.biUnion (fun t => (G.neighborFinset t ∩ R).offDiag) := by
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
  -- Cardinalities of the four `c`-classes.
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
  have eq_csum : N1 + 2 * N2 + 3 * N3 = 15 := by
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
  have hsq28 : 28 ≤ 2 * N2 + 6 * N3 := by rw [eq_sqsum]; omega
  -- The linear system forces `(n₀,n₁,n₂,n₃) = (1,0,0,5)`.
  have hN0eq : N0 = 1 := by omega
  have hN1eq : N1 = 0 := by omega
  have hN2eq : N2 = 0 := by omega
  have hN3eq : N3 = 5 := by omega
  -- Extract the unique all-poor twin `t₆`.
  rw [hN0def] at hN0eq
  obtain ⟨t6, ht6eq⟩ := Finset.card_eq_one.mp hN0eq
  have ht6mem : t6 ∈ Iso.filter (fun t => (G.neighborFinset t ∩ R).card = 0) := by
    rw [ht6eq]; exact Finset.mem_singleton_self t6
  rw [Finset.mem_filter] at ht6mem
  obtain ⟨ht6Iso, ht6c0⟩ := ht6mem
  refine ⟨t6, ht6Iso, ht6c0, ?_⟩
  intro t htIso htne
  have h3 := hc3 t htIso
  have hf1 : Iso.filter (fun t => (G.neighborFinset t ∩ R).card = 1) = ∅ :=
    Finset.card_eq_zero.mp (by rw [← hN1def]; exact hN1eq)
  have hf2 : Iso.filter (fun t => (G.neighborFinset t ∩ R).card = 2) = ∅ :=
    Finset.card_eq_zero.mp (by rw [← hN2def]; exact hN2eq)
  have hne1 : (G.neighborFinset t ∩ R).card ≠ 1 := by
    intro hc
    have hmem : t ∈ Iso.filter (fun t => (G.neighborFinset t ∩ R).card = 1) :=
      Finset.mem_filter.mpr ⟨htIso, hc⟩
    rw [hf1] at hmem; exact absurd hmem (Finset.notMem_empty t)
  have hne2 : (G.neighborFinset t ∩ R).card ≠ 2 := by
    intro hc
    have hmem : t ∈ Iso.filter (fun t => (G.neighborFinset t ∩ R).card = 2) :=
      Finset.mem_filter.mpr ⟨htIso, hc⟩
    rw [hf2] at hmem; exact absurd hmem (Finset.notMem_empty t)
  have hne0 : (G.neighborFinset t ∩ R).card ≠ 0 := by
    intro hc
    have hmem : t ∈ Iso.filter (fun t => (G.neighborFinset t ∩ R).card = 0) :=
      Finset.mem_filter.mpr ⟨htIso, hc⟩
    rw [ht6eq, Finset.mem_singleton] at hmem; exact htne hmem
  omega

end N20

end ACMax
