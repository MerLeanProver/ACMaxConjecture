import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N19.Core
import ACMaxConjecture.SmallCases.N19.TwoHubSelect
import ACMaxConjecture.SmallCases.N19.StarTriangleStruct
import ACMaxConjecture.SmallCases.N19.RichCount
import ACMaxConjecture.SmallCases.N19.RichZdeg
import ACMaxConjecture.SmallCases.N19.ZVertex
import ACMaxConjecture.SmallCases.N19.ZPoorDispatch
import ACMaxConjecture.SmallCases.N19.ZPoorCut

/-!
# The `r ≠ 7` rich-count crux and the no-iso-zero-hub bundle (`n = 19`, `|Hub| = 11`)

This file closes the structural residual `hnozero ∧ |R| = 6` for the clean `(11, 6, 44)` octahedron,
the last gap in `TwinCert19OctaMass`.

* `rich_count_ne_seven_nineteen` (`r ≠ 7`).  **Mechanical port** of `rich_count_ne_seven_eighteen`:
  the trace argument is identical because the off-diagonal count (`|R| = 7 ⟹ 42`), the per-twin
  rich-trace bound (`|Iso| = 6`), the all-degree-`4` handshake (`∑_R deg = 28`) and the `z_R ≥ 2`
  rich-side `Z`-mass are all unchanged at `|Hub| = 11`.  (The `n = 18` lower bound `S ≥ 15` is *not*
  used by the trace argument; only `z_R ≥ 2` and `Off.card = 42` drive `Q ≥ 16 + S`, forcing every
  twin to meet three rich hubs, `S = 18`, hence two iso-degree-`4` rich hubs, excluded by
  `two_iso_four_hubs_impossible_nineteen`.)  The only `|Hub| = 11` adaptation is that
  `zdeg_split_nineteen` returns a disjunction with `ZPoorCutConfig G`, discharged by `hcut`.

* `rich_six_no_iso_zero_nineteen` — the `hnozero ∧ |R| = 6` bundle.  `|R| ∈ {6, 7}`
  (`rich_count_ge_six_nineteen` via the `r = 5` octahedron residual `r5_resid_nineteen`,
  `rich_count_le_seven_nineteen`); `r ≠ 7` pins `|R| = 6`.
-/

namespace ACMax

open scoped Classical

namespace N19

/-- **Two iso-degree-`4` hubs are impossible (`|Iso| = 6`).**  Port of
`two_iso_four_hubs_impossible_eighteen`: if two distinct hubs `a, b` each meet all four neighbours
inside `Iso` and share at most one `M`-isolated twin, their iso-traces union to `≥ 7 > 6`. -/
theorem two_iso_four_hubs_impossible_nineteen (G : SimpleGraph (Fin 19)) (Iso : Finset (Fin 19))
    (hIso : Iso.card = 6) (a b : Fin 19)
    (ha4 : (G.neighborFinset a ∩ Iso).card = 4) (hb4 : (G.neighborFinset b ∩ Iso).card = 4)
    (hshare : (G.neighborFinset a ∩ G.neighborFinset b ∩ Iso).card ≤ 1) :
    False := by
  classical
  have hunionsub : (G.neighborFinset a ∩ Iso) ∪ (G.neighborFinset b ∩ Iso) ⊆ Iso := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx <;> exact (Finset.mem_inter.mp hx).2
  have hunionle : ((G.neighborFinset a ∩ Iso) ∪ (G.neighborFinset b ∩ Iso)).card ≤ 6 := by
    calc ((G.neighborFinset a ∩ Iso) ∪ (G.neighborFinset b ∩ Iso)).card
        ≤ Iso.card := Finset.card_le_card hunionsub
      _ = 6 := hIso
  have hinter : (G.neighborFinset a ∩ Iso) ∩ (G.neighborFinset b ∩ Iso)
      = G.neighborFinset a ∩ G.neighborFinset b ∩ Iso := by
    ext x; simp only [Finset.mem_inter]; tauto
  have hIE := Finset.card_union_add_card_inter
    (G.neighborFinset a ∩ Iso) (G.neighborFinset b ∩ Iso)
  rw [hinter] at hIE
  omega

/-- **`r ≠ 7` — the rich count is not seven (`n = 19`, `|Hub| = 11`).**  Port of
`rich_count_ne_seven_eighteen`; the `Z`-side rich bound `z_R ≥ 2` comes from `zdeg_split_nineteen`,
whose `ZPoorCutConfig` disjunct is discharged by `hcut`. -/
theorem rich_count_ne_seven_nineteen (G : SimpleGraph (Fin 19)) (Hub Iso : Finset (Fin 19))
    (hdeg4 : ∀ h ∈ Hub, G.degree h = 4)
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdisj : Disjoint Hub Iso) (hHub : Hub.card = 11) (hIso : Iso.card = 6)
    (hisodeg3 : ∀ t ∈ Iso, G.degree t = 3)
    (hdeg3 : ∀ v : Fin 19, 3 ≤ G.degree v)
    (hdsum : ∑ w ∈ Hub, G.degree w = 44)
    (hleak : ∑ h ∈ Hub, (G.neighborFinset h ∩ (Finset.univ \ (Hub ∪ Iso))).card ≤ 4)
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hno2hub : ¬∃ h₁ h₂ : Fin 19, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card)
    (hC4 : ¬∃ a b c d : Fin 19, ({a, b, c, d} : Finset (Fin 19)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (hK23 : ¬∃ a b c d e : Fin 19, ({a, b, c, d, e} : Finset (Fin 19)).card = 5 ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
      G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 19)
    (hT : ¬∃ x y z : Fin 19, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧
      G.degree x + G.degree y + G.degree z ≤ 11)
    (hcut : ¬ ZPoorCutConfig G) :
    (Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)).card ≠ 7 := by
  classical
  intro hr7
  set Z : Finset (Fin 19) := Finset.univ \ (Hub ∪ Iso) with hZdef
  set R : Finset (Fin 19) := Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card) with hRdef
  have hRsubHub : R ⊆ Hub := Finset.filter_subset _ _
  have hRmem : ∀ a, a ∈ R ↔ a ∈ Hub ∧ 2 ≤ (G.neighborFinset a ∩ Iso).card := by
    intro a; rw [hRdef, Finset.mem_filter]
  -- Each rich hub has `≤ 2` rich (hence hub) neighbours.
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
  -- `z_R ≥ 2`.
  obtain ⟨hzRge, _⟩ := (zdeg_split_nineteen G Hub Iso hdeg4 hiso3 hdisj hHub hIso hdeg3 hisodeg3
    hdsum hleak hshare hno2hub hC4 hK23 hT).resolve_right hcut
  rw [← hRdef, ← hZdef] at hzRge
  -- `S := ∑_R a`, cross-counted as `∑_t c_t`.
  set S : ℕ := ∑ r ∈ R, (G.neighborFinset r ∩ Iso).card with hSdef
  have hcross : ∑ t ∈ Iso, (G.neighborFinset t ∩ R).card = S := by
    rw [hSdef]; exact cross_count_nineteen G Iso R
  -- Rich-degree handshake: `∑_R|N∩Hub| + S + z_R = 28`.
  have hdeg28 : ∑ r ∈ R, G.degree r = 28 := by
    rw [Finset.sum_congr rfl (fun r hr => hdeg4 r (hRsubHub hr)), Finset.sum_const, hr7,
      smul_eq_mul]
  have hsplit3 : ∑ r ∈ R, (G.neighborFinset r ∩ Hub).card + S
      + ∑ r ∈ R, (G.neighborFinset r ∩ Z).card = 28 := by
    have hcong : ∑ r ∈ R, ((G.neighborFinset r ∩ Hub).card + (G.neighborFinset r ∩ Iso).card
        + (G.neighborFinset r ∩ Z).card) = ∑ r ∈ R, G.degree r :=
      Finset.sum_congr rfl (fun r _ => nbr_split_three_nineteen G Hub Iso hdisj r)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hcong
    rw [hdeg28] at hcong; rw [hSdef]; omega
  -- Off-diagonal of `R`.
  set Off : Finset (Fin 19 × Fin 19) := R.offDiag with hOffdef
  have hOffcard : Off.card = 42 := by rw [hOffdef, Finset.offDiag_card, hr7]
  set Dadj : Finset (Fin 19 × Fin 19) := Off.filter (fun p => G.Adj p.1 p.2) with hDadjdef
  set D : Finset (Fin 19 × Fin 19) := Off.filter (fun p => ¬G.Adj p.1 p.2) with hDdef
  have hDsplit : D.card + Dadj.card = Off.card := by
    rw [hDdef, hDadjdef, add_comm]
    exact Finset.card_filter_add_card_filter_not _
  -- `Dadj ≤ ∑_R|N∩R| ≤ ∑_R|N∩Hub|`.
  have hDadjle : Dadj.card ≤ ∑ a ∈ R, (G.neighborFinset a ∩ R).card := by
    have hmaps : (Dadj : Set (Fin 19 × Fin 19)).MapsTo Prod.fst R := by
      intro p hp
      rw [hDadjdef, Finset.coe_filter] at hp
      have hpoff : p ∈ Off := hp.1
      rw [hOffdef, Finset.mem_offDiag] at hpoff
      exact hpoff.1
    rw [Finset.card_eq_sum_card_fiberwise hmaps]
    apply Finset.sum_le_sum
    intro a _
    have hsub : Dadj.filter (fun p => p.1 = a) ⊆ (G.neighborFinset a ∩ R).map
        ⟨fun b => (a, b), fun b₁ b₂ h => by simpa using h⟩ := by
      intro p hp
      rw [Finset.mem_filter, hDadjdef, Finset.mem_filter, hOffdef, Finset.mem_offDiag] at hp
      obtain ⟨⟨⟨_, hp2R, _⟩, hadj⟩, hfst⟩ := hp
      rw [Finset.mem_map]
      refine ⟨p.2, ?_, ?_⟩
      · rw [Finset.mem_inter, G.mem_neighborFinset]; exact ⟨hfst ▸ hadj, hp2R⟩
      · rw [← hfst]
        exact Prod.eta p
    calc (Dadj.filter (fun p => p.1 = a)).card
        ≤ ((G.neighborFinset a ∩ R).map _).card := Finset.card_le_card hsub
      _ = (G.neighborFinset a ∩ R).card := Finset.card_map _
  have hRHub : ∑ a ∈ R, (G.neighborFinset a ∩ R).card
      ≤ ∑ a ∈ R, (G.neighborFinset a ∩ Hub).card := by
    apply Finset.sum_le_sum
    intro a _
    exact Finset.card_le_card (Finset.inter_subset_inter (Finset.Subset.refl _) hRsubHub)
  -- Non-adjacent rich pairs embed into the twins' rich-trace off-diagonals.
  have hDbiU : D ⊆ Iso.biUnion (fun t => (G.neighborFinset t ∩ R).offDiag) := by
    intro p hp
    rw [hDdef, Finset.mem_filter, hOffdef, Finset.mem_offDiag] at hp
    obtain ⟨⟨hp1R, hp2R, hne⟩, hnadj⟩ := hp
    obtain ⟨hp1Hub, hp1e⟩ := (hRmem p.1).mp hp1R
    obtain ⟨hp2Hub, hp2e⟩ := (hRmem p.2).mp hp2R
    have hsh1 := rich_nonadj_share_eq_one_nineteen G Hub Iso hshare hno2hub p.1 p.2 hp1Hub hp2Hub
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
  have hDle : D.card ≤ ∑ t ∈ Iso, ((G.neighborFinset t ∩ R).card * (G.neighborFinset t ∩ R).card
      - (G.neighborFinset t ∩ R).card) := by
    calc D.card ≤ (Iso.biUnion (fun t => (G.neighborFinset t ∩ R).offDiag)).card :=
          Finset.card_le_card hDbiU
      _ ≤ ∑ t ∈ Iso, ((G.neighborFinset t ∩ R).offDiag).card := Finset.card_biUnion_le
      _ = ∑ t ∈ Iso, ((G.neighborFinset t ∩ R).card * (G.neighborFinset t ∩ R).card
            - (G.neighborFinset t ∩ R).card) :=
          Finset.sum_congr rfl (fun t _ => Finset.offDiag_card _)
  -- Combine the two bounds: `∑_t (c_t² − c_t) ≥ 16 + S`.
  set Q : ℕ := ∑ t ∈ Iso, ((G.neighborFinset t ∩ R).card * (G.neighborFinset t ∩ R).card
      - (G.neighborFinset t ∩ R).card) with hQdef
  have hQbig : 16 + S ≤ Q := by omega
  -- Per-twin bound: `c_t² − c_t ≤ c_t + 3·[c_t = 3]`, summing to `S + 3·n₃`.
  set n3 : ℕ := (Iso.filter (fun t => (G.neighborFinset t ∩ R).card = 3)).card with hn3def
  have hQsmall : Q ≤ S + 3 * n3 := by
    have hpt : ∀ t ∈ Iso, (G.neighborFinset t ∩ R).card * (G.neighborFinset t ∩ R).card
        - (G.neighborFinset t ∩ R).card
        ≤ (G.neighborFinset t ∩ R).card
          + 3 * (if (G.neighborFinset t ∩ R).card = 3 then 1 else 0) := by
      intro t ht
      have hc3 : (G.neighborFinset t ∩ R).card ≤ 3 := by
        calc (G.neighborFinset t ∩ R).card ≤ (G.neighborFinset t ∩ Hub).card :=
              Finset.card_le_card (Finset.inter_subset_inter (Finset.Subset.refl _) hRsubHub)
          _ = 3 := hiso3 t ht
      set c := (G.neighborFinset t ∩ R).card with hcv
      interval_cases c <;> simp
    calc Q ≤ ∑ t ∈ Iso, ((G.neighborFinset t ∩ R).card
              + 3 * (if (G.neighborFinset t ∩ R).card = 3 then 1 else 0)) :=
          Finset.sum_le_sum hpt
      _ = (∑ t ∈ Iso, (G.neighborFinset t ∩ R).card)
            + 3 * ∑ t ∈ Iso, (if (G.neighborFinset t ∩ R).card = 3 then 1 else 0) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ = S + 3 * n3 := by rw [hcross, hn3def, Finset.card_filter]
  -- `n₃ = 6`: every twin meets exactly three rich hubs, whence `S = 18`.
  have hn3le : n3 ≤ 6 := by
    rw [hn3def, ← hIso]; exact Finset.card_le_card (Finset.filter_subset _ _)
  have hn3_6 : n3 = 6 := by omega
  have hfilter_all : Iso.filter (fun t => (G.neighborFinset t ∩ R).card = 3) = Iso :=
    Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by rw [hIso, ← hn3def, hn3_6])
  have hallc3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ R).card = 3 := by
    intro t ht
    have hmem : t ∈ Iso.filter (fun t => (G.neighborFinset t ∩ R).card = 3) := by
      rw [hfilter_all]; exact ht
    exact (Finset.mem_filter.mp hmem).2
  have hS18 : S = 18 := by
    rw [← hcross, Finset.sum_congr rfl hallc3, Finset.sum_const, hIso, smul_eq_mul]
  -- `N2`: at most two rich hubs have iso-degree `≥ 3`.
  set A3 : Finset (Fin 19) := R.filter (fun h => 3 ≤ (G.neighborFinset h ∩ Iso).card) with hA3def
  have hN2 : A3.card ≤ 2 := by
    have heq : A3 = Hub.filter (fun h => G.degree h = 4 ∧ 3 ≤ (G.neighborFinset h ∩ Iso).card) := by
      rw [hA3def, hRdef, Finset.filter_filter]
      apply Finset.filter_congr
      intro a ha; constructor
      · rintro ⟨_, h3⟩; exact ⟨hdeg4 a ha, h3⟩
      · rintro ⟨_, h3⟩; exact ⟨by omega, h3⟩
    rw [heq]; exact rich_a3_count_le_two_nineteen G Hub Iso hdisj hshare hno2hub
  -- The poor-of-`R` hubs carry iso-degree exactly `2`.
  have hAsplit : ∑ r ∈ A3, (G.neighborFinset r ∩ Iso).card
      + ∑ r ∈ R.filter (fun h => ¬ 3 ≤ (G.neighborFinset h ∩ Iso).card),
          (G.neighborFinset r ∩ Iso).card = S := by
    rw [hSdef, hA3def]
    exact Finset.sum_filter_add_sum_filter_not R _ _
  have hPc2 : ∑ r ∈ R.filter (fun h => ¬ 3 ≤ (G.neighborFinset h ∩ Iso).card),
      (G.neighborFinset r ∩ Iso).card = 2 * (R.filter
        (fun h => ¬ 3 ≤ (G.neighborFinset h ∩ Iso).card)).card := by
    rw [Finset.sum_congr rfl (fun r hr => ?_), Finset.sum_const, smul_eq_mul, mul_comm]
    rw [Finset.mem_filter] at hr
    have h2 := ((hRmem r).mp hr.1).2
    omega
  have hPccard : A3.card + (R.filter (fun h => ¬ 3 ≤ (G.neighborFinset h ∩ Iso).card)).card = 7 := by
    have := Finset.card_filter_add_card_filter_not (s := R)
      (fun h => 3 ≤ (G.neighborFinset h ∩ Iso).card)
    rw [← hA3def, hr7] at this; exact this
  have hAle : ∑ r ∈ A3, (G.neighborFinset r ∩ Iso).card ≤ 4 * A3.card := by
    calc ∑ r ∈ A3, (G.neighborFinset r ∩ Iso).card ≤ ∑ _r ∈ A3, 4 := by
          apply Finset.sum_le_sum
          intro r hr
          rw [hA3def, Finset.mem_filter] at hr
          have hrHub : r ∈ Hub := hRsubHub hr.1
          calc (G.neighborFinset r ∩ Iso).card ≤ (G.neighborFinset r).card :=
                Finset.card_le_card Finset.inter_subset_left
            _ = 4 := by rw [G.card_neighborFinset_eq_degree, hdeg4 r hrHub]
      _ = 4 * A3.card := by rw [Finset.sum_const, smul_eq_mul]; ring
  have hkey : ∑ r ∈ A3, (G.neighborFinset r ∩ Iso).card
      + 2 * (R.filter (fun h => ¬ 3 ≤ (G.neighborFinset h ∩ Iso).card)).card = 18 := by
    have h := hAsplit
    rw [hPc2, hS18] at h
    exact h
  have hA3card : A3.card = 2 := by omega
  have hAsum : ∑ r ∈ A3, (G.neighborFinset r ∩ Iso).card = 8 := by omega
  -- Extract the two iso-degree-`4` rich hubs.
  obtain ⟨w1, w2, hw12, hA3eq⟩ := Finset.card_eq_two.mp hA3card
  have hw1A3 : w1 ∈ A3 := by rw [hA3eq]; exact Finset.mem_insert_self _ _
  have hw2A3 : w2 ∈ A3 := by rw [hA3eq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hw1Hub : w1 ∈ Hub := hRsubHub (Finset.mem_of_mem_filter _ hw1A3)
  have hw2Hub : w2 ∈ Hub := hRsubHub (Finset.mem_of_mem_filter _ hw2A3)
  have hsumpair : (G.neighborFinset w1 ∩ Iso).card + (G.neighborFinset w2 ∩ Iso).card = 8 := by
    have h := hAsum
    rw [hA3eq, Finset.sum_pair hw12] at h
    exact h
  have hw1le : (G.neighborFinset w1 ∩ Iso).card ≤ 4 := by
    calc (G.neighborFinset w1 ∩ Iso).card ≤ (G.neighborFinset w1).card :=
          Finset.card_le_card Finset.inter_subset_left
      _ = 4 := by rw [G.card_neighborFinset_eq_degree, hdeg4 w1 hw1Hub]
  have hw2le : (G.neighborFinset w2 ∩ Iso).card ≤ 4 := by
    calc (G.neighborFinset w2 ∩ Iso).card ≤ (G.neighborFinset w2).card :=
          Finset.card_le_card Finset.inter_subset_left
      _ = 4 := by rw [G.card_neighborFinset_eq_degree, hdeg4 w2 hw2Hub]
  have hw14 : (G.neighborFinset w1 ∩ Iso).card = 4 := by omega
  have hw24 : (G.neighborFinset w2 ∩ Iso).card = 4 := by omega
  -- `w1` has all neighbours in `Iso`, hence is non-adjacent to `w2`.
  have hNw1Iso : G.neighborFinset w1 ⊆ Iso := by
    have hd4 : (G.neighborFinset w1).card = 4 := by
      rw [G.card_neighborFinset_eq_degree, hdeg4 w1 hw1Hub]
    have heq : G.neighborFinset w1 ∩ Iso = G.neighborFinset w1 :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by rw [hd4, hw14])
    rw [← heq]; exact Finset.inter_subset_right
  have hnadj : ¬G.Adj w1 w2 := by
    intro hadj
    have hw2N : w2 ∈ G.neighborFinset w1 := (G.mem_neighborFinset w1 w2).mpr hadj
    exact Finset.disjoint_left.mp hdisj hw2Hub (hNw1Iso hw2N)
  have hsh : (G.neighborFinset w1 ∩ G.neighborFinset w2 ∩ Iso).card ≤ 1 :=
    hshare w1 hw1Hub (hdeg4 w1 hw1Hub) w2 hw2Hub (hdeg4 w2 hw2Hub) hw12 hnadj
  exact two_iso_four_hubs_impossible_nineteen G Iso hIso w1 w2 hw14 hw24 hsh

/-- **The `hnozero ∧ |R| = 6` structural bundle (`n = 19`, `|Hub| = 11`, `(11, 6, 44)`).**  In the
clean no-two-hub octahedron with `¬ ZPoorCutConfig G`: every hub has iso-degree `≥ 1`, and the rich
count is exactly `6`.

* `|R| = 6`: `|R| ∈ {6, 7}` (`rich_count_ge_six_nineteen` via the `r = 5` residual
  `r5_resid_nineteen`, `rich_count_le_seven_nineteen`); `rich_count_ne_seven_nineteen` kills `7`.
* `hnozero`: a hub `h₀` of iso-degree `0` has `|N(h₀) ∩ Hub| + |N(h₀) ∩ Z| = 4`.  If it meets both
  `M`-edge endpoints `z₁, z₂` (`|N(h₀) ∩ Z| = 2`), the triangle `{h₀, z₁, z₂}` (the `M`-edge `z₁∼z₂`)
  has degree sum `4 + 3 + 3 = 10 ≤ 11`, a good triangle excluded by `hT`.  The complementary case
  `|N(h₀) ∩ Z| ≤ 1` (so `|N(h₀) ∩ Hub| ≥ 3`, a near-internal poor hub) is the genuinely-new
  `|Hub| = 11` fifth-poor-hub residual. -/
theorem rich_six_no_iso_zero_nineteen (G : SimpleGraph (Fin 19)) (Hub Iso : Finset (Fin 19))
    (hdeg4 : ∀ h ∈ Hub, G.degree h = 4)
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdisj : Disjoint Hub Iso) (hHub : Hub.card = 11) (hIso : Iso.card = 6)
    (hisodeg3 : ∀ t ∈ Iso, G.degree t = 3)
    (hdeg3 : ∀ v : Fin 19, 3 ≤ G.degree v)
    (hdsum : ∑ w ∈ Hub, G.degree w = 44)
    (hleak : ∑ h ∈ Hub, (G.neighborFinset h ∩ (Finset.univ \ (Hub ∪ Iso))).card ≤ 4)
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hno2hub : ¬∃ h₁ h₂ : Fin 19, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card)
    (hC4 : ¬∃ a b c d : Fin 19, ({a, b, c, d} : Finset (Fin 19)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (hK23 : ¬∃ a b c d e : Fin 19, ({a, b, c, d, e} : Finset (Fin 19)).card = 5 ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
      G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 19)
    (hT : ¬∃ x y z : Fin 19, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧
      G.degree x + G.degree y + G.degree z ≤ 11)
    (hcut : ¬ ZPoorCutConfig G) :
    (∀ h ∈ Hub, 1 ≤ (G.neighborFinset h ∩ Iso).card) ∧
    (Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)).card = 6 := by
  classical
  set Z : Finset (Fin 19) := Finset.univ \ (Hub ∪ Iso) with hZdef
  set R : Finset (Fin 19) := Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card) with hRdef
  -- **`|R| = 6`.**
  have hle7 : R.card ≤ 7 :=
    rich_count_le_seven_nineteen G Hub Iso hdeg4 hiso3 hdisj hHub hIso hshare hno2hub
  have hoct5 := r5_resid_nineteen G Hub Iso hdeg4 hiso3 hdisj hHub hIso hdeg3 hisodeg3 hdsum hleak
    hshare hno2hub hC4 hK23 hT
  have hge6 : 6 ≤ R.card := (rich_count_ge_six_nineteen G Hub Iso hdeg4 hiso3 hdisj hHub hIso
    hshare hno2hub hoct5).resolve_right hcut
  have hne7 : R.card ≠ 7 := rich_count_ne_seven_nineteen G Hub Iso hdeg4 hiso3 hdisj hHub hIso
    hisodeg3 hdeg3 hdsum hleak hshare hno2hub hC4 hK23 hT hcut
  have hRcard : R.card = 6 := by omega
  refine ⟨?_, hRcard⟩
  -- **`hnozero`.**
  intro h₀ hh₀Hub
  by_contra hlt
  have hiso0 : (G.neighborFinset h₀ ∩ Iso).card = 0 := by omega
  -- Degree split of `h₀`: `|N ∩ Hub| + |N ∩ Z| = 4`.
  have hsplit := nbr_split_three_nineteen G Hub Iso hdisj h₀
  rw [hiso0, hdeg4 h₀ hh₀Hub, ← hZdef] at hsplit
  -- The two `M`-edge endpoints, each of degree `3`, meeting two hubs, mutually adjacent.
  have hZcard : Z.card = 2 := z_card_two_nineteen Hub Iso hdisj hHub hIso
  have hzfacts := z_two_hub_nbrs_nineteen G Hub Iso hiso3 hdisj hHub hIso hdsum hdeg3 hisodeg3 hleak
  by_cases hz2 : 2 ≤ (G.neighborFinset h₀ ∩ Z).card
  · -- `h₀` meets both endpoints: good triangle `{h₀, z₁, z₂}`, degree sum `10 ≤ 11`.
    have hNZeq : G.neighborFinset h₀ ∩ Z = Z :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by rw [hZcard]; exact hz2)
    obtain ⟨z1, z2, hz12, hZeq2⟩ := Finset.card_eq_two.mp hZcard
    have hz1Z : z1 ∈ Z := by rw [hZeq2]; exact Finset.mem_insert_self _ _
    have hz2Z : z2 ∈ Z := by rw [hZeq2]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    have hz1mem : z1 ∈ G.neighborFinset h₀ ∩ Z := by rw [hNZeq]; exact hz1Z
    have hz2mem : z2 ∈ G.neighborFinset h₀ ∩ Z := by rw [hNZeq]; exact hz2Z
    have hadj1 : G.Adj h₀ z1 := (G.mem_neighborFinset _ _).mp (Finset.mem_inter.mp hz1mem).1
    have hadj2 : G.Adj h₀ z2 := (G.mem_neighborFinset _ _).mp (Finset.mem_inter.mp hz2mem).1
    -- `z1 ∼ z2` (the `M`-edge): `z1` has exactly one `Z`-neighbour, which must be `z2`.
    obtain ⟨_, hz1hub2, hz1deg3⟩ := hzfacts z1 hz1Z
    obtain ⟨hz2iso0, _, hz2deg3⟩ := hzfacts z2 hz2Z
    have hz1iso0 : (G.neighborFinset z1 ∩ Iso).card = 0 := (hzfacts z1 hz1Z).1
    have hz1split := nbr_split_three_nineteen G Hub Iso hdisj z1
    rw [hz1iso0, hz1deg3, hz1hub2, ← hZdef] at hz1split
    have hz1Z1 : (G.neighborFinset z1 ∩ Z).card = 1 := by omega
    obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hz1Z1
    have hwZ : w ∈ Z := by
      have : w ∈ G.neighborFinset z1 ∩ Z := by rw [hw]; exact Finset.mem_singleton_self _
      exact (Finset.mem_inter.mp this).2
    have hz1w : G.Adj z1 w := by
      have : w ∈ G.neighborFinset z1 ∩ Z := by rw [hw]; exact Finset.mem_singleton_self _
      exact (G.mem_neighborFinset _ _).mp (Finset.mem_inter.mp this).1
    -- `w ∈ Z = {z1, z2}` and `w ≠ z1`, so `w = z2`.
    have hwz2 : w = z2 := by
      rw [hZeq2, Finset.mem_insert, Finset.mem_singleton] at hwZ
      rcases hwZ with h | h
      · exact absurd (h ▸ hz1w) (G.irrefl)
      · exact h
    have hz1z2 : G.Adj z1 z2 := hwz2 ▸ hz1w
    -- Distinctness: `h₀ ∈ Hub`, `z1, z2 ∈ Z` disjoint from `Hub`.
    have hh₀notZ : h₀ ∉ Z := by
      rw [hZdef, Finset.mem_sdiff]
      rintro ⟨_, hcon⟩
      exact hcon (Finset.mem_union_left _ hh₀Hub)
    have hh₀z1 : h₀ ≠ z1 := fun e => hh₀notZ (e ▸ hz1Z)
    have hh₀z2 : h₀ ≠ z2 := fun e => hh₀notZ (e ▸ hz2Z)
    exact hT ⟨h₀, z1, z2, hh₀z1, hz12, hh₀z2, hadj1, hz1z2, hadj2, by
      rw [hdeg4 h₀ hh₀Hub, hz1deg3, hz2deg3]; norm_num⟩
  · -- `|N(h₀) ∩ Z| ≤ 1`, so `|N(h₀) ∩ Hub| ≥ 3`: the near-internal fifth-poor-hub residual.
    -- **Strategy.**  An iso-degree-`0` poor hub forces `S = ∑_R isoDeg ≥ 14` (the five poor hubs
    -- absorb `≤ 4` of the `18` incidences), so some rich hub `h₁` has iso-degree `≥ 3` — whence its
    -- whole neighbourhood is `≥ 3` twins plus `≤ 1` other vertex.  Each `M`-edge endpoint meets a
    -- rich hub (`each_z_meets_rich_nineteen`, discharged by `hcut`); a degree count shows `h₁` cannot
    -- block both `Z`-endpoints' rich partners, so `h₁` is non-adjacent to some rich hub `h₂` meeting
    -- an `M`-end `z` with `h₁ ≁ z`.  The pair `(h₁, h₂)` with `h₁`'s two private twins, `h₂`'s one
    -- private twin and the `Z`-leaf `z` assembles a `TwoHubConfig` (`two_hub_zleaf_nineteen`),
    -- contradicting `hcut`.
    have hHubge3 : 3 ≤ (G.neighborFinset h₀ ∩ Hub).card := by omega
    set P : Finset (Fin 19) := Hub.filter (fun h => ¬ 2 ≤ (G.neighborFinset h ∩ Iso).card)
      with hPdef
    -- Total iso-incidence is `18`.
    have hsum18 : ∑ a ∈ Hub, (G.neighborFinset a ∩ Iso).card = 18 := by
      have h := hub_iso_sum_nineteen G Hub Iso hiso3; rw [hIso] at h; omega
    have hsplitRP : (∑ r ∈ R, (G.neighborFinset r ∩ Iso).card)
        + ∑ g ∈ P, (G.neighborFinset g ∩ Iso).card = 18 := by
      rw [hRdef, hPdef,
        Finset.sum_filter_add_sum_filter_not Hub (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)]
      exact hsum18
    have hPcard : P.card = 5 := by
      have hc := Finset.card_filter_add_card_filter_not (s := Hub)
        (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)
      rw [← hRdef, ← hPdef, hHub, hRcard] at hc; omega
    have hh₀P : h₀ ∈ P := by
      rw [hPdef, Finset.mem_filter]; exact ⟨hh₀Hub, by rw [hiso0]; omega⟩
    -- The five poor hubs carry `≤ 4` incidences (`h₀` carries `0`, the others `≤ 1`).
    have hPsum_le : ∑ g ∈ P, (G.neighborFinset g ∩ Iso).card ≤ 4 := by
      have hpe : ∑ g ∈ P, (G.neighborFinset g ∩ Iso).card
          = (G.neighborFinset h₀ ∩ Iso).card
            + ∑ g ∈ P.erase h₀, (G.neighborFinset g ∩ Iso).card :=
        (Finset.add_sum_erase P _ hh₀P).symm
      have herase : ∑ g ∈ P.erase h₀, (G.neighborFinset g ∩ Iso).card ≤ 4 := by
        calc ∑ g ∈ P.erase h₀, (G.neighborFinset g ∩ Iso).card
            ≤ ∑ _g ∈ P.erase h₀, 1 := by
              apply Finset.sum_le_sum; intro g hg
              have hgP : g ∈ P := Finset.mem_of_mem_erase hg
              rw [hPdef, Finset.mem_filter] at hgP; omega
          _ = (P.erase h₀).card := by rw [Finset.sum_const, smul_eq_mul, mul_one]
          _ = 4 := by rw [Finset.card_erase_of_mem hh₀P, hPcard]
      rw [hpe, hiso0]; omega
    -- Hence `S ≥ 14`, so some rich hub has iso-degree `≥ 3`.
    have hex3 : ∃ w ∈ R, 3 ≤ (G.neighborFinset w ∩ Iso).card := by
      by_contra hcon
      push Not at hcon
      have hle12 : ∑ r ∈ R, (G.neighborFinset r ∩ Iso).card ≤ 12 := by
        calc ∑ r ∈ R, (G.neighborFinset r ∩ Iso).card ≤ ∑ _r ∈ R, 2 := by
              apply Finset.sum_le_sum; intro r hr; have := hcon r hr; omega
          _ = 12 := by rw [Finset.sum_const, hRcard, smul_eq_mul]
      omega
    obtain ⟨h₁, h₁R, h₁iso3⟩ := hex3
    have h₁Hub : h₁ ∈ Hub := by
      have := h₁R; rw [hRdef, Finset.mem_filter] at this; exact this.1
    -- `h₁` has at most one neighbour outside `Iso` (iso-degree `≥ 3`, degree `4`).
    have h₁split := nbr_split_three_nineteen G Hub Iso hdisj h₁
    rw [hdeg4 h₁ h₁Hub, ← hZdef] at h₁split
    have h₁out : (G.neighborFinset h₁ ∩ Hub).card + (G.neighborFinset h₁ ∩ Z).card ≤ 1 := by omega
    -- The two `M`-edge endpoints `z1, z2`, each meeting a rich hub `p1, p2`.
    obtain ⟨z1, z2, hz12, hZeq2⟩ := Finset.card_eq_two.mp hZcard
    have hz1Z : z1 ∈ Z := by rw [hZeq2]; exact Finset.mem_insert_self _ _
    have hz2Z : z2 ∈ Z := by rw [hZeq2]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    have hmeetsrich := each_z_meets_rich_nineteen G Hub Iso hdeg4 hiso3 hdisj hHub hIso hdeg3
      hisodeg3 hdsum hleak hshare hno2hub hC4 hK23 hT
    have hz1rich : 1 ≤ (G.neighborFinset z1 ∩ R).card := by
      have h := (hmeetsrich z1 hz1Z).resolve_right hcut; rwa [← hRdef] at h
    have hz2rich : 1 ≤ (G.neighborFinset z2 ∩ R).card := by
      have h := (hmeetsrich z2 hz2Z).resolve_right hcut; rwa [← hRdef] at h
    obtain ⟨p1, hp1⟩ := Finset.card_pos.mp hz1rich
    obtain ⟨p2, hp2⟩ := Finset.card_pos.mp hz2rich
    rw [Finset.mem_inter, G.mem_neighborFinset] at hp1 hp2
    obtain ⟨hz1p1, hp1R⟩ := hp1
    obtain ⟨hz2p2, hp2R⟩ := hp2
    have hp1Hub : p1 ∈ Hub := by
      have := hp1R; rw [hRdef, Finset.mem_filter] at this; exact this.1
    have hp2Hub : p2 ∈ Hub := by
      have := hp2R; rw [hRdef, Finset.mem_filter] at this; exact this.1
    have hp1iso2 : 2 ≤ (G.neighborFinset p1 ∩ Iso).card := by
      have := hp1R; rw [hRdef, Finset.mem_filter] at this; exact this.2
    -- **The cut assembler.**  Any rich `h₂` met by an `M`-end `z`, non-adjacent to `h₁` (with
    -- `h₁ ≁ z`), assembles a `Z`-leaf `TwoHubConfig`, contradicting `hcut`.
    have mkcut : ∀ z h₂ : Fin 19, z ∈ Z → h₂ ∈ R → G.Adj z h₂ →
        ¬G.Adj h₁ z → ¬G.Adj h₁ h₂ → False := by
      intro z h₂ hzZ h₂R hzadj hn1z hn12
      have h₂Hub : h₂ ∈ Hub := by
        have := h₂R; rw [hRdef, Finset.mem_filter] at this; exact this.1
      have h₂iso2 : 2 ≤ (G.neighborFinset h₂ ∩ Iso).card := by
        have := h₂R; rw [hRdef, Finset.mem_filter] at this; exact this.2
      have hne12 : h₁ ≠ h₂ := fun he => hn1z (he ▸ hzadj.symm)
      obtain ⟨a, b, haIso, hbIso, hab, ha1, hb1, hna2, hnb2⟩ :=
        exists_two_private_twins_nineteen G Hub Iso hshare h₁ h₂ h₁Hub h₂Hub
          (hdeg4 h₁ h₁Hub) (hdeg4 h₂ h₂Hub) hne12 hn12 h₁iso3
      obtain ⟨c, hcIso, hc2, hn1c⟩ :=
        exists_one_private_twin_nineteen G Hub Iso hshare h₂ h₁ h₂Hub h₁Hub
          (hdeg4 h₂ h₂Hub) (hdeg4 h₁ h₁Hub) hne12 hn12 h₂iso2
      have htwo := two_hub_zleaf_nineteen G Hub Iso hiso3 hdisj hHub hIso hdsum hdeg3 hisodeg3
        hleak h₁ h₂ a b c z h₁Hub h₂Hub (hdeg4 h₁ h₁Hub) (hdeg4 h₂ h₂Hub) haIso hbIso hcIso hzZ
        ha1 hb1 hc2 hzadj hn12 hn1c hn1z hna2 hnb2 hab
      exact hcut (Or.inl htwo)
    -- Find a good `(z, h₂)`: try `(z1, p1)`, then `(z2, p2)`; else both are blocked.
    by_cases hP1 : ¬G.Adj h₁ z1 ∧ ¬G.Adj h₁ p1
    · exact mkcut z1 p1 hz1Z hp1R hz1p1 hP1.1 hP1.2
    by_cases hP2 : ¬G.Adj h₁ z2 ∧ ¬G.Adj h₁ p2
    · exact mkcut z2 p2 hz2Z hp2R hz2p2 hP2.1 hP2.2
    -- Both blocked: a degree count rules this out.
    rw [not_and_or, not_not, not_not] at hP1 hP2
    rcases hP1 with hb1 | hb1 <;> rcases hP2 with hb2 | hb2
    · -- `h₁ ~ z1` and `h₁ ~ z2`: two distinct `Z`-neighbours.
      have h2z : 2 ≤ (G.neighborFinset h₁ ∩ Z).card := by
        have hsub : ({z1, z2} : Finset (Fin 19)) ⊆ G.neighborFinset h₁ ∩ Z := by
          intro x hx; rw [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hb1, hz1Z⟩
          · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hb2, hz2Z⟩
        have := Finset.card_le_card hsub; rwa [Finset.card_pair hz12] at this
      omega
    · -- `h₁ ~ z1` (a `Z`-vertex) and `h₁ ~ p2` (a hub).
      have h1z : 1 ≤ (G.neighborFinset h₁ ∩ Z).card :=
        Finset.card_pos.mpr ⟨z1, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hb1, hz1Z⟩⟩
      have h1h : 1 ≤ (G.neighborFinset h₁ ∩ Hub).card :=
        Finset.card_pos.mpr ⟨p2, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hb2, hp2Hub⟩⟩
      omega
    · -- `h₁ ~ p1` (a hub) and `h₁ ~ z2` (a `Z`-vertex).
      have h1z : 1 ≤ (G.neighborFinset h₁ ∩ Z).card :=
        Finset.card_pos.mpr ⟨z2, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hb2, hz2Z⟩⟩
      have h1h : 1 ≤ (G.neighborFinset h₁ ∩ Hub).card :=
        Finset.card_pos.mpr ⟨p1, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hb1, hp1Hub⟩⟩
      omega
    · -- `h₁ ~ p1` and `h₁ ~ p2`: two hub-neighbours.
      by_cases hpp : p1 = p2
      · -- `p1 = p2 = ν`: a rich hub adjacent to `h₁` and meeting both `z1, z2` — degree `≥ 5`.
        subst hpp
        have hνsplit := nbr_split_three_nineteen G Hub Iso hdisj p1
        rw [hdeg4 p1 hp1Hub, ← hZdef] at hνsplit
        have hνhub : 1 ≤ (G.neighborFinset p1 ∩ Hub).card :=
          Finset.card_pos.mpr ⟨h₁, Finset.mem_inter.mpr
            ⟨(G.mem_neighborFinset _ _).mpr hb1.symm, h₁Hub⟩⟩
        have hνz : 2 ≤ (G.neighborFinset p1 ∩ Z).card := by
          have hsub : ({z1, z2} : Finset (Fin 19)) ⊆ G.neighborFinset p1 ∩ Z := by
            intro x hx; rw [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl
            · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hz1p1.symm, hz1Z⟩
            · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hz2p2.symm, hz2Z⟩
          have := Finset.card_le_card hsub; rwa [Finset.card_pair hz12] at this
        omega
      · -- `p1 ≠ p2`: two distinct hub-neighbours.
        have h2h : 2 ≤ (G.neighborFinset h₁ ∩ Hub).card := by
          have hsub : ({p1, p2} : Finset (Fin 19)) ⊆ G.neighborFinset h₁ ∩ Hub := by
            intro x hx; rw [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl
            · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hb1, hp1Hub⟩
            · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hb2, hp2Hub⟩
          have := Finset.card_le_card hsub; rwa [Finset.card_pair hpp] at this
        omega

end N19

end ACMax
