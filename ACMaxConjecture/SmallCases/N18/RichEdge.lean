import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N18.Core
import ACMaxConjecture.SmallCases.N18.TwoHubSelect
import ACMaxConjecture.SmallCases.N18.StarTriangleStruct
import ACMaxConjecture.SmallCases.N18.RichCount
import ACMaxConjecture.SmallCases.N18.RichTrace
import ACMaxConjecture.SmallCases.N18.RichZdeg
import ACMaxConjecture.SmallCases.N18.RichEdgeExtract

/-!
# Rich internal-edge lower bound and the `r ≠ 7` rich-count crux (`n = 18`)

For the tight `e(M) = 1`, all-degree-`4`, `(|Hub|, |Iso|) = (10, 6)` profile, the *rich* hubs are
`R = {h : 2 ≤ |N(h) ∩ Iso|}`.  This file contains two global structural cores.

* `rich_count_ne_seven_eighteen` (`r ≠ 7`).  Combining the off-diagonal trace count
  (`N1`: each non-adjacent rich pair shares a *unique* `M`-isolated twin) with the rich-degree
  handshake (`∑_R|N ∩ Hub| = 28 − ∑_R a − z_R`, `z_R ≥ 2` from `zdeg_split`) pins the rich-internal
  edge mass both above and below.  Writing `c_t := |N(t) ∩ R|` and `S := ∑_R a`, the non-adjacent
  ordered rich pairs `42 − ∑_R|N ∩ R|` embed into the twins' rich-trace off-diagonals
  `∑_t (c_t² − c_t)`, forcing `∑_t (c_t² − c_t) ≥ 16 + S`.  Since `c_t² − c_t ≤ c_t + 3·[c_t = 3]`,
  this drives every twin to meet *three* rich hubs, hence `S = 18`; then `N2` forces two iso-degree-`4`
  rich hubs, excluded by `two_iso_four_hubs_impossible`.

* `rich_edge_ge_four_eighteen` (`r = 6 ⟹ ∑_R|N ∩ R| ≥ 8`, the LINCHPIN).  This is the matching
  lower bound to `rich_edge_le_four`; together they pin `E(R, R) = 4` and (via the handshake and
  `z_R ≥ 2`) give `E(R, P) = 0`.  The remaining bad rich–poor edge (whose poor twin misses the rich
  hub) is discharged by `two_hub_or_cert_from_rp_edge_eighteen` (see `TwinCert18RichEdgeExtract`),
  which forces the rigid octahedron and extracts a good triangle / `K₂,₃` / `C₄`; that octahedron
  development carries the two remaining documented `sorry`s of the covering-design frontier.
-/

namespace ACMax

open scoped Classical

namespace N18

/-- **`r ≠ 7` — the rich count is not seven (CRUX, now proved).**  With all hubs degree `4`, each
`M`-isolated twin meeting exactly three hubs, the `Z`-distribution (`z_R ≥ 2` via `zdeg_split`), the
degree-`4` share bound, no good two-hub pair, and the good-`C₄`/`K₂₃` exclusions, the rich hubs
`R = {h : 2 ≤ |N(h) ∩ Iso|}` cannot number exactly seven. -/
theorem rich_count_ne_seven_eighteen (G : SimpleGraph (Fin 18)) (Hub Iso : Finset (Fin 18))
    (hdeg4 : ∀ h ∈ Hub, G.degree h = 4)
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdisj : Disjoint Hub Iso) (hHub : Hub.card = 10) (hIso : Iso.card = 6)
    (hisodeg3 : ∀ t ∈ Iso, G.degree t = 3)
    (hdeg3 : ∀ v : Fin 18, 3 ≤ G.degree v)
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
    (hK23 : ¬∃ a b c d e : Fin 18, ({a, b, c, d, e} : Finset (Fin 18)).card = 5 ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
      G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 19)
    (hT : ¬∃ x y z : Fin 18, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧
      G.degree x + G.degree y + G.degree z ≤ 11) :
    (Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)).card ≠ 7 := by
  classical
  intro hr7
  set Z : Finset (Fin 18) := Finset.univ \ (Hub ∪ Iso) with hZdef
  set R : Finset (Fin 18) := Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card) with hRdef
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
  obtain ⟨hzRge, _⟩ := zdeg_split_eighteen G Hub Iso hdeg4 hiso3 hdisj hHub hIso hdeg3 hisodeg3
    hdsum hleak hshare hno2hub hC4 hK23 hT
  rw [← hRdef, ← hZdef] at hzRge
  -- `S := ∑_R a`, cross-counted as `∑_t c_t`.
  set S : ℕ := ∑ r ∈ R, (G.neighborFinset r ∩ Iso).card with hSdef
  have hcross : ∑ t ∈ Iso, (G.neighborFinset t ∩ R).card = S := by
    rw [hSdef]; exact cross_count G Iso R
  have hS15 : 15 ≤ S := by
    have h := rich_iso_sum_ge_fifteen_eighteen G Hub Iso hiso3 hHub hIso hr7
    rw [← hRdef] at h; rw [hSdef]; exact h
  -- Rich-degree handshake: `∑_R|N∩Hub| + S + z_R = 28`.
  have hdeg28 : ∑ r ∈ R, G.degree r = 28 := by
    rw [Finset.sum_congr rfl (fun r hr => hdeg4 r (hRsubHub hr)), Finset.sum_const, hr7,
      smul_eq_mul]
  have hsplit3 : ∑ r ∈ R, (G.neighborFinset r ∩ Hub).card + S
      + ∑ r ∈ R, (G.neighborFinset r ∩ Z).card = 28 := by
    have hcong : ∑ r ∈ R, ((G.neighborFinset r ∩ Hub).card + (G.neighborFinset r ∩ Iso).card
        + (G.neighborFinset r ∩ Z).card) = ∑ r ∈ R, G.degree r :=
      Finset.sum_congr rfl (fun r _ => nbr_split_three_eighteen G Hub Iso hdisj r)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hcong
    rw [hdeg28] at hcong; rw [hSdef]; omega
  -- Off-diagonal of `R`.
  set Off : Finset (Fin 18 × Fin 18) := R.offDiag with hOffdef
  have hOffcard : Off.card = 42 := by rw [hOffdef, Finset.offDiag_card, hr7]
  set Dadj : Finset (Fin 18 × Fin 18) := Off.filter (fun p => G.Adj p.1 p.2) with hDadjdef
  set D : Finset (Fin 18 × Fin 18) := Off.filter (fun p => ¬G.Adj p.1 p.2) with hDdef
  have hDsplit : D.card + Dadj.card = Off.card := by
    rw [hDdef, hDadjdef, add_comm]
    exact Finset.card_filter_add_card_filter_not _
  -- `Dadj ≤ ∑_R|N∩R| ≤ ∑_R|N∩Hub|`.
  have hDadjle : Dadj.card ≤ ∑ a ∈ R, (G.neighborFinset a ∩ R).card := by
    have hmaps : (Dadj : Set (Fin 18 × Fin 18)).MapsTo Prod.fst R := by
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
  set A3 : Finset (Fin 18) := R.filter (fun h => 3 ≤ (G.neighborFinset h ∩ Iso).card) with hA3def
  have hN2 : A3.card ≤ 2 := by
    have heq : A3 = Hub.filter (fun h => G.degree h = 4 ∧ 3 ≤ (G.neighborFinset h ∩ Iso).card) := by
      rw [hA3def, hRdef, Finset.filter_filter]
      apply Finset.filter_congr
      intro a ha; constructor
      · rintro ⟨_, h3⟩; exact ⟨hdeg4 a ha, h3⟩
      · rintro ⟨_, h3⟩; exact ⟨by omega, h3⟩
    rw [heq]; exact rich_a3_count_le_two_eighteen G Hub Iso hdisj hshare hno2hub
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
  exact two_iso_four_hubs_impossible_eighteen G Iso hIso w1 w2 hw14 hw24 hsh

/-- **Rich internal edge lower bound (`r = 6`, the LINCHPIN).**  Matching `rich_edge_le_four`, the
six rich hubs span *at least* four internal edges, i.e. `∑_{r∈R}|N(r) ∩ R| ≥ 8`.  Together with
`rich_edge_le_four` this pins `E(R, R) = 4`, and with the handshake and `z_R ≥ 2` forces
`E(R, P) = 0` (`rich_poor_no_edge`).  The bad rich–poor edge (poor twin missing the rich hub) is
discharged via `two_hub_or_cert_from_rp_edge_eighteen` over the rigid octahedron. -/
theorem rich_edge_ge_four_eighteen (G : SimpleGraph (Fin 18)) (Hub Iso : Finset (Fin 18))
    (hdeg4 : ∀ h ∈ Hub, G.degree h = 4)
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdisj : Disjoint Hub Iso) (hHub : Hub.card = 10) (hIso : Iso.card = 6)
    (hisodeg3 : ∀ t ∈ Iso, G.degree t = 3) (hdeg3 : ∀ v : Fin 18, 3 ≤ G.degree v)
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
    (hK23 : ¬∃ a b c d e : Fin 18, ({a, b, c, d, e} : Finset (Fin 18)).card = 5 ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
      G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 19)
    (hT : ¬∃ x y z : Fin 18, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧
      G.degree x + G.degree y + G.degree z ≤ 11)
    (hr6 : (Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)).card = 6)
    (hnozero : ∀ h ∈ Hub, 1 ≤ (G.neighborFinset h ∩ Iso).card) :
    8 ≤ ∑ r ∈ Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card),
      (G.neighborFinset r ∩ Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)).card := by
  classical
  set Z : Finset (Fin 18) := Finset.univ \ (Hub ∪ Iso) with hZdef
  set R : Finset (Fin 18) := Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card) with hRdef
  set P : Finset (Fin 18) := Hub.filter (fun h => ¬ 2 ≤ (G.neighborFinset h ∩ Iso).card) with hPdef
  have hRsubHub : R ⊆ Hub := Finset.filter_subset _ _
  have hPsubHub : P ⊆ Hub := Finset.filter_subset _ _
  have hunion : R ∪ P = Hub := Finset.filter_union_filter_not_eq _ Hub
  have hdisjRP : Disjoint R P := Finset.disjoint_filter_filter_not Hub Hub _
  have hPcard : P.card = 4 := by
    have hs := Finset.card_filter_add_card_filter_not
      (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card) (s := Hub)
    rw [← hRdef, ← hPdef, hHub, hr6] at hs; omega
  -- Poor hubs have iso-degree exactly `1`.
  have hPpoor : ∀ g ∈ P, (G.neighborFinset g ∩ Iso).card = 1 := by
    intro g hg
    have hgHub : g ∈ Hub := hPsubHub hg
    rw [hPdef, Finset.mem_filter] at hg
    have := hnozero g hgHub; omega
  -- `z_R = 2` (sharp).
  obtain ⟨hzR2, _⟩ := zdeg_split_sharp_eighteen G Hub Iso hdeg4 hiso3 hdisj hHub hIso hdeg3
    hisodeg3 hdsum hleak hshare hno2hub hC4 hK23 hT
  rw [← hRdef, ← hZdef] at hzR2
  -- `∑_R isoDeg = 14`: total `18`, poor side `= |P| = 4`.
  have hiso18 : ∑ h ∈ Hub, (G.neighborFinset h ∩ Iso).card = 18 := by
    have := hub_iso_sum_eighteen G Hub Iso hiso3; rw [hIso] at this; omega
  have hisoP : ∑ g ∈ P, (G.neighborFinset g ∩ Iso).card = 4 := by
    have heq : ∑ g ∈ P, (G.neighborFinset g ∩ Iso).card = ∑ _g ∈ P, 1 :=
      Finset.sum_congr rfl (fun g hg => hPpoor g hg)
    rw [heq, Finset.sum_const, hPcard, smul_eq_mul, mul_one]
  have hisoR : ∑ r ∈ R, (G.neighborFinset r ∩ Iso).card = 14 := by
    have hsp : ∑ r ∈ R, (G.neighborFinset r ∩ Iso).card
        + ∑ g ∈ P, (G.neighborFinset g ∩ Iso).card = 18 := by
      rw [hRdef, hPdef,
        Finset.sum_filter_add_sum_filter_not Hub (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)]
      exact hiso18
    omega
  -- **`E(R, P) = 0`** proved directly via the degree-`11` triangle (`hT ≤ 11`).
  have hERP : ∀ r ∈ R, ∀ g ∈ P, ¬G.Adj r g := by
    intro r hr g hg hadj
    have hrHub : r ∈ Hub := hRsubHub hr
    have hgHub : g ∈ Hub := hPsubHub hg
    -- `g` has a unique `M`-isolated twin `t`, and `g ~ t`.
    have hg1 : (G.neighborFinset g ∩ Iso).card = 1 := hPpoor g hg
    obtain ⟨t, ht⟩ := Finset.card_eq_one.mp hg1
    have htmem : t ∈ G.neighborFinset g ∩ Iso := by rw [ht]; exact Finset.mem_singleton_self _
    rw [Finset.mem_inter, G.mem_neighborFinset] at htmem
    obtain ⟨hgt, htIso⟩ := htmem
    have hrg : r ≠ g := fun he => Finset.disjoint_left.mp hdisjRP hr (he ▸ hg)
    have hrt : r ≠ t := fun he => Finset.disjoint_left.mp hdisj hrHub (he ▸ htIso)
    have hgtne : g ≠ t := fun he => Finset.disjoint_left.mp hdisj hgHub (he ▸ htIso)
    by_cases hrtadj : G.Adj r t
    · -- Subcase A: `r ~ t`.  Triangle `{r, g, t}` has degree sum `4 + 4 + 3 = 11`.
      refine hT ⟨r, g, t, hrg, hgtne, hrt, hadj, hgt, hrtadj, ?_⟩
      rw [hdeg4 r hrHub, hdeg4 g hgHub, hisodeg3 t htIso]
    · -- Subcase B: `r ≁ t`.  The bad rich–poor edge whose poor twin misses the rich hub forces the
      -- rigid octahedron, killed by the poor/`Z` cert (`two_hub_or_cert_from_rp_edge_eighteen`).
      have hgr : ¬ 2 ≤ (G.neighborFinset g ∩ Iso).card := by
        have h := hg; rw [hPdef, Finset.mem_filter] at h; exact h.2
      exact two_hub_or_cert_from_rp_edge_eighteen G Hub Iso R hRdef hdeg4 hiso3 hdisj hHub hIso
        hisodeg3 hdeg3 hdsum hleak hshare hno2hub hC4 hK23 hT (by rw [hRdef]; exact hr6) hnozero
        r g t hr hgHub hg1 hgr hadj htIso hgt hrtadj
  -- `∑_R |N ∩ P| = 0`.
  have hRP0 : ∑ r ∈ R, (G.neighborFinset r ∩ P).card = 0 := by
    apply Finset.sum_eq_zero
    intro r hr
    rw [Finset.card_eq_zero]
    ext x
    simp only [Finset.mem_inter, Finset.notMem_empty, iff_false, not_and]
    intro hxN hxP
    exact hERP r hr x hxP ((G.mem_neighborFinset r x).mp hxN)
  -- Rich-degree handshake `∑_R|N∩R| + ∑_R|N∩P| + 14 + z_R = 24`.
  have hdeg24 : ∑ r ∈ R, G.degree r = 24 := by
    rw [Finset.sum_congr rfl (fun r hr => hdeg4 r (hRsubHub hr)), Finset.sum_const, hr6,
      smul_eq_mul]
  have hsplit3 : ∑ r ∈ R, (G.neighborFinset r ∩ Hub).card
      + ∑ r ∈ R, (G.neighborFinset r ∩ Iso).card + ∑ r ∈ R, (G.neighborFinset r ∩ Z).card = 24 := by
    have hcong : ∑ r ∈ R, ((G.neighborFinset r ∩ Hub).card + (G.neighborFinset r ∩ Iso).card
        + (G.neighborFinset r ∩ Z).card) = ∑ r ∈ R, G.degree r :=
      Finset.sum_congr rfl (fun r _ => nbr_split_three_eighteen G Hub Iso hdisj r)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hdeg24] at hcong; exact hcong
  have hHubsplit : ∑ r ∈ R, (G.neighborFinset r ∩ Hub).card
      = ∑ r ∈ R, (G.neighborFinset r ∩ R).card + ∑ r ∈ R, (G.neighborFinset r ∩ P).card := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro r _
    rw [← hunion, Finset.inter_union_distrib_left, Finset.card_union_of_disjoint]
    exact Finset.disjoint_left.mpr (fun x hx1 hx2 =>
      Finset.disjoint_left.mp hdisjRP (Finset.mem_inter.mp hx1).2 (Finset.mem_inter.mp hx2).2)
  rw [hHubsplit, hisoR] at hsplit3
  omega

end N18

end ACMax
