import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N20.Core
import ACMaxConjecture.SmallCases.N20.Core
import ACMaxConjecture.SmallCases.StarCertificates
import ACMaxConjecture.SmallCases.N20.TwoHubSelect
import ACMaxConjecture.SmallCases.N20.FatCentre

/-!
# Degree-`7`-aware two-hub corner selection for `n = 20` (`|Hub| = 9`, `∑deg = 39` regime)

This file supplies `two_hub_deg7_select_hub9_twenty`, the hub-pair *selection* lemma for the
`|Hub| = 9`, `∑_{Hub} deg = 39` two-hub `s ≤ 2` corner that carries a degree-`≥ 6` hub (so the
degree-`5`-restricted selector does not apply).  The two surviving profiles are
`(|Hub|, |Iso|, ∑deg) ∈ {(9, 11, 39), (9, 9, 39)}` (the `e(M) = 0` and `e(M) = 1` cuts).

As in `two_hub_deg7_select_twenty` the selection is routed through the **degree-`4`-restricted**
share (`hshare`), feeding the shared `strong_deg4_count_le_two_deg5_twenty` / `deg4_sum_le_twenty`
engine, and the residual hubs `R = {h ∈ Hub : deg ≠ 4}` are bounded directly by their degree
(`∑_R isoDeg ≤ ∑_R deg`).  With `∑_R deg = 39 − 4·|T| = 3 + 4·|R|` and the degree-`≥ 6` witness
(`∑_R deg ≥ 5·|R| + 1`), the residual count `|R| ≤ 2` is forced.

* **`(9, 11, 39)`:** `3·|Iso| = 33 ≤ (2·|T| + 2) + ∑_R deg = 23 + 2·|R| ≤ 27`, absurd — the
  selection cannot be refuted, so a good non-adjacent degree-`4` pair exists.
* **`(9, 9, 39)`:** counting only *ties* (`27 = 27`), pinning `|T| = 7`, `|R| = 2` (one degree-`6`
  and one degree-`5` hub) and `∑_T isoDeg = 16`.  The tie is closed by the **fat-centre-aware
  off-diagonal double count** on the seven degree-`4` hubs `T`, threading the hub-edge bound
  `∑_{Hub}|N ∩ Hub| ≤ 8` (`e(Hub) = 4` at `e(M) = 1`): the ordered off-diagonal iso-share sum
  `= ∑_{t∈Iso} d_t(d_t − 1) ≤ 2·16 = 32` (`subset_offDiag_share_eq_twenty`), yet assuming no good
  pair forces every non-adjacent ordered degree-`4` pair to share `≥ 1`, giving `≥ 42 − 8 = 34`,
  a contradiction.
-/

namespace ACMax

open scoped Classical

namespace N20

/-- **All degree-`4` hubs have iso-degree `≥ 2` at the tight `|T| = 7` fat-centre profile.**  If the
seven degree-`4` hubs `T` carry the iso-degree budget `∑_{T} isoDeg = 16` and the strong-hub count
`hmf` gives `#{isoDeg ≥ 3} + #{isoDeg ≥ 4} ≤ 2`, then the threshold decomposition is *tight*
(`c₁ = c₂ = 7`), so every degree-`4` hub has iso-degree `≥ 2`. -/
theorem deg4_isoDeg_ge_two_hub9_twenty (G : SimpleGraph (Fin 20)) (Hub Iso : Finset (Fin 20))
    (hmf : (Hub.filter (fun h => G.degree h = 4 ∧ 3 ≤ (G.neighborFinset h ∩ Iso).card)).card
      + (Hub.filter (fun h => G.degree h = 4 ∧ 4 ≤ (G.neighborFinset h ∩ Iso).card)).card ≤ 2)
    (hTcard : (Hub.filter (fun h => G.degree h = 4)).card = 7)
    (hsum : ∑ v ∈ Hub.filter (fun h => G.degree h = 4), (G.neighborFinset v ∩ Iso).card = 16) :
    ∀ w ∈ Hub.filter (fun h => G.degree h = 4), 2 ≤ (G.neighborFinset w ∩ Iso).card := by
  classical
  set T : Finset (Fin 20) := Hub.filter (fun h => G.degree h = 4) with hT
  intro w hw
  by_contra hlt
  push Not at hlt
  have hiso_le : ∀ a ∈ T, (G.neighborFinset a ∩ Iso).card ≤ 4 := by
    intro a ha
    have hd : G.degree a = 4 := (Finset.mem_filter.mp ha).2
    calc (G.neighborFinset a ∩ Iso).card
        ≤ (G.neighborFinset a).card := Finset.card_le_card Finset.inter_subset_left
      _ = G.degree a := G.card_neighborFinset_eq_degree a
      _ = 4 := hd
  have hdecomp : ∀ a ∈ T, (G.neighborFinset a ∩ Iso).card
      = (if 1 ≤ (G.neighborFinset a ∩ Iso).card then 1 else 0)
        + (if 2 ≤ (G.neighborFinset a ∩ Iso).card then 1 else 0)
        + (if 3 ≤ (G.neighborFinset a ∩ Iso).card then 1 else 0)
        + (if 4 ≤ (G.neighborFinset a ∩ Iso).card then 1 else 0) := by
    intro a ha; have := hiso_le a ha; split_ifs <;> omega
  have hcong : ∑ a ∈ T, (G.neighborFinset a ∩ Iso).card
      = ∑ a ∈ T, ((if 1 ≤ (G.neighborFinset a ∩ Iso).card then 1 else 0)
        + (if 2 ≤ (G.neighborFinset a ∩ Iso).card then 1 else 0)
        + (if 3 ≤ (G.neighborFinset a ∩ Iso).card then 1 else 0)
        + (if 4 ≤ (G.neighborFinset a ∩ Iso).card then 1 else 0)) :=
    Finset.sum_congr rfl hdecomp
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.card_filter, ← Finset.card_filter, ← Finset.card_filter, ← Finset.card_filter] at hcong
  have h3 : T.filter (fun h => 3 ≤ (G.neighborFinset h ∩ Iso).card)
      = Hub.filter (fun h => G.degree h = 4 ∧ 3 ≤ (G.neighborFinset h ∩ Iso).card) := by
    rw [hT, Finset.filter_filter]
  have h4 : T.filter (fun h => 4 ≤ (G.neighborFinset h ∩ Iso).card)
      = Hub.filter (fun h => G.degree h = 4 ∧ 4 ≤ (G.neighborFinset h ∩ Iso).card) := by
    rw [hT, Finset.filter_filter]
  have hn1 : (T.filter (fun h => 1 ≤ (G.neighborFinset h ∩ Iso).card)).card ≤ T.card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  -- The `w` with iso-degree `≤ 1` is excluded from `#{isoDeg ≥ 2}`, so that count is `≤ 6`.
  have hn2 : (T.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)).card ≤ 6 := by
    have hsub : T.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card) ⊆ T.erase w := by
      intro x hx
      rw [Finset.mem_filter] at hx
      rw [Finset.mem_erase]
      refine ⟨?_, hx.1⟩
      rintro rfl
      omega
    calc (T.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)).card
        ≤ (T.erase w).card := Finset.card_le_card hsub
      _ = T.card - 1 := Finset.card_erase_of_mem hw
      _ = 6 := by rw [hTcard]
  rw [h3, h4] at hcong
  omega

/-- **Fat-centre good-pair selection (`n = 20`, `(9, 9, 39)`).**  In the `s = 2`, `|Hub| = 9`
two-hub residual with one degree-`6` fat centre, one degree-`5` hub and seven degree-`4` hubs
(`∑_{Hub} deg = 39`), a good non-adjacent degree-`4` pair with `≥ 2` private twins on each side
exists.  Assuming no such pair, the residual count is pinned to `|T| = 7`, `∑_T isoDeg = 16` and
the off-diagonal double count on `T` overshoots: `34 ≤ ∑_{offDiag} share = ∑_t d_t(d_t − 1) ≤ 32`. -/
theorem fat_centre_two_hub_pair_hub9_twenty (G : SimpleGraph (Fin 20)) (Hub Iso : Finset (Fin 20))
    (hHub9 : Hub.card = 9) (hIso9 : Iso.card = 9)
    (hdeg : ∀ h ∈ Hub, 4 ≤ G.degree h) (hdeg7 : ∀ h ∈ Hub, G.degree h ≤ 7)
    (hdeg6ex : ∃ h ∈ Hub, 6 ≤ G.degree h)
    (hsum39 : ∑ w ∈ Hub, G.degree w = 39)
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hdisj : Disjoint Hub Iso)
    (hhubsum : ∑ w ∈ Hub, (G.neighborFinset w ∩ Hub).card ≤ 8) :
    ∃ h₁ h₂ : Fin 20, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card := by
  classical
  by_contra hcon
  have key := nogood_of_not_select_twenty G Hub Iso hcon
  have hmf := strong_deg4_count_le_two_deg5_twenty G Hub Iso hdisj hshare key
  have hisoSum := hub_iso_sum_twenty G Hub Iso hiso3
  have hTsum_le := deg4_sum_le_twenty G Hub Iso hmf
  set T : Finset (Fin 20) := Hub.filter (fun h => G.degree h = 4) with hTdef
  set R : Finset (Fin 20) := Hub.filter (fun h => ¬ G.degree h = 4) with hRdef
  have hpartIso : ∑ v ∈ T, (G.neighborFinset v ∩ Iso).card
      + ∑ v ∈ R, (G.neighborFinset v ∩ Iso).card = ∑ v ∈ Hub, (G.neighborFinset v ∩ Iso).card :=
    Finset.sum_filter_add_sum_filter_not Hub (fun h => G.degree h = 4) _
  have hRdeg5ge : ∀ v ∈ R, 5 ≤ G.degree v := by
    intro v hv; rw [hRdef, Finset.mem_filter] at hv
    have := hdeg v hv.1; omega
  have hRiso_le : ∑ v ∈ R, (G.neighborFinset v ∩ Iso).card ≤ ∑ v ∈ R, G.degree v := by
    apply Finset.sum_le_sum
    intro v _
    rw [← G.card_neighborFinset_eq_degree]; exact Finset.card_le_card Finset.inter_subset_left
  have hpartDeg : ∑ v ∈ T, G.degree v + ∑ v ∈ R, G.degree v = ∑ v ∈ Hub, G.degree v :=
    Finset.sum_filter_add_sum_filter_not Hub (fun h => G.degree h = 4) _
  have hTdeg : ∑ v ∈ T, G.degree v = 4 * T.card := by
    rw [Finset.sum_congr rfl (fun x hx => (Finset.mem_filter.mp hx).2), Finset.sum_const,
      smul_eq_mul, mul_comm]
  have hRdeg_le : ∑ v ∈ R, G.degree v ≤ 7 * R.card := by
    have hle7 : ∀ v ∈ R, G.degree v ≤ 7 := by
      intro v hv; rw [hRdef, Finset.mem_filter] at hv; exact hdeg7 v hv.1
    calc ∑ v ∈ R, G.degree v ≤ ∑ _v ∈ R, 7 := Finset.sum_le_sum hle7
      _ = 7 * R.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  obtain ⟨fatw, hfatHub, hfat6⟩ := hdeg6ex
  have hfatR : fatw ∈ R := by rw [hRdef, Finset.mem_filter]; exact ⟨hfatHub, by omega⟩
  have hRdeg_ge : 5 * R.card + 1 ≤ ∑ v ∈ R, G.degree v := by
    have hsplit : ∑ v ∈ R, G.degree v
        = G.degree fatw + ∑ v ∈ R.erase fatw, G.degree v := (Finset.add_sum_erase R _ hfatR).symm
    have hbb : 5 * (R.erase fatw).card ≤ ∑ v ∈ R.erase fatw, G.degree v := by
      calc 5 * (R.erase fatw).card = ∑ _v ∈ R.erase fatw, 5 := by
            rw [Finset.sum_const, smul_eq_mul, mul_comm]
        _ ≤ ∑ v ∈ R.erase fatw, G.degree v :=
            Finset.sum_le_sum (fun v hv => hRdeg5ge v (Finset.mem_of_mem_erase hv))
    have hec : (R.erase fatw).card = R.card - 1 := Finset.card_erase_of_mem hfatR
    have hRpos : 1 ≤ R.card := Finset.card_pos.mpr ⟨fatw, hfatR⟩
    omega
  have hcard : T.card + R.card = Hub.card :=
    Finset.card_filter_add_card_filter_not (fun h => G.degree h = 4)
  -- **Pin `|T| = 7` and `∑_T isoDeg = 16`.**
  have hHubiso27 : ∑ a ∈ Hub, (G.neighborFinset a ∩ Iso).card = 27 := by rw [hisoSum, hIso9]
  rw [hHubiso27] at hpartIso
  rw [hsum39] at hpartDeg
  rw [hHub9] at hcard
  have hT7 : T.card = 7 := by omega
  have hTsum16 : ∑ v ∈ T, (G.neighborFinset v ∩ Iso).card = 16 := by omega
  have hTsubHub : T ⊆ Hub := Finset.filter_subset _ _
  have hTdeg4 : ∀ w ∈ T, G.degree w = 4 := fun w hw => (Finset.mem_filter.mp hw).2
  -- **All degree-`4` hubs have iso-degree `≥ 2`.**
  have hge2 : ∀ w ∈ T, 2 ≤ (G.neighborFinset w ∩ Iso).card :=
    deg4_isoDeg_ge_two_hub9_twenty G Hub Iso hmf (by rw [← hTdef]; exact hT7)
      (by rw [← hTdef]; exact hTsum16)
  -- **Off-diagonal double count on `T`.**
  have hident := subset_offDiag_share_eq_twenty G T Iso
  -- Right side `≤ 32`.
  have hdt_le : ∀ t ∈ Iso, (G.neighborFinset t ∩ T).card ≤ 3 := by
    intro t ht
    calc (G.neighborFinset t ∩ T).card
        ≤ (G.neighborFinset t ∩ Hub).card :=
          Finset.card_le_card (Finset.inter_subset_inter (Finset.Subset.refl _) hTsubHub)
      _ = 3 := hiso3 t ht
  have hRHSle : ∑ t ∈ Iso, (G.neighborFinset t ∩ T).card * ((G.neighborFinset t ∩ T).card - 1)
      ≤ ∑ t ∈ Iso, 2 * (G.neighborFinset t ∩ T).card := by
    apply Finset.sum_le_sum
    intro t ht
    have hc3 := hdt_le t ht
    calc (G.neighborFinset t ∩ T).card * ((G.neighborFinset t ∩ T).card - 1)
        ≤ (G.neighborFinset t ∩ T).card * 2 :=
          Nat.mul_le_mul_left _ (by omega)
      _ = 2 * (G.neighborFinset t ∩ T).card := by ring
  have hdtsum : ∑ t ∈ Iso, (G.neighborFinset t ∩ T).card = 16 := by
    rw [cross_count_twenty G Iso T]; exact hTsum16
  have hRHS32 : ∑ t ∈ Iso, (G.neighborFinset t ∩ T).card * ((G.neighborFinset t ∩ T).card - 1)
      ≤ 32 := by
    have heq : ∑ t ∈ Iso, 2 * (G.neighborFinset t ∩ T).card = 2 * 16 := by
      rw [← Finset.mul_sum, hdtsum]
    omega
  -- Left side `≥ 34`.
  set OD : Finset (Fin 20 × Fin 20) := T.offDiag with hODdef
  have hODcard : OD.card = 42 := by
    have h : OD.card = T.card * T.card - T.card := by rw [hODdef, Finset.offDiag_card]
    rw [hT7] at h; omega
  have hadjle : (OD.filter (fun p => G.Adj p.1 p.2)).card ≤ 8 := by
    have hsub : ∑ w ∈ T, (G.neighborFinset w ∩ T).card ≤ 8 := by
      calc ∑ w ∈ T, (G.neighborFinset w ∩ T).card
          ≤ ∑ w ∈ T, (G.neighborFinset w ∩ Hub).card :=
            Finset.sum_le_sum (fun w _ =>
              Finset.card_le_card (Finset.inter_subset_inter (Finset.Subset.refl _) hTsubHub))
        _ ≤ ∑ w ∈ Hub, (G.neighborFinset w ∩ Hub).card :=
            Finset.sum_le_sum_of_subset_of_nonneg hTsubHub (fun _ _ _ => Nat.zero_le _)
        _ ≤ 8 := hhubsum
    exact hub_offDiag_adj_le_twenty G T 8 hsub
  -- Non-adjacent ordered pairs share `≥ 1`.
  have hshare_ge : ∀ p ∈ OD.filter (fun p => ¬ G.Adj p.1 p.2),
      1 ≤ (G.neighborFinset p.1 ∩ G.neighborFinset p.2 ∩ Iso).card := by
    intro p hp
    rw [Finset.mem_filter, hODdef, Finset.mem_offDiag] at hp
    obtain ⟨⟨h1T, h2T, hne⟩, hnadj⟩ := hp
    have hk := key p.1 (hTsubHub h1T) p.2 (hTsubHub h2T) (hTdeg4 p.1 h1T) (hTdeg4 p.2 h2T)
      hne hnadj
    have hm1 := hge2 p.1 h1T
    have hm2 := hge2 p.2 h2T
    have : 2 ≤ min ((G.neighborFinset p.1 ∩ Iso).card) ((G.neighborFinset p.2 ∩ Iso).card) :=
      le_min hm1 hm2
    omega
  have hLHSge : 34 ≤ ∑ p ∈ OD, (G.neighborFinset p.1 ∩ G.neighborFinset p.2 ∩ Iso).card := by
    have hfilterle : ∑ p ∈ OD.filter (fun p => ¬ G.Adj p.1 p.2),
        (G.neighborFinset p.1 ∩ G.neighborFinset p.2 ∩ Iso).card
        ≤ ∑ p ∈ OD, (G.neighborFinset p.1 ∩ G.neighborFinset p.2 ∩ Iso).card := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      exact fun _ _ _ => Nat.zero_le _
    have hnonadjcard : (OD.filter (fun p => ¬ G.Adj p.1 p.2)).card
        = 42 - (OD.filter (fun p => G.Adj p.1 p.2)).card := by
      have hpc := Finset.card_filter_add_card_filter_not (s := OD) (fun p => G.Adj p.1 p.2)
      rw [hODcard] at hpc; omega
    have hcardsum : (OD.filter (fun p => ¬ G.Adj p.1 p.2)).card
        ≤ ∑ p ∈ OD.filter (fun p => ¬ G.Adj p.1 p.2),
          (G.neighborFinset p.1 ∩ G.neighborFinset p.2 ∩ Iso).card := by
      have := Finset.card_nsmul_le_sum (OD.filter (fun p => ¬ G.Adj p.1 p.2))
        (fun p => (G.neighborFinset p.1 ∩ G.neighborFinset p.2 ∩ Iso).card) 1
        (fun p hp => hshare_ge p hp)
      simpa using this
    omega
  rw [hident] at hLHSge
  omega

/-- **PART: the degree-`7` two-hub corner selector (`|Hub| = 9`, `∑deg = 39`, `n = 20`).**  In the
degree-`≥ 6`-carrying `|Hub| = 9` two-hub `s ≤ 2` corner (`(9, 11, 39)` at `e(M) = 0` and
`(9, 9, 39)` at `e(M) = 1`), routed via the degree-`4`-restricted share (`hshare`) and threading the
hub-edge bound `∑_{Hub}|N ∩ Hub| ≤ 8`, either two non-adjacent degree-`4` hubs each retain `≥ 2`
private `M`-isolated twins (a good two-hub opposite-twin pair), or the corner realises one of the
four configuration cuts.  Both surviving profiles populate only the good-pair disjunct:
`(9, 11, 39)` by pure counting, `(9, 9, 39)` by the fat-centre off-diagonal double count. -/
theorem two_hub_deg7_select_hub9_twenty (G : SimpleGraph (Fin 20)) (Hub Iso : Finset (Fin 20))
    (hdeg : ∀ h ∈ Hub, 4 ≤ G.degree h) (hdeg7 : ∀ h ∈ Hub, G.degree h ≤ 7)
    (hex6 : ∃ h ∈ Hub, 6 ≤ G.degree h)
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hdisj : Disjoint Hub Iso)
    (hregime :
      (Hub.card = 9 ∧ Iso.card = 11 ∧ ∑ w ∈ Hub, G.degree w = 39) ∨
      (Hub.card = 9 ∧ Iso.card = 9 ∧ ∑ w ∈ Hub, G.degree w = 39))
    (hhubsum : ∑ w ∈ Hub, (G.neighborFinset w ∩ Hub).card ≤ 8) :
    (∃ h₁ h₂ : Fin 20, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card) ∨
      SingleVertexConfig G ∨ TwoTwinConfig G ∨ TwoHubConfig G ∨ HubTriangleConfig G := by
  classical
  refine Or.inl ?_
  rcases hregime with ⟨hHub, hIso, hdsum⟩ | ⟨hHub, hIso, hdsum⟩
  · -- **`(9, 11, 39)`: pure counting refutes the no-good-pair assumption.**
    by_contra hcon
    have key := nogood_of_not_select_twenty G Hub Iso hcon
    have hmf := strong_deg4_count_le_two_deg5_twenty G Hub Iso hdisj hshare key
    have hisoSum := hub_iso_sum_twenty G Hub Iso hiso3
    have hTsum_le := deg4_sum_le_twenty G Hub Iso hmf
    set T : Finset (Fin 20) := Hub.filter (fun h => G.degree h = 4) with hTdef
    set R : Finset (Fin 20) := Hub.filter (fun h => ¬ G.degree h = 4) with hRdef
    have hpartIso : ∑ v ∈ T, (G.neighborFinset v ∩ Iso).card
        + ∑ v ∈ R, (G.neighborFinset v ∩ Iso).card = ∑ v ∈ Hub, (G.neighborFinset v ∩ Iso).card :=
      Finset.sum_filter_add_sum_filter_not Hub (fun h => G.degree h = 4) _
    have hRdeg5ge : ∀ v ∈ R, 5 ≤ G.degree v := by
      intro v hv; rw [hRdef, Finset.mem_filter] at hv
      have := hdeg v hv.1; omega
    have hRiso_le : ∑ v ∈ R, (G.neighborFinset v ∩ Iso).card ≤ ∑ v ∈ R, G.degree v := by
      apply Finset.sum_le_sum
      intro v _
      rw [← G.card_neighborFinset_eq_degree]; exact Finset.card_le_card Finset.inter_subset_left
    have hpartDeg : ∑ v ∈ T, G.degree v + ∑ v ∈ R, G.degree v = ∑ v ∈ Hub, G.degree v :=
      Finset.sum_filter_add_sum_filter_not Hub (fun h => G.degree h = 4) _
    have hTdeg : ∑ v ∈ T, G.degree v = 4 * T.card := by
      rw [Finset.sum_congr rfl (fun x hx => (Finset.mem_filter.mp hx).2), Finset.sum_const,
        smul_eq_mul, mul_comm]
    have hRdeg_le : ∑ v ∈ R, G.degree v ≤ 7 * R.card := by
      have hle7 : ∀ v ∈ R, G.degree v ≤ 7 := by
        intro v hv; rw [hRdef, Finset.mem_filter] at hv; exact hdeg7 v hv.1
      calc ∑ v ∈ R, G.degree v ≤ ∑ _v ∈ R, 7 := Finset.sum_le_sum hle7
        _ = 7 * R.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    have hRdeg_ge5 : 5 * R.card ≤ ∑ v ∈ R, G.degree v := by
      calc 5 * R.card = ∑ _v ∈ R, 5 := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
        _ ≤ ∑ v ∈ R, G.degree v := Finset.sum_le_sum (fun v hv => hRdeg5ge v hv)
    have hcard : T.card + R.card = Hub.card :=
      Finset.card_filter_add_card_filter_not (fun h => G.degree h = 4)
    have hHubiso33 : ∑ a ∈ Hub, (G.neighborFinset a ∩ Iso).card = 33 := by rw [hisoSum, hIso]
    rw [hHubiso33] at hpartIso
    rw [hdsum] at hpartDeg
    rw [hHub] at hcard
    omega
  · -- **`(9, 9, 39)`: the fat-centre off-diagonal double count.**
    exact fat_centre_two_hub_pair_hub9_twenty G Hub Iso hHub hIso hdeg hdeg7 hex6 hdsum hiso3
      hshare hdisj hhubsum

end N20

end ACMax
