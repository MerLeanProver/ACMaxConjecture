import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N19.Core
import ACMaxConjecture.SmallCases.N19.TwoHubSelect

/-!
# `n = 19`, `e(M) = 2` fat-centre corner `(9, 8, 38)` (`|D| = 10`, `|Hub| = 9`)

This file closes the `s = 2`, `|D| = 10` residual of `two_hub_config_nineteen` at
`TwinCert19.lean:608` in which the nine hubs consist of one degree-`6` **fat centre** and eight
degree-`4` hubs (`∑_{Hub} deg = 38`), with `|Iso| = 8` `M`-isolated twins each meeting exactly three
hubs and `e(Hub) = 5` internal hub edges.

The counting used by `deg6_witness_select_nineteen` only *ties* here (the master inequality reads
`24 = 24`), so it cannot close the corner.  We instead run a **fat-centre-aware off-diagonal
double count** on the eight degree-`4` hubs `W`:

* `∑_{p∈W.offDiag} |N p.1 ∩ N p.2 ∩ Iso| = ∑_{t∈Iso} d_t (d_t − 1)` where `d_t := |N t ∩ W| ≤ 3`
  (`subset_offDiag_share_eq_nineteen`);
* the right side is `≤ 2·∑_t d_t = 2·∑_{W} isoDeg = 2·18 = 36` (each `d_t ≤ 3` gives
  `d_t(d_t−1) ≤ 2 d_t`), where `∑_{W} isoDeg = 18` because the fat centre absorbs the remaining
  `24 − 18 = 6` iso-incidences (`deg4_sum_le_nineteen` forces `≤ 18`, and `isoDeg(fat) ≤ 6` forces
  `≥ 18`);
* assuming **no** good degree-`4` pair, every degree-`4` hub has iso-degree `≥ 2` (tightness of the
  threshold decomposition), so by the `min ≤ share + 1` refutation (`nogood_of_not_select_nineteen`)
  every non-adjacent ordered degree-`4` pair has `share ≥ 1`, whence the left side is
  `≥ |W.offDiag| − #adjacent = 56 − 10 = 46` (adjacent ordered pairs number `≤ 2·e(Hub) = 10`).

`46 ≤ 36` is absurd, so a good non-adjacent degree-`4` pair with `≥ 2` private twins each exists —
delivering `TwoHubConfig` at the call site via `pairToTH`. -/

namespace ACMax

open scoped Classical

namespace N19

/-- **Adjacent ordered hub pairs equal the hub-incidence sum (`n = 19`).**  With
`∑_{w∈Hub}|N w ∩ Hub| ≤ k`, the ordered off-diagonal adjacent pairs number at most `k`. -/
theorem hub_offDiag_adj_le_nineteen (G : SimpleGraph (Fin 19)) (Hub : Finset (Fin 19)) (k : ℕ)
    (hHubsum : ∑ w ∈ Hub, (G.neighborFinset w ∩ Hub).card ≤ k) :
    (Hub.offDiag.filter (fun p => G.Adj p.1 p.2)).card ≤ k := by
  classical
  have hfilt : Hub.offDiag.filter (fun p => G.Adj p.1 p.2)
      = (Hub ×ˢ Hub).filter (fun p => G.Adj p.1 p.2) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_offDiag, Finset.mem_product]
    constructor
    · rintro ⟨⟨h1, h2, _⟩, hadj⟩; exact ⟨⟨h1, h2⟩, hadj⟩
    · rintro ⟨⟨h1, h2⟩, hadj⟩; exact ⟨⟨h1, h2, G.ne_of_adj hadj⟩, hadj⟩
  rw [hfilt, Finset.card_filter, Finset.sum_product]
  have hrow : ∀ a : Fin 19, ∑ b ∈ Hub, (if G.Adj a b then 1 else 0)
      = (G.neighborFinset a ∩ Hub).card := by
    intro a
    rw [Finset.inter_comm, ← Finset.filter_mem_eq_inter, Finset.card_filter]
    exact Finset.sum_congr rfl (fun b _ => by simp only [G.mem_neighborFinset])
  rw [Finset.sum_congr rfl (fun a _ => hrow a)]
  exact hHubsum

/-- **Subset off-diagonal share double count (`n = 19`).**  For any vertex subset `W`, the ordered
off-diagonal iso-share sum equals `∑_{t∈Iso} d_t (d_t − 1)` where `d_t = |N t ∩ W|`. -/
theorem subset_offDiag_share_eq_nineteen (G : SimpleGraph (Fin 19)) (W Iso : Finset (Fin 19)) :
    ∑ p ∈ W.offDiag, (G.neighborFinset p.1 ∩ G.neighborFinset p.2 ∩ Iso).card
      = ∑ t ∈ Iso, (G.neighborFinset t ∩ W).card * ((G.neighborFinset t ∩ W).card - 1) := by
  classical
  have hcard : ∀ a b : Fin 19, (G.neighborFinset a ∩ G.neighborFinset b ∩ Iso).card
      = ∑ t ∈ Iso, (if G.Adj a t then 1 else 0) * (if G.Adj b t then 1 else 0) := by
    intro a b
    rw [show G.neighborFinset a ∩ G.neighborFinset b ∩ Iso
        = Iso.filter (fun t => G.Adj a t ∧ G.Adj b t) by
      ext t
      simp only [Finset.mem_inter, Finset.mem_filter, G.mem_neighborFinset]
      tauto]
    rw [Finset.card_filter]
    apply Finset.sum_congr rfl
    intro t _
    by_cases ha : G.Adj a t <;> by_cases hb : G.Adj b t <;> simp [ha, hb]
  rw [Finset.sum_congr rfl (fun p _ => hcard p.1 p.2), Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  set g : Fin 19 → ℕ := fun a => if G.Adj a t then 1 else 0 with hg
  have hS : ∑ a ∈ W, g a = (G.neighborFinset t ∩ W).card := by
    rw [show (G.neighborFinset t ∩ W) = W.filter (fun a => G.Adj a t) by
      ext a
      simp only [Finset.mem_inter, Finset.mem_filter, G.mem_neighborFinset]
      rw [SimpleGraph.adj_comm]
      tauto]
    rw [Finset.card_filter]
  have hprod : ∑ p ∈ W ×ˢ W, g p.1 * g p.2 = (∑ a ∈ W, g a) * (∑ a ∈ W, g a) := by
    rw [Finset.sum_mul_sum, Finset.sum_product]
  have hdiag : ∑ p ∈ W.diag, g p.1 * g p.2 = ∑ a ∈ W, g a := by
    rw [Finset.diag, Finset.sum_map]
    change ∑ a ∈ W, g a * g a = _
    apply Finset.sum_congr rfl
    intro a _
    rw [hg]
    by_cases ha : G.Adj a t <;> simp [ha]
  have hsplit : ∑ p ∈ W.diag, g p.1 * g p.2 + ∑ p ∈ W.offDiag, g p.1 * g p.2
      = ∑ p ∈ W ×ˢ W, g p.1 * g p.2 := by
    rw [← Finset.sum_union (Finset.disjoint_diag_offDiag W), Finset.diag_union_offDiag]
  rw [hdiag, hprod, hS] at hsplit
  rw [show ∑ p ∈ W.offDiag, (if G.Adj p.1 t then 1 else 0) * (if G.Adj p.2 t then 1 else 0)
      = ∑ p ∈ W.offDiag, g p.1 * g p.2 from rfl, Nat.sub_one, Nat.mul_pred]
  omega

/-- **All degree-`4` hubs have iso-degree `≥ 2` at the tight fat-centre profile.**  If the eight
degree-`4` hubs `T` carry the full iso-degree budget `∑_{T} isoDeg = 18` and the strong-hub count
`hmf` gives `#{isoDeg ≥ 3} + #{isoDeg ≥ 4} ≤ 2`, then the threshold decomposition is *tight*
(`c₁ = c₂ = 8`), so every degree-`4` hub has iso-degree `≥ 2`. -/
theorem deg4_isoDeg_ge_two_nineteen (G : SimpleGraph (Fin 19)) (Hub Iso : Finset (Fin 19))
    (hmf : (Hub.filter (fun h => G.degree h = 4 ∧ 3 ≤ (G.neighborFinset h ∩ Iso).card)).card
      + (Hub.filter (fun h => G.degree h = 4 ∧ 4 ≤ (G.neighborFinset h ∩ Iso).card)).card ≤ 2)
    (hTcard : (Hub.filter (fun h => G.degree h = 4)).card = 8)
    (hsum : ∑ v ∈ Hub.filter (fun h => G.degree h = 4), (G.neighborFinset v ∩ Iso).card = 18) :
    ∀ w ∈ Hub.filter (fun h => G.degree h = 4), 2 ≤ (G.neighborFinset w ∩ Iso).card := by
  classical
  set T : Finset (Fin 19) := Hub.filter (fun h => G.degree h = 4) with hT
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
  -- The `w` with iso-degree `≤ 1` is excluded from `#{isoDeg ≥ 2}`, so that count is `≤ 7`.
  have hn2 : (T.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)).card ≤ 7 := by
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
      _ = 7 := by rw [hTcard]
  rw [h3, h4] at hcong
  omega

/-- **Fat-centre good-pair selection (`n = 19`, `(9, 8, 38)`).**  In the `s = 2`, `|D| = 10`
two-hub residual with one degree-`6` fat centre and eight degree-`4` hubs, a good non-adjacent
degree-`4` pair with `≥ 2` private twins on each side exists. -/
theorem fat_centre_two_hub_pair_nineteen (G : SimpleGraph (Fin 19)) (Hub Iso : Finset (Fin 19))
    (hHub9 : Hub.card = 9) (hIso8 : Iso.card = 8)
    (hdeg : ∀ h ∈ Hub, 4 ≤ G.degree h) (hdeg7 : ∀ h ∈ Hub, G.degree h ≤ 7)
    (hdeg6ex : ∃ h ∈ Hub, 6 ≤ G.degree h)
    (hsum38 : ∑ w ∈ Hub, G.degree w = 38)
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hdisj : Disjoint Hub Iso)
    (hhubsum : ∑ w ∈ Hub, (G.neighborFinset w ∩ Hub).card ≤ 10) :
    ∃ h₁ h₂ : Fin 19, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card := by
  classical
  by_contra hcon
  have key := nogood_of_not_select_nineteen G Hub Iso hcon
  have hmf := strong_deg4_count_le_two_deg5_nineteen G Hub Iso hdisj hshare key
  -- **Degree structure: one degree-`6` fat centre, eight degree-`4` hubs.**
  obtain ⟨fat, hfatHub, hfat6⟩ := hdeg6ex
  have hcerase : (Hub.erase fat).card = 8 := by
    rw [Finset.card_erase_of_mem hfatHub, hHub9]
  have hgeErase : 4 * (Hub.erase fat).card ≤ ∑ v ∈ Hub.erase fat, G.degree v := by
    have hbb : ∀ x ∈ Hub.erase fat, 4 ≤ G.degree x := fun i hi =>
      hdeg i (Finset.mem_of_mem_erase hi)
    have h := Finset.card_nsmul_le_sum (Hub.erase fat) (fun v => G.degree v) 4 hbb
    simpa [smul_eq_mul, mul_comm] using h
  have hsplitfat := Finset.add_sum_erase Hub (fun v => G.degree v) hfatHub
  rw [hsum38] at hsplitfat
  have hfat7 := hdeg7 fat hfatHub
  have hfatdeg : G.degree fat = 6 := by omega
  have heraseSum : ∑ v ∈ Hub.erase fat, G.degree v = 32 := by omega
  -- Every non-`fat` hub has degree `4`.
  have hother : ∀ w ∈ Hub, w ≠ fat → G.degree w = 4 := by
    intro w hwHub hwne
    have hwE : w ∈ Hub.erase fat := Finset.mem_erase.mpr ⟨hwne, hwHub⟩
    by_contra hd4
    have hw5 : 5 ≤ G.degree w := by have := hdeg w hwHub; omega
    have hsplitw := Finset.add_sum_erase (Hub.erase fat) (fun v => G.degree v) hwE
    have hge2 : 4 * ((Hub.erase fat).erase w).card
        ≤ ∑ v ∈ (Hub.erase fat).erase w, G.degree v := by
      have hbb : ∀ x ∈ (Hub.erase fat).erase w, 4 ≤ G.degree x := fun i hi =>
        hdeg i (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hi))
      have h := Finset.card_nsmul_le_sum ((Hub.erase fat).erase w) (fun v => G.degree v) 4 hbb
      simpa [smul_eq_mul, mul_comm] using h
    have hc2 : ((Hub.erase fat).erase w).card = 7 := by
      rw [Finset.card_erase_of_mem hwE, hcerase]
    rw [heraseSum] at hsplitw
    omega
  -- `T := Hub.filter (deg = 4)` is `Hub.erase fat`, of card `8`.
  set T : Finset (Fin 19) := Hub.filter (fun h => G.degree h = 4) with hTdef
  have hcompl : Hub.filter (fun h => ¬ G.degree h = 4) = {fat} := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hwHub, hwd⟩
      by_contra hwne
      exact hwd (hother w hwHub hwne)
    · rintro rfl; exact ⟨hfatHub, by omega⟩
  have hTcard : T.card = 8 := by
    have hpc := Finset.card_filter_add_card_filter_not (s := Hub) (fun h => G.degree h = 4)
    rw [hcompl, Finset.card_singleton, hHub9] at hpc
    rw [hTdef]; omega
  have hTsubHub : T ⊆ Hub := Finset.filter_subset _ _
  have hTdeg4 : ∀ w ∈ T, G.degree w = 4 := fun w hw => (Finset.mem_filter.mp hw).2
  -- **Iso-degree budget: `∑_{T} isoDeg = 18` (fat absorbs the other `6`).**
  have hHubiso : ∑ a ∈ Hub, (G.neighborFinset a ∩ Iso).card = 24 := by
    rw [hub_iso_sum_nineteen G Hub Iso hiso3, hIso8]
  have hpartIso : ∑ v ∈ T, (G.neighborFinset v ∩ Iso).card
      + ∑ v ∈ Hub.filter (fun h => ¬ G.degree h = 4), (G.neighborFinset v ∩ Iso).card
      = ∑ v ∈ Hub, (G.neighborFinset v ∩ Iso).card :=
    Finset.sum_filter_add_sum_filter_not Hub (fun h => G.degree h = 4) _
  have hfatiso : ∑ v ∈ Hub.filter (fun h => ¬ G.degree h = 4), (G.neighborFinset v ∩ Iso).card
      = (G.neighborFinset fat ∩ Iso).card := by rw [hcompl, Finset.sum_singleton]
  have hfatisole : (G.neighborFinset fat ∩ Iso).card ≤ 6 := by
    calc (G.neighborFinset fat ∩ Iso).card
        ≤ (G.neighborFinset fat).card := Finset.card_le_card Finset.inter_subset_left
      _ = G.degree fat := G.card_neighborFinset_eq_degree fat
      _ = 6 := hfatdeg
  have hTsumle : ∑ v ∈ T, (G.neighborFinset v ∩ Iso).card ≤ 18 := by
    have h := deg4_sum_le_nineteen G Hub Iso hmf
    rw [← hTdef] at h; rw [hTcard] at h; omega
  have hTsum18 : ∑ v ∈ T, (G.neighborFinset v ∩ Iso).card = 18 := by
    rw [hHubiso, hfatiso] at hpartIso; omega
  -- **All degree-`4` hubs have iso-degree `≥ 2`.**
  have hge2 : ∀ w ∈ T, 2 ≤ (G.neighborFinset w ∩ Iso).card :=
    deg4_isoDeg_ge_two_nineteen G Hub Iso hmf (by rw [← hTdef]; exact hTcard)
      (by rw [← hTdef]; exact hTsum18)
  -- **Off-diagonal double count on `T`.**
  have hident := subset_offDiag_share_eq_nineteen G T Iso
  -- Right side `≤ 36`.
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
  have hdtsum : ∑ t ∈ Iso, (G.neighborFinset t ∩ T).card = 18 := by
    rw [cross_count_nineteen G Iso T]; exact hTsum18
  have hRHS36 : ∑ t ∈ Iso, (G.neighborFinset t ∩ T).card * ((G.neighborFinset t ∩ T).card - 1)
      ≤ 36 := by
    have heq : ∑ t ∈ Iso, 2 * (G.neighborFinset t ∩ T).card = 2 * 18 := by
      rw [← Finset.mul_sum, hdtsum]
    omega
  -- Left side `≥ 46`.
  set OD : Finset (Fin 19 × Fin 19) := T.offDiag with hODdef
  have hODcard : OD.card = 56 := by
    have h : OD.card = T.card * T.card - T.card := by rw [hODdef, Finset.offDiag_card]
    rw [hTcard] at h; omega
  have hadjle : (OD.filter (fun p => G.Adj p.1 p.2)).card ≤ 10 := by
    have hsub : ∑ w ∈ T, (G.neighborFinset w ∩ T).card ≤ 10 := by
      calc ∑ w ∈ T, (G.neighborFinset w ∩ T).card
          ≤ ∑ w ∈ T, (G.neighborFinset w ∩ Hub).card :=
            Finset.sum_le_sum (fun w _ =>
              Finset.card_le_card (Finset.inter_subset_inter (Finset.Subset.refl _) hTsubHub))
        _ ≤ ∑ w ∈ Hub, (G.neighborFinset w ∩ Hub).card :=
            Finset.sum_le_sum_of_subset_of_nonneg hTsubHub (fun _ _ _ => Nat.zero_le _)
        _ ≤ 10 := hhubsum
    exact hub_offDiag_adj_le_nineteen G T 10 hsub
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
  have hLHSge : 46 ≤ ∑ p ∈ OD, (G.neighborFinset p.1 ∩ G.neighborFinset p.2 ∩ Iso).card := by
    have hfilterle : ∑ p ∈ OD.filter (fun p => ¬ G.Adj p.1 p.2),
        (G.neighborFinset p.1 ∩ G.neighborFinset p.2 ∩ Iso).card
        ≤ ∑ p ∈ OD, (G.neighborFinset p.1 ∩ G.neighborFinset p.2 ∩ Iso).card := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      exact fun _ _ _ => Nat.zero_le _
    have hnonadjcard : (OD.filter (fun p => ¬ G.Adj p.1 p.2)).card
        = 56 - (OD.filter (fun p => G.Adj p.1 p.2)).card := by
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

end N19

end ACMax
