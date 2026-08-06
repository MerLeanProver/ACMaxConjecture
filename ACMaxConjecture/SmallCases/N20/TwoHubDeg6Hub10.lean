import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N20.Core
import ACMaxConjecture.SmallCases.N20.Core
import ACMaxConjecture.SmallCases.StarCertificates
import ACMaxConjecture.SmallCases.N20.TwoHubSelect
import ACMaxConjecture.SmallCases.N20.FatCentre

/-!
# Degree-`6`-aware two-hub corner selection for `n = 20` (`|Hub| = 10`, `∑deg = 42`)

This file supplies `two_hub_deg6_select_hub10_twenty`, the hub-pair *selection* lemma for the two
`s ≤ 2` two-hub corners with `|Hub| = 10`, `∑_{Hub} deg = 42` and a **degree-`6`** hub present (so
the degree-`≤ 5` selector `two_hub_corner_select_deg5_twenty` does not apply):

* `s = 0`: `(|Hub|, |Iso|, ∑deg) = (10, 10, 42)`;
* `s = 2`: `(|Hub|, |Iso|, ∑deg) = (10, 8, 42)`.

Since every hub has degree `4 ≤ deg ≤ 6`, `∑deg = 42` over ten hubs with a witnessed degree-`6` hub
`F` forces `Hub \ {F}` to be nine degree-`4` hubs (`42 = 6 + 9·4`) — `F` is the **unique** fat
centre.  Write `T = Hub \ {F}` and `f = |N F ∩ Iso|`.

* **`(10, 10, 42)` (counting):**  `∑_{Hub} isoDeg = 30`, and the threshold bound gives
  `∑_T isoDeg ≤ 2·9 + 2 = 20`; but `∑_T isoDeg = 30 − f ≥ 24`, a contradiction.
* **`(10, 8, 42)` (fat-centre double count):**  `∑_{Hub} isoDeg = 24`, so `∑_T isoDeg = 24 − f`.
  Because `T = Hub \ {F}`, every `M`-isolated twin `t` has `|N t ∩ T| = 3 − [t ∼ F]`, so the
  off-diagonal iso-share double count over `T` is **exact**: `∑_{T.offDiag} share = 48 − 4f`.  On the
  rich degree-`4` hubs (iso-degree `≥ 2`, cardinality `c₂`) the no-good-pair assumption forces every
  non-adjacent ordered pair to share `≥ 1`, whence `∑_{T.offDiag} share ≥ c₂² − 5c₂ + σ` with
  `σ = ∑_{rich} isoDeg ≥ 2c₂`; combined with the threshold `∑_T isoDeg ≤ 11 + c₂` (which forces
  `c₂ ≥ 13 − f ≥ 7`) the exact value `48 − 4f` is too small — a contradiction for every `c₂ ≤ 9`.

In both corners the good non-adjacent degree-`4` opposite-twin pair therefore exists, so the widened
conclusion is realised through its first (`Or.inl`) disjunct; the configuration disjuncts stay unused.
-/

namespace ACMax

open scoped Classical

namespace N20

/-- **Degree-`6` `|Hub| = 10` two-hub corner selector (`n = 20`).**  In the `∑deg = 42` two-hub
`s ≤ 2` corners with `|Iso| ∈ {10, 8}` and a witnessed degree-`6` hub (`hex6`), each `M`-isolated
twin meeting exactly three hubs (`hiso3`) and the good-`C₄` share `≤ 1` for **degree-`4`** hub pairs
(`hshare`), there exist two non-adjacent degree-`4` hubs each retaining `≥ 2` private `M`-isolated
twins.  Both corners close on the good pair, so the configuration disjuncts stay unused. -/
theorem two_hub_deg6_select_hub10_twenty (G : SimpleGraph (Fin 20)) (Hub Iso : Finset (Fin 20))
    (hdeg : ∀ h ∈ Hub, 4 ≤ G.degree h) (hdeg6 : ∀ h ∈ Hub, G.degree h ≤ 6)
    (hex6 : ∃ h ∈ Hub, 6 ≤ G.degree h)
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hdisj : Disjoint Hub Iso)
    (hregime :
      (Hub.card = 10 ∧ Iso.card = 10 ∧ ∑ w ∈ Hub, G.degree w = 42) ∨
      (Hub.card = 10 ∧ Iso.card = 8 ∧ ∑ w ∈ Hub, G.degree w = 42)) :
    (∃ h₁ h₂ : Fin 20, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card) ∨
      SingleVertexConfig G ∨ TwoTwinConfig G ∨ TwoHubConfig G ∨ HubTriangleConfig G := by
  classical
  refine Or.inl ?_
  by_contra hcon
  have key := nogood_of_not_select_twenty G Hub Iso hcon
  have hmf := strong_deg4_count_le_two_deg5_twenty G Hub Iso hdisj hshare key
  obtain ⟨F, hFHub, hF6⟩ := hex6
  have hFdeg : G.degree F = 6 := le_antisymm (hdeg6 F hFHub) hF6
  have hHub10 : Hub.card = 10 := by rcases hregime with ⟨h, _, _⟩ | ⟨h, _, _⟩ <;> exact h
  have hsum42 : ∑ w ∈ Hub, G.degree w = 42 := by
    rcases hregime with ⟨_, _, h⟩ | ⟨_, _, h⟩ <;> exact h
  -- **`Hub \ {F}` is nine degree-`4` hubs.**
  have hcerase : (Hub.erase F).card = 9 := by rw [Finset.card_erase_of_mem hFHub, hHub10]
  have heraseSum : ∑ v ∈ Hub.erase F, G.degree v = 36 := by
    have h := Finset.add_sum_erase Hub (fun v => G.degree v) hFHub
    rw [hsum42, hFdeg] at h; omega
  have hother : ∀ w ∈ Hub, w ≠ F → G.degree w = 4 := by
    intro w hwHub hwne
    have hwE : w ∈ Hub.erase F := Finset.mem_erase.mpr ⟨hwne, hwHub⟩
    by_contra hd4
    have hw5 : 5 ≤ G.degree w := by have := hdeg w hwHub; omega
    have hsplitw := Finset.add_sum_erase (Hub.erase F) (fun v => G.degree v) hwE
    have hge2 : 4 * ((Hub.erase F).erase w).card ≤ ∑ v ∈ (Hub.erase F).erase w, G.degree v := by
      have hbb : ∀ x ∈ (Hub.erase F).erase w, 4 ≤ G.degree x := fun i hi =>
        hdeg i (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hi))
      have h := Finset.card_nsmul_le_sum ((Hub.erase F).erase w) (fun v => G.degree v) 4 hbb
      simpa [smul_eq_mul, mul_comm] using h
    have hc2 : ((Hub.erase F).erase w).card = 8 := by
      rw [Finset.card_erase_of_mem hwE, hcerase]
    rw [hc2] at hge2
    rw [heraseSum] at hsplitw
    omega
  set T : Finset (Fin 20) := Hub.filter (fun h => G.degree h = 4) with hTdef
  have hTeq : T = Hub.erase F := by
    ext w
    simp only [hTdef, Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨hwHub, hwd⟩
      refine ⟨?_, hwHub⟩
      rintro rfl
      omega
    · rintro ⟨hwne, hwHub⟩
      exact ⟨hwHub, hother w hwHub hwne⟩
  have hTcard : T.card = 9 := by rw [hTeq]; exact hcerase
  have hTsubHub : T ⊆ Hub := Finset.filter_subset _ _
  have hTdeg4 : ∀ w ∈ T, G.degree w = 4 := fun w hw => (Finset.mem_filter.mp hw).2
  -- **Iso-degree budget.**
  have hHubiso : ∑ a ∈ Hub, (G.neighborFinset a ∩ Iso).card = 3 * Iso.card :=
    hub_iso_sum_twenty G Hub Iso hiso3
  have hisoSplit : (G.neighborFinset F ∩ Iso).card + ∑ v ∈ T, (G.neighborFinset v ∩ Iso).card
      = 3 * Iso.card := by
    have h := Finset.add_sum_erase Hub (fun v => (G.neighborFinset v ∩ Iso).card) hFHub
    rw [hHubiso] at h
    rw [hTeq]; exact h
  have hfle : (G.neighborFinset F ∩ Iso).card ≤ 6 := by
    calc (G.neighborFinset F ∩ Iso).card ≤ (G.neighborFinset F).card :=
          Finset.card_le_card Finset.inter_subset_left
      _ = G.degree F := G.card_neighborFinset_eq_degree F
      _ = 6 := hFdeg
  have hTsumle : ∑ v ∈ T, (G.neighborFinset v ∩ Iso).card ≤ 20 := by
    have h := deg4_sum_le_twenty G Hub Iso hmf
    rw [← hTdef] at h; rw [hTcard] at h; omega
  rcases hregime with ⟨_, hIso, _⟩ | ⟨_, hIso, _⟩
  · -- **`(10, 10, 42)`: counting.**
    rw [hIso] at hisoSplit
    omega
  · -- **`(10, 8, 42)`: fat-centre double count.**
    -- **Threshold decomposition on `T`.**
    have hiso_le4 : ∀ a ∈ T, (G.neighborFinset a ∩ Iso).card ≤ 4 := by
      intro a ha
      calc (G.neighborFinset a ∩ Iso).card ≤ (G.neighborFinset a).card :=
            Finset.card_le_card Finset.inter_subset_left
        _ = G.degree a := G.card_neighborFinset_eq_degree a
        _ = 4 := hTdeg4 a ha
    have hdecomp : ∀ a ∈ T, (G.neighborFinset a ∩ Iso).card
        = (if 1 ≤ (G.neighborFinset a ∩ Iso).card then 1 else 0)
          + (if 2 ≤ (G.neighborFinset a ∩ Iso).card then 1 else 0)
          + (if 3 ≤ (G.neighborFinset a ∩ Iso).card then 1 else 0)
          + (if 4 ≤ (G.neighborFinset a ∩ Iso).card then 1 else 0) := by
      intro a ha; have := hiso_le4 a ha; split_ifs <;> omega
    have hcong : ∑ a ∈ T, (G.neighborFinset a ∩ Iso).card
        = ∑ a ∈ T, ((if 1 ≤ (G.neighborFinset a ∩ Iso).card then 1 else 0)
          + (if 2 ≤ (G.neighborFinset a ∩ Iso).card then 1 else 0)
          + (if 3 ≤ (G.neighborFinset a ∩ Iso).card then 1 else 0)
          + (if 4 ≤ (G.neighborFinset a ∩ Iso).card then 1 else 0)) := Finset.sum_congr rfl hdecomp
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.card_filter, ← Finset.card_filter, ← Finset.card_filter, ← Finset.card_filter] at hcong
    have hc3eq : T.filter (fun h => 3 ≤ (G.neighborFinset h ∩ Iso).card)
        = Hub.filter (fun h => G.degree h = 4 ∧ 3 ≤ (G.neighborFinset h ∩ Iso).card) := by
      rw [hTdef, Finset.filter_filter]
    have hc4eq : T.filter (fun h => 4 ≤ (G.neighborFinset h ∩ Iso).card)
        = Hub.filter (fun h => G.degree h = 4 ∧ 4 ≤ (G.neighborFinset h ∩ Iso).card) := by
      rw [hTdef, Finset.filter_filter]
    rw [hc3eq, hc4eq] at hcong
    have hc1le : (T.filter (fun h => 1 ≤ (G.neighborFinset h ∩ Iso).card)).card ≤ 9 := by
      have := Finset.card_le_card
        (Finset.filter_subset (fun h => 1 ≤ (G.neighborFinset h ∩ Iso).card) T)
      omega
    set T2 : Finset (Fin 20) := T.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card) with hT2def
    have hT2subT : T2 ⊆ T := Finset.filter_subset _ _
    have hT2subHub : T2 ⊆ Hub := hT2subT.trans hTsubHub
    -- **Exact off-diagonal iso-share double count over `T = Hub \ {F}`.**
    have hident := subset_offDiag_share_eq_twenty G T Iso
    have hsummand : ∀ t ∈ Iso,
        (G.neighborFinset t ∩ T).card * ((G.neighborFinset t ∩ T).card - 1)
        = (if F ∈ G.neighborFinset t then 2 else 6) := by
      intro t ht
      have htH : (G.neighborFinset t ∩ Hub).card = 3 := hiso3 t ht
      have hTe : G.neighborFinset t ∩ T = (G.neighborFinset t ∩ Hub).erase F := by
        rw [hTeq]
        ext x
        simp only [Finset.mem_inter, Finset.mem_erase]
        tauto
      by_cases hF : F ∈ G.neighborFinset t
      · have hFmem : F ∈ G.neighborFinset t ∩ Hub := Finset.mem_inter.mpr ⟨hF, hFHub⟩
        rw [hTe, Finset.card_erase_of_mem hFmem, htH]; simp [hF]
      · have hFnmem : F ∉ G.neighborFinset t ∩ Hub := fun h => hF (Finset.mem_inter.mp h).1
        rw [hTe, Finset.erase_eq_of_notMem hFnmem, htH]; simp [hF]
    have hRHS : (∑ t ∈ Iso, (G.neighborFinset t ∩ T).card * ((G.neighborFinset t ∩ T).card - 1))
        = 2 * (Iso.filter (fun t => F ∈ G.neighborFinset t)).card
          + 6 * (Iso.filter (fun t => ¬ F ∈ G.neighborFinset t)).card := by
      rw [Finset.sum_congr rfl hsummand, Finset.sum_ite, Finset.sum_const, Finset.sum_const,
        smul_eq_mul, smul_eq_mul]
      ring
    have hLHSval : ∑ p ∈ T.offDiag,
        (G.neighborFinset p.1 ∩ G.neighborFinset p.2 ∩ Iso).card
        = 2 * (Iso.filter (fun t => F ∈ G.neighborFinset t)).card
          + 6 * (Iso.filter (fun t => ¬ F ∈ G.neighborFinset t)).card := hident.trans hRHS
    have hAeq : (Iso.filter (fun t => F ∈ G.neighborFinset t)) = G.neighborFinset F ∩ Iso := by
      ext t
      simp only [Finset.mem_filter, Finset.mem_inter, G.mem_neighborFinset]
      rw [SimpleGraph.adj_comm]; tauto
    have hA : (Iso.filter (fun t => F ∈ G.neighborFinset t)).card
        = (G.neighborFinset F ∩ Iso).card := by rw [hAeq]
    have hAB : (Iso.filter (fun t => F ∈ G.neighborFinset t)).card
        + (Iso.filter (fun t => ¬ F ∈ G.neighborFinset t)).card = Iso.card :=
      Finset.card_filter_add_card_filter_not (s := Iso) (fun t => F ∈ G.neighborFinset t)
    -- **Lower bound on the off-diagonal share sum from the no-good-pair assumption.**
    have hoffsub : T2.offDiag ⊆ T.offDiag := by
      intro p hp; rw [Finset.mem_offDiag] at hp ⊢
      exact ⟨hT2subT hp.1, hT2subT hp.2.1, hp.2.2⟩
    have hshare_ge : ∀ p ∈ T2.offDiag.filter (fun p => ¬ G.Adj p.1 p.2),
        1 ≤ (G.neighborFinset p.1 ∩ G.neighborFinset p.2 ∩ Iso).card := by
      intro p hp
      rw [Finset.mem_filter, Finset.mem_offDiag] at hp
      obtain ⟨⟨h1, h2, hne⟩, hnadj⟩ := hp
      have h1T := hT2subT h1
      have h2T := hT2subT h2
      have hk := key p.1 (hTsubHub h1T) p.2 (hTsubHub h2T) (hTdeg4 p.1 h1T) (hTdeg4 p.2 h2T)
        hne hnadj
      have hm1 : 2 ≤ (G.neighborFinset p.1 ∩ Iso).card := (Finset.mem_filter.mp h1).2
      have hm2 : 2 ≤ (G.neighborFinset p.2 ∩ Iso).card := (Finset.mem_filter.mp h2).2
      have : 2 ≤ min ((G.neighborFinset p.1 ∩ Iso).card) ((G.neighborFinset p.2 ∩ Iso).card) :=
        le_min hm1 hm2
      omega
    have hLHSge : (T2.offDiag.filter (fun p => ¬ G.Adj p.1 p.2)).card
        ≤ ∑ p ∈ T.offDiag, (G.neighborFinset p.1 ∩ G.neighborFinset p.2 ∩ Iso).card := by
      calc (T2.offDiag.filter (fun p => ¬ G.Adj p.1 p.2)).card
          = ∑ _p ∈ T2.offDiag.filter (fun p => ¬ G.Adj p.1 p.2), 1 := by
            rw [Finset.sum_const, smul_eq_mul, mul_one]
        _ ≤ ∑ p ∈ T2.offDiag.filter (fun p => ¬ G.Adj p.1 p.2),
              (G.neighborFinset p.1 ∩ G.neighborFinset p.2 ∩ Iso).card :=
            Finset.sum_le_sum hshare_ge
        _ ≤ ∑ p ∈ T.offDiag, (G.neighborFinset p.1 ∩ G.neighborFinset p.2 ∩ Iso).card :=
            Finset.sum_le_sum_of_subset_of_nonneg
              (Finset.Subset.trans (Finset.filter_subset _ _) hoffsub)
              (fun _ _ _ => Nat.zero_le _)
    -- **Adjacent ordered rich pairs are absorbed by the degree-`4`/iso-degree budget.**
    have hadjle : (T2.offDiag.filter (fun p => G.Adj p.1 p.2)).card
        ≤ ∑ w ∈ T2, (G.neighborFinset w ∩ T2).card :=
      hub_offDiag_adj_le_twenty G T2 (∑ w ∈ T2, (G.neighborFinset w ∩ T2).card) (le_refl _)
    have hsum4 : (∑ w ∈ T2, (G.neighborFinset w ∩ T2).card)
        + (∑ w ∈ T2, (G.neighborFinset w ∩ Iso).card) ≤ 4 * T2.card := by
      have hpt : ∀ w ∈ T2, (G.neighborFinset w ∩ T2).card
          + (G.neighborFinset w ∩ Iso).card ≤ 4 := by
        intro w hw
        have hwd4 : G.degree w = 4 := hTdeg4 w (hT2subT hw)
        have hsub : (G.neighborFinset w ∩ T2).card ≤ (G.neighborFinset w ∩ Hub).card :=
          Finset.card_le_card (Finset.inter_subset_inter (Finset.Subset.refl _) hT2subHub)
        have hnb := hub_neighbor_le_twenty G Hub Iso hdisj w hwd4
        omega
      have hs := Finset.sum_le_sum hpt
      rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_comm] at hs
      exact hs
    have hsig2 : 2 * T2.card ≤ ∑ w ∈ T2, (G.neighborFinset w ∩ Iso).card := by
      have hge : ∀ w ∈ T2, 2 ≤ (G.neighborFinset w ∩ Iso).card :=
        fun w hw => (Finset.mem_filter.mp hw).2
      calc 2 * T2.card = ∑ _w ∈ T2, 2 := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
        _ ≤ ∑ w ∈ T2, (G.neighborFinset w ∩ Iso).card := Finset.sum_le_sum hge
    have hsplitOD : (T2.offDiag.filter (fun p => ¬ G.Adj p.1 p.2)).card
        + (T2.offDiag.filter (fun p => G.Adj p.1 p.2)).card = T2.offDiag.card := by
      rw [add_comm]
      exact Finset.card_filter_add_card_filter_not (s := T2.offDiag) (fun p => G.Adj p.1 p.2)
    have hODcard : T2.offDiag.card = T2.card * T2.card - T2.card := Finset.offDiag_card T2
    have hc2ub : T2.card ≤ 9 := le_trans (Finset.card_le_card hT2subT) (le_of_eq hTcard)
    rw [hIso] at hisoSplit hAB
    -- **Final arithmetic.**
    set c := T2.card with hcdef
    clear_value c
    interval_cases c <;> omega

end N20

end ACMax
