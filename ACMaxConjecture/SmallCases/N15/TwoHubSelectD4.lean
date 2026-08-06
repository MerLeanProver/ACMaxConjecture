import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N15.TwoHubSelectBudget

/-!
# `|Hub| = 7` corner with a unique iso-degree-`4` hub (`F.card = 1`)

This file supplies `two_hub_corner_select_fifteen_oneFour`, the `|Hub| = 7` branch of
`two_hub_corner_select_fifteen` when exactly one degree-`4` hub has iso-degree `4`.  Writing
`u = #{iso-deg ≥ 2}` and `m = #{iso-deg ≥ 3}`, the F=1 profiles are
`(4,3,3,3,3,2,0)` `(u,m)=(6,5)`, `(4,3,3,3,3,1,1)` `(5,5)`, `(4,3,3,3,2,2,1)` `(6,4)`,
`(4,3,3,2,2,2,2)` `(7,3)`.

* `u = 7` (`(4,3,3,2,2,2,2)`): handled by `two_hub_corner_b2_fifteen` — the medium-hub pigeonhole.
  Each of the four iso-degree-`2` hubs spends its share budget `4` across the other mediums and the
  three strong hubs; the forced shares on non-adjacent medium and strong-medium pairs over-spend
  the `≤ 6`-edge budget unless a non-adjacent medium pair shares `0`, a good pair.
* `(u,m) = (6,5)` (`(4,3,3,3,3,2,0)`): closed by `budget_card_bound` (`u(u−1)+m(m−1) = 50 > 48`).
* `(u,m) ∈ {(5,5), (6,4)}` (`(4,3,3,3,3,1,1)`, `(4,3,3,3,2,2,1)`): the genuine weak-hub residual,
  closed by the unique iso-degree-`4` hub `g`.  Its column is tight (`share(g,w) = iso(w) − 1` for
  every `w ≠ g`), so each of its four twins keeps exactly two neighbours in `W = {iso ≥ 2}`; the
  off-diagonal share sum over `W` is then `8 + d_x(d_x−1) + d_y(d_y−1)` for the two outside twins,
  while the forced strong-pair shares (`key`) need `≥ 5` adjacent `W`-pairs — but an iso-degree-`1`
  hub must keep a hub neighbour (`iso_one_hub_has_hub_neighbor`), eating two of the `≤ 6` ordered
  hub edges, leaving `≤ 4`.  Contradiction; no `K₂,₃` alignment needed.
-/

namespace ACMax

open scoped Classical

namespace N15

/-- **`|Hub| = 7`, `u = 7` medium-hub pigeonhole.**  Seven degree-`4` hubs all of iso-degree `≥ 2`,
exactly one of iso-degree `4`; the four iso-degree-`2` (medium) hubs `M2` and three strong hubs
`M3`.  Assuming no good pair, the forced shares `≥ 1` on non-adjacent medium and strong-medium
pairs over-spend the `≤ 6` ordered-edge budget, contradiction; hence a good pair exists. -/
theorem two_hub_corner_b2_fifteen (G : SimpleGraph (Fin 15)) (Hub Iso : Finset (Fin 15))
    (hHub7 : Hub.card = 7) (hIso6 : Iso.card = 6)
    (hdeg4 : ∀ h ∈ Hub, G.degree h = 4)
    (hHubsum : ∑ w ∈ Hub, (G.neighborFinset w ∩ Hub).card ≤ 6)
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hFone : (Hub.filter (fun h => (G.neighborFinset h ∩ Iso).card = 4)).card = 1)
    (hallge2 : ∀ h ∈ Hub, 2 ≤ (G.neighborFinset h ∩ Iso).card) :
    ∃ h₁ h₂ : Fin 15, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card := by
  classical
  by_contra hcon
  have key := nogood_of_not_select G Hub Iso hdeg4 hcon
  have hdle4 : ∀ a ∈ Hub, (G.neighborFinset a ∩ Iso).card ≤ 4 := by
    intro a ha
    have h1 : (G.neighborFinset a ∩ Iso).card ≤ G.degree a := by
      rw [← G.card_neighborFinset_eq_degree]
      exact Finset.card_le_card Finset.inter_subset_left
    rw [hdeg4 a ha] at h1; exact h1
  set M3 : Finset (Fin 15) := Hub.filter (fun h => 3 ≤ (G.neighborFinset h ∩ Iso).card) with hM3
  set M2 : Finset (Fin 15) := Hub.filter (fun h => ¬ 3 ≤ (G.neighborFinset h ∩ Iso).card) with hM2
  have hM3sub : M3 ⊆ Hub := by rw [hM3]; exact Finset.filter_subset _ _
  have hM2sub : M2 ⊆ Hub := by rw [hM2]; exact Finset.filter_subset _ _
  have hM2iso2 : ∀ m ∈ M2, (G.neighborFinset m ∩ Iso).card = 2 := by
    intro m hm
    have h2 := hallge2 m (hM2sub hm)
    rw [hM2, Finset.mem_filter] at hm
    omega
  have hM3iso : ∀ h ∈ M3, 3 ≤ (G.neighborFinset h ∩ Iso).card := by
    intro h hh; rw [hM3, Finset.mem_filter] at hh; exact hh.2
  have hdisjM : Disjoint M2 M3 := by
    rw [Finset.disjoint_left]
    intro a ha2 ha3
    rw [hM2, Finset.mem_filter] at ha2
    rw [hM3, Finset.mem_filter] at ha3
    exact ha2.2 ha3.2
  -- Cardinalities: `|M3| = 3`, `|M2| = 4`.
  have hunion : M3.card + M2.card = 7 := by
    rw [hM3, hM2, Finset.card_filter_add_card_filter_not, hHub7]
  have hsumsplit : ∑ a ∈ M3, (G.neighborFinset a ∩ Iso).card
      + ∑ a ∈ M2, (G.neighborFinset a ∩ Iso).card = 18 := by
    rw [hM3, hM2, Finset.sum_filter_add_sum_filter_not,
      hub_iso_degree_sum G Hub Iso hIso6 hiso3]
  have hM2sum : ∑ a ∈ M2, (G.neighborFinset a ∩ Iso).card = 2 * M2.card := by
    rw [Finset.sum_congr rfl hM2iso2, Finset.sum_const, smul_eq_mul, mul_comm]
  have hM3sum : ∑ a ∈ M3, (G.neighborFinset a ∩ Iso).card = 3 * M3.card + 1 := by
    have hdec : ∀ a ∈ M3, (G.neighborFinset a ∩ Iso).card
        = 3 + (if (G.neighborFinset a ∩ Iso).card = 4 then 1 else 0) := by
      intro a ha
      have h3 := hM3iso a ha
      have h4 := hdle4 a (hM3sub ha)
      split_ifs <;> omega
    rw [Finset.sum_congr rfl hdec, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul,
      mul_comm, Finset.sum_boole, Nat.cast_id]
    have hfeq : M3.filter (fun a => (G.neighborFinset a ∩ Iso).card = 4)
        = Hub.filter (fun h => (G.neighborFinset h ∩ Iso).card = 4) := by
      rw [hM3, Finset.filter_filter]
      apply Finset.filter_congr
      intro x hx
      have h4 := hdle4 x hx
      omega
    rw [hfeq, hFone]
  have hM3card : M3.card = 3 := by omega
  have hM2card : M2.card = 4 := by omega
  -- Per-medium share split: `∑_{M2.erase m} + ∑_{M3} = 4`.
  have hsplit : ∀ m ∈ M2, ∑ x ∈ M2.erase m,
        (G.neighborFinset m ∩ G.neighborFinset x ∩ Iso).card
      + ∑ h ∈ M3, (G.neighborFinset m ∩ G.neighborFinset h ∩ Iso).card = 4 := by
    intro m hm
    have hmHub : m ∈ Hub := hM2sub hm
    have hpv := per_vertex_share_sum_erase G Hub Iso hiso3 m hmHub
    rw [hM2iso2 m hm] at hpv
    have hmM3 : m ∉ M3 := by
      rw [hM3, Finset.mem_filter]
      rintro ⟨_, h3⟩
      rw [hM2, Finset.mem_filter] at hm
      exact hm.2 h3
    have hHubeq : Hub = M2 ∪ M3 := by
      rw [hM2, hM3, Finset.union_comm, Finset.filter_union_filter_not_eq]
    have hHubem : Hub.erase m = M2.erase m ∪ M3 := by
      rw [hHubeq, Finset.erase_union_distrib, Finset.erase_eq_of_notMem hmM3]
    have hdisj : Disjoint (M2.erase m) M3 :=
      Finset.disjoint_of_subset_left (Finset.erase_subset _ _) hdisjM
    rw [hHubem, Finset.sum_union hdisj] at hpv
    omega
  -- `S_M2M2 + S_M2H = 16`.
  have h16 : (∑ p ∈ M2.offDiag, (G.neighborFinset p.1 ∩ G.neighborFinset p.2 ∩ Iso).card)
      + (∑ m ∈ M2, ∑ h ∈ M3, (G.neighborFinset m ∩ G.neighborFinset h ∩ Iso).card) = 16 := by
    have hcong := Finset.sum_congr rfl hsplit
    rw [Finset.sum_add_distrib,
      ← sum_offDiag_erase M2 (fun a b => (G.neighborFinset a ∩ G.neighborFinset b ∩ Iso).card),
      Finset.sum_const, hM2card, smul_eq_mul] at hcong
    omega
  -- Lower bound `12 ≤ S_M2M2 + A_M2M2`.
  have hSMMge : 12 ≤ (∑ p ∈ M2.offDiag,
        (G.neighborFinset p.1 ∩ G.neighborFinset p.2 ∩ Iso).card)
      + (M2.offDiag.filter (fun p => G.Adj p.1 p.2)).card := by
    have hpt : ∀ p ∈ M2.offDiag, (if ¬G.Adj p.1 p.2 then 1 else 0)
        ≤ (G.neighborFinset p.1 ∩ G.neighborFinset p.2 ∩ Iso).card := by
      intro p hp
      rw [Finset.mem_offDiag] at hp
      by_cases hadj : G.Adj p.1 p.2
      · simp [hadj]
      · rw [if_pos hadj]
        have hk := key p.1 (hM2sub hp.1) p.2 (hM2sub hp.2.1) hp.2.2 hadj
        have h2a := hallge2 p.1 (hM2sub hp.1)
        have h2b := hallge2 p.2 (hM2sub hp.2.1)
        omega
    have h1 := Finset.sum_le_sum hpt
    rw [← Finset.card_filter] at h1
    have h2 := Finset.card_filter_add_card_filter_not (s := M2.offDiag) (fun p => G.Adj p.1 p.2)
    have h3 : M2.offDiag.card = 12 := by rw [Finset.offDiag_card, hM2card]
    omega
  -- Lower bound `12 ≤ S_M2H + A_M2H`.
  have hSMHge : 12 ≤ (∑ m ∈ M2, ∑ h ∈ M3,
        (G.neighborFinset m ∩ G.neighborFinset h ∩ Iso).card)
      + ((M2 ×ˢ M3).filter (fun p => G.Adj p.1 p.2)).card := by
    have hpt : ∀ p ∈ M2 ×ˢ M3, (if ¬G.Adj p.1 p.2 then 1 else 0)
        ≤ (G.neighborFinset p.1 ∩ G.neighborFinset p.2 ∩ Iso).card := by
      intro p hp
      rw [Finset.mem_product] at hp
      by_cases hadj : G.Adj p.1 p.2
      · simp [hadj]
      · rw [if_pos hadj]
        have hne : p.1 ≠ p.2 :=
          fun he => (Finset.disjoint_left.mp hdisjM hp.1) (he ▸ hp.2)
        have hk := key p.1 (hM2sub hp.1) p.2 (hM3sub hp.2) hne hadj
        have h2a := hallge2 p.1 (hM2sub hp.1)
        have h3b := hM3iso p.2 hp.2
        omega
    have h1 := Finset.sum_le_sum hpt
    rw [← Finset.card_filter] at h1
    have heq : (∑ p ∈ M2 ×ˢ M3, (G.neighborFinset p.1 ∩ G.neighborFinset p.2 ∩ Iso).card)
        = ∑ m ∈ M2, ∑ h ∈ M3, (G.neighborFinset m ∩ G.neighborFinset h ∩ Iso).card :=
      Finset.sum_product' M2 M3
        (fun a b => (G.neighborFinset a ∩ G.neighborFinset b ∩ Iso).card)
    rw [heq] at h1
    have h2 := Finset.card_filter_add_card_filter_not (s := M2 ×ˢ M3) (fun p => G.Adj p.1 p.2)
    have h3 : (M2 ×ˢ M3).card = 12 := by rw [Finset.card_product, hM2card, hM3card]
    omega
  -- The two adjacency counts are disjoint subsets of the `≤ 6` ordered hub edges.
  have hAle : (M2.offDiag.filter (fun p => G.Adj p.1 p.2)).card
      + ((M2 ×ˢ M3).filter (fun p => G.Adj p.1 p.2)).card ≤ 6 := by
    have hsub1 : M2.offDiag.filter (fun p => G.Adj p.1 p.2)
        ⊆ Hub.offDiag.filter (fun p => G.Adj p.1 p.2) := by
      apply Finset.filter_subset_filter
      intro p hp
      rw [Finset.mem_offDiag] at hp ⊢
      exact ⟨hM2sub hp.1, hM2sub hp.2.1, hp.2.2⟩
    have hsub2 : (M2 ×ˢ M3).filter (fun p => G.Adj p.1 p.2)
        ⊆ Hub.offDiag.filter (fun p => G.Adj p.1 p.2) := by
      intro p hp
      rw [Finset.mem_filter, Finset.mem_product] at hp
      rw [Finset.mem_filter, Finset.mem_offDiag]
      refine ⟨⟨hM2sub hp.1.1, hM3sub hp.1.2, ?_⟩, hp.2⟩
      exact fun he => (Finset.disjoint_left.mp hdisjM hp.1.1) (he ▸ hp.1.2)
    have hdisj : Disjoint (M2.offDiag.filter (fun p => G.Adj p.1 p.2))
        ((M2 ×ˢ M3).filter (fun p => G.Adj p.1 p.2)) := by
      rw [Finset.disjoint_left]
      intro p hp1 hp2
      rw [Finset.mem_filter, Finset.mem_offDiag] at hp1
      rw [Finset.mem_filter, Finset.mem_product] at hp2
      exact (Finset.disjoint_left.mp hdisjM hp1.1.2.1) hp2.1.2
    have hcardun := Finset.card_union_of_disjoint hdisj
    have hsubun : (M2.offDiag.filter (fun p => G.Adj p.1 p.2))
        ∪ ((M2 ×ˢ M3).filter (fun p => G.Adj p.1 p.2))
        ⊆ Hub.offDiag.filter (fun p => G.Adj p.1 p.2) := Finset.union_subset hsub1 hsub2
    have hle := Finset.card_le_card hsubun
    have hadj6 := hub_offDiag_adj_le G Hub 6 hHubsum
    omega
  omega

/-- **`|Hub| = 7` corner with a unique iso-degree-`4` hub.**  Seven degree-`4` hubs, exactly one of
iso-degree `4`; `u = #{iso-deg ≥ 2}`, `m = #{iso-deg ≥ 3}`.  The cases `u = 7`
(`two_hub_corner_b2_fifteen`) and `(u,m) = (6,5)` (`budget_card_bound`) reduce to budget; the
residual `(u,m) ∈ {(5,5),(6,4)}` weak-hub corner is closed via the unique iso-degree-`4` hub's
tight column plus the iso-degree-`1` hub-neighbour count (no `K₂,₃` alignment needed). -/
theorem two_hub_corner_select_fifteen_oneFour
    (G : SimpleGraph (Fin 15)) (Hub Iso : Finset (Fin 15))
    (hHub7 : Hub.card = 7) (hIso6 : Iso.card = 6)
    (hdeg4 : ∀ h ∈ Hub, G.degree h = 4)
    (hHubsum : ∑ w ∈ Hub, (G.neighborFinset w ∩ Hub).card ≤ 6)
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (_hshare : ∀ h₁ ∈ Hub, ∀ h₂ ∈ Hub, h₁ ≠ h₂ → ¬G.Adj h₁ h₂ →
      (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 2)
    (hdisj : Disjoint Hub Iso)
    (hFone : (Hub.filter (fun h => (G.neighborFinset h ∩ Iso).card = 4)).card = 1) :
    ∃ h₁ h₂ : Fin 15, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card := by
  classical
  set U : Finset (Fin 15) := Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card) with hU
  have hUsub : U ⊆ Hub := by rw [hU]; exact Finset.filter_subset _ _
  by_cases h7 : U.card = 7
  · -- `u = 7`: every hub is usable; delegate to the medium-hub pigeonhole.
    have hUeq : U = Hub := Finset.eq_of_subset_of_card_le hUsub (by rw [hHub7, h7])
    have hallge2 : ∀ h ∈ Hub, 2 ≤ (G.neighborFinset h ∩ Iso).card := by
      intro h hh
      rw [← hUeq, hU, Finset.mem_filter] at hh
      exact hh.2
    exact two_hub_corner_b2_fifteen G Hub Iso hHub7 hIso6 hdeg4 hHubsum hiso3 hFone hallge2
  · -- `u ≤ 6`: budget closes `(u,m) = (6,5)`; the rest is the residual.
    by_contra hcon
    have key := nogood_of_not_select G Hub Iso hdeg4 hcon
    have hbig := budget_card_bound G Hub Iso hHubsum hiso3 hIso6 key
    rw [← hU] at hbig
    have hdle4 : ∀ a ∈ Hub, (G.neighborFinset a ∩ Iso).card ≤ 4 := by
      intro a ha
      have h1 : (G.neighborFinset a ∩ Iso).card ≤ G.degree a := by
        rw [← G.card_neighborFinset_eq_degree]
        exact Finset.card_le_card Finset.inter_subset_left
      rw [hdeg4 a ha] at h1; exact h1
    set M3 : Finset (Fin 15) := Hub.filter (fun h => 3 ≤ (G.neighborFinset h ∩ Iso).card) with hM3
    have hM3U : M3 ⊆ U := by
      intro x hx
      rw [hM3, Finset.mem_filter] at hx
      rw [hU, Finset.mem_filter]
      exact ⟨hx.1, by omega⟩
    have hdecomp : ∀ a ∈ Hub, (G.neighborFinset a ∩ Iso).card
        = (if 1 ≤ (G.neighborFinset a ∩ Iso).card then 1 else 0)
          + (if 2 ≤ (G.neighborFinset a ∩ Iso).card then 1 else 0)
          + (if 3 ≤ (G.neighborFinset a ∩ Iso).card then 1 else 0)
          + (if 4 ≤ (G.neighborFinset a ∩ Iso).card then 1 else 0) := by
      intro a ha
      have h4 := hdle4 a ha
      split_ifs <;> omega
    set n1 : ℕ := (Hub.filter (fun h => 1 ≤ (G.neighborFinset h ∩ Iso).card)).card with hn1
    have hn4eq : (Hub.filter (fun h => 4 ≤ (G.neighborFinset h ∩ Iso).card)).card = 1 := by
      have hfeq : Hub.filter (fun h => 4 ≤ (G.neighborFinset h ∩ Iso).card)
          = Hub.filter (fun h => (G.neighborFinset h ∩ Iso).card = 4) := by
        apply Finset.filter_congr
        intro x hx
        have h4 := hdle4 x hx
        omega
      rw [hfeq, hFone]
    have hsumeq : n1 + U.card + M3.card + 1 = 18 := by
      have hcong : ∑ a ∈ Hub, (G.neighborFinset a ∩ Iso).card
          = ∑ a ∈ Hub, ((if 1 ≤ (G.neighborFinset a ∩ Iso).card then 1 else 0)
            + (if 2 ≤ (G.neighborFinset a ∩ Iso).card then 1 else 0)
            + (if 3 ≤ (G.neighborFinset a ∩ Iso).card then 1 else 0)
            + (if 4 ≤ (G.neighborFinset a ∩ Iso).card then 1 else 0)) :=
        Finset.sum_congr rfl hdecomp
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
        ← Finset.card_filter, ← Finset.card_filter, ← Finset.card_filter, ← Finset.card_filter,
        hub_iso_degree_sum G Hub Iso hIso6 hiso3, hn4eq] at hcong
      rw [hn1, hU, hM3]
      omega
    have hn1le : n1 ≤ 7 := by
      rw [hn1, ← hHub7]; exact Finset.card_le_card (Finset.filter_subset _ _)
    have hun1 : U.card ≤ n1 := by
      rw [hn1, hU]
      apply Finset.card_le_card
      intro x hx
      rw [Finset.mem_filter] at hx ⊢
      exact ⟨hx.1, by omega⟩
    have hu7 : U.card ≤ 7 := by rw [← hHub7]; exact Finset.card_le_card hUsub
    have hmu : M3.card ≤ U.card := Finset.card_le_card hM3U
    set u := U.card with hu_def
    set m := M3.card with hm_def
    have hcU : U.offDiag.card = u * u - u := by rw [Finset.offDiag_card, hu_def]
    have hcM : M3.offDiag.card = m * m - m := by rw [Finset.offDiag_card, hm_def]
    by_cases h65 : u = 6 ∧ m = 5
    · obtain ⟨h6, h5⟩ := h65
      rw [h6] at hcU
      rw [h5] at hcM
      omega
    · -- Residual weak-hub corner: `(u,m) ∈ {(5,5),(6,4)}`.
      -- Pin the profile: `n1 = 7` (all hubs meet a twin), `u ∈ {5,6}`.
      have hn17 : n1 = 7 := by omega
      have hum : (u = 5 ∧ m = 5) ∨ (u = 6 ∧ m = 4) := by omega
      have hallge1 : ∀ w ∈ Hub, 1 ≤ (G.neighborFinset w ∩ Iso).card := by
        intro w hw
        have hfull : Hub.filter (fun h => 1 ≤ (G.neighborFinset h ∩ Iso).card) = Hub :=
          Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by rw [hHub7, ← hn1, hn17])
        have hwmem : w ∈ Hub.filter (fun h => 1 ≤ (G.neighborFinset h ∩ Iso).card) := by
          rw [hfull]; exact hw
        exact (Finset.mem_filter.mp hwmem).2
      -- The unique iso-degree-`4` hub `g`.
      obtain ⟨g, hgsingle⟩ := Finset.card_eq_one.mp hFone
      have hgmem : g ∈ Hub.filter (fun h => (G.neighborFinset h ∩ Iso).card = 4) := by
        rw [hgsingle]; exact Finset.mem_singleton_self g
      have hgHub : g ∈ Hub := (Finset.mem_filter.mp hgmem).1
      have hgiso4 : (G.neighborFinset g ∩ Iso).card = 4 := (Finset.mem_filter.mp hgmem).2
      have hgdeg : G.degree g = 4 := hdeg4 g hgHub
      -- `g`'s neighbours are all isolated twins: `N g ⊆ Iso`.
      have hgsub : G.neighborFinset g ⊆ Iso := by
        have hdc : (G.neighborFinset g).card = 4 := by
          rw [G.card_neighborFinset_eq_degree, hgdeg]
        have heq : G.neighborFinset g ∩ Iso = G.neighborFinset g :=
          Finset.eq_of_subset_of_card_le Finset.inter_subset_left (le_of_eq (by rw [hdc, hgiso4]))
        rw [← heq]; exact Finset.inter_subset_right
      -- `g` has no hub neighbour, hence is non-adjacent to every hub.
      have hgnoHub : ∀ w ∈ Hub, ¬ G.Adj g w := by
        intro w hw hadj
        have hwN : w ∈ G.neighborFinset g := (G.mem_neighborFinset g w).mpr hadj
        exact Finset.disjoint_left.mp hdisj hw (hgsub hwN)
      -- Every hub other than `g` has iso-degree `≤ 3`.
      have hisow3 : ∀ w ∈ Hub, w ≠ g → (G.neighborFinset w ∩ Iso).card ≤ 3 := by
        intro w hw hwg
        by_contra hc
        have hw4 : (G.neighborFinset w ∩ Iso).card = 4 := by have := hdle4 w hw; omega
        have hwmem : w ∈ Hub.filter (fun h => (G.neighborFinset h ∩ Iso).card = 4) :=
          Finset.mem_filter.mpr ⟨hw, hw4⟩
        rw [hgsingle, Finset.mem_singleton] at hwmem
        exact hwg hwmem
      -- Column lower bound: `share(g,w) ≥ iso(w) − 1` for every `w ≠ g`.
      have hpt : ∀ w ∈ Hub.erase g, (G.neighborFinset w ∩ Iso).card - 1
          ≤ (G.neighborFinset g ∩ G.neighborFinset w ∩ Iso).card := by
        intro w hw
        have hwHub : w ∈ Hub := Finset.mem_of_mem_erase hw
        have hwg : w ≠ g := Finset.ne_of_mem_erase hw
        have h3 := hisow3 w hwHub hwg
        have hk := key g hgHub w hwHub (fun he => hwg he.symm) (hgnoHub w hwHub)
        rw [hgiso4, min_eq_right (by omega)] at hk
        omega
      -- Column total is `2·4 = 8`.
      have hcolsum := per_vertex_share_sum_erase G Hub Iso hiso3 g hgHub
      rw [hgiso4] at hcolsum
      -- `∑_{w≠g} iso(w) = 14`, hence `∑_{w≠g}(iso(w) − 1) = 8`.
      have hsum14 : ∑ w ∈ Hub.erase g, (G.neighborFinset w ∩ Iso).card = 14 := by
        have h18 := hub_iso_degree_sum G Hub Iso hIso6 hiso3
        have hae := Finset.add_sum_erase Hub
          (fun w => (G.neighborFinset w ∩ Iso).card) hgHub
        rw [hgiso4] at hae
        omega
      have hlowsum : ∑ w ∈ Hub.erase g, ((G.neighborFinset w ∩ Iso).card - 1) = 8 := by
        have hcongr : ∑ w ∈ Hub.erase g, ((G.neighborFinset w ∩ Iso).card - 1 + 1)
            = ∑ w ∈ Hub.erase g, (G.neighborFinset w ∩ Iso).card :=
          Finset.sum_congr rfl
            (fun w hw => by have := hallge1 w (Finset.mem_of_mem_erase hw); omega)
        rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one, hsum14,
          Finset.card_erase_of_mem hgHub, hHub7] at hcongr
        omega
      -- Hence equality throughout: `share(g,w) = iso(w) − 1` for every `w ≠ g`.
      have heqcol : ∀ w ∈ Hub.erase g, (G.neighborFinset w ∩ Iso).card - 1
          = (G.neighborFinset g ∩ G.neighborFinset w ∩ Iso).card := by
        have hsumeq2 : ∑ w ∈ Hub.erase g, ((G.neighborFinset w ∩ Iso).card - 1)
            = ∑ w ∈ Hub.erase g, (G.neighborFinset g ∩ G.neighborFinset w ∩ Iso).card := by
          rw [hlowsum, hcolsum]
        exact (Finset.sum_eq_sum_iff_of_le hpt).mp hsumeq2
      -- The strong/weak split of `Hub.erase g`: `W` (iso ≥ 2) and `L` (iso = 1).
      set W : Finset (Fin 15) := U.erase g with hWdef
      have hWsub : W ⊆ Hub := fun x hx => hUsub (Finset.mem_of_mem_erase hx)
      have hgU : g ∈ U := by
        rw [hU, Finset.mem_filter]; exact ⟨hgHub, by rw [hgiso4]; norm_num⟩
      have hWcard : W.card = u - 1 := by rw [hWdef, Finset.card_erase_of_mem hgU]
      have hWmem : ∀ w, w ∈ W ↔ (w ∈ Hub ∧ w ≠ g ∧ 2 ≤ (G.neighborFinset w ∩ Iso).card) := by
        intro w
        rw [hWdef, Finset.mem_erase, hU, Finset.mem_filter]; tauto
      set L : Finset (Fin 15) := (Hub.erase g) \ W with hLdef
      have hWsubE : W ⊆ Hub.erase g := by
        intro x hx
        obtain ⟨hxHub, hxg, _⟩ := (hWmem x).mp hx
        exact Finset.mem_erase.mpr ⟨hxg, hxHub⟩
      have hLiso1 : ∀ w ∈ L, (G.neighborFinset w ∩ Iso).card = 1 := by
        intro w hw
        rw [hLdef, Finset.mem_sdiff] at hw
        obtain ⟨hwE, hwW⟩ := hw
        have hwHub := Finset.mem_of_mem_erase hwE
        have hwg := Finset.ne_of_mem_erase hwE
        have hlt : ¬ 2 ≤ (G.neighborFinset w ∩ Iso).card :=
          fun hge => hwW ((hWmem w).mpr ⟨hwHub, hwg, hge⟩)
        have := hallge1 w hwHub; omega
      have hLcard : L.card = 7 - u := by
        have hca := Finset.card_sdiff_add_card_eq_card hWsubE
        rw [Finset.card_erase_of_mem hgHub, hHub7, hWcard, ← hLdef] at hca
        omega
      -- `∑_{w∈W} iso(w) = 7 + u`.
      have hSW : ∑ w ∈ W, (G.neighborFinset w ∩ Iso).card = 7 + u := by
        have hsd := Finset.sum_sdiff (f := fun w => (G.neighborFinset w ∩ Iso).card) hWsubE
        rw [← hLdef, hsum14] at hsd
        have hLsum : ∑ w ∈ L, (G.neighborFinset w ∩ Iso).card = L.card := by
          rw [Finset.sum_congr rfl (fun w hw => hLiso1 w hw), Finset.sum_const, smul_eq_mul,
            mul_one]
        rw [hLsum, hLcard] at hsd
        omega
      -- Each twin in `T_g = N g ∩ Iso` has exactly two `W`-neighbours.
      have htwin2 : ∀ t ∈ G.neighborFinset g ∩ Iso, (G.neighborFinset t ∩ W).card = 2 := by
        intro t ht
        obtain ⟨htg, htIso⟩ := Finset.mem_inter.mp ht
        have htgN : g ∈ G.neighborFinset t := by
          rw [G.mem_neighborFinset] at htg ⊢; exact htg.symm
        have hNtHub : (G.neighborFinset t ∩ Hub).card = 3 := hiso3 t htIso
        have hsplitN : G.neighborFinset t ∩ Hub
            = (G.neighborFinset t ∩ W) ∪ (G.neighborFinset t ∩ (Hub \ W)) := by
          rw [← Finset.inter_union_distrib_left, Finset.union_sdiff_of_subset hWsub]
        have hdisjWc : Disjoint (G.neighborFinset t ∩ W) (G.neighborFinset t ∩ (Hub \ W)) := by
          apply Finset.disjoint_left.mpr
          intro a ha1 ha2
          exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp ha2).2).2 (Finset.mem_inter.mp ha1).2
        have hrest : G.neighborFinset t ∩ (Hub \ W) = {g} := by
          apply Finset.eq_singleton_iff_unique_mem.mpr
          refine ⟨?_, ?_⟩
          · rw [Finset.mem_inter, Finset.mem_sdiff]
            exact ⟨htgN, hgHub, by rw [hWdef]; exact Finset.notMem_erase g U⟩
          · intro a ha
            rw [Finset.mem_inter, Finset.mem_sdiff] at ha
            obtain ⟨haNt, haHub, haW⟩ := ha
            by_contra hag
            have haE : a ∈ Hub.erase g := Finset.mem_erase.mpr ⟨hag, haHub⟩
            have haiso1 : (G.neighborFinset a ∩ Iso).card = 1 := by
              have hlt : ¬ 2 ≤ (G.neighborFinset a ∩ Iso).card :=
                fun hge => haW ((hWmem a).mpr ⟨haHub, hag, hge⟩)
              have := hallge1 a haHub; omega
            have hcol := heqcol a haE
            rw [haiso1] at hcol
            have htNa : t ∈ G.neighborFinset a := by
              rw [G.mem_neighborFinset] at haNt ⊢; exact haNt.symm
            have htmem : t ∈ G.neighborFinset g ∩ G.neighborFinset a ∩ Iso := by
              rw [Finset.mem_inter, Finset.mem_inter]; exact ⟨⟨htg, htNa⟩, htIso⟩
            exact (Finset.card_ne_zero_of_mem htmem) hcol.symm
        rw [hsplitN, Finset.card_union_of_disjoint hdisjWc, hrest, Finset.card_singleton] at hNtHub
        omega
      -- Strong hubs inside `W` are `M3.erase g`, of cardinality `m − 1`.
      have hgM3 : g ∈ M3 := by rw [hM3, Finset.mem_filter]; exact ⟨hgHub, by rw [hgiso4]; norm_num⟩
      have hMWeq : M3 ∩ W = M3.erase g := by
        ext a
        simp only [Finset.mem_inter, Finset.mem_erase, hWdef]
        constructor
        · rintro ⟨haM3, hag, _⟩; exact ⟨hag, haM3⟩
        · rintro ⟨hag, haM3⟩; exact ⟨haM3, hag, hM3U haM3⟩
      have hMWcard : (M3 ∩ W).card = m - 1 := by rw [hMWeq, Finset.card_erase_of_mem hgM3]
      -- The two twins outside `T_g`.
      have hdiff2 : (Iso \ (G.neighborFinset g ∩ Iso)).card = 2 := by
        have hca := Finset.card_sdiff_add_card_eq_card
          (Finset.inter_subset_right (s₁ := G.neighborFinset g) (s₂ := Iso))
        rw [hgiso4, hIso6] at hca; omega
      obtain ⟨x, y, hxy, hxyeq⟩ := Finset.card_eq_two.mp hdiff2
      have hxmem : x ∈ Iso \ (G.neighborFinset g ∩ Iso) := by
        rw [hxyeq]; exact Finset.mem_insert_self x {y}
      have hymem : y ∈ Iso \ (G.neighborFinset g ∩ Iso) := by
        rw [hxyeq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self y)
      have hxIso : x ∈ Iso := (Finset.mem_sdiff.mp hxmem).1
      have hyIso : y ∈ Iso := (Finset.mem_sdiff.mp hymem).1
      set dx : ℕ := (G.neighborFinset x ∩ W).card with hdxdef
      set dy : ℕ := (G.neighborFinset y ∩ W).card with hdydef
      have hdxle : dx ≤ 3 := by
        rw [hdxdef]
        have hsub : G.neighborFinset x ∩ W ⊆ G.neighborFinset x ∩ Hub :=
          fun a ha => Finset.mem_inter.mpr
            ⟨(Finset.mem_inter.mp ha).1, hWsub (Finset.mem_inter.mp ha).2⟩
        have hle := Finset.card_le_card hsub
        rw [hiso3 x hxIso] at hle; exact hle
      have hdyle : dy ≤ 3 := by
        rw [hdydef]
        have hsub : G.neighborFinset y ∩ W ⊆ G.neighborFinset y ∩ Hub :=
          fun a ha => Finset.mem_inter.mpr
            ⟨(Finset.mem_inter.mp ha).1, hWsub (Finset.mem_inter.mp ha).2⟩
        have hle := Finset.card_le_card hsub
        rw [hiso3 y hyIso] at hle; exact hle
      -- The ordered off-diagonal share sum over `W`.
      have hSsheq : ∑ p ∈ W.offDiag, (G.neighborFinset p.1 ∩ G.neighborFinset p.2 ∩ Iso).card
          = 8 + (dx * (dx - 1) + dy * (dy - 1)) := by
        rw [subset_offDiag_share_eq G W Iso]
        have hsd := Finset.sum_sdiff (f := fun t => (G.neighborFinset t ∩ W).card
          * ((G.neighborFinset t ∩ W).card - 1))
          (Finset.inter_subset_right (s₁ := G.neighborFinset g) (s₂ := Iso))
        have hTgsum : ∑ t ∈ G.neighborFinset g ∩ Iso, (G.neighborFinset t ∩ W).card
            * ((G.neighborFinset t ∩ W).card - 1) = 8 := by
          have hc : ∀ t ∈ G.neighborFinset g ∩ Iso, (G.neighborFinset t ∩ W).card
              * ((G.neighborFinset t ∩ W).card - 1) = 2 := fun t ht => by rw [htwin2 t ht]
          rw [Finset.sum_congr rfl hc, Finset.sum_const, hgiso4, smul_eq_mul]
        have hxysum : ∑ t ∈ Iso \ (G.neighborFinset g ∩ Iso), (G.neighborFinset t ∩ W).card
            * ((G.neighborFinset t ∩ W).card - 1) = dx * (dx - 1) + dy * (dy - 1) := by
          rw [hxyeq, Finset.sum_pair hxy, ← hdxdef, ← hdydef]
        rw [← hsd, hTgsum, hxysum]; ring
      -- `dx + dy = u − 1`.
      have hdsum : dx + dy = u - 1 := by
        have hcross := cross_count G Iso W
        rw [hSW] at hcross
        have hsd2 := Finset.sum_sdiff (f := fun t => (G.neighborFinset t ∩ W).card)
          (Finset.inter_subset_right (s₁ := G.neighborFinset g) (s₂ := Iso))
        have hTgd : ∑ t ∈ G.neighborFinset g ∩ Iso, (G.neighborFinset t ∩ W).card = 8 := by
          rw [Finset.sum_congr rfl htwin2, Finset.sum_const, hgiso4, smul_eq_mul]
        have hxyd : ∑ t ∈ Iso \ (G.neighborFinset g ∩ Iso), (G.neighborFinset t ∩ W).card
            = dx + dy := by rw [hxyeq, Finset.sum_pair hxy, ← hdxdef, ← hdydef]
        rw [hxyd, hTgd, hcross] at hsd2
        omega
      -- **Lower bound** on `∑(min − 1)`.
      have hfilt : W.offDiag.filter (fun p => p.1 ∈ M3 ∧ p.2 ∈ M3) = (M3 ∩ W).offDiag := by
        ext p
        simp only [Finset.mem_filter, Finset.mem_offDiag, Finset.mem_inter]
        constructor
        · rintro ⟨⟨hp1W, hp2W, hne⟩, hp1M, hp2M⟩
          exact ⟨⟨hp1M, hp1W⟩, ⟨hp2M, hp2W⟩, hne⟩
        · rintro ⟨⟨hp1M, hp1W⟩, ⟨hp2M, hp2W⟩, hne⟩
          exact ⟨⟨hp1W, hp2W, hne⟩, hp1M, hp2M⟩
      have hE2 : W.offDiag.card + (M3 ∩ W).offDiag.card
          ≤ ∑ p ∈ W.offDiag, (min (G.neighborFinset p.1 ∩ Iso).card
              (G.neighborFinset p.2 ∩ Iso).card - 1) := by
        have hlb : ∀ p ∈ W.offDiag, 1 + (if p.1 ∈ M3 ∧ p.2 ∈ M3 then 1 else 0)
            ≤ min (G.neighborFinset p.1 ∩ Iso).card (G.neighborFinset p.2 ∩ Iso).card - 1 := by
          intro p hp
          rw [Finset.mem_offDiag] at hp
          obtain ⟨hp1, hp2, _⟩ := hp
          obtain ⟨_, _, hp1ge⟩ := (hWmem p.1).mp hp1
          obtain ⟨_, _, hp2ge⟩ := (hWmem p.2).mp hp2
          by_cases hb : p.1 ∈ M3 ∧ p.2 ∈ M3
          · rw [if_pos hb]
            have h1 : 3 ≤ (G.neighborFinset p.1 ∩ Iso).card := by
              have hh := hb.1; rw [hM3, Finset.mem_filter] at hh; exact hh.2
            have h2 : 3 ≤ (G.neighborFinset p.2 ∩ Iso).card := by
              have hh := hb.2; rw [hM3, Finset.mem_filter] at hh; exact hh.2
            have := le_min h1 h2; omega
          · rw [if_neg hb]
            have := le_min hp1ge hp2ge; omega
        calc W.offDiag.card + (M3 ∩ W).offDiag.card
            = ∑ p ∈ W.offDiag, (1 + (if p.1 ∈ M3 ∧ p.2 ∈ M3 then 1 else 0)) := by
              rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one,
                ← Finset.card_filter, hfilt]
          _ ≤ _ := Finset.sum_le_sum hlb
      -- **Upper bound**: `∑(min − 1) ≤ ∑ share + 2·adjW`.
      have hE3 : ∑ p ∈ W.offDiag, (min (G.neighborFinset p.1 ∩ Iso).card
            (G.neighborFinset p.2 ∩ Iso).card - 1)
          ≤ (∑ p ∈ W.offDiag, (G.neighborFinset p.1 ∩ G.neighborFinset p.2 ∩ Iso).card)
            + 2 * (W.offDiag.filter (fun p => G.Adj p.1 p.2)).card := by
        have hub : ∀ p ∈ W.offDiag, min (G.neighborFinset p.1 ∩ Iso).card
            (G.neighborFinset p.2 ∩ Iso).card - 1
            ≤ (G.neighborFinset p.1 ∩ G.neighborFinset p.2 ∩ Iso).card
              + 2 * (if G.Adj p.1 p.2 then 1 else 0) := by
          intro p hp
          rw [Finset.mem_offDiag] at hp
          obtain ⟨hp1, hp2, hp12⟩ := hp
          obtain ⟨hp1Hub, hp1g, _⟩ := (hWmem p.1).mp hp1
          obtain ⟨hp2Hub, hp2g, _⟩ := (hWmem p.2).mp hp2
          by_cases hadj : G.Adj p.1 p.2
          · rw [if_pos hadj]
            have ha := hisow3 p.1 hp1Hub hp1g
            have hmin := min_le_left (G.neighborFinset p.1 ∩ Iso).card
              (G.neighborFinset p.2 ∩ Iso).card
            have := le_trans hmin ha; omega
          · rw [if_neg hadj]
            have hk := key p.1 hp1Hub p.2 hp2Hub hp12 hadj; omega
        calc ∑ p ∈ W.offDiag, (min (G.neighborFinset p.1 ∩ Iso).card
              (G.neighborFinset p.2 ∩ Iso).card - 1)
            ≤ ∑ p ∈ W.offDiag, ((G.neighborFinset p.1 ∩ G.neighborFinset p.2 ∩ Iso).card
                + 2 * (if G.Adj p.1 p.2 then 1 else 0)) := Finset.sum_le_sum hub
          _ = _ := by
              rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.card_filter]
      -- **adjacency budget**: at most `4` ordered adjacent `W`-pairs.
      have hadjWle4 : (W.offDiag.filter (fun p => G.Adj p.1 p.2)).card ≤ 4 := by
        obtain ⟨h0, hh0L⟩ := Finset.card_pos.mp (show 0 < L.card by rw [hLcard]; omega)
        rw [hLdef, Finset.mem_sdiff] at hh0L
        obtain ⟨hh0E, hh0W⟩ := hh0L
        have hh0Hub : h0 ∈ Hub := Finset.mem_of_mem_erase hh0E
        have hh0iso1 : (G.neighborFinset h0 ∩ Iso).card = 1 := by
          have hlt : ¬ 2 ≤ (G.neighborFinset h0 ∩ Iso).card :=
            fun hge => hh0W ((hWmem h0).mpr ⟨hh0Hub, Finset.ne_of_mem_erase hh0E, hge⟩)
          have := hallge1 h0 hh0Hub; omega
        have hh0nb := iso_one_hub_has_hub_neighbor G Hub Iso hHub7 hIso6 hdisj h0
          (hdeg4 h0 hh0Hub) hh0iso1
        obtain ⟨h', hh'⟩ := Finset.card_pos.mp (by omega : 0 < (G.neighborFinset h0 ∩ Hub).card)
        have hh'Hub : h' ∈ Hub := (Finset.mem_inter.mp hh').2
        have hadjh : G.Adj h0 h' := (G.mem_neighborFinset h0 h').mp (Finset.mem_inter.mp hh').1
        have hh0h' : h0 ≠ h' := G.ne_of_adj hadjh
        have hpairsub : ({(h0, h'), (h', h0)} : Finset (Fin 15 × Fin 15)) ⊆
            Hub.offDiag.filter (fun p => G.Adj p.1 p.2)
              \ W.offDiag.filter (fun p => G.Adj p.1 p.2) := by
          intro p hp
          simp only [Finset.mem_insert, Finset.mem_singleton] at hp
          rw [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_filter, Finset.mem_offDiag]
          rcases hp with rfl | rfl
          · refine ⟨⟨⟨hh0Hub, hh'Hub, hh0h'⟩, hadjh⟩, ?_⟩
            intro hcon2
            exact hh0W (Finset.mem_offDiag.mp hcon2.1).1
          · refine ⟨⟨⟨hh'Hub, hh0Hub, hh0h'.symm⟩, hadjh.symm⟩, ?_⟩
            intro hcon2
            exact hh0W (Finset.mem_offDiag.mp hcon2.1).2.1
        have hpaircard : ({(h0, h'), (h', h0)} : Finset (Fin 15 × Fin 15)).card = 2 := by
          rw [Finset.card_insert_of_notMem (by
            simp only [Finset.mem_singleton, Prod.mk.injEq, not_and]
            intro he; exact absurd he hh0h'), Finset.card_singleton]
        have hadjWsub : W.offDiag.filter (fun p => G.Adj p.1 p.2)
            ⊆ Hub.offDiag.filter (fun p => G.Adj p.1 p.2) := by
          apply Finset.filter_subset_filter
          intro p hp
          rw [Finset.mem_offDiag] at hp ⊢; exact ⟨hWsub hp.1, hWsub hp.2.1, hp.2.2⟩
        have h2le : 2 ≤ (Hub.offDiag.filter (fun p => G.Adj p.1 p.2)
            \ W.offDiag.filter (fun p => G.Adj p.1 p.2)).card := by
          rw [← hpaircard]; exact Finset.card_le_card hpairsub
        have hsdc := Finset.card_sdiff_add_card_eq_card hadjWsub
        have hadj6 := hub_offDiag_adj_le G Hub 6 hHubsum
        omega
      -- Numeric closure.
      clear_value dx dy
      have hWoff : W.offDiag.card = (u - 1) * (u - 1) - (u - 1) := by
        rw [Finset.offDiag_card, hWcard]
      have hMWoff : (M3 ∩ W).offDiag.card = (m - 1) * (m - 1) - (m - 1) := by
        rw [Finset.offDiag_card, hMWcard]
      -- Combine the bounds into a single inequality.
      have hcomb : W.offDiag.card + (M3 ∩ W).offDiag.card
          ≤ 16 + (dx * (dx - 1) + dy * (dy - 1)) := by
        rw [hSsheq] at hE3
        omega
      clear hE2 hE3 hSsheq hadjWle4
      rcases hum with ⟨hu5, hm5⟩ | ⟨hu6, hm4⟩
      · rw [hu5] at hWoff hdsum
        rw [hm5] at hMWoff
        interval_cases dx <;> interval_cases dy <;> omega
      · rw [hu6] at hWoff hdsum
        rw [hm4] at hMWoff
        interval_cases dx <;> interval_cases dy <;> omega

/-- **Hub-pair selection for the `n = 15` two-hub `e(M) = 1` (`s = 2`) residual.**  Given a hub set
of degree-`≤ 5` vertices with `e(Hub) ≤ 3` (`hHubsum`), every `M`-isolated twin meeting exactly
three hubs (`hiso3`), the twins `M`-independent (`hisoIndep`), the good-`K_{2,3}` share bound
(`hshare`), and one of the two `e(M) = 1` regimes (`hregime`: `|Hub| = 7`, `|Iso| = 6`, all degree
`4`; or `|Hub| = 6`, `|Iso| = 7`, `e(Hub) = 0`), there exist two non-adjacent degree-`4` hubs each
retaining `≥ 2` private isolated twins.

The clean extremal sub-case (at least two degree-`4` hubs of iso-degree `4`) is fully proved; the
`|Hub| = 7` corner is dispatched on `F.card` to `two_hub_corner_select_fifteen_noFour` (`F.card = 0`)
and `two_hub_corner_select_fifteen_oneFour` (`F.card = 1`), and the `|Hub| = 6` corner is proved
inline. -/
theorem two_hub_corner_select_fifteen (G : SimpleGraph (Fin 15)) (Hub Iso : Finset (Fin 15))
    (hdeg : ∀ h ∈ Hub, 4 ≤ G.degree h)
    (hdeg5 : ∀ h ∈ Hub, G.degree h ≤ 5)
    (hHubsum : ∑ w ∈ Hub, (G.neighborFinset w ∩ Hub).card ≤ 6)
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hisoIndep : ∀ a ∈ Iso, ∀ b ∈ Iso, ¬G.Adj a b)
    (hshare : ∀ h₁ ∈ Hub, ∀ h₂ ∈ Hub, h₁ ≠ h₂ → ¬G.Adj h₁ h₂ →
      (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 2)
    (hdisj : Disjoint Hub Iso)
    (hregime : (Hub.card = 7 ∧ Iso.card = 6 ∧ ∀ h ∈ Hub, G.degree h = 4) ∨
      (Hub.card = 6 ∧ Iso.card = 7 ∧
        (∑ w ∈ Hub, (G.neighborFinset w ∩ Hub).card = 0) ∧
        ∑ w ∈ Hub, G.degree w = 25)) :
    ∃ h₁ h₂ : Fin 15, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card := by
  classical
  set F : Finset (Fin 15) :=
    Hub.filter (fun h => G.degree h = 4 ∧ (G.neighborFinset h ∩ Iso).card = 4) with hFdef
  by_cases hk : 2 ≤ F.card
  · -- **Clean extremal case: two degree-`4` hubs of iso-degree `4`.**
    obtain ⟨h₁, hh1F, h₂, hh2F, hne⟩ := Finset.one_lt_card.mp hk
    obtain ⟨hh1, hd1, h1iso4⟩ := Finset.mem_filter.mp hh1F
    obtain ⟨hh2, hd2, h2iso4⟩ := Finset.mem_filter.mp hh2F
    -- Iso-degree `4` with degree `4` forces all neighbours into `Iso`.
    have hsub : ∀ h ∈ Hub, G.degree h = 4 → (G.neighborFinset h ∩ Iso).card = 4 →
        G.neighborFinset h ⊆ Iso := by
      intro h hh hdh hh4
      have hdc : (G.neighborFinset h).card = 4 := by
        rw [G.card_neighborFinset_eq_degree, hdh]
      have heq : G.neighborFinset h ∩ Iso = G.neighborFinset h :=
        Finset.eq_of_subset_of_card_le Finset.inter_subset_left (le_of_eq (by rw [hdc, hh4]))
      rw [← heq]; exact Finset.inter_subset_right
    have h1sub : G.neighborFinset h₁ ⊆ Iso := hsub h₁ hh1 hd1 h1iso4
    have h2sub : G.neighborFinset h₂ ⊆ Iso := hsub h₂ hh2 hd2 h2iso4
    have hnadj : ¬G.Adj h₁ h₂ := by
      intro hadj
      have h2in : h₂ ∈ Iso := h1sub ((G.mem_neighborFinset h₁ h₂).mpr hadj)
      have h1in : h₁ ∈ Iso := h2sub ((G.mem_neighborFinset h₂ h₁).mpr hadj.symm)
      exact hisoIndep h₁ h1in h₂ h2in hadj
    have hsh : (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 2 :=
      hshare h₁ hh1 h₂ hh2 hne hnadj
    have hsh' : (G.neighborFinset h₂ ∩ G.neighborFinset h₁ ∩ Iso).card ≤ 2 :=
      hshare h₂ hh2 h₁ hh1 (Ne.symm hne) (fun h => hnadj h.symm)
    have hfin := select_finish G Iso h₁ h₂ (by omega) (by omega)
    exact ⟨h₁, h₂, hh1, hh2, hd1, hd2, hne, hnadj, hfin.1, hfin.2⟩
  · -- **Residual corner: at most one degree-`4` hub of iso-degree `4`.**
    have hF1 : F.card ≤ 1 := by omega
    rcases hregime with ⟨hHub7, hIso6, hdeg4⟩ | ⟨hHub6, hIso7, hHub0, hdsum⟩
    · -- **`|Hub| = 7` corner.**  Dispatch on `F.card`: `0` (no iso-degree-`4` hub, budget leaf)
      -- or `1` (a unique iso-degree-`4` hub).
      rcases Nat.eq_zero_or_pos F.card with hF0 | hFpos
      · have hnoFour : ∀ h ∈ Hub, (G.neighborFinset h ∩ Iso).card ≠ 4 := by
          intro h hh hiso4
          rw [Finset.card_eq_zero] at hF0
          have hmem : h ∈ F := by
            rw [hFdef, Finset.mem_filter]; exact ⟨hh, hdeg4 h hh, hiso4⟩
          rw [hF0] at hmem; exact absurd hmem (Finset.notMem_empty h)
        exact two_hub_corner_select_fifteen_noFour G Hub Iso hHub7 hIso6 hdeg4 hHubsum hiso3
          hnoFour
      · have hF1' : F.card = 1 := by omega
        have hFeq : F = Hub.filter (fun h => (G.neighborFinset h ∩ Iso).card = 4) := by
          rw [hFdef]
          apply Finset.filter_congr
          intro x hx
          exact ⟨fun h => h.2, fun h => ⟨hdeg4 x hx, h⟩⟩
        have hFone : (Hub.filter (fun h => (G.neighborFinset h ∩ Iso).card = 4)).card = 1 := by
          rw [← hFeq]; exact hF1'
        exact two_hub_corner_select_fifteen_oneFour G Hub Iso hHub7 hIso6 hdeg4 hHubsum hiso3
          hshare hdisj hFone
    · -- **`|Hub| = 6` degree-`5`-exclusion corner: fully proved.**  Exactly one degree-`5` hub `g`;
      -- the five degree-`4` hubs `T` are all strong (iso-degree `≥ 3`, profile `(4,3,3,3,3)`), and
      -- `e(Hub) = 0` makes every pair non-adjacent.  The strong off-diagonal share sum is exactly
      -- `∑_{T.offDiag} = 2·16 − 10 = 22`, so `filter_le_one_card_ge` yields `≥ 9` low-share
      -- (hence non-adjacent) strong pairs, each keeping `≥ 3 − 1 = 2` private isolated twins.
      have hisosum : ∑ a ∈ Hub, (G.neighborFinset a ∩ Iso).card = 21 := by
        rw [cross_count G Hub Iso]
        calc ∑ t ∈ Iso, (G.neighborFinset t ∩ Hub).card
            = ∑ _t ∈ Iso, 3 := Finset.sum_congr rfl (fun t ht => hiso3 t ht)
          _ = 21 := by rw [Finset.sum_const, hIso7, smul_eq_mul]
      have hdeg45 : ∀ h ∈ Hub, G.degree h = 4 ∨ G.degree h = 5 := by
        intro h hh; have := hdeg h hh; have := hdeg5 h hh; omega
      -- Exactly one degree-`5` hub.
      set D5 : Finset (Fin 15) := Hub.filter (fun h => G.degree h = 5) with hD5def
      have hD5card : D5.card = 1 := by
        have hsplit : ∀ h ∈ Hub, G.degree h = 4 + (if G.degree h = 5 then 1 else 0) := by
          intro h hh; rcases hdeg45 h hh with h4 | h5
          · rw [h4]; simp
          · rw [h5]; simp
        have hss : ∑ h ∈ Hub, G.degree h
            = 4 * Hub.card + D5.card := by
          rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul,
            mul_comm, hD5def, Finset.sum_boole, Nat.cast_id]
        rw [hdsum, hHub6] at hss; omega
      obtain ⟨g, hgeq⟩ := Finset.card_eq_one.mp hD5card
      have hgD5 : g ∈ D5 := by rw [hgeq]; exact Finset.mem_singleton_self g
      have hgHub : g ∈ Hub := (Finset.mem_filter.mp hgD5).1
      have hgdeg5 : G.degree g = 5 := (Finset.mem_filter.mp hgD5).2
      -- The degree-`4` hubs are exactly `Hub.erase g`.
      set T : Finset (Fin 15) := Hub.erase g with hTdef
      have hTsub : T ⊆ Hub := Finset.erase_subset _ _
      have hTdeg4 : ∀ v ∈ T, G.degree v = 4 := by
        intro v hv
        have hvHub : v ∈ Hub := hTsub hv
        have hvne : v ≠ g := Finset.ne_of_mem_erase hv
        rcases hdeg45 v hvHub with h4 | h5
        · exact h4
        · exfalso
          have hvD5 : v ∈ D5 := Finset.mem_filter.mpr ⟨hvHub, h5⟩
          rw [hgeq, Finset.mem_singleton] at hvD5
          exact hvne hvD5
      have hT5 : T.card = 5 := by rw [hTdef, Finset.card_erase_of_mem hgHub, hHub6]
      -- `iso-deg g ≤ 5` and `∑_T iso-deg = 21 − iso-deg g ≥ 16`.
      have hgiso_le : (G.neighborFinset g ∩ Iso).card ≤ 5 := by
        have h := Finset.card_le_card (Finset.inter_subset_left
          (s₁ := G.neighborFinset g) (s₂ := Iso))
        rwa [G.card_neighborFinset_eq_degree, hgdeg5] at h
      have hTsumsplit : (G.neighborFinset g ∩ Iso).card
          + ∑ v ∈ T, (G.neighborFinset v ∩ Iso).card = 21 := by
        rw [hTdef, Finset.add_sum_erase Hub (fun v => (G.neighborFinset v ∩ Iso).card) hgHub]
        exact hisosum
      have hTsumge : 16 ≤ ∑ v ∈ T, (G.neighborFinset v ∩ Iso).card := by omega
      -- All degree-`4` hubs are strong (iso-degree `≥ 3`).
      have hTstrong : ∀ v ∈ T, 3 ≤ (G.neighborFinset v ∩ Iso).card := by
        intro v hv
        by_contra hlt
        push Not at hlt
        have hv2 : (G.neighborFinset v ∩ Iso).card ≤ 2 := by omega
        -- Upper-bound the rest of `T` by `3 + [iso-deg = 4]`.
        have hbnd : ∀ x ∈ T.erase v, (G.neighborFinset x ∩ Iso).card
            ≤ 3 + (if (G.neighborFinset x ∩ Iso).card = 4 then 1 else 0) := by
          intro x hx
          have hxHub : x ∈ Hub := hTsub (Finset.mem_of_mem_erase hx)
          have hxdeg4 : G.degree x = 4 := hTdeg4 x (Finset.mem_of_mem_erase hx)
          have hxle : (G.neighborFinset x ∩ Iso).card ≤ 4 := by
            have h := Finset.card_le_card (Finset.inter_subset_left
              (s₁ := G.neighborFinset x) (s₂ := Iso))
            rwa [G.card_neighborFinset_eq_degree, hxdeg4] at h
          by_cases hc : (G.neighborFinset x ∩ Iso).card = 4
          · simp [hc]
          · rw [if_neg hc]; omega
        have hFle : (((T.erase v).filter
            (fun x => (G.neighborFinset x ∩ Iso).card = 4)).card) ≤ 1 := by
          refine le_trans (Finset.card_le_card ?_) hF1
          intro x hx
          rw [Finset.mem_filter] at hx ⊢
          obtain ⟨hxTe, hx4⟩ := hx
          exact ⟨hTsub (Finset.mem_of_mem_erase hxTe),
            hTdeg4 x (Finset.mem_of_mem_erase hxTe), hx4⟩
        have herasele : ∑ x ∈ T.erase v, (G.neighborFinset x ∩ Iso).card ≤ 13 := by
          calc ∑ x ∈ T.erase v, (G.neighborFinset x ∩ Iso).card
              ≤ ∑ x ∈ T.erase v,
                (3 + if (G.neighborFinset x ∩ Iso).card = 4 then 1 else 0) :=
                Finset.sum_le_sum hbnd
            _ = 3 * (T.erase v).card
                + ((T.erase v).filter (fun x => (G.neighborFinset x ∩ Iso).card = 4)).card := by
                rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_comm,
                  Finset.sum_boole, Nat.cast_id]
            _ ≤ 13 := by
                rw [Finset.card_erase_of_mem hv, hT5]; omega
        have hsplitv := Finset.add_sum_erase T
          (fun x => (G.neighborFinset x ∩ Iso).card) hv
        omega
      -- Exact strong sum `∑_T iso-deg = 16` and `iso-deg g = 5`.
      have hTsumle : ∑ v ∈ T, (G.neighborFinset v ∩ Iso).card ≤ 16 := by
        have hbnd : ∀ v ∈ T, (G.neighborFinset v ∩ Iso).card
            ≤ 3 + (if (G.neighborFinset v ∩ Iso).card = 4 then 1 else 0) := by
          intro v hv
          have hvdeg4 : G.degree v = 4 := hTdeg4 v hv
          have hvle : (G.neighborFinset v ∩ Iso).card ≤ 4 := by
            have h := Finset.card_le_card (Finset.inter_subset_left
              (s₁ := G.neighborFinset v) (s₂ := Iso))
            rwa [G.card_neighborFinset_eq_degree, hvdeg4] at h
          by_cases hc : (G.neighborFinset v ∩ Iso).card = 4
          · simp [hc]
          · rw [if_neg hc]; omega
        have hFle : ((T.filter (fun v => (G.neighborFinset v ∩ Iso).card = 4)).card) ≤ 1 := by
          refine le_trans (Finset.card_le_card ?_) hF1
          intro x hx
          rw [Finset.mem_filter] at hx ⊢
          exact ⟨hTsub hx.1, hTdeg4 x hx.1, hx.2⟩
        calc ∑ v ∈ T, (G.neighborFinset v ∩ Iso).card
            ≤ ∑ v ∈ T, (3 + if (G.neighborFinset v ∩ Iso).card = 4 then 1 else 0) :=
              Finset.sum_le_sum hbnd
          _ = 3 * T.card
              + (T.filter (fun v => (G.neighborFinset v ∩ Iso).card = 4)).card := by
              rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_comm,
                Finset.sum_boole, Nat.cast_id]
          _ ≤ 16 := by rw [hT5]; omega
      have hTsum16 : ∑ v ∈ T, (G.neighborFinset v ∩ Iso).card = 16 := by omega
      have hgiso5 : (G.neighborFinset g ∩ Iso).card = 5 := by omega
      -- Column of `g`: `∑_{v∈T} share(v, g) = 2·iso-deg g = 10`.
      have hgcol : ∑ v ∈ T, (G.neighborFinset v ∩ G.neighborFinset g ∩ Iso).card = 10 := by
        have h := per_vertex_share_sum_erase G Hub Iso hiso3 g hgHub
        rw [hgiso5] at h
        rw [hTdef]
        rw [Finset.sum_congr rfl (fun v _ => by
          rw [show G.neighborFinset v ∩ G.neighborFinset g
            = G.neighborFinset g ∩ G.neighborFinset v from Finset.inter_comm _ _])]
        omega
      -- Strong off-diagonal share sum `= 22`.
      have hToff : ∑ p ∈ T.offDiag,
          (G.neighborFinset p.1 ∩ G.neighborFinset p.2 ∩ Iso).card = 22 := by
        have hinner : ∀ v ∈ T, ∑ x ∈ T.erase v,
            (G.neighborFinset v ∩ G.neighborFinset x ∩ Iso).card
            + (G.neighborFinset v ∩ G.neighborFinset g ∩ Iso).card
            = 2 * (G.neighborFinset v ∩ Iso).card := by
          intro v hv
          have hvHub := hTsub hv
          have hfull := per_vertex_share_sum_erase G Hub Iso hiso3 v hvHub
          have hvne : v ≠ g := Finset.ne_of_mem_erase hv
          have hev : Hub.erase v = insert g (T.erase v) := by
            rw [hTdef]
            ext x
            simp only [Finset.mem_insert, Finset.mem_erase]
            constructor
            · rintro ⟨hxv, hxHub⟩
              by_cases hxg : x = g
              · exact Or.inl hxg
              · exact Or.inr ⟨hxv, hxg, hxHub⟩
            · rintro (hxg | ⟨hxv, _, hxHub⟩)
              · subst hxg; exact ⟨Ne.symm hvne, hgHub⟩
              · exact ⟨hxv, hxHub⟩
          rw [hev, Finset.sum_insert (by
            intro hmem
            have hgT : g ∈ T := (Finset.mem_erase.mp hmem).2
            rw [hTdef] at hgT
            exact (Finset.mem_erase.mp hgT).1 rfl)] at hfull
          omega
        have hsum2 := Finset.sum_congr rfl hinner
        rw [Finset.sum_add_distrib] at hsum2
        have hTdd : ∑ v ∈ T, 2 * (G.neighborFinset v ∩ Iso).card = 32 := by
          rw [← Finset.mul_sum]; omega
        rw [sum_offDiag_erase T
          (fun a b => (G.neighborFinset a ∩ G.neighborFinset b ∩ Iso).card)]
        omega
      have hToffcard : T.offDiag.card = 20 := by rw [Finset.offDiag_card, hT5]
      have hcount := filter_le_one_card_ge T.offDiag
        (fun p => (G.neighborFinset p.1 ∩ G.neighborFinset p.2 ∩ Iso).card) 22 (le_of_eq hToff)
      -- `e(Hub) = 0` makes every off-diagonal pair non-adjacent.
      have hadj0 : (T.offDiag.filter (fun p => G.Adj p.1 p.2)).card ≤ 0 := by
        have hoffsub : T.offDiag ⊆ Hub.offDiag := by
          intro p hp
          rw [Finset.mem_offDiag] at hp ⊢
          exact ⟨hTsub hp.1, hTsub hp.2.1, hp.2.2⟩
        exact le_trans (Finset.card_le_card (Finset.filter_subset_filter _ hoffsub))
          (hub_offDiag_adj_le G Hub 0 (le_of_eq hHub0))
      have hne : ((T.offDiag.filter
          (fun p => (G.neighborFinset p.1 ∩ G.neighborFinset p.2 ∩ Iso).card ≤ 1)) \
          (T.offDiag.filter (fun p => G.Adj p.1 p.2))).Nonempty := by
        rw [← Finset.card_pos]
        have hge := Finset.le_card_sdiff
          (T.offDiag.filter (fun p => G.Adj p.1 p.2))
          (T.offDiag.filter
            (fun p => (G.neighborFinset p.1 ∩ G.neighborFinset p.2 ∩ Iso).card ≤ 1))
        omega
      obtain ⟨p, hp⟩ := hne
      rw [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_filter] at hp
      obtain ⟨⟨hpoff, hpsh⟩, hpadj⟩ := hp
      obtain ⟨hp1T, hp2T, hp12⟩ := Finset.mem_offDiag.mp hpoff
      have hp1Hub : p.1 ∈ Hub := hTsub hp1T
      have hp2Hub : p.2 ∈ Hub := hTsub hp2T
      have hnadj : ¬G.Adj p.1 p.2 := fun h => hpadj ⟨hpoff, h⟩
      have ha3 : 3 ≤ (G.neighborFinset p.1 ∩ Iso).card := hTstrong p.1 hp1T
      have hb3 : 3 ≤ (G.neighborFinset p.2 ∩ Iso).card := hTstrong p.2 hp2T
      have hsh2 : (G.neighborFinset p.2 ∩ G.neighborFinset p.1 ∩ Iso).card ≤ 1 := by
        rw [Finset.inter_comm (G.neighborFinset p.2) (G.neighborFinset p.1)]; exact hpsh
      have hfin := select_finish G Iso p.1 p.2 (by omega) (by omega)
      exact ⟨p.1, p.2, hp1Hub, hp2Hub, hTdeg4 p.1 hp1T, hTdeg4 p.2 hp2T, hp12, hnadj,
        hfin.1, hfin.2⟩

end N15

end ACMax
