import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N18.Core

/-!
# Hub-pair selection for the `n = 18` two-hub `e(M) ≤ 1` residual

This file is the `n = 18` port of `TwinCert17TwoHubSelect`.  It supplies the **shared selection
engine** (`select_finish_eighteen`, `hub_iso_sum_eighteen`, `nogood_of_not_select_eighteen`,
`hub_neighbor_le_eighteen`, `strong_deg4_count_le_two_deg5_eighteen`, `deg4_sum_le_eighteen`,
`residual_arith_eighteen`), the tight-profile router `two_hub_select_eM1_tight_eighteen`, and the
entry point `two_hub_corner_select_eighteen`.

At `e(M) ≤ 1` the handshake `e(M) = 22 − 3·|Hub| + e(Hub)` (total `e(G) = 32`) together with the
degree relation `∑_{Hub} deg = 3·|Hub| + 10` (equivalently `#{deg-5 hubs} = 10 − |Hub|`) yields the
regimes `|Hub| ∈ {7, 8, 9, 10}`, `|Iso|` correspondingly (`|Iso| = 18 − |Hub|` for `e(M) = 0`,
`|Iso| = 16 − |Hub|` for `e(M) = 1`):

* `e(M) = 0`: `(|Hub|, |Iso|, ∑deg) ∈ {(8,10,34), (9,9,37), (10,8,40)}`;
* `e(M) = 1`: `(|Hub|, |Iso|, ∑deg) ∈ {(7,9,31), (8,8,34), (9,7,37), (10,6,40)}`.

The **key simplification** (as for `n = 16`/`n = 17`) is the sharp share bound
`nonadj_hubs_share_le_one_iso` (non-adjacent degree-`4` hubs share at most **one** `M`-isolated
twin).  With share `≤ 1`, the strong degree-`4` hubs (iso-degree `≥ 3`) form a clique, each with
`≤ 1` hub-neighbour, so they number `≤ 2`.  Erasing the `10 − |Hub|` degree-`5` hubs, the
degree-`4` iso-degree total clashes with the threshold bound `∑_{deg-4} isoDeg ≤ 2·|deg-4| + 2`,
giving the residual master inequality `3·|Iso| + 10·|Hub| ≤ 3·∑deg + 2`.

The `n = 18` degree-excess is `64 − 54 = 10 ≡ 1 (mod 3)` (vs `n = 17`'s `9 ≡ 0`).  Checking the
master inequality against each regime, the four profiles `(8,10,34)`, `(9,9,37)`, `(10,8,40)`,
`(7,9,31)` are refuted outright (`3·|Iso| + 10·|Hub| > 3·∑deg + 2`).  The three `e(M) = 1` profiles
`(8,8,34)` (tight, `104 = 104`), `(9,7,37)` (slack `2`) and `(10,6,40)` (slack `4`) survive the bare
counting — the `mod-3` slack did **not** close them (it is wider than `n = 17`'s).  They are routed
through `two_hub_select_eM1_tight_eighteen`; the all-degree-`4` `(10,6,40)` profile is the analog of
`n = 17`'s `(9,6,36)` and (with `(9,7,37)`) needs the separate structural low-vertex/triangle
development of `TwinCert17TwoHubTight96`, isolated here as a single documented `sorry`. -/

namespace ACMax

open scoped Classical

namespace N18

/-- **Finish the selection.**  From a non-adjacent degree-`4` pair `h₁, h₂ ∈ Hub` whose iso-degree
exceeds their share by `≥ 2` on each side, extract the two private-twin bounds. -/
theorem select_finish_eighteen (G : SimpleGraph (Fin 18)) (Iso : Finset (Fin 18)) (h₁ h₂ : Fin 18)
    (hsh1 : (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card + 2
      ≤ (G.neighborFinset h₁ ∩ Iso).card)
    (hsh2 : (G.neighborFinset h₂ ∩ G.neighborFinset h₁ ∩ Iso).card + 2
      ≤ (G.neighborFinset h₂ ∩ Iso).card) :
    2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
    2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card := by
  classical
  refine ⟨?_, ?_⟩
  · have hkey := Finset.card_sdiff_add_card_inter (G.neighborFinset h₁ ∩ Iso)
      (G.neighborFinset h₂)
    have hinter : (G.neighborFinset h₁ ∩ Iso) ∩ G.neighborFinset h₂
        = G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso := Finset.inter_right_comm _ _ _
    rw [hinter] at hkey; omega
  · have hkey := Finset.card_sdiff_add_card_inter (G.neighborFinset h₂ ∩ Iso)
      (G.neighborFinset h₁)
    have hinter : (G.neighborFinset h₂ ∩ Iso) ∩ G.neighborFinset h₁
        = G.neighborFinset h₂ ∩ G.neighborFinset h₁ ∩ Iso := Finset.inter_right_comm _ _ _
    rw [hinter] at hkey; omega

/-- **Total iso-degree is `3·|Iso|`.**  Each `M`-isolated twin meets exactly three hubs. -/
theorem hub_iso_sum_eighteen (G : SimpleGraph (Fin 18)) (Hub Iso : Finset (Fin 18))
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3) :
    ∑ a ∈ Hub, (G.neighborFinset a ∩ Iso).card = 3 * Iso.card := by
  rw [cross_count G Hub Iso]
  calc ∑ t ∈ Iso, (G.neighborFinset t ∩ Hub).card
      = ∑ _t ∈ Iso, 3 := Finset.sum_congr rfl (fun t ht => hiso3 t ht)
    _ = 3 * Iso.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

/-- **No good pair from a refuted selection.**  Packages `select_finish_eighteen` into the
`min(iso-deg) ≤ share + 1` form on non-adjacent degree-`4` hub pairs, given a refutation `hcon` of
the selection goal. -/
theorem nogood_of_not_select_eighteen (G : SimpleGraph (Fin 18)) (Hub Iso : Finset (Fin 18))
    (hcon : ¬ ∃ h₁ h₂ : Fin 18, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card) :
    ∀ a ∈ Hub, ∀ b ∈ Hub, G.degree a = 4 → G.degree b = 4 → a ≠ b → ¬G.Adj a b →
      min ((G.neighborFinset a ∩ Iso).card) ((G.neighborFinset b ∩ Iso).card)
        ≤ (G.neighborFinset a ∩ G.neighborFinset b ∩ Iso).card + 1 := by
  intro a ha b hb hda hdb hne hnadj
  by_contra hlt
  push Not at hlt
  have hsa : (G.neighborFinset a ∩ G.neighborFinset b ∩ Iso).card + 2
      ≤ (G.neighborFinset a ∩ Iso).card := by omega
  have hcomm : (G.neighborFinset b ∩ G.neighborFinset a ∩ Iso).card
      = (G.neighborFinset a ∩ G.neighborFinset b ∩ Iso).card := by
    rw [Finset.inter_comm (G.neighborFinset b) (G.neighborFinset a)]
  have hsb : (G.neighborFinset b ∩ G.neighborFinset a ∩ Iso).card + 2
      ≤ (G.neighborFinset b ∩ Iso).card := by rw [hcomm]; omega
  have hfin := select_finish_eighteen G Iso a b hsa hsb
  exact hcon ⟨a, b, ha, hb, hda, hdb, hne, hnadj, hfin.1, hfin.2⟩

/-- **A degree-`4` hub's hub-neighbour count is bounded by `4 −` its iso-degree.**  The neighbours
in `Hub` and in `Iso` are disjoint (`hdisj`) subsets of the degree-`4` neighbourhood. -/
theorem hub_neighbor_le_eighteen (G : SimpleGraph (Fin 18)) (Hub Iso : Finset (Fin 18))
    (hdisj : Disjoint Hub Iso) (a : Fin 18) (hda : G.degree a = 4) :
    (G.neighborFinset a ∩ Hub).card + (G.neighborFinset a ∩ Iso).card ≤ 4 := by
  classical
  have hdc : (G.neighborFinset a).card = 4 := by rw [G.card_neighborFinset_eq_degree, hda]
  have hdisj' : Disjoint (G.neighborFinset a ∩ Hub) (G.neighborFinset a ∩ Iso) := by
    apply Finset.disjoint_left.mpr
    intro x hx1 hx2
    exact Finset.disjoint_left.mp hdisj (Finset.mem_inter.mp hx1).2 (Finset.mem_inter.mp hx2).2
  have hun : (G.neighborFinset a ∩ Hub) ∪ (G.neighborFinset a ∩ Iso) ⊆ G.neighborFinset a := by
    rw [← Finset.inter_union_distrib_left]; exact Finset.inter_subset_left
  have hle := Finset.card_le_card hun
  rw [Finset.card_union_of_disjoint hdisj', hdc] at hle
  exact hle

/-- **The strong degree-`4` hubs number `≤ 2` (degree-`4`-restricted share).**  Under the refuted
selection (`key`) and the share-`≤ 1` bound restricted to degree-`4` hub pairs (`hshare`), the set
`A` of degree-`4` hubs of iso-degree `≥ 3` is a clique; each member has `≤ 4 − 3 = 1`
hub-neighbours, so `|A| ≤ 2`, and an iso-degree-`4` member forces `|A| ≤ 1`.  Hence `|A| + |B| ≤ 2`
where `B` are the iso-degree-`4` degree-`4` hubs.  The restricted share lets a degree-`5` hub sit in
`Hub`. -/
theorem strong_deg4_count_le_two_deg5_eighteen (G : SimpleGraph (Fin 18))
    (Hub Iso : Finset (Fin 18)) (hdisj : Disjoint Hub Iso)
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (key : ∀ a ∈ Hub, ∀ b ∈ Hub, G.degree a = 4 → G.degree b = 4 → a ≠ b → ¬G.Adj a b →
      min ((G.neighborFinset a ∩ Iso).card) ((G.neighborFinset b ∩ Iso).card)
        ≤ (G.neighborFinset a ∩ G.neighborFinset b ∩ Iso).card + 1) :
    (Hub.filter (fun h => G.degree h = 4 ∧ 3 ≤ (G.neighborFinset h ∩ Iso).card)).card
      + (Hub.filter (fun h => G.degree h = 4 ∧ 4 ≤ (G.neighborFinset h ∩ Iso).card)).card ≤ 2 := by
  classical
  set A : Finset (Fin 18) :=
    Hub.filter (fun h => G.degree h = 4 ∧ 3 ≤ (G.neighborFinset h ∩ Iso).card) with hA
  set B : Finset (Fin 18) :=
    Hub.filter (fun h => G.degree h = 4 ∧ 4 ≤ (G.neighborFinset h ∩ Iso).card) with hB
  have hAprop : ∀ a ∈ A, a ∈ Hub ∧ G.degree a = 4 ∧ 3 ≤ (G.neighborFinset a ∩ Iso).card := by
    intro a ha; rw [hA, Finset.mem_filter] at ha; exact ⟨ha.1, ha.2.1, ha.2.2⟩
  have hBA : B ⊆ A := by
    intro x hx; rw [hB, Finset.mem_filter] at hx; rw [hA, Finset.mem_filter]
    exact ⟨hx.1, hx.2.1, by omega⟩
  have hclique : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → G.Adj a b := by
    intro a ha b hb hab
    by_contra hnadj
    obtain ⟨haHub, hda, ha3⟩ := hAprop a ha
    obtain ⟨hbHub, hdb, hb3⟩ := hAprop b hb
    have hk := key a haHub b hbHub hda hdb hab hnadj
    have hs := hshare a haHub hda b hbHub hdb hab hnadj
    have : 3 ≤ min ((G.neighborFinset a ∩ Iso).card) ((G.neighborFinset b ∩ Iso).card) :=
      le_min ha3 hb3
    omega
  have hkey : ∀ a ∈ A, A.card - 1 + (G.neighborFinset a ∩ Iso).card ≤ 4 := by
    intro a ha
    obtain ⟨haHub, hda, _⟩ := hAprop a ha
    have hsub : A.erase a ⊆ G.neighborFinset a ∩ Hub := by
      intro b hb
      have hbA : b ∈ A := Finset.mem_of_mem_erase hb
      have hba : b ≠ a := Finset.ne_of_mem_erase hb
      have hbHub := (hAprop b hbA).1
      rw [Finset.mem_inter, G.mem_neighborFinset]
      exact ⟨(hclique a ha b hbA (Ne.symm hba)), hbHub⟩
    have hc1 : A.card - 1 ≤ (G.neighborFinset a ∩ Hub).card := by
      rw [← Finset.card_erase_of_mem ha]; exact Finset.card_le_card hsub
    have hc2 := hub_neighbor_le_eighteen G Hub Iso hdisj a hda
    omega
  rcases Finset.eq_empty_or_nonempty B with hBe | hBne
  · have hBcard : B.card = 0 := by rw [hBe]; rfl
    rcases Finset.eq_empty_or_nonempty A with hAe | ⟨a, ha⟩
    · rw [hAe]; simp [hBcard]
    · obtain ⟨_, _, ha3⟩ := hAprop a ha
      have := hkey a ha
      have hApos : 1 ≤ A.card := Finset.card_pos.mpr ⟨a, ha⟩
      omega
  · obtain ⟨a, haB⟩ := hBne
    have haA : a ∈ A := hBA haB
    have ha4 : 4 ≤ (G.neighborFinset a ∩ Iso).card := by
      rw [hB, Finset.mem_filter] at haB; exact haB.2.2
    have := hkey a haA
    have hBleA : B.card ≤ A.card := Finset.card_le_card hBA
    have hApos : 1 ≤ A.card := Finset.card_pos.mpr ⟨a, haA⟩
    omega

/-- **Degree-`4` iso-degree threshold sum bound.**  For the degree-`4` hubs `T = {deg = 4}`
(each of iso-degree `≤ 4`), the threshold decomposition gives
`∑_{T} isoDeg = c₁ + c₂ + c₃ + c₄` with `c₁, c₂ ≤ |T|` and `c₃ + c₄ ≤ 2` by the strong-hub bound
(`hmf`), hence `∑_{T} isoDeg ≤ 2·|T| + 2`. -/
theorem deg4_sum_le_eighteen (G : SimpleGraph (Fin 18)) (Hub Iso : Finset (Fin 18))
    (hmf : (Hub.filter (fun h => G.degree h = 4 ∧ 3 ≤ (G.neighborFinset h ∩ Iso).card)).card
      + (Hub.filter (fun h => G.degree h = 4 ∧ 4 ≤ (G.neighborFinset h ∩ Iso).card)).card ≤ 2) :
    ∑ v ∈ Hub.filter (fun h => G.degree h = 4), (G.neighborFinset v ∩ Iso).card
      ≤ 2 * (Hub.filter (fun h => G.degree h = 4)).card + 2 := by
  classical
  set T : Finset (Fin 18) := Hub.filter (fun h => G.degree h = 4) with hT
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
  have hn2 : (T.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)).card ≤ T.card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  rw [h3, h4] at hcong
  omega

/-- **Residual master inequality.**  In the `e(M) ≤ 1` residual (every hub of degree `4` or `5`,
each `M`-isolated twin meeting exactly three hubs, the degree-`4`-restricted share `≤ 1`) with a
*refuted* selection (`hcon`), erasing the degree-`5` hubs gives
`3·|Iso| + 10·|Hub| ≤ 3·∑deg + 2`: the degree-`4` iso-sum is `≤ 2·|deg-4| + 2` (threshold/clique),
the degree-`5` iso-sum is `≤ 5·|deg-5|`, and `∑deg = 4·|deg-4| + 5·|deg-5|`.  Every non-tight
regime violates this numerically, refuting `hcon`. -/
theorem residual_arith_eighteen (G : SimpleGraph (Fin 18)) (Hub Iso : Finset (Fin 18))
    (hdisj : Disjoint Hub Iso)
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdeg45 : ∀ h ∈ Hub, G.degree h = 4 ∨ G.degree h = 5)
    (hcon : ¬ ∃ h₁ h₂ : Fin 18, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card) :
    3 * Iso.card + 10 * Hub.card ≤ 3 * (∑ w ∈ Hub, G.degree w) + 2 := by
  classical
  have hiso_le : ∀ a : Fin 18, (G.neighborFinset a ∩ Iso).card ≤ G.degree a := by
    intro a
    rw [← G.card_neighborFinset_eq_degree]; exact Finset.card_le_card Finset.inter_subset_left
  have key := nogood_of_not_select_eighteen G Hub Iso hcon
  have hmf := strong_deg4_count_le_two_deg5_eighteen G Hub Iso hdisj hshare key
  have hisoSum := hub_iso_sum_eighteen G Hub Iso hiso3
  have hTsum_le := deg4_sum_le_eighteen G Hub Iso hmf
  set T : Finset (Fin 18) := Hub.filter (fun h => G.degree h = 4) with hT
  set R : Finset (Fin 18) := Hub.filter (fun h => ¬ G.degree h = 4) with hR
  have hpartIso : ∑ v ∈ T, (G.neighborFinset v ∩ Iso).card
      + ∑ v ∈ R, (G.neighborFinset v ∩ Iso).card = ∑ v ∈ Hub, (G.neighborFinset v ∩ Iso).card :=
    Finset.sum_filter_add_sum_filter_not Hub (fun h => G.degree h = 4) _
  have hRdeg5 : ∀ v ∈ R, G.degree v = 5 := by
    intro v hv; rw [hR, Finset.mem_filter] at hv
    rcases hdeg45 v hv.1 with h4 | h5
    · exact absurd h4 hv.2
    · exact h5
  have hRiso_le : ∑ v ∈ R, (G.neighborFinset v ∩ Iso).card ≤ 5 * R.card := by
    calc ∑ v ∈ R, (G.neighborFinset v ∩ Iso).card
        ≤ ∑ _v ∈ R, 5 := Finset.sum_le_sum (fun v hv => by
          have := hiso_le v; rw [hRdeg5 v hv] at this; exact this)
      _ = 5 * R.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have hpartDeg : ∑ v ∈ T, G.degree v + ∑ v ∈ R, G.degree v = ∑ v ∈ Hub, G.degree v :=
    Finset.sum_filter_add_sum_filter_not Hub (fun h => G.degree h = 4) _
  have hTdeg : ∑ v ∈ T, G.degree v = 4 * T.card := by
    rw [Finset.sum_congr rfl (fun x hx => (Finset.mem_filter.mp hx).2), Finset.sum_const,
      smul_eq_mul, mul_comm]
  have hRdeg : ∑ v ∈ R, G.degree v = 5 * R.card := by
    rw [Finset.sum_congr rfl (fun x hx => hRdeg5 x hx), Finset.sum_const, smul_eq_mul, mul_comm]
  have hcard : T.card + R.card = Hub.card :=
    Finset.card_filter_add_card_filter_not (fun h => G.degree h = 4)
  omega

end N18

end ACMax
