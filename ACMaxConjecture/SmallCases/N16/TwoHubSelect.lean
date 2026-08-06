import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N16.Core

/-!
# Hub-pair selection for the `n = 16` two-hub `e(M) ≤ 1` residual

This file supplies `two_hub_corner_select_sixteen`, the hub-pair *selection* lemma feeding the
`e(M) ≤ 1` (`s ≤ 2`, no-cherry) branch of `two_hub_config_sixteen`.

At `e(M) ≤ 1` the residual two-hub structure has three regimes:
* `e(M) = 0`: `|Hub| = 8` (all degree `4`, `|Iso| = 8`, `e(Hub) = 4`);
* `e(M) = 1`: `|Hub| = 7` (one degree-`5` + six degree-`4`, `|Iso| = 7`, `e(Hub) = 2`);
* `e(M) = 1`: `|Hub| = 8` (all degree `4`, `|Iso| = 6`, `e(Hub) = 5`).

The **key simplification** over `n = 15` is the sharper share bound `nonadj_hubs_share_le_one_iso`
(non-adjacent degree-`4` hubs share at most **one** `M`-isolated twin, via the good-`C₄` `Σ ≤ 14`
threshold).  With share `≤ 1`, any two non-adjacent degree-`4` hubs of iso-degree `≥ 3` keep
`≥ 3 − 1 = 2` private twins each.  The "no good pair" refutation then forces the set `S` of
degree-`4` iso-degree-`≥ 3` hubs to be a *clique*, and each such hub has `≤ 1` hub-neighbour, so
`|S| ≤ 2`; the regime arithmetic (with a single off-diagonal share-sum bound `≤ 46` for the tight
`|Iso| = 6` regime) then contradicts the iso-degree total `3·|Iso|`.  This eliminates the delicate
`n = 15` weak-hub `K₂,₃`-impossibility cluster entirely.
-/

namespace ACMax

open scoped Classical

namespace N16

/-- **Per-vertex share double count.**  For any `v`, summing the iso-shares `|N v ∩ N x ∩ Iso|`
over hubs `x ∈ Hub` counts each isolated twin `t ∈ N v ∩ Iso` once per hub adjacent to it, i.e.
`|N t ∩ Hub| = 3` times, giving `3·|N v ∩ Iso|`. -/
theorem per_vertex_share_sum_sixteen (G : SimpleGraph (Fin 16)) (Hub Iso : Finset (Fin 16))
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3) (v : Fin 16) :
    ∑ x ∈ Hub, (G.neighborFinset v ∩ G.neighborFinset x ∩ Iso).card
      = 3 * (G.neighborFinset v ∩ Iso).card := by
  classical
  have hset : ∀ x : Fin 16, (G.neighborFinset v ∩ G.neighborFinset x ∩ Iso).card
      = (G.neighborFinset x ∩ (G.neighborFinset v ∩ Iso)).card := by
    intro x
    rw [Finset.inter_comm (G.neighborFinset v) (G.neighborFinset x), Finset.inter_assoc]
  rw [Finset.sum_congr rfl (fun x _ => hset x),
    cross_count G Hub (G.neighborFinset v ∩ Iso)]
  calc ∑ t ∈ (G.neighborFinset v ∩ Iso), (G.neighborFinset t ∩ Hub).card
      = ∑ _t ∈ (G.neighborFinset v ∩ Iso), 3 :=
        Finset.sum_congr rfl (fun t ht => hiso3 t (Finset.mem_inter.mp ht).2)
    _ = 3 * (G.neighborFinset v ∩ Iso).card := by
        rw [Finset.sum_const, smul_eq_mul, mul_comm]

/-- **Adjacent ordered hub pairs equal the hub-incidence sum.**  With `∑_{w∈Hub}|N w ∩ Hub| ≤ k`,
the ordered off-diagonal adjacent pairs number at most `k`. -/
theorem hub_offDiag_adj_le_sixteen (G : SimpleGraph (Fin 16)) (Hub : Finset (Fin 16)) (k : ℕ)
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
  have hrow : ∀ a : Fin 16, ∑ b ∈ Hub, (if G.Adj a b then 1 else 0)
      = (G.neighborFinset a ∩ Hub).card := by
    intro a
    rw [Finset.inter_comm, ← Finset.filter_mem_eq_inter, Finset.card_filter]
    exact Finset.sum_congr rfl (fun b _ => by simp only [G.mem_neighborFinset])
  rw [Finset.sum_congr rfl (fun a _ => hrow a)]
  exact hHubsum

/-- **Exact off-diagonal share sum.**  In any hub set where every isolated twin meets exactly three
hubs (`hiso3`), the ordered off-diagonal share double count is `6·|Iso|` (independent of `|Hub|`):
each twin sits in `3·2 = 6` ordered hub pairs. -/
theorem hub_offDiag_share_sum_sixteen (G : SimpleGraph (Fin 16)) (Hub Iso : Finset (Fin 16))
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3) :
    ∑ p ∈ Hub.offDiag, (G.neighborFinset p.1 ∩ G.neighborFinset p.2 ∩ Iso).card
      = 6 * Iso.card := by
  classical
  let F : Fin 16 → Fin 16 → ℕ :=
    fun a b => (G.neighborFinset a ∩ G.neighborFinset b ∩ Iso).card
  show ∑ p ∈ Hub.offDiag, F p.1 p.2 = 6 * Iso.card
  have hT : ∑ a ∈ Hub, (G.neighborFinset a ∩ Iso).card = 3 * Iso.card := by
    rw [cross_count G Hub Iso]
    calc ∑ t ∈ Iso, (G.neighborFinset t ∩ Hub).card
        = ∑ _t ∈ Iso, 3 := Finset.sum_congr rfl (fun t ht => hiso3 t ht)
      _ = 3 * Iso.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have hrow : ∀ a : Fin 16, ∑ b ∈ Hub, F a b = 3 * (G.neighborFinset a ∩ Iso).card := by
    intro a
    show ∑ b ∈ Hub, (G.neighborFinset a ∩ G.neighborFinset b ∩ Iso).card
      = 3 * (G.neighborFinset a ∩ Iso).card
    exact per_vertex_share_sum_sixteen G Hub Iso hiso3 a
  have hprod : ∑ p ∈ Hub ×ˢ Hub, F p.1 p.2 = 9 * Iso.card := by
    rw [Finset.sum_product', Finset.sum_congr rfl (fun a _ => hrow a), ← Finset.mul_sum, hT]
    ring
  have hdiagval : ∀ a : Fin 16, F a a = (G.neighborFinset a ∩ Iso).card := by
    intro a
    show (G.neighborFinset a ∩ G.neighborFinset a ∩ Iso).card = (G.neighborFinset a ∩ Iso).card
    rw [Finset.inter_self]
  have hdiagsum : ∑ p ∈ Hub.diag, F p.1 p.2 = 3 * Iso.card := by
    rw [Finset.diag, Finset.sum_map]
    change ∑ a ∈ Hub, F a a = _
    rw [Finset.sum_congr rfl (fun a _ => hdiagval a), hT]
  have hsplit : ∑ p ∈ Hub.diag, F p.1 p.2 + ∑ p ∈ Hub.offDiag, F p.1 p.2
      = ∑ p ∈ Hub ×ˢ Hub, F p.1 p.2 := by
    rw [← Finset.sum_union (Finset.disjoint_diag_offDiag Hub), Finset.diag_union_offDiag]
  rw [hdiagsum, hprod] at hsplit; omega

/-- **Finish the selection.**  From a non-adjacent degree-`4` pair `h₁, h₂ ∈ Hub` whose iso-degree
exceeds their share by `≥ 2` on each side, extract the two private-twin bounds. -/
theorem select_finish_sixteen (G : SimpleGraph (Fin 16)) (Iso : Finset (Fin 16)) (h₁ h₂ : Fin 16)
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
theorem hub_iso_sum_sixteen (G : SimpleGraph (Fin 16)) (Hub Iso : Finset (Fin 16))
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3) :
    ∑ a ∈ Hub, (G.neighborFinset a ∩ Iso).card = 3 * Iso.card := by
  rw [cross_count G Hub Iso]
  calc ∑ t ∈ Iso, (G.neighborFinset t ∩ Hub).card
      = ∑ _t ∈ Iso, 3 := Finset.sum_congr rfl (fun t ht => hiso3 t ht)
    _ = 3 * Iso.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

/-- **No good pair from a refuted selection.**  Packages `select_finish_sixteen` into the
`min(iso-deg) ≤ share + 1` form on non-adjacent degree-`4` hub pairs, given a refutation `hcon` of
the selection goal. -/
theorem nogood_of_not_select_sixteen (G : SimpleGraph (Fin 16)) (Hub Iso : Finset (Fin 16))
    (hcon : ¬ ∃ h₁ h₂ : Fin 16, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
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
  have hfin := select_finish_sixteen G Iso a b hsa hsb
  exact hcon ⟨a, b, ha, hb, hda, hdb, hne, hnadj, hfin.1, hfin.2⟩

/-- **A degree-`4` hub's hub-neighbour count is bounded by `4 −` its iso-degree.**  The neighbours
in `Hub` and in `Iso` are disjoint (`hdisj`) subsets of the degree-`4` neighbourhood. -/
theorem hub_neighbor_le_sixteen (G : SimpleGraph (Fin 16)) (Hub Iso : Finset (Fin 16))
    (hdisj : Disjoint Hub Iso) (a : Fin 16) (hda : G.degree a = 4) :
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

/-- **The strong degree-`4` hubs number `≤ 2` (with iso-degree-`4` slack).**  Under the refuted
selection (`key`) and the share-`≤ 1` bound (`hshare`), the set `A` of degree-`4` hubs of iso-degree
`≥ 3` is a clique; each member has `≤ 4 − 3 = 1` hub-neighbours, so `|A| ≤ 2`, and an iso-degree-`4`
member (`0` hub-neighbours) forces `|A| ≤ 1`.  Hence `|A| + |B| ≤ 2` where `B` are the iso-degree-`4`
degree-`4` hubs. -/
theorem strong_deg4_count_le_two_sixteen (G : SimpleGraph (Fin 16)) (Hub Iso : Finset (Fin 16))
    (hdisj : Disjoint Hub Iso)
    (hshare : ∀ h₁ ∈ Hub, ∀ h₂ ∈ Hub, h₁ ≠ h₂ → ¬G.Adj h₁ h₂ →
      (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (key : ∀ a ∈ Hub, ∀ b ∈ Hub, G.degree a = 4 → G.degree b = 4 → a ≠ b → ¬G.Adj a b →
      min ((G.neighborFinset a ∩ Iso).card) ((G.neighborFinset b ∩ Iso).card)
        ≤ (G.neighborFinset a ∩ G.neighborFinset b ∩ Iso).card + 1) :
    (Hub.filter (fun h => G.degree h = 4 ∧ 3 ≤ (G.neighborFinset h ∩ Iso).card)).card
      + (Hub.filter (fun h => G.degree h = 4 ∧ 4 ≤ (G.neighborFinset h ∩ Iso).card)).card ≤ 2 := by
  classical
  set A : Finset (Fin 16) :=
    Hub.filter (fun h => G.degree h = 4 ∧ 3 ≤ (G.neighborFinset h ∩ Iso).card) with hA
  set B : Finset (Fin 16) :=
    Hub.filter (fun h => G.degree h = 4 ∧ 4 ≤ (G.neighborFinset h ∩ Iso).card) with hB
  have hAprop : ∀ a ∈ A, a ∈ Hub ∧ G.degree a = 4 ∧ 3 ≤ (G.neighborFinset a ∩ Iso).card := by
    intro a ha; rw [hA, Finset.mem_filter] at ha; exact ⟨ha.1, ha.2.1, ha.2.2⟩
  have hBA : B ⊆ A := by
    intro x hx; rw [hB, Finset.mem_filter] at hx; rw [hA, Finset.mem_filter]
    exact ⟨hx.1, hx.2.1, by omega⟩
  -- `A` is a clique.
  have hclique : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → G.Adj a b := by
    intro a ha b hb hab
    by_contra hnadj
    obtain ⟨haHub, hda, ha3⟩ := hAprop a ha
    obtain ⟨hbHub, hdb, hb3⟩ := hAprop b hb
    have hk := key a haHub b hbHub hda hdb hab hnadj
    have hs := hshare a haHub b hbHub hab hnadj
    have : 3 ≤ min ((G.neighborFinset a ∩ Iso).card) ((G.neighborFinset b ∩ Iso).card) :=
      le_min ha3 hb3
    omega
  -- Each `a ∈ A` has `A.erase a ⊆ N a ∩ Hub`, so `|A| − 1 ≤ |N a ∩ Hub| ≤ 4 − iso-deg a`.
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
    have hc2 := hub_neighbor_le_sixteen G Hub Iso hdisj a hda
    omega
  -- Case on whether `B` is empty.
  rcases Finset.eq_empty_or_nonempty B with hBe | hBne
  · have hBcard : B.card = 0 := by rw [hBe]; rfl
    -- `A.card ≤ 2`: pick any element (if nonempty) and use iso-deg `≥ 3`.
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

/-- **Hub-pair selection for the `n = 16` two-hub `e(M) ≤ 1` residual.**  Given a hub set of
degree-`≤ 5` vertices, every `M`-isolated twin meeting exactly three hubs (`hiso3`), the twins
`M`-independent (`hisoIndep`), the sharp good-`C₄` share bound (`hshare`, share `≤ 1`), and one of
the three `e(M) ≤ 1` regimes (`hregime`), there exist two non-adjacent degree-`4` hubs each
retaining `≥ 2` private `M`-isolated twins.

All profiles close by the share-`≤ 1` clique bound (`strong_deg4_count_le_two_sixteen`): the
extremal case (two degree-`4` iso-degree-`4` hubs) is direct; the residual closes by iso-degree
arithmetic, with the tight `|Iso| = 6` regime additionally using the off-diagonal share-sum bound
`|U.offDiag| ≤ 6·|Iso| + e(Hub)`.  No `n = 15`-style weak-hub `K₂,₃` impossibility is needed. -/
theorem two_hub_corner_select_sixteen (G : SimpleGraph (Fin 16)) (Hub Iso : Finset (Fin 16))
    (hdeg : ∀ h ∈ Hub, 4 ≤ G.degree h)
    (hdeg5 : ∀ h ∈ Hub, G.degree h ≤ 5)
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (_hisoIndep : ∀ a ∈ Iso, ∀ b ∈ Iso, ¬G.Adj a b)
    (hshare : ∀ h₁ ∈ Hub, ∀ h₂ ∈ Hub, h₁ ≠ h₂ → ¬G.Adj h₁ h₂ →
      (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hdisj : Disjoint Hub Iso)
    (hregime :
      (Hub.card = 8 ∧ Iso.card = 8 ∧ (∀ h ∈ Hub, G.degree h = 4) ∧
        (∑ w ∈ Hub, (G.neighborFinset w ∩ Hub).card = 8)) ∨
      (Hub.card = 7 ∧ Iso.card = 7 ∧ (∑ w ∈ Hub, G.degree w = 29) ∧
        (∑ w ∈ Hub, (G.neighborFinset w ∩ Hub).card = 4)) ∨
      (Hub.card = 8 ∧ Iso.card = 6 ∧ (∀ h ∈ Hub, G.degree h = 4) ∧
        (∑ w ∈ Hub, (G.neighborFinset w ∩ Hub).card = 10))) :
    ∃ h₁ h₂ : Fin 16, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card := by
  classical
  -- Iso-degree never exceeds degree.
  have hiso_le : ∀ a : Fin 16, (G.neighborFinset a ∩ Iso).card ≤ G.degree a := by
    intro a
    rw [← G.card_neighborFinset_eq_degree]; exact Finset.card_le_card Finset.inter_subset_left
  set F : Finset (Fin 16) :=
    Hub.filter (fun h => G.degree h = 4 ∧ (G.neighborFinset h ∩ Iso).card = 4) with hFdef
  by_cases hk : 2 ≤ F.card
  · -- **Extremal case: two degree-`4` hubs of iso-degree `4`.**
    obtain ⟨h₁, hh1F, h₂, hh2F, hne⟩ := Finset.one_lt_card.mp hk
    obtain ⟨hh1, hd1, h1iso4⟩ := Finset.mem_filter.mp hh1F
    obtain ⟨hh2, hd2, h2iso4⟩ := Finset.mem_filter.mp hh2F
    have hsub : ∀ h : Fin 16, G.degree h = 4 → (G.neighborFinset h ∩ Iso).card = 4 →
        G.neighborFinset h ⊆ Iso := by
      intro h hdh hh4
      have hdc : (G.neighborFinset h).card = 4 := by rw [G.card_neighborFinset_eq_degree, hdh]
      have heq : G.neighborFinset h ∩ Iso = G.neighborFinset h :=
        Finset.eq_of_subset_of_card_le Finset.inter_subset_left (le_of_eq (by rw [hdc, hh4]))
      rw [← heq]; exact Finset.inter_subset_right
    have h1sub : G.neighborFinset h₁ ⊆ Iso := hsub h₁ hd1 h1iso4
    have hnadj : ¬G.Adj h₁ h₂ := by
      intro hadj
      exact Finset.disjoint_left.mp hdisj hh2 (h1sub ((G.mem_neighborFinset h₁ h₂).mpr hadj))
    have hsh : (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1 :=
      hshare h₁ hh1 h₂ hh2 hne hnadj
    have hsh' : (G.neighborFinset h₂ ∩ G.neighborFinset h₁ ∩ Iso).card ≤ 1 :=
      hshare h₂ hh2 h₁ hh1 (Ne.symm hne) (fun h => hnadj h.symm)
    have hfin := select_finish_sixteen G Iso h₁ h₂ (by omega) (by omega)
    exact ⟨h₁, h₂, hh1, hh2, hd1, hd2, hne, hnadj, hfin.1, hfin.2⟩
  · -- **Residual: at most one degree-`4` hub of iso-degree `4`.**
    by_contra hcon
    have key := nogood_of_not_select_sixteen G Hub Iso hcon
    have hmf := strong_deg4_count_le_two_sixteen G Hub Iso hdisj hshare key
    set m3 : Finset (Fin 16) := Hub.filter (fun h => G.degree h = 4 ∧
      3 ≤ (G.neighborFinset h ∩ Iso).card) with hm3
    set f4 : Finset (Fin 16) := Hub.filter (fun h => G.degree h = 4 ∧
      4 ≤ (G.neighborFinset h ∩ Iso).card) with hf4
    have hisoSum := hub_iso_sum_sixteen G Hub Iso hiso3
    rcases hregime with ⟨hHub8, hIso8, hdeg4, _hHubsum⟩ |
      ⟨hHub7, hIso7, hdsum, hHubsum⟩ | ⟨hHub8, hIso6, hdeg4, hHubsum⟩
    · -- **Regime (A): `|Hub| = 8`, `|Iso| = 8`, all degree `4`.**
      have hm3eq : m3 = Hub.filter (fun h => 3 ≤ (G.neighborFinset h ∩ Iso).card) := by
        rw [hm3]; exact Finset.filter_congr (fun x hx => by rw [hdeg4 x hx]; tauto)
      have hf4eq : f4 = Hub.filter (fun h => 4 ≤ (G.neighborFinset h ∩ Iso).card) := by
        rw [hf4]; exact Finset.filter_congr (fun x hx => by rw [hdeg4 x hx]; tauto)
      have hdecomp : ∀ a ∈ Hub, (G.neighborFinset a ∩ Iso).card
          = (if 1 ≤ (G.neighborFinset a ∩ Iso).card then 1 else 0)
            + (if 2 ≤ (G.neighborFinset a ∩ Iso).card then 1 else 0)
            + (if 3 ≤ (G.neighborFinset a ∩ Iso).card then 1 else 0)
            + (if 4 ≤ (G.neighborFinset a ∩ Iso).card then 1 else 0) := by
        intro a ha
        have := hiso_le a; rw [hdeg4 a ha] at this; split_ifs <;> omega
      have hcong : ∑ a ∈ Hub, (G.neighborFinset a ∩ Iso).card
          = ∑ a ∈ Hub, ((if 1 ≤ (G.neighborFinset a ∩ Iso).card then 1 else 0)
            + (if 2 ≤ (G.neighborFinset a ∩ Iso).card then 1 else 0)
            + (if 3 ≤ (G.neighborFinset a ∩ Iso).card then 1 else 0)
            + (if 4 ≤ (G.neighborFinset a ∩ Iso).card then 1 else 0)) :=
        Finset.sum_congr rfl hdecomp
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
        ← Finset.card_filter, ← Finset.card_filter, ← Finset.card_filter, ← Finset.card_filter,
        hisoSum, hIso8, ← hm3eq, ← hf4eq] at hcong
      have hn1 : (Hub.filter (fun h => 1 ≤ (G.neighborFinset h ∩ Iso).card)).card ≤ 8 := by
        rw [← hHub8]; exact Finset.card_le_card (Finset.filter_subset _ _)
      have hu : (Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)).card ≤ 8 := by
        rw [← hHub8]; exact Finset.card_le_card (Finset.filter_subset _ _)
      omega
    · -- **Regime (B): `|Hub| = 7`, `|Iso| = 7`, one degree-`5` + six degree-`4`.**
      have hdeg45 : ∀ h ∈ Hub, G.degree h = 4 ∨ G.degree h = 5 := by
        intro h hh; have := hdeg h hh; have := hdeg5 h hh; omega
      set D5 : Finset (Fin 16) := Hub.filter (fun h => G.degree h = 5) with hD5
      have hD5card : D5.card = 1 := by
        have hsplit : ∀ h ∈ Hub, G.degree h = 4 + (if G.degree h = 5 then 1 else 0) := by
          intro h hh; rcases hdeg45 h hh with h4 | h5
          · rw [h4]; simp
          · rw [h5]; simp
        have hss : ∑ h ∈ Hub, G.degree h = 4 * Hub.card + D5.card := by
          rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul,
            mul_comm, hD5, Finset.sum_boole, Nat.cast_id]
        rw [hdsum, hHub7] at hss; omega
      obtain ⟨g, hgeq⟩ := Finset.card_eq_one.mp hD5card
      have hgD5 : g ∈ D5 := by rw [hgeq]; exact Finset.mem_singleton_self g
      have hgHub : g ∈ Hub := (Finset.mem_filter.mp hgD5).1
      have hgdeg5 : G.degree g = 5 := (Finset.mem_filter.mp hgD5).2
      set T : Finset (Fin 16) := Hub.erase g with hT
      have hTsub : T ⊆ Hub := Finset.erase_subset _ _
      have hTdeg4 : ∀ v ∈ T, G.degree v = 4 := by
        intro v hv
        have hvHub : v ∈ Hub := hTsub hv
        rcases hdeg45 v hvHub with h4 | h5
        · exact h4
        · exfalso
          have hvD5 : v ∈ D5 := Finset.mem_filter.mpr ⟨hvHub, h5⟩
          rw [hgeq, Finset.mem_singleton] at hvD5
          exact (Finset.ne_of_mem_erase hv) hvD5
      have hT6 : T.card = 6 := by rw [hT, Finset.card_erase_of_mem hgHub, hHub7]
      -- `∑_T iso-deg = 21 − iso-deg g ≥ 16`.
      have hgiso_le : (G.neighborFinset g ∩ Iso).card ≤ 5 := by
        have := hiso_le g; rw [hgdeg5] at this; exact this
      have hTsumsplit : (G.neighborFinset g ∩ Iso).card
          + ∑ v ∈ T, (G.neighborFinset v ∩ Iso).card = 21 := by
        rw [hT, Finset.add_sum_erase Hub (fun v => (G.neighborFinset v ∩ Iso).card) hgHub]
        rw [hisoSum, hIso7]
      have hTsumge : 16 ≤ ∑ v ∈ T, (G.neighborFinset v ∩ Iso).card := by omega
      -- Threshold decomposition over `T` (all degree `4`).
      have hAeq : m3 = T.filter (fun h => 3 ≤ (G.neighborFinset h ∩ Iso).card) := by
        rw [hm3, hT]; ext x
        simp only [Finset.mem_filter, Finset.mem_erase]
        constructor
        · rintro ⟨hxHub, hxd4, hx3⟩
          refine ⟨⟨?_, hxHub⟩, hx3⟩
          intro he; rw [he] at hxd4; omega
        · rintro ⟨⟨hxg, hxHub⟩, hx3⟩
          exact ⟨hxHub, hTdeg4 x (Finset.mem_erase.mpr ⟨hxg, hxHub⟩), hx3⟩
      have hBeq : f4 = T.filter (fun h => 4 ≤ (G.neighborFinset h ∩ Iso).card) := by
        rw [hf4, hT]; ext x
        simp only [Finset.mem_filter, Finset.mem_erase]
        constructor
        · rintro ⟨hxHub, hxd4, hx4⟩
          refine ⟨⟨?_, hxHub⟩, hx4⟩
          intro he; rw [he] at hxd4; omega
        · rintro ⟨⟨hxg, hxHub⟩, hx4⟩
          exact ⟨hxHub, hTdeg4 x (Finset.mem_erase.mpr ⟨hxg, hxHub⟩), hx4⟩
      have hdecomp : ∀ a ∈ T, (G.neighborFinset a ∩ Iso).card
          = (if 1 ≤ (G.neighborFinset a ∩ Iso).card then 1 else 0)
            + (if 2 ≤ (G.neighborFinset a ∩ Iso).card then 1 else 0)
            + (if 3 ≤ (G.neighborFinset a ∩ Iso).card then 1 else 0)
            + (if 4 ≤ (G.neighborFinset a ∩ Iso).card then 1 else 0) := by
        intro a ha
        have := hiso_le a; rw [hTdeg4 a ha] at this; split_ifs <;> omega
      have hcong : ∑ a ∈ T, (G.neighborFinset a ∩ Iso).card
          = ∑ a ∈ T, ((if 1 ≤ (G.neighborFinset a ∩ Iso).card then 1 else 0)
            + (if 2 ≤ (G.neighborFinset a ∩ Iso).card then 1 else 0)
            + (if 3 ≤ (G.neighborFinset a ∩ Iso).card then 1 else 0)
            + (if 4 ≤ (G.neighborFinset a ∩ Iso).card then 1 else 0)) :=
        Finset.sum_congr rfl hdecomp
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
        ← Finset.card_filter, ← Finset.card_filter, ← Finset.card_filter, ← Finset.card_filter,
        ← hAeq, ← hBeq] at hcong
      have hn1 : (T.filter (fun h => 1 ≤ (G.neighborFinset h ∩ Iso).card)).card ≤ 6 := by
        rw [← hT6]; exact Finset.card_le_card (Finset.filter_subset _ _)
      have hu : (T.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)).card ≤ 6 := by
        rw [← hT6]; exact Finset.card_le_card (Finset.filter_subset _ _)
      omega
    · -- **Regime (C): `|Hub| = 8`, `|Iso| = 6`, all degree `4` (tight; needs the share-sum).**
      have hm3eq : m3 = Hub.filter (fun h => 3 ≤ (G.neighborFinset h ∩ Iso).card) := by
        rw [hm3]; exact Finset.filter_congr (fun x hx => by rw [hdeg4 x hx]; tauto)
      have hf4eq : f4 = Hub.filter (fun h => 4 ≤ (G.neighborFinset h ∩ Iso).card) := by
        rw [hf4]; exact Finset.filter_congr (fun x hx => by rw [hdeg4 x hx]; tauto)
      set U : Finset (Fin 16) := Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card) with hU
      have hUsub : U ⊆ Hub := Finset.filter_subset _ _
      -- **Share-sum bound `|U.offDiag| ≤ 6·|Iso| + e(Hub)` giving `u ≤ 7`.**
      have hUge : ∀ p ∈ U.offDiag, (if ¬G.Adj p.1 p.2 then 1 else 0)
          ≤ (G.neighborFinset p.1 ∩ G.neighborFinset p.2 ∩ Iso).card := by
        intro p hp
        rw [Finset.mem_offDiag] at hp
        obtain ⟨hp1, hp2, hp12⟩ := hp
        by_cases hadj : G.Adj p.1 p.2
        · simp [hadj]
        · rw [if_pos hadj]
          have hp1H := hUsub hp1
          have hp2H := hUsub hp2
          have h2a : 2 ≤ (G.neighborFinset p.1 ∩ Iso).card := (Finset.mem_filter.mp hp1).2
          have h2b : 2 ≤ (G.neighborFinset p.2 ∩ Iso).card := (Finset.mem_filter.mp hp2).2
          have hk := key p.1 hp1H p.2 hp2H (hdeg4 p.1 hp1H) (hdeg4 p.2 hp2H) hp12 hadj
          have : 2 ≤ min ((G.neighborFinset p.1 ∩ Iso).card)
              ((G.neighborFinset p.2 ∩ Iso).card) := le_min h2a h2b
          omega
      have hsumge : (U.offDiag.filter (fun p => ¬G.Adj p.1 p.2)).card
          ≤ ∑ p ∈ U.offDiag, (G.neighborFinset p.1 ∩ G.neighborFinset p.2 ∩ Iso).card := by
        rw [Finset.card_filter]; exact Finset.sum_le_sum hUge
      have hsumle : ∑ p ∈ U.offDiag,
          (G.neighborFinset p.1 ∩ G.neighborFinset p.2 ∩ Iso).card ≤ 6 * Iso.card := by
        rw [← hub_offDiag_share_sum_sixteen G Hub Iso hiso3]
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => Nat.zero_le _)
        intro p hp
        rw [Finset.mem_offDiag] at hp ⊢
        exact ⟨hUsub hp.1, hUsub hp.2.1, hp.2.2⟩
      have hadjU : (U.offDiag.filter (fun p => G.Adj p.1 p.2)).card ≤ 10 := by
        refine le_trans (Finset.card_le_card ?_) (hub_offDiag_adj_le_sixteen G Hub 10 (by
          rw [hHubsum]))
        apply Finset.filter_subset_filter
        intro p hp
        rw [Finset.mem_offDiag] at hp ⊢
        exact ⟨hUsub hp.1, hUsub hp.2.1, hp.2.2⟩
      have hpart := Finset.card_filter_add_card_filter_not (s := U.offDiag)
        (fun p => G.Adj p.1 p.2)
      have hUoff : U.offDiag.card = U.card * U.card - U.card := Finset.offDiag_card U
      have hu8 : U.card ≤ 8 := by rw [← hHub8]; exact Finset.card_le_card hUsub
      have hu7 : U.card ≤ 7 := by
        by_contra hge
        have : U.card = 8 := by omega
        rw [this] at hUoff
        rw [hIso6] at hsumle
        omega
      -- Threshold decomposition over `Hub` (all degree `4`).
      have hdecomp : ∀ a ∈ Hub, (G.neighborFinset a ∩ Iso).card
          = (if 1 ≤ (G.neighborFinset a ∩ Iso).card then 1 else 0)
            + (if 2 ≤ (G.neighborFinset a ∩ Iso).card then 1 else 0)
            + (if 3 ≤ (G.neighborFinset a ∩ Iso).card then 1 else 0)
            + (if 4 ≤ (G.neighborFinset a ∩ Iso).card then 1 else 0) := by
        intro a ha
        have := hiso_le a; rw [hdeg4 a ha] at this; split_ifs <;> omega
      have hcong : ∑ a ∈ Hub, (G.neighborFinset a ∩ Iso).card
          = ∑ a ∈ Hub, ((if 1 ≤ (G.neighborFinset a ∩ Iso).card then 1 else 0)
            + (if 2 ≤ (G.neighborFinset a ∩ Iso).card then 1 else 0)
            + (if 3 ≤ (G.neighborFinset a ∩ Iso).card then 1 else 0)
            + (if 4 ≤ (G.neighborFinset a ∩ Iso).card then 1 else 0)) :=
        Finset.sum_congr rfl hdecomp
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
        ← Finset.card_filter, ← Finset.card_filter, ← Finset.card_filter, ← Finset.card_filter,
        hisoSum, hIso6, ← hU, ← hm3eq, ← hf4eq] at hcong
      have hn1 : (Hub.filter (fun h => 1 ≤ (G.neighborFinset h ∩ Iso).card)).card ≤ 8 := by
        rw [← hHub8]; exact Finset.card_le_card (Finset.filter_subset _ _)
      omega

end N16

end ACMax
