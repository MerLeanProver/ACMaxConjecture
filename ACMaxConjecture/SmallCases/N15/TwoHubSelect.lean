import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N15.Core

/-!
# Hub-pair selection for the `n = 15` two-hub `e(M) = 1` (`s = 2`) residual

This file supplies `two_hub_corner_select_fifteen`, the hub-pair *selection* lemma feeding the
`e(M) = 1` (`s = 2`) branch of `two_hub_config_fifteen` (in `TwinCert15Align`).

At `e(M) = 1` the residual two-hub structure has two regimes:
* `|Hub| = 7` (all degree `4`, `e(Hub) = 3`, `|Iso| = 6`);
* `|Hub| = 6` (one degree-`5` hub, five degree-`4` hubs, `e(Hub) = 0`, `|Iso| = 7`).

The counting infrastructure (`per_vertex_share_sum(_erase)`, `filter_le_one_card_ge`,
`sum_offDiag_erase`, `hub_offDiag_adj_le`, `hub_offDiag_share_sum`,
`two_hub_corner_pair_count_fifteen`) is the `n`-independent port of the `n = 14` chain
(`Fin 14 → Fin 15`, `cross_count_fourteen → cross_count`).

The clean extremal sub-case (at least two **degree-`4`** hubs of iso-degree `4`) is fully proved:
such hubs are hub-isolated, pairwise non-adjacent, and the share bound leaves each `≥ 2` private
isolated twins.  The complementary corner (at most one such hub — the genuine weak-hub /
degree-`5`-exclusion pigeonhole) is isolated as the one documented `sorry`.
-/

namespace ACMax

open scoped Classical

namespace N15

/-- **Per-vertex share double count.**  For any `v`, summing the iso-shares `|N v ∩ N x ∩ Iso|`
over hubs `x ∈ Hub` counts each isolated twin `t ∈ N v ∩ Iso` once per hub adjacent to it, i.e.
`|N t ∩ Hub| = 3` times, giving `3·|N v ∩ Iso|`. -/
theorem per_vertex_share_sum (G : SimpleGraph (Fin 15)) (Hub Iso : Finset (Fin 15))
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3) (v : Fin 15) :
    ∑ x ∈ Hub, (G.neighborFinset v ∩ G.neighborFinset x ∩ Iso).card
      = 3 * (G.neighborFinset v ∩ Iso).card := by
  classical
  have hset : ∀ x : Fin 15, (G.neighborFinset v ∩ G.neighborFinset x ∩ Iso).card
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

/-- **Off-diagonal per-vertex share double count.**  For a hub `v ∈ Hub`, removing the diagonal
term `|N v ∩ Iso|` from `per_vertex_share_sum` leaves `∑_{x∈Hub\{v}} = 2·|N v ∩ Iso|`. -/
theorem per_vertex_share_sum_erase (G : SimpleGraph (Fin 15)) (Hub Iso : Finset (Fin 15))
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3) (v : Fin 15) (hv : v ∈ Hub) :
    ∑ x ∈ Hub.erase v, (G.neighborFinset v ∩ G.neighborFinset x ∩ Iso).card
      = 2 * (G.neighborFinset v ∩ Iso).card := by
  classical
  have hdiag : (G.neighborFinset v ∩ G.neighborFinset v ∩ Iso).card
      = (G.neighborFinset v ∩ Iso).card := by rw [Finset.inter_self]
  have hsplit := Finset.add_sum_erase Hub
    (fun x => (G.neighborFinset v ∩ G.neighborFinset x ∩ Iso).card) hv
  rw [hdiag] at hsplit
  have hfull := per_vertex_share_sum G Hub Iso hiso3 v
  omega

/-- **Generic low-value pigeonhole.**  If `∑_{p∈s} f p ≤ B`, the elements with `f p ≤ 1` number at
least `s.card − B/2`.  Stated multiplicatively. -/
theorem filter_le_one_card_ge {α : Type*} (s : Finset α) (f : α → ℕ) (B : ℕ)
    (h : ∑ p ∈ s, f p ≤ B) :
    2 * s.card ≤ 2 * (s.filter (fun p => f p ≤ 1)).card + B := by
  classical
  have hsplit : (s.filter (fun p => f p ≤ 1)).card
      + (s.filter (fun p => ¬ f p ≤ 1)).card = s.card :=
    Finset.card_filter_add_card_filter_not (s := s) (fun p => f p ≤ 1)
  have hlb : 2 * (s.filter (fun p => ¬ f p ≤ 1)).card
      ≤ ∑ p ∈ s.filter (fun p => ¬ f p ≤ 1), f p := by
    have hh := Finset.card_nsmul_le_sum (s.filter (fun p => ¬ f p ≤ 1)) f 2
      (fun p hp => by have := (Finset.mem_filter.mp hp).2; omega)
    simpa [smul_eq_mul, mul_comm] using hh
  have hsub : ∑ p ∈ s.filter (fun p => ¬ f p ≤ 1), f p ≤ ∑ p ∈ s, f p :=
    Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  omega

/-- **Off-diagonal sum as an iterated erase sum.** -/
theorem sum_offDiag_erase {α : Type*} [DecidableEq α] (s : Finset α) (f : α → α → ℕ) :
    ∑ p ∈ s.offDiag, f p.1 p.2 = ∑ a ∈ s, ∑ b ∈ s.erase a, f a b := by
  classical
  have hset : s.offDiag = (s ×ˢ s).filter (fun p => p.2 ≠ p.1) := by
    ext p
    simp only [Finset.mem_offDiag, Finset.mem_filter, Finset.mem_product]
    tauto
  rw [hset, Finset.sum_filter, Finset.sum_product]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  dsimp only
  rw [← Finset.sum_filter, Finset.filter_ne']

/-- **Adjacent ordered hub pairs equal the hub-incidence sum.**  With `∑_{w∈Hub}|N w ∩ Hub| ≤ k`,
the ordered off-diagonal adjacent pairs number at most `k`. -/
theorem hub_offDiag_adj_le (G : SimpleGraph (Fin 15)) (Hub : Finset (Fin 15)) (k : ℕ)
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
  have hrow : ∀ a : Fin 15, ∑ b ∈ Hub, (if G.Adj a b then 1 else 0)
      = (G.neighborFinset a ∩ Hub).card := by
    intro a
    rw [Finset.inter_comm, ← Finset.filter_mem_eq_inter, Finset.card_filter]
    exact Finset.sum_congr rfl (fun b _ => by simp only [G.mem_neighborFinset])
  rw [Finset.sum_congr rfl (fun a _ => hrow a)]
  exact hHubsum

/-- **Exact off-diagonal share sum.**  In any hub set where every isolated twin meets exactly three
hubs (`hiso3`), the ordered off-diagonal share double count is `∑_{(h₁,h₂)∈Hub.offDiag} share
= 6·|Iso|` (independent of `|Hub|`): each twin sits in `3·2 = 6` ordered hub pairs. -/
theorem hub_offDiag_share_sum (G : SimpleGraph (Fin 15)) (Hub Iso : Finset (Fin 15))
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3) :
    ∑ p ∈ Hub.offDiag, (G.neighborFinset p.1 ∩ G.neighborFinset p.2 ∩ Iso).card = 6 * Iso.card := by
  classical
  let F : Fin 15 → Fin 15 → ℕ :=
    fun a b => (G.neighborFinset a ∩ G.neighborFinset b ∩ Iso).card
  show ∑ p ∈ Hub.offDiag, F p.1 p.2 = 6 * Iso.card
  have hT : ∑ a ∈ Hub, (G.neighborFinset a ∩ Iso).card = 3 * Iso.card := by
    rw [cross_count G Hub Iso]
    calc ∑ t ∈ Iso, (G.neighborFinset t ∩ Hub).card
        = ∑ _t ∈ Iso, 3 := Finset.sum_congr rfl (fun t ht => hiso3 t ht)
      _ = 3 * Iso.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have hrow : ∀ a : Fin 15, ∑ b ∈ Hub, F a b = 3 * (G.neighborFinset a ∩ Iso).card := by
    intro a
    show ∑ b ∈ Hub, (G.neighborFinset a ∩ G.neighborFinset b ∩ Iso).card
      = 3 * (G.neighborFinset a ∩ Iso).card
    exact per_vertex_share_sum G Hub Iso hiso3 a
  have hprod : ∑ p ∈ Hub ×ˢ Hub, F p.1 p.2 = 9 * Iso.card := by
    rw [Finset.sum_product', Finset.sum_congr rfl (fun a _ => hrow a), ← Finset.mul_sum, hT]
    ring
  have hdiagval : ∀ a : Fin 15, F a a = (G.neighborFinset a ∩ Iso).card := by
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
theorem select_finish (G : SimpleGraph (Fin 15)) (Iso : Finset (Fin 15)) (h₁ h₂ : Fin 15)
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

/-- **Subset off-diagonal share double count.**  For any vertex subset `W`, the ordered
off-diagonal iso-share sum equals `∑_{t∈Iso} d_t (d_t − 1)` where `d_t = |N t ∩ W|` is the number
of `W`-vertices adjacent to the isolated twin `t`. -/
theorem subset_offDiag_share_eq (G : SimpleGraph (Fin 15)) (W Iso : Finset (Fin 15)) :
    ∑ p ∈ W.offDiag, (G.neighborFinset p.1 ∩ G.neighborFinset p.2 ∩ Iso).card
      = ∑ t ∈ Iso, (G.neighborFinset t ∩ W).card * ((G.neighborFinset t ∩ W).card - 1) := by
  classical
  have hcard : ∀ a b : Fin 15, (G.neighborFinset a ∩ G.neighborFinset b ∩ Iso).card
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
  set g : Fin 15 → ℕ := fun a => if G.Adj a t then 1 else 0 with hg
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

/-- **An iso-degree-`1` hub keeps a hub neighbour.**  With `|Hub| = 7`, `|Iso| = 6` disjoint, the
`15 − 13 = 2` outside vertices cannot absorb all of a degree-`4` hub's neighbours: a hub `h` of
iso-degree `1` has `|N h ∩ Hub| ≥ 4 − 1 − 2 = 1`. -/
theorem iso_one_hub_has_hub_neighbor (G : SimpleGraph (Fin 15)) (Hub Iso : Finset (Fin 15))
    (hHub7 : Hub.card = 7) (hIso6 : Iso.card = 6) (hdisj : Disjoint Hub Iso)
    (h : Fin 15) (hdeg4 : G.degree h = 4) (hiso1 : (G.neighborFinset h ∩ Iso).card = 1) :
    1 ≤ (G.neighborFinset h ∩ Hub).card := by
  classical
  have hcard4 : (G.neighborFinset h).card = 4 := by
    rw [G.card_neighborFinset_eq_degree, hdeg4]
  set R : Finset (Fin 15) := Finset.univ \ (Hub ∪ Iso) with hR
  have hHubIso : (Hub ∪ Iso).card = 13 := by
    rw [Finset.card_union_of_disjoint hdisj, hHub7, hIso6]
  have hRcard : R.card = 2 := by
    have hReq : R = (Hub ∪ Iso)ᶜ := by rw [hR, Finset.compl_eq_univ_sdiff]
    rw [hReq, Finset.card_compl, hHubIso, Fintype.card_fin]
  have hcover : G.neighborFinset h = (G.neighborFinset h ∩ Hub) ∪ (G.neighborFinset h ∩ Iso)
      ∪ (G.neighborFinset h ∩ R) := by
    rw [← Finset.inter_union_distrib_left, ← Finset.inter_union_distrib_left,
      show Hub ∪ Iso ∪ R = Finset.univ by
        rw [hR]; ext x; simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ,
          true_and, iff_true]; tauto,
      Finset.inter_univ]
  have hle1 : (G.neighborFinset h ∩ R).card ≤ 2 := by
    rw [← hRcard]; exact Finset.card_le_card Finset.inter_subset_right
  have hunion := hcover
  apply_fun Finset.card at hunion
  have hub1 : ((G.neighborFinset h ∩ Hub) ∪ (G.neighborFinset h ∩ Iso)
      ∪ (G.neighborFinset h ∩ R)).card
      ≤ (G.neighborFinset h ∩ Hub).card + (G.neighborFinset h ∩ Iso).card
        + (G.neighborFinset h ∩ R).card := by
    refine le_trans (Finset.card_union_le _ _) ?_
    exact Nat.add_le_add_right (Finset.card_union_le _ _) _
  rw [hcard4] at hunion
  omega

end N15

end ACMax
