import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N20.Core
import ACMaxConjecture.SmallCases.N20.TwoHubSelect

/-!
# `n = 19`, `e(M) = 2` fat-centre corner `(9, 8, 38)` (`|D| = 10`, `|Hub| = 9`)

This file closes the `s = 2`, `|D| = 10` residual of `two_hub_config_twenty` at
`TwinCert20.lean:608` in which the nine hubs consist of one degree-`6` **fat centre** and eight
degree-`4` hubs (`∑_{Hub} deg = 38`), with `|Iso| = 8` `M`-isolated twins each meeting exactly three
hubs and `e(Hub) = 5` internal hub edges.

The counting used by `deg6_witness_select_twenty` only *ties* here (the master inequality reads
`24 = 24`), so it cannot close the corner.  We instead run a **fat-centre-aware off-diagonal
double count** on the eight degree-`4` hubs `W`:

* `∑_{p∈W.offDiag} |N p.1 ∩ N p.2 ∩ Iso| = ∑_{t∈Iso} d_t (d_t − 1)` where `d_t := |N t ∩ W| ≤ 3`
  (`subset_offDiag_share_eq_twenty`);
* the right side is `≤ 2·∑_t d_t = 2·∑_{W} isoDeg = 2·18 = 36` (each `d_t ≤ 3` gives
  `d_t(d_t−1) ≤ 2 d_t`), where `∑_{W} isoDeg = 18` because the fat centre absorbs the remaining
  `24 − 18 = 6` iso-incidences (`deg4_sum_le_twenty` forces `≤ 18`, and `isoDeg(fat) ≤ 6` forces
  `≥ 18`);
* assuming **no** good degree-`4` pair, every degree-`4` hub has iso-degree `≥ 2` (tightness of the
  threshold decomposition), so by the `min ≤ share + 1` refutation (`nogood_of_not_select_twenty`)
  every non-adjacent ordered degree-`4` pair has `share ≥ 1`, whence the left side is
  `≥ |W.offDiag| − #adjacent = 56 − 10 = 46` (adjacent ordered pairs number `≤ 2·e(Hub) = 10`).

`46 ≤ 36` is absurd, so a good non-adjacent degree-`4` pair with `≥ 2` private twins each exists —
delivering `TwoHubConfig` at the call site via `pairToTH`. -/

namespace ACMax

open scoped Classical

namespace N20

/-- **Adjacent ordered hub pairs equal the hub-incidence sum (`n = 19`).**  With
`∑_{w∈Hub}|N w ∩ Hub| ≤ k`, the ordered off-diagonal adjacent pairs number at most `k`. -/
theorem hub_offDiag_adj_le_twenty (G : SimpleGraph (Fin 20)) (Hub : Finset (Fin 20)) (k : ℕ)
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
  have hrow : ∀ a : Fin 20, ∑ b ∈ Hub, (if G.Adj a b then 1 else 0)
      = (G.neighborFinset a ∩ Hub).card := by
    intro a
    rw [Finset.inter_comm, ← Finset.filter_mem_eq_inter, Finset.card_filter]
    exact Finset.sum_congr rfl (fun b _ => by simp only [G.mem_neighborFinset])
  rw [Finset.sum_congr rfl (fun a _ => hrow a)]
  exact hHubsum

/-- **Subset off-diagonal share double count (`n = 19`).**  For any vertex subset `W`, the ordered
off-diagonal iso-share sum equals `∑_{t∈Iso} d_t (d_t − 1)` where `d_t = |N t ∩ W|`. -/
theorem subset_offDiag_share_eq_twenty (G : SimpleGraph (Fin 20)) (W Iso : Finset (Fin 20)) :
    ∑ p ∈ W.offDiag, (G.neighborFinset p.1 ∩ G.neighborFinset p.2 ∩ Iso).card
      = ∑ t ∈ Iso, (G.neighborFinset t ∩ W).card * ((G.neighborFinset t ∩ W).card - 1) := by
  classical
  have hcard : ∀ a b : Fin 20, (G.neighborFinset a ∩ G.neighborFinset b ∩ Iso).card
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
  set g : Fin 20 → ℕ := fun a => if G.Adj a t then 1 else 0 with hg
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

end N20

end ACMax
