import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N14.Core

/-!
# Sharper share double counts for the `n = 14` two-hub iso-degree-`4` corner

An exact double-count leaf feeding the weak-hub residual of `two_hub_corner_b2`.

* `per_vertex_share_sum` — for any vertex `v`, `∑_{x∈Hub}|N v ∩ N x ∩ Iso| = 3·|N v ∩ Iso|`
  (each isolated twin `t ∈ N v ∩ Iso` lies in exactly `|N t ∩ Hub| = 3` of the shares).  The
  off-diagonal corollary `per_vertex_share_sum_erase` gives `∑_{x∈Hub\{v}} = 2·|N v ∩ Iso|`.
-/

namespace ACMax

open scoped Classical

namespace N14

/-- **Per-vertex share double count.**  For any `v`, summing the iso-shares `|N v ∩ N x ∩ Iso|`
over hubs `x ∈ Hub` counts each isolated twin `t ∈ N v ∩ Iso` once per hub adjacent to it, i.e.
`|N t ∩ Hub| = 3` times.  Hence the total is `3·|N v ∩ Iso|`. -/
theorem per_vertex_share_sum (G : SimpleGraph (Fin 14)) (Hub Iso : Finset (Fin 14))
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3) (v : Fin 14) :
    ∑ x ∈ Hub, (G.neighborFinset v ∩ G.neighborFinset x ∩ Iso).card
      = 3 * (G.neighborFinset v ∩ Iso).card := by
  classical
  have hset : ∀ x : Fin 14, (G.neighborFinset v ∩ G.neighborFinset x ∩ Iso).card
      = (G.neighborFinset x ∩ (G.neighborFinset v ∩ Iso)).card := by
    intro x
    rw [Finset.inter_comm (G.neighborFinset v) (G.neighborFinset x), Finset.inter_assoc]
  rw [Finset.sum_congr rfl (fun x _ => hset x),
    cross_count_fourteen G Hub (G.neighborFinset v ∩ Iso)]
  calc ∑ t ∈ (G.neighborFinset v ∩ Iso), (G.neighborFinset t ∩ Hub).card
      = ∑ _t ∈ (G.neighborFinset v ∩ Iso), 3 :=
        Finset.sum_congr rfl (fun t ht => hiso3 t (Finset.mem_inter.mp ht).2)
    _ = 3 * (G.neighborFinset v ∩ Iso).card := by
        rw [Finset.sum_const, smul_eq_mul, mul_comm]

/-- **Off-diagonal per-vertex share double count.**  For a hub `v ∈ Hub`, removing the diagonal
term `|N v ∩ N v ∩ Iso| = |N v ∩ Iso|` from `per_vertex_share_sum` leaves
`∑_{x∈Hub\{v}}|N v ∩ N x ∩ Iso| = 2·|N v ∩ Iso|`. -/
theorem per_vertex_share_sum_erase (G : SimpleGraph (Fin 14)) (Hub Iso : Finset (Fin 14))
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3) (v : Fin 14) (hv : v ∈ Hub) :
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
least `s.card − B/2`: each `p` with `f p ≥ 2` contributes `≥ 2` to the sum, so at most `B/2` of them
exist.  Stated multiplicatively to avoid division. -/
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

/-- **Off-diagonal sum as an iterated erase sum.**  `∑_{(a,b)∈s.offDiag} f a b = ∑_{a∈s}∑_{b∈s\{a}}
f a b`, the standard decomposition of the off-diagonal of `s ×ˢ s`. -/
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

/-- **At most four adjacent ordered hub pairs (fully proved).**  With at most two hub-edges
(`hHubsum : ∑_{w∈Hub}|N w ∩ Hub| ≤ 4`), the ordered off-diagonal adjacent pairs number at most `4`:
the count equals `∑_{a∈Hub}|N a ∩ Hub|`. -/
theorem hub_offDiag_adj_le_four (G : SimpleGraph (Fin 14)) (Hub : Finset (Fin 14))
    (hHubsum : ∑ w ∈ Hub, (G.neighborFinset w ∩ Hub).card ≤ 4) :
    (Hub.offDiag.filter (fun p => G.Adj p.1 p.2)).card ≤ 4 := by
  classical
  have hfilt : Hub.offDiag.filter (fun p => G.Adj p.1 p.2)
      = (Hub ×ˢ Hub).filter (fun p => G.Adj p.1 p.2) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_offDiag, Finset.mem_product]
    constructor
    · rintro ⟨⟨h1, h2, _⟩, hadj⟩; exact ⟨⟨h1, h2⟩, hadj⟩
    · rintro ⟨⟨h1, h2⟩, hadj⟩; exact ⟨⟨h1, h2, G.ne_of_adj hadj⟩, hadj⟩
  rw [hfilt, Finset.card_filter, Finset.sum_product]
  have hrow : ∀ a : Fin 14, ∑ b ∈ Hub, (if G.Adj a b then 1 else 0)
      = (G.neighborFinset a ∩ Hub).card := by
    intro a
    rw [Finset.inter_comm, ← Finset.filter_mem_eq_inter, Finset.card_filter]
    exact Finset.sum_congr rfl (fun b _ => by simp only [G.mem_neighborFinset])
  rw [Finset.sum_congr rfl (fun a _ => hrow a)]
  exact hHubsum

end N14

end ACMax
