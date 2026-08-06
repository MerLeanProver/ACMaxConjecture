import ACMaxConjecture.Counting.ResidualInterface
import ACMaxConjecture.Counting.SqrtGirth

/-!
# IB1: the twin-rooted level-sharp 3-ball count

The kill of the seven islands needs a *sharp* bound on
`|closeSet G t| = |B(t, 3)|` for a heavy-free deg-3 twin `t`.  The crude Moore bound
`card_closeSet_le` gives `1 + D + D² + D³ = 85` at `D = 4`, which is far too weak
(`> 63 ≥ n`).  This file lands the honest level-charge bound

  `|closeSet G t| ≤ 40 + X`,   `X = excessX n G`,

matching the pure `{3, 4}` count `1 + 3 + 9 + 27 = 40` plus a single copy of the total
degree excess.

## The mechanism (NO girth, NO injectivity)

Working with the BFS distance levels `Lᵢ = {v | dist t v = i}`, every non-root level
vertex has at least one neighbour one level *down* (the penultimate vertex of a geodesic —
`exists_dist_pred_nbr`).  This unconditional parent edge is the whole engine:

* **`children_le`** — a level-`i` vertex (`i ≥ 1`) sends at most `deg − 1` edges *up* to
  level `i + 1`, since one of its edges is spent on the parent at level `i − 1`.
* **`level_growth_le`** — `|L_{i+1}| ≤ Σ_{v ∈ Lᵢ}(deg v − 1)`: each child lands in the
  `biUnion` of the up-neighbourhoods of `Lᵢ`, so `card_biUnion_le` and `children_le`
  telescope.  No uniqueness of the parent is needed — the inequality only over-counts.

The excess is absorbed by `level_sum_bound` (`Σ_{v ∈ S}(deg v − 1) ≤ 3|S| + X`).  With `t`
heavy-free its three neighbours are all degree `≤ 4`, so `|L₂| ≤ 9` carries **no** excess,
and the single copy of `X` enters only at `|L₃| ≤ 27 + X`.  The distance ball
`closeSet G t` is contained in `{t} ∪ L₁ ∪ L₂ ∪ L₃` (`dist_le_three_of_mem_closeSet`
plus reachability), giving `1 + 3 + 9 + (27 + X) = 40 + X`.
-/

namespace ACMax

open scoped Classical
open SimpleGraph Finset

variable {n : ℕ}

/-- **Parent edge (girth-free).**  A vertex `v` at distance `i + 1` from `x` has a
neighbour `w` at distance `i` — the penultimate vertex of a shortest `x → v` walk. -/
theorem exists_dist_pred_nbr (G : SimpleGraph (Fin n)) (x v : Fin n) (i : ℕ)
    (hv : G.dist x v = i + 1) : ∃ w, G.Adj v w ∧ G.dist x w = i := by
  classical
  have hrxv : G.Reachable x v := Reachable.of_dist_ne_zero (by rw [hv]; omega)
  obtain ⟨g, -, hglen⟩ := hrxv.exists_path_of_dist
  have hi_lt : i < g.length := by rw [hglen, hv]; omega
  have hadj_uv : G.Adj (g.getVert i) v := by
    have h := g.adj_getVert_succ hi_lt
    rwa [show i + 1 = g.length by rw [hglen, hv], g.getVert_length] at h
  have hle : G.dist x (g.getVert i) ≤ i := by
    have hw := SimpleGraph.dist_le (g.take i)
    rw [Walk.take_length, show i ⊓ g.length = i by rw [hglen, hv]; omega] at hw
    exact hw
  have hge : i ≤ G.dist x (g.getVert i) := by
    have hru : G.Reachable x (g.getVert i) := (g.take i).reachable
    have htri := hru.dist_triangle_left v
    rw [hv, SimpleGraph.dist_eq_one_iff_adj.mpr hadj_uv] at htri
    omega
  exact ⟨g.getVert i, hadj_uv.symm, le_antisymm hle hge⟩

/-- **Children bound (girth-free).**  A level-`i` vertex `v` (`1 ≤ i`) sends at most
`deg v − 1` edges up to level `i + 1`: one of its neighbours is a parent at level
`i − 1`, so it is excluded from the up-neighbourhood. -/
theorem children_le (G : SimpleGraph (Fin n)) (x v : Fin n) (i : ℕ) (hi : 1 ≤ i)
    (hv : G.dist x v = i) :
    ((G.neighborFinset v).filter (fun w => G.dist x w = i + 1)).card ≤ G.degree v - 1 := by
  classical
  obtain ⟨p, hadj, hp⟩ := exists_dist_pred_nbr G x v (i - 1) (by rw [hv]; omega)
  have hpN : p ∈ G.neighborFinset v := by rw [SimpleGraph.mem_neighborFinset]; exact hadj
  have hsub : (G.neighborFinset v).filter (fun w => G.dist x w = i + 1)
      ⊆ (G.neighborFinset v).erase p := by
    intro w hw
    rw [Finset.mem_filter] at hw
    obtain ⟨hwN, hwd⟩ := hw
    rw [Finset.mem_erase]
    refine ⟨?_, hwN⟩
    rintro rfl
    omega
  calc ((G.neighborFinset v).filter (fun w => G.dist x w = i + 1)).card
      ≤ ((G.neighborFinset v).erase p).card := Finset.card_le_card hsub
    _ = G.degree v - 1 := by
        rw [Finset.card_erase_of_mem hpN, SimpleGraph.card_neighborFinset_eq_degree]

/-- **Level growth (girth-free).**  `|L_{i+1}| ≤ Σ_{v ∈ Lᵢ}(deg v − 1)` for `1 ≤ i`:
each level-`(i+1)` vertex lies in the up-neighbourhood of its parent, so the level is
covered by the `biUnion` of the up-neighbourhoods of `Lᵢ`. -/
theorem level_growth_le (G : SimpleGraph (Fin n)) (x : Fin n) (i : ℕ) (hi : 1 ≤ i) :
    (univ.filter (fun v => G.dist x v = i + 1)).card
      ≤ ∑ v ∈ univ.filter (fun v => G.dist x v = i), (G.degree v - 1) := by
  classical
  set A := univ.filter (fun v => G.dist x v = i) with hA
  set B := univ.filter (fun v => G.dist x v = i + 1) with hB
  have hsub : B ⊆ A.biUnion
      (fun v => (G.neighborFinset v).filter (fun w => G.dist x w = i + 1)) := by
    intro w hw
    simp only [hB, Finset.mem_filter, Finset.mem_univ, true_and] at hw
    obtain ⟨v, hadj, hvd⟩ := exists_dist_pred_nbr G x w i hw
    rw [Finset.mem_biUnion]
    refine ⟨v, ?_, ?_⟩
    · simp only [hA, Finset.mem_filter, Finset.mem_univ, true_and]; exact hvd
    · rw [Finset.mem_filter, SimpleGraph.mem_neighborFinset]; exact ⟨hadj.symm, hw⟩
  calc B.card
      ≤ (A.biUnion
          (fun v => (G.neighborFinset v).filter (fun w => G.dist x w = i + 1))).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ v ∈ A, ((G.neighborFinset v).filter (fun w => G.dist x w = i + 1)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ v ∈ A, (G.degree v - 1) :=
        Finset.sum_le_sum (fun v hv => by
          simp only [hA, Finset.mem_filter, Finset.mem_univ, true_and] at hv
          exact children_le G x v i hi hv)

/-- **Excess sum bound.**  `Σ_{v ∈ S}(deg v − 4) ≤ X`: only heavy vertices (`deg ≥ 5`)
contribute, and `S`'s heavies inject into all heavies. -/
theorem excess_sub_sum_le (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) :
    (∑ v ∈ S, (G.degree v - 4)) ≤ excessX n G := by
  rw [excessX]
  have heq : ∑ v ∈ S, (G.degree v - 4)
      = ∑ v ∈ S.filter (fun v => 5 ≤ G.degree v), (G.degree v - 4) := by
    refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
    intro v hv hnv
    simp only [Finset.mem_filter, not_and, not_le] at hnv
    have hlt : G.degree v < 5 := hnv hv
    omega
  rw [heq]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.filter_subset_filter _ (Finset.subset_univ S)) (fun _ _ _ => Nat.zero_le _)

/-- **Weighted level bound.**  `Σ_{v ∈ S}(deg v − 1) ≤ 3|S| + X`: split
`deg v − 1 ≤ 3 + (deg v − 4)` and absorb the excess. -/
theorem level_sum_bound (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) :
    (∑ v ∈ S, (G.degree v - 1)) ≤ 3 * S.card + excessX n G := by
  calc (∑ v ∈ S, (G.degree v - 1))
      ≤ ∑ v ∈ S, (3 + (G.degree v - 4)) := Finset.sum_le_sum (fun v _ => by omega)
    _ = 3 * S.card + ∑ v ∈ S, (G.degree v - 4) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, Nat.mul_comm]
    _ ≤ 3 * S.card + excessX n G := by
        have := excess_sub_sum_le G S; omega

/-- **Reachability of the ball.**  Every vertex of `closeSet G t` is reachable from `t`
(within three adjacency steps by construction). -/
theorem reachable_of_mem_closeSet (G : SimpleGraph (Fin n)) (t v : Fin n)
    (hv : v ∈ closeSet G t) : G.Reachable t v := by
  unfold closeSet at hv
  rw [Finset.mem_insert] at hv
  rcases hv with rfl | hv
  · exact Reachable.refl _
  rw [Finset.mem_union] at hv
  rcases hv with hAB | hC
  · rw [Finset.mem_union] at hAB
    rcases hAB with hAdj | hB
    · rw [SimpleGraph.mem_neighborFinset] at hAdj
      exact hAdj.reachable
    · rw [Finset.mem_biUnion] at hB
      obtain ⟨w, hw, hvw⟩ := hB
      rw [SimpleGraph.mem_neighborFinset] at hw hvw
      exact hw.reachable.trans hvw.reachable
  · rw [Finset.mem_biUnion] at hC
    obtain ⟨y, hy, hvy⟩ := hC
    rw [Finset.mem_biUnion] at hy
    obtain ⟨w, hw, hyw⟩ := hy
    rw [SimpleGraph.mem_neighborFinset] at hw hyw hvy
    exact (hw.reachable.trans hyw.reachable).trans hvy.reachable

/-- **IB1: the twin-rooted level-sharp 3-ball count.**  A deg-3 root `t` all of whose
neighbours are light (`deg ≤ 4`, i.e. a heavy-free twin) has

  `|closeSet G t| ≤ 40 + X`,   `X = excessX n G`.

Level charge: `|L₁| = 3`, `|L₂| ≤ 9` (the three light neighbours carry no excess), and
`|L₃| ≤ 27 + X`; the distance ball is covered by `{t} ∪ L₁ ∪ L₂ ∪ L₃`. -/
theorem twin_ball_le (G : SimpleGraph (Fin n)) (t : Fin n) (ht : G.degree t = 3)
    (hnbr : ∀ w, G.Adj t w → G.degree w ≤ 4) :
    (closeSet G t).card ≤ 40 + excessX n G := by
  classical
  have hL1 : (univ.filter (fun v => G.dist t v = 1)).card = 3 := by
    have heq : univ.filter (fun v => G.dist t v = 1) = G.neighborFinset t := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, SimpleGraph.mem_neighborFinset]
      exact SimpleGraph.dist_eq_one_iff_adj
    rw [heq, SimpleGraph.card_neighborFinset_eq_degree, ht]
  have hL2 : (univ.filter (fun v => G.dist t v = 2)).card ≤ 9 := by
    have hg : (univ.filter (fun v => G.dist t v = 2)).card
        ≤ ∑ v ∈ univ.filter (fun v => G.dist t v = 1), (G.degree v - 1) :=
      level_growth_le G t 1 (le_refl 1)
    have hb : ∑ v ∈ univ.filter (fun v => G.dist t v = 1), (G.degree v - 1) ≤ 9 := by
      calc ∑ v ∈ univ.filter (fun v => G.dist t v = 1), (G.degree v - 1)
          ≤ ∑ _v ∈ univ.filter (fun v => G.dist t v = 1), 3 :=
            Finset.sum_le_sum (fun v hv => by
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
              have := hnbr v (SimpleGraph.dist_eq_one_iff_adj.mp hv); omega)
        _ = 3 * (univ.filter (fun v => G.dist t v = 1)).card := by
            rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
        _ = 9 := by rw [hL1]
    exact le_trans hg hb
  have hL3 : (univ.filter (fun v => G.dist t v = 3)).card ≤ 27 + excessX n G := by
    have hg : (univ.filter (fun v => G.dist t v = 3)).card
        ≤ ∑ v ∈ univ.filter (fun v => G.dist t v = 2), (G.degree v - 1) :=
      level_growth_le G t 2 (by norm_num)
    have hb := level_sum_bound G (univ.filter (fun v => G.dist t v = 2))
    omega
  have hcover : closeSet G t ⊆ insert t ((univ.filter (fun v => G.dist t v = 1))
      ∪ (univ.filter (fun v => G.dist t v = 2)) ∪ (univ.filter (fun v => G.dist t v = 3))) := by
    intro v hv
    by_cases hvt : v = t
    · rw [hvt]; exact Finset.mem_insert_self _ _
    · have hd3 : G.dist t v ≤ 3 := dist_le_three_of_mem_closeSet G t v hv
      have hreach : G.Reachable t v := reachable_of_mem_closeSet G t v hv
      have hd0 : G.dist t v ≠ 0 := fun h0 => hvt ((hreach.dist_eq_zero_iff.mp h0).symm)
      have hcase : G.dist t v = 1 ∨ G.dist t v = 2 ∨ G.dist t v = 3 := by omega
      refine Finset.mem_insert_of_mem ?_
      rcases hcase with h | h | h
      · exact Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_filter.mpr ⟨Finset.mem_univ v, h⟩))
      · exact Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨Finset.mem_univ v, h⟩))
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ v, h⟩)
  have hu1 := Finset.card_union_le
    ((univ.filter (fun v => G.dist t v = 1)) ∪ (univ.filter (fun v => G.dist t v = 2)))
    (univ.filter (fun v => G.dist t v = 3))
  have hu2 := Finset.card_union_le
    (univ.filter (fun v => G.dist t v = 1)) (univ.filter (fun v => G.dist t v = 2))
  have hins := Finset.card_insert_le t ((univ.filter (fun v => G.dist t v = 1))
    ∪ (univ.filter (fun v => G.dist t v = 2)) ∪ (univ.filter (fun v => G.dist t v = 3)))
  have hcard := Finset.card_le_card hcover
  omega

end ACMax
