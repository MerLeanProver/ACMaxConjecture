import ACMaxConjecture.Base

/-!
# Residual counting identities

Two elementary identities used by the general counting argument:

* `cross_count` double-counts incidences between two vertex sets;
* `residual_degree_sum` evaluates the degree sum when the graph has `2(n - 2)` edges.
-/

namespace ACMax

open scoped Classical

/-- Incidences from `X` to `Y` equal incidences from `Y` to `X`. -/
theorem cross_count {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (X Y : Finset V) :
    ∑ v ∈ X, (G.neighborFinset v ∩ Y).card =
      ∑ w ∈ Y, (G.neighborFinset w ∩ X).card := by
  have hL : ∀ v : V, (G.neighborFinset v ∩ Y).card =
      ∑ w ∈ Y, if G.Adj v w then 1 else 0 := by
    intro v
    rw [Finset.inter_comm, ← Finset.filter_mem_eq_inter, Finset.card_filter]
    exact Finset.sum_congr rfl fun w _ => by
      simp only [G.mem_neighborFinset]
  have hR : ∀ w : V, (G.neighborFinset w ∩ X).card =
      ∑ v ∈ X, if G.Adj v w then 1 else 0 := by
    intro w
    rw [Finset.inter_comm, ← Finset.filter_mem_eq_inter, Finset.card_filter]
    exact Finset.sum_congr rfl fun v _ => by
      simp only [G.mem_neighborFinset, SimpleGraph.adj_comm]
  simp_rw [hL, hR]
  exact Finset.sum_comm

/-- A graph on `n ≥ 2` vertices with `2(n - 2)` edges has total degree `4n - 8`. -/
theorem residual_degree_sum (n : ℕ) (hn : 2 ≤ n) (G : SimpleGraph (Fin n))
    (hm : G.edgeFinset.card = 2 * (n - 2)) :
    ∑ v : Fin n, G.degree v = 4 * n - 8 := by
  rw [SimpleGraph.sum_degrees_eq_twice_card_edges, hm]
  omega

end ACMax
