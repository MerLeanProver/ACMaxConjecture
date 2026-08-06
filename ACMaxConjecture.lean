import ACMaxConjecture.UpperBound

/-!
# ACMAX conjecture (algebraic-connectivity maximizer for `m = 2(n-2)`)

For `n ≥ 4`, among all simple graphs on `n` vertices with exactly `2(n-2)` edges,
the algebraic connectivity is at most `2`, and this bound is attained by the complete
bipartite graph `K_{2,n-2}` (whose algebraic connectivity equals `2`).

The statement decomposes into the equality clause (`algConn_completeBipartite_two`)
and the universal upper-bound clause (`algConn_le_two_of_card`).
-/

namespace ACMax

open scoped Classical

/-- **ACMAX conjecture.** For `n ≥ 4`, the complete bipartite graph `K_{2,n-2}` has
algebraic connectivity `2`, and every simple graph on `n` vertices with exactly
`2(n-2)` edges has algebraic connectivity at most `2`. -/
theorem acmax_conjecture (n : ℕ) (hn : 4 ≤ n) [Nonempty (Fin n)] :
    algConn (completeBipartiteGraph (Fin 2) (Fin (n - 2))) = 2 ∧
      ∀ G : SimpleGraph (Fin n), G.edgeFinset.card = 2 * (n - 2) → algConn G ≤ 2 :=
  ⟨algConn_completeBipartite_two n hn,
    fun G hm => algConn_le_two_of_card n hn G hm⟩

end ACMax
