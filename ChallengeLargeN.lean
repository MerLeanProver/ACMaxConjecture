import Mathlib

/-!
# Comparator challenge — the ACMAX conjecture for large `n`

**Self-contained**: this file imports Mathlib and nothing else.  The definition of algebraic
connectivity is reproduced verbatim from `ACMaxConjecture/Spectral/AlgConn.lean`.

This is the large-`n` half of the conjecture, `n ≥ 123`, which the development proves by a
self-contained argument using none of the finite-range machinery.  See `ACMaxLargeN.lean`.
-/

namespace ACMax

open scoped Classical

/-- The **algebraic connectivity** of a finite simple graph: the second-smallest eigenvalue of its
Laplacian `L(G) = D(G) - A(G)`. -/
noncomputable def algConn {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) : ℝ :=
  (SimpleGraph.posSemidef_lapMatrix ℝ G).isHermitian.eigenvalues₀
    ⟨Fintype.card V - 2, Nat.sub_lt Fintype.card_pos (by norm_num)⟩

end ACMax

open ACMax
open scoped Classical

/-- **THE ACMAX CONJECTURE FOR `n ≥ 123`.**  `K_{2,n-2}` has algebraic connectivity exactly `2`,
and every simple graph on `n` vertices with exactly `2(n-2)` edges has algebraic connectivity at
most `2`. -/
theorem acmax_large_n_challenge :
    ∀ (n : ℕ) [Nonempty (Fin n)], 123 ≤ n →
      algConn (completeBipartiteGraph (Fin 2) (Fin (n - 2))) = 2 ∧
        ∀ G : SimpleGraph (Fin n), G.edgeFinset.card = 2 * (n - 2) → algConn G ≤ 2 := by
  sorry
