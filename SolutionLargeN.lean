import ACMaxLargeN

/-!
# Comparator solution — the ACMAX conjecture for large `n`

The challenge statement of `ChallengeLargeN.lean`, proved by the development's
`ACMax.acmax_conjecture_large_n`.  Its dependency cone is the single file `ACMaxLargeN.lean`
over Mathlib: no per-order case analysis and no kernel `decide` bands.
-/

open ACMax
open scoped Classical

theorem acmax_large_n_challenge :
    ∀ (n : ℕ) [Nonempty (Fin n)], 123 ≤ n →
      algConn (completeBipartiteGraph (Fin 2) (Fin (n - 2))) = 2 ∧
        ∀ G : SimpleGraph (Fin n), G.edgeFinset.card = 2 * (n - 2) → algConn G ≤ 2 :=
  fun n _ hn => ACMax.acmax_conjecture_large_n n hn
