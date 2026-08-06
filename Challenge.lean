import Mathlib
import ACMaxConjecture.Spectral.AlgConn

/-!
The ACMAX conjecture (Kolokolnikov, Conjecture 1.5, arXiv:1412.6147) as a
comparator challenge: the statement only, with a `sorry`.  Imports are limited
to Mathlib and the definitional layer (`Spectral.AlgConn` defines `ACMax.algConn`).
-/

open ACMax
open scoped Classical

theorem acmax_challenge :
    ∀ (n : ℕ) [Nonempty (Fin n)], 4 ≤ n →
      algConn (completeBipartiteGraph (Fin 2) (Fin (n - 2))) = 2 ∧
        ∀ G : SimpleGraph (Fin n), G.edgeFinset.card = 2 * (n - 2) → algConn G ≤ 2 := by
  sorry
