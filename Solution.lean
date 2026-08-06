import ACMaxConjecture

/-!
The comparator solution: the challenge statement proved by the library's
`ACMax.acmax_conjecture`.
-/

open ACMax
open scoped Classical

theorem acmax_challenge :
    ∀ (n : ℕ) [Nonempty (Fin n)], 4 ≤ n →
      algConn (completeBipartiteGraph (Fin 2) (Fin (n - 2))) = 2 ∧
        ∀ G : SimpleGraph (Fin n), G.edgeFinset.card = 2 * (n - 2) → algConn G ≤ 2 :=
  fun n _ hn => ACMax.acmax_conjecture n hn
