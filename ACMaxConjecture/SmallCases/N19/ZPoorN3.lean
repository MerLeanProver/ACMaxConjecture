import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N19.Core
import ACMaxConjecture.SmallCases.N19.RichCount
import ACMaxConjecture.SmallCases.N19.StarTriangleStruct

/-!
# The `r = 7`, `S = 15` rich iso-degree sequence and poor-incidence concentration (`n = 18`)

For the tight `e(M) = 1`, all-degree-`4`, `(|Hub|, |Iso|) = (11, 6)` profile with seven rich hubs
(`R = {h : 2 ≤ |N(h) ∩ Iso|}`, `|R| = 7`) and iso-incidence sum `S = ∑_R |N ∩ Iso| = 15`, the
six remaining iso-incidences live on the three poor hubs.
-/

namespace ACMax

open scoped Classical

namespace N19

/-- **Off-diagonal split of the rich pairs (LEAF).**  The ordered off-diagonal pairs of `R` split
into the non-adjacent (`D`) and adjacent (`Dadj`) parts, and their cardinalities sum to the
off-diagonal count `|R|² − |R|`.  This is the counting identity factored out of
`rich_count_le_seven_nineteen`. -/
theorem offdiag_eq_nineteen (G : SimpleGraph (Fin 19)) (R : Finset (Fin 19)) :
    (R.offDiag.filter (fun p => ¬G.Adj p.1 p.2)).card
      + (R.offDiag.filter (fun p => G.Adj p.1 p.2)).card
      = R.card * R.card - R.card := by
  classical
  rw [add_comm, Finset.card_filter_add_card_filter_not, Finset.offDiag_card]

end N19

end ACMax
