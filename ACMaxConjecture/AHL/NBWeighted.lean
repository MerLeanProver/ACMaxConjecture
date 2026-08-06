import ACMaxConjecture.AHL.NBWalkCount
import Mathlib.Combinatorics.SimpleGraph.Walk.Operations
import Mathlib.Algebra.Order.Chebyshev

/-!
# The total non-backtracking walk count

This file defines **`nbTotalWalks`** — `mₖ`, the total number of length-`k` non-backtracking walks
in a graph, summed over all ordered start/end vertex pairs.  This is the quantity fed to the
Alon–Hoory–Linial irregular Moore bound chain; the walk-count and average-degree lemmas that consume
it live downstream (`AHL.AHLAmGm`, `Band.Sum`, and `Band.Edge`).
-/

namespace ACMax

open SimpleGraph Finset

variable {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableEq V] [DecidableRel G.Adj]

/-- `mₖ`: the total number of length-`k` non-backtracking walks, summed over all ordered
start/end pairs.  By definition this is `∑ x, ∑ v, ((G.finsetWalkLength k x v).filter …).card`. -/
def nbTotalWalks (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) : ℕ :=
  ∑ x : V, ∑ v : V, ((G.finsetWalkLength k x v).filter IsNonBacktracking).card

end ACMax
