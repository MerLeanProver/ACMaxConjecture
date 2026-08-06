import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# Non-backtracking walks

This file begins the Alon–Hoory–Linial walk-counting chain used by the final
SUM and EDGE Moore bounds.  The chain continues through `AHL.NBWalkCount`,
`AHL.NBWeighted`, the stationary marginals, and `AHL.AHLAmGm`.

This file lands the *non-backtracking walk* machinery the bound is counted over.  A walk is
**non-backtracking** when it never immediately reverses a step: `w.getVert (i + 2) ≠ w.getVert i`
for every valid `i`.  This is the exact `getVert` form the SQRT ray/ball rows consume.

## Contents

* **`IsNonBacktracking`** — the predicate and its length-`≤ 1` base cases.
* **`nb_extension_count`** — the `deg − 1` branching atom: the neighbours of `y` other than the
  arrived-from vertex `z` number `deg y − 1`.  This is the per-step count the future AM-GM-weighted
  AHL count consumes.

## Scope note

The degree-weighted lower bound on the *number* of non-backtracking walks and the weighted AM-GM
assembly into the Moore bound are the follow-up counting node; this file lands the foundation only.
-/

namespace ACMax

open SimpleGraph

/-- A walk is **non-backtracking** when it never immediately reverses a step: for every position
`i` with `i + 2 ≤ w.length`, the vertex two steps ahead differs from the current one.  (For `nil`
and single-edge walks the condition is vacuous.) -/
def IsNonBacktracking {V : Type*} {G : SimpleGraph V} {u v : V} (w : G.Walk u v) : Prop :=
  ∀ i : ℕ, i + 2 ≤ w.length → w.getVert (i + 2) ≠ w.getVert i

/-- Any walk of length at most `1` (in particular `nil` and a single edge) is non-backtracking:
there is no position `i` with `i + 2 ≤ w.length`. -/
theorem isNonBacktracking_of_length_le_one {V : Type*} {G : SimpleGraph V} {u v : V}
    {w : G.Walk u v} (hw : w.length ≤ 1) : IsNonBacktracking w := by
  intro i hi; omega

/-- A single-edge walk is non-backtracking. -/
theorem isNonBacktracking_cons_nil {V : Type*} {G : SimpleGraph V} {u v : V} (h : G.Adj u v) :
    IsNonBacktracking (Walk.cons h Walk.nil) :=
  isNonBacktracking_of_length_le_one (by simp)

/-- **The `deg − 1` branching atom.**  A non-backtracking walk arriving at `y` from `z` may continue
to any neighbour of `y` *except* `z`; these valid next-vertices are `neighborFinset y \ {z}` and
there are exactly `deg y − 1` of them.  This is the per-step count the AHL non-backtracking-walk
count is built on. -/
theorem nb_extension_count {V : Type*} (G : SimpleGraph V) [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] {y z : V} (h : G.Adj y z) :
    (G.neighborFinset y \ {z}).card = G.degree y - 1 := by
  classical
  have hz : z ∈ G.neighborFinset y := (G.mem_neighborFinset y z).mpr h
  rw [Finset.sdiff_singleton_eq_erase, Finset.card_erase_of_mem hz,
    G.card_neighborFinset_eq_degree]

end ACMax
