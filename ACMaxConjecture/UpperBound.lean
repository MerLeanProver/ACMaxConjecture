import ACMaxConjecture.Band.Final

/-!
# Universal upper bound — PROVED (2026-07-14)

`algConn_le_two_of_card`: every simple graph on `Fin n` with exactly `2(n-2)`
edges has algebraic connectivity at most `2`.

This statement is Conjecture 1.5 of T. Kolokolnikov, *Maximizing algebraic
connectivity for certain families of graphs* (Linear Algebra and its
Applications, 2015; arXiv:1412.6147): the complete bipartite graph `K_{2,n-2}`
maximizes algebraic connectivity among all `n`-vertex graphs with `2(n-2)` edges.
It was an OPEN problem (verified computationally only for `n ≤ 13`); this library
now proves it in full, sorry-free and axiom-clean, for every `n ≥ 4`.  The proof
below is the second component of `ACMax.acmax_conjecture_general`
(`ACMaxConjecture/Band/Final.lean`), the endpoint of the general campaign:
the moat dispatch, the counting-row/starved-census
machinery, the island discharge, and the Alon–Hoory–Linial girth bound with its
SUM/EDGE Moore band discharge (kernel `decide` on `64 ≤ n ≤ 271`, certificate
bands to `1099`, import-free kills beyond).
-/

namespace ACMax

open scoped Classical

/-- **PROVED (Kolokolnikov, Conjecture 1.5, arXiv:1412.6147).** Every simple graph on
`Fin n` with exactly `2(n-2)` edges has algebraic connectivity at most `2`.  This is
the second component of `ACMax.acmax_conjecture_general` (`Band/Final.lean`),
re-assembled as the canonical root-level `ACMax.acmax_conjecture`. -/
theorem algConn_le_two_of_card (n : ℕ) (hn : 4 ≤ n) [Nonempty (Fin n)]
    (G : SimpleGraph (Fin n)) (hm : G.edgeFinset.card = 2 * (n - 2)) :
    algConn G ≤ 2 :=
  (acmax_conjecture_general n hn).2 G hm

-- HISTORY: this theorem was the library's original open `sorry` (2026-05 – 2026-07-14).  The
-- closure proceeded in stages: the finite cases `4 ≤ n ≤ 20` (now sharing the
-- `Cases12To20` dispatcher, with order-specific TwinCert structure); the moat and
-- starved-census dispatch; the island discharge
-- (`Islands/Dead.lean`, reducing everything to the starved
-- censuses on `55 ≤ n ≤ 1099`); and finally the Alon–Hoory–Linial band discharge
-- (`AHL/NBWalk` → `AHL/AHLAmGm`, the SUM/EDGE Moore forms, kernel `decide` on
-- `64 ≤ n ≤ 271`, certificate bands to `1099`), assembled hypothesis-free in
-- `Band/Final.lean` as `ACMax.acmax_conjecture_general` (the canonical
-- `ACMax.acmax_conjecture` in the root module re-assembles it).
end ACMax
