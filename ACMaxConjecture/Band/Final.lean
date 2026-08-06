import ACMaxConjecture.Band.Assembly
import ACMaxConjecture.Band.Decide

/-!
# THE ACMAX CONJECTURE — the final splice

This file discharges the one staged hypothesis of the band-discharge assembly (`Band.Assembly`,
node B10) with the kernel-`decide` lemma (`Band.Decide`, node B8), producing the **hypothesis-free**
ACMAX conjecture
(Kolokolnikov, Conjecture 1.5, arXiv:1412.6147): for every `n ≥ 4`,

* `algConn (K_{2,n-2}) = 2`, and
* every simple graph on `Fin n` with exactly `2(n-2)` edges has `algConn ≤ 2`.

The two ingredients meet at the reducible `abbrev AhlBandLowDecide`; the `let`-bindings in
`ahl_band_low_decide`'s statement unfold definitionally into the abbrev's expanded form.
-/

namespace ACMax

open scoped Classical

/-- **The B8 kernel-decide lemma in the `AhlBandLowDecide` shape.**  The `let`-form conclusion of
`ahl_band_low_decide` zeta-reduces to the expanded form of the abbrev, so this is a definitional
repackaging. -/
theorem ahl_band_low : AhlBandLowDecide :=
  ahl_band_low_decide

/-- **THE ACMAX CONJECTURE (Kolokolnikov, Conjecture 1.5, arXiv:1412.6147), hypothesis-free.**
For every `n ≥ 4`: the complete bipartite graph `K_{2,n-2}` has algebraic connectivity exactly
`2`, and it maximizes algebraic connectivity among all simple graphs on `n` vertices with
`m = 2(n-2)` edges — every such graph `G` has `algConn G ≤ 2`. -/
theorem acmax_conjecture_general :
    ∀ (n : ℕ) [Nonempty (Fin n)], 4 ≤ n →
      algConn (completeBipartiteGraph (Fin 2) (Fin (n - 2))) = 2 ∧
        ∀ G : SimpleGraph (Fin n), G.edgeFinset.card = 2 * (n - 2) → algConn G ≤ 2 :=
  acmax_conjecture_of_decide ahl_band_low


end ACMax
