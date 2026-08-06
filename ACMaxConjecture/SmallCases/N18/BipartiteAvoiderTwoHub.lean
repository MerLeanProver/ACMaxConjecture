import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.Certificates
import ACMaxConjecture.SmallCases.N18.Core

/-!
# Shared distinct-twin `TwoHubConfig` machinery for the `n = 18` bipartite-avoider residuals

The three `n = 18` hub-triangle bipartite-avoider residuals (`P₄` `|D| = 9` `|FF| = 4` `C₄`-plus-
apexes, the `C₅`/`K_{2,3}` five-avoider cherry corner, and the fat-star `|FF| = 6` `K_{3,3}` corner)
all share the same closing step: a triangle-free set of degree-`4` hubs, just above the good-`C₄` /
good-`K_{2,3}` thresholds, forces — via a shared-twin double count — two *non-adjacent* degree-`4`
hubs each carrying two **private** `M`-isolated twins, which assemble a `TwoHubConfig`
(`dense_two_hub_assemble`) and contradict `¬TwoHubConfig`.

This file collects the genuinely shared, configuration-independent counting lemma
`cherry_double_count` (the double count of pairwise shared twins as `∑_t (deg_S t)²`), reused by all
three corners.
-/

namespace ACMax

open scoped Classical

namespace N18

/-- **Shared-twin double count.**  For any hub set `S` and twin set `Iso`, the double sum over
ordered hub pairs of their shared-twin count equals the sum over twins of the square of the twin's
`S`-degree.  This is the bookkeeping identity behind every distinct-twin `TwoHubConfig` extraction. -/
theorem cherry_double_count (G : SimpleGraph (Fin 18)) (S Iso : Finset (Fin 18)) :
    ∑ h ∈ S, ∑ h' ∈ S, (G.neighborFinset h ∩ G.neighborFinset h' ∩ Iso).card
      = ∑ t ∈ Iso, (G.neighborFinset t ∩ S).card * (G.neighborFinset t ∩ S).card := by
  classical
  have hcard : ∀ h h' : Fin 18,
      (G.neighborFinset h ∩ G.neighborFinset h' ∩ Iso).card
        = ∑ t ∈ Iso, (if G.Adj h t ∧ G.Adj h' t then 1 else 0) := by
    intro h h'
    rw [Finset.inter_comm, ← Finset.filter_mem_eq_inter, Finset.card_filter]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    by_cases hh : G.Adj h t ∧ G.Adj h' t
    · simp only [Finset.mem_inter, G.mem_neighborFinset, hh.1, hh.2, and_self, if_pos]
    · rw [if_neg, if_neg hh]
      rw [Finset.mem_inter, G.mem_neighborFinset, G.mem_neighborFinset]
      exact hh
  have hSdeg : ∀ t : Fin 18, (G.neighborFinset t ∩ S).card
      = ∑ h ∈ S, (if G.Adj h t then 1 else 0) := by
    intro t
    rw [Finset.inter_comm, ← Finset.filter_mem_eq_inter, Finset.card_filter]
    exact Finset.sum_congr rfl (fun h _ => by simp only [G.mem_neighborFinset, SimpleGraph.adj_comm])
  simp_rw [hcard]
  have key : ∀ h ∈ S,
      (∑ h' ∈ S, ∑ t ∈ Iso, (if G.Adj h t ∧ G.Adj h' t then 1 else 0))
        = ∑ t ∈ Iso, ∑ h' ∈ S, (if G.Adj h t ∧ G.Adj h' t then 1 else 0) :=
    fun h _ => Finset.sum_comm
  rw [Finset.sum_congr rfl key, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [hSdeg, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl (fun h _ => ?_)
  refine Finset.sum_congr rfl (fun h' _ => ?_)
  by_cases h1 : G.Adj h t <;> by_cases h2 : G.Adj h' t <;> simp [h1, h2]

end N18

end ACMax
