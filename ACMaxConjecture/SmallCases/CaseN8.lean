import ACMaxConjecture.Base
import ACMaxConjecture.Spectral.AlgConn
import ACMaxConjecture.Cuts.LowDegreeVertex
import ACMaxConjecture.Cuts.BalancedCut
import ACMaxConjecture.Cuts.Cubic8
import ACMaxConjecture.Spectral.AlgConnK2

/-!
# The ACMAX conjecture for `n = 8`

The first case where `δ ≥ 3` is possible.  Split: a vertex of degree `≤ 2` is handled
by `algConn_le_two_of_low_degree_vertex`; otherwise every degree is `≥ 3`, and since
`∑ deg = 2·12 = 24 = 3·8` this forces a **3-regular** graph, handled by the balanced
cut produced by `cubic8_balanced_cut_exists` together with
`algConn_le_two_of_balanced_cut`.
-/

namespace ACMax

open scoped Classical

/-- Upper bound clause for `n = 8`. -/
theorem upperBound_eight (G : SimpleGraph (Fin 8)) (hm : G.edgeFinset.card = 12) :
    algConn G ≤ 2 := by
  have hsum : ∑ v : Fin 8, G.degree v = 24 := by
    rw [SimpleGraph.sum_degrees_eq_twice_card_edges, hm]
  by_cases hlow : ∃ v : Fin 8, G.degree v ≤ 2
  · let : DecidableEq (Fin 8) := fun a b => Classical.propDecidable (a = b)
    obtain ⟨u, hdeg⟩ := hlow
    refine algConn_le_two_of_low_degree_vertex G u hdeg ?_
    rw [← Finset.card_pos, Finset.card_sdiff, Finset.inter_univ]
    have hcard : (insert u (G.neighborFinset u)).card ≤ 3 := by
      calc (insert u (G.neighborFinset u)).card
          ≤ (G.neighborFinset u).card + 1 := Finset.card_insert_le _ _
        _ = G.degree u + 1 := by rw [SimpleGraph.card_neighborFinset_eq_degree]
        _ ≤ 3 := by omega
    have huniv : (Finset.univ : Finset (Fin 8)).card = 8 := by simp
    omega
  · simp only [not_exists, not_le] at hlow
    have h3 : ∀ v : Fin 8, 3 ≤ G.degree v := fun v => by have := hlow v; omega
    have hreg : ∀ v : Fin 8, G.degree v = 3 := by
      intro w
      refine le_antisymm ?_ (h3 w)
      have hadd := Finset.add_sum_erase (Finset.univ : Finset (Fin 8))
        (fun v => G.degree v) (Finset.mem_univ w)
      have hge : (21 : ℕ) ≤ ∑ v ∈ Finset.univ.erase w, G.degree v := by
        calc (21 : ℕ) = ∑ _v ∈ Finset.univ.erase w, 3 := by
              rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ w)]
              simp
          _ ≤ ∑ v ∈ Finset.univ.erase w, G.degree v :=
              Finset.sum_le_sum (fun v _ => h3 v)
      omega
    let : DecidableEq (Fin 8) := instDecidableEqFin 8
    obtain ⟨A, hA4, hAcut⟩ := cubic8_balanced_cut_exists G hreg
    refine algConn_le_two_of_balanced_cut G A ?_ ?_
    · rw [hA4, Fintype.card_fin]
    · rw [Fintype.card_fin]
      convert hAcut using 2
      apply Finset.sum_congr rfl
      intro a _
      congr 1
      ext x
      simp [Finset.mem_sdiff]

/-- The full ACMAX conjecture for `n = 8` (`K_{2,6}` is the maximizer; bound `2`). -/
theorem acmax_conjecture_eight :
    algConn (completeBipartiteGraph (Fin 2) (Fin 6)) = 2 ∧
      ∀ G : SimpleGraph (Fin 8), G.edgeFinset.card = 12 → algConn G ≤ 2 := by
  exact ⟨algConn_completeBipartite_two 8 (by norm_num), fun G hm => upperBound_eight G hm⟩

end ACMax
