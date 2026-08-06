import ACMaxConjecture.Base
import ACMaxConjecture.Spectral.AlgConn
import ACMaxConjecture.Cuts.LowDegreeVertex
import ACMaxConjecture.Spectral.AlgConnK2

/-!
# The ACMAX conjecture for `n = 6` and `n = 7`

Both follow uniformly from `algConn_le_two_of_low_degree_vertex`: since
`2 · (2(n-2)) < 3n` for `n ≤ 7`, the degree sum `2|E| < 3n` forces a vertex of
degree `≤ 2`, and its closed neighborhood omits at least `n - 3 ≥ 1` vertices.
-/

namespace ACMax

open scoped Classical

/-- Upper bound clause for `n = 6`. -/
theorem upperBound_six (G : SimpleGraph (Fin 6)) (hm : G.edgeFinset.card = 8) :
    algConn G ≤ 2 := by
  let : DecidableEq (Fin 6) := fun a b => Classical.propDecidable (a = b)
  have hsum : ∑ v : Fin 6, G.degree v = 16 := by
    rw [SimpleGraph.sum_degrees_eq_twice_card_edges, hm]
  have hex : ∃ u : Fin 6, G.degree u ≤ 2 := by
    by_contra h
    have h3 : ∀ v : Fin 6, 3 ≤ G.degree v := by
      intro v
      by_contra hv
      exact h ⟨v, by omega⟩
    have hge : (18 : ℕ) ≤ ∑ v : Fin 6, G.degree v := by
      calc (18 : ℕ) = ∑ _v : Fin 6, 3 := by simp
        _ ≤ ∑ v : Fin 6, G.degree v := Finset.sum_le_sum (fun v _ => h3 v)
    omega
  obtain ⟨u, hdeg⟩ := hex
  refine algConn_le_two_of_low_degree_vertex G u hdeg ?_
  rw [← Finset.card_pos, Finset.card_sdiff, Finset.inter_univ]
  have hcard : (insert u (G.neighborFinset u)).card ≤ 3 := by
    calc (insert u (G.neighborFinset u)).card
        ≤ (G.neighborFinset u).card + 1 := Finset.card_insert_le _ _
      _ = G.degree u + 1 := by rw [SimpleGraph.card_neighborFinset_eq_degree]
      _ ≤ 3 := by omega
  have huniv : (Finset.univ : Finset (Fin 6)).card = 6 := by simp
  omega

/-- The full ACMAX conjecture for `n = 6` (`K_{2,4}` is the maximizer; bound `2`). -/
theorem acmax_conjecture_six :
    algConn (completeBipartiteGraph (Fin 2) (Fin 4)) = 2 ∧
      ∀ G : SimpleGraph (Fin 6), G.edgeFinset.card = 8 → algConn G ≤ 2 := by
  exact ⟨algConn_completeBipartite_two 6 (by norm_num), fun G hm => upperBound_six G hm⟩

/-- Upper bound clause for `n = 7`. -/
theorem upperBound_seven (G : SimpleGraph (Fin 7)) (hm : G.edgeFinset.card = 10) :
    algConn G ≤ 2 := by
  let : DecidableEq (Fin 7) := fun a b => Classical.propDecidable (a = b)
  have hsum : ∑ v : Fin 7, G.degree v = 20 := by
    rw [SimpleGraph.sum_degrees_eq_twice_card_edges, hm]
  have hex : ∃ u : Fin 7, G.degree u ≤ 2 := by
    by_contra h
    have h3 : ∀ v : Fin 7, 3 ≤ G.degree v := by
      intro v
      by_contra hv
      exact h ⟨v, by omega⟩
    have hge : (21 : ℕ) ≤ ∑ v : Fin 7, G.degree v := by
      calc (21 : ℕ) = ∑ _v : Fin 7, 3 := by simp
        _ ≤ ∑ v : Fin 7, G.degree v := Finset.sum_le_sum (fun v _ => h3 v)
    omega
  obtain ⟨u, hdeg⟩ := hex
  refine algConn_le_two_of_low_degree_vertex G u hdeg ?_
  rw [← Finset.card_pos, Finset.card_sdiff, Finset.inter_univ]
  have hcard : (insert u (G.neighborFinset u)).card ≤ 3 := by
    calc (insert u (G.neighborFinset u)).card
        ≤ (G.neighborFinset u).card + 1 := Finset.card_insert_le _ _
      _ = G.degree u + 1 := by rw [SimpleGraph.card_neighborFinset_eq_degree]
      _ ≤ 3 := by omega
  have huniv : (Finset.univ : Finset (Fin 7)).card = 7 := by simp
  omega

/-- The full ACMAX conjecture for `n = 7` (`K_{2,5}` is the maximizer; bound `2`). -/
theorem acmax_conjecture_seven :
    algConn (completeBipartiteGraph (Fin 2) (Fin 5)) = 2 ∧
      ∀ G : SimpleGraph (Fin 7), G.edgeFinset.card = 10 → algConn G ≤ 2 := by
  exact ⟨algConn_completeBipartite_two 7 (by norm_num), fun G hm => upperBound_seven G hm⟩

end ACMax
