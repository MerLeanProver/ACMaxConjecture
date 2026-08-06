import ACMaxConjecture.Base
import ACMaxConjecture.Spectral.AlgConn
import ACMaxConjecture.Cuts.Reductions
import ACMaxConjecture.Spectral.AlgConnK2

/-!
# The ACMAX conjecture for `n = 5`

The upper bound follows from the workhorse reduction via a complement-graph count:
`Gᶜ` has `10 - 6 = 4` edges, `∑_w deg_{Gᶜ}(w) = 8`, so by Cauchy–Schwarz and
integrality `∑_w deg_{Gᶜ}(w)² ≥ ⌈64/5⌉ = 13`.  Since
`∑_{edges of Gᶜ} (deg_{Gᶜ}u + deg_{Gᶜ}v) = ∑_w deg_{Gᶜ}(w)² ≥ 13` over only `4`
edges, some edge of `Gᶜ` has degree sum `≥ 4`; its endpoints are non-adjacent in `G`
with `deg_G`-sum `= 8 - (deg_{Gᶜ}-sum) ≤ 4`, so `algConn_le_two_of_nonadj_pair`
applies.
-/

namespace ACMax

open scoped Classical

/-- Upper bound clause for `n = 5`. -/
theorem upperBound_five (G : SimpleGraph (Fin 5)) (hm : G.edgeFinset.card = 6) :
    algConn G ≤ 2 := by
  classical
  have hrow : ∀ (u : Fin 5) (c : ℕ), (∑ v, if Gᶜ.Adj u v then c else 0) = Gᶜ.degree u * c := by
    intro u c
    have hf : (Finset.univ.filter (fun v => Gᶜ.Adj u v)) = Gᶜ.neighborFinset u := by
      ext v
      simp [SimpleGraph.mem_neighborFinset]
    rw [← Finset.sum_filter, hf, Finset.sum_const, smul_eq_mul,
      SimpleGraph.card_neighborFinset_eq_degree]
  have hcol : ∀ (v : Fin 5) (c : ℕ), (∑ u, if Gᶜ.Adj u v then c else 0) = Gᶜ.degree v * c := by
    intro v c
    have hf : (Finset.univ.filter (fun u => Gᶜ.Adj u v)) = Gᶜ.neighborFinset v := by
      ext u
      simp [SimpleGraph.mem_neighborFinset, SimpleGraph.adj_comm]
    rw [← Finset.sum_filter, hf, Finset.sum_const, smul_eq_mul,
      SimpleGraph.card_neighborFinset_eq_degree]
  have hdeg4 : ∀ w : Fin 5, G.degree w + Gᶜ.degree w = 4 := by
    intro w
    have hlt : G.degree w < 5 := by
      have := G.degree_lt_card_verts w
      simpa using this
    rw [SimpleGraph.degree_compl]
    simp only [Fintype.card_fin]
    omega
  have hGsum : ∑ w, G.degree w = 12 := by
    rw [SimpleGraph.sum_degrees_eq_twice_card_edges, hm]
  have hGcsum : ∑ w, Gᶜ.degree w = 8 := by
    have h20 : ∑ w : Fin 5, (G.degree w + Gᶜ.degree w) = 20 := by
      rw [Finset.sum_congr rfl (fun w _ => hdeg4 w)]
      simp
    rw [Finset.sum_add_distrib, hGsum] at h20
    omega
  have hCS : 64 ≤ 5 * ∑ w, (Gᶜ.degree w) ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin 5)))
      (f := fun w => Gᶜ.degree w)
    simpa [Finset.card_univ, Fintype.card_fin, hGcsum] using h
  have hsq13 : 13 ≤ ∑ w, (Gᶜ.degree w) ^ 2 := by omega
  have hexists : ∃ u v : Fin 5, Gᶜ.Adj u v ∧ 4 ≤ Gᶜ.degree u + Gᶜ.degree v := by
    by_contra hcon
    push Not at hcon
    set T := ∑ u, ∑ v : Fin 5, if Gᶜ.Adj u v then Gᶜ.degree u + Gᶜ.degree v else 0 with hTdef
    have hT : T = 2 * ∑ w, (Gᶜ.degree w) ^ 2 := by
      rw [hTdef]
      have hsplit : ∀ u v : Fin 5,
          (if Gᶜ.Adj u v then Gᶜ.degree u + Gᶜ.degree v else 0)
            = (if Gᶜ.Adj u v then Gᶜ.degree u else 0)
              + (if Gᶜ.Adj u v then Gᶜ.degree v else 0) := by
        intro u v
        by_cases h : Gᶜ.Adj u v <;> simp [h]
      simp_rw [hsplit, Finset.sum_add_distrib]
      have hA : (∑ u, ∑ v : Fin 5, if Gᶜ.Adj u v then Gᶜ.degree u else 0)
          = ∑ w, (Gᶜ.degree w) ^ 2 := by
        apply Finset.sum_congr rfl
        intro u _
        rw [hrow u (Gᶜ.degree u), sq]
      have hB : (∑ u, ∑ v : Fin 5, if Gᶜ.Adj u v then Gᶜ.degree v else 0)
          = ∑ w, (Gᶜ.degree w) ^ 2 := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro v _
        rw [hcol v (Gᶜ.degree v), sq]
      rw [hA, hB]
      ring
    have hTle : T ≤ 24 := by
      rw [hTdef]
      calc (∑ u, ∑ v : Fin 5, if Gᶜ.Adj u v then Gᶜ.degree u + Gᶜ.degree v else 0)
          ≤ ∑ u, ∑ v : Fin 5, if Gᶜ.Adj u v then 3 else 0 := by
            apply Finset.sum_le_sum
            intro u _
            apply Finset.sum_le_sum
            intro v _
            split_ifs with h
            · have := hcon u v h
              omega
            · omega
        _ = ∑ u : Fin 5, Gᶜ.degree u * 3 := by simp_rw [hrow]
        _ = 24 := by rw [← Finset.sum_mul, hGcsum]; norm_num
    omega
  obtain ⟨u, v, hadj, hsum⟩ := hexists
  obtain ⟨huv, hnadj⟩ := (SimpleGraph.compl_adj G u v).mp hadj
  have hGdeg : G.degree u + G.degree v ≤ 4 := by
    have h1 := hdeg4 u
    have h2 := hdeg4 v
    omega
  exact algConn_le_two_of_nonadj_pair G u v huv hnadj hGdeg

/-- The full ACMAX conjecture for `n = 5` (`K_{2,3}` is the maximizer; bound `2`). -/
theorem acmax_conjecture_five :
    algConn (completeBipartiteGraph (Fin 2) (Fin 3)) = 2 ∧
      ∀ G : SimpleGraph (Fin 5), G.edgeFinset.card = 6 → algConn G ≤ 2 := by
  exact ⟨algConn_completeBipartite_two 5 (by norm_num), fun G hm => upperBound_five G hm⟩

end ACMax
