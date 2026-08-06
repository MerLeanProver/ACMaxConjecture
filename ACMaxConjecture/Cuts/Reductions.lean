import ACMaxConjecture.Base
import ACMaxConjecture.Spectral.AlgConn
import ACMaxConjecture.Spectral.RayleighUpper

/-!
# Reduction lemmas for the algebraic-connectivity upper bound

The workhorse certificate for `algConn G ≤ 2`: if `G` has two **non-adjacent**
vertices `u, v` whose degrees sum to at most `4`, then the test vector
`x = e_u - e_v` (which is orthogonal to the all-ones vector) certifies
`algConn G ≤ 2` via the Courant–Fischer bridge, because
`xᵀ L x = deg u + deg v ≤ 4 = 2 · ‖x‖²`.

This single uniform lemma closes every *tight* graph (`λ₂ = 2`), since each such
graph has two non-adjacent degree-2 vertices.
-/

namespace ACMax

open scoped Classical
open Matrix

/-- If `G` has two non-adjacent vertices whose degrees sum to at most `4`, then the
algebraic connectivity of `G` is at most `2`. -/
theorem algConn_le_two_of_nonadj_pair {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (u v : V) (huv : u ≠ v) (hadj : ¬ G.Adj u v)
    (hdeg : G.degree u + G.degree v ≤ 4) :
    algConn G ≤ 2 := by
  classical
  set x : V → ℝ := fun w => (if w = u then 1 else 0) - (if w = v then 1 else 0) with hxdef
  have hxu : x u = 1 := by simp [hxdef, huv]
  have hxv : x v = -1 := by simp [hxdef, Ne.symm huv]
  have hx0 : ∑ i, x i = 0 := by
    simp only [hxdef, Finset.sum_sub_distrib]
    rw [Finset.sum_ite_eq', Finset.sum_ite_eq']
    simp
  have hsqpt : ∀ i, (x i) ^ 2 = (if i = u then (1 : ℝ) else 0) + (if i = v then 1 else 0) := by
    intro i
    by_cases hiu : i = u
    · subst hiu; simp [hxdef, huv]
    · by_cases hiv : i = v
      · subst hiv; simp [hxdef, hiu]
      · simp [hxdef, hiu, hiv]
  have hsq : ∑ i, (x i) ^ 2 = 2 := by
    simp only [hsqpt, Finset.sum_add_distrib]
    rw [Finset.sum_ite_eq', Finset.sum_ite_eq']
    norm_num
  have hdot : ∀ g : V → ℝ, dotProduct x g = g u - g v := by
    intro g
    simp only [dotProduct, hxdef, sub_mul, ite_mul, one_mul, zero_mul,
      Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hsu : ∑ w ∈ G.neighborFinset u, x w = 0 := by
    apply Finset.sum_eq_zero
    intro w hw
    rw [SimpleGraph.mem_neighborFinset] at hw
    have hwu : w ≠ u := hw.ne'
    have hwv : w ≠ v := by rintro rfl; exact hadj hw
    simp [hxdef, hwu, hwv]
  have hsv : ∑ w ∈ G.neighborFinset v, x w = 0 := by
    apply Finset.sum_eq_zero
    intro w hw
    rw [SimpleGraph.mem_neighborFinset] at hw
    have hwv : w ≠ v := hw.ne'
    have hwu : w ≠ u := by rintro rfl; exact hadj hw.symm
    simp [hxdef, hwu, hwv]
  have hquad : dotProduct x ((G.lapMatrix ℝ).mulVec x) = (G.degree u : ℝ) + G.degree v := by
    rw [hdot]
    rw [SimpleGraph.lapMatrix_mulVec_apply, SimpleGraph.lapMatrix_mulVec_apply]
    rw [hxu, hxv, hsu, hsv]
    ring
  have key := algConn_mul_sq_le G x hx0
  rw [hsq, hquad] at key
  have hdeg' : (G.degree u : ℝ) + G.degree v ≤ 4 := by exact_mod_cast hdeg
  linarith

end ACMax
