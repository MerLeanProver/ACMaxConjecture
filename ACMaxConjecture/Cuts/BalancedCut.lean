import ACMaxConjecture.Base
import ACMaxConjecture.Spectral.AlgConn
import ACMaxConjecture.Spectral.RayleighUpper
import ACMaxConjecture.Spectral.TestVector

/-!
# Balanced-cut certificate

If `A` is a balanced vertex set (`2|A| = |V|`) whose edge boundary to its complement
has at most `|V|/2` edges, then the `±1` vector `x = 𝟙_A − 𝟙_{Aᶜ}` is orthogonal to
`𝟙`, has squared norm `|V|`, and Laplacian quadratic form `4 · cut`, so
`xᵀ L x = 4·cut ≤ 2|V| = 2‖x‖²` and hence `algConn G ≤ 2`.

This is the certificate that handles the near-regular (`δ ≥ 3`) graphs, where local
degree-based vectors fail and a global balanced cut is needed.
-/

namespace ACMax

open scoped Classical
open Matrix

/-- A balanced bipartition whose cut has at most `|V|/2` edges certifies
`algConn G ≤ 2`.  Here the cut is counted as `∑_{a ∈ A} |N(a) \ A|`. -/
theorem algConn_le_two_of_balanced_cut {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (A : Finset V)
    (hbal : 2 * A.card = Fintype.card V)
    (hcut : 2 * (∑ a ∈ A, (G.neighborFinset a \ A).card) ≤ Fintype.card V) :
    algConn G ≤ 2 := by
  classical
  set N : ℕ := Fintype.card V with hN
  set cut : ℕ := ∑ a ∈ A, (G.neighborFinset a \ A).card with hcutdef
  set x : V → ℝ := fun v => if v ∈ A then 1 else -1 with hx
  -- Obligation 1: `x` is orthogonal to the all-ones vector.
  have hsum0 : ∑ i, x i = 0 := by
    have hval : ∀ i, x i = 2 * (if i ∈ A then (1 : ℝ) else 0) - 1 := by
      intro i; simp only [hx]; split <;> norm_num
    have hbalR : (2 : ℝ) * (A.card : ℝ) = (N : ℝ) := by exact_mod_cast hbal
    simp_rw [hval, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_boole,
      Finset.filter_univ_mem, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    rw [← hN]
    linarith [hbalR]
  -- Obligation 2: `x` is nonzero.
  have hne : ∃ i, x i ≠ 0 := by
    refine ⟨Classical.arbitrary V, ?_⟩
    simp only [hx]; split <;> norm_num
  -- Norm: every coordinate is `±1`, so `∑ (x i)^2 = N`.
  have hnorm : ∑ i, (x i) ^ 2 = (N : ℝ) := by
    have hsq : ∀ i, (x i) ^ 2 = 1 := by
      intro i; simp only [hx]; split <;> norm_num
    simp_rw [hsq, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, hN]
  -- Count lemma: ordered adjacent pairs `(i ∈ A, j ∉ A)` total `cut`.
  have hcount1 :
      (∑ i, ∑ j, if (G.Adj i j ∧ i ∈ A ∧ j ∉ A) then (1 : ℝ) else 0) = (cut : ℝ) := by
    have hinner : ∀ i, (∑ j, if (G.Adj i j ∧ i ∈ A ∧ j ∉ A) then (1 : ℝ) else 0) =
        if i ∈ A then ((G.neighborFinset i \ A).card : ℝ) else 0 := by
      intro i
      by_cases hi : i ∈ A
      · simp only [hi, true_and, if_true]
        have hfilt : (Finset.univ.filter fun j => G.Adj i j ∧ j ∉ A) =
            G.neighborFinset i \ A := by
          ext j; simp [SimpleGraph.mem_neighborFinset, Finset.mem_sdiff]
        rw [Finset.sum_boole, hfilt]
      · simp [hi]
    simp_rw [hinner]
    rw [Finset.sum_ite_mem, Finset.univ_inter, hcutdef]
    push_cast
    rfl
  -- Count lemma: ordered adjacent pairs `(i ∉ A, j ∈ A)` also total `cut`.
  have hcount2 :
      (∑ i, ∑ j, if (G.Adj i j ∧ i ∉ A ∧ j ∈ A) then (1 : ℝ) else 0) = (cut : ℝ) := by
    rw [← hcount1, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    refine if_congr ?_ rfl rfl
    rw [SimpleGraph.adj_comm]
    tauto
  -- Quadratic form equals `4 · cut`.
  have hquad : dotProduct x ((G.lapMatrix ℝ).mulVec x) = 4 * (cut : ℝ) := by
    rw [← Matrix.toLinearMap₂'_apply', SimpleGraph.lapMatrix_toLinearMap₂']
    have hterm : ∀ i j, (if G.Adj i j then (x i - x j) ^ 2 else 0) =
        4 * (if (G.Adj i j ∧ i ∈ A ∧ j ∉ A) then (1 : ℝ) else 0) +
        4 * (if (G.Adj i j ∧ i ∉ A ∧ j ∈ A) then (1 : ℝ) else 0) := by
      intro i j
      simp only [hx]
      by_cases hadj : G.Adj i j <;> by_cases hiA : i ∈ A <;> by_cases hjA : j ∈ A <;>
        simp [hadj, hiA, hjA] <;> norm_num
    simp_rw [hterm, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hcount1, hcount2]
    ring
  -- Conclude via the universal test-vector certificate.
  apply algConn_le_two_of_testvector G x hsum0 hne
  rw [hquad, hnorm]
  have hc : (2 : ℝ) * (cut : ℝ) ≤ (N : ℝ) := by exact_mod_cast hcut
  linarith

end ACMax
