import ACMaxConjecture.Base
import ACMaxConjecture.Spectral.TestVector


/-!
# The weighted double-star certificate

`algConn_le_two_of_weighted_double_star` is the reusable spectral certificate
for a pair of non-adjacent vertices with disjoint neighbourhoods.  Nonnegative
weights on the two stars define a balanced test vector; a single explicit
quadratic inequality then proves `algConn G ≤ 2`.

This is the only declaration from the former far-pair collection needed by the
final ACMAX proof.  Its slot specialization lives in `Counting.CompactCell`.
-/

namespace ACMax

open scoped Classical
open Matrix

variable {V : Type*} [Fintype V]

/-! ## The weighted double-star master certificate -/

set_option maxHeartbeats 1600000 in
/-- **The weighted double-star master certificate.**  Two vertices `u ≠ v`, not
adjacent, with disjoint neighbourhoods, and nonnegative weights (`au` on `u`,
`p w` on `w ∈ N(u)`; `av`, `q` on the `v`-side, negated) that are balanced
(`au + Σ p = av + Σ q`) and satisfy the worst-case quadratic-form bound: then
`algConn G ≤ 2`.  Cross edges `N(u)–N(v)` are allowed and cost `(p w + q w')²`;
each further edge at `w ∈ N(u)` (to anywhere except `u` and `N(v)`) is charged
`(p w)²` per endpoint slot. -/
theorem algConn_le_two_of_weighted_double_star [Nonempty V]
    (G : SimpleGraph V) (u v : V) (au av : ℝ) (p q : V → ℝ)
    (hne : u ≠ v) (huv : ¬G.Adj u v)
    (hcap : ∀ w : V, ¬(G.Adj u w ∧ G.Adj v w))
    (hau : 0 < au)
    (hp : ∀ w ∈ G.neighborFinset u, 0 ≤ p w)
    (hq : ∀ w ∈ G.neighborFinset v, 0 ≤ q w)
    (hbal : au + ∑ w ∈ G.neighborFinset u, p w
          = av + ∑ w ∈ G.neighborFinset v, q w)
    (hQ : (∑ w ∈ G.neighborFinset u, (au - p w) ^ 2)
        + (∑ w ∈ G.neighborFinset v, (av - q w) ^ 2)
        + (∑ w ∈ G.neighborFinset u, ∑ w' ∈ G.neighborFinset v,
            (if G.Adj w w' then (p w + q w') ^ 2 else 0))
        + (∑ w ∈ G.neighborFinset u,
            ((G.neighborFinset w \ insert u (G.neighborFinset v)).card : ℝ)
              * p w ^ 2)
        + (∑ w ∈ G.neighborFinset v,
            ((G.neighborFinset w \ insert v (G.neighborFinset u)).card : ℝ)
              * q w ^ 2)
        ≤ 2 * (au ^ 2 + (∑ w ∈ G.neighborFinset u, p w ^ 2)
             + (av ^ 2 + ∑ w ∈ G.neighborFinset v, q w ^ 2))) :
    algConn G ≤ 2 := by
  classical
  set A := G.neighborFinset u with hA
  set B := G.neighborFinset v with hB
  -- Membership bookkeeping.
  have hmemA : ∀ w : V, w ∈ A ↔ G.Adj u w := fun w => G.mem_neighborFinset u w
  have hmemB : ∀ w : V, w ∈ B ↔ G.Adj v w := fun w => G.mem_neighborFinset v w
  have huA : u ∉ A := fun h => G.irrefl ((hmemA u).mp h)
  have hvA : v ∉ A := fun h => huv ((hmemA v).mp h)
  have huB : u ∉ B := fun h => huv (G.adj_symm ((hmemB u).mp h))
  have hvB : v ∉ B := fun h => G.irrefl ((hmemB v).mp h)
  have hAB : ∀ w : V, w ∈ A → w ∉ B :=
    fun w hwA hwB => hcap w ⟨(hmemA w).mp hwA, (hmemB w).mp hwB⟩
  -- The test vector.
  set x : V → ℝ := fun w =>
    ((if w = u then au else 0) + (if w ∈ A then p w else 0))
      - ((if w = v then av else 0) + (if w ∈ B then q w else 0)) with hxdef
  have hxu : x u = au := by simp [hxdef, hne, huA, huB]
  have hxv : x v = -av := by simp [hxdef, hne.symm, hvA, hvB]
  have hxA : ∀ w ∈ A, x w = p w := by
    intro w hw
    have h1 : w ≠ u := fun e => huA (e ▸ hw)
    have h2 : w ≠ v := fun e => hvA (e ▸ hw)
    have h3 : w ∉ B := hAB w hw
    simp [hxdef, h1, h2, hw, h3]
  have hxB : ∀ w ∈ B, x w = -(q w) := by
    intro w hw
    have h1 : w ≠ u := fun e => huB (e ▸ hw)
    have h2 : w ≠ v := fun e => hvB (e ▸ hw)
    have h3 : w ∉ A := fun hwA => hAB w hwA hw
    simp [hxdef, h1, h2, h3, hw]
  have hxZ : ∀ w : V, w ≠ u → w ≠ v → w ∉ A → w ∉ B → x w = 0 := by
    intro w h1 h2 h3 h4
    simp [hxdef, h1, h2, h3, h4]
  -- Orthogonality to the all-ones vector.
  have hsum0 : ∑ i, x i = 0 := by
    simp only [hxdef]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_ite_eq' Finset.univ u fun _ => au,
      Finset.sum_ite_eq' Finset.univ v fun _ => av,
      Finset.sum_ite_mem, Finset.sum_ite_mem, Finset.univ_inter, Finset.univ_inter]
    simp only [Finset.mem_univ, if_true]
    linarith [hbal]
  -- Nonvanishing.
  have hne0 : ∃ i, x i ≠ 0 := ⟨u, by rw [hxu]; exact ne_of_gt hau⟩
  -- Squared norm.
  have hnorm : ∑ i, x i ^ 2
      = au ^ 2 + (∑ w ∈ A, p w ^ 2) + (av ^ 2 + ∑ w ∈ B, q w ^ 2) := by
    have hsq : ∀ i : V, x i ^ 2
        = ((if i = u then au ^ 2 else 0) + (if i ∈ A then p i ^ 2 else 0))
          + ((if i = v then av ^ 2 else 0) + (if i ∈ B then q i ^ 2 else 0)) := by
      intro i
      by_cases hiu : i = u
      · subst hiu; rw [hxu]; simp [hne, huA, huB]
      · by_cases hiv : i = v
        · subst hiv; rw [hxv]; simp [hne.symm, hvA, hvB]
        · by_cases hiA : i ∈ A
          · rw [hxA i hiA]; simp [hiu, hiv, hiA, hAB i hiA]
          · by_cases hiB : i ∈ B
            · rw [hxB i hiB]; simp [hiu, hiv, hiA, hiB]
            · rw [hxZ i hiu hiv hiA hiB]; simp [hiu, hiv, hiA, hiB]
    simp_rw [hsq]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_ite_eq' Finset.univ u fun _ => au ^ 2,
      Finset.sum_ite_eq' Finset.univ v fun _ => av ^ 2,
      Finset.sum_ite_mem, Finset.sum_ite_mem, Finset.univ_inter, Finset.univ_inter]
    simp only [Finset.mem_univ, if_true]
  -- Per-ordered-pair upper bound on the quadratic-form summand.
  have hterm : ∀ i j : V,
      (if G.Adj i j then (x i - x j) ^ 2 else 0) ≤
        (if G.Adj i j ∧ i = u then (au - p j) ^ 2 else 0)
      + (if G.Adj i j ∧ j = u then (au - p i) ^ 2 else 0)
      + (if G.Adj i j ∧ i = v then (av - q j) ^ 2 else 0)
      + (if G.Adj i j ∧ j = v then (av - q i) ^ 2 else 0)
      + (if G.Adj i j ∧ i ∈ A ∧ j ∈ B then (p i + q j) ^ 2 else 0)
      + (if G.Adj i j ∧ i ∈ B ∧ j ∈ A then (p j + q i) ^ 2 else 0)
      + (if G.Adj i j ∧ i ∈ A ∧ j ≠ u ∧ j ∉ B then p i ^ 2 else 0)
      + (if G.Adj i j ∧ j ∈ A ∧ i ≠ u ∧ i ∉ B then p j ^ 2 else 0)
      + (if G.Adj i j ∧ i ∈ B ∧ j ≠ v ∧ j ∉ A then q i ^ 2 else 0)
      + (if G.Adj i j ∧ j ∈ B ∧ i ≠ v ∧ i ∉ A then q j ^ 2 else 0) := by
    intro i j
    by_cases hadj : G.Adj i j
    · -- Nonnegativity of every summand.
      have nn1 : (0:ℝ) ≤ if G.Adj i j ∧ i = u then (au - p j) ^ 2 else 0 := by
        split <;> positivity
      have nn2 : (0:ℝ) ≤ if G.Adj i j ∧ j = u then (au - p i) ^ 2 else 0 := by
        split <;> positivity
      have nn3 : (0:ℝ) ≤ if G.Adj i j ∧ i = v then (av - q j) ^ 2 else 0 := by
        split <;> positivity
      have nn4 : (0:ℝ) ≤ if G.Adj i j ∧ j = v then (av - q i) ^ 2 else 0 := by
        split <;> positivity
      have nn5 : (0:ℝ) ≤ if G.Adj i j ∧ i ∈ A ∧ j ∈ B then (p i + q j) ^ 2 else 0 := by
        split <;> positivity
      have nn6 : (0:ℝ) ≤ if G.Adj i j ∧ i ∈ B ∧ j ∈ A then (p j + q i) ^ 2 else 0 := by
        split <;> positivity
      have nn7 : (0:ℝ) ≤ if G.Adj i j ∧ i ∈ A ∧ j ≠ u ∧ j ∉ B then p i ^ 2 else 0 := by
        split <;> positivity
      have nn8 : (0:ℝ) ≤ if G.Adj i j ∧ j ∈ A ∧ i ≠ u ∧ i ∉ B then p j ^ 2 else 0 := by
        split <;> positivity
      have nn9 : (0:ℝ) ≤ if G.Adj i j ∧ i ∈ B ∧ j ≠ v ∧ j ∉ A then q i ^ 2 else 0 := by
        split <;> positivity
      have nn10 : (0:ℝ) ≤ if G.Adj i j ∧ j ∈ B ∧ i ≠ v ∧ i ∉ A then q j ^ 2 else 0 := by
        split <;> positivity
      rw [if_pos hadj]
      by_cases hiu : i = u
      · -- `u → N(u)` edge.
        have hjA : j ∈ A := (hmemA j).mpr (hiu ▸ hadj)
        have e1 : (if G.Adj i j ∧ i = u then (au - p j) ^ 2 else 0) = (au - p j) ^ 2 :=
          if_pos ⟨hadj, hiu⟩
        have hxi : x i = au := by rw [hiu]; exact hxu
        rw [hxi, hxA j hjA]
        linarith [nn2, nn3, nn4, nn5, nn6, nn7, nn8, nn9, nn10]
      · by_cases hju : j = u
        · -- `N(u) → u` edge.
          have hiA : i ∈ A := (hmemA i).mpr (G.adj_symm (hju ▸ hadj))
          have e2 : (if G.Adj i j ∧ j = u then (au - p i) ^ 2 else 0) = (au - p i) ^ 2 :=
            if_pos ⟨hadj, hju⟩
          have hxj : x j = au := by rw [hju]; exact hxu
          have hval : (p i - au) ^ 2 = (au - p i) ^ 2 := by ring
          rw [hxj, hxA i hiA, hval]
          linarith [nn1, nn3, nn4, nn5, nn6, nn7, nn8, nn9, nn10]
        · by_cases hiv : i = v
          · -- `v → N(v)` edge.
            have hjB : j ∈ B := (hmemB j).mpr (hiv ▸ hadj)
            have e3 : (if G.Adj i j ∧ i = v then (av - q j) ^ 2 else 0) = (av - q j) ^ 2 :=
              if_pos ⟨hadj, hiv⟩
            have hxi : x i = -av := by rw [hiv]; exact hxv
            have hval : (-av - -(q j)) ^ 2 = (av - q j) ^ 2 := by ring
            rw [hxi, hxB j hjB, hval]
            linarith [nn1, nn2, nn4, nn5, nn6, nn7, nn8, nn9, nn10]
          · by_cases hjv : j = v
            · -- `N(v) → v` edge.
              have hiB : i ∈ B := (hmemB i).mpr (G.adj_symm (hjv ▸ hadj))
              have e4 : (if G.Adj i j ∧ j = v then (av - q i) ^ 2 else 0)
                  = (av - q i) ^ 2 := if_pos ⟨hadj, hjv⟩
              have hxj : x j = -av := by rw [hjv]; exact hxv
              have hval : (-(q i) - -av) ^ 2 = (av - q i) ^ 2 := by ring
              rw [hxj, hxB i hiB, hval]
              linarith [nn1, nn2, nn3, nn5, nn6, nn7, nn8, nn9, nn10]
            · -- Neither endpoint is a centre.
              by_cases hiA : i ∈ A
              · by_cases hjB : j ∈ B
                · -- cross edge `N(u) → N(v)`.
                  have e5 : (if G.Adj i j ∧ i ∈ A ∧ j ∈ B then (p i + q j) ^ 2 else 0)
                      = (p i + q j) ^ 2 := if_pos ⟨hadj, hiA, hjB⟩
                  have hval : (p i - -(q j)) ^ 2 = (p i + q j) ^ 2 := by ring
                  rw [hxA i hiA, hxB j hjB, hval]
                  linarith [nn1, nn2, nn3, nn4, nn6, nn7, nn8, nn9, nn10]
                · by_cases hjA : j ∈ A
                  · -- internal `N(u)` edge: charge both slots.
                    have e7 : (if G.Adj i j ∧ i ∈ A ∧ j ≠ u ∧ j ∉ B then p i ^ 2 else 0)
                        = p i ^ 2 := if_pos ⟨hadj, hiA, hju, hjB⟩
                    have e8 : (if G.Adj i j ∧ j ∈ A ∧ i ≠ u ∧ i ∉ B then p j ^ 2 else 0)
                        = p j ^ 2 := if_pos ⟨hadj, hjA, hiu, hAB i hiA⟩
                    have hb : (p i - p j) ^ 2 ≤ p i ^ 2 + p j ^ 2 := by
                      nlinarith [mul_nonneg (hp i hiA) (hp j hjA)]
                    rw [hxA i hiA, hxA j hjA]
                    linarith [nn1, nn2, nn3, nn4, nn5, nn6, nn9, nn10]
                  · -- leak `N(u) → Z`.
                    have e7 : (if G.Adj i j ∧ i ∈ A ∧ j ≠ u ∧ j ∉ B then p i ^ 2 else 0)
                        = p i ^ 2 := if_pos ⟨hadj, hiA, hju, hjB⟩
                    have hval : (p i - 0) ^ 2 = p i ^ 2 := by ring
                    rw [hxA i hiA, hxZ j hju hjv hjA hjB, hval]
                    linarith [nn1, nn2, nn3, nn4, nn5, nn6, nn8, nn9, nn10]
              · by_cases hiB : i ∈ B
                · by_cases hjA : j ∈ A
                  · -- cross edge `N(v) → N(u)`.
                    have e6 : (if G.Adj i j ∧ i ∈ B ∧ j ∈ A then (p j + q i) ^ 2 else 0)
                        = (p j + q i) ^ 2 := if_pos ⟨hadj, hiB, hjA⟩
                    have hval : (-(q i) - p j) ^ 2 = (p j + q i) ^ 2 := by ring
                    rw [hxB i hiB, hxA j hjA, hval]
                    linarith [nn1, nn2, nn3, nn4, nn5, nn7, nn8, nn9, nn10]
                  · by_cases hjB : j ∈ B
                    · -- internal `N(v)` edge.
                      have e9 : (if G.Adj i j ∧ i ∈ B ∧ j ≠ v ∧ j ∉ A then q i ^ 2 else 0)
                          = q i ^ 2 := if_pos ⟨hadj, hiB, hjv, hjA⟩
                      have e10 : (if G.Adj i j ∧ j ∈ B ∧ i ≠ v ∧ i ∉ A then q j ^ 2 else 0)
                          = q j ^ 2 := if_pos ⟨hadj, hjB, hiv, hiA⟩
                      have hb : (-(q i) - -(q j)) ^ 2 ≤ q i ^ 2 + q j ^ 2 := by
                        nlinarith [mul_nonneg (hq i hiB) (hq j hjB)]
                      rw [hxB i hiB, hxB j hjB]
                      linarith [nn1, nn2, nn3, nn4, nn5, nn6, nn7, nn8]
                    · -- leak `N(v) → Z`.
                      have e9 : (if G.Adj i j ∧ i ∈ B ∧ j ≠ v ∧ j ∉ A then q i ^ 2 else 0)
                          = q i ^ 2 := if_pos ⟨hadj, hiB, hjv, hjA⟩
                      have hval : (-(q i) - 0) ^ 2 = q i ^ 2 := by ring
                      rw [hxB i hiB, hxZ j hju hjv hjA hjB, hval]
                      linarith [nn1, nn2, nn3, nn4, nn5, nn6, nn7, nn8, nn10]
                · by_cases hjA : j ∈ A
                  · -- leak `Z → N(u)`.
                    have e8 : (if G.Adj i j ∧ j ∈ A ∧ i ≠ u ∧ i ∉ B then p j ^ 2 else 0)
                        = p j ^ 2 := if_pos ⟨hadj, hjA, hiu, hiB⟩
                    have hval : (0 - p j) ^ 2 = p j ^ 2 := by ring
                    rw [hxZ i hiu hiv hiA hiB, hxA j hjA, hval]
                    linarith [nn1, nn2, nn3, nn4, nn5, nn6, nn7, nn9, nn10]
                  · by_cases hjB : j ∈ B
                    · -- leak `Z → N(v)`.
                      have e10 : (if G.Adj i j ∧ j ∈ B ∧ i ≠ v ∧ i ∉ A then q j ^ 2 else 0)
                          = q j ^ 2 := if_pos ⟨hadj, hjB, hiv, hiA⟩
                      have hval : (0 - -(q j)) ^ 2 = q j ^ 2 := by ring
                      rw [hxZ i hiu hiv hiA hiB, hxB j hjB, hval]
                      linarith [nn1, nn2, nn3, nn4, nn5, nn6, nn7, nn8, nn9]
                    · -- `Z → Z`: zero.
                      rw [hxZ i hiu hiv hiA hiB, hxZ j hju hjv hjA hjB]
                      norm_num
                      linarith [nn1, nn2, nn3, nn4, nn5, nn6, nn7, nn8, nn9, nn10]
    · simp [hadj]
  -- Sum-over-neighbours helper.
  have hnbr_sum : ∀ (z : V) (f : V → ℝ),
      (∑ j, if G.Adj z j then f j else 0) = ∑ j ∈ G.neighborFinset z, f j := by
    intro z f
    rw [← Finset.sum_filter]
    congr 1
    ext j
    simp [SimpleGraph.mem_neighborFinset]
  -- Count lemma: `u`-centre edges (`i = u`).
  have hC1 : (∑ i, ∑ j, if G.Adj i j ∧ i = u then (au - p j) ^ 2 else 0)
      = ∑ w ∈ A, (au - p w) ^ 2 := by
    have h1 : ∀ i j : V, (if G.Adj i j ∧ i = u then (au - p j) ^ 2 else 0)
        = if i = u then (if G.Adj i j then (au - p j) ^ 2 else 0) else 0 := by
      intro i j
      by_cases h1 : i = u <;> by_cases h2 : G.Adj i j <;> simp [h1, h2]
    have h2 : ∀ i : V,
        (∑ j, if i = u then (if G.Adj i j then (au - p j) ^ 2 else 0) else 0)
        = if i = u then (∑ j, if G.Adj i j then (au - p j) ^ 2 else 0) else 0 := by
      intro i
      by_cases h : i = u <;> simp [h]
    simp_rw [h1, h2]
    rw [Finset.sum_ite_eq' Finset.univ u]
    simp only [Finset.mem_univ, if_true]
    exact hnbr_sum u _
  have hC2 : (∑ i, ∑ j, if G.Adj i j ∧ j = u then (au - p i) ^ 2 else 0)
      = ∑ w ∈ A, (au - p w) ^ 2 := by
    rw [← hC1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    refine if_congr ?_ rfl rfl
    rw [SimpleGraph.adj_comm]
  -- Count lemma: `v`-centre edges.
  have hC3 : (∑ i, ∑ j, if G.Adj i j ∧ i = v then (av - q j) ^ 2 else 0)
      = ∑ w ∈ B, (av - q w) ^ 2 := by
    have h1 : ∀ i j : V, (if G.Adj i j ∧ i = v then (av - q j) ^ 2 else 0)
        = if i = v then (if G.Adj i j then (av - q j) ^ 2 else 0) else 0 := by
      intro i j
      by_cases h1 : i = v <;> by_cases h2 : G.Adj i j <;> simp [h1, h2]
    have h2 : ∀ i : V,
        (∑ j, if i = v then (if G.Adj i j then (av - q j) ^ 2 else 0) else 0)
        = if i = v then (∑ j, if G.Adj i j then (av - q j) ^ 2 else 0) else 0 := by
      intro i
      by_cases h : i = v <;> simp [h]
    simp_rw [h1, h2]
    rw [Finset.sum_ite_eq' Finset.univ v]
    simp only [Finset.mem_univ, if_true]
    exact hnbr_sum v _
  have hC4 : (∑ i, ∑ j, if G.Adj i j ∧ j = v then (av - q i) ^ 2 else 0)
      = ∑ w ∈ B, (av - q w) ^ 2 := by
    rw [← hC3, Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    refine if_congr ?_ rfl rfl
    rw [SimpleGraph.adj_comm]
  -- Count lemma: cross edges.
  have hC5 : (∑ i, ∑ j, if G.Adj i j ∧ i ∈ A ∧ j ∈ B then (p i + q j) ^ 2 else 0)
      = ∑ w ∈ A, ∑ w' ∈ B, (if G.Adj w w' then (p w + q w') ^ 2 else 0) := by
    have h1 : ∀ i j : V, (if G.Adj i j ∧ i ∈ A ∧ j ∈ B then (p i + q j) ^ 2 else 0)
        = if i ∈ A then (if j ∈ B then (if G.Adj i j then (p i + q j) ^ 2 else 0)
            else 0) else 0 := by
      intro i j
      by_cases h1 : i ∈ A <;> by_cases h2 : j ∈ B <;> by_cases h3 : G.Adj i j <;>
        simp [h1, h2, h3]
    have h2 : ∀ i : V,
        (∑ j, if i ∈ A then (if j ∈ B then (if G.Adj i j then (p i + q j) ^ 2 else 0)
            else 0) else 0)
        = if i ∈ A then (∑ j, if j ∈ B then (if G.Adj i j then (p i + q j) ^ 2 else 0)
            else 0) else 0 := by
      intro i
      by_cases h : i ∈ A <;> simp [h]
    simp_rw [h1, h2]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  have hC6 : (∑ i, ∑ j, if G.Adj i j ∧ i ∈ B ∧ j ∈ A then (p j + q i) ^ 2 else 0)
      = ∑ w ∈ A, ∑ w' ∈ B, (if G.Adj w w' then (p w + q w') ^ 2 else 0) := by
    rw [← hC5, Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    refine if_congr ?_ rfl rfl
    rw [SimpleGraph.adj_comm]
    tauto
  -- Count lemma: `N(u)` leak slots.
  have hC7 : (∑ i, ∑ j, if G.Adj i j ∧ i ∈ A ∧ j ≠ u ∧ j ∉ B then p i ^ 2 else 0)
      = ∑ w ∈ A, ((G.neighborFinset w \ insert u B).card : ℝ) * p w ^ 2 := by
    have h1 : ∀ i j : V, (if G.Adj i j ∧ i ∈ A ∧ j ≠ u ∧ j ∉ B then p i ^ 2 else 0)
        = if i ∈ A then (if j ∈ G.neighborFinset i \ insert u B then p i ^ 2 else 0)
            else 0 := by
      intro i j
      have hmem : j ∈ G.neighborFinset i \ insert u B ↔ G.Adj i j ∧ j ≠ u ∧ j ∉ B := by
        simp only [Finset.mem_sdiff, SimpleGraph.mem_neighborFinset, Finset.mem_insert,
          not_or]
      by_cases h1 : i ∈ A <;> by_cases h2 : G.Adj i j ∧ j ≠ u ∧ j ∉ B <;>
        simp [h1, h2, hmem]
    have h2 : ∀ i : V,
        (∑ j, if i ∈ A then (if j ∈ G.neighborFinset i \ insert u B then p i ^ 2 else 0)
            else 0)
        = if i ∈ A then (∑ j, if j ∈ G.neighborFinset i \ insert u B then p i ^ 2 else 0)
            else 0 := by
      intro i
      by_cases h : i ∈ A <;> simp [h]
    simp_rw [h1, h2]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
  have hC8 : (∑ i, ∑ j, if G.Adj i j ∧ j ∈ A ∧ i ≠ u ∧ i ∉ B then p j ^ 2 else 0)
      = ∑ w ∈ A, ((G.neighborFinset w \ insert u B).card : ℝ) * p w ^ 2 := by
    rw [← hC7, Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    refine if_congr ?_ rfl rfl
    rw [SimpleGraph.adj_comm]
  -- Count lemma: `N(v)` leak slots.
  have hC9 : (∑ i, ∑ j, if G.Adj i j ∧ i ∈ B ∧ j ≠ v ∧ j ∉ A then q i ^ 2 else 0)
      = ∑ w ∈ B, ((G.neighborFinset w \ insert v A).card : ℝ) * q w ^ 2 := by
    have h1 : ∀ i j : V, (if G.Adj i j ∧ i ∈ B ∧ j ≠ v ∧ j ∉ A then q i ^ 2 else 0)
        = if i ∈ B then (if j ∈ G.neighborFinset i \ insert v A then q i ^ 2 else 0)
            else 0 := by
      intro i j
      have hmem : j ∈ G.neighborFinset i \ insert v A ↔ G.Adj i j ∧ j ≠ v ∧ j ∉ A := by
        simp only [Finset.mem_sdiff, SimpleGraph.mem_neighborFinset, Finset.mem_insert,
          not_or]
      by_cases h1 : i ∈ B <;> by_cases h2 : G.Adj i j ∧ j ≠ v ∧ j ∉ A <;>
        simp [h1, h2, hmem]
    have h2 : ∀ i : V,
        (∑ j, if i ∈ B then (if j ∈ G.neighborFinset i \ insert v A then q i ^ 2 else 0)
            else 0)
        = if i ∈ B then (∑ j, if j ∈ G.neighborFinset i \ insert v A then q i ^ 2 else 0)
            else 0 := by
      intro i
      by_cases h : i ∈ B <;> simp [h]
    simp_rw [h1, h2]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
  have hC10 : (∑ i, ∑ j, if G.Adj i j ∧ j ∈ B ∧ i ≠ v ∧ i ∉ A then q j ^ 2 else 0)
      = ∑ w ∈ B, ((G.neighborFinset w \ insert v A).card : ℝ) * q w ^ 2 := by
    rw [← hC9, Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    refine if_congr ?_ rfl rfl
    rw [SimpleGraph.adj_comm]
  -- Assemble the ordered-pair bound.
  have hsum_bound : (∑ i, ∑ j, if G.Adj i j then (x i - x j) ^ 2 else 0)
      ≤ 2 * ((∑ w ∈ A, (au - p w) ^ 2) + (∑ w ∈ B, (av - q w) ^ 2)
        + (∑ w ∈ A, ∑ w' ∈ B, (if G.Adj w w' then (p w + q w') ^ 2 else 0))
        + (∑ w ∈ A, ((G.neighborFinset w \ insert u B).card : ℝ) * p w ^ 2)
        + (∑ w ∈ B, ((G.neighborFinset w \ insert v A).card : ℝ) * q w ^ 2)) := by
    calc (∑ i, ∑ j, if G.Adj i j then (x i - x j) ^ 2 else 0)
        ≤ ∑ i, ∑ j,
            ((if G.Adj i j ∧ i = u then (au - p j) ^ 2 else 0)
          + (if G.Adj i j ∧ j = u then (au - p i) ^ 2 else 0)
          + (if G.Adj i j ∧ i = v then (av - q j) ^ 2 else 0)
          + (if G.Adj i j ∧ j = v then (av - q i) ^ 2 else 0)
          + (if G.Adj i j ∧ i ∈ A ∧ j ∈ B then (p i + q j) ^ 2 else 0)
          + (if G.Adj i j ∧ i ∈ B ∧ j ∈ A then (p j + q i) ^ 2 else 0)
          + (if G.Adj i j ∧ i ∈ A ∧ j ≠ u ∧ j ∉ B then p i ^ 2 else 0)
          + (if G.Adj i j ∧ j ∈ A ∧ i ≠ u ∧ i ∉ B then p j ^ 2 else 0)
          + (if G.Adj i j ∧ i ∈ B ∧ j ≠ v ∧ j ∉ A then q i ^ 2 else 0)
          + (if G.Adj i j ∧ j ∈ B ∧ i ≠ v ∧ i ∉ A then q j ^ 2 else 0)) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
      _ = 2 * ((∑ w ∈ A, (au - p w) ^ 2) + (∑ w ∈ B, (av - q w) ^ 2)
            + (∑ w ∈ A, ∑ w' ∈ B, (if G.Adj w w' then (p w + q w') ^ 2 else 0))
            + (∑ w ∈ A, ((G.neighborFinset w \ insert u B).card : ℝ) * p w ^ 2)
            + (∑ w ∈ B, ((G.neighborFinset w \ insert v A).card : ℝ) * q w ^ 2)) := by
          simp_rw [Finset.sum_add_distrib]
          rw [hC1, hC2, hC3, hC4, hC5, hC6, hC7, hC8, hC9, hC10]
          ring
  -- Conclude via the universal test-vector certificate.
  apply algConn_le_two_of_testvector G x hsum0 hne0
  rw [← Matrix.toLinearMap₂'_apply', SimpleGraph.lapMatrix_toLinearMap₂', hnorm]
  linarith [hsum_bound, hQ]


end ACMax
