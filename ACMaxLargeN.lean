/-
  THE ACMAX CONJECTURE FOR `n >= 123`, in one file.

  For every `n >= 123`: `K_{2,n-2}` has algebraic connectivity exactly `2`, and every simple
  graph on `n` vertices with exactly `2(n-2)` edges has algebraic connectivity at most `2`.
  The theorem is `ACMax.acmax_conjecture_large_n`, at the very end.

  THE ARGUMENT. Normalise a counterexample (Part III) to a *starved census*: minimum degree
  3, no edge between two degree-3 vertices. Then play two facts against each other. Locally
  (Part V), a short cycle among the degree-<=4 vertices yields an explicit vertex partition
  whose Rayleigh quotient certifies the bound -- so a counterexample has large girth there.
  Globally (Part VI), a set of large girth carrying edge excess needs more vertices than it
  has. The census rows (Part VII) pin the excess tightly enough that the two collide.

  ASSEMBLED from the canonical modules under `ACMaxConjecture/`, with every theorem
  unreachable from the main theorem pruned away, then reorganised into the seven parts
  below. Each source module is wrapped in its own `section ... end` so that its `variable`,
  `open` and `set_option` declarations stay scoped as they are when compiled separately.
  The canonical modules remain the place to edit the proof; this file is the reading and
  independent-checking artifact.
-/

import Mathlib
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Girth
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring


/-! ########################################################################################
   PART I --- Algebraic connectivity

   The definition of `algConn` and the two Courant--Fischer bridges: an upper bound from any
   test vector orthogonal to the constant vector, and the matching lower bound used for the
   equality clause.
   ######################################################################################## -/

/- ---------------------------------------- Spectral.AlgConn ---------------- -/
section
/-! Definitions only (from `ACMaxConjecture/Spectral/AlgConn.lean`); the theorems of that module are not
    reachable from the main theorem and have been pruned. -/

namespace ACMax

open scoped Classical

/-- Algebraic connectivity of a finite simple graph: the second-smallest eigenvalue
of the graph Laplacian `L(G) = D(G) - A(G)`. -/
noncomputable def algConn {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) : ℝ :=
  (SimpleGraph.posSemidef_lapMatrix ℝ G).isHermitian.eigenvalues₀
    ⟨Fintype.card V - 2, Nat.sub_lt Fintype.card_pos (by norm_num)⟩

end ACMax
end

/- ---------------------------------------- Spectral.RayleighUpper ---------- -/
section
/-!
# Variational (Courant–Fischer) upper bound for algebraic connectivity

`algConn_mul_sq_le`: for any test vector `x` orthogonal to the all-ones vector
(`∑ i, x i = 0`), the second-smallest Laplacian eigenvalue is bounded by the
Rayleigh quotient of `x`, in division-free form
`algConn G * ‖x‖² ≤ xᵀ L x`.

This is the reusable bridge both clauses of the ACMAX conjecture rely on.
-/

namespace ACMax

open scoped Classical
open Matrix

theorem algConn_mul_sq_le {V : Type*} [Fintype V] [Nonempty V] (G : SimpleGraph V)
    (x : V → ℝ) (hx0 : ∑ i, x i = 0) :
    algConn G * (∑ i, (x i) ^ 2) ≤ dotProduct x ((G.lapMatrix ℝ).mulVec x) := by
  classical
  set A : Matrix V V ℝ := G.lapMatrix ℝ with hAdef
  have hPSD : A.PosSemidef := SimpleGraph.posSemidef_lapMatrix ℝ G
  have hHerm : A.IsHermitian := hPSD.isHermitian
  set U := hHerm.eigenvectorUnitary with hUdef
  set lam : V → ℝ := hHerm.eigenvalues with hlamdef
  set D : Matrix V V ℝ := Matrix.diagonal lam with hDdef
  -- rewrite the squared norm as a dot product
  have hsum : (∑ i, (x i) ^ 2) = x ⬝ᵥ x := by
    have h : x ⬝ᵥ x = ∑ i, x i * x i := rfl
    rw [h]; simp [pow_two]
  rw [hsum]
  -- unitary facts
  have hU1 : (U : Matrix V V ℝ) * star (U : Matrix V V ℝ) = 1 :=
    Matrix.mem_unitaryGroup_iff.mp U.2
  have hU2 : star (U : Matrix V V ℝ) * (U : Matrix V V ℝ) = 1 :=
    Matrix.UnitaryGroup.star_mul_self U
  have hst : star (U : Matrix V V ℝ) = (U : Matrix V V ℝ)ᵀ := by
    ext i j
    simp [Matrix.star_apply, Matrix.transpose_apply, star_trivial]
  rcases le_or_gt (algConn G) 0 with hc0 | hcpos
  · -- trivial case: LHS ≤ 0 ≤ RHS
    have hxx : 0 ≤ x ⬝ᵥ x := by rw [← hsum]; positivity
    have hrhs : 0 ≤ x ⬝ᵥ (A *ᵥ x) := by
      have h := hPSD.re_dotProduct_nonneg x
      simpa using h
    have hle : algConn G * (x ⬝ᵥ x) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hc0 hxx
    linarith
  · -- main case: 0 < algConn G
    set y : V → ℝ := star (U : Matrix V V ℝ) *ᵥ x with hydef
    -- spectral relation A * U = U * D
    have hAU : A * (U : Matrix V V ℝ) = (U : Matrix V V ℝ) * D := by
      ext i j
      have hcol : (fun k => (U : Matrix V V ℝ) k j) = ⇑(hHerm.eigenvectorBasis j) := by
        funext k
        exact Matrix.IsHermitian.eigenvectorUnitary_apply hHerm k j
      have hL : (A * (U : Matrix V V ℝ)) i j = (lam j • ⇑(hHerm.eigenvectorBasis j)) i := by
        have hrfl : (A * (U : Matrix V V ℝ)) i j
            = (A *ᵥ (fun k => (U : Matrix V V ℝ) k j)) i := rfl
        rw [hrfl, hcol, hHerm.mulVec_eigenvectorBasis]
      rw [hL, hDdef, Matrix.mul_diagonal]
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [← Matrix.IsHermitian.eigenvectorUnitary_apply hHerm i j]
      ring
    have hAgen : ∀ w : V → ℝ,
        A *ᵥ ((U : Matrix V V ℝ) *ᵥ w) = (U : Matrix V V ℝ) *ᵥ (D *ᵥ w) := by
      intro w
      rw [Matrix.mulVec_mulVec, hAU, ← Matrix.mulVec_mulVec]
    -- x = U *ᵥ y
    have hxy : x = (U : Matrix V V ℝ) *ᵥ y := by
      rw [hydef, Matrix.mulVec_mulVec, hU1, Matrix.one_mulVec]
    have hAx : A *ᵥ x = (U : Matrix V V ℝ) *ᵥ (D *ᵥ y) := by
      rw [hxy]; exact hAgen y
    -- U preserves the dot product
    have hpres : ∀ a b : V → ℝ,
        ((U : Matrix V V ℝ) *ᵥ a) ⬝ᵥ ((U : Matrix V V ℝ) *ᵥ b) = a ⬝ᵥ b := by
      intro a b
      rw [Matrix.dotProduct_mulVec]
      have hv : Matrix.vecMul ((U : Matrix V V ℝ) *ᵥ a) (U : Matrix V V ℝ) = a := by
        rw [← Matrix.mulVec_transpose, ← hst, Matrix.mulVec_mulVec, hU2, Matrix.one_mulVec]
      rw [hv]
    have hxx : x ⬝ᵥ x = y ⬝ᵥ y := by rw [hxy]; exact hpres y y
    have hquad : x ⬝ᵥ (A *ᵥ x) = y ⬝ᵥ (D *ᵥ y) := by
      rw [hAx, hxy]; exact hpres y (D *ᵥ y)
    -- index data
    have hcard2 : Fintype.card V - 2 < Fintype.card V := Nat.sub_lt Fintype.card_pos (by norm_num)
    let e := Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card V))
    have hlam : ∀ i, lam i = hHerm.eigenvalues₀ (e.symm i) := by intro i; rw [hlamdef]; rfl
    have hc : algConn G = hHerm.eigenvalues₀ ⟨Fintype.card V - 2, hcard2⟩ := rfl
    -- the diagonal kills z on the positive eigenvalues
    -- key: y i = 0 whenever lam i < algConn G
    have hzero : ∀ i, lam i < algConn G → y i = 0 := by
      intro i hi
      set ones : V → ℝ := fun _ => (1 : ℝ) with hones
      set z : V → ℝ := star (U : Matrix V V ℝ) *ᵥ ones with hz
      have hones_eq : ones = (U : Matrix V V ℝ) *ᵥ z := by
        rw [hz, Matrix.mulVec_mulVec, hU1, Matrix.one_mulVec]
      have hAones : A *ᵥ ones = 0 := by
        rw [hAdef]; exact SimpleGraph.lapMatrix_mulVec_const_eq_zero G
      have hUDz : (U : Matrix V V ℝ) *ᵥ (D *ᵥ z) = 0 := by
        rw [← hAgen z, ← hones_eq, hAones]
      have hDz : D *ᵥ z = 0 := by
        have hcong := congrArg (fun w => star (U : Matrix V V ℝ) *ᵥ w) hUDz
        simp only [Matrix.mulVec_zero] at hcong
        rw [Matrix.mulVec_mulVec, hU2, Matrix.one_mulVec] at hcong
        exact hcong
      have hlamz : ∀ k, lam k * z k = 0 := by
        intro k
        have hck := congrFun hDz k
        rw [hDdef, Matrix.mulVec_diagonal] at hck
        simpa using hck
      -- e.symm i sits strictly past card - 2
      have hk2 : (Fintype.card V - 2 : ℕ) < (e.symm i).val := by
        by_contra hcon
        rw [not_lt] at hcon
        have hle : (e.symm i) ≤ (⟨Fintype.card V - 2, hcard2⟩ : Fin (Fintype.card V)) :=
          Fin.le_def.mpr hcon
        have hmono := hHerm.eigenvalues₀_antitone hle
        rw [← hlam i, ← hc] at hmono
        linarith
      -- z vanishes off i
      have hknz : ∀ k, k ≠ i → z k = 0 := by
        intro k hk
        have hkne : (e.symm k).val ≠ (e.symm i).val := by
          intro h
          exact hk (e.symm.injective (Fin.ext h))
        have hle : (e.symm k) ≤ (⟨Fintype.card V - 2, hcard2⟩ : Fin (Fintype.card V)) := by
          rw [Fin.le_def]
          show (e.symm k).val ≤ Fintype.card V - 2
          have h1 := (e.symm i).isLt
          have h2 := (e.symm k).isLt
          omega
        have hge : algConn G ≤ lam k := by
          have hmono := hHerm.eigenvalues₀_antitone hle
          rwa [← hlam k, ← hc] at hmono
        have hkpos : lam k ≠ 0 := by linarith
        rcases mul_eq_zero.mp (hlamz k) with h | h
        · exact absurd h hkpos
        · exact h
      -- 1 = U j i * z i for every j
      have huzi : ∀ j, (U : Matrix V V ℝ) j i * z i = 1 := by
        intro j
        have h1 : (1 : ℝ) = ∑ k, (U : Matrix V V ℝ) j k * z k := by
          have hcj := congrFun hones_eq j
          simpa [hones, Matrix.mulVec, dotProduct] using hcj
        rw [Finset.sum_eq_single i] at h1
        · exact h1.symm
        · intro k _ hk; rw [hknz k hk, mul_zero]
        · intro h; exact absurd (Finset.mem_univ i) h
      -- expand y i
      have hyi : y i = ∑ j, (U : Matrix V V ℝ) j i * x j := by
        rw [hydef]
        simp only [Matrix.mulVec, dotProduct]
        apply Finset.sum_congr rfl
        intro j _
        rw [Matrix.star_apply, star_trivial]
      have key : z i * y i = 0 := by
        have h2 : z i * y i = ∑ j, x j := by
          rw [hyi, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          rw [← mul_assoc, mul_comm (z i) ((U : Matrix V V ℝ) j i), huzi j, one_mul]
        rw [h2, hx0]
      rcases mul_eq_zero.mp key with h | h
      · exfalso
        have hj := huzi (Classical.arbitrary V)
        rw [h, mul_zero] at hj
        exact one_ne_zero hj.symm
      · exact h
    -- assemble the bound
    rw [hxx, hquad]
    have e1 : y ⬝ᵥ y = ∑ j, y j ^ 2 := by
      have h : y ⬝ᵥ y = ∑ j, y j * y j := rfl
      rw [h]; apply Finset.sum_congr rfl; intro j _; rw [pow_two]
    have e2 : y ⬝ᵥ (D *ᵥ y) = ∑ j, lam j * y j ^ 2 := by
      have h : y ⬝ᵥ (D *ᵥ y) = ∑ j, y j * (D *ᵥ y) j := rfl
      rw [h]; apply Finset.sum_congr rfl; intro j _
      rw [hDdef, Matrix.mulVec_diagonal]; ring
    rw [e1, e2, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    rcases le_or_gt (algConn G) (lam j) with hle | hlt
    · exact mul_le_mul_of_nonneg_right hle (sq_nonneg _)
    · rw [hzero j hlt]; simp

end ACMax
end

/- ---------------------------------------- Spectral.TestVector ------------- -/
section
/-!
# Universal test-vector interface

`algConn_le_two_of_testvector`: any nonzero vector `x` orthogonal to the all-ones
vector whose Laplacian quadratic form is at most `2 ‖x‖²` certifies `algConn G ≤ 2`.

This is the direct corollary of the Courant–Fischer bridge `algConn_mul_sq_le` that
every concrete upper-bound certificate in the `Cuts/` chapter factors through: the
balanced, weighted and signed cuts, the induced-`2K₂` bound and the good-`C₄`/`K_{2,3}`
certificates all build an explicit `x ⊥ 𝟙` and discharge the Rayleigh inequality here.
-/

namespace ACMax

open scoped Classical
open Matrix

/-- Universal certificate: a nonzero `x ⊥ 𝟙` with `xᵀ L x ≤ 2‖x‖²` forces
`algConn G ≤ 2`. -/
theorem algConn_le_two_of_testvector {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (x : V → ℝ) (hx0 : ∑ i, x i = 0) (hxne : ∃ i, x i ≠ 0)
    (hQ : dotProduct x ((G.lapMatrix ℝ).mulVec x) ≤ 2 * ∑ i, (x i) ^ 2) :
    algConn G ≤ 2 := by
  classical
  set S : ℝ := ∑ i, (x i) ^ 2 with hSdef
  have hSnonneg : 0 ≤ S := Finset.sum_nonneg fun i _ => sq_nonneg (x i)
  obtain ⟨j, hj⟩ := hxne
  have hSpos : 0 < S := by
    refine Finset.sum_pos' (fun i _ => sq_nonneg (x i)) ?_
    exact ⟨j, Finset.mem_univ j, by positivity⟩
  have key := algConn_mul_sq_le G x hx0
  have hchain : algConn G * S ≤ 2 * S := le_trans key hQ
  rw [mul_comm (algConn G) S, mul_comm 2 S] at hchain
  exact le_of_mul_le_mul_left hchain hSpos

end ACMax
end


/-! ########################################################################################
   PART II --- The cut toolbox

   Certificates built from explicit vertex partitions. Each says: exhibit this configuration
   and `algConn G <= 2` follows.
   ######################################################################################## -/

/- ---------------------------------------- Cuts.LowDegreeVertex ------------ -/
section
/-!
# A single low-degree vertex already forces `algConn ≤ 2`

If `G` has a vertex `u` of degree `≤ 2` and there is at least one vertex outside
`{u} ∪ N(u)`, then `algConn G ≤ 2`.

Certificate: with `C := N(u)` (`|C| = deg u ≤ 2`) and `T := V ∖ ({u} ∪ C)`, take
`x := |T|·e_u − 𝟙_T`.  Then `∑ x = 0`, `∑ x² = |T|² + |T|`, and the only edges that
contribute to the Laplacian form are the `deg u` edges `u`–`C` (each `|T|²`) and the
`T`–`C` edges (each `1`); there are no `u`–`T` edges.  Since every vertex of `T` meets
at most `|C| ≤ 2` vertices of `C`, the `T`–`C` edge count is `≤ 2|T|`, so
`xᵀ L x = deg u · |T|² + e(T,C) ≤ 2|T|² + 2|T| = 2 ∑ x²`.

This closes every `n ≤ 7` instance of the conjecture: `m = 2(n-2) < 3n/2` for `n ≤ 7`
forces a vertex of degree `≤ 2`.  The open core is exactly the graphs with minimum
degree `≥ 3` (possible only for `n ≥ 8`).
-/

namespace ACMax

open scoped Classical
open Matrix

/-- If `G` has a vertex of degree `≤ 2` with a vertex outside its closed neighborhood,
then `algConn G ≤ 2`. -/
theorem algConn_le_two_of_low_degree_vertex {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (u : V) (hdeg : G.degree u ≤ 2)
    (hT : (Finset.univ \ insert u (G.neighborFinset u)).Nonempty) :
    algConn G ≤ 2 := by
  classical
  set C : Finset V := G.neighborFinset u with hCdef
  set T : Finset V := Finset.univ \ insert u C with hTdef
  set t : ℕ := T.card with htdef
  have htpos : 0 < t := by rw [htdef]; exact hT.card_pos
  -- membership facts for the three blocks {u}, C, T
  have huC : u ∉ C := by simp [hCdef]
  have huT : u ∉ T := by rw [hTdef]; simp
  have hT_not_C : ∀ w ∈ T, w ∉ C := by
    intro w hw
    rw [hTdef, Finset.mem_sdiff, Finset.mem_insert, not_or] at hw
    exact hw.2.2
  have hT_ne_u : ∀ w ∈ T, w ≠ u := by
    intro w hw
    rw [hTdef, Finset.mem_sdiff, Finset.mem_insert, not_or] at hw
    exact hw.2.1
  -- the test vector x = t·e_u − 𝟙_T
  set x : V → ℝ := fun w => (if w = u then (t : ℝ) else 0) - (if w ∈ T then 1 else 0) with hxdef
  have hxu : x u = t := by simp [hxdef, huT]
  have hxT : ∀ w ∈ T, x w = -1 := by
    intro w hw
    simp [hxdef, hT_ne_u w hw, hw]
  have hxC : ∀ w ∈ C, x w = 0 := by
    intro w hw
    have hwu : w ≠ u := fun h => huC (h ▸ hw)
    have hwT : w ∉ T := fun h => hT_not_C w h hw
    simp [hxdef, hwu, hwT]
  -- (1) ∑ x = 0
  have hx0 : ∑ i, x i = 0 := by
    have h1 : ∑ i, (if i = u then (t : ℝ) else 0) = t := by
      rw [Finset.sum_ite_eq' Finset.univ u (fun _ => (t : ℝ))]; simp
    have h2 : ∑ i, (if i ∈ T then (1 : ℝ) else 0) = t := by
      rw [Finset.sum_ite_mem Finset.univ T (fun _ => (1 : ℝ)), Finset.univ_inter,
        Finset.sum_const, nsmul_eq_mul, mul_one, htdef]
    simp only [hxdef, Finset.sum_sub_distrib]
    rw [h1, h2]; ring
  -- (2) ∃ i, x i ≠ 0
  have htne : (t : ℝ) ≠ 0 := by
    have : t ≠ 0 := by omega
    exact_mod_cast this
  have hxne : ∃ i, x i ≠ 0 := ⟨u, by rw [hxu]; exact htne⟩
  -- norm: ∑ x² = t² + t
  have hsq : ∑ i, (x i) ^ 2 = (t : ℝ) ^ 2 + t := by
    have hpt : ∀ i, (x i) ^ 2 = (if i = u then (t : ℝ) ^ 2 else 0) + (if i ∈ T then 1 else 0) := by
      intro i
      by_cases hiu : i = u
      · subst hiu; rw [hxu]; simp [huT]
      · by_cases hiT : i ∈ T
        · rw [hxT i hiT]; simp [hiu, hiT]
        · have hxi : x i = 0 := by simp [hxdef, hiu, hiT]
          rw [hxi]; simp [hiu, hiT]
    simp only [hpt, Finset.sum_add_distrib]
    rw [Finset.sum_ite_eq' Finset.univ u (fun _ => (t : ℝ) ^ 2),
      Finset.sum_ite_mem Finset.univ T (fun _ => (1 : ℝ)), Finset.univ_inter,
      Finset.sum_const, nsmul_eq_mul, mul_one, htdef]
    simp
  -- per-vertex bound for the T block
  have hterm : ∀ v ∈ T, (G.degree v : ℝ) + ∑ w ∈ G.neighborFinset v, x w ≤ 2 := by
    intro v hv
    have huNv : u ∉ G.neighborFinset v := by
      rw [SimpleGraph.mem_neighborFinset]
      intro hadj
      have hvC : v ∈ C := by rw [hCdef, SimpleGraph.mem_neighborFinset]; exact hadj.symm
      exact hT_not_C v hv hvC
    have hsum1 : ∑ w ∈ G.neighborFinset v, (if w = u then (t : ℝ) else 0) = 0 := by
      rw [Finset.sum_ite_eq' (G.neighborFinset v) u (fun _ => (t : ℝ))]; simp [huNv]
    have hsum2 : ∑ w ∈ G.neighborFinset v, x w = -((G.neighborFinset v ∩ T).card : ℝ) := by
      simp only [hxdef, Finset.sum_sub_distrib]
      rw [hsum1, Finset.sum_ite_mem, Finset.sum_const, nsmul_eq_mul, mul_one]; ring
    rw [hsum2]
    have hcard : (G.neighborFinset v ∩ T).card + (G.neighborFinset v \ T).card = G.degree v := by
      rw [Finset.card_inter_add_card_sdiff, SimpleGraph.card_neighborFinset_eq_degree]
    have hsub : G.neighborFinset v \ T ⊆ C := by
      intro w hw
      rw [Finset.mem_sdiff] at hw
      have hwu : w ≠ u := by rintro rfl; exact huNv hw.1
      have hwins : w ∈ insert u C := by
        by_contra hc
        exact hw.2 (by rw [hTdef, Finset.mem_sdiff]; exact ⟨Finset.mem_univ w, hc⟩)
      rw [Finset.mem_insert] at hwins
      rcases hwins with h | h
      · exact absurd h hwu
      · exact h
    have hCle2 : C.card ≤ 2 := by rw [hCdef, SimpleGraph.card_neighborFinset_eq_degree]; exact hdeg
    have hb : ((G.neighborFinset v \ T).card : ℝ) ≤ 2 := by
      exact_mod_cast le_trans (Finset.card_le_card hsub) hCle2
    have hcardR : ((G.neighborFinset v ∩ T).card : ℝ) + ((G.neighborFinset v \ T).card : ℝ)
        = (G.degree v : ℝ) := by exact_mod_cast hcard
    linarith
  -- (3) the quadratic form, expanded then bounded
  have hexp : dotProduct x ((G.lapMatrix ℝ).mulVec x)
      = (G.degree u : ℝ) * (t : ℝ) ^ 2
        + ∑ v ∈ T, ((G.degree v : ℝ) + ∑ w ∈ G.neighborFinset v, x w) := by
    have e0 : dotProduct x ((G.lapMatrix ℝ).mulVec x)
        = ∑ v, x v * ((G.degree v : ℝ) * x v - ∑ w ∈ G.neighborFinset v, x w) := by
      simp only [dotProduct, SimpleGraph.lapMatrix_mulVec_apply]
    have hgu : x u * ((G.degree u : ℝ) * x u - ∑ w ∈ G.neighborFinset u, x w)
        = (G.degree u : ℝ) * (t : ℝ) ^ 2 := by
      have hzero : ∑ w ∈ G.neighborFinset u, x w = 0 := by
        apply Finset.sum_eq_zero
        intro w hw
        rw [← hCdef] at hw
        exact hxC w hw
      rw [hzero, hxu]; ring
    have hCsum : ∑ v ∈ C, x v * ((G.degree v : ℝ) * x v - ∑ w ∈ G.neighborFinset v, x w) = 0 := by
      apply Finset.sum_eq_zero
      intro v hv
      rw [hxC v hv]; ring
    have hTg : ∑ v ∈ T, x v * ((G.degree v : ℝ) * x v - ∑ w ∈ G.neighborFinset v, x w)
        = ∑ v ∈ T, ((G.degree v : ℝ) + ∑ w ∈ G.neighborFinset v, x w) := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [hxT v hv]; ring
    rw [e0, ← Finset.sum_sdiff (Finset.subset_univ (insert u C)), ← hTdef,
      Finset.sum_insert huC, hgu, hCsum, hTg]
    ring
  have hTbound : ∑ v ∈ T, ((G.degree v : ℝ) + ∑ w ∈ G.neighborFinset v, x w) ≤ 2 * t := by
    calc ∑ v ∈ T, ((G.degree v : ℝ) + ∑ w ∈ G.neighborFinset v, x w)
        ≤ ∑ _v ∈ T, (2 : ℝ) := Finset.sum_le_sum hterm
      _ = 2 * t := by rw [Finset.sum_const, nsmul_eq_mul, htdef]; ring
  have hQ : dotProduct x ((G.lapMatrix ℝ).mulVec x) ≤ 2 * ∑ i, (x i) ^ 2 := by
    rw [hsq, hexp]
    have hdu : (G.degree u : ℝ) ≤ 2 := by exact_mod_cast hdeg
    nlinarith [hTbound, mul_le_mul_of_nonneg_right hdu (sq_nonneg (t : ℝ))]
  exact algConn_le_two_of_testvector G x hx0 hxne hQ

end ACMax
end


/-! ########################################################################################
   PART III --- Reduction to the residual core

   Any counterexample can be normalised: minimum degree 3 and no edge joining two degree-3
   vertices. What survives is the *starved census*.
   ######################################################################################## -/

/- ---------------------------------------- Reduction.Reduction ------------- -/
section
/-! Definitions only (from `ACMaxConjecture/Reduction/Reduction.lean`); the theorems of that module are not
    reachable from the main theorem and have been pruned. -/

namespace ACMax

open scoped Classical

/-! ## The `n`-uniform certificate predicates

Each predicate carries its degree-sum threshold in the exact `n`-uniform form consumed by the
corresponding generic cut lemma, so that the dispatch below gives away no slack. -/

/-- A **good triangle**: three mutually adjacent vertices whose degree sum satisfies the
`n`-uniform weighted-cut inequality `n·(∑deg − 6) ≤ 2·(3·(n−3))`.  (The triangle `A = {x,y,z}`
sends exactly `∑deg − 6` edges to `Aᶜ`, so this is precisely the hypothesis of
`algConn_le_two_of_weighted_cut`.)  At `n = 19` this is `∑deg ≤ 11`. -/
def HasGoodTriangle (n : ℕ) (G : SimpleGraph (Fin n)) : Prop :=
  ∃ x y z : Fin n, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
    G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧
    n * (G.degree x + G.degree y + G.degree z - 6) ≤ 2 * (3 * (n - 3))

/-- An **induced `2K₂` on degree-`3` vertices**: four distinct vertices of degree `3` spanning
exactly the two edges `ab`, `cd`.  Its degree sum is `12`, so `algConn_le_two_of_ind_2K2`
applies (for every `n`). -/
def HasDeg3Ind2K2 (n : ℕ) (G : SimpleGraph (Fin n)) : Prop :=
  ∃ a b c d : Fin n, ({a, b, c, d} : Finset (Fin n)).card = 4 ∧
    G.degree a = 3 ∧ G.degree b = 3 ∧ G.degree c = 3 ∧ G.degree d = 3 ∧
    G.Adj a b ∧ G.Adj c d ∧ ¬G.Adj a c ∧ ¬G.Adj a d ∧ ¬G.Adj b c ∧ ¬G.Adj b d

/-- A **good `C₄`**: an induced `4`-cycle `a-b-c-d-a` with the `n`-uniform threshold
`n·(∑deg − 8) ≤ 2·(4·(n−4))` — exactly the hypothesis of `algConn_le_two_of_good_C4`.
At `n = 19` this is `∑deg ≤ 14`. -/
def HasGoodC4 (n : ℕ) (G : SimpleGraph (Fin n)) : Prop :=
  ∃ a b c d : Fin n, ({a, b, c, d} : Finset (Fin n)).card = 4 ∧
    G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
    n * (G.degree a + G.degree b + G.degree c + G.degree d - 8) ≤ 2 * (4 * (n - 4))

/-- A **good `K_{2,3}`**: an induced complete bipartite `K_{2,3}` (parts `{a,b}`, `{c,d,e}`)
with the `n`-uniform threshold `n·(∑deg − 12) ≤ 2·(5·(n−5))` — exactly the hypothesis of
`algConn_le_two_of_good_K23`.  At `n = 19` this is `∑deg ≤ 19`. -/
def HasGoodK23 (n : ℕ) (G : SimpleGraph (Fin n)) : Prop :=
  ∃ a b c d e : Fin n, ({a, b, c, d, e} : Finset (Fin n)).card = 5 ∧
    G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
    ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
    n * (G.degree a + G.degree b + G.degree c + G.degree d + G.degree e - 12)
      ≤ 2 * (5 * (n - 5))

/-! ## The residual predicate -/

/-- **The residual core** — exactly the class of graphs that survives the generic reduction
steps 1–5 (see the module docstring).  Every field is the *precise* negation of the branch
condition the corresponding step consumes; nothing is weakened and nothing extraneous is added:

* `connected` — step 1 (disconnected graphs are closed by `algConn_le_two_of_not_connected`);
* `min_degree` — step 2 (a degree-`≤2` vertex is closed by `algConn_le_two_of_low_degree_vertex`);
* `edge_card`, `n_ge` — the standing hypotheses (from which `≥ 8` degree-`3` vertices follow,
  `card_deg3_ge_eight`);
* `no_good_triangle` — step 4a (weighted cut on a triangle);
* `iso_deg3` — the negation of "every degree-`3` vertex has a degree-`3` neighbour"
  (step 5 consumes that hypothesis to extract an induced `2K₂` inside the degree-`3` set);
* `no_deg3_ind2K2` — step 5's certificate directly (an induced `2K₂` on degree-`3` vertices
  closes the graph regardless of how it was found);
* `no_good_C4`, `no_good_K23` — steps 4b, 4c.

For `12 ≤ n ≤ 18` this class is closed unconditionally by the per-`n` developments
(`TwinCert12`–`TwinCert18`); in general it is OPEN. -/
structure ResidualCore (n : ℕ) (G : SimpleGraph (Fin n)) : Prop where
  n_ge : 12 ≤ n
  edge_card : G.edgeFinset.card = 2 * (n - 2)
  connected : G.Connected
  min_degree : ∀ v : Fin n, 3 ≤ G.degree v
  iso_deg3 : ∃ t : Fin n, G.degree t = 3 ∧ ∀ w : Fin n, G.Adj t w → G.degree w ≠ 3
  no_good_triangle : ¬HasGoodTriangle n G
  no_deg3_ind2K2 : ¬HasDeg3Ind2K2 n G
  no_good_C4 : ¬HasGoodC4 n G
  no_good_K23 : ¬HasGoodK23 n G

-- NOTE (2026-07-14): the residual statement `residual_algConn_le_two` — every `ResidualCore`
-- graph has algebraic connectivity at most `2` — was formerly the single `sorry` of this file
-- (the sharpest honest form of the then-open conjecture).  It is now PROVED, axiom-clean, in
-- `ACMaxConjecture.Band.Final` as a corollary of the full conjecture
-- `ACMax.acmax_conjecture_general`; it cannot live here because `Band.Final` (transitively)
-- imports this file.  The unconditional `n ≥ 12` master dispatch
-- (`algConn_le_two_of_card_general`) lives there too, for the same reason.

/-! ## Step 3: the handshake counting lemma -/

/-! ## The master reduction -/

/-! ## Sanity checks at `n = 19`

The `n`-uniform thresholds specialise at `n = 19` to exactly the numeric thresholds used by the
per-`n` residual `exists_twin_signed_cert_nineteen` (`TwinCert19.lean`): -/

/-- Good-triangle threshold at `n = 19`: `19·(S−6) ≤ 2·(3·16) = 96 ⟺ S ≤ 11`. -/
example : ∀ S : ℕ, 19 * (S - 6) ≤ 2 * (3 * (19 - 3)) ↔ S ≤ 11 := by intro S; omega

/-- Good-`C₄` threshold at `n = 19`: `19·(S−8) ≤ 2·(4·15) = 120 ⟺ S ≤ 14`. -/
example : ∀ S : ℕ, 19 * (S - 8) ≤ 2 * (4 * (19 - 4)) ↔ S ≤ 14 := by intro S; omega

/-- Good-`K_{2,3}` threshold at `n = 19`: `19·(S−12) ≤ 2·(5·14) = 140 ⟺ S ≤ 19`. -/
example : ∀ S : ℕ, 19 * (S - 12) ≤ 2 * (5 * (19 - 5)) ↔ S ≤ 19 := by intro S; omega

end ACMax
end

/- ---------------------------------------- Reduction.Residual -------------- -/
section
/-!
# Uniformly-provable foundation layers for the general ACMAX residual program

This file formalizes, **for general `n`** (no `Fin`-enumeration, no `decide`; only
counting / pigeonhole / `omega`), the four foundation layers of the uniform residual
program identified by the investigation of the per-`n` architecture (`n = 12..19`):

* **L1 — thresholds as functions of `n`.**  The `n`-uniform good-certificate inequalities
  `n·(Σdeg − 2k) ≤ 2k(n−k)` of `Reduction.Reduction` are converted to explicit per-degree-sum
  thresholds `goodTriThreshold / goodC4Threshold / goodK23Threshold` (`Σdeg ≤ thr(n)`),
  together with the full saturation ladder: the good-triangle threshold is `11` for **all**
  `n ≥ 18`, the good-`C₄` threshold is `14` on `16 ≤ n < 32` and `15` for `n ≥ 32`, and the
  good-`K₂,₃` threshold is `19` on `17 ≤ n < 25`, `20` on `25 ≤ n < 50` and `21` for
  `n ≥ 50` (after `n = 50` the whole good-certificate layer is literally `n`-invariant).

* **L2 — the handshake package for `ResidualCore`.**  With `D = {deg = 3}`,
  `Hub = {deg ≥ 4}`: `∑ deg = 4n − 8`; `|D| + |Hub| = n`; the **excess identity**
  `∑_{Hub} (deg − 3) = n − 8`; hence `|Hub| ≤ n − 8` (and `|D| ≥ 8`, re-exported from
  `card_deg3_ge_eight`); and the generalized `e(M)/e_H` handshake
  `2·e(M) + 6·|Hub| = 2(n+4) + 2·e_H` (in incidence-sum form), the `n`-generic form of the
  per-`n` formulas `e(M) = (n+4) − 3|Hub| + e_H` (`= 22 − 3|Hub| + e_H` at `n = 18`,
  `23 − 3|Hub| + e_H` at `n = 19`).  No all-hubs-degree-4 hypothesis is needed: the excess
  identity supplies `∑_{Hub} deg = 3|Hub| + (n − 8)` in general.

* **L3 — the share lemmas, generalized.**  Two non-adjacent degree-`4` hubs share at most
  **one** common `M`-isolated degree-`3` twin for every `n ≥ 16` (two shared twins form an
  induced `C₄` of `Σdeg = 14 ≤ goodC4Threshold n`), and two non-adjacent degree-`≤ 5` hubs
  share at most **two** for every `n ≥ 17` (three form an induced `K₂,₃` of
  `Σdeg ≤ 19 ≤ goodK23Threshold n`) — the `n`-generic ports of
  `nonadj_hubs_share_le_one_iso` / `nonadj_hubs_share_le_two_iso`, consuming
  `¬HasGoodC4 n G` / `¬HasGoodK23 n G` verbatim.

* **L7 — the TWO-BLOCK construction** (the validated 6th cut, the umbrella of the five
  per-`n` boundary configurations and the certificate that kills the `n ≥ 23` fat-regime
  escaper family).  `TwoBlockConfig` asks for disjoint equal-size blocks `P, N` with
  `2·e(P,N) + leak(P) + leak(N) ≤ 4|P|`, where `leak(X) = e(X, Xᶜ)` **includes** the
  cross-edges (`leak(P) = e(P,N) + e(P,Z)`), so the form is *exactly* equal to the
  hypothesis `4·e(P,N) + e(P,Z) + e(N,Z) ≤ 4|P|` of `algConn_le_two_of_signed`
  (`twoBlock_eq_signed`; validated numerically on the verified `n = 23, 25` escapers: both forms
  agree exactly, values `21 ≤ 44`, `23 ≤ 44`, `25 ≤ 40`, Rayleigh `≤ 1.25`).  The certificate
  `two_block_cut_certificate : TwoBlockConfig n G → algConn G ≤ 2` is a direct application
  of the already-general signed-cut lemma.  Any witness assembled in the signed form — in
  particular the output of each of the five per-`n` `*_cut_certificate` lemmas — is a
  `TwoBlockConfig` witness by `twoBlockConfig_iff_signed`.

Everything here is sorry-free and axiom-clean.
-/

namespace ACMax

open scoped Classical

/-! ## L1 — good-certificate thresholds as functions of `n`

The generic cut criteria of `Reduction.Reduction` are `n·(Σdeg − 2k) ≤ 2·(k·(n − k))` for the
`k`-vertex gadgets (`k = 3` triangle, `4` cycle, `5` `K₂,₃`).  Solving for `Σdeg` gives the
explicit thresholds below (`ℕ`-division; `thr = 2k + ⌊2k(n−k)/n⌋`). -/

/-- Degree-sum threshold for a **good triangle**: `Σdeg ≤ goodTriThreshold n` iff the
`n`-uniform inequality `n·(Σdeg − 6) ≤ 2·(3·(n−3))` holds.  Equals `11` for all `n ≥ 18`. -/
def goodTriThreshold (n : ℕ) : ℕ := 6 + 6 * (n - 3) / n

/-- Degree-sum threshold for a **good `C₄`**: `Σdeg ≤ goodC4Threshold n` iff
`n·(Σdeg − 8) ≤ 2·(4·(n−4))`.  Equals `14` on `16 ≤ n < 32` and `15` for all `n ≥ 32`. -/
def goodC4Threshold (n : ℕ) : ℕ := 8 + 8 * (n - 4) / n

/-! ### The saturation ladder -/

/-! ## L2 — the handshake package

Throughout, `D = univ.filter (deg = 3)` and `Hub = univ.filter (4 ≤ deg)`. -/

/-- **Bipartite double count** (generic-`V` port of `cross_count_nineteen`): for any two
vertex sets, the `X→Y` incidences equal the `Y→X` incidences.  The `DecidableEq` binder
lets the lemma instantiate to whichever instance the call site elaborated with
(`instDecidableEqFin` at `Fin n`, `Classical.propDecidable` at generic `V`). -/
theorem cross_count {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (X Y : Finset V) :
    ∑ v ∈ X, (G.neighborFinset v ∩ Y).card = ∑ w ∈ Y, (G.neighborFinset w ∩ X).card := by
  have hL : ∀ v : V, (G.neighborFinset v ∩ Y).card
      = ∑ w ∈ Y, (if G.Adj v w then 1 else 0) := by
    intro v
    rw [Finset.inter_comm, ← Finset.filter_mem_eq_inter, Finset.card_filter]
    exact Finset.sum_congr rfl (fun w _ => by simp only [G.mem_neighborFinset])
  have hR : ∀ w : V, (G.neighborFinset w ∩ X).card
      = ∑ v ∈ X, (if G.Adj v w then 1 else 0) := by
    intro w
    rw [Finset.inter_comm, ← Finset.filter_mem_eq_inter, Finset.card_filter]
    exact Finset.sum_congr rfl
      (fun v _ => by simp only [G.mem_neighborFinset, SimpleGraph.adj_comm])
  simp_rw [hL, hR]
  exact Finset.sum_comm

/-- **(a) Degree sum.**  `2(n−2)` edges give `∑ deg = 4n − 8` (`n ≥ 2`). -/
theorem residual_degree_sum (n : ℕ) (hn : 2 ≤ n) (G : SimpleGraph (Fin n))
    (hm : G.edgeFinset.card = 2 * (n - 2)) :
    ∑ v : Fin n, G.degree v = 4 * n - 8 := by
  rw [SimpleGraph.sum_degrees_eq_twice_card_edges, hm]
  omega

/-! ## L3 — the share lemmas, generalized

`n`-generic ports of `nonadj_hubs_share_le_one_iso` / `nonadj_hubs_share_le_two_iso`
(`TwinCert19Core`), consuming `¬HasGoodC4 n G` / `¬HasGoodK23 n G` verbatim.  The
constants are exactly those of the per-`n` layer from the respective tie points onward:
share `≤ 1` for degree-4 pairs from `n = 16` (`C₄` tie `Σ = 14`), share `≤ 2` for
degree-`≤ 5` pairs from `n = 17` (`K₂,₃` tie `Σ = 19`); both only gain slack as `n` grows. -/

/-! ## L7 — the TWO-BLOCK construction (the validated 6th cut)

`leak(X) := ∑_{v∈X} |N(v) \ X| = e(X, Xᶜ)` counts **all** edges leaving `X`, including
those into the opposite block.  Since `N` and `Z = (P ∪ N)ᶜ` partition `Pᶜ ⊇ N(p) \ P`,
`leak(P) = e(P,N) + e(P,Z)` and symmetrically `leak(N) = e(N,P) + e(N,Z)` with
`e(N,P) = e(P,N)`; hence

  `2·e(P,N) + leak(P) + leak(N) = 4·e(P,N) + e(P,Z) + e(N,Z)`,

so the report form of the two-block inequality is *literally equal* to the hypothesis of
`algConn_le_two_of_signed` (there is no discrepancy — validated to exact integer equality
on the verified `n = 23, 25` fat-regime escapers). -/

/-- **The TWO-BLOCK signed-cut configuration** (the 6th construction): disjoint equal-size
nonempty blocks `P, N` with

  `2·e(P,N) + leak(P) + leak(N) ≤ 4·|P|`,   `leak(X) = ∑_{v∈X} |N(v) \ X|`.

All five per-`n` boundary configurations (`SingleVertex`, `TwoTwin`, `TwoHub`,
`HubTriangle`, `StarTriangle`) are `|P| = 3` instances (their `_cut_certificate` lemmas
output exactly the equivalent signed form — see `twoBlockConfig_iff_signed`), and the new
fat-regime instances (two disjoint closed carrier stars; a starved internally-bound hub
cycle vs any sparse block) kill every verified `n ≥ 23` escaper of the 5-construction set.

Stated for an arbitrary finite vertex type (like the whole spectral base layer), so that
its instances match `algConn_le_two_of_signed` exactly; at `Fin n` this is the
`TwoBlockConfig n G` of the residual program. -/
def TwoBlockConfig {V : Type*} [Fintype V] (G : SimpleGraph V) : Prop :=
  ∃ P N : Finset V, Disjoint P N ∧ P.card = N.card ∧ 0 < P.card ∧
    2 * (∑ p ∈ P, (G.neighborFinset p ∩ N).card)
      + (∑ p ∈ P, (G.neighborFinset p \ P).card)
      + (∑ q ∈ N, (G.neighborFinset q \ N).card)
    ≤ 4 * P.card

end ACMax
end


/-! ########################################################################################
   PART IV --- Census vocabulary and ledgers

   Hubs, twins, twin slots, and the arithmetic that tracks them. Most of this part supplies
   definitions rather than theorems -- the rows that use them are Part VII.
   ######################################################################################## -/

/- ---------------------------------------- Counting.DoubleStar ------------- -/
section
/-!
# Double-open-star certificates and the M-edge dispatch vocabulary

The signed-cut toolbox for two-hub configurations, together with the vocabulary
that classifies a residual graph by its `M`-edges (edges between degree-3
vertices). Two hubs `g ≠ h` and their degree-3 twins assemble a *double open
star*, whose signed cut bounds algebraic connectivity by `2` under an explicit
leak budget.

## Vocabulary

`deg3Set` (the degree-3 set `D`), `hubSet` (degree `≥ 4`), `hubTwins g`
(degree-3 neighbours of `g`), `privTwins g h` / `sharedTwins g h` (twins of `g`
private to it / shared with `h`), `intDeg g` (non-degree-3 neighbours of `g`),
`mCross g h`, `mIncidence` (the `D`–`D` incidence sum), and `isoTwins`
(degree-3 vertices with no degree-3 neighbour).

## Main results

* `W1Config`, `w1_cut_certificate`, `w1_algConn_le_two` — the **W1
  double-open-star certificate**: with `P = {g} ∪ privTwins g h` and
  `N = {h} ∪ privTwins h g ∪ F` (far pads `F` balancing the sizes), the leak
  budget `|F| + intDeg g + intDeg h + 2·sharedTwins + 2·[g ~ h] + 4·mCross ≤ 4`
  produces a `TwoBlockConfig`, hence `algConn G ≤ 2`.
* `eM_trichotomy` — `mIncidence G ∈ {0, 2} ∨ 4 ≤ mIncidence G`, the gate
  splitting the dispatch into the no-`M`-edge, single-`M`-edge and cherry cases.
* `SeaFatBoundary`, `w1Config_of_pair`, `dsValue` — the resource boundary where
  no hub pair yields a cheap W1 witness, and the firing bridge back into
  `W1Config`.
* `two_hub_opposite_twin_twoBlock`, `two_hub_private_pair_twoBlock`,
  `star3_leak_le_six` — raw six-vertex two-block certificates (over
  `[DecidableEq V]`) that tolerate shared twins and `M`-crosses beyond the W1
  master arithmetic, used in the rich-sea regime.
-/

namespace ACMax

open scoped Classical

variable {V : Type*} [Fintype V]

/-! ## The double-star vocabulary -/

/-- The degree-3 set `D`. -/
noncomputable def deg3Set (G : SimpleGraph V) : Finset V :=
  Finset.univ.filter (fun v => G.degree v = 3)

theorem mem_deg3Set {G : SimpleGraph V} {v : V} : v ∈ deg3Set G ↔ G.degree v = 3 := by
  unfold deg3Set
  simp

/-- The degree-3 twins of a hub: `D3(g) = N(g) ∩ D`. -/
noncomputable def hubTwins (G : SimpleGraph V) (g : V) : Finset V :=
  G.neighborFinset g ∩ deg3Set G

/-- The **private** twins of `g` against `h`: `D3(g) \ D3(h)` — the `P`-side block body
of the double open star. -/
noncomputable def privTwins (G : SimpleGraph V) (g h : V) : Finset V :=
  hubTwins G g \ hubTwins G h

/-- The **shared** twins `s(g,h) = D3(g) ∩ D3(h)`. -/
noncomputable def sharedTwins (G : SimpleGraph V) (g h : V) : Finset V :=
  hubTwins G g ∩ hubTwins G h

/-- The **internal degree** `i(g) = deg g − |D3(g)|` — the number of non-degree-3
neighbours (the design's `intdeg`). -/
noncomputable def intDeg (G : SimpleGraph V) (g : V) : ℕ :=
  (G.neighborFinset g \ deg3Set G).card

/-- The **`M`-cross count**: the number of edges between the two private sides (each such
edge is a `D`–`D` edge, i.e. an `M`-edge; in the residual world `e(M) ≤ 1` forces
`mCross ≤ 1`, so this count coincides with the design's `[M-cross]` indicator). -/
noncomputable def mCross (G : SimpleGraph V) (g h : V) : ℕ :=
  ∑ t ∈ privTwins G g h, (G.neighborFinset t ∩ privTwins G h g).card

/-- The adjacency indicator `[g ~ h]`. -/
noncomputable def adjInd (G : SimpleGraph V) (g h : V) : ℕ :=
  if G.Adj g h then 1 else 0

/-- The `D`–`D` incidence sum `∑_{v∈D} |N(v) ∩ D| = 2·e(M)`. -/
noncomputable def mIncidence (G : SimpleGraph V) : ℕ :=
  ∑ v ∈ deg3Set G, (G.neighborFinset v ∩ deg3Set G).card

/-! ### Vocabulary lemmas -/

/-! ## Part 1 — the W1 certificate

The leak/cross bookkeeping of the double open star, block by block. -/

/-- **The W1 (DOUBLE-OPEN-STAR) configuration** — the design's `DS_pair` witness in its
exact validated form (`scratchpad/general_w1_check.py`: 74/74 saved escapers fire, all
assembled witnesses re-verified integer-exactly).  Data: hubs `g ≠ h` and a **far pad
set** `F` (degree-3 vertices with no edge into `P₀ ∪ N₀`) padding the `h`-side to equal
size, satisfying the **master arithmetic**

  `|F| + i(g) + i(h) + 2·s(g,h) + 2·[g ~ h] + 4·mCross(g,h) ≤ 4`

(`|F| = gap`; the `4·mCross` count form matches the design's `4·[M-cross]` indicator on
the whole `e(M) ≤ 1` residual world, and is one-sidedly *stronger* as a hypothesis when
`mCross ≥ 2`, so the certificate below is sound for it verbatim).  Instances: TwoHub is
the `(4,4,2,2,s=0)` **tie**; the clean TwoStar is `(d,d,0,0,s=0)` at slack `4`; blocking
a pair needs DS-value `≥ 5`.  The design's `(+2 M-pad)` refinement (using the `e(M) = 1`
edge pair as a 2-pad at cost `4` instead of `6`) is NOT formalized — the base `≤ 4` form
is the one validated on all 74 + 301 builds. -/
def W1Config (G : SimpleGraph V) : Prop :=
  ∃ g h : V, ∃ F : Finset V,
    4 ≤ G.degree g ∧ 4 ≤ G.degree h ∧ g ≠ h ∧
    (∀ f ∈ F, G.degree f = 3) ∧
    (∀ f ∈ F, ∀ w ∈ insert g (privTwins G g h) ∪ insert h (privTwins G h g),
      ¬G.Adj f w) ∧
    F.card + (privTwins G h g).card = (privTwins G g h).card ∧
    F.card + intDeg G g + intDeg G h + 2 * (sharedTwins G g h).card
      + 2 * adjInd G g h + 4 * mCross G g h ≤ 4

/-! ### Subsumption: TwoHub and TwoStar are W1 instances -/

/-! ## The M-edge dispatch predicates

The case predicates of the glue tree, with the mechanical dispatch-direction
lemmas: the `mIncidence` trichotomy that isolates the cherry / single-`M`-edge /
no-`M`-edge worlds, and the `SeaFatBoundary` resource gate. -/

/-- **C0 — the cherry world**: `e(M) ≥ 2` (incidence form).  Routed to the per-`n`
cherry constructions (SingleVertex / TwoTwin / HubTriangle). -/
def CaseCherry (G : SimpleGraph V) : Prop := 4 ≤ mIncidence G

/-- **C5 — the `e(M) = 0` world.**  Closing counting: NEEDS-NEW-COUNTING (L5.7; the
MaxHub-style extremal counting survives only `n ≤ 20`). -/
def CaseMZero (G : SimpleGraph V) : Prop := mIncidence G = 0

/-- **The DS value of a hub pair** — the design's master-arithmetic left-hand side, with
the gap in `ℕ`-symmetric form `(p_g − p_h) + (p_h − p_g) = |p_g − p_h|`. -/
noncomputable def dsValue (G : SimpleGraph V) (g h : V) : ℕ :=
  ((privTwins G g h).card - (privTwins G h g).card)
    + ((privTwins G h g).card - (privTwins G g h).card)
    + intDeg G g + intDeg G h + 2 * (sharedTwins G g h).card
    + 2 * adjInd G g h + 4 * mCross G g h

/-- **C2 — the ¬W1-resource boundary predicate** (design §2a): every hub pair is
DS-blocked (`value ≥ 5`).  The output of the (open) C2 resource LP: `≤ 1` clean deg-4
hub, `O(√n)` unburied hubs, `e_H ≥ (3/2)(|Hub| − O(√n))` — NEEDS-C2-COUNTING. -/
def SeaFatBoundary (G : SimpleGraph V) : Prop :=
  ∀ g h : V, 4 ≤ G.degree g → 4 ≤ G.degree h → g ≠ h → 5 ≤ dsValue G g h

/-- The `M`-isolated degree-3 twins (`Iso`): degree-3 vertices with no degree-3
neighbour. -/
noncomputable def isoTwins (G : SimpleGraph V) : Finset V :=
  (deg3Set G).filter (fun t => ∀ w : V, G.Adj t w → G.degree w ≠ 3)

end ACMax


/-! ## Rich-sea two-block cut certificates

Raw six-vertex two-block certificates over `[DecidableEq V]`, used in the
rich-sea regime where shared twins and `M`-crosses block the clean W1 master
arithmetic. The `[DecidableEq V]` binder lets every `∩`/`∪` in the statements
instantiate to the ambient instance; `classical_inter_eq` / `classical_sdiff_eq`
bridge it to the `Classical` instance pinned inside `richHubs` / `mIncidence`
(`DecidableEq` is a subsingleton). Key certificates:
`two_hub_opposite_twin_twoBlock`, `two_hub_private_pair_twoBlock`, and the leak
bound `star3_leak_le_six`. -/

namespace ACMax

open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### The classical-instance bridges -/

/-- The hub set: vertices of degree `≥ 4`. -/
noncomputable def hubSet (G : SimpleGraph V) : Finset V :=
  Finset.univ.filter (fun v => 4 ≤ G.degree v)

omit [DecidableEq V] in
theorem mem_hubSet {G : SimpleGraph V} {v : V} : v ∈ hubSet G ↔ 4 ≤ G.degree v := by
  unfold hubSet
  simp

omit [DecidableEq V] in
theorem mem_isoTwins {G : SimpleGraph V} {t : V} :
    t ∈ isoTwins G ↔ G.degree t = 3 ∧ ∀ w : V, G.Adj t w → G.degree w ≠ 3 := by
  unfold isoTwins deg3Set
  simp

/-! ### Iso-twin bookkeeping -/

/-! ### The certificates -/

end ACMax
end

/- ---------------------------------------- Counting.PoorCorner ------------- -/
section
/-! Definitions only (from `ACMaxConjecture/Counting/PoorCorner.lean`); the theorems of that module are not
    reachable from the main theorem and have been pruned. -/

namespace ACMax

open scoped Classical

variable {V : Type*} [Fintype V]

/-! ## Existence of a far twin pair -/

end ACMax


/-! ## The service-bound counting closure (Lemmas S and E)

The service bound behind `exists_far_deg3_pair_lowcross`. Assuming every far
pair has cross `≥ 4`, the far pair from `exists_far_deg3_pair` has an endpoint
that is either an `M`-end or iso. **Lemma E** (`service_count_end`) rules out the
`M`-end via demand `≥ 3k₀` against slot budget `B₀ = k₀` (`phi_end`) and pair
budget `6x + y ≤ k₀² − k₀`. **Lemma S** (`service_count_iso`) rules out the iso
side via demand `≥ 4k − 1` against `B = k + 2` (`phi_iso`) and `6x + y ≤ k² − k`
(`service_supply`); `omega` closes both endgames (`service_endgame_end`,
`service_endgame_iso`). The section builds the vocabulary, threshold bricks,
corner structure, mediator swap, service supply, deg-3 bonus and φ-identities
these two lemmas consume. -/

namespace ACMax

open scoped Classical

/-! ## Vocabulary: the far set of a degree-3 vertex -/

/-- `farOf n G t`: the degree-3 vertices at combinatorial distance `≥ 3` from `t`
(distinct, non-adjacent, no common neighbour). -/
noncomputable def farOf (n : ℕ) (G : SimpleGraph (Fin n)) (t : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun s => G.degree s = 3 ∧ s ≠ t ∧ ¬G.Adj t s ∧
    ∀ w : Fin n, ¬(G.Adj t w ∧ G.Adj s w))

/-! ## Threshold bricks (tri-11 / C4-14, valid for all `n ≥ 18`) -/

/-! ## The corner degree-3 set and the unique `M`-edge -/

/-! ## The mediator regrouping (the anchor swap) -/

/-! ## The service supply bound (shared core of Lemmas S and E) -/

/-! ## The degree-3 bonus bounds -/

/-! ## The φ-identities (slot budgets) -/

/-! ## The omega endgames -/

/-! ## Lemma S and Lemma E -/

/-! ## B2⁺ — the low-cross far pair -/

/-! ## The band dispatch and the corner closure -/

end ACMax
end

/- ---------------------------------------- Counting.Cherry ----------------- -/
section
/-! Definitions only (from `ACMaxConjecture/Counting/Cherry.lean`); the theorems of that module are not
    reachable from the main theorem and have been pruned. -/

namespace ACMax

open scoped Classical

variable {V : Type*} [Fintype V]

/-! ## The cherry -/

/-- A **cherry**: a degree-`3` centre `z` with two distinct, non-adjacent degree-`3`
neighbours `x, y` — the `P₃` inside the degree-`3` graph `M` that every `e(M) ≥ 2`
residual contains (`exists_cherry`).  The blocks below always use the cherry as the
`N`-side `{z, x, y}` (leak `≤ 5` for size `3`: excess `−1`, the best small block in the
calculus). -/
structure Cherry (G : SimpleGraph V) (x z y : V) : Prop where
  deg_x : G.degree x = 3
  deg_z : G.degree z = 3
  deg_y : G.degree y = 3
  adj_zx : G.Adj z x
  adj_zy : G.Adj z y
  ne_xy : x ≠ y
  nadj_xy : ¬G.Adj x y

namespace Cherry

variable {G : SimpleGraph V} {x z y : V}

end Cherry

/-! ## Small Finset helpers -/

set_option linter.unusedSectionVars false in
/-! ## The cherry `N`-side leak bound and the assembly lemma -/

/-! ## The three cherry cut certificates -/

/-! ## Cherry extraction -/

/-! ## The counting layer -/

/-- The **cherry-touching hubs**: hubs adjacent to a cherry vertex. -/
noncomputable def cherryHubs (G : SimpleGraph V) (x z y : V) : Finset V :=
  (hubSet G).filter (fun w => G.Adj w z ∨ G.Adj w x ∨ G.Adj w y)

/-! ## The pigeonholes -/

/-- The **rich low hubs**: hubs of degree `≤ 5` with at least two `M`-isolated twins —
exactly the TwoTwin-eligible centres. -/
noncomputable def richLowHubs (G : SimpleGraph V) : Finset V :=
  (hubSet G).filter
    (fun w => G.degree w ≤ 5 ∧ 2 ≤ (G.neighborFinset w ∩ isoTwins G).card)

/-- The **bad neighbours** of an apex `t` against a cherry: neighbours of degree `≥ 5`
or touching the cherry — the vertices that block the SingleVertex pair selection. -/
noncomputable def badApexNbrs (G : SimpleGraph V) (x z y t : V) : Finset V :=
  (G.neighborFinset t).filter (fun w => 5 ≤ G.degree w ∨ w ∈ cherryHubs G x z y)

/-! ## The dispatch -/

end ACMax


/-! ## Closing the blocked cherry corner in the sea `e(M) = 2` regime

Closes the residual `blockedCherryCorner` of `caseCherry_dichotomy` when
`mIncidence G = 4` (`e(M) = 2`, so `M` is exactly the `P₃` cherry) and `Δ ≤ 4`
(the sea), for every `n ≥ 18`. With `e(M) = 2` the cherry carries the whole of
`M` (`eM_four_nbrs`), so every degree-3 vertex outside `{x, z, y}` is an iso twin
and `|Iso| ≥ 5` (`eM_four_iso_card`). In the sea *bad = cherry-touching*, so the
corner demands `∑_{t∈Iso} |N(t) ∩ CT| ≥ 2|Iso|`, forcing `≥ 3` rich
cherry-touching hubs, of which `z` blocks at most one — hence two `z`-avoiding
rich hubs (`corner_rich_pair_exists`). Such a pair closes (`p3_pair_close`): the
crossing budget vanishes (`mCross_eq_zero_of_zavoid`) and a short case analysis
on `|D3| ∈ {3, 4}` and adjacency fires `W1Config` with or without a far pad, or
falls back to the raw `two_hub_private_pair_twoBlock`. -/

namespace ACMax

open scoped Classical

variable {V : Type*} [Fintype V]

/-! ## Small helpers -/

/-- The **iso-twin neighbours** of a hub, as a pinned `def` so that its instances stay
stable across the `Fin n` / generic-`V` boundary. -/
noncomputable def isoNbrs (G : SimpleGraph V) (g : V) : Finset V :=
  G.neighborFinset g ∩ isoTwins G

/-! ## The `e(M) = 2` structure: the cherry is the whole of `M` -/

/-! ## The pair atoms -/

/-! ## The pair closes -/

/-! ## The pigeonhole: two `z`-avoiding rich cherry-touching hubs exist -/

/-! ## The corner closure and the C0 assembly -/

end ACMax
end

/- ---------------------------------------- Counting.CherryMShape ----------- -/
section
/-! Definitions only (from `ACMaxConjecture/Counting/CherryMShape.lean`); the theorems of that module are not
    reachable from the main theorem and have been pruned. -/

namespace ACMax

open scoped Classical

variable {V : Type*} [Fintype V]

/-! ## Small neighbourhood atoms -/

/-! ## The exclusion atoms (F0 / F1 / F5 / the universal share bound) -/

/-! ## The iso-twin supply and the corner pigeonhole -/

/-! ## The five M-shapes

Each shape structure records: the degrees, the `M`-edges, all pairwise
distinctness, the **`M`-neighbour pinning** of every shape vertex (`mnbr_*`: its
only degree-`3` neighbours are its `M`-partners), and the isolation of every
degree-`3` vertex outside the shape (`iso_rest`).  These are exactly the facts the
classification tree produces and the kill lemmas consume. -/

/-- The `P4` shape: `M` is the path `a−b−c−d` (plus iso twins). -/
structure MShapeP4 (G : SimpleGraph V) (a b c d : V) : Prop where
  deg_a : G.degree a = 3
  deg_b : G.degree b = 3
  deg_c : G.degree c = 3
  deg_d : G.degree d = 3
  adj_ab : G.Adj a b
  adj_bc : G.Adj b c
  adj_cd : G.Adj c d
  ne_ac : a ≠ c
  ne_ad : a ≠ d
  ne_bd : b ≠ d
  mnbr_a : ∀ w : V, G.Adj a w → G.degree w = 3 → w = b
  mnbr_b : ∀ w : V, G.Adj b w → G.degree w = 3 → w = a ∨ w = c
  mnbr_c : ∀ w : V, G.Adj c w → G.degree w = 3 → w = b ∨ w = d
  mnbr_d : ∀ w : V, G.Adj d w → G.degree w = 3 → w = c
  iso_rest : ∀ v : V, G.degree v = 3 → v ≠ a → v ≠ b → v ≠ c → v ≠ d →
    v ∈ isoTwins G

namespace MShapeP4

variable {G : SimpleGraph V} {a b c d : V}

end MShapeP4

/-- The `claw` shape: `M` is `K_{1,3}` at centre `z₀` with leaves `x₁, x₂, x₃`. -/
structure MShapeClaw (G : SimpleGraph V) (z₀ x₁ x₂ x₃ : V) : Prop where
  deg_z : G.degree z₀ = 3
  deg_1 : G.degree x₁ = 3
  deg_2 : G.degree x₂ = 3
  deg_3 : G.degree x₃ = 3
  adj_1 : G.Adj z₀ x₁
  adj_2 : G.Adj z₀ x₂
  adj_3 : G.Adj z₀ x₃
  ne_12 : x₁ ≠ x₂
  ne_13 : x₁ ≠ x₃
  ne_23 : x₂ ≠ x₃
  mnbr_1 : ∀ w : V, G.Adj x₁ w → G.degree w = 3 → w = z₀
  mnbr_2 : ∀ w : V, G.Adj x₂ w → G.degree w = 3 → w = z₀
  mnbr_3 : ∀ w : V, G.Adj x₃ w → G.degree w = 3 → w = z₀
  iso_rest : ∀ v : V, G.degree v = 3 → v ≠ z₀ → v ≠ x₁ → v ≠ x₂ → v ≠ x₃ →
    v ∈ isoTwins G

/-- The `chair` shape: centre `q` with leaves `l₁, l₂` and the path `q−p−e`. -/
structure MShapeChair (G : SimpleGraph V) (q l₁ l₂ p e : V) : Prop where
  deg_q : G.degree q = 3
  deg_l₁ : G.degree l₁ = 3
  deg_l₂ : G.degree l₂ = 3
  deg_p : G.degree p = 3
  deg_e : G.degree e = 3
  adj_l₁ : G.Adj q l₁
  adj_l₂ : G.Adj q l₂
  adj_p : G.Adj q p
  adj_pe : G.Adj p e
  ne_l₁l₂ : l₁ ≠ l₂
  ne_l₁p : l₁ ≠ p
  ne_l₂p : l₂ ≠ p
  ne_l₁e : l₁ ≠ e
  ne_l₂e : l₂ ≠ e
  ne_qe : q ≠ e
  mnbr_l₁ : ∀ w : V, G.Adj l₁ w → G.degree w = 3 → w = q
  mnbr_l₂ : ∀ w : V, G.Adj l₂ w → G.degree w = 3 → w = q
  mnbr_p : ∀ w : V, G.Adj p w → G.degree w = 3 → w = q ∨ w = e
  mnbr_e : ∀ w : V, G.Adj e w → G.degree w = 3 → w = p
  iso_rest : ∀ v : V, G.degree v = 3 → v ≠ q → v ≠ l₁ → v ≠ l₂ → v ≠ p → v ≠ e →
    v ∈ isoTwins G

/-- The `S22` shape: the double star — adjacent centres `q₁ ~ q₂` with leaves
`l₁, l₂` at `q₁` and `m₁, m₂` at `q₂`. -/
structure MShapeS22 (G : SimpleGraph V) (q₁ q₂ l₁ l₂ m₁ m₂ : V) : Prop where
  deg_q₁ : G.degree q₁ = 3
  deg_q₂ : G.degree q₂ = 3
  deg_l₁ : G.degree l₁ = 3
  deg_l₂ : G.degree l₂ = 3
  deg_m₁ : G.degree m₁ = 3
  deg_m₂ : G.degree m₂ = 3
  adj_qq : G.Adj q₁ q₂
  adj_l₁ : G.Adj q₁ l₁
  adj_l₂ : G.Adj q₁ l₂
  adj_m₁ : G.Adj q₂ m₁
  adj_m₂ : G.Adj q₂ m₂
  ne_l₁l₂ : l₁ ≠ l₂
  ne_m₁m₂ : m₁ ≠ m₂
  ne_q₁m₁ : q₁ ≠ m₁
  ne_q₁m₂ : q₁ ≠ m₂
  ne_q₂l₁ : q₂ ≠ l₁
  ne_q₂l₂ : q₂ ≠ l₂
  ne_l₁m₁ : l₁ ≠ m₁
  ne_l₁m₂ : l₁ ≠ m₂
  ne_l₂m₁ : l₂ ≠ m₁
  ne_l₂m₂ : l₂ ≠ m₂
  mnbr_l₁ : ∀ w : V, G.Adj l₁ w → G.degree w = 3 → w = q₁
  mnbr_l₂ : ∀ w : V, G.Adj l₂ w → G.degree w = 3 → w = q₁
  mnbr_m₁ : ∀ w : V, G.Adj m₁ w → G.degree w = 3 → w = q₂
  mnbr_m₂ : ∀ w : V, G.Adj m₂ w → G.degree w = 3 → w = q₂
  iso_rest : ∀ v : V, G.degree v = 3 → v ≠ q₁ → v ≠ q₂ → v ≠ l₁ → v ≠ l₂ →
    v ≠ m₁ → v ≠ m₂ → v ∈ isoTwins G

/-- The `C5` shape: `M` is the `5`-cycle `v₀−v₁−v₂−v₃−v₄−v₀`. -/
structure MShapeC5 (G : SimpleGraph V) (v₀ v₁ v₂ v₃ v₄ : V) : Prop where
  deg_0 : G.degree v₀ = 3
  deg_1 : G.degree v₁ = 3
  deg_2 : G.degree v₂ = 3
  deg_3 : G.degree v₃ = 3
  deg_4 : G.degree v₄ = 3
  adj_01 : G.Adj v₀ v₁
  adj_12 : G.Adj v₁ v₂
  adj_23 : G.Adj v₂ v₃
  adj_34 : G.Adj v₃ v₄
  adj_40 : G.Adj v₄ v₀
  ne_02 : v₀ ≠ v₂
  ne_03 : v₀ ≠ v₃
  ne_13 : v₁ ≠ v₃
  ne_14 : v₁ ≠ v₄
  ne_24 : v₂ ≠ v₄
  mnbr_0 : ∀ w : V, G.Adj v₀ w → G.degree w = 3 → w = v₁ ∨ w = v₄
  mnbr_1 : ∀ w : V, G.Adj v₁ w → G.degree w = 3 → w = v₀ ∨ w = v₂
  mnbr_2 : ∀ w : V, G.Adj v₂ w → G.degree w = 3 → w = v₁ ∨ w = v₃
  mnbr_3 : ∀ w : V, G.Adj v₃ w → G.degree w = 3 → w = v₂ ∨ w = v₄
  mnbr_4 : ∀ w : V, G.Adj v₄ w → G.degree w = 3 → w = v₃ ∨ w = v₀
  iso_rest : ∀ v : V, G.degree v = 3 → v ≠ v₀ → v ≠ v₁ → v ≠ v₂ → v ≠ v₃ →
    v ≠ v₄ → v ∈ isoTwins G

/-! ## The S22 kill: the double star splits into its two stars

`P = {q₁, l₁, l₂}` vs `N = {q₂, m₁, m₂}`: the only crossing edge is `q₁q₂`,
each centre leaks `≤ 1`, each leaf `≤ 2` — the exact tie `2·1 + 5 + 5 = 12 = 4·3`.
Unconditional: no corner, no sea, no `n`-threshold. -/

/-! ## The claw / chair / C5 kills: any rich hub TwoTwin-fires

By F1/F5 the `M`-neighbourhood of a degree-`4` hub is a pairwise-`M`-distance-`≥ 3`
set — and in these three shapes every such set misses one of the shape's cherries,
so a rich hub avoids a full cherry and `two_twin_cherry_twoBlock` fires.  The
corner pigeonhole (`corner_rich_one`) supplies the rich hub. -/

/-! ## The P4 kill

The only shape with genuine corner escapers.  Roles for a rich hub `g`
(by F1/F5): `B` (`~b` only), `C` (`~c` only), `A` (`~a ∧ ~d`); anything else
avoids the cherry `(a,b,c)` or `(b,c,d)` and is TT-killed.  The corner
pigeonhole gives two rich cherry-touching hubs, double roles are impossible,
and each role pair fires an explicit cut. -/

/-! ## The M-shape classification

Under `¬goodTriangle` (`n ≥ 6`), `¬goodC4` (`n ≥ 8`) and `¬deg3-2K₂`, the
degree-`3` graph with `e(M) ≥ 3` is exactly one of the five shapes.  The tree:
a vertex of `M`-degree `3` exists (→ claw / chair / S22, by the third-neighbour
case analysis) or not (→ P4 / C5, growing the cherry to a path). -/

/-! ## The assembly: the `e(M) ≥ 3` corner closure and the full Δ ≤ 4 C0 -/

end ACMax


/-! ## The complete `Δ ≤ 4` sea closure

Assembles the `Δ ≤ 4` sub-cases of `ResidualCore` into `residual_sea_algConn_le_two`,
dispatched by `eM_trichotomy` on `mIncidence G` (`= 2·e(M)`): `e(M) ≤ 1` (the poor
corner) via `x0_corner_close`, and `CaseCherry` (`e(M) ≥ 2`) via
`caseCherry_algConn_le_two_of_sea`. -/

namespace ACMax

open scoped Classical

end ACMax
end

/- ---------------------------------------- Counting.CompactCell ------------ -/
section
/-! Definitions only (from `ACMaxConjecture/Counting/CompactCell.lean`); the theorems of that module are not
    reachable from the main theorem and have been pruned. -/

namespace ACMax

open scoped Classical
open Finset

variable {V : Type*} [Fintype V]

/-! ## The `σ` ecology quantities -/

/-- The **slot value function** `σ(d) = (d−3)/(d−2)`: the per-slot worst-case
surplus of a degree-`d` neighbour used as a leak carrier.  `σ(3) = 0`,
`σ(4) = 1/2`, `σ(5) = 2/3`, `σ(6) = 3/4`, `σ → 1`. -/
noncomputable def sigma (d : ℕ) : ℝ := ((d : ℝ) - 3) / ((d : ℝ) - 2)

/-- The **mass factor** `c_u = 1 + Σ_{w∈N(u)} 1/(deg w − 2)`. -/
noncomputable def cW (G : SimpleGraph V) (u : V) : ℝ :=
  1 + ∑ w ∈ G.neighborFinset u, (1 : ℝ) / ((G.degree w : ℝ) - 2)

/-- The **`σ`-sum** `Σσ_u = Σ_{w∈N(u)} σ(deg w)`. -/
noncomputable def sigS (G : SimpleGraph V) (u : V) : ℝ :=
  ∑ w ∈ G.neighborFinset u, sigma (G.degree w)

/-! ### `σ` arithmetic (`L-FB-2` real-valued facts) -/

/-! ## `cW` positivity -/

/-! ## `L-FB-1`: the slot far-pair certificate -/

/-! ## The slot-far-pair packaging and the fat-side assembly -/

/-! ## The spread half: the usable-far-pair firing law

The *spread* (large-diameter) half of the fat side. The workhorse
`algConn_le_two_of_usable_far_pair` is the cross-free instance of the slot
far-pair certificate: two `σ`-usable vertices (`sigS ≤ 2`) at distance `≥ 4`
close, the slot value collapsing to `c_v²·(Σσ_u − 2) + c_u²·(Σσ_v − 2) ≤ 0`. This
strengthens the all-degree-`≤ 4` far-pair law to every usable profile.
`spread_fat_close` discharges any fat `ResidualCore` graph carrying such a pair,
so `HasUsableFarPair` reduces the open input to the compact boundary only. -/

/-! ## The `HasUsableFarPair` packaging + spread closer -/

/-- **A usable clean far pair exists.**  `G` has two vertices at distance `≥ 4`
(combinatorially: `u ≠ v`, `¬Adj u v`, no common neighbour, no `N(u)`–`N(v)` edge)
each of which is `σ`-usable.  This is the exact *spread* witness: present on every
diameter-`≥ 4` "buried" world and absent on every diameter-`3` compact cell
inhabitant. -/
def HasUsableFarPair (G : SimpleGraph V) : Prop :=
  ∃ u v : V, u ≠ v ∧ ¬G.Adj u v ∧ (∀ w : V, ¬(G.Adj u w ∧ G.Adj v w)) ∧
    (∀ w w' : V, G.Adj u w → G.Adj v w' → ¬G.Adj w w') ∧
    sigS G u ≤ 2 ∧ sigS G v ≤ 2

/-! ## σ-profile suppression lemmas

Sharp bounds on the σ-sum `sigS G u = Σ_{w∈N(u)} σ(deg w)` in a min-degree-3
world: `usable_deg3_of_light` (a degree-3 vertex with all neighbours of degree
`≤ 5` is usable) and `nonusable_deg3_structure` (a non-usable degree-3 vertex has
all three neighbours of degree `≥ 4`, one of degree `≥ 6`, and two of degree
`≥ 5`). -/

/-! ### σ arithmetic on the profile intervals -/

/-! ## σ-sum versus the heavy-neighbour count -/

/-! ## The non-usable degree-3 frontier -/

end ACMax


/-! ## The parametric compact-covering theorem

On the compact cell (`¬HasUsableFarPair G`), every vertex outside the radius-3
ball around a usable vertex `u₀` is non-usable. Non-usable light (degree `≤ 4`)
vertices each have a heavy neighbour, so number at most `5·X`, and the heavy
vertices number at most `X`, where `X = ∑_{deg v ≥ 5} (deg v − 4)` is the total
degree excess. Since every degree is at most `4 + X`, the radius-3 ball gives the
covering bound `n ≤ 1 + (4+X) + (4+X)² + (4+X)³ + 6·X` (`compact_covering`): a
compact `ResidualCore` world is finite in `n` for each fixed excess `X`. -/

namespace ACMax

open scoped Classical
open Finset

variable {n : ℕ}

/-- The **total degree excess** `X = ∑_{deg v ≥ 5} (deg v − 4)` (ℕ-valued;
the truncated subtraction is exact since every summand has degree ≥ 5). -/
noncomputable def excessX (n : ℕ) (G : SimpleGraph (Fin n)) : ℕ :=
  ∑ v ∈ Finset.univ.filter (fun v => 5 ≤ G.degree v), (G.degree v - 4)

/-- The **radius-3 combinatorial ball** around `u₀`: `u₀` together with its
neighbours, second neighbours, and third neighbours. -/
noncomputable def closeSet (G : SimpleGraph (Fin n)) (u₀ : Fin n) : Finset (Fin n) :=
  insert u₀ (G.neighborFinset u₀
    ∪ (G.neighborFinset u₀).biUnion (fun w => G.neighborFinset w)
    ∪ ((G.neighborFinset u₀).biUnion (fun w => G.neighborFinset w)).biUnion
        (fun w => G.neighborFinset w))

/-! ## The linear compact-covering theorem

Sharpens the cubic `compact_covering` bound to a **linear** one. With minimum
degree 3 each breadth-first layer satisfies `|Lₖ₊₁| ≤ 4·|Lₖ| + X`, so
`|B₃(u₀)| ≤ 85 + 27·X`; combined with the far-vertex partition (non-usable light
`≤ 5X`, heavy `≤ X`) this gives `n ≤ 53 + 19·X`. The assembly
`acmax_general_of_xbound_linear` uses the linear bound `boundLin` in place of the
cubic one. -/

/-- The linear covering bound evaluated at an excess bound `C₀`: the light-anchor
cover `53 + 6·C₀` (the disjoint-slot 6X covering: heavy counts are dominated
by their own excess pools) when a light usable vertex exists; the second arm
`199990` dominates both the all-usable-heavy case (`n + 8 ≤ 5·29877`) and the
hoarding wall (`199985 = 6·33322 + 53`). -/
def boundLin (C₀ : ℕ) : ℕ := max ((151 + 11 * C₀) / 2) 520

end ACMax
end

/- ---------------------------------------- Counting.HubCross --------------- -/
section
/-! Definitions only (from `ACMaxConjecture/Counting/HubCross.lean`); the theorems of that module are not
    reachable from the main theorem and have been pruned. -/

namespace ACMax

open scoped Classical
open Finset

variable {V : Type*} [Fintype V]

end ACMax


/-! ## Big clean twins

The *big clean twins* `bigCleanTwins G = {u : deg u = 3 ∧ sigS u ≤ 2 ∧
(∃ x ~ u, deg x ≥ 9) ∧ (∀ x ~ u, deg x ≠ 3)}` are the usable degree-3 vertices
with a big neighbour and no degree-3 neighbour. By σ-rigidity their
neighbourhoods are completely determined (`bigCleanTwins_nbr_deg`,
`bigCleanTwins_unique_big`), and the bipartite incidence counts `sum_big_inc_le`
/ `sum_small_inc_le` feed the hub-cross pair-coverage count. -/

namespace ACMax

open scoped Classical
open Finset

/-- The **big clean twins**: usable degree-3 vertices with a degree-`≥ 9`
neighbour and no degree-3 neighbour. -/
noncomputable def bigCleanTwins {n : ℕ} (G : SimpleGraph (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter (fun u : Fin n =>
    G.degree u = 3 ∧ sigS G u ≤ 2 ∧
    (∃ x ∈ G.neighborFinset u, 9 ≤ G.degree x) ∧
    (∀ x ∈ G.neighborFinset u, G.degree x ≠ 3))

end ACMax
end

/- ---------------------------------------- Counting.Quotient --------------- -/
section
/-!
# The quotient (class-vector) master certificate

The opening move of the quotient program for the mid-range
`19 ≤ n ≤ 598 693`: by Haemers interlacing, for *any* partition of the vertex
set into `m` classes, `λ₂(G)` is at most the second eigenvalue of the `m×m`
quotient matrix — and for the *second* eigenvalue specifically, the quotient
bound is witnessed by a **class-constant test vector**, so it follows from the
universal single-vector certificate.  The value of the packaging is that the
Rayleigh data reduces to *aggregate* quantities: class sizes and inter-class
edge counts, exactly what the campaign's counting machinery produces.

* `classSize c i` — the size of class `i`;
* `interEdges G c i j` — the number of **ordered** adjacent pairs `(u,v)` with
  `u` in class `i` and `v` in class `j` (`interEdges i j = interEdges j i`;
  the diagonal counts internal edges twice but is killed by `(x i − x i)² = 0`);
* `algConn_le_two_of_class_vector` — the master: a class-valued vector `x`
  with `Σᵢ nᵢ xᵢ = 0` and

    `Σᵢⱼ Eᵢⱼ (xᵢ − xⱼ)² ≤ 4·Σᵢ nᵢ xᵢ²`

  certifies `algConn G ≤ 2`  (the `4` is `2 × 2`: one factor because ordered
  pairs double-count edges, one from the target `λ₂ ≤ 2`);
* `algConn_le_two_of_sparse_cut` — the classical Fiedler cut bound as the
  `m = 2` instance: `n·e(S, Sᶜ) ≤ 2·|S|·|Sᶜ|` certifies `algConn ≤ 2`
  (stated with the ordered cross count: `n·E ≤ 4·|S|·|Sᶜ|`);
* degree-class handshake identities on the residual cell, expressing the
  quotient data of the degree partition `{3}/{4}/{≥5}` in ledger terms.
-/

namespace ACMax

open scoped Classical
open Finset

variable {V : Type*} [Fintype V]

/-! ## Quotient data -/

/-- The size of class `i` under the class map `c`. -/
noncomputable def classSize {m : ℕ} (c : V → Fin m) (i : Fin m) : ℕ :=
  (Finset.univ.filter (fun v => c v = i)).card

/-- The number of **ordered** adjacent pairs from class `i` to class `j`. -/
noncomputable def interEdges {m : ℕ} (G : SimpleGraph V) (c : V → Fin m)
    (i j : Fin m) : ℕ :=
  ((Finset.univ.filter (fun v => c v = i)) ×ˢ
    (Finset.univ.filter (fun v => c v = j))).filter
      (fun p => G.Adj p.1 p.2) |>.card

/-- Fiberwise decomposition of a vertex sum by classes. -/
theorem sum_classes {m : ℕ} {M : Type*} [AddCommMonoid M]
    (c : V → Fin m) (f : V → M) :
    ∑ v : V, f v
      = ∑ i : Fin m, ∑ v ∈ Finset.univ.filter (fun v => c v = i), f v :=
  (Finset.sum_fiberwise Finset.univ c f).symm

/-- A class-constant square sum aggregates to class sizes. -/
theorem sum_sq_classes {m : ℕ} (c : V → Fin m) (x : Fin m → ℝ) :
    ∑ v : V, x (c v) ^ 2
      = ∑ i : Fin m, (classSize c i : ℝ) * x i ^ 2 := by
  rw [sum_classes c (fun v => x (c v) ^ 2)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_congr rfl (fun v hv => by
    rw [(Finset.mem_filter.mp hv).2]), Finset.sum_const, nsmul_eq_mul]
  rfl

/-- The inter-class count as a double indicator sum over the fibers. -/
theorem interEdges_eq_sum {m : ℕ} (G : SimpleGraph V) (c : V → Fin m)
    (i j : Fin m) :
    (interEdges G c i j : ℝ)
      = ∑ u ∈ Finset.univ.filter (fun v => c v = i),
          ∑ v ∈ Finset.univ.filter (fun v => c v = j),
          (if G.Adj u v then (1 : ℝ) else 0) := by
  classical
  rw [interEdges, Finset.card_filter]
  push_cast
  rw [Finset.sum_product]

/-- The edge quadratic form aggregates to inter-class counts. -/
theorem sum_edge_sq_classes {m : ℕ} (G : SimpleGraph V) (c : V → Fin m)
    (x : Fin m → ℝ) :
    ∑ u : V, ∑ v : V,
        (if G.Adj u v then (x (c u) - x (c v)) ^ 2 else 0)
      = ∑ i : Fin m, ∑ j : Fin m,
          (interEdges G c i j : ℝ) * (x i - x j) ^ 2 := by
  classical
  -- fiberwise in `u`, then in `v`
  rw [sum_classes c (fun u => ∑ v : V,
    (if G.Adj u v then (x (c u) - x (c v)) ^ 2 else 0))]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hswap : ∑ u ∈ Finset.univ.filter (fun v => c v = i), ∑ v : V,
      (if G.Adj u v then (x (c u) - x (c v)) ^ 2 else 0)
      = ∑ j : Fin m, ∑ u ∈ Finset.univ.filter (fun v => c v = i),
          ∑ v ∈ Finset.univ.filter (fun v => c v = j),
          (if G.Adj u v then (x (c u) - x (c v)) ^ 2 else 0) := by
    have h1 : ∀ u : V, ∑ v : V,
        (if G.Adj u v then (x (c u) - x (c v)) ^ 2 else 0)
        = ∑ j : Fin m, ∑ v ∈ Finset.univ.filter (fun v => c v = j),
            (if G.Adj u v then (x (c u) - x (c v)) ^ 2 else 0) := fun u =>
      (Finset.sum_fiberwise Finset.univ c
        (fun v => if G.Adj u v then (x (c u) - x (c v)) ^ 2 else 0)).symm
    rw [Finset.sum_congr rfl fun u _ => h1 u]
    exact Finset.sum_comm
  rw [hswap]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [interEdges_eq_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun u hu => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun v hv => ?_
  rw [(Finset.mem_filter.mp hu).2, (Finset.mem_filter.mp hv).2]
  split <;> ring

/-! ## The master certificate -/

/-- **The quotient master certificate** (Haemers interlacing for `λ₂`).
Given a partition into `m` classes and a class-valued vector `x` with

* balance: `Σᵢ nᵢ·xᵢ = 0`,
* some class of nonzero value is inhabited, and
* the aggregate Rayleigh bound `Σᵢⱼ Eᵢⱼ·(xᵢ − xⱼ)² ≤ 4·Σᵢ nᵢ·xᵢ²`
  (`Eᵢⱼ` the ordered inter-class adjacency counts),

we get `algConn G ≤ 2`.  All data is aggregate: sizes and edge counts. -/
theorem algConn_le_two_of_class_vector [Nonempty V]
    (G : SimpleGraph V) {m : ℕ} (c : V → Fin m) (x : Fin m → ℝ)
    (hbal : ∑ i : Fin m, (classSize c i : ℝ) * x i = 0)
    (hne : ∃ v : V, x (c v) ≠ 0)
    (hQ : ∑ i : Fin m, ∑ j : Fin m,
        (interEdges G c i j : ℝ) * (x i - x j) ^ 2
      ≤ 4 * ∑ i : Fin m, (classSize c i : ℝ) * x i ^ 2) :
    algConn G ≤ 2 := by
  classical
  have hbal' : ∑ v : V, x (c v) = 0 := by
    have h1 : ∑ v : V, x (c v) = ∑ i : Fin m, (classSize c i : ℝ) * x i := by
      rw [sum_classes c (fun v => x (c v))]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_congr rfl (fun v hv => by
        rw [(Finset.mem_filter.mp hv).2]), Finset.sum_const, nsmul_eq_mul]
      rfl
    rw [h1, hbal]
  apply algConn_le_two_of_testvector G (fun v => x (c v)) hbal' hne
  rw [← Matrix.toLinearMap₂'_apply', SimpleGraph.lapMatrix_toLinearMap₂']
  rw [sum_edge_sq_classes G c x, sum_sq_classes c x]
  linarith [hQ]

/-! ## The classical sparse-cut instance (`m = 2`) -/

/-! ## Handshake identities for the quotient data -/

/-- Inter-class counts are symmetric. -/
theorem interEdges_symm {m : ℕ} (G : SimpleGraph V) (c : V → Fin m)
    (i j : Fin m) : interEdges G c i j = interEdges G c j i := by
  classical
  rw [interEdges, interEdges]
  refine Finset.card_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_
  · intro p hp
    rw [Finset.mem_filter, Finset.mem_product] at hp ⊢
    exact ⟨⟨hp.1.2, hp.1.1⟩, G.adj_symm hp.2⟩
  · intro p _ q _ hpq
    exact Prod.ext (congrArg Prod.snd hpq) (congrArg Prod.fst hpq)
  · intro p hp
    refine ⟨(p.2, p.1), ?_, rfl⟩
    rw [Finset.mem_filter, Finset.mem_product] at hp ⊢
    exact ⟨⟨hp.1.2, hp.1.1⟩, G.adj_symm hp.2⟩

/-! ## The two-cluster law (`m = 3`) -/

/-- **The two-cluster law.**  Two disjoint nonempty vertex sets with *no*
edges between them and boundaries `∂₁, ∂₂` (ordered counts of edges leaving
each cluster) satisfying

  `∂₁·|S₂|² + ∂₂·|S₁|² ≤ 2·|S₁|·|S₂|·(|S₁| + |S₂|)`

certify `algConn ≤ 2`.  For equal sizes `s` this reads `∂₁ + ∂₂ ≤ 4s` —
e.g. two disjoint `M`-edges with no cross edges fire at the exact tie
(`∂ = 4` each, `s = 2`), recovering the cell's `2K₂` exclusion. -/
theorem algConn_le_two_of_two_clusters [Nonempty V]
    (G : SimpleGraph V) (S₁ S₂ : Finset V)
    (hS₁ : S₁.Nonempty) (hS₂ : S₂.Nonempty) (hdisj : Disjoint S₁ S₂)
    (hnc : ∀ u ∈ S₁, ∀ v ∈ S₂, ¬G.Adj u v)
    (hcut : ((S₁ ×ˢ (S₁ ∪ S₂)ᶜ).filter (fun p => G.Adj p.1 p.2)).card
          * S₂.card ^ 2
        + ((S₂ ×ˢ (S₁ ∪ S₂)ᶜ).filter (fun p => G.Adj p.1 p.2)).card
          * S₁.card ^ 2
      ≤ 2 * S₁.card * S₂.card * (S₁.card + S₂.card)) :
    algConn G ≤ 2 := by
  classical
  set c : V → Fin 3 := fun v => if v ∈ S₁ then 0 else if v ∈ S₂ then 1 else 2
    with hc
  set x : Fin 3 → ℝ := fun i =>
    if i = 0 then (S₂.card : ℝ) else if i = 1 then -(S₁.card : ℝ) else 0
    with hx
  have hfib0 : Finset.univ.filter (fun v => c v = 0) = S₁ := by
    ext v
    rw [Finset.mem_filter]
    simp only [Finset.mem_univ, true_and, hc]
    by_cases h1 : v ∈ S₁
    · rw [if_pos h1]
      exact ⟨fun _ => h1, fun _ => rfl⟩
    · rw [if_neg h1]
      by_cases h2 : v ∈ S₂
      · rw [if_pos h2]
        exact ⟨fun h => absurd h (by decide), fun h => absurd h h1⟩
      · rw [if_neg h2]
        exact ⟨fun h => absurd h (by decide), fun h => absurd h h1⟩
  have hfib1 : Finset.univ.filter (fun v => c v = 1) = S₂ := by
    ext v
    rw [Finset.mem_filter]
    simp only [Finset.mem_univ, true_and, hc]
    by_cases h1 : v ∈ S₁
    · rw [if_pos h1]
      refine ⟨fun h => absurd h (by decide), fun h => ?_⟩
      exact absurd (Finset.disjoint_left.mp hdisj h1) (fun hh => hh h)
    · rw [if_neg h1]
      by_cases h2 : v ∈ S₂
      · rw [if_pos h2]
        exact ⟨fun _ => h2, fun _ => rfl⟩
      · rw [if_neg h2]
        exact ⟨fun h => absurd h (by decide), fun h => absurd h h2⟩
  have hfib2 : Finset.univ.filter (fun v => c v = 2) = (S₁ ∪ S₂)ᶜ := by
    ext v
    rw [Finset.mem_filter, Finset.mem_compl, Finset.mem_union]
    simp only [Finset.mem_univ, true_and, hc]
    by_cases h1 : v ∈ S₁
    · rw [if_pos h1]
      exact ⟨fun h => absurd h (by decide), fun h => absurd (Or.inl h1) h⟩
    · rw [if_neg h1]
      by_cases h2 : v ∈ S₂
      · rw [if_pos h2]
        exact ⟨fun h => absurd h (by decide), fun h => absurd (Or.inr h2) h⟩
      · rw [if_neg h2]
        exact ⟨fun _ => fun h => h.elim (fun hh => h1 hh) (fun hh => h2 hh),
          fun _ => rfl⟩
  have hx0 : x 0 = (S₂.card : ℝ) := by simp [hx]
  have hx1 : x 1 = -(S₁.card : ℝ) := by simp [hx]
  have hx2 : x 2 = 0 := by simp [hx]
  obtain ⟨s₀, hs₀⟩ := hS₁
  refine algConn_le_two_of_class_vector G c x ?_ ⟨s₀, ?_⟩ ?_
  · -- balance
    rw [Fin.sum_univ_three, classSize, classSize, classSize,
      hfib0, hfib1, hfib2, hx0, hx1, hx2]
    ring
  · -- nonzero at a vertex of `S₁`
    have hcs : c s₀ = 0 := by
      rw [hc]
      simp [hs₀]
    rw [hcs, hx0]
    have : 0 < S₂.card := Finset.card_pos.mpr hS₂
    exact ne_of_gt (by exact_mod_cast this)
  · -- the aggregate Rayleigh bound
    simp only [Fin.sum_univ_three]
    rw [classSize, classSize, classSize, hfib0, hfib1, hfib2]
    -- the S₁–S₂ blocks vanish
    have hE01 : interEdges G c 0 1 = 0 := by
      rw [interEdges, hfib0, hfib1, Finset.card_eq_zero,
        Finset.filter_eq_empty_iff]
      intro p hp
      rw [Finset.mem_product] at hp
      exact hnc p.1 hp.1 p.2 hp.2
    have hE10 : interEdges G c 1 0 = 0 := by
      rw [interEdges_symm, hE01]
    -- the boundary blocks
    have hE02 : interEdges G c 0 2
        = ((S₁ ×ˢ (S₁ ∪ S₂)ᶜ).filter (fun p => G.Adj p.1 p.2)).card := by
      rw [interEdges, hfib0, hfib2]
    have hE12 : interEdges G c 1 2
        = ((S₂ ×ˢ (S₁ ∪ S₂)ᶜ).filter (fun p => G.Adj p.1 p.2)).card := by
      rw [interEdges, hfib1, hfib2]
    have hE20 : interEdges G c 2 0
        = ((S₁ ×ˢ (S₁ ∪ S₂)ᶜ).filter (fun p => G.Adj p.1 p.2)).card := by
      rw [interEdges_symm, hE02]
    have hE21 : interEdges G c 2 1
        = ((S₂ ×ˢ (S₁ ∪ S₂)ᶜ).filter (fun p => G.Adj p.1 p.2)).card := by
      rw [interEdges_symm, hE12]
    rw [hE01, hE10, hE02, hE12, hE20, hE21, hx0, hx1, hx2]
    -- cast the cut hypothesis and close
    set e₁ : ℕ := ((S₁ ×ˢ (S₁ ∪ S₂)ᶜ).filter (fun p => G.Adj p.1 p.2)).card
    set e₂ : ℕ := ((S₂ ×ˢ (S₁ ∪ S₂)ᶜ).filter (fun p => G.Adj p.1 p.2)).card
    have hcutR : (e₁ : ℝ) * (S₂.card : ℝ) ^ 2 + (e₂ : ℝ) * (S₁.card : ℝ) ^ 2
        ≤ 2 * (S₁.card : ℝ) * (S₂.card : ℝ)
          * ((S₁.card : ℝ) + (S₂.card : ℝ)) := by
      have h1 : ((e₁ * S₂.card ^ 2 + e₂ * S₁.card ^ 2 : ℕ) : ℝ)
          ≤ ((2 * S₁.card * S₂.card * (S₁.card + S₂.card) : ℕ) : ℝ) :=
        Nat.cast_le.mpr hcut
      push_cast at h1
      linarith
    ring_nf
    nlinarith [hcutR]


/-! ## The degree-class partition on the residual cell -/

variable {n : ℕ}

/-! ## The two-hub block cut (the endgame seed) -/

end ACMax
end

/- ---------------------------------------- Counting.SigmaCloud ------------- -/
section
/-! Definitions only (from `ACMaxConjecture/Counting/SigmaCloud.lean`); the theorems of that module are not
    reachable from the main theorem and have been pruned. -/

namespace ACMax

open scoped Classical
open Finset

variable {V : Type*} [Fintype V]

end ACMax


/-! ## The unified σ-transfer (`c = 5/4`)

The supply bound behind `β = 105/128`. Partition each heavy vertex `w`
(degree `d ≥ 5`) into `a₃` degree-3 twins, `f` degree-4 and `j` heavy neighbours
(σ-mass `S_w`), so `sigS w = f/2 + S_w`. The transfer inequality
`σ(d)·(a₃ + j) ≤ (5/4)(d − 4) + S_w` charges `σ(d)` per heavy neighbour and
refunds the σ-mass received; summed over heavies the transfer terms cancel
identically, leaving `Σ σ(d)·a₃ ≤ (5/4)·X + exceptions`. It holds for every heavy
vertex except the `W₅` overflow (`1/12`, `sigma_transfer_w5`) and the SFB-capped
usable classes (`a₃ ≥ d − 2`, `5 ≤ d ≤ 15`). The per-degree certificates are
`(d−4)(d−6+2f) ≥ 0` (non-usable), a triple-gap tie at `d = 5, f = 0`, and
`(d−16)(d−2) ≥ 0` (saturated `d ≥ 16`). -/

namespace ACMax

open scoped Classical
open Finset

variable {n : ℕ}

/-! ## σ set-sum bounds -/

/-! ## The neighbourhood profile of a heavy vertex -/

/-! ## The pointwise transfer inequalities -/

/-! ## The extended capped-class count (`d ≤ 15`) -/

/-! ## The exchange identity and the summed transfer -/

/-! ## The `W₅ᵇ` cloud bound

`W₅ᵇ` — usable degree-5 hubs with two twins and a big neighbour — is the sole
class obstructing `β < 7/8`; it is bounded by a two-round pair coverage driven by
the σ-laws. Each member has neighbourhood `{h, ≤4, ≤4, 3, 3}` with `deg h ≥ 9` the
unique non-light neighbour (`w5big_structure`), so LAW A / LAW B fire at side-σ
exactly `1` / slack `1/(deg h − 2)`. Unless a σ-law fires, every member pair has a
light-endpoint common neighbour or cross (`w5big_pair_mechanism`), each big hub
carrying `≤ 269` members (`w5big_cloud_le`), giving `|W₅ᵇ| ≤ 5441`
(`w5big_card_le`). -/

/-- The `W₅ᵇ` class: usable degree-5 hubs with exactly two twins and a big
neighbour. -/
noncomputable def w5big (G : SimpleGraph (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter (fun w : Fin n =>
    G.degree w = 5 ∧ sigS G w ≤ 2 ∧ (hubTwins G w).card = 2
      ∧ ∃ x ∈ G.neighborFinset w, 9 ≤ G.degree x)

end ACMax

namespace ACMax

open scoped Classical
open Finset

section GenericV

variable {V : Type*} [Fintype V]

/-- **The σ-law firing configuration**: either a LAW A apex configuration or
a LAW B cross configuration exists (stated erase-free: the LAW A side
condition is `sigS ≤ 1 + σ(deg g)` and the no-cross condition is pure
adjacency). -/
def W5LawConfig (G : SimpleGraph V) : Prop :=
  (∃ u v g : V, u ≠ v ∧ ¬G.Adj u v ∧ G.Adj u g ∧ G.Adj v g
    ∧ (∀ w : V, w ≠ g → ¬(G.Adj u w ∧ G.Adj v w))
    ∧ (∀ w w' : V, G.Adj u w → w ≠ g → G.Adj v w' → w' ≠ g → ¬G.Adj w w')
    ∧ sigS G u ≤ 1 + sigma (G.degree g)
    ∧ sigS G v ≤ 1 + sigma (G.degree g))
  ∨ (∃ u v h h' : V, u ≠ v ∧ ¬G.Adj u v
    ∧ (∀ w : V, ¬(G.Adj u w ∧ G.Adj v w))
    ∧ G.Adj u h ∧ G.Adj v h'
    ∧ (∀ w w' : V, G.Adj u w → G.Adj v w' → G.Adj w w' → w = h ∧ w' = h')
    ∧ sigS G u + 1 / ((G.degree h : ℝ) - 2) ≤ 2
    ∧ sigS G v + 1 / ((G.degree h' : ℝ) - 2) ≤ 2)

end GenericV

variable {n : ℕ}

end ACMax
end

/- ---------------------------------------- Counting.XBoundAssembly --------- -/
section
/-!
# The master X-bound assembly

Combines the D1 suppressed-mass bound `suppressed_card_le` with the degree
handshake to bound the total excess `X = excessX n G` on the `SeaFatBoundary`
linearly in the number of *usable* (unsuppressed, `sigS ≤ 2`) degree-3 vertices.

1. `deg3_card_eq_eight_add_excess` — handshake: `|D₃| = 8 + X`.
2. `deg3_usable_suppressed_split` — `|D₃| = m + s` (usable + suppressed).
3. `sfb_excess_bound_beta` — the sharpened excess bound on the boundary (`n ≥ 512`),
   dispatched through the slope-`11/2` light-anchor cover
   (`compact_covering_eleven_halves`).
-/

namespace ACMax

open scoped Classical
open Finset

/-- **Handshake**: with `2(n−2)` edges and minimum degree 3, the degree-3 set has
exactly `8 + X` members, where `X = excessX n G` is the total degree excess. -/
theorem deg3_card_eq_eight_add_excess (n : ℕ) (G : SimpleGraph (Fin n))
    (hn : 2 ≤ n) (hm : G.edgeFinset.card = 2 * (n - 2))
    (h3 : ∀ v, 3 ≤ G.degree v) :
    (deg3Set G).card = 8 + excessX n G := by
  classical
  -- handshake: `∑ deg + 8 = 4n`
  have hsum : ∑ v : Fin n, G.degree v = 2 * (2 * (n - 2)) := by
    rw [G.sum_degrees_eq_twice_card_edges, hm]
  have hsum8 : ∑ v : Fin n, G.degree v + 8 = 4 * n := by omega
  set D3 := Finset.univ.filter (fun v : Fin n => G.degree v = 3) with hD3
  set D4 := Finset.univ.filter (fun v : Fin n => G.degree v = 4) with hD4
  set D5 := Finset.univ.filter (fun v : Fin n => 5 ≤ G.degree v) with hD5
  -- the three degree classes partition the vertex set
  have hcard : D3.card + D4.card + D5.card = n := by
    have hpt : ∀ v : Fin n,
        (if G.degree v = 3 then 1 else 0) + (if G.degree v = 4 then 1 else 0)
          + (if 5 ≤ G.degree v then 1 else 0) = 1 := by
      intro v
      have := h3 v
      split_ifs <;> omega
    calc D3.card + D4.card + D5.card
        = ∑ v : Fin n, ((if G.degree v = 3 then 1 else 0)
            + (if G.degree v = 4 then 1 else 0)
            + (if 5 ≤ G.degree v then 1 else 0)) := by
          simp only [hD3, hD4, hD5, Finset.card_filter, ← Finset.sum_add_distrib]
      _ = ∑ _v : Fin n, 1 := Finset.sum_congr rfl (fun v _ => hpt v)
      _ = n := by simp
  -- the degree sum splits along the partition
  have hdegsum : ∑ v : Fin n, G.degree v
      = 3 * D3.card + 4 * D4.card + ∑ v ∈ D5, G.degree v := by
    have hpt : ∀ v : Fin n, G.degree v
        = 3 * (if G.degree v = 3 then 1 else 0) + 4 * (if G.degree v = 4 then 1 else 0)
          + (if 5 ≤ G.degree v then G.degree v else 0) := by
      intro v
      have := h3 v
      split_ifs <;> omega
    calc ∑ v : Fin n, G.degree v
        = ∑ v : Fin n, (3 * (if G.degree v = 3 then 1 else 0)
            + 4 * (if G.degree v = 4 then 1 else 0)
            + (if 5 ≤ G.degree v then G.degree v else 0)) :=
          Finset.sum_congr rfl (fun v _ => hpt v)
      _ = 3 * D3.card + 4 * D4.card + ∑ v ∈ D5, G.degree v := by
          simp only [hD3, hD4, hD5, Finset.card_filter, Finset.sum_filter,
            Finset.mul_sum, mul_ite, mul_one, mul_zero, ← Finset.sum_add_distrib]
  -- the heavy degree sum is the excess plus `4·|D₅|`
  have hex : excessX n G + 4 * D5.card = ∑ v ∈ D5, G.degree v := by
    have h4 : ∀ v ∈ D5, G.degree v - 4 + 4 = G.degree v := by
      intro v hv
      have : 5 ≤ G.degree v := (Finset.mem_filter.mp hv).2
      omega
    calc excessX n G + 4 * D5.card
        = ∑ v ∈ D5, (G.degree v - 4) + ∑ _v ∈ D5, 4 := by
          rw [excessX, ← hD5, Finset.sum_const, smul_eq_mul, mul_comm]
      _ = ∑ v ∈ D5, (G.degree v - 4 + 4) := Finset.sum_add_distrib.symm
      _ = ∑ v ∈ D5, G.degree v := Finset.sum_congr rfl h4
  have hd3 : (deg3Set G).card = D3.card := by rw [deg3Set, ← hD3]
  omega

end ACMax
end

/- ---------------------------------------- Counting.LargeN ----------------- -/
section
/-! Definitions only (from `ACMaxConjecture/Counting/LargeN.lean`); the theorems of that module are not
    reachable from the main theorem and have been pruned. -/

/-! ## Hoarding basics for the two-mega pair

`unblocked_gap_pos_nonadj`: a DS-unblocked pair (`dsValue ≤ 4`) of degree-`≥ 4`
hubs with a positive private-twin gap is non-adjacent (adjacency already costs
`1 + 1 + 1 + 2 = 5 > 4`). -/

namespace ACMax

open scoped Classical
open Finset

variable {V : Type*} [Fintype V]

/-! ## Killing the hoarding regime and the final assembly

`dsValue_comm` (the DS value is symmetric); `hoarding_impossible` (for `n ≥ 520`
on the compact cell a DS-unblocked pair with a positive gap cannot hoard the
degree-3 supply — the cross-pack bound `|Pg|·|Ph| ≤ |D|·(76 + 14S)` contradicts a
quadratic lower bound); `hunblocked_large` (off the `SeaFatBoundary` some pair
fires as a `W1Config`); and the dispatch `acmax_general_final`. -/

end ACMax


/-! ## The 3-connectivity reduction

`HasTwoCut` (a two-vertex cut `{a, b}` separating nonempty disjoint sets with no
cross edges, the hypothesis bundle of `algConn_le_two_of_two_vertex_cut`),
`algConn_le_two_of_hasTwoCut` (any two-cut gives `algConn G ≤ 2`), and
`acmax_general_final_threeconn` (the dispatch with the boundary m-bound hypothesis
weakened by also assuming `¬HasTwoCut G`). -/

namespace ACMax

open scoped Classical
open Finset

/-- A two-vertex cut: `a ≠ b` together with nonempty disjoint `A`, `B`
covering all remaining vertices and with no `A`–`B` edges. -/
def HasTwoCut {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∃ (a b : Fin n) (A B : Finset (Fin n)),
    a ≠ b ∧ A.Nonempty ∧ B.Nonempty ∧ Disjoint A B ∧
    a ∉ A ∪ B ∧ b ∉ A ∪ B ∧
    (∀ v : Fin n, v ∈ A ∨ v ∈ B ∨ v = a ∨ v = b) ∧
    (∀ u ∈ A, ∀ v ∈ B, ¬G.Adj u v)

/-! ## Hub-cross pair coverage: m-bound to max-cloud bound

The payoff of the hub-cross firing law: on the compact boundary cell the usable
degree-3 count `m` is linearly controlled by the max-cloud bound
`A = max_{deg w ≥ 9} #(usable degree-3 neighbours of w)`. By `usable_deg3_split_mid`,
`m ≤ 268 + |T'|` with `T' = bigCleanTwins G`; unless a `FiringConfig` exists,
every ordered pair of `T'` is covered by a common neighbour or a
partner-involving cross (the pure hub–hub cross being excluded by the law), and
charging every cross to the degree-4 partner set gives
`|T'|·(|T'|−1) ≤ (13A + 26)·|T'|`, hence `m ≤ 13·A + 172`
(`usable_deg3_card_le_of_cloud`). `acmax_general_final_cloud` replaces the m-bound
hypothesis of `acmax_general_final_threeconn` by this max-cloud bound. -/

/-! ## The firing configuration -/

/-- A **firing configuration** for the hub-cross law: the full hypothesis set of
`algConn_le_two_of_hub_cross_pair`. -/
def FiringConfig (n : ℕ) (G : SimpleGraph (Fin n)) (u v g g' : Fin n) : Prop :=
  G.degree u = 3 ∧ G.degree v = 3 ∧ u ≠ v ∧ ¬G.Adj u v ∧
  (∀ w, ¬(G.Adj u w ∧ G.Adj v w)) ∧ G.Adj u g ∧ G.Adj v g' ∧
  4 ≤ G.degree g ∧ 4 ≤ G.degree g' ∧
  (∀ w, G.Adj u w → w ≠ g → G.degree w ≤ 4) ∧
  (∀ w, G.Adj v w → w ≠ g' → G.degree w ≤ 4) ∧
  (∀ w w', G.Adj u w → G.Adj v w' → G.Adj w w' → w = g ∧ w' = g')

/-! ## Auxiliary caps -/

/-! ## The pair-coverage master count -/

/-! ## Quadratic root + the m-bound assembly -/

/-! ## The cloud bound and unconditional large-`n` ACMAX

The payoff of the apex-tie law: the A-bound is a theorem. Fix a hub `g` of degree
`≥ 9` with clean twin cloud `C = N(g) ∩ bigCleanTwins G`, `A = |C|`. Unless an
apex configuration exists, every ordered pair of `C` is covered by a shared
degree-4 partner (`≤ 6A`) or a partner–partner cross (`≤ 128A`), so
`A(A−1) ≤ 102A`, i.e. `A ≤ 61`, and the usable cloud of any degree-`≥ 9` vertex
has `≤ 151` members (`cloud_usable_card_le`). `acmax_general_residual_large` then
proves `algConn ≤ 2` for large `n` with no cell hypotheses, reducing the general
conjecture to a finite range. -/

/-! ## The apex firing configuration -/

/-- An **apex configuration**: the full hypothesis set of the apex-tie law
`algConn_le_two_of_apex_twin_pair`. -/
def ApexConfig (n : ℕ) (G : SimpleGraph (Fin n)) (u v g : Fin n) : Prop :=
  G.degree u = 3 ∧ G.degree v = 3 ∧ u ≠ v ∧ ¬G.Adj u v ∧
  G.Adj u g ∧ G.Adj v g ∧
  (∀ w, w ≠ g → ¬(G.Adj u w ∧ G.Adj v w)) ∧
  (∀ w, G.Adj u w → w ≠ g → G.degree w ≤ 4) ∧
  (∀ w, G.Adj v w → w ≠ g → G.degree w ≤ 4) ∧
  (∀ w w', G.Adj u w → w ≠ g → G.Adj v w' → w' ≠ g → ¬G.Adj w w')

/-! ## Cloud structure helpers -/

/-! ## The same-cloud mechanism -/

/-! ## Sharpening the usable-count cap chain

Sharpens the concrete m-bound by two improvements. `cloud_card_le_sharp` tightens
the cloud cap to `A ≤ 13`: charging both the shared-partner and partner-cross
channels to the same degree-4 partner set gives `offDiag + cross ≤ 6·c_x`
pointwise, so `A(A−1) ≤ 12A`. `usable_deg3_card_le_sharp` then gives `m ≤ 341` via
`usable_deg3_card_le_of_cloud`, and `acmax_general_residual_large_sharp` /
`acmax_conjecture_large_n_sharp` rethread the argument with `C_m' = 341`, reducing
the wall to `boundLin ((128·341 + 34508)/23) = 18764`. The standalone lever
`iso_twin_le_one_double_hub` (every degree-3 vertex has at most one degree-4
neighbour carrying a second degree-3 neighbour) is proved here but not consumed by
the sharpened bound. -/

/-! ## The sharpened cloud bound `A ≤ 13` -/

/-! ## Threading the sharpened mid-leaf bound into the wall chain

Threads the sharpened mid-leaves bound (`143 → 108`, from spending the base mid
leaf's own σ-budget `Σσ ≤ 2 ⟹ Σdeg ≤ 19`) through the usable-count chain: the
coverage improves to `13A + 137`, the usable cap to `C_m = 306`, and the wall to
`boundLin 3203 = 17692`. The three theorems mirror `usable_deg3_card_le_of_cloud`,
`usable_deg3_card_le_sharp` and `acmax_conjecture_large_n_sharp` with the
sharpened constants; the original chain is left untouched. -/

end ACMax
end

/- ---------------------------------------- Counting.ResidualInterface ------ -/
section
/-!
# The residual-core interface lemmas

Generic (`n`-free where possible) glue lemmas mediating between the residual-core
structure and the counting/covering layers. Here `M = G[D]` is the subgraph
induced on the degree-3 set `D`, and iso twins are the `M`-isolated degree-3
vertices.

## Main results

* `each_iso_three_hubs_general` — an `M`-isolated degree-3 vertex meets exactly
  the three hubs (`4 ≤ deg`).
* `hub_iso_sum_general` — the two-hub selection engine's core count
  `∑_{a∈Hub} |N(a) ∩ Iso| = 3·|Iso|`.
* `dist_le_three_of_mem_closeSet` — the metric half of the compact-ball interface:
  every membership certificate for the radius-3 combinatorial ball `closeSet G u₀`
  is a walk of length `≤ 3`, so `closeSet` sits inside the graph-distance ball.
* `s0_of_no_medge`, `deg3_eq_isoTwins_of_s0`, `twin_incidence_total` — the
  `e(M) = 0` normalization: with no degree-3–degree-3 edge, `D` *is* the iso-twin
  set and the twin incidence total is `3·|Iso|`.
-/

namespace ACMax

open scoped Classical

/-- **B3 — Each `M`-isolated twin meets exactly three hubs.**  An `M`-isolated degree-`3`
twin `t` (`(N t ∩ D).card = 0`) has all three of its neighbours in `Hub`, so
`(N t ∩ Hub).card = 3`. -/
theorem each_iso_three_hubs_general {V : Type*} [Fintype V] (G : SimpleGraph V)
    (D Hub : Finset V)
    (hmemD : ∀ v : V, v ∈ D ↔ G.degree v = 3)
    (hmemHub : ∀ v : V, v ∈ Hub ↔ 4 ≤ G.degree v)
    (h3 : ∀ v : V, 3 ≤ G.degree v)
    (t : V) (htD : t ∈ D) (htiso : (G.neighborFinset t ∩ D).card = 0) :
    (G.neighborFinset t ∩ Hub).card = 3 := by
  classical
  have hDH : ∀ v : V, v ∈ D ∨ v ∈ Hub := fun v => by
    rcases Nat.lt_or_ge (G.degree v) 4 with h | h
    · exact Or.inl ((hmemD v).mpr (by have := h3 v; omega))
    · exact Or.inr ((hmemHub v).mpr h)
  have hsub : G.neighborFinset t ⊆ Hub := by
    intro x hx
    rcases hDH x with hxD | hxH
    · exfalso
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem] at htiso
      exact htiso x (Finset.mem_inter.mpr ⟨hx, hxD⟩)
    · exact hxH
  rw [Finset.inter_eq_left.mpr hsub, G.card_neighborFinset_eq_degree, (hmemD t).mp htD]

end ACMax


/-! ## The two-hub selection engine

Abstract `Finset` counting over given sets `Hub, Iso`: `hub_iso_sum_general`
records `∑_{a∈Hub} |N(a) ∩ Iso| = 3·|Iso|`, since each iso twin meets exactly
three hubs. -/

namespace ACMax

open scoped Classical

variable {V : Type*} [Fintype V]

/-- **Total iso-degree is `3·|Iso|`.**  Each `M`-isolated twin meets exactly three hubs. -/
theorem hub_iso_sum_general (G : SimpleGraph V) (Hub Iso : Finset V)
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3) :
    ∑ a ∈ Hub, (G.neighborFinset a ∩ Iso).card = 3 * Iso.card := by
  rw [cross_count G Hub Iso]
  calc ∑ t ∈ Iso, (G.neighborFinset t ∩ Hub).card
      = ∑ _t ∈ Iso, 3 := Finset.sum_congr rfl (fun t ht => hiso3 t ht)
    _ = 3 * Iso.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

end ACMax


/-! ## The `closeSet → dist` bound

The metric half of the compact-ball interface: every membership certificate for
the radius-3 combinatorial ball `closeSet G u₀` is a walk of length `≤ 3`, so
`closeSet` sits inside the graph-distance ball of radius 3 around `u₀`. -/

namespace ACMax

open scoped Classical
open Finset

variable {n : ℕ}

end ACMax


/-! ## The `e(M) = 0` normalization

The normalization leaves for the `e(M) = 0` case: `s0_of_no_medge` pushes the
absence of a degree-3–degree-3 edge into the pointwise `hs0` form,
`deg3_eq_isoTwins_of_s0` shows the degree-3 set then coincides with the iso-twin
set, and `twin_incidence_total` records the resulting incidence total
`∑_{h∈Hub} |N(h) ∩ Iso| = 3·|Iso|`. -/

namespace ACMax

open scoped Classical

variable {V : Type*} [Fintype V]

/-- **B-0a (push).**  The negation of a degree-`3`–degree-`3` edge, in the pointwise
`hs0` form the downstream `e(M) = 0` fight consumes. -/
theorem s0_of_no_medge (G : SimpleGraph V)
    (h : ¬ ∃ v w : V, G.degree v = 3 ∧ G.degree w = 3 ∧ G.Adj v w) :
    ∀ v w : V, G.degree v = 3 → G.degree w = 3 → ¬G.Adj v w :=
  fun v w hv hw hadj => h ⟨v, w, hv, hw, hadj⟩

/-- **B-0a (identification).**  Under `hs0` (no degree-`3`–degree-`3` adjacency) every
degree-`3` vertex is `M`-isolated, so the degree-`3` set coincides with the `M`-isolated
twin set: `deg3Set G = isoTwins G`.  The forward inclusion is the `(a)`-step `hsub` of
`xmz_pigeonhole_input`; the reverse is the definitional `isoTwins ⊆ deg3Set`. -/
theorem deg3_eq_isoTwins_of_s0 (G : SimpleGraph V)
    (hs0 : ∀ v w : V, G.degree v = 3 → G.degree w = 3 → ¬G.Adj v w) :
    deg3Set G = isoTwins G := by
  apply Finset.Subset.antisymm
  · intro v hv
    have hvd3 : G.degree v = 3 := mem_deg3Set.mp hv
    exact mem_isoTwins.mpr ⟨hvd3, fun w hadj hw3 => hs0 v w hvd3 hw3 hadj⟩
  · intro v hv
    exact mem_deg3Set.mpr (mem_isoTwins.mp hv).1

/-- **B-0c.**  The twin-incidence total.  Under `hs0` (`e(M) = 0`) and minimum degree `3`
each `M`-isolated twin meets exactly three hubs (`each_iso_three_hubs_general`), so the
hub-to-twin incidence sum is `3·|Iso|` (`hub_iso_sum_general`):
`∑_{h∈Hub} |N(h) ∩ Iso| = 3·|Iso|`.  This is the exact shape the `B1` residue fights
(e.g. the single-heavy budget `xmz_single5_budget`) consume; the banked
`hub_iso_sum_general` already carries this statement for *given* `Hub, Iso`, and this leaf
supplies its per-twin hypothesis directly from the definition of `isoTwins` (whose members
are intrinsically `M`-isolated), so only minimum degree `3` is needed here — the `hs0`
`e(M) = 0` hypothesis of the surrounding node is what identifies `|Iso| = n₃` upstream
(`deg3_eq_isoTwins_of_s0`), not this incidence identity. -/
theorem twin_incidence_total (G : SimpleGraph V)
    (h3 : ∀ v : V, 3 ≤ G.degree v) :
    ∑ h ∈ hubSet G, (G.neighborFinset h ∩ isoTwins G).card = 3 * (isoTwins G).card := by
  apply hub_iso_sum_general G (hubSet G) (isoTwins G)
  intro t ht
  have htd3 : G.degree t = 3 := (mem_isoTwins.mp ht).1
  have htiso : ∀ w : V, G.Adj t w → G.degree w ≠ 3 := (mem_isoTwins.mp ht).2
  refine each_iso_three_hubs_general G (deg3Set G) (hubSet G)
    (fun v => mem_deg3Set) (fun v => mem_hubSet) h3 t (mem_deg3Set.mpr htd3) ?_
  rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro x hx
  rw [Finset.mem_inter] at hx
  exact htiso x ((G.mem_neighborFinset t x).mp hx.1) (mem_deg3Set.mp hx.2)

end ACMax
end

/- ---------------------------------------- Spectral.RayleighLower ---------- -/
section
/-!
# Lower companion of the Courant–Fischer bridge

`le_algConn_of_forall`: if the Laplacian quadratic form dominates `c · ‖x‖²` for
every `x` orthogonal to the all-ones vector (`∑ i, x i = 0`), then `c ≤ algConn G`.
This is the reverse direction used to certify the *lower* bound `algConn ≥ 2`.
-/

namespace ACMax

open scoped Classical
open Matrix

theorem le_algConn_of_forall {V : Type*} [Fintype V] [Nonempty V] [Nontrivial V]
    (G : SimpleGraph V) (c : ℝ)
    (h : ∀ x : V → ℝ, ∑ i, x i = 0 →
      c * (∑ i, (x i) ^ 2) ≤ dotProduct x ((G.lapMatrix ℝ).mulVec x)) :
    c ≤ algConn G := by
  classical
  set A : Matrix V V ℝ := G.lapMatrix ℝ with hAdef
  have hPSD : A.PosSemidef := SimpleGraph.posSemidef_lapMatrix ℝ G
  have hHerm : A.IsHermitian := hPSD.isHermitian
  set U := hHerm.eigenvectorUnitary with hUdef
  set lam : V → ℝ := hHerm.eigenvalues with hlamdef
  -- the unitary `star U * U = 1` gives orthonormality of the columns of `U`
  have hU2 : star (U : Matrix V V ℝ) * (U : Matrix V V ℝ) = 1 :=
    Matrix.UnitaryGroup.star_mul_self U
  have horth : ∀ i j : V,
      (∑ k, (U : Matrix V V ℝ) k i * (U : Matrix V V ℝ) k j) = if i = j then 1 else 0 := by
    intro i j
    have hh := congrFun (congrFun hU2 i) j
    rw [Matrix.mul_apply, Matrix.one_apply] at hh
    rw [← hh]
    apply Finset.sum_congr rfl
    intro k _
    rw [Matrix.star_apply, star_trivial]
  -- index data: `j0` realises the second-smallest eigenvalue, `j1` the smallest
  have hcard2 : Fintype.card V - 2 < Fintype.card V := Nat.sub_lt Fintype.card_pos (by norm_num)
  have hcard1 : Fintype.card V - 1 < Fintype.card V := Nat.sub_lt Fintype.card_pos (by norm_num)
  have hN : 1 < Fintype.card V := Fintype.one_lt_card
  let e := Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card V))
  have hlam : ∀ i, lam i = hHerm.eigenvalues₀ (e.symm i) := by intro i; rw [hlamdef]; rfl
  have hc : algConn G = hHerm.eigenvalues₀ ⟨Fintype.card V - 2, hcard2⟩ := rfl
  set j0 : V := e ⟨Fintype.card V - 2, hcard2⟩ with hj0
  set j1 : V := e ⟨Fintype.card V - 1, hcard1⟩ with hj1
  have hej0 : e.symm j0 = ⟨Fintype.card V - 2, hcard2⟩ := by rw [hj0]; exact e.symm_apply_apply _
  have hej1 : e.symm j1 = ⟨Fintype.card V - 1, hcard1⟩ := by rw [hj1]; exact e.symm_apply_apply _
  have hj0ne1 : j0 ≠ j1 := by
    intro heq
    have h2 : (⟨Fintype.card V - 2, hcard2⟩ : Fin (Fintype.card V))
        = ⟨Fintype.card V - 1, hcard1⟩ := by rw [← hej0, ← hej1, heq]
    have h3 : Fintype.card V - 2 = Fintype.card V - 1 := Fin.mk_eq_mk.mp h2
    omega
  have hlamj0 : lam j0 = algConn G := by rw [hlam j0, hej0]; exact hc.symm
  have hlamj1 : lam j1 ≤ algConn G := by
    rw [hlam j1, hej1, hc]
    exact hHerm.eigenvalues₀_antitone (Fin.mk_le_mk.mpr (by omega))
  -- the eigenvector columns of `U` and their spectral relation
  set v0 : V → ℝ := fun k => (U : Matrix V V ℝ) k j0 with hv0def
  set v1 : V → ℝ := fun k => (U : Matrix V V ℝ) k j1 with hv1def
  have hAv0 : A *ᵥ v0 = lam j0 • v0 := by
    have hcol : v0 = ⇑(hHerm.eigenvectorBasis j0) := by
      funext k; exact Matrix.IsHermitian.eigenvectorUnitary_apply hHerm k j0
    rw [hcol, hHerm.mulVec_eigenvectorBasis]
  have hAv1 : A *ᵥ v1 = lam j1 • v1 := by
    have hcol : v1 = ⇑(hHerm.eigenvectorBasis j1) := by
      funext k; exact Matrix.IsHermitian.eigenvectorUnitary_apply hHerm k j1
    rw [hcol, hHerm.mulVec_eigenvectorBasis]
  have hnorm0 : v0 ⬝ᵥ v0 = 1 := by
    have hr := horth j0 j0
    rw [if_pos rfl] at hr
    exact hr
  have hnorm1 : v1 ⬝ᵥ v1 = 1 := by
    have hr := horth j1 j1
    rw [if_pos rfl] at hr
    exact hr
  have hcross : v0 ⬝ᵥ v1 = 0 := by
    have hr := horth j0 j1
    rw [if_neg hj0ne1] at hr
    exact hr
  have hcross' : v1 ⬝ᵥ v0 = 0 := by
    have hr := horth j1 j0
    rw [if_neg (fun hh => hj0ne1 hh.symm)] at hr
    exact hr
  -- split on whether the second-smallest eigenvector is already orthogonal to `1`
  rcases eq_or_ne (∑ k, v0 k) 0 with hS0 | hS0
  · -- `v0 ⊥ 1`: it directly certifies the bound at the second-smallest eigenvalue
    have hb := h v0 hS0
    have hsq : (∑ k, (v0 k) ^ 2) = v0 ⬝ᵥ v0 := by
      have hr : v0 ⬝ᵥ v0 = ∑ k, v0 k * v0 k := rfl
      rw [hr]; apply Finset.sum_congr rfl; intro k _; rw [pow_two]
    have hAq : v0 ⬝ᵥ (A *ᵥ v0) = lam j0 := by
      rw [hAv0, dotProduct_smul, smul_eq_mul, hnorm0, mul_one]
    rw [hsq, hnorm0, mul_one, hAq, hlamj0] at hb
    exact hb
  · -- otherwise combine `v0`, `v1` into a kernel-of-`∑` vector with Rayleigh quotient
    -- bounded by `algConn`
    set w : V → ℝ := (∑ k, v1 k) • v0 - (∑ k, v0 k) • v1 with hwdef
    have hsumw : ∑ k, w k = 0 := by
      have h1 : ∑ k, w k
          = (∑ k, v1 k) * (∑ k, v0 k) - (∑ k, v0 k) * (∑ k, v1 k) := by
        simp only [hwdef, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_sub_distrib,
          ← Finset.mul_sum]
      rw [h1]; ring
    have hAw : A *ᵥ w
        = (∑ k, v1 k) • (lam j0 • v0) - (∑ k, v0 k) • (lam j1 • v1) := by
      rw [hwdef, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul, hAv0, hAv1]
    have hnormw : w ⬝ᵥ w = (∑ k, v0 k) ^ 2 + (∑ k, v1 k) ^ 2 := by
      conv_lhs => rw [hwdef]
      simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct,
        dotProduct_smul, smul_eq_mul, hnorm0, hnorm1, hcross, hcross']
      ring
    have hquadw : w ⬝ᵥ (A *ᵥ w)
        = (∑ k, v1 k) ^ 2 * lam j0 + (∑ k, v0 k) ^ 2 * lam j1 := by
      rw [hAw]
      conv_lhs => rw [hwdef]
      simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct,
        dotProduct_smul, smul_eq_mul, hnorm0, hnorm1, hcross, hcross']
      ring
    have hbnd := h w hsumw
    have hsqw : (∑ k, (w k) ^ 2) = w ⬝ᵥ w := by
      have hr : w ⬝ᵥ w = ∑ k, w k * w k := rfl
      rw [hr]; apply Finset.sum_congr rfl; intro k _; rw [pow_two]
    rw [hsqw, hnormw, hquadw] at hbnd
    have hpos : 0 < (∑ k, v0 k) ^ 2 + (∑ k, v1 k) ^ 2 := by
      have h2 : 0 < (∑ k, v0 k) ^ 2 := by rw [pow_two]; exact mul_self_pos.mpr hS0
      nlinarith [sq_nonneg (∑ k, v1 k)]
    have hub : (∑ k, v1 k) ^ 2 * lam j0 + (∑ k, v0 k) ^ 2 * lam j1
        ≤ algConn G * ((∑ k, v0 k) ^ 2 + (∑ k, v1 k) ^ 2) := by
      rw [hlamj0]
      nlinarith [mul_le_mul_of_nonneg_left hlamj1 (sq_nonneg (∑ k, v0 k)),
        sq_nonneg (∑ k, v1 k), sq_nonneg (∑ k, v0 k)]
    have hfin : c * ((∑ k, v0 k) ^ 2 + (∑ k, v1 k) ^ 2)
        ≤ algConn G * ((∑ k, v0 k) ^ 2 + (∑ k, v1 k) ^ 2) := le_trans hbnd hub
    exact le_of_mul_le_mul_right hfin hpos

end ACMax
end

/- ---------------------------------------- Spectral.AlgConnK2 -------------- -/
section
/-!
# Algebraic connectivity of `K_{2,n-2}` equals `2`

`algConn_completeBipartite_two`: the equality clause of the ACMAX conjecture.
The Laplacian spectrum of `K_{2,n-2}` is `0, 2^(n-3), (n-2), n`, so its
second-smallest eigenvalue is `2`.
-/

namespace ACMax

open scoped Classical

theorem algConn_completeBipartite_two (n : ℕ) (hn : 4 ≤ n) :
    algConn (completeBipartiteGraph (Fin 2) (Fin (n - 2))) = 2 := by
  classical
  set m := n - 2 with hm
  let : DecidableEq (Fin 2 ⊕ Fin m) := fun a b => Classical.propDecidable (a = b)
  have : Nontrivial (Fin 2 ⊕ Fin m) := ⟨Sum.inl 0, Sum.inl 1, by simp⟩
  set G : SimpleGraph (Fin 2 ⊕ Fin m) := completeBipartiteGraph (Fin 2) (Fin m) with hG
  -- adjacency description
  have hadj : ∀ i j : Fin 2 ⊕ Fin m, G.Adj i j ↔
      (i.isLeft ∧ j.isRight) ∨ (i.isRight ∧ j.isLeft) := by
    intro i j; rw [hG]; rfl
  -- splitting lemmas over the sum type
  have hsplit : ∀ y : Fin 2 ⊕ Fin m → ℝ,
      ∑ w, y w = y (Sum.inl 0) + y (Sum.inl 1) + ∑ k : Fin m, y (Sum.inr k) := by
    intro y; rw [Fintype.sum_sum_type, Fin.sum_univ_two]
  have hsq : ∀ y : Fin 2 ⊕ Fin m → ℝ,
      ∑ w, (y w) ^ 2
        = (y (Sum.inl 0)) ^ 2 + (y (Sum.inl 1)) ^ 2 + ∑ k : Fin m, (y (Sum.inr k)) ^ 2 := by
    intro y; rw [Fintype.sum_sum_type, Fin.sum_univ_two]
  -- the Laplacian quadratic form as a clean leaf sum
  have hQ : ∀ y : Fin 2 ⊕ Fin m → ℝ,
      dotProduct y ((G.lapMatrix ℝ).mulVec y)
        = ∑ k : Fin m,
            ((y (Sum.inl 0) - y (Sum.inr k)) ^ 2 + (y (Sum.inl 1) - y (Sum.inr k)) ^ 2) := by
    intro y
    rw [← Matrix.toLinearMap₂'_apply' (G.lapMatrix ℝ) y y, SimpleGraph.lapMatrix_toLinearMap₂']
    simp only [hadj, Fintype.sum_sum_type, Fin.sum_univ_two, Sum.isLeft_inl, Sum.isRight_inl,
      Sum.isLeft_inr, Sum.isRight_inr, Bool.false_eq_true, and_true, and_false, or_false,
      false_or, if_true, if_false, Finset.sum_const_zero, add_zero, zero_add]
    rw [div_eq_iff (by norm_num : (2 : ℝ) ≠ 0)]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    ring
  -- ===== Upper bound: algConn ≤ 2 =====
  have hupper : algConn G ≤ 2 := by
    have hm0 : 0 < m := by omega
    have hm1 : 1 < m := by omega
    set i0 : Fin m := ⟨0, hm0⟩ with hi0
    set i1 : Fin m := ⟨1, hm1⟩ with hi1
    have hne : i0 ≠ i1 := by
      rw [hi0, hi1]; intro h; exact absurd (Fin.mk.inj_iff.mp h) (by norm_num)
    set g : Fin m → ℝ := fun k => (if k = i0 then (1 : ℝ) else 0) - (if k = i1 then 1 else 0)
      with hgdef
    set x : Fin 2 ⊕ Fin m → ℝ := Sum.elim (fun _ => (0 : ℝ)) g with hxdef
    -- ∑ g = 0
    have hg_sum : ∑ k : Fin m, g k = 0 := by
      simp only [hgdef, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      ring
    have hg_i0 : g i0 = 1 := by
      simp [hgdef, hne]
    have hS2pos : 0 < ∑ k : Fin m, (g k) ^ 2 := by
      apply Finset.sum_pos' (fun k _ => sq_nonneg _)
      exact ⟨i0, Finset.mem_univ _, by rw [hg_i0]; norm_num⟩
    -- ∑ x = 0
    have hx0 : ∑ w, x w = 0 := by
      rw [hsplit x, hxdef]
      simp only [Sum.elim_inl, Sum.elim_inr]
      rw [hg_sum]; ring
    -- ∑ x² = S2
    have hsumsq : ∑ w, (x w) ^ 2 = ∑ k : Fin m, (g k) ^ 2 := by
      rw [hsq x, hxdef]
      simp only [Sum.elim_inl, Sum.elim_inr]
      ring
    -- Q x = 2 * S2
    have hQval : (∑ k : Fin m,
        ((x (Sum.inl 0) - x (Sum.inr k)) ^ 2 + (x (Sum.inl 1) - x (Sum.inr k)) ^ 2))
        = 2 * ∑ k : Fin m, (g k) ^ 2 := by
      rw [hxdef]
      simp only [Sum.elim_inl, Sum.elim_inr]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _; ring
    have key := algConn_mul_sq_le G x hx0
    have hbound : algConn G * (∑ i, x i ^ 2) ≤ 2 * ∑ k : Fin m, (g k) ^ 2 :=
      calc algConn G * (∑ i, x i ^ 2)
          ≤ dotProduct x ((G.lapMatrix ℝ).mulVec x) := key
        _ = 2 * ∑ k : Fin m, (g k) ^ 2 := by rw [hQ x, hQval]
    rw [hsumsq] at hbound
    exact le_of_mul_le_mul_right hbound hS2pos
  -- ===== Lower bound: 2 ≤ algConn =====
  have hlower : 2 ≤ algConn G := by
    apply le_algConn_of_forall G 2
    intro x hx0
    have hmR : (2 : ℝ) ≤ (m : ℝ) := by
      have h2m : 2 ≤ m := by omega
      exact_mod_cast h2m
    -- constraint from orthogonality to the all-ones vector
    have hsum : x (Sum.inl 0) + x (Sum.inl 1) + ∑ k : Fin m, x (Sum.inr k) = 0 := by
      rw [← hsplit x]; exact hx0
    -- expansion of a shifted sum of squares
    have e1 : ∀ t : ℝ, ∑ k : Fin m, (t - x (Sum.inr k)) ^ 2
        = (m : ℝ) * t ^ 2 - 2 * t * (∑ k : Fin m, x (Sum.inr k))
          + ∑ k : Fin m, (x (Sum.inr k)) ^ 2 := by
      intro t
      have hterm : ∀ k : Fin m,
          (t - x (Sum.inr k)) ^ 2 = t ^ 2 - 2 * t * (x (Sum.inr k)) + (x (Sum.inr k)) ^ 2 :=
        fun k => by ring
      simp only [hterm]
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
    have hQval : (∑ k : Fin m,
        ((x (Sum.inl 0) - x (Sum.inr k)) ^ 2 + (x (Sum.inl 1) - x (Sum.inr k)) ^ 2))
        = (m : ℝ) * ((x (Sum.inl 0)) ^ 2 + (x (Sum.inl 1)) ^ 2)
          - 2 * ((x (Sum.inl 0)) + (x (Sum.inl 1))) * (∑ k : Fin m, x (Sum.inr k))
          + 2 * (∑ k : Fin m, (x (Sum.inr k)) ^ 2) := by
      rw [Finset.sum_add_distrib, e1 (x (Sum.inl 0)), e1 (x (Sum.inl 1))]; ring
    have hSc : (∑ k : Fin m, x (Sum.inr k)) = -((x (Sum.inl 0)) + (x (Sum.inl 1))) := by
      linarith
    rw [hsq x]
    calc 2 * ((x (Sum.inl 0)) ^ 2 + (x (Sum.inl 1)) ^ 2 + ∑ k : Fin m, (x (Sum.inr k)) ^ 2)
        ≤ ∑ k : Fin m,
            ((x (Sum.inl 0) - x (Sum.inr k)) ^ 2 + (x (Sum.inl 1) - x (Sum.inr k)) ^ 2) := by
          rw [hQval, hSc]
          nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (m : ℝ) - 2)
            (add_nonneg (sq_nonneg (x (Sum.inl 0))) (sq_nonneg (x (Sum.inl 1)))),
            sq_nonneg ((x (Sum.inl 0)) + (x (Sum.inl 1)))]
      _ = dotProduct x ((G.lapMatrix ℝ).mulVec x) := (hQ x).symm
  exact le_antisymm hupper hlower

end ACMax
end


/-! ########################################################################################
   PART V --- The certificate: moats

   The local half of the argument. A short cycle among the degree-<=4 vertices, together with
   its neighbourhood moat, is a two-cluster cut. `MoatSharp` credits back the bulk's share of
   the excess ledger, lengthening the reach from `9k <= n+8` to `12k + X <= 2n`.
   ######################################################################################## -/

/- ---------------------------------------- Counting.Moats ------------------ -/
section
/-!
# Two-cluster moat kills and the thin-twin averaging row

The *moat* family of two-cluster cut certificates: a low-degree tie-block `S₁`
whose closed neighbourhood forms a zeroed *moat* `F`, so that
`algConn_le_two_of_two_clusters` fires `algConn G ≤ 2` with no diameter, census
or cell hypotheses. Each vertex of `S₁` keeps an external degree budget of `2`,
so the boundary hits the two-cluster tie `∂₁ ≤ 2|S₁|` and the excess ledger
`Σ_v (deg v − 3) = n − 8` (`total_excess_eq`) caps the bulk boundary.

## Main results

* `medge_moat_fires` — an `M`-edge (a degree-3–degree-3 edge) fires at `n ≥ 12`.
* `star_moat_fires` (and `z1_star_moat_fires`) — a hub `h` hoarding `deg h − 2`
  degree-3 twins fires at `9·deg h ≤ n + 15`.
* `master_cycle_fires` — a cycle with degree-sum tie `Σ deg ≤ 4k` fires at
  `n ≥ 3·Σ(deg − 1) − 8`.
* `deco_edge_moat_fires` (and `z4c_fires`) — an adjacent hub pair hoarding
  `deg u − 3`, `deg v − 3` twins fires at `9·(deg u + deg v) ≤ n + 42`.
* The **thin-twin averaging row**: the double-counting swap
  `∑_{t∈T} E₁(t) = ∑_v (deg v − 3)·|N(v) ∩ T|` (`twin_E1_sum_swap`) with the
  excess ledger and a multiplicity cap `K` yields
  `∃ t ∈ T, |T|·E₁(t) ≤ K·(n − 8)` (`thin_twin_exists_of_multcap`), with the
  unconditional instances `thin_twin_exists_deg5` and
  `thin_twin_exists_iso_of_multcap`.
-/

/-! ## The thin-twin averaging row

The averaging engine producing a *thin* twin (bounded `1`-ball excess
`E₁(t) = sphereExc G t 1`). The double-counting swap `twin_E1_sum_swap` holds for
any root set `T`; combined with `total_excess_eq` and a multiplicity cap
`|N(v) ∩ T| ≤ K` it gives `∑_{t∈T} E₁(t) ≤ K·(n − 8)` and the averaging existence
`thin_twin_exists_of_multcap`. The cap `K` stays explicit (a heavy vertex's
multiplicity is unbounded); the clean instances are `thin_twin_exists_deg5`
(`K = 5` when `Δ ≤ 5`) and `thin_twin_exists_iso_of_multcap` (on `isoTwins G`). -/

namespace ACMax

open Finset
open scoped Classical

/-- **The excess ledger.**  On the `m = 2(n−2)`, `δ ≥ 3` census (`n ≥ 8`) the total degree
excess is `Σ_v (deg v − 3) = n − 8`: the handshake `Σ deg = 2·2(n−2) = 4n − 8` minus the
base `3n`. -/
theorem total_excess_eq {n : ℕ} (hn : 8 ≤ n) (G : SimpleGraph (Fin n))
    (hm : G.edgeFinset.card = 2 * (n - 2)) (h3 : ∀ v : Fin n, 3 ≤ G.degree v) :
    ∑ v : Fin n, (G.degree v - 3) = n - 8 := by
  have hhandshake : ∑ v : Fin n, G.degree v = 2 * (2 * (n - 2)) := by
    rw [G.sum_degrees_eq_twice_card_edges, hm]
  have hcancel : ∑ v : Fin n, G.degree v = (∑ v : Fin n, (G.degree v - 3)) + 3 * n := by
    have h3n : ∑ _v : Fin n, (3 : ℕ) = 3 * n := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_comm]
    rw [← h3n, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun v _ => (Nat.sub_add_cancel (h3 v)).symm)
  omega

/-! ## The M-moat kill

Instantiates `algConn_le_two_of_two_clusters` with the tie-block `S₁ = {u, p}`
(an `M`-edge) against the bulk, moat `F = (N(u) ∪ N(p)) ∖ {u,p}`: `∂₁ = 4`,
`|F| ≤ 4`, so `medge_moat_fires` gives `algConn G ≤ 2` for every `n ≥ 12`. -/

/-- **QM1 — the M-moat certificate.**  A graph on `Fin n` (`n ≥ 12`) with `2(n−2)` edges,
minimum degree `≥ 3`, and one degree-`3`–degree-`3` edge `u–p` has `algConn G ≤ 2`.

Instantiate the two-cluster law with the tie-block `S₁ = {u, p}` against the bulk
`S₂ = ({u, p} ∪ F)ᶜ`, where `F = (N(u) ∪ N(p)) ∖ {u, p}` is the moat.  Boundary counts:
`∂₁ ≤ 4`, and (using that each moat vertex is adjacent to `u` or `p`, and the excess ledger
`Σ_v (deg v − 3) = n − 8`) `∂₂ ≤ 2·|S₂|`; the Fiedler cut condition then holds since `|F| ≤ 4`
and `n ≥ 12`. -/
theorem medge_moat_fires {n : ℕ} [Nonempty (Fin n)] (hn : 12 ≤ n)
    (G : SimpleGraph (Fin n)) (hm : G.edgeFinset.card = 2 * (n - 2))
    (h3 : ∀ v : Fin n, 3 ≤ G.degree v) (u p : Fin n) (hM : G.Adj u p)
    (hu : G.degree u = 3) (hp : G.degree p = 3) :
    algConn G ≤ 2 := by
  classical
  let : DecidableEq (Fin n) := Classical.decEq (Fin n)
  have hup : u ≠ p := hM.ne
  set S₁ : Finset (Fin n) := {u, p} with hS1def
  set F : Finset (Fin n) := (G.neighborFinset u ∪ G.neighborFinset p) \ S₁ with hFdef
  set S₂ : Finset (Fin n) := (S₁ ∪ F)ᶜ with hS2def
  -- basic cardinalities and memberships
  have hS1card : S₁.card = 2 := by rw [hS1def]; exact Finset.card_pair hup
  have hFsub : F ⊆ G.neighborFinset u ∪ G.neighborFinset p := by
    rw [hFdef]; exact Finset.sdiff_subset
  have huF : u ∉ F := by
    rw [hFdef, Finset.mem_sdiff]
    rintro ⟨_, hu2⟩
    exact hu2 (by rw [hS1def]; exact Finset.mem_insert_self u {p})
  have hpF : p ∉ F := by
    rw [hFdef, Finset.mem_sdiff]
    rintro ⟨_, hp2⟩
    exact hp2 (by rw [hS1def]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self p))
  have hFcard : F.card ≤ 4 := by
    have hsubpair : S₁ ⊆ G.neighborFinset u ∪ G.neighborFinset p := by
      rw [hS1def]
      intro x hx
      rw [Finset.mem_insert, Finset.mem_singleton] at hx
      rw [Finset.mem_union, G.mem_neighborFinset, G.mem_neighborFinset]
      rcases hx with rfl | rfl
      · exact Or.inr hM.symm
      · exact Or.inl hM
    have hunion : (G.neighborFinset u ∪ G.neighborFinset p).card ≤ 6 := by
      calc (G.neighborFinset u ∪ G.neighborFinset p).card
          ≤ (G.neighborFinset u).card + (G.neighborFinset p).card := Finset.card_union_le _ _
        _ = 6 := by
            rw [G.card_neighborFinset_eq_degree, G.card_neighborFinset_eq_degree, hu, hp]
    rw [hFdef, Finset.card_sdiff_of_subset hsubpair, hS1card]
    omega
  have hdisjS1F : Disjoint S₁ F := by
    rw [Finset.disjoint_left]
    intro a ha haF
    rw [hFdef, Finset.mem_sdiff] at haF
    exact haF.2 ha
  have hS2card : S₂.card = n - (2 + F.card) := by
    rw [hS2def, Finset.card_compl, Fintype.card_fin,
      Finset.card_union_of_disjoint hdisjS1F, hS1card]
  -- the counting helper: an ordered adjacency block splits into neighbourhood slices
  have hcnt : ∀ (A C : Finset (Fin n)),
      ((A ×ˢ C).filter (fun q => G.Adj q.1 q.2)).card
        = ∑ a ∈ A, (G.neighborFinset a ∩ C).card := by
    intro A C
    rw [Finset.card_filter, Finset.sum_product]
    refine Finset.sum_congr rfl fun a _ => ?_
    have hset : G.neighborFinset a ∩ C = C.filter (fun v => G.Adj a v) := by
      ext v
      simp only [Finset.mem_inter, Finset.mem_filter, SimpleGraph.mem_neighborFinset]
      exact and_comm
    rw [hset, Finset.card_filter]
  -- the transpose helper (adjacency is symmetric)
  have htrans : ∀ (A C : Finset (Fin n)),
      ((A ×ˢ C).filter (fun q => G.Adj q.1 q.2)).card
        = ((C ×ˢ A).filter (fun q => G.Adj q.1 q.2)).card := by
    intro A C
    refine Finset.card_bij (fun q _ => (q.2, q.1)) ?_ ?_ ?_
    · intro q hq
      rw [Finset.mem_filter, Finset.mem_product] at hq ⊢
      exact ⟨⟨hq.1.2, hq.1.1⟩, G.adj_symm hq.2⟩
    · intro q _ r _ hqr
      exact Prod.ext (congrArg Prod.snd hqr) (congrArg Prod.fst hqr)
    · intro q hq
      refine ⟨(q.2, q.1), ?_, rfl⟩
      rw [Finset.mem_filter, Finset.mem_product] at hq ⊢
      exact ⟨⟨hq.1.2, hq.1.1⟩, G.adj_symm hq.2⟩
  -- ∂₁ ≤ 4
  have he1 : ((S₁ ×ˢ F).filter (fun q => G.Adj q.1 q.2)).card ≤ 4 := by
    rw [hcnt S₁ F, hS1def, Finset.sum_pair hup]
    have hu2 : (G.neighborFinset u ∩ F).card ≤ 2 := by
      have hsub : G.neighborFinset u ∩ F ⊆ (G.neighborFinset u).erase p := by
        intro x hx
        rw [Finset.mem_inter] at hx
        rw [Finset.mem_erase]
        exact ⟨fun hxp => hpF (hxp ▸ hx.2), hx.1⟩
      calc (G.neighborFinset u ∩ F).card
          ≤ ((G.neighborFinset u).erase p).card := Finset.card_le_card hsub
        _ = G.degree u - 1 := by
            rw [Finset.card_erase_of_mem ((G.mem_neighborFinset u p).mpr hM),
              G.card_neighborFinset_eq_degree]
        _ = 2 := by rw [hu]
    have hp2 : (G.neighborFinset p ∩ F).card ≤ 2 := by
      have hsub : G.neighborFinset p ∩ F ⊆ (G.neighborFinset p).erase u := by
        intro x hx
        rw [Finset.mem_inter] at hx
        rw [Finset.mem_erase]
        exact ⟨fun hxu => huF (hxu ▸ hx.2), hx.1⟩
      calc (G.neighborFinset p ∩ F).card
          ≤ ((G.neighborFinset p).erase u).card := Finset.card_le_card hsub
        _ = G.degree p - 1 := by
            rw [Finset.card_erase_of_mem ((G.mem_neighborFinset p u).mpr hM.symm),
              G.card_neighborFinset_eq_degree]
        _ = 2 := by rw [hp]
    omega
  -- ∂₂ ≤ 2·|S₂|
  have he2 : ((S₂ ×ˢ F).filter (fun q => G.Adj q.1 q.2)).card ≤ 2 * S₂.card := by
    rw [htrans S₂ F, hcnt F S₂]
    have hbound : ∀ w ∈ F, (G.neighborFinset w ∩ S₂).card ≤ G.degree w - 1 := by
      intro w hw
      obtain ⟨a, haS1, haw⟩ : ∃ a, a ∈ S₁ ∧ G.Adj a w := by
        have hmem : w ∈ G.neighborFinset u ∪ G.neighborFinset p := hFsub hw
        rw [Finset.mem_union, G.mem_neighborFinset, G.mem_neighborFinset] at hmem
        rcases hmem with h | h
        · exact ⟨u, by rw [hS1def]; exact Finset.mem_insert_self u {p}, h⟩
        · exact ⟨p, by rw [hS1def]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self p), h⟩
      have haNw : a ∈ G.neighborFinset w := (G.mem_neighborFinset w a).mpr haw.symm
      have haS2 : a ∉ S₂ := by
        rw [hS2def, Finset.mem_compl, not_not]
        exact Finset.mem_union_left F haS1
      have hsub : G.neighborFinset w ∩ S₂ ⊆ (G.neighborFinset w).erase a := by
        intro x hx
        rw [Finset.mem_inter] at hx
        rw [Finset.mem_erase]
        refine ⟨?_, hx.1⟩
        rintro rfl
        exact haS2 hx.2
      calc (G.neighborFinset w ∩ S₂).card
          ≤ ((G.neighborFinset w).erase a).card := Finset.card_le_card hsub
        _ = G.degree w - 1 := by
            rw [Finset.card_erase_of_mem haNw, G.card_neighborFinset_eq_degree]
    have hexc : ∑ w ∈ F, (G.degree w - 3) ≤ n - 8 := by
      calc ∑ w ∈ F, (G.degree w - 3)
          ≤ ∑ w : Fin n, (G.degree w - 3) := Finset.sum_le_sum_of_subset (Finset.subset_univ F)
        _ = n - 8 := total_excess_eq (by omega) G hm h3
    have hpt : ∀ w ∈ F, G.degree w - 1 = (G.degree w - 3) + 2 := by
      intro w _
      have := h3 w
      omega
    calc ∑ w ∈ F, (G.neighborFinset w ∩ S₂).card
        ≤ ∑ w ∈ F, (G.degree w - 1) := Finset.sum_le_sum hbound
      _ = ∑ w ∈ F, (G.degree w - 3) + F.card * 2 := by
          rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, Finset.sum_const,
            smul_eq_mul]
      _ ≤ 2 * S₂.card := by omega
  -- assemble the two-cluster law
  have hS1ne : S₁.Nonempty := by rw [hS1def]; exact Finset.insert_nonempty u {p}
  have hS2ne : S₂.Nonempty := by
    rw [← Finset.card_pos, hS2card]; omega
  have hdisj : Disjoint S₁ S₂ := by
    rw [Finset.disjoint_left]
    intro a ha1 ha2
    rw [hS2def, Finset.mem_compl] at ha2
    exact ha2 (Finset.mem_union_left F ha1)
  have hnc : ∀ a ∈ S₁, ∀ v ∈ S₂, ¬G.Adj a v := by
    intro a ha v hv hadj
    rw [hS2def, Finset.mem_compl] at hv
    have hvnotS1 : v ∉ S₁ := fun h => hv (Finset.mem_union_left F h)
    have hvnotF : v ∉ F := fun h => hv (Finset.mem_union_right S₁ h)
    rw [hS1def, Finset.mem_insert, Finset.mem_singleton] at ha
    have hvmem : v ∈ G.neighborFinset u ∪ G.neighborFinset p := by
      rw [Finset.mem_union, G.mem_neighborFinset, G.mem_neighborFinset]
      rcases ha with rfl | rfl
      · exact Or.inl hadj
      · exact Or.inr hadj
    apply hvnotF
    rw [hFdef, Finset.mem_sdiff]
    exact ⟨hvmem, hvnotS1⟩
  have hFeq : (S₁ ∪ S₂)ᶜ = F := by
    ext v
    constructor
    · intro hv
      rw [Finset.mem_compl, Finset.mem_union, not_or] at hv
      obtain ⟨hvS1, hvS2⟩ := hv
      rw [hS2def, Finset.mem_compl, not_not, Finset.mem_union] at hvS2
      rcases hvS2 with h | h
      · exact absurd h hvS1
      · exact h
    · intro hv
      rw [Finset.mem_compl, Finset.mem_union, not_or]
      exact ⟨Finset.disjoint_right.mp hdisjS1F hv,
        by rw [hS2def, Finset.mem_compl, not_not]; exact Finset.mem_union_right S₁ hv⟩
  refine algConn_le_two_of_two_clusters G S₁ S₂ hS1ne hS2ne hdisj hnc ?_
  rw [hFeq, hS1card]
  have hbound1 := Nat.mul_le_mul he1 (le_refl (S₂.card ^ 2))
  have hbound2 := Nat.mul_le_mul he2 (le_refl ((2 : ℕ) ^ 2))
  refine le_trans (add_le_add hbound1 hbound2) (le_of_eq ?_)
  ring

/-! ## The star-moat kill

The `e(M) = 0` generalization: the star tie-block `S₁ = insert h K` (a hub `h`
with `|K| = deg h − 2` degree-3 twins), each `S₁`-vertex keeping external budget
`2`, so crediting the hub's excess back gives `star_moat_fires` at
`9·deg h ≤ n + 15` (`z1_star_moat_fires`: a degree-4 hub with two twins at
`n ≥ 21`). The twins need not be pairwise non-adjacent — an internal edge only
shrinks the boundary slices. -/

/-- **MZ1 — the star-moat certificate.**  A graph on `Fin n` with `2(n−2)` edges, minimum
degree `≥ 3`, a hub `h` and a twin set `K ⊆ N(h)` of degree-`3` vertices with `|K| = deg h − 2`
has `algConn G ≤ 2` whenever `9·deg h ≤ n + 15`.

Instantiate the two-cluster law with the tie-block `S₁ = insert h K` against the bulk
`S₂ = (S₁ ∪ F)ᶜ`, `F = (⋃_{x ∈ S₁} N(x)) ∖ S₁` the moat: each slice `N(x) ∖ S₁` has `≤ 2`
elements (hub loses `K`, twins lose the hub), so `∂₁ ≤ 2|S₁|` and `|F| ≤ 2|S₁|`, and the
hub-credited excess ledger gives `∂₂ ≤ 2|S₂|`; the Fiedler cut condition closes by `ring`. -/
theorem star_moat_fires {n : ℕ} [Nonempty (Fin n)]
    (G : SimpleGraph (Fin n)) (hm : G.edgeFinset.card = 2 * (n - 2))
    (h3 : ∀ v : Fin n, 3 ≤ G.degree v) (h : Fin n) (K : Finset (Fin n))
    (hKsub : K ⊆ G.neighborFinset h) (hKdeg : ∀ t ∈ K, G.degree t = 3)
    (hKcard : K.card = G.degree h - 2) (hfire : 9 * G.degree h ≤ n + 15) :
    algConn G ≤ 2 := by
  classical
  let : DecidableEq (Fin n) := Classical.decEq (Fin n)
  have hdeg3 : 3 ≤ G.degree h := h3 h
  have hn8 : 8 ≤ n := by omega
  have hhK : h ∉ K := by
    intro hh
    have hmem := hKsub hh
    rw [G.mem_neighborFinset] at hmem
    exact (G.ne_of_adj hmem) rfl
  set S₁ : Finset (Fin n) := insert h K with hS1def
  set F : Finset (Fin n) := (S₁.biUnion (fun x => G.neighborFinset x)) \ S₁ with hFdef
  set S₂ : Finset (Fin n) := (S₁ ∪ F)ᶜ with hS2def
  have hS1card : S₁.card = G.degree h - 1 := by
    rw [hS1def, Finset.card_insert_of_notMem hhK, hKcard]
    omega
  have hS1ne : S₁.Nonempty := by rw [hS1def]; exact Finset.insert_nonempty h K
  have huF : h ∉ F := by
    rw [hFdef]
    intro hmem
    rw [Finset.mem_sdiff] at hmem
    exact hmem.2 (by rw [hS1def]; exact Finset.mem_insert_self h K)
  have hdisjS1F : Disjoint S₁ F := by
    rw [Finset.disjoint_left]
    intro a ha haF
    rw [hFdef, Finset.mem_sdiff] at haF
    exact haF.2 ha
  have hS2card : S₂.card = n - (S₁.card + F.card) := by
    rw [hS2def, Finset.card_compl, Fintype.card_fin,
      Finset.card_union_of_disjoint hdisjS1F]
  -- the counting helper: an ordered adjacency block splits into neighbourhood slices
  have hcnt : ∀ (A C : Finset (Fin n)),
      ((A ×ˢ C).filter (fun q => G.Adj q.1 q.2)).card
        = ∑ a ∈ A, (G.neighborFinset a ∩ C).card := by
    intro A C
    rw [Finset.card_filter, Finset.sum_product]
    refine Finset.sum_congr rfl fun a _ => ?_
    have hset : G.neighborFinset a ∩ C = C.filter (fun v => G.Adj a v) := by
      ext v
      simp only [Finset.mem_inter, Finset.mem_filter, SimpleGraph.mem_neighborFinset]
      exact and_comm
    rw [hset, Finset.card_filter]
  -- the transpose helper (adjacency is symmetric)
  have htrans : ∀ (A C : Finset (Fin n)),
      ((A ×ˢ C).filter (fun q => G.Adj q.1 q.2)).card
        = ((C ×ˢ A).filter (fun q => G.Adj q.1 q.2)).card := by
    intro A C
    refine Finset.card_bij (fun q _ => (q.2, q.1)) ?_ ?_ ?_
    · intro q hq
      rw [Finset.mem_filter, Finset.mem_product] at hq ⊢
      exact ⟨⟨hq.1.2, hq.1.1⟩, G.adj_symm hq.2⟩
    · intro q _ r _ hqr
      exact Prod.ext (congrArg Prod.snd hqr) (congrArg Prod.fst hqr)
    · intro q hq
      refine ⟨(q.2, q.1), ?_, rfl⟩
      rw [Finset.mem_filter, Finset.mem_product] at hq ⊢
      exact ⟨⟨hq.1.2, hq.1.1⟩, G.adj_symm hq.2⟩
  -- every slice `N(x) ∖ S₁` has at most two elements (external-degree budget 2)
  have hsliceH : (G.neighborFinset h \ S₁).card ≤ 2 := by
    have hsub : G.neighborFinset h \ S₁ ⊆ G.neighborFinset h \ K :=
      Finset.sdiff_subset_sdiff (le_refl _) (by rw [hS1def]; exact Finset.subset_insert h K)
    calc (G.neighborFinset h \ S₁).card
        ≤ (G.neighborFinset h \ K).card := Finset.card_le_card hsub
      _ = (G.neighborFinset h).card - K.card := Finset.card_sdiff_of_subset hKsub
      _ = G.degree h - K.card := by rw [G.card_neighborFinset_eq_degree]
      _ ≤ 2 := by rw [hKcard]; omega
  have hsliceT : ∀ t ∈ K, (G.neighborFinset t \ S₁).card ≤ 2 := by
    intro t htK
    have htNh : t ∈ G.neighborFinset h := hKsub htK
    have hht : G.Adj h t := (G.mem_neighborFinset h t).mp htNh
    have hhNt : h ∈ G.neighborFinset t := (G.mem_neighborFinset t h).mpr hht.symm
    have hsub : G.neighborFinset t \ S₁ ⊆ (G.neighborFinset t).erase h := by
      intro x hx
      rw [Finset.mem_sdiff] at hx
      rw [Finset.mem_erase]
      refine ⟨fun hxh => hx.2 ?_, hx.1⟩
      rw [hS1def, hxh]
      exact Finset.mem_insert_self h K
    calc (G.neighborFinset t \ S₁).card
        ≤ ((G.neighborFinset t).erase h).card := Finset.card_le_card hsub
      _ = G.degree t - 1 := by
          rw [Finset.card_erase_of_mem hhNt, G.card_neighborFinset_eq_degree]
      _ = 2 := by rw [hKdeg t htK]
  have hslice : ∀ x ∈ S₁, (G.neighborFinset x \ S₁).card ≤ 2 := by
    intro x hx
    rw [hS1def, Finset.mem_insert] at hx
    rcases hx with rfl | hxK
    · exact hsliceH
    · exact hsliceT x hxK
  -- ∂₁ ≤ 2·|S₁|
  have hterm : ∀ a ∈ S₁, (G.neighborFinset a ∩ F).card ≤ 2 := by
    intro a ha
    have hsub : G.neighborFinset a ∩ F ⊆ G.neighborFinset a \ S₁ := by
      intro x hx
      rw [Finset.mem_inter] at hx
      rw [Finset.mem_sdiff]
      refine ⟨hx.1, ?_⟩
      have hxF := hx.2
      rw [hFdef, Finset.mem_sdiff] at hxF
      exact hxF.2
    exact le_trans (Finset.card_le_card hsub) (hslice a ha)
  have he1 : ((S₁ ×ˢ F).filter (fun q => G.Adj q.1 q.2)).card ≤ 2 * S₁.card := by
    rw [hcnt S₁ F]
    calc ∑ a ∈ S₁, (G.neighborFinset a ∩ F).card
        ≤ ∑ _a ∈ S₁, 2 := Finset.sum_le_sum hterm
      _ = 2 * S₁.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  -- |F| ≤ 2·|S₁|
  have hFcard : F.card ≤ 2 * S₁.card := by
    have hFsub2 : F ⊆ S₁.biUnion (fun x => G.neighborFinset x \ S₁) := by
      intro y hy
      rw [hFdef, Finset.mem_sdiff] at hy
      obtain ⟨hyNS, hyS1⟩ := hy
      rw [Finset.mem_biUnion] at hyNS ⊢
      obtain ⟨x, hxS1, hyx⟩ := hyNS
      exact ⟨x, hxS1, Finset.mem_sdiff.mpr ⟨hyx, hyS1⟩⟩
    calc F.card
        ≤ (S₁.biUnion (fun x => G.neighborFinset x \ S₁)).card := Finset.card_le_card hFsub2
      _ ≤ ∑ x ∈ S₁, (G.neighborFinset x \ S₁).card := Finset.card_biUnion_le
      _ ≤ ∑ _x ∈ S₁, 2 := Finset.sum_le_sum hslice
      _ = 2 * S₁.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  -- the hub-credited excess ledger: Σ_F (deg − 3) ≤ (n − 8) − (deg h − 3)
  have hFsubErase : F ⊆ Finset.univ.erase h := by
    intro x hx
    rw [Finset.mem_erase]
    refine ⟨?_, Finset.mem_univ x⟩
    rintro rfl
    exact huF hx
  have hexc : ∑ w ∈ F, (G.degree w - 3) ≤ n - 8 - (G.degree h - 3) := by
    have hle : ∑ w ∈ F, (G.degree w - 3)
        ≤ ∑ w ∈ Finset.univ.erase h, (G.degree w - 3) :=
      Finset.sum_le_sum_of_subset hFsubErase
    have hsplit : (G.degree h - 3) + ∑ w ∈ Finset.univ.erase h, (G.degree w - 3)
        = ∑ w : Fin n, (G.degree w - 3) :=
      Finset.add_sum_erase _ (fun w => G.degree w - 3) (Finset.mem_univ h)
    have htot : ∑ w : Fin n, (G.degree w - 3) = n - 8 := total_excess_eq hn8 G hm h3
    omega
  have hS2ne : S₂.Nonempty := by
    rw [← Finset.card_pos, hS2card]; omega
  have hdisj : Disjoint S₁ S₂ := by
    rw [Finset.disjoint_left]
    intro a ha1 ha2
    rw [hS2def, Finset.mem_compl] at ha2
    exact ha2 (Finset.mem_union_left F ha1)
  have hnc : ∀ a ∈ S₁, ∀ v ∈ S₂, ¬G.Adj a v := by
    intro a ha v hv hadj
    rw [hS2def, Finset.mem_compl] at hv
    have hvnotS1 : v ∉ S₁ := fun hh => hv (Finset.mem_union_left F hh)
    have hvnotF : v ∉ F := fun hh => hv (Finset.mem_union_right S₁ hh)
    apply hvnotF
    rw [hFdef, Finset.mem_sdiff]
    refine ⟨?_, hvnotS1⟩
    rw [Finset.mem_biUnion]
    exact ⟨a, ha, (G.mem_neighborFinset a v).mpr hadj⟩
  have hFeq : (S₁ ∪ S₂)ᶜ = F := by
    ext v
    constructor
    · intro hv
      rw [Finset.mem_compl, Finset.mem_union, not_or] at hv
      obtain ⟨hvS1, hvS2⟩ := hv
      rw [hS2def, Finset.mem_compl, not_not, Finset.mem_union] at hvS2
      rcases hvS2 with hh | hh
      · exact absurd hh hvS1
      · exact hh
    · intro hv
      rw [Finset.mem_compl, Finset.mem_union, not_or]
      exact ⟨Finset.disjoint_right.mp hdisjS1F hv,
        by rw [hS2def, Finset.mem_compl, not_not]; exact Finset.mem_union_right S₁ hv⟩
  -- ∂₂ ≤ 2·|S₂|
  have he2 : ((S₂ ×ˢ F).filter (fun q => G.Adj q.1 q.2)).card ≤ 2 * S₂.card := by
    rw [htrans S₂ F, hcnt F S₂]
    have hbound : ∀ w ∈ F, (G.neighborFinset w ∩ S₂).card ≤ G.degree w - 1 := by
      intro w hw
      obtain ⟨a, haS1, haw⟩ : ∃ a ∈ S₁, G.Adj a w := by
        have hwF := hw
        rw [hFdef, Finset.mem_sdiff, Finset.mem_biUnion] at hwF
        obtain ⟨⟨a, haS1, hwa⟩, _⟩ := hwF
        exact ⟨a, haS1, (G.mem_neighborFinset a w).mp hwa⟩
      have haNw : a ∈ G.neighborFinset w := (G.mem_neighborFinset w a).mpr haw.symm
      have haS2 : a ∉ S₂ := by
        rw [hS2def, Finset.mem_compl, not_not]
        exact Finset.mem_union_left F haS1
      have hsub : G.neighborFinset w ∩ S₂ ⊆ (G.neighborFinset w).erase a := by
        intro x hx
        rw [Finset.mem_inter] at hx
        rw [Finset.mem_erase]
        refine ⟨?_, hx.1⟩
        rintro rfl
        exact haS2 hx.2
      calc (G.neighborFinset w ∩ S₂).card
          ≤ ((G.neighborFinset w).erase a).card := Finset.card_le_card hsub
        _ = G.degree w - 1 := by
            rw [Finset.card_erase_of_mem haNw, G.card_neighborFinset_eq_degree]
    have hpt : ∀ w ∈ F, G.degree w - 1 = (G.degree w - 3) + 2 := by
      intro w _
      have := h3 w
      omega
    calc ∑ w ∈ F, (G.neighborFinset w ∩ S₂).card
        ≤ ∑ w ∈ F, (G.degree w - 1) := Finset.sum_le_sum hbound
      _ = ∑ w ∈ F, (G.degree w - 3) + F.card * 2 := by
          rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, Finset.sum_const,
            smul_eq_mul]
      _ ≤ 2 * S₂.card := by omega
  -- assemble the two-cluster law at the tie
  refine algConn_le_two_of_two_clusters G S₁ S₂ hS1ne hS2ne hdisj hnc ?_
  rw [hFeq]
  have hbound1 := Nat.mul_le_mul he1 (le_refl (S₂.card ^ 2))
  have hbound2 := Nat.mul_le_mul he2 (le_refl (S₁.card ^ 2))
  refine le_trans (add_le_add hbound1 hbound2) (le_of_eq ?_)
  ring

/-! ## The master-cycle kill

A cycle `c : ZMod k → Fin n` (injective, cyclic adjacency) with degree-sum tie
`Σ deg ≤ 4·k` is a tie-block: each cycle vertex has two on-cycle neighbours so
external slice `≤ deg − 2`, giving `∂₁ ≤ Σ(deg − 2) ≤ 2k`; crediting the cycle
excess back, `master_cycle_fires` fires at `n ≥ 3·Σ(deg − 1) − 8` (specializing
to `C_k`, the `(3,4,5)`-triangle at `n ≥ 19`, and alternating rows). -/

/-- **W1 — the master-cycle certificate.**  A graph on `Fin n` with `2(n−2)` edges, minimum
degree `≥ 3`, and an injective `c : ZMod k → Fin n` (`k ≥ 3`) forming a cycle
(`c i ~ c (i+1)` cyclically) whose degree sum satisfies the tie `Σ deg (c i) ≤ 4·k` has
`algConn G ≤ 2` whenever `3·Σ (deg (c i) − 1) ≤ n + 8`.

Instantiate the two-cluster law with the tie-block `S₁ = image c` (the cycle) against the bulk
`S₂ = (S₁ ∪ F)ᶜ`, `F = (⋃_{x ∈ S₁} N(x)) ∖ S₁` the moat: each slice `N(c i) ∖ S₁` has
`≤ deg (c i) − 2` elements (the two cycle neighbours stay inside), so `∂₁ ≤ Σ(deg − 2) ≤ 2·k`
and `|F| ≤ Σ(deg − 2)`, and the full excess ledger gives `∂₂ ≤ 2·|S₂|`; the Fiedler cut
condition closes by `ring`. -/
theorem master_cycle_fires {n : ℕ} [Nonempty (Fin n)] {k : ℕ} [NeZero k] (hk : 3 ≤ k)
    (G : SimpleGraph (Fin n)) (hm : G.edgeFinset.card = 2 * (n - 2))
    (h3 : ∀ v : Fin n, 3 ≤ G.degree v) (c : ZMod k → Fin n) (hcinj : Function.Injective c)
    (hadj : ∀ i : ZMod k, G.Adj (c i) (c (i + 1)))
    (hsum : ∑ i : ZMod k, G.degree (c i) ≤ 4 * k)
    (hn : 3 * (∑ i : ZMod k, (G.degree (c i) - 1)) ≤ n + 8) :
    algConn G ≤ 2 := by
  classical
  let : DecidableEq (Fin n) := Classical.decEq (Fin n)
  have hn8 : 8 ≤ n := by
    have hb : 3 * k ≤ ∑ i : ZMod k, G.degree (c i) := by
      calc 3 * k = ∑ _i : ZMod k, 3 := by
            rw [Finset.sum_const, Finset.card_univ, ZMod.card, smul_eq_mul, mul_comm]
        _ ≤ ∑ i : ZMod k, G.degree (c i) := Finset.sum_le_sum (fun i _ => h3 (c i))
    have hP : 2 * k ≤ ∑ i : ZMod k, (G.degree (c i) - 1) := by
      calc 2 * k = ∑ _i : ZMod k, 2 := by
            rw [Finset.sum_const, Finset.card_univ, ZMod.card, smul_eq_mul, mul_comm]
        _ ≤ ∑ i : ZMod k, (G.degree (c i) - 1) :=
            Finset.sum_le_sum (fun i _ => by have := h3 (c i); omega)
    omega
  -- the two distinct cycle neighbours of every vertex live in `S₁`
  have h2ne : (2 : ZMod k) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod k) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    have := Nat.le_of_dvd (by norm_num) h'
    omega
  set S₁ : Finset (Fin n) := Finset.image c Finset.univ with hS1def
  set F : Finset (Fin n) := (S₁.biUnion (fun x => G.neighborFinset x)) \ S₁ with hFdef
  set S₂ : Finset (Fin n) := (S₁ ∪ F)ᶜ with hS2def
  set D : ℕ := ∑ i : ZMod k, G.degree (c i) with hDdef
  have hS1card : S₁.card = k := by
    rw [hS1def, Finset.card_image_of_injective _ hcinj, Finset.card_univ, ZMod.card]
  have hS1ne : S₁.Nonempty :=
    ⟨c 0, Finset.mem_image.mpr ⟨0, Finset.mem_univ 0, rfl⟩⟩
  have hDS1 : ∑ x ∈ S₁, G.degree x = D := by
    rw [hDdef, hS1def, Finset.sum_image (fun x _ y _ h => hcinj h)]
  -- per-vertex slice bound: each cycle vertex has `≥ 2` neighbours inside `S₁`
  have hsliceIdx : ∀ i : ZMod k,
      (G.neighborFinset (c i) \ S₁).card ≤ G.degree (c i) - 2 := by
    intro i
    have hib : (i - 1) + 1 = i := by ring
    have hadjb : G.Adj (c i) (c (i - 1)) := by
      have hh := hadj (i - 1)
      rw [hib] at hh
      exact hh.symm
    have hkey : (i : ZMod k) + 1 ≠ i - 1 := by
      intro heq
      apply h2ne
      have h2 : (2 : ZMod k) = (i + 1) - (i - 1) := by ring
      rw [heq, sub_self] at h2
      exact h2
    have hdist : c (i + 1) ≠ c (i - 1) := fun heq => hkey (hcinj heq)
    have h2le : 2 ≤ (G.neighborFinset (c i) ∩ S₁).card := by
      have hsub : ({c (i + 1), c (i - 1)} : Finset (Fin n))
          ⊆ G.neighborFinset (c i) ∩ S₁ := by
        intro x hx
        rw [Finset.mem_insert, Finset.mem_singleton] at hx
        rw [Finset.mem_inter]
        rcases hx with rfl | rfl
        · exact ⟨(G.mem_neighborFinset _ _).mpr (hadj i),
            Finset.mem_image.mpr ⟨i + 1, Finset.mem_univ _, rfl⟩⟩
        · exact ⟨(G.mem_neighborFinset _ _).mpr hadjb,
            Finset.mem_image.mpr ⟨i - 1, Finset.mem_univ _, rfl⟩⟩
      calc 2 = ({c (i + 1), c (i - 1)} : Finset (Fin n)).card := by
            rw [Finset.card_pair hdist]
        _ ≤ _ := Finset.card_le_card hsub
    have hcard : (G.neighborFinset (c i) ∩ S₁).card + (G.neighborFinset (c i) \ S₁).card
        = G.degree (c i) := by
      rw [Finset.card_inter_add_card_sdiff, G.card_neighborFinset_eq_degree]
    omega
  have hslice : ∀ x ∈ S₁, (G.neighborFinset x \ S₁).card ≤ G.degree x - 2 := by
    intro x hx
    rw [hS1def, Finset.mem_image] at hx
    obtain ⟨i, _, rfl⟩ := hx
    exact hsliceIdx i
  -- the disjointness / cardinality bookkeeping (mirrors `star_moat_fires`)
  have hdisjS1F : Disjoint S₁ F := by
    rw [Finset.disjoint_left]
    intro a ha haF
    rw [hFdef, Finset.mem_sdiff] at haF
    exact haF.2 ha
  have hS2card : S₂.card = n - (S₁.card + F.card) := by
    rw [hS2def, Finset.card_compl, Fintype.card_fin,
      Finset.card_union_of_disjoint hdisjS1F]
  have hkfn : S₁.card + F.card ≤ n := by
    have h : (S₁ ∪ F).card ≤ Fintype.card (Fin n) := Finset.card_le_univ _
    rw [Fintype.card_fin, Finset.card_union_of_disjoint hdisjS1F] at h
    exact h
  -- the counting helper: an ordered adjacency block splits into neighbourhood slices
  have hcnt : ∀ (A C : Finset (Fin n)),
      ((A ×ˢ C).filter (fun q => G.Adj q.1 q.2)).card
        = ∑ a ∈ A, (G.neighborFinset a ∩ C).card := by
    intro A C
    rw [Finset.card_filter, Finset.sum_product]
    refine Finset.sum_congr rfl fun a _ => ?_
    have hset : G.neighborFinset a ∩ C = C.filter (fun v => G.Adj a v) := by
      ext v
      simp only [Finset.mem_inter, Finset.mem_filter, SimpleGraph.mem_neighborFinset]
      exact and_comm
    rw [hset, Finset.card_filter]
  -- the transpose helper (adjacency is symmetric)
  have htrans : ∀ (A C : Finset (Fin n)),
      ((A ×ˢ C).filter (fun q => G.Adj q.1 q.2)).card
        = ((C ×ˢ A).filter (fun q => G.Adj q.1 q.2)).card := by
    intro A C
    refine Finset.card_bij (fun q _ => (q.2, q.1)) ?_ ?_ ?_
    · intro q hq
      rw [Finset.mem_filter, Finset.mem_product] at hq ⊢
      exact ⟨⟨hq.1.2, hq.1.1⟩, G.adj_symm hq.2⟩
    · intro q _ r _ hqr
      exact Prod.ext (congrArg Prod.snd hqr) (congrArg Prod.fst hqr)
    · intro q hq
      refine ⟨(q.2, q.1), ?_, rfl⟩
      rw [Finset.mem_filter, Finset.mem_product] at hq ⊢
      exact ⟨⟨hq.1.2, hq.1.1⟩, G.adj_symm hq.2⟩
  -- `Σ_{S₁}(deg − 2) + 2·|S₁| = D` and `Σ_{S₁}(deg − 3) + 3·|S₁| = D`
  have keyB : (∑ x ∈ S₁, (G.degree x - 2)) + 2 * S₁.card = D := by
    have h1 : 2 * S₁.card = ∑ _x ∈ S₁, 2 := by
      rw [Finset.sum_const, smul_eq_mul, mul_comm]
    rw [h1, ← Finset.sum_add_distrib, ← hDS1]
    exact Finset.sum_congr rfl (fun x _ => Nat.sub_add_cancel (by have := h3 x; omega))
  have keyX : (∑ x ∈ S₁, (G.degree x - 3)) + 3 * S₁.card = D := by
    have h1 : 3 * S₁.card = ∑ _x ∈ S₁, 3 := by
      rw [Finset.sum_const, smul_eq_mul, mul_comm]
    rw [h1, ← Finset.sum_add_distrib, ← hDS1]
    exact Finset.sum_congr rfl (fun x _ => Nat.sub_add_cancel (h3 x))
  have keyP : (∑ i : ZMod k, (G.degree (c i) - 1)) + k = D := by
    have hstep : ∑ i : ZMod k, ((G.degree (c i) - 1) + 1) = D := by
      rw [hDdef]
      exact Finset.sum_congr rfl (fun i _ => Nat.sub_add_cancel (by have := h3 (c i); omega))
    rw [Finset.sum_add_distrib] at hstep
    simp only [Finset.sum_const, Finset.card_univ, ZMod.card, smul_eq_mul, mul_one] at hstep
    exact hstep
  -- the moat is capped by the same slice budget
  have hFB : F.card ≤ ∑ x ∈ S₁, (G.degree x - 2) := by
    have hFsub2 : F ⊆ S₁.biUnion (fun x => G.neighborFinset x \ S₁) := by
      intro y hy
      rw [hFdef, Finset.mem_sdiff] at hy
      obtain ⟨hyNS, hyS1⟩ := hy
      rw [Finset.mem_biUnion] at hyNS ⊢
      obtain ⟨x, hxS1, hyx⟩ := hyNS
      exact ⟨x, hxS1, Finset.mem_sdiff.mpr ⟨hyx, hyS1⟩⟩
    calc F.card
        ≤ (S₁.biUnion (fun x => G.neighborFinset x \ S₁)).card := Finset.card_le_card hFsub2
      _ ≤ ∑ x ∈ S₁, (G.neighborFinset x \ S₁).card := Finset.card_biUnion_le
      _ ≤ ∑ x ∈ S₁, (G.degree x - 2) := Finset.sum_le_sum hslice
  have keyF : F.card + 2 * S₁.card ≤ D := by
    have := keyB
    omega
  -- the full excess ledger: `Σ_F(deg − 3) + Σ_{S₁}(deg − 3) ≤ n − 8`
  have hexc : (∑ w ∈ F, (G.degree w - 3)) + (∑ x ∈ S₁, (G.degree x - 3)) ≤ n - 8 := by
    have hunion : (∑ w ∈ F, (G.degree w - 3)) + (∑ x ∈ S₁, (G.degree x - 3))
        = ∑ w ∈ (F ∪ S₁), (G.degree w - 3) := (Finset.sum_union hdisjS1F.symm).symm
    rw [hunion]
    calc ∑ w ∈ (F ∪ S₁), (G.degree w - 3)
        ≤ ∑ w : Fin n, (G.degree w - 3) := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
      _ = n - 8 := total_excess_eq hn8 G hm h3
  have hS2ne : S₂.Nonempty := by
    rw [← Finset.card_pos, hS2card]
    have := keyF; have := hsum; have := keyX; have := keyP; have := hn; have := hS1card
    omega
  have hdisj : Disjoint S₁ S₂ := by
    rw [Finset.disjoint_left]
    intro a ha1 ha2
    rw [hS2def, Finset.mem_compl] at ha2
    exact ha2 (Finset.mem_union_left F ha1)
  have hnc : ∀ a ∈ S₁, ∀ v ∈ S₂, ¬G.Adj a v := by
    intro a ha v hv hadjav
    rw [hS2def, Finset.mem_compl] at hv
    have hvnotS1 : v ∉ S₁ := fun hh => hv (Finset.mem_union_left F hh)
    have hvnotF : v ∉ F := fun hh => hv (Finset.mem_union_right S₁ hh)
    apply hvnotF
    rw [hFdef, Finset.mem_sdiff]
    refine ⟨?_, hvnotS1⟩
    rw [Finset.mem_biUnion]
    exact ⟨a, ha, (G.mem_neighborFinset a v).mpr hadjav⟩
  have hFeq : (S₁ ∪ S₂)ᶜ = F := by
    ext v
    constructor
    · intro hv
      rw [Finset.mem_compl, Finset.mem_union, not_or] at hv
      obtain ⟨hvS1, hvS2⟩ := hv
      rw [hS2def, Finset.mem_compl, not_not, Finset.mem_union] at hvS2
      rcases hvS2 with hh | hh
      · exact absurd hh hvS1
      · exact hh
    · intro hv
      rw [Finset.mem_compl, Finset.mem_union, not_or]
      exact ⟨Finset.disjoint_right.mp hdisjS1F hv,
        by rw [hS2def, Finset.mem_compl, not_not]; exact Finset.mem_union_right S₁ hv⟩
  -- ∂₁ ≤ 2·|S₁|
  have he1 : ((S₁ ×ˢ F).filter (fun q => G.Adj q.1 q.2)).card ≤ 2 * S₁.card := by
    rw [hcnt S₁ F]
    have hterm : ∀ a ∈ S₁, (G.neighborFinset a ∩ F).card ≤ G.degree a - 2 := by
      intro a ha
      have hsub : G.neighborFinset a ∩ F ⊆ G.neighborFinset a \ S₁ := by
        intro x hx
        rw [Finset.mem_inter] at hx
        rw [Finset.mem_sdiff]
        refine ⟨hx.1, ?_⟩
        have hxF := hx.2
        rw [hFdef, Finset.mem_sdiff] at hxF
        exact hxF.2
      exact le_trans (Finset.card_le_card hsub) (hslice a ha)
    calc ∑ a ∈ S₁, (G.neighborFinset a ∩ F).card
        ≤ ∑ a ∈ S₁, (G.degree a - 2) := Finset.sum_le_sum hterm
      _ ≤ 2 * S₁.card := by
          have := keyB; have := hsum; have := hS1card; omega
  -- ∂₂ ≤ 2·|S₂|
  have he2 : ((S₂ ×ˢ F).filter (fun q => G.Adj q.1 q.2)).card ≤ 2 * S₂.card := by
    rw [htrans S₂ F, hcnt F S₂]
    have hbound : ∀ w ∈ F, (G.neighborFinset w ∩ S₂).card ≤ G.degree w - 1 := by
      intro w hw
      obtain ⟨a, haS1, haw⟩ : ∃ a ∈ S₁, G.Adj a w := by
        have hwF := hw
        rw [hFdef, Finset.mem_sdiff, Finset.mem_biUnion] at hwF
        obtain ⟨⟨a, haS1, hwa⟩, _⟩ := hwF
        exact ⟨a, haS1, (G.mem_neighborFinset a w).mp hwa⟩
      have haNw : a ∈ G.neighborFinset w := (G.mem_neighborFinset w a).mpr haw.symm
      have haS2 : a ∉ S₂ := by
        rw [hS2def, Finset.mem_compl, not_not]
        exact Finset.mem_union_left F haS1
      have hsub : G.neighborFinset w ∩ S₂ ⊆ (G.neighborFinset w).erase a := by
        intro x hx
        rw [Finset.mem_inter] at hx
        rw [Finset.mem_erase]
        refine ⟨?_, hx.1⟩
        rintro rfl
        exact haS2 hx.2
      calc (G.neighborFinset w ∩ S₂).card
          ≤ ((G.neighborFinset w).erase a).card := Finset.card_le_card hsub
        _ = G.degree w - 1 := by
            rw [Finset.card_erase_of_mem haNw, G.card_neighborFinset_eq_degree]
    have hpt : ∀ w ∈ F, G.degree w - 1 = (G.degree w - 3) + 2 := by
      intro w _
      have := h3 w
      omega
    calc ∑ w ∈ F, (G.neighborFinset w ∩ S₂).card
        ≤ ∑ w ∈ F, (G.degree w - 1) := Finset.sum_le_sum hbound
      _ = ∑ w ∈ F, (G.degree w - 3) + F.card * 2 := by
          rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, Finset.sum_const,
            smul_eq_mul]
      _ ≤ 2 * S₂.card := by
          have := hexc; have := keyX; have := keyP; have := hsum; have := hn
          have := keyF; have := hS2card; have := hkfn; have := hS1card
          omega
  -- assemble the two-cluster law at the tie
  refine algConn_le_two_of_two_clusters G S₁ S₂ hS1ne hS2ne hdisj hnc ?_
  rw [hFeq]
  have hbound1 := Nat.mul_le_mul he1 (le_refl (S₂.card ^ 2))
  have hbound2 := Nat.mul_le_mul he2 (le_refl (S₁.card ^ 2))
  refine le_trans (add_le_add hbound1 hbound2) (le_of_eq ?_)
  ring

/-! ## The decorated-edge moat kill

The *decorated-edge* generalization of the star-moat certificate: the tie-block
`S₁ = {u, v} ∪ Ku ∪ Kv` (an adjacent hub pair with `|Ku| = deg u − 3`,
`|Kv| = deg v − 3` twins), each `S₁`-vertex keeping external budget `2`;
crediting both hubs' excess back, `deco_edge_moat_fires` fires at
`9·(deg u + deg v) ≤ n + 42` (`z4c_fires`: adjacent degree-4 hubs with one twin
each at `n ≥ 30`). -/

/-- **W3 — the decorated-edge moat certificate.**  A graph on `Fin n` with `2(n−2)` edges,
minimum degree `≥ 3`, adjacent hubs `u, v`, and twin sets `Ku ⊆ N(u)`, `Kv ⊆ N(v)` of degree-`3`
vertices with `|Ku| = deg u − 3`, `|Kv| = deg v − 3` (disjoint, and avoiding the opposite hub)
has `algConn G ≤ 2` whenever `9·(deg u + deg v) ≤ n + 42`.

Instantiate the two-cluster law with the tie-block `S₁ = {u, v} ∪ Ku ∪ Kv` against the bulk
`S₂ = (S₁ ∪ F)ᶜ`, `F = (⋃_{x ∈ S₁} N(x)) ∖ S₁` the moat: each slice `N(x) ∖ S₁` has `≤ 2`
elements (each hub loses the other hub and its twins; each twin loses its hub), so `∂₁ ≤ 2|S₁|`
and `|F| ≤ 2|S₁|`, and the pair-credited excess ledger gives `∂₂ ≤ 2|S₂|`; the Fiedler cut
condition closes by `ring`. -/
theorem deco_edge_moat_fires {n : ℕ} [Nonempty (Fin n)]
    (G : SimpleGraph (Fin n)) (hm : G.edgeFinset.card = 2 * (n - 2))
    (h3 : ∀ w : Fin n, 3 ≤ G.degree w) (u v : Fin n) (Ku Kv : Finset (Fin n))
    (huv : G.Adj u v)
    (hKusub : Ku ⊆ G.neighborFinset u) (hKudeg : ∀ t ∈ Ku, G.degree t = 3)
    (hKucard : Ku.card = G.degree u - 3)
    (hKvsub : Kv ⊆ G.neighborFinset v) (hKvdeg : ∀ t ∈ Kv, G.degree t = 3)
    (hKvcard : Kv.card = G.degree v - 3)
    (huKv : u ∉ Kv) (hvKu : v ∉ Ku) (hKuKv : Disjoint Ku Kv)
    (hfire : 9 * (G.degree u + G.degree v) ≤ n + 42) :
    algConn G ≤ 2 := by
  classical
  let : DecidableEq (Fin n) := Classical.decEq (Fin n)
  have hdeg3u : 3 ≤ G.degree u := h3 u
  have hdeg3v : 3 ≤ G.degree v := h3 v
  have hn8 : 8 ≤ n := by omega
  have huv' : u ≠ v := G.ne_of_adj huv
  have huKu : u ∉ Ku := by
    intro hu
    have hmem := hKusub hu
    rw [G.mem_neighborFinset] at hmem
    exact (G.ne_of_adj hmem) rfl
  have hvKv : v ∉ Kv := by
    intro hv
    have hmem := hKvsub hv
    rw [G.mem_neighborFinset] at hmem
    exact (G.ne_of_adj hmem) rfl
  set S₁ : Finset (Fin n) := insert u (insert v (Ku ∪ Kv)) with hS1def
  set F : Finset (Fin n) := (S₁.biUnion (fun x => G.neighborFinset x)) \ S₁ with hFdef
  set S₂ : Finset (Fin n) := (S₁ ∪ F)ᶜ with hS2def
  have hu_notin : u ∉ insert v (Ku ∪ Kv) := by
    rw [Finset.mem_insert, Finset.mem_union]
    rintro (h | h | h)
    · exact huv' h
    · exact huKu h
    · exact huKv h
  have hv_notin : v ∉ Ku ∪ Kv := by
    rw [Finset.mem_union]
    rintro (h | h)
    · exact hvKu h
    · exact hvKv h
  have hS1card : S₁.card = G.degree u + G.degree v - 4 := by
    rw [hS1def, Finset.card_insert_of_notMem hu_notin,
      Finset.card_insert_of_notMem hv_notin, Finset.card_union_of_disjoint hKuKv,
      hKucard, hKvcard]
    omega
  have hS1ne : S₁.Nonempty := by rw [hS1def]; exact Finset.insert_nonempty u _
  have huF : u ∉ F := by
    rw [hFdef]
    intro hmem
    rw [Finset.mem_sdiff] at hmem
    exact hmem.2 (by rw [hS1def]; exact Finset.mem_insert_self u _)
  have hvF : v ∉ F := by
    rw [hFdef]
    intro hmem
    rw [Finset.mem_sdiff] at hmem
    exact hmem.2 (by rw [hS1def]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self v _))
  have hdisjS1F : Disjoint S₁ F := by
    rw [Finset.disjoint_left]
    intro a ha haF
    rw [hFdef, Finset.mem_sdiff] at haF
    exact haF.2 ha
  have hS2card : S₂.card = n - (S₁.card + F.card) := by
    rw [hS2def, Finset.card_compl, Fintype.card_fin,
      Finset.card_union_of_disjoint hdisjS1F]
  -- the counting helper: an ordered adjacency block splits into neighbourhood slices
  have hcnt : ∀ (A C : Finset (Fin n)),
      ((A ×ˢ C).filter (fun q => G.Adj q.1 q.2)).card
        = ∑ a ∈ A, (G.neighborFinset a ∩ C).card := by
    intro A C
    rw [Finset.card_filter, Finset.sum_product]
    refine Finset.sum_congr rfl fun a _ => ?_
    have hset : G.neighborFinset a ∩ C = C.filter (fun v => G.Adj a v) := by
      ext v
      simp only [Finset.mem_inter, Finset.mem_filter, SimpleGraph.mem_neighborFinset]
      exact and_comm
    rw [hset, Finset.card_filter]
  -- the transpose helper (adjacency is symmetric)
  have htrans : ∀ (A C : Finset (Fin n)),
      ((A ×ˢ C).filter (fun q => G.Adj q.1 q.2)).card
        = ((C ×ˢ A).filter (fun q => G.Adj q.1 q.2)).card := by
    intro A C
    refine Finset.card_bij (fun q _ => (q.2, q.1)) ?_ ?_ ?_
    · intro q hq
      rw [Finset.mem_filter, Finset.mem_product] at hq ⊢
      exact ⟨⟨hq.1.2, hq.1.1⟩, G.adj_symm hq.2⟩
    · intro q _ r _ hqr
      exact Prod.ext (congrArg Prod.snd hqr) (congrArg Prod.fst hqr)
    · intro q hq
      refine ⟨(q.2, q.1), ?_, rfl⟩
      rw [Finset.mem_filter, Finset.mem_product] at hq ⊢
      exact ⟨⟨hq.1.2, hq.1.1⟩, G.adj_symm hq.2⟩
  -- every slice `N(x) ∖ S₁` has at most two elements (external-degree budget 2)
  have hsliceU : (G.neighborFinset u \ S₁).card ≤ 2 := by
    have hivku_nb : insert v Ku ⊆ G.neighborFinset u :=
      Finset.insert_subset ((G.mem_neighborFinset u v).mpr huv) hKusub
    have hivku_S1 : insert v Ku ⊆ S₁ := by
      refine Finset.insert_subset ?_ ?_
      · rw [hS1def]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self v _)
      · intro x hxKu
        rw [hS1def]
        exact Finset.mem_insert_of_mem
          (Finset.mem_insert_of_mem (Finset.mem_union_left Kv hxKu))
    have hsub : G.neighborFinset u \ S₁ ⊆ G.neighborFinset u \ insert v Ku :=
      Finset.sdiff_subset_sdiff (le_refl _) hivku_S1
    calc (G.neighborFinset u \ S₁).card
        ≤ (G.neighborFinset u \ insert v Ku).card := Finset.card_le_card hsub
      _ = (G.neighborFinset u).card - (insert v Ku).card :=
          Finset.card_sdiff_of_subset hivku_nb
      _ = G.degree u - (insert v Ku).card := by rw [G.card_neighborFinset_eq_degree]
      _ = 2 := by rw [Finset.card_insert_of_notMem hvKu, hKucard]; omega
  have hsliceV : (G.neighborFinset v \ S₁).card ≤ 2 := by
    have hiukv_nb : insert u Kv ⊆ G.neighborFinset v :=
      Finset.insert_subset ((G.mem_neighborFinset v u).mpr huv.symm) hKvsub
    have hiukv_S1 : insert u Kv ⊆ S₁ := by
      refine Finset.insert_subset ?_ ?_
      · rw [hS1def]; exact Finset.mem_insert_self u _
      · intro x hxKv
        rw [hS1def]
        exact Finset.mem_insert_of_mem
          (Finset.mem_insert_of_mem (Finset.mem_union_right Ku hxKv))
    have hsub : G.neighborFinset v \ S₁ ⊆ G.neighborFinset v \ insert u Kv :=
      Finset.sdiff_subset_sdiff (le_refl _) hiukv_S1
    calc (G.neighborFinset v \ S₁).card
        ≤ (G.neighborFinset v \ insert u Kv).card := Finset.card_le_card hsub
      _ = (G.neighborFinset v).card - (insert u Kv).card :=
          Finset.card_sdiff_of_subset hiukv_nb
      _ = G.degree v - (insert u Kv).card := by rw [G.card_neighborFinset_eq_degree]
      _ = 2 := by rw [Finset.card_insert_of_notMem huKv, hKvcard]; omega
  have hsliceTu : ∀ t ∈ Ku, (G.neighborFinset t \ S₁).card ≤ 2 := by
    intro t htK
    have htNu : t ∈ G.neighborFinset u := hKusub htK
    have hut : G.Adj u t := (G.mem_neighborFinset u t).mp htNu
    have huNt : u ∈ G.neighborFinset t := (G.mem_neighborFinset t u).mpr hut.symm
    have hsub : G.neighborFinset t \ S₁ ⊆ (G.neighborFinset t).erase u := by
      intro x hx
      rw [Finset.mem_sdiff] at hx
      rw [Finset.mem_erase]
      refine ⟨fun hxu => hx.2 ?_, hx.1⟩
      rw [hS1def, hxu]
      exact Finset.mem_insert_self u _
    calc (G.neighborFinset t \ S₁).card
        ≤ ((G.neighborFinset t).erase u).card := Finset.card_le_card hsub
      _ = G.degree t - 1 := by
          rw [Finset.card_erase_of_mem huNt, G.card_neighborFinset_eq_degree]
      _ = 2 := by rw [hKudeg t htK]
  have hsliceTv : ∀ t ∈ Kv, (G.neighborFinset t \ S₁).card ≤ 2 := by
    intro t htK
    have htNv : t ∈ G.neighborFinset v := hKvsub htK
    have hvt : G.Adj v t := (G.mem_neighborFinset v t).mp htNv
    have hvNt : v ∈ G.neighborFinset t := (G.mem_neighborFinset t v).mpr hvt.symm
    have hsub : G.neighborFinset t \ S₁ ⊆ (G.neighborFinset t).erase v := by
      intro x hx
      rw [Finset.mem_sdiff] at hx
      rw [Finset.mem_erase]
      refine ⟨fun hxv => hx.2 ?_, hx.1⟩
      rw [hS1def, hxv]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_self v _)
    calc (G.neighborFinset t \ S₁).card
        ≤ ((G.neighborFinset t).erase v).card := Finset.card_le_card hsub
      _ = G.degree t - 1 := by
          rw [Finset.card_erase_of_mem hvNt, G.card_neighborFinset_eq_degree]
      _ = 2 := by rw [hKvdeg t htK]
  have hslice : ∀ x ∈ S₁, (G.neighborFinset x \ S₁).card ≤ 2 := by
    intro x hx
    rw [hS1def, Finset.mem_insert, Finset.mem_insert, Finset.mem_union] at hx
    rcases hx with rfl | rfl | hxKu | hxKv
    · exact hsliceU
    · exact hsliceV
    · exact hsliceTu x hxKu
    · exact hsliceTv x hxKv
  -- ∂₁ ≤ 2·|S₁|
  have hterm : ∀ a ∈ S₁, (G.neighborFinset a ∩ F).card ≤ 2 := by
    intro a ha
    have hsub : G.neighborFinset a ∩ F ⊆ G.neighborFinset a \ S₁ := by
      intro x hx
      rw [Finset.mem_inter] at hx
      rw [Finset.mem_sdiff]
      refine ⟨hx.1, ?_⟩
      have hxF := hx.2
      rw [hFdef, Finset.mem_sdiff] at hxF
      exact hxF.2
    exact le_trans (Finset.card_le_card hsub) (hslice a ha)
  have he1 : ((S₁ ×ˢ F).filter (fun q => G.Adj q.1 q.2)).card ≤ 2 * S₁.card := by
    rw [hcnt S₁ F]
    calc ∑ a ∈ S₁, (G.neighborFinset a ∩ F).card
        ≤ ∑ _a ∈ S₁, 2 := Finset.sum_le_sum hterm
      _ = 2 * S₁.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  -- |F| ≤ 2·|S₁|
  have hFcard : F.card ≤ 2 * S₁.card := by
    have hFsub2 : F ⊆ S₁.biUnion (fun x => G.neighborFinset x \ S₁) := by
      intro y hy
      rw [hFdef, Finset.mem_sdiff] at hy
      obtain ⟨hyNS, hyS1⟩ := hy
      rw [Finset.mem_biUnion] at hyNS ⊢
      obtain ⟨x, hxS1, hyx⟩ := hyNS
      exact ⟨x, hxS1, Finset.mem_sdiff.mpr ⟨hyx, hyS1⟩⟩
    calc F.card
        ≤ (S₁.biUnion (fun x => G.neighborFinset x \ S₁)).card := Finset.card_le_card hFsub2
      _ ≤ ∑ x ∈ S₁, (G.neighborFinset x \ S₁).card := Finset.card_biUnion_le
      _ ≤ ∑ _x ∈ S₁, 2 := Finset.sum_le_sum hslice
      _ = 2 * S₁.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  -- the pair-credited excess ledger: Σ_F (deg − 3) ≤ (n − 8) − (deg u − 3) − (deg v − 3)
  have hFsubErase : F ⊆ (Finset.univ.erase u).erase v := by
    intro x hx
    rw [Finset.mem_erase, Finset.mem_erase]
    refine ⟨?_, ?_, Finset.mem_univ x⟩
    · rintro rfl; exact hvF hx
    · rintro rfl; exact huF hx
  have hexc : ∑ w ∈ F, (G.degree w - 3)
      ≤ (n - 8) - (G.degree u - 3) - (G.degree v - 3) := by
    have hle : ∑ w ∈ F, (G.degree w - 3)
        ≤ ∑ w ∈ (Finset.univ.erase u).erase v, (G.degree w - 3) :=
      Finset.sum_le_sum_of_subset hFsubErase
    have hsplit1 : (G.degree u - 3) + ∑ w ∈ Finset.univ.erase u, (G.degree w - 3)
        = ∑ w : Fin n, (G.degree w - 3) :=
      Finset.add_sum_erase _ (fun w => G.degree w - 3) (Finset.mem_univ u)
    have hsplit2 : (G.degree v - 3) + ∑ w ∈ (Finset.univ.erase u).erase v, (G.degree w - 3)
        = ∑ w ∈ Finset.univ.erase u, (G.degree w - 3) :=
      Finset.add_sum_erase _ (fun w => G.degree w - 3)
        (Finset.mem_erase.mpr ⟨huv'.symm, Finset.mem_univ v⟩)
    have htot : ∑ w : Fin n, (G.degree w - 3) = n - 8 := total_excess_eq hn8 G hm h3
    omega
  have hS2ne : S₂.Nonempty := by
    rw [← Finset.card_pos, hS2card]; omega
  have hdisj : Disjoint S₁ S₂ := by
    rw [Finset.disjoint_left]
    intro a ha1 ha2
    rw [hS2def, Finset.mem_compl] at ha2
    exact ha2 (Finset.mem_union_left F ha1)
  have hnc : ∀ a ∈ S₁, ∀ w ∈ S₂, ¬G.Adj a w := by
    intro a ha w hw hadj
    rw [hS2def, Finset.mem_compl] at hw
    have hwnotS1 : w ∉ S₁ := fun hh => hw (Finset.mem_union_left F hh)
    have hwnotF : w ∉ F := fun hh => hw (Finset.mem_union_right S₁ hh)
    apply hwnotF
    rw [hFdef, Finset.mem_sdiff]
    refine ⟨?_, hwnotS1⟩
    rw [Finset.mem_biUnion]
    exact ⟨a, ha, (G.mem_neighborFinset a w).mpr hadj⟩
  have hFeq : (S₁ ∪ S₂)ᶜ = F := by
    ext w
    constructor
    · intro hw
      rw [Finset.mem_compl, Finset.mem_union, not_or] at hw
      obtain ⟨hwS1, hwS2⟩ := hw
      rw [hS2def, Finset.mem_compl, not_not, Finset.mem_union] at hwS2
      rcases hwS2 with hh | hh
      · exact absurd hh hwS1
      · exact hh
    · intro hw
      rw [Finset.mem_compl, Finset.mem_union, not_or]
      exact ⟨Finset.disjoint_right.mp hdisjS1F hw,
        by rw [hS2def, Finset.mem_compl, not_not]; exact Finset.mem_union_right S₁ hw⟩
  -- ∂₂ ≤ 2·|S₂|
  have he2 : ((S₂ ×ˢ F).filter (fun q => G.Adj q.1 q.2)).card ≤ 2 * S₂.card := by
    rw [htrans S₂ F, hcnt F S₂]
    have hbound : ∀ w ∈ F, (G.neighborFinset w ∩ S₂).card ≤ G.degree w - 1 := by
      intro w hw
      obtain ⟨a, haS1, haw⟩ : ∃ a ∈ S₁, G.Adj a w := by
        have hwF := hw
        rw [hFdef, Finset.mem_sdiff, Finset.mem_biUnion] at hwF
        obtain ⟨⟨a, haS1, hwa⟩, _⟩ := hwF
        exact ⟨a, haS1, (G.mem_neighborFinset a w).mp hwa⟩
      have haNw : a ∈ G.neighborFinset w := (G.mem_neighborFinset w a).mpr haw.symm
      have haS2 : a ∉ S₂ := by
        rw [hS2def, Finset.mem_compl, not_not]
        exact Finset.mem_union_left F haS1
      have hsub : G.neighborFinset w ∩ S₂ ⊆ (G.neighborFinset w).erase a := by
        intro x hx
        rw [Finset.mem_inter] at hx
        rw [Finset.mem_erase]
        refine ⟨?_, hx.1⟩
        rintro rfl
        exact haS2 hx.2
      calc (G.neighborFinset w ∩ S₂).card
          ≤ ((G.neighborFinset w).erase a).card := Finset.card_le_card hsub
        _ = G.degree w - 1 := by
            rw [Finset.card_erase_of_mem haNw, G.card_neighborFinset_eq_degree]
    have hpt : ∀ w ∈ F, G.degree w - 1 = (G.degree w - 3) + 2 := by
      intro w _
      have := h3 w
      omega
    calc ∑ w ∈ F, (G.neighborFinset w ∩ S₂).card
        ≤ ∑ w ∈ F, (G.degree w - 1) := Finset.sum_le_sum hbound
      _ = ∑ w ∈ F, (G.degree w - 3) + F.card * 2 := by
          rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, Finset.sum_const,
            smul_eq_mul]
      _ ≤ 2 * S₂.card := by omega
  -- assemble the two-cluster law at the tie
  refine algConn_le_two_of_two_clusters G S₁ S₂ hS1ne hS2ne hdisj hnc ?_
  rw [hFeq]
  have hbound1 := Nat.mul_le_mul he1 (le_refl (S₂.card ^ 2))
  have hbound2 := Nat.mul_le_mul he2 (le_refl (S₁.card ^ 2))
  refine le_trans (add_le_add hbound1 hbound2) (le_of_eq ?_)
  ring

/-- **Z4c — the adjacent degree-`4` decorated edge.**  Adjacent degree-`4` hubs `u, v`, each with
a degree-`3` neighbour (`tu` of `u`, `tv` of `v`, distinct and off the hubs), fire at every
`n ≥ 30` (`9·(4 + 4) = 72 ≤ n + 42 ⟺ n ≥ 30`).  The twins may be adjacent to each other. -/
theorem z4c_fires {n : ℕ} [Nonempty (Fin n)] (hn : 30 ≤ n)
    (G : SimpleGraph (Fin n)) (hm : G.edgeFinset.card = 2 * (n - 2))
    (h3 : ∀ w : Fin n, 3 ≤ G.degree w) (u v tu tv : Fin n)
    (huv : G.Adj u v) (hdu : G.degree u = 4) (hdv : G.degree v = 4)
    (hutu : G.Adj u tu) (hvtv : G.Adj v tv)
    (hdtu : G.degree tu = 3) (hdtv : G.degree tv = 3)
    (htuv : tu ≠ tv) (hutv : u ≠ tv) (hvtu : v ≠ tu) :
    algConn G ≤ 2 := by
  refine deco_edge_moat_fires G hm h3 u v {tu} {tv} huv ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro x hx
    rw [Finset.mem_singleton] at hx
    subst hx
    rw [G.mem_neighborFinset]; exact hutu
  · intro t ht
    rw [Finset.mem_singleton] at ht
    subst ht; exact hdtu
  · rw [Finset.card_singleton, hdu]
  · intro x hx
    rw [Finset.mem_singleton] at hx
    subst hx
    rw [G.mem_neighborFinset]; exact hvtv
  · intro t ht
    rw [Finset.mem_singleton] at ht
    subst ht; exact hdtv
  · rw [Finset.card_singleton, hdv]
  · rw [Finset.mem_singleton]; exact hutv
  · rw [Finset.mem_singleton]; exact hvtu
  · rw [Finset.disjoint_singleton]; exact htuv
  · rw [hdu, hdv]; omega

end ACMax
end

/- ---------------------------------------- Counting.MoatSharp -------------- -/
section
/-!
# The bulk-credited master-cycle moat (`master_cycle_fires_sharp`)

`master_cycle_fires` (`Counting/Moats.lean`) bounds the outer boundary `∂₂ ≤ Σ_F(deg − 1)` and
then caps `Σ_F(deg − 3)` by the *whole* excess budget `n − 8`, via `F ∪ S₁ ⊆ univ`.  That step
throws away `Σ_{S₂}(deg − 3)`, the excess sitting in the **bulk** — which, on the starved census,
is the bulk of the excess: only `n₃ = X + 8` vertices have degree `3`, so every one of the other
`|S₂| − n₃` bulk vertices spends at least `1`.

Keeping that term turns the ledger into an identity over the partition `S₁ ⊔ F ⊔ S₂ = univ` and
replaces the firing threshold

  `3·Σ_{S₁}(deg − 1) ≤ n + 8`     (i.e. `9k ≤ n + 8` on a degree-`≤ 4` cycle)

by the strictly weaker

  `4·Σ_{S₁} deg + n₃ ≤ 2n + 8 + 4k`   (i.e. `12k + n₃ ≤ 2n + 8`, i.e. `12k + X ≤ 2n`).

Since the hoarding law gives `3X + 26 ≤ n`, the new threshold dominates the old at *every* cell:
the forbidden cycle length rises from `(n+8)/9` to `(2n − X)/12`, a factor `1.2`–`1.5`.

Everything else — the slice bound, the moat cap `|F| ≤ Σ_{S₁}(deg − 2)`, the two-cluster tie — is
verbatim `master_cycle_fires`; only the ledger and the threshold change.
-/

namespace ACMax

open Finset
open scoped Classical

theorem master_cycle_fires_sharp {n : ℕ} [Nonempty (Fin n)] {k n₃ : ℕ} [NeZero k]
    (hk : 3 ≤ k)
    (G : SimpleGraph (Fin n)) (hm : G.edgeFinset.card = 2 * (n - 2))
    (h3 : ∀ v : Fin n, 3 ≤ G.degree v) (c : ZMod k → Fin n) (hcinj : Function.Injective c)
    (hadj : ∀ i : ZMod k, G.Adj (c i) (c (i + 1)))
    (hsum : ∑ i : ZMod k, G.degree (c i) ≤ 4 * k)
    (hn3 : (Finset.univ.filter (fun v : Fin n => G.degree v = 3)).card ≤ n₃)
    (hn : 4 * (∑ i : ZMod k, G.degree (c i)) + n₃ ≤ 2 * n + 8 + 4 * k) :
    algConn G ≤ 2 := by
  classical
  let : DecidableEq (Fin n) := Classical.decEq (Fin n)
  have hn8 : 8 ≤ n := by
    have hb : 3 * k ≤ ∑ i : ZMod k, G.degree (c i) := by
      calc 3 * k = ∑ _i : ZMod k, 3 := by
            rw [Finset.sum_const, Finset.card_univ, ZMod.card, smul_eq_mul, mul_comm]
        _ ≤ ∑ i : ZMod k, G.degree (c i) := Finset.sum_le_sum (fun i _ => h3 (c i))
    have hP : 2 * k ≤ ∑ i : ZMod k, (G.degree (c i) - 1) := by
      calc 2 * k = ∑ _i : ZMod k, 2 := by
            rw [Finset.sum_const, Finset.card_univ, ZMod.card, smul_eq_mul, mul_comm]
        _ ≤ ∑ i : ZMod k, (G.degree (c i) - 1) :=
            Finset.sum_le_sum (fun i _ => by have := h3 (c i); omega)
    omega
  -- the two distinct cycle neighbours of every vertex live in `S₁`
  have h2ne : (2 : ZMod k) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod k) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    have := Nat.le_of_dvd (by norm_num) h'
    omega
  set S₁ : Finset (Fin n) := Finset.image c Finset.univ with hS1def
  set F : Finset (Fin n) := (S₁.biUnion (fun x => G.neighborFinset x)) \ S₁ with hFdef
  set S₂ : Finset (Fin n) := (S₁ ∪ F)ᶜ with hS2def
  set D : ℕ := ∑ i : ZMod k, G.degree (c i) with hDdef
  have hS1card : S₁.card = k := by
    rw [hS1def, Finset.card_image_of_injective _ hcinj, Finset.card_univ, ZMod.card]
  have hS1ne : S₁.Nonempty :=
    ⟨c 0, Finset.mem_image.mpr ⟨0, Finset.mem_univ 0, rfl⟩⟩
  have hDS1 : ∑ x ∈ S₁, G.degree x = D := by
    rw [hDdef, hS1def, Finset.sum_image (fun x _ y _ h => hcinj h)]
  -- per-vertex slice bound: each cycle vertex has `≥ 2` neighbours inside `S₁`
  have hsliceIdx : ∀ i : ZMod k,
      (G.neighborFinset (c i) \ S₁).card ≤ G.degree (c i) - 2 := by
    intro i
    have hib : (i - 1) + 1 = i := by ring
    have hadjb : G.Adj (c i) (c (i - 1)) := by
      have hh := hadj (i - 1)
      rw [hib] at hh
      exact hh.symm
    have hkey : (i : ZMod k) + 1 ≠ i - 1 := by
      intro heq
      apply h2ne
      have h2 : (2 : ZMod k) = (i + 1) - (i - 1) := by ring
      rw [heq, sub_self] at h2
      exact h2
    have hdist : c (i + 1) ≠ c (i - 1) := fun heq => hkey (hcinj heq)
    have h2le : 2 ≤ (G.neighborFinset (c i) ∩ S₁).card := by
      have hsub : ({c (i + 1), c (i - 1)} : Finset (Fin n))
          ⊆ G.neighborFinset (c i) ∩ S₁ := by
        intro x hx
        rw [Finset.mem_insert, Finset.mem_singleton] at hx
        rw [Finset.mem_inter]
        rcases hx with rfl | rfl
        · exact ⟨(G.mem_neighborFinset _ _).mpr (hadj i),
            Finset.mem_image.mpr ⟨i + 1, Finset.mem_univ _, rfl⟩⟩
        · exact ⟨(G.mem_neighborFinset _ _).mpr hadjb,
            Finset.mem_image.mpr ⟨i - 1, Finset.mem_univ _, rfl⟩⟩
      calc 2 = ({c (i + 1), c (i - 1)} : Finset (Fin n)).card := by
            rw [Finset.card_pair hdist]
        _ ≤ _ := Finset.card_le_card hsub
    have hcard : (G.neighborFinset (c i) ∩ S₁).card + (G.neighborFinset (c i) \ S₁).card
        = G.degree (c i) := by
      rw [Finset.card_inter_add_card_sdiff, G.card_neighborFinset_eq_degree]
    omega
  have hslice : ∀ x ∈ S₁, (G.neighborFinset x \ S₁).card ≤ G.degree x - 2 := by
    intro x hx
    rw [hS1def, Finset.mem_image] at hx
    obtain ⟨i, _, rfl⟩ := hx
    exact hsliceIdx i
  -- the disjointness / cardinality bookkeeping (mirrors `star_moat_fires`)
  have hdisjS1F : Disjoint S₁ F := by
    rw [Finset.disjoint_left]
    intro a ha haF
    rw [hFdef, Finset.mem_sdiff] at haF
    exact haF.2 ha
  have hS2card : S₂.card = n - (S₁.card + F.card) := by
    rw [hS2def, Finset.card_compl, Fintype.card_fin,
      Finset.card_union_of_disjoint hdisjS1F]
  have hkfn : S₁.card + F.card ≤ n := by
    have h : (S₁ ∪ F).card ≤ Fintype.card (Fin n) := Finset.card_le_univ _
    rw [Fintype.card_fin, Finset.card_union_of_disjoint hdisjS1F] at h
    exact h
  -- the counting helper: an ordered adjacency block splits into neighbourhood slices
  have hcnt : ∀ (A C : Finset (Fin n)),
      ((A ×ˢ C).filter (fun q => G.Adj q.1 q.2)).card
        = ∑ a ∈ A, (G.neighborFinset a ∩ C).card := by
    intro A C
    rw [Finset.card_filter, Finset.sum_product]
    refine Finset.sum_congr rfl fun a _ => ?_
    have hset : G.neighborFinset a ∩ C = C.filter (fun v => G.Adj a v) := by
      ext v
      simp only [Finset.mem_inter, Finset.mem_filter, SimpleGraph.mem_neighborFinset]
      exact and_comm
    rw [hset, Finset.card_filter]
  -- the transpose helper (adjacency is symmetric)
  have htrans : ∀ (A C : Finset (Fin n)),
      ((A ×ˢ C).filter (fun q => G.Adj q.1 q.2)).card
        = ((C ×ˢ A).filter (fun q => G.Adj q.1 q.2)).card := by
    intro A C
    refine Finset.card_bij (fun q _ => (q.2, q.1)) ?_ ?_ ?_
    · intro q hq
      rw [Finset.mem_filter, Finset.mem_product] at hq ⊢
      exact ⟨⟨hq.1.2, hq.1.1⟩, G.adj_symm hq.2⟩
    · intro q _ r _ hqr
      exact Prod.ext (congrArg Prod.snd hqr) (congrArg Prod.fst hqr)
    · intro q hq
      refine ⟨(q.2, q.1), ?_, rfl⟩
      rw [Finset.mem_filter, Finset.mem_product] at hq ⊢
      exact ⟨⟨hq.1.2, hq.1.1⟩, G.adj_symm hq.2⟩
  -- `Σ_{S₁}(deg − 2) + 2·|S₁| = D` and `Σ_{S₁}(deg − 3) + 3·|S₁| = D`
  have keyB : (∑ x ∈ S₁, (G.degree x - 2)) + 2 * S₁.card = D := by
    have h1 : 2 * S₁.card = ∑ _x ∈ S₁, 2 := by
      rw [Finset.sum_const, smul_eq_mul, mul_comm]
    rw [h1, ← Finset.sum_add_distrib, ← hDS1]
    exact Finset.sum_congr rfl (fun x _ => Nat.sub_add_cancel (by have := h3 x; omega))
  have keyX : (∑ x ∈ S₁, (G.degree x - 3)) + 3 * S₁.card = D := by
    have h1 : 3 * S₁.card = ∑ _x ∈ S₁, 3 := by
      rw [Finset.sum_const, smul_eq_mul, mul_comm]
    rw [h1, ← Finset.sum_add_distrib, ← hDS1]
    exact Finset.sum_congr rfl (fun x _ => Nat.sub_add_cancel (h3 x))
  have keyP : (∑ i : ZMod k, (G.degree (c i) - 1)) + k = D := by
    have hstep : ∑ i : ZMod k, ((G.degree (c i) - 1) + 1) = D := by
      rw [hDdef]
      exact Finset.sum_congr rfl (fun i _ => Nat.sub_add_cancel (by have := h3 (c i); omega))
    rw [Finset.sum_add_distrib] at hstep
    simp only [Finset.sum_const, Finset.card_univ, ZMod.card, smul_eq_mul, mul_one] at hstep
    exact hstep
  -- the moat is capped by the same slice budget
  have hFB : F.card ≤ ∑ x ∈ S₁, (G.degree x - 2) := by
    have hFsub2 : F ⊆ S₁.biUnion (fun x => G.neighborFinset x \ S₁) := by
      intro y hy
      rw [hFdef, Finset.mem_sdiff] at hy
      obtain ⟨hyNS, hyS1⟩ := hy
      rw [Finset.mem_biUnion] at hyNS ⊢
      obtain ⟨x, hxS1, hyx⟩ := hyNS
      exact ⟨x, hxS1, Finset.mem_sdiff.mpr ⟨hyx, hyS1⟩⟩
    calc F.card
        ≤ (S₁.biUnion (fun x => G.neighborFinset x \ S₁)).card := Finset.card_le_card hFsub2
      _ ≤ ∑ x ∈ S₁, (G.neighborFinset x \ S₁).card := Finset.card_biUnion_le
      _ ≤ ∑ x ∈ S₁, (G.degree x - 2) := Finset.sum_le_sum hslice
  have keyF : F.card + 2 * S₁.card ≤ D := by
    have := keyB
    omega
  -- the **full** excess ledger: `S₁ ⊔ F ⊔ S₂ = univ`, so the bulk excess is kept, not discarded
  have hexc3 : (∑ w ∈ F, (G.degree w - 3)) + (∑ x ∈ S₁, (G.degree x - 3))
      + (∑ v ∈ S₂, (G.degree v - 3)) = n - 8 := by
    have hunion : (∑ w ∈ F, (G.degree w - 3)) + (∑ x ∈ S₁, (G.degree x - 3))
        = ∑ w ∈ (F ∪ S₁), (G.degree w - 3) := (Finset.sum_union hdisjS1F.symm).symm
    have hcompl : S₂ = (F ∪ S₁)ᶜ := by rw [hS2def, Finset.union_comm]
    rw [hunion, hcompl, Finset.sum_add_sum_compl]
    exact total_excess_eq hn8 G hm h3
  -- the bulk excess is at least `|S₂| − n₃`: every non-degree-`3` bulk vertex spends `≥ 1`
  have hE2 : S₂.card ≤ (∑ v ∈ S₂, (G.degree v - 3)) + n₃ := by
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := S₂) (p := fun v => G.degree v = 3)
    have hle : (S₂.filter (fun v => G.degree v = 3)).card ≤ n₃ := by
      refine le_trans (Finset.card_le_card ?_) hn3
      intro v hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
      exact hv.2
    have hge : (S₂.filter (fun v => ¬ G.degree v = 3)).card
        ≤ ∑ v ∈ S₂, (G.degree v - 3) := by
      calc (S₂.filter (fun v => ¬ G.degree v = 3)).card
          = ∑ _v ∈ S₂.filter (fun v => ¬ G.degree v = 3), 1 := by
            rw [Finset.sum_const, smul_eq_mul, mul_one]
        _ ≤ ∑ v ∈ S₂.filter (fun v => ¬ G.degree v = 3), (G.degree v - 3) := by
            refine Finset.sum_le_sum fun v hv => ?_
            rw [Finset.mem_filter] at hv
            have := h3 v
            omega
        _ ≤ ∑ v ∈ S₂, (G.degree v - 3) :=
            Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    omega
  have hS2ne : S₂.Nonempty := by
    rw [← Finset.card_pos, hS2card]
    have := keyF; have := hsum; have := keyX; have := keyP; have := hn; have := hS1card
    omega
  have hdisj : Disjoint S₁ S₂ := by
    rw [Finset.disjoint_left]
    intro a ha1 ha2
    rw [hS2def, Finset.mem_compl] at ha2
    exact ha2 (Finset.mem_union_left F ha1)
  have hnc : ∀ a ∈ S₁, ∀ v ∈ S₂, ¬G.Adj a v := by
    intro a ha v hv hadjav
    rw [hS2def, Finset.mem_compl] at hv
    have hvnotS1 : v ∉ S₁ := fun hh => hv (Finset.mem_union_left F hh)
    have hvnotF : v ∉ F := fun hh => hv (Finset.mem_union_right S₁ hh)
    apply hvnotF
    rw [hFdef, Finset.mem_sdiff]
    refine ⟨?_, hvnotS1⟩
    rw [Finset.mem_biUnion]
    exact ⟨a, ha, (G.mem_neighborFinset a v).mpr hadjav⟩
  have hFeq : (S₁ ∪ S₂)ᶜ = F := by
    ext v
    constructor
    · intro hv
      rw [Finset.mem_compl, Finset.mem_union, not_or] at hv
      obtain ⟨hvS1, hvS2⟩ := hv
      rw [hS2def, Finset.mem_compl, not_not, Finset.mem_union] at hvS2
      rcases hvS2 with hh | hh
      · exact absurd hh hvS1
      · exact hh
    · intro hv
      rw [Finset.mem_compl, Finset.mem_union, not_or]
      exact ⟨Finset.disjoint_right.mp hdisjS1F hv,
        by rw [hS2def, Finset.mem_compl, not_not]; exact Finset.mem_union_right S₁ hv⟩
  -- ∂₁ ≤ 2·|S₁|
  have he1 : ((S₁ ×ˢ F).filter (fun q => G.Adj q.1 q.2)).card ≤ 2 * S₁.card := by
    rw [hcnt S₁ F]
    have hterm : ∀ a ∈ S₁, (G.neighborFinset a ∩ F).card ≤ G.degree a - 2 := by
      intro a ha
      have hsub : G.neighborFinset a ∩ F ⊆ G.neighborFinset a \ S₁ := by
        intro x hx
        rw [Finset.mem_inter] at hx
        rw [Finset.mem_sdiff]
        refine ⟨hx.1, ?_⟩
        have hxF := hx.2
        rw [hFdef, Finset.mem_sdiff] at hxF
        exact hxF.2
      exact le_trans (Finset.card_le_card hsub) (hslice a ha)
    calc ∑ a ∈ S₁, (G.neighborFinset a ∩ F).card
        ≤ ∑ a ∈ S₁, (G.degree a - 2) := Finset.sum_le_sum hterm
      _ ≤ 2 * S₁.card := by
          have := keyB; have := hsum; have := hS1card; omega
  -- ∂₂ ≤ 2·|S₂|
  have he2 : ((S₂ ×ˢ F).filter (fun q => G.Adj q.1 q.2)).card ≤ 2 * S₂.card := by
    rw [htrans S₂ F, hcnt F S₂]
    have hbound : ∀ w ∈ F, (G.neighborFinset w ∩ S₂).card ≤ G.degree w - 1 := by
      intro w hw
      obtain ⟨a, haS1, haw⟩ : ∃ a ∈ S₁, G.Adj a w := by
        have hwF := hw
        rw [hFdef, Finset.mem_sdiff, Finset.mem_biUnion] at hwF
        obtain ⟨⟨a, haS1, hwa⟩, _⟩ := hwF
        exact ⟨a, haS1, (G.mem_neighborFinset a w).mp hwa⟩
      have haNw : a ∈ G.neighborFinset w := (G.mem_neighborFinset w a).mpr haw.symm
      have haS2 : a ∉ S₂ := by
        rw [hS2def, Finset.mem_compl, not_not]
        exact Finset.mem_union_left F haS1
      have hsub : G.neighborFinset w ∩ S₂ ⊆ (G.neighborFinset w).erase a := by
        intro x hx
        rw [Finset.mem_inter] at hx
        rw [Finset.mem_erase]
        refine ⟨?_, hx.1⟩
        rintro rfl
        exact haS2 hx.2
      calc (G.neighborFinset w ∩ S₂).card
          ≤ ((G.neighborFinset w).erase a).card := Finset.card_le_card hsub
        _ = G.degree w - 1 := by
            rw [Finset.card_erase_of_mem haNw, G.card_neighborFinset_eq_degree]
    have hpt : ∀ w ∈ F, G.degree w - 1 = (G.degree w - 3) + 2 := by
      intro w _
      have := h3 w
      omega
    calc ∑ w ∈ F, (G.neighborFinset w ∩ S₂).card
        ≤ ∑ w ∈ F, (G.degree w - 1) := Finset.sum_le_sum hbound
      _ = ∑ w ∈ F, (G.degree w - 3) + F.card * 2 := by
          rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, Finset.sum_const,
            smul_eq_mul]
      _ ≤ 2 * S₂.card := by
          have := hexc3; have := hE2; have := keyX; have := hsum; have := hn
          have := keyF; have := hS2card; have := hkfn; have := hS1card
          omega
  -- assemble the two-cluster law at the tie
  refine algConn_le_two_of_two_clusters G S₁ S₂ hS1ne hS2ne hdisj hnc ?_
  rw [hFeq]
  have hbound1 := Nat.mul_le_mul he1 (le_refl (S₂.card ^ 2))
  have hbound2 := Nat.mul_le_mul he2 (le_refl (S₁.card ^ 2))
  refine le_trans (add_le_add hbound1 hbound2) (le_of_eq ?_)
  ring

/-- **The degree-`3` census identity** `n₃ = X + 8`.  From the excess ledger
`Σ_v (deg v − 3) = n − 8`: a degree-`3` vertex spends `0`, and every other vertex spends
`(deg − 4) + 1`, so `n − 8 = X + (n − n₃)`. -/
theorem n3_eq_excess_add_eight {n : ℕ} (hn : 8 ≤ n) (G : SimpleGraph (Fin n))
    (hm : G.edgeFinset.card = 2 * (n - 2)) (h3 : ∀ v : Fin n, 3 ≤ G.degree v) :
    (Finset.univ.filter (fun v : Fin n => G.degree v = 3)).card = excessX n G + 8 := by
  classical
  have htot := total_excess_eq hn G hm h3
  set A := Finset.univ.filter (fun v : Fin n => G.degree v = 3) with hA
  set B := Finset.univ.filter (fun v : Fin n => ¬ G.degree v = 3) with hB
  have hcard : A.card + B.card = n := by
    rw [hA, hB, Finset.card_filter_add_card_filter_not, Finset.card_univ, Fintype.card_fin]
  have hsplit : (∑ v ∈ A, (G.degree v - 3)) + (∑ v ∈ B, (G.degree v - 3)) = n - 8 := by
    rw [hA, hB, Finset.sum_filter_add_sum_filter_not]; exact htot
  have hA0 : (∑ v ∈ A, (G.degree v - 3)) = 0 := by
    refine Finset.sum_eq_zero fun v hv => ?_
    rw [hA, Finset.mem_filter] at hv
    omega
  have hBval : (∑ v ∈ B, (G.degree v - 3)) = (∑ v ∈ B, (G.degree v - 4)) + B.card := by
    have hpt : ∀ v ∈ B, G.degree v - 3 = (G.degree v - 4) + 1 := by
      intro v hv
      rw [hB, Finset.mem_filter] at hv
      have := h3 v
      omega
    rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one]
  have hexc : (∑ v ∈ B, (G.degree v - 4)) = excessX n G := by
    unfold excessX
    refine (Finset.sum_subset ?_ ?_).symm
    · intro v hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
      simp only [hB, Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    · intro v hv hv2
      simp only [hB, Finset.mem_filter, Finset.mem_univ, true_and] at hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv2
      have := h3 v
      omega
  omega

/-- **The sharpened tier-9 short-cycle kill.**  A cycle of degree-`≤ 4` vertices fires the
two-cluster moat whenever `12·k + X ≤ 2n` — against `9·k ≤ n + 8` for `v9_short_cycle_fires`.
Since the hoarding law gives `3X + 26 ≤ n`, the new threshold is strictly weaker at every cell:
the forbidden length rises from `(n+8)/9` to `(2n − X)/12`. -/
theorem v9_short_cycle_fires_sharp {n : ℕ} [Nonempty (Fin n)] {k : ℕ} [NeZero k] (hk : 3 ≤ k)
    (G : SimpleGraph (Fin n)) (hm : G.edgeFinset.card = 2 * (n - 2))
    (h3 : ∀ v : Fin n, 3 ≤ G.degree v) (c : ZMod k → Fin n)
    (hcinj : Function.Injective c) (hadj : ∀ i : ZMod k, G.Adj (c i) (c (i + 1)))
    (hdeg : ∀ i : ZMod k, G.degree (c i) ≤ 4) (hn8 : 8 ≤ n)
    (hn : 12 * k + excessX n G ≤ 2 * n) :
    algConn G ≤ 2 := by
  have hDle : ∑ i : ZMod k, G.degree (c i) ≤ 4 * k := by
    calc ∑ i : ZMod k, G.degree (c i)
        ≤ ∑ _i : ZMod k, 4 := Finset.sum_le_sum (fun i _ => hdeg i)
      _ = 4 * k := by
          rw [Finset.sum_const, Finset.card_univ, ZMod.card, smul_eq_mul, mul_comm]
  refine master_cycle_fires_sharp (n₃ := excessX n G + 8) hk G hm h3 c hcinj hadj hDle
    (le_of_eq (n3_eq_excess_add_eight hn8 G hm h3)) ?_
  omega

end ACMax
end


/-! ########################################################################################
   PART VI --- The engine: a ball double count

   The global half, and pure counting: a set of large girth carrying edge excess `t` needs
   `|S|(1+2r) + t(3r^2-r) <= |S|^2`. No reference to `algConn` appears here.
   ######################################################################################## -/

/- ---------------------------------------- Counting.SqrtGirth -------------- -/
section
/-!
# The SQRT girth cluster

A self-contained girth development: from an *edge excess* `t` on a graph one
extracts a short cycle, quantified by the SQRT bound `(g − 5)² ≤ 2|S|²/t`. The
engine is a BFS ball-excess count in a graph with no cycle of length `≤ 2r + 1`.

## Main results

* `exists_isCycle_of_excess`, `acyclic_card_edge_le`,
  `induced_pairs_eq_two_mul_edges` — from `|S|` edges inside `S`, extract a cycle
  whose support lies in `S` (the induced subgraph is not acyclic).
* `cycle_walk_to_zmod` — the `Walk.IsCycle → (c : ZMod k → Fin n)` conversion into
  the cyclic-map form the `master_cycle_fires` firing surface expects.
* `level_no_internal_edge`, `level_unique_parent`, `level_children_count`,
  `level_card_growth` — the BFS-level growth rows exposing the tree-like ball
  structure up to radius `r` (girth-only, no min-degree hypothesis).
* `ball_weighted_lower` — the quadratic degree-weighted ball lower bound
  `1 + 2r + Σ_{i<r}(r − i)·ε_i(x) ≤ |B(x, r)|` (an equality under connectivity,
  `ε_i` = level excess).
* `sum_level_excess_swap` and the SQRT double count
  `|V|·(1 + 2r) + 2·t·r² ≤ |V|²`, together with the 2-core extraction
  `two_core_of_excess` (`degWithin`, `edgeSumWithin`).
-/

namespace ACMax

open SimpleGraph

variable {V : Type*}

/-- **Ordered adjacent pairs count twice the induced edges.**  The number of ordered pairs
`(x, y)` with `x, y ∈ S` and `G.Adj x y` equals `2 * (G.induce ↑S).edgeFinset.card`. -/
theorem induced_pairs_eq_two_mul_edges [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (S : Finset V) :
    ((S ×ˢ S).filter (fun q => G.Adj q.1 q.2)).card
      = 2 * (G.induce (↑S : Set V)).edgeFinset.card := by
  have hbij : (Finset.univ : Finset (G.induce (↑S : Set V)).Dart).card
      = ((S ×ˢ S).filter (fun q => G.Adj q.1 q.2)).card := by
    apply Finset.card_bij (fun d _ => ((d.fst : V), (d.snd : V)))
    · intro d _
      rw [Finset.mem_filter, Finset.mem_product]
      exact ⟨⟨Finset.mem_coe.mp d.fst.2, Finset.mem_coe.mp d.snd.2⟩, d.adj⟩
    · intro d₁ _ d₂ _ heq
      rw [Prod.mk.injEq] at heq
      exact Dart.ext _ _ (Prod.ext (Subtype.ext heq.1) (Subtype.ext heq.2))
    · intro q hq
      rw [Finset.mem_filter, Finset.mem_product] at hq
      obtain ⟨⟨hq1, hq2⟩, hadj⟩ := hq
      exact ⟨⟨(⟨q.1, Finset.mem_coe.mpr hq1⟩, ⟨q.2, Finset.mem_coe.mpr hq2⟩), hadj⟩,
        Finset.mem_univ _, rfl⟩
  rw [← hbij, Finset.card_univ, dart_card_eq_twice_card_edges]

end ACMax


/-! ## The `ZMod`-cycle conversion

`cycle_walk_to_zmod`: from a cycle walk `w` whose support lies inside `S`, produce
`k = w.length ≥ 3` and an injective `c : ZMod k → Fin n` with cyclic adjacency
`c i ~ c (i+1)` and `c i ∈ S` — the cyclic-map form the `master_cycle_fires` firing
surface expects (`c i = w.getVert i.val`, injectivity via `IsCycle.isPath_dropLast`,
cyclic adjacency via `adj_getVert_succ`). -/

namespace ACMax

open SimpleGraph

/-- **The `Walk.IsCycle → ZMod k` conversion.**  A cycle walk `w` in `G` of length `k` whose
support sits inside `S` yields `3 ≤ k` and an injective cyclic map `c : ZMod k → Fin n`
(`c i ~ c (i+1)`, `c i ∈ S`) — the existential shape demanded by `GirthExcessBound`.  Reusable
for any girth discharge that produces a bounded-length cycle walk. -/
theorem cycle_walk_to_zmod {n : ℕ} {G : SimpleGraph (Fin n)} {v : Fin n} {w : G.Walk v v}
    (hcyc : w.IsCycle) {S : Finset (Fin n)} (hsupp : ∀ x ∈ w.support, x ∈ S) :
    3 ≤ w.length ∧ ∃ c : ZMod w.length → Fin n, Function.Injective c ∧
      (∀ i : ZMod w.length, G.Adj (c i) (c (i + 1))) ∧ (∀ i : ZMod w.length, c i ∈ S) := by
  have hlen3 : 3 ≤ w.length := hcyc.three_le_length
  have : NeZero w.length := ⟨by omega⟩
  -- `getVert` is injective on `{0, …, k−1}` because the cycle minus its repeated endpoint is a path
  have hinj : ∀ a b : ℕ, a < w.length → b < w.length → w.getVert a = w.getVert b → a = b := by
    intro a b ha hb hab
    have hpath : w.dropLast.IsPath := hcyc.isPath_dropLast
    have hla : w.dropLast.length = w.length - 1 := w.length_dropLast
    have hga : w.dropLast.getVert a = w.getVert a := by
      show (w.take (w.length - 1)).getVert a = w.getVert a
      rw [Walk.take_getVert, inf_eq_right.mpr (show a ≤ w.length - 1 by omega)]
    have hgb : w.dropLast.getVert b = w.getVert b := by
      show (w.take (w.length - 1)).getVert b = w.getVert b
      rw [Walk.take_getVert, inf_eq_right.mpr (show b ≤ w.length - 1 by omega)]
    have ha' : a ∈ {i | i ≤ w.dropLast.length} := by show a ≤ w.dropLast.length; omega
    have hb' : b ∈ {i | i ≤ w.dropLast.length} := by show b ≤ w.dropLast.length; omega
    exact hpath.getVert_injOn ha' hb' (by rw [hga, hgb]; exact hab)
  refine ⟨hlen3, fun i => w.getVert i.val, ?_, ?_, ?_⟩
  · intro i j hij
    have hij' : w.getVert i.val = w.getVert j.val := hij
    exact ZMod.val_injective w.length (hinj i.val j.val (ZMod.val_lt i) (ZMod.val_lt j) hij')
  · intro i
    have hmlt : i.val < w.length := ZMod.val_lt i
    have hval : ((i.val + 1 : ℕ) : ZMod w.length) = i + 1 := by
      rw [Nat.cast_add, Nat.cast_one, ZMod.natCast_zmod_val]
    have hv1 : (i + 1).val = (i.val + 1) % w.length := by rw [← hval, ZMod.val_natCast]
    show G.Adj (w.getVert i.val) (w.getVert (i + 1).val)
    rw [hv1]
    by_cases hc : i.val + 1 < w.length
    · rw [Nat.mod_eq_of_lt hc]
      exact w.adj_getVert_succ hmlt
    · have heq : i.val + 1 = w.length := by omega
      rw [heq, Nat.mod_self, w.getVert_zero]
      have hadj := w.adj_getVert_succ hmlt
      rw [heq, w.getVert_length] at hadj
      exact hadj
  · intro i
    exact hsupp _ (w.getVert_mem_support i.val)

end ACMax


/-! ## BFS-level growth rows

The BFS levels `L_i(x) = {v | dist x v = i}` in a graph with no cycle of length
`≤ 2r + 1` are tree-like: no edge inside a level (`level_no_internal_edge`), a
level-`(i+1)` vertex has a unique parent (`level_unique_parent`), a level-`i`
vertex sends `deg v − 1` edges up (`level_children_count`), and the levels grow by
`|L_{i+1}| = Σ_{v∈L_i}(deg v − 1)` (`level_card_growth`). All four are girth-only
(no min-degree hypothesis). -/

namespace ACMax

open SimpleGraph Finset

/-- The distance from `x` to a vertex on a walk `x → z` is bounded by the walk's length. -/
theorem dist_le_of_mem_support {V : Type*} (G : SimpleGraph V) {x z : V} (g : G.Walk x z) {w : V}
    (hw : w ∈ g.support) : G.dist x w ≤ g.length := by
  classical
  exact (SimpleGraph.dist_le (g.takeUntil w hw)).trans (g.length_takeUntil_le_length hw)

/-- Two distinct paths with the same endpoints whose total length is `≤ 2r + 1` are impossible
under the girth hypothesis: they close a cycle of length `≤ 2r + 1`. -/
theorem no_short_cycle_of_paths {V : Type*} (G : SimpleGraph V) {r : ℕ}
    (hg : ∀ (v : V) (c : G.Walk v v), c.IsCycle → 2 * r + 1 < c.length) {x y : V}
    {P Q : G.Walk x y} (hP : P.IsPath) (hQ : Q.IsPath) (hne : P ≠ Q)
    (hlen : P.length + Q.length ≤ 2 * r + 1) : False := by
  classical
  obtain ⟨u, -, -, c, hc, hcl⟩ := hP.exists_isCycle_length_le_add_of_ne hQ hne
  have h1 := hg u c hc
  omega

/-- On a geodesic `g : x → y`, a vertex `z ≠ y` at the same distance from `x` as `y` cannot lie on
`g` (the geodesic reaches distance `dist x y` only at its endpoint). -/
theorem notMem_geodesic_of_dist_eq {V : Type*} (G : SimpleGraph V) {x y : V} (g : G.Walk x y)
    (hglen : g.length = G.dist x y) {z : V} (hdist : G.dist x z = G.dist x y) (hne : z ≠ y) :
    z ∉ g.support := by
  classical
  intro hz
  have hAB : (g.takeUntil z hz).append (g.dropUntil z hz) = g := g.take_spec hz
  have hlen : (g.takeUntil z hz).length + (g.dropUntil z hz).length = g.length := by
    rw [← Walk.length_append, hAB]
  have hxz : G.dist x z ≤ (g.takeUntil z hz).length := SimpleGraph.dist_le _
  have hzy : G.dist z y ≤ (g.dropUntil z hz).length := SimpleGraph.dist_le _
  have hrzy : G.Reachable z y := (g.dropUntil z hz).reachable
  have hdzy : G.dist z y = 0 := by omega
  exact hne (hrzy.dist_eq_zero_iff.mp hdzy)

/-- **No same-level edge.**  Under `hg` (no cycle of length `≤ 2r + 1`), no two vertices at the same
BFS level `L_i(x)` with `1 ≤ i ≤ r` are adjacent — the edge plus two `dist`-`i` geodesics would
close a cycle of length `≤ 2i + 1 ≤ 2r + 1`. -/
theorem level_no_internal_edge {V : Type*} (G : SimpleGraph V) {r : ℕ}
    (hg : ∀ (v : V) (c : G.Walk v v), c.IsCycle → 2 * r + 1 < c.length) (x : V) {i : ℕ}
    (hi1 : 1 ≤ i) (hir : i ≤ r) {v w : V} (hv : G.dist x v = i) (hw : G.dist x w = i) :
    ¬ G.Adj v w := by
  intro hadj
  have hrxw : G.Reachable x w := Reachable.of_dist_ne_zero (by rw [hw]; omega)
  obtain ⟨gw, hgwP, hgwlen⟩ := hrxw.exists_path_of_dist
  have hrxv : G.Reachable x v := Reachable.of_dist_ne_zero (by rw [hv]; omega)
  obtain ⟨gv, hgvP, hgvlen⟩ := hrxv.exists_path_of_dist
  have hvw : v ≠ w := hadj.ne
  have hvnotin : v ∉ gw.support :=
    notMem_geodesic_of_dist_eq G gw hgwlen (z := v) (by rw [hv, hw]) hvw
  have hadjwv : G.Adj w v := hadj.symm
  have hP1 : (gw.concat hadjwv).IsPath := hgwP.concat hvnotin hadjwv
  have hne : gw.concat hadjwv ≠ gv := by
    intro heq
    have h1 : (gw.concat hadjwv).length = i + 1 := by rw [Walk.length_concat, hgwlen, hw]
    rw [heq, hgvlen, hv] at h1
    omega
  refine no_short_cycle_of_paths G hg hP1 hgvP hne ?_
  rw [Walk.length_concat, hgwlen, hgvlen, hv, hw]
  omega

/-- **Unique parent.**  Under `hg`, a level-`(i+1)` vertex `v` (`i + 1 ≤ r`) has exactly one
neighbour at level `i`: `((N v) ∩ L_i).card = 1`.  Existence is the penultimate vertex of a
geodesic `x → v`; uniqueness is a short cycle from two length-`(i+1)` paths to `v`. -/
theorem level_unique_parent {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {r : ℕ} (hg : ∀ (v : V) (c : G.Walk v v), c.IsCycle → 2 * r + 1 < c.length) (x : V) {i : ℕ}
    (hir : i + 1 ≤ r) {v : V} (hv : G.dist x v = i + 1) :
    ((G.neighborFinset v).filter (fun w => G.dist x w = i)).card = 1 := by
  classical
  refine le_antisymm ?_ ?_
  · rw [Finset.card_le_one]
    intro p1 hp1 p2 hp2
    by_contra hp1p2
    simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset] at hp1 hp2
    obtain ⟨hadj1, hd1⟩ := hp1
    obtain ⟨hadj2, hd2⟩ := hp2
    have hrxv : G.Reachable x v := Reachable.of_dist_ne_zero (by rw [hv]; omega)
    have hr1 : G.Reachable x p1 := hrxv.trans hadj1.reachable
    have hr2 : G.Reachable x p2 := hrxv.trans hadj2.reachable
    obtain ⟨g1, hg1P, hg1len⟩ := hr1.exists_path_of_dist
    obtain ⟨g2, hg2P, hg2len⟩ := hr2.exists_path_of_dist
    have hvn1 : v ∉ g1.support := by
      intro hmem
      have hle := dist_le_of_mem_support G g1 hmem
      rw [hg1len, hd1, hv] at hle; omega
    have hvn2 : v ∉ g2.support := by
      intro hmem
      have hle := dist_le_of_mem_support G g2 hmem
      rw [hg2len, hd2, hv] at hle; omega
    have hadj1v : G.Adj p1 v := hadj1.symm
    have hadj2v : G.Adj p2 v := hadj2.symm
    have hP1 : (g1.concat hadj1v).IsPath := hg1P.concat hvn1 hadj1v
    have hP2 : (g2.concat hadj2v).IsPath := hg2P.concat hvn2 hadj2v
    have hne : g1.concat hadj1v ≠ g2.concat hadj2v := by
      intro heq
      apply hp1p2
      have e1 : (g1.concat hadj1v).penultimate = p1 := Walk.penultimate_concat g1 hadj1v
      have e2 : (g2.concat hadj2v).penultimate = p2 := Walk.penultimate_concat g2 hadj2v
      rw [← e1, ← e2, heq]
    refine no_short_cycle_of_paths G hg hP1 hP2 hne ?_
    rw [Walk.length_concat, Walk.length_concat, hg1len, hg2len, hd1, hd2]
    omega
  · have hrxv : G.Reachable x v := Reachable.of_dist_ne_zero (by rw [hv]; omega)
    obtain ⟨g, hgP, hglen⟩ := hrxv.exists_path_of_dist
    have hi_lt : i < g.length := by rw [hglen, hv]; omega
    have hadj_uv : G.Adj (g.getVert i) v := by
      have h := g.adj_getVert_succ hi_lt
      rwa [show i + 1 = g.length by rw [hglen, hv], g.getVert_length] at h
    have hle : G.dist x (g.getVert i) ≤ i := by
      have hw := SimpleGraph.dist_le (g.take i)
      rw [Walk.take_length, show i ⊓ g.length = i by rw [hglen, hv]; omega] at hw
      exact hw
    have hge : i ≤ G.dist x (g.getVert i) := by
      have hru : G.Reachable x (g.getVert i) := (g.take i).reachable
      have htri := hru.dist_triangle_left v
      rw [hv, SimpleGraph.dist_eq_one_iff_adj.mpr hadj_uv] at htri
      omega
    refine Finset.one_le_card.mpr ⟨g.getVert i, ?_⟩
    rw [Finset.mem_filter, SimpleGraph.mem_neighborFinset]
    exact ⟨hadj_uv.symm, le_antisymm hle hge⟩

/-- **Children count.**  Under `hg`, a level-`i` vertex `v` (`1 ≤ i ≤ r`) has exactly `deg v − 1`
neighbours at level `i + 1`.  Its neighbourhood splits into the unique parent (level `i − 1`), no
same-level neighbour, and the remaining `deg v − 1` children at level `i + 1`. -/
theorem level_children_count {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {r : ℕ} (hg : ∀ (v : V) (c : G.Walk v v), c.IsCycle → 2 * r + 1 < c.length) (x : V) {i : ℕ}
    (hi1 : 1 ≤ i) (hir : i ≤ r) {v : V} (hv : G.dist x v = i) :
    ((G.neighborFinset v).filter (fun w => G.dist x w = i + 1)).card = G.degree v - 1 := by
  classical
  have hrxv : G.Reachable x v := Reachable.of_dist_ne_zero (by rw [hv]; omega)
  have hbound : ∀ w ∈ G.neighborFinset v, G.dist x w = i - 1 ∨ G.dist x w = i + 1 := by
    intro w hw
    have hadj : G.Adj v w := (G.mem_neighborFinset v w).mp hw
    have hrxw : G.Reachable x w := hrxv.trans hadj.reachable
    have hvw1 : G.dist v w = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hadj
    have hwv1 : G.dist w v = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hadj.symm
    have hup : G.dist x w ≤ i + 1 := by
      have htri := hrxv.dist_triangle_left w; rw [hv, hvw1] at htri; omega
    have hlow : i ≤ G.dist x w + 1 := by
      have htri := hrxw.dist_triangle_left v; rw [hv, hwv1] at htri; omega
    have hne : G.dist x w ≠ i := fun heq =>
      level_no_internal_edge G hg x hi1 hir hv heq hadj
    omega
  have hpart : (G.neighborFinset v).filter (fun w => ¬ G.dist x w = i + 1)
      = (G.neighborFinset v).filter (fun w => G.dist x w = i - 1) := by
    ext w
    simp only [Finset.mem_filter, and_congr_right_iff]
    intro hw
    have := hbound w hw
    omega
  have hpar : ((G.neighborFinset v).filter (fun w => G.dist x w = i - 1)).card = 1 := by
    have hv' : G.dist x v = (i - 1) + 1 := by rw [Nat.sub_add_cancel hi1]; exact hv
    have hir' : (i - 1) + 1 ≤ r := by rw [Nat.sub_add_cancel hi1]; exact hir
    exact level_unique_parent G hg x hir' hv'
  have hsplit := Finset.card_filter_add_card_filter_not (s := G.neighborFinset v)
    (fun w => G.dist x w = i + 1)
  simp only [hpart, hpar, G.card_neighborFinset_eq_degree] at hsplit
  omega

/-- **Level identity.**  Under `hg`, for `1 ≤ i` and `i + 1 ≤ r` the BFS level `L_{i+1}(x)` has
cardinality `Σ_{v ∈ L_i}(deg v − 1)`.  Proof: double-count the `L_i`–`L_{i+1}` edges — the parent
map (`level_unique_parent`) counts each child once, the children map (`level_children_count`) sums
to `Σ(deg v − 1)`, and the two counts agree by symmetry of adjacency. -/
theorem level_card_growth {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {r : ℕ} (hg : ∀ (v : V) (c : G.Walk v v), c.IsCycle → 2 * r + 1 < c.length) (x : V) {i : ℕ}
    (hi1 : 1 ≤ i) (hir : i + 1 ≤ r) :
    (univ.filter (fun v => G.dist x v = i + 1)).card
      = ∑ v ∈ univ.filter (fun v => G.dist x v = i), (G.degree v - 1) := by
  classical
  set A := univ.filter (fun v => G.dist x v = i) with hA
  set B := univ.filter (fun v => G.dist x v = i + 1) with hB
  have hLHS : B.card = ∑ u ∈ B, (A.filter (fun w => G.Adj u w)).card := by
    rw [Finset.card_eq_sum_ones]
    refine Finset.sum_congr rfl (fun u hu => ?_)
    simp only [hB, Finset.mem_filter, Finset.mem_univ, true_and] at hu
    have hconv : A.filter (fun w => G.Adj u w)
        = (G.neighborFinset u).filter (fun w => G.dist x w = i) := by
      ext w
      simp only [hA, Finset.mem_filter, Finset.mem_univ, true_and, SimpleGraph.mem_neighborFinset]
      tauto
    rw [hconv, level_unique_parent G hg x hir hu]
  have hRHS : ∑ v ∈ A, (G.degree v - 1) = ∑ v ∈ A, (B.filter (fun w => G.Adj v w)).card := by
    refine Finset.sum_congr rfl (fun v hv => ?_)
    simp only [hA, Finset.mem_filter, Finset.mem_univ, true_and] at hv
    have hconv : B.filter (fun w => G.Adj v w)
        = (G.neighborFinset v).filter (fun w => G.dist x w = i + 1) := by
      ext w
      simp only [hB, Finset.mem_filter, Finset.mem_univ, true_and, SimpleGraph.mem_neighborFinset]
      tauto
    rw [hconv, level_children_count G hg x hi1 (by omega) hv]
  have hswap : ∑ u ∈ B, (A.filter (fun w => G.Adj u w)).card
      = ∑ v ∈ A, (B.filter (fun w => G.Adj v w)).card := by
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun v _ => Finset.sum_congr rfl (fun u _ => ?_))
    exact if_congr (G.adj_comm u v) rfl rfl
  rw [hLHS, hswap, hRHS]

/-! ## The quadratic degree-weighted ball lower bound

The engine behind `(g − 5)² ≤ 2|S|²/t`. For a root `x` in a **connected** graph
with minimum degree `≥ 2` and no cycle of length `≤ 2r + 1`, with level excess
`ε_i(x) = Σ_{v∈L_i}(deg v − 2)`, the ball satisfies

  `1 + 2r + Σ_{i < r}(r − i)·ε_i(x) ≤ |B(x, r)|`.

Under connectivity this is an equality: the ball partitions into levels whose
sizes telescope through `level_card_growth`, each excess `ε_i` surfacing in the
`r − i` levels `i+1, …, r`. Connectivity is essential — `SimpleGraph.dist`
returns `0` for unreachable pairs, so without it `L_0` and the ball absorb the far
part of the graph and the bound breaks (`ball_weighted_lower`). -/

/-- **Triangular double-sum identity.**  `Σ_{i < r} Σ_{k ≤ i} ε k = Σ_{k < r}(r − k)·ε k`: reindex
the lower-triangular pairs `k ≤ i < r` by their column `k`, which appears in the `r − k` rows
`k, …, r − 1`. -/
theorem sum_range_triangle (r : ℕ) (ε : ℕ → ℕ) :
    ∑ i ∈ range r, ∑ k ∈ range (i + 1), ε k = ∑ k ∈ range r, (r - k) * ε k := by
  induction r with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ (fun k => (n + 1 - k) * ε k),
      Finset.sum_range_succ ε]
    have hk : ∑ k ∈ range n, (n + 1 - k) * ε k = ∑ k ∈ range n, ((n - k) * ε k + ε k) := by
      refine Finset.sum_congr rfl (fun k hk => ?_)
      rw [Finset.mem_range] at hk
      have hsub : n + 1 - k = (n - k) + 1 := by omega
      rw [hsub, add_mul, one_mul]
    rw [hk, Finset.sum_add_distrib]
    have hnn : n + 1 - n = 1 := by omega
    rw [hnn, one_mul]
    omega

/-- **Quadratic degree-weighted ball bound.**  In a connected graph with minimum degree at least
`2` and no cycle of length `≤ 2r + 1`, the ball `B(x, r) = {v | dist x v ≤ r}` satisfies
`1 + 2r + Σ_{i < r}(r − i)·ε_i(x) ≤ |B(x, r)|`, where `ε_i(x) = Σ_{v ∈ L_i}(deg v − 2)` is the
excess at BFS level `L_i(x) = {v | dist x v = i}`.  Under connectivity the bound is an exact
equality; the levels telescope through `level_card_growth`. -/
theorem ball_weighted_lower {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {r : ℕ} (hmin : ∀ v, 2 ≤ G.degree v)
    (hg : ∀ (v : V) (c : G.Walk v v), c.IsCycle → 2 * r + 1 < c.length)
    (hconn : G.Connected) (x : V) :
    1 + 2 * r + ∑ i ∈ range r, (r - i) *
        (∑ v ∈ univ.filter (fun v => G.dist x v = i), (G.degree v - 2))
      ≤ (univ.filter (fun v => G.dist x v ≤ r)).card := by
  classical
  -- Level `0` is exactly `{x}` (connectivity rules out spurious unreachable vertices).
  have hL0 : univ.filter (fun v => G.dist x v = 0) = ({x} : Finset V) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro h
      have hr : G.Reachable x v := hconn.preconnected x v
      exact (hr.dist_eq_zero_iff.mp h).symm
    · rintro rfl
      exact SimpleGraph.dist_self
  -- Closed form for level sizes: `|L_j| = 2 + Σ_{i < j} ε_i` for `1 ≤ j ≤ r`.
  have hclosed : ∀ j, 1 ≤ j → j ≤ r →
      (univ.filter (fun v => G.dist x v = j)).card
        = 2 + ∑ i ∈ range j,
            (∑ v ∈ univ.filter (fun v => G.dist x v = i), (G.degree v - 2)) := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base =>
      intro _
      have hL1 : univ.filter (fun v => G.dist x v = 1) = G.neighborFinset x := by
        ext v
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, SimpleGraph.mem_neighborFinset]
        exact SimpleGraph.dist_eq_one_iff_adj
      rw [Finset.sum_range_one, hL1, G.card_neighborFinset_eq_degree, hL0, Finset.sum_singleton]
      have := hmin x
      omega
    | succ n hn ih =>
      intro hnr
      have hdn := ih (by omega)
      rw [Finset.sum_range_succ, level_card_growth G hg x hn (by omega)]
      have hconv : ∑ v ∈ univ.filter (fun v => G.dist x v = n), (G.degree v - 1)
          = (∑ v ∈ univ.filter (fun v => G.dist x v = n), (G.degree v - 2))
            + (univ.filter (fun v => G.dist x v = n)).card := by
        rw [Finset.card_eq_sum_ones, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun v _ => ?_)
        have := hmin v
        omega
      rw [hconv, hdn]
      omega
  -- The ball is the disjoint union of the levels `L_0, …, L_r`.
  have hmem : ∀ v ∈ univ.filter (fun v => G.dist x v ≤ r), G.dist x v ∈ range (r + 1) := by
    intro v hv
    rw [Finset.mem_filter] at hv
    rw [Finset.mem_range]
    omega
  have hball : (univ.filter (fun v => G.dist x v ≤ r)).card
      = ∑ i ∈ range (r + 1), (univ.filter (fun v => G.dist x v = i)).card := by
    rw [Finset.card_eq_sum_card_fiberwise hmem]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [Finset.mem_range] at hi
    congr 1
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  have hd0 : (univ.filter (fun v => G.dist x v = 0)).card = 1 := by
    rw [hL0, Finset.card_singleton]
  -- Assemble the telescoped equality, then read off the inequality.
  have hfinal : (univ.filter (fun v => G.dist x v ≤ r)).card
      = 1 + 2 * r + ∑ i ∈ range r, (r - i) *
          (∑ v ∈ univ.filter (fun v => G.dist x v = i), (G.degree v - 2)) := by
    rw [hball, Finset.sum_range_succ', hd0]
    have hstep : ∑ i ∈ range r, (univ.filter (fun v => G.dist x v = i + 1)).card
        = 2 * r + ∑ i ∈ range r, (r - i) *
            (∑ v ∈ univ.filter (fun v => G.dist x v = i), (G.degree v - 2)) := by
      have h1 : ∑ i ∈ range r, (univ.filter (fun v => G.dist x v = i + 1)).card
          = ∑ i ∈ range r, (2 + ∑ k ∈ range (i + 1),
              (∑ v ∈ univ.filter (fun v => G.dist x v = k), (G.degree v - 2))) := by
        refine Finset.sum_congr rfl (fun i hi => ?_)
        rw [Finset.mem_range] at hi
        exact hclosed (i + 1) (by omega) (by omega)
      rw [h1, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul,
        sum_range_triangle]
      omega
    rw [hstep]
    omega
  exact hfinal.ge

/-! ## The SQRT double count

The global double count turning the per-root `ball_weighted_lower` into
`(g − 5)² ≤ 2|S|²/t`.  Fix a **connected** graph on a finite `V`, minimum degree
`≥ 2`, edge excess `t` (`|V| + t ≤ e(G)`), and no cycle of length
`≤ 2r + 1`. Summing the ball bound over all roots, using the swap
`sum_level_excess_swap` (`Σ_x ε_i(x) = Σ_v (deg v − 2)·|L_i(v)|` by distance
symmetry), the level floor `level_card_ge_two` and the handshake
`Σ_v (deg v − 2) ≥ 2t`, yields the quadratic

  `|V|·(1 + 2r) + 2·t·r² ≤ |V|²`.

The full `GirthExcessBound` discharge additionally needs a component descent
(picking the component carrying the excess), the contrapositive arithmetic, and
the `exists_isCycle_of_excess` / `cycle_walk_to_zmod` witness plumbing. -/

/-- **Triangular Gauss sum.**  `2·Σ_{i<m}(m − i) = m·(m + 1)`: the descending run
`m, m−1, …, 1` has twice-sum `m(m+1)`. -/
theorem two_mul_sum_range_sub (m : ℕ) :
    2 * ∑ i ∈ Finset.range m, (m - i) = m * (m + 1) := by
  induction m with
  | zero => simp
  | succ k ih =>
    have hsplit : ∑ i ∈ Finset.range (k + 1), (k + 1 - i)
        = (∑ i ∈ Finset.range k, (k - i)) + (k + 1) := by
      rw [Finset.sum_range_succ' (fun i => k + 1 - i) k, Nat.sub_zero]
      congr 1
      exact Finset.sum_congr rfl (fun i _ => by omega)
    rw [hsplit, Nat.mul_add, ih]
    ring

/-- **BFS levels are at least as wide as the root degree.**  The sharpening of `level_card_ge_two`
that the SQRT double count actually wants: in a graph with minimum degree at least `2` and no cycle
of length `≤ 2r + 1`, every BFS level `L_j(x) = {v | dist x v = j}` with `1 ≤ j ≤ r` has at least
`deg x` vertices — the `deg x` branches leaving `x` stay separated all the way out to radius `r`,
since two of them meeting at distance `j ≤ r` would close a cycle of length `≤ 2j ≤ 2r`.

Formally this is the *same* induction as `level_card_ge_two`, which already produces `deg x` at the
base level (`L_1(x)` is the neighbourhood) and then only ever needs `deg v − 1 ≥ 1` to carry the
floor outward; `level_card_ge_two` immediately weakens the base to `2 ≤ deg x` and loses the extra
`deg x − 2`.  Keeping it multiplies the excess term of `sqrt_double_count` by `3/2`. -/
theorem level_card_ge_deg {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {r : ℕ} (hmin : ∀ v, 2 ≤ G.degree v)
    (hg : ∀ (v : V) (c : G.Walk v v), c.IsCycle → 2 * r + 1 < c.length) (x : V) {j : ℕ}
    (hj1 : 1 ≤ j) (hjr : j ≤ r) :
    G.degree x ≤ (univ.filter (fun v => G.dist x v = j)).card := by
  classical
  revert hjr
  induction j, hj1 using Nat.le_induction with
  | base =>
    intro _
    have hL1 : univ.filter (fun v => G.dist x v = 1) = G.neighborFinset x := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, SimpleGraph.mem_neighborFinset]
      exact SimpleGraph.dist_eq_one_iff_adj
    rw [hL1, G.card_neighborFinset_eq_degree]
  | succ n hn ih =>
    intro hnr
    have hgen : G.degree x ≤ (univ.filter (fun v => G.dist x v = n)).card := ih (by omega)
    rw [level_card_growth G hg x hn (by omega)]
    calc G.degree x ≤ (univ.filter (fun v => G.dist x v = n)).card := hgen
      _ = ∑ _v ∈ univ.filter (fun v => G.dist x v = n), 1 := by rw [Finset.card_eq_sum_ones]
      _ ≤ ∑ v ∈ univ.filter (fun v => G.dist x v = n), (G.degree v - 1) :=
          Finset.sum_le_sum (fun v _ => by have := hmin v; omega)

/-- **The BFS-level swap.**  Summing the level-`i` excess `Σ_{v : dist x v = i}(deg v − 2)` over all
roots `x` regroups (by symmetry of distance) as `Σ_v (deg v − 2)·|{x : dist v x = i}|`. -/
theorem sum_level_excess_swap {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (i : ℕ) :
    ∑ x : V, (∑ v ∈ univ.filter (fun v => G.dist x v = i), (G.degree v - 2))
      = ∑ v : V, (univ.filter (fun x => G.dist v x = i)).card * (G.degree v - 2) := by
  classical
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  have hfeq : univ.filter (fun x => G.dist x v = i) = univ.filter (fun x => G.dist v x = i) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [SimpleGraph.dist_comm]
  rw [← Finset.sum_filter, hfeq, Finset.sum_const, smul_eq_mul]

/-- **The SQRT double count.**  In a connected graph `G` on a finite `V` with minimum degree at
least `2`, edge excess `t` (`|V| + t ≤ e(G)`), and no cycle of length `≤ 2r + 1`, the ball double
count gives `|V|·(1 + 2r) + t·(3r² − r) ≤ |V|²`.  Summing `ball_weighted_lower` over all roots,
swapping (`sum_level_excess_swap`), and feeding the handshake `Σ_v(deg v − 2) ≥ 2t` together with
the level floor `|L_i(v)| ≥ deg v` (`1 ≤ i ≤ r`, `level_card_ge_deg`) telescoped by
`two_mul_sum_range_sub`.

The excess weight is `3r² − r`, not the `2r²` obtained from the weaker floor `|L_i(v)| ≥ 2`
(`level_card_ge_two`): an excess vertex `v` is seen at distance `i` by at least `deg v ≥ 3` roots,
not merely `2`, so `W i ≥ 3D` for `1 ≤ i ≤ r` and the triangular telescope returns
`rD + 3D·r(r−1)/2 ≥ t(3r² − r)`.  Since `3r² − r ≥ 2r²` for `r ≥ 1`, this strictly strengthens the
old conclusion, and it is what pulls the import-free girth floor down. -/
theorem sqrt_double_count {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {r t : ℕ} (hmin : ∀ v, 2 ≤ G.degree v)
    (hg : ∀ (v : V) (c : G.Walk v v), c.IsCycle → 2 * r + 1 < c.length)
    (hconn : G.Connected) (hexc : Fintype.card V + t ≤ G.edgeFinset.card) :
    Fintype.card V * (1 + 2 * r) + t * (3 * r ^ 2 - r) ≤ (Fintype.card V) ^ 2 := by
  classical
  -- The per-root quadratic ball bound.
  have hbw : ∀ x : V, 1 + 2 * r + ∑ i ∈ range r, (r - i) *
      (∑ v ∈ univ.filter (fun v => G.dist x v = i), (G.degree v - 2))
      ≤ (univ.filter (fun v => G.dist x v ≤ r)).card :=
    fun x => ball_weighted_lower G hmin hg hconn x
  have hsum1 : ∑ x : V, (1 + 2 * r + ∑ i ∈ range r, (r - i) *
      (∑ v ∈ univ.filter (fun v => G.dist x v = i), (G.degree v - 2)))
      ≤ ∑ x : V, (univ.filter (fun v => G.dist x v ≤ r)).card :=
    Finset.sum_le_sum (fun x _ => hbw x)
  -- Each ball fits in `V`, so the summed balls are at most `|V|²`.
  have hRHS : ∑ x : V, (univ.filter (fun v => G.dist x v ≤ r)).card ≤ (Fintype.card V) ^ 2 := by
    calc ∑ x : V, (univ.filter (fun v => G.dist x v ≤ r)).card
        ≤ ∑ _x : V, Fintype.card V :=
          Finset.sum_le_sum (fun x _ => (Finset.card_filter_le _ _).trans_eq Finset.card_univ)
      _ = Fintype.card V * Fintype.card V := by
          rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
      _ = (Fintype.card V) ^ 2 := (pow_two _).symm
  -- The excess-weighted degree data.
  set D : ℕ := ∑ v : V, (G.degree v - 2) with hD
  set W : ℕ → ℕ := fun i =>
    ∑ v : V, (univ.filter (fun x => G.dist v x = i)).card * (G.degree v - 2) with hW
  -- The swap: `Σ_x Σ_i (r−i)·ε_i(x) = Σ_i (r−i)·W i`.
  have hswapall : ∑ x : V, ∑ i ∈ range r, (r - i) *
        (∑ v ∈ univ.filter (fun v => G.dist x v = i), (G.degree v - 2))
      = ∑ i ∈ range r, (r - i) * W i := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Finset.mul_sum]
    congr 1
    simp only [hW]
    exact sum_level_excess_swap G i
  -- `W 0 = D` (level `0` is the singleton root).
  have hW0 : W 0 = D := by
    simp only [hW, hD]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    have hcard : (univ.filter (fun x => G.dist v x = 0)).card = 1 := by
      have hset : univ.filter (fun x => G.dist v x = 0) = ({v} : Finset V) := by
        ext w
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · intro h
          exact ((hconn.preconnected v w).dist_eq_zero_iff.mp h).symm
        · rintro rfl
          exact SimpleGraph.dist_self
      rw [hset, Finset.card_singleton]
    rw [hcard, one_mul]
  -- `3·D ≤ W i` for `1 ≤ i ≤ r` (each level is at least as wide as the root degree, which is
  -- `≥ 3` at every vertex that carries excess).
  have hWi : ∀ i, 1 ≤ i → i ≤ r → 3 * D ≤ W i := by
    intro i hi1 hir
    simp only [hW, hD]
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun v _ => ?_)
    calc 3 * (G.degree v - 2) ≤ G.degree v * (G.degree v - 2) := by
          rcases Nat.lt_or_ge (G.degree v) 3 with hlt | hge
          · have : G.degree v - 2 = 0 := by omega
            simp [this]
          · exact Nat.mul_le_mul_right _ hge
      _ ≤ (univ.filter (fun x => G.dist v x = i)).card * (G.degree v - 2) :=
          Nat.mul_le_mul_right _ (level_card_ge_deg G hmin hg v hi1 hir)
  -- The handshake: `2t ≤ D`.
  have hD2t : 2 * t ≤ D := by
    have hsum : ∑ v : V, G.degree v = 2 * G.edgeFinset.card :=
      G.sum_degrees_eq_twice_card_edges
    have hDeq : ∑ v : V, G.degree v
        = (∑ v : V, (G.degree v - 2)) + 2 * Fintype.card V := by
      calc ∑ v : V, G.degree v = ∑ v : V, ((G.degree v - 2) + 2) :=
            Finset.sum_congr rfl (fun v _ => by have := hmin v; omega)
        _ = (∑ v : V, (G.degree v - 2)) + ∑ _v : V, (2 : ℕ) := Finset.sum_add_distrib
        _ = (∑ v : V, (G.degree v - 2)) + 2 * Fintype.card V := by
            rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.mul_comm]
    rw [hD]
    omega
  -- The triangular weight telescopes to `t·(3r² − r)`: the root level contributes `r·D` and each
  -- of the `r − 1` inner levels at least `3D`, so `2·Σ ≥ 2rD + 3D·r(r−1) = D·(3r² − r)`.
  have hDr : t * (3 * r ^ 2 - r) ≤ ∑ i ∈ range r, (r - i) * W i := by
    rcases Nat.eq_zero_or_pos r with hr0 | hrpos
    · rw [hr0]; simp
    · obtain ⟨m, hr⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
      have hrw : ∑ i ∈ range r, (r - i) * W i
          = (∑ i ∈ range m, (m - i) * W (i + 1)) + (m + 1) * D := by
        rw [hr, Finset.sum_range_succ' (fun i => (m + 1 - i) * W i) m]
        congr 1
        · apply Finset.sum_congr rfl
          intro i _
          congr 1
          omega
        · rw [Nat.sub_zero, hW0]
      have hrsub : 3 * r ^ 2 - r = (m + 1) * (3 * m + 2) := by
        have h : 3 * r ^ 2 = (m + 1) * (3 * m + 2) + r := by subst hr; ring
        omega
      rw [hrw, hrsub]
      have hlow : (∑ i ∈ range m, (m - i)) * (3 * D)
          ≤ ∑ i ∈ range m, (m - i) * W (i + 1) := by
        rw [Finset.sum_mul]
        apply Finset.sum_le_sum
        intro i hi
        rw [Finset.mem_range] at hi
        exact mul_le_mul_right (hWi (i + 1) (by omega) (by omega)) (m - i)
      have hgauss : 2 * ∑ i ∈ range m, (m - i) = m * (m + 1) := two_mul_sum_range_sub m
      have hSUM : 3 * (m * (m + 1)) * D ≤ 2 * ∑ i ∈ range m, (m - i) * W (i + 1) := by
        calc 3 * (m * (m + 1)) * D = (2 * ∑ i ∈ range m, (m - i)) * (3 * D) := by
              rw [hgauss]; ring
          _ = 2 * ((∑ i ∈ range m, (m - i)) * (3 * D)) := by ring
          _ ≤ 2 * ∑ i ∈ range m, (m - i) * W (i + 1) := Nat.mul_le_mul_left 2 hlow
      -- Double both sides so the `D ≥ 2t` substitution is subtraction-free.
      refine Nat.le_of_mul_le_mul_left ?_ (show 0 < 2 by norm_num)
      calc 2 * (t * ((m + 1) * (3 * m + 2)))
          = 3 * (m * (m + 1)) * (2 * t) + (m + 1) * (2 * t) * 2 := by ring
        _ ≤ 3 * (m * (m + 1)) * D + (m + 1) * D * 2 := by gcongr
        _ ≤ 2 * (∑ i ∈ range m, (m - i) * W (i + 1)) + (m + 1) * D * 2 :=
            Nat.add_le_add_right hSUM _
        _ = 2 * ((∑ i ∈ range m, (m - i) * W (i + 1)) + (m + 1) * D) := by ring
  -- Assemble.
  calc Fintype.card V * (1 + 2 * r) + t * (3 * r ^ 2 - r)
      ≤ Fintype.card V * (1 + 2 * r) + ∑ i ∈ range r, (r - i) * W i :=
        Nat.add_le_add_left hDr _
    _ = ∑ x : V, (1 + 2 * r + ∑ i ∈ range r, (r - i) *
          (∑ v ∈ univ.filter (fun v => G.dist x v = i), (G.degree v - 2))) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul, hswapall]
    _ ≤ ∑ x : V, (univ.filter (fun v => G.dist x v ≤ r)).card := hsum1
    _ ≤ (Fintype.card V) ^ 2 := hRHS

end ACMax


/-! ## The 2-core extraction

The entry piece: from a graph with edge excess `t`, extract an induced subgraph of
minimum degree `≥ 2` still carrying the whole excess (`two_core_of_excess`). The
within-`S` bookkeeping is `degWithin G S v` (neighbours of `v` inside `S`) and
`edgeSumWithin G S = ∑_{u∈S} degWithin G S u` (twice the induced edge count), with
the handshake `edgeSumWithin_eq_pairs` and the erase law `edgeSumWithin_erase`. -/

namespace ACMax

open SimpleGraph Finset

variable {V : Type*}

/-- The number of neighbours of `v` lying inside the finite set `S` — the degree of `v` in the
induced subgraph `G.induce ↑S`. -/
def degWithin (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (v : V) : ℕ :=
  (S.filter (fun w => G.Adj v w)).card

/-- Twice the number of edges of `G` with both endpoints in `S`, written as the within-`S`
degree sum. -/
def edgeSumWithin (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : ℕ :=
  ∑ u ∈ S, degWithin G S u

/-- **The within-`S` handshake.**  The within-`S` degree sum equals the number of ordered adjacent
pairs with both coordinates in `S`. -/
theorem edgeSumWithin_eq_pairs [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) :
    edgeSumWithin G S = ((S ×ˢ S).filter (fun q => G.Adj q.1 q.2)).card := by
  rw [edgeSumWithin, Finset.card_filter, Finset.sum_product]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  rw [degWithin, Finset.card_filter]

/-- **The erase law.**  Deleting a vertex `v ∈ S` drops the within-`S` degree sum by exactly twice
the within-`S` degree of `v`. -/
theorem edgeSumWithin_erase [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {S : Finset V} {v : V} (hv : v ∈ S) :
    edgeSumWithin G S = edgeSumWithin G (S.erase v) + 2 * degWithin G S v := by
  have hstep : ∀ u : V, degWithin G S u
      = degWithin G (S.erase v) u + (if G.Adj u v then 1 else 0) := by
    intro u
    rw [degWithin, degWithin]
    have hS : S = insert v (S.erase v) := (Finset.insert_erase hv).symm
    nth_rewrite 1 [hS]
    rw [Finset.filter_insert]
    by_cases hadj : G.Adj u v
    · have hvnotin : v ∉ (S.erase v).filter (fun w => G.Adj u w) := by
        simp [Finset.mem_filter, Finset.mem_erase]
      rw [if_pos hadj, Finset.card_insert_of_notMem hvnotin, if_pos hadj]
    · rw [if_neg hadj, if_neg hadj, add_zero]
  have hcount : ∑ u ∈ S.erase v, (if G.Adj u v then (1 : ℕ) else 0) = degWithin G S v := by
    have h1 : ∑ u ∈ S.erase v, (if G.Adj u v then (1 : ℕ) else 0)
        = ∑ u ∈ S, (if G.Adj u v then (1 : ℕ) else 0) :=
      Finset.sum_erase (f := fun u => if G.Adj u v then (1 : ℕ) else 0) (a := v) S
        (by simp [SimpleGraph.irrefl])
    rw [h1, degWithin, Finset.card_filter]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    exact if_congr (G.adj_comm u v) rfl rfl
  rw [edgeSumWithin, ← Finset.add_sum_erase _ _ hv]
  rw [Finset.sum_congr rfl (fun u _ => hstep u)]
  rw [Finset.sum_add_distrib, hcount, edgeSumWithin]
  omega

/-- **The 2-core induction.**  Starting from any `S` carrying the excess `2·|S| + 2t ≤
edgeSumWithin G S`, one reaches a nonempty subset of minimum within-degree `≥ 2` still carrying the
excess, by repeatedly deleting a within-degree `≤ 1` vertex. -/
theorem two_core_aux [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] {t : ℕ}
    (ht : 1 ≤ t) :
    ∀ S : Finset V, 2 * S.card + 2 * t ≤ edgeSumWithin G S →
      ∃ S' : Finset V, S' ⊆ S ∧ S'.Nonempty ∧
        (∀ v ∈ S', 2 ≤ degWithin G S' v) ∧ 2 * S'.card + 2 * t ≤ edgeSumWithin G S' := by
  refine Finset.strongInduction (fun S ih => ?_)
  intro hinv
  have hSne : S.Nonempty := by
    rcases S.eq_empty_or_nonempty with rfl | h
    · rw [edgeSumWithin, Finset.sum_empty, Finset.card_empty] at hinv; omega
    · exact h
  by_cases hmin : ∀ v ∈ S, 2 ≤ degWithin G S v
  · exact ⟨S, subset_rfl, hSne, hmin, hinv⟩
  · simp only [not_forall, not_le] at hmin
    obtain ⟨v, hvS, hvdeg⟩ := hmin
    have hpos : 1 ≤ S.card := Finset.card_pos.mpr hSne
    have hkey := edgeSumWithin_erase G hvS
    have hcard' : (S.erase v).card = S.card - 1 := Finset.card_erase_of_mem hvS
    have hnew : 2 * (S.erase v).card + 2 * t ≤ edgeSumWithin G (S.erase v) := by omega
    obtain ⟨S', hsub, hne', hmin', hinv'⟩ := ih (S.erase v) (Finset.erase_ssubset hvS) hnew
    exact ⟨S', hsub.trans (Finset.erase_subset _ _), hne', hmin', hinv'⟩

end ACMax
end


/-! ########################################################################################
   PART VII --- The counting rows, the collision, and the theorem

   The census rows pin the degree profile (they are proved by exhibiting the certificates of
   Part V), the profile makes the ball count of Part VI contradict itself, and the main
   theorem follows for every `n >= 123`.
   ######################################################################################## -/

/- ---------------------------------------- Counting.StarvedCensus ---------- -/
section
/-!
# The starved-world census and the owner-choke rows

The pure-counting census of the *starved world* — the `e(M) = 0` stratum: a
never-firing graph on `Fin n` with `2(n−2)` edges, minimum degree `≥ 3`, and no
degree-3–degree-3 edge. Its degree-3 vertices are *twins* (all `M`-isolated), the
degree-4 vertices the *sea*, the degree-`≥ 4` vertices the *hubs*. The
contrapositive of the star-moat law caps twin-hoarding (`starved_cap`), and
feeding the caps into the twin-incidence total against the degree-excess ledger
`Σ_h(deg − 3) = n − 8` produces the census rows.

## Main results

* `starved_cap`, `hoarding_law`, `slots_law` — the cap and the two aggregate rows;
  the hoarding row gives the giant census `n_g ≤ 1` at `n ≤ 49`.
* `starved_owner_choke_35_49` — with the owner-choke `7·t₄ + 3X ≤ 4n − 32`, the
  `35 ≤ n ≤ 49` band dies by pure counting.
* `slots_law_sharp` — the per-`p` sharpened slots row `24 + 2X ≤ t₄ + p + h₆₊ + 4n_g`
  split along the honest per-heavy caps (`p` = saturated degree-5 hubs).
* `choke_count`, `p_choke_count`, `p_choke_row` — the owner-choke and its per-`p`
  sharpening `7·t₄ + 8·p + 3X + 32 ≤ 4n`, with the independence rows
  `owner_independence`, `owner_sat_independence`.
* `deco_edge_shared_twin_fires`, `sat_sat_independence`,
  `p_choke_row_unconditional` — the shared-twin decorated-edge moat (fires at
  `9·(deg u + deg v) ≤ n + 56`) discharging the last moat-provenance hypothesis.
-/

namespace ACMax

open Finset
open scoped Classical

/-- **The starved cap** (contrapositive of `star_moat_fires`).  In a never-firing census world
(`m = 2(n−2)`, `δ ≥ 3`) a hub `h` under the cap horizon `9·deg h ≤ n + 15` owns at most
`deg h − 3` `M`-isolated twins: if it owned `deg h − 2`, that twin star would fire. -/
theorem starved_cap {n : ℕ} [Nonempty (Fin n)] (G : SimpleGraph (Fin n))
    (hm : G.edgeFinset.card = 2 * (n - 2)) (h3 : ∀ v : Fin n, 3 ≤ G.degree v)
    (hnf : ¬ algConn G ≤ 2) (h : Fin n) (hfire : 9 * G.degree h ≤ n + 15) :
    (G.neighborFinset h ∩ isoTwins G).card ≤ G.degree h - 3 := by
  by_contra hlt
  -- extract a twin star of the exact firing size `deg h − 2`
  have hge : G.degree h - 2 ≤ (G.neighborFinset h ∩ isoTwins G).card := by omega
  obtain ⟨K, hKsub, hKcard⟩ := Finset.exists_subset_card_eq hge
  apply hnf
  refine star_moat_fires G hm h3 h K ?_ ?_ hKcard hfire
  · exact fun x hx => (Finset.mem_inter.mp (hKsub hx)).1
  · exact fun t ht => (mem_isoTwins.mp (Finset.mem_inter.mp (hKsub ht)).2).1

/-- **The twin total.**  Under `hs0` (`e(M) = 0`) the degree-`3` set is the `M`-isolated twin
set, so the hub-to-twin incidence sum is `3·(8 + X) = 24 + 3X`. -/
theorem twin_total_eq {n : ℕ} (G : SimpleGraph (Fin n)) (hn : 2 ≤ n)
    (hm : G.edgeFinset.card = 2 * (n - 2)) (h3 : ∀ v : Fin n, 3 ≤ G.degree v)
    (hs0 : ∀ v w : Fin n, G.degree v = 3 → G.degree w = 3 → ¬G.Adj v w) :
    ∑ h ∈ hubSet G, (G.neighborFinset h ∩ isoTwins G).card = 24 + 3 * excessX n G := by
  have h1 := twin_incidence_total G h3
  have h2 : (isoTwins G).card = 8 + excessX n G := by
    rw [← deg3_eq_isoTwins_of_s0 G hs0, deg3_card_eq_eight_add_excess n G hn hm h3]
  have hbridge : ∑ h ∈ hubSet G, (G.neighborFinset h ∩ isoTwins G).card
      = 3 * (isoTwins G).card := by
    rw [← h1]
    refine Finset.sum_congr rfl (fun h _ => ?_)
    congr 1
    apply Finset.ext
    intro x
    simp only [Finset.mem_inter]
  rw [hbridge, h2]; ring

/-- **Heavies are bounded by the excess.**  The number of heavies (`deg ≥ 5`) is at most the
total excess `X`, since each heavy contributes `deg − 4 ≥ 1`. -/
theorem heavy_le_excess {n : ℕ} (G : SimpleGraph (Fin n)) :
    (Finset.univ.filter (fun h => 5 ≤ G.degree h)).card ≤ excessX n G := by
  have hcard : (Finset.univ.filter (fun h => 5 ≤ G.degree h)).card
      = ∑ _h ∈ Finset.univ.filter (fun h => 5 ≤ G.degree h), 1 := by
    rw [Finset.sum_const, smul_eq_mul, mul_one]
  rw [hcard]
  show ∑ _h ∈ Finset.univ.filter (fun h => 5 ≤ G.degree h), 1
      ≤ ∑ h ∈ Finset.univ.filter (fun v => 5 ≤ G.degree v), (G.degree h - 4)
  apply Finset.sum_le_sum
  intro h hh
  rw [Finset.mem_filter] at hh
  omega

/-! ## The per-`p` sharpened slots row (D1)

Sharpens `slots_law` by splitting the deg-`≥ 5` twin demand along the per-heavy
caps `starved_cap` (no independence law). The twin total `24 + 3X` splits into the
deg-4 owner slots `t₄` and a deg-`≥ 5` remainder `≤ X + p + h₆₊ + 4n_g`, giving the
sharpened row `24 + 2X ≤ t₄ + p + h₆₊ + 4n_g` (`p` = saturated deg-5 hubs,
`h₆₊` = non-giant deg-`≥ 6` hubs, `n_g` = giants). -/

/-- **D1 — the per-`p` sharpened slots row.**  In a never-firing starved census (`m = 2(n−2)`,
`δ ≥ 3`, `hs0`) the twin total `24 + 3X` splits along the honest per-heavy caps into
`24 + 2X ≤ t₄ + p + h₆₊ + 4·n_g`, where `t₄ = ∑_{deg-4 hubs} |N(h) ∩ Iso|`, `p` is the count of
saturated deg-`5` hubs (deg `5`, owning exactly `2` `M`-isolated twins), `h₆₊` the count of
non-giant deg-`≥ 6` hubs (`6 ≤ deg`, `9·deg ≤ n + 15`) and `n_g` the number of giants
(`n + 15 < 9·deg`).  Each deg-`≥ 5` hub contributes at most `(deg − 4)` plus one of the class
credits, so the deg-`≥ 5` remainder is `≤ X + p + h₆₊ + 4·n_g`; the star-moat cap `starved_cap`
supplies the non-giant per-hub bounds. -/
theorem slots_p_row {n : ℕ} [Nonempty (Fin n)] (G : SimpleGraph (Fin n)) (hn : 8 ≤ n)
    (hm : G.edgeFinset.card = 2 * (n - 2)) (h3 : ∀ v : Fin n, 3 ≤ G.degree v)
    (hnf : ¬ algConn G ≤ 2)
    (hs0 : ∀ v w : Fin n, G.degree v = 3 → G.degree w = 3 → ¬G.Adj v w) :
    24 + 2 * excessX n G
      ≤ (∑ h ∈ (hubSet G).filter (fun h => G.degree h = 4),
            (G.neighborFinset h ∩ isoTwins G).card)
        + ((hubSet G).filter (fun h => G.degree h = 5 ∧
            (G.neighborFinset h ∩ isoTwins G).card = 2)).card
        + ((hubSet G).filter (fun h => 6 ≤ G.degree h ∧
            ¬ (n + 15 < 9 * G.degree h))).card
        + 4 * ((hubSet G).filter (fun h => n + 15 < 9 * G.degree h)).card := by
  have htot := twin_total_eq G (by omega) hm h3 hs0
  have hsplit := Finset.sum_filter_add_sum_filter_not (hubSet G)
    (fun h => G.degree h = 4) (fun h => (G.neighborFinset h ∩ isoTwins G).card)
  -- the set of deg-`≥ 5` hubs, and its identification with `univ.filter (5 ≤ deg)`
  have hDn4 : (hubSet G).filter (fun h => ¬ G.degree h = 4)
      = Finset.univ.filter (fun h => 5 ≤ G.degree h) := by
    ext x
    simp only [Finset.mem_filter, mem_hubSet, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hh, hne⟩; omega
    · intro h5; exact ⟨by omega, by omega⟩
  -- the sharpened deg-`≥ 5` cap: the remainder is `≤ X + p + h₆₊ + 4·n_g`
  have hcapP : ∑ h ∈ (hubSet G).filter (fun h => ¬ G.degree h = 4),
      (G.neighborFinset h ∩ isoTwins G).card
      ≤ excessX n G
        + ((hubSet G).filter (fun h => G.degree h = 5 ∧
            (G.neighborFinset h ∩ isoTwins G).card = 2)).card
        + ((hubSet G).filter (fun h => 6 ≤ G.degree h ∧
            ¬ (n + 15 < 9 * G.degree h))).card
        + 4 * ((hubSet G).filter (fun h => n + 15 < 9 * G.degree h)).card := by
    have hpt : ∀ h ∈ (hubSet G).filter (fun h => ¬ G.degree h = 4),
        (G.neighborFinset h ∩ isoTwins G).card
        ≤ (G.degree h - 4)
          + (if G.degree h = 5 ∧ (G.neighborFinset h ∩ isoTwins G).card = 2 then 1 else 0)
          + (if 6 ≤ G.degree h ∧ ¬ (n + 15 < 9 * G.degree h) then 1 else 0)
          + 4 * (if n + 15 < 9 * G.degree h then 1 else 0) := by
      intro h hh
      rw [Finset.mem_filter] at hh
      obtain ⟨hhub, hne4⟩ := hh
      have hdeg4 : 4 ≤ G.degree h := mem_hubSet.mp hhub
      have hcardle : (G.neighborFinset h ∩ isoTwins G).card ≤ G.degree h :=
        le_of_le_of_eq (Finset.card_le_card Finset.inter_subset_left)
          (G.card_neighborFinset_eq_degree h)
      by_cases hg : n + 15 < 9 * G.degree h
      · split_ifs <;> omega
      · have hcap := starved_cap G hm h3 hnf h (by omega)
        split_ifs <;> omega
    calc ∑ h ∈ (hubSet G).filter (fun h => ¬ G.degree h = 4),
            (G.neighborFinset h ∩ isoTwins G).card
        ≤ ∑ h ∈ (hubSet G).filter (fun h => ¬ G.degree h = 4),
            ((G.degree h - 4)
              + (if G.degree h = 5 ∧ (G.neighborFinset h ∩ isoTwins G).card = 2 then 1 else 0)
              + (if 6 ≤ G.degree h ∧ ¬ (n + 15 < 9 * G.degree h) then 1 else 0)
              + 4 * (if n + 15 < 9 * G.degree h then 1 else 0)) := Finset.sum_le_sum hpt
      _ ≤ excessX n G
            + ((hubSet G).filter (fun h => G.degree h = 5 ∧
                (G.neighborFinset h ∩ isoTwins G).card = 2)).card
            + ((hubSet G).filter (fun h => 6 ≤ G.degree h ∧
                ¬ (n + 15 < 9 * G.degree h))).card
            + 4 * ((hubSet G).filter (fun h => n + 15 < 9 * G.degree h)).card := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
          have hA : ∑ h ∈ (hubSet G).filter (fun h => ¬ G.degree h = 4), (G.degree h - 4)
              = excessX n G := by rw [hDn4]; rfl
          have hB : ∑ h ∈ (hubSet G).filter (fun h => ¬ G.degree h = 4),
              (if G.degree h = 5 ∧ (G.neighborFinset h ∩ isoTwins G).card = 2 then 1 else 0)
              ≤ ((hubSet G).filter (fun h => G.degree h = 5 ∧
                  (G.neighborFinset h ∩ isoTwins G).card = 2)).card := by
            rw [← Finset.card_filter]
            apply Finset.card_le_card
            intro x hx
            simp only [Finset.mem_filter, mem_hubSet] at hx ⊢
            exact ⟨hx.1.1, hx.2⟩
          have hC : ∑ h ∈ (hubSet G).filter (fun h => ¬ G.degree h = 4),
              (if 6 ≤ G.degree h ∧ ¬ (n + 15 < 9 * G.degree h) then 1 else 0)
              ≤ ((hubSet G).filter (fun h => 6 ≤ G.degree h ∧
                  ¬ (n + 15 < 9 * G.degree h))).card := by
            rw [← Finset.card_filter]
            apply Finset.card_le_card
            intro x hx
            simp only [Finset.mem_filter, mem_hubSet] at hx ⊢
            exact ⟨hx.1.1, hx.2⟩
          have hD : ∑ h ∈ (hubSet G).filter (fun h => ¬ G.degree h = 4),
              4 * (if n + 15 < 9 * G.degree h then 1 else 0)
              ≤ 4 * ((hubSet G).filter (fun h => n + 15 < 9 * G.degree h)).card := by
            rw [← Finset.mul_sum, ← Finset.card_filter]
            gcongr
            exact Finset.filter_subset _ _
          omega
  omega

/-! ## Independence and triangle helpers -/

/-- Triangle test. -/
theorem tri_deg445_fires {n : ℕ} [Nonempty (Fin n)] (hn : 16 ≤ n)
    (G : SimpleGraph (Fin n)) (hm : G.edgeFinset.card = 2 * (n - 2))
    (h3 : ∀ v : Fin n, 3 ≤ G.degree v) (a b t : Fin n)
    (hab : G.Adj a b) (hat : G.Adj a t) (hbt : G.Adj b t)
    (hda : G.degree a = 4) (hdb : G.degree b = 4) (hdt : G.degree t = 3) :
    algConn G ≤ 2 := by
  have hne_ab : a ≠ b := G.ne_of_adj hab
  have hne_at : a ≠ t := by intro h; rw [h, hdt] at hda; omega
  have hne_bt : b ≠ t := by intro h; rw [h, hdt] at hdb; omega
  have e0 : (![a, b, t] : Fin 3 → Fin n) 0 = a := rfl
  have e1 : (![a, b, t] : Fin 3 → Fin n) 1 = b := rfl
  have e2 : (![a, b, t] : Fin 3 → Fin n) 2 = t := rfl
  refine master_cycle_fires (k := 3) (by norm_num) G hm h3 ![a, b, t] ?_ ?_ ?_ ?_
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all <;> rfl
  · intro i
    fin_cases i
    · show G.Adj a b; exact hab
    · show G.Adj b t; exact hbt
    · show G.Adj t a; exact hat.symm
  · have hsplit : (∑ i : ZMod 3, G.degree (![a, b, t] i))
        = G.degree a + G.degree b + G.degree t := by
      have h := Fin.sum_univ_three (fun i : Fin 3 => G.degree (![a, b, t] i))
      rw [e0, e1, e2] at h
      exact h
    rw [hsplit, hda, hdb, hdt]; omega
  · have hsplit : (∑ i : ZMod 3, (G.degree (![a, b, t] i) - 1))
        = (G.degree a - 1) + (G.degree b - 1) + (G.degree t - 1) := by
      have h := Fin.sum_univ_three (fun i : Fin 3 => G.degree (![a, b, t] i) - 1)
      rw [e0, e1, e2] at h
      exact h
    rw [hsplit, hda, hdb, hdt]
    omega

/-- **Owner independence.**  In a never-firing starved census (`m = 2(n−2)`, `δ ≥ 3`) at
`n ≥ 30`, any two *distinct* degree-`4` vertices `o₁, o₂`, each carrying a degree-`3` neighbour
(`t₁` resp. `t₂`), are non-adjacent.  If they were adjacent: distinct twins (`t₁ ≠ t₂`) fire the
`(4,4)` decorated edge `z4c_fires`; a shared twin (`t₁ = t₂`) makes `{o₁, o₂, t₁}` a
degree-`(4,4,3)` triangle which fires the master cycle `tri_deg445_fires` — either way
contradicting `¬ algConn G ≤ 2`. -/
theorem owner_independence {n : ℕ} [Nonempty (Fin n)] (hn : 30 ≤ n)
    (G : SimpleGraph (Fin n)) (hm : G.edgeFinset.card = 2 * (n - 2))
    (h3 : ∀ v : Fin n, 3 ≤ G.degree v) (hnf : ¬ algConn G ≤ 2)
    (o₁ o₂ t₁ t₂ : Fin n) (ho1 : G.degree o₁ = 4) (ho2 : G.degree o₂ = 4)
    (ht1 : G.Adj o₁ t₁) (hdt1 : G.degree t₁ = 3)
    (ht2 : G.Adj o₂ t₂) (hdt2 : G.degree t₂ = 3) :
    ¬ G.Adj o₁ o₂ := by
  intro hadj
  apply hnf
  by_cases htw : t₁ = t₂
  · subst htw
    exact tri_deg445_fires (by omega) G hm h3 o₁ o₂ t₁ hadj ht1 ht2 ho1 ho2 hdt1
  · have hutv : o₁ ≠ t₂ := by intro h; rw [h, hdt2] at ho1; omega
    have hvtu : o₂ ≠ t₁ := by intro h; rw [h, hdt1] at ho2; omega
    exact z4c_fires hn G hm h3 o₁ o₂ t₁ t₂ hadj ho1 ho2 ht1 ht2 hdt1 hdt2 htw hutv hvtu

/-! ## The per-`p` sharpened owner-choke

Sharpens the owner-choke `choke_count` (`7·t₄ + 3X + 32 ≤ 4n`) by `8·p`, where `p`
counts saturated degree-5 hubs (owning exactly two twins). A saturated degree-5
hub spends 2 edges on its twins and, by the decorated-edge law, 0 on owners and 0
on other saturated hubs, so its remaining 3 edges land on non-owner
non-saturated hubs; the transposed slice count gives `p_choke_count` /
`p_choke_row` (`7·t₄ + 8·p + 3X + 32 ≤ 4n`). The `(4,5)` independence is
`owner_sat_independence`; the `(5,5)` independence is threaded as `hindep55`. -/

/-- **N5 — the per-`p` sharpened owner-choke (counting core).**  In a starved census
(`m = 2(n−2)`, `δ ≥ 3`, `hs0`) under the degree-`4` twin cap (`hcap4`) and the three independence
rows — degree-`4` owners pairwise non-adjacent (`hindep44`), owner–saturated non-adjacent
(`hindep45`), saturated–saturated non-adjacent (`hindep55`) — the degree-`4` owner-slot total
`t₄ = ∑_{deg 4 hubs} |N(h) ∩ Iso|` and the saturated degree-`5` count `p` satisfy the sharpened
choke `7·t₄ + 8·p + 3·X + 32 ≤ 4n`.

Owners `O` (degree-`4`, one twin) each spend `3` edges on non-owner non-saturated hubs `NH`;
saturated degree-`5`s `P` (two twins) each spend `3` edges on `NH` (the `2` twin edges and the
`0` owner/saturated edges being excluded by independence).  The bipartite double count
`cross_count` transposes `∑_{O ∪ P} |N(·) ∩ NH| = 3·t₄ + 3·p` into
`∑_{NH} |N(w) ∩ (O ∪ P)| ≤ ∑_{NH} deg w`, and the hub degree total
`∑_{Hub} deg + 3X + 32 = 4n` splits as `∑_{NH} deg + 4·t₄ + 5·p`; combining gives the choke. -/
theorem p_choke_count {n : ℕ} [Nonempty (Fin n)] (hn : 8 ≤ n)
    (G : SimpleGraph (Fin n)) (hm : G.edgeFinset.card = 2 * (n - 2))
    (h3 : ∀ v : Fin n, 3 ≤ G.degree v)
    (hs0 : ∀ v w : Fin n, G.degree v = 3 → G.degree w = 3 → ¬G.Adj v w)
    (hcap4 : ∀ h : Fin n, G.degree h = 4 → (G.neighborFinset h ∩ isoTwins G).card ≤ 1)
    (hindep44 : ∀ o₁ o₂ : Fin n, G.degree o₁ = 4 → G.degree o₂ = 4 →
        (G.neighborFinset o₁ ∩ isoTwins G).Nonempty →
        (G.neighborFinset o₂ ∩ isoTwins G).Nonempty → o₁ ≠ o₂ → ¬ G.Adj o₁ o₂)
    (hindep45 : ∀ o s : Fin n, G.degree o = 4 →
        (G.neighborFinset o ∩ isoTwins G).Nonempty → G.degree s = 5 →
        (G.neighborFinset s ∩ isoTwins G).card = 2 → ¬ G.Adj o s)
    (hindep55 : ∀ s₁ s₂ : Fin n, G.degree s₁ = 5 →
        (G.neighborFinset s₁ ∩ isoTwins G).card = 2 → G.degree s₂ = 5 →
        (G.neighborFinset s₂ ∩ isoTwins G).card = 2 → s₁ ≠ s₂ → ¬ G.Adj s₁ s₂) :
    7 * (∑ h ∈ (hubSet G).filter (fun h => G.degree h = 4),
            (G.neighborFinset h ∩ isoTwins G).card)
        + 8 * ((hubSet G).filter (fun h => G.degree h = 5 ∧
            (G.neighborFinset h ∩ isoTwins G).card = 2)).card
        + 3 * excessX n G + 32 ≤ 4 * n := by
  classical
  -- the hub degree total `∑_{Hub} deg + 3X + 32 = 4n`
  have hhand : ∑ v : Fin n, G.degree v = 2 * (2 * (n - 2)) := by
    rw [G.sum_degrees_eq_twice_card_edges, hm]
  have hcard3 : (deg3Set G).card = 8 + excessX n G :=
    deg3_card_eq_eight_add_excess n G (by omega) hm h3
  have hdisj : Disjoint (hubSet G) (deg3Set G) := by
    rw [Finset.disjoint_left]
    intro v hv hv'
    rw [mem_hubSet] at hv
    rw [mem_deg3Set] at hv'
    omega
  have hunion : hubSet G ∪ deg3Set G = Finset.univ := by
    ext v
    simp only [Finset.mem_union, mem_hubSet, mem_deg3Set, Finset.mem_univ, iff_true]
    have := h3 v
    omega
  have hd3sum : ∑ t ∈ deg3Set G, G.degree t = 3 * (deg3Set G).card := by
    have hc : ∑ t ∈ deg3Set G, G.degree t = ∑ _t ∈ deg3Set G, 3 :=
      Finset.sum_congr rfl (fun t ht => mem_deg3Set.mp ht)
    rw [hc, Finset.sum_const, smul_eq_mul, mul_comm]
  have hpart : ∑ h ∈ hubSet G, G.degree h + ∑ t ∈ deg3Set G, G.degree t
      = ∑ v : Fin n, G.degree v := by
    rw [← Finset.sum_union hdisj, hunion]
  have hHubsum : ∑ h ∈ hubSet G, G.degree h + 3 * excessX n G + 32 = 4 * n := by
    omega
  -- the owner set, the saturated degree-`5` set, and the non-owner non-saturated hubs
  set D4 := (hubSet G).filter (fun h => G.degree h = 4) with hD4def
  set O := D4.filter (fun h => (G.neighborFinset h ∩ isoTwins G).Nonempty) with hOdef
  set P := (hubSet G).filter (fun h => G.degree h = 5 ∧
    (G.neighborFinset h ∩ isoTwins G).card = 2) with hPdef
  set SP := O ∪ P with hSPdef
  set NH := hubSet G \ SP with hNHdef
  have hOsubD4 : O ⊆ D4 := Finset.filter_subset _ _
  have hD4subHub : D4 ⊆ hubSet G := Finset.filter_subset _ _
  have hOsubHub : O ⊆ hubSet G := hOsubD4.trans hD4subHub
  have hPsubHub : P ⊆ hubSet G := Finset.filter_subset _ _
  have hSPsubHub : SP ⊆ hubSet G := by
    rw [hSPdef]; exact Finset.union_subset hOsubHub hPsubHub
  have hOPdisj : Disjoint O P := by
    rw [Finset.disjoint_left]
    intro x hxO hxP
    have hx4 : G.degree x = 4 := by
      have hxD4 := hOsubD4 hxO
      rw [hD4def, Finset.mem_filter] at hxD4
      exact hxD4.2
    have hx5 : G.degree x = 5 := by
      rw [hPdef, Finset.mem_filter] at hxP
      exact hxP.2.1
    omega
  -- `t₄ = |O|` via the degree-`4` twin cap
  have ht4 : ∑ h ∈ D4, (G.neighborFinset h ∩ isoTwins G).card = O.card := by
    rw [hOdef, Finset.card_filter]
    refine Finset.sum_congr rfl (fun h hh => ?_)
    rw [hD4def, Finset.mem_filter] at hh
    by_cases hne : (G.neighborFinset h ∩ isoTwins G).Nonempty
    · rw [if_pos hne]
      have hle := hcap4 h hh.2
      have hge := Finset.card_pos.mpr hne
      omega
    · rw [if_neg hne]
      exact Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hne)
  -- each owner has exactly three non-owner non-saturated hub neighbours
  have hsliceO : ∀ o ∈ O, (G.neighborFinset o ∩ NH).card = 3 := by
    intro o ho
    have hoD4 : o ∈ D4 := hOsubD4 ho
    rw [hOdef, Finset.mem_filter] at ho
    obtain ⟨_, hoNE⟩ := ho
    rw [hD4def, Finset.mem_filter] at hoD4
    obtain ⟨_, hodeg⟩ := hoD4
    have hiso1 : (G.neighborFinset o ∩ isoTwins G).card = 1 := by
      have hle := hcap4 o hodeg
      have hge := Finset.card_pos.mpr hoNE
      omega
    have hseteq : G.neighborFinset o ∩ NH = G.neighborFinset o \ isoTwins G := by
      ext x
      constructor
      · intro hx
        rw [Finset.mem_inter] at hx
        obtain ⟨hxN, hxNH⟩ := hx
        rw [hNHdef, Finset.mem_sdiff] at hxNH
        obtain ⟨hxHub, _⟩ := hxNH
        rw [Finset.mem_sdiff]
        refine ⟨hxN, ?_⟩
        intro hxIso
        have hd3 : G.degree x = 3 := (mem_isoTwins.mp hxIso).1
        rw [mem_hubSet] at hxHub
        omega
      · intro hx
        rw [Finset.mem_sdiff] at hx
        obtain ⟨hxN, hxIso⟩ := hx
        have hAdj : G.Adj o x := (G.mem_neighborFinset o x).mp hxN
        have hdeg_x_ne3 : G.degree x ≠ 3 := by
          intro h3x
          apply hxIso
          have hmem : x ∈ deg3Set G := mem_deg3Set.mpr h3x
          rwa [deg3_eq_isoTwins_of_s0 G hs0] at hmem
        have hxHub : x ∈ hubSet G := by
          rw [mem_hubSet]; have := h3 x; omega
        have hxSP : x ∉ SP := by
          rw [hSPdef, Finset.mem_union, not_or]
          refine ⟨?_, ?_⟩
          · intro hxO
            have hxD4 : x ∈ D4 := hOsubD4 hxO
            rw [hOdef, Finset.mem_filter] at hxO
            obtain ⟨_, hxNE⟩ := hxO
            rw [hD4def, Finset.mem_filter] at hxD4
            obtain ⟨_, hxdeg⟩ := hxD4
            exact hindep44 o x hodeg hxdeg hoNE hxNE (G.ne_of_adj hAdj) hAdj
          · intro hxP
            rw [hPdef, Finset.mem_filter] at hxP
            obtain ⟨_, hx5, hx2⟩ := hxP
            exact hindep45 o x hodeg hoNE hx5 hx2 hAdj
        rw [Finset.mem_inter, hNHdef, Finset.mem_sdiff]
        exact ⟨hxN, hxHub, hxSP⟩
    rw [hseteq]
    have hsum := Finset.card_inter_add_card_sdiff (G.neighborFinset o) (isoTwins G)
    rw [hiso1, G.card_neighborFinset_eq_degree, hodeg] at hsum
    omega
  -- each saturated degree-`5` has exactly three non-owner non-saturated hub neighbours
  have hsliceP : ∀ s ∈ P, (G.neighborFinset s ∩ NH).card = 3 := by
    intro s hs
    rw [hPdef, Finset.mem_filter] at hs
    obtain ⟨_, hs5, hs2⟩ := hs
    have hseteq : G.neighborFinset s ∩ NH = G.neighborFinset s \ isoTwins G := by
      ext x
      constructor
      · intro hx
        rw [Finset.mem_inter] at hx
        obtain ⟨hxN, hxNH⟩ := hx
        rw [hNHdef, Finset.mem_sdiff] at hxNH
        obtain ⟨hxHub, _⟩ := hxNH
        rw [Finset.mem_sdiff]
        refine ⟨hxN, ?_⟩
        intro hxIso
        have hd3 : G.degree x = 3 := (mem_isoTwins.mp hxIso).1
        rw [mem_hubSet] at hxHub
        omega
      · intro hx
        rw [Finset.mem_sdiff] at hx
        obtain ⟨hxN, hxIso⟩ := hx
        have hAdj : G.Adj s x := (G.mem_neighborFinset s x).mp hxN
        have hdeg_x_ne3 : G.degree x ≠ 3 := by
          intro h3x
          apply hxIso
          have hmem : x ∈ deg3Set G := mem_deg3Set.mpr h3x
          rwa [deg3_eq_isoTwins_of_s0 G hs0] at hmem
        have hxHub : x ∈ hubSet G := by
          rw [mem_hubSet]; have := h3 x; omega
        have hxSP : x ∉ SP := by
          rw [hSPdef, Finset.mem_union, not_or]
          refine ⟨?_, ?_⟩
          · intro hxO
            have hxD4 : x ∈ D4 := hOsubD4 hxO
            rw [hOdef, Finset.mem_filter] at hxO
            obtain ⟨_, hxNE⟩ := hxO
            rw [hD4def, Finset.mem_filter] at hxD4
            obtain ⟨_, hxdeg⟩ := hxD4
            exact hindep45 x s hxdeg hxNE hs5 hs2 hAdj.symm
          · intro hxP
            rw [hPdef, Finset.mem_filter] at hxP
            obtain ⟨_, hx5, hx2⟩ := hxP
            exact hindep55 s x hs5 hs2 hx5 hx2 (G.ne_of_adj hAdj) hAdj
        rw [Finset.mem_inter, hNHdef, Finset.mem_sdiff]
        exact ⟨hxN, hxHub, hxSP⟩
    rw [hseteq]
    have hsum := Finset.card_inter_add_card_sdiff (G.neighborFinset s) (isoTwins G)
    rw [hs2, G.card_neighborFinset_eq_degree, hs5] at hsum
    omega
  -- the joint slice count `∑_{O ∪ P} |N(·) ∩ NH| = 3·|O| + 3·|P|`
  have hslicesum : ∑ v ∈ SP, (G.neighborFinset v ∩ NH).card = 3 * O.card + 3 * P.card := by
    have e1 : ∑ v ∈ O, (G.neighborFinset v ∩ NH).card = 3 * O.card := by
      rw [Finset.sum_congr rfl hsliceO, Finset.sum_const, smul_eq_mul, mul_comm]
    have e2 : ∑ v ∈ P, (G.neighborFinset v ∩ NH).card = 3 * P.card := by
      rw [Finset.sum_congr rfl hsliceP, Finset.sum_const, smul_eq_mul, mul_comm]
    rw [hSPdef, Finset.sum_union hOPdisj, e1, e2]
  -- transpose the count and cap it by the non-owner-non-saturated hub degree total
  have hcc := cross_count G SP NH
  have hcap2 : ∑ w ∈ NH, (G.neighborFinset w ∩ SP).card ≤ ∑ w ∈ NH, G.degree w := by
    refine Finset.sum_le_sum (fun w _ => ?_)
    calc (G.neighborFinset w ∩ SP).card ≤ (G.neighborFinset w).card :=
          Finset.card_le_card Finset.inter_subset_left
      _ = G.degree w := G.card_neighborFinset_eq_degree w
  have hOdeg : ∑ o ∈ O, G.degree o = 4 * O.card := by
    have hpt : ∀ o ∈ O, G.degree o = 4 := by
      intro o ho
      have hoD4 : o ∈ D4 := hOsubD4 ho
      rw [hD4def, Finset.mem_filter] at hoD4
      exact hoD4.2
    rw [Finset.sum_congr rfl hpt, Finset.sum_const, smul_eq_mul, mul_comm]
  have hPdeg : ∑ s ∈ P, G.degree s = 5 * P.card := by
    have hpt : ∀ s ∈ P, G.degree s = 5 := by
      intro s hs
      rw [hPdef, Finset.mem_filter] at hs
      exact hs.2.1
    rw [Finset.sum_congr rfl hpt, Finset.sum_const, smul_eq_mul, mul_comm]
  have hSPdeg : ∑ v ∈ SP, G.degree v = 4 * O.card + 5 * P.card := by
    rw [hSPdef, Finset.sum_union hOPdisj, hOdeg, hPdeg]
  have hNHsum : ∑ w ∈ NH, G.degree w + ∑ v ∈ SP, G.degree v
      = ∑ h ∈ hubSet G, G.degree h := by
    rw [hNHdef]
    exact Finset.sum_sdiff hSPsubHub
  rw [ht4]
  omega

/-- **The `(4,5)` decorated-edge independence.**  In a never-firing starved census
(`m = 2(n−2)`, `δ ≥ 3`) at `n ≥ 39`, a degree-`4` owner `o` (carrying a twin) and a saturated
degree-`5` hub `s` (owning exactly `2` twins) are non-adjacent.  If they were adjacent: a shared
twin makes `{o, s, t}` a degree-`(4,5,3)` triangle (`Σdeg = 12 = 4·3`) firing `master_cycle_fires`
(`n ≥ 19`); distinct twins fire the `(4,5)` decorated edge `deco_edge_moat_fires`
(`9·(4 + 5) = 81 ≤ n + 42`, i.e. `n ≥ 39`) — either way contradicting `¬ algConn G ≤ 2`. -/
theorem owner_sat_independence {n : ℕ} [Nonempty (Fin n)] (hn : 39 ≤ n)
    (G : SimpleGraph (Fin n)) (hm : G.edgeFinset.card = 2 * (n - 2))
    (h3 : ∀ v : Fin n, 3 ≤ G.degree v) (hnf : ¬ algConn G ≤ 2)
    (o s : Fin n) (hdo : G.degree o = 4) (hds : G.degree s = 5)
    (hoNE : (G.neighborFinset o ∩ isoTwins G).Nonempty)
    (hscard : (G.neighborFinset s ∩ isoTwins G).card = 2) :
    ¬ G.Adj o s := by
  classical
  intro hadj
  apply hnf
  obtain ⟨t, ht⟩ := hoNE
  rw [Finset.mem_inter] at ht
  obtain ⟨htN, htIso⟩ := ht
  have hot : G.Adj o t := (G.mem_neighborFinset o t).mp htN
  have hdt : G.degree t = 3 := (mem_isoTwins.mp htIso).1
  have hne_st : s ≠ t := by intro h; rw [h, hdt] at hds; omega
  set Ks := G.neighborFinset s ∩ isoTwins G with hKsdef
  by_cases htin : t ∈ Ks
  · have hst : G.Adj s t := by
      rw [hKsdef, Finset.mem_inter] at htin
      exact (G.mem_neighborFinset s t).mp htin.1
    have hne_os : o ≠ s := by intro h; rw [h, hds] at hdo; omega
    have hne_ot : o ≠ t := by intro h; rw [h, hdt] at hdo; omega
    have e0 : (![o, s, t] : Fin 3 → Fin n) 0 = o := rfl
    have e1 : (![o, s, t] : Fin 3 → Fin n) 1 = s := rfl
    have e2 : (![o, s, t] : Fin 3 → Fin n) 2 = t := rfl
    refine master_cycle_fires (k := 3) (by norm_num) G hm h3 ![o, s, t] ?_ ?_ ?_ ?_
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all <;> rfl
    · intro i
      fin_cases i
      · show G.Adj o s; exact hadj
      · show G.Adj s t; exact hst
      · show G.Adj t o; exact hot.symm
    · have hsplit : (∑ i : ZMod 3, G.degree (![o, s, t] i))
          = G.degree o + G.degree s + G.degree t := by
        have h := Fin.sum_univ_three (fun i : Fin 3 => G.degree (![o, s, t] i))
        rw [e0, e1, e2] at h
        exact h
      rw [hsplit, hdo, hds, hdt]
    · have hsplit : (∑ i : ZMod 3, (G.degree (![o, s, t] i) - 1))
          = (G.degree o - 1) + (G.degree s - 1) + (G.degree t - 1) := by
        have h := Fin.sum_univ_three (fun i : Fin 3 => G.degree (![o, s, t] i) - 1)
        rw [e0, e1, e2] at h
        exact h
      rw [hsplit, hdo, hds, hdt]; omega
  · refine deco_edge_moat_fires G hm h3 o s {t} Ks hadj ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro x hx
      rw [Finset.mem_singleton] at hx
      subst hx
      rw [G.mem_neighborFinset]; exact hot
    · intro x hx
      rw [Finset.mem_singleton] at hx
      subst hx; exact hdt
    · rw [Finset.card_singleton, hdo]
    · rw [hKsdef]; exact Finset.inter_subset_left
    · intro x hx
      rw [hKsdef, Finset.mem_inter] at hx
      exact (mem_isoTwins.mp hx.2).1
    · rw [hscard, hds]
    · intro hoKs
      rw [hKsdef, Finset.mem_inter] at hoKs
      have := (mem_isoTwins.mp hoKs.2).1
      omega
    · rw [Finset.mem_singleton]; exact hne_st
    · rw [Finset.disjoint_singleton_left]; exact htin
    · rw [hdo, hds]; omega

/-- **N5 — the per-`p` sharpened owner-choke (assembled row).**  A never-firing starved census
(`m = 2(n−2)`, `δ ≥ 3`, `hs0`) on `n ≥ 48` satisfies the sharpened choke
`7·t₄ + 8·p + 3·X + 32 ≤ 4n`.  The degree-`4` twin cap is the contrapositive of the star moat
(`starved_cap` at `deg = 4`), the `(4,4)` independence is `owner_independence`, and the `(4,5)`
independence is `owner_sat_independence`; the `(5,5)` independence `hindep55` is threaded as the
single moat-provenance hypothesis (its shared-single-twin subcase requires a shared-twin
decorated-edge moat, a separate node — `scratchpad/ahl_import.md` §1.3/§4.4). -/
theorem p_choke_row {n : ℕ} [Nonempty (Fin n)] (hn : 48 ≤ n)
    (G : SimpleGraph (Fin n)) (hm : G.edgeFinset.card = 2 * (n - 2))
    (h3 : ∀ v : Fin n, 3 ≤ G.degree v)
    (hs0 : ∀ v w : Fin n, G.degree v = 3 → G.degree w = 3 → ¬G.Adj v w)
    (hnf : ¬ algConn G ≤ 2)
    (hindep55 : ∀ s₁ s₂ : Fin n, G.degree s₁ = 5 →
        (G.neighborFinset s₁ ∩ isoTwins G).card = 2 → G.degree s₂ = 5 →
        (G.neighborFinset s₂ ∩ isoTwins G).card = 2 → s₁ ≠ s₂ → ¬ G.Adj s₁ s₂) :
    7 * (∑ h ∈ (hubSet G).filter (fun h => G.degree h = 4),
            (G.neighborFinset h ∩ isoTwins G).card)
        + 8 * ((hubSet G).filter (fun h => G.degree h = 5 ∧
            (G.neighborFinset h ∩ isoTwins G).card = 2)).card
        + 3 * excessX n G + 32 ≤ 4 * n := by
  have hcap4 : ∀ h : Fin n, G.degree h = 4 →
      (G.neighborFinset h ∩ isoTwins G).card ≤ 1 := by
    intro h hh
    have hc := starved_cap G hm h3 hnf h (by rw [hh]; omega)
    rw [hh] at hc
    omega
  have hindep44 : ∀ o₁ o₂ : Fin n, G.degree o₁ = 4 → G.degree o₂ = 4 →
      (G.neighborFinset o₁ ∩ isoTwins G).Nonempty →
      (G.neighborFinset o₂ ∩ isoTwins G).Nonempty → o₁ ≠ o₂ → ¬ G.Adj o₁ o₂ := by
    intro o₁ o₂ ho1 ho2 hn1 hn2 _hne
    obtain ⟨t₁, ht1⟩ := hn1
    obtain ⟨t₂, ht2⟩ := hn2
    rw [Finset.mem_inter, G.mem_neighborFinset] at ht1 ht2
    exact owner_independence (by omega) G hm h3 hnf o₁ o₂ t₁ t₂ ho1 ho2 ht1.1
      (mem_isoTwins.mp ht1.2).1 ht2.1 (mem_isoTwins.mp ht2.2).1
  have hindep45 : ∀ o s : Fin n, G.degree o = 4 →
      (G.neighborFinset o ∩ isoTwins G).Nonempty → G.degree s = 5 →
      (G.neighborFinset s ∩ isoTwins G).card = 2 → ¬ G.Adj o s := by
    intro o s ho hoNE hs hscard
    exact owner_sat_independence (by omega) G hm h3 hnf o s ho hs hoNE hscard
  exact p_choke_count (by omega) G hm h3 hs0 hcap4 hindep44 hindep45 hindep55

/-! ## The shared-twin decorated-edge moat and the unconditional row

Reworks the decorated-edge moat for the overlapping-twin case and discharges the
last hypothesis of the per-`p` owner-choke. `deco_edge_shared_twin_fires`: adjacent
hubs sharing exactly one twin fire at `9·(deg u + deg v) ≤ n + 56` (the shared
twin has external budget `1`, so the threshold is easier than the disjoint
`n + 42`). `sat_sat_independence`: two adjacent saturated degree-5 hubs are
non-adjacent at `n ≥ 48`. `p_choke_row_unconditional`: the census-only per-`p`
choke row, discharging `hindep55` via `sat_sat_independence`. -/

/-- **The shared-twin decorated-edge moat certificate.**  A graph on `Fin n` with `2(n−2)` edges,
minimum degree `≥ 3`, adjacent hubs `u, v`, and twin sets `Ku ⊆ N(u)`, `Kv ⊆ N(v)` of degree-`3`
vertices with `|Ku| = deg u − 3`, `|Kv| = deg v − 3` (avoiding the opposite hub) sharing *exactly
one* common twin (`Ku ∩ Kv = {t₀}`) has `algConn G ≤ 2` whenever `9·(deg u + deg v) ≤ n + 56`.

Instantiate the two-cluster law with the tie-block `S₁ = {u, v} ∪ Ku ∪ Kv` (`|S₁| = deg u +
deg v − 5`) against the bulk `S₂ = (S₁ ∪ F)ᶜ`, `F = (⋃_{x ∈ S₁} N(x)) ∖ S₁` the moat: every hub
slice loses `deg − 2` internally (budget `2`) and every twin loses its hub (budget `2`), except the
shared twin `t₀` which loses *both* hubs (budget `1`), so `|F| + 1 ≤ 2·|S₁|`; the pair-credited
excess ledger then gives `∂₂ ≤ 2·|S₂|` and the Fiedler cut condition closes by `ring`. -/
theorem deco_edge_shared_twin_fires {n : ℕ} [Nonempty (Fin n)]
    (G : SimpleGraph (Fin n)) (hm : G.edgeFinset.card = 2 * (n - 2))
    (h3 : ∀ w : Fin n, 3 ≤ G.degree w) (u v t₀ : Fin n) (Ku Kv : Finset (Fin n))
    (huv : G.Adj u v)
    (hKusub : Ku ⊆ G.neighborFinset u) (hKudeg : ∀ t ∈ Ku, G.degree t = 3)
    (hKucard : Ku.card = G.degree u - 3)
    (hKvsub : Kv ⊆ G.neighborFinset v) (hKvdeg : ∀ t ∈ Kv, G.degree t = 3)
    (hKvcard : Kv.card = G.degree v - 3)
    (huKv : u ∉ Kv) (hvKu : v ∉ Ku) (hshare : Ku ∩ Kv = {t₀})
    (hfire : 9 * (G.degree u + G.degree v) ≤ n + 56) :
    algConn G ≤ 2 := by
  classical
  -- process the overlap hypothesis in the canonical `Fin` instance, before switching to
  -- the classical instance the two-cluster law expects
  have ht0mem : t₀ ∈ Ku ∩ Kv := by rw [hshare]; exact Finset.mem_singleton_self t₀
  have ht0Ku : t₀ ∈ Ku := Finset.mem_of_mem_inter_left ht0mem
  have ht0Kv : t₀ ∈ Kv := Finset.mem_of_mem_inter_right ht0mem
  have huniq : ∀ a : Fin n, a ∈ Ku → a ∈ Kv → a = t₀ := by
    intro a ha hb
    have hmem : a ∈ Ku ∩ Kv := Finset.mem_inter.mpr ⟨ha, hb⟩
    rw [hshare] at hmem
    exact Finset.mem_singleton.mp hmem
  let : DecidableEq (Fin n) := Classical.decEq (Fin n)
  have hdeg3u : 3 ≤ G.degree u := h3 u
  have hdeg3v : 3 ≤ G.degree v := h3 v
  have huv' : u ≠ v := G.ne_of_adj huv
  have hdt0 : G.degree t₀ = 3 := hKudeg t₀ ht0Ku
  have hKupos : 1 ≤ Ku.card := Finset.card_pos.mpr ⟨t₀, ht0Ku⟩
  have hKvpos : 1 ≤ Kv.card := Finset.card_pos.mpr ⟨t₀, ht0Kv⟩
  have hn8 : 8 ≤ n := by omega
  have hshare' : Ku ∩ Kv = {t₀} := by
    ext a
    simp only [Finset.mem_inter, Finset.mem_singleton]
    constructor
    · rintro ⟨ha, hb⟩
      exact huniq a ha hb
    · rintro rfl
      exact ⟨ht0Ku, ht0Kv⟩
  have huKu : u ∉ Ku := by
    intro hu
    have hmem := hKusub hu
    rw [G.mem_neighborFinset] at hmem
    exact (G.ne_of_adj hmem) rfl
  have hvKv : v ∉ Kv := by
    intro hv
    have hmem := hKvsub hv
    rw [G.mem_neighborFinset] at hmem
    exact (G.ne_of_adj hmem) rfl
  set S₁ : Finset (Fin n) := insert u (insert v (Ku ∪ Kv)) with hS1def
  set F : Finset (Fin n) := (S₁.biUnion (fun x => G.neighborFinset x)) \ S₁ with hFdef
  set S₂ : Finset (Fin n) := (S₁ ∪ F)ᶜ with hS2def
  have hu_notin : u ∉ insert v (Ku ∪ Kv) := by
    rw [Finset.mem_insert, Finset.mem_union]
    rintro (h | h | h)
    · exact huv' h
    · exact huKu h
    · exact huKv h
  have hv_notin : v ∉ Ku ∪ Kv := by
    rw [Finset.mem_union]
    rintro (h | h)
    · exact hvKu h
    · exact hvKv h
  have hunioncard : (Ku ∪ Kv).card = Ku.card + Kv.card - 1 := by
    have h := Finset.card_union_add_card_inter Ku Kv
    rw [hshare', Finset.card_singleton] at h
    omega
  have hS1card : S₁.card = G.degree u + G.degree v - 5 := by
    rw [hS1def, Finset.card_insert_of_notMem hu_notin,
      Finset.card_insert_of_notMem hv_notin, hunioncard, hKucard, hKvcard]
    omega
  have hS1ne : S₁.Nonempty := by rw [hS1def]; exact Finset.insert_nonempty u _
  have huF : u ∉ F := by
    rw [hFdef]
    intro hmem
    rw [Finset.mem_sdiff] at hmem
    exact hmem.2 (by rw [hS1def]; exact Finset.mem_insert_self u _)
  have hvF : v ∉ F := by
    rw [hFdef]
    intro hmem
    rw [Finset.mem_sdiff] at hmem
    exact hmem.2 (by rw [hS1def]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self v _))
  have hdisjS1F : Disjoint S₁ F := by
    rw [Finset.disjoint_left]
    intro a ha haF
    rw [hFdef, Finset.mem_sdiff] at haF
    exact haF.2 ha
  have hS2card : S₂.card = n - (S₁.card + F.card) := by
    rw [hS2def, Finset.card_compl, Fintype.card_fin,
      Finset.card_union_of_disjoint hdisjS1F]
  have hcnt : ∀ (A C : Finset (Fin n)),
      ((A ×ˢ C).filter (fun q => G.Adj q.1 q.2)).card
        = ∑ a ∈ A, (G.neighborFinset a ∩ C).card := by
    intro A C
    rw [Finset.card_filter, Finset.sum_product]
    refine Finset.sum_congr rfl fun a _ => ?_
    have hset : G.neighborFinset a ∩ C = C.filter (fun v => G.Adj a v) := by
      ext v
      simp only [Finset.mem_inter, Finset.mem_filter, SimpleGraph.mem_neighborFinset]
      exact and_comm
    rw [hset, Finset.card_filter]
  have htrans : ∀ (A C : Finset (Fin n)),
      ((A ×ˢ C).filter (fun q => G.Adj q.1 q.2)).card
        = ((C ×ˢ A).filter (fun q => G.Adj q.1 q.2)).card := by
    intro A C
    refine Finset.card_bij (fun q _ => (q.2, q.1)) ?_ ?_ ?_
    · intro q hq
      rw [Finset.mem_filter, Finset.mem_product] at hq ⊢
      exact ⟨⟨hq.1.2, hq.1.1⟩, G.adj_symm hq.2⟩
    · intro q _ r _ hqr
      exact Prod.ext (congrArg Prod.snd hqr) (congrArg Prod.fst hqr)
    · intro q hq
      refine ⟨(q.2, q.1), ?_, rfl⟩
      rw [Finset.mem_filter, Finset.mem_product] at hq ⊢
      exact ⟨⟨hq.1.2, hq.1.1⟩, G.adj_symm hq.2⟩
  have hsliceU : (G.neighborFinset u \ S₁).card ≤ 2 := by
    have hivku_nb : insert v Ku ⊆ G.neighborFinset u :=
      Finset.insert_subset ((G.mem_neighborFinset u v).mpr huv) hKusub
    have hivku_S1 : insert v Ku ⊆ S₁ := by
      refine Finset.insert_subset ?_ ?_
      · rw [hS1def]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self v _)
      · intro x hxKu
        rw [hS1def]
        exact Finset.mem_insert_of_mem
          (Finset.mem_insert_of_mem (Finset.mem_union_left Kv hxKu))
    have hsub : G.neighborFinset u \ S₁ ⊆ G.neighborFinset u \ insert v Ku :=
      Finset.sdiff_subset_sdiff (le_refl _) hivku_S1
    calc (G.neighborFinset u \ S₁).card
        ≤ (G.neighborFinset u \ insert v Ku).card := Finset.card_le_card hsub
      _ = (G.neighborFinset u).card - (insert v Ku).card :=
          Finset.card_sdiff_of_subset hivku_nb
      _ = G.degree u - (insert v Ku).card := by rw [G.card_neighborFinset_eq_degree]
      _ = 2 := by rw [Finset.card_insert_of_notMem hvKu, hKucard]; omega
  have hsliceV : (G.neighborFinset v \ S₁).card ≤ 2 := by
    have hiukv_nb : insert u Kv ⊆ G.neighborFinset v :=
      Finset.insert_subset ((G.mem_neighborFinset v u).mpr huv.symm) hKvsub
    have hiukv_S1 : insert u Kv ⊆ S₁ := by
      refine Finset.insert_subset ?_ ?_
      · rw [hS1def]; exact Finset.mem_insert_self u _
      · intro x hxKv
        rw [hS1def]
        exact Finset.mem_insert_of_mem
          (Finset.mem_insert_of_mem (Finset.mem_union_right Ku hxKv))
    have hsub : G.neighborFinset v \ S₁ ⊆ G.neighborFinset v \ insert u Kv :=
      Finset.sdiff_subset_sdiff (le_refl _) hiukv_S1
    calc (G.neighborFinset v \ S₁).card
        ≤ (G.neighborFinset v \ insert u Kv).card := Finset.card_le_card hsub
      _ = (G.neighborFinset v).card - (insert u Kv).card :=
          Finset.card_sdiff_of_subset hiukv_nb
      _ = G.degree v - (insert u Kv).card := by rw [G.card_neighborFinset_eq_degree]
      _ = 2 := by rw [Finset.card_insert_of_notMem huKv, hKvcard]; omega
  have hsliceTu : ∀ t ∈ Ku, (G.neighborFinset t \ S₁).card ≤ 2 := by
    intro t htK
    have htNu : t ∈ G.neighborFinset u := hKusub htK
    have hut : G.Adj u t := (G.mem_neighborFinset u t).mp htNu
    have huNt : u ∈ G.neighborFinset t := (G.mem_neighborFinset t u).mpr hut.symm
    have hsub : G.neighborFinset t \ S₁ ⊆ (G.neighborFinset t).erase u := by
      intro x hx
      rw [Finset.mem_sdiff] at hx
      rw [Finset.mem_erase]
      refine ⟨fun hxu => hx.2 ?_, hx.1⟩
      rw [hS1def, hxu]
      exact Finset.mem_insert_self u _
    calc (G.neighborFinset t \ S₁).card
        ≤ ((G.neighborFinset t).erase u).card := Finset.card_le_card hsub
      _ = G.degree t - 1 := by
          rw [Finset.card_erase_of_mem huNt, G.card_neighborFinset_eq_degree]
      _ = 2 := by rw [hKudeg t htK]
  have hsliceTv : ∀ t ∈ Kv, (G.neighborFinset t \ S₁).card ≤ 2 := by
    intro t htK
    have htNv : t ∈ G.neighborFinset v := hKvsub htK
    have hvt : G.Adj v t := (G.mem_neighborFinset v t).mp htNv
    have hvNt : v ∈ G.neighborFinset t := (G.mem_neighborFinset t v).mpr hvt.symm
    have hsub : G.neighborFinset t \ S₁ ⊆ (G.neighborFinset t).erase v := by
      intro x hx
      rw [Finset.mem_sdiff] at hx
      rw [Finset.mem_erase]
      refine ⟨fun hxv => hx.2 ?_, hx.1⟩
      rw [hS1def, hxv]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_self v _)
    calc (G.neighborFinset t \ S₁).card
        ≤ ((G.neighborFinset t).erase v).card := Finset.card_le_card hsub
      _ = G.degree t - 1 := by
          rw [Finset.card_erase_of_mem hvNt, G.card_neighborFinset_eq_degree]
      _ = 2 := by rw [hKvdeg t htK]
  have hslice : ∀ x ∈ S₁, (G.neighborFinset x \ S₁).card ≤ 2 := by
    intro x hx
    rw [hS1def, Finset.mem_insert, Finset.mem_insert, Finset.mem_union] at hx
    rcases hx with rfl | rfl | hxKu | hxKv
    · exact hsliceU
    · exact hsliceV
    · exact hsliceTu x hxKu
    · exact hsliceTv x hxKv
  have hsliceT0 : (G.neighborFinset t₀ \ S₁).card ≤ 1 := by
    have hut0 : G.Adj u t₀ := (G.mem_neighborFinset u t₀).mp (hKusub ht0Ku)
    have hvt0 : G.Adj v t₀ := (G.mem_neighborFinset v t₀).mp (hKvsub ht0Kv)
    have huNt0 : u ∈ G.neighborFinset t₀ := (G.mem_neighborFinset t₀ u).mpr hut0.symm
    have hvNt0 : v ∈ G.neighborFinset t₀ := (G.mem_neighborFinset t₀ v).mpr hvt0.symm
    have huvsub : ({u, v} : Finset (Fin n)) ⊆ G.neighborFinset t₀ := by
      intro x hx
      rw [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact huNt0
      · exact hvNt0
    have huvS1 : ({u, v} : Finset (Fin n)) ⊆ S₁ := by
      intro x hx
      rw [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with hxu | hxv
      · rw [hxu, hS1def]; exact Finset.mem_insert_self u _
      · rw [hxv, hS1def]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self v _)
    have hsub : G.neighborFinset t₀ \ S₁ ⊆ G.neighborFinset t₀ \ {u, v} :=
      Finset.sdiff_subset_sdiff (le_refl _) huvS1
    calc (G.neighborFinset t₀ \ S₁).card
        ≤ (G.neighborFinset t₀ \ {u, v}).card := Finset.card_le_card hsub
      _ = G.degree t₀ - 2 := by
          rw [Finset.card_sdiff_of_subset huvsub, G.card_neighborFinset_eq_degree,
            Finset.card_pair_eq_two_iff.mpr huv']
      _ = 1 := by rw [hdt0]
  have hterm : ∀ a ∈ S₁, (G.neighborFinset a ∩ F).card ≤ 2 := by
    intro a ha
    have hsub : G.neighborFinset a ∩ F ⊆ G.neighborFinset a \ S₁ := by
      intro x hx
      rw [Finset.mem_inter] at hx
      rw [Finset.mem_sdiff]
      refine ⟨hx.1, ?_⟩
      have hxF := hx.2
      rw [hFdef, Finset.mem_sdiff] at hxF
      exact hxF.2
    exact le_trans (Finset.card_le_card hsub) (hslice a ha)
  have he1 : ((S₁ ×ˢ F).filter (fun q => G.Adj q.1 q.2)).card ≤ 2 * S₁.card := by
    rw [hcnt S₁ F]
    calc ∑ a ∈ S₁, (G.neighborFinset a ∩ F).card
        ≤ ∑ _a ∈ S₁, 2 := Finset.sum_le_sum hterm
      _ = 2 * S₁.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have ht0S1 : t₀ ∈ S₁ := by
    rw [hS1def]
    exact Finset.mem_insert_of_mem
      (Finset.mem_insert_of_mem (Finset.mem_union_left Kv ht0Ku))
  have hsumbound : ∑ x ∈ S₁, (G.neighborFinset x \ S₁).card + 1 ≤ 2 * S₁.card := by
    have hsplit : (G.neighborFinset t₀ \ S₁).card
        + ∑ x ∈ S₁.erase t₀, (G.neighborFinset x \ S₁).card
        = ∑ x ∈ S₁, (G.neighborFinset x \ S₁).card :=
      Finset.add_sum_erase S₁ (fun x => (G.neighborFinset x \ S₁).card) ht0S1
    have herase : ∑ x ∈ S₁.erase t₀, (G.neighborFinset x \ S₁).card
        ≤ 2 * (S₁.erase t₀).card := by
      calc ∑ x ∈ S₁.erase t₀, (G.neighborFinset x \ S₁).card
          ≤ ∑ _x ∈ S₁.erase t₀, 2 :=
            Finset.sum_le_sum (fun x hx => hslice x (Finset.mem_of_mem_erase hx))
        _ = 2 * (S₁.erase t₀).card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    have hcarderase : (S₁.erase t₀).card = S₁.card - 1 := Finset.card_erase_of_mem ht0S1
    have hS1pos : 1 ≤ S₁.card := Finset.card_pos.mpr ⟨t₀, ht0S1⟩
    omega
  have hFcard : F.card + 1 ≤ 2 * S₁.card := by
    have hFsub2 : F ⊆ S₁.biUnion (fun x => G.neighborFinset x \ S₁) := by
      intro y hy
      rw [hFdef, Finset.mem_sdiff] at hy
      obtain ⟨hyNS, hyS1⟩ := hy
      rw [Finset.mem_biUnion] at hyNS ⊢
      obtain ⟨x, hxS1, hyx⟩ := hyNS
      exact ⟨x, hxS1, Finset.mem_sdiff.mpr ⟨hyx, hyS1⟩⟩
    have hFle : F.card ≤ ∑ x ∈ S₁, (G.neighborFinset x \ S₁).card :=
      le_trans (Finset.card_le_card hFsub2) Finset.card_biUnion_le
    omega
  have hFsubErase : F ⊆ (Finset.univ.erase u).erase v := by
    intro x hx
    rw [Finset.mem_erase, Finset.mem_erase]
    refine ⟨?_, ?_, Finset.mem_univ x⟩
    · rintro rfl; exact hvF hx
    · rintro rfl; exact huF hx
  have hexc : ∑ w ∈ F, (G.degree w - 3)
      ≤ (n - 8) - (G.degree u - 3) - (G.degree v - 3) := by
    have hle : ∑ w ∈ F, (G.degree w - 3)
        ≤ ∑ w ∈ (Finset.univ.erase u).erase v, (G.degree w - 3) :=
      Finset.sum_le_sum_of_subset hFsubErase
    have hsplit1 : (G.degree u - 3) + ∑ w ∈ Finset.univ.erase u, (G.degree w - 3)
        = ∑ w : Fin n, (G.degree w - 3) :=
      Finset.add_sum_erase _ (fun w => G.degree w - 3) (Finset.mem_univ u)
    have hsplit2 : (G.degree v - 3) + ∑ w ∈ (Finset.univ.erase u).erase v, (G.degree w - 3)
        = ∑ w ∈ Finset.univ.erase u, (G.degree w - 3) :=
      Finset.add_sum_erase _ (fun w => G.degree w - 3)
        (Finset.mem_erase.mpr ⟨huv'.symm, Finset.mem_univ v⟩)
    have htot : ∑ w : Fin n, (G.degree w - 3) = n - 8 := total_excess_eq hn8 G hm h3
    omega
  have hS2ne : S₂.Nonempty := by
    rw [← Finset.card_pos, hS2card]; omega
  have hdisj : Disjoint S₁ S₂ := by
    rw [Finset.disjoint_left]
    intro a ha1 ha2
    rw [hS2def, Finset.mem_compl] at ha2
    exact ha2 (Finset.mem_union_left F ha1)
  have hnc : ∀ a ∈ S₁, ∀ w ∈ S₂, ¬G.Adj a w := by
    intro a ha w hw hadj
    rw [hS2def, Finset.mem_compl] at hw
    have hwnotS1 : w ∉ S₁ := fun hh => hw (Finset.mem_union_left F hh)
    have hwnotF : w ∉ F := fun hh => hw (Finset.mem_union_right S₁ hh)
    apply hwnotF
    rw [hFdef, Finset.mem_sdiff]
    refine ⟨?_, hwnotS1⟩
    rw [Finset.mem_biUnion]
    exact ⟨a, ha, (G.mem_neighborFinset a w).mpr hadj⟩
  have hFeq : (S₁ ∪ S₂)ᶜ = F := by
    ext w
    constructor
    · intro hw
      rw [Finset.mem_compl, Finset.mem_union, not_or] at hw
      obtain ⟨hwS1, hwS2⟩ := hw
      rw [hS2def, Finset.mem_compl, not_not, Finset.mem_union] at hwS2
      rcases hwS2 with hh | hh
      · exact absurd hh hwS1
      · exact hh
    · intro hw
      rw [Finset.mem_compl, Finset.mem_union, not_or]
      exact ⟨Finset.disjoint_right.mp hdisjS1F hw,
        by rw [hS2def, Finset.mem_compl, not_not]; exact Finset.mem_union_right S₁ hw⟩
  have he2 : ((S₂ ×ˢ F).filter (fun q => G.Adj q.1 q.2)).card ≤ 2 * S₂.card := by
    rw [htrans S₂ F, hcnt F S₂]
    have hbound : ∀ w ∈ F, (G.neighborFinset w ∩ S₂).card ≤ G.degree w - 1 := by
      intro w hw
      obtain ⟨a, haS1, haw⟩ : ∃ a ∈ S₁, G.Adj a w := by
        have hwF := hw
        rw [hFdef, Finset.mem_sdiff, Finset.mem_biUnion] at hwF
        obtain ⟨⟨a, haS1, hwa⟩, _⟩ := hwF
        exact ⟨a, haS1, (G.mem_neighborFinset a w).mp hwa⟩
      have haNw : a ∈ G.neighborFinset w := (G.mem_neighborFinset w a).mpr haw.symm
      have haS2 : a ∉ S₂ := by
        rw [hS2def, Finset.mem_compl, not_not]
        exact Finset.mem_union_left F haS1
      have hsub : G.neighborFinset w ∩ S₂ ⊆ (G.neighborFinset w).erase a := by
        intro x hx
        rw [Finset.mem_inter] at hx
        rw [Finset.mem_erase]
        refine ⟨?_, hx.1⟩
        rintro rfl
        exact haS2 hx.2
      calc (G.neighborFinset w ∩ S₂).card
          ≤ ((G.neighborFinset w).erase a).card := Finset.card_le_card hsub
        _ = G.degree w - 1 := by
            rw [Finset.card_erase_of_mem haNw, G.card_neighborFinset_eq_degree]
    have hpt : ∀ w ∈ F, G.degree w - 1 = (G.degree w - 3) + 2 := by
      intro w _
      have := h3 w
      omega
    calc ∑ w ∈ F, (G.neighborFinset w ∩ S₂).card
        ≤ ∑ w ∈ F, (G.degree w - 1) := Finset.sum_le_sum hbound
      _ = ∑ w ∈ F, (G.degree w - 3) + F.card * 2 := by
          rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, Finset.sum_const,
            smul_eq_mul]
      _ ≤ 2 * S₂.card := by omega
  refine algConn_le_two_of_two_clusters G S₁ S₂ hS1ne hS2ne hdisj hnc ?_
  rw [hFeq]
  have hbound1 := Nat.mul_le_mul he1 (le_refl (S₂.card ^ 2))
  have hbound2 := Nat.mul_le_mul he2 (le_refl (S₁.card ^ 2))
  refine le_trans (add_le_add hbound1 hbound2) (le_of_eq ?_)
  ring

/-- **The `(5,5)` saturated-pair independence.**  In a never-firing starved census
(`m = 2(n−2)`, `δ ≥ 3`) at `n ≥ 48`, two saturated degree-`5` hubs `s₁, s₂` — each owning exactly
`2` `M`-isolated twins — are non-adjacent.  If they were adjacent: disjoint twin sets fire the
disjoint decorated edge (`deco_edge_moat_fires`, `90 ≤ n + 42`); one shared twin fires the
shared-twin decorated edge (`deco_edge_shared_twin_fires`, `90 ≤ n + 56`); two shared twins form a
`(5,3,5,3)` `4`-cycle `s₁, t₁, s₂, t₂` firing `master_cycle_fires` (`Σdeg = 16 = 4·4`,
`3·12 = 36 ≤ n + 8`) — either way contradicting `¬ algConn G ≤ 2`. -/
theorem sat_sat_independence {n : ℕ} [Nonempty (Fin n)] (hn : 48 ≤ n)
    (G : SimpleGraph (Fin n)) (hm : G.edgeFinset.card = 2 * (n - 2))
    (h3 : ∀ v : Fin n, 3 ≤ G.degree v) (hnf : ¬ algConn G ≤ 2)
    (s₁ s₂ : Fin n) (hd1 : G.degree s₁ = 5) (hd2 : G.degree s₂ = 5)
    (hc1 : (G.neighborFinset s₁ ∩ isoTwins G).card = 2)
    (hc2 : (G.neighborFinset s₂ ∩ isoTwins G).card = 2) (hne : s₁ ≠ s₂) :
    ¬ G.Adj s₁ s₂ := by
  classical
  intro hadj
  apply hnf
  set K1 := G.neighborFinset s₁ ∩ isoTwins G with hK1def
  set K2 := G.neighborFinset s₂ ∩ isoTwins G with hK2def
  have hK1sub : K1 ⊆ G.neighborFinset s₁ := by rw [hK1def]; exact Finset.inter_subset_left
  have hK2sub : K2 ⊆ G.neighborFinset s₂ := by rw [hK2def]; exact Finset.inter_subset_left
  have hK1deg : ∀ t ∈ K1, G.degree t = 3 := by
    intro t ht; rw [hK1def, Finset.mem_inter] at ht; exact (mem_isoTwins.mp ht.2).1
  have hK2deg : ∀ t ∈ K2, G.degree t = 3 := by
    intro t ht; rw [hK2def, Finset.mem_inter] at ht; exact (mem_isoTwins.mp ht.2).1
  have hs1notK2 : s₁ ∉ K2 := by
    rw [hK2def, Finset.mem_inter]; rintro ⟨_, hiso⟩
    have := (mem_isoTwins.mp hiso).1; omega
  have hs2notK1 : s₂ ∉ K1 := by
    rw [hK1def, Finset.mem_inter]; rintro ⟨_, hiso⟩
    have := (mem_isoTwins.mp hiso).1; omega
  have hInterLe : (K1 ∩ K2).card ≤ 2 := by
    calc (K1 ∩ K2).card ≤ K1.card := Finset.card_le_card Finset.inter_subset_left
      _ = 2 := hc1
  have hcases : (K1 ∩ K2).card = 0 ∨ (K1 ∩ K2).card = 1 ∨ (K1 ∩ K2).card = 2 := by omega
  rcases hcases with h0 | h1 | h2
  · have hdisj : Disjoint K1 K2 :=
      Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp h0)
    exact deco_edge_moat_fires G hm h3 s₁ s₂ K1 K2 hadj hK1sub hK1deg
      (by rw [hc1, hd1]) hK2sub hK2deg (by rw [hc2, hd2]) hs1notK2 hs2notK1 hdisj
      (by rw [hd1, hd2]; omega)
  · obtain ⟨t₀, ht0⟩ := Finset.card_eq_one.mp h1
    exact deco_edge_shared_twin_fires G hm h3 s₁ s₂ t₀ K1 K2 hadj hK1sub hK1deg
      (by rw [hc1, hd1]) hK2sub hK2deg (by rw [hc2, hd2]) hs1notK2 hs2notK1 ht0
      (by rw [hd1, hd2]; omega)
  · obtain ⟨t₁, t₂, ht12ne, hK1eq⟩ := Finset.card_eq_two.mp hc1
    have ht1K1 : t₁ ∈ K1 := by rw [hK1eq]; exact Finset.mem_insert_self t₁ _
    have ht2K1 : t₂ ∈ K1 := by
      rw [hK1eq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self t₂)
    have hInterEq : K1 ∩ K2 = K1 :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
    have ht1K2 : t₁ ∈ K2 := by
      have hmem : t₁ ∈ K1 ∩ K2 := by rw [hInterEq]; exact ht1K1
      exact (Finset.mem_inter.mp hmem).2
    have ht2K2 : t₂ ∈ K2 := by
      have hmem : t₂ ∈ K1 ∩ K2 := by rw [hInterEq]; exact ht2K1
      exact (Finset.mem_inter.mp hmem).2
    have hdt1 : G.degree t₁ = 3 := hK1deg t₁ ht1K1
    have hdt2 : G.degree t₂ = 3 := hK1deg t₂ ht2K1
    have has1t1 : G.Adj s₁ t₁ := (G.mem_neighborFinset s₁ t₁).mp (hK1sub ht1K1)
    have has1t2 : G.Adj s₁ t₂ := (G.mem_neighborFinset s₁ t₂).mp (hK1sub ht2K1)
    have has2t1 : G.Adj s₂ t₁ := (G.mem_neighborFinset s₂ t₁).mp (hK2sub ht1K2)
    have has2t2 : G.Adj s₂ t₂ := (G.mem_neighborFinset s₂ t₂).mp (hK2sub ht2K2)
    have hs1t1 : s₁ ≠ t₁ := by intro h; rw [h, hdt1] at hd1; omega
    have hs1t2 : s₁ ≠ t₂ := by intro h; rw [h, hdt2] at hd1; omega
    have hs2t1 : s₂ ≠ t₁ := by intro h; rw [h, hdt1] at hd2; omega
    have hs2t2 : s₂ ≠ t₂ := by intro h; rw [h, hdt2] at hd2; omega
    have e0 : (![s₁, t₁, s₂, t₂] : Fin 4 → Fin n) 0 = s₁ := rfl
    have e1 : (![s₁, t₁, s₂, t₂] : Fin 4 → Fin n) 1 = t₁ := rfl
    have e2 : (![s₁, t₁, s₂, t₂] : Fin 4 → Fin n) 2 = s₂ := rfl
    have e3 : (![s₁, t₁, s₂, t₂] : Fin 4 → Fin n) 3 = t₂ := rfl
    refine master_cycle_fires (k := 4) (by norm_num) G hm h3 ![s₁, t₁, s₂, t₂] ?_ ?_ ?_ ?_
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all <;> rfl
    · intro i
      fin_cases i
      · show G.Adj s₁ t₁; exact has1t1
      · show G.Adj t₁ s₂; exact has2t1.symm
      · show G.Adj s₂ t₂; exact has2t2
      · show G.Adj t₂ s₁; exact has1t2.symm
    · have hsplit : (∑ i : ZMod 4, G.degree (![s₁, t₁, s₂, t₂] i))
          = G.degree s₁ + G.degree t₁ + G.degree s₂ + G.degree t₂ := by
        have h := Fin.sum_univ_four (fun i : Fin 4 => G.degree (![s₁, t₁, s₂, t₂] i))
        rw [e0, e1, e2, e3] at h
        exact h
      rw [hsplit, hd1, hdt1, hd2, hdt2]
    · have hsplit : (∑ i : ZMod 4, (G.degree (![s₁, t₁, s₂, t₂] i) - 1))
          = (G.degree s₁ - 1) + (G.degree t₁ - 1) + (G.degree s₂ - 1)
            + (G.degree t₂ - 1) := by
        have h := Fin.sum_univ_four (fun i : Fin 4 => G.degree (![s₁, t₁, s₂, t₂] i) - 1)
        rw [e0, e1, e2, e3] at h
        exact h
      rw [hsplit, hd1, hdt1, hd2, hdt2]; omega

/-- **The fully census-only per-`p` owner-choke row.**  A never-firing starved census
(`m = 2(n−2)`, `δ ≥ 3`, `hs0`) on `n ≥ 48` satisfies the sharpened choke
`7·t₄ + 8·p + 3·X + 32 ≤ 4n`, with the `(5,5)` saturated-pair independence discharged internally
by `sat_sat_independence` (no moat-provenance hypothesis remains). -/
theorem p_choke_row_unconditional {n : ℕ} [Nonempty (Fin n)] (hn : 48 ≤ n)
    (G : SimpleGraph (Fin n)) (hm : G.edgeFinset.card = 2 * (n - 2))
    (h3 : ∀ v : Fin n, 3 ≤ G.degree v)
    (hs0 : ∀ v w : Fin n, G.degree v = 3 → G.degree w = 3 → ¬G.Adj v w)
    (hnf : ¬ algConn G ≤ 2) :
    7 * (∑ h ∈ (hubSet G).filter (fun h => G.degree h = 4),
            (G.neighborFinset h ∩ isoTwins G).card)
        + 8 * ((hubSet G).filter (fun h => G.degree h = 5 ∧
            (G.neighborFinset h ∩ isoTwins G).card = 2)).card
        + 3 * excessX n G + 32 ≤ 4 * n := by
  refine p_choke_row hn G hm h3 hs0 hnf ?_
  intro s₁ s₂ hd1 hc1 hd2 hc2 hne
  exact sat_sat_independence hn G hm h3 hnf s₁ s₂ hd1 hd2 hc1 hc2 hne

end ACMax
end

/- ---------------------------------------- Counting.V9Discharge ------------ -/
section
/-!
# The tier-9 girth discharge of the starved census

Kills the never-firing starved census import-free for `n ≥ 388`, by a girth
argument on the honest population `V₉ = {v : deg v ≤ 4}` (twins and sea together).
On the window boundary the deg-4-only sea has excess `O(1)`, but including the
twins turns the honest excess into `t₉ = n − 4 − X − 3h = Θ(n)` (`X = excessX`,
`h = #heavies`), which the SQRT girth bound consumes.

## Main results

* `v9_size_row`, `v9_density_row_quant` — the tight size row `n ≤ |V₉| + X` and the
  honest quantitative excess `v9Pairs ≥ 2|V₉| + 2·t₉`.
* `v9_short_cycle_fires`, `v9_girth` — the direct deg-`≤ 4` instance of
  `master_cycle_fires` (a `V₉`-cycle with `9k ≤ n + 8` fires), so a never-firing
  graph has no short `V₉`-cycle.
* `GirthExcessBound`, `girth_excess_bound_holds` — the census-free girth import and
  its unconditional proof, assembling the SQRT cluster with a component descent.
* `starved_v9_kill_of_import`, `starved_v9_kill_sqrt` — the rebased kill, with the
  import discharged via the self-provable SQRT Moore side condition.
* `strip_cubic`, `moore_strip_core`, `moore_strip_arith`, `starved_dead_ge_388` —
  the import-free kill of the whole starved census for `n ≥ 388`, a single branch:
  the derived constraint `10X + 7h ≤ 4n − 200` (`slots_p_row`,
  `p_choke_row_unconditional`, `heavy_full_budget`) discharges the SQRT side
  condition at the ball radius `r = ⌊(⌊(n+8)/9⌋ − 1)/2⌋`.  The former `n ≥ 1100`
  threshold came from three separate losses in the girth bound (see
  `GirthExcessBound`) and a `119`-fold giant credit in `heavy_full_budget`.
-/

namespace ACMax

open Finset
open scoped Classical

/-- **The honest tier-9 population `V₉`**: the degree-`≤ 4` vertices (the twins `deg 3` together
with the sea `deg 4`).  Its complement is exactly the heavies `{deg ≥ 5}`, so `V₉` is almost
everything and its internal excess is `Θ(n)`. -/
noncomputable def v9Set {n : ℕ} (G : SimpleGraph (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter (fun v => G.degree v ≤ 4)

/-- Membership in the tier-9 population. -/
theorem mem_v9Set {n : ℕ} {G : SimpleGraph (Fin n)} {v : Fin n} :
    v ∈ v9Set G ↔ G.degree v ≤ 4 := by
  unfold v9Set; simp

open Classical in
/-- **Ordered adjacent pairs within `V₉`** (twice the number of internal tier-9 edges);
`2·|V₉| < v9Pairs G` is the density row "average tier-9 degree `> 2`". -/
noncomputable def v9Pairs {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  ((v9Set G ×ˢ v9Set G).filter (fun q => G.Adj q.1 q.2)).card

/-- **The tier-9 size row.**  `n ≤ |V₉| + X` (`X = excessX n G`): `Fin n` partitions as
`V₉ ⊔ V₉ᶜ` with `V₉ᶜ ⊆ {deg ≥ 5}`, so `|V₉ᶜ| ≤ |heavies| ≤ X` (`heavy_le_excess`).  The twins
and sea are all inside `V₉`, so the size row is tight (`|V₉| ≥ n − X`, not `n − 8 − 2X`). -/
theorem v9_size_row {n : ℕ} (G : SimpleGraph (Fin n)) :
    n ≤ (v9Set G).card + excessX n G := by
  have hRsub : (v9Set G)ᶜ ⊆ Finset.univ.filter (fun w => 5 ≤ G.degree w) := by
    intro v hv
    rw [Finset.mem_compl, mem_v9Set] at hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ v, by omega⟩
  have hRcard : (v9Set G)ᶜ.card ≤ excessX n G :=
    le_trans (Finset.card_le_card hRsub) (heavy_le_excess G)
  have hcardsum : (v9Set G).card + (v9Set G)ᶜ.card = n := by
    rw [Finset.card_add_card_compl, Fintype.card_fin]
  omega

/-- **The tier-9 quantitative density row** (the honest `t₉ = Θ(n)`).  On a census graph
(`m = 2(n−2)`, `n ≥ 2`) the internal tier-9 pairs satisfy
`2|V₉| + 2n ≤ v9Pairs + 2X + 6h + 8` (`X = excessX n G`, `h = |V₉ᶜ|`), i.e.
`v9Pairs ≥ 2|V₉| + 2·t₉` with the honest excess `t₉ = n − 4 − X − 3h`.  The twins are inside
`V₉`, so the only leakage is to `V₉ᶜ ⊆ heavies`: the total-degree identity `∑ deg = 4n − 8`
(`residual_degree_sum`) and the bipartite `cross_count` give `v9Pairs ≥ 4n − 8 − 2∑_R deg`, and
`∑_R deg = ∑_R(deg − 4) + 4h ≤ X + 4h`. -/
theorem v9_density_row_quant {n : ℕ} (G : SimpleGraph (Fin n)) (hn : 2 ≤ n)
    (hm : G.edgeFinset.card = 2 * (n - 2)) :
    2 * (v9Set G).card + 2 * n
      ≤ v9Pairs G + 2 * excessX n G + 6 * (v9Set G)ᶜ.card + 8 := by
  have hL : ∀ v : Fin n, (G.neighborFinset v ∩ v9Set G).card
      = ∑ w ∈ v9Set G, (if G.Adj v w then 1 else 0) := by
    intro v
    rw [Finset.inter_comm, ← Finset.filter_mem_eq_inter, Finset.card_filter]
    exact Finset.sum_congr rfl (fun w _ => by simp only [G.mem_neighborFinset])
  have hSP : v9Pairs G = ∑ v ∈ v9Set G, (G.neighborFinset v ∩ v9Set G).card := by
    unfold v9Pairs
    rw [Finset.card_filter, Finset.sum_product]
    exact Finset.sum_congr rfl (fun a _ => (hL a).symm)
  have hpartv : ∀ v ∈ v9Set G,
      (G.neighborFinset v ∩ v9Set G).card + (G.neighborFinset v \ v9Set G).card
        = G.degree v := by
    intro v _
    rw [Finset.card_inter_add_card_sdiff, G.card_neighborFinset_eq_degree]
  have hsumV : v9Pairs G + ∑ v ∈ v9Set G, (G.neighborFinset v \ v9Set G).card
      = ∑ v ∈ v9Set G, G.degree v := by
    rw [hSP, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl hpartv
  have hsdiff : ∀ v : Fin n, G.neighborFinset v \ v9Set G
      = G.neighborFinset v ∩ (v9Set G)ᶜ := by
    intro v; ext x
    simp only [Finset.mem_sdiff, Finset.mem_inter, Finset.mem_compl]
  have hLeave : ∑ v ∈ v9Set G, (G.neighborFinset v \ v9Set G).card
      ≤ ∑ w ∈ (v9Set G)ᶜ, G.degree w := by
    calc ∑ v ∈ v9Set G, (G.neighborFinset v \ v9Set G).card
        = ∑ v ∈ v9Set G, (G.neighborFinset v ∩ (v9Set G)ᶜ).card :=
          Finset.sum_congr rfl (fun v _ => by rw [hsdiff v])
      _ = ∑ w ∈ (v9Set G)ᶜ, (G.neighborFinset w ∩ v9Set G).card :=
          cross_count G (v9Set G) (v9Set G)ᶜ
      _ ≤ ∑ w ∈ (v9Set G)ᶜ, G.degree w :=
          Finset.sum_le_sum (fun w _ => by
            rw [← G.card_neighborFinset_eq_degree]
            exact Finset.card_le_card Finset.inter_subset_left)
  have htot : ∑ v : Fin n, G.degree v = 4 * n - 8 := residual_degree_sum n hn G hm
  have hsplit : (∑ v ∈ v9Set G, G.degree v) + ∑ w ∈ (v9Set G)ᶜ, G.degree w
      = ∑ v : Fin n, G.degree v := Finset.sum_add_sum_compl (v9Set G) (fun v => G.degree v)
  have hRsub : (v9Set G)ᶜ ⊆ Finset.univ.filter (fun w => 5 ≤ G.degree w) := by
    intro v hv
    rw [Finset.mem_compl, mem_v9Set] at hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ v, by omega⟩
  have hRexc : ∑ w ∈ (v9Set G)ᶜ, (G.degree w - 4) ≤ excessX n G := by
    unfold excessX
    exact Finset.sum_le_sum_of_subset hRsub
  have hRdeg : ∑ w ∈ (v9Set G)ᶜ, G.degree w
      = (∑ w ∈ (v9Set G)ᶜ, (G.degree w - 4)) + 4 * (v9Set G)ᶜ.card := by
    have hpt : ∀ w ∈ (v9Set G)ᶜ, G.degree w = (G.degree w - 4) + 4 := by
      intro w hw
      rw [Finset.mem_compl, mem_v9Set] at hw
      omega
    rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_comm]
  have hcardsum : (v9Set G).card + (v9Set G)ᶜ.card = n := by
    rw [Finset.card_add_card_compl, Fintype.card_fin]
  omega

/-- **N3 — the census-free girth import (SW5′).**  The single graph-generic girth surface that
replaces the falsified `AHLSeaTier9`/`AHLSeaTier18` bylines: quantified over an *arbitrary*
*nonempty* subset `S : Finset (Fin n)` and its excess `t` (no `seaSet`, no `excessX` — nothing
census; the `S.Nonempty` guard closes the vacuous `S = ∅, t = 0` slot where both side conditions
hold but no cycle can land), it says a subgraph on `S` with excess `2|S| + 2t ≤ pairs(S)`
(i.e. `e(S) ≥ |S| + t`) that also meets the
strength-specific Moore side condition — here the self-provable **SQRT** form, stated at the ball
*radius* `r` rather than at a cycle-length target, as

  `|S|² < |S|·(2r + 1) + t·(3r² − r)`

— contains a cycle of length `3 ≤ k ≤ 2r + 1` inside `S`.  This is the exact negation of the
`sqrt_double_count` conclusion transported from the `2`-core to `S`, so no strength is thrown away
between the ball count and the side condition: the older shape `2|S|² ≤ (L − 5)²·t` is the same
inequality after discarding the `|S|(2r+1)` ball term, weakening the level floor `|L_i| ≥ deg` to
`≥ 2`, and rounding `2r ≥ L − 2` down to `L − 5`.  Recovering those three losses is what moves the
import-free floor from `n ≥ 1071` to `n ≥ 379`.  Threaded as a hypothesis and discharged externally
(the AHL strength, N8, reaches further down the band); never proved here. -/
def GirthExcessBound (n : ℕ) (G : SimpleGraph (Fin n)) : Prop :=
  ∀ (S : Finset (Fin n)) (t r : ℕ), S.Nonempty → 1 ≤ t → 1 ≤ r →
    2 * S.card + 2 * t ≤ ((S ×ˢ S).filter (fun q => G.Adj q.1 q.2)).card →
    S.card ^ 2 < S.card * (2 * r + 1) + t * (3 * r ^ 2 - r) →
    ∃ k : ℕ, 3 ≤ k ∧ k ≤ 2 * r + 1 ∧
      ∃ c : ZMod k → Fin n, Function.Injective c ∧
        (∀ i : ZMod k, G.Adj (c i) (c (i + 1))) ∧ (∀ i : ZMod k, c i ∈ S)

end ACMax


/-! ## The SQRT discharge of `GirthExcessBound`

Assembles the SQRT girth cluster into `girth_excess_bound_holds : ∀ n G,
GirthExcessBound n G`. The one new ingredient is the **component descent**: after
extracting a min-degree-2 core (`two_core_aux`), a mediant/pigeonhole selects a
component `C` on which `sqrt_double_count` gives `|C|·(1+2r) + 2·t_C·r² ≤ |C|²`,
colliding with the SQRT side condition to force a short cycle that lifts back to
`G`. `starved_v9_kill_sqrt` is the rebased kill with this import discharged. -/

namespace ACMax

open SimpleGraph Finset

variable {V : Type*}

/-- **Induced degree equals the within-`S` degree.**  For `w ∈ S`, the degree of `w` in the induced
subgraph `G.induce ↑S` is exactly `degWithin G S w`. -/
theorem induce_degree_eq_degWithin [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (S : Finset V) (w : (↑S : Set V)) :
    (G.induce (↑S : Set V)).degree w = degWithin G S w.val := by
  rw [degWithin, ← SimpleGraph.card_neighborFinset_eq_degree]
  refine Finset.card_bij (fun (u : (↑S : Set V)) _ => (u : V)) ?_ ?_ ?_
  · intro u hu
    rw [SimpleGraph.mem_neighborFinset, SimpleGraph.induce_adj] at hu
    exact Finset.mem_filter.mpr ⟨Finset.mem_coe.mp u.2, hu⟩
  · intro u1 _ u2 _ heq
    exact Subtype.ext heq
  · intro z hz
    rw [Finset.mem_filter] at hz
    refine ⟨⟨z, Finset.mem_coe.mpr hz.1⟩, ?_, rfl⟩
    rw [SimpleGraph.mem_neighborFinset, SimpleGraph.induce_adj]
    exact hz.2

/-- **Component degree preservation.**  In a graph `H`, the degree of a vertex `u` in the induced
graph on its connected component's support equals its degree in `H`, since every neighbour of `u`
lies in the same component. -/
theorem degree_induce_supp_eq [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] (C : H.ConnectedComponent) (u : (C.supp : Set V)) :
    (H.induce (C.supp : Set V)).degree u = H.degree u.val := by
  have hsub : H.neighborSet u.val ⊆ C.supp := fun w hw => C.mem_supp_of_adj_mem_supp u.2 hw
  exact SimpleGraph.degree_induce_of_neighborSet_subset hsub

/-- **Component size as a fibre.**  The number of vertices in a connected component `C` equals the
number of vertices mapping to `C` under `connectedComponentMk`. -/
theorem card_supp_eq_fiber [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    [DecidableEq H.ConnectedComponent] (C : H.ConnectedComponent) :
    Fintype.card C.supp
      = (Finset.univ.filter (fun v => H.connectedComponentMk v = C)).card := by
  rw [← Set.toFinset_card]
  congr 1
  ext v
  simp only [Set.mem_toFinset, Finset.mem_filter, Finset.mem_univ, true_and,
    ConnectedComponent.mem_supp_iff]

/-- **Component degree sum.**  Summing `H.degree` over the vertices of a connected component `C`
equals twice the edge count of `C.toSimpleGraph`, via the component handshake and degree
preservation. -/
theorem sum_degree_component_eq [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] [DecidableEq H.ConnectedComponent] (C : H.ConnectedComponent) :
    ∑ v ∈ Finset.univ.filter (fun v => H.connectedComponentMk v = C), H.degree v
      = 2 * (H.induce (C.supp : Set V)).edgeFinset.card := by
  have hstep : (∑ v ∈ Finset.univ.filter (fun v => H.connectedComponentMk v = C), H.degree v)
      = ∑ a : {v // v ∈ C.supp}, H.degree (a : V) := by
    apply Finset.sum_subtype
    intro x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, ConnectedComponent.mem_supp_iff]
  rw [hstep, ← (H.induce (C.supp : Set V)).sum_degrees_eq_twice_card_edges]
  exact Finset.sum_congr rfl (fun a _ => (degree_induce_supp_eq H C a).symm)

/-- **The mediant pigeonhole.**  Given nonneg fibre sizes `nc` and excesses `tc` over a nonempty
finite index with total size `N` and total excess `≥ t`, some index `C` satisfies
`nc C² · t ≤ N² · tc C`.  Otherwise summing the strict reverse inequalities collides with
`∑ nc² ≤ (∑ nc)² = N²`. -/
theorem exists_mediant_component {κ : Type*} [Fintype κ] (nc tc : κ → ℕ) {N t : ℕ}
    (hne : (Finset.univ : Finset κ).Nonempty) (hN : ∑ C : κ, nc C = N)
    (ht : t ≤ ∑ C : κ, tc C) :
    ∃ C : κ, nc C ^ 2 * t ≤ N ^ 2 * tc C := by
  by_contra hcon
  push Not at hcon
  have hsq : ∑ C : κ, nc C ^ 2 ≤ N ^ 2 := by
    have h1 : ∑ C : κ, nc C ^ 2 ≤ ∑ C : κ, nc C * N := by
      apply Finset.sum_le_sum
      intro C _
      have hle : nc C ≤ N := by
        rw [← hN]
        exact Finset.single_le_sum (fun D _ => Nat.zero_le _) (Finset.mem_univ C)
      calc nc C ^ 2 = nc C * nc C := pow_two (nc C)
        _ ≤ nc C * N := by gcongr
    calc ∑ C : κ, nc C ^ 2 ≤ ∑ C : κ, nc C * N := h1
      _ = (∑ C : κ, nc C) * N := by rw [Finset.sum_mul]
      _ = N * N := by rw [hN]
      _ = N ^ 2 := (pow_two N).symm
  have hsum : N ^ 2 * ∑ C : κ, tc C < t * ∑ C : κ, nc C ^ 2 := by
    have hlt : ∑ C : κ, N ^ 2 * tc C < ∑ C : κ, nc C ^ 2 * t :=
      Finset.sum_lt_sum_of_nonempty hne (fun C _ => hcon C)
    calc N ^ 2 * ∑ C : κ, tc C = ∑ C : κ, N ^ 2 * tc C := by rw [Finset.mul_sum]
      _ < ∑ C : κ, nc C ^ 2 * t := hlt
      _ = t * ∑ C : κ, nc C ^ 2 := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl (fun C _ => by ring)
  have hbad : N ^ 2 * t < N ^ 2 * t := by
    calc N ^ 2 * t ≤ N ^ 2 * ∑ C : κ, tc C := by gcongr
      _ < t * ∑ C : κ, nc C ^ 2 := hsum
      _ ≤ t * N ^ 2 := by gcongr
      _ = N ^ 2 * t := by ring
  exact absurd hbad (lt_irrefl _)

/-- **The SQRT discharge.**  `GirthExcessBound` holds for every `n` and `G`.  Given a nonempty `S`
with `2|S| + 2t ≤ pairs(S)` (edge excess `t`) and the SQRT side condition `2|S|² ≤ (L−5)²·t` with
`6 ≤ L`, there is a cycle of length `3 ≤ k ≤ L` inside `S`.  Assembly: extract the min-degree-`2`
`2`-core (`two_core_aux`), pick the excess-carrying component (`exists_mediant_component`), collide
`sqrt_double_count` with the side condition (`r = ⌊(L−1)/2⌋`), and lift the resulting short cycle
through the two induced-graph embeddings to `G` via `cycle_walk_to_zmod`. -/
theorem girth_excess_bound_holds (n : ℕ) (G : SimpleGraph (Fin n)) : GirthExcessBound n G := by
  classical
  intro S t r hSne ht1 hr1 hpairs hside
  have hScard1 : 1 ≤ S.card := Finset.card_pos.mpr hSne
  -- Rewrite the pair count as the within-`S` degree sum, then extract the `2`-core.
  have hpairs' : 2 * S.card + 2 * t ≤ edgeSumWithin G S := by
    rw [edgeSumWithin_eq_pairs]; exact hpairs
  obtain ⟨S', hS'sub, hS'ne, hS'min, hS'inv⟩ := two_core_aux G ht1 S hpairs'
  set H : SimpleGraph (↥(↑S' : Set (Fin n))) := G.induce (↑S' : Set (Fin n)) with hHdef
  have : Nonempty (↥(↑S' : Set (Fin n))) := (Finset.coe_nonempty.mpr hS'ne).to_subtype
  have : DecidableEq H.ConnectedComponent := Classical.decEq _
  have hcardV' : Fintype.card (↥(↑S' : Set (Fin n))) = S'.card := by
    rw [← Set.toFinset_card, Finset.toFinset_coe]
  set NN : ℕ := Fintype.card (↥(↑S' : Set (Fin n))) with hNNdef
  have hHexc : NN + t ≤ H.edgeFinset.card := by
    have hDS : edgeSumWithin G S' = 2 * H.edgeFinset.card := by
      rw [edgeSumWithin_eq_pairs]; exact induced_pairs_eq_two_mul_edges G S'
    rw [hcardV']; omega
  have hHmin : ∀ w : ↥(↑S' : Set (Fin n)), 2 ≤ H.degree w := by
    intro w
    have hh : H.degree w = degWithin G S' w.val := induce_degree_eq_degWithin G S' w
    rw [hh]
    exact hS'min w.val (Finset.mem_coe.mp w.2)
  -- Component partition data.
  have hnc_le_ec : ∀ C : H.ConnectedComponent,
      Fintype.card C.supp ≤ (H.induce (C.supp : Set (↥(↑S' : Set (Fin n))))).edgeFinset.card := by
    intro C
    have hkey := sum_degree_component_eq H C
    have hconst : ∑ _v ∈ Finset.univ.filter (fun v => H.connectedComponentMk v = C), (2 : ℕ)
        = 2 * Fintype.card C.supp := by
      rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm, card_supp_eq_fiber H C]
    have hge : 2 * Fintype.card C.supp
        ≤ ∑ v ∈ Finset.univ.filter (fun v => H.connectedComponentMk v = C), H.degree v := by
      rw [← hconst]
      exact Finset.sum_le_sum (fun v _ => hHmin v)
    rw [hkey] at hge
    omega
  have hcard_sum : ∑ C : H.ConnectedComponent, Fintype.card C.supp = NN := by
    have hfw := Finset.card_eq_sum_card_fiberwise
      (s := (Finset.univ : Finset (↥(↑S' : Set (Fin n)))))
      (t := (Finset.univ : Finset H.ConnectedComponent))
      (f := H.connectedComponentMk) (fun v _ => Finset.mem_univ _)
    simp only [Finset.card_univ] at hfw
    rw [hNNdef, hfw]
    exact Finset.sum_congr rfl (fun C _ => card_supp_eq_fiber H C)
  have hedge_part : ∑ C : H.ConnectedComponent,
      (H.induce (C.supp : Set (↥(↑S' : Set (Fin n))))).edgeFinset.card = H.edgeFinset.card := by
    have hfib := Finset.sum_fiberwise (Finset.univ : Finset (↥(↑S' : Set (Fin n))))
      H.connectedComponentMk (fun v => H.degree v)
    have hhand := H.sum_degrees_eq_twice_card_edges
    have h2 : ∑ C : H.ConnectedComponent,
          2 * (H.induce (C.supp : Set (↥(↑S' : Set (Fin n))))).edgeFinset.card
        = 2 * H.edgeFinset.card := by
      rw [← hhand, ← hfib]
      exact Finset.sum_congr rfl (fun C _ => (sum_degree_component_eq H C).symm)
    rw [← Finset.mul_sum] at h2
    omega
  have htc_sum : t ≤ ∑ C : H.ConnectedComponent,
      ((H.induce (C.supp : Set (↥(↑S' : Set (Fin n))))).edgeFinset.card - Fintype.card C.supp) := by
    have hsplit : (∑ C : H.ConnectedComponent,
          ((H.induce (C.supp : Set (↥(↑S' : Set (Fin n))))).edgeFinset.card - Fintype.card C.supp))
          + ∑ C : H.ConnectedComponent, Fintype.card C.supp
        = ∑ C : H.ConnectedComponent,
          (H.induce (C.supp : Set (↥(↑S' : Set (Fin n))))).edgeFinset.card := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun C _ => Nat.sub_add_cancel (hnc_le_ec C))
    rw [hcard_sum, hedge_part] at hsplit
    omega
  have hne : (Finset.univ : Finset H.ConnectedComponent).Nonempty := Finset.univ_nonempty
  -- Select the excess-carrying component via the mediant.
  obtain ⟨C, hmed⟩ := exists_mediant_component
    (fun C : H.ConnectedComponent => Fintype.card C.supp)
    (fun C : H.ConnectedComponent =>
      (H.induce (C.supp : Set (↥(↑S' : Set (Fin n))))).edgeFinset.card - Fintype.card C.supp)
    hne hcard_sum htc_sum
  have hmed2 : Fintype.card (C.supp : Set (↥(↑S' : Set (Fin n)))) ^ 2 * t
      ≤ NN ^ 2 * ((H.induce (C.supp : Set (↥(↑S' : Set (Fin n))))).edgeFinset.card
        - Fintype.card C.supp) := hmed
  have : Nonempty (C.supp : Set (↥(↑S' : Set (Fin n)))) :=
    (SimpleGraph.ConnectedComponent.nonempty_supp C).to_subtype
  -- No cycle of length `≤ 2r+1` collides with the SQRT side condition, so a short cycle exists.
  have hcyc : ∃ (u : (C.supp : Set (↥(↑S' : Set (Fin n)))))
      (w : (H.induce (C.supp : Set (↥(↑S' : Set (Fin n))))).Walk u u),
      w.IsCycle ∧ w.length ≤ 2 * r + 1 := by
    by_contra hcon
    push Not at hcon
    have hg : ∀ (u : (C.supp : Set (↥(↑S' : Set (Fin n)))))
        (w : (H.induce (C.supp : Set (↥(↑S' : Set (Fin n))))).Walk u u),
        w.IsCycle → 2 * r + 1 < w.length := fun u w hw => hcon u w hw
    have hmin_C : ∀ u : (C.supp : Set (↥(↑S' : Set (Fin n)))),
        2 ≤ (H.induce (C.supp : Set (↥(↑S' : Set (Fin n))))).degree u := by
      intro u
      rw [degree_induce_supp_eq H C u]
      exact hHmin u.val
    have hconn_C : (H.induce (C.supp : Set (↥(↑S' : Set (Fin n))))).Connected :=
      SimpleGraph.ConnectedComponent.connected_toSimpleGraph C
    have hle := hnc_le_ec C
    have hexc_C : Fintype.card (C.supp : Set (↥(↑S' : Set (Fin n))))
        + ((H.induce (C.supp : Set (↥(↑S' : Set (Fin n))))).edgeFinset.card - Fintype.card C.supp)
        ≤ (H.induce (C.supp : Set (↥(↑S' : Set (Fin n))))).edgeFinset.card := by omega
    have hsqrt := sqrt_double_count (H.induce (C.supp : Set (↥(↑S' : Set (Fin n)))))
      hmin_C hg hconn_C hexc_C
    -- Abbreviations for the arithmetic collision.
    set nc := Fintype.card (C.supp : Set (↥(↑S' : Set (Fin n)))) with hncval
    set ec := (H.induce (C.supp : Set (↥(↑S' : Set (Fin n))))).edgeFinset.card with hecval
    set w : ℕ := 3 * r ^ 2 - r with hwdef
    have hncpos : 0 < nc := Fintype.card_pos
    have hncNN : nc ≤ NN := by
      rw [← hcard_sum]
      exact Finset.single_le_sum (f := fun D : H.ConnectedComponent => Fintype.card D.supp)
        (fun D _ => Nat.zero_le _) (Finset.mem_univ C)
    have hNleS : NN ≤ S.card := by
      rw [hcardV']; exact Finset.card_le_card hS'sub
    -- (i) Multiply the component ball count by `NN²` and feed in the mediant, so that the
    -- component excess `ec − nc` is replaced by the global excess `t`.
    have key1 : NN ^ 2 * (nc * (2 * r + 1)) + w * (nc ^ 2 * t) ≤ NN ^ 2 * nc ^ 2 := by
      have hstep : w * (nc ^ 2 * t) ≤ NN ^ 2 * ((ec - nc) * w) := by
        calc w * (nc ^ 2 * t) ≤ w * (NN ^ 2 * (ec - nc)) := Nat.mul_le_mul_left w hmed2
          _ = NN ^ 2 * ((ec - nc) * w) := by ring
      calc NN ^ 2 * (nc * (2 * r + 1)) + w * (nc ^ 2 * t)
          ≤ NN ^ 2 * (nc * (1 + 2 * r)) + NN ^ 2 * ((ec - nc) * w) := by
            have hcomm : NN ^ 2 * (nc * (2 * r + 1)) = NN ^ 2 * (nc * (1 + 2 * r)) := by ring
            rw [hcomm]
            exact Nat.add_le_add_left hstep _
        _ = NN ^ 2 * (nc * (1 + 2 * r) + (ec - nc) * w) := by ring
        _ ≤ NN ^ 2 * nc ^ 2 := Nat.mul_le_mul_left _ hsqrt
    -- (ii) Trade one factor `NN` for `nc` in the ball term and cancel `nc²`.
    have key2 : NN * (2 * r + 1) + t * w ≤ NN ^ 2 := by
      have hmul : (NN * (2 * r + 1) + t * w) * nc ^ 2 ≤ NN ^ 2 * nc ^ 2 := by
        have hswap : NN * (2 * r + 1) * nc ^ 2 ≤ NN ^ 2 * (nc * (2 * r + 1)) := by
          have e1 : NN * (2 * r + 1) * nc ^ 2 = (nc * (2 * r + 1)) * (nc * NN) := by ring
          have e2 : NN ^ 2 * (nc * (2 * r + 1)) = (nc * (2 * r + 1)) * (NN * NN) := by ring
          rw [e1, e2]
          gcongr
        have hrest : t * w * nc ^ 2 = w * (nc ^ 2 * t) := by ring
        calc (NN * (2 * r + 1) + t * w) * nc ^ 2
            = NN * (2 * r + 1) * nc ^ 2 + t * w * nc ^ 2 := by ring
          _ ≤ NN ^ 2 * (nc * (2 * r + 1)) + w * (nc ^ 2 * t) := by
              rw [hrest]; exact Nat.add_le_add_right hswap _
          _ ≤ NN ^ 2 * nc ^ 2 := key1
      exact Nat.le_of_mul_le_mul_right hmul (pow_pos hncpos 2)
    -- (iii) Transport `NN ↦ |S|`: `x ↦ x² − x(2r+1)` is monotone above `(2r+1)/2`, and `key2`
    -- itself forces `2r + 1 ≤ NN`.
    have hNNpos : 0 < NN := lt_of_lt_of_le hncpos hncNN
    have h2r1 : 2 * r + 1 ≤ NN := by
      have h : NN * (2 * r + 1) ≤ NN * NN := by
        calc NN * (2 * r + 1) ≤ NN * (2 * r + 1) + t * w := Nat.le_add_right _ _
          _ ≤ NN ^ 2 := key2
          _ = NN * NN := by ring
      exact Nat.le_of_mul_le_mul_left h hNNpos
    have hmono : NN ^ 2 + S.card * (2 * r + 1) ≤ S.card ^ 2 + NN * (2 * r + 1) := by
      obtain ⟨d, hd⟩ : ∃ d, S.card = NN + d := ⟨S.card - NN, by omega⟩
      have h1 : d * (2 * r + 1) ≤ d * NN := Nat.mul_le_mul_left d h2r1
      rw [hd]
      nlinarith [h1]
    -- (iv) Collide with the side condition.
    omega
  -- Lift the short cycle from the component graph to `G` and convert to `ZMod`.
  obtain ⟨u, w, hwcyc, hwlen⟩ := hcyc
  set w1 := w.map
    (SimpleGraph.Embedding.induce (G := H) (C.supp : Set (↥(↑S' : Set (Fin n))))).toHom with hw1def
  set w2 := w1.map (SimpleGraph.Embedding.induce (G := G) (↑S' : Set (Fin n))).toHom with hw2def
  have hw1cyc : w1.IsCycle := by
    rw [hw1def]
    exact hwcyc.map
      (SimpleGraph.Embedding.induce (G := H) (C.supp : Set (↥(↑S' : Set (Fin n))))).injective
  have hw2cyc : w2.IsCycle := by
    rw [hw2def]
    exact hw1cyc.map (SimpleGraph.Embedding.induce (G := G) (↑S' : Set (Fin n))).injective
  have hlen : w2.length = w.length := by
    rw [hw2def, hw1def, SimpleGraph.Walk.length_map, SimpleGraph.Walk.length_map]
  have hsupp : ∀ x ∈ w2.support, x ∈ S := by
    intro x hx
    rw [hw2def, SimpleGraph.Walk.support_map, List.mem_map] at hx
    obtain ⟨y, _, rfl⟩ := hx
    exact hS'sub (Finset.mem_coe.mp y.2)
  obtain ⟨hk3, hex⟩ := cycle_walk_to_zmod hw2cyc hsupp
  exact ⟨w2.length, hk3, by omega, hex⟩

end ACMax


/-! ## The honest heavy budget

The one counting row that lives here rather than in `Counting.StarvedCensus`: the heavy budget
`h + h₆₊ + 4·n_g ≤ X`, which the `MASTER′` assembly consumes.  The `n ≥ 388` dispatch that this
section used to carry has been superseded by `Counting.V9DischargeSharp` (`starved_dead_ge_123`),
which runs the same collision at the bulk-credited moat radius of `Counting.MoatSharp`.
-/

namespace ACMax

open Finset
open scoped Classical

/-- **The honest heavy budget** (D1′).  At `n ≥ 57` the total excess `X = excessX n G` dominates
`h + h₆₊ + 4·n_g`, where `h = |V₉ᶜ|` counts the heavies (`deg ≥ 5`), `h₆₊` the non-giant
deg-`≥6` hubs and `n_g` the giants (`n + 15 < 9·deg`).  Each deg-`≥5` vertex spends `deg − 4 ≥ 1`
excess (that is `h`), each deg-`≥6` non-giant an extra `1` (so `2 ≤ deg − 4`), and each giant
(`deg ≥ 9` already at `n ≥ 57`) an extra `4` (so `5 ≤ deg − 4`).

The giant credit is `4` — exactly what the `MASTER′` assembly consumes (`28·n_g ≤ 7·4·n_g`).  It
used to be `119`, which forced `n ≥ 1100` on this row alone and so on the whole import-free band;
`4` costs the assembly nothing and holds from `n = 57`. -/
theorem heavy_full_budget {n : ℕ} (G : SimpleGraph (Fin n)) (hn : 57 ≤ n) :
    (v9Set G)ᶜ.card
      + ((hubSet G).filter (fun h => 6 ≤ G.degree h ∧ ¬ (n + 15 < 9 * G.degree h))).card
      + 4 * ((hubSet G).filter (fun h => n + 15 < 9 * G.degree h)).card
      ≤ excessX n G := by
  have hhub : hubSet G = Finset.univ.filter (fun v => 4 ≤ G.degree v) := rfl
  have hexc : excessX n G = ∑ v ∈ hubSet G, (G.degree v - 4) := by
    unfold excessX
    rw [hhub]
    refine Finset.sum_subset ?_ ?_
    · intro v hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
      omega
    · intro v hv hv2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv hv2
      omega
  have hcard5 : (v9Set G)ᶜ.card = ((hubSet G).filter (fun v => 5 ≤ G.degree v)).card := by
    congr 1
    ext v
    simp only [Finset.mem_compl, mem_v9Set, Finset.mem_filter, mem_hubSet]
    omega
  rw [hexc, hcard5, Finset.card_filter, Finset.card_filter, Finset.card_filter,
    Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro v hv
  rw [mem_hubSet] at hv
  split_ifs <;> omega

end ACMax
end

/- ---------------------------------------- Counting.V9DischargeSharp ------- -/
section
/-!
# The import-free starved kill at `n ≥ 123` (bulk-credited moat)

`Counting/V9Discharge.lean` closes the starved census import-free from `n ≥ 388`, at ball radius
`r = ⌊(⌊(n+8)/9⌋ − 1)/2⌋` — the radius the *old* moat threshold `9k ≤ n + 8` allows.

`Counting/MoatSharp.lean` sharpens that threshold to `12k + X ≤ 2n` by keeping the bulk excess
`Σ_{S₂}(deg − 3)` that `master_cycle_fires` discards.  The admissible radius rises to

  `r = ⌊(2n − X − 12)/24⌋`,

and re-running the same discharge with it drops the import-free threshold from `388` to **`123`**.

**Why `123`.**  The integer condition `|V₉|² < |V₉|(2r+1) + t₉(3r² − r)` holds on the whole
counting region from `n = 111` upward; the discharge below makes the same two relaxations as the
`388` route — `r` replaced by its uniform lower bound (`24r ≥ 2n − X − 35`, dropping `⌊·⌋`) and the
region replaced by an `H`-monotone endpoint — landing the *proved* threshold at `123`.

**Route.**  Unlike the `388` version, the radius now depends on `X`, so the excess term carries
`A = 2N − X − 35` rather than an `X`-free square.  Both `t₉` and `A` are bounded below by `X`-free
linear forms that are *simultaneously* tight at `X = X_max`, so pushing `X` to the master maximum
costs nothing:  `10·t₉ ≥ 6N + 160 − 23H` and `10·A ≥ 16N + 7H − 150`.  What remains is a two-
variable cubic that is monotone decreasing in `H` (every `H`-coefficient is negative at `N ≥ 123`),
so its minimum sits at `17H = 4N − 200`; there `4913·gap − cubic` splits *exactly* as a sum of
three manifestly non-negative products, and `strip_cubic_sharp` closes.
-/

namespace ACMax

open Finset
open scoped Classical

/-! ## The arithmetic core -/

/-- **The sharp strip cubic.**  The single-variable inequality the `n ≥ 123` region arithmetic
bottoms out at, after `X` is pushed to its master maximum and `H` to the end of its range.
Substituting `N = 123 + u` makes every coefficient non-negative
(`1068496017 + 1122649307u + 11552736u² + 20700u³`), which is what `nlinarith` finds. -/
theorem strip_cubic_sharp {N : ℤ} (hN : 123 ≤ N) :
    779812849 * N + 755972700 < 20700 * N ^ 3 + 3914436 * N ^ 2 := by
  have hu : (0 : ℤ) ≤ N - 123 := by linarith
  nlinarith [hu, mul_nonneg hu hu, mul_nonneg (mul_nonneg hu hu) hu]

/-- **The two-variable core.**  After both `X`-eliminations the target is a cubic in `(N, H)`:

  `4608000·(N−H)² < 38400·(N−H)·(Q+120) + 23·P·Q²`,  `P = 6N+160−23H`, `Q = 16N+7H−150`.

Every `H`-coefficient of the gap is negative at `N ≥ 123`, so the minimum is at `17H = 4N − 200`,
and `4913·gap − cubic` is *identically* `289(M−17H)(−c₁) + 17(M²−(17H)²)(−c₂) + (M³−(17H)³)·25921`
with `M = 4N − 200`, `−c₁ = 104512N² − 11944120N + 18478500 ≥ 0` (its larger root is `≈ 112.7`)
and `−c₂ = 111734N + 3585580 ≥ 0`.  So `linarith` closes on those three products plus the cubic. -/
theorem moore_strip_twovar_sharp {N H : ℤ} (hN : 123 ≤ N) (hH : 0 ≤ H)
    (hs : 17 * H ≤ 4 * N - 200) :
    4608000 * (N - H) ^ 2
      < 38400 * ((N - H) * (16 * N + 7 * H - 30))
        + 23 * ((6 * N + 160 - 23 * H) * (16 * N + 7 * H - 150) ^ 2) := by
  have hd : (0 : ℤ) ≤ (4 * N - 200) - 17 * H := by linarith
  have hHm : (0 : ℤ) ≤ 17 * H := by linarith
  have hnc1 : (0 : ℤ) ≤ 104512 * N ^ 2 - 11944120 * N + 18478500 := by nlinarith [hN]
  have hnc2 : (0 : ℤ) ≤ 111734 * N + 3585580 := by linarith
  have hsq : (0 : ℤ) ≤ (4 * N - 200) ^ 2 + 17 * H * (4 * N - 200) + (17 * H) ^ 2 := by
    nlinarith [hHm, hd, sq_nonneg (4 * N - 200), sq_nonneg (17 * H)]
  have e1 := mul_nonneg hd hnc1
  have e2 := mul_nonneg (mul_nonneg hd (by linarith : (0 : ℤ) ≤ (4 * N - 200) + 17 * H)) hnc2
  have e3 := mul_nonneg (mul_nonneg hd hsq) (by norm_num : (0 : ℤ) ≤ 25921)
  have hcub := strip_cubic_sharp hN
  linarith [e1, e2, e3, hcub]

/-- **The `R`-free core of the sharp strip discharge.**  On the counting region
(`0 ≤ H ≤ X`, `10X + 7H ≤ 4N − 200`) at `N ≥ 123`,

  `4608·(N−H)² < 384·(N−H)·(2N−X−23) + 23·(N−4−X−3H)·(2N−X−35)²`.

Both `X`-dependent factors are pushed to the master maximum simultaneously — `10·t ≥ 6N+160−23H`
and `10·A ≥ 16N+7H−150`, equalities together at `X = X_max` — and `moore_strip_twovar_sharp`
closes what is left. -/
theorem moore_strip_core_sharp {N X H : ℤ} (hN : 123 ≤ N) (hH : 0 ≤ H) (hHX : H ≤ X)
    (hmaster : 10 * X + 7 * H ≤ 4 * N - 200) :
    4608 * (N - H) ^ 2
      < 384 * ((N - H) * (2 * N - X - 23))
        + 23 * ((N - 4 - X - 3 * H) * (2 * N - X - 35) ^ 2) := by
  have h17 : 17 * H ≤ 4 * N - 200 := by linarith
  have hvpos : (0 : ℤ) ≤ N - H := by linarith
  have hPpos : (0 : ℤ) ≤ 6 * N + 160 - 23 * H := by linarith
  have hQpos : (0 : ℤ) ≤ 16 * N + 7 * H - 150 := by linarith
  have hP : 6 * N + 160 - 23 * H ≤ 10 * (N - 4 - X - 3 * H) := by linarith
  have hQ : 16 * N + 7 * H - 150 ≤ 10 * (2 * N - X - 35) := by linarith
  -- the ball factor, pushed to the master maximum
  have hA : 38400 * ((N - H) * (16 * N + 7 * H - 30))
      ≤ 1000 * (384 * ((N - H) * (2 * N - X - 23))) := by nlinarith [hvpos, hQ]
  -- the excess factor, pushed to the master maximum
  have hQ2 : (16 * N + 7 * H - 150) ^ 2 ≤ (10 * (2 * N - X - 35)) ^ 2 := by
    nlinarith [hQpos, hQ]
  have hmul : (6 * N + 160 - 23 * H) * (16 * N + 7 * H - 150) ^ 2
      ≤ (10 * (N - 4 - X - 3 * H)) * (10 * (2 * N - X - 35)) ^ 2 :=
    mul_le_mul hP hQ2 (sq_nonneg _) (by linarith)
  have hB : 23 * ((6 * N + 160 - 23 * H) * (16 * N + 7 * H - 150) ^ 2)
      ≤ 1000 * (23 * ((N - 4 - X - 3 * H) * (2 * N - X - 35) ^ 2)) := by nlinarith [hmul]
  have htv := moore_strip_twovar_sharp hN hH h17
  linarith [hA, hB, htv]

/-- **The sharp strip Moore arithmetic.**  On the counting region, `MASTER′` together with
`H ≤ X`, `N ≥ 123` and the sharpened radius bound `2N − X − 35 ≤ 24R` forces the SQRT side
condition

  `(N − H)² < (N − H)(2R + 1) + (N − 4 − X − 3H)(3R² − R)`.

Route: `moore_strip_core_sharp` supplies the `R`-free inequality; then `12(2R+1) ≥ 2N−X−23`
upgrades the ball term and `23(2N−X−35)² ≤ 4608(3R²−R)` the excess term (from `(2N−X−35)² ≤
576R²` and `23R² ≤ 8(3R²−R)`, the latter by `R ≥ 8`), both by the same factor `4608 = 384·12`. -/
theorem moore_strip_arith_sharp {N X H R : ℤ} (hN : 123 ≤ N)
    (hH : 0 ≤ H) (hHX : H ≤ X) (hR : 2 * N - X - 35 ≤ 24 * R)
    (hmaster : 10 * X + 7 * H ≤ 4 * N - 200) :
    (N - H) ^ 2 < (N - H) * (2 * R + 1) + (N - 4 - X - 3 * H) * (3 * R ^ 2 - R) := by
  have hR8 : (8 : ℤ) ≤ R := by omega
  have hvpos : (0 : ℤ) ≤ N - H := by linarith
  have hq : (0 : ℤ) ≤ N - 4 - X - 3 * H := by linarith
  have hApos : (0 : ℤ) ≤ 2 * N - X - 35 := by linarith
  have hcore := moore_strip_core_sharp hN hH hHX hmaster
  -- the ball term: `12(2R + 1) = 24R + 12 ≥ 2N − X − 23`
  have hball : (N - H) * (2 * N - X - 23) ≤ 12 * ((N - H) * (2 * R + 1)) := by
    nlinarith [hvpos, hR]
  -- the excess term
  have hsq : (2 * N - X - 35) ^ 2 ≤ 576 * R ^ 2 := by nlinarith [hR, hApos]
  have hRR : 23 * R ^ 2 ≤ 8 * (3 * R ^ 2 - R) := by nlinarith [hR8]
  have hexc : 23 * (2 * N - X - 35) ^ 2 ≤ 4608 * (3 * R ^ 2 - R) := by nlinarith [hsq, hRR]
  have hB : 23 * ((N - 4 - X - 3 * H) * (2 * N - X - 35) ^ 2)
      ≤ 4608 * ((N - 4 - X - 3 * H) * (3 * R ^ 2 - R)) := by nlinarith [hq, hexc]
  linarith [hcore, hball, hB]

/-! ## The graph-level dispatch -/

/-- **The sharpened tier-9 girth.**  In a never-firing starved census, `V₉` contains no cycle of
length `k` with `12k + X ≤ 2n` — against `9k ≤ n + 8` for `v9_girth`. -/
theorem v9_girth_sharp {n : ℕ} [Nonempty (Fin n)] {k : ℕ} [NeZero k]
    (G : SimpleGraph (Fin n)) (hm : G.edgeFinset.card = 2 * (n - 2))
    (h3 : ∀ v : Fin n, 3 ≤ G.degree v) (hnf : ¬ algConn G ≤ 2)
    (hk : 3 ≤ k) (hn8 : 8 ≤ n) (hkn : 12 * k + excessX n G ≤ 2 * n) (c : ZMod k → Fin n)
    (hcinj : Function.Injective c) (hadj : ∀ i : ZMod k, G.Adj (c i) (c (i + 1)))
    (hmem : ∀ i : ZMod k, c i ∈ v9Set G) : False :=
  hnf (v9_short_cycle_fires_sharp hk G hm h3 c hcinj hadj
    (fun i => mem_v9Set.mp (hmem i)) hn8 hkn)

/-- **The rebased tier-9 kill at the sharpened moat obligation.**  Identical to
`starved_v9_kill_sqrt` except that the moat obligation is `12(2r+1) + X ≤ 2n` rather than
`9(2r+1) ≤ n + 8`: the cycle the ball count produces has length at most `2r + 1`, and a `V₉`-cycle
that short fires `v9_short_cycle_fires_sharp`. -/
theorem starved_v9_kill_sharp {n : ℕ} [Nonempty (Fin n)] (G : SimpleGraph (Fin n))
    (hlo : 55 ≤ n) (hm : G.edgeFinset.card = 2 * (n - 2))
    (h3 : ∀ v : Fin n, 3 ≤ G.degree v) (hnf : ¬ algConn G ≤ 2)
    (hpos : excessX n G + 3 * (v9Set G)ᶜ.card + 5 ≤ n)
    (r : ℕ) (hr1 : 1 ≤ r) (hrn : 12 * (2 * r + 1) + excessX n G ≤ 2 * n)
    (hMoore : (v9Set G).card ^ 2
      < (v9Set G).card * (2 * r + 1)
        + (n - 4 - excessX n G - 3 * (v9Set G)ᶜ.card) * (3 * r ^ 2 - r)) : False := by
  set t9 : ℕ := n - 4 - excessX n G - 3 * (v9Set G)ᶜ.card with ht9def
  have hRsub : (v9Set G)ᶜ ⊆ Finset.univ.filter (fun w => 5 ≤ G.degree w) := by
    intro v hv
    rw [Finset.mem_compl, mem_v9Set] at hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ v, by omega⟩
  have hRcard : (v9Set G)ᶜ.card ≤ excessX n G :=
    le_trans (Finset.card_le_card hRsub) (heavy_le_excess G)
  have hexc : 2 * (v9Set G).card + 2 * t9 ≤ v9Pairs G := by
    have hq := v9_density_row_quant G (by omega) hm
    rw [ht9def]
    omega
  have ht1 : 1 ≤ t9 := by rw [ht9def]; omega
  have hne : (v9Set G).Nonempty := by
    rw [← Finset.card_pos]
    have hsize := v9_size_row G
    omega
  obtain ⟨k, hk3, hkr, c, hcinj, hadj, hmem⟩ :=
    girth_excess_bound_holds n G (v9Set G) t9 r hne ht1 hr1 hexc hMoore
  have : NeZero k := ⟨by omega⟩
  exact v9_girth_sharp G hm h3 hnf hk3 (by omega) (by omega) c hcinj hadj hmem

/-- **D3′ — the import-free starved kill at `n ≥ 123`.**  A never-firing starved census
(`m = 2(n−2)`, `δ ≥ 3`, `hs0`) on `123 ≤ n` cannot exist, with no external girth byline.  Same
single branch as `starved_dead_ge_388`, run at the bulk-credited radius
`r = ⌊(2n − X − 12)/24⌋` and discharged by `moore_strip_arith_sharp`. -/
theorem starved_dead_ge_123 {n : ℕ} [Nonempty (Fin n)] (G : SimpleGraph (Fin n))
    (hn : 123 ≤ n) (hm : G.edgeFinset.card = 2 * (n - 2))
    (h3 : ∀ v : Fin n, 3 ≤ G.degree v) (hnf : ¬ algConn G ≤ 2)
    (hs0 : ∀ v w : Fin n, G.degree v = 3 → G.degree w = 3 → ¬G.Adj v w) : False := by
  have hD1 := slots_p_row G (by omega) hm h3 hnf hs0
  have hPC := p_choke_row_unconditional (by omega) G hm h3 hs0 hnf
  have hbud := heavy_full_budget G (by omega)
  have hMaster : 10 * excessX n G + 7 * (v9Set G)ᶜ.card ≤ 4 * n - 200 := by omega
  have hhX : (v9Set G)ᶜ.card ≤ excessX n G := by
    have hRsub : (v9Set G)ᶜ ⊆ Finset.univ.filter (fun w => 5 ≤ G.degree w) := by
      intro v hv
      rw [Finset.mem_compl, mem_v9Set] at hv
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ v, by omega⟩
    exact le_trans (Finset.card_le_card hRsub) (heavy_le_excess G)
  have hpos : excessX n G + 3 * (v9Set G)ᶜ.card + 5 ≤ n := by omega
  -- the bulk-credited ball radius `r = ⌊(2n − X − 12)/24⌋`
  set Xe := excessX n G with hXe
  set Hc := (v9Set G)ᶜ.card with hHc
  have hr1 : 1 ≤ (2 * n - Xe - 12) / 24 := by omega
  have hrn : 12 * (2 * ((2 * n - Xe - 12) / 24) + 1) + Xe ≤ 2 * n := by omega
  have hr24 : 2 * n - Xe - 35 ≤ 24 * ((2 * n - Xe - 12) / 24) := by omega
  have hVhh : (v9Set G).card + Hc = n := by
    rw [hHc, Finset.card_add_card_compl, Fintype.card_fin]
  have hMoore : (v9Set G).card ^ 2
      < (v9Set G).card * (2 * ((2 * n - Xe - 12) / 24) + 1)
        + (n - 4 - Xe - 3 * Hc)
          * (3 * ((2 * n - Xe - 12) / 24) ^ 2 - ((2 * n - Xe - 12) / 24)) := by
    set Vc := (v9Set G).card with hVc
    set Rl := (2 * n - Xe - 12) / 24 with hRl
    -- make the radius opaque: `omega` must not reason under the nested `⌊·⌋`
    clear_value Rl
    clear hRl
    obtain ⟨q, hq⟩ : ∃ q, n = 4 + Xe + 3 * Hc + q := ⟨n - (4 + Xe + 3 * Hc), by omega⟩
    have e1 : n - 4 - Xe - 3 * Hc = q := by omega
    have e2 : Vc = 4 + Xe + 2 * Hc + q := by omega
    have hkey := moore_strip_arith_sharp (N := (n : ℤ)) (X := (Xe : ℤ)) (H := (Hc : ℤ))
      (R := (Rl : ℤ)) (by exact_mod_cast hn) (Int.natCast_nonneg _)
      (Nat.cast_le.mpr hhX) (by omega) (by omega)
    have hnZ : (n : ℤ) = 4 + (Xe : ℤ) + 3 * (Hc : ℤ) + (q : ℤ) := by exact_mod_cast hq
    have ea : (n : ℤ) - (Hc : ℤ) = 4 + (Xe : ℤ) + 2 * (Hc : ℤ) + (q : ℤ) := by rw [hnZ]; ring
    have eb : (n : ℤ) - 4 - (Xe : ℤ) - 3 * (Hc : ℤ) = (q : ℤ) := by rw [hnZ]; ring
    rw [ea, eb] at hkey
    have hle : Rl ≤ 3 * Rl ^ 2 :=
      calc Rl = Rl * 1 := (Nat.mul_one Rl).symm
        _ ≤ Rl * (3 * Rl) := Nat.mul_le_mul_left Rl (by omega)
        _ = 3 * Rl ^ 2 := by ring
    set w := 3 * Rl ^ 2 - Rl with hwdef
    have hw : 3 * Rl ^ 2 = w + Rl := by rw [hwdef, Nat.sub_add_cancel hle]
    have hwZ : (3 : ℤ) * (Rl : ℤ) ^ 2 - (Rl : ℤ) = (w : ℤ) := by
      have hcast : ((3 * Rl ^ 2 : ℕ) : ℤ) = ((w + Rl : ℕ) : ℤ) := by exact_mod_cast hw
      push_cast at hcast
      linarith
    rw [hwZ] at hkey
    rw [e1, e2]
    exact_mod_cast hkey
  exact starved_v9_kill_sharp G (by omega) hm h3 hnf hpos ((2 * n - Xe - 12) / 24) hr1 hrn hMoore

end ACMax
end

/- ---------------------------------------- Counting.LargeNMain ------------- -/
section
/-!
# The ACMAX conjecture for large `n` — the self-contained half

For every `n ≥ 123`, among all simple graphs on `n` vertices with exactly `2(n-2)` edges the
algebraic connectivity is at most `2`, and the bound is attained by `K_{2,n-2}`.

This module is deliberately separate from `ACMaxConjecture.lean`, which carries the conjecture
for every `n ≥ 4`.  The point of the separation is that the large-`n` half is a genuinely
self-contained argument: it uses none of the finite-range machinery (`SmallCases/`, `AHL/`,
`Band/`, `Islands/`), and its whole dependency cone is `384` declarations across `15` modules,
against `7169` declarations for the full conjecture.

**The argument.**  A counterexample is normalized by two elementary cuts — a low-degree vertex
(Fiedler's `λ₂ ≤ δ`) and an edge between two degree-`3` vertices (`medge_moat_fires`) — into a
*starved census*: minimum degree `3`, no edge joining two degree-`3` vertices.  Such a census is
then impossible at `n ≥ 123` by `starved_dead_ge_123`, which plays a local cut certificate against
a global ball count:

* **local** — a short cycle among the degree-`≤ 4` vertices fires a two-cluster cut
  (`v9_short_cycle_fires_sharp`, at the bulk-credited threshold `12k + X ≤ 2n` of
  `Counting.MoatSharp`), so a never-firing census has large girth there;
* **global** — a set of large girth carrying positive edge excess needs more vertices than it has
  (`sqrt_double_count`, `Counting.SqrtGirth`).

The counting rows of `Counting.StarvedCensus` pin the degree profile tightly enough that the two
collide.
-/

namespace ACMax

open scoped Classical

/-- **The ACMAX conjecture for `n ≥ 123`.**  `K_{2,n-2}` has algebraic connectivity `2`, and every
simple graph on `Fin n` with exactly `2(n-2)` edges has algebraic connectivity at most `2`. -/
theorem acmax_conjecture_large_n (n : ℕ) (hn : 123 ≤ n) [Nonempty (Fin n)] :
    algConn (completeBipartiteGraph (Fin 2) (Fin (n - 2))) = 2 ∧
      ∀ G : SimpleGraph (Fin n), G.edgeFinset.card = 2 * (n - 2) → algConn G ≤ 2 := by
  refine ⟨algConn_completeBipartite_two n (by omega), fun G hm => ?_⟩
  let : DecidableEq (Fin n) := fun a b => Classical.propDecidable (a = b)
  rcases Classical.em (∃ v : Fin n, G.degree v ≤ 2) with hlow | hlow
  · -- a vertex of degree `≤ 2`: Fiedler's cut
    obtain ⟨u, hdeg⟩ := hlow
    refine algConn_le_two_of_low_degree_vertex G u hdeg ?_
    rw [Finset.sdiff_nonempty]
    intro hsub
    have huniv : (Finset.univ : Finset (Fin n)).card ≤ (insert u (G.neighborFinset u)).card :=
      Finset.card_le_card hsub
    rw [Finset.card_univ, Fintype.card_fin] at huniv
    have hcard : (insert u (G.neighborFinset u)).card ≤ 3 := by
      calc (insert u (G.neighborFinset u)).card
          ≤ (G.neighborFinset u).card + 1 := Finset.card_insert_le _ _
        _ = G.degree u + 1 := by rw [SimpleGraph.card_neighborFinset_eq_degree]
        _ ≤ 3 := by omega
    omega
  · simp only [not_exists, not_le] at hlow
    have h3 : ∀ v : Fin n, 3 ≤ G.degree v := fun v => by have := hlow v; omega
    by_cases hMedge : ∃ v w : Fin n, G.degree v = 3 ∧ G.degree w = 3 ∧ G.Adj v w
    · -- an edge between two degree-`3` vertices: the M-edge moat
      obtain ⟨u, p, hu, hp, hadj⟩ := hMedge
      exact medge_moat_fires (by omega) G hm h3 u p hadj hu hp
    · -- the starved census, killed import-free
      have hs0 : ∀ v w : Fin n, G.degree v = 3 → G.degree w = 3 → ¬G.Adj v w :=
        s0_of_no_medge G hMedge
      by_contra hnf
      exact starved_dead_ge_123 G hn hm h3 hnf hs0

end ACMax
end

