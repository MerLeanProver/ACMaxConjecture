import ACMaxConjecture.AHL.AHLAmGm
import ACMaxConjecture.AHL.NBWalkCount
import ACMaxConjecture.Counting.SqrtGirth
import ACMaxConjecture.Band.Sum

/-!
# The AHL even-girth EDGE Moore bound — node B4 of the band discharge

This file lands node **B4** of the AHL band discharge, the *even-girth two-sided* companion of the
vertex-ball (SUM) Moore rung.  Writing `n = Fintype.card V`
and `D = ∑ v, G.degree v`, its per-cell kill condition is `t·v^(s+1) < (v + 2t)^(s+1) − v^(s+1)`
with `s + 1 = ⌊(L + 1)/2⌋`; it is load-bearing exactly on the odd-`L` stretch `n ∈ {77, …, 81}` the
SUM form misses.

The estimate comes from a **two-sided walk-pair injectivity**: for each
*undirected* edge `{a, b}` the endpoints of all non-backtracking walks whose
first dart is `(a, b)` or `(b, a)` and whose length is in `[1, s + 1]` are pairwise distinct.  This
gains the extra factor of two over the one-sided SUM count.

## Contents

* **`nb_walk_isPath_of_girth_sharp`** (B1) — at girth `> r`, every
  non-backtracking walk of length `≤ r` is a path; it is imported from
  `Band.Sum`.
* **`edge_collision`** — the four-case collision core: two non-backtracking walks of length `≤ s + 1`
  with the same endpoint and the same undirected first edge are equal (as bundled walks).
* **`nb_edge_ball_injectivity`** — the summed injectivity `2·Σ_{k=1}^{s+1} mₖ ≤ D·n` at girth
  `> 2s + 1`.
* **`nb_walk_count_avg_lower`** — the denominator-cleared per-length AM–GM lower bound
  `D·(D − n)^(k−1) ≤ mₖ·n^(k−1)`.
* **`ahl_edge_moore`** — the ℕ-cleared even-girth Moore bound
  `2·Σ_{k<s+1} (D − n)^k·n^(s−k) ≤ n^(s+1)`.
* **`ahl_edge_girth_bound`** — the girth-side contrapositive.
-/

namespace ACMax

open SimpleGraph Finset

/- The sharp non-backtracking path lemma (B1) is imported from `ACMaxConjecture.Band.Sum`
(`nb_walk_isPath_of_girth_sharp`) — a duplicate copy here would clash with it downstream. -/

variable {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableEq V] [DecidableRel G.Adj]

omit [Fintype V] [DecidableRel G.Adj] in
/-- **The two-sided collision core** (B4).  Two non-backtracking walks `w₁ : x₁ → v`, `w₂ : x₂ → v`
of length in `[1, s + 1]` with the same endpoint `v` and the same *undirected* first edge
`s(x₁, w₁.snd) = s(x₂, w₂.snd)` are equal as bundled walks, at girth `> 2s + 1`.  Both are paths
(`nb_walk_isPath_of_girth_sharp`, radius `s + 1`).  Destructuring the two first edges, the undirected
match splits into the **same-direction** case (`x₁ = x₂`, `w₁.snd = w₂.snd`), where dropping the
common first edge gives two paths whose distinctness would close a cycle of length `≤ 2s`, and the
**opposite-direction** case (`x₁ = w₂.snd`, `w₁.snd = x₂`), which is impossible: the tail of `w₁` and
`w₂` are distinct paths (differing at the first step by non-backtracking, or `w₂` closed) closing a
cycle of length `≤ 2s + 1`. -/
theorem edge_collision {s : ℕ}
    (hg : ∀ (v : V) (c : G.Walk v v), c.IsCycle → 2 * s + 1 < c.length)
    {x₁ x₂ v : V} (w₁ : G.Walk x₁ v) (w₂ : G.Walk x₂ v)
    (h1 : 1 ≤ w₁.length) (h1s : w₁.length ≤ s + 1) (h1nb : IsNonBacktracking w₁)
    (h2 : 1 ≤ w₂.length) (h2s : w₂.length ≤ s + 1) (h2nb : IsNonBacktracking w₂)
    (hedge : s(x₁, w₁.snd) = s(x₂, w₂.snd)) :
    (⟨x₁, v, w₁⟩ : Σ a : V, Σ b : V, G.Walk a b) = ⟨x₂, v, w₂⟩ := by
  have hgS : ∀ (u : V) (c : G.Walk u u), c.IsCycle → s + 1 < c.length := by
    intro u c hc; have := hg u c hc; omega
  have hP1 : w₁.IsPath := nb_walk_isPath_of_girth_sharp G hgS w₁ h1nb h1s
  have hP2 : w₂.IsPath := nb_walk_isPath_of_girth_sharp G hgS w₂ h2nb h2s
  obtain ⟨y₁, e₁, p₁, rfl⟩ := Walk.not_nil_iff.mp (Walk.not_nil_iff_lt_length.mpr h1)
  obtain ⟨y₂, e₂, p₂, rfl⟩ := Walk.not_nil_iff.mp (Walk.not_nil_iff_lt_length.mpr h2)
  simp only [Walk.snd_cons] at hedge
  rw [Walk.length_cons] at h1s h2s
  have hl1 : p₁.length ≤ s := by omega
  have hl2 : p₂.length ≤ s := by omega
  have hp1 : p₁.IsPath := ((Walk.cons_isPath_iff e₁ p₁).mp hP1).1
  have hp2 : p₂.IsPath := ((Walk.cons_isPath_iff e₂ p₂).mp hP2).1
  rcases Sym2.eq_iff.mp hedge with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · subst ha; subst hb
    have hpp : p₁ = p₂ := by
      by_contra hne
      exact no_short_cycle_of_paths G hg hp1 hp2 hne (by omega)
    subst hpp
    rfl
  · subst y₂; subst x₂
    exfalso
    by_cases hnil : p₁.Nil
    · have hyv : y₁ = v := hnil.eq
      subst hyv
      exact Walk.not_nil_cons (Walk.isPath_iff_nil.mp hP2)
    · have hsnd2 : (Walk.cons e₂ p₂).snd = x₁ := Walk.snd_cons p₂ e₂
      have hsnd1 : p₁.snd ≠ x₁ := by
        intro hc
        have hpos : 0 < p₁.length := Walk.not_nil_iff_lt_length.mp hnil
        have hhead := h1nb 0 (by rw [Walk.length_cons]; omega)
        rw [Walk.getVert_zero] at hhead
        apply hhead
        rw [show (0 : ℕ) + 2 = 1 + 1 by rfl, Walk.getVert_cons_succ]
        exact hc
      have hne : p₁ ≠ Walk.cons e₂ p₂ := by
        intro heq; rw [heq, hsnd2] at hsnd1; exact hsnd1 rfl
      exact no_short_cycle_of_paths G hg hp1 hP2 hne (by rw [Walk.length_cons]; omega)

/-- **The two-sided (edge) injectivity, summed** (B4).  If there is no cycle of length `≤ 2s + 1`,
then `2·Σ_{k=1}^{s+1} mₖ ≤ D·n`.  Each non-backtracking walk of length in `[1, s + 1]` is tagged by
its undirected first edge and its endpoint; `edge_collision` makes this tag injective, and the tag
lands in `edgeFinset ×ˢ univ` (size `|E|·n = (D/2)·n`). -/
theorem nb_edge_ball_injectivity {s : ℕ}
    (hg : ∀ (v : V) (c : G.Walk v v), c.IsCycle → 2 * s + 1 < c.length) :
    2 * ∑ k ∈ Finset.Icc 1 (s + 1), nbTotalWalks G k ≤ (∑ v, G.degree v) * Fintype.card V := by
  classical
  set W : Finset (Σ x : V, Σ v : V, G.Walk x v) :=
    (Finset.Icc 1 (s + 1)).biUnion (fun k => nbAll (G := G) k) with hW
  have hcardW : W.card = ∑ k ∈ Finset.Icc 1 (s + 1), nbTotalWalks G k := by
    rw [hW, Finset.card_biUnion]
    · exact Finset.sum_congr rfl (fun k _ => card_nbAll k)
    · intro k _ k' _ hkk'
      refine Finset.disjoint_left.mpr fun t ht ht' => ?_
      exact hkk' ((mem_nbAll.mp ht).1.symm.trans (mem_nbAll.mp ht').1)
  have hmaps : Set.MapsTo (fun t : Σ x : V, Σ v : V, G.Walk x v => (s(t.1, t.2.2.snd), t.2.1))
      ↑W ↑(G.edgeFinset ×ˢ (Finset.univ : Finset V)) := by
    intro t ht
    obtain ⟨x, v, w⟩ := t
    rw [Finset.mem_coe, hW, Finset.mem_biUnion] at ht
    obtain ⟨k, hk, htk⟩ := ht
    obtain ⟨hlen, _⟩ := mem_nbAll.mp htk
    have hklen : 1 ≤ w.length := by rw [hlen]; exact (Finset.mem_Icc.mp hk).1
    have hadj : G.Adj x w.snd := w.adj_snd (Walk.not_nil_iff_lt_length.mpr hklen)
    show (s(x, w.snd), v) ∈ ↑(G.edgeFinset ×ˢ (Finset.univ : Finset V))
    rw [Finset.mem_product]
    exact ⟨by rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]; exact hadj,
      Finset.mem_univ _⟩
  have hinj : Set.InjOn (fun t : Σ x : V, Σ v : V, G.Walk x v => (s(t.1, t.2.2.snd), t.2.1)) ↑W := by
    intro t ht t' ht' hφeq
    obtain ⟨x₁, v₁, w₁⟩ := t
    obtain ⟨x₂, v₂, w₂⟩ := t'
    rw [Finset.mem_coe, hW, Finset.mem_biUnion] at ht ht'
    obtain ⟨k, hk, htk⟩ := ht
    obtain ⟨k', hk', ht'k⟩ := ht'
    obtain ⟨hlen, hnb⟩ := mem_nbAll.mp htk
    obtain ⟨hlen', hnb'⟩ := mem_nbAll.mp ht'k
    simp only [Prod.mk.injEq] at hφeq
    obtain ⟨hE, hv⟩ := hφeq
    subst hv
    obtain ⟨hk1, hk1s⟩ := Finset.mem_Icc.mp hk
    obtain ⟨hk2, hk2s⟩ := Finset.mem_Icc.mp hk'
    refine edge_collision hg w₁ w₂ ?_ ?_ hnb ?_ ?_ hnb' hE
    · rw [hlen]; exact hk1
    · rw [hlen]; exact hk1s
    · rw [hlen']; exact hk2
    · rw [hlen']; exact hk2s
  have hle : W.card ≤ (G.edgeFinset ×ˢ (Finset.univ : Finset V)).card :=
    Finset.card_le_card_of_injOn _ hmaps hinj
  calc 2 * ∑ k ∈ Finset.Icc 1 (s + 1), nbTotalWalks G k
      = 2 * W.card := by rw [hcardW]
    _ ≤ 2 * (G.edgeFinset ×ˢ (Finset.univ : Finset V)).card := by omega
    _ = 2 * (G.edgeFinset.card * Fintype.card V) := by
        rw [Finset.card_product, Finset.card_univ]
    _ = (2 * G.edgeFinset.card) * Fintype.card V := by ring
    _ = (∑ v, G.degree v) * Fintype.card V := by
        rw [← SimpleGraph.sum_degrees_eq_twice_card_edges]

/-- **The denominator-cleared AM–GM walk-count lower bound.**  Under `δ ≥ 2` (and `V` nonempty), for
`1 ≤ k`, `D·(D − n)^(k−1) ≤ mₖ·n^(k−1)`.  This is the ℝ AM–GM lower bound
`D·((D − n)/n)^(k−1) ≤ mₖ` (`lambda_ge`, `nb_amgm_lambda`) multiplied through by `n^(k−1)` and cast
to `ℕ` via `n ≤ D`; it is the sharp Moore ingredient the edge sum consumes. -/
theorem nb_walk_count_avg_lower (hδ2 : ∀ v, 2 ≤ G.degree v) [Nonempty V] {k : ℕ} (hk : 1 ≤ k) :
    (∑ v, G.degree v) * ((∑ v, G.degree v) - Fintype.card V) ^ (k - 1) ≤
      nbTotalWalks G k * (Fintype.card V) ^ (k - 1) := by
  have hn : 0 < Fintype.card V := Fintype.card_pos
  have hn' : (0 : ℝ) < (Fintype.card V : ℝ) := by exact_mod_cast hn
  have hnD : Fintype.card V ≤ ∑ v, G.degree v := by
    have h : ∑ _v : V, 1 ≤ ∑ v, G.degree v := Finset.sum_le_sum fun v _ => by have := hδ2 v; omega
    simpa using h
  have hDge : (2 * Fintype.card V : ℝ) ≤ ∑ v, (G.degree v : ℝ) := by
    have h : ∑ _v : V, (2 : ℝ) ≤ ∑ v, (G.degree v : ℝ) :=
      Finset.sum_le_sum fun v _ => by exact_mod_cast hδ2 v
    simpa [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm] using h
  have hDpos : (0 : ℝ) < ∑ v, (G.degree v : ℝ) := by linarith
  have hbase : (0 : ℝ) ≤ ((∑ v, (G.degree v : ℝ)) - Fintype.card V) / Fintype.card V :=
    div_nonneg (by linarith) hn'.le
  have hpow : (((∑ v, (G.degree v : ℝ)) - Fintype.card V) / Fintype.card V) ^ (k - 1)
      ≤ (Lambda G) ^ (k - 1) := pow_le_pow_left₀ hbase (lambda_ge hδ2 hn) (k - 1)
  have hlam_np : (Lambda G) ^ ((k : ℝ) - 1) = (Lambda G) ^ (k - 1) := by
    rw [show ((k : ℝ) - 1) = ((k - 1 : ℕ) : ℝ) by rw [Nat.cast_sub hk, Nat.cast_one],
      Real.rpow_natCast]
  have hreal : (∑ v, (G.degree v : ℝ)) *
        (((∑ v, (G.degree v : ℝ)) - Fintype.card V) / Fintype.card V) ^ (k - 1) ≤
      (nbTotalWalks G k : ℝ) := by
    calc (∑ v, (G.degree v : ℝ)) *
            (((∑ v, (G.degree v : ℝ)) - Fintype.card V) / Fintype.card V) ^ (k - 1)
        ≤ (∑ v, (G.degree v : ℝ)) * (Lambda G) ^ (k - 1) :=
          mul_le_mul_of_nonneg_left hpow hDpos.le
      _ ≤ (nbTotalWalks G k : ℝ) := by have h := nb_amgm_lambda hδ2 hk; rwa [hlam_np] at h
  have hpn : (0 : ℝ) ≤ (Fintype.card V : ℝ) ^ (k - 1) := by positivity
  have hmul := mul_le_mul_of_nonneg_right hreal hpn
  rw [mul_assoc, ← mul_pow, div_mul_cancel₀ _ (ne_of_gt hn')] at hmul
  have hDcast : ((∑ v, G.degree v : ℕ) : ℝ) = ∑ v, (G.degree v : ℝ) := by push_cast; rfl
  rw [← hDcast] at hmul
  rw [show ((∑ v, G.degree v : ℕ) : ℝ) - (Fintype.card V : ℝ)
        = (((∑ v, G.degree v) - Fintype.card V : ℕ) : ℝ) from (Nat.cast_sub hnD).symm] at hmul
  exact_mod_cast hmul

/-- **The even-girth (EDGE) Moore bound** (B4).  Under `δ ≥ 2` (and `V` nonempty) with no cycle of
length `≤ 2s + 1`, the ℕ-cleared even-girth Moore inequality
`2·Σ_{k<s+1} (D − n)^k·n^(s−k) ≤ n^(s+1)` holds.  Combining the two-sided injectivity
`2·Σ mₖ ≤ D·n` with the per-length AM–GM lower bound `D·(D − n)^(k−1) ≤ mₖ·n^(k−1)` gives
`D·(2·S) ≤ D·n^(s+1)` after clearing; cancel `D > 0`. -/
theorem ahl_edge_moore (hδ2 : ∀ v, 2 ≤ G.degree v) [Nonempty V] {s : ℕ}
    (hg : ∀ (v : V) (c : G.Walk v v), c.IsCycle → 2 * s + 1 < c.length) :
    2 * ∑ k ∈ Finset.range (s + 1),
        ((∑ v, G.degree v) - Fintype.card V) ^ k * (Fintype.card V) ^ (s - k)
      ≤ (Fintype.card V) ^ (s + 1) := by
  set n := Fintype.card V with hn_def
  set D := ∑ v, G.degree v with hD_def
  have hn : 0 < n := Fintype.card_pos
  have hnD : n ≤ D := by
    rw [hn_def, hD_def]
    have h : ∑ _v : V, 1 ≤ ∑ v, G.degree v := Finset.sum_le_sum fun v _ => by have := hδ2 v; omega
    simpa using h
  have hDpos : 0 < D := by omega
  set S := ∑ k ∈ Finset.range (s + 1), (D - n) ^ k * n ^ (s - k) with hS_def
  set Smk := ∑ k ∈ Finset.Icc 1 (s + 1), nbTotalWalks G k with hSmk_def
  have hSre : ∑ k ∈ Finset.Icc 1 (s + 1), (D - n) ^ (k - 1) * n ^ (s - (k - 1)) = S := by
    rw [hS_def, ← Finset.Ico_add_one_right_eq_Icc 1 (s + 1), Finset.sum_Ico_eq_sum_range]
    apply Finset.sum_congr
    · rw [Nat.add_sub_cancel]
    · intro i _; rw [show 1 + i - 1 = i by omega]
  have hstar : D * S ≤ n ^ s * Smk := by
    rw [← hSre, hSmk_def, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    obtain ⟨hk1, hks⟩ := Finset.mem_Icc.mp hk
    have hlow := nb_walk_count_avg_lower hδ2 hk1
    rw [← hn_def, ← hD_def] at hlow
    have hks' : k - 1 ≤ s := by omega
    calc D * ((D - n) ^ (k - 1) * n ^ (s - (k - 1)))
        = (D * (D - n) ^ (k - 1)) * n ^ (s - (k - 1)) := by ring
      _ ≤ (nbTotalWalks G k * n ^ (k - 1)) * n ^ (s - (k - 1)) :=
          Nat.mul_le_mul hlow (le_refl _)
      _ = nbTotalWalks G k * (n ^ (k - 1) * n ^ (s - (k - 1))) := by ring
      _ = nbTotalWalks G k * n ^ s := by rw [← pow_add, Nat.add_sub_cancel' hks']
      _ = n ^ s * nbTotalWalks G k := by ring
  have hinj : 2 * Smk ≤ D * n := by
    rw [hSmk_def, hn_def, hD_def]; exact nb_edge_ball_injectivity hg
  have key : D * (2 * S) ≤ D * n ^ (s + 1) := by
    calc D * (2 * S) = 2 * (D * S) := by ring
      _ ≤ 2 * (n ^ s * Smk) := Nat.mul_le_mul (le_refl _) hstar
      _ = n ^ s * (2 * Smk) := by ring
      _ ≤ n ^ s * (D * n) := Nat.mul_le_mul (le_refl _) hinj
      _ = D * n ^ (s + 1) := by rw [pow_succ]; ring
  exact Nat.le_of_mul_le_mul_left key hDpos

/-- **The girth-side corollary** (B4).  Contrapositive of `ahl_edge_moore`: under `δ ≥ 2` (and `V`
nonempty), if `n^(s+1) < 2·Σ_{k<s+1} (D − n)^k·n^(s−k)` then `G` contains a cycle of length
`≤ 2s + 1`.  This is the form the band discharge instantiates at the `V₉/2`-core for the odd-`L`
stretch `n ∈ {77, …, 81}`. -/
theorem ahl_edge_girth_bound (hδ2 : ∀ v, 2 ≤ G.degree v) [Nonempty V] {s : ℕ}
    (hbig : (Fintype.card V) ^ (s + 1)
        < 2 * ∑ k ∈ Finset.range (s + 1),
            ((∑ v, G.degree v) - Fintype.card V) ^ k * (Fintype.card V) ^ (s - k)) :
    ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ c.length ≤ 2 * s + 1 := by
  by_contra h
  have hg : ∀ (v : V) (c : G.Walk v v), c.IsCycle → 2 * s + 1 < c.length := by
    intro v c hc
    by_contra hlen
    exact h ⟨v, c, hc, not_lt.mp hlen⟩
  exact absurd (ahl_edge_moore hδ2 hg) (not_le.mpr hbig)

end ACMax
