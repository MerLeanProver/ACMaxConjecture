import ACMaxConjecture.Spectral.TestVector
import ACMaxConjecture.Counting.CompactCell
import ACMaxConjecture.Counting.DoubleStar


/-!
# Class-vector and two-cluster certificates

For a partition of the vertex set, a class-constant test vector reduces the
Rayleigh quotient to class sizes and ordered inter-class edge counts.  The
master theorem `algConn_le_two_of_class_vector` packages that reduction.

* `classSize c i` — the size of class `i`;
* `interEdges G c i j` — the number of **ordered** adjacent pairs `(u,v)` with
  `u` in class `i` and `v` in class `j` (`interEdges i j = interEdges j i`;
  the diagonal counts internal edges twice but is killed by `(x i − x i)² = 0`);
* `algConn_le_two_of_class_vector` — the master: a class-valued vector `x`
  with `Σᵢ nᵢ xᵢ = 0` and

    `Σᵢⱼ Eᵢⱼ (xᵢ − xⱼ)² ≤ 4·Σᵢ nᵢ xᵢ²`

  certifies `algConn G ≤ 2`  (the `4` is `2 × 2`: one factor because ordered
  pairs double-count edges, one from the target `λ₂ ≤ 2`);
* `algConn_le_two_of_two_clusters` specializes the master to two active
  clusters separated by a zero-valued moat.  This is the form used by the moat
  arguments in `Counting.Moats`.
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



end ACMax
