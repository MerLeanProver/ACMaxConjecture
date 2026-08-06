import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N17.Core
import ACMaxConjecture.SmallCases.Certificates
import ACMaxConjecture.SmallCases.N17.HubTriangleStruct

/-!
# The `|A| = 4` `C₄` corner of the `n = 17`, `e(M) = 2`, single-`P₃`-cherry hub-triangle obligation

This file supplies the genuinely new `n = 17` ingredients needed to close the cherry-avoider
triangle obligation `cherry_avoider_triangle` whose `|A| = 4` sub-case admits, by pure counting, a
triangle-free `C₄` of avoiders (the Mantel boundary `e(A) = 4 = ⌊16/4⌋`).

* `mantel_five` — a self-contained Mantel triangle extractor: a `5`-vertex set whose internal
  incidence total is `≥ 14` (`e ≥ 7 > ⌊25/4⌋ = 6`) carries a triangle.  Closes the `|A| = 5`
  sub-case outright.
* The `|A| = 4` rigidity and the `C₄`-exclusion via the residual configs live alongside.
-/

namespace ACMax

open scoped Classical

namespace N17

/-- **Mantel triangle on five vertices.**  If `A` has five vertices and its internal-incidence
total `∑_{g ∈ A} |N(g) ∩ A| = 2·e(A)` is at least `14` (so `e(A) ≥ 7 > ⌊25/4⌋ = 6`), then `A`
contains a triangle.  Proof: a triangle-free graph forces, for every edge `pq`, the disjointness
`N_A(p) ∩ N_A(q) = ∅` hence `deg_A p + deg_A q ≤ 5`; splitting `A` into the low-degree part
`Lo = {deg_A ≤ 2}` and the high-degree part `Hi = {deg_A ≥ 3}`, every `Hi`-vertex sends all its
edges into `Lo`, so `∑_A deg_A ≤ 2|Lo| + |Hi|·|Lo| ≤ 12 < 14`, a contradiction. -/
theorem mantel_five (G : SimpleGraph (Fin 17)) (A : Finset (Fin 17)) (hA5 : A.card = 5)
    (hsum : 14 ≤ ∑ g ∈ A, (G.neighborFinset g ∩ A).card) :
    ∃ a b c : Fin 17, a ∈ A ∧ b ∈ A ∧ c ∈ A ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      G.Adj a b ∧ G.Adj a c ∧ G.Adj b c := by
  classical
  by_contra hcon
  push Not at hcon
  have hTF : ∀ a b c : Fin 17, a ∈ A → b ∈ A → c ∈ A →
      G.Adj a b → G.Adj a c → G.Adj b c → False := by
    intro a b c ha hb hc h1 h2 h3
    exact hcon a b c ha hb hc h1.ne h2.ne h3.ne h1 h2 h3
  set d : Fin 17 → ℕ := fun g => (G.neighborFinset g ∩ A).card with hd
  have hpair : ∀ p ∈ A, ∀ q ∈ A, G.Adj p q → d p + d q ≤ 5 := by
    intro p hp q hq hpq
    have hdisj : Disjoint (G.neighborFinset p ∩ A) (G.neighborFinset q ∩ A) := by
      rw [Finset.disjoint_left]
      intro c hcp hcq
      rw [Finset.mem_inter, G.mem_neighborFinset] at hcp hcq
      obtain ⟨hpc, hcA⟩ := hcp
      obtain ⟨hqc, _⟩ := hcq
      exact hTF p q c hp hq hcA hpq hpc hqc
    have hsub : (G.neighborFinset p ∩ A) ∪ (G.neighborFinset q ∩ A) ⊆ A :=
      Finset.union_subset Finset.inter_subset_right Finset.inter_subset_right
    have hle := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdisj, hA5] at hle
    exact hle
  set Lo := A.filter (fun g => d g ≤ 2) with hLo
  set Hi := A.filter (fun g => ¬ d g ≤ 2) with hHi
  have hpart : Lo.card + Hi.card = 5 := by
    rw [hLo, hHi, Finset.card_filter_add_card_filter_not, hA5]
  have hNsubLo : ∀ a ∈ Hi, G.neighborFinset a ∩ A ⊆ Lo := by
    intro a haHi b hb
    rw [hHi, Finset.mem_filter] at haHi
    obtain ⟨haA, hda⟩ := haHi
    rw [Finset.mem_inter, G.mem_neighborFinset] at hb
    obtain ⟨hab, hbA⟩ := hb
    rw [hLo, Finset.mem_filter]
    refine ⟨hbA, ?_⟩
    have := hpair a haA b hbA hab
    omega
  have hHibound : ∀ a ∈ Hi, d a ≤ Lo.card := fun a ha =>
    Finset.card_le_card (hNsubLo a ha)
  have hHisum : ∑ a ∈ Hi, d a ≤ Hi.card * Lo.card := by
    calc ∑ a ∈ Hi, d a ≤ ∑ _a ∈ Hi, Lo.card := Finset.sum_le_sum hHibound
      _ = Hi.card * Lo.card := by rw [Finset.sum_const, smul_eq_mul]
  have hLosum : ∑ a ∈ Lo, d a ≤ 2 * Lo.card := by
    calc ∑ a ∈ Lo, d a ≤ ∑ _a ∈ Lo, 2 := by
          apply Finset.sum_le_sum
          intro a ha
          rw [hLo, Finset.mem_filter] at ha
          exact ha.2
      _ = 2 * Lo.card := by rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
  have hsplit : ∑ a ∈ A, d a = ∑ a ∈ Lo, d a + ∑ a ∈ Hi, d a := by
    rw [hLo, hHi]
    exact (Finset.sum_filter_add_sum_filter_not A (fun g => d g ≤ 2) d).symm
  have hsum' : 14 ≤ ∑ a ∈ A, d a := hsum
  rw [hsplit] at hsum'
  have hLc : Lo.card ≤ 5 := by omega
  interval_cases hlc : Lo.card <;> omega

/-- **Mantel upper bound on four vertices.**  A triangle-free `4`-vertex set has internal-incidence
total `∑_{g ∈ A} |N(g) ∩ A| ≤ 9` (the loose `Lo`/`Hi` bound; the true Mantel value is `8`, but the
slack `9` suffices for the `|A| = 4` counting after integer rounding).  Same `Lo`/`Hi` split as
`mantel_five`, with the per-edge bound `deg_A p + deg_A q ≤ 4`. -/
theorem mantel_quad_le (G : SimpleGraph (Fin 17)) (A : Finset (Fin 17)) (hA4 : A.card = 4)
    (hTF : ∀ a b c : Fin 17, a ∈ A → b ∈ A → c ∈ A →
      G.Adj a b → G.Adj a c → G.Adj b c → False) :
    ∑ g ∈ A, (G.neighborFinset g ∩ A).card ≤ 9 := by
  classical
  set d : Fin 17 → ℕ := fun g => (G.neighborFinset g ∩ A).card with hd
  have hpair : ∀ p ∈ A, ∀ q ∈ A, G.Adj p q → d p + d q ≤ 4 := by
    intro p hp q hq hpq
    have hdisj : Disjoint (G.neighborFinset p ∩ A) (G.neighborFinset q ∩ A) := by
      rw [Finset.disjoint_left]
      intro c hcp hcq
      rw [Finset.mem_inter, G.mem_neighborFinset] at hcp hcq
      obtain ⟨hpc, hcA⟩ := hcp
      obtain ⟨hqc, _⟩ := hcq
      exact hTF p q c hp hq hcA hpq hpc hqc
    have hsub : (G.neighborFinset p ∩ A) ∪ (G.neighborFinset q ∩ A) ⊆ A :=
      Finset.union_subset Finset.inter_subset_right Finset.inter_subset_right
    have hle := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdisj, hA4] at hle
    exact hle
  set Lo := A.filter (fun g => d g ≤ 2) with hLo
  set Hi := A.filter (fun g => ¬ d g ≤ 2) with hHi
  have hpart : Lo.card + Hi.card = 4 := by
    rw [hLo, hHi, Finset.card_filter_add_card_filter_not, hA4]
  have hNsubLo : ∀ a ∈ Hi, G.neighborFinset a ∩ A ⊆ Lo := by
    intro a haHi b hb
    rw [hHi, Finset.mem_filter] at haHi
    obtain ⟨haA, hda⟩ := haHi
    rw [Finset.mem_inter, G.mem_neighborFinset] at hb
    obtain ⟨hab, hbA⟩ := hb
    rw [hLo, Finset.mem_filter]
    refine ⟨hbA, ?_⟩
    have := hpair a haA b hbA hab
    omega
  have hHibound : ∀ a ∈ Hi, d a ≤ Lo.card := fun a ha =>
    Finset.card_le_card (hNsubLo a ha)
  have hHisum : ∑ a ∈ Hi, d a ≤ Hi.card * Lo.card := by
    calc ∑ a ∈ Hi, d a ≤ ∑ _a ∈ Hi, Lo.card := Finset.sum_le_sum hHibound
      _ = Hi.card * Lo.card := by rw [Finset.sum_const, smul_eq_mul]
  have hLosum : ∑ a ∈ Lo, d a ≤ 2 * Lo.card := by
    calc ∑ a ∈ Lo, d a ≤ ∑ _a ∈ Lo, 2 := by
          apply Finset.sum_le_sum
          intro a ha
          rw [hLo, Finset.mem_filter] at ha
          exact ha.2
      _ = 2 * Lo.card := by rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
  have hsplit : ∑ a ∈ A, d a = ∑ a ∈ Lo, d a + ∑ a ∈ Hi, d a := by
    rw [hLo, hHi]
    exact (Finset.sum_filter_add_sum_filter_not A (fun g => d g ≤ 2) d).symm
  rw [hsplit]
  have hLc : Lo.card ≤ 4 := by omega
  interval_cases hlc : Lo.card <;> omega

end N17

end ACMax
