import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N19.Core

/-!
# The `|D| = 10`, `e(M) = 5` dominating-edge double-star structure (`n = 19`)

With a dominating `M`-edge `c₁–c₂` and `Σ_D |N ∩ D| = 10`, both centres are
`D`-full: the incidence sum decomposes as `2x + 2y − 2 = 10` with
`x = |N(c₁) ∩ D| ≤ 3`, `y = |N(c₂) ∩ D| ≤ 3`, so `x = y = 3` — each centre
carries the other centre plus exactly two leaves.  No leaf touches the other
centre (the triangle `{ℓ, c₁, c₂}` has degree sum `9 ≤ 10`, killed by `hT`),
so each leaf has `M`-degree exactly `1` and the `M`-structure is the full
double-star on six vertices.
-/

namespace ACMax

open scoped Classical

namespace N19

set_option maxHeartbeats 1000000 in
/-- **The dominating-edge double-star structure at `|D| = 10`, `e(M) = 5`.** -/
theorem eM5_domedge_leaves_nineteen (G : SimpleGraph (Fin 19))
    (_h3 : ∀ v : Fin 19, 3 ≤ G.degree v)
    (hT : ¬∃ x y z : Fin 19, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    (_hD10 : (Finset.univ.filter (fun w : Fin 19 => G.degree w = 3)).card = 10)
    (c₁ c₂ : Fin 19) (hc1D : G.degree c₁ = 3) (hc2D : G.degree c₂ = 3)
    (hc12 : G.Adj c₁ c₂)
    (hcov : ∀ p q : Fin 19, G.degree p = 3 → G.degree q = 3 → G.Adj p q →
      p = c₁ ∨ p = c₂ ∨ q = c₁ ∨ q = c₂)
    (hsum10 : ∑ v ∈ Finset.univ.filter (fun w : Fin 19 => G.degree w = 3),
      (G.neighborFinset v ∩ Finset.univ.filter (fun w : Fin 19 => G.degree w = 3)).card
        = 10) :
    ∃ l₁ l₂ l₃ l₄ : Fin 19,
      l₁ ≠ l₂ ∧ l₁ ≠ l₃ ∧ l₁ ≠ l₄ ∧ l₂ ≠ l₃ ∧ l₂ ≠ l₄ ∧ l₃ ≠ l₄ ∧
      l₁ ≠ c₁ ∧ l₁ ≠ c₂ ∧ l₂ ≠ c₁ ∧ l₂ ≠ c₂ ∧
      l₃ ≠ c₁ ∧ l₃ ≠ c₂ ∧ l₄ ≠ c₁ ∧ l₄ ≠ c₂ ∧
      G.degree l₁ = 3 ∧ G.degree l₂ = 3 ∧ G.degree l₃ = 3 ∧ G.degree l₄ = 3 ∧
      G.Adj l₁ c₁ ∧ G.Adj l₂ c₁ ∧ G.Adj l₃ c₂ ∧ G.Adj l₄ c₂ ∧
      ¬G.Adj l₁ c₂ ∧ ¬G.Adj l₂ c₂ ∧ ¬G.Adj l₃ c₁ ∧ ¬G.Adj l₄ c₁ ∧
      (∀ w : Fin 19, G.Adj c₁ w → w = c₂ ∨ w = l₁ ∨ w = l₂) ∧
      (∀ w : Fin 19, G.Adj c₂ w → w = c₁ ∨ w = l₃ ∨ w = l₄) := by
  classical
  set D : Finset (Fin 19) := Finset.univ.filter (fun w : Fin 19 => G.degree w = 3) with hDdef
  have hmemD : ∀ v : Fin 19, v ∈ D ↔ G.degree v = 3 := by
    intro v; simp [hDdef]
  have hc1D' : c₁ ∈ D := (hmemD c₁).mpr hc1D
  have hc2D' : c₂ ∈ D := (hmemD c₂).mpr hc2D
  have hc2A : c₂ ∈ G.neighborFinset c₁ ∩ D :=
    Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hc12, hc2D'⟩
  have hc1B : c₁ ∈ G.neighborFinset c₂ ∩ D :=
    Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hc12.symm, hc1D'⟩
  have hxle : (G.neighborFinset c₁ ∩ D).card ≤ 3 := by
    calc (G.neighborFinset c₁ ∩ D).card ≤ (G.neighborFinset c₁).card :=
          Finset.card_le_card Finset.inter_subset_left
      _ = 3 := by rw [G.card_neighborFinset_eq_degree]; exact hc1D
  have hyle : (G.neighborFinset c₂ ∩ D).card ≤ 3 := by
    calc (G.neighborFinset c₂ ∩ D).card ≤ (G.neighborFinset c₂).card :=
          Finset.card_le_card Finset.inter_subset_left
      _ = 3 := by rw [G.card_neighborFinset_eq_degree]; exact hc2D
  have hxpos : 1 ≤ (G.neighborFinset c₁ ∩ D).card := Finset.card_pos.mpr ⟨c₂, hc2A⟩
  have hypos : 1 ≤ (G.neighborFinset c₂ ∩ D).card := Finset.card_pos.mpr ⟨c₁, hc1B⟩
  -- Split the incidence sum: the `c₁`-term, the `c₂`-term, and the leaf terms.
  have hc2e : c₂ ∈ D.erase c₁ := Finset.mem_erase.mpr ⟨hc12.ne', hc2D'⟩
  have hsplit1 : (G.neighborFinset c₁ ∩ D).card
      + ∑ v ∈ D.erase c₁, (G.neighborFinset v ∩ D).card
      = ∑ v ∈ D, (G.neighborFinset v ∩ D).card :=
    Finset.add_sum_erase D (fun v => (G.neighborFinset v ∩ D).card) hc1D'
  have hsplit2 : (G.neighborFinset c₂ ∩ D).card
      + ∑ v ∈ (D.erase c₁).erase c₂, (G.neighborFinset v ∩ D).card
      = ∑ v ∈ D.erase c₁, (G.neighborFinset v ∩ D).card :=
    Finset.add_sum_erase (D.erase c₁) (fun v => (G.neighborFinset v ∩ D).card) hc2e
  -- Every leaf's `D`-neighbourhood is its adjacency trace on `{c₁, c₂}`.
  have hper : ∀ v ∈ (D.erase c₁).erase c₂, G.neighborFinset v ∩ D
      = ({c₁, c₂} : Finset (Fin 19)).filter (fun c => G.Adj v c) := by
    intro v hv
    have hv2 : v ≠ c₂ := (Finset.mem_erase.mp hv).1
    have hv1 : v ≠ c₁ := (Finset.mem_erase.mp (Finset.mem_erase.mp hv).2).1
    have hvD : v ∈ D := (Finset.mem_erase.mp (Finset.mem_erase.mp hv).2).2
    ext w
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset, Finset.mem_filter,
      Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hadj, hwD⟩
      rcases hcov v w ((hmemD v).mp hvD) ((hmemD w).mp hwD) hadj with e | e | e | e
      · exact absurd e hv1
      · exact absurd e hv2
      · exact ⟨Or.inl e, hadj⟩
      · exact ⟨Or.inr e, hadj⟩
    · rintro ⟨hw, hadj⟩
      refine ⟨hadj, ?_⟩
      rcases hw with rfl | rfl
      · exact hc1D'
      · exact hc2D'
  have hcardpair : ∀ v : Fin 19,
      ((({c₁, c₂} : Finset (Fin 19))).filter (fun c => G.Adj v c)).card
        = (if G.Adj v c₁ then 1 else 0) + (if G.Adj v c₂ then 1 else 0) := by
    intro v
    rw [Finset.card_filter]
    exact Finset.sum_pair hc12.ne
  have hsumS : ∑ v ∈ (D.erase c₁).erase c₂, (G.neighborFinset v ∩ D).card
      = ((D.erase c₁).erase c₂ |>.filter (fun v => G.Adj v c₁)).card
        + ((D.erase c₁).erase c₂ |>.filter (fun v => G.Adj v c₂)).card := by
    rw [Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun v hv => ?_
    rw [hper v hv]
    exact hcardpair v
  -- The two leaf-count filters are the erased centre neighbourhoods.
  have hfilt1 : ((D.erase c₁).erase c₂ |>.filter (fun v => G.Adj v c₁))
      = (G.neighborFinset c₁ ∩ D).erase c₂ := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_inter,
      SimpleGraph.mem_neighborFinset]
    constructor
    · rintro ⟨⟨hwc2, _hwc1, hwD⟩, hadj⟩
      exact ⟨hwc2, hadj.symm, hwD⟩
    · rintro ⟨hwc2, hadj, hwD⟩
      exact ⟨⟨hwc2, hadj.ne', hwD⟩, hadj.symm⟩
  have hfilt2 : ((D.erase c₁).erase c₂ |>.filter (fun v => G.Adj v c₂))
      = (G.neighborFinset c₂ ∩ D).erase c₁ := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_inter,
      SimpleGraph.mem_neighborFinset]
    constructor
    · rintro ⟨⟨_hwc2, hwc1, hwD⟩, hadj⟩
      exact ⟨hwc1, hadj.symm, hwD⟩
    · rintro ⟨hwc1, hadj, hwD⟩
      exact ⟨⟨hadj.ne', hwc1, hwD⟩, hadj.symm⟩
  have he1 : ((G.neighborFinset c₁ ∩ D).erase c₂).card = (G.neighborFinset c₁ ∩ D).card - 1 :=
    Finset.card_erase_of_mem hc2A
  have he2 : ((G.neighborFinset c₂ ∩ D).erase c₁).card = (G.neighborFinset c₂ ∩ D).card - 1 :=
    Finset.card_erase_of_mem hc1B
  -- Assemble: `x + y + (x − 1) + (y − 1) = 10` with `x, y ≤ 3` forces `x = y = 3`.
  have h10 : (G.neighborFinset c₁ ∩ D).card + ((G.neighborFinset c₂ ∩ D).card
      + (((G.neighborFinset c₁ ∩ D).card - 1) + ((G.neighborFinset c₂ ∩ D).card - 1)))
      = 10 := by
    rw [← he1, ← he2, ← hfilt1, ← hfilt2, ← hsumS, hsplit2, hsplit1]
    exact hsum10
  have hx : (G.neighborFinset c₁ ∩ D).card = 3 := by omega
  have hy : (G.neighborFinset c₂ ∩ D).card = 3 := by omega
  -- Extract the two leaves on each side.
  have herase1 : ((G.neighborFinset c₁ ∩ D).erase c₂).card = 2 := by rw [he1, hx]
  have herase2 : ((G.neighborFinset c₂ ∩ D).erase c₁).card = 2 := by rw [he2, hy]
  obtain ⟨l₁, l₂, hl12, hset1⟩ := Finset.card_eq_two.mp herase1
  obtain ⟨l₃, l₄, hl34, hset2⟩ := Finset.card_eq_two.mp herase2
  have hmem1 : ∀ w : Fin 19, w = l₁ ∨ w = l₂ → w ≠ c₂ ∧ G.Adj c₁ w ∧ G.degree w = 3 := by
    intro w hw
    have hwe : w ∈ (G.neighborFinset c₁ ∩ D).erase c₂ := by
      rw [hset1]; rcases hw with rfl | rfl <;> simp
    rw [Finset.mem_erase] at hwe
    obtain ⟨hwc2, hwND⟩ := hwe
    obtain ⟨hwN, hwD⟩ := Finset.mem_inter.mp hwND
    exact ⟨hwc2, (G.mem_neighborFinset _ _).mp hwN, (hmemD w).mp hwD⟩
  have hmem2 : ∀ w : Fin 19, w = l₃ ∨ w = l₄ → w ≠ c₁ ∧ G.Adj c₂ w ∧ G.degree w = 3 := by
    intro w hw
    have hwe : w ∈ (G.neighborFinset c₂ ∩ D).erase c₁ := by
      rw [hset2]; rcases hw with rfl | rfl <;> simp
    rw [Finset.mem_erase] at hwe
    obtain ⟨hwc1, hwND⟩ := hwe
    obtain ⟨hwN, hwD⟩ := Finset.mem_inter.mp hwND
    exact ⟨hwc1, (G.mem_neighborFinset _ _).mp hwN, (hmemD w).mp hwD⟩
  obtain ⟨h1c2, ha1, hd1⟩ := hmem1 l₁ (Or.inl rfl)
  obtain ⟨h2c2, ha2, hd2⟩ := hmem1 l₂ (Or.inr rfl)
  obtain ⟨h3c1, ha3, hd3⟩ := hmem2 l₃ (Or.inl rfl)
  obtain ⟨h4c1, ha4, hd4⟩ := hmem2 l₄ (Or.inr rfl)
  -- No leaf reaches the opposite centre: the triangle has degree sum `9 ≤ 10`.
  have hn1 : ¬G.Adj l₁ c₂ := fun hadj =>
    hT ⟨c₁, l₁, c₂, ha1.ne, hadj.ne, hc12.ne, ha1, hadj, hc12, by omega⟩
  have hn2 : ¬G.Adj l₂ c₂ := fun hadj =>
    hT ⟨c₁, l₂, c₂, ha2.ne, hadj.ne, hc12.ne, ha2, hadj, hc12, by omega⟩
  have hn3 : ¬G.Adj l₃ c₁ := fun hadj =>
    hT ⟨c₂, l₃, c₁, ha3.ne, hadj.ne, hc12.ne', ha3, hadj, hc12.symm, by omega⟩
  have hn4 : ¬G.Adj l₄ c₁ := fun hadj =>
    hT ⟨c₂, l₄, c₁, ha4.ne, hadj.ne, hc12.ne', ha4, hadj, hc12.symm, by omega⟩
  -- Cross-side distinctness: a shared leaf would touch both centres.
  have h13 : l₁ ≠ l₃ := fun e => hn1 (by rw [e]; exact ha3.symm)
  have h14 : l₁ ≠ l₄ := fun e => hn1 (by rw [e]; exact ha4.symm)
  have h23 : l₂ ≠ l₃ := fun e => hn2 (by rw [e]; exact ha3.symm)
  have h24 : l₂ ≠ l₄ := fun e => hn2 (by rw [e]; exact ha4.symm)
  -- Centre-fullness: the three known neighbours exhaust the degree-`3` neighbourhood.
  have hsub1 : ({c₂, l₁, l₂} : Finset (Fin 19)) ⊆ G.neighborFinset c₁ := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rw [SimpleGraph.mem_neighborFinset]
    rcases hw with rfl | rfl | rfl
    · exact hc12
    · exact ha1
    · exact ha2
  have hcard1 : ({c₂, l₁, l₂} : Finset (Fin 19)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨fun e => h1c2 e.symm, fun e => h2c2 e.symm⟩),
      Finset.card_insert_of_notMem (by simp only [Finset.mem_singleton]; exact hl12),
      Finset.card_singleton]
  have hNcard1 : (G.neighborFinset c₁).card = 3 := by
    rw [G.card_neighborFinset_eq_degree]; exact hc1D
  have hNc1 : G.neighborFinset c₁ = {c₂, l₁, l₂} :=
    (Finset.eq_of_subset_of_card_le hsub1 (le_of_eq (hNcard1.trans hcard1.symm))).symm
  have hsub2 : ({c₁, l₃, l₄} : Finset (Fin 19)) ⊆ G.neighborFinset c₂ := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rw [SimpleGraph.mem_neighborFinset]
    rcases hw with rfl | rfl | rfl
    · exact hc12.symm
    · exact ha3
    · exact ha4
  have hcard2 : ({c₁, l₃, l₄} : Finset (Fin 19)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨fun e => h3c1 e.symm, fun e => h4c1 e.symm⟩),
      Finset.card_insert_of_notMem (by simp only [Finset.mem_singleton]; exact hl34),
      Finset.card_singleton]
  have hNcard2 : (G.neighborFinset c₂).card = 3 := by
    rw [G.card_neighborFinset_eq_degree]; exact hc2D
  have hNc2 : G.neighborFinset c₂ = {c₁, l₃, l₄} :=
    (Finset.eq_of_subset_of_card_le hsub2 (le_of_eq (hNcard2.trans hcard2.symm))).symm
  have hfull1 : ∀ w : Fin 19, G.Adj c₁ w → w = c₂ ∨ w = l₁ ∨ w = l₂ := by
    intro w hw
    have hmem : w ∈ G.neighborFinset c₁ := (G.mem_neighborFinset _ _).mpr hw
    rw [hNc1] at hmem
    simpa using hmem
  have hfull2 : ∀ w : Fin 19, G.Adj c₂ w → w = c₁ ∨ w = l₃ ∨ w = l₄ := by
    intro w hw
    have hmem : w ∈ G.neighborFinset c₂ := (G.mem_neighborFinset _ _).mpr hw
    rw [hNc2] at hmem
    simpa using hmem
  exact ⟨l₁, l₂, l₃, l₄, hl12, h13, h14, h23, h24, hl34,
    ha1.ne', h1c2, ha2.ne', h2c2, h3c1, ha3.ne', h4c1, ha4.ne',
    hd1, hd2, hd3, hd4, ha1.symm, ha2.symm, ha3.symm, ha4.symm,
    hn1, hn2, hn3, hn4, hfull1, hfull2⟩

end N19

end ACMax
