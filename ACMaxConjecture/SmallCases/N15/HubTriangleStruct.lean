import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.Certificates

/-!
# Structural leaves for the `n = 15`, `e(M) = 3`, `|D| = 8` hub-triangle corner

This file collects the *concrete, decidable-free* structural facts about the residual
configuration consumed by `exists_hub_triangle_config_residual` in `TwinCert15HubTriangle`:
the seven degree-`4` hubs (`Dᶜ`), the four `M`-isolated degree-`3` twins (`Iso`), and the
`M = P₄` path `L₁–c₁–c₂–L₂`.  Each lemma takes exactly the residual hypotheses it needs and
proves a single counting fact used by the triangle-forcing case analysis.
-/

namespace ACMax

open scoped Classical

namespace N15

/-- **Neighbour split.**  For every vertex `v`, the `D`-neighbours and the `Dᶜ`-neighbours
partition `N(v)`, so their cardinalities sum to `G.degree v`. -/
theorem nbr_split_DC (G : SimpleGraph (Fin 15)) (D : Finset (Fin 15)) (v : Fin 15) :
    (G.neighborFinset v ∩ D).card + (G.neighborFinset v ∩ Dᶜ).card = G.degree v := by
  classical
  have hdisj : Disjoint (G.neighborFinset v ∩ D) (G.neighborFinset v ∩ Dᶜ) := by
    apply Finset.disjoint_left.mpr
    intro a ha ha'
    rw [Finset.mem_inter] at ha ha'
    exact (Finset.mem_compl.mp ha'.2) ha.2
  have hun : (G.neighborFinset v ∩ D) ∪ (G.neighborFinset v ∩ Dᶜ) = G.neighborFinset v := by
    rw [← Finset.inter_union_distrib_left, Finset.union_compl, Finset.inter_univ]
  rw [← Finset.card_union_of_disjoint hdisj, hun, G.card_neighborFinset_eq_degree]

/-- **Leaf `D`-neighbourhoods.**  `L₁` has exactly one `D`-neighbour (`c₁`) and `L₂` exactly one
(`c₂`): the cover lemma `hcov` forces every `M`-edge to meet `{c₁, c₂}`, and `L₁ ≁ c₂`,
`L₂ ≁ c₁`. -/
theorem leaf_nbr_D (G : SimpleGraph (Fin 15)) (D : Finset (Fin 15)) (L₁ c₁ c₂ L₂ : Fin 15)
    (hcov : ∀ p q : Fin 15, p ∈ D → q ∈ D → G.Adj p q →
      p = c₁ ∨ p = c₂ ∨ q = c₁ ∨ q = c₂)
    (hL1D : L₁ ∈ D) (hc1D : c₁ ∈ D) (hL2D : L₂ ∈ D) (hc2D : c₂ ∈ D)
    (hac1L1 : G.Adj c₁ L₁) (hac2L2 : G.Adj c₂ L₂)
    (hnL1c2 : ¬G.Adj L₁ c₂) (hnc1L2 : ¬G.Adj c₁ L₂)
    (hL1nc1 : L₁ ≠ c₁) (hL1nc2 : L₁ ≠ c₂) (hL2nc1 : L₂ ≠ c₁) (hL2nc2 : L₂ ≠ c₂) :
    G.neighborFinset L₁ ∩ D = {c₁} ∧ G.neighborFinset L₂ ∩ D = {c₂} := by
  classical
  constructor
  · apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨?_, ?_⟩
    · rw [Finset.mem_inter, G.mem_neighborFinset]; exact ⟨hac1L1.symm, hc1D⟩
    · intro a ha
      rw [Finset.mem_inter, G.mem_neighborFinset] at ha
      obtain ⟨hadj, haD⟩ := ha
      rcases hcov L₁ a hL1D haD hadj with h | h | h | h
      · exact absurd h hL1nc1
      · exact absurd h hL1nc2
      · exact h
      · subst h; exact absurd hadj hnL1c2
  · apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨?_, ?_⟩
    · rw [Finset.mem_inter, G.mem_neighborFinset]; exact ⟨hac2L2.symm, hc2D⟩
    · intro a ha
      rw [Finset.mem_inter, G.mem_neighborFinset] at ha
      obtain ⟨hadj, haD⟩ := ha
      rcases hcov L₂ a hL2D haD hadj with h | h | h | h
      · exact absurd h hL2nc1
      · exact absurd h hL2nc2
      · subst h; exact absurd hadj.symm hnc1L2
      · exact h

/-- **Path hub-incidence counts.**  In the residual configuration the four path vertices send
exactly `2 + 1 + 1 + 2 = 6` edges to the seven hubs: `c₁, c₂` have one hub-neighbour each (in-`M`
degree `2`), while the leaves `L₁, L₂` have two each (in-`M` degree `1`). -/
theorem path_hub_incidence (G : SimpleGraph (Fin 15)) (D : Finset (Fin 15)) (L₁ c₁ c₂ L₂ : Fin 15)
    (hcov : ∀ p q : Fin 15, p ∈ D → q ∈ D → G.Adj p q →
      p = c₁ ∨ p = c₂ ∨ q = c₁ ∨ q = c₂)
    (hNc1D : G.neighborFinset c₁ ∩ D = {c₂, L₁}) (hNc2D : G.neighborFinset c₂ ∩ D = {c₁, L₂})
    (hL1D : L₁ ∈ D) (hc1D : c₁ ∈ D) (hL2D : L₂ ∈ D) (hc2D : c₂ ∈ D)
    (hac1L1 : G.Adj c₁ L₁) (hac2L2 : G.Adj c₂ L₂)
    (hnL1c2 : ¬G.Adj L₁ c₂) (hnc1L2 : ¬G.Adj c₁ L₂)
    (hc1deg : G.degree c₁ = 3) (hc2deg : G.degree c₂ = 3)
    (hL1deg : G.degree L₁ = 3) (hL2deg : G.degree L₂ = 3)
    (hL1nc1 : L₁ ≠ c₁) (hL1nc2 : L₁ ≠ c₂) (hL2nc1 : L₂ ≠ c₁) (hL2nc2 : L₂ ≠ c₂) :
    (G.neighborFinset c₁ ∩ Dᶜ).card = 1 ∧ (G.neighborFinset c₂ ∩ Dᶜ).card = 1 ∧
      (G.neighborFinset L₁ ∩ Dᶜ).card = 2 ∧ (G.neighborFinset L₂ ∩ Dᶜ).card = 2 := by
  classical
  obtain ⟨hNL1, hNL2⟩ := leaf_nbr_D G D L₁ c₁ c₂ L₂ hcov hL1D hc1D hL2D hc2D hac1L1 hac2L2
    hnL1c2 hnc1L2 hL1nc1 hL1nc2 hL2nc1 hL2nc2
  have hcard_c1 : (G.neighborFinset c₁ ∩ D).card = 2 := by
    rw [hNc1D]; rw [Finset.card_insert_of_notMem (by simp [Ne.symm hL1nc2]), Finset.card_singleton]
  have hcard_c2 : (G.neighborFinset c₂ ∩ D).card = 2 := by
    rw [hNc2D]; rw [Finset.card_insert_of_notMem (by simp [Ne.symm hL2nc1]),
      Finset.card_singleton]
  have hcard_L1 : (G.neighborFinset L₁ ∩ D).card = 1 := by rw [hNL1, Finset.card_singleton]
  have hcard_L2 : (G.neighborFinset L₂ ∩ D).card = 1 := by rw [hNL2, Finset.card_singleton]
  have s1 := nbr_split_DC G D c₁
  have s2 := nbr_split_DC G D c₂
  have s3 := nbr_split_DC G D L₁
  have s4 := nbr_split_DC G D L₂
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

/-- **Hub and twin counts.**  In the `|D| = 8` corner there are seven hubs (`Dᶜ.card = 7`) and four
`M`-isolated twins (`Iso.card = 4`): `D` is the disjoint union of the path `{L₁, c₁, c₂, L₂}` and
`Iso`, by `hisochar` (every non-path degree-`3` vertex is an isolated twin). -/
theorem hub_struct (G : SimpleGraph (Fin 15)) (D Iso : Finset (Fin 15)) (L₁ c₁ c₂ L₂ : Fin 15)
    (hIsodef : Iso = D.filter (fun v => (G.neighborFinset v ∩ D).card = 0))
    (hisochar : ∀ w : Fin 15, w ∈ D → w ≠ L₁ → w ≠ c₁ → w ≠ c₂ → w ≠ L₂ → w ∈ Iso)
    (hL1D : L₁ ∈ D) (hc1D : c₁ ∈ D) (hc2D : c₂ ∈ D) (hL2D : L₂ ∈ D)
    (hac1L1 : G.Adj c₁ L₁) (hc12 : G.Adj c₁ c₂) (hac2L2 : G.Adj c₂ L₂)
    (hnc1L2 : ¬G.Adj c₁ L₂) (hL1nc2 : L₁ ≠ c₂) (hL2nc1 : L₂ ≠ c₁)
    (hD8 : D.card = 8) :
    Dᶜ.card = 7 ∧ Iso.card = 4 := by
  classical
  have hDc : Dᶜ.card = 7 := by
    rw [Finset.card_compl, Fintype.card_fin, hD8]
  refine ⟨hDc, ?_⟩
  -- the four path vertices are pairwise distinct
  have hL1c1 : L₁ ≠ c₁ := (G.ne_of_adj hac1L1).symm
  have hc1c2 : c₁ ≠ c₂ := G.ne_of_adj hc12
  have hc2L2 : c₂ ≠ L₂ := G.ne_of_adj hac2L2
  have hL1L2 : L₁ ≠ L₂ := by
    rintro rfl; exact hnc1L2 hac1L1
  have hc1L2 : c₁ ≠ L₂ := (Ne.symm hL2nc1)
  set P : Finset (Fin 15) := {L₁, c₁, c₂, L₂} with hP
  have hPcard : P.card = 4 := by
    rw [hP, Finset.card_insert_of_notMem (by simp [hL1c1, hL1nc2, hL1L2]),
      Finset.card_insert_of_notMem (by simp [hc1c2, hc1L2]),
      Finset.card_insert_of_notMem (by simp [hc2L2]), Finset.card_singleton]
  have hIsoD : Iso ⊆ D := by rw [hIsodef]; exact Finset.filter_subset _ _
  have hPD : P ⊆ D := by
    intro x hx; rw [hP] at hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  -- path vertices are not isolated twins (each has a D-neighbour)
  have hPnIso : Disjoint P Iso := by
    rw [Finset.disjoint_left]
    intro x hxP hxIso
    rw [hIsodef, Finset.mem_filter] at hxIso
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem] at hxIso
    rw [hP] at hxP
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxP
    rcases hxP with rfl | rfl | rfl | rfl
    · exact hxIso.2 c₁ (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hac1L1.symm, hc1D⟩)
    · exact hxIso.2 c₂ (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hc12, hc2D⟩)
    · exact hxIso.2 c₁ (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hc12.symm, hc1D⟩)
    · exact hxIso.2 c₂ (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hac2L2.symm, hc2D⟩)
  have hcover : D ⊆ P ∪ Iso := by
    intro x hxD
    by_cases hx1 : x = L₁
    · subst hx1; exact Finset.mem_union_left _ (by rw [hP]; simp)
    by_cases hx2 : x = c₁
    · subst hx2; exact Finset.mem_union_left _ (by rw [hP]; simp)
    by_cases hx3 : x = c₂
    · subst hx3; exact Finset.mem_union_left _ (by rw [hP]; simp)
    by_cases hx4 : x = L₂
    · subst hx4; exact Finset.mem_union_left _ (by rw [hP]; simp)
    · exact Finset.mem_union_right _ (hisochar x hxD hx1 hx2 hx3 hx4)
  have hDeq : D = P ∪ Iso :=
    Finset.Subset.antisymm hcover (Finset.union_subset hPD hIsoD)
  have hcardU : (P ∪ Iso).card = P.card + Iso.card := Finset.card_union_of_disjoint hPnIso
  rw [hDeq, hcardU, hPcard] at hD8
  omega

/-- **Generic avoider count.**  If three vertices `a, b, c` together have at most `4`
hub-neighbours and there are `7` hubs, then at least `3` hubs avoid all of `a, b, c`. -/
theorem avoiders_ge_three_aux (G : SimpleGraph (Fin 15)) (D : Finset (Fin 15)) (a b c : Fin 15)
    (hDc7 : Dᶜ.card = 7)
    (hbound : (G.neighborFinset a ∩ Dᶜ).card + (G.neighborFinset b ∩ Dᶜ).card
      + (G.neighborFinset c ∩ Dᶜ).card ≤ 4) :
    3 ≤ (Dᶜ.filter (fun g => ¬G.Adj g a ∧ ¬G.Adj g b ∧ ¬G.Adj g c)).card := by
  classical
  set Av := Dᶜ.filter (fun g => ¬G.Adj g a ∧ ¬G.Adj g b ∧ ¬G.Adj g c) with hAv
  have hsub : Dᶜ ⊆ Av ∪ ((G.neighborFinset a ∩ Dᶜ) ∪
      ((G.neighborFinset b ∩ Dᶜ) ∪ (G.neighborFinset c ∩ Dᶜ))) := by
    intro g hg
    by_cases ha : G.Adj g a
    · exact Finset.mem_union_right _ (Finset.mem_union_left _
        (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr ha.symm, hg⟩))
    by_cases hb : G.Adj g b
    · exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_union_left _
        (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hb.symm, hg⟩)))
    by_cases hc : G.Adj g c
    · exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_union_right _
        (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hc.symm, hg⟩)))
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hg, ha, hb, hc⟩)
  have hcardle := Finset.card_le_card hsub
  have h1 := Finset.card_union_le Av ((G.neighborFinset a ∩ Dᶜ) ∪
      ((G.neighborFinset b ∩ Dᶜ) ∪ (G.neighborFinset c ∩ Dᶜ)))
  have h2 := Finset.card_union_le (G.neighborFinset a ∩ Dᶜ)
      ((G.neighborFinset b ∩ Dᶜ) ∪ (G.neighborFinset c ∩ Dᶜ))
  have h3 := Finset.card_union_le (G.neighborFinset b ∩ Dᶜ) (G.neighborFinset c ∩ Dᶜ)
  omega

/-- **Each cherry has at least three avoiding hubs.**  Cherry `{L₁, c₁, c₂}` collects only
`2 + 1 + 1 = 4` hub-incidences (`L₁` two, `c₁`/`c₂` one each), so `≥ 3` of the seven hubs avoid it;
symmetrically for `{c₁, c₂, L₂}`. -/
theorem cherry_avoiders_ge_three (G : SimpleGraph (Fin 15)) (D : Finset (Fin 15))
    (L₁ c₁ c₂ L₂ : Fin 15) (hDc7 : Dᶜ.card = 7)
    (hc1 : (G.neighborFinset c₁ ∩ Dᶜ).card = 1) (hc2 : (G.neighborFinset c₂ ∩ Dᶜ).card = 1)
    (hL1 : (G.neighborFinset L₁ ∩ Dᶜ).card = 2) (hL2 : (G.neighborFinset L₂ ∩ Dᶜ).card = 2) :
    3 ≤ (Dᶜ.filter (fun g => ¬G.Adj g L₁ ∧ ¬G.Adj g c₁ ∧ ¬G.Adj g c₂)).card ∧
      3 ≤ (Dᶜ.filter (fun g => ¬G.Adj g c₁ ∧ ¬G.Adj g c₂ ∧ ¬G.Adj g L₂)).card := by
  refine ⟨avoiders_ge_three_aux G D L₁ c₁ c₂ hDc7 (by omega),
    avoiders_ge_three_aux G D c₁ c₂ L₂ hDc7 (by omega)⟩

/-- **Cherry-avoider internal degree `≥ 2`.**  A degree-`4` hub whose every `D`-neighbour is
either a single allowed leaf or an `M`-isolated twin, with at most one twin-neighbour (fact `(W)`),
sends at most `2` edges into `D`, hence at least `2` edges to other hubs. -/
theorem avoider_internal_ge_two (G : SimpleGraph (Fin 15)) (D Iso : Finset (Fin 15))
    (g allowed : Fin 15) (hdg : G.degree g = 4) (hIso1 : (G.neighborFinset g ∩ Iso).card ≤ 1)
    (hclass : ∀ x : Fin 15, G.Adj g x → x ∈ D → x = allowed ∨ x ∈ Iso) :
    2 ≤ (G.neighborFinset g ∩ Dᶜ).card := by
  classical
  have hsub : G.neighborFinset g ∩ D ⊆ insert allowed (G.neighborFinset g ∩ Iso) := by
    intro x hx
    rw [Finset.mem_inter, G.mem_neighborFinset] at hx
    obtain ⟨hadj, hxD⟩ := hx
    rcases hclass x hadj hxD with h | h
    · exact Finset.mem_insert.mpr (Or.inl h)
    · exact Finset.mem_insert_of_mem (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hadj, h⟩)
  have hcard : (G.neighborFinset g ∩ D).card ≤ 2 := by
    calc (G.neighborFinset g ∩ D).card
        ≤ (insert allowed (G.neighborFinset g ∩ Iso)).card := Finset.card_le_card hsub
      _ ≤ (G.neighborFinset g ∩ Iso).card + 1 := Finset.card_insert_le _ _
      _ ≤ 2 := by omega
  have hsplit := nbr_split_DC G D g
  omega

/-- **Fully-free internal degree `≥ 3`.**  A degree-`4` hub all of whose `D`-neighbours are
`M`-isolated twins (it avoids every path vertex), with at most one twin-neighbour (fact `(W)`),
sends at most `1` edge into `D`, hence at least `3` edges to other hubs. -/
theorem fully_free_internal_ge_three (G : SimpleGraph (Fin 15)) (D Iso : Finset (Fin 15))
    (g : Fin 15) (hdg : G.degree g = 4) (hIso1 : (G.neighborFinset g ∩ Iso).card ≤ 1)
    (hclass : ∀ x : Fin 15, G.Adj g x → x ∈ D → x ∈ Iso) :
    3 ≤ (G.neighborFinset g ∩ Dᶜ).card := by
  classical
  have hsub : G.neighborFinset g ∩ D ⊆ G.neighborFinset g ∩ Iso := by
    intro x hx
    rw [Finset.mem_inter, G.mem_neighborFinset] at hx
    obtain ⟨hadj, hxD⟩ := hx
    exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hadj, hclass x hadj hxD⟩
  have hcard : (G.neighborFinset g ∩ D).card ≤ 1 := le_trans (Finset.card_le_card hsub) hIso1
  have hsplit := nbr_split_DC G D g
  omega

/-- **Path / Iso partition of `D`.**  The four path vertices and the `M`-isolated twins partition
`D`: `{L₁, c₁, c₂, L₂} ∪ Iso = D` and the two parts are disjoint. -/
theorem path_iso_partition (G : SimpleGraph (Fin 15)) (D Iso : Finset (Fin 15))
    (L₁ c₁ c₂ L₂ : Fin 15)
    (hIsodef : Iso = D.filter (fun v => (G.neighborFinset v ∩ D).card = 0))
    (hisochar : ∀ w : Fin 15, w ∈ D → w ≠ L₁ → w ≠ c₁ → w ≠ c₂ → w ≠ L₂ → w ∈ Iso)
    (hL1D : L₁ ∈ D) (hc1D : c₁ ∈ D) (hc2D : c₂ ∈ D) (hL2D : L₂ ∈ D)
    (hac1L1 : G.Adj c₁ L₁) (hc12 : G.Adj c₁ c₂) (hac2L2 : G.Adj c₂ L₂) :
    ({L₁, c₁, c₂, L₂} : Finset (Fin 15)) ∪ Iso = D ∧
      Disjoint ({L₁, c₁, c₂, L₂} : Finset (Fin 15)) Iso := by
  classical
  set P : Finset (Fin 15) := {L₁, c₁, c₂, L₂} with hP
  have hIsoD : Iso ⊆ D := by rw [hIsodef]; exact Finset.filter_subset _ _
  have hPD : P ⊆ D := by
    intro x hx; rw [hP] at hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  have hPnIso : Disjoint P Iso := by
    rw [Finset.disjoint_left]
    intro x hxP hxIso
    rw [hIsodef, Finset.mem_filter] at hxIso
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem] at hxIso
    rw [hP] at hxP
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxP
    rcases hxP with rfl | rfl | rfl | rfl
    · exact hxIso.2 c₁ (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hac1L1.symm, hc1D⟩)
    · exact hxIso.2 c₂ (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hc12, hc2D⟩)
    · exact hxIso.2 c₁ (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hc12.symm, hc1D⟩)
    · exact hxIso.2 c₂ (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hac2L2.symm, hc2D⟩)
  have hcover : D ⊆ P ∪ Iso := by
    intro x hxD
    by_cases hx1 : x = L₁
    · subst hx1; exact Finset.mem_union_left _ (by rw [hP]; simp)
    by_cases hx2 : x = c₁
    · subst hx2; exact Finset.mem_union_left _ (by rw [hP]; simp)
    by_cases hx3 : x = c₂
    · subst hx3; exact Finset.mem_union_left _ (by rw [hP]; simp)
    by_cases hx4 : x = L₂
    · subst hx4; exact Finset.mem_union_left _ (by rw [hP]; simp)
    · exact Finset.mem_union_right _ (hisochar x hxD hx1 hx2 hx3 hx4)
  exact ⟨Finset.Subset.antisymm (Finset.union_subset hPD hIsoD) hcover, hPnIso⟩

end N15

end ACMax
