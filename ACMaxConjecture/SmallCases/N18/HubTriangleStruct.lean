import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.Certificates

/-!
# Structural leaves for the `n = 18`, `e(M) = 3`, `|D| = 8` hub-triangle corner

This file collects the *concrete, decidable-free* structural facts about the residual
configuration consumed by `exists_hub_triangle_config_residual_eighteen` in
`TwinCert18HubTriangle`: the **ten** degree-`4` hubs (`Dᶜ`), the four `M`-isolated degree-`3`
twins (`Iso`), and the `M = P₄` path `L₁–c₁–c₂–L₂`.  Each lemma takes exactly the residual
hypotheses it needs and proves a single counting fact used by the triangle-forcing case analysis.

The `n = 18` deltas from `n = 17` are `|Hub| = 10` (vs `9`), so each cherry has `≥ 6` avoiders
(vs `≥ 5`) and the hub-internal-degree total is `∑ int = 4·10 − 6 − 12 = 22` (vs `18`).  The wider
budget pins the fully-free count to `|FF| ∈ {2, 3, 4, 5, 6, 7}`.
-/

namespace ACMax

open scoped Classical

namespace N18

/-- **Neighbour split.**  For every vertex `v`, the `D`-neighbours and the `Dᶜ`-neighbours
partition `N(v)`, so their cardinalities sum to `G.degree v`. -/
theorem nbr_split_DC (G : SimpleGraph (Fin 18)) (D : Finset (Fin 18)) (v : Fin 18) :
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
theorem leaf_nbr_D (G : SimpleGraph (Fin 18)) (D : Finset (Fin 18)) (L₁ c₁ c₂ L₂ : Fin 18)
    (hcov : ∀ p q : Fin 18, p ∈ D → q ∈ D → G.Adj p q →
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
exactly `2 + 1 + 1 + 2 = 6` edges to the nine hubs: `c₁, c₂` have one hub-neighbour each (in-`M`
degree `2`), while the leaves `L₁, L₂` have two each (in-`M` degree `1`). -/
theorem path_hub_incidence (G : SimpleGraph (Fin 18)) (D : Finset (Fin 18)) (L₁ c₁ c₂ L₂ : Fin 18)
    (hcov : ∀ p q : Fin 18, p ∈ D → q ∈ D → G.Adj p q →
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

/-- **Each `M`-isolated twin has exactly three hub-neighbours.**  By definition `Iso` is the set of
degree-`3` vertices with no `D`-neighbour, so all three of its edges go to hubs. -/
theorem iso_three_hub_nbrs (G : SimpleGraph (Fin 18)) (D Iso : Finset (Fin 18))
    (hIsodef : Iso = D.filter (fun v => (G.neighborFinset v ∩ D).card = 0))
    (hIsoprop : ∀ v ∈ Iso, G.degree v = 3 ∧ (∀ w : Fin 18, G.Adj v w → G.degree w ≠ 3))
    (t : Fin 18) (htIso : t ∈ Iso) :
    G.neighborFinset t ∩ D = ∅ ∧ (G.neighborFinset t ∩ Dᶜ).card = 3 := by
  classical
  have htmem : t ∈ D ∧ (G.neighborFinset t ∩ D).card = 0 := by
    rw [hIsodef, Finset.mem_filter] at htIso; exact htIso
  have hempty : G.neighborFinset t ∩ D = ∅ := Finset.card_eq_zero.mp htmem.2
  have htdeg : G.degree t = 3 := (hIsoprop t htIso).1
  have hsplit := nbr_split_DC G D t
  rw [htmem.2, htdeg] at hsplit
  exact ⟨hempty, by omega⟩

/-- **Hub and twin counts.**  In the `|D| = 8` corner there are ten hubs (`Dᶜ.card = 10`) and four
`M`-isolated twins (`Iso.card = 4`): `D` is the disjoint union of the path `{L₁, c₁, c₂, L₂}` and
`Iso`, by `hisochar` (every non-path degree-`3` vertex is an isolated twin). -/
theorem hub_struct (G : SimpleGraph (Fin 18)) (D Iso : Finset (Fin 18)) (L₁ c₁ c₂ L₂ : Fin 18)
    (hIsodef : Iso = D.filter (fun v => (G.neighborFinset v ∩ D).card = 0))
    (hisochar : ∀ w : Fin 18, w ∈ D → w ≠ L₁ → w ≠ c₁ → w ≠ c₂ → w ≠ L₂ → w ∈ Iso)
    (hL1D : L₁ ∈ D) (hc1D : c₁ ∈ D) (hc2D : c₂ ∈ D) (hL2D : L₂ ∈ D)
    (hac1L1 : G.Adj c₁ L₁) (hc12 : G.Adj c₁ c₂) (hac2L2 : G.Adj c₂ L₂)
    (hnc1L2 : ¬G.Adj c₁ L₂) (hL1nc2 : L₁ ≠ c₂) (hL2nc1 : L₂ ≠ c₁)
    (hD8 : D.card = 8) :
    Dᶜ.card = 10 ∧ Iso.card = 4 := by
  classical
  have hDc : Dᶜ.card = 10 := by
    rw [Finset.card_compl, Fintype.card_fin, hD8]
  refine ⟨hDc, ?_⟩
  have hL1c1 : L₁ ≠ c₁ := (G.ne_of_adj hac1L1).symm
  have hc1c2 : c₁ ≠ c₂ := G.ne_of_adj hc12
  have hc2L2 : c₂ ≠ L₂ := G.ne_of_adj hac2L2
  have hL1L2 : L₁ ≠ L₂ := by
    rintro rfl; exact hnc1L2 hac1L1
  have hc1L2 : c₁ ≠ L₂ := (Ne.symm hL2nc1)
  set P : Finset (Fin 18) := {L₁, c₁, c₂, L₂} with hP
  have hPcard : P.card = 4 := by
    rw [hP, Finset.card_insert_of_notMem (by simp [hL1c1, hL1nc2, hL1L2]),
      Finset.card_insert_of_notMem (by simp [hc1c2, hc1L2]),
      Finset.card_insert_of_notMem (by simp [hc2L2]), Finset.card_singleton]
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
  have hDeq : D = P ∪ Iso :=
    Finset.Subset.antisymm hcover (Finset.union_subset hPD hIsoD)
  have hcardU : (P ∪ Iso).card = P.card + Iso.card := Finset.card_union_of_disjoint hPnIso
  rw [hDeq, hcardU, hPcard] at hD8
  omega

/-- **Generic avoider count.**  If three vertices `a, b, c` together have at most `4`
hub-neighbours and there are `10` hubs, then at least `6` hubs avoid all of `a, b, c`. -/
theorem avoiders_ge_six_aux (G : SimpleGraph (Fin 18)) (D : Finset (Fin 18)) (a b c : Fin 18)
    (hDc9 : Dᶜ.card = 10)
    (hbound : (G.neighborFinset a ∩ Dᶜ).card + (G.neighborFinset b ∩ Dᶜ).card
      + (G.neighborFinset c ∩ Dᶜ).card ≤ 4) :
    6 ≤ (Dᶜ.filter (fun g => ¬G.Adj g a ∧ ¬G.Adj g b ∧ ¬G.Adj g c)).card := by
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

/-- **Each cherry has at least six avoiding hubs.**  Cherry `{L₁, c₁, c₂}` collects only
`2 + 1 + 1 = 4` hub-incidences (`L₁` two, `c₁`/`c₂` one each), so `≥ 6` of the ten hubs avoid it;
symmetrically for `{c₁, c₂, L₂}`. -/
theorem cherry_avoiders_ge_six (G : SimpleGraph (Fin 18)) (D : Finset (Fin 18))
    (L₁ c₁ c₂ L₂ : Fin 18) (hDc9 : Dᶜ.card = 10)
    (hc1 : (G.neighborFinset c₁ ∩ Dᶜ).card = 1) (hc2 : (G.neighborFinset c₂ ∩ Dᶜ).card = 1)
    (hL1 : (G.neighborFinset L₁ ∩ Dᶜ).card = 2) (hL2 : (G.neighborFinset L₂ ∩ Dᶜ).card = 2) :
    6 ≤ (Dᶜ.filter (fun g => ¬G.Adj g L₁ ∧ ¬G.Adj g c₁ ∧ ¬G.Adj g c₂)).card ∧
      6 ≤ (Dᶜ.filter (fun g => ¬G.Adj g c₁ ∧ ¬G.Adj g c₂ ∧ ¬G.Adj g L₂)).card := by
  refine ⟨avoiders_ge_six_aux G D L₁ c₁ c₂ hDc9 (by omega),
    avoiders_ge_six_aux G D c₁ c₂ L₂ hDc9 (by omega)⟩

/-- **Cherry-avoider internal degree `≥ 2`.**  A degree-`4` hub whose every `D`-neighbour is
either a single allowed leaf or an `M`-isolated twin, with at most one twin-neighbour (fact `(W)`),
sends at most `2` edges into `D`, hence at least `2` edges to other hubs. -/
theorem avoider_internal_ge_two (G : SimpleGraph (Fin 18)) (D Iso : Finset (Fin 18))
    (g allowed : Fin 18) (hdg : G.degree g = 4) (hIso1 : (G.neighborFinset g ∩ Iso).card ≤ 1)
    (hclass : ∀ x : Fin 18, G.Adj g x → x ∈ D → x = allowed ∨ x ∈ Iso) :
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
theorem fully_free_internal_ge_three (G : SimpleGraph (Fin 18)) (D Iso : Finset (Fin 18))
    (g : Fin 18) (hdg : G.degree g = 4) (hIso1 : (G.neighborFinset g ∩ Iso).card ≤ 1)
    (hclass : ∀ x : Fin 18, G.Adj g x → x ∈ D → x ∈ Iso) :
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
theorem path_iso_partition (G : SimpleGraph (Fin 18)) (D Iso : Finset (Fin 18))
    (L₁ c₁ c₂ L₂ : Fin 18)
    (hIsodef : Iso = D.filter (fun v => (G.neighborFinset v ∩ D).card = 0))
    (hisochar : ∀ w : Fin 18, w ∈ D → w ≠ L₁ → w ≠ c₁ → w ≠ c₂ → w ≠ L₂ → w ∈ Iso)
    (hL1D : L₁ ∈ D) (hc1D : c₁ ∈ D) (hc2D : c₂ ∈ D) (hL2D : L₂ ∈ D)
    (hac1L1 : G.Adj c₁ L₁) (hc12 : G.Adj c₁ c₂) (hac2L2 : G.Adj c₂ L₂) :
    ({L₁, c₁, c₂, L₂} : Finset (Fin 18)) ∪ Iso = D ∧
      Disjoint ({L₁, c₁, c₂, L₂} : Finset (Fin 18)) Iso := by
  classical
  set P : Finset (Fin 18) := {L₁, c₁, c₂, L₂} with hP
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

/-- **Residual incidence sums.**  Over the ten hubs the path-, iso- and hub-internal incidences
total `6`, `12`, `22` respectively, and per hub the three split the degree `4`:
`path(g) + iso(g) + int(g) = 4`. -/
theorem residual_incidence_sums (G : SimpleGraph (Fin 18)) (D Iso : Finset (Fin 18))
    (L₁ c₁ c₂ L₂ : Fin 18)
    (hIsodef : Iso = D.filter (fun v => (G.neighborFinset v ∩ D).card = 0))
    (hIsoprop : ∀ v ∈ Iso, G.degree v = 3 ∧ (∀ w : Fin 18, G.Adj v w → G.degree w ≠ 3))
    (hisochar : ∀ w : Fin 18, w ∈ D → w ≠ L₁ → w ≠ c₁ → w ≠ c₂ → w ≠ L₂ → w ∈ Iso)
    (hL1D : L₁ ∈ D) (hc1D : c₁ ∈ D) (hc2D : c₂ ∈ D) (hL2D : L₂ ∈ D)
    (hac1L1 : G.Adj c₁ L₁) (hc12 : G.Adj c₁ c₂) (hac2L2 : G.Adj c₂ L₂)
    (hnc1L2 : ¬G.Adj c₁ L₂)
    (hdeg4 : ∀ w : Fin 18, w ∈ Dᶜ → G.degree w = 4)
    (hcard_c1 : (G.neighborFinset c₁ ∩ Dᶜ).card = 1)
    (hcard_c2 : (G.neighborFinset c₂ ∩ Dᶜ).card = 1)
    (hcard_L1 : (G.neighborFinset L₁ ∩ Dᶜ).card = 2)
    (hcard_L2 : (G.neighborFinset L₂ ∩ Dᶜ).card = 2)
    (hIso4 : Iso.card = 4)
    (hL1nc2 : L₁ ≠ c₂) (hL2nc1 : L₂ ≠ c₁) :
    (∑ g ∈ Dᶜ, (G.neighborFinset g ∩ ({L₁, c₁, c₂, L₂} : Finset (Fin 18))).card = 6) ∧
      (∑ g ∈ Dᶜ, (G.neighborFinset g ∩ Iso).card = 12) ∧
      (∀ g ∈ Dᶜ, (G.neighborFinset g ∩ ({L₁, c₁, c₂, L₂} : Finset (Fin 18))).card
        + (G.neighborFinset g ∩ Iso).card + (G.neighborFinset g ∩ Dᶜ).card = 4) := by
  classical
  set P : Finset (Fin 18) := {L₁, c₁, c₂, L₂} with hP
  have hL1c1 : L₁ ≠ c₁ := (G.ne_of_adj hac1L1).symm
  have hc1c2 : c₁ ≠ c₂ := G.ne_of_adj hc12
  have hc2L2 : c₂ ≠ L₂ := G.ne_of_adj hac2L2
  have hL1L2 : L₁ ≠ L₂ := by rintro rfl; exact hnc1L2 hac1L1
  have hsum_path : ∑ g ∈ Dᶜ, (G.neighborFinset g ∩ P).card = 6 := by
    rw [cross_count G Dᶜ P, hP, Finset.sum_insert (by simp [hL1c1, hL1nc2, hL1L2]),
      Finset.sum_insert (by simp [hc1c2, Ne.symm hL2nc1]),
      Finset.sum_insert (by simp [hc2L2]), Finset.sum_singleton]
    omega
  have hsum_iso : ∑ g ∈ Dᶜ, (G.neighborFinset g ∩ Iso).card = 12 := by
    rw [cross_count G Dᶜ Iso]
    have heach : ∀ t ∈ Iso, (G.neighborFinset t ∩ Dᶜ).card = 3 := by
      intro t ht
      exact (iso_three_hub_nbrs G D Iso hIsodef hIsoprop t ht).2
    rw [Finset.sum_congr rfl heach, Finset.sum_const, smul_eq_mul, hIso4]
  obtain ⟨hDeq, hdisj⟩ :=
    path_iso_partition G D Iso L₁ c₁ c₂ L₂ hIsodef hisochar hL1D hc1D hc2D hL2D hac1L1 hc12 hac2L2
  have hper : ∀ g ∈ Dᶜ, (G.neighborFinset g ∩ P).card + (G.neighborFinset g ∩ Iso).card
      + (G.neighborFinset g ∩ Dᶜ).card = 4 := by
    intro g hg
    have hdj : Disjoint (G.neighborFinset g ∩ P) (G.neighborFinset g ∩ Iso) := by
      rw [Finset.disjoint_left]
      intro a ha ha'
      rw [Finset.mem_inter] at ha ha'
      exact (Finset.disjoint_left.mp hdisj) ha.2 ha'.2
    have hPI : (G.neighborFinset g ∩ P).card + (G.neighborFinset g ∩ Iso).card
        = (G.neighborFinset g ∩ D).card := by
      rw [← Finset.card_union_of_disjoint hdj, ← Finset.inter_union_distrib_left, hP, hDeq]
    have hsplit := nbr_split_DC G D g
    have hd4 := hdeg4 g hg
    omega
  exact ⟨hsum_path, hsum_iso, hper⟩

/-- **Fully-free hub budget.**  With avoider internal degree `≥ 2` (`hA1int`, `hA2int`), fully-free
internal degree `≥ 3` (`hFFint`), `|A1|, |A2| ≥ 6`, `FF = A1 ∩ A2`, and the hub-internal-degree
total `∑_{Dᶜ} f = 22`, the fully-free count lies in `{2, 3, 4, 5, 6, 7}`. -/
theorem active_hub_budget_eighteen (Dc A1 A2 FF : Finset (Fin 18)) (f : Fin 18 → ℕ)
    (hA1sub : A1 ⊆ Dc) (hA2sub : A2 ⊆ Dc) (hFF : FF = A1 ∩ A2)
    (hA1card : 6 ≤ A1.card) (hA2card : 6 ≤ A2.card)
    (hA1int : ∀ g ∈ A1, 2 ≤ f g) (hA2int : ∀ g ∈ A2, 2 ≤ f g)
    (hFFint : ∀ g ∈ FF, 3 ≤ f g) (hSum18 : ∑ w ∈ Dc, f w = 22) :
    2 ≤ FF.card ∧ FF.card ≤ 7 := by
  classical
  have hFFsubA1 : FF ⊆ A1 := by rw [hFF]; exact Finset.inter_subset_left
  have hFFsubA2 : FF ⊆ A2 := by rw [hFF]; exact Finset.inter_subset_right
  have hFFsub : FF ⊆ Dc := hFFsubA1.trans hA1sub
  -- `|FF| ≤ 7`: `3|FF| ≤ ∑_{FF} f ≤ ∑_{Dᶜ} f = 22`.
  have hFFsum_le : ∑ g ∈ FF, f g ≤ 22 := by
    rw [← hSum18]
    exact Finset.sum_le_sum_of_subset_of_nonneg hFFsub (fun _ _ _ => Nat.zero_le _)
  have hFFsum_ge3 : 3 * FF.card ≤ ∑ g ∈ FF, f g := by
    have := Finset.card_nsmul_le_sum FF f 3 hFFint
    simpa [smul_eq_mul, Nat.mul_comm] using this
  have hle6 : FF.card ≤ 7 := by omega
  -- `|FF| ≥ 2`: inclusion–exclusion over `A1 ⊔ (A2 \ A1) = A1 ∪ A2 ⊆ Dᶜ`.
  refine ⟨?_, hle6⟩
  have hUsub : A1 ∪ A2 ⊆ Dc := Finset.union_subset hA1sub hA2sub
  have hUsum_le : ∑ g ∈ A1 ∪ A2, f g ≤ 22 := by
    rw [← hSum18]
    exact Finset.sum_le_sum_of_subset_of_nonneg hUsub (fun _ _ _ => Nat.zero_le _)
  have hdisj : Disjoint A1 (A2 \ A1) := Finset.disjoint_sdiff
  have hunion_eq : A1 ∪ (A2 \ A1) = A1 ∪ A2 := by
    rw [Finset.union_sdiff_self_eq_union]
  have hUsplit : ∑ g ∈ A1 ∪ A2, f g = (∑ g ∈ A1, f g) + ∑ g ∈ A2 \ A1, f g := by
    rw [← hunion_eq, Finset.sum_union hdisj]
  have hA1split : (∑ g ∈ A1 \ FF, f g) + ∑ g ∈ FF, f g = ∑ g ∈ A1, f g :=
    Finset.sum_sdiff hFFsubA1
  have hA1FFinter : (A1 ∩ FF).card = FF.card := by
    rw [Finset.inter_eq_right.mpr hFFsubA1]
  have hA1mfcard : (A1 \ FF).card + FF.card = A1.card := by
    rw [← hA1FFinter]; exact Finset.card_sdiff_add_card_inter A1 FF
  have hA1mf_ge : 2 * (A1 \ FF).card ≤ ∑ g ∈ A1 \ FF, f g := by
    have := Finset.card_nsmul_le_sum (A1 \ FF) f 2
      (fun g hg => hA1int g ((Finset.mem_sdiff.mp hg).1))
    simpa [smul_eq_mul, Nat.mul_comm] using this
  have hA2A1FF : (A2 ∩ A1).card = FF.card := by rw [hFF, Finset.inter_comm]
  have hA2mA1 : (A2 \ A1).card + FF.card = A2.card := by
    rw [← hA2A1FF]; exact Finset.card_sdiff_add_card_inter A2 A1
  have hA2mA1_ge : 2 * (A2 \ A1).card ≤ ∑ g ∈ A2 \ A1, f g := by
    have := Finset.card_nsmul_le_sum (A2 \ A1) f 2
      (fun g hg => hA2int g ((Finset.mem_sdiff.mp hg).1))
    simpa [smul_eq_mul, Nat.mul_comm] using this
  have hFFleA1 : FF.card ≤ A1.card := Finset.card_le_card hFFsubA1
  omega

end N18

end ACMax
