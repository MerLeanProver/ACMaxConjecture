import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N17.Core
import ACMaxConjecture.SmallCases.Certificates
import ACMaxConjecture.SmallCases.N17.HubTriangleStruct
import ACMaxConjecture.SmallCases.N17.HubTriangleFF

/-!
# Hub-triangle existence for the `n = 17`, `e(M) = 4`, `|D| = 8` fat double-star corner

This file is the `e(M) = 4` analogue of `TwinCert17HubTriangle`
(`exists_hub_triangle_config_residual_seventeen`).  The `M`-structure is a **fat dominating-edge
double-star**: a centre edge `c₁–c₂`, with `c₁` carrying two leaves `L₁, L₁'`
(`N c₁ ∩ D = {c₂, L₁, L₁'}`, the *fat* centre) and `c₂` carrying one leaf `L₂`
(`N c₂ ∩ D = {c₁, L₂}`), for `4` `M`-edges.  In the `|D| = 8` (`|Hub| = 9`, all-degree-`4`) corner
there are `|Iso| = 3` `M`-isolated twins and the hub-internal-degree total is
`∑ int = 4·9 − 7 − 9 = 20` (vs the `e(M) = 3` `P₄` value `18`).

The target cherry is the fat centre with its two leaves `L₁–c₁–L₁'` (an induced `P₃`, since
`L₁ ≁ L₁'`).  We force a triangle among its avoider hubs (`A1`), packaged as `HubTriangleConfig G`
via `hub_triangle_cut_certificate`.  The dispatch mirrors the proved `P₄` chain with the new
constants (`|Iso| = 3`, `∑ int = 20`, `|A2| ≥ 6`).
-/

namespace ACMax

open scoped Classical

namespace N17

/-- **Hub / twin counts for the fat double-star.**  `D` is the disjoint union of the five-vertex
path `{c₁, c₂, L₁, L₁', L₂}` and the `M`-isolated twins `Iso`; with `|D| = 8` this gives
`Dᶜ.card = 9` and `Iso.card = 3`. -/
theorem hub_struct_fatstar (G : SimpleGraph (Fin 17)) (D Iso : Finset (Fin 17))
    (c₁ c₂ L₁ L₁' L₂ : Fin 17)
    (hIsodef : Iso = D.filter (fun v => (G.neighborFinset v ∩ D).card = 0))
    (hisochar : ∀ w : Fin 17, w ∈ D → w ≠ c₁ → w ≠ c₂ → w ≠ L₁ → w ≠ L₁' → w ≠ L₂ → w ∈ Iso)
    (hc1D : c₁ ∈ D) (hc2D : c₂ ∈ D) (hL1D : L₁ ∈ D) (hL1'D : L₁' ∈ D) (hL2D : L₂ ∈ D)
    (hac1L1 : G.Adj c₁ L₁) (hac1L1' : G.Adj c₁ L₁') (hc12 : G.Adj c₁ c₂) (hac2L2 : G.Adj c₂ L₂)
    (hL1nL1' : L₁ ≠ L₁') (hL1nc2 : L₁ ≠ c₂) (hL1'nc2 : L₁' ≠ c₂) (hL2nc1 : L₂ ≠ c₁)
    (hnc1L2 : ¬G.Adj c₁ L₂) (hL2nL1 : L₂ ≠ L₁) (hL2nL1' : L₂ ≠ L₁')
    (hD8 : D.card = 8) :
    Dᶜ.card = 9 ∧ Iso.card = 3 := by
  classical
  have hDc : Dᶜ.card = 9 := by rw [Finset.card_compl, Fintype.card_fin, hD8]
  refine ⟨hDc, ?_⟩
  have hc1c2 : c₁ ≠ c₂ := G.ne_of_adj hc12
  have hc1L1 : c₁ ≠ L₁ := G.ne_of_adj hac1L1
  have hc1L1' : c₁ ≠ L₁' := G.ne_of_adj hac1L1'
  have hc2L2 : c₂ ≠ L₂ := G.ne_of_adj hac2L2
  set P : Finset (Fin 17) := {c₁, c₂, L₁, L₁', L₂} with hP
  have hPcard : P.card = 5 := by
    rw [hP, Finset.card_insert_of_notMem (by simp [hc1c2, hc1L1, hc1L1', Ne.symm hL2nc1]),
      Finset.card_insert_of_notMem (by simp [Ne.symm hL1nc2, Ne.symm hL1'nc2, hc2L2]),
      Finset.card_insert_of_notMem (by simp [hL1nL1', Ne.symm hL2nL1]),
      Finset.card_insert_of_notMem (by simp [Ne.symm hL2nL1']), Finset.card_singleton]
  have hIsoD : Iso ⊆ D := by rw [hIsodef]; exact Finset.filter_subset _ _
  have hPD : P ⊆ D := by
    intro x hx; rw [hP] at hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> assumption
  have hPnIso : Disjoint P Iso := by
    rw [Finset.disjoint_left]
    intro x hxP hxIso
    rw [hIsodef, Finset.mem_filter] at hxIso
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem] at hxIso
    rw [hP] at hxP
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxP
    rcases hxP with rfl | rfl | rfl | rfl | rfl
    · exact hxIso.2 c₂ (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hc12, hc2D⟩)
    · exact hxIso.2 c₁ (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hc12.symm, hc1D⟩)
    · exact hxIso.2 c₁ (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hac1L1.symm, hc1D⟩)
    · exact hxIso.2 c₁ (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hac1L1'.symm, hc1D⟩)
    · exact hxIso.2 c₂ (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hac2L2.symm, hc2D⟩)
  have hcover : D ⊆ P ∪ Iso := by
    intro x hxD
    by_cases hx1 : x = c₁
    · subst hx1; exact Finset.mem_union_left _ (by rw [hP]; simp)
    by_cases hx2 : x = c₂
    · subst hx2; exact Finset.mem_union_left _ (by rw [hP]; simp)
    by_cases hx3 : x = L₁
    · subst hx3; exact Finset.mem_union_left _ (by rw [hP]; simp)
    by_cases hx4 : x = L₁'
    · subst hx4; exact Finset.mem_union_left _ (by rw [hP]; simp)
    by_cases hx5 : x = L₂
    · subst hx5; exact Finset.mem_union_left _ (by rw [hP]; simp)
    · exact Finset.mem_union_right _ (hisochar x hxD hx1 hx2 hx3 hx4 hx5)
  have hDeq : D = P ∪ Iso := Finset.Subset.antisymm hcover (Finset.union_subset hPD hIsoD)
  have hcardU : (P ∪ Iso).card = P.card + Iso.card := Finset.card_union_of_disjoint hPnIso
  rw [hDeq, hcardU, hPcard] at hD8
  omega

/-- **Path / Iso partition of `D` for the fat double-star.**  The five path vertices and the
`M`-isolated twins partition `D`. -/
theorem path_iso_partition_fatstar (G : SimpleGraph (Fin 17)) (D Iso : Finset (Fin 17))
    (c₁ c₂ L₁ L₁' L₂ : Fin 17)
    (hIsodef : Iso = D.filter (fun v => (G.neighborFinset v ∩ D).card = 0))
    (hisochar : ∀ w : Fin 17, w ∈ D → w ≠ c₁ → w ≠ c₂ → w ≠ L₁ → w ≠ L₁' → w ≠ L₂ → w ∈ Iso)
    (hc1D : c₁ ∈ D) (hc2D : c₂ ∈ D) (hL1D : L₁ ∈ D) (hL1'D : L₁' ∈ D) (hL2D : L₂ ∈ D)
    (hac1L1 : G.Adj c₁ L₁) (hac1L1' : G.Adj c₁ L₁') (hc12 : G.Adj c₁ c₂) (hac2L2 : G.Adj c₂ L₂) :
    ({c₁, c₂, L₁, L₁', L₂} : Finset (Fin 17)) ∪ Iso = D ∧
      Disjoint ({c₁, c₂, L₁, L₁', L₂} : Finset (Fin 17)) Iso := by
  classical
  set P : Finset (Fin 17) := {c₁, c₂, L₁, L₁', L₂} with hP
  have hIsoD : Iso ⊆ D := by rw [hIsodef]; exact Finset.filter_subset _ _
  have hPD : P ⊆ D := by
    intro x hx; rw [hP] at hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> assumption
  have hPnIso : Disjoint P Iso := by
    rw [Finset.disjoint_left]
    intro x hxP hxIso
    rw [hIsodef, Finset.mem_filter] at hxIso
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem] at hxIso
    rw [hP] at hxP
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxP
    rcases hxP with rfl | rfl | rfl | rfl | rfl
    · exact hxIso.2 c₂ (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hc12, hc2D⟩)
    · exact hxIso.2 c₁ (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hc12.symm, hc1D⟩)
    · exact hxIso.2 c₁ (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hac1L1.symm, hc1D⟩)
    · exact hxIso.2 c₁ (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hac1L1'.symm, hc1D⟩)
    · exact hxIso.2 c₂ (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hac2L2.symm, hc2D⟩)
  have hcover : D ⊆ P ∪ Iso := by
    intro x hxD
    by_cases hx1 : x = c₁
    · subst hx1; exact Finset.mem_union_left _ (by rw [hP]; simp)
    by_cases hx2 : x = c₂
    · subst hx2; exact Finset.mem_union_left _ (by rw [hP]; simp)
    by_cases hx3 : x = L₁
    · subst hx3; exact Finset.mem_union_left _ (by rw [hP]; simp)
    by_cases hx4 : x = L₁'
    · subst hx4; exact Finset.mem_union_left _ (by rw [hP]; simp)
    by_cases hx5 : x = L₂
    · subst hx5; exact Finset.mem_union_left _ (by rw [hP]; simp)
    · exact Finset.mem_union_right _ (hisochar x hxD hx1 hx2 hx3 hx4 hx5)
  exact ⟨Finset.Subset.antisymm (Finset.union_subset hPD hIsoD) hcover, hPnIso⟩

/-- **Path hub-incidence counts for the fat double-star.**  From the exact path neighbourhoods, the
five path vertices send `0 + 1 + 2 + 2 + 2 = 7` edges to the nine hubs. -/
theorem path_hub_incidence_fatstar (G : SimpleGraph (Fin 17)) (D : Finset (Fin 17))
    (c₁ c₂ L₁ L₁' L₂ : Fin 17)
    (hNc1D : G.neighborFinset c₁ ∩ D = {c₂, L₁, L₁'})
    (hNc2D : G.neighborFinset c₂ ∩ D = {c₁, L₂})
    (hNL1D : G.neighborFinset L₁ ∩ D = {c₁}) (hNL1'D : G.neighborFinset L₁' ∩ D = {c₁})
    (hNL2D : G.neighborFinset L₂ ∩ D = {c₂})
    (hc1deg : G.degree c₁ = 3) (hc2deg : G.degree c₂ = 3) (hL1deg : G.degree L₁ = 3)
    (hL1'deg : G.degree L₁' = 3) (hL2deg : G.degree L₂ = 3)
    (hL1nL1' : L₁ ≠ L₁') (hL1nc2 : L₁ ≠ c₂) (hL1'nc2 : L₁' ≠ c₂) (hL2nc1 : L₂ ≠ c₁) :
    (G.neighborFinset c₁ ∩ Dᶜ).card = 0 ∧ (G.neighborFinset c₂ ∩ Dᶜ).card = 1 ∧
      (G.neighborFinset L₁ ∩ Dᶜ).card = 2 ∧ (G.neighborFinset L₁' ∩ Dᶜ).card = 2 ∧
      (G.neighborFinset L₂ ∩ Dᶜ).card = 2 := by
  classical
  have hcard_c1D : (G.neighborFinset c₁ ∩ D).card = 3 := by
    rw [hNc1D, Finset.card_insert_of_notMem (by simp [Ne.symm hL1nc2, Ne.symm hL1'nc2]),
      Finset.card_insert_of_notMem (by simp [hL1nL1']), Finset.card_singleton]
  have hcard_c2D : (G.neighborFinset c₂ ∩ D).card = 2 := by
    rw [hNc2D, Finset.card_insert_of_notMem (by simp [Ne.symm hL2nc1]), Finset.card_singleton]
  have hcard_L1D : (G.neighborFinset L₁ ∩ D).card = 1 := by rw [hNL1D, Finset.card_singleton]
  have hcard_L1'D : (G.neighborFinset L₁' ∩ D).card = 1 := by rw [hNL1'D, Finset.card_singleton]
  have hcard_L2D : (G.neighborFinset L₂ ∩ D).card = 1 := by rw [hNL2D, Finset.card_singleton]
  have s1 := nbr_split_DC G D c₁
  have s2 := nbr_split_DC G D c₂
  have s3 := nbr_split_DC G D L₁
  have s4 := nbr_split_DC G D L₁'
  have s5 := nbr_split_DC G D L₂
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> omega

/-- **Residual incidence sums for the fat double-star.**  Over the nine hubs the path-, iso- and
hub-internal incidences total `7`, `9`, `20` respectively, and per hub the three split the degree
`4`. -/
theorem incidence_sums_fatstar (G : SimpleGraph (Fin 17)) (D Iso : Finset (Fin 17))
    (c₁ c₂ L₁ L₁' L₂ : Fin 17)
    (hIsodef : Iso = D.filter (fun v => (G.neighborFinset v ∩ D).card = 0))
    (hIsoprop : ∀ v ∈ Iso, G.degree v = 3 ∧ (∀ w : Fin 17, G.Adj v w → G.degree w ≠ 3))
    (hisochar : ∀ w : Fin 17, w ∈ D → w ≠ c₁ → w ≠ c₂ → w ≠ L₁ → w ≠ L₁' → w ≠ L₂ → w ∈ Iso)
    (hc1D : c₁ ∈ D) (hc2D : c₂ ∈ D) (hL1D : L₁ ∈ D) (hL1'D : L₁' ∈ D) (hL2D : L₂ ∈ D)
    (hac1L1 : G.Adj c₁ L₁) (hac1L1' : G.Adj c₁ L₁') (hc12 : G.Adj c₁ c₂) (hac2L2 : G.Adj c₂ L₂)
    (hdeg4 : ∀ w : Fin 17, w ∈ Dᶜ → G.degree w = 4)
    (hcard_c1 : (G.neighborFinset c₁ ∩ Dᶜ).card = 0)
    (hcard_c2 : (G.neighborFinset c₂ ∩ Dᶜ).card = 1)
    (hcard_L1 : (G.neighborFinset L₁ ∩ Dᶜ).card = 2)
    (hcard_L1' : (G.neighborFinset L₁' ∩ Dᶜ).card = 2)
    (hcard_L2 : (G.neighborFinset L₂ ∩ Dᶜ).card = 2)
    (hIso3 : Iso.card = 3)
    (hc1c2 : c₁ ≠ c₂) (hc1L1 : c₁ ≠ L₁) (hc1L1' : c₁ ≠ L₁') (hc1L2 : c₁ ≠ L₂)
    (hc2L1 : c₂ ≠ L₁) (hc2L1' : c₂ ≠ L₁') (hc2L2 : c₂ ≠ L₂)
    (hL1L1' : L₁ ≠ L₁') (hL1L2 : L₁ ≠ L₂) (hL1'L2 : L₁' ≠ L₂) :
    (∑ g ∈ Dᶜ, (G.neighborFinset g ∩ ({c₁, c₂, L₁, L₁', L₂} : Finset (Fin 17))).card = 7) ∧
      (∑ g ∈ Dᶜ, (G.neighborFinset g ∩ Iso).card = 9) ∧
      (∀ g ∈ Dᶜ, (G.neighborFinset g ∩ ({c₁, c₂, L₁, L₁', L₂} : Finset (Fin 17))).card
        + (G.neighborFinset g ∩ Iso).card + (G.neighborFinset g ∩ Dᶜ).card = 4) := by
  classical
  set P : Finset (Fin 17) := {c₁, c₂, L₁, L₁', L₂} with hP
  have hsum_path : ∑ g ∈ Dᶜ, (G.neighborFinset g ∩ P).card = 7 := by
    rw [cross_count G Dᶜ P, hP,
      Finset.sum_insert (by simp [hc1c2, hc1L1, hc1L1', hc1L2]),
      Finset.sum_insert (by simp [hc2L1, hc2L1', hc2L2]),
      Finset.sum_insert (by simp [hL1L1', hL1L2]),
      Finset.sum_insert (by simp [hL1'L2]), Finset.sum_singleton]
    omega
  have hsum_iso : ∑ g ∈ Dᶜ, (G.neighborFinset g ∩ Iso).card = 9 := by
    rw [cross_count G Dᶜ Iso]
    have heach : ∀ t ∈ Iso, (G.neighborFinset t ∩ Dᶜ).card = 3 := by
      intro t ht
      exact (iso_three_hub_nbrs G D Iso hIsodef hIsoprop t ht).2
    rw [Finset.sum_congr rfl heach, Finset.sum_const, smul_eq_mul, hIso3]
  obtain ⟨hDeq, hdisj⟩ :=
    path_iso_partition_fatstar G D Iso c₁ c₂ L₁ L₁' L₂ hIsodef hisochar hc1D hc2D hL1D hL1'D hL2D
      hac1L1 hac1L1' hc12 hac2L2
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

/-- **Fully-free hub budget for the fat double-star.**  With avoider internal degree `≥ 2`, fully-
free internal degree `≥ 3`, `|A1| ≥ 5`, `|A2| ≥ 6`, `FF = A1 ∩ A2`, and the hub-internal-degree
total `∑_{Dᶜ} f = 20`, the fully-free count lies in `{2, 3, 4, 5, 6}`. -/
theorem active_hub_budget_fatstar (Dc A1 A2 FF : Finset (Fin 17)) (f : Fin 17 → ℕ)
    (hA1sub : A1 ⊆ Dc) (hA2sub : A2 ⊆ Dc) (hFF : FF = A1 ∩ A2)
    (hA1card : 5 ≤ A1.card) (hA2card : 6 ≤ A2.card)
    (hA1int : ∀ g ∈ A1, 2 ≤ f g) (hA2int : ∀ g ∈ A2, 2 ≤ f g)
    (hFFint : ∀ g ∈ FF, 3 ≤ f g) (hSum20 : ∑ w ∈ Dc, f w = 20) :
    2 ≤ FF.card ∧ FF.card ≤ 6 := by
  classical
  have hFFsubA1 : FF ⊆ A1 := by rw [hFF]; exact Finset.inter_subset_left
  have hFFsubA2 : FF ⊆ A2 := by rw [hFF]; exact Finset.inter_subset_right
  have hFFsub : FF ⊆ Dc := hFFsubA1.trans hA1sub
  have hFFsum_le : ∑ g ∈ FF, f g ≤ 20 := by
    rw [← hSum20]
    exact Finset.sum_le_sum_of_subset_of_nonneg hFFsub (fun _ _ _ => Nat.zero_le _)
  have hFFsum_ge3 : 3 * FF.card ≤ ∑ g ∈ FF, f g := by
    have := Finset.card_nsmul_le_sum FF f 3 hFFint
    simpa [smul_eq_mul, Nat.mul_comm] using this
  have hle6 : FF.card ≤ 6 := by omega
  refine ⟨?_, hle6⟩
  have hUsub : A1 ∪ A2 ⊆ Dc := Finset.union_subset hA1sub hA2sub
  have hUsum_le : ∑ g ∈ A1 ∪ A2, f g ≤ 20 := by
    rw [← hSum20]
    exact Finset.sum_le_sum_of_subset_of_nonneg hUsub (fun _ _ _ => Nat.zero_le _)
  have hdisj : Disjoint A1 (A2 \ A1) := Finset.disjoint_sdiff
  have hunion_eq : A1 ∪ (A2 \ A1) = A1 ∪ A2 := by rw [Finset.union_sdiff_self_eq_union]
  have hUsplit : ∑ g ∈ A1 ∪ A2, f g = (∑ g ∈ A1, f g) + ∑ g ∈ A2 \ A1, f g := by
    rw [← hunion_eq, Finset.sum_union hdisj]
  have hA1split : (∑ g ∈ A1 \ FF, f g) + ∑ g ∈ FF, f g = ∑ g ∈ A1, f g :=
    Finset.sum_sdiff hFFsubA1
  have hA1FFinter : (A1 ∩ FF).card = FF.card := by rw [Finset.inter_eq_right.mpr hFFsubA1]
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

/-- **Avoider internal degree `≥ 2` with two allowed leaves (fat-star variant).**  A degree-`4` hub
whose every `D`-neighbour is one of two allowed leaves `a₁, a₂` or an `M`-isolated twin, with at
most one twin-neighbour and not adjacent to both `a₁` and `a₂`, sends at most `2` edges into `D`,
hence at least `2` edges to other hubs. -/
theorem avoider_internal_ge_two_pair (G : SimpleGraph (Fin 17)) (D Iso : Finset (Fin 17))
    (g a₁ a₂ : Fin 17) (hdg : G.degree g = 4) (hIso1 : (G.neighborFinset g ∩ Iso).card ≤ 1)
    (hnboth : ¬(G.Adj g a₁ ∧ G.Adj g a₂))
    (hclass : ∀ x : Fin 17, G.Adj g x → x ∈ D → x = a₁ ∨ x = a₂ ∨ x ∈ Iso) :
    2 ≤ (G.neighborFinset g ∩ Dᶜ).card := by
  classical
  set A : Finset (Fin 17) := if G.Adj g a₁ then {a₁} else (if G.Adj g a₂ then {a₂} else ∅) with hA
  have hAcard : A.card ≤ 1 := by
    rw [hA]; split <;> [skip; split] <;> simp
  have hsub : G.neighborFinset g ∩ D ⊆ A ∪ (G.neighborFinset g ∩ Iso) := by
    intro x hx
    rw [Finset.mem_inter, G.mem_neighborFinset] at hx
    obtain ⟨hadj, hxD⟩ := hx
    rcases hclass x hadj hxD with h | h | h
    · subst h
      refine Finset.mem_union_left _ ?_
      rw [hA]; simp [hadj]
    · subst h
      refine Finset.mem_union_left _ ?_
      have hna1 : ¬G.Adj g a₁ := fun h1 => hnboth ⟨h1, hadj⟩
      rw [hA]; simp [hna1, hadj]
    · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hadj, h⟩)
  have hcard : (G.neighborFinset g ∩ D).card ≤ 2 := by
    calc (G.neighborFinset g ∩ D).card
        ≤ (A ∪ (G.neighborFinset g ∩ Iso)).card := Finset.card_le_card hsub
      _ ≤ A.card + (G.neighborFinset g ∩ Iso).card := Finset.card_union_le _ _
      _ ≤ 2 := by omega
  have hsplit := nbr_split_DC G D g
  omega

/-- **Isolated-twin incidence bound (`|Iso| = 3`).**  If every `M`-isolated twin has at most one
neighbour in a hub set `A`, then the total iso-incidence over `A` is at most `|Iso| = 3`. -/
theorem iso_incidence_le_three (G : SimpleGraph (Fin 17)) (Iso A : Finset (Fin 17))
    (hIso3 : Iso.card = 3)
    (hbound : ∀ t ∈ Iso, (G.neighborFinset t ∩ A).card ≤ 1) :
    (∑ g ∈ A, (G.neighborFinset g ∩ Iso).card) ≤ 3 := by
  classical
  rw [cross_count G A Iso]
  calc (∑ t ∈ Iso, (G.neighborFinset t ∩ A).card)
      ≤ ∑ _t ∈ Iso, 1 := Finset.sum_le_sum hbound
    _ = Iso.card := by rw [Finset.sum_const, smul_eq_mul, Nat.mul_one]
    _ = 3 := hIso3

/-- **Two non-adjacent iso-`3` hubs are impossible (`|Iso| = 3`).**  Two distinct non-adjacent
degree-`4` hubs each adjacent to all three `M`-isolated twins share all `3` (`≥ 2`), contradicting
the good-`C₄` share bound. -/
theorem two_iso3_nonadj_false_fs (G : SimpleGraph (Fin 17)) (D Iso : Finset (Fin 17))
    (hC4 : ¬∃ a b c d : Fin 17, ({a, b, c, d} : Finset (Fin 17)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (hIsoD : Iso ⊆ D)
    (hIsoprop : ∀ v ∈ Iso, G.degree v = 3 ∧ (∀ w : Fin 17, G.Adj v w → G.degree w ≠ 3))
    (hdeg4 : ∀ w : Fin 17, w ∈ Dᶜ → G.degree w = 4) (hIso3 : Iso.card = 3)
    (h₁ h₂ : Fin 17) (hh1Dc : h₁ ∈ Dᶜ) (hh2Dc : h₂ ∈ Dᶜ) (hh12 : h₁ ≠ h₂)
    (hnadj : ¬G.Adj h₁ h₂)
    (hiso1 : (G.neighborFinset h₁ ∩ Iso).card = 3)
    (hiso2 : (G.neighborFinset h₂ ∩ Iso).card = 3) :
    False := by
  classical
  have hshare := nonadj_hubs_share_le_one_iso G D Iso hC4 hIsoD hIsoprop hdeg4
    h₁ h₂ hh1Dc hh2Dc hh12 hnadj
  have hsub1 : G.neighborFinset h₁ ∩ Iso ⊆ Iso := Finset.inter_subset_right
  have hsub2 : G.neighborFinset h₂ ∩ Iso ⊆ Iso := Finset.inter_subset_right
  have hunion_le : ((G.neighborFinset h₁ ∩ Iso) ∪ (G.neighborFinset h₂ ∩ Iso)).card ≤ 3 := by
    calc ((G.neighborFinset h₁ ∩ Iso) ∪ (G.neighborFinset h₂ ∩ Iso)).card
        ≤ Iso.card := Finset.card_le_card (Finset.union_subset hsub1 hsub2)
      _ = 3 := hIso3
  have hincl := Finset.card_union_add_card_inter
    (G.neighborFinset h₁ ∩ Iso) (G.neighborFinset h₂ ∩ Iso)
  have hinter_eq : (G.neighborFinset h₁ ∩ Iso) ∩ (G.neighborFinset h₂ ∩ Iso)
      = (G.neighborFinset h₁ ∩ G.neighborFinset h₂) ∩ Iso := by
    rw [Finset.inter_inter_inter_comm, Finset.inter_self]
  rw [hiso1, hiso2, hinter_eq] at hincl
  omega

/-- **Fully-free internal-edge lower bound (fat-star, `∑ = 20`).**  For `FF ⊆ Dᶜ` with total
`Dᶜ`-internal degree `20`, `∑_{FF}(N ∩ FF) ≥ 2·∑_{FF}(N ∩ Dᶜ) − 20`. -/
theorem ff_internal_edge_lb_twenty (G : SimpleGraph (Fin 17)) (Dc FF : Finset (Fin 17))
    (hFFsub : FF ⊆ Dc)
    (hSum : ∑ w ∈ Dc, (G.neighborFinset w ∩ Dc).card = 20) :
    2 * (∑ g ∈ FF, (G.neighborFinset g ∩ Dc).card)
      ≤ (∑ g ∈ FF, (G.neighborFinset g ∩ FF).card) + 20 := by
  classical
  have hsplit : ∀ g : Fin 17, (G.neighborFinset g ∩ Dc).card
      = (G.neighborFinset g ∩ FF).card + (G.neighborFinset g ∩ (Dc \ FF)).card := by
    intro g
    rw [← Finset.card_union_of_disjoint, ← Finset.inter_union_distrib_left,
      Finset.union_sdiff_of_subset hFFsub]
    apply Finset.disjoint_left.mpr
    intro a ha ha'
    rw [Finset.mem_inter] at ha ha'
    exact (Finset.mem_sdiff.mp ha'.2).2 ha.2
  have hsdiff : (∑ w ∈ Dc \ FF, (G.neighborFinset w ∩ Dc).card)
      + ∑ g ∈ FF, (G.neighborFinset g ∩ Dc).card = 20 := by
    rw [Finset.sum_sdiff hFFsub, hSum]
  have hcross : ∑ g ∈ FF, (G.neighborFinset g ∩ (Dc \ FF)).card
      = ∑ w ∈ Dc \ FF, (G.neighborFinset w ∩ FF).card :=
    cross_count G FF (Dc \ FF)
  have hleak_le : ∑ w ∈ Dc \ FF, (G.neighborFinset w ∩ FF).card
      ≤ ∑ w ∈ Dc \ FF, (G.neighborFinset w ∩ Dc).card := by
    apply Finset.sum_le_sum
    intro w _
    exact Finset.card_le_card (Finset.inter_subset_inter (Finset.Subset.refl _) hFFsub)
  have hFFFFsum : (∑ g ∈ FF, (G.neighborFinset g ∩ FF).card)
      + ∑ g ∈ FF, (G.neighborFinset g ∩ (Dc \ FF)).card
      = ∑ g ∈ FF, (G.neighborFinset g ∩ Dc).card := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun g _ => (hsplit g).symm)
  omega

/-- **Generic avoider count `≥ 6`.**  If three vertices `a, b, c` together have at most `3`
hub-neighbours and there are `9` hubs, then at least `6` hubs avoid all of `a, b, c`. -/
theorem avoiders_ge_six_aux (G : SimpleGraph (Fin 17)) (D : Finset (Fin 17)) (a b c : Fin 17)
    (hDc9 : Dᶜ.card = 9)
    (hbound : (G.neighborFinset a ∩ Dᶜ).card + (G.neighborFinset b ∩ Dᶜ).card
      + (G.neighborFinset c ∩ Dᶜ).card ≤ 3) :
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

/-- **Asymmetric iso-share contradiction (`|Iso| = 3`).**  A degree-`4` hub `h₁` adjacent to all
three `M`-isolated twins (`iso = 3`) and a non-adjacent degree-`4` hub `h₂` with `iso ≥ 2` share at
least `2` twins, contradicting `nonadj_hubs_share_le_one_iso`. -/
theorem iso3_other_share_false (G : SimpleGraph (Fin 17)) (D Iso : Finset (Fin 17))
    (hC4 : ¬∃ a b c d : Fin 17, ({a, b, c, d} : Finset (Fin 17)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (hIsoD : Iso ⊆ D)
    (hIsoprop : ∀ v ∈ Iso, G.degree v = 3 ∧ (∀ w : Fin 17, G.Adj v w → G.degree w ≠ 3))
    (hdeg4 : ∀ w : Fin 17, w ∈ Dᶜ → G.degree w = 4) (hIso3 : Iso.card = 3)
    (h₁ h₂ : Fin 17) (hh1Dc : h₁ ∈ Dᶜ) (hh2Dc : h₂ ∈ Dᶜ) (hh12 : h₁ ≠ h₂)
    (hnadj : ¬G.Adj h₁ h₂)
    (hiso1 : (G.neighborFinset h₁ ∩ Iso).card = 3)
    (hiso2 : 2 ≤ (G.neighborFinset h₂ ∩ Iso).card) :
    False := by
  classical
  have hIsosub : Iso ⊆ G.neighborFinset h₁ := by
    have hsub : G.neighborFinset h₁ ∩ Iso ⊆ Iso := Finset.inter_subset_right
    have : G.neighborFinset h₁ ∩ Iso = Iso :=
      Finset.eq_of_subset_of_card_le hsub (by rw [hiso1, hIso3])
    rw [← this]; exact Finset.inter_subset_left
  have hshare := nonadj_hubs_share_le_one_iso G D Iso hC4 hIsoD hIsoprop hdeg4
    h₁ h₂ hh1Dc hh2Dc hh12 hnadj
  have hsub2 : G.neighborFinset h₂ ∩ Iso ⊆ (G.neighborFinset h₁ ∩ G.neighborFinset h₂) ∩ Iso := by
    intro x hx
    rw [Finset.mem_inter] at hx
    exact Finset.mem_inter.mpr ⟨Finset.mem_inter.mpr ⟨hIsosub hx.2, hx.1⟩, hx.2⟩
  have := Finset.card_le_card hsub2
  omega

/-- **No avoider triangle ⇒ contradiction (the fat double-star `|FF|`-dispatch core).**  Dispatches
on `|FF| ∈ {2, 3, 4, 5, 6}`.  The richer budget (`|Iso| = 3`, `∑ int = 20`, `|A2| ≥ 6`) collapses
most cases to pure counting / single Mantel triangles, leaving one documented residual at
`|FF| = 4`, `∑_FF int = 14`. -/
theorem iso_rich_force_fatstar (G : SimpleGraph (Fin 17))
    (D Iso : Finset (Fin 17)) (c₁ c₂ L₁ L₁' L₂ : Fin 17)
    (hT : ¬∃ x y z : Fin 17, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    (hC4 : ¬∃ a b c d : Fin 17, ({a, b, c, d} : Finset (Fin 17)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (hIsodef : Iso = D.filter (fun v => (G.neighborFinset v ∩ D).card = 0))
    (hIsoprop : ∀ v ∈ Iso, G.degree v = 3 ∧ (∀ w : Fin 17, G.Adj v w → G.degree w ≠ 3))
    (hisochar : ∀ w : Fin 17, w ∈ D → w ≠ c₁ → w ≠ c₂ → w ≠ L₁ → w ≠ L₁' → w ≠ L₂ → w ∈ Iso)
    (hc1deg : G.degree c₁ = 3) (hc2deg : G.degree c₂ = 3) (hL1deg : G.degree L₁ = 3)
    (hL1'deg : G.degree L₁' = 3) (hL2deg : G.degree L₂ = 3)
    (hac1L1 : G.Adj c₁ L₁) (hac1L1' : G.Adj c₁ L₁') (hc12 : G.Adj c₁ c₂) (hac2L2 : G.Adj c₂ L₂)
    (hL1nL1' : ¬G.Adj L₁ L₁') (hL1nL1'ne : L₁ ≠ L₁')
    (hc1L2 : c₁ ≠ L₂) (hc2L1 : c₂ ≠ L₁) (hc2L1' : c₂ ≠ L₁')
    (hL1L2 : L₁ ≠ L₂) (hL1'L2 : L₁' ≠ L₂)
    (hdeg4 : ∀ w : Fin 17, w ∈ Dᶜ → G.degree w = 4)
    (hc1D : c₁ ∈ D) (hc2D : c₂ ∈ D) (hL1D : L₁ ∈ D) (hL1'D : L₁' ∈ D) (hL2D : L₂ ∈ D)
    (hW : ∀ g : Fin 17, g ∈ Dᶜ →
      ((¬G.Adj g L₁ ∧ ¬G.Adj g c₁ ∧ ¬G.Adj g L₁') ∨
        (¬G.Adj g c₁ ∧ ¬G.Adj g c₂ ∧ ¬G.Adj g L₂)) →
      (G.neighborFinset g ∩ Iso).card ≤ 1)
    (hA : ∀ t : Fin 17, t ∈ Iso → ∀ p q : Fin 17, p ≠ q →
      G.Adj t p → G.Adj t q →
      ¬((¬G.Adj p L₁ ∧ ¬G.Adj p c₁ ∧ ¬G.Adj p L₁' ∧
          ¬G.Adj q L₁ ∧ ¬G.Adj q c₁ ∧ ¬G.Adj q L₁') ∨
        (¬G.Adj p c₁ ∧ ¬G.Adj p c₂ ∧ ¬G.Adj p L₂ ∧
          ¬G.Adj q c₁ ∧ ¬G.Adj q c₂ ∧ ¬G.Adj q L₂)))
    (hDc9 : Dᶜ.card = 9) (hIso3 : Iso.card = 3)
    (hcard_c1 : (G.neighborFinset c₁ ∩ Dᶜ).card = 0)
    (hcard_c2 : (G.neighborFinset c₂ ∩ Dᶜ).card = 1)
    (hcard_L1 : (G.neighborFinset L₁ ∩ Dᶜ).card = 2)
    (hcard_L1' : (G.neighborFinset L₁' ∩ Dᶜ).card = 2)
    (hcard_L2 : (G.neighborFinset L₂ ∩ Dᶜ).card = 2)
    (hSum20 : ∑ w ∈ Dᶜ, (G.neighborFinset w ∩ Dᶜ).card = 20)
    (htri1 : ¬∃ a b c : Fin 17, a ∈ Dᶜ ∧ b ∈ Dᶜ ∧ c ∈ Dᶜ ∧
      G.Adj a b ∧ G.Adj a c ∧ G.Adj b c ∧
      (¬G.Adj a L₁ ∧ ¬G.Adj a c₁ ∧ ¬G.Adj a L₁') ∧
      (¬G.Adj b L₁ ∧ ¬G.Adj b c₁ ∧ ¬G.Adj b L₁') ∧
      (¬G.Adj c L₁ ∧ ¬G.Adj c c₁ ∧ ¬G.Adj c L₁'))
    (htri2 : ¬∃ a b c : Fin 17, a ∈ Dᶜ ∧ b ∈ Dᶜ ∧ c ∈ Dᶜ ∧
      G.Adj a b ∧ G.Adj a c ∧ G.Adj b c ∧
      (¬G.Adj a c₁ ∧ ¬G.Adj a c₂ ∧ ¬G.Adj a L₂) ∧
      (¬G.Adj b c₁ ∧ ¬G.Adj b c₂ ∧ ¬G.Adj b L₂) ∧
      (¬G.Adj c c₁ ∧ ¬G.Adj c c₂ ∧ ¬G.Adj c L₂)) :
    False := by
  classical
  obtain ⟨hDeq, _hdisj⟩ :=
    path_iso_partition_fatstar G D Iso c₁ c₂ L₁ L₁' L₂ hIsodef hisochar hc1D hc2D hL1D hL1'D hL2D
      hac1L1 hac1L1' hc12 hac2L2
  have hclassP : ∀ x : Fin 17, x ∈ D →
      x = c₁ ∨ x = c₂ ∨ x = L₁ ∨ x = L₁' ∨ x = L₂ ∨ x ∈ Iso := by
    intro x hx
    rw [← hDeq] at hx
    rcases Finset.mem_union.mp hx with h | h
    · simp only [Finset.mem_insert, Finset.mem_singleton] at h; tauto
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
  have hIsoD : Iso ⊆ D := by rw [hIsodef]; exact Finset.filter_subset _ _
  set A1 := Dᶜ.filter (fun g => ¬G.Adj g L₁ ∧ ¬G.Adj g c₁ ∧ ¬G.Adj g L₁') with hA1def
  set A2 := Dᶜ.filter (fun g => ¬G.Adj g c₁ ∧ ¬G.Adj g c₂ ∧ ¬G.Adj g L₂) with hA2def
  set FF := A1 ∩ A2 with hFFdef
  have hA1sub : A1 ⊆ Dᶜ := by rw [hA1def]; exact Finset.filter_subset _ _
  have hA2sub : A2 ⊆ Dᶜ := by rw [hA2def]; exact Finset.filter_subset _ _
  have hFFsubA1 : FF ⊆ A1 := by rw [hFFdef]; exact Finset.inter_subset_left
  have hFFsubA2 : FF ⊆ A2 := by rw [hFFdef]; exact Finset.inter_subset_right
  have hFFsub : FF ⊆ Dᶜ := hFFsubA1.trans hA1sub
  -- A1 internal degree ≥ 2 (via `hT`: no `g–c₂–L₂` triangle).
  have hA1int : ∀ g ∈ A1, 2 ≤ (G.neighborFinset g ∩ Dᶜ).card := by
    intro g hg
    rw [hA1def, Finset.mem_filter] at hg
    obtain ⟨hgDc, hgL1, hgc1, hgL1'⟩ := hg
    have hgD : g ∉ D := Finset.mem_compl.mp hgDc
    have hnboth : ¬(G.Adj g c₂ ∧ G.Adj g L₂) := by
      rintro ⟨hgc2, hgL2⟩
      apply hT
      refine ⟨g, c₂, L₂, ?_, hac2L2.ne, ?_, hgc2, hac2L2, hgL2, ?_⟩
      · rintro rfl; exact hgD hc2D
      · rintro rfl; exact hgD hL2D
      · have := hdeg4 g hgDc; omega
    refine avoider_internal_ge_two_pair G D Iso g c₂ L₂ (hdeg4 g hgDc)
      (hW g hgDc (Or.inl ⟨hgL1, hgc1, hgL1'⟩)) hnboth ?_
    intro x hadj hxD
    rcases hclassP x hxD with h | h | h | h | h | h
    · exact absurd (h ▸ hadj) hgc1
    · exact Or.inl h
    · exact absurd (h ▸ hadj) hgL1
    · exact absurd (h ▸ hadj) hgL1'
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  -- A2 internal degree ≥ 2 (via `hC4`: no `g–L₁–c₁–L₁'` good `C₄`).
  have hA2int : ∀ g ∈ A2, 2 ≤ (G.neighborFinset g ∩ Dᶜ).card := by
    intro g hg
    rw [hA2def, Finset.mem_filter] at hg
    obtain ⟨hgDc, hgc1, hgc2, hgL2⟩ := hg
    have hgD : g ∉ D := Finset.mem_compl.mp hgDc
    have hnboth : ¬(G.Adj g L₁ ∧ G.Adj g L₁') := by
      rintro ⟨hgL1, hgL1'⟩
      apply hC4
      refine ⟨g, L₁, c₁, L₁', ?_, hgL1, hac1L1.symm, hac1L1', hgL1'.symm, hgc1, hL1nL1', ?_⟩
      · rw [Finset.card_insert_of_notMem (by
              simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
              exact ⟨hgL1.ne, fun e => hgD (e ▸ hc1D), hgL1'.ne⟩),
            Finset.card_insert_of_notMem (by
              simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
              exact ⟨hac1L1.ne', hL1nL1'ne⟩),
            Finset.card_insert_of_notMem (by simp [hac1L1'.ne]), Finset.card_singleton]
      · have := hdeg4 g hgDc; omega
    refine avoider_internal_ge_two_pair G D Iso g L₁ L₁' (hdeg4 g hgDc)
      (hW g hgDc (Or.inr ⟨hgc1, hgc2, hgL2⟩)) hnboth ?_
    intro x hadj hxD
    rcases hclassP x hxD with h | h | h | h | h | h
    · exact absurd (h ▸ hadj) hgc1
    · exact absurd (h ▸ hadj) hgc2
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact absurd (h ▸ hadj) hgL2
    · exact Or.inr (Or.inr h)
  -- FF internal degree ≥ 3.
  have hFFint : ∀ g ∈ FF, 3 ≤ (G.neighborFinset g ∩ Dᶜ).card := by
    intro g hg
    have hgA1 := hFFsubA1 hg
    have hgA2 := hFFsubA2 hg
    rw [hA1def, Finset.mem_filter] at hgA1
    rw [hA2def, Finset.mem_filter] at hgA2
    obtain ⟨hgDc, hgL1, hgc1, hgL1'⟩ := hgA1
    obtain ⟨_, _, hgc2, hgL2⟩ := hgA2
    refine fully_free_internal_ge_three G D Iso g (hdeg4 g hgDc)
      (hW g hgDc (Or.inl ⟨hgL1, hgc1, hgL1'⟩)) ?_
    intro x hadj hxD
    rcases hclassP x hxD with h | h | h | h | h | h
    · exact absurd (h ▸ hadj) hgc1
    · exact absurd (h ▸ hadj) hgc2
    · exact absurd (h ▸ hadj) hgL1
    · exact absurd (h ▸ hadj) hgL1'
    · exact absurd (h ▸ hadj) hgL2
    · exact h
  -- `|A1| ≥ 5`, `|A2| ≥ 6`.
  have hA1card : 5 ≤ A1.card := by
    have := avoiders_ge_five_aux G D L₁ c₁ L₁' hDc9 (by omega)
    rwa [← hA1def] at this
  have hA2card : 6 ≤ A2.card := by
    have := avoiders_ge_six_aux G D c₁ c₂ L₂ hDc9 (by omega)
    rwa [← hA2def] at this
  -- Inclusion–exclusion budget: `|FF| ∈ {2, 3, 4, 5, 6}`.
  obtain ⟨hFFlb, hFFub⟩ :=
    active_hub_budget_fatstar Dᶜ A1 A2 FF (fun g => (G.neighborFinset g ∩ Dᶜ).card)
      hA1sub hA2sub hFFdef hA1card hA2card hA1int hA2int hFFint hSum20
  -- Residual incidence sums (path / iso totals and the per-hub split).
  obtain ⟨_hsumP, hsumI, hper⟩ :=
    incidence_sums_fatstar G D Iso c₁ c₂ L₁ L₁' L₂ hIsodef hIsoprop hisochar hc1D hc2D hL1D hL1'D
      hL2D hac1L1 hac1L1' hc12 hac2L2 hdeg4 hcard_c1 hcard_c2 hcard_L1 hcard_L1' hcard_L2 hIso3
      hc12.ne hac1L1.ne hac1L1'.ne hc1L2 hc2L1 hc2L1' hac2L2.ne hL1nL1'ne hL1L2 hL1'L2
  set P : Finset (Fin 17) := {c₁, c₂, L₁, L₁', L₂} with hPdef
  -- The inactive hubs `B = Dᶜ \ (A1 ∪ A2)`.
  set B := Dᶜ \ (A1 ∪ A2) with hBdef
  have hUsub : A1 ∪ A2 ⊆ Dᶜ := Finset.union_subset hA1sub hA2sub
  have hBsub : B ⊆ Dᶜ := by rw [hBdef]; exact Finset.sdiff_subset
  have hBpart : (∑ g ∈ B, (G.neighborFinset g ∩ Dᶜ).card)
      + ∑ g ∈ A1 ∪ A2, (G.neighborFinset g ∩ Dᶜ).card = 20 := by
    rw [hBdef, Finset.sum_sdiff hUsub, hSum20]
  have hIsoBpart : (∑ g ∈ B, (G.neighborFinset g ∩ Iso).card)
      + ∑ g ∈ A1 ∪ A2, (G.neighborFinset g ∩ Iso).card = 9 := by
    rw [hBdef, Finset.sum_sdiff hUsub, hsumI]
  -- A1/A2 internal sum split for the int lower bound on `A1 ∪ A2`.
  have hAUint2 : ∀ g ∈ A1 ∪ A2, 2 ≤ (G.neighborFinset g ∩ Dᶜ).card := by
    intro g hg
    rcases Finset.mem_union.mp hg with h | h
    · exact hA1int g h
    · exact hA2int g h
  have hUFFsub : FF ⊆ A1 ∪ A2 := hFFsubA1.trans Finset.subset_union_left
  have hUint_split : (∑ g ∈ (A1 ∪ A2) \ FF, (G.neighborFinset g ∩ Dᶜ).card)
      + ∑ g ∈ FF, (G.neighborFinset g ∩ Dᶜ).card
      = ∑ g ∈ A1 ∪ A2, (G.neighborFinset g ∩ Dᶜ).card := Finset.sum_sdiff hUFFsub
  have hUmFF_ge : 2 * ((A1 ∪ A2) \ FF).card
      ≤ ∑ g ∈ (A1 ∪ A2) \ FF, (G.neighborFinset g ∩ Dᶜ).card := by
    have := Finset.card_nsmul_le_sum ((A1 ∪ A2) \ FF)
      (fun g => (G.neighborFinset g ∩ Dᶜ).card) 2
      (fun g hg => hAUint2 g ((Finset.mem_sdiff.mp hg).1))
    simpa [smul_eq_mul, Nat.mul_comm] using this
  have hUmFFcard : ((A1 ∪ A2) \ FF).card + FF.card = (A1 ∪ A2).card := by
    have hFFinter : ((A1 ∪ A2) ∩ FF).card = FF.card := by
      rw [Finset.inter_eq_right.mpr hUFFsub]
    rw [← hFFinter]; exact Finset.card_sdiff_add_card_inter (A1 ∪ A2) FF
  have hFFsum_ge3 : 3 * FF.card ≤ ∑ g ∈ FF, (G.neighborFinset g ∩ Dᶜ).card := by
    have := Finset.card_nsmul_le_sum FF (fun g => (G.neighborFinset g ∩ Dᶜ).card) 3 hFFint
    simpa [smul_eq_mul, Nat.mul_comm] using this
  -- Iso-incidence bounds: each twin has `≤ 1` neighbour in `A1` and in `A2`.
  have hisoA1bd : ∀ t ∈ Iso, (G.neighborFinset t ∩ A1).card ≤ 1 := by
    intro t htIso
    by_contra hgt
    rw [not_le] at hgt
    obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp hgt
    rw [Finset.mem_inter, G.mem_neighborFinset] at hp hq
    obtain ⟨htp, hpA1⟩ := hp
    obtain ⟨htq, hqA1⟩ := hq
    rw [hA1def, Finset.mem_filter] at hpA1 hqA1
    obtain ⟨_, hpL1, hpc1, hpL1'⟩ := hpA1
    obtain ⟨_, hqL1, hqc1, hqL1'⟩ := hqA1
    exact hA t htIso p q hpq htp htq (Or.inl ⟨hpL1, hpc1, hpL1', hqL1, hqc1, hqL1'⟩)
  have hisoA2bd : ∀ t ∈ Iso, (G.neighborFinset t ∩ A2).card ≤ 1 := by
    intro t htIso
    by_contra hgt
    rw [not_le] at hgt
    obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp hgt
    rw [Finset.mem_inter, G.mem_neighborFinset] at hp hq
    obtain ⟨htp, hpA2⟩ := hp
    obtain ⟨htq, hqA2⟩ := hq
    rw [hA2def, Finset.mem_filter] at hpA2 hqA2
    obtain ⟨_, hpc1, hpc2, hpL2⟩ := hpA2
    obtain ⟨_, hqc1, hqc2, hqL2⟩ := hqA2
    exact hA t htIso p q hpq htp htq (Or.inr ⟨hpc1, hpc2, hpL2, hqc1, hqc2, hqL2⟩)
  have hisoA1le : (∑ g ∈ A1, (G.neighborFinset g ∩ Iso).card) ≤ 3 :=
    iso_incidence_le_three G Iso A1 hIso3 hisoA1bd
  have hisoA2le : (∑ g ∈ A2, (G.neighborFinset g ∩ Iso).card) ≤ 3 :=
    iso_incidence_le_three G Iso A2 hIso3 hisoA2bd
  have hIsoUnionInter : (∑ g ∈ A1 ∪ A2, (G.neighborFinset g ∩ Iso).card)
      + ∑ g ∈ FF, (G.neighborFinset g ∩ Iso).card
      = (∑ g ∈ A1, (G.neighborFinset g ∩ Iso).card)
        + ∑ g ∈ A2, (G.neighborFinset g ∩ Iso).card := by
    rw [hFFdef]; exact Finset.sum_union_inter
  -- Fully-free path-freeness: `iso + int = 4` on `FF`.
  have hFFpath0 : ∀ g ∈ FF, (G.neighborFinset g ∩ P).card = 0 := by
    intro g hg
    have hgA1 := hFFsubA1 hg
    have hgA2 := hFFsubA2 hg
    rw [hA1def, Finset.mem_filter] at hgA1
    rw [hA2def, Finset.mem_filter] at hgA2
    obtain ⟨_, hgL1, hgc1, hgL1'⟩ := hgA1
    obtain ⟨_, _, hgc2, hgL2⟩ := hgA2
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro a ha
    rw [Finset.mem_inter, G.mem_neighborFinset, hPdef] at ha
    obtain ⟨hadj, hmem⟩ := ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl
    · exact hgc1 hadj
    · exact hgc2 hadj
    · exact hgL1 hadj
    · exact hgL1' hadj
    · exact hgL2 hadj
  have hFFsum4 : (∑ g ∈ FF, (G.neighborFinset g ∩ Iso).card)
      + ∑ g ∈ FF, (G.neighborFinset g ∩ Dᶜ).card = 4 * FF.card := by
    have hcongr : ∀ g ∈ FF, (G.neighborFinset g ∩ Iso).card
        + (G.neighborFinset g ∩ Dᶜ).card = 4 := by
      intro g hg
      have hp := hper g (hFFsub hg)
      have h0 := hFFpath0 g hg
      omega
    rw [← Finset.sum_add_distrib, Finset.sum_congr rfl hcongr, Finset.sum_const, smul_eq_mul,
      Nat.mul_comm]
  -- Each inactive hub touches a cherry (`path ≥ 1`), hence `iso ≤ 3`.
  have hpath1 : ∀ h ∈ B, 1 ≤ (G.neighborFinset h ∩ P).card := by
    intro h hh
    rw [hBdef, Finset.mem_sdiff] at hh
    obtain ⟨hhDc, hhU⟩ := hh
    have hhA1 : h ∉ A1 := fun hmem => hhU (Finset.mem_union_left _ hmem)
    have hpred : ¬(¬G.Adj h L₁ ∧ ¬G.Adj h c₁ ∧ ¬G.Adj h L₁') := by
      intro hp
      exact hhA1 (by rw [hA1def, Finset.mem_filter]; exact ⟨hhDc, hp⟩)
    apply Finset.card_pos.mpr
    push Not at hpred
    by_cases h1 : G.Adj h L₁
    · exact ⟨L₁, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr h1, by rw [hPdef]; simp⟩⟩
    · by_cases h2 : G.Adj h c₁
      · exact ⟨c₁, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr h2, by rw [hPdef]; simp⟩⟩
      · exact ⟨L₁', Finset.mem_inter.mpr
          ⟨(G.mem_neighborFinset _ _).mpr (hpred h1 h2), by rw [hPdef]; simp⟩⟩
  have hisoB_le : (∑ g ∈ B, (G.neighborFinset g ∩ Iso).card) ≤ 3 * B.card := by
    have hle : ∀ g ∈ B, (G.neighborFinset g ∩ Iso).card ≤ 3 := by
      intro g hg
      have hgDc : g ∈ Dᶜ := hBsub hg
      have hp := hper g hgDc
      have hpa := hpath1 g hg
      omega
    calc (∑ g ∈ B, (G.neighborFinset g ∩ Iso).card) ≤ ∑ _g ∈ B, 3 := Finset.sum_le_sum hle
      _ = 3 * B.card := by rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
  -- Card relations.
  have hBcard_eq : B.card + (A1 ∪ A2).card = Dᶜ.card := by
    rw [hBdef, Finset.card_sdiff_add_card, Finset.union_eq_left.mpr hUsub]
  have hUcard : (A1 ∪ A2).card + FF.card = A1.card + A2.card := by
    rw [hFFdef]; exact Finset.card_union_add_card_inter A1 A2
  -- Redistribution: `∑_B iso ≥ 3 + ∑_FF iso`.
  have hredist : 3 + (∑ g ∈ FF, (G.neighborFinset g ∩ Iso).card)
      ≤ ∑ g ∈ B, (G.neighborFinset g ∩ Iso).card := by omega
  have hFFisoA1 : (∑ g ∈ FF, (G.neighborFinset g ∩ Iso).card) ≤ 3 :=
    le_trans (Finset.sum_le_sum_of_subset_of_nonneg hFFsubA1 (fun _ _ _ => Nat.zero_le _)) hisoA1le
  -- Dispatch on `|FF|`.
  have hFFcases : FF.card = 2 ∨ FF.card = 3 ∨ FF.card = 4 ∨ FF.card = 5 ∨ FF.card = 6 := by omega
  -- `getA2`: a triangle inside `FF` contradicts `htri2`.
  have getA2 : ∀ g : Fin 17, g ∈ FF →
      g ∈ Dᶜ ∧ ¬G.Adj g c₁ ∧ ¬G.Adj g c₂ ∧ ¬G.Adj g L₂ := by
    intro g hg
    have hgA2 := hFFsubA2 hg
    rw [hA2def, Finset.mem_filter] at hgA2; exact hgA2
  rcases hFFcases with hFF | hFF | hFF | hFF | hFF
  · -- `|FF| = 2`: budget forces `|B| = 0`, but `∑_B iso ≥ 3 > 0`.
    exfalso
    have hUcardle : (A1 ∪ A2).card ≤ 9 := by rw [← hDc9]; exact Finset.card_le_card hUsub
    have hB0 : B.card = 0 := by omega
    have hisoB0 : (∑ g ∈ B, (G.neighborFinset g ∩ Iso).card) = 0 := by
      rw [Finset.card_eq_zero.mp hB0, Finset.sum_empty]
    omega
  · -- `|FF| = 3`: `|B| ≤ 1`.  Either `|B| = 0` (`∑_B iso = 0 < 3`) or `|B| = 1` (a counting
    -- contradiction: `∑_FF int = 12`, the single inactive hub is internally isolated, and the
    -- five active non-`FF` hubs carry `∑ int ≥ 10`, so `∑_{A1∪A2} int ≥ 22 > 20`).
    exfalso
    have hUcardle : (A1 ∪ A2).card ≤ 9 := by rw [← hDc9]; exact Finset.card_le_card hUsub
    have hBle1 : B.card ≤ 1 := by omega
    interval_cases hBc : B.card
    · have hisoB0 : (∑ g ∈ B, (G.neighborFinset g ∩ Iso).card) = 0 := by
        rw [Finset.card_eq_zero.mp hBc, Finset.sum_empty]
      omega
    · -- `|B| = 1`: `∑_B int ≤ 1 → ∑_{A1∪A2} int ≥ 19`, but `∑_FF int = 12` and the five
      -- non-`FF` active hubs give `∑ ≥ 10`, forcing `∑_{A1∪A2} int ≥ 22 > 20`.
      have hBint_le : (∑ g ∈ B, (G.neighborFinset g ∩ Dᶜ).card) ≤ 3 := by
        have hle : ∀ g ∈ B, (G.neighborFinset g ∩ Dᶜ).card ≤ 3 := by
          intro g hg
          have hp := hper g (hBsub hg)
          have hpa := hpath1 g hg
          omega
        calc (∑ g ∈ B, (G.neighborFinset g ∩ Dᶜ).card) ≤ ∑ _g ∈ B, 3 := Finset.sum_le_sum hle
          _ = 3 * B.card := by rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
          _ ≤ 3 := by omega
      -- `∑_FF iso = 0`, `∑_B iso = 3`.
      have hFFiso0 : (∑ g ∈ FF, (G.neighborFinset g ∩ Iso).card) = 0 := by omega
      have hFFint12 : (∑ g ∈ FF, (G.neighborFinset g ∩ Dᶜ).card) = 12 := by omega
      -- The single inactive hub is internally isolated: `int = 0`.
      have hBint0 : (∑ g ∈ B, (G.neighborFinset g ∩ Dᶜ).card) = 0 := by
        have hiso3 : (∑ g ∈ B, (G.neighborFinset g ∩ Iso).card) = 3 := by omega
        obtain ⟨h, hheq⟩ := Finset.card_eq_one.mp hBc
        have hhB : h ∈ B := by rw [hheq]; simp
        have hp := hper h (hBsub hhB)
        have hpa := hpath1 h hhB
        have hisoh : (G.neighborFinset h ∩ Iso).card = 3 := by
          rw [hheq, Finset.sum_singleton] at hiso3; exact hiso3
        rw [hheq, Finset.sum_singleton]; omega
      omega
  · -- `|FF| = 4`: `|B| ≤ 2`, `∑_FF int ∈ {13, 14, 15, 16}`.  `13` ⇒ two iso-`3` non-adjacent
    -- inactive hubs (share); `14` ⇒ `∑_B int = 0` with an asymmetric iso-`3`/iso-`≥ 2` share;
    -- `≥ 15` ⇒ a Mantel-`4` triangle in `FF ⊆ A2`.
    exfalso
    have hUcardle : (A1 ∪ A2).card ≤ 9 := by rw [← hDc9]; exact Finset.card_le_card hUsub
    have hBle2 : B.card ≤ 2 := by omega
    have hScase : (∑ g ∈ FF, (G.neighborFinset g ∩ Dᶜ).card) = 13
        ∨ (∑ g ∈ FF, (G.neighborFinset g ∩ Dᶜ).card) = 14
        ∨ 15 ≤ ∑ g ∈ FF, (G.neighborFinset g ∩ Dᶜ).card := by omega
    rcases hScase with hS | hS | hS
    · -- `∑_FF int = 13`: `∑_FF iso = 3`, `∑_B iso ≥ 6`, `|B| = 2`, both iso-`3`, int-`0`.
      have hFFiso3 : (∑ g ∈ FF, (G.neighborFinset g ∩ Iso).card) = 3 := by omega
      have hisoB6 : 6 ≤ ∑ g ∈ B, (G.neighborFinset g ∩ Iso).card := by omega
      have hB2 : B.card = 2 := by omega
      obtain ⟨h₁, h₂, hh12, hBeq⟩ := Finset.card_eq_two.mp hB2
      have hh1B : h₁ ∈ B := by rw [hBeq]; simp
      have hh2B : h₂ ∈ B := by rw [hBeq]; simp
      have hh1Dc : h₁ ∈ Dᶜ := hBsub hh1B
      have hh2Dc : h₂ ∈ Dᶜ := hBsub hh2B
      have hisosum : (G.neighborFinset h₁ ∩ Iso).card + (G.neighborFinset h₂ ∩ Iso).card
          = ∑ g ∈ B, (G.neighborFinset g ∩ Iso).card := by rw [hBeq, Finset.sum_pair hh12]
      have hp1 := hper h₁ hh1Dc
      have hp2 := hper h₂ hh2Dc
      have hpa1 := hpath1 h₁ hh1B
      have hpa2 := hpath1 h₂ hh2B
      have hiso1 : (G.neighborFinset h₁ ∩ Iso).card = 3 := by omega
      have hiso2 : (G.neighborFinset h₂ ∩ Iso).card = 3 := by omega
      have hint1 : (G.neighborFinset h₁ ∩ Dᶜ).card = 0 := by omega
      have hnadj : ¬G.Adj h₁ h₂ := by
        intro hadj
        have hmem : h₂ ∈ G.neighborFinset h₁ ∩ Dᶜ :=
          Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hadj, hh2Dc⟩
        rw [Finset.card_eq_zero] at hint1
        rw [hint1] at hmem; exact (Finset.notMem_empty _) hmem
      exact two_iso3_nonadj_false_fs G D Iso hC4 hIsoD hIsoprop hdeg4 hIso3 h₁ h₂ hh1Dc hh2Dc hh12
        hnadj hiso1 hiso2
    · -- `∑_FF int = 14`: `|B| = 2`, `∑_B int = 0` (both inactive hubs internally isolated), and
      -- `∑_B iso ≥ 5` forces one hub adjacent to all three twins and the other to `≥ 2`, sharing
      -- `≥ 2` — an `iso3_other_share_false` contradiction.
      have hisoB5 : 5 ≤ ∑ g ∈ B, (G.neighborFinset g ∩ Iso).card := by omega
      have hB2 : B.card = 2 := by omega
      have hBint0 : (∑ g ∈ B, (G.neighborFinset g ∩ Dᶜ).card) = 0 := by omega
      obtain ⟨h₁, h₂, hh12, hBeq⟩ := Finset.card_eq_two.mp hB2
      have hh1B : h₁ ∈ B := by rw [hBeq]; simp
      have hh2B : h₂ ∈ B := by rw [hBeq]; simp
      have hh1Dc : h₁ ∈ Dᶜ := hBsub hh1B
      have hh2Dc : h₂ ∈ Dᶜ := hBsub hh2B
      have hisosum : (G.neighborFinset h₁ ∩ Iso).card + (G.neighborFinset h₂ ∩ Iso).card
          = ∑ g ∈ B, (G.neighborFinset g ∩ Iso).card := by rw [hBeq, Finset.sum_pair hh12]
      have hintsum : (G.neighborFinset h₁ ∩ Dᶜ).card + (G.neighborFinset h₂ ∩ Dᶜ).card
          = ∑ g ∈ B, (G.neighborFinset g ∩ Dᶜ).card := by rw [hBeq, Finset.sum_pair hh12]
      have hint1 : (G.neighborFinset h₁ ∩ Dᶜ).card = 0 := by omega
      have hp1 := hper h₁ hh1Dc
      have hp2 := hper h₂ hh2Dc
      have hpa1 := hpath1 h₁ hh1B
      have hpa2 := hpath1 h₂ hh2B
      have hnadj : ¬G.Adj h₁ h₂ := by
        intro hadj
        have hmem : h₂ ∈ G.neighborFinset h₁ ∩ Dᶜ :=
          Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hadj, hh2Dc⟩
        rw [Finset.card_eq_zero] at hint1
        rw [hint1] at hmem; exact (Finset.notMem_empty _) hmem
      -- One of the two inactive hubs is adjacent to all three twins.
      have hiso1le : (G.neighborFinset h₁ ∩ Iso).card ≤ 3 := by omega
      have hiso2le : (G.neighborFinset h₂ ∩ Iso).card ≤ 3 := by omega
      by_cases hc1 : (G.neighborFinset h₁ ∩ Iso).card = 3
      · exact iso3_other_share_false G D Iso hC4 hIsoD hIsoprop hdeg4 hIso3 h₁ h₂ hh1Dc hh2Dc hh12
          hnadj hc1 (by omega)
      · have hc2 : (G.neighborFinset h₂ ∩ Iso).card = 3 := by omega
        exact iso3_other_share_false G D Iso hC4 hIsoD hIsoprop hdeg4 hIso3 h₂ h₁ hh2Dc hh1Dc
          (Ne.symm hh12) (fun hadj => hnadj hadj.symm) hc2 (by omega)
    · -- `∑_FF int ≥ 15`: `∑_FF(N ∩ FF) ≥ 10`, a Mantel-`4` triangle in `FF ⊆ A2`.
      have hedge : 10 ≤ ∑ g ∈ FF, (G.neighborFinset g ∩ FF).card := by
        have hlb := ff_internal_edge_lb_twenty G Dᶜ FF hFFsub hSum20
        omega
      obtain ⟨a, b, c, haFF, hbFF, hcFF, hab, hac, hbc⟩ := mantel_four_triangle G FF hFF hedge
      obtain ⟨haDc, hac1, hac2, haL2⟩ := getA2 a haFF
      obtain ⟨hbDc, hbc1, hbc2, hbL2⟩ := getA2 b hbFF
      obtain ⟨hcDc, hcc1, hcc2, hcL2⟩ := getA2 c hcFF
      exact htri2 ⟨a, b, c, haDc, hbDc, hcDc, hab, hac, hbc,
        ⟨hac1, hac2, haL2⟩, ⟨hbc1, hbc2, hbL2⟩, ⟨hcc1, hcc2, hcL2⟩⟩
  · -- `|FF| = 5`: `∑_FF int ≥ 17 → ∑_FF(N ∩ FF) ≥ 14`, a Mantel-`5` triangle in `FF ⊆ A2`,
    -- contradicting `htri2`.
    exfalso
    have hFFint17 : 17 ≤ ∑ g ∈ FF, (G.neighborFinset g ∩ Dᶜ).card := by omega
    have hedge : 14 ≤ ∑ g ∈ FF, (G.neighborFinset g ∩ FF).card := by
      have hlb := ff_internal_edge_lb_twenty G Dᶜ FF hFFsub hSum20
      omega
    obtain ⟨a, b, c, haFF, hbFF, hcFF, hab, hac, hbc⟩ := mantel_five_triangle G FF hFF hedge
    obtain ⟨haDc, hac1, hac2, haL2⟩ := getA2 a haFF
    obtain ⟨hbDc, hbc1, hbc2, hbL2⟩ := getA2 b hbFF
    obtain ⟨hcDc, hcc1, hcc2, hcL2⟩ := getA2 c hcFF
    exact htri2 ⟨a, b, c, haDc, hbDc, hcDc, hab, hac, hbc,
      ⟨hac1, hac2, haL2⟩, ⟨hbc1, hbc2, hbL2⟩, ⟨hcc1, hcc2, hcL2⟩⟩
  · -- `|FF| = 6`: `∑_FF iso ≤ 3` and `iso + int = 4` per fully-free hub force `∑_FF int ≥ 21 > 20`.
    exfalso
    omega

/-- **Hub-triangle existence in the `n = 17`, `|D| = 8`, `e(M) = 4` fat double-star corner.**  Under
the residual hypotheses (nine degree-`4` hubs, the fat dominating-edge double-star
`L₁, L₁' – c₁ – c₂ – L₂` with three `M`-isolated twins, and the falsity of
`SingleVertexConfig`/`TwoTwinConfig`/`TwoHubConfig`), the graph contains three pairwise-adjacent
hubs avoiding the fat cherry `L₁–c₁–L₁'`, packaged as `HubTriangleConfig G`. -/
theorem exists_hub_triangle_config_fatstar_seventeen (G : SimpleGraph (Fin 17))
    (D Iso : Finset (Fin 17)) (c₁ c₂ L₁ L₁' L₂ : Fin 17)
    (hT : ¬∃ x y z : Fin 17, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    (hC4 : ¬∃ a b c d : Fin 17, ({a, b, c, d} : Finset (Fin 17)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (hmemD : ∀ v : Fin 17, v ∈ D ↔ G.degree v = 3)
    (hIsodef : Iso = D.filter (fun v => (G.neighborFinset v ∩ D).card = 0))
    (hIsoprop : ∀ v ∈ Iso, G.degree v = 3 ∧ (∀ w : Fin 17, G.Adj v w → G.degree w ≠ 3))
    (hisochar : ∀ w : Fin 17, w ∈ D → w ≠ c₁ → w ≠ c₂ → w ≠ L₁ → w ≠ L₁' → w ≠ L₂ → w ∈ Iso)
    (hNc1D : G.neighborFinset c₁ ∩ D = {c₂, L₁, L₁'})
    (hNc2D : G.neighborFinset c₂ ∩ D = {c₁, L₂})
    (hNL1D : G.neighborFinset L₁ ∩ D = {c₁}) (hNL1'D : G.neighborFinset L₁' ∩ D = {c₁})
    (hNL2D : G.neighborFinset L₂ ∩ D = {c₂})
    (hc1deg : G.degree c₁ = 3) (hc2deg : G.degree c₂ = 3) (hL1deg : G.degree L₁ = 3)
    (hL1'deg : G.degree L₁' = 3) (hL2deg : G.degree L₂ = 3)
    (hac1L1 : G.Adj c₁ L₁) (hac1L1' : G.Adj c₁ L₁') (hc12 : G.Adj c₁ c₂) (hac2L2 : G.Adj c₂ L₂)
    (hnL1L1' : ¬G.Adj L₁ L₁') (hnL1c2 : ¬G.Adj L₁ c₂) (hnL1'c2 : ¬G.Adj L₁' c₂)
    (hnc1L2 : ¬G.Adj c₁ L₂)
    (hL1nL1' : L₁ ≠ L₁') (hL1nc2 : L₁ ≠ c₂) (hL1'nc2 : L₁' ≠ c₂) (hL2nc1 : L₂ ≠ c₁)
    (hL1nL2 : L₁ ≠ L₂) (hL1'nL2 : L₁' ≠ L₂)
    (hdeg4 : ∀ w : Fin 17, w ∈ Dᶜ → G.degree w = 4) (hD8 : D.card = 8)
    (hsv : ¬SingleVertexConfig G) (htt : ¬TwoTwinConfig G) (_hth : ¬TwoHubConfig G) :
    HubTriangleConfig G := by
  classical
  have hL1D : L₁ ∈ D := (hmemD L₁).mpr hL1deg
  have hL1'D : L₁' ∈ D := (hmemD L₁').mpr hL1'deg
  have hc1D : c₁ ∈ D := (hmemD c₁).mpr hc1deg
  have hc2D : c₂ ∈ D := (hmemD c₂).mpr hc2deg
  have hL2D : L₂ ∈ D := (hmemD L₂).mpr hL2deg
  have hc1nc2 : c₁ ≠ c₂ := hc12.ne
  have hc1nL1 : c₁ ≠ L₁ := hac1L1.ne
  have hc1nL1' : c₁ ≠ L₁' := hac1L1'.ne
  have hc2nL2 : c₂ ≠ L₂ := hac2L2.ne
  -- **(W) [from `¬TwoTwinConfig`].**  Any hub avoiding a cherry has `≤ 1` `M`-isolated-twin
  -- neighbour.
  have hW : ∀ g : Fin 17, g ∈ Dᶜ →
      ((¬G.Adj g L₁ ∧ ¬G.Adj g c₁ ∧ ¬G.Adj g L₁') ∨
        (¬G.Adj g c₁ ∧ ¬G.Adj g c₂ ∧ ¬G.Adj g L₂)) →
      (G.neighborFinset g ∩ Iso).card ≤ 1 := by
    intro g hgDc havoid
    by_contra hge2
    rw [not_le] at hge2
    obtain ⟨s1, hs1m, s2, hs2m, hs12⟩ := Finset.one_lt_card.mp hge2
    rw [Finset.mem_inter, G.mem_neighborFinset] at hs1m hs2m
    obtain ⟨hgs1, hs1Iso⟩ := hs1m
    obtain ⟨hgs2, hs2Iso⟩ := hs2m
    obtain ⟨hs1deg, hs1iso⟩ := hIsoprop s1 hs1Iso
    obtain ⟨hs2deg, hs2iso⟩ := hIsoprop s2 hs2Iso
    have hgdeg5 : G.degree g ≤ 5 := by have := hdeg4 g hgDc; omega
    apply htt
    rcases havoid with ⟨hgL1, hgc1, hgL1'⟩ | ⟨hgc1, hgc2, hgL2⟩
    · exact ⟨s1, s2, g, L₁, c₁, L₁', hs1deg, hs2deg, hgdeg5,
        hL1deg, hc1deg, hL1'deg, hgs1.symm, hgs2.symm, hac1L1.symm, hac1L1',
        (fun ha => hs1iso L₁ ha hL1deg), (fun ha => hs1iso c₁ ha hc1deg),
        (fun ha => hs1iso L₁' ha hL1'deg),
        (fun ha => hs2iso L₁ ha hL1deg), (fun ha => hs2iso c₁ ha hc1deg),
        (fun ha => hs2iso L₁' ha hL1'deg),
        hgL1, hgc1, hgL1', hs12,
        (by rintro rfl; exact hs1iso c₁ hac1L1.symm hc1deg),
        (by rintro rfl; exact hs1iso L₁ hac1L1 hL1deg),
        (by rintro rfl; exact hs1iso c₁ hac1L1'.symm hc1deg),
        (by rintro rfl; exact hs2iso c₁ hac1L1.symm hc1deg),
        (by rintro rfl; exact hs2iso L₁ hac1L1 hL1deg),
        (by rintro rfl; exact hs2iso c₁ hac1L1'.symm hc1deg),
        (by rintro rfl; exact (Finset.mem_compl.mp hgDc) hL1D),
        (by rintro rfl; exact (Finset.mem_compl.mp hgDc) hc1D),
        (by rintro rfl; exact (Finset.mem_compl.mp hgDc) hL1'D),
        hac1L1.ne', hac1L1'.ne, hL1nL1'⟩
    · exact ⟨s1, s2, g, c₁, c₂, L₂, hs1deg, hs2deg, hgdeg5,
        hc1deg, hc2deg, hL2deg, hgs1.symm, hgs2.symm, hc12, hac2L2,
        (fun ha => hs1iso c₁ ha hc1deg), (fun ha => hs1iso c₂ ha hc2deg),
        (fun ha => hs1iso L₂ ha hL2deg),
        (fun ha => hs2iso c₁ ha hc1deg), (fun ha => hs2iso c₂ ha hc2deg),
        (fun ha => hs2iso L₂ ha hL2deg),
        hgc1, hgc2, hgL2, hs12,
        (by rintro rfl; exact hs1iso c₂ hc12 hc2deg),
        (by rintro rfl; exact hs1iso L₂ hac2L2 hL2deg),
        (by rintro rfl; exact hs1iso c₂ hac2L2.symm hc2deg),
        (by rintro rfl; exact hs2iso c₂ hc12 hc2deg),
        (by rintro rfl; exact hs2iso L₂ hac2L2 hL2deg),
        (by rintro rfl; exact hs2iso c₂ hac2L2.symm hc2deg),
        (by rintro rfl; exact (Finset.mem_compl.mp hgDc) hc1D),
        (by rintro rfl; exact (Finset.mem_compl.mp hgDc) hc2D),
        (by rintro rfl; exact (Finset.mem_compl.mp hgDc) hL2D),
        hc12.ne, hac2L2.ne, hL2nc1.symm⟩
  -- **(A) [from `¬SingleVertexConfig`].**
  have hA : ∀ t : Fin 17, t ∈ Iso → ∀ p q : Fin 17, p ≠ q →
      G.Adj t p → G.Adj t q →
      ¬((¬G.Adj p L₁ ∧ ¬G.Adj p c₁ ∧ ¬G.Adj p L₁' ∧
          ¬G.Adj q L₁ ∧ ¬G.Adj q c₁ ∧ ¬G.Adj q L₁') ∨
        (¬G.Adj p c₁ ∧ ¬G.Adj p c₂ ∧ ¬G.Adj p L₂ ∧
          ¬G.Adj q c₁ ∧ ¬G.Adj q c₂ ∧ ¬G.Adj q L₂)) := by
    intro t htIso p q hpq htp htq havoid
    have htiso_prop : ∀ w : Fin 17, G.Adj t w → G.degree w ≠ 3 := (hIsoprop t htIso).2
    have htdeg : G.degree t = 3 := (hIsoprop t htIso).1
    have hpDc : p ∈ Dᶜ :=
      Finset.mem_compl.mpr (fun hpD => htiso_prop p htp ((hmemD p).mp hpD))
    have hqDc : q ∈ Dᶜ :=
      Finset.mem_compl.mpr (fun hqD => htiso_prop q htq ((hmemD q).mp hqD))
    have hdp : G.degree p = 4 := hdeg4 p hpDc
    have hdq : G.degree q = 4 := hdeg4 q hqDc
    apply hsv
    rcases havoid with ⟨hpL1, hpc1, hpL1', hqL1, hqc1, hqL1'⟩ |
      ⟨hpc1, hpc2, hpL2, hqc1, hqc2, hqL2⟩
    · have hsum0 : ∑ w ∈ ({t, p, q} : Finset (Fin 17)),
          (G.neighborFinset w ∩ ({L₁, c₁, L₁'} : Finset (Fin 17))).card = 0 := by
        apply Finset.sum_eq_zero
        intro w hw
        rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
        intro a ha
        rw [Finset.mem_inter, G.mem_neighborFinset] at ha
        obtain ⟨hadj, hmem⟩ := ha
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw hmem
        rcases hw with rfl | rfl | rfl <;> rcases hmem with rfl | rfl | rfl
        · exact htiso_prop _ hadj hL1deg
        · exact htiso_prop _ hadj hc1deg
        · exact htiso_prop _ hadj hL1'deg
        · exact hpL1 hadj
        · exact hpc1 hadj
        · exact hpL1' hadj
        · exact hqL1 hadj
        · exact hqc1 hadj
        · exact hqL1' hadj
      exact ⟨t, p, q, L₁, c₁, L₁', htdeg, hL1deg, hc1deg, hL1'deg, htp, htq,
        hac1L1.symm, hac1L1', hnL1L1', (by rw [hsum0, hdp, hdq]; omega), hpq,
        (fun e => htiso_prop c₁ (by rw [e]; exact hac1L1.symm) hc1deg),
        (fun e => htiso_prop L₁ (by rw [e]; exact hac1L1) hL1deg),
        (fun e => htiso_prop c₁ (by rw [e]; exact hac1L1'.symm) hc1deg),
        (by rintro rfl; omega), (by rintro rfl; omega), (by rintro rfl; omega),
        (by rintro rfl; omega), (by rintro rfl; omega), (by rintro rfl; omega),
        hac1L1.ne', hac1L1'.ne, hL1nL1'⟩
    · have hsum0 : ∑ w ∈ ({t, p, q} : Finset (Fin 17)),
          (G.neighborFinset w ∩ ({c₁, c₂, L₂} : Finset (Fin 17))).card = 0 := by
        apply Finset.sum_eq_zero
        intro w hw
        rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
        intro a ha
        rw [Finset.mem_inter, G.mem_neighborFinset] at ha
        obtain ⟨hadj, hmem⟩ := ha
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw hmem
        rcases hw with rfl | rfl | rfl <;> rcases hmem with rfl | rfl | rfl
        · exact htiso_prop _ hadj hc1deg
        · exact htiso_prop _ hadj hc2deg
        · exact htiso_prop _ hadj hL2deg
        · exact hpc1 hadj
        · exact hpc2 hadj
        · exact hpL2 hadj
        · exact hqc1 hadj
        · exact hqc2 hadj
        · exact hqL2 hadj
      exact ⟨t, p, q, c₁, c₂, L₂, htdeg, hc1deg, hc2deg, hL2deg, htp, htq,
        hc12, hac2L2, hnc1L2, (by rw [hsum0, hdp, hdq]; omega), hpq,
        (fun e => htiso_prop c₂ (by rw [e]; exact hc12) hc2deg),
        (fun e => htiso_prop c₁ (by rw [e]; exact hc12.symm) hc1deg),
        (fun e => htiso_prop c₂ (by rw [e]; exact hac2L2.symm) hc2deg),
        (by rintro rfl; omega), (by rintro rfl; omega), (by rintro rfl; omega),
        (by rintro rfl; omega), (by rintro rfl; omega), (by rintro rfl; omega),
        hc12.ne, hac2L2.ne, hL2nc1.symm⟩
  -- Hubs (`Dᶜ`) are disjoint from the path vertices.
  have hubne : ∀ g : Fin 17, g ∈ Dᶜ → g ≠ c₁ ∧ g ≠ c₂ ∧ g ≠ L₁ ∧ g ≠ L₁' ∧ g ≠ L₂ := by
    intro g hg
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rintro rfl
    · exact (Finset.mem_compl.mp hg) hc1D
    · exact (Finset.mem_compl.mp hg) hc2D
    · exact (Finset.mem_compl.mp hg) hL1D
    · exact (Finset.mem_compl.mp hg) hL1'D
    · exact (Finset.mem_compl.mp hg) hL2D
  -- Hub / twin counts and the hub-incidence cards.
  obtain ⟨hDc9, hIso3⟩ := hub_struct_fatstar G D Iso c₁ c₂ L₁ L₁' L₂ hIsodef hisochar hc1D hc2D
    hL1D hL1'D hL2D hac1L1 hac1L1' hc12 hac2L2 hL1nL1' hL1nc2 hL1'nc2 hL2nc1 hnc1L2 hL1nL2.symm
    hL1'nL2.symm hD8
  obtain ⟨hcard_c1, hcard_c2, hcard_L1, hcard_L1', hcard_L2⟩ :=
    path_hub_incidence_fatstar G D c₁ c₂ L₁ L₁' L₂ hNc1D hNc2D hNL1D hNL1'D hNL2D hc1deg hc2deg
      hL1deg hL1'deg hL2deg hL1nL1' hL1nc2 hL1'nc2 hL2nc1
  obtain ⟨hsumP, hsumI, hper⟩ :=
    incidence_sums_fatstar G D Iso c₁ c₂ L₁ L₁' L₂ hIsodef hIsoprop hisochar hc1D hc2D hL1D hL1'D
      hL2D hac1L1 hac1L1' hc12 hac2L2 hdeg4 hcard_c1 hcard_c2 hcard_L1 hcard_L1' hcard_L2 hIso3
      hc1nc2 hc1nL1 hc1nL1' hL2nc1.symm (Ne.symm hL1nc2) (Ne.symm hL1'nc2) hac2L2.ne hL1nL1'
      hL1nL2 hL1'nL2
  have hSum20 : ∑ w ∈ Dᶜ, (G.neighborFinset w ∩ Dᶜ).card = 20 := by
    have htot : ∑ g ∈ Dᶜ, ((G.neighborFinset g ∩ ({c₁, c₂, L₁, L₁', L₂} : Finset (Fin 17))).card
        + (G.neighborFinset g ∩ Iso).card + (G.neighborFinset g ∩ Dᶜ).card)
        = ∑ _g ∈ Dᶜ, 4 := Finset.sum_congr rfl hper
    rw [Finset.sum_const, smul_eq_mul, hDc9, Finset.sum_add_distrib, Finset.sum_add_distrib,
      hsumP, hsumI] at htot
    omega
  -- **Branch 1: a triangle of cherry-`{L₁,c₁,L₁'}` avoiders ⇒ `HubTriangleConfig` directly.**
  by_cases htri1 : ∃ a b c : Fin 17, a ∈ Dᶜ ∧ b ∈ Dᶜ ∧ c ∈ Dᶜ ∧
      G.Adj a b ∧ G.Adj a c ∧ G.Adj b c ∧
      (¬G.Adj a L₁ ∧ ¬G.Adj a c₁ ∧ ¬G.Adj a L₁') ∧
      (¬G.Adj b L₁ ∧ ¬G.Adj b c₁ ∧ ¬G.Adj b L₁') ∧
      (¬G.Adj c L₁ ∧ ¬G.Adj c c₁ ∧ ¬G.Adj c L₁')
  · obtain ⟨a, b, c, haDc, hbDc, hcDc, hab, hac, hbc,
      ⟨haL1, hac1, haL1'⟩, ⟨hbL1, hbc1, hbL1'⟩, ⟨hcL1, hcc1, hcL1'⟩⟩ := htri1
    obtain ⟨_, _, haneL1, haneL1', _⟩ := hubne a haDc
    obtain ⟨_, _, hbneL1, hbneL1', _⟩ := hubne b hbDc
    obtain ⟨_, _, hcneL1, hcneL1', _⟩ := hubne c hcDc
    obtain ⟨hanec1, _, _, _, _⟩ := hubne a haDc
    obtain ⟨hbnec1, _, _, _, _⟩ := hubne b hbDc
    obtain ⟨hcnec1, _, _, _, _⟩ := hubne c hcDc
    exact ⟨a, b, c, L₁, c₁, L₁', hL1deg, hc1deg, hL1'deg, hab, hac, hbc,
      hac1L1.symm, hac1L1', haL1, hac1, haL1', hbL1, hbc1, hbL1', hcL1, hcc1, hcL1',
      (by have := hdeg4 a haDc; have := hdeg4 b hbDc; have := hdeg4 c hcDc; omega),
      haneL1, hanec1, haneL1', hbneL1, hbnec1, hbneL1', hcneL1, hcnec1, hcneL1',
      hac1L1.ne', hac1L1'.ne, hL1nL1'⟩
  -- **Branch 2: a triangle of cherry-`{c₁,c₂,L₂}` avoiders ⇒ `HubTriangleConfig` directly.**
  by_cases htri2 : ∃ a b c : Fin 17, a ∈ Dᶜ ∧ b ∈ Dᶜ ∧ c ∈ Dᶜ ∧
      G.Adj a b ∧ G.Adj a c ∧ G.Adj b c ∧
      (¬G.Adj a c₁ ∧ ¬G.Adj a c₂ ∧ ¬G.Adj a L₂) ∧
      (¬G.Adj b c₁ ∧ ¬G.Adj b c₂ ∧ ¬G.Adj b L₂) ∧
      (¬G.Adj c c₁ ∧ ¬G.Adj c c₂ ∧ ¬G.Adj c L₂)
  · obtain ⟨a, b, c, haDc, hbDc, hcDc, hab, hac, hbc,
      ⟨hac1, hac2, haL2⟩, ⟨hbc1, hbc2, hbL2⟩, ⟨hcc1, hcc2, hcL2⟩⟩ := htri2
    obtain ⟨hanec1, hanec2, _, _, haneL2⟩ := hubne a haDc
    obtain ⟨hbnec1, hbnec2, _, _, hbneL2⟩ := hubne b hbDc
    obtain ⟨hcnec1, hcnec2, _, _, hcneL2⟩ := hubne c hcDc
    exact ⟨a, b, c, c₁, c₂, L₂, hc1deg, hc2deg, hL2deg, hab, hac, hbc,
      hc12, hac2L2, hac1, hac2, haL2, hbc1, hbc2, hbL2, hcc1, hcc2, hcL2,
      (by have := hdeg4 a haDc; have := hdeg4 b hbDc; have := hdeg4 c hcDc; omega),
      hanec1, hanec2, haneL2, hbnec1, hbnec2, hbneL2, hcnec1, hcnec2, hcneL2,
      hc12.ne, hac2L2.ne, hL2nc1.symm⟩
  -- **Branch 3: no avoider triangle for either cherry ⇒ contradiction.**
  exact absurd (iso_rich_force_fatstar G D Iso c₁ c₂ L₁ L₁' L₂ hT hC4 hIsodef hIsoprop hisochar
    hc1deg hc2deg hL1deg hL1'deg hL2deg hac1L1 hac1L1' hc12 hac2L2 hnL1L1' hL1nL1'
    hL2nc1.symm hL1nc2.symm hL1'nc2.symm hL1nL2 hL1'nL2 hdeg4 hc1D hc2D hL1D hL1'D hL2D hW hA hDc9
    hIso3
    hcard_c1 hcard_c2 hcard_L1 hcard_L1' hcard_L2 hSum20 htri1 htri2) (fun h => h)

end N17

end ACMax
