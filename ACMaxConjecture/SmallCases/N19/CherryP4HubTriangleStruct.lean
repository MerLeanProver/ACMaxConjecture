import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N19.Core
import ACMaxConjecture.SmallCases.StarCertificates
import ACMaxConjecture.SmallCases.N19.Core

/-!
# Structural counts for the `n = 17`, `e(M) = 3`, `P₄`-cherry `|D| ∈ {9, 10}` hub-triangle corner

Constant-generalised port of `TwinCert17HubTriangleStruct` (the `|D| = 8` corner): the residual
degree-`3` graph is the path `L₁–c₁–c₂–L₂` plus `M`-isolated twins `Iso`, and the hubs are `Dᶜ`.
With `|D| = d` the counts are `Dᶜ.card = 17 − d`, `Iso.card = d − 4`, hub path-incidence total `6`,
iso-incidence total `3·(d − 4)`, and hub-internal total `70 − 6·d` (`16` at `d = 9`, `10` at
`d = 10`).  All counts are derived from `hIsoprop` (twins have no degree-`3` neighbour) without the
`Iso = D.filter …` definitional hypothesis used by the `|D| = 8` version.
-/

namespace ACMax

open scoped Classical

namespace N19

/-- **Generalised residual structural counts (`n = 19`, `P₄` cherry).**  From the path/`Iso`
description of the degree-`3` set `D` (`|D| = d`), the cherry incidence data, and the handshake
edge count, derive the hub count `17 − d`, the twin count `d − 4`, the per-vertex path/iso/internal
hub-incidence totals (`6`, `3·(d − 4)`, `70 − 6·d`), and the per-hub degree split. -/
theorem cherry_p4_hub_struct_nineteen (G : SimpleGraph (Fin 19))
    (hm : G.edgeFinset.card = 34)
    (L₁ c₁ c₂ L₂ : Fin 19) (D Iso : Finset (Fin 19))
    (hT : ¬∃ x y z : Fin 19, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    (hmemD : ∀ v : Fin 19, v ∈ D ↔ G.degree v = 3)
    (hIsoprop : ∀ v ∈ Iso, G.degree v = 3 ∧ (∀ w : Fin 19, G.Adj v w → G.degree w ≠ 3))
    (hisochar : ∀ w : Fin 19, w ∈ D → w ≠ L₁ → w ≠ c₁ → w ≠ c₂ → w ≠ L₂ → w ∈ Iso)
    (hL1deg : G.degree L₁ = 3) (hc1deg : G.degree c₁ = 3)
    (hc2deg : G.degree c₂ = 3) (hL2deg : G.degree L₂ = 3)
    (hac1L1 : G.Adj c₁ L₁) (hc12 : G.Adj c₁ c₂) (hac2L2 : G.Adj c₂ L₂)
    (hL1nc2 : L₁ ≠ c₂) (hL2nc1 : L₂ ≠ c₁)
    (hNc1D : G.neighborFinset c₁ ∩ D = {c₂, L₁}) (hNc2D : G.neighborFinset c₂ ∩ D = {c₁, L₂})
    (hin1 : (G.neighborFinset c₁ ∩ D).card = 2) (hin2 : (G.neighborFinset c₂ ∩ D).card = 2)
    (hs6 : ∑ v ∈ D, (G.neighborFinset v ∩ D).card = 6) :
    Dᶜ.card = 19 - D.card ∧ Iso.card = D.card - 4 ∧
      (G.neighborFinset c₁ ∩ Dᶜ).card = 1 ∧ (G.neighborFinset c₂ ∩ Dᶜ).card = 1 ∧
      (G.neighborFinset L₁ ∩ Dᶜ).card = 2 ∧ (G.neighborFinset L₂ ∩ Dᶜ).card = 2 ∧
      (∑ g ∈ Dᶜ, (G.neighborFinset g ∩ ({L₁, c₁, c₂, L₂} : Finset (Fin 19))).card = 6) ∧
      (∑ g ∈ Dᶜ, (G.neighborFinset g ∩ Iso).card = 3 * (D.card - 4)) ∧
      (∑ g ∈ Dᶜ, (G.neighborFinset g ∩ Dᶜ).card = 74 - 6 * D.card) ∧
      (∀ g : Fin 19, g ∈ Dᶜ →
        (G.neighborFinset g ∩ ({L₁, c₁, c₂, L₂} : Finset (Fin 19))).card
          + (G.neighborFinset g ∩ Iso).card + (G.neighborFinset g ∩ Dᶜ).card = G.degree g) := by
  classical
  set P : Finset (Fin 19) := {L₁, c₁, c₂, L₂} with hP
  -- Neighbour split into `D`-part and `Dᶜ`-part.
  have hsplit : ∀ v : Fin 19,
      (G.neighborFinset v ∩ D).card + (G.neighborFinset v ∩ Dᶜ).card = G.degree v := by
    intro v
    have hdisj : Disjoint (G.neighborFinset v ∩ D) (G.neighborFinset v ∩ Dᶜ) :=
      Finset.disjoint_left.mpr (fun a ha ha' =>
        (Finset.mem_compl.mp (Finset.mem_inter.mp ha').2) (Finset.mem_inter.mp ha).2)
    have hun : (G.neighborFinset v ∩ D) ∪ (G.neighborFinset v ∩ Dᶜ) = G.neighborFinset v := by
      rw [← Finset.inter_union_distrib_left, Finset.union_compl, Finset.inter_univ]
    rw [← Finset.card_union_of_disjoint hdisj, hun, G.card_neighborFinset_eq_degree]
  -- Path vertices live in `D`.
  have hL1D : L₁ ∈ D := (hmemD L₁).mpr hL1deg
  have hc1D : c₁ ∈ D := (hmemD c₁).mpr hc1deg
  have hc2D : c₂ ∈ D := (hmemD c₂).mpr hc2deg
  have hL2D : L₂ ∈ D := (hmemD L₂).mpr hL2deg
  -- Distinctness among path vertices.
  have hL1c1 : L₁ ≠ c₁ := (G.ne_of_adj hac1L1).symm
  have hc1c2 : c₁ ≠ c₂ := G.ne_of_adj hc12
  have hc2L2 : c₂ ≠ L₂ := G.ne_of_adj hac2L2
  have hL1L2 : L₁ ≠ L₂ := by
    intro he
    exact hT ⟨c₁, c₂, L₁, hc1c2, he.symm ▸ hc2L2, hL1c1.symm, hc12,
      he.symm ▸ hac2L2, hac1L1, by omega⟩
  -- `Iso ⊆ D`, and each twin has no `D`-neighbour, hence three hub-neighbours.
  have hIsoD : Iso ⊆ D := fun v hv => (hmemD v).mpr (hIsoprop v hv).1
  have hisoND : ∀ t : Fin 19, t ∈ Iso → (G.neighborFinset t ∩ D).card = 0 := by
    intro t ht
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro a ha
    rw [Finset.mem_inter, G.mem_neighborFinset] at ha
    exact (hIsoprop t ht).2 a ha.1 ((hmemD a).mp ha.2)
  have hisohub : ∀ t : Fin 19, t ∈ Iso → (G.neighborFinset t ∩ Dᶜ).card = 3 := by
    intro t ht
    have := hsplit t
    rw [hisoND t ht, (hIsoprop t ht).1] at this
    omega
  -- Path / Iso partition of `D`.
  have hPD : P ⊆ D := by
    intro x hx; rw [hP] at hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  have hPnIso : Disjoint P Iso := by
    rw [Finset.disjoint_left]
    intro x hxP hxIso
    have hx0 := hisoND x hxIso
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem] at hx0
    rw [hP] at hxP
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxP
    rcases hxP with rfl | rfl | rfl | rfl
    · exact hx0 c₁ (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hac1L1.symm, hc1D⟩)
    · exact hx0 c₂ (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hc12, hc2D⟩)
    · exact hx0 c₁ (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hc12.symm, hc1D⟩)
    · exact hx0 c₂ (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hac2L2.symm, hc2D⟩)
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
  have hDeq : D = P ∪ Iso := Finset.Subset.antisymm hcover (Finset.union_subset hPD hIsoD)
  have hPcard : P.card = 4 := by
    rw [hP, Finset.card_insert_of_notMem (by simp [hL1c1, hL1nc2, hL1L2]),
      Finset.card_insert_of_notMem (by simp [hc1c2, Ne.symm hL2nc1]),
      Finset.card_insert_of_notMem (by simp [hc2L2]), Finset.card_singleton]
  have hIsocard : Iso.card = D.card - 4 := by
    have hcardU : (P ∪ Iso).card = P.card + Iso.card := Finset.card_union_of_disjoint hPnIso
    rw [hDeq, hcardU, hPcard]; omega
  have hDccard : Dᶜ.card = 19 - D.card := by
    have h := Finset.card_add_card_compl D
    simp only [Fintype.card_fin] at h; omega
  -- Leaf `D`-neighbour counts: `(N L₁ ∩ D).card = 1`, `(N L₂ ∩ D).card = 1`.
  have hL1ge : 1 ≤ (G.neighborFinset L₁ ∩ D).card :=
    Finset.card_pos.mpr ⟨c₁, Finset.mem_inter.mpr
      ⟨(G.mem_neighborFinset L₁ c₁).mpr hac1L1.symm, hc1D⟩⟩
  have hL2ge : 1 ≤ (G.neighborFinset L₂ ∩ D).card :=
    Finset.card_pos.mpr ⟨c₂, Finset.mem_inter.mpr
      ⟨(G.mem_neighborFinset L₂ c₂).mpr hac2L2.symm, hc2D⟩⟩
  -- `∑_{D} (N ∩ D) = ∑_{P}(N ∩ D)` because `Iso`-vertices contribute `0`.
  have hsumP_D : ∑ v ∈ P, (G.neighborFinset v ∩ D).card = 6 := by
    have hsumeq : ∑ v ∈ D, (G.neighborFinset v ∩ D).card
        = (∑ v ∈ P, (G.neighborFinset v ∩ D).card)
          + ∑ v ∈ Iso, (G.neighborFinset v ∩ D).card := by
      rw [hDeq, Finset.sum_union hPnIso]
    have hIso0 : ∑ v ∈ Iso, (G.neighborFinset v ∩ D).card = 0 :=
      Finset.sum_eq_zero (fun v hv => hisoND v hv)
    rw [hIso0, add_zero] at hsumeq
    omega
  have hsumP_expand : (G.neighborFinset L₁ ∩ D).card + (G.neighborFinset c₁ ∩ D).card
      + (G.neighborFinset c₂ ∩ D).card + (G.neighborFinset L₂ ∩ D).card = 6 := by
    rw [hP, Finset.sum_insert (by simp [hL1c1, hL1nc2, hL1L2]),
      Finset.sum_insert (by simp [hc1c2, Ne.symm hL2nc1]),
      Finset.sum_insert (by simp [hc2L2]), Finset.sum_singleton] at hsumP_D
    omega
  have hL1D1 : (G.neighborFinset L₁ ∩ D).card = 1 := by omega
  have hL2D1 : (G.neighborFinset L₂ ∩ D).card = 1 := by omega
  -- Hub-incidence counts of the path vertices.
  have hc1hub : (G.neighborFinset c₁ ∩ Dᶜ).card = 1 := by
    have := hsplit c₁; rw [hin1, hc1deg] at this; omega
  have hc2hub : (G.neighborFinset c₂ ∩ Dᶜ).card = 1 := by
    have := hsplit c₂; rw [hin2, hc2deg] at this; omega
  have hL1hub : (G.neighborFinset L₁ ∩ Dᶜ).card = 2 := by
    have := hsplit L₁; rw [hL1D1, hL1deg] at this; omega
  have hL2hub : (G.neighborFinset L₂ ∩ Dᶜ).card = 2 := by
    have := hsplit L₂; rw [hL2D1, hL2deg] at this; omega
  -- Hub path-incidence total `= 6`.
  have hsumPath : ∑ g ∈ Dᶜ, (G.neighborFinset g ∩ P).card = 6 := by
    rw [cross_count_nineteen G Dᶜ P, hP,
      Finset.sum_insert (by simp [hL1c1, hL1nc2, hL1L2]),
      Finset.sum_insert (by simp [hc1c2, Ne.symm hL2nc1]),
      Finset.sum_insert (by simp [hc2L2]), Finset.sum_singleton]
    omega
  -- Hub iso-incidence total `= 3·(|D| − 4)`.
  have hsumIso : ∑ g ∈ Dᶜ, (G.neighborFinset g ∩ Iso).card = 3 * (D.card - 4) := by
    rw [cross_count_nineteen G Dᶜ Iso,
      Finset.sum_congr rfl (fun t ht => hisohub t ht), Finset.sum_const, smul_eq_mul, hIsocard,
      Nat.mul_comm]
  -- Per-hub degree split.
  have hper : ∀ g : Fin 19, g ∈ Dᶜ →
      (G.neighborFinset g ∩ P).card + (G.neighborFinset g ∩ Iso).card
        + (G.neighborFinset g ∩ Dᶜ).card = G.degree g := by
    intro g _
    have hdj : Disjoint (G.neighborFinset g ∩ P) (G.neighborFinset g ∩ Iso) :=
      Finset.disjoint_left.mpr (fun a ha ha' =>
        (Finset.disjoint_left.mp hPnIso) (Finset.mem_inter.mp ha).2 (Finset.mem_inter.mp ha').2)
    have hPI : (G.neighborFinset g ∩ P).card + (G.neighborFinset g ∩ Iso).card
        = (G.neighborFinset g ∩ D).card := by
      rw [← Finset.card_union_of_disjoint hdj, ← Finset.inter_union_distrib_left, ← hDeq]
    have := hsplit g
    omega
  -- Hub-internal total via handshake `∑ deg = 64`.
  have hsumInternal : ∑ g ∈ Dᶜ, (G.neighborFinset g ∩ Dᶜ).card = 74 - 6 * D.card := by
    have hsum60 : ∑ v : Fin 19, G.degree v = 68 := by
      rw [SimpleGraph.sum_degrees_eq_twice_card_edges, hm]
    have hsumDt : ∑ v ∈ D, G.degree v = 3 * D.card := by
      rw [Finset.sum_congr rfl (fun v hv => (hmemD v).mp hv), Finset.sum_const, smul_eq_mul,
        mul_comm]
    have hsumsplit : ∑ v ∈ D, G.degree v + ∑ v ∈ Dᶜ, G.degree v = 68 := by
      rw [Finset.sum_add_sum_compl]; exact hsum60
    have hcross : ∑ v ∈ D, (G.neighborFinset v ∩ Dᶜ).card
        = ∑ w ∈ Dᶜ, (G.neighborFinset w ∩ D).card := cross_count_nineteen G D Dᶜ
    have hcongD : ∑ v ∈ D,
        ((G.neighborFinset v ∩ D).card + (G.neighborFinset v ∩ Dᶜ).card)
        = ∑ v ∈ D, G.degree v := Finset.sum_congr rfl (fun v _ => hsplit v)
    rw [Finset.sum_add_distrib, hs6, hsumDt] at hcongD
    have hcongDc : ∑ w ∈ Dᶜ,
        ((G.neighborFinset w ∩ D).card + (G.neighborFinset w ∩ Dᶜ).card)
        = ∑ w ∈ Dᶜ, G.degree w := Finset.sum_congr rfl (fun w _ => hsplit w)
    rw [Finset.sum_add_distrib, ← hcross] at hcongDc
    omega
  exact ⟨hDccard, hIsocard, hc1hub, hc2hub, hL1hub, hL2hub, hsumPath, hsumIso, hsumInternal, hper⟩

end N19

end ACMax
