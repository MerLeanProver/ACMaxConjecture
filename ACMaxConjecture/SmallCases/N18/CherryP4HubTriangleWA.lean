import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.Certificates
import ACMaxConjecture.SmallCases.N18.Core
import ACMaxConjecture.SmallCases.N18.HubTriangleStruct

/-!
# Helper facts for the `n = 17`, `P₄`-cherry `|D| ∈ {9, 10}` hub-triangle core

This file collects the per-hub helper lemmas used by the `|D| ∈ {9, 10}` analog of
`iso_rich_force_eighteen` (the `|FF|`-dispatch core of the `|D| = 8` corner).  Because the hubs
here are not uniformly degree `4` (one degree-`5` hub for `|D| = 9`, two degree-`5` or one
degree-`6` for `|D| = 10`), the `|D| = 8` ingredients are restated with **per-hub** degree
hypotheses:

* `cherry_p4_W_facts_eighteen` — `(W)`: a degree-`≤ 5` cherry-avoiding hub has `≤ 1` iso-twin
  (from `¬TwoTwinConfig`).
* `avoider_internal_ge_two_pt`, `fully_free_internal_ge_three_pt` — the internal-degree lower
  bounds with `4 ≤ deg g` (rather than `deg g = 4`).
* `avoiders_ge_gen` — the generic avoider count `Dᶜ.card − 4`.
* `ff_internal_edge_lb_gen` — the in-`FF` edge-mass bound with a parametric internal total.
* `hub_deg_upper_pt`, `hub_deg3_upper` — degree-sum routing bounds from the hub degree total.
-/

namespace ACMax

open scoped Classical

namespace N18

/-- **Generic avoider count.**  If `a, b, c` together have `≤ 4` hub-neighbours, then at least
`Dᶜ.card − 4` hubs avoid all of `a, b, c`. -/
theorem avoiders_ge_gen (G : SimpleGraph (Fin 18)) (D : Finset (Fin 18)) (a b c : Fin 18)
    (hbound : (G.neighborFinset a ∩ Dᶜ).card + (G.neighborFinset b ∩ Dᶜ).card
      + (G.neighborFinset c ∩ Dᶜ).card ≤ 4) :
    Dᶜ.card - 4 ≤ (Dᶜ.filter (fun g => ¬G.Adj g a ∧ ¬G.Adj g b ∧ ¬G.Adj g c)).card := by
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

/-- **Cherry-avoider internal degree `≥ 2` (per-hub degree).**  Restatement of
`avoider_internal_ge_two` requiring only `4 ≤ G.degree g`. -/
theorem avoider_internal_ge_two_pt (G : SimpleGraph (Fin 18)) (D Iso : Finset (Fin 18))
    (g allowed : Fin 18) (hdg : 4 ≤ G.degree g) (hIso1 : (G.neighborFinset g ∩ Iso).card ≤ 1)
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

/-- **Fully-free internal degree `≥ 3` (per-hub degree).**  Restatement of
`fully_free_internal_ge_three` requiring only `4 ≤ G.degree g`. -/
theorem fully_free_internal_ge_three_pt (G : SimpleGraph (Fin 18)) (D Iso : Finset (Fin 18))
    (g : Fin 18) (hdg : 4 ≤ G.degree g) (hIso1 : (G.neighborFinset g ∩ Iso).card ≤ 1)
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

/-- **In-`FF` edge-mass bound (parametric internal total).**  Generalisation of
`ff_internal_edge_lb` to an arbitrary `Dᶜ`-internal degree total `S`. -/
theorem ff_internal_edge_lb_gen (G : SimpleGraph (Fin 18)) (Dc FF : Finset (Fin 18)) (S : ℕ)
    (hFFsub : FF ⊆ Dc)
    (hSum : ∑ w ∈ Dc, (G.neighborFinset w ∩ Dc).card = S) :
    2 * (∑ g ∈ FF, (G.neighborFinset g ∩ Dc).card)
      ≤ (∑ g ∈ FF, (G.neighborFinset g ∩ FF).card) + S := by
  classical
  have hsplit : ∀ g : Fin 18, (G.neighborFinset g ∩ Dc).card
      = (G.neighborFinset g ∩ FF).card + (G.neighborFinset g ∩ (Dc \ FF)).card := by
    intro g
    rw [← Finset.card_union_of_disjoint, ← Finset.inter_union_distrib_left,
      Finset.union_sdiff_of_subset hFFsub]
    apply Finset.disjoint_left.mpr
    intro a ha ha'
    rw [Finset.mem_inter] at ha ha'
    exact (Finset.mem_sdiff.mp ha'.2).2 ha.2
  have hsdiff : (∑ w ∈ Dc \ FF, (G.neighborFinset w ∩ Dc).card)
      + ∑ g ∈ FF, (G.neighborFinset g ∩ Dc).card = S := by
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

/-- **Single-hub degree upper bound from the hub total.**  If every hub of `S` has degree `≥ 4`
and `∑_S deg = T`, then any one hub has degree `≤ T − 4·(|S| − 1)`. -/
theorem hub_deg_upper_pt (S : Finset (Fin 18)) (f : Fin 18 → ℕ) (T : ℕ)
    (lb : ∀ g ∈ S, 4 ≤ f g) (hsum : ∑ g ∈ S, f g = T) (g0 : Fin 18) (hg0 : g0 ∈ S) :
    f g0 + 4 * (S.card - 1) ≤ T := by
  classical
  have hpart : f g0 + ∑ g ∈ S.erase g0, f g = T := by
    rw [← hsum, Finset.add_sum_erase _ _ hg0]
  have hge : 4 * (S.erase g0).card ≤ ∑ g ∈ S.erase g0, f g := by
    have := Finset.card_nsmul_le_sum (S.erase g0) f 4
      (fun g hg => lb g (Finset.mem_of_mem_erase hg))
    simpa [smul_eq_mul, Nat.mul_comm] using this
  have hcard : (S.erase g0).card = S.card - 1 := Finset.card_erase_of_mem hg0
  omega

/-- **Triple-hub degree upper bound from the hub total.**  If every hub of `S` has degree `≥ 4`
and `∑_S deg = T`, then any three distinct hubs have degree sum `≤ T − 4·(|S| − 3)`. -/
theorem hub_deg3_upper (S : Finset (Fin 18)) (f : Fin 18 → ℕ) (T : ℕ)
    (lb : ∀ g ∈ S, 4 ≤ f g) (hsum : ∑ g ∈ S, f g = T) (a b c : Fin 18)
    (haS : a ∈ S) (hbS : b ∈ S) (hcS : c ∈ S) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    f a + f b + f c + 4 * (S.card - 3) ≤ T := by
  classical
  have hTsub : ({a, b, c} : Finset (Fin 18)) ⊆ S := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  have hpart : (∑ g ∈ ({a, b, c} : Finset (Fin 18)), f g) + ∑ g ∈ S \ {a, b, c}, f g = T := by
    rw [← hsum, add_comm, Finset.sum_sdiff hTsub]
  have htriple : (∑ g ∈ ({a, b, c} : Finset (Fin 18)), f g) = f a + f b + f c := by
    rw [Finset.sum_insert (by simp [hab, hac]), Finset.sum_insert (by simp [hbc]),
      Finset.sum_singleton, add_assoc]
  have hcard3 : ({a, b, c} : Finset (Fin 18)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hab, hac]),
      Finset.card_insert_of_notMem (by simp [hbc]), Finset.card_singleton]
  have hge : 4 * (S \ {a, b, c}).card ≤ ∑ g ∈ S \ {a, b, c}, f g := by
    have := Finset.card_nsmul_le_sum (S \ {a, b, c}) f 4
      (fun g hg => lb g ((Finset.mem_sdiff.mp hg).1))
    simpa [smul_eq_mul, Nat.mul_comm] using this
  have hcardsub : (S \ {a, b, c}).card + 3 = S.card := by
    rw [← hcard3]; exact Finset.card_sdiff_add_card_eq_card hTsub
  omega

/-- **(W) for `|D| ∈ {9, 10}` (per-hub degree).**  A degree-`≤ 5` hub avoiding a cherry has at
most one `M`-isolated-twin neighbour: two such twins plus the hub and the cherry assemble a
`TwoTwinConfig`, contradicting `¬TwoTwinConfig`.  Port of the `hW` block of
`exists_hub_triangle_config_residual_eighteen`, requiring `G.degree g ≤ 5` directly. -/
theorem cherry_p4_W_facts_eighteen (G : SimpleGraph (Fin 18)) (D Iso : Finset (Fin 18))
    (L₁ c₁ c₂ L₂ : Fin 18)
    (hIsoprop : ∀ v ∈ Iso, G.degree v = 3 ∧ (∀ w : Fin 18, G.Adj v w → G.degree w ≠ 3))
    (hL1deg : G.degree L₁ = 3) (hc1deg : G.degree c₁ = 3)
    (hc2deg : G.degree c₂ = 3) (hL2deg : G.degree L₂ = 3)
    (hac1L1 : G.Adj c₁ L₁) (hc12 : G.Adj c₁ c₂) (hac2L2 : G.Adj c₂ L₂)
    (hL1nc2 : L₁ ≠ c₂) (hL2nc1 : L₂ ≠ c₁)
    (hL1D : L₁ ∈ D) (hc1D : c₁ ∈ D) (hc2D : c₂ ∈ D) (hL2D : L₂ ∈ D)
    (htt : ¬TwoTwinConfig G) :
    ∀ g : Fin 18, g ∈ Dᶜ → G.degree g ≤ 5 →
      ((¬G.Adj g L₁ ∧ ¬G.Adj g c₁ ∧ ¬G.Adj g c₂) ∨
        (¬G.Adj g c₁ ∧ ¬G.Adj g c₂ ∧ ¬G.Adj g L₂)) →
      (G.neighborFinset g ∩ Iso).card ≤ 1 := by
  intro g hgDc hgdeg5 havoid
  by_contra hge2
  rw [not_le] at hge2
  obtain ⟨s1, hs1m, s2, hs2m, hs12⟩ := Finset.one_lt_card.mp hge2
  rw [Finset.mem_inter, G.mem_neighborFinset] at hs1m hs2m
  obtain ⟨hgs1, hs1Iso⟩ := hs1m
  obtain ⟨hgs2, hs2Iso⟩ := hs2m
  obtain ⟨hs1deg, hs1iso⟩ := hIsoprop s1 hs1Iso
  obtain ⟨hs2deg, hs2iso⟩ := hIsoprop s2 hs2Iso
  apply htt
  rcases havoid with ⟨hgL1, hgc1, hgc2⟩ | ⟨hgc1, hgc2, hgL2⟩
  · exact ⟨s1, s2, g, L₁, c₁, c₂, hs1deg, hs2deg, hgdeg5,
      hL1deg, hc1deg, hc2deg, hgs1.symm, hgs2.symm, hac1L1.symm, hc12,
      (fun ha => hs1iso L₁ ha hL1deg), (fun ha => hs1iso c₁ ha hc1deg),
      (fun ha => hs1iso c₂ ha hc2deg),
      (fun ha => hs2iso L₁ ha hL1deg), (fun ha => hs2iso c₁ ha hc1deg),
      (fun ha => hs2iso c₂ ha hc2deg),
      hgL1, hgc1, hgc2, hs12,
      (by rintro rfl; exact hs1iso c₁ hac1L1.symm hc1deg),
      (by rintro rfl; exact hs1iso c₂ hc12 hc2deg),
      (by rintro rfl; exact hs1iso c₁ hc12.symm hc1deg),
      (by rintro rfl; exact hs2iso c₁ hac1L1.symm hc1deg),
      (by rintro rfl; exact hs2iso c₂ hc12 hc2deg),
      (by rintro rfl; exact hs2iso c₁ hc12.symm hc1deg),
      (by rintro rfl; exact (Finset.mem_compl.mp hgDc) hL1D),
      (by rintro rfl; exact (Finset.mem_compl.mp hgDc) hc1D),
      (by rintro rfl; exact (Finset.mem_compl.mp hgDc) hc2D),
      hac1L1.symm.ne, hc12.ne, hL1nc2⟩
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

end N18

end ACMax
