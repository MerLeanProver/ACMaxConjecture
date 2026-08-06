import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.Certificates
import ACMaxConjecture.SmallCases.N17.Core
import ACMaxConjecture.SmallCases.N17.HubTriangleStruct

/-!
# Helper facts for the `n = 17`, `P₄`-cherry `|D| ∈ {9, 10}` hub-triangle core

This file collects the per-hub helper lemmas used by the `|D| ∈ {9, 10}` analog of
`iso_rich_force_seventeen` (the `|FF|`-dispatch core of the `|D| = 8` corner).  Because the hubs
here are not uniformly degree `4` (one degree-`5` hub for `|D| = 9`, two degree-`5` or one
degree-`6` for `|D| = 10`), the `|D| = 8` ingredients are restated with **per-hub** degree
hypotheses:

* `cherry_p4_W_facts_seventeen` — `(W)`: a degree-`≤ 5` cherry-avoiding hub has `≤ 1` iso-twin
  (from `¬TwoTwinConfig`).
* `avoider_internal_ge_two_pt`, `fully_free_internal_ge_three_pt` — the internal-degree lower
  bounds with `4 ≤ deg g` (rather than `deg g = 4`).
* `avoiders_ge_gen` — the generic avoider count `Dᶜ.card − 4`.
* `ff_internal_edge_lb_gen` — the in-`FF` edge-mass bound with a parametric internal total.
* `hub_deg_upper_pt`, `hub_deg3_upper` — degree-sum routing bounds from the hub degree total.
-/

namespace ACMax

open scoped Classical

namespace N17

/-- **Generic avoider count.**  If `a, b, c` together have `≤ 4` hub-neighbours, then at least
`Dᶜ.card − 4` hubs avoid all of `a, b, c`. -/
theorem avoiders_ge_gen (G : SimpleGraph (Fin 17)) (D : Finset (Fin 17)) (a b c : Fin 17)
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
theorem avoider_internal_ge_two_pt (G : SimpleGraph (Fin 17)) (D Iso : Finset (Fin 17))
    (g allowed : Fin 17) (hdg : 4 ≤ G.degree g) (hIso1 : (G.neighborFinset g ∩ Iso).card ≤ 1)
    (hclass : ∀ x : Fin 17, G.Adj g x → x ∈ D → x = allowed ∨ x ∈ Iso) :
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
theorem fully_free_internal_ge_three_pt (G : SimpleGraph (Fin 17)) (D Iso : Finset (Fin 17))
    (g : Fin 17) (hdg : 4 ≤ G.degree g) (hIso1 : (G.neighborFinset g ∩ Iso).card ≤ 1)
    (hclass : ∀ x : Fin 17, G.Adj g x → x ∈ D → x ∈ Iso) :
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
theorem ff_internal_edge_lb_gen (G : SimpleGraph (Fin 17)) (Dc FF : Finset (Fin 17)) (S : ℕ)
    (hFFsub : FF ⊆ Dc)
    (hSum : ∑ w ∈ Dc, (G.neighborFinset w ∩ Dc).card = S) :
    2 * (∑ g ∈ FF, (G.neighborFinset g ∩ Dc).card)
      ≤ (∑ g ∈ FF, (G.neighborFinset g ∩ FF).card) + S := by
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
theorem hub_deg_upper_pt (S : Finset (Fin 17)) (f : Fin 17 → ℕ) (T : ℕ)
    (lb : ∀ g ∈ S, 4 ≤ f g) (hsum : ∑ g ∈ S, f g = T) (g0 : Fin 17) (hg0 : g0 ∈ S) :
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
theorem hub_deg3_upper (S : Finset (Fin 17)) (f : Fin 17 → ℕ) (T : ℕ)
    (lb : ∀ g ∈ S, 4 ≤ f g) (hsum : ∑ g ∈ S, f g = T) (a b c : Fin 17)
    (haS : a ∈ S) (hbS : b ∈ S) (hcS : c ∈ S) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    f a + f b + f c + 4 * (S.card - 3) ≤ T := by
  classical
  have hTsub : ({a, b, c} : Finset (Fin 17)) ⊆ S := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  have hpart : (∑ g ∈ ({a, b, c} : Finset (Fin 17)), f g) + ∑ g ∈ S \ {a, b, c}, f g = T := by
    rw [← hsum, add_comm, Finset.sum_sdiff hTsub]
  have htriple : (∑ g ∈ ({a, b, c} : Finset (Fin 17)), f g) = f a + f b + f c := by
    rw [Finset.sum_insert (by simp [hab, hac]), Finset.sum_insert (by simp [hbc]),
      Finset.sum_singleton, add_assoc]
  have hcard3 : ({a, b, c} : Finset (Fin 17)).card = 3 := by
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
`exists_hub_triangle_config_residual_seventeen`, requiring `G.degree g ≤ 5` directly. -/
theorem cherry_p4_W_facts_seventeen (G : SimpleGraph (Fin 17)) (D Iso : Finset (Fin 17))
    (L₁ c₁ c₂ L₂ : Fin 17)
    (hIsoprop : ∀ v ∈ Iso, G.degree v = 3 ∧ (∀ w : Fin 17, G.Adj v w → G.degree w ≠ 3))
    (hL1deg : G.degree L₁ = 3) (hc1deg : G.degree c₁ = 3)
    (hc2deg : G.degree c₂ = 3) (hL2deg : G.degree L₂ = 3)
    (hac1L1 : G.Adj c₁ L₁) (hc12 : G.Adj c₁ c₂) (hac2L2 : G.Adj c₂ L₂)
    (hL1nc2 : L₁ ≠ c₂) (hL2nc1 : L₂ ≠ c₁)
    (hL1D : L₁ ∈ D) (hc1D : c₁ ∈ D) (hc2D : c₂ ∈ D) (hL2D : L₂ ∈ D)
    (htt : ¬TwoTwinConfig G) :
    ∀ g : Fin 17, g ∈ Dᶜ → G.degree g ≤ 5 →
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

/-- **Budget collapse for `|D| = 9`.**  With `8` hubs, internal-degree total `12`, avoider
internal degree `≥ 2`, fully-free internal degree `≥ 3` and avoider counts `≥ 4`, the avoider
sets coincide: `A1 = A2 = FF`, `|FF| = 4`, and the in-`FF` internal-degree total is exactly
`12`. -/
theorem budget_force_nine (Dc A1 A2 FF : Finset (Fin 17)) (f : Fin 17 → ℕ)
    (hA1sub : A1 ⊆ Dc) (hA2sub : A2 ⊆ Dc) (hFF : FF = A1 ∩ A2)
    (hA1lb : Dc.card - 4 ≤ A1.card) (hA2lb : Dc.card - 4 ≤ A2.card)
    (hA1int : ∀ g ∈ A1, 2 ≤ f g) (hA2int : ∀ g ∈ A2, 2 ≤ f g) (hFFint : ∀ g ∈ FF, 3 ≤ f g)
    (hsum : ∑ g ∈ Dc, f g = 12) (hDc8 : Dc.card = 8) :
    A1.card = 4 ∧ A2.card = 4 ∧ FF.card = 4 ∧ ∑ g ∈ FF, f g = 12 := by
  classical
  have hFFsubA1 : FF ⊆ A1 := by rw [hFF]; exact Finset.inter_subset_left
  have hFFsubA2 : FF ⊆ A2 := by rw [hFF]; exact Finset.inter_subset_right
  have hFFsub : FF ⊆ Dc := hFFsubA1.trans hA1sub
  have hUsub : A1 ∪ A2 ⊆ Dc := Finset.union_subset hA1sub hA2sub
  -- `∑_{A1∪A2} f ≤ 12`.
  have hUle : ∑ g ∈ A1 ∪ A2, f g ≤ 12 := by
    rw [← hsum]; exact Finset.sum_le_sum_of_subset_of_nonneg hUsub (fun _ _ _ => Nat.zero_le _)
  have hFFle : ∑ g ∈ FF, f g ≤ 12 := by
    rw [← hsum]; exact Finset.sum_le_sum_of_subset_of_nonneg hFFsub (fun _ _ _ => Nat.zero_le _)
  -- Decompositions.
  have hdisj : Disjoint A1 (A2 \ A1) := Finset.disjoint_sdiff
  have hunion_eq : A1 ∪ (A2 \ A1) = A1 ∪ A2 := Finset.union_sdiff_self_eq_union
  have hUsplit : ∑ g ∈ A1 ∪ A2, f g = (∑ g ∈ A1, f g) + ∑ g ∈ A2 \ A1, f g := by
    rw [← hunion_eq, Finset.sum_union hdisj]
  have hA1split : (∑ g ∈ A1 \ FF, f g) + ∑ g ∈ FF, f g = ∑ g ∈ A1, f g :=
    Finset.sum_sdiff hFFsubA1
  have hFF_ge : 3 * FF.card ≤ ∑ g ∈ FF, f g := by
    have := Finset.card_nsmul_le_sum FF f 3 hFFint
    simpa [smul_eq_mul, Nat.mul_comm] using this
  have hA1mf_ge : 2 * (A1 \ FF).card ≤ ∑ g ∈ A1 \ FF, f g := by
    have := Finset.card_nsmul_le_sum (A1 \ FF) f 2
      (fun g hg => hA1int g ((Finset.mem_sdiff.mp hg).1))
    simpa [smul_eq_mul, Nat.mul_comm] using this
  have hA2mA1_ge : 2 * (A2 \ A1).card ≤ ∑ g ∈ A2 \ A1, f g := by
    have := Finset.card_nsmul_le_sum (A2 \ A1) f 2
      (fun g hg => hA2int g ((Finset.mem_sdiff.mp hg).1))
    simpa [smul_eq_mul, Nat.mul_comm] using this
  -- Card relations.
  have hA1FFinter : (A1 ∩ FF).card = FF.card := by rw [Finset.inter_eq_right.mpr hFFsubA1]
  have hA1mfcard : (A1 \ FF).card + FF.card = A1.card := by
    rw [← hA1FFinter]; exact Finset.card_sdiff_add_card_inter A1 FF
  have hA2A1FF : (A2 ∩ A1).card = FF.card := by rw [hFF, Finset.inter_comm]
  have hA2mA1card : (A2 \ A1).card + FF.card = A2.card := by
    rw [← hA2A1FF]; exact Finset.card_sdiff_add_card_inter A2 A1
  have hFFleA1 : FF.card ≤ A1.card := Finset.card_le_card hFFsubA1
  have hFFleA2 : FF.card ≤ A2.card := Finset.card_le_card hFFsubA2
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

/-- **Clean-avoider counting contradiction for `|D| = 10`.**  If one avoider set `A` (avoiding the
lone degree-`6` hub `h6`) is wholly degree-`4` (internal degree `≥ 2`, `≥ 3` on the shared part
`FF = A ∩ B`) while the other set `B` is degree-`4` off `h6`, with both `≥ 3` and internal total
`6`, then no consistent assignment exists. -/
theorem ten_avoider_clean_contra (Dc A B FF : Finset (Fin 17)) (f : Fin 17 → ℕ) (h6 : Fin 17)
    (hAsub : A ⊆ Dc) (hBsub : B ⊆ Dc) (hFF : FF = A ∩ B)
    (hAint : ∀ g ∈ A, 2 ≤ f g) (hFFint : ∀ g ∈ FF, 3 ≤ f g)
    (hBint : ∀ g ∈ B, g ≠ h6 → 2 ≤ f g) (_hh6A : h6 ∉ A)
    (hAcard : 3 ≤ A.card) (hBcard : 3 ≤ B.card) (hsum : ∑ g ∈ Dc, f g = 6) : False := by
  classical
  have hFFsubA : FF ⊆ A := by rw [hFF]; exact Finset.inter_subset_left
  have hFFsub : FF ⊆ Dc := hFFsubA.trans hAsub
  have hAsumlb : 2 * A.card + FF.card ≤ ∑ g ∈ A, f g := by
    have hsplit : (∑ g ∈ A \ FF, f g) + ∑ g ∈ FF, f g = ∑ g ∈ A, f g := Finset.sum_sdiff hFFsubA
    have h1 : 2 * (A \ FF).card ≤ ∑ g ∈ A \ FF, f g := by
      have := Finset.card_nsmul_le_sum (A \ FF) f 2
        (fun g hg => hAint g ((Finset.mem_sdiff.mp hg).1))
      simpa [smul_eq_mul, Nat.mul_comm] using this
    have h2 : 3 * FF.card ≤ ∑ g ∈ FF, f g := by
      have := Finset.card_nsmul_le_sum FF f 3 hFFint
      simpa [smul_eq_mul, Nat.mul_comm] using this
    have hc : (A \ FF).card + FF.card = A.card := by
      have := Finset.card_sdiff_add_card_inter A FF
      rwa [Finset.inter_eq_right.mpr hFFsubA] at this
    omega
  have hAsumle : ∑ g ∈ A, f g ≤ 6 := by
    rw [← hsum]; exact Finset.sum_le_sum_of_subset_of_nonneg hAsub (fun _ _ _ => Nat.zero_le _)
  by_cases hFFempty : FF.card = 0
  · -- `FF = ∅`: `∑_A f = 6`, `|A| = 3`, so `∑_{Dc\A} f = 0`, yet `B` has a degree-`4` hub there.
    have hABdisj : Disjoint A B := by
      rw [Finset.disjoint_iff_inter_eq_empty, ← hFF]; exact Finset.card_eq_zero.mp hFFempty
    have hpart : (∑ g ∈ Dc \ A, f g) + ∑ g ∈ A, f g = 6 := by rw [Finset.sum_sdiff hAsub, hsum]
    have hDcAzero : ∑ g ∈ Dc \ A, f g = 0 := by omega
    obtain ⟨g, hgB, hgne⟩ := Finset.exists_mem_ne (by omega : 1 < B.card) h6
    have hgA : g ∉ A := fun hgA => (Finset.disjoint_left.mp hABdisj) hgA hgB
    have hgDcA : g ∈ Dc \ A := Finset.mem_sdiff.mpr ⟨hBsub hgB, hgA⟩
    have hg0 : f g = 0 := (Finset.sum_eq_zero_iff.mp hDcAzero) g hgDcA
    have := hBint g hgB hgne
    omega
  · -- `FF ≠ ∅`: `∑_A f ≥ 2·3 + 1 = 7 > 6`.
    omega

/-- **All-degree-`≤ 5` counting contradiction for `|D| = 10`.**  If both avoider sets have internal
degree `≥ 2` (and `≥ 3` on `FF = A1 ∩ A2`), are `≥ 3` in size, and the internal total is `6`, then
the union is forced to size `3`, so `A1 = A2 = FF` carries `∑_FF f ≥ 9 > 6`. -/
theorem budget_contra_ten (Dc A1 A2 FF : Finset (Fin 17)) (f : Fin 17 → ℕ)
    (hA1sub : A1 ⊆ Dc) (hA2sub : A2 ⊆ Dc) (hFF : FF = A1 ∩ A2)
    (hA1card : 3 ≤ A1.card) (hA2card : 3 ≤ A2.card)
    (hint2 : ∀ g ∈ A1, 2 ≤ f g) (hint2' : ∀ g ∈ A2, 2 ≤ f g) (hFFint : ∀ g ∈ FF, 3 ≤ f g)
    (hsum : ∑ g ∈ Dc, f g = 6) : False := by
  classical
  have hUsub : A1 ∪ A2 ⊆ Dc := Finset.union_subset hA1sub hA2sub
  have hUint : ∀ g ∈ A1 ∪ A2, 2 ≤ f g :=
    fun g hg => (Finset.mem_union.mp hg).elim (hint2 g) (hint2' g)
  have hUlb : 2 * (A1 ∪ A2).card ≤ ∑ g ∈ A1 ∪ A2, f g := by
    have := Finset.card_nsmul_le_sum (A1 ∪ A2) f 2 hUint
    simpa [smul_eq_mul, Nat.mul_comm] using this
  have hUle : ∑ g ∈ A1 ∪ A2, f g ≤ 6 := by
    rw [← hsum]; exact Finset.sum_le_sum_of_subset_of_nonneg hUsub (fun _ _ _ => Nat.zero_le _)
  have hA1leU : A1.card ≤ (A1 ∪ A2).card := Finset.card_le_card Finset.subset_union_left
  have hUcard : (A1 ∪ A2).card = 3 := by omega
  have hA1U : A1 = A1 ∪ A2 :=
    Finset.eq_of_subset_of_card_le Finset.subset_union_left (by omega)
  have hA2U : A2 = A1 ∪ A2 :=
    Finset.eq_of_subset_of_card_le Finset.subset_union_right (by omega)
  have hA1eqA2 : A1 = A2 := hA1U.trans hA2U.symm
  have hFFeq : FF = A1 := by rw [hFF, ← hA1eqA2, Finset.inter_self]
  have hA1c3 : A1.card = 3 := by rw [hA1U, hUcard]
  have hFFlb : 3 * FF.card ≤ ∑ g ∈ FF, f g := by
    have := Finset.card_nsmul_le_sum FF f 3 hFFint
    simpa [smul_eq_mul, Nat.mul_comm] using this
  have hFFle : ∑ g ∈ FF, f g ≤ 6 := by
    rw [← hsum]
    exact Finset.sum_le_sum_of_subset_of_nonneg (hFFeq ▸ hA1sub) (fun _ _ _ => Nat.zero_le _)
  have hFFc3 : FF.card = 3 := by rw [hFFeq, hA1c3]
  omega

end N17

end ACMax
