import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N17.Core
import ACMaxConjecture.SmallCases.Certificates
import ACMaxConjecture.SmallCases.N17.HubTriangleStruct
import ACMaxConjecture.SmallCases.N17.HubTriangleCherryC4
import ACMaxConjecture.SmallCases.N17.HubTriangleCherryC4TwoHub

/-!
# Hub-triangle existence for the `n = 17`, `e(M) = 2`, single-`P₃`-cherry residual corner

This file isolates the hub-triangle existence obligation in the `e(M) = 2`, `|D| = 8`
(`|Hub| = 9`, all-degree-`4`) corner where the residual `M` is a **single `P₃` cherry** `x–y–z`
(`y` the middle, in-`M` degree `2`; `x, z` the endpoints, in-`M` degree `1`).  It is the
single-cherry analogue of `TwinCert17HubTriangle` (`e(M) = 3`, `P₄`, two cherries), and is the
`n = 17` port of `TwinCert16HubTriangleCherry`.

## The residual configuration
* `D` = the degree-`3` vertices, `|D| = 8`; `Dᶜ` = the **nine** hubs, all of degree `4` (`hdeg4`).
* `M = P₃` cherry `x–y–z` (`hNyD : N(y) ∩ D = {x, z}`, `haxy`, `hayz`), plus `|Iso| = 5`
  `M`-isolated degree-`3` twins (`Iso`).
* `e(Hub) = 8` hub-hub edges (`∑_{Dᶜ} int = 16`, from the per-hub split
  `path(g) + iso(g) + int(g) = 4` over nine hubs: `4·9 − 5 − 15 = 16`).

## The target
`HubTriangleConfig G`: three pairwise-adjacent hubs avoiding the cherry `{x, y, z}`; their degree
sum is `12 ≤ 13` automatically.  The cherry meets `≤ 2 + 1 + 2 = 5` hubs, so `≥ 4` hubs avoid it;
each avoider is fully free (`int ≥ 3`).

## `n = 17` delta (the triangle-extraction core)
For `n = 16` the budget `∑ int = 12` pinned the avoider set to `|A| ≤ 4` and a leak count forced
it *complete*, giving the triangle immediately.  For `n = 17` the looser budget `∑ int = 16`
admits `|A| ∈ {4, 5}`: the `|A| = 5` sub-case still forces a triangle by Mantel
(`e(A) ≥ 7 > ⌊25/4⌋ = 6`), but the `|A| = 4` sub-case admits a triangle-free `C₄` of avoiders by
pure counting (`e(A) ≥ 4 = ⌊16/4⌋`, exactly the Mantel boundary), so the clean clique-forcing of
`n = 16` does **not** port.  The `|A| = 5` triangle and the `|A| = 4` Mantel bound are supplied by
`mantel_five`/`mantel_quad_le` (`TwinCert17HubTriangleCherryC4`); the `|A| = 4` rigidity (each
avoider `int = 3` with a single private twin) splits on whether two avoiders share a twin: a shared
twin assembles a `SingleVertexConfig` (contradicting `¬SingleVertexConfig`), while four distinct
twins assemble a `TwoHubConfig` (contradicting `¬TwoHubConfig`) via
`cherry_C4_distinct_twin_twoHub` (`TwinCert17HubTriangleCherryC4TwoHub`).
-/

namespace ACMax

open scoped Classical

namespace N17

/-- **Cherry / Iso partition of `D`.**  The three cherry vertices and the `M`-isolated twins
partition `D`: `{x, y, z} ∪ Iso = D` and the two parts are disjoint. -/
theorem cherry_partition (G : SimpleGraph (Fin 17)) (D Iso : Finset (Fin 17)) (x y z : Fin 17)
    (hIsodef : Iso = D.filter (fun v => (G.neighborFinset v ∩ D).card = 0))
    (hisochar : ∀ w : Fin 17, w ∈ D → w ≠ x → w ≠ y → w ≠ z → w ∈ Iso)
    (hxD : x ∈ D) (hyD : y ∈ D) (hzD : z ∈ D)
    (haxy : G.Adj x y) (hayz : G.Adj y z) :
    ({x, y, z} : Finset (Fin 17)) ∪ Iso = D ∧ Disjoint ({x, y, z} : Finset (Fin 17)) Iso := by
  classical
  set P : Finset (Fin 17) := {x, y, z} with hP
  have hIsoD : Iso ⊆ D := by rw [hIsodef]; exact Finset.filter_subset _ _
  have hPD : P ⊆ D := by
    intro v hv; rw [hP] at hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl <;> assumption
  have hPnIso : Disjoint P Iso := by
    rw [Finset.disjoint_left]
    intro v hvP hvIso
    rw [hIsodef, Finset.mem_filter] at hvIso
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem] at hvIso
    rw [hP] at hvP
    simp only [Finset.mem_insert, Finset.mem_singleton] at hvP
    rcases hvP with rfl | rfl | rfl
    · exact hvIso.2 y (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr haxy, hyD⟩)
    · exact hvIso.2 x (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr haxy.symm, hxD⟩)
    · exact hvIso.2 y (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hayz.symm, hyD⟩)
  have hcover : D ⊆ P ∪ Iso := by
    intro v hvD
    by_cases h1 : v = x
    · subst h1; exact Finset.mem_union_left _ (by rw [hP]; simp)
    by_cases h2 : v = y
    · subst h2; exact Finset.mem_union_left _ (by rw [hP]; simp)
    by_cases h3 : v = z
    · subst h3; exact Finset.mem_union_left _ (by rw [hP]; simp)
    · exact Finset.mem_union_right _ (hisochar v hvD h1 h2 h3)
  exact ⟨Finset.Subset.antisymm (Finset.union_subset hPD hIsoD) hcover, hPnIso⟩

/-- **Cherry hub-incidence counts.**  The middle vertex `y` (in-`M` degree `2`) has one
hub-neighbour, the endpoints `x, z` (in-`M` degree `1`) have two each. -/
theorem cherry_leaf_card (G : SimpleGraph (Fin 17)) (D : Finset (Fin 17)) (x y z : Fin 17)
    (hcov : ∀ p q : Fin 17, p ∈ D → q ∈ D → G.Adj p q → p = y ∨ q = y)
    (hNyD : G.neighborFinset y ∩ D = {x, z})
    (hxD : x ∈ D) (hyD : y ∈ D) (hzD : z ∈ D)
    (haxy : G.Adj x y) (hayz : G.Adj y z)
    (hxy : x ≠ y) (hzy : z ≠ y) (hxz : x ≠ z)
    (hxdeg : G.degree x = 3) (hydeg : G.degree y = 3) (hzdeg : G.degree z = 3) :
    (G.neighborFinset x ∩ Dᶜ).card = 2 ∧ (G.neighborFinset y ∩ Dᶜ).card = 1 ∧
      (G.neighborFinset z ∩ Dᶜ).card = 2 := by
  classical
  have hNx : G.neighborFinset x ∩ D = {y} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr haxy, hyD⟩, ?_⟩
    intro a ha
    rw [Finset.mem_inter, G.mem_neighborFinset] at ha
    obtain ⟨hadj, haD⟩ := ha
    rcases hcov x a hxD haD hadj with h | h
    · exact absurd h hxy
    · exact h
  have hNz : G.neighborFinset z ∩ D = {y} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hayz.symm, hyD⟩, ?_⟩
    intro a ha
    rw [Finset.mem_inter, G.mem_neighborFinset] at ha
    obtain ⟨hadj, haD⟩ := ha
    rcases hcov z a hzD haD hadj with h | h
    · exact absurd h hzy
    · exact h
  have hcardx : (G.neighborFinset x ∩ D).card = 1 := by rw [hNx, Finset.card_singleton]
  have hcardz : (G.neighborFinset z ∩ D).card = 1 := by rw [hNz, Finset.card_singleton]
  have hcardy : (G.neighborFinset y ∩ D).card = 2 := by
    rw [hNyD, Finset.card_insert_of_notMem (by simp [hxz]), Finset.card_singleton]
  have sx := nbr_split_DC G D x
  have sy := nbr_split_DC G D y
  have sz := nbr_split_DC G D z
  refine ⟨?_, ?_, ?_⟩ <;> omega

/-- **Cherry residual incidence sums.**  Over the nine hubs the cherry-, iso- and hub-internal
incidences total `5`, `15`, `16` respectively, and per hub the three split the degree `4`. -/
theorem cherry_residual_sums (G : SimpleGraph (Fin 17)) (D Iso : Finset (Fin 17)) (x y z : Fin 17)
    (hIsodef : Iso = D.filter (fun v => (G.neighborFinset v ∩ D).card = 0))
    (hIsoprop : ∀ v ∈ Iso, G.degree v = 3 ∧ (∀ w : Fin 17, G.Adj v w → G.degree w ≠ 3))
    (hisochar : ∀ w : Fin 17, w ∈ D → w ≠ x → w ≠ y → w ≠ z → w ∈ Iso)
    (hxD : x ∈ D) (hyD : y ∈ D) (hzD : z ∈ D)
    (haxy : G.Adj x y) (hayz : G.Adj y z)
    (hxy : x ≠ y) (hzy : z ≠ y) (hxz : x ≠ z)
    (hdeg4 : ∀ w : Fin 17, w ∈ Dᶜ → G.degree w = 4)
    (hcx : (G.neighborFinset x ∩ Dᶜ).card = 2) (hcy : (G.neighborFinset y ∩ Dᶜ).card = 1)
    (hcz : (G.neighborFinset z ∩ Dᶜ).card = 2) (hIso5 : Iso.card = 5) :
    (∑ g ∈ Dᶜ, (G.neighborFinset g ∩ ({x, y, z} : Finset (Fin 17))).card = 5) ∧
      (∑ g ∈ Dᶜ, (G.neighborFinset g ∩ Iso).card = 15) ∧
      (∀ g ∈ Dᶜ, (G.neighborFinset g ∩ ({x, y, z} : Finset (Fin 17))).card
        + (G.neighborFinset g ∩ Iso).card + (G.neighborFinset g ∩ Dᶜ).card = 4) := by
  classical
  set P : Finset (Fin 17) := {x, y, z} with hP
  have hsum_path : ∑ g ∈ Dᶜ, (G.neighborFinset g ∩ P).card = 5 := by
    rw [cross_count G Dᶜ P, hP, Finset.sum_insert (by simp [hxy, hxz]),
      Finset.sum_insert (by simp [Ne.symm hzy]), Finset.sum_singleton]
    omega
  have hsum_iso : ∑ g ∈ Dᶜ, (G.neighborFinset g ∩ Iso).card = 15 := by
    rw [cross_count G Dᶜ Iso]
    have heach : ∀ t ∈ Iso, (G.neighborFinset t ∩ Dᶜ).card = 3 := by
      intro t ht
      exact (iso_three_hub_nbrs G D Iso hIsodef hIsoprop t ht).2
    rw [Finset.sum_congr rfl heach, Finset.sum_const, smul_eq_mul, hIso5]
  obtain ⟨hDeq, hdisj⟩ :=
    cherry_partition G D Iso x y z hIsodef hisochar hxD hyD hzD haxy hayz
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

/-- **At least four cherry-avoiding hubs.**  The cherry `{x, y, z}` collects only
`2 + 1 + 2 = 5` hub-incidences, so `≥ 4` of the nine hubs avoid all three vertices. -/
theorem cherry_avoiders_ge_four (G : SimpleGraph (Fin 17)) (D : Finset (Fin 17)) (x y z : Fin 17)
    (hDc9 : Dᶜ.card = 9)
    (hcx : (G.neighborFinset x ∩ Dᶜ).card = 2) (hcy : (G.neighborFinset y ∩ Dᶜ).card = 1)
    (hcz : (G.neighborFinset z ∩ Dᶜ).card = 2) :
    4 ≤ (Dᶜ.filter (fun g => ¬G.Adj g x ∧ ¬G.Adj g y ∧ ¬G.Adj g z)).card := by
  classical
  set Av := Dᶜ.filter (fun g => ¬G.Adj g x ∧ ¬G.Adj g y ∧ ¬G.Adj g z) with hAv
  have hsub : Dᶜ ⊆ Av ∪ ((G.neighborFinset x ∩ Dᶜ) ∪
      ((G.neighborFinset y ∩ Dᶜ) ∪ (G.neighborFinset z ∩ Dᶜ))) := by
    intro g hg
    by_cases ha : G.Adj g x
    · exact Finset.mem_union_right _ (Finset.mem_union_left _
        (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr ha.symm, hg⟩))
    by_cases hb : G.Adj g y
    · exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_union_left _
        (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hb.symm, hg⟩)))
    by_cases hc : G.Adj g z
    · exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_union_right _
        (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hc.symm, hg⟩)))
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hg, ha, hb, hc⟩)
  have hcardle := Finset.card_le_card hsub
  have h1 := Finset.card_union_le Av ((G.neighborFinset x ∩ Dᶜ) ∪
      ((G.neighborFinset y ∩ Dᶜ) ∪ (G.neighborFinset z ∩ Dᶜ)))
  have h2 := Finset.card_union_le (G.neighborFinset x ∩ Dᶜ)
      ((G.neighborFinset y ∩ Dᶜ) ∪ (G.neighborFinset z ∩ Dᶜ))
  have h3 := Finset.card_union_le (G.neighborFinset y ∩ Dᶜ) (G.neighborFinset z ∩ Dᶜ)
  omega

/-- **Hub-triangle existence in the `n = 17`, `|D| = 8`, `e(M) = 2`, single-`P₃`-cherry corner.**
Under the residual hypotheses (nine degree-`4` hubs, `8` hub-hub edges, `M = P₃` cherry `x–y–z`
with five `M`-isolated twins, and the falsity of `SingleVertexConfig`/`TwoTwinConfig`/
`TwoHubConfig`), the graph contains three pairwise-adjacent hubs avoiding the cherry, packaged as
`HubTriangleConfig G`.  Every avoider is fully free (`int ≥ 3`); the triangle is dispatched on
`|A| ∈ {4, 5}` via `mantel_five`/`mantel_quad_le` and the residual-config exclusions, with the
`|A| = 4` distinct-twin `TwoHubConfig` assembly delegated to `cherry_C4_distinct_twin_twoHub`. -/
theorem exists_hub_triangle_config_cherry_residual_seventeen (G : SimpleGraph (Fin 17))
    (D Iso : Finset (Fin 17)) (x y z : Fin 17)
    (hmemD : ∀ v : Fin 17, v ∈ D ↔ G.degree v = 3)
    (hIsodef : Iso = D.filter (fun v => (G.neighborFinset v ∩ D).card = 0))
    (hIsoprop : ∀ v ∈ Iso, G.degree v = 3 ∧ (∀ w : Fin 17, G.Adj v w → G.degree w ≠ 3))
    (hisochar : ∀ w : Fin 17, w ∈ D → w ≠ x → w ≠ y → w ≠ z → w ∈ Iso)
    (hcov : ∀ p q : Fin 17, p ∈ D → q ∈ D → G.Adj p q → p = y ∨ q = y)
    (hNyD : G.neighborFinset y ∩ D = {x, z})
    (hxdeg : G.degree x = 3) (hydeg : G.degree y = 3) (hzdeg : G.degree z = 3)
    (haxy : G.Adj x y) (hayz : G.Adj y z) (hnxz : ¬G.Adj x z) (hxz : x ≠ z)
    (hdeg4 : ∀ w : Fin 17, w ∈ Dᶜ → G.degree w = 4)
    (hD8 : D.card = 8)
    (hC4 : ¬∃ a b c d : Fin 17, ({a, b, c, d} : Finset (Fin 17)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (hsv : ¬SingleVertexConfig G) (htt : ¬TwoTwinConfig G) (hth : ¬TwoHubConfig G) :
    HubTriangleConfig G := by
  classical
  have hxD : x ∈ D := (hmemD x).mpr hxdeg
  have hyD : y ∈ D := (hmemD y).mpr hydeg
  have hzD : z ∈ D := (hmemD z).mpr hzdeg
  have hxy : x ≠ y := haxy.ne
  have hzy : z ≠ y := hayz.ne'
  -- **(W) [from `¬TwoTwinConfig`].**  Any cherry-avoiding hub has `≤ 1` `M`-isolated-twin
  -- neighbour: two such twins plus the hub and the cherry assemble a `TwoTwinConfig`.
  have hW : ∀ g : Fin 17, g ∈ Dᶜ → (¬G.Adj g x ∧ ¬G.Adj g y ∧ ¬G.Adj g z) →
      (G.neighborFinset g ∩ Iso).card ≤ 1 := by
    intro g hgDc havoid
    obtain ⟨hgx, hgy, hgz⟩ := havoid
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
    exact ⟨s1, s2, g, x, y, z, hs1deg, hs2deg, hgdeg5, hxdeg, hydeg, hzdeg,
      hgs1.symm, hgs2.symm, haxy, hayz,
      (fun ha => hs1iso x ha hxdeg), (fun ha => hs1iso y ha hydeg),
      (fun ha => hs1iso z ha hzdeg),
      (fun ha => hs2iso x ha hxdeg), (fun ha => hs2iso y ha hydeg),
      (fun ha => hs2iso z ha hzdeg),
      hgx, hgy, hgz, hs12,
      (by rintro rfl; exact hs1iso y haxy hydeg),
      (by rintro rfl; exact hs1iso x haxy.symm hxdeg),
      (by rintro rfl; exact hs1iso y hayz.symm hydeg),
      (by rintro rfl; exact hs2iso y haxy hydeg),
      (by rintro rfl; exact hs2iso x haxy.symm hxdeg),
      (by rintro rfl; exact hs2iso y hayz.symm hydeg),
      (by rintro rfl; exact (Finset.mem_compl.mp hgDc) hxD),
      (by rintro rfl; exact (Finset.mem_compl.mp hgDc) hyD),
      (by rintro rfl; exact (Finset.mem_compl.mp hgDc) hzD),
      haxy.ne, hayz.ne, hxz⟩
  -- Structural counts: nine hubs, five `M`-isolated twins.
  obtain ⟨hDeq, hdisj⟩ :=
    cherry_partition G D Iso x y z hIsodef hisochar hxD hyD hzD haxy hayz
  have hDc9 : Dᶜ.card = 9 := by rw [Finset.card_compl, Fintype.card_fin, hD8]
  have hIso5 : Iso.card = 5 := by
    have hPcard : ({x, y, z} : Finset (Fin 17)).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [hxy, hxz]),
        Finset.card_insert_of_notMem (by simp [Ne.symm hzy]), Finset.card_singleton]
    have hcardU := Finset.card_union_of_disjoint hdisj
    rw [hDeq, hPcard, hD8] at hcardU
    omega
  -- Cherry hub-incidence counts and the residual sums (`∑ int = 16`).
  obtain ⟨hcx, hcy, hcz⟩ :=
    cherry_leaf_card G D x y z hcov hNyD hxD hyD hzD haxy hayz hxy hzy hxz hxdeg hydeg hzdeg
  obtain ⟨hsumP, hsumI, hper⟩ :=
    cherry_residual_sums G D Iso x y z hIsodef hIsoprop hisochar hxD hyD hzD haxy hayz
      hxy hzy hxz hdeg4 hcx hcy hcz hIso5
  have hSum16 : ∑ w ∈ Dᶜ, (G.neighborFinset w ∩ Dᶜ).card = 16 := by
    have htot : ∑ g ∈ Dᶜ, ((G.neighborFinset g ∩ ({x, y, z} : Finset (Fin 17))).card
        + (G.neighborFinset g ∩ Iso).card + (G.neighborFinset g ∩ Dᶜ).card)
        = ∑ _g ∈ Dᶜ, 4 := Finset.sum_congr rfl hper
    rw [Finset.sum_const, smul_eq_mul, hDc9, Finset.sum_add_distrib, Finset.sum_add_distrib,
      hsumP, hsumI] at htot
    omega
  -- The cherry-avoider set, with `≥ 4` members each of internal degree `≥ 3`.
  set A := Dᶜ.filter (fun g => ¬G.Adj g x ∧ ¬G.Adj g y ∧ ¬G.Adj g z) with hAdef
  have hAsub : A ⊆ Dᶜ := Finset.filter_subset _ _
  have hA4 : 4 ≤ A.card := by
    rw [hAdef]; exact cherry_avoiders_ge_four G D x y z hDc9 hcx hcy hcz
  have hclassP : ∀ v : Fin 17, v ∈ D → v = x ∨ v = y ∨ v = z ∨ v ∈ Iso := by
    intro v hv
    rw [← hDeq] at hv
    rcases Finset.mem_union.mp hv with h | h
    · simp only [Finset.mem_insert, Finset.mem_singleton] at h; tauto
    · tauto
  have hAint : ∀ g ∈ A, 3 ≤ (G.neighborFinset g ∩ Dᶜ).card := by
    intro g hg
    rw [hAdef, Finset.mem_filter] at hg
    obtain ⟨hgDc, hgx, hgy, hgz⟩ := hg
    refine fully_free_internal_ge_three G D Iso g (hdeg4 g hgDc)
      (hW g hgDc ⟨hgx, hgy, hgz⟩) ?_
    intro w hadj hwD
    rcases hclassP w hwD with h | h | h | h
    · exact absurd (h ▸ hadj) hgx
    · exact absurd (h ▸ hadj) hgy
    · exact absurd (h ▸ hadj) hgz
    · exact h
  -- Avoider membership unfolding and the `|A| ≤ 5` budget.
  have getA : ∀ g : Fin 17, g ∈ A → g ∈ Dᶜ ∧ ¬G.Adj g x ∧ ¬G.Adj g y ∧ ¬G.Adj g z := by
    intro g hg; rw [hAdef, Finset.mem_filter] at hg; exact hg
  have hIsoD : Iso ⊆ D := by rw [hIsodef]; exact Finset.filter_subset _ _
  have hAle16 : ∑ g ∈ A, (G.neighborFinset g ∩ Dᶜ).card ≤ 16 :=
    le_of_le_of_eq
      (Finset.sum_le_sum_of_subset_of_nonneg hAsub (fun _ _ _ => Nat.zero_le _)) hSum16
  have hSAint_ge : 3 * A.card ≤ ∑ g ∈ A, (G.neighborFinset g ∩ Dᶜ).card := by
    have := Finset.card_nsmul_le_sum A (fun g => (G.neighborFinset g ∩ Dᶜ).card) 3 hAint
    simpa [smul_eq_mul, Nat.mul_comm] using this
  have hAcard5 : A.card ≤ 5 := by omega
  -- Counting prelims shared by the `|A| = 4` and `|A| = 5` sub-cases.
  have hsplitA : ∀ g : Fin 17, (G.neighborFinset g ∩ Dᶜ).card
      = (G.neighborFinset g ∩ A).card + (G.neighborFinset g ∩ (Dᶜ \ A)).card := by
    intro g
    rw [← Finset.card_union_of_disjoint, ← Finset.inter_union_distrib_left,
      Finset.union_sdiff_of_subset hAsub]
    apply Finset.disjoint_left.mpr
    intro w hw hw'
    rw [Finset.mem_inter] at hw hw'
    exact (Finset.mem_sdiff.mp hw'.2).2 hw.2
  have hSAsplit : (∑ g ∈ A, (G.neighborFinset g ∩ A).card)
      + ∑ g ∈ A, (G.neighborFinset g ∩ (Dᶜ \ A)).card
      = ∑ g ∈ A, (G.neighborFinset g ∩ Dᶜ).card := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun g _ => (hsplitA g).symm)
  have hcross : ∑ g ∈ A, (G.neighborFinset g ∩ (Dᶜ \ A)).card
      = ∑ w ∈ Dᶜ \ A, (G.neighborFinset w ∩ A).card :=
    cross_count G A (Dᶜ \ A)
  have hleak_le : ∑ w ∈ Dᶜ \ A, (G.neighborFinset w ∩ A).card
      ≤ ∑ w ∈ Dᶜ \ A, (G.neighborFinset w ∩ Dᶜ).card :=
    Finset.sum_le_sum (fun w _ =>
      Finset.card_le_card (Finset.inter_subset_inter (Finset.Subset.refl _) hAsub))
  have hsdiff : (∑ w ∈ Dᶜ \ A, (G.neighborFinset w ∩ Dᶜ).card)
      + ∑ g ∈ A, (G.neighborFinset g ∩ Dᶜ).card = 16 := by
    rw [Finset.sum_sdiff hAsub, hSum16]
  -- Cherry vertices are not `M`-isolated twins.
  have hxIso : x ∉ Iso := Finset.disjoint_left.mp hdisj (by simp)
  have hyIso : y ∉ Iso := Finset.disjoint_left.mp hdisj (by simp)
  have hzIso : z ∉ Iso := Finset.disjoint_left.mp hdisj (by simp)
  -- A twin shared by two avoiders assembles a `SingleVertexConfig`, contradicting `hsv`.
  have shared : ∀ g₁ g₂ t : Fin 17, g₁ ∈ A → g₂ ∈ A → g₁ ≠ g₂ → t ∈ Iso →
      G.Adj g₁ t → G.Adj g₂ t → False := by
    intro g₁ g₂ t hg1 hg2 hne htIso ha1 ha2
    obtain ⟨hg1Dc, hg1x, hg1y, hg1z⟩ := getA g₁ hg1
    obtain ⟨hg2Dc, hg2x, hg2y, hg2z⟩ := getA g₂ hg2
    have htdeg : G.degree t = 3 := (hIsoprop t htIso).1
    have htiso := (hIsoprop t htIso).2
    have htg1 : t ≠ g₁ := fun e => (Finset.mem_compl.mp hg1Dc) (e ▸ hIsoD htIso)
    have htg2 : t ≠ g₂ := fun e => (Finset.mem_compl.mp hg2Dc) (e ▸ hIsoD htIso)
    have htx : t ≠ x := fun e => hxIso (e ▸ htIso)
    have hty : t ≠ y := fun e => hyIso (e ▸ htIso)
    have htz : t ≠ z := fun e => hzIso (e ▸ htIso)
    have hg1ne : g₁ ≠ x ∧ g₁ ≠ y ∧ g₁ ≠ z := by
      refine ⟨?_, ?_, ?_⟩ <;> rintro rfl
      · exact (Finset.mem_compl.mp hg1Dc) hxD
      · exact (Finset.mem_compl.mp hg1Dc) hyD
      · exact (Finset.mem_compl.mp hg1Dc) hzD
    have hg2ne : g₂ ≠ x ∧ g₂ ≠ y ∧ g₂ ≠ z := by
      refine ⟨?_, ?_, ?_⟩ <;> rintro rfl
      · exact (Finset.mem_compl.mp hg2Dc) hxD
      · exact (Finset.mem_compl.mp hg2Dc) hyD
      · exact (Finset.mem_compl.mp hg2Dc) hzD
    have hptt : (G.neighborFinset t ∩ ({x, y, z} : Finset (Fin 17))).card = 0 := by
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro w hw
      rw [Finset.mem_inter, G.mem_neighborFinset] at hw
      obtain ⟨hadj, hmem⟩ := hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with rfl | rfl | rfl
      · exact htiso _ hadj hxdeg
      · exact htiso _ hadj hydeg
      · exact htiso _ hadj hzdeg
    have hpath0 : ∀ g : Fin 17, g ∈ A →
        (G.neighborFinset g ∩ ({x, y, z} : Finset (Fin 17))).card = 0 := by
      intro g hg
      obtain ⟨_, hgx, hgy, hgz⟩ := getA g hg
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro w hw
      rw [Finset.mem_inter, G.mem_neighborFinset] at hw
      obtain ⟨hadj, hmem⟩ := hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with rfl | rfl | rfl
      · exact hgx hadj
      · exact hgy hadj
      · exact hgz hadj
    apply hsv
    refine ⟨t, g₁, g₂, x, y, z, htdeg, hxdeg, hydeg, hzdeg, ha1.symm, ha2.symm,
      haxy, hayz, hnxz, ?_, hne, htx, hty, htz, hg1ne.1, hg1ne.2.1, hg1ne.2.2,
      hg2ne.1, hg2ne.2.1, hg2ne.2.2, haxy.ne, hayz.ne, hxz⟩
    have e2 := hpath0 g₁ hg1
    have e3 := hpath0 g₂ hg2
    have hsumeval : (∑ p ∈ ({t, g₁, g₂} : Finset (Fin 17)),
        (G.neighborFinset p ∩ ({x, y, z} : Finset (Fin 17))).card) = 0 := by
      rw [Finset.sum_insert (by simp [htg1, htg2]),
        Finset.sum_insert (by simp [hne]), Finset.sum_singleton]
      omega
    rw [hsumeval, hdeg4 g₁ hg1Dc, hdeg4 g₂ hg2Dc]
    split <;> omega
  -- The triangle, by dispatch on `|A| ∈ {4, 5}`.
  have htri : ∃ a b c : Fin 17, a ∈ A ∧ b ∈ A ∧ c ∈ A ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      G.Adj a b ∧ G.Adj a c ∧ G.Adj b c := by
    rcases (by omega : A.card = 4 ∨ A.card = 5) with hcard4 | hcard5
    · by_cases htri4 : ∃ a b c : Fin 17, a ∈ A ∧ b ∈ A ∧ c ∈ A ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
          G.Adj a b ∧ G.Adj a c ∧ G.Adj b c
      · exact htri4
      · exfalso
        have hTF : ∀ a b c : Fin 17, a ∈ A → b ∈ A → c ∈ A →
            G.Adj a b → G.Adj a c → G.Adj b c → False := by
          intro a b c ha hb hc h1 h2 h3
          exact htri4 ⟨a, b, c, ha, hb, hc, h1.ne, h2.ne, h3.ne, h1, h2, h3⟩
        have hmantel := mantel_quad_le G A hcard4 hTF
        have hg3 : ∀ g ∈ A, (G.neighborFinset g ∩ Dᶜ).card = 3 := by
          intro g hg
          by_contra hne3
          have hge4 : 4 ≤ (G.neighborFinset g ∩ Dᶜ).card :=
            lt_of_le_of_ne (hAint g hg) (Ne.symm hne3)
          have hrest : 3 * (A.erase g).card
              ≤ ∑ w ∈ A.erase g, (G.neighborFinset w ∩ Dᶜ).card := by
            have := Finset.card_nsmul_le_sum (A.erase g)
              (fun w => (G.neighborFinset w ∩ Dᶜ).card) 3
              (fun w hw => hAint w (Finset.mem_of_mem_erase hw))
            simpa [smul_eq_mul, Nat.mul_comm] using this
          have hadd := Finset.add_sum_erase A (fun w => (G.neighborFinset w ∩ Dᶜ).card) hg
          rw [Finset.card_erase_of_mem hg, hcard4] at hrest
          rw [hcard4] at hSAint_ge
          omega
        have hiso1eq : ∀ g ∈ A, (G.neighborFinset g ∩ Iso).card = 1 := by
          intro g hg
          have hp := hper g (hAsub hg)
          have hint := hg3 g hg
          obtain ⟨_, hgx, hgy, hgz⟩ := getA g hg
          have hpath0 : (G.neighborFinset g ∩ ({x, y, z} : Finset (Fin 17))).card = 0 := by
            rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
            intro w hw
            rw [Finset.mem_inter, G.mem_neighborFinset] at hw
            obtain ⟨hadj, hmem⟩ := hw
            simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
            rcases hmem with rfl | rfl | rfl
            · exact hgx hadj
            · exact hgy hadj
            · exact hgz hadj
          omega
        by_cases hdist : ∀ g₁ ∈ A, ∀ g₂ ∈ A, g₁ ≠ g₂ →
            Disjoint (G.neighborFinset g₁ ∩ Iso) (G.neighborFinset g₂ ∩ Iso)
        · -- Distinct twins → `TwoHubConfig`, contradicting `hth`.  The four avoiders form an
          -- induced `C₄` (`e(Dᶜ \ A) = 0`, each avoider `int = 3` with a single private twin);
          -- their distinct twins assemble two non-adjacent degree-`4` hubs each carrying `≥ 2`
          -- private twins, packaged by `cherry_C4_distinct_twin_twoHub`.
          apply hth
          have hAdc4 : Dᶜ.card = 9 := hDc9
          -- `e(Dᶜ \ A) = 0`: the five non-avoider hubs are pairwise non-adjacent.
          have hAint12 : ∑ g ∈ A, (G.neighborFinset g ∩ Dᶜ).card = 12 := by
            rw [Finset.sum_congr rfl hg3, Finset.sum_const, hcard4, smul_eq_mul]
          have hnonADc4 : ∑ w ∈ Dᶜ \ A, (G.neighborFinset w ∩ Dᶜ).card = 4 := by
            have h := hsdiff; rw [hAint12] at h; omega
          have hAnonA_ge3 : 3 ≤ ∑ g ∈ A, (G.neighborFinset g ∩ (Dᶜ \ A)).card := by
            have h := hSAsplit; rw [hAint12] at h; omega
          have hnonAsplit : (∑ w ∈ Dᶜ \ A, (G.neighborFinset w ∩ A).card)
              + ∑ w ∈ Dᶜ \ A, (G.neighborFinset w ∩ (Dᶜ \ A)).card
              = ∑ w ∈ Dᶜ \ A, (G.neighborFinset w ∩ Dᶜ).card := by
            rw [← Finset.sum_add_distrib]
            exact Finset.sum_congr rfl (fun w _ => (hsplitA w).symm)
          have hnonANonA_le1 : ∑ w ∈ Dᶜ \ A, (G.neighborFinset w ∩ (Dᶜ \ A)).card ≤ 1 := by
            have h1 := hnonAsplit
            rw [hnonADc4] at h1
            rw [hcross] at hAnonA_ge3
            omega
          have hindep : ∀ p ∈ Dᶜ \ A, ∀ q ∈ Dᶜ \ A, ¬G.Adj p q := by
            intro p hp q hq hadj
            have hpq : p ≠ q := G.ne_of_adj hadj
            have hqmem : q ∈ G.neighborFinset p ∩ (Dᶜ \ A) :=
              Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hadj, hq⟩
            have hpmem : p ∈ G.neighborFinset q ∩ (Dᶜ \ A) :=
              Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hadj.symm, hp⟩
            have hpge : 1 ≤ (G.neighborFinset p ∩ (Dᶜ \ A)).card := Finset.card_pos.mpr ⟨q, hqmem⟩
            have hqge : 1 ≤ (G.neighborFinset q ∩ (Dᶜ \ A)).card := Finset.card_pos.mpr ⟨p, hpmem⟩
            have hsub : ({p, q} : Finset (Fin 17)) ⊆ Dᶜ \ A := by
              intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
              rcases hw with rfl | rfl <;> assumption
            have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub
              (f := fun w => (G.neighborFinset w ∩ (Dᶜ \ A)).card) (fun i _ _ => Nat.zero_le _)
            rw [Finset.sum_pair hpq] at hle
            omega
          -- `iso ≤ 3` for non-avoider hubs (each meets the cherry).
          have hisole3 : ∀ h ∈ Dᶜ \ A, (G.neighborFinset h ∩ Iso).card ≤ 3 := by
            intro h hh
            rw [Finset.mem_sdiff] at hh
            obtain ⟨hhDc, hhnA⟩ := hh
            have hnotP : ¬(¬G.Adj h x ∧ ¬G.Adj h y ∧ ¬G.Adj h z) := by
              intro hP; exact hhnA (by rw [hAdef, Finset.mem_filter]; exact ⟨hhDc, hP⟩)
            have hor : G.Adj h x ∨ G.Adj h y ∨ G.Adj h z := by
              by_contra hc
              push Not at hc
              exact hnotP hc
            have hne : (G.neighborFinset h ∩ ({x, y, z} : Finset (Fin 17))).Nonempty := by
              rcases hor with h1 | h1 | h1
              · exact ⟨x, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr h1, by simp⟩⟩
              · exact ⟨y, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr h1, by simp⟩⟩
              · exact ⟨z, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr h1, by simp⟩⟩
            have hpath1 : 1 ≤ (G.neighborFinset h ∩ ({x, y, z} : Finset (Fin 17))).card :=
              hne.card_pos
            have h4 := hper h hhDc
            omega
          exact cherry_C4_distinct_twin_twoHub G D Iso A hIsodef hIsoprop hIsoD hdeg4 hC4 hAsub
            hcard4 hiso1eq hdist hindep hIso5 hDc9 hsumI hisole3
        · push Not at hdist
          obtain ⟨g₁, hg1, g₂, hg2, hne, hnd⟩ := hdist
          rw [Finset.not_disjoint_iff] at hnd
          obtain ⟨t, ht1, ht2⟩ := hnd
          rw [Finset.mem_inter, G.mem_neighborFinset] at ht1 ht2
          exact shared g₁ g₂ t hg1 hg2 hne ht1.2 ht1.1 ht2.1
    · apply mantel_five G A hcard5
      rw [hcard5] at hSAint_ge
      omega
  obtain ⟨a, b, c, haA, hbA, hcA, hab, hac, hbc, hadj_ab, hadj_ac, hadj_bc⟩ := htri
  obtain ⟨haDc, hax, hay, haz⟩ := getA a haA
  obtain ⟨hbDc, hbx, hby, hbz⟩ := getA b hbA
  obtain ⟨hcDc, hcxx, hcyy, hczz⟩ := getA c hcA
  have hubne : ∀ g : Fin 17, g ∈ Dᶜ → g ≠ x ∧ g ≠ y ∧ g ≠ z := by
    intro g hg
    refine ⟨?_, ?_, ?_⟩ <;> rintro rfl
    · exact (Finset.mem_compl.mp hg) hxD
    · exact (Finset.mem_compl.mp hg) hyD
    · exact (Finset.mem_compl.mp hg) hzD
  obtain ⟨hanex, haney, hanez⟩ := hubne a haDc
  obtain ⟨hbnex, hbney, hbnez⟩ := hubne b hbDc
  obtain ⟨hcnex, hcney, hcnez⟩ := hubne c hcDc
  exact ⟨a, b, c, x, y, z, hxdeg, hydeg, hzdeg, hadj_ab, hadj_ac, hadj_bc,
    haxy, hayz, hax, hay, haz, hbx, hby, hbz, hcxx, hcyy, hczz,
    (by have := hdeg4 a haDc; have := hdeg4 b hbDc; have := hdeg4 c hcDc; omega),
    hanex, haney, hanez, hbnex, hbney, hbnez, hcnex, hcney, hcnez,
    haxy.ne, hayz.ne, hxz⟩

end N17

end ACMax
