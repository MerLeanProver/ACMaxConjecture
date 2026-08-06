import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N18.Core
import ACMaxConjecture.SmallCases.Certificates
import ACMaxConjecture.SmallCases.N18.HubTriangleStruct
import ACMaxConjecture.SmallCases.N18.HubTriangleFF
import ACMaxConjecture.SmallCases.N18.CherryC5TwoHub

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

namespace N18

/-- **Cherry / Iso partition of `D`.**  The three cherry vertices and the `M`-isolated twins
partition `D`: `{x, y, z} ∪ Iso = D` and the two parts are disjoint. -/
theorem cherry_partition (G : SimpleGraph (Fin 18)) (D Iso : Finset (Fin 18)) (x y z : Fin 18)
    (hIsodef : Iso = D.filter (fun v => (G.neighborFinset v ∩ D).card = 0))
    (hisochar : ∀ w : Fin 18, w ∈ D → w ≠ x → w ≠ y → w ≠ z → w ∈ Iso)
    (hxD : x ∈ D) (hyD : y ∈ D) (hzD : z ∈ D)
    (haxy : G.Adj x y) (hayz : G.Adj y z) :
    ({x, y, z} : Finset (Fin 18)) ∪ Iso = D ∧ Disjoint ({x, y, z} : Finset (Fin 18)) Iso := by
  classical
  set P : Finset (Fin 18) := {x, y, z} with hP
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
theorem cherry_leaf_card (G : SimpleGraph (Fin 18)) (D : Finset (Fin 18)) (x y z : Fin 18)
    (hcov : ∀ p q : Fin 18, p ∈ D → q ∈ D → G.Adj p q → p = y ∨ q = y)
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
theorem cherry_residual_sums (G : SimpleGraph (Fin 18)) (D Iso : Finset (Fin 18)) (x y z : Fin 18)
    (hIsodef : Iso = D.filter (fun v => (G.neighborFinset v ∩ D).card = 0))
    (hIsoprop : ∀ v ∈ Iso, G.degree v = 3 ∧ (∀ w : Fin 18, G.Adj v w → G.degree w ≠ 3))
    (hisochar : ∀ w : Fin 18, w ∈ D → w ≠ x → w ≠ y → w ≠ z → w ∈ Iso)
    (hxD : x ∈ D) (hyD : y ∈ D) (hzD : z ∈ D)
    (haxy : G.Adj x y) (hayz : G.Adj y z)
    (hxy : x ≠ y) (hzy : z ≠ y) (hxz : x ≠ z)
    (hdeg4 : ∀ w : Fin 18, w ∈ Dᶜ → G.degree w = 4)
    (hcx : (G.neighborFinset x ∩ Dᶜ).card = 2) (hcy : (G.neighborFinset y ∩ Dᶜ).card = 1)
    (hcz : (G.neighborFinset z ∩ Dᶜ).card = 2) (hIso5 : Iso.card = 5) :
    (∑ g ∈ Dᶜ, (G.neighborFinset g ∩ ({x, y, z} : Finset (Fin 18))).card = 5) ∧
      (∑ g ∈ Dᶜ, (G.neighborFinset g ∩ Iso).card = 15) ∧
      (∀ g ∈ Dᶜ, (G.neighborFinset g ∩ ({x, y, z} : Finset (Fin 18))).card
        + (G.neighborFinset g ∩ Iso).card + (G.neighborFinset g ∩ Dᶜ).card = 4) := by
  classical
  set P : Finset (Fin 18) := {x, y, z} with hP
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

/-- **At least five cherry-avoiding hubs.**  The cherry `{x, y, z}` collects only
`2 + 1 + 2 = 5` hub-incidences, so `≥ 5` of the ten hubs avoid all three vertices. -/
theorem cherry_avoiders_ge_five (G : SimpleGraph (Fin 18)) (D : Finset (Fin 18)) (x y z : Fin 18)
    (hDc9 : Dᶜ.card = 10)
    (hcx : (G.neighborFinset x ∩ Dᶜ).card = 2) (hcy : (G.neighborFinset y ∩ Dᶜ).card = 1)
    (hcz : (G.neighborFinset z ∩ Dᶜ).card = 2) :
    5 ≤ (Dᶜ.filter (fun g => ¬G.Adj g x ∧ ¬G.Adj g y ∧ ¬G.Adj g z)).card := by
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

/-- **Hub-triangle existence in the `n = 18`, `|D| = 8`, `e(M) = 2`, single-`P₃`-cherry corner.**
Under the residual hypotheses (ten degree-`4` hubs, `10` hub-hub edges `∑ int = 20`, `M = P₃`
cherry `x–y–z` with five `M`-isolated twins, and the falsity of `SingleVertexConfig`/
`TwoTwinConfig`/`TwoHubConfig`), the graph contains three pairwise-adjacent hubs avoiding the
cherry, packaged as `HubTriangleConfig G`.  Every avoider is fully free (`int ≥ 3`); the triangle
is dispatched on `|A| ∈ {5, 6}` via the leak bound `∑_A(N ∩ A) ≥ 2·∑_A int − 20` and
`mantel_five_triangle`/`mantel_six_triangle`.  The `|A| = 6` `K_{3,3}` corner is closed: it is
**vacuous**, since the cherry meets `2 + 1 + 2 = 5` hubs while only `|Dᶜ \ A| = 4` non-avoiders
exist and each meets `≤ 1` cherry vertex (two cherry neighbours give a good triangle `Σ ≤ 10`
via `hT10`, or for the endpoints a good `C₄` `Σ = 13` via `hC4`).  One dense-but-triangle-free
residual carries a documented `sorry`: `|A| = 5`, `∑_A int ∈ {15, 16}` (a `C₅` / `K_{2,3}` of
avoiders), which needs the five-avoider distinct-twin `TwoHubConfig` assembly. -/
theorem exists_hub_triangle_config_cherry_residual_eighteen (G : SimpleGraph (Fin 18))
    (D Iso : Finset (Fin 18)) (x y z : Fin 18)
    (hmemD : ∀ v : Fin 18, v ∈ D ↔ G.degree v = 3)
    (hIsodef : Iso = D.filter (fun v => (G.neighborFinset v ∩ D).card = 0))
    (hIsoprop : ∀ v ∈ Iso, G.degree v = 3 ∧ (∀ w : Fin 18, G.Adj v w → G.degree w ≠ 3))
    (hisochar : ∀ w : Fin 18, w ∈ D → w ≠ x → w ≠ y → w ≠ z → w ∈ Iso)
    (hcov : ∀ p q : Fin 18, p ∈ D → q ∈ D → G.Adj p q → p = y ∨ q = y)
    (hNyD : G.neighborFinset y ∩ D = {x, z})
    (hxdeg : G.degree x = 3) (hydeg : G.degree y = 3) (hzdeg : G.degree z = 3)
    (haxy : G.Adj x y) (hayz : G.Adj y z) (hnxz : ¬G.Adj x z) (hxz : x ≠ z)
    (hdeg4 : ∀ w : Fin 18, w ∈ Dᶜ → G.degree w = 4)
    (hD8 : D.card = 8)
    (hC4 : ¬∃ a b c d : Fin 18, ({a, b, c, d} : Finset (Fin 18)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (hT10 : ¬∃ a b c : Fin 18, a ≠ b ∧ b ≠ c ∧ a ≠ c ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj a c ∧ G.degree a + G.degree b + G.degree c ≤ 10)
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
  have hW : ∀ g : Fin 18, g ∈ Dᶜ → (¬G.Adj g x ∧ ¬G.Adj g y ∧ ¬G.Adj g z) →
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
  have hDc9 : Dᶜ.card = 10 := by rw [Finset.card_compl, Fintype.card_fin, hD8]
  have hIso5 : Iso.card = 5 := by
    have hPcard : ({x, y, z} : Finset (Fin 18)).card = 3 := by
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
  have hSum16 : ∑ w ∈ Dᶜ, (G.neighborFinset w ∩ Dᶜ).card = 20 := by
    have htot : ∑ g ∈ Dᶜ, ((G.neighborFinset g ∩ ({x, y, z} : Finset (Fin 18))).card
        + (G.neighborFinset g ∩ Iso).card + (G.neighborFinset g ∩ Dᶜ).card)
        = ∑ _g ∈ Dᶜ, 4 := Finset.sum_congr rfl hper
    rw [Finset.sum_const, smul_eq_mul, hDc9, Finset.sum_add_distrib, Finset.sum_add_distrib,
      hsumP, hsumI] at htot
    omega
  -- The cherry-avoider set, with `≥ 5` members each of internal degree `≥ 3`.
  set A := Dᶜ.filter (fun g => ¬G.Adj g x ∧ ¬G.Adj g y ∧ ¬G.Adj g z) with hAdef
  have hAsub : A ⊆ Dᶜ := Finset.filter_subset _ _
  have hA4 : 5 ≤ A.card := by
    rw [hAdef]; exact cherry_avoiders_ge_five G D x y z hDc9 hcx hcy hcz
  have hclassP : ∀ v : Fin 18, v ∈ D → v = x ∨ v = y ∨ v = z ∨ v ∈ Iso := by
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
  have getA : ∀ g : Fin 18, g ∈ A → g ∈ Dᶜ ∧ ¬G.Adj g x ∧ ¬G.Adj g y ∧ ¬G.Adj g z := by
    intro g hg; rw [hAdef, Finset.mem_filter] at hg; exact hg
  have hIsoD : Iso ⊆ D := by rw [hIsodef]; exact Finset.filter_subset _ _
  have hAle16 : ∑ g ∈ A, (G.neighborFinset g ∩ Dᶜ).card ≤ 20 :=
    le_of_le_of_eq
      (Finset.sum_le_sum_of_subset_of_nonneg hAsub (fun _ _ _ => Nat.zero_le _)) hSum16
  have hSAint_ge : 3 * A.card ≤ ∑ g ∈ A, (G.neighborFinset g ∩ Dᶜ).card := by
    have := Finset.card_nsmul_le_sum A (fun g => (G.neighborFinset g ∩ Dᶜ).card) 3 hAint
    simpa [smul_eq_mul, Nat.mul_comm] using this
  have hAcard5 : A.card ≤ 6 := by omega
  -- Counting prelims shared by the `|A| = 4` and `|A| = 5` sub-cases.
  have hsplitA : ∀ g : Fin 18, (G.neighborFinset g ∩ Dᶜ).card
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
      + ∑ g ∈ A, (G.neighborFinset g ∩ Dᶜ).card = 20 := by
    rw [Finset.sum_sdiff hAsub, hSum16]
  -- The triangle, by dispatch on `|A| ∈ {5, 6}`.  Each avoider is fully free (`int ≥ 3`), and the
  -- in-`A` edge mass obeys the leak bound `∑_A(N ∩ A) ≥ 2·∑_A int − 20`.  When `∑_A int` is large
  -- enough a Mantel triangle is forced: `|A| = 5`, `∑_A int ≥ 17` (`∑_A(N ∩ A) ≥ 14`) via
  -- `mantel_five_triangle`; `|A| = 6`, `∑_A int = 20` (`∑_A(N ∩ A) ≥ 20 ≥ 19`) via
  -- `mantel_six_triangle`.  The `|A| = 6` corner is closed by **vacuity** (`5` cherry incidences
  -- cannot land on the `4` non-avoiders, each meeting `≤ 1` cherry vertex via `hT10` / `hC4`).
  -- One dense-but-triangle-free residual remains a documented `sorry`: `|A| = 5`,
  -- `∑_A int ∈ {15, 16}` (a `C₅` / `K_{2,3}` of avoiders) needs the distinct-twin `TwoHubConfig`
  -- assembly for five avoiders — a cluster beyond the `n = 17` `C₄` port (`hindep` no longer holds
  -- for the `K_{2,3}` sub-structure, and the shared-twin double count has borderline cases).
  have htri : ∃ a b c : Fin 18, a ∈ A ∧ b ∈ A ∧ c ∈ A ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      G.Adj a b ∧ G.Adj a c ∧ G.Adj b c := by
    rcases (by omega : A.card = 5 ∨ A.card = 6) with hcard5 | hcard6
    · by_cases hbig : 17 ≤ ∑ g ∈ A, (G.neighborFinset g ∩ Dᶜ).card
      · obtain ⟨a, b, c, haA, hbA, hcA, hab, hac, hbc⟩ :=
          mantel_five_triangle G A hcard5 (by omega)
        exact ⟨a, b, c, haA, hbA, hcA, hab.ne, hac.ne, hbc.ne, hab, hac, hbc⟩
      · -- `|A| = 5`, `∑_A int ∈ {15, 16}`: the five cherry-avoiders form a triangle-free `C₅` /
        -- `K_{2,3}`; the goal is discharged by deriving `False` from the non-avoider hubs.
        exfalso
        -- **Shared-twin case [from `¬SingleVertexConfig`].**  If two cherry-avoiders `p, q` share an
        -- `M`-isolated twin `t`, the apex `t` with `p, q` and the cherry `x–y–z` forms a
        -- `SingleVertexConfig` (all of `t, p, q` avoid the cherry, so the cross term vanishes and the
        -- side condition reads `8 ≤ 8`), contradicting `hsv`.
        by_cases hshared : ∃ t : Fin 18, t ∈ Iso ∧ ∃ p : Fin 18, p ∈ A ∧ ∃ q : Fin 18, q ∈ A ∧
            p ≠ q ∧ G.Adj p t ∧ G.Adj q t
        · obtain ⟨t, htIso, p, hpA, q, hqA, hpq, hpt, hqt⟩ := hshared
          apply hsv
          obtain ⟨hpDc, hpx, hpy, hpz⟩ := getA p hpA
          obtain ⟨hqDc, hqx, hqy, hqz⟩ := getA q hqA
          have htdeg : G.degree t = 3 := (hIsoprop t htIso).1
          have htiso : ∀ w : Fin 18, G.Adj t w → G.degree w ≠ 3 := (hIsoprop t htIso).2
          have hpdeg : G.degree p = 4 := hdeg4 p hpDc
          have hqdeg : G.degree q = 4 := hdeg4 q hqDc
          have htnotxyz : t ∉ ({x, y, z} : Finset (Fin 18)) :=
            fun hmem => (Finset.disjoint_left.mp hdisj hmem) htIso
          have htx : t ≠ x := fun e => htnotxyz (by rw [e]; simp)
          have hty : t ≠ y := fun e => htnotxyz (by rw [e]; simp)
          have htz : t ≠ z := fun e => htnotxyz (by rw [e]; simp)
          have hpx' : p ≠ x := fun e => (Finset.mem_compl.mp hpDc) (e ▸ hxD)
          have hpy' : p ≠ y := fun e => (Finset.mem_compl.mp hpDc) (e ▸ hyD)
          have hpz' : p ≠ z := fun e => (Finset.mem_compl.mp hpDc) (e ▸ hzD)
          have hqx' : q ≠ x := fun e => (Finset.mem_compl.mp hqDc) (e ▸ hxD)
          have hqy' : q ≠ y := fun e => (Finset.mem_compl.mp hqDc) (e ▸ hyD)
          have hqz' : q ≠ z := fun e => (Finset.mem_compl.mp hqDc) (e ▸ hzD)
          have hsum0 : ∑ w ∈ ({t, p, q} : Finset (Fin 18)),
              (G.neighborFinset w ∩ ({x, y, z} : Finset (Fin 18))).card = 0 := by
            apply Finset.sum_eq_zero
            intro w hw
            rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
            intro a ha
            rw [Finset.mem_inter, G.mem_neighborFinset] at ha
            obtain ⟨hadj, hmem⟩ := ha
            simp only [Finset.mem_insert, Finset.mem_singleton] at hw hmem
            rcases hw with rfl | rfl | rfl <;> rcases hmem with rfl | rfl | rfl
            · exact htiso _ hadj hxdeg
            · exact htiso _ hadj hydeg
            · exact htiso _ hadj hzdeg
            · exact hpx hadj
            · exact hpy hadj
            · exact hpz hadj
            · exact hqx hadj
            · exact hqy hadj
            · exact hqz hadj
          exact ⟨t, p, q, x, y, z, htdeg, hxdeg, hydeg, hzdeg, hpt.symm, hqt.symm, haxy, hayz, hnxz,
            (by rw [hsum0, hpdeg, hqdeg]; split <;> omega), hpq,
            htx, hty, htz, hpx', hpy', hpz', hqx', hqy', hqz', hxy, hayz.ne, hxz⟩
        · -- **Distinct-twin case.**  Each `M`-isolated twin meets `≤ 1` cherry-avoider, so every twin
          -- has `≥ 2` neighbours among the five non-avoiders `S = Dᶜ \ A` (`∑_S iso ≥ 10`).  A
          -- non-adjacent pair of `S`-hubs each carrying two private `M`-isolated twins assembles a
          -- `TwoHubConfig`, discharged by `cherry_C5_distinct_twin_twoHub_eighteen`.
          exact absurd
            (cherry_C5_distinct_twin_twoHub_eighteen G D Iso A x y z hIsodef hIsoprop hIsoD hdeg4
              hC4 hAsub hcard5 hIso5 hDc9
              (fun g hg => (getA g hg).2)
              (by intro h hhDc hhA
                  by_contra hcon
                  push Not at hcon
                  exact hhA (by rw [hAdef, Finset.mem_filter]
                                exact ⟨hhDc, hcon.1, hcon.2.1, hcon.2.2⟩))
              hper
              (by intro t ht
                  by_contra hgt
                  rw [not_le] at hgt
                  obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp hgt
                  rw [Finset.mem_inter, G.mem_neighborFinset] at hp hq
                  exact hshared ⟨t, ht, p, hp.2, q, hq.2, hpq, hp.1.symm, hq.1.symm⟩)
              hsumI)
            hth
    · by_cases hbig : 20 ≤ ∑ g ∈ A, (G.neighborFinset g ∩ Dᶜ).card
      · obtain ⟨a, b, c, haA, hbA, hcA, hab, hac, hbc⟩ :=
          mantel_six_triangle G A hcard6 (by omega)
        exact ⟨a, b, c, haA, hbA, hcA, hab.ne, hac.ne, hbc.ne, hab, hac, hbc⟩
      · -- `|A| = 6` is **vacuous**: the cherry `x–y–z` meets `2 + 1 + 2 = 5` hubs, but only
        -- `|Dᶜ \ A| = 4` non-avoider hubs exist, and each meets `≤ 1` cherry vertex (two cherry
        -- neighbours give a good triangle `Σ = 10 ≤ 10` via `hT10`, or — for the endpoints `x, z`
        -- — a good `C₄` `x–y–z–h` with `Σ = 13 ≤ 14` via `hC4`).
        exfalso
        have hle1 : ∀ h : Fin 18, h ∈ Dᶜ →
            (G.neighborFinset h ∩ ({x, y, z} : Finset (Fin 18))).card ≤ 1 := by
          intro h hhDc
          have hhdeg : G.degree h = 4 := hdeg4 h hhDc
          have hhne : h ≠ x ∧ h ≠ y ∧ h ≠ z := by
            refine ⟨?_, ?_, ?_⟩ <;> rintro rfl
            · exact (Finset.mem_compl.mp hhDc) hxD
            · exact (Finset.mem_compl.mp hhDc) hyD
            · exact (Finset.mem_compl.mp hhDc) hzD
          have htri : ∀ u v : Fin 18, u ≠ v → G.Adj u v → G.Adj h u → G.Adj h v →
              G.degree u = 3 → G.degree v = 3 → False := by
            intro u v huv hauv hhu hhv hu3 hv3
            exact hT10 ⟨u, v, h, huv, (G.ne_of_adj hhv).symm, (G.ne_of_adj hhu).symm,
              hauv, hhv.symm, hhu.symm, by omega⟩
          have hc4xz : G.Adj h x → G.Adj h z → False := by
            intro hhx hhz
            by_cases hhy : G.Adj h y
            · exact htri x y hxy haxy hhx hhy hxdeg hydeg
            · apply hC4
              refine ⟨x, y, z, h, ?_, haxy, hayz, hhz.symm, hhx, hnxz,
                fun ha => hhy ha.symm, by omega⟩
              rw [Finset.card_insert_of_notMem (by
                    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
                    exact ⟨hxy, hxz, fun e => hhne.1 e.symm⟩),
                  Finset.card_insert_of_notMem (by
                    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
                    exact ⟨hzy.symm, fun e => hhne.2.1 e.symm⟩),
                  Finset.card_insert_of_notMem (by
                    simp only [Finset.mem_singleton]
                    exact fun e => hhne.2.2 e.symm), Finset.card_singleton]
          by_contra hge2
          rw [not_le] at hge2
          obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp hge2
          rw [Finset.mem_inter, G.mem_neighborFinset] at hp hq
          obtain ⟨hhp, hpP⟩ := hp
          obtain ⟨hhq, hqP⟩ := hq
          simp only [Finset.mem_insert, Finset.mem_singleton] at hpP hqP
          rcases hpP with rfl | rfl | rfl <;> rcases hqP with rfl | rfl | rfl
          · exact hpq rfl
          · exact htri p q hxy haxy hhp hhq hxdeg hydeg
          · exact hc4xz hhp hhq
          · exact htri q p hxy haxy hhq hhp hxdeg hydeg
          · exact hpq rfl
          · exact htri p q hzy.symm hayz hhp hhq hydeg hzdeg
          · exact hc4xz hhq hhp
          · exact htri q p hzy.symm hayz hhq hhp hydeg hzdeg
          · exact hpq rfl
        have hA0 : ∀ g : Fin 18, g ∈ A →
            (G.neighborFinset g ∩ ({x, y, z} : Finset (Fin 18))).card = 0 := by
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
        have hAsum0 : ∑ g ∈ A, (G.neighborFinset g ∩ ({x, y, z} : Finset (Fin 18))).card = 0 :=
          Finset.sum_eq_zero (fun g hg => hA0 g hg)
        have hkey : ∑ g ∈ Dᶜ \ A,
            (G.neighborFinset g ∩ ({x, y, z} : Finset (Fin 18))).card = 5 := by
          have h := Finset.sum_sdiff (f := fun g =>
            (G.neighborFinset g ∩ ({x, y, z} : Finset (Fin 18))).card) hAsub
          rw [hAsum0, hsumP] at h; omega
        have hub4 : (Dᶜ \ A).card = 4 := by
          have h := Finset.card_sdiff_add_card_inter Dᶜ A
          rw [Finset.inter_eq_right.mpr hAsub, hDc9, hcard6] at h
          omega
        have hle : ∑ g ∈ Dᶜ \ A,
            (G.neighborFinset g ∩ ({x, y, z} : Finset (Fin 18))).card ≤ (Dᶜ \ A).card := by
          calc ∑ g ∈ Dᶜ \ A, (G.neighborFinset g ∩ ({x, y, z} : Finset (Fin 18))).card
              ≤ ∑ _g ∈ Dᶜ \ A, 1 :=
                Finset.sum_le_sum (fun g hg => hle1 g (Finset.mem_sdiff.mp hg).1)
            _ = (Dᶜ \ A).card := by rw [Finset.sum_const, smul_eq_mul, Nat.mul_one]
        omega
  obtain ⟨a, b, c, haA, hbA, hcA, hab, hac, hbc, hadj_ab, hadj_ac, hadj_bc⟩ := htri
  obtain ⟨haDc, hax, hay, haz⟩ := getA a haA
  obtain ⟨hbDc, hbx, hby, hbz⟩ := getA b hbA
  obtain ⟨hcDc, hcxx, hcyy, hczz⟩ := getA c hcA
  have hubne : ∀ g : Fin 18, g ∈ Dᶜ → g ≠ x ∧ g ≠ y ∧ g ≠ z := by
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

end N18

end ACMax
