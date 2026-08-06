import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N16.Core
import ACMaxConjecture.SmallCases.Certificates
import ACMaxConjecture.SmallCases.N16.HubTriangleStruct

/-!
# Hub-triangle existence for the `n = 16`, `e(M) = 2`, single-`P₃`-cherry residual corner

This file isolates the hub-triangle existence obligation in the `e(M) = 2`, `|D| = 8`
(`|Hub| = 8`, all-degree-`4`) corner where the residual `M` is a **single `P₃` cherry**
`x–y–z` (`y` the middle, in-`M` degree `2`; `x, z` the endpoints, in-`M` degree `1`).  It is the
single-cherry analogue of `TwinCert16HubTriangle` (`e(M) = 3`, `P₄`, two cherries), and is
genuinely simpler: there is only one cherry, so *every* cherry-avoiding hub is fully free
(internal degree `≥ 3`), the hub-internal-degree total is `∑ int = 2·e(Hub) = 12`, and the
avoider set is pinned to a `3`- or `4`-clique outright (no `TwoHubConfig`/share-`≤ 1` detour).

## The residual configuration
* `D` = the degree-`3` vertices, `|D| = 8`; `Dᶜ` = the eight hubs, all of degree `4` (`hdeg4`).
* `M = P₃` cherry `x–y–z` (`hNyD : N(y) ∩ D = {x, z}`, `haxy`, `hayz`), plus `|Iso| = 5`
  `M`-isolated degree-`3` twins (`Iso`).
* `e(Hub) = 6` hub-hub edges (`∑_{Dᶜ} int = 12`, from the per-hub split
  `path(g) + iso(g) + int(g) = 4` over eight hubs: `4·8 − 5 − 15 = 12`).

## The target
`HubTriangleConfig G`: three pairwise-adjacent hubs avoiding the cherry `{x, y, z}`; their degree
sum is `12 ≤ 13` automatically.  The cherry meets `≤ 2 + 1 + 2 = 5` hubs, so `≥ 3` hubs avoid it;
each avoider is fully free (`int ≥ 3`), `3·|A| ≤ 12` pins `|A| ≤ 4`, and a leak count forces the
avoider set to be complete — yielding the triangle.
-/

namespace ACMax

open scoped Classical

namespace N16

/-- **Cherry / Iso partition of `D`.**  The three cherry vertices and the `M`-isolated twins
partition `D`: `{x, y, z} ∪ Iso = D` and the two parts are disjoint. -/
theorem cherry_partition (G : SimpleGraph (Fin 16)) (D Iso : Finset (Fin 16)) (x y z : Fin 16)
    (hIsodef : Iso = D.filter (fun v => (G.neighborFinset v ∩ D).card = 0))
    (hisochar : ∀ w : Fin 16, w ∈ D → w ≠ x → w ≠ y → w ≠ z → w ∈ Iso)
    (hxD : x ∈ D) (hyD : y ∈ D) (hzD : z ∈ D)
    (haxy : G.Adj x y) (hayz : G.Adj y z) :
    ({x, y, z} : Finset (Fin 16)) ∪ Iso = D ∧ Disjoint ({x, y, z} : Finset (Fin 16)) Iso := by
  classical
  set P : Finset (Fin 16) := {x, y, z} with hP
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
theorem cherry_leaf_card (G : SimpleGraph (Fin 16)) (D : Finset (Fin 16)) (x y z : Fin 16)
    (hcov : ∀ p q : Fin 16, p ∈ D → q ∈ D → G.Adj p q → p = y ∨ q = y)
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

/-- **Cherry residual incidence sums.**  Over the eight hubs the cherry-, iso- and hub-internal
incidences total `5`, `15`, `12` respectively, and per hub the three split the degree `4`. -/
theorem cherry_residual_sums (G : SimpleGraph (Fin 16)) (D Iso : Finset (Fin 16)) (x y z : Fin 16)
    (hIsodef : Iso = D.filter (fun v => (G.neighborFinset v ∩ D).card = 0))
    (hIsoprop : ∀ v ∈ Iso, G.degree v = 3 ∧ (∀ w : Fin 16, G.Adj v w → G.degree w ≠ 3))
    (hisochar : ∀ w : Fin 16, w ∈ D → w ≠ x → w ≠ y → w ≠ z → w ∈ Iso)
    (hxD : x ∈ D) (hyD : y ∈ D) (hzD : z ∈ D)
    (haxy : G.Adj x y) (hayz : G.Adj y z)
    (hxy : x ≠ y) (hzy : z ≠ y) (hxz : x ≠ z)
    (hdeg4 : ∀ w : Fin 16, w ∈ Dᶜ → G.degree w = 4)
    (hcx : (G.neighborFinset x ∩ Dᶜ).card = 2) (hcy : (G.neighborFinset y ∩ Dᶜ).card = 1)
    (hcz : (G.neighborFinset z ∩ Dᶜ).card = 2) (hIso5 : Iso.card = 5) :
    (∑ g ∈ Dᶜ, (G.neighborFinset g ∩ ({x, y, z} : Finset (Fin 16))).card = 5) ∧
      (∑ g ∈ Dᶜ, (G.neighborFinset g ∩ Iso).card = 15) ∧
      (∀ g ∈ Dᶜ, (G.neighborFinset g ∩ ({x, y, z} : Finset (Fin 16))).card
        + (G.neighborFinset g ∩ Iso).card + (G.neighborFinset g ∩ Dᶜ).card = 4) := by
  classical
  set P : Finset (Fin 16) := {x, y, z} with hP
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

/-- **At least three cherry-avoiding hubs.**  The cherry `{x, y, z}` collects only
`2 + 1 + 2 = 5` hub-incidences, so `≥ 3` of the eight hubs avoid all three vertices. -/
theorem cherry_avoiders_ge_three (G : SimpleGraph (Fin 16)) (D : Finset (Fin 16)) (x y z : Fin 16)
    (hDc8 : Dᶜ.card = 8)
    (hcx : (G.neighborFinset x ∩ Dᶜ).card = 2) (hcy : (G.neighborFinset y ∩ Dᶜ).card = 1)
    (hcz : (G.neighborFinset z ∩ Dᶜ).card = 2) :
    3 ≤ (Dᶜ.filter (fun g => ¬G.Adj g x ∧ ¬G.Adj g y ∧ ¬G.Adj g z)).card := by
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

/-- **A clique among the cherry-avoiders.**  If `A ⊆ Dᶜ` has `≥ 3` members each of hub-internal
degree `≥ 3`, and the hub-internal-degree total is `12`, then `|A| ≤ 4` (`3|A| ≤ 12`) and a leak
count forces `A` to be complete; in particular three of its members are pairwise adjacent. -/
theorem cherry_avoider_triangle (G : SimpleGraph (Fin 16)) (Dc A : Finset (Fin 16))
    (hAsub : A ⊆ Dc) (hA3 : 3 ≤ A.card)
    (hAint : ∀ g ∈ A, 3 ≤ (G.neighborFinset g ∩ Dc).card)
    (hSum12 : ∑ w ∈ Dc, (G.neighborFinset w ∩ Dc).card = 12) :
    ∃ a b c : Fin 16, a ∈ A ∧ b ∈ A ∧ c ∈ A ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      G.Adj a b ∧ G.Adj a c ∧ G.Adj b c := by
  classical
  have hSAint_ge : 3 * A.card ≤ ∑ g ∈ A, (G.neighborFinset g ∩ Dc).card := by
    have := Finset.card_nsmul_le_sum A (fun g => (G.neighborFinset g ∩ Dc).card) 3 hAint
    simpa [smul_eq_mul, Nat.mul_comm] using this
  have hSAint_le : ∑ g ∈ A, (G.neighborFinset g ∩ Dc).card ≤ 12 := by
    rw [← hSum12]
    exact Finset.sum_le_sum_of_subset_of_nonneg hAsub (fun _ _ _ => Nat.zero_le _)
  have hAcard4 : A.card ≤ 4 := by omega
  have hsplit : ∀ g : Fin 16, (G.neighborFinset g ∩ Dc).card
      = (G.neighborFinset g ∩ A).card + (G.neighborFinset g ∩ (Dc \ A)).card := by
    intro g
    rw [← Finset.card_union_of_disjoint, ← Finset.inter_union_distrib_left,
      Finset.union_sdiff_of_subset hAsub]
    apply Finset.disjoint_left.mpr
    intro a ha ha'
    rw [Finset.mem_inter] at ha ha'
    exact (Finset.mem_sdiff.mp ha'.2).2 ha.2
  have hSAsplit : (∑ g ∈ A, (G.neighborFinset g ∩ A).card)
      + ∑ g ∈ A, (G.neighborFinset g ∩ (Dc \ A)).card
      = ∑ g ∈ A, (G.neighborFinset g ∩ Dc).card := by
    rw [← Finset.sum_add_distrib]
    exact (Finset.sum_congr rfl (fun g _ => (hsplit g).symm))
  have hcross : ∑ g ∈ A, (G.neighborFinset g ∩ (Dc \ A)).card
      = ∑ w ∈ Dc \ A, (G.neighborFinset w ∩ A).card :=
    cross_count G A (Dc \ A)
  have hleak_le : ∑ w ∈ Dc \ A, (G.neighborFinset w ∩ A).card
      ≤ ∑ w ∈ Dc \ A, (G.neighborFinset w ∩ Dc).card := by
    apply Finset.sum_le_sum
    intro w _
    exact Finset.card_le_card (Finset.inter_subset_inter (Finset.Subset.refl _) hAsub)
  have hsdiff : (∑ w ∈ Dc \ A, (G.neighborFinset w ∩ Dc).card)
      + ∑ g ∈ A, (G.neighborFinset g ∩ Dc).card = 12 := by
    rw [Finset.sum_sdiff hAsub, hSum12]
  have hSANA_ge : 6 * A.card ≤ (∑ g ∈ A, (G.neighborFinset g ∩ A).card) + 12 := by
    omega
  have hNAle : ∀ g ∈ A, (G.neighborFinset g ∩ A).card ≤ A.card - 1 := by
    intro g hg
    have hsubg : G.neighborFinset g ∩ A ⊆ A.erase g := by
      intro w hw
      rw [Finset.mem_inter, G.mem_neighborFinset] at hw
      exact Finset.mem_erase.mpr ⟨fun e => G.irrefl (e ▸ hw.1), hw.2⟩
    have := Finset.card_le_card hsubg
    rwa [Finset.card_erase_of_mem hg] at this
  have hclique : ∀ g ∈ A, (G.neighborFinset g ∩ A).card = A.card - 1 := by
    intro g₀ hg₀
    have hadd := Finset.add_sum_erase A (fun g => (G.neighborFinset g ∩ A).card) hg₀
    have hb : ∀ g ∈ A.erase g₀, (G.neighborFinset g ∩ A).card ≤ A.card - 1 :=
      fun g hg => hNAle g (Finset.mem_of_mem_erase hg)
    have herase_le : ∑ g ∈ A.erase g₀, (G.neighborFinset g ∩ A).card
        ≤ (A.card - 1) * (A.card - 1) := by
      calc ∑ g ∈ A.erase g₀, (G.neighborFinset g ∩ A).card
          ≤ (A.erase g₀).card • (A.card - 1) := Finset.sum_le_card_nsmul _ _ _ hb
        _ = (A.card - 1) * (A.card - 1) := by rw [Finset.card_erase_of_mem hg₀, smul_eq_mul]
    have hub := hNAle g₀ hg₀
    have hcase : A.card = 3 ∨ A.card = 4 := by omega
    rcases hcase with h3 | h4
    · rw [h3] at herase_le hub hSANA_ge ⊢; omega
    · rw [h4] at herase_le hub hSANA_ge ⊢; omega
  have hadj : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → G.Adj a b := by
    intro a ha b hb hab
    have heq : G.neighborFinset a ∩ A = A.erase a := by
      apply Finset.eq_of_subset_of_card_le
      · intro w hw
        rw [Finset.mem_inter, G.mem_neighborFinset] at hw
        exact Finset.mem_erase.mpr ⟨fun e => G.irrefl (e ▸ hw.1), hw.2⟩
      · rw [Finset.card_erase_of_mem ha]; exact le_of_eq (hclique a ha).symm
    have hbmem : b ∈ G.neighborFinset a ∩ A := by
      rw [heq]; exact Finset.mem_erase.mpr ⟨hab.symm, hb⟩
    rw [Finset.mem_inter, G.mem_neighborFinset] at hbmem
    exact hbmem.1
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < A.card)
  have hpair : ({a, b} : Finset (Fin 16)).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simp [hab]), Finset.card_singleton]
  have hex : ∃ c : Fin 16, c ∈ A ∧ c ∉ ({a, b} : Finset (Fin 16)) := by
    by_contra hcon
    push Not at hcon
    have hsub : A ⊆ ({a, b} : Finset (Fin 16)) := fun c hc => hcon c hc
    have := Finset.card_le_card hsub
    rw [hpair] at this; omega
  obtain ⟨c, hcA, hcpair⟩ := hex
  simp only [Finset.mem_insert, Finset.mem_singleton] at hcpair
  push Not at hcpair
  obtain ⟨hca, hcb⟩ := hcpair
  exact ⟨a, b, c, ha, hb, hcA, hab, Ne.symm hca, Ne.symm hcb,
    hadj a ha b hb hab, hadj a ha c hcA (Ne.symm hca), hadj b hb c hcA (Ne.symm hcb)⟩

/-- **Hub-triangle existence in the `n = 16`, `|D| = 8`, `e(M) = 2`, single-`P₃`-cherry corner.**
Under the residual hypotheses (eight degree-`4` hubs, `6` hub-hub edges, `M = P₃` cherry `x–y–z`
with five `M`-isolated twins, and the falsity of `SingleVertexConfig`/`TwoTwinConfig`/
`TwoHubConfig`), the graph contains three pairwise-adjacent hubs avoiding the cherry, packaged as
`HubTriangleConfig G`.  The single cherry makes every avoider fully free (`int ≥ 3`); with
`∑ int = 12` the avoider set (`≥ 3` members) is pinned to a `3`/`4`-clique, giving the triangle. -/
theorem exists_hub_triangle_config_cherry_residual_sixteen (G : SimpleGraph (Fin 16))
    (D Iso : Finset (Fin 16)) (x y z : Fin 16)
    (hmemD : ∀ v : Fin 16, v ∈ D ↔ G.degree v = 3)
    (hIsodef : Iso = D.filter (fun v => (G.neighborFinset v ∩ D).card = 0))
    (hIsoprop : ∀ v ∈ Iso, G.degree v = 3 ∧ (∀ w : Fin 16, G.Adj v w → G.degree w ≠ 3))
    (hisochar : ∀ w : Fin 16, w ∈ D → w ≠ x → w ≠ y → w ≠ z → w ∈ Iso)
    (hcov : ∀ p q : Fin 16, p ∈ D → q ∈ D → G.Adj p q → p = y ∨ q = y)
    (hNyD : G.neighborFinset y ∩ D = {x, z})
    (hxdeg : G.degree x = 3) (hydeg : G.degree y = 3) (hzdeg : G.degree z = 3)
    (haxy : G.Adj x y) (hayz : G.Adj y z) (hnxz : ¬G.Adj x z) (hxz : x ≠ z)
    (hdeg4 : ∀ w : Fin 16, w ∈ Dᶜ → G.degree w = 4)
    (hD8 : D.card = 8)
    (_hsv : ¬SingleVertexConfig G) (htt : ¬TwoTwinConfig G) (_hth : ¬TwoHubConfig G) :
    HubTriangleConfig G := by
  classical
  have hxD : x ∈ D := (hmemD x).mpr hxdeg
  have hyD : y ∈ D := (hmemD y).mpr hydeg
  have hzD : z ∈ D := (hmemD z).mpr hzdeg
  have hxy : x ≠ y := haxy.ne
  have hzy : z ≠ y := hayz.ne'
  -- **(W) [from `¬TwoTwinConfig`].**  Any cherry-avoiding hub has `≤ 1` `M`-isolated-twin
  -- neighbour: two such twins plus the hub and the cherry assemble a `TwoTwinConfig`.
  have hW : ∀ g : Fin 16, g ∈ Dᶜ → (¬G.Adj g x ∧ ¬G.Adj g y ∧ ¬G.Adj g z) →
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
  -- Structural counts: eight hubs, five `M`-isolated twins.
  obtain ⟨hDeq, hdisj⟩ :=
    cherry_partition G D Iso x y z hIsodef hisochar hxD hyD hzD haxy hayz
  have hDc8 : Dᶜ.card = 8 := by rw [Finset.card_compl, Fintype.card_fin, hD8]
  have hIso5 : Iso.card = 5 := by
    have hPcard : ({x, y, z} : Finset (Fin 16)).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [hxy, hxz]),
        Finset.card_insert_of_notMem (by simp [Ne.symm hzy]), Finset.card_singleton]
    have hcardU := Finset.card_union_of_disjoint hdisj
    rw [hDeq, hPcard, hD8] at hcardU
    omega
  -- Cherry hub-incidence counts and the residual sums (`∑ int = 12`).
  obtain ⟨hcx, hcy, hcz⟩ :=
    cherry_leaf_card G D x y z hcov hNyD hxD hyD hzD haxy hayz hxy hzy hxz hxdeg hydeg hzdeg
  obtain ⟨hsumP, hsumI, hper⟩ :=
    cherry_residual_sums G D Iso x y z hIsodef hIsoprop hisochar hxD hyD hzD haxy hayz
      hxy hzy hxz hdeg4 hcx hcy hcz hIso5
  have hSum12 : ∑ w ∈ Dᶜ, (G.neighborFinset w ∩ Dᶜ).card = 12 := by
    have htot : ∑ g ∈ Dᶜ, ((G.neighborFinset g ∩ ({x, y, z} : Finset (Fin 16))).card
        + (G.neighborFinset g ∩ Iso).card + (G.neighborFinset g ∩ Dᶜ).card)
        = ∑ _g ∈ Dᶜ, 4 := Finset.sum_congr rfl hper
    rw [Finset.sum_const, smul_eq_mul, hDc8, Finset.sum_add_distrib, Finset.sum_add_distrib,
      hsumP, hsumI] at htot
    omega
  -- The cherry-avoider set, with `≥ 3` members each of internal degree `≥ 3`.
  set A := Dᶜ.filter (fun g => ¬G.Adj g x ∧ ¬G.Adj g y ∧ ¬G.Adj g z) with hAdef
  have hAsub : A ⊆ Dᶜ := Finset.filter_subset _ _
  have hA3 : 3 ≤ A.card := by
    rw [hAdef]; exact cherry_avoiders_ge_three G D x y z hDc8 hcx hcy hcz
  have hclassP : ∀ v : Fin 16, v ∈ D → v = x ∨ v = y ∨ v = z ∨ v ∈ Iso := by
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
  -- Force a triangle among the avoiders and package it as `HubTriangleConfig`.
  obtain ⟨a, b, c, haA, hbA, hcA, hab, hac, hbc, hadj_ab, hadj_ac, hadj_bc⟩ :=
    cherry_avoider_triangle G Dᶜ A hAsub hA3 hAint hSum12
  have getA : ∀ g : Fin 16, g ∈ A → g ∈ Dᶜ ∧ ¬G.Adj g x ∧ ¬G.Adj g y ∧ ¬G.Adj g z := by
    intro g hg; rw [hAdef, Finset.mem_filter] at hg; exact hg
  obtain ⟨haDc, hax, hay, haz⟩ := getA a haA
  obtain ⟨hbDc, hbx, hby, hbz⟩ := getA b hbA
  obtain ⟨hcDc, hcxx, hcyy, hczz⟩ := getA c hcA
  have hubne : ∀ g : Fin 16, g ∈ Dᶜ → g ≠ x ∧ g ≠ y ∧ g ≠ z := by
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

end N16

end ACMax
