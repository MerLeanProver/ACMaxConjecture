import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N19.Core
import ACMaxConjecture.SmallCases.N19.Core
import ACMaxConjecture.SmallCases.StarCertificates
import ACMaxConjecture.SmallCases.N19.HubTriangleStruct
import ACMaxConjecture.SmallCases.N19.HubTriangleFF
import ACMaxConjecture.SmallCases.N19.Align8Helpers
import ACMaxConjecture.SmallCases.N19.BipartiteAvoiderTwoHub

/-!
# Hub-triangle existence for the `n = 19`, `e(M) = 2`, single-`P₃`-cherry residual corner

This file isolates the hub-triangle existence obligation in the `e(M) = 2`, `|D| = 8`
(`|Hub| = 11`, all-degree-`4`) corner where the residual `M` is a **single `P₃` cherry** `x–y–z`
(`y` the middle, in-`M` degree `2`; `x, z` the endpoints, in-`M` degree `1`).  It is the
`n = 19` port of `TwinCert18HubTriangleCherry`.

## The residual configuration
* `D` = the degree-`3` vertices, `|D| = 8`; `Dᶜ` = the **eleven** hubs, all of degree `4` (`hdeg4`).
* `M = P₃` cherry `x–y–z` (`hNyD : N(y) ∩ D = {x, z}`, `haxy`, `hayz`), plus `|Iso| = 5`
  `M`-isolated degree-`3` twins (`Iso`).

## The target
`HubTriangleConfig G`: three pairwise-adjacent hubs avoiding the cherry `{x, y, z}`; their degree
sum is `12 ≤ 13` automatically.

## `n = 19` delta (the triangle-extraction core)
Every hub meets `≤ 1` cherry vertex (good triangle `Σ ≤ 10` / good `C₄` `Σ = 13`); since the cherry
collects exactly `2 + 1 + 2 = 5` hub-incidences, **exactly five** hubs are cherry-incident, so the
avoider set is pinned to `|A| = 6` (no longer the `n = 18` `|A| ∈ {5, 6}` split).  When the in-`A`
edge mass `∑_A(N ∩ A) ≥ 19` a Mantel triangle is forced (`mantel_six_triangle`); otherwise the
avoiders form a triangle-free `C₆`/`K_{3,3}`, split on whether two avoiders share an `M`-isolated
twin: a shared twin assembles a `SingleVertexConfig` (contradicting `¬SingleVertexConfig`), while
the distinct-twin case assembles a `TwoHubConfig`.  The `|A| = 6` distinct-twin `TwoHubConfig`
assembly is the genuine `n = 19` boundary, now closed axiom-clean by
`cherry_C6_distinct_twin_twoHub_nineteen` (the `|S| = 5`, `|Iso| = 5`, `∑_Dᶜ iso = 15` counts are
unchanged from `|A| = 5`, so the `C₅` extraction ports verbatim with `|A| = 6`, `|Dᶜ| = 11`).
-/

namespace ACMax

open scoped Classical

namespace N19

/-- **Cherry / Iso partition of `D`.**  The three cherry vertices and the `M`-isolated twins
partition `D`: `{x, y, z} ∪ Iso = D` and the two parts are disjoint. -/
theorem cherry_partition (G : SimpleGraph (Fin 19)) (D Iso : Finset (Fin 19)) (x y z : Fin 19)
    (hIsodef : Iso = D.filter (fun v => (G.neighborFinset v ∩ D).card = 0))
    (hisochar : ∀ w : Fin 19, w ∈ D → w ≠ x → w ≠ y → w ≠ z → w ∈ Iso)
    (hxD : x ∈ D) (hyD : y ∈ D) (hzD : z ∈ D)
    (haxy : G.Adj x y) (hayz : G.Adj y z) :
    ({x, y, z} : Finset (Fin 19)) ∪ Iso = D ∧ Disjoint ({x, y, z} : Finset (Fin 19)) Iso := by
  classical
  set P : Finset (Fin 19) := {x, y, z} with hP
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
theorem cherry_leaf_card (G : SimpleGraph (Fin 19)) (D : Finset (Fin 19)) (x y z : Fin 19)
    (hcov : ∀ p q : Fin 19, p ∈ D → q ∈ D → G.Adj p q → p = y ∨ q = y)
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
theorem cherry_residual_sums (G : SimpleGraph (Fin 19)) (D Iso : Finset (Fin 19)) (x y z : Fin 19)
    (hIsodef : Iso = D.filter (fun v => (G.neighborFinset v ∩ D).card = 0))
    (hIsoprop : ∀ v ∈ Iso, G.degree v = 3 ∧ (∀ w : Fin 19, G.Adj v w → G.degree w ≠ 3))
    (hisochar : ∀ w : Fin 19, w ∈ D → w ≠ x → w ≠ y → w ≠ z → w ∈ Iso)
    (hxD : x ∈ D) (hyD : y ∈ D) (hzD : z ∈ D)
    (haxy : G.Adj x y) (hayz : G.Adj y z)
    (hxy : x ≠ y) (hzy : z ≠ y) (hxz : x ≠ z)
    (hdeg4 : ∀ w : Fin 19, w ∈ Dᶜ → G.degree w = 4)
    (hcx : (G.neighborFinset x ∩ Dᶜ).card = 2) (hcy : (G.neighborFinset y ∩ Dᶜ).card = 1)
    (hcz : (G.neighborFinset z ∩ Dᶜ).card = 2) (hIso5 : Iso.card = 5) :
    (∑ g ∈ Dᶜ, (G.neighborFinset g ∩ ({x, y, z} : Finset (Fin 19))).card = 5) ∧
      (∑ g ∈ Dᶜ, (G.neighborFinset g ∩ Iso).card = 15) ∧
      (∀ g ∈ Dᶜ, (G.neighborFinset g ∩ ({x, y, z} : Finset (Fin 19))).card
        + (G.neighborFinset g ∩ Iso).card + (G.neighborFinset g ∩ Dᶜ).card = 4) := by
  classical
  set P : Finset (Fin 19) := {x, y, z} with hP
  have hsum_path : ∑ g ∈ Dᶜ, (G.neighborFinset g ∩ P).card = 5 := by
    rw [cross_count_nineteen G Dᶜ P, hP, Finset.sum_insert (by simp [hxy, hxz]),
      Finset.sum_insert (by simp [Ne.symm hzy]), Finset.sum_singleton]
    omega
  have hsum_iso : ∑ g ∈ Dᶜ, (G.neighborFinset g ∩ Iso).card = 15 := by
    rw [cross_count_nineteen G Dᶜ Iso]
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

/-- **Distinct-twin `TwoHubConfig` assembly for the `|A| = 5` `C₅` cherry corner.** -/
theorem cherry_C6_distinct_twin_twoHub_nineteen (G : SimpleGraph (Fin 19))
    (D Iso A : Finset (Fin 19)) (x y z : Fin 19)
    (hIsodef : Iso = D.filter (fun v => (G.neighborFinset v ∩ D).card = 0))
    (hIsoprop : ∀ v ∈ Iso, G.degree v = 3 ∧ (∀ w : Fin 19, G.Adj v w → G.degree w ≠ 3))
    (hIsoD : Iso ⊆ D)
    (hdeg4 : ∀ w : Fin 19, w ∈ Dᶜ → G.degree w = 4)
    (hC4 : ¬∃ a b c d : Fin 19, ({a, b, c, d} : Finset (Fin 19)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (hAsub : A ⊆ Dᶜ) (hcard6 : A.card = 6) (hIso5 : Iso.card = 5) (hDc11 : Dᶜ.card = 11)
    (_havoid : ∀ g ∈ A, ¬G.Adj g x ∧ ¬G.Adj g y ∧ ¬G.Adj g z)
    (hScherry : ∀ h : Fin 19, h ∈ Dᶜ → h ∉ A → G.Adj h x ∨ G.Adj h y ∨ G.Adj h z)
    (hsplit4 : ∀ h : Fin 19, h ∈ Dᶜ → (G.neighborFinset h ∩ ({x, y, z} : Finset (Fin 19))).card
      + (G.neighborFinset h ∩ Iso).card + (G.neighborFinset h ∩ Dᶜ).card = 4)
    (hdistinct : ∀ t ∈ Iso, (G.neighborFinset t ∩ A).card ≤ 1)
    (hisoSum : ∑ g ∈ Dᶜ, (G.neighborFinset g ∩ Iso).card = 15) :
    TwoHubConfig G := by
  classical
  set S : Finset (Fin 19) := Dᶜ \ A with hSdef
  have hSsub : S ⊆ Dᶜ := by rw [hSdef]; exact Finset.sdiff_subset
  have hScard : S.card = 5 := by
    have h := Finset.card_sdiff_add_card_inter Dᶜ A
    rw [Finset.inter_eq_right.mpr hAsub, hDc11, hcard6] at h
    rw [hSdef]; omega
  -- Every `S`-hub meets a cherry vertex, so its cherry incidence is `≥ 1`.
  have hcher1 : ∀ h : Fin 19, h ∈ S →
      1 ≤ (G.neighborFinset h ∩ ({x, y, z} : Finset (Fin 19))).card := by
    intro h hh
    rw [hSdef, Finset.mem_sdiff] at hh
    obtain ⟨hhDc, hhA⟩ := hh
    rcases hScherry h hhDc hhA with hax | hay | haz
    · exact Finset.card_pos.mpr
        ⟨x, by rw [Finset.mem_inter, G.mem_neighborFinset]; exact ⟨hax, by simp⟩⟩
    · exact Finset.card_pos.mpr
        ⟨y, by rw [Finset.mem_inter, G.mem_neighborFinset]; exact ⟨hay, by simp⟩⟩
    · exact Finset.card_pos.mpr
        ⟨z, by rw [Finset.mem_inter, G.mem_neighborFinset]; exact ⟨haz, by simp⟩⟩
  -- Hence `isoDeg h + internalDeg h ≤ 3` for every `S`-hub.
  have hisoint : ∀ h : Fin 19, h ∈ S → (G.neighborFinset h ∩ Iso).card
      + (G.neighborFinset h ∩ Dᶜ).card ≤ 3 := by
    intro h hh
    have h4 := hsplit4 h (hSsub hh)
    have h1 := hcher1 h hh
    omega
  -- An `isoDeg = 3` hub has hub-internal degree `0`, hence is non-adjacent to every hub.
  have hinternal0 : ∀ h : Fin 19, h ∈ S → (G.neighborFinset h ∩ Iso).card = 3 →
      ∀ h' : Fin 19, h' ∈ Dᶜ → ¬G.Adj h h' := by
    intro h hh hiso3 h' hh'Dc hadj
    have hle := hisoint h hh
    have hpos : 1 ≤ (G.neighborFinset h ∩ Dᶜ).card :=
      Finset.card_pos.mpr
        ⟨h', by rw [Finset.mem_inter, G.mem_neighborFinset]; exact ⟨hadj, hh'Dc⟩⟩
    omega
  -- An `isoDeg = 2` hub has hub-internal degree `≤ 1`.
  have hint_le1 : ∀ h : Fin 19, h ∈ S → (G.neighborFinset h ∩ Iso).card = 2 →
      (G.neighborFinset h ∩ Dᶜ).card ≤ 1 := by
    intro h hh hiso2
    have hle := hisoint h hh
    omega
  -- Each twin meets `≥ 2` of the five `S`-hubs.
  have hdt : ∀ t : Fin 19, t ∈ Iso → 2 ≤ (G.neighborFinset t ∩ S).card := by
    intro t ht
    have h3 := (iso_three_hub_nbrs G D Iso hIsodef hIsoprop t ht).2
    have hA1 := hdistinct t ht
    have hpart : (G.neighborFinset t ∩ A).card + (G.neighborFinset t ∩ S).card
        = (G.neighborFinset t ∩ Dᶜ).card := by
      rw [hSdef, ← Finset.card_union_of_disjoint, ← Finset.inter_union_distrib_left,
        Finset.union_sdiff_of_subset hAsub]
      apply Finset.disjoint_left.mpr
      intro w hw hw'
      rw [Finset.mem_inter] at hw hw'
      exact (Finset.mem_sdiff.mp hw'.2).2 hw.2
    omega
  -- The good-`C₄` shared-twin bound on non-adjacent `S`-hub pairs.
  have hshare1 : ∀ p : Fin 19, p ∈ S → ∀ q : Fin 19, q ∈ S → p ≠ q → ¬G.Adj p q →
      (G.neighborFinset p ∩ G.neighborFinset q ∩ Iso).card ≤ 1 := by
    intro p hp q hq hpq hnadj
    exact nonadj_hubs_share_le_one_iso G D Iso hC4 hIsoD hIsoprop hdeg4 p q
      (hSsub hp) (hSsub hq) hpq hnadj
  -- Sharp `sdiff` bound: private twins of `p` against `q`.
  have hsd : ∀ p q : Fin 19, (G.neighborFinset p ∩ Iso).card
      - (G.neighborFinset p ∩ G.neighborFinset q ∩ Iso).card
      ≤ ((G.neighborFinset p ∩ Iso) \ G.neighborFinset q).card := by
    intro p q
    have heq : (G.neighborFinset p ∩ Iso) ∩ G.neighborFinset q
        = G.neighborFinset p ∩ G.neighborFinset q ∩ Iso := by
      ext w; simp only [Finset.mem_inter]; tauto
    have h2 := Finset.card_sdiff_add_card_inter (G.neighborFinset p ∩ Iso) (G.neighborFinset q)
    rw [heq] at h2; omega
  -- Twin-incidence sums: `∑_A isoDeg ≤ 5`, hence `∑_S isoDeg ≥ 10`.
  have hAiso_le : ∑ g ∈ A, (G.neighborFinset g ∩ Iso).card ≤ 5 := by
    rw [cross_count_nineteen G A Iso]
    calc ∑ t ∈ Iso, (G.neighborFinset t ∩ A).card ≤ ∑ _t ∈ Iso, 1 :=
          Finset.sum_le_sum (fun t ht => hdistinct t ht)
      _ = 5 := by rw [Finset.sum_const, hIso5, smul_eq_mul, Nat.mul_one]
  have hSiso_ge : 10 ≤ ∑ h ∈ S, (G.neighborFinset h ∩ Iso).card := by
    have hs := Finset.sum_sdiff (f := fun g => (G.neighborFinset g ∩ Iso).card) hAsub
    rw [hisoSum] at hs
    rw [hSdef]; omega
  -- The good non-adjacent pair, each side carrying two private `M`-isolated twins.
  have hpair : ∃ h₁ ∈ S, ∃ h₂ ∈ S, h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card := by
    set R : Finset (Fin 19) := S.filter (fun h => 3 ≤ (G.neighborFinset h ∩ Iso).card) with hRdef
    by_cases hRcase : 2 ≤ R.card
    · -- **Case A.**  Two `isoDeg = 3` hubs: both hub-internal-free, hence non-adjacent.
      obtain ⟨h₁, hh1R, h₂, hh2R, hne⟩ := Finset.one_lt_card.mp hRcase
      have hh1n : h₁ ∈ S := Finset.mem_of_mem_filter _ hh1R
      have hh2n : h₂ ∈ S := Finset.mem_of_mem_filter _ hh2R
      have hi1 : (G.neighborFinset h₁ ∩ Iso).card = 3 := by
        have := (Finset.mem_filter.mp hh1R).2; have hle := hisoint h₁ hh1n; omega
      have hi2 : (G.neighborFinset h₂ ∩ Iso).card = 3 := by
        have := (Finset.mem_filter.mp hh2R).2; have hle := hisoint h₂ hh2n; omega
      have hnadj : ¬G.Adj h₁ h₂ := hinternal0 h₁ hh1n hi1 h₂ (hSsub hh2n)
      have hs12 := hshare1 h₁ hh1n h₂ hh2n hne hnadj
      have hs21 := hshare1 h₂ hh2n h₁ hh1n (Ne.symm hne) (fun a => hnadj a.symm)
      refine ⟨h₁, hh1n, h₂, hh2n, hne, hnadj, ?_, ?_⟩
      · have := hsd h₁ h₂; omega
      · have := hsd h₂ h₁; omega
    · -- **Case B.**  At most one `isoDeg = 3` hub, so `∑_S isoDeg ≤ 11`.
      have hRle1 : R.card ≤ 1 := by omega
      set Tval : ℕ := ∑ h ∈ S, (G.neighborFinset h ∩ Iso).card with hTvaldef
      have hT11 : Tval ≤ 11 := by
        have hsplit := Finset.sum_filter_add_sum_filter_not S
          (fun h => 3 ≤ (G.neighborFinset h ∩ Iso).card) (fun h => (G.neighborFinset h ∩ Iso).card)
        rw [← hRdef, ← hTvaldef] at hsplit
        set NR : Finset (Fin 19) :=
          S.filter (fun h => ¬3 ≤ (G.neighborFinset h ∩ Iso).card) with hNRdef
        have hRsum : (∑ h ∈ R, (G.neighborFinset h ∩ Iso).card) ≤ 3 * R.card := by
          calc (∑ h ∈ R, (G.neighborFinset h ∩ Iso).card) ≤ ∑ _h ∈ R, 3 :=
                Finset.sum_le_sum (fun h hh => by
                  have := hisoint h (Finset.mem_of_mem_filter _ hh); omega)
            _ = 3 * R.card := by rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
        have hNRsum : (∑ h ∈ NR, (G.neighborFinset h ∩ Iso).card) ≤ 2 * NR.card := by
          calc (∑ h ∈ NR, (G.neighborFinset h ∩ Iso).card) ≤ ∑ _h ∈ NR, 2 :=
                Finset.sum_le_sum (fun h hh => by
                  have := (Finset.mem_filter.mp hh).2; omega)
            _ = 2 * NR.card := by rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
        have hcardsum : R.card + NR.card = 5 := by
          have h : R.card + NR.card = S.card := Finset.card_filter_add_card_filter_not _
          rw [hScard] at h; exact h
        omega
      -- The `isoDeg ≥ 2` hubs.
      set Q : Finset (Fin 19) := S.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card) with hQdef
      have hQsub : Q ⊆ S := Finset.filter_subset _ _
      by_cases hQ5 : Q.card = 5
      · -- **Sub-case `|Q| = 5`:** every `S`-hub has `isoDeg ≥ 2`.
        have hQeqS : Q = S := Finset.eq_of_subset_of_card_le hQsub (by rw [hScard, hQ5])
        have hiso2 : ∀ p : Fin 19, p ∈ S → 2 ≤ (G.neighborFinset p ∩ Iso).card := by
          intro p hp
          have hpQ : p ∈ Q := by rw [hQeqS]; exact hp
          exact (Finset.mem_filter.mp hpQ).2
        by_contra hcon
        -- No good pair ⟹ every non-adjacent distinct `S`-pair shares a twin.
        have hsg : ∀ p : Fin 19, p ∈ S → ∀ q : Fin 19, q ∈ S → p ≠ q → ¬G.Adj p q →
            1 ≤ (G.neighborFinset p ∩ G.neighborFinset q ∩ Iso).card := by
          intro p hp q hq hpq hnadj
          by_contra hs0
          rw [not_le, Nat.lt_one_iff] at hs0
          refine hcon ⟨p, hp, q, hq, hpq, hnadj, ?_, ?_⟩
          · have h1 := hsd p q; have h2 := hiso2 p hp; omega
          · have h1 := hsd q p; have h2 := hiso2 q hq
            have hcomm : (G.neighborFinset q ∩ G.neighborFinset p ∩ Iso).card = 0 := by
              rw [show G.neighborFinset q ∩ G.neighborFinset p
                = G.neighborFinset p ∩ G.neighborFinset q from Finset.inter_comm _ _]; exact hs0
            omega
        -- Exact double count: `∑∑ share + 30 = 5·Tval`.
        have hcross : ∑ t ∈ Iso, (G.neighborFinset t ∩ S).card = Tval :=
          (cross_count_nineteen G S Iso).symm
        have hsq : ∑ t ∈ Iso, (G.neighborFinset t ∩ S).card * (G.neighborFinset t ∩ S).card + 30
            = 5 * Tval := by
          have hper : ∀ t ∈ Iso, (G.neighborFinset t ∩ S).card * (G.neighborFinset t ∩ S).card + 6
              = 5 * (G.neighborFinset t ∩ S).card := by
            intro t ht
            have h2 := hdt t ht
            have h3 : (G.neighborFinset t ∩ S).card ≤ 3 := by
              calc (G.neighborFinset t ∩ S).card ≤ (G.neighborFinset t ∩ Dᶜ).card :=
                    Finset.card_le_card (Finset.inter_subset_inter (Finset.Subset.refl _) hSsub)
                _ = 3 := (iso_three_hub_nbrs G D Iso hIsodef hIsoprop t ht).2
            obtain hd | hd : (G.neighborFinset t ∩ S).card = 2 ∨ (G.neighborFinset t ∩ S).card = 3 :=
              by omega
            · rw [hd]
            · rw [hd]
          have hsum : ∑ t ∈ Iso, ((G.neighborFinset t ∩ S).card * (G.neighborFinset t ∩ S).card + 6)
              = ∑ t ∈ Iso, 5 * (G.neighborFinset t ∩ S).card := Finset.sum_congr rfl hper
          rw [Finset.sum_add_distrib, Finset.sum_const, hIso5, smul_eq_mul, ← Finset.mul_sum,
            hcross] at hsum
          omega
        have hexact : (∑ p ∈ S, ∑ q ∈ S,
            (G.neighborFinset p ∩ G.neighborFinset q ∩ Iso).card) + 30 = 5 * Tval := by
          rw [cherry_double_count G S Iso]; exact hsq
        -- Lower bound: `∑∑ share ≥ 2·Tval + 5`.
        have hrow : ∀ p : Fin 19, p ∈ S → 2 * (G.neighborFinset p ∩ Iso).card + 1
            ≤ ∑ q ∈ S, (G.neighborFinset p ∩ G.neighborFinset q ∩ Iso).card := by
          intro p hp
          have herase := Finset.add_sum_erase S
            (fun q => (G.neighborFinset p ∩ G.neighborFinset q ∩ Iso).card) hp
          have hpp : (G.neighborFinset p ∩ G.neighborFinset p ∩ Iso).card
              = (G.neighborFinset p ∩ Iso).card := by rw [Finset.inter_self]
          have hlow : ((S.erase p).filter (fun q => ¬G.Adj p q)).card
              ≤ ∑ q ∈ S.erase p, (G.neighborFinset p ∩ G.neighborFinset q ∩ Iso).card := by
            rw [Finset.card_filter]
            apply Finset.sum_le_sum
            intro q hq
            rw [Finset.mem_erase] at hq
            by_cases hadj : G.Adj p q
            · simp [hadj]
            · simp only [hadj, if_true, not_false_iff]
              exact hsg p hp q (Finset.mem_of_mem_erase (Finset.mem_erase.mpr hq))
                (Ne.symm hq.1) hadj
          have hfcard : 1 + (G.neighborFinset p ∩ Iso).card
              ≤ ((S.erase p).filter (fun q => ¬G.Adj p q)).card := by
            have hcf : ((S.erase p).filter (fun q => G.Adj p q)).card
                + ((S.erase p).filter (fun q => ¬G.Adj p q)).card = (S.erase p).card :=
              Finset.card_filter_add_card_filter_not _
            have heraseC : (S.erase p).card = 4 := by rw [Finset.card_erase_of_mem hp, hScard]
            have hadjle : ((S.erase p).filter (fun q => G.Adj p q)).card
                ≤ (G.neighborFinset p ∩ Dᶜ).card := by
              apply Finset.card_le_card
              intro q hq
              rw [Finset.mem_filter, Finset.mem_erase] at hq
              rw [Finset.mem_inter, G.mem_neighborFinset]
              exact ⟨hq.2, hSsub hq.1.2⟩
            have hii := hisoint p hp
            omega
          omega
        have hlb : 2 * Tval + 5 ≤ ∑ p ∈ S, ∑ q ∈ S,
            (G.neighborFinset p ∩ G.neighborFinset q ∩ Iso).card := by
          have hsumform : ∑ p ∈ S, (2 * (G.neighborFinset p ∩ Iso).card + 1) = 2 * Tval + 5 := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, hScard, smul_eq_mul,
              ← hTvaldef]
          rw [← hsumform]
          exact Finset.sum_le_sum hrow
        omega
      · -- **Sub-case `|Q| = 4`:** the rigid `isoDeg`-multiset `(1, 2, 2, 2, 3)` (`Tval = 10`).  The
        -- unique `isoDeg = 1` hub `h₀` forces one twin `t₀` to meet a single `Q`-hub, sharpening the
        -- `Q`-double count to `∑_{p,q∈Q} share ≤ 2·T_Q − 1 < 2·T_Q ≤ ∑_{p,q∈Q} share`.
        have hRsubQ : R ⊆ Q := by
          intro a ha
          rw [hQdef, Finset.mem_filter]
          exact ⟨Finset.mem_of_mem_filter _ ha, by have := (Finset.mem_filter.mp ha).2; omega⟩
        -- Per-hub `isoDeg ≤ 1 + [h∈Q] + [h∈R]`, giving `Tval ≤ 5 + |Q| + |R|`.
        have hpt : ∀ h ∈ S, (G.neighborFinset h ∩ Iso).card
            ≤ 1 + ((if h ∈ Q then 1 else 0) + (if h ∈ R then 1 else 0)) := by
          intro h hh
          by_cases hQm : h ∈ Q
          · by_cases hRm : h ∈ R
            · simp only [hQm, hRm, if_true]; have := hisoint h hh; omega
            · simp only [hQm, hRm, if_true, if_false]
              have hnr : ¬3 ≤ (G.neighborFinset h ∩ Iso).card := fun hge =>
                hRm (by rw [hRdef, Finset.mem_filter]; exact ⟨hh, hge⟩)
              omega
          · have hRm : h ∉ R := fun ha => hQm (hRsubQ ha)
            simp only [hQm, hRm, if_false]
            have hnq : ¬2 ≤ (G.neighborFinset h ∩ Iso).card := fun hge =>
              hQm (by rw [hQdef, Finset.mem_filter]; exact ⟨hh, hge⟩)
            omega
        have hbound : Tval ≤ 5 + (Q.card + R.card) := by
          have hsumb : Tval ≤ ∑ h ∈ S,
              (1 + ((if h ∈ Q then 1 else 0) + (if h ∈ R then 1 else 0))) := by
            rw [hTvaldef]; exact Finset.sum_le_sum hpt
          have hev : ∑ h ∈ S, (1 + ((if h ∈ Q then 1 else 0) + (if h ∈ R then 1 else 0)))
              = 5 + (Q.card + R.card) := by
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, hScard,
              smul_eq_mul, Finset.sum_boole, Finset.sum_boole, Finset.filter_mem_eq_inter,
              Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hQsub,
              Finset.inter_eq_right.mpr (hRsubQ.trans hQsub)]
            push_cast
            ring
          omega
        have hQcard5 : Q.card ≤ 5 := by rw [← hScard]; exact Finset.card_le_card hQsub
        have hQcard4 : Q.card = 4 := by omega
        have hTval10 : Tval = 10 := by omega
        have hRcard1 : R.card = 1 := by omega
        -- Every twin meets exactly two `S`-hubs.
        have hdt2 : ∀ t : Fin 19, t ∈ Iso → (G.neighborFinset t ∩ S).card = 2 := by
          have hsumdt : ∑ t ∈ Iso, (G.neighborFinset t ∩ S).card = 10 := by
            rw [← cross_count_nineteen G S Iso, ← hTvaldef]; exact hTval10
          intro t ht
          by_contra hne
          have hge3 : 3 ≤ (G.neighborFinset t ∩ S).card := by have := hdt t ht; omega
          have hbig : 11 ≤ ∑ t' ∈ Iso, (G.neighborFinset t' ∩ S).card := by
            rw [← Finset.add_sum_erase Iso (fun t' => (G.neighborFinset t' ∩ S).card) ht]
            have hrest : 8 ≤ ∑ t' ∈ Iso.erase t, (G.neighborFinset t' ∩ S).card := by
              have h := Finset.card_nsmul_le_sum (Iso.erase t)
                (fun t' => (G.neighborFinset t' ∩ S).card) 2
                (fun t' ht' => hdt t' (Finset.mem_of_mem_erase ht'))
              simp only [smul_eq_mul] at h
              rw [Finset.card_erase_of_mem ht, hIso5] at h; omega
            omega
          omega
        -- The unique `isoDeg = 1` hub `h₀` and its twin `t₀`.
        have hSQcard : (S \ Q).card = 1 := by
          have h := Finset.card_sdiff_add_card_inter S Q
          rw [Finset.inter_eq_right.mpr hQsub, hScard, hQcard4] at h
          omega
        obtain ⟨h₀, hh0eq⟩ := Finset.card_eq_one.mp hSQcard
        have hh0mem : h₀ ∈ S \ Q := by rw [hh0eq]; exact Finset.mem_singleton_self h₀
        have hh0S : h₀ ∈ S := (Finset.mem_sdiff.mp hh0mem).1
        have hh0Q : h₀ ∉ Q := (Finset.mem_sdiff.mp hh0mem).2
        have hiso0_le1 : (G.neighborFinset h₀ ∩ Iso).card ≤ 1 := by
          by_contra h; rw [not_le] at h
          exact hh0Q (by rw [hQdef, Finset.mem_filter]; exact ⟨hh0S, by omega⟩)
        have hQsum_ge : 8 ≤ ∑ q ∈ Q, (G.neighborFinset q ∩ Iso).card := by
          have h := Finset.card_nsmul_le_sum Q (fun q => (G.neighborFinset q ∩ Iso).card) 2
            (fun q hq => (Finset.mem_filter.mp hq).2)
          simp only [smul_eq_mul] at h
          rw [hQcard4] at h; omega
        have hQsum_le : ∑ q ∈ Q, (G.neighborFinset q ∩ Iso).card ≤ 8 + R.card := by
          have hptQ : ∀ q ∈ Q, (G.neighborFinset q ∩ Iso).card ≤ 2 + (if q ∈ R then 1 else 0) := by
            intro q hq
            by_cases hRm : q ∈ R
            · simp only [hRm, if_true]; have := hisoint q (hQsub hq); omega
            · simp only [hRm, if_false]
              have hnr : ¬3 ≤ (G.neighborFinset q ∩ Iso).card := fun hge =>
                hRm (by rw [hRdef, Finset.mem_filter]; exact ⟨hQsub hq, hge⟩)
              omega
          calc ∑ q ∈ Q, (G.neighborFinset q ∩ Iso).card
              ≤ ∑ q ∈ Q, (2 + (if q ∈ R then 1 else 0)) := Finset.sum_le_sum hptQ
            _ = 8 + R.card := by
                rw [Finset.sum_add_distrib, Finset.sum_const, hQcard4, smul_eq_mul,
                  Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hRsubQ]
                push_cast; ring
        have hsplitQ : (∑ q ∈ Q, (G.neighborFinset q ∩ Iso).card)
            + (G.neighborFinset h₀ ∩ Iso).card = Tval := by
          have hss := Finset.sum_sdiff (f := fun h => (G.neighborFinset h ∩ Iso).card) hQsub
          rw [hh0eq, Finset.sum_singleton] at hss
          rw [hTvaldef]; omega
        have hiso0 : (G.neighborFinset h₀ ∩ Iso).card = 1 := by omega
        obtain ⟨t₀, ht0eq⟩ := Finset.card_eq_one.mp hiso0
        have ht0mem : t₀ ∈ G.neighborFinset h₀ ∩ Iso := by
          rw [ht0eq]; exact Finset.mem_singleton_self t₀
        have ht0adj : G.Adj h₀ t₀ ∧ t₀ ∈ Iso := by
          rw [Finset.mem_inter, G.mem_neighborFinset] at ht0mem; exact ht0mem
        -- `t₀` meets exactly one `Q`-hub.
        have ht0Q1 : (G.neighborFinset t₀ ∩ Q).card = 1 := by
          have hpart : (G.neighborFinset t₀ ∩ Q).card + (G.neighborFinset t₀ ∩ (S \ Q)).card
              = (G.neighborFinset t₀ ∩ S).card := by
            rw [← Finset.card_union_of_disjoint, ← Finset.inter_union_distrib_left,
              Finset.union_sdiff_of_subset hQsub]
            apply Finset.disjoint_left.mpr
            intro w hw hw'
            rw [Finset.mem_inter] at hw hw'
            exact (Finset.mem_sdiff.mp hw'.2).2 hw.2
          have hsq1 : (G.neighborFinset t₀ ∩ (S \ Q)).card = 1 := by
            rw [hh0eq, Finset.inter_singleton_of_mem
              ((G.mem_neighborFinset _ _).mpr ht0adj.1.symm), Finset.card_singleton]
          have hsts : (G.neighborFinset t₀ ∩ S).card = 2 := hdt2 t₀ ht0adj.2
          omega
        -- Every twin meets `≤ 2` of the four `Q`-hubs.
        have htQ2 : ∀ t : Fin 19, t ∈ Iso → (G.neighborFinset t ∩ Q).card ≤ 2 := by
          intro t ht
          calc (G.neighborFinset t ∩ Q).card ≤ (G.neighborFinset t ∩ S).card :=
                Finset.card_le_card (Finset.inter_subset_inter (Finset.Subset.refl _) hQsub)
            _ = 2 := hdt2 t ht
        set TQ : ℕ := ∑ q ∈ Q, (G.neighborFinset q ∩ Iso).card with hTQdef
        have hcrossQ : ∑ t ∈ Iso, (G.neighborFinset t ∩ Q).card = TQ :=
          (cross_count_nineteen G Q Iso).symm
        -- Sharpened double count: `∑_t (N t ∩ Q)² + 1 ≤ 2·TQ`.
        have hRHSle : (∑ t ∈ Iso, (G.neighborFinset t ∩ Q).card * (G.neighborFinset t ∩ Q).card) + 1
            ≤ 2 * TQ := by
          have hsplit_erase : (G.neighborFinset t₀ ∩ Q).card
              + ∑ t ∈ Iso.erase t₀, (G.neighborFinset t ∩ Q).card = TQ := by
            rw [Finset.add_sum_erase Iso (fun t => (G.neighborFinset t ∩ Q).card) ht0adj.2]
            exact hcrossQ
          have hrest : ∑ t ∈ Iso.erase t₀,
              (G.neighborFinset t ∩ Q).card * (G.neighborFinset t ∩ Q).card
              ≤ 2 * ∑ t ∈ Iso.erase t₀, (G.neighborFinset t ∩ Q).card := by
            rw [Finset.mul_sum]
            apply Finset.sum_le_sum
            intro t ht'
            have h2 := htQ2 t (Finset.mem_of_mem_erase ht')
            nlinarith [h2]
          have ht0sq : (G.neighborFinset t₀ ∩ Q).card * (G.neighborFinset t₀ ∩ Q).card = 1 := by
            rw [ht0Q1]
          rw [← Finset.add_sum_erase Iso
            (fun t => (G.neighborFinset t ∩ Q).card * (G.neighborFinset t ∩ Q).card) ht0adj.2]
          omega
        -- No good pair ⟹ every non-adjacent distinct `Q`-pair shares a twin.
        by_contra hcon
        have hsgQ : ∀ p : Fin 19, p ∈ Q → ∀ q : Fin 19, q ∈ Q → p ≠ q → ¬G.Adj p q →
            1 ≤ (G.neighborFinset p ∩ G.neighborFinset q ∩ Iso).card := by
          intro p hp q hq hpq hnadj
          by_contra hs0
          rw [not_le, Nat.lt_one_iff] at hs0
          have hip := (Finset.mem_filter.mp hp).2
          have hiq := (Finset.mem_filter.mp hq).2
          refine hcon ⟨p, hQsub hp, q, hQsub hq, hpq, hnadj, ?_, ?_⟩
          · have := hsd p q; omega
          · have := hsd q p
            have hcomm : (G.neighborFinset q ∩ G.neighborFinset p ∩ Iso).card = 0 := by
              rw [show G.neighborFinset q ∩ G.neighborFinset p
                = G.neighborFinset p ∩ G.neighborFinset q from Finset.inter_comm _ _]; exact hs0
            omega
        have hrowQ : ∀ p : Fin 19, p ∈ Q → 2 * (G.neighborFinset p ∩ Iso).card
            ≤ ∑ q ∈ Q, (G.neighborFinset p ∩ G.neighborFinset q ∩ Iso).card := by
          intro p hp
          have herase := Finset.add_sum_erase Q
            (fun q => (G.neighborFinset p ∩ G.neighborFinset q ∩ Iso).card) hp
          have hpp : (G.neighborFinset p ∩ G.neighborFinset p ∩ Iso).card
              = (G.neighborFinset p ∩ Iso).card := by rw [Finset.inter_self]
          have hlow : ((Q.erase p).filter (fun q => ¬G.Adj p q)).card
              ≤ ∑ q ∈ Q.erase p, (G.neighborFinset p ∩ G.neighborFinset q ∩ Iso).card := by
            rw [Finset.card_filter]
            apply Finset.sum_le_sum
            intro q hq
            rw [Finset.mem_erase] at hq
            by_cases hadj : G.Adj p q
            · simp [hadj]
            · simp only [hadj, if_true, not_false_iff]
              exact hsgQ p hp q (Finset.mem_of_mem_erase (Finset.mem_erase.mpr hq))
                (Ne.symm hq.1) hadj
          have hfcard : (G.neighborFinset p ∩ Iso).card
              ≤ ((Q.erase p).filter (fun q => ¬G.Adj p q)).card := by
            have hcf : ((Q.erase p).filter (fun q => G.Adj p q)).card
                + ((Q.erase p).filter (fun q => ¬G.Adj p q)).card = (Q.erase p).card :=
              Finset.card_filter_add_card_filter_not _
            have heraseC : (Q.erase p).card = 3 := by rw [Finset.card_erase_of_mem hp, hQcard4]
            have hadjle : ((Q.erase p).filter (fun q => G.Adj p q)).card
                ≤ (G.neighborFinset p ∩ Dᶜ).card := by
              apply Finset.card_le_card
              intro q hq
              rw [Finset.mem_filter, Finset.mem_erase] at hq
              rw [Finset.mem_inter, G.mem_neighborFinset]
              exact ⟨hq.2, hSsub (hQsub hq.1.2)⟩
            have hii := hisoint p (hQsub hp)
            omega
          omega
        have hexactQ : (∑ p ∈ Q, ∑ q ∈ Q,
            (G.neighborFinset p ∩ G.neighborFinset q ∩ Iso).card)
            = ∑ t ∈ Iso, (G.neighborFinset t ∩ Q).card * (G.neighborFinset t ∩ Q).card :=
          cherry_double_count G Q Iso
        have hlbQ : 2 * TQ ≤ ∑ p ∈ Q, ∑ q ∈ Q,
            (G.neighborFinset p ∩ G.neighborFinset q ∩ Iso).card := by
          have hform : ∑ p ∈ Q, 2 * (G.neighborFinset p ∩ Iso).card = 2 * TQ := by
            rw [← Finset.mul_sum, ← hTQdef]
          rw [← hform]
          exact Finset.sum_le_sum hrowQ
        rw [hexactQ] at hlbQ
        omega
  -- Common extraction of the `TwoHubConfig` from the good pair (via `dense_two_hub_assemble`).
  obtain ⟨h₁, hh1n, h₂, hh2n, hne, hnadj, hp1, hp2⟩ := hpair
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hp1
  obtain ⟨c, hc, d, hd, hcd⟩ := Finset.one_lt_card.mp hp2
  have getmem : ∀ w u v : Fin 19, w ∈ (G.neighborFinset u ∩ Iso) \ G.neighborFinset v →
      G.Adj u w ∧ w ∈ Iso ∧ ¬G.Adj v w := by
    intro w u v hw
    rw [Finset.mem_sdiff, Finset.mem_inter, G.mem_neighborFinset] at hw
    exact ⟨hw.1.1, hw.1.2, fun hadj => hw.2 ((G.mem_neighborFinset _ _).mpr hadj)⟩
  obtain ⟨ha1, haI, ha2⟩ := getmem a h₁ h₂ ha
  obtain ⟨hb1, hbI, hb2⟩ := getmem b h₁ h₂ hb
  obtain ⟨hc1, hcI, hc2⟩ := getmem c h₂ h₁ hc
  obtain ⟨hd1, hdI, hd2⟩ := getmem d h₂ h₁ hd
  have hdh1 : G.degree h₁ = 4 := hdeg4 h₁ (hSsub hh1n)
  have hdh2 : G.degree h₂ = 4 := hdeg4 h₂ (hSsub hh2n)
  exact dense_two_hub_assemble G h₁ h₂ a b c d hdh1 hdh2 (hIsoprop a haI).1 (hIsoprop b hbI).1
    (hIsoprop c hcI).1 (hIsoprop d hdI).1 ha1.symm hb1.symm hc1.symm hd1.symm hnadj
    hc2 hd2 (fun hadj => ha2 hadj.symm) (fun hadj => hb2 hadj.symm)
    (hIsoprop a haI).2 (hIsoprop b hbI).2 hab hcd

/-- **Hub-triangle existence in the `n = 19`, `|D| = 8`, `e(M) = 2`, single-`P₃`-cherry corner.**
Under the residual hypotheses (eleven degree-`4` hubs, `M = P₃` cherry `x–y–z` with five
`M`-isolated twins, and the falsity of `SingleVertexConfig`/`TwoTwinConfig`/`TwoHubConfig`), the
graph contains three pairwise-adjacent hubs avoiding the cherry, packaged as `HubTriangleConfig G`.
Every hub meets `≤ 1` cherry vertex (a good triangle `Σ ≤ 10` via `hT10`, or — for the endpoints —
a good `C₄` `Σ = 13 ≤ 14` via `hC4`); since the cherry collects exactly `2 + 1 + 2 = 5`
hub-incidences, **exactly five** hubs are cherry-incident, forcing `|A| = 6` cherry-avoiders.  When
the in-`A` edge mass `∑_A(N ∩ A) ≥ 19` a Mantel triangle is forced (`mantel_six_triangle`);
otherwise the avoiders form a triangle-free `C₆`/`K_{3,3}`, split on whether two avoiders share an
`M`-isolated twin: a shared twin assembles a `SingleVertexConfig` (contradicting
`¬SingleVertexConfig`), while the distinct-twin case assembles a `TwoHubConfig`.  The distinct-twin
`TwoHubConfig` assembly for the genuine `n = 19` `|A| = 6` avoider set is closed axiom-clean by
`cherry_C6_distinct_twin_twoHub_nineteen`: the controlling counts `|S| = 5`, `|Iso| = 5`,
`∑_Dᶜ iso = 15` are unchanged from the `|A| = 5` corner, so the `C₅` extraction ports verbatim. -/
theorem exists_hub_triangle_config_cherry_residual_nineteen (G : SimpleGraph (Fin 19))
    (D Iso : Finset (Fin 19)) (x y z : Fin 19)
    (hmemD : ∀ v : Fin 19, v ∈ D ↔ G.degree v = 3)
    (hIsodef : Iso = D.filter (fun v => (G.neighborFinset v ∩ D).card = 0))
    (hIsoprop : ∀ v ∈ Iso, G.degree v = 3 ∧ (∀ w : Fin 19, G.Adj v w → G.degree w ≠ 3))
    (hisochar : ∀ w : Fin 19, w ∈ D → w ≠ x → w ≠ y → w ≠ z → w ∈ Iso)
    (hcov : ∀ p q : Fin 19, p ∈ D → q ∈ D → G.Adj p q → p = y ∨ q = y)
    (hNyD : G.neighborFinset y ∩ D = {x, z})
    (hxdeg : G.degree x = 3) (hydeg : G.degree y = 3) (hzdeg : G.degree z = 3)
    (haxy : G.Adj x y) (hayz : G.Adj y z) (hnxz : ¬G.Adj x z) (hxz : x ≠ z)
    (hdeg4 : ∀ w : Fin 19, w ∈ Dᶜ → G.degree w = 4)
    (hD8 : D.card = 8)
    (hC4 : ¬∃ a b c d : Fin 19, ({a, b, c, d} : Finset (Fin 19)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (hT10 : ¬∃ a b c : Fin 19, a ≠ b ∧ b ≠ c ∧ a ≠ c ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj a c ∧ G.degree a + G.degree b + G.degree c ≤ 10)
    (hsv : ¬SingleVertexConfig G) (_htt : ¬TwoTwinConfig G) (hth : ¬TwoHubConfig G) :
    HubTriangleConfig G := by
  classical
  have hxD : x ∈ D := (hmemD x).mpr hxdeg
  have hyD : y ∈ D := (hmemD y).mpr hydeg
  have hzD : z ∈ D := (hmemD z).mpr hzdeg
  have hxy : x ≠ y := haxy.ne
  have hzy : z ≠ y := hayz.ne'
  -- Structural counts: eleven hubs, five `M`-isolated twins.
  obtain ⟨hDeq, hdisj⟩ :=
    cherry_partition G D Iso x y z hIsodef hisochar hxD hyD hzD haxy hayz
  have hDc9 : Dᶜ.card = 11 := by rw [Finset.card_compl, Fintype.card_fin, hD8]
  have hIso5 : Iso.card = 5 := by
    have hPcard : ({x, y, z} : Finset (Fin 19)).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [hxy, hxz]),
        Finset.card_insert_of_notMem (by simp [Ne.symm hzy]), Finset.card_singleton]
    have hcardU := Finset.card_union_of_disjoint hdisj
    rw [hDeq, hPcard, hD8] at hcardU
    omega
  -- Cherry hub-incidence counts and the residual cherry-incidence sum (`∑ path = 5`).
  obtain ⟨hcx, hcy, hcz⟩ :=
    cherry_leaf_card G D x y z hcov hNyD hxD hyD hzD haxy hayz hxy hzy hxz hxdeg hydeg hzdeg
  obtain ⟨hsumP, hisoSum, hsplit4⟩ :=
    cherry_residual_sums G D Iso x y z hIsodef hIsoprop hisochar hxD hyD hzD haxy hayz
      hxy hzy hxz hdeg4 hcx hcy hcz hIso5
  -- The cherry-avoider set.
  set A := Dᶜ.filter (fun g => ¬G.Adj g x ∧ ¬G.Adj g y ∧ ¬G.Adj g z) with hAdef
  have hAsub : A ⊆ Dᶜ := Finset.filter_subset _ _
  have getA : ∀ g : Fin 19, g ∈ A → g ∈ Dᶜ ∧ ¬G.Adj g x ∧ ¬G.Adj g y ∧ ¬G.Adj g z := by
    intro g hg; rw [hAdef, Finset.mem_filter] at hg; exact hg
  -- **Every hub meets `≤ 1` cherry vertex.**  Two cherry neighbours give a good triangle `Σ ≤ 10`
  -- via `hT10`, or — for the endpoints `x, z` — a good `C₄` `x–y–z–h` with `Σ = 13 ≤ 14` via `hC4`.
  have hle1 : ∀ h : Fin 19, h ∈ Dᶜ →
      (G.neighborFinset h ∩ ({x, y, z} : Finset (Fin 19))).card ≤ 1 := by
    intro h hhDc
    have hhdeg : G.degree h = 4 := hdeg4 h hhDc
    have hhne : h ≠ x ∧ h ≠ y ∧ h ≠ z := by
      refine ⟨?_, ?_, ?_⟩ <;> rintro rfl
      · exact (Finset.mem_compl.mp hhDc) hxD
      · exact (Finset.mem_compl.mp hhDc) hyD
      · exact (Finset.mem_compl.mp hhDc) hzD
    have htri : ∀ u v : Fin 19, u ≠ v → G.Adj u v → G.Adj h u → G.Adj h v →
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
  -- Avoiders are cherry-free; non-avoiders meet `≥ 1` cherry vertex (hence exactly `1`).
  have hA0 : ∀ g : Fin 19, g ∈ A →
      (G.neighborFinset g ∩ ({x, y, z} : Finset (Fin 19))).card = 0 := by
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
  have hScherry : ∀ h : Fin 19, h ∈ Dᶜ → h ∉ A →
      1 ≤ (G.neighborFinset h ∩ ({x, y, z} : Finset (Fin 19))).card := by
    intro h hhDc hhA
    have hadj : G.Adj h x ∨ G.Adj h y ∨ G.Adj h z := by
      by_contra hcon
      push Not at hcon
      exact hhA (by rw [hAdef, Finset.mem_filter]; exact ⟨hhDc, hcon.1, hcon.2.1, hcon.2.2⟩)
    rcases hadj with hax | hay | haz
    · exact Finset.card_pos.mpr
        ⟨x, by rw [Finset.mem_inter, G.mem_neighborFinset]; exact ⟨hax, by simp⟩⟩
    · exact Finset.card_pos.mpr
        ⟨y, by rw [Finset.mem_inter, G.mem_neighborFinset]; exact ⟨hay, by simp⟩⟩
    · exact Finset.card_pos.mpr
        ⟨z, by rw [Finset.mem_inter, G.mem_neighborFinset]; exact ⟨haz, by simp⟩⟩
  -- The cherry meets exactly the five non-avoider hubs, so `|Dᶜ \ A| = 5` and `|A| = 6`.
  have hScard : (Dᶜ \ A).card = 5 := by
    have hsplit := Finset.sum_sdiff (f := fun g =>
      (G.neighborFinset g ∩ ({x, y, z} : Finset (Fin 19))).card) hAsub
    have hA0sum : ∑ g ∈ A,
        (G.neighborFinset g ∩ ({x, y, z} : Finset (Fin 19))).card = 0 :=
      Finset.sum_eq_zero hA0
    have hSeq : ∀ g ∈ Dᶜ \ A,
        (G.neighborFinset g ∩ ({x, y, z} : Finset (Fin 19))).card = 1 := by
      intro g hg
      rw [Finset.mem_sdiff] at hg
      have hge := hScherry g hg.1 hg.2
      have hle := hle1 g hg.1
      omega
    have hScount : ∑ g ∈ Dᶜ \ A,
        (G.neighborFinset g ∩ ({x, y, z} : Finset (Fin 19))).card = (Dᶜ \ A).card := by
      rw [Finset.sum_congr rfl hSeq, Finset.sum_const, smul_eq_mul, Nat.mul_one]
    omega
  have hcard6 : A.card = 6 := by
    have h := Finset.card_sdiff_add_card_inter Dᶜ A
    rw [Finset.inter_eq_right.mpr hAsub, hDc9] at h
    omega
  -- The triangle: a Mantel triangle when the in-`A` edge mass is high, else the twin dispatch.
  have htri : ∃ a b c : Fin 19, a ∈ A ∧ b ∈ A ∧ c ∈ A ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      G.Adj a b ∧ G.Adj a c ∧ G.Adj b c := by
    rcases Nat.lt_or_ge (∑ g ∈ A, (G.neighborFinset g ∩ A).card) 19 with _hbig | hbig
    · -- `∑_A(N ∩ A) ≤ 18`: the six cherry-avoiders form a triangle-free `C₆` / `K_{3,3}`; the goal
      -- is discharged by deriving `False` from the avoider/twin structure.
      exfalso
      -- **Shared-twin case [from `¬SingleVertexConfig`].**  If two cherry-avoiders `p, q` share an
      -- `M`-isolated twin `t`, the apex `t` with `p, q` and the cherry `x–y–z` forms a
      -- `SingleVertexConfig` (all of `t, p, q` avoid the cherry, so the cross term vanishes and the
      -- side condition reads `8 ≤ 8`), contradicting `hsv`.
      by_cases hshared : ∃ t : Fin 19, t ∈ Iso ∧ ∃ p : Fin 19, p ∈ A ∧ ∃ q : Fin 19, q ∈ A ∧
          p ≠ q ∧ G.Adj p t ∧ G.Adj q t
      · obtain ⟨t, htIso, p, hpA, q, hqA, hpq, hpt, hqt⟩ := hshared
        apply hsv
        obtain ⟨hpDc, hpx, hpy, hpz⟩ := getA p hpA
        obtain ⟨hqDc, hqx, hqy, hqz⟩ := getA q hqA
        have htdeg : G.degree t = 3 := (hIsoprop t htIso).1
        have htiso : ∀ w : Fin 19, G.Adj t w → G.degree w ≠ 3 := (hIsoprop t htIso).2
        have hpdeg : G.degree p = 4 := hdeg4 p hpDc
        have hqdeg : G.degree q = 4 := hdeg4 q hqDc
        have htnotxyz : t ∉ ({x, y, z} : Finset (Fin 19)) :=
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
        have hsum0 : ∑ w ∈ ({t, p, q} : Finset (Fin 19)),
            (G.neighborFinset w ∩ ({x, y, z} : Finset (Fin 19))).card = 0 := by
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
      · -- **Distinct-twin case.**  Each `M`-isolated twin meets `≤ 1` cherry-avoider (else the two
        -- shared avoiders give `hshared`), so every twin has `≥ 2` neighbours among the non-avoiders,
        -- and a non-adjacent pair of non-avoider hubs each carrying two private `M`-isolated twins
        -- assembles a `TwoHubConfig`.  At genuine `n = 19` the avoider set is `|A| = 6`, `|Dᶜ| = 11`,
        -- with the unchanged `|S| = 5`, `|Iso| = 5`, `∑_Dᶜ iso = 15`, closed by the bespoke
        -- `cherry_C6_distinct_twin_twoHub_nineteen`.
        refine absurd ?_ hth
        have hIsoD : Iso ⊆ D := by rw [hIsodef]; exact Finset.filter_subset _ _
        have hdistinct : ∀ t ∈ Iso, (G.neighborFinset t ∩ A).card ≤ 1 := by
          intro t ht
          by_contra hcon
          rw [not_le] at hcon
          obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp hcon
          rw [Finset.mem_inter, G.mem_neighborFinset] at hp hq
          exact hshared ⟨t, ht, p, hp.2, q, hq.2, hpq, hp.1.symm, hq.1.symm⟩
        have hScherryDisj : ∀ h : Fin 19, h ∈ Dᶜ → h ∉ A →
            G.Adj h x ∨ G.Adj h y ∨ G.Adj h z := by
          intro h hhDc hhA
          by_contra hcon
          push Not at hcon
          exact hhA (by rw [hAdef, Finset.mem_filter]; exact ⟨hhDc, hcon.1, hcon.2.1, hcon.2.2⟩)
        exact cherry_C6_distinct_twin_twoHub_nineteen G D Iso A x y z hIsodef hIsoprop hIsoD
          hdeg4 hC4 hAsub hcard6 hIso5 hDc9 (fun g hg => (getA g hg).2) hScherryDisj hsplit4
          hdistinct hisoSum
    · obtain ⟨a, b, c, haA, hbA, hcA, hab, hac, hbc⟩ :=
        mantel_six_triangle G A hcard6 hbig
      exact ⟨a, b, c, haA, hbA, hcA, hab.ne, hac.ne, hbc.ne, hab, hac, hbc⟩
  obtain ⟨a, b, c, haA, hbA, hcA, hab, hac, hbc, hadj_ab, hadj_ac, hadj_bc⟩ := htri
  obtain ⟨haDc, hax, hay, haz⟩ := getA a haA
  obtain ⟨hbDc, hbx, hby, hbz⟩ := getA b hbA
  obtain ⟨hcDc, hcxx, hcyy, hczz⟩ := getA c hcA
  have hubne : ∀ g : Fin 19, g ∈ Dᶜ → g ≠ x ∧ g ≠ y ∧ g ≠ z := by
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

end N19

end ACMax
