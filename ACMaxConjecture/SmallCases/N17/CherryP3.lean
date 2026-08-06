import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N17.Core
import ACMaxConjecture.SmallCases.Certificates
import ACMaxConjecture.SmallCases.N17.Dense
import ACMaxConjecture.SmallCases.N17.CherryCore

/-!
# `n = 17`, `e(M) = 2` (`P₃` cherry) alignment corners for `|D| ∈ {9, 10, 11}`

These helper lemmas close the `P₃`-cherry residual of `exists_align_four_config_seventeen`
(`ACMaxConjecture/TwinCert17.lean`).  At `s = 4`, `e(M) = 2`, the matching `M` is the single cherry
`x–y–z` (centre `y`); the `M`-isolated degree-`3` vertices form `Iso = D \ {x, y, z}` and every
other degree-`3` vertex is one of `x, y, z`.  The covering configuration for each `|D|` value is:

* `|D| = 11` (`|Hub| = 6`): **vacuous** — the cross-count forces `29 ≤ 27`, a contradiction.
* `|D| = 9` (`|Hub| = 8`, one degree-`5` + seven degree-`4`, `|Iso| = 6`): a cherry-avoiding
  degree-`4` hub with `≥ 2` `M`-isolated twins gives `TwoTwinConfig`, else two non-adjacent
  degree-`4` hubs with `2` private twins each give `TwoHubConfig`.
* `|D| = 10` (`|Hub| = 7`): two non-adjacent degree-`4` hubs (no `Dᶜ`-neighbours) with `2`
  private twins each give `TwoHubConfig`.
-/

namespace ACMax

open scoped Classical

namespace N17

/-- **`P₃`-cherry `|D| = 11` corner is vacuous (`n = 17`, `e(M) = 2`).**  With `|D| = 11` the
cherry `x–y–z` is the only `M`-edge pair, so `∑_{v∈D}|N v ∩ D| = 4`.  The cross-count
`∑_{w∈Dᶜ}|N w ∩ D| = ∑_{v∈D}|N v ∩ Dᶜ| = 3·11 − 4 = 29` exceeds `∑_{w∈Dᶜ}deg w = 60 − 33 = 27`
(`|N w ∩ D| ≤ deg w` pointwise), a contradiction. -/
theorem cherry_p3_D11_vacuous_seventeen (G : SimpleGraph (Fin 17))
    (hm : G.edgeFinset.card = 30) (D : Finset (Fin 17)) (x y z : Fin 17)
    (hmemD : ∀ v : Fin 17, v ∈ D ↔ G.degree v = 3)
    (hcov : ∀ p q : Fin 17, p ∈ D → q ∈ D → G.Adj p q → p = y ∨ q = y)
    (hxD : x ∈ D) (hyD : y ∈ D) (hzD : z ∈ D)
    (hxyA : G.Adj x y) (hyzA : G.Adj y z)
    (hxy_ne : x ≠ y) (hyz_ne : y ≠ z) (hxz_ne : x ≠ z)
    (hNyD : G.neighborFinset y ∩ D = ({x, z} : Finset (Fin 17)))
    (hDcard : D.card = 11) :
    SingleVertexConfig G ∨ TwoTwinConfig G ∨ TwoHubConfig G ∨ HubTriangleConfig G := by
  classical
  exfalso
  have hdegD : ∀ v : Fin 17, v ∈ D → G.degree v = 3 := fun v hv => (hmemD v).mp hv
  -- `N x ∩ D = {y}` and `N z ∩ D = {y}` from `hcov`.
  have hNxD : G.neighborFinset x ∩ D = ({y} : Finset (Fin 17)) := by
    apply Finset.Subset.antisymm
    · intro w hw
      rw [Finset.mem_inter, G.mem_neighborFinset] at hw
      obtain ⟨hxw, hwD⟩ := hw
      rcases hcov x w hxD hwD hxw with e | e
      · exact absurd e hxy_ne
      · rw [Finset.mem_singleton, e]
    · intro w hw
      rw [Finset.mem_singleton] at hw; subst w
      exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset x y).mpr hxyA, hyD⟩
  have hNzD : G.neighborFinset z ∩ D = ({y} : Finset (Fin 17)) := by
    apply Finset.Subset.antisymm
    · intro w hw
      rw [Finset.mem_inter, G.mem_neighborFinset] at hw
      obtain ⟨hzw, hwD⟩ := hw
      rcases hcov z w hzD hwD hzw with e | e
      · exact absurd e hyz_ne.symm
      · rw [Finset.mem_singleton, e]
    · intro w hw
      rw [Finset.mem_singleton] at hw; subst w
      exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset z y).mpr hyzA.symm, hyD⟩
  -- Degree split into `D` and `Dᶜ` parts.
  have hdsplit : ∀ v : Fin 17,
      (G.neighborFinset v ∩ D).card + (G.neighborFinset v ∩ Dᶜ).card = G.degree v := by
    intro v
    have hdisj : Disjoint (G.neighborFinset v ∩ D) (G.neighborFinset v ∩ Dᶜ) :=
      Finset.disjoint_left.mpr (fun a ha ha' =>
        (Finset.mem_compl.mp (Finset.mem_inter.mp ha').2) (Finset.mem_inter.mp ha).2)
    have hun : (G.neighborFinset v ∩ D) ∪ (G.neighborFinset v ∩ Dᶜ) = G.neighborFinset v := by
      rw [← Finset.inter_union_distrib_left, Finset.union_compl, Finset.inter_univ]
    rw [← Finset.card_union_of_disjoint hdisj, hun, G.card_neighborFinset_eq_degree]
  -- `∑_{v∈D}|N v ∩ D| = 4`.
  have hxyz_sub : ({x, y, z} : Finset (Fin 17)) ⊆ D := by
    intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl <;> assumption
  have hother0 : ∀ v ∈ D, v ∉ ({x, y, z} : Finset (Fin 17)) →
      (G.neighborFinset v ∩ D).card = 0 := by
    intro v hvD hvxyz
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro w hw
    rw [Finset.mem_inter, G.mem_neighborFinset] at hw
    obtain ⟨hvw, hwD⟩ := hw
    rcases hcov v w hvD hwD hvw with e | e
    · exact hvxyz (by rw [e]; simp)
    · have : v ∈ G.neighborFinset y ∩ D :=
        Finset.mem_inter.mpr ⟨(G.mem_neighborFinset y v).mpr (e ▸ hvw).symm, hvD⟩
      rw [hNyD, Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with rfl | rfl
      · exact hvxyz (by simp)
      · exact hvxyz (by simp)
  have hsumD_in : ∑ v ∈ D, (G.neighborFinset v ∩ D).card = 4 := by
    rw [← Finset.sum_subset hxyz_sub (fun v hv hnv => hother0 v hv hnv),
      Finset.sum_insert (by simp [hxy_ne, hxz_ne]),
      Finset.sum_insert (by simp [hyz_ne]), Finset.sum_singleton,
      hNxD, hNyD, hNzD, Finset.card_pair hxz_ne, Finset.card_singleton]
    rfl
  -- `∑_{v∈D} deg v = 33`.

  have hsumDdeg : ∑ v ∈ D, G.degree v = 33 := by
    rw [Finset.sum_congr rfl (fun v hv => hdegD v hv), Finset.sum_const, smul_eq_mul,
      hDcard]
  -- `∑_{v∈D}|N v ∩ Dᶜ| = 29`.
  have hcross_D : ∑ v ∈ D, (G.neighborFinset v ∩ Dᶜ).card = 29 := by
    have hcong : ∑ v ∈ D,
        ((G.neighborFinset v ∩ D).card + (G.neighborFinset v ∩ Dᶜ).card)
          = ∑ v ∈ D, G.degree v := Finset.sum_congr rfl (fun v _ => hdsplit v)
    rw [Finset.sum_add_distrib, hsumD_in, hsumDdeg] at hcong
    omega
  -- `∑_{w∈Dᶜ} deg w = 27`.
  have hsum60 : ∑ v : Fin 17, G.degree v = 60 := by
    rw [SimpleGraph.sum_degrees_eq_twice_card_edges, hm]
  have hsumDcdeg : ∑ w ∈ Dᶜ, G.degree w = 27 := by
    have hsplit : ∑ v ∈ D, G.degree v + ∑ w ∈ Dᶜ, G.degree w = 60 := by
      rw [Finset.sum_add_sum_compl]; exact hsum60
    rw [hsumDdeg] at hsplit; omega
  -- Cross-count equality and the pointwise bound.
  have hcc := cross_count G D Dᶜ
  have hbound : ∑ w ∈ Dᶜ, (G.neighborFinset w ∩ D).card ≤ ∑ w ∈ Dᶜ, G.degree w :=
    Finset.sum_le_sum (fun w _ => by
      calc (G.neighborFinset w ∩ D).card ≤ (G.neighborFinset w).card :=
            Finset.card_le_card Finset.inter_subset_left
        _ = G.degree w := G.card_neighborFinset_eq_degree w)
  rw [← hcc, hcross_D, hsumDcdeg] at hbound
  omega

/-- **`P₃`-cherry `|D| = 9` corner (`n = 17`, `e(M) = 2`).**  Here `|Hub| = 8` (one degree-`5` plus
seven degree-`4` hubs), `|Iso| = 6` and `∑_{v∈Iso}|N v ∩ Hub| = 18`.  The cherry `x–y–z` sends
`2 + 1 + 2 = 5` edges into `Hub`, so at least `8 − 5 = 3` hubs avoid it.  A two-route dichotomy:
either a cherry-avoiding degree-`4` hub carries `≥ 2` `M`-isolated twins (`TwoTwinConfig`, the route
below via `twotwin_assemble_cherry_seventeen`), or the tie configuration forces two non-adjacent
degree-`4` hubs with two private twins each (`TwoHubConfig`, share `≤ 1` via
`nonadj_hubs_share_le_one_iso`). -/
theorem cherry_p3_config_D9_seventeen (G : SimpleGraph (Fin 17))
    (hm : G.edgeFinset.card = 30) (h3 : ∀ v : Fin 17, 3 ≤ G.degree v)
    (_hT : ¬∃ x y z : Fin 17, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    (_h2k2 : ¬∃ a b c d : Fin 17, ({a, b, c, d} : Finset (Fin 17)).card = 4 ∧
      G.degree a = 3 ∧ G.degree b = 3 ∧ G.degree c = 3 ∧ G.degree d = 3 ∧
      G.Adj a b ∧ G.Adj c d ∧ ¬G.Adj a c ∧ ¬G.Adj a d ∧ ¬G.Adj b c ∧ ¬G.Adj b d)
    (_hC4 : ¬∃ a b c d : Fin 17, ({a, b, c, d} : Finset (Fin 17)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (_hK23 : ¬∃ a b c d e : Fin 17, ({a, b, c, d, e} : Finset (Fin 17)).card = 5 ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
      G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 19)
    (D Iso : Finset (Fin 17)) (x y z : Fin 17)
    (hmemD : ∀ v : Fin 17, v ∈ D ↔ G.degree v = 3)
    (hIsoprop : ∀ v ∈ Iso, G.degree v = 3 ∧ (∀ w : Fin 17, G.Adj v w → G.degree w ≠ 3))
    (hisochar : ∀ w : Fin 17, w ∈ D → w ≠ x → w ≠ y → w ≠ z → w ∈ Iso)
    (hcov : ∀ p q : Fin 17, p ∈ D → q ∈ D → G.Adj p q → p = y ∨ q = y)
    (hNyD : G.neighborFinset y ∩ D = ({x, z} : Finset (Fin 17)))
    (hdegx : G.degree x = 3) (hdegy : G.degree y = 3) (hdegz : G.degree z = 3)
    (hxyA : G.Adj x y) (hyzA : G.Adj y z) (hxzN : ¬G.Adj x z)
    (hxy_ne : x ≠ y) (hyz_ne : y ≠ z) (hxz_ne : x ≠ z)
    (hDcard : D.card = 9) :
    SingleVertexConfig G ∨ TwoTwinConfig G ∨ TwoHubConfig G ∨ HubTriangleConfig G := by
  classical
  -- All eight hubs have degree `≤ 5` (`∑_{Dᶜ} deg = 33`, `|Dᶜ| = 8`, excess `1`), so the corrected
  -- cherry-avoiding pigeonhole (`p3_cherry_two_twin_seventeen`) yields a cherry-avoiding degree-`≤ 5`
  -- hub carrying two `M`-isolated twins, hence a `TwoTwinConfig`.
  have hDc8 : Dᶜ.card = 8 := by
    have h := Finset.card_add_card_compl D
    simp only [Fintype.card_fin] at h; omega
  have hsum60 : ∑ v : Fin 17, G.degree v = 60 := by
    rw [SimpleGraph.sum_degrees_eq_twice_card_edges, hm]
  have hsumD : ∑ v ∈ D, G.degree v = 27 := by
    have h1 : ∑ v ∈ D, G.degree v = 3 * D.card := by
      rw [Finset.sum_congr rfl (fun v hv => (hmemD v).mp hv), Finset.sum_const, smul_eq_mul,
        mul_comm]
    omega
  have hsumDc : ∑ w ∈ Dᶜ, G.degree w = 33 := by
    have h : ∑ v ∈ D, G.degree v + ∑ w ∈ Dᶜ, G.degree w = 60 := by
      rw [Finset.sum_add_sum_compl]; exact hsum60
    omega
  have hdeg5 : ∀ h : Fin 17, h ∈ (Dᶜ : Finset (Fin 17)) → G.degree h ≤ 5 := by
    intro h hh
    have hge : 4 * (Dᶜ.erase h).card ≤ ∑ w ∈ Dᶜ.erase h, G.degree w := by
      have := Finset.card_nsmul_le_sum (Dᶜ.erase h) (fun w => G.degree w) 4
        (fun w hw => by
          have hwc : w ∈ Dᶜ := Finset.mem_of_mem_erase hw
          rw [Finset.mem_compl, hmemD] at hwc; have := h3 w; omega)
      simpa [smul_eq_mul, Nat.mul_comm] using this
    have hcard7 : (Dᶜ.erase h).card = 7 := by rw [Finset.card_erase_of_mem hh, hDc8]
    have hsumsplit : ∑ w ∈ Dᶜ.erase h, G.degree w + G.degree h = ∑ w ∈ Dᶜ, G.degree w :=
      Finset.sum_erase_add Dᶜ (fun w => G.degree w) hh
    omega
  exact Or.inr (Or.inl (p3_cherry_two_twin_seventeen G D Iso Dᶜ x y z hm h3 hmemD hIsoprop
    hisochar hcov hNyD hdegx hdegy hdegz hxyA hyzA hxzN hxy_ne hyz_ne hxz_ne
    (Finset.Subset.refl _) hdeg5 (by omega)
    (by intro a h1 h2 h3'; rw [hDc8] at h1; rw [hDcard] at h2 h3'
        have ha : a = 3 := by omega
        subst ha; omega)))

/-- **`P₃`-cherry `|D| = 10` corner (`n = 17`, `e(M) = 2`).**  Here `|Hub| = 7` with degree-excess
`2` (hubs are *not* all degree-`4` and *not* independent: `∑_{w∈Dᶜ}|N w ∩ Dᶜ| = 4`).  At least two
degree-`4` hubs have no `Dᶜ`-neighbour (hence are mutually non-adjacent and all-`D`-neighboured) and
carry two private `M`-isolated twins; the degree-`4`-restricted share bound (the `C₄`
`h₁–a–h₂–b` has degree-sum `4 + 4 + 3 + 3 = 14 ≤ 14`, excluded by `hC4`) gives `TwoHubConfig`. -/
theorem cherry_p3_two_hub_D10_seventeen (G : SimpleGraph (Fin 17))
    (hm : G.edgeFinset.card = 30) (h3 : ∀ v : Fin 17, 3 ≤ G.degree v)
    (_hT : ¬∃ x y z : Fin 17, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    (_h2k2 : ¬∃ a b c d : Fin 17, ({a, b, c, d} : Finset (Fin 17)).card = 4 ∧
      G.degree a = 3 ∧ G.degree b = 3 ∧ G.degree c = 3 ∧ G.degree d = 3 ∧
      G.Adj a b ∧ G.Adj c d ∧ ¬G.Adj a c ∧ ¬G.Adj a d ∧ ¬G.Adj b c ∧ ¬G.Adj b d)
    (_hC4 : ¬∃ a b c d : Fin 17, ({a, b, c, d} : Finset (Fin 17)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (_hK23 : ¬∃ a b c d e : Fin 17, ({a, b, c, d, e} : Finset (Fin 17)).card = 5 ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
      G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 19)
    (D Iso : Finset (Fin 17)) (x y z : Fin 17)
    (hmemD : ∀ v : Fin 17, v ∈ D ↔ G.degree v = 3)
    (hIsoprop : ∀ v ∈ Iso, G.degree v = 3 ∧ (∀ w : Fin 17, G.Adj v w → G.degree w ≠ 3))
    (hisochar : ∀ w : Fin 17, w ∈ D → w ≠ x → w ≠ y → w ≠ z → w ∈ Iso)
    (hcov : ∀ p q : Fin 17, p ∈ D → q ∈ D → G.Adj p q → p = y ∨ q = y)
    (hNyD : G.neighborFinset y ∩ D = ({x, z} : Finset (Fin 17)))
    (hdegx : G.degree x = 3) (hdegy : G.degree y = 3) (hdegz : G.degree z = 3)
    (hxyA : G.Adj x y) (hyzA : G.Adj y z) (hxzN : ¬G.Adj x z)
    (hxy_ne : x ≠ y) (hyz_ne : y ≠ z) (hxz_ne : x ≠ z)
    (hDcard : D.card = 10) :
    SingleVertexConfig G ∨ TwoTwinConfig G ∨ TwoHubConfig G ∨ HubTriangleConfig G := by
  classical
  -- `|Dᶜ| = 7`, `∑_{Dᶜ} deg = 30` (excess `2`), so at most one hub has degree `≥ 6`; the deg-`≤ 5`
  -- part `Hub5` has `≥ 6` hubs, and the corrected pigeonhole yields a cherry-avoiding deg-`≤ 5` hub
  -- with two `M`-isolated twins, hence a `TwoTwinConfig`.
  have hDc7 : Dᶜ.card = 7 := by
    have h := Finset.card_add_card_compl D
    simp only [Fintype.card_fin] at h; omega
  have hsum60 : ∑ v : Fin 17, G.degree v = 60 := by
    rw [SimpleGraph.sum_degrees_eq_twice_card_edges, hm]
  have hsumD : ∑ v ∈ D, G.degree v = 30 := by
    have h1 : ∑ v ∈ D, G.degree v = 3 * D.card := by
      rw [Finset.sum_congr rfl (fun v hv => (hmemD v).mp hv), Finset.sum_const, smul_eq_mul,
        mul_comm]
    omega
  have hsumDc : ∑ w ∈ Dᶜ, G.degree w = 30 := by
    have h : ∑ v ∈ D, G.degree v + ∑ w ∈ Dᶜ, G.degree w = 60 := by
      rw [Finset.sum_add_sum_compl]; exact hsum60
    omega
  set Hub5 : Finset (Fin 17) := Dᶜ.filter (fun w => G.degree w ≤ 5) with hHub5def
  set H6 : Finset (Fin 17) := Dᶜ.filter (fun w => ¬G.degree w ≤ 5) with hH6def
  have hHub5sub : Hub5 ⊆ Dᶜ := Finset.filter_subset _ _
  have hHub5deg5 : ∀ h : Fin 17, h ∈ Hub5 → G.degree h ≤ 5 :=
    fun h hh => (Finset.mem_filter.mp hh).2
  have hpart : Hub5.card + H6.card = Dᶜ.card := by
    rw [hHub5def, hH6def]; exact Finset.card_filter_add_card_filter_not _
  have hsplitdeg : ∑ w ∈ Hub5, G.degree w + ∑ w ∈ H6, G.degree w = ∑ w ∈ Dᶜ, G.degree w := by
    rw [hHub5def, hH6def]; exact Finset.sum_filter_add_sum_filter_not Dᶜ _ _
  have hH6sum : 6 * H6.card ≤ ∑ w ∈ H6, G.degree w := by
    have := Finset.card_nsmul_le_sum H6 (fun w => G.degree w) 6
      (fun w hw => by
        have hw2 := Finset.mem_filter.mp hw; omega)
    simpa [smul_eq_mul, Nat.mul_comm] using this
  have hHub5sum : 4 * Hub5.card ≤ ∑ w ∈ Hub5, G.degree w := by
    have := Finset.card_nsmul_le_sum Hub5 (fun w => G.degree w) 4
      (fun w hw => by
        have hwc : w ∈ Dᶜ := hHub5sub hw
        rw [Finset.mem_compl, hmemD] at hwc; have := h3 w; omega)
    simpa [smul_eq_mul, Nat.mul_comm] using this
  have hHub5ge6 : 6 ≤ Hub5.card := by omega
  exact Or.inr (Or.inl (p3_cherry_two_twin_seventeen G D Iso Hub5 x y z hm h3 hmemD hIsoprop
    hisochar hcov hNyD hdegx hdegy hdegz hxyA hyzA hxzN hxy_ne hyz_ne hxz_ne
    hHub5sub hHub5deg5 (by omega)
    (by intro a h1 h2 h3'; rw [hDcard] at h2 h3'
        have ha : a = 1 := by omega
        subst ha; omega)))

end N17

end ACMax
