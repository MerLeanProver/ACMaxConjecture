import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N20.Core
import ACMaxConjecture.SmallCases.StarCertificates
import ACMaxConjecture.SmallCases.N20.BipartiteAvoiderTwoHub

/-!
# `n = 20` dense-cherry `|D| = 9` (`11` hubs) ISO1 hard-`c` subcase — the anchor tie

The no-isolated-degree-`4`-hub world (`hID40`).  With every degree-`4` hub internally non-isolated
and a single degree-`5` hub `h₅`, the internal-mass ledger `∑ int = 24` runs a one-inequality
inclusion–exclusion tie against the two cherry-avoider families `A1` (avoids `L₁, c₁, c₂`) and
`A2` (avoids `c₁, c₂, L₂`), each of size `≥ 7`.  The tie `|A1| = |A2| = 7` pins every `A2`-hub to
`int ∈ {2, 3}` (`isoinc = 1`), and pigeonholing `A2 ∖ {h₅}` (`≥ 6` hubs) into the five `Iso` twins
gives a shared pair — a triangle (`Σ = 11`, `hT`) or a `SingleVertexConfig` (`hsv`).
-/

namespace ACMax

open scoped Classical

namespace N20

/-- **The `|Hub| = 11` internal-mass inclusion–exclusion tie.**  Two avoider families `A1, A2 ⊆ Dc`
of size `≥ 7`, a weight `b` that is `≥ 2` on `A1 ∪ A2`, `≥ 3` on `FF = A1 ∩ A2`, and `≥ 1` off
`A1 ∪ A2` away from a single exceptional vertex `h5`, with total `∑ b = 24`, forces every
`(A1 ∪ A2) ∖ FF` weight to `2` and every `FF` weight to `3` (all inequalities are equalities). -/
theorem tie_extract_eleven (Dc A1 A2 FF : Finset (Fin 20)) (b : Fin 20 → ℕ) (h5 : Fin 20)
    (hUsub : A1 ∪ A2 ⊆ Dc) (hFF : FF = A1 ∩ A2)
    (hDc : Dc.card = 11) (hA1 : 7 ≤ A1.card) (hA2 : 7 ≤ A2.card)
    (hb2 : ∀ g ∈ A1 ∪ A2, 2 ≤ b g) (hb3 : ∀ g ∈ FF, 3 ≤ b g)
    (hb1 : ∀ g ∈ Dc, g ∉ A1 ∪ A2 → g ≠ h5 → 1 ≤ b g)
    (hsum : ∑ g ∈ Dc, b g = 24) :
    (∀ g ∈ A1 ∪ A2, g ∉ FF → b g = 2) ∧ (∀ g ∈ FF, b g = 3) := by
  classical
  set U : Finset (Fin 20) := A1 ∪ A2 with hUdef
  have hFFU : FF ⊆ U := by
    rw [hFF, hUdef]; exact Finset.inter_subset_left.trans Finset.subset_union_left
  -- **Cardinal bookkeeping.**
  have hIE : U.card + FF.card = A1.card + A2.card := by
    rw [hUdef, hFF]; exact Finset.card_union_add_card_inter A1 A2
  have hUFF : (U \ FF).card + FF.card = U.card := Finset.card_sdiff_add_card_eq_card hFFU
  have hTcard : (Dc \ U).card + U.card = Dc.card := Finset.card_sdiff_add_card_eq_card hUsub
  have hTh5 : (Dc \ U).card ≤ ((Dc \ U) \ {h5}).card + 1 := by
    have h := (Finset.card_le_card_sdiff_add_card
      (s := Dc \ U) (t := ({h5} : Finset (Fin 20))))
    rwa [Finset.card_singleton] at h
  -- **Sum decomposition** `∑_{Dc} = ∑_{FF} + ∑_{U∖FF} + ∑_{Dc∖U}`.
  have hsplit1 : ∑ g ∈ Dc \ U, b g + ∑ g ∈ U, b g = ∑ g ∈ Dc, b g := Finset.sum_sdiff hUsub
  have hsplit2 : ∑ g ∈ U \ FF, b g + ∑ g ∈ FF, b g = ∑ g ∈ U, b g := Finset.sum_sdiff hFFU
  -- **Per-block lower bounds.**
  have hlbFF : FF.card * 3 ≤ ∑ g ∈ FF, b g := by
    have := Finset.card_nsmul_le_sum FF b 3 hb3
    simpa [smul_eq_mul] using this
  have hlbUFF : (U \ FF).card * 2 ≤ ∑ g ∈ U \ FF, b g := by
    have := Finset.card_nsmul_le_sum (U \ FF) b 2
      (fun g hg => hb2 g (Finset.mem_sdiff.mp hg).1)
    simpa [smul_eq_mul] using this
  have hlbT1 : ((Dc \ U) \ {h5}).card ≤ ∑ g ∈ (Dc \ U) \ {h5}, b g := by
    have := Finset.card_nsmul_le_sum ((Dc \ U) \ {h5}) b 1 (by
      intro g hg
      obtain ⟨hgT, hgh5⟩ := Finset.mem_sdiff.mp hg
      obtain ⟨hgDc, hgU⟩ := Finset.mem_sdiff.mp hgT
      exact hb1 g hgDc hgU (Finset.notMem_singleton.mp hgh5))
    simpa [smul_eq_mul] using this
  have hlbT : ∑ g ∈ (Dc \ U) \ {h5}, b g ≤ ∑ g ∈ Dc \ U, b g :=
    Finset.sum_le_sum_of_subset (Finset.sdiff_subset)
  -- **The tie.**  All block inequalities collapse to equalities.
  have hsFF : ∑ g ∈ FF, b g = FF.card * 3 := by omega
  have hsUFF : ∑ g ∈ U \ FF, b g = (U \ FF).card * 2 := by omega
  refine ⟨?_, ?_⟩
  · intro g hg hgFF
    have hgUFF : g ∈ U \ FF := Finset.mem_sdiff.mpr ⟨hg, hgFF⟩
    have hzero : ∑ x ∈ U \ FF, (b x - 2) = 0 := by
      have hcc : ∑ x ∈ U \ FF, ((b x - 2) + 2) = ∑ x ∈ U \ FF, b x :=
        Finset.sum_congr rfl (fun x hx =>
          Nat.sub_add_cancel (hb2 x (Finset.mem_sdiff.mp hx).1))
      rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul] at hcc
      omega
    have := (Finset.sum_eq_zero_iff.mp hzero) g hgUFF
    have hge := hb2 g hg
    omega
  · intro g hg
    have hzero : ∑ x ∈ FF, (b x - 3) = 0 := by
      have hcc : ∑ x ∈ FF, ((b x - 3) + 3) = ∑ x ∈ FF, b x :=
        Finset.sum_congr rfl (fun x hx => Nat.sub_add_cancel (hb3 x hx))
      rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul] at hcc
      omega
    have := (Finset.sum_eq_zero_iff.mp hzero) g hg
    have hge := hb3 g hg
    omega

/-- **`|D| = 9` (`11` hubs) ISO1 hard-`c` subcase, anchor-tie world.**  The no-isolated-degree-`4`-hub
corner (`hID40`): the internal-mass ledger `∑ int = 24` ties `|A1| = |A2| = 7`, every `A2`-hub carries
`isoinc = 1`, and the `A2 ∖ {h₅}` pigeonhole into the five `Iso` twins closes via `hT`/`hsv`. -/
theorem iso1_id40_anchor_tie_eleven (G : SimpleGraph (Fin 20))
    (D Iso : Finset (Fin 20)) (L₁ c₁ c₂ L₂ h₅ : Fin 20)
    (_hmemD : ∀ v : Fin 20, v ∈ D ↔ G.degree v = 3)
    (hIsoprop : ∀ v ∈ Iso, G.degree v = 3 ∧ (∀ w : Fin 20, G.Adj v w → G.degree w ≠ 3))
    (hclassP : ∀ x : Fin 20, x ∈ D → x = L₁ ∨ x = c₁ ∨ x = c₂ ∨ x = L₂ ∨ x ∈ Iso)
    (hL1deg : G.degree L₁ = 3) (hc1deg : G.degree c₁ = 3)
    (hc2deg : G.degree c₂ = 3) (hL2deg : G.degree L₂ = 3)
    (hac1L1 : G.Adj c₁ L₁) (hc12 : G.Adj c₁ c₂) (hac2L2 : G.Adj c₂ L₂)
    (hL1nc2 : L₁ ≠ c₂) (hL2nc1 : L₂ ≠ c₁)
    (hNc1D : G.neighborFinset c₁ ∩ D = {c₂, L₁}) (hNc2D : G.neighborFinset c₂ ∩ D = {c₁, L₂})
    (hL1D : L₁ ∈ D) (hc1D : c₁ ∈ D) (hc2D : c₂ ∈ D) (hL2D : L₂ ∈ D)
    (htt : ¬TwoTwinConfig G) (_hth : ¬TwoHubConfig G) (hsv : ¬SingleVertexConfig G)
    (hT : ¬∃ x y z : Fin 20, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 11)
    (_hC4 : ¬∃ a b c d : Fin 20, ({a, b, c, d} : Finset (Fin 20)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (hHub11 : Dᶜ.card = 11) (hIsocard : Iso.card = 5)
    (hdeg5 : ∀ h : Fin 20, h ∈ Dᶜ → G.degree h ≤ 5)
    (hper : ∀ h : Fin 20, h ∈ Dᶜ →
      (G.neighborFinset h ∩ ({L₁, c₁, c₂, L₂} : Finset (Fin 20))).card
        + (G.neighborFinset h ∩ Iso).card + (G.neighborFinset h ∩ Dᶜ).card = G.degree h)
    (hsumPath : ∑ g ∈ Dᶜ, (G.neighborFinset g ∩ ({L₁, c₁, c₂, L₂} : Finset (Fin 20))).card = 6)
    (_hsumIso15 : ∑ h ∈ Dᶜ, (G.neighborFinset h ∩ Iso).card = 15)
    (hc1hub : (G.neighborFinset c₁ ∩ Dᶜ).card = 1)
    (hc2hub : (G.neighborFinset c₂ ∩ Dᶜ).card = 1)
    (hL1hub : (G.neighborFinset L₁ ∩ Dᶜ).card = 2)
    (hL2hub : (G.neighborFinset L₂ ∩ Dᶜ).card = 2)
    (hID40 : ∀ h : Fin 20, h ∈ Dᶜ → G.degree h = 4 → (G.neighborFinset h ∩ Dᶜ).card ≠ 0)
    (_hh5Dc : h₅ ∈ Dᶜ) (hh5d : G.degree h₅ = 5)
    (hdegOth : ∀ h : Fin 20, h ∈ Dᶜ → h ≠ h₅ → G.degree h = 4)
    (hsumInt : ∑ h ∈ Dᶜ, (G.neighborFinset h ∩ Dᶜ).card = 24)
    (hntri1 : ¬∃ a b c : Fin 20, a ∈ Dᶜ ∧ b ∈ Dᶜ ∧ c ∈ Dᶜ ∧
      G.Adj a b ∧ G.Adj a c ∧ G.Adj b c ∧
      (¬G.Adj a L₁ ∧ ¬G.Adj a c₁ ∧ ¬G.Adj a c₂) ∧
      (¬G.Adj b L₁ ∧ ¬G.Adj b c₁ ∧ ¬G.Adj b c₂) ∧
      (¬G.Adj c L₁ ∧ ¬G.Adj c c₁ ∧ ¬G.Adj c c₂) ∧
      G.degree a + G.degree b + G.degree c ≤ 13) :
    False := by
  classical
  set P : Finset (Fin 20) := {L₁, c₁, c₂, L₂} with hPdef
  have hIso_nadj : ∀ t : Fin 20, t ∈ Iso → ∀ w : Fin 20, G.degree w = 3 → ¬G.Adj t w :=
    fun t ht w hw hadj => (hIsoprop t ht).2 w hadj hw
  have hc1nIso : c₁ ∉ Iso := fun h => (hIsoprop c₁ h).2 L₁ hac1L1 hL1deg
  have hc2nIso : c₂ ∉ Iso := fun h => (hIsoprop c₂ h).2 c₁ hc12.symm hc1deg
  have hL1nIso : L₁ ∉ Iso := fun h => (hIsoprop L₁ h).2 c₁ hac1L1.symm hc1deg
  have hL2nIso : L₂ ∉ Iso := fun h => (hIsoprop L₂ h).2 c₂ hac2L2.symm hc2deg
  have hL1L2 : L₁ ≠ L₂ := by
    intro he
    exact hT ⟨c₁, c₂, L₁, G.ne_of_adj hc12, he.symm ▸ G.ne_of_adj hac2L2,
      G.ne_of_adj hac1L1, hc12, he.symm ▸ hac2L2, hac1L1, by omega⟩
  have hnc1L2 : ¬G.Adj c₁ L₂ := by
    intro hadj
    have hmem : L₂ ∈ G.neighborFinset c₁ ∩ D :=
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset c₁ L₂).mpr hadj, hL2D⟩
    rw [hNc1D] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h
    · exact (G.ne_of_adj hac2L2) h.symm
    · exact hL1L2 h.symm
  have hubD_ne : ∀ h : Fin 20, h ∈ Dᶜ → h ≠ L₁ ∧ h ≠ c₁ ∧ h ≠ c₂ ∧ h ≠ L₂ := by
    intro h hh
    have hhD : h ∉ D := Finset.mem_compl.mp hh
    exact ⟨fun he => hhD (he ▸ hL1D), fun he => hhD (he ▸ hc1D),
      fun he => hhD (he ▸ hc2D), fun he => hhD (he ▸ hL2D)⟩
  have hge4 : ∀ g : Fin 20, g ∈ Dᶜ → 4 ≤ G.degree g := by
    intro g hg
    have : G.degree g = 4 ∨ G.degree g = 5 := by
      by_cases h5 : g = h₅
      · exact Or.inr (by rw [h5]; exact hh5d)
      · exact Or.inl (hdegOth g hg h5)
    omega
  have hdeg4ne3 : ∀ u w : Fin 20, G.degree u = 4 → G.degree w = 3 → u ≠ w := by
    intro u w hu hw he; rw [he] at hu; omega
  have hIsone : ∀ u w : Fin 20, u ∈ Iso → w ∉ Iso → u ≠ w :=
    fun u w hu hw he => hw (he ▸ hu)
  have hcincA1 : ∀ g : Fin 20, ¬G.Adj g L₁ → ¬G.Adj g c₁ → ¬G.Adj g c₂ →
      (G.neighborFinset g ∩ P).card ≤ 1 := by
    intro g h1 h2 h3
    have hsub : G.neighborFinset g ∩ P ⊆ {L₂} := by
      intro w hw
      obtain ⟨hwN, hwP⟩ := Finset.mem_inter.mp hw
      simp only [hPdef, Finset.mem_insert, Finset.mem_singleton] at hwP
      have hadj := (G.mem_neighborFinset g w).mp hwN
      rcases hwP with rfl | rfl | rfl | rfl
      · exact absurd hadj h1
      · exact absurd hadj h2
      · exact absurd hadj h3
      · exact Finset.mem_singleton_self _
    calc (G.neighborFinset g ∩ P).card ≤ ({L₂} : Finset (Fin 20)).card := Finset.card_le_card hsub
      _ = 1 := Finset.card_singleton _
  have hcincA2 : ∀ g : Fin 20, ¬G.Adj g c₁ → ¬G.Adj g c₂ → ¬G.Adj g L₂ →
      (G.neighborFinset g ∩ P).card ≤ 1 := by
    intro g h1 h2 h3
    have hsub : G.neighborFinset g ∩ P ⊆ {L₁} := by
      intro w hw
      obtain ⟨hwN, hwP⟩ := Finset.mem_inter.mp hw
      simp only [hPdef, Finset.mem_insert, Finset.mem_singleton] at hwP
      have hadj := (G.mem_neighborFinset g w).mp hwN
      rcases hwP with rfl | rfl | rfl | rfl
      · exact Finset.mem_singleton_self _
      · exact absurd hadj h1
      · exact absurd hadj h2
      · exact absurd hadj h3
    calc (G.neighborFinset g ∩ P).card ≤ ({L₁} : Finset (Fin 20)).card := Finset.card_le_card hsub
      _ = 1 := Finset.card_singleton _
  have hcinc0 : ∀ g : Fin 20, ¬G.Adj g L₁ → ¬G.Adj g c₁ → ¬G.Adj g c₂ → ¬G.Adj g L₂ →
      (G.neighborFinset g ∩ P).card = 0 := by
    intro g h1 h2 h3 h4
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro w hw
    obtain ⟨hwN, hwP⟩ := Finset.mem_inter.mp hw
    simp only [hPdef, Finset.mem_insert, Finset.mem_singleton] at hwP
    have hadj := (G.mem_neighborFinset g w).mp hwN
    rcases hwP with rfl | rfl | rfl | rfl
    · exact h1 hadj
    · exact h2 hadj
    · exact h3 hadj
    · exact h4 hadj
  have hpurecardA2 : ∀ x : Fin 20, ¬G.Adj x c₁ → ¬G.Adj x c₂ → ¬G.Adj x L₂ →
      (G.neighborFinset x ∩ ({c₁, c₂, L₂} : Finset (Fin 20))).card = 0 := by
    intro x h1 h2 h3
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro w hw
    obtain ⟨hwN, hwm⟩ := Finset.mem_inter.mp hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hwm
    have hadj := (G.mem_neighborFinset x w).mp hwN
    rcases hwm with rfl | rfl | rfl
    · exact h1 hadj
    · exact h2 hadj
    · exact h3 hadj
  -- **The two cherry-avoider families.**
  set A1 : Finset (Fin 20) :=
    Dᶜ.filter (fun h => ¬G.Adj h L₁ ∧ ¬G.Adj h c₁ ∧ ¬G.Adj h c₂) with hA1def
  set A2 : Finset (Fin 20) :=
    Dᶜ.filter (fun h => ¬G.Adj h c₁ ∧ ¬G.Adj h c₂ ∧ ¬G.Adj h L₂) with hA2def
  set FF : Finset (Fin 20) := A1 ∩ A2 with hFFdef
  have hA1sub : A1 ⊆ Dᶜ := by rw [hA1def]; exact Finset.filter_subset _ _
  have hA2sub : A2 ⊆ Dᶜ := by rw [hA2def]; exact Finset.filter_subset _ _
  have hUsub : A1 ∪ A2 ⊆ Dᶜ := Finset.union_subset hA1sub hA2sub
  have hA1card : 7 ≤ A1.card := by
    have hcover : Dᶜ ⊆ A1 ∪ ((G.neighborFinset L₁ ∩ Dᶜ) ∪
        ((G.neighborFinset c₁ ∩ Dᶜ) ∪ (G.neighborFinset c₂ ∩ Dᶜ))) := by
      intro x hx
      by_cases hp : ¬G.Adj x L₁ ∧ ¬G.Adj x c₁ ∧ ¬G.Adj x c₂
      · exact Finset.mem_union_left _ (by rw [hA1def]; exact Finset.mem_filter.mpr ⟨hx, hp⟩)
      · refine Finset.mem_union_right _ ?_
        by_cases hxL1 : G.Adj x L₁
        · exact Finset.mem_union_left _
            (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset L₁ x).mpr hxL1.symm, hx⟩)
        · by_cases hxc1 : G.Adj x c₁
          · exact Finset.mem_union_right _ (Finset.mem_union_left _
              (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset c₁ x).mpr hxc1.symm, hx⟩))
          · by_cases hxc2 : G.Adj x c₂
            · exact Finset.mem_union_right _ (Finset.mem_union_right _
                (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset c₂ x).mpr hxc2.symm, hx⟩))
            · exact absurd ⟨hxL1, hxc1, hxc2⟩ hp
    have u2 := Finset.card_union_le (G.neighborFinset c₁ ∩ Dᶜ) (G.neighborFinset c₂ ∩ Dᶜ)
    have u1 := Finset.card_union_le (G.neighborFinset L₁ ∩ Dᶜ)
      ((G.neighborFinset c₁ ∩ Dᶜ) ∪ (G.neighborFinset c₂ ∩ Dᶜ))
    rw [hc1hub, hc2hub] at u2
    rw [hL1hub] at u1
    have hcov := Finset.card_le_card hcover
    have hun := Finset.card_union_le A1 ((G.neighborFinset L₁ ∩ Dᶜ) ∪
      ((G.neighborFinset c₁ ∩ Dᶜ) ∪ (G.neighborFinset c₂ ∩ Dᶜ)))
    rw [hHub11] at hcov; omega
  have hA2card : 7 ≤ A2.card := by
    have hcover : Dᶜ ⊆ A2 ∪ ((G.neighborFinset c₁ ∩ Dᶜ) ∪
        ((G.neighborFinset c₂ ∩ Dᶜ) ∪ (G.neighborFinset L₂ ∩ Dᶜ))) := by
      intro x hx
      by_cases hp : ¬G.Adj x c₁ ∧ ¬G.Adj x c₂ ∧ ¬G.Adj x L₂
      · exact Finset.mem_union_left _ (by rw [hA2def]; exact Finset.mem_filter.mpr ⟨hx, hp⟩)
      · refine Finset.mem_union_right _ ?_
        by_cases hxc1 : G.Adj x c₁
        · exact Finset.mem_union_left _
            (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset c₁ x).mpr hxc1.symm, hx⟩)
        · by_cases hxc2 : G.Adj x c₂
          · exact Finset.mem_union_right _ (Finset.mem_union_left _
              (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset c₂ x).mpr hxc2.symm, hx⟩))
          · by_cases hxL2 : G.Adj x L₂
            · exact Finset.mem_union_right _ (Finset.mem_union_right _
                (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset L₂ x).mpr hxL2.symm, hx⟩))
            · exact absurd ⟨hxc1, hxc2, hxL2⟩ hp
    have u2 := Finset.card_union_le (G.neighborFinset c₂ ∩ Dᶜ) (G.neighborFinset L₂ ∩ Dᶜ)
    have u1 := Finset.card_union_le (G.neighborFinset c₁ ∩ Dᶜ)
      ((G.neighborFinset c₂ ∩ Dᶜ) ∪ (G.neighborFinset L₂ ∩ Dᶜ))
    rw [hc2hub, hL2hub] at u2
    rw [hc1hub] at u1
    have hcov := Finset.card_le_card hcover
    have hun := Finset.card_union_le A2 ((G.neighborFinset c₁ ∩ Dᶜ) ∪
      ((G.neighborFinset c₂ ∩ Dᶜ) ∪ (G.neighborFinset L₂ ∩ Dᶜ)))
    rw [hHub11] at hcov; omega
  -- **Internal-mass lower bounds.**
  have hb2 : ∀ g ∈ A1 ∪ A2, 2 ≤ (G.neighborFinset g ∩ Dᶜ).card := by
    intro g hg
    rcases Finset.mem_union.mp hg with hgA1 | hgA2
    · rw [hA1def, Finset.mem_filter] at hgA1
      obtain ⟨hgDc, hnL1, hnc1, hnc2⟩ := hgA1
      obtain ⟨hne_L1, hne_c1, hne_c2, _⟩ := hubD_ne g hgDc
      have hiso1 : (G.neighborFinset g ∩ Iso).card ≤ 1 := by
        by_contra hgt; push Not at hgt
        exact htt (twotwin_of_centre_twenty G Iso g L₁ c₁ c₂ hIsoprop hL1deg hc1deg hc2deg
          (hdeg5 g hgDc) hac1L1.symm hc12 hnL1 hnc1 hnc2 hL1nIso hc1nIso hc2nIso
          hne_L1 hne_c1 hne_c2 (G.ne_of_adj hac1L1).symm (G.ne_of_adj hc12) hL1nc2 (by omega))
      have hcinc := hcincA1 g hnL1 hnc1 hnc2
      have hdec := hper g hgDc
      have hge := hge4 g hgDc
      omega
    · rw [hA2def, Finset.mem_filter] at hgA2
      obtain ⟨hgDc, hnc1, hnc2, hnL2⟩ := hgA2
      obtain ⟨_, hne_c1, hne_c2, hne_L2⟩ := hubD_ne g hgDc
      have hiso1 : (G.neighborFinset g ∩ Iso).card ≤ 1 := by
        by_contra hgt; push Not at hgt
        exact htt (twotwin_of_centre_twenty G Iso g c₁ c₂ L₂ hIsoprop hc1deg hc2deg hL2deg
          (hdeg5 g hgDc) hc12 hac2L2 hnc1 hnc2 hnL2 hc1nIso hc2nIso hL2nIso
          hne_c1 hne_c2 hne_L2 (G.ne_of_adj hc12) (G.ne_of_adj hac2L2) (Ne.symm hL2nc1) (by omega))
      have hcinc := hcincA2 g hnc1 hnc2 hnL2
      have hdec := hper g hgDc
      have hge := hge4 g hgDc
      omega
  have hb3 : ∀ g ∈ FF, 3 ≤ (G.neighborFinset g ∩ Dᶜ).card := by
    intro g hg
    have hgA1 : g ∈ A1 := Finset.mem_of_mem_inter_left (hFFdef ▸ hg)
    have hgA2 : g ∈ A2 := Finset.mem_of_mem_inter_right (hFFdef ▸ hg)
    rw [hA1def, Finset.mem_filter] at hgA1
    obtain ⟨hgDc, hnL1, hnc1, hnc2⟩ := hgA1
    rw [hA2def, Finset.mem_filter] at hgA2
    obtain ⟨_, _, _, hnL2⟩ := hgA2
    obtain ⟨hne_L1, hne_c1, hne_c2, _⟩ := hubD_ne g hgDc
    have hiso1 : (G.neighborFinset g ∩ Iso).card ≤ 1 := by
      by_contra hgt; push Not at hgt
      exact htt (twotwin_of_centre_twenty G Iso g L₁ c₁ c₂ hIsoprop hL1deg hc1deg hc2deg
        (hdeg5 g hgDc) hac1L1.symm hc12 hnL1 hnc1 hnc2 hL1nIso hc1nIso hc2nIso
        hne_L1 hne_c1 hne_c2 (G.ne_of_adj hac1L1).symm (G.ne_of_adj hc12) hL1nc2 (by omega))
    have hcinc0v := hcinc0 g hnL1 hnc1 hnc2 hnL2
    have hdec := hper g hgDc
    have hge := hge4 g hgDc
    omega
  have hb1 : ∀ g ∈ Dᶜ, g ∉ A1 ∪ A2 → g ≠ h₅ → 1 ≤ (G.neighborFinset g ∩ Dᶜ).card := by
    intro g hgDc _ hgne5
    have hd4 := hdegOth g hgDc hgne5
    have := hID40 g hgDc hd4
    omega
  -- **Apply the tie.**
  have hextr := tie_extract_eleven Dᶜ A1 A2 FF (fun g => (G.neighborFinset g ∩ Dᶜ).card) h₅
    hUsub hFFdef hHub11 hA1card hA2card hb2 hb3 hb1 hsumInt
  -- **Every `A2`-hub `≠ h₅` carries an `Iso` twin.**
  have hOthiso1 : ∀ g : Fin 20, g ∈ A2 → g ≠ h₅ → 1 ≤ (G.neighborFinset g ∩ Iso).card := by
    intro g hgA2 hgne5
    have hgU : g ∈ A1 ∪ A2 := Finset.mem_union_right _ hgA2
    have hgA2f := hgA2
    rw [hA2def, Finset.mem_filter] at hgA2f
    obtain ⟨hgDc, hnc1, hnc2, hnL2⟩ := hgA2f
    have hd4 := hdegOth g hgDc hgne5
    have hdec := hper g hgDc
    by_cases hgFF : g ∈ FF
    · have hint3 := hextr.2 g hgFF
      have hgA1 : g ∈ A1 := Finset.mem_of_mem_inter_left (hFFdef ▸ hgFF)
      rw [hA1def, Finset.mem_filter] at hgA1
      obtain ⟨_, hnL1, _, _⟩ := hgA1
      have hcinc0v := hcinc0 g hnL1 hnc1 hnc2 hnL2
      omega
    · have hint2 := hextr.1 g hgU hgFF
      have hcinc := hcincA2 g hnc1 hnc2 hnL2
      omega
  -- **Pigeonhole `A2 ∖ {h₅}` (`≥ 6` hubs) into the five `Iso` twins.**
  set f : Fin 20 → Fin 20 :=
    fun x => if hx : (G.neighborFinset x ∩ Iso).Nonempty then hx.choose else x
    with hfdef
  have hftwin : ∀ g ∈ A2.erase h₅, G.Adj g (f g) ∧ f g ∈ Iso := by
    intro g hg
    have hgA2 := Finset.mem_of_mem_erase hg
    have hgne5 := Finset.ne_of_mem_erase hg
    have hne : (G.neighborFinset g ∩ Iso).Nonempty :=
      Finset.card_pos.mp (by have := hOthiso1 g hgA2 hgne5; omega)
    have hmem : f g ∈ G.neighborFinset g ∩ Iso := by
      simp only [hfdef, dif_pos hne]; exact hne.choose_spec
    obtain ⟨hN, hI⟩ := Finset.mem_inter.mp hmem
    exact ⟨(G.mem_neighborFinset g (f g)).mp hN, hI⟩
  have hdomcard : 5 < (A2.erase h₅).card := by
    by_cases h5A2 : h₅ ∈ A2
    · rw [Finset.card_erase_of_mem h5A2]; omega
    · rw [Finset.erase_eq_of_notMem h5A2]; omega
  obtain ⟨F, hFmem, F', hF'mem, hFF', hff⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to
      (s := A2.erase h₅) (t := Iso) (f := f) (by rw [hIsocard]; exact hdomcard)
      (by
        intro g hg
        rw [Finset.mem_coe] at hg
        exact Finset.mem_coe.mpr (hftwin g hg).2)
  have htwI : f F ∈ Iso := (hftwin F hFmem).2
  have hAFt : G.Adj F (f F) := (hftwin F hFmem).1
  have hAF't : G.Adj F' (f F) := by
    have h := (hftwin F' hF'mem).1; rwa [← hff] at h
  have hFne5 : F ≠ h₅ := Finset.ne_of_mem_erase hFmem
  have hF'ne5 : F' ≠ h₅ := Finset.ne_of_mem_erase hF'mem
  have hFA2 : F ∈ A2 := Finset.mem_of_mem_erase hFmem
  have hF'A2 : F' ∈ A2 := Finset.mem_of_mem_erase hF'mem
  rw [hA2def, Finset.mem_filter] at hFA2 hF'A2
  obtain ⟨hFDc, hFnc1, hFnc2, hFnL2⟩ := hFA2
  obtain ⟨hF'Dc, hF'nc1, hF'nc2, hF'nL2⟩ := hF'A2
  have hdF : G.degree F = 4 := hdegOth F hFDc hFne5
  have hdF' : G.degree F' = 4 := hdegOth F' hF'Dc hF'ne5
  have hdegfF : G.degree (f F) = 3 := (hIsoprop (f F) htwI).1
  by_cases hadjFF' : G.Adj F F'
  · exact hT ⟨F, F', f F, hFF', hdeg4ne3 F' (f F) hdF' hdegfF,
      hdeg4ne3 F (f F) hdF hdegfF, hadjFF', hAF't, hAFt, by omega⟩
  · refine hsv ⟨f F, F, F', c₁, c₂, L₂, hdegfF, hc1deg, hc2deg, hL2deg,
      hAFt.symm, hAF't.symm, hc12, hac2L2, hnc1L2, ?_,
      hFF', hIsone (f F) c₁ htwI hc1nIso, hIsone (f F) c₂ htwI hc2nIso,
      hIsone (f F) L₂ htwI hL2nIso, hdeg4ne3 F c₁ hdF hc1deg,
      hdeg4ne3 F c₂ hdF hc2deg, hdeg4ne3 F L₂ hdF hL2deg,
      hdeg4ne3 F' c₁ hdF' hc1deg, hdeg4ne3 F' c₂ hdF' hc2deg,
      hdeg4ne3 F' L₂ hdF' hL2deg, G.ne_of_adj hc12, G.ne_of_adj hac2L2, Ne.symm hL2nc1⟩
    have hsum0 : (∑ p ∈ ({f F, F, F'} : Finset (Fin 20)),
        (G.neighborFinset p ∩ ({c₁, c₂, L₂} : Finset (Fin 20))).card) = 0 := by
      apply Finset.sum_eq_zero
      intro p hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | hpF | hpF'
      · exact hpurecardA2 (f F) (hIso_nadj (f F) htwI c₁ hc1deg)
          (hIso_nadj (f F) htwI c₂ hc2deg) (hIso_nadj (f F) htwI L₂ hL2deg)
      · rw [hpF]; exact hpurecardA2 F hFnc1 hFnc2 hFnL2
      · rw [hpF']; exact hpurecardA2 F' hF'nc1 hF'nc2 hF'nL2
    rw [hsum0, if_neg hadjFF']; omega

end N20

end ACMax
