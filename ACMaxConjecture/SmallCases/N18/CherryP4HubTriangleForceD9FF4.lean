import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.Certificates
import ACMaxConjecture.SmallCases.N18.Core
import ACMaxConjecture.SmallCases.N18.Align8Helpers
import ACMaxConjecture.SmallCases.N18.CherryP4HubTriangleShare

/-!
# The `n = 18`, `P₄`-cherry, `|D| = 9`, `|FF| = 4` hub-triangle escape corner

This file closes the lone documented `sorry` of `iso_rich_force_p4_eighteen` (the `|D| = 9`,
`|FF| = 4` branch).  At that point there are `9` hubs of degree `∈ {4, 5}` with `∑ deg = 37`
(exactly one degree-`5` hub) and total internal incidence `16`.  The avoider analysis forces:

* **`zero_internal_hubs_d9_ff4`** — the `6` avoiders `A1 ∪ A2` (with `FF = A1 ∩ A2`, `|FF| = 4`)
  consume all `16` internal incidences, so the `3` non-avoiders have `0` hub-neighbours; two of
  them are degree-`4`.
* **`isolated_hub_iso_rich_d9_ff4`** — one of those two isolated degree-`4` hubs has `≥ 3`
  `M`-isolated neighbours (at most one cherry neighbour), because two hubs each adjacent to two
  cherry vertices would force a good triangle (`hT`) or a good `C₄` (`hC4`).
* **`two_isolated_hub_twohubconfig_d9_ff4`** — the `Iso`-rich isolated hub and its companion
  package into a `TwoHubConfig`, contradicting `hth`.
-/

namespace ACMax

open scoped Classical

namespace N18

/-- **Node 1.**  In the `|D| = 9`, `|FF| = 4` regime the six avoiders `A1 ∪ A2` already carry all
`16` internal hub-incidences, so the three non-avoiders are isolated in `Dᶜ`; two of them have
degree `4`. -/
theorem zero_internal_hubs_d9_ff4 (G : SimpleGraph (Fin 18)) (D A1 A2 FF : Finset (Fin 18))
    (hA1sub : A1 ⊆ Dᶜ) (hA2sub : A2 ⊆ Dᶜ) (hFF : FF = A1 ∩ A2)
    (hA1c : A1.card = 5) (hA2c : A2.card = 5) (hFF4 : FF.card = 4)
    (hA1int : ∀ g ∈ A1, 2 ≤ (G.neighborFinset g ∩ Dᶜ).card)
    (hA2int : ∀ g ∈ A2, 2 ≤ (G.neighborFinset g ∩ Dᶜ).card)
    (hFFint : ∀ g ∈ FF, 3 ≤ (G.neighborFinset g ∩ Dᶜ).card)
    (hint16 : ∑ g ∈ Dᶜ, (G.neighborFinset g ∩ Dᶜ).card = 16)
    (hdeg37 : ∑ g ∈ Dᶜ, G.degree g = 37)
    (hge4 : ∀ g ∈ Dᶜ, 4 ≤ G.degree g) (hdeg5 : ∀ g ∈ Dᶜ, G.degree g ≤ 5)
    (hDc9 : Dᶜ.card = 9) :
    ∃ h₁ h₂ : Fin 18, h₁ ∈ Dᶜ \ (A1 ∪ A2) ∧ h₂ ∈ Dᶜ \ (A1 ∪ A2) ∧ h₁ ≠ h₂ ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧
      G.neighborFinset h₁ ∩ Dᶜ = ∅ ∧ G.neighborFinset h₂ ∩ Dᶜ = ∅ := by
  classical
  set f : Fin 18 → ℕ := fun g => (G.neighborFinset g ∩ Dᶜ).card with hf
  have hFFsubA1 : FF ⊆ A1 := by rw [hFF]; exact Finset.inter_subset_left
  have hFFsubA2 : FF ⊆ A2 := by rw [hFF]; exact Finset.inter_subset_right
  have hUsub : A1 ∪ A2 ⊆ Dᶜ := Finset.union_subset hA1sub hA2sub
  -- Cardinalities of the avoider pieces.
  have hA1FF : (A1 \ FF).card = 1 := by
    have h := Finset.card_sdiff_add_card_inter A1 FF
    rw [Finset.inter_eq_right.mpr hFFsubA1] at h; omega
  have hA2A1 : (A2 \ A1).card = 1 := by
    have h := Finset.card_sdiff_add_card_inter A2 A1
    have : (A2 ∩ A1).card = FF.card := by rw [hFF, Finset.inter_comm]
    omega
  have hUcard : (A1 ∪ A2).card = 6 := by
    have h := Finset.card_union_add_card_inter A1 A2
    rw [← hFF] at h; omega
  -- Lower bound on the avoider internal mass.
  have hUlb : 16 ≤ ∑ g ∈ A1 ∪ A2, f g := by
    have hdisj : Disjoint A1 (A2 \ A1) := Finset.disjoint_sdiff
    have hunion : A1 ∪ (A2 \ A1) = A1 ∪ A2 := Finset.union_sdiff_self_eq_union
    have hsplitU : ∑ g ∈ A1 ∪ A2, f g = (∑ g ∈ A1, f g) + ∑ g ∈ A2 \ A1, f g := by
      rw [← hunion, Finset.sum_union hdisj]
    have hA1split : (∑ g ∈ A1 \ FF, f g) + ∑ g ∈ FF, f g = ∑ g ∈ A1, f g :=
      Finset.sum_sdiff hFFsubA1
    have hmf : 2 * (A1 \ FF).card ≤ ∑ g ∈ A1 \ FF, f g := by
      have := Finset.card_nsmul_le_sum (A1 \ FF) f 2
        (fun g hg => hA1int g (Finset.mem_sdiff.mp hg).1)
      simpa [smul_eq_mul, Nat.mul_comm] using this
    have hFFlb : 3 * FF.card ≤ ∑ g ∈ FF, f g := by
      have := Finset.card_nsmul_le_sum FF f 3 hFFint
      simpa [smul_eq_mul, Nat.mul_comm] using this
    have hA2A1lb : 2 * (A2 \ A1).card ≤ ∑ g ∈ A2 \ A1, f g := by
      have := Finset.card_nsmul_le_sum (A2 \ A1) f 2
        (fun g hg => hA2int g (Finset.mem_sdiff.mp hg).1)
      simpa [smul_eq_mul, Nat.mul_comm] using this
    rw [hsplitU, ← hA1split]; rw [hA1FF, hA2A1, hFF4] at *; omega
  -- The non-avoiders carry zero internal mass.
  have hsdiff : (∑ g ∈ Dᶜ \ (A1 ∪ A2), f g) + ∑ g ∈ A1 ∪ A2, f g = ∑ g ∈ Dᶜ, f g :=
    Finset.sum_sdiff hUsub
  have hTzero : ∑ g ∈ Dᶜ \ (A1 ∪ A2), f g = 0 := by
    have : ∑ g ∈ Dᶜ, f g = 16 := hint16
    omega
  have hTcard : (Dᶜ \ (A1 ∪ A2)).card = 3 := by
    rw [Finset.card_sdiff_of_subset hUsub, hUcard, hDc9]
  have hTint : ∀ g ∈ Dᶜ \ (A1 ∪ A2), G.neighborFinset g ∩ Dᶜ = ∅ := by
    intro g hg
    have hfg : f g = 0 := by
      by_contra hne
      have : 0 < ∑ g ∈ Dᶜ \ (A1 ∪ A2), f g :=
        Finset.sum_pos' (fun _ _ => Nat.zero_le _) ⟨g, hg, Nat.pos_of_ne_zero hne⟩
      omega
    simpa [hf, Finset.card_eq_zero] using hfg
  -- Exactly one degree-`5` hub, so at least two of the three non-avoiders are degree `4`.
  set T : Finset (Fin 18) := Dᶜ \ (A1 ∪ A2) with hTdef
  have hTsub : T ⊆ Dᶜ := Finset.sdiff_subset
  have hdeg5count : (Dᶜ.filter (fun g => G.degree g = 5)).card = 1 := by
    have hpart := Finset.sum_filter_add_sum_filter_not Dᶜ (fun g => G.degree g = 5)
      (fun g => G.degree g)
    have h4 : ∀ g ∈ Dᶜ.filter (fun g => ¬ G.degree g = 5), G.degree g = 4 := by
      intro g hg
      rw [Finset.mem_filter] at hg
      have := hge4 g hg.1; have := hdeg5 g hg.1; omega
    have h5 : ∀ g ∈ Dᶜ.filter (fun g => G.degree g = 5), G.degree g = 5 := by
      intro g hg; exact (Finset.mem_filter.mp hg).2
    rw [Finset.sum_congr rfl h5, Finset.sum_congr rfl h4, Finset.sum_const, Finset.sum_const,
      smul_eq_mul, smul_eq_mul] at hpart
    have hcc : (Dᶜ.filter (fun g => G.degree g = 5)).card
        + (Dᶜ.filter (fun g => ¬ G.degree g = 5)).card = 9 := by
      rw [Finset.card_filter_add_card_filter_not]; exact hDc9
    rw [hdeg37] at hpart; omega
  have hT4card : 2 ≤ (T.filter (fun g => G.degree g = 4)).card := by
    have hsub5 : T.filter (fun g => G.degree g = 5) ⊆ Dᶜ.filter (fun g => G.degree g = 5) :=
      Finset.filter_subset_filter _ hTsub
    have hle5 : (T.filter (fun g => G.degree g = 5)).card ≤ 1 := by
      rw [← hdeg5count]; exact Finset.card_le_card hsub5
    have hpartT := Finset.card_filter_add_card_filter_not (s := T)
      (p := fun g => G.degree g = 5)
    have h45 : T.filter (fun g => ¬ G.degree g = 5) = T.filter (fun g => G.degree g = 4) := by
      apply Finset.filter_congr
      intro g hg
      have hgDc := hTsub hg
      have := hge4 g hgDc; have := hdeg5 g hgDc
      constructor <;> intro <;> omega
    rw [h45] at hpartT; omega
  obtain ⟨h₁, h1mem, h₂, h2mem, hne⟩ := Finset.one_lt_card.mp
    (by omega : 1 < (T.filter (fun g => G.degree g = 4)).card)
  rw [Finset.mem_filter] at h1mem h2mem
  exact ⟨h₁, h₂, h1mem.1, h2mem.1, hne, h1mem.2, h2mem.2,
    hTint h₁ h1mem.1, hTint h₂ h2mem.1⟩

/-- **Single-hub path dichotomy.**  A degree-`4` hub `h` adjacent to at least two cherry-path
vertices (`{L₁, c₁, c₂, L₂}`) must in fact be adjacent to exactly the two leaves `L₁, L₂` (and to
neither `c₁` nor `c₂`): any other pair of path-neighbours produces either a good triangle (cherry
edge plus `h`, degree sum `4 + 3 + 3 = 10 ≤ 10`) or a good `C₄` (degree sum `4 + 3 + 3 + 3 = 13 ≤
14`), excluded by `hT`/`hC4`. -/
theorem deg4_path_bad_of_two (G : SimpleGraph (Fin 18)) (L₁ c₁ c₂ L₂ h : Fin 18)
    (hT : ¬∃ x y z : Fin 18, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    (hC4 : ¬∃ a b c d : Fin 18, ({a, b, c, d} : Finset (Fin 18)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (hac1L1 : G.Adj c₁ L₁) (hc12 : G.Adj c₁ c₂) (hac2L2 : G.Adj c₂ L₂)
    (hnc1L2 : ¬G.Adj c₁ L₂) (hnc2L1 : ¬G.Adj c₂ L₁)
    (hL1nc2 : L₁ ≠ c₂) (hL2nc1 : L₂ ≠ c₁)
    (hL1d : G.degree L₁ = 3) (hc1d : G.degree c₁ = 3)
    (hc2d : G.degree c₂ = 3) (hL2d : G.degree L₂ = 3) (hhd : G.degree h = 4)
    (hp2 : 2 ≤ (G.neighborFinset h ∩ ({L₁, c₁, c₂, L₂} : Finset (Fin 18))).card) :
    G.Adj h L₁ ∧ G.Adj h L₂ ∧ ¬G.Adj h c₁ ∧ ¬G.Adj h c₂ := by
  classical
  -- Distinctness.
  have hne_hc1 : h ≠ c₁ := by intro he; rw [he] at hhd; omega
  have hne_hc2 : h ≠ c₂ := by intro he; rw [he] at hhd; omega
  have hne_hL1 : h ≠ L₁ := by intro he; rw [he] at hhd; omega
  have hne_hL2 : h ≠ L₂ := by intro he; rw [he] at hhd; omega
  have hc1L1 : c₁ ≠ L₁ := (G.ne_of_adj hac1L1)
  have hc1c2 : c₁ ≠ c₂ := (G.ne_of_adj hc12)
  have hc2L2 : c₂ ≠ L₂ := (G.ne_of_adj hac2L2)
  have hc1L2 : c₁ ≠ L₂ := Ne.symm hL2nc1
  have hL1L2 : L₁ ≠ L₂ := by
    intro he; apply hnc1L2; rw [← he]; exact hac1L1
  -- Pair-membership helper.
  have pair_mem : ∀ (S : Finset (Fin 18)) (a b : Fin 18), a ≠ b → S ⊆ {a, b} → 2 ≤ S.card →
      a ∈ S ∧ b ∈ S := by
    intro S a b hab hsub hcard
    have hcab : ({a, b} : Finset (Fin 18)).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simp [hab]), Finset.card_singleton]
    have heq : S = {a, b} := Finset.eq_of_subset_of_card_le hsub (by omega)
    rw [heq]; exact ⟨by simp, by simp⟩
  -- Card-`4` of the path set (for the `C₄` witnesses).
  have hP4 : ({h, c₁, c₂, L₂} : Finset (Fin 18)).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [hne_hc1, hne_hc2, hne_hL2]),
      Finset.card_insert_of_notMem (by simp [hc1c2, hc1L2]),
      Finset.card_insert_of_notMem (by simp [hc2L2]), Finset.card_singleton]
  have hP4' : ({h, c₂, c₁, L₁} : Finset (Fin 18)).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [hne_hc2, hne_hc1, hne_hL1]),
      Finset.card_insert_of_notMem (by simp [Ne.symm hc1c2, Ne.symm hL1nc2]),
      Finset.card_insert_of_notMem (by simp [hc1L1]), Finset.card_singleton]
  -- `¬ G.Adj h c₁`.
  have hnc1 : ¬G.Adj h c₁ := by
    intro hhc1
    by_cases hhL1 : G.Adj h L₁
    · exact hT ⟨h, c₁, L₁, hne_hc1, hc1L1, hne_hL1, hhc1, hac1L1, hhL1, by omega⟩
    · by_cases hhc2 : G.Adj h c₂
      · exact hT ⟨h, c₁, c₂, hne_hc1, hc1c2, hne_hc2, hhc1, hc12, hhc2, by omega⟩
      · have hsub : G.neighborFinset h ∩ ({L₁, c₁, c₂, L₂} : Finset (Fin 18)) ⊆ {c₁, L₂} := by
          intro x hx
          rw [Finset.mem_inter, G.mem_neighborFinset] at hx
          obtain ⟨hadj, hxP⟩ := hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hxP ⊢
          rcases hxP with rfl | rfl | rfl | rfl
          · exact absurd hadj hhL1
          · exact Or.inl rfl
          · exact absurd hadj hhc2
          · exact Or.inr rfl
        obtain ⟨_, hmL2⟩ := pair_mem _ c₁ L₂ hc1L2 hsub hp2
        have hhL2 : G.Adj h L₂ :=
          (G.mem_neighborFinset h L₂).mp (Finset.mem_inter.mp hmL2).1
        exact hC4 ⟨h, c₁, c₂, L₂, hP4, hhc1, hc12, hac2L2, hhL2.symm, hhc2, hnc1L2, by omega⟩
  -- `¬ G.Adj h c₂`.
  have hnc2 : ¬G.Adj h c₂ := by
    intro hhc2
    by_cases hhL2 : G.Adj h L₂
    · exact hT ⟨h, c₂, L₂, hne_hc2, hc2L2, hne_hL2, hhc2, hac2L2, hhL2, by omega⟩
    · have hhc1 : ¬G.Adj h c₁ := hnc1
      have hsub : G.neighborFinset h ∩ ({L₁, c₁, c₂, L₂} : Finset (Fin 18)) ⊆ {c₂, L₁} := by
        intro x hx
        rw [Finset.mem_inter, G.mem_neighborFinset] at hx
        obtain ⟨hadj, hxP⟩ := hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hxP ⊢
        rcases hxP with rfl | rfl | rfl | rfl
        · exact Or.inr rfl
        · exact absurd hadj hhc1
        · exact Or.inl rfl
        · exact absurd hadj hhL2
      obtain ⟨_, hmL1⟩ := pair_mem _ c₂ L₁ (Ne.symm hL1nc2) hsub hp2
      have hhL1 : G.Adj h L₁ :=
        (G.mem_neighborFinset h L₁).mp (Finset.mem_inter.mp hmL1).1
      exact hC4 ⟨h, c₂, c₁, L₁, hP4', hhc2, hc12.symm, hac1L1, hhL1.symm, hhc1, hnc2L1, by omega⟩
  -- Both leaves are neighbours.
  have hsub : G.neighborFinset h ∩ ({L₁, c₁, c₂, L₂} : Finset (Fin 18)) ⊆ {L₁, L₂} := by
    intro x hx
    rw [Finset.mem_inter, G.mem_neighborFinset] at hx
    obtain ⟨hadj, hxP⟩ := hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxP ⊢
    rcases hxP with rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact absurd hadj hnc1
    · exact absurd hadj hnc2
    · exact Or.inr rfl
  obtain ⟨hmL1, hmL2⟩ := pair_mem _ L₁ L₂ hL1L2 hsub hp2
  refine ⟨(G.mem_neighborFinset h L₁).mp (Finset.mem_inter.mp hmL1).1,
    (G.mem_neighborFinset h L₂).mp (Finset.mem_inter.mp hmL2).1, hnc1, hnc2⟩

/-- **Node 2.**  Of the two isolated degree-`4` hubs at least one has `≥ 3` `M`-isolated neighbours
(at most one cherry-path neighbour).  Were both adjacent to `≥ 2` cherry vertices, the single-hub
dichotomy would force each adjacent to both leaves `L₁, L₂`; together with a third hub-neighbour of
`L₁` (`hL1other`) that contradicts `|N L₁ ∩ Dᶜ| = 2`. -/
theorem isolated_hub_iso_rich_d9_ff4 (G : SimpleGraph (Fin 18)) (D Iso : Finset (Fin 18))
    (L₁ c₁ c₂ L₂ h₁ h₂ : Fin 18)
    (hT : ¬∃ x y z : Fin 18, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    (hC4 : ¬∃ a b c d : Fin 18, ({a, b, c, d} : Finset (Fin 18)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (hclassP : ∀ x ∈ D, x = L₁ ∨ x = c₁ ∨ x = c₂ ∨ x = L₂ ∨ x ∈ Iso)
    (hIsoprop : ∀ v ∈ Iso, G.degree v = 3 ∧ (∀ w : Fin 18, G.Adj v w → G.degree w ≠ 3))
    (hac1L1 : G.Adj c₁ L₁) (hc12 : G.Adj c₁ c₂) (hac2L2 : G.Adj c₂ L₂)
    (hnc1L2 : ¬G.Adj c₁ L₂) (hnc2L1 : ¬G.Adj c₂ L₁)
    (hL1nc2 : L₁ ≠ c₂) (hL2nc1 : L₂ ≠ c₁)
    (hL1d : G.degree L₁ = 3) (hc1d : G.degree c₁ = 3)
    (hc2d : G.degree c₂ = 3) (hL2d : G.degree L₂ = 3)
    (hh1Dc : h₁ ∈ Dᶜ) (hh2Dc : h₂ ∈ Dᶜ) (hh1d : G.degree h₁ = 4) (hh2d : G.degree h₂ = 4)
    (hh10 : G.neighborFinset h₁ ∩ Dᶜ = ∅) (hh20 : G.neighborFinset h₂ ∩ Dᶜ = ∅)
    (hne12 : h₁ ≠ h₂) (hL1hub : (G.neighborFinset L₁ ∩ Dᶜ).card = 2)
    (hL1other : ∃ x : Fin 18, x ∈ Dᶜ ∧ x ≠ h₁ ∧ x ≠ h₂ ∧ G.Adj x L₁) :
    3 ≤ (G.neighborFinset h₁ ∩ Iso).card ∨ 3 ≤ (G.neighborFinset h₂ ∩ Iso).card := by
  classical
  set P : Finset (Fin 18) := {L₁, c₁, c₂, L₂} with hPdef
  -- Path vertices are not `M`-isolated, so `P` and `Iso` are disjoint.
  have hPnotIso : ∀ x ∈ P, x ∉ Iso := by
    intro x hx hxIso
    simp only [hPdef, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact (hIsoprop x hxIso).2 c₁ hac1L1.symm hc1d
    · exact (hIsoprop x hxIso).2 c₂ hc12 hc2d
    · exact (hIsoprop x hxIso).2 c₁ hc12.symm hc1d
    · exact (hIsoprop x hxIso).2 c₂ hac2L2.symm hc2d
  have hdisjPI : Disjoint P Iso := by
    rw [Finset.disjoint_left]; intro x hxP hxIso; exact hPnotIso x hxP hxIso
  -- For an isolated degree-`4` hub, `|N ∩ Iso| + |N ∩ P| = 4`.
  have iso_count : ∀ h : Fin 18, G.neighborFinset h ∩ Dᶜ = ∅ → G.degree h = 4 →
      (G.neighborFinset h ∩ Iso).card + (G.neighborFinset h ∩ P).card = 4 := by
    intro h hh0 hhd
    have hsubD : G.neighborFinset h ⊆ D := by
      intro x hx
      by_contra hxD
      have hmem : x ∈ G.neighborFinset h ∩ Dᶜ :=
        Finset.mem_inter.mpr ⟨hx, Finset.mem_compl.mpr hxD⟩
      rw [hh0] at hmem; exact absurd hmem (Finset.notMem_empty x)
    have hsubPI : G.neighborFinset h ⊆ P ∪ Iso := by
      intro x hx
      rcases hclassP x (hsubD hx) with h' | h' | h' | h' | h'
      · exact Finset.mem_union_left _ (by simp [hPdef, h'])
      · exact Finset.mem_union_left _ (by simp [hPdef, h'])
      · exact Finset.mem_union_left _ (by simp [hPdef, h'])
      · exact Finset.mem_union_left _ (by simp [hPdef, h'])
      · exact Finset.mem_union_right _ h'
    have hdisj' : Disjoint (G.neighborFinset h ∩ P) (G.neighborFinset h ∩ Iso) := by
      apply Finset.disjoint_left.mpr
      intro a haP haIso
      exact (Finset.disjoint_left.mp hdisjPI) (Finset.mem_inter.mp haP).2
        (Finset.mem_inter.mp haIso).2
    have hunion : G.neighborFinset h ∩ (P ∪ Iso) = G.neighborFinset h :=
      Finset.inter_eq_left.mpr hsubPI
    have hcard : (G.neighborFinset h ∩ P).card + (G.neighborFinset h ∩ Iso).card
        = G.degree h := by
      rw [← Finset.card_union_of_disjoint hdisj', ← Finset.inter_union_distrib_left, hunion,
        G.card_neighborFinset_eq_degree]
    omega
  by_contra hcon
  rw [not_or, not_le, not_le] at hcon
  obtain ⟨hlt1, hlt2⟩ := hcon
  have hp1 : 2 ≤ (G.neighborFinset h₁ ∩ P).card := by
    have := iso_count h₁ hh10 hh1d; omega
  have hp2 : 2 ≤ (G.neighborFinset h₂ ∩ P).card := by
    have := iso_count h₂ hh20 hh2d; omega
  have hbad1 := deg4_path_bad_of_two G L₁ c₁ c₂ L₂ h₁ hT hC4 hac1L1 hc12 hac2L2 hnc1L2 hnc2L1
    hL1nc2 hL2nc1 hL1d hc1d hc2d hL2d hh1d hp1
  have hbad2 := deg4_path_bad_of_two G L₁ c₁ c₂ L₂ h₂ hT hC4 hac1L1 hc12 hac2L2 hnc1L2 hnc2L1
    hL1nc2 hL2nc1 hL1d hc1d hc2d hL2d hh2d hp2
  obtain ⟨hh1L1, _, _, _⟩ := hbad1
  obtain ⟨hh2L1, _, _, _⟩ := hbad2
  obtain ⟨x, hxDc, hxh1, hxh2, hxL1⟩ := hL1other
  have hsub3 : ({h₁, h₂, x} : Finset (Fin 18)) ⊆ G.neighborFinset L₁ ∩ Dᶜ := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl
    · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset L₁ a).mpr hh1L1.symm, hh1Dc⟩
    · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset L₁ a).mpr hh2L1.symm, hh2Dc⟩
    · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset L₁ a).mpr hxL1.symm, hxDc⟩
  have hcard3 : ({h₁, h₂, x} : Finset (Fin 18)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hne12, Ne.symm hxh1]),
      Finset.card_insert_of_notMem (by simp [Ne.symm hxh2]), Finset.card_singleton]
  have := Finset.card_le_card hsub3
  rw [hcard3, hL1hub] at this
  omega

/-- **Node 3.**  The `Iso`-rich isolated degree-`4` hub `h₁` and its companion `h₂` package into a
`TwoHubConfig`.  Pick `a, b`: two `M`-isolated neighbours of `h₁` not adjacent to `h₂` (possible
since `h₁` has `≥ 3` such neighbours and shares `≤ 1` with `h₂`).  Pick `c, d`: two degree-`3`
neighbours of `h₂` not adjacent to `h₁` (possible since `h₁, h₂` share `≤ 1` `M`-isolated twin and
`≤ 1` cherry vertex, so `≤ 2` of `h₂`'s four neighbours meet `h₁`). -/
theorem two_isolated_hub_twohubconfig_d9_ff4 (G : SimpleGraph (Fin 18)) (D Iso : Finset (Fin 18))
    (L₁ c₁ c₂ L₂ h₁ h₂ : Fin 18)
    (hC4 : ¬∃ a b c d : Fin 18, ({a, b, c, d} : Finset (Fin 18)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (hmemD : ∀ v : Fin 18, v ∈ D ↔ G.degree v = 3) (hIsoD : Iso ⊆ D)
    (hclassP : ∀ x ∈ D, x = L₁ ∨ x = c₁ ∨ x = c₂ ∨ x = L₂ ∨ x ∈ Iso)
    (hIsoprop : ∀ v ∈ Iso, G.degree v = 3 ∧ (∀ w : Fin 18, G.Adj v w → G.degree w ≠ 3))
    (hac1L1 : G.Adj c₁ L₁) (hc12 : G.Adj c₁ c₂) (hac2L2 : G.Adj c₂ L₂)
    (hc1d : G.degree c₁ = 3) (hc2d : G.degree c₂ = 3)
    (hh1Dc : h₁ ∈ Dᶜ) (hh2Dc : h₂ ∈ Dᶜ) (hh1d : G.degree h₁ = 4) (hh2d : G.degree h₂ = 4)
    (hh10 : G.neighborFinset h₁ ∩ Dᶜ = ∅) (hh20 : G.neighborFinset h₂ ∩ Dᶜ = ∅)
    (hne12 : h₁ ≠ h₂) (hIso_rich : 3 ≤ (G.neighborFinset h₁ ∩ Iso).card) :
    TwoHubConfig G := by
  classical
  set P : Finset (Fin 18) := {L₁, c₁, c₂, L₂} with hPdef
  -- Path vertices are not `M`-isolated, so `P` and `Iso` are disjoint.
  have hPnotIso : ∀ x ∈ P, x ∉ Iso := by
    intro x hx hxIso
    simp only [hPdef, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact (hIsoprop x hxIso).2 c₁ hac1L1.symm hc1d
    · exact (hIsoprop x hxIso).2 c₂ hc12 hc2d
    · exact (hIsoprop x hxIso).2 c₁ hc12.symm hc1d
    · exact (hIsoprop x hxIso).2 c₂ hac2L2.symm hc2d
  have hdisjPI : Disjoint P Iso := by
    rw [Finset.disjoint_left]; intro x hxP hxIso; exact hPnotIso x hxP hxIso
  -- `N h₂ ⊆ D` (since `h₂` is isolated in `Dᶜ`).
  have hN2subD : G.neighborFinset h₂ ⊆ D := by
    intro x hx
    by_contra hxD
    have hmem : x ∈ G.neighborFinset h₂ ∩ Dᶜ :=
      Finset.mem_inter.mpr ⟨hx, Finset.mem_compl.mpr hxD⟩
    rw [hh20] at hmem; exact absurd hmem (Finset.notMem_empty x)
  -- `|N h₁ ∩ Iso| + |N h₁ ∩ P| = 4`, hence `h₁` has at most one cherry neighbour.
  have hp1le : (G.neighborFinset h₁ ∩ P).card ≤ 1 := by
    have hsubD : G.neighborFinset h₁ ⊆ D := by
      intro x hx
      by_contra hxD
      have hmem : x ∈ G.neighborFinset h₁ ∩ Dᶜ :=
        Finset.mem_inter.mpr ⟨hx, Finset.mem_compl.mpr hxD⟩
      rw [hh10] at hmem; exact absurd hmem (Finset.notMem_empty x)
    have hsubPI : G.neighborFinset h₁ ⊆ P ∪ Iso := by
      intro x hx
      rcases hclassP x (hsubD hx) with h' | h' | h' | h' | h'
      · exact Finset.mem_union_left _ (by simp [hPdef, h'])
      · exact Finset.mem_union_left _ (by simp [hPdef, h'])
      · exact Finset.mem_union_left _ (by simp [hPdef, h'])
      · exact Finset.mem_union_left _ (by simp [hPdef, h'])
      · exact Finset.mem_union_right _ h'
    have hdisj' : Disjoint (G.neighborFinset h₁ ∩ P) (G.neighborFinset h₁ ∩ Iso) := by
      apply Finset.disjoint_left.mpr
      intro a haP haIso
      exact (Finset.disjoint_left.mp hdisjPI) (Finset.mem_inter.mp haP).2
        (Finset.mem_inter.mp haIso).2
    have hunion : G.neighborFinset h₁ ∩ (P ∪ Iso) = G.neighborFinset h₁ :=
      Finset.inter_eq_left.mpr hsubPI
    have hcard : (G.neighborFinset h₁ ∩ P).card + (G.neighborFinset h₁ ∩ Iso).card
        = G.degree h₁ := by
      rw [← Finset.card_union_of_disjoint hdisj', ← Finset.inter_union_distrib_left, hunion,
        G.card_neighborFinset_eq_degree]
    omega
  -- `¬ G.Adj h₁ h₂`.
  have hnadj12 : ¬G.Adj h₁ h₂ := by
    intro hadj
    have hmem : h₂ ∈ G.neighborFinset h₁ ∩ Dᶜ :=
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset h₁ h₂).mpr hadj, hh2Dc⟩
    rw [hh10] at hmem; exact absurd hmem (Finset.notMem_empty h₂)
  -- The shared `M`-isolated twins are `≤ 1`.
  have hshare := nonadj_deg4_hubs_share_le_one_iso_pointwise G D Iso hC4 hIsoD hIsoprop h₁ h₂
    hh1Dc hh2Dc hh1d hh2d hne12 hnadj12
  -- Selection of `a, b` (in `(N h₁ ∩ Iso) \ N h₂`).
  have heq4 : (G.neighborFinset h₁ ∩ Iso) ∩ G.neighborFinset h₂
      = (G.neighborFinset h₁ ∩ G.neighborFinset h₂) ∩ Iso := by
    ext z; simp only [Finset.mem_inter]; tauto
  have hab_card : 2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card := by
    have hsplit := Finset.card_sdiff_add_card_inter (G.neighborFinset h₁ ∩ Iso)
      (G.neighborFinset h₂)
    rw [heq4] at hsplit
    omega
  obtain ⟨a, hamem, b, hbmem, hab⟩ := Finset.one_lt_card.mp
    (by omega : 1 < ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card)
  -- Selection of `c, d` (in `N h₂ \ N h₁`).
  have heq5 : (G.neighborFinset h₂ ∩ G.neighborFinset h₁) ∩ Iso
      = (G.neighborFinset h₁ ∩ G.neighborFinset h₂) ∩ Iso := by
    ext z; simp only [Finset.mem_inter]; tauto
  have hcommon_le : (G.neighborFinset h₂ ∩ G.neighborFinset h₁).card ≤ 2 := by
    have hsubPI : G.neighborFinset h₂ ∩ G.neighborFinset h₁ ⊆ P ∪ Iso := by
      intro x hx
      rcases hclassP x (hN2subD (Finset.mem_inter.mp hx).1) with h' | h' | h' | h' | h'
      · exact Finset.mem_union_left _ (by simp [hPdef, h'])
      · exact Finset.mem_union_left _ (by simp [hPdef, h'])
      · exact Finset.mem_union_left _ (by simp [hPdef, h'])
      · exact Finset.mem_union_left _ (by simp [hPdef, h'])
      · exact Finset.mem_union_right _ h'
    have hdisj' : Disjoint ((G.neighborFinset h₂ ∩ G.neighborFinset h₁) ∩ P)
        ((G.neighborFinset h₂ ∩ G.neighborFinset h₁) ∩ Iso) := by
      apply Finset.disjoint_left.mpr
      intro a haP haIso
      exact (Finset.disjoint_left.mp hdisjPI) (Finset.mem_inter.mp haP).2
        (Finset.mem_inter.mp haIso).2
    have hunion : (G.neighborFinset h₂ ∩ G.neighborFinset h₁) ∩ (P ∪ Iso)
        = G.neighborFinset h₂ ∩ G.neighborFinset h₁ := Finset.inter_eq_left.mpr hsubPI
    have hcard : ((G.neighborFinset h₂ ∩ G.neighborFinset h₁) ∩ P).card
        + ((G.neighborFinset h₂ ∩ G.neighborFinset h₁) ∩ Iso).card
        = (G.neighborFinset h₂ ∩ G.neighborFinset h₁).card := by
      rw [← Finset.card_union_of_disjoint hdisj', ← Finset.inter_union_distrib_left, hunion]
    have hPpart : ((G.neighborFinset h₂ ∩ G.neighborFinset h₁) ∩ P).card
        ≤ (G.neighborFinset h₁ ∩ P).card := by
      apply Finset.card_le_card
      intro x hx
      rw [Finset.mem_inter] at hx ⊢
      exact ⟨(Finset.mem_inter.mp hx.1).2, hx.2⟩
    have hIsopart : ((G.neighborFinset h₂ ∩ G.neighborFinset h₁) ∩ Iso).card ≤ 1 := by
      rw [heq5]; exact hshare
    omega
  have hcd_card : 2 ≤ (G.neighborFinset h₂ \ G.neighborFinset h₁).card := by
    have hsplit := Finset.card_sdiff_add_card_inter (G.neighborFinset h₂) (G.neighborFinset h₁)
    rw [G.card_neighborFinset_eq_degree, hh2d] at hsplit
    omega
  obtain ⟨c, hcmem, d, hdmem, hcd⟩ := Finset.one_lt_card.mp
    (by omega : 1 < (G.neighborFinset h₂ \ G.neighborFinset h₁).card)
  -- Unpack the four chosen vertices.
  obtain ⟨haNI, haN2⟩ := Finset.mem_sdiff.mp hamem
  obtain ⟨hbNI, hbN2⟩ := Finset.mem_sdiff.mp hbmem
  obtain ⟨haN1, haIso⟩ := Finset.mem_inter.mp haNI
  obtain ⟨hbN1, hbIso⟩ := Finset.mem_inter.mp hbNI
  obtain ⟨hcN2, hcN1⟩ := Finset.mem_sdiff.mp hcmem
  obtain ⟨hdN2, hdN1⟩ := Finset.mem_sdiff.mp hdmem
  have hah1 : G.Adj a h₁ := ((G.mem_neighborFinset h₁ a).mp haN1).symm
  have hbh1 : G.Adj b h₁ := ((G.mem_neighborFinset h₁ b).mp hbN1).symm
  have hch2 : G.Adj c h₂ := ((G.mem_neighborFinset h₂ c).mp hcN2).symm
  have hdh2 : G.Adj d h₂ := ((G.mem_neighborFinset h₂ d).mp hdN2).symm
  have hn_ah2 : ¬G.Adj a h₂ := fun hadj => haN2 ((G.mem_neighborFinset h₂ a).mpr hadj.symm)
  have hn_bh2 : ¬G.Adj b h₂ := fun hadj => hbN2 ((G.mem_neighborFinset h₂ b).mpr hadj.symm)
  have hn_h1c : ¬G.Adj h₁ c := fun hadj => hcN1 ((G.mem_neighborFinset h₁ c).mpr hadj)
  have hn_h1d : ¬G.Adj h₁ d := fun hadj => hdN1 ((G.mem_neighborFinset h₁ d).mpr hadj)
  have hdega : G.degree a = 3 := (hIsoprop a haIso).1
  have hdegb : G.degree b = 3 := (hIsoprop b hbIso).1
  have hdegc : G.degree c = 3 := (hmemD c).mp (hN2subD hcN2)
  have hdegd : G.degree d = 3 := (hmemD d).mp (hN2subD hdN2)
  exact dense_two_hub_assemble G h₁ h₂ a b c d hh1d hh2d hdega hdegb hdegc hdegd
    hah1 hbh1 hch2 hdh2 hnadj12 hn_h1c hn_h1d hn_ah2 hn_bh2
    (hIsoprop a haIso).2 (hIsoprop b hbIso).2 hab hcd

end N18

end ACMax
