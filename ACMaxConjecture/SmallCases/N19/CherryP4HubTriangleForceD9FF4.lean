import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N19.Core
import ACMaxConjecture.SmallCases.StarCertificates
import ACMaxConjecture.SmallCases.N19.Core
import ACMaxConjecture.SmallCases.N19.Align8Helpers
import ACMaxConjecture.SmallCases.N19.CherryP4HubTriangleShare

/-!
# The `n = 19`, `P₄`-cherry, `|D| = 9`, `|FF| = 4` hub-triangle escape corner

This file closes the lone documented `sorry` of `iso_rich_force_p4_nineteen` (the `|D| = 9`,
`|FF| = 4` branch).  At that point there are `9` hubs of degree `∈ {4, 5}` with `∑ deg = 37`
(exactly one degree-`5` hub) and total internal incidence `16`.  The avoider analysis forces:

* **`two_isolated_hub_twohubconfig_d9_ff4`** — the `Iso`-rich isolated hub and its companion
  package into a `TwoHubConfig`, contradicting `hth`.
-/

namespace ACMax

open scoped Classical

namespace N19

/-- **Single-hub path dichotomy.**  A degree-`4` hub `h` adjacent to at least two cherry-path
vertices (`{L₁, c₁, c₂, L₂}`) must in fact be adjacent to exactly the two leaves `L₁, L₂` (and to
neither `c₁` nor `c₂`): any other pair of path-neighbours produces either a good triangle (cherry
edge plus `h`, degree sum `4 + 3 + 3 = 10 ≤ 10`) or a good `C₄` (degree sum `4 + 3 + 3 + 3 = 13 ≤
14`), excluded by `hT`/`hC4`. -/
theorem deg4_path_bad_of_two (G : SimpleGraph (Fin 19)) (L₁ c₁ c₂ L₂ h : Fin 19)
    (hT : ¬∃ x y z : Fin 19, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    (hC4 : ¬∃ a b c d : Fin 19, ({a, b, c, d} : Finset (Fin 19)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (hac1L1 : G.Adj c₁ L₁) (hc12 : G.Adj c₁ c₂) (hac2L2 : G.Adj c₂ L₂)
    (hnc1L2 : ¬G.Adj c₁ L₂) (hnc2L1 : ¬G.Adj c₂ L₁)
    (hL1nc2 : L₁ ≠ c₂) (hL2nc1 : L₂ ≠ c₁)
    (hL1d : G.degree L₁ = 3) (hc1d : G.degree c₁ = 3)
    (hc2d : G.degree c₂ = 3) (hL2d : G.degree L₂ = 3) (hhd : G.degree h = 4)
    (hp2 : 2 ≤ (G.neighborFinset h ∩ ({L₁, c₁, c₂, L₂} : Finset (Fin 19))).card) :
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
  have pair_mem : ∀ (S : Finset (Fin 19)) (a b : Fin 19), a ≠ b → S ⊆ {a, b} → 2 ≤ S.card →
      a ∈ S ∧ b ∈ S := by
    intro S a b hab hsub hcard
    have hcab : ({a, b} : Finset (Fin 19)).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simp [hab]), Finset.card_singleton]
    have heq : S = {a, b} := Finset.eq_of_subset_of_card_le hsub (by omega)
    rw [heq]; exact ⟨by simp, by simp⟩
  -- Card-`4` of the path set (for the `C₄` witnesses).
  have hP4 : ({h, c₁, c₂, L₂} : Finset (Fin 19)).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [hne_hc1, hne_hc2, hne_hL2]),
      Finset.card_insert_of_notMem (by simp [hc1c2, hc1L2]),
      Finset.card_insert_of_notMem (by simp [hc2L2]), Finset.card_singleton]
  have hP4' : ({h, c₂, c₁, L₁} : Finset (Fin 19)).card = 4 := by
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
      · have hsub : G.neighborFinset h ∩ ({L₁, c₁, c₂, L₂} : Finset (Fin 19)) ⊆ {c₁, L₂} := by
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
      have hsub : G.neighborFinset h ∩ ({L₁, c₁, c₂, L₂} : Finset (Fin 19)) ⊆ {c₂, L₁} := by
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
  have hsub : G.neighborFinset h ∩ ({L₁, c₁, c₂, L₂} : Finset (Fin 19)) ⊆ {L₁, L₂} := by
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

/-- **Node 2′ (`n = 19` pair version, no `hL1other`).**  Of *two* isolated degree-`4` hubs
`h₁ ≠ h₂` at least one is `Iso`-rich (`≥ 3` `M`-isolated neighbours).  If *both* failed, each would
carry `≥ 2` cherry-path neighbours, so the single-hub dichotomy `deg4_path_bad_of_two` forces *both*
adjacent to *both* leaves `L₁, L₂`.  Then `h₁-L₁-h₂-L₂` is an induced 4-cycle (`¬G.Adj h₁ h₂` since
`h₁` is `Dᶜ`-isolated, `¬G.Adj L₁ L₂` by hypothesis) of degree sum `4+3+4+3 = 14 ≤ 14`, a good `C₄`
excluded by `hC4`.  This avoids the `|N L₁ ∩ Dᶜ| = 2` third-neighbour argument of the n=18 route, so
it is robust to the excess-11 dilution. -/
theorem isolated_pair_iso_rich_nineteen (G : SimpleGraph (Fin 19)) (D Iso : Finset (Fin 19))
    (L₁ c₁ c₂ L₂ h₁ h₂ : Fin 19)
    (hT : ¬∃ x y z : Fin 19, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    (hC4 : ¬∃ a b c d : Fin 19, ({a, b, c, d} : Finset (Fin 19)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (hclassP : ∀ x ∈ D, x = L₁ ∨ x = c₁ ∨ x = c₂ ∨ x = L₂ ∨ x ∈ Iso)
    (hIsoprop : ∀ v ∈ Iso, G.degree v = 3 ∧ (∀ w : Fin 19, G.Adj v w → G.degree w ≠ 3))
    (hac1L1 : G.Adj c₁ L₁) (hc12 : G.Adj c₁ c₂) (hac2L2 : G.Adj c₂ L₂)
    (hnc1L2 : ¬G.Adj c₁ L₂) (hnc2L1 : ¬G.Adj c₂ L₁)
    (hL1nc2 : L₁ ≠ c₂) (hL2nc1 : L₂ ≠ c₁)
    (hL1d : G.degree L₁ = 3) (hc1d : G.degree c₁ = 3)
    (hc2d : G.degree c₂ = 3) (hL2d : G.degree L₂ = 3)
    (hh2Dc : h₂ ∈ Dᶜ) (hh1d : G.degree h₁ = 4) (hh2d : G.degree h₂ = 4)
    (hh10 : G.neighborFinset h₁ ∩ Dᶜ = ∅) (hh20 : G.neighborFinset h₂ ∩ Dᶜ = ∅)
    (hne12 : h₁ ≠ h₂) (hnL1L2 : ¬G.Adj L₁ L₂) :
    3 ≤ (G.neighborFinset h₁ ∩ Iso).card ∨ 3 ≤ (G.neighborFinset h₂ ∩ Iso).card := by
  classical
  set P : Finset (Fin 19) := {L₁, c₁, c₂, L₂} with hPdef
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
  have iso_count : ∀ h : Fin 19, G.neighborFinset h ∩ Dᶜ = ∅ → G.degree h = 4 →
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
  obtain ⟨hh1L1, hh1L2, _, _⟩ := hbad1
  obtain ⟨hh2L1, hh2L2, _, _⟩ := hbad2
  -- `¬ G.Adj h₁ h₂` from `h₁`'s `Dᶜ`-isolation.
  have hnadj12 : ¬G.Adj h₁ h₂ := by
    intro hadj
    have hmem : h₂ ∈ G.neighborFinset h₁ ∩ Dᶜ :=
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset h₁ h₂).mpr hadj, hh2Dc⟩
    rw [hh10] at hmem; exact absurd hmem (Finset.notMem_empty h₂)
  -- Distinctness for the `C₄` witness `{h₁, L₁, h₂, L₂}`.
  have hne_h1L1 : h₁ ≠ L₁ := by intro he; rw [he] at hh1d; omega
  have hne_h1L2 : h₁ ≠ L₂ := by intro he; rw [he] at hh1d; omega
  have hne_h2L1 : h₂ ≠ L₁ := by intro he; rw [he] at hh2d; omega
  have hne_h2L2 : h₂ ≠ L₂ := by intro he; rw [he] at hh2d; omega
  have hL1L2 : L₁ ≠ L₂ := by intro he; apply hnc1L2; rw [← he]; exact hac1L1
  have hcard4 : ({h₁, L₁, h₂, L₂} : Finset (Fin 19)).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [hne_h1L1, hne12, hne_h1L2]),
      Finset.card_insert_of_notMem (by simp [Ne.symm hne_h2L1, hL1L2]),
      Finset.card_insert_of_notMem (by simp [hne_h2L2]), Finset.card_singleton]
  exact hC4 ⟨h₁, L₁, h₂, L₂, hcard4, hh1L1, hh2L1.symm, hh2L2, hh1L2.symm,
    hnadj12, hnL1L2, by omega⟩

/-- **Node 3.**  The `Iso`-rich isolated degree-`4` hub `h₁` and its companion `h₂` package into a
`TwoHubConfig`.  Pick `a, b`: two `M`-isolated neighbours of `h₁` not adjacent to `h₂` (possible
since `h₁` has `≥ 3` such neighbours and shares `≤ 1` with `h₂`).  Pick `c, d`: two degree-`3`
neighbours of `h₂` not adjacent to `h₁` (possible since `h₁, h₂` share `≤ 1` `M`-isolated twin and
`≤ 1` cherry vertex, so `≤ 2` of `h₂`'s four neighbours meet `h₁`). -/
theorem two_isolated_hub_twohubconfig_d9_ff4 (G : SimpleGraph (Fin 19)) (D Iso : Finset (Fin 19))
    (L₁ c₁ c₂ L₂ h₁ h₂ : Fin 19)
    (hC4 : ¬∃ a b c d : Fin 19, ({a, b, c, d} : Finset (Fin 19)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (hmemD : ∀ v : Fin 19, v ∈ D ↔ G.degree v = 3) (hIsoD : Iso ⊆ D)
    (hclassP : ∀ x ∈ D, x = L₁ ∨ x = c₁ ∨ x = c₂ ∨ x = L₂ ∨ x ∈ Iso)
    (hIsoprop : ∀ v ∈ Iso, G.degree v = 3 ∧ (∀ w : Fin 19, G.Adj v w → G.degree w ≠ 3))
    (hac1L1 : G.Adj c₁ L₁) (hc12 : G.Adj c₁ c₂) (hac2L2 : G.Adj c₂ L₂)
    (hc1d : G.degree c₁ = 3) (hc2d : G.degree c₂ = 3)
    (hh1Dc : h₁ ∈ Dᶜ) (hh2Dc : h₂ ∈ Dᶜ) (hh1d : G.degree h₁ = 4) (hh2d : G.degree h₂ = 4)
    (hh10 : G.neighborFinset h₁ ∩ Dᶜ = ∅) (hh20 : G.neighborFinset h₂ ∩ Dᶜ = ∅)
    (hne12 : h₁ ≠ h₂) (hIso_rich : 3 ≤ (G.neighborFinset h₁ ∩ Iso).card) :
    TwoHubConfig G := by
  classical
  set P : Finset (Fin 19) := {L₁, c₁, c₂, L₂} with hPdef
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

end N19

end ACMax
