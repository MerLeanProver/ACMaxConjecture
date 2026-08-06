import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N15.Core
import ACMaxConjecture.SmallCases.Certificates
import ACMaxConjecture.SmallCases.N15.HubTriangleStruct
import ACMaxConjecture.SmallCases.N15.HubTriangleFF

/-!
# Triangle forcing for the `n = 15`, `e(M) = 3`, `|D| = 8` hub-triangle corner

This file closes the single hard combinatorial core of `exists_hub_triangle_config_residual`.
Under the residual hypotheses, no avoider triangle for cherry `{c₁, c₂, L₂}` (`htri2`) is
contradictory, because the seven-hub incidence structure forces such a triangle.

The argument is a case split on the number of *fully-free* hubs (degree-`4` hubs avoiding all four
path vertices `L₁, c₁, c₂, L₂`):

* there are between `1` and `2` of them (`fully_free_exists`, `fully_free_le_two`);
* with exactly **one** fully-free hub `f`, the cherry-`{c₁,c₂,L₂}` avoiders (`≥ 3`, internal
  degree `≥ 2`) and the cherry-`{L₁,c₁,c₂}` avoiders (`≥ 3`, internal degree `≥ 2`) overlap only in
  `f`, so they span `≥ 5` distinct hubs of total hub-internal degree `≥ 3 + 2·4 = 11 > 10`,
  contradicting `∑ internal = 10`;
* with exactly **two** fully-free hubs `f₁, f₂`, an edge-count forces `f₁ ∼ f₂` and `f₁, f₂` to
  carry every hub-edge, so any cherry-`{c₁,c₂,L₂}` avoider outside `{f₁, f₂}` (one exists, since
  there are `≥ 3` such avoiders) is adjacent to both — a triangle.
-/

namespace ACMax

open scoped Classical

namespace N15

/-- **Forced avoider triangle (the two-hub core).**  Under the residual hypotheses, the assumption
`htri2` that cherry `{c₁,c₂,L₂}` has no triangle of pairwise-adjacent avoiding hubs is
contradictory. -/
theorem hub_triangle_from_structure (G : SimpleGraph (Fin 15))
    (D Iso : Finset (Fin 15)) (L₁ c₁ c₂ L₂ : Fin 15)
    (hIsodef : Iso = D.filter (fun v => (G.neighborFinset v ∩ D).card = 0))
    (_hIsoprop : ∀ v ∈ Iso, G.degree v = 3 ∧ (∀ w : Fin 15, G.Adj v w → G.degree w ≠ 3))
    (hisochar : ∀ w : Fin 15, w ∈ D → w ≠ L₁ → w ≠ c₁ → w ≠ c₂ → w ≠ L₂ → w ∈ Iso)
    (hL1D : L₁ ∈ D) (hc1D : c₁ ∈ D) (hc2D : c₂ ∈ D) (hL2D : L₂ ∈ D)
    (hac1L1 : G.Adj c₁ L₁) (hc12 : G.Adj c₁ c₂) (hac2L2 : G.Adj c₂ L₂)
    (hnc1L2 : ¬G.Adj c₁ L₂)
    (hdeg4 : ∀ w : Fin 15, w ∈ Dᶜ → G.degree w = 4)
    (hDc7 : Dᶜ.card = 7) (_hIso4 : Iso.card = 4)
    (hcard_c1 : (G.neighborFinset c₁ ∩ Dᶜ).card = 1)
    (hcard_c2 : (G.neighborFinset c₂ ∩ Dᶜ).card = 1)
    (hcard_L1 : (G.neighborFinset L₁ ∩ Dᶜ).card = 2)
    (hcard_L2 : (G.neighborFinset L₂ ∩ Dᶜ).card = 2)
    (hSum10 : ∑ w ∈ Dᶜ, (G.neighborFinset w ∩ Dᶜ).card = 10)
    (hL1nc2 : L₁ ≠ c₂) (hL2nc1 : L₂ ≠ c₁)
    (hW : ∀ g : Fin 15, g ∈ Dᶜ →
      ((¬G.Adj g L₁ ∧ ¬G.Adj g c₁ ∧ ¬G.Adj g c₂) ∨
        (¬G.Adj g c₁ ∧ ¬G.Adj g c₂ ∧ ¬G.Adj g L₂)) →
      (G.neighborFinset g ∩ Iso).card ≤ 1)
    (htri2 : ¬∃ a b c : Fin 15, a ∈ Dᶜ ∧ b ∈ Dᶜ ∧ c ∈ Dᶜ ∧
      G.Adj a b ∧ G.Adj a c ∧ G.Adj b c ∧
      (¬G.Adj a c₁ ∧ ¬G.Adj a c₂ ∧ ¬G.Adj a L₂) ∧
      (¬G.Adj b c₁ ∧ ¬G.Adj b c₂ ∧ ¬G.Adj b L₂) ∧
      (¬G.Adj c c₁ ∧ ¬G.Adj c c₂ ∧ ¬G.Adj c L₂)) :
    False := by
  classical
  -- distinctness among the four path vertices
  have hL1c1 : L₁ ≠ c₁ := (G.ne_of_adj hac1L1).symm
  have hc1c2 : c₁ ≠ c₂ := G.ne_of_adj hc12
  have hc2L2 : c₂ ≠ L₂ := G.ne_of_adj hac2L2
  have hc1L2 : c₁ ≠ L₂ := hL2nc1.symm
  have hL1L2 : L₁ ≠ L₂ := by rintro rfl; exact hnc1L2 hac1L1
  -- the path / iso partition of `D`
  obtain ⟨hDeq, _hdisj⟩ :=
    path_iso_partition G D Iso L₁ c₁ c₂ L₂ hIsodef hisochar hL1D hc1D hc2D hL2D hac1L1 hc12 hac2L2
  have hclassP : ∀ x : Fin 15, x ∈ D → x = L₁ ∨ x = c₁ ∨ x = c₂ ∨ x = L₂ ∨ x ∈ Iso := by
    intro x hx
    rw [← hDeq] at hx
    rcases Finset.mem_union.mp hx with h | h
    · simp only [Finset.mem_insert, Finset.mem_singleton] at h; tauto
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
  -- the three avoider sets
  set A1 : Finset (Fin 15) :=
    Dᶜ.filter (fun g => ¬G.Adj g L₁ ∧ ¬G.Adj g c₁ ∧ ¬G.Adj g c₂) with hA1def
  set A2 : Finset (Fin 15) :=
    Dᶜ.filter (fun g => ¬G.Adj g c₁ ∧ ¬G.Adj g c₂ ∧ ¬G.Adj g L₂) with hA2def
  set FF : Finset (Fin 15) :=
    Dᶜ.filter (fun g => ¬G.Adj g L₁ ∧ ¬G.Adj g c₁ ∧ ¬G.Adj g c₂ ∧ ¬G.Adj g L₂) with hFFdef
  -- internal-degree lower bounds
  have hA2int : ∀ g : Fin 15, g ∈ A2 → 2 ≤ (G.neighborFinset g ∩ Dᶜ).card := by
    intro g hg
    rw [hA2def, Finset.mem_filter] at hg
    obtain ⟨hgDc, hgc1, hgc2, hgL2⟩ := hg
    refine avoider_internal_ge_two G D Iso g L₁ (hdeg4 g hgDc)
      (hW g hgDc (Or.inr ⟨hgc1, hgc2, hgL2⟩)) ?_
    intro x hadj hxD
    rcases hclassP x hxD with h | h | h | h | h
    · exact Or.inl h
    · exact absurd (h ▸ hadj) hgc1
    · exact absurd (h ▸ hadj) hgc2
    · exact absurd (h ▸ hadj) hgL2
    · exact Or.inr h
  have hA1int : ∀ g : Fin 15, g ∈ A1 → 2 ≤ (G.neighborFinset g ∩ Dᶜ).card := by
    intro g hg
    rw [hA1def, Finset.mem_filter] at hg
    obtain ⟨hgDc, hgL1, hgc1, hgc2⟩ := hg
    refine avoider_internal_ge_two G D Iso g L₂ (hdeg4 g hgDc)
      (hW g hgDc (Or.inl ⟨hgL1, hgc1, hgc2⟩)) ?_
    intro x hadj hxD
    rcases hclassP x hxD with h | h | h | h | h
    · exact absurd (h ▸ hadj) hgL1
    · exact absurd (h ▸ hadj) hgc1
    · exact absurd (h ▸ hadj) hgc2
    · exact Or.inl h
    · exact Or.inr h
  have hFFint : ∀ g : Fin 15, g ∈ FF → 3 ≤ (G.neighborFinset g ∩ Dᶜ).card := by
    intro g hg
    rw [hFFdef, Finset.mem_filter] at hg
    obtain ⟨hgDc, hgL1, hgc1, hgc2, hgL2⟩ := hg
    refine fully_free_internal_ge_three G D Iso g (hdeg4 g hgDc)
      (hW g hgDc (Or.inl ⟨hgL1, hgc1, hgc2⟩)) ?_
    intro x hadj hxD
    rcases hclassP x hxD with h | h | h | h | h
    · exact absurd (h ▸ hadj) hgL1
    · exact absurd (h ▸ hadj) hgc1
    · exact absurd (h ▸ hadj) hgc2
    · exact absurd (h ▸ hadj) hgL2
    · exact h
  -- subset facts
  have hA1sub : A1 ⊆ Dᶜ := by rw [hA1def]; exact Finset.filter_subset _ _
  have hA2sub : A2 ⊆ Dᶜ := by rw [hA2def]; exact Finset.filter_subset _ _
  have hFFsub : FF ⊆ Dᶜ := by rw [hFFdef]; exact Finset.filter_subset _ _
  -- cherry avoider lower bounds and fully-free counts
  obtain ⟨hA1card, hA2card⟩ :=
    cherry_avoiders_ge_three G D L₁ c₁ c₂ L₂ hDc7 hcard_c1 hcard_c2 hcard_L1 hcard_L2
  rw [← hA1def] at hA1card
  rw [← hA2def] at hA2card
  have hFFle2 : FF.card ≤ 2 := fully_free_le_two G D FF hFFsub hFFint hSum10
  obtain ⟨f₀, hf₀Dc, hf₀L1, hf₀c1, hf₀c2, hf₀L2⟩ :=
    fully_free_exists G D L₁ c₁ c₂ L₂ hDc7 hcard_c1 hcard_c2 hcard_L1 hcard_L2
      hL1c1 hL1nc2 hL1L2 hc1c2 hc1L2 hc2L2
  have hf₀FF : f₀ ∈ FF := by
    rw [hFFdef, Finset.mem_filter]; exact ⟨hf₀Dc, hf₀L1, hf₀c1, hf₀c2, hf₀L2⟩
  -- case split on a second fully-free hub
  by_cases hsecond : ∃ f' : Fin 15, f' ∈ FF ∧ f' ≠ f₀
  · -- |FF| = 2 case: `f₀ ∼ f₁` carry every hub-edge, so an avoider triangle exists.
    obtain ⟨f₁, hf₁FF, hf₁ne⟩ := hsecond
    obtain ⟨hf₁Dc, hf₁L1, hf₁c1, hf₁c2, hf₁L2⟩ := by
      have h := hf₁FF; rw [hFFdef, Finset.mem_filter] at h; exact h
    have hf₀1 : f₀ ≠ f₁ := fun e => hf₁ne e.symm
    have hcf0 : 3 ≤ (G.neighborFinset f₀ ∩ Dᶜ).card := hFFint f₀ hf₀FF
    have hcf1 : 3 ≤ (G.neighborFinset f₁ ∩ Dᶜ).card := hFFint f₁ hf₁FF
    set pair : Finset (Fin 15) := {f₀, f₁} with hpairdef
    have hpairsub : pair ⊆ Dᶜ := by
      rw [hpairdef]; intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hf₀Dc
      · exact hf₁Dc
    have hpairsum : ∀ φ : Fin 15 → ℕ, ∑ w ∈ pair, φ w = φ f₀ + φ f₁ := by
      intro φ; rw [hpairdef, Finset.sum_insert (by simp [hf₀1]), Finset.sum_singleton]
    have hsplit : ∀ w : Fin 15, (G.neighborFinset w ∩ Dᶜ).card
        = (G.neighborFinset w ∩ pair).card + (G.neighborFinset w ∩ (Dᶜ \ pair)).card := by
      intro w
      rw [← Finset.card_union_of_disjoint, ← Finset.inter_union_distrib_left,
        Finset.union_sdiff_of_subset hpairsub]
      apply Finset.disjoint_left.mpr
      intro a ha ha'
      rw [Finset.mem_inter] at ha ha'
      exact (Finset.mem_sdiff.mp ha'.2).2 ha.2
    have hcc : ∑ w ∈ Dᶜ, (G.neighborFinset w ∩ pair).card
        = (G.neighborFinset f₀ ∩ Dᶜ).card + (G.neighborFinset f₁ ∩ Dᶜ).card := by
      rw [cross_count G Dᶜ pair, hpairsum]
    have hSumsplit : (∑ w ∈ Dᶜ, (G.neighborFinset w ∩ pair).card)
        + ∑ w ∈ Dᶜ, (G.neighborFinset w ∩ (Dᶜ \ pair)).card = 10 := by
      rw [← Finset.sum_add_distrib, ← hSum10]
      exact Finset.sum_congr rfl (fun w _ => (hsplit w).symm)
    have hRsum : ∑ w ∈ Dᶜ, (G.neighborFinset w ∩ (Dᶜ \ pair)).card
        = (∑ w ∈ Dᶜ \ pair, (G.neighborFinset w ∩ (Dᶜ \ pair)).card)
          + ((G.neighborFinset f₀ ∩ (Dᶜ \ pair)).card
            + (G.neighborFinset f₁ ∩ (Dᶜ \ pair)).card) := by
      rw [← Finset.sum_sdiff hpairsub, hpairsum]
    by_cases hadj : G.Adj f₀ f₁
    · -- adjacent: every hub-edge meets `{f₀, f₁}`, giving a common avoider neighbour.
      have hp0 : (G.neighborFinset f₀ ∩ pair).card = 1 := by
        have he : G.neighborFinset f₀ ∩ pair = {f₁} := by
          rw [hpairdef]
          apply Finset.eq_singleton_iff_unique_mem.mpr
          refine ⟨by rw [Finset.mem_inter, G.mem_neighborFinset]; exact ⟨hadj, by simp⟩, ?_⟩
          intro a ha
          rw [Finset.mem_inter, G.mem_neighborFinset] at ha
          simp only [Finset.mem_insert, Finset.mem_singleton] at ha
          rcases ha.2 with rfl | rfl
          · exact (G.irrefl ha.1).elim
          · rfl
        rw [he, Finset.card_singleton]
      have hp1 : (G.neighborFinset f₁ ∩ pair).card = 1 := by
        have he : G.neighborFinset f₁ ∩ pair = {f₀} := by
          rw [hpairdef]
          apply Finset.eq_singleton_iff_unique_mem.mpr
          refine ⟨by rw [Finset.mem_inter, G.mem_neighborFinset]; exact ⟨hadj.symm, by simp⟩, ?_⟩
          intro a ha
          rw [Finset.mem_inter, G.mem_neighborFinset] at ha
          simp only [Finset.mem_insert, Finset.mem_singleton] at ha
          rcases ha.2 with rfl | rfl
          · rfl
          · exact (G.irrefl ha.1).elim
        rw [he, Finset.card_singleton]
      have e0 := hsplit f₀
      have e1 := hsplit f₁
      -- the residual hubs carry no edge: their internal-to-residual degree sums to 0
      have hzero : ∑ w ∈ Dᶜ \ pair, (G.neighborFinset w ∩ (Dᶜ \ pair)).card = 0 := by
        rw [hcc] at hSumsplit
        rw [hRsum] at hSumsplit
        omega
      have hzeroeach : ∀ w ∈ Dᶜ \ pair, (G.neighborFinset w ∩ (Dᶜ \ pair)).card = 0 :=
        (Finset.sum_eq_zero_iff).mp hzero
      -- find an avoider outside `{f₀, f₁}`
      have hpairA2 : pair ⊆ A2 := by
        rw [hpairdef]; intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · rw [hA2def, Finset.mem_filter]; exact ⟨hf₀Dc, hf₀c1, hf₀c2, hf₀L2⟩
        · rw [hA2def, Finset.mem_filter]; exact ⟨hf₁Dc, hf₁c1, hf₁c2, hf₁L2⟩
      have hpaircard : pair.card = 2 := by
        rw [hpairdef, Finset.card_insert_of_notMem (by simp [hf₀1]), Finset.card_singleton]
      have hex : ∃ w : Fin 15, w ∈ A2 ∧ w ∉ pair := by
        by_contra hcon
        push Not at hcon
        have : A2 ⊆ pair := fun w hw => hcon w hw
        have := Finset.card_le_card this
        omega
      obtain ⟨w, hwA2, hwpair⟩ := hex
      have hwDc : w ∈ Dᶜ := hA2sub hwA2
      have hwR : w ∈ Dᶜ \ pair := Finset.mem_sdiff.mpr ⟨hwDc, hwpair⟩
      have hwc : (G.neighborFinset w ∩ Dᶜ).card = (G.neighborFinset w ∩ pair).card := by
        have := hsplit w; rw [hzeroeach w hwR] at this; omega
      have hw2 : 2 ≤ (G.neighborFinset w ∩ pair).card := by
        have := hA2int w hwA2; omega
      have hweq : G.neighborFinset w ∩ pair = pair :=
        Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by rw [hpaircard]; exact hw2)
      have hwf0 : G.Adj w f₀ := by
        have : f₀ ∈ G.neighborFinset w ∩ pair := by rw [hweq, hpairdef]; simp
        rw [Finset.mem_inter, G.mem_neighborFinset] at this; exact this.1
      have hwf1 : G.Adj w f₁ := by
        have : f₁ ∈ G.neighborFinset w ∩ pair := by rw [hweq, hpairdef]; simp
        rw [Finset.mem_inter, G.mem_neighborFinset] at this; exact this.1
      obtain ⟨_, hwc1, hwc2, hwL2⟩ := by
        have h := hwA2; rw [hA2def, Finset.mem_filter] at h; exact h
      exact htri2 ⟨f₀, f₁, w, hf₀Dc, hf₁Dc, hwDc, hadj, hwf0.symm, hwf1.symm,
        ⟨hf₀c1, hf₀c2, hf₀L2⟩, ⟨hf₁c1, hf₁c2, hf₁L2⟩, ⟨hwc1, hwc2, hwL2⟩⟩
    · -- non-adjacent: the two fully-free hubs would force ≥ 12 hub-edge incidences.
      have hp0 : (G.neighborFinset f₀ ∩ pair).card = 0 := by
        rw [Finset.card_eq_zero, hpairdef, Finset.eq_empty_iff_forall_notMem]
        intro a ha
        rw [Finset.mem_inter, G.mem_neighborFinset] at ha
        simp only [Finset.mem_insert, Finset.mem_singleton] at ha
        rcases ha.2 with rfl | rfl
        · exact G.irrefl ha.1
        · exact hadj ha.1
      have hp1 : (G.neighborFinset f₁ ∩ pair).card = 0 := by
        rw [Finset.card_eq_zero, hpairdef, Finset.eq_empty_iff_forall_notMem]
        intro a ha
        rw [Finset.mem_inter, G.mem_neighborFinset] at ha
        simp only [Finset.mem_insert, Finset.mem_singleton] at ha
        rcases ha.2 with rfl | rfl
        · exact hadj ha.1.symm
        · exact G.irrefl ha.1
      have e0 := hsplit f₀
      have e1 := hsplit f₁
      have hRnn : 0 ≤ ∑ w ∈ Dᶜ \ pair, (G.neighborFinset w ∩ (Dᶜ \ pair)).card := Nat.zero_le _
      rw [hcc] at hSumsplit
      rw [hRsum] at hSumsplit
      omega
  · -- |FF| = 1 case: the avoiders span ≥ 5 hubs of total internal degree ≥ 11 > 10.
    push Not at hsecond
    have hcap : ∀ g : Fin 15, g ∈ A1 → g ∈ A2 → g = f₀ := by
      intro g hg1 hg2
      rw [hA1def, Finset.mem_filter] at hg1
      rw [hA2def, Finset.mem_filter] at hg2
      obtain ⟨hgDc, hgL1, hgc1, hgc2⟩ := hg1
      obtain ⟨_, _, _, hgL2⟩ := hg2
      exact hsecond g (by rw [hFFdef, Finset.mem_filter]; exact ⟨hgDc, hgL1, hgc1, hgc2, hgL2⟩)
    have hf₀A1 : f₀ ∈ A1 := by rw [hA1def, Finset.mem_filter]; exact ⟨hf₀Dc, hf₀L1, hf₀c1, hf₀c2⟩
    have hf₀A2 : f₀ ∈ A2 := by rw [hA2def, Finset.mem_filter]; exact ⟨hf₀Dc, hf₀c1, hf₀c2, hf₀L2⟩
    have hT1sub : A1.erase f₀ ⊆ Dᶜ := (Finset.erase_subset _ _).trans hA1sub
    have hT2sub : A2.erase f₀ ⊆ Dᶜ := (Finset.erase_subset _ _).trans hA2sub
    have hT1card : 2 ≤ (A1.erase f₀).card := by
      rw [Finset.card_erase_of_mem hf₀A1]; omega
    have hT2card : 2 ≤ (A2.erase f₀).card := by
      rw [Finset.card_erase_of_mem hf₀A2]; omega
    have hdisjT : Disjoint (A1.erase f₀) (A2.erase f₀) := by
      rw [Finset.disjoint_left]
      intro g hgT1 hgT2
      exact (Finset.mem_erase.mp hgT1).1
        (hcap g (Finset.mem_erase.mp hgT1).2 (Finset.mem_erase.mp hgT2).2)
    have hf₀nT : f₀ ∉ A1.erase f₀ ∪ A2.erase f₀ := by
      rw [Finset.mem_union]; push Not
      exact ⟨fun h => (Finset.mem_erase.mp h).1 rfl, fun h => (Finset.mem_erase.mp h).1 rfl⟩
    have hsumT1 : 2 * (A1.erase f₀).card ≤ ∑ g ∈ A1.erase f₀, (G.neighborFinset g ∩ Dᶜ).card := by
      have := Finset.card_nsmul_le_sum (A1.erase f₀)
        (fun g => (G.neighborFinset g ∩ Dᶜ).card) 2
        (fun g hg => hA1int g (Finset.mem_of_mem_erase hg))
      simpa [smul_eq_mul, mul_comm] using this
    have hsumT2 : 2 * (A2.erase f₀).card ≤ ∑ g ∈ A2.erase f₀, (G.neighborFinset g ∩ Dᶜ).card := by
      have := Finset.card_nsmul_le_sum (A2.erase f₀)
        (fun g => (G.neighborFinset g ∩ Dᶜ).card) 2
        (fun g hg => hA2int g (Finset.mem_of_mem_erase hg))
      simpa [smul_eq_mul, mul_comm] using this
    have hSsub : insert f₀ (A1.erase f₀ ∪ A2.erase f₀) ⊆ Dᶜ := by
      rw [Finset.insert_subset_iff]
      exact ⟨hf₀Dc, Finset.union_subset hT1sub hT2sub⟩
    have hsumS : ∑ g ∈ insert f₀ (A1.erase f₀ ∪ A2.erase f₀), (G.neighborFinset g ∩ Dᶜ).card
        = (G.neighborFinset f₀ ∩ Dᶜ).card
          + ((∑ g ∈ A1.erase f₀, (G.neighborFinset g ∩ Dᶜ).card)
            + ∑ g ∈ A2.erase f₀, (G.neighborFinset g ∩ Dᶜ).card) := by
      rw [Finset.sum_insert hf₀nT, Finset.sum_union hdisjT]
    have hle : ∑ g ∈ insert f₀ (A1.erase f₀ ∪ A2.erase f₀), (G.neighborFinset g ∩ Dᶜ).card
        ≤ ∑ w ∈ Dᶜ, (G.neighborFinset w ∩ Dᶜ).card :=
      Finset.sum_le_sum_of_subset_of_nonneg hSsub (fun _ _ _ => Nat.zero_le _)
    have hf₀int : 3 ≤ (G.neighborFinset f₀ ∩ Dᶜ).card := hFFint f₀ hf₀FF
    rw [hSum10, hsumS] at hle
    omega

end N15

end ACMax
