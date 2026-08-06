import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N20.Core
import ACMaxConjecture.SmallCases.StarCertificates
import ACMaxConjecture.SmallCases.N20.BipartiteAvoiderTwoHub
import ACMaxConjecture.SmallCases.N20.CherryP4HubTriangleForceHardC11

/-!
# `n = 20` dense-cherry `|D| = 9` (`11` hubs) ISO1 hard-`c` subcase — the `h₅`-open world

Companion to `iso1_hard_c_subcase_eleven` (the `h₅`-closed, deficit-`1` handler): here the
degree-`5` hub `h₅` is *internally non-isolated* (`1 ≤ intdeg h₅`), so its `Iso`-cap drops to
`3` and the ledger `∑ B = 3 + 3 + 9 = 15 = ∑ isoinc` is **deficit `0`** (every hub sits exactly
at its cap).  With `h₁ ~ c₁` and `cinc h₁ ≤ 1` (`isoinc h₁ = 3`) the Case-`I`/`II` dichotomy
`iso1_d9_caseI_hardc11` disposes of low-internal partners; in Case `II` the tight ledger pins
the nine degree-`4` hubs `≠ h₁, h₅` to `isoinc = 1`.  A slot count (`c₁` has hub-slot `{h₁}`,
`c₂`/`L₁` hold `1`/`2`) leaves `≥ 6` cherry-`P₃`-avoiders, which pigeonhole into the five `Iso`
twins to a shared pair — a triangle (`Σ = 11`, `hT`) or a `SingleVertexConfig` (`hsv`).
-/

namespace ACMax

open scoped Classical

namespace N20

/-- **`|D| = 9` (`11` hubs) ISO1 hard-`c` subcase, `h₅`-open world (deficit `0`).**  The `cinc h₁ ≤ 1`,
`h₁ ~ c₁`, `1 ≤ intdeg h₅` corner of the `|Dᶜ| = 11` dense-cherry near-`K₅` ISO1 kernel. -/
theorem iso1_hardc0_h5open_eleven (G : SimpleGraph (Fin 20))
    (D Iso : Finset (Fin 20)) (L₁ c₁ c₂ L₂ h₁ h₅ : Fin 20)
    (hmemD : ∀ v : Fin 20, v ∈ D ↔ G.degree v = 3)
    (hIsoprop : ∀ v ∈ Iso, G.degree v = 3 ∧ (∀ w : Fin 20, G.Adj v w → G.degree w ≠ 3))
    (hclassP : ∀ x : Fin 20, x ∈ D → x = L₁ ∨ x = c₁ ∨ x = c₂ ∨ x = L₂ ∨ x ∈ Iso)
    (hL1deg : G.degree L₁ = 3) (hc1deg : G.degree c₁ = 3)
    (hc2deg : G.degree c₂ = 3) (hL2deg : G.degree L₂ = 3)
    (hac1L1 : G.Adj c₁ L₁) (hc12 : G.Adj c₁ c₂) (hac2L2 : G.Adj c₂ L₂)
    (hL1nc2 : L₁ ≠ c₂) (hL2nc1 : L₂ ≠ c₁)
    (hNc1D : G.neighborFinset c₁ ∩ D = {c₂, L₁}) (hNc2D : G.neighborFinset c₂ ∩ D = {c₁, L₂})
    (hL1D : L₁ ∈ D) (hc1D : c₁ ∈ D) (hc2D : c₂ ∈ D) (hL2D : L₂ ∈ D)
    (htt : ¬TwoTwinConfig G) (hth : ¬TwoHubConfig G) (hsv : ¬SingleVertexConfig G)
    (hT : ¬∃ x y z : Fin 20, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 11)
    (hC4 : ¬∃ a b c d : Fin 20, ({a, b, c, d} : Finset (Fin 20)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (hHub11 : Dᶜ.card = 11) (hIsocard : Iso.card = 5)
    (hdeg5 : ∀ h : Fin 20, h ∈ Dᶜ → G.degree h ≤ 5)
    (hper : ∀ h : Fin 20, h ∈ Dᶜ →
      (G.neighborFinset h ∩ ({L₁, c₁, c₂, L₂} : Finset (Fin 20))).card
        + (G.neighborFinset h ∩ Iso).card + (G.neighborFinset h ∩ Dᶜ).card = G.degree h)
    (hsumPath : ∑ g ∈ Dᶜ, (G.neighborFinset g ∩ ({L₁, c₁, c₂, L₂} : Finset (Fin 20))).card = 6)
    (hsumIso15 : ∑ h ∈ Dᶜ, (G.neighborFinset h ∩ Iso).card = 15)
    (hc1hub : (G.neighborFinset c₁ ∩ Dᶜ).card = 1)
    (hc2hub : (G.neighborFinset c₂ ∩ Dᶜ).card = 1)
    (hL1hub : (G.neighborFinset L₁ ∩ Dᶜ).card = 2)
    (hL2hub : (G.neighborFinset L₂ ∩ Dᶜ).card = 2)
    (hh1Dc : h₁ ∈ Dᶜ) (hh1d : G.degree h₁ = 4) (hh1iso : G.neighborFinset h₁ ∩ Dᶜ = ∅)
    (hRc1 : G.Adj h₁ c₁)
    (hcinc1 : (G.neighborFinset h₁ ∩ ({L₁, c₁, c₂, L₂} : Finset (Fin 20))).card ≤ 1)
    (hh5Dc : h₅ ∈ Dᶜ) (hh5d : G.degree h₅ = 5)
    (hdeg5int : 1 ≤ (G.neighborFinset h₅ ∩ Dᶜ).card) (hne15 : h₁ ≠ h₅)
    (hdegOth : ∀ h : Fin 20, h ∈ Dᶜ → h ≠ h₁ → h ≠ h₅ → G.degree h = 4)
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
  have hL1L2 : L₁ ≠ L₂ := by
    intro he
    exact hT ⟨c₁, c₂, L₁, G.ne_of_adj hc12, he.symm ▸ G.ne_of_adj hac2L2,
      G.ne_of_adj hac1L1, hc12, he.symm ▸ hac2L2, hac1L1, by omega⟩
  have hnc2L1 : ¬G.Adj c₂ L₁ := by
    intro hadj
    have hmem : L₁ ∈ G.neighborFinset c₂ ∩ D :=
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset c₂ L₁).mpr hadj, hL1D⟩
    rw [hNc2D] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h
    · exact (G.ne_of_adj hac1L1) h.symm
    · exact hL1L2 h
  have hN1subD : G.neighborFinset h₁ ⊆ D := by
    intro x hx
    by_contra hxD
    have hmem : x ∈ G.neighborFinset h₁ ∩ Dᶜ :=
      Finset.mem_inter.mpr ⟨hx, Finset.mem_compl.mpr hxD⟩
    rw [hh1iso] at hmem; exact absurd hmem (Finset.notMem_empty x)
  have hdeg3N1 : ∀ x : Fin 20, x ∈ G.neighborFinset h₁ → G.degree x = 3 :=
    fun x hx => (hmemD x).mp (hN1subD hx)
  have hc1N1 : c₁ ∈ G.neighborFinset h₁ := (G.mem_neighborFinset h₁ c₁).mpr hRc1
  have hcinc1' : (G.neighborFinset h₁ ∩ P).card = 1 := by
    have hc1mem : c₁ ∈ G.neighborFinset h₁ ∩ P :=
      Finset.mem_inter.mpr ⟨hc1N1, by simp [hPdef]⟩
    have hpos : 1 ≤ (G.neighborFinset h₁ ∩ P).card := Finset.card_pos.mpr ⟨c₁, hc1mem⟩
    omega
  have hh1int0 : (G.neighborFinset h₁ ∩ Dᶜ).card = 0 := by rw [hh1iso]; exact Finset.card_empty
  have hisoinc3 : (G.neighborFinset h₁ ∩ Iso).card = 3 := by
    have := hper h₁ hh1Dc
    rw [hcinc1', hh1int0, hh1d] at this; omega
  have hN1char : ∀ x : Fin 20, x ∈ G.neighborFinset h₁ → x = c₁ ∨ x ∈ Iso := by
    intro x hx
    have hadj : G.Adj h₁ x := (G.mem_neighborFinset h₁ x).mp hx
    rcases hclassP x (hN1subD hx) with h | h | h | h | h
    · exfalso
      have hL1mem : L₁ ∈ G.neighborFinset h₁ ∩ P :=
        Finset.mem_inter.mpr ⟨h ▸ hx, by simp [hPdef]⟩
      have hc1mem : c₁ ∈ G.neighborFinset h₁ ∩ P :=
        Finset.mem_inter.mpr ⟨hc1N1, by simp [hPdef]⟩
      have hsub : ({c₁, L₁} : Finset (Fin 20)) ⊆ G.neighborFinset h₁ ∩ P := by
        intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl
        · exact hc1mem
        · exact hL1mem
      have hcard2 : ({c₁, L₁} : Finset (Fin 20)).card = 2 := by
        rw [Finset.card_insert_of_notMem (by simp [G.ne_of_adj hac1L1]), Finset.card_singleton]
      have := Finset.card_le_card hsub; rw [hcard2, hcinc1'] at this; omega
    · exact Or.inl h
    · exfalso
      have hmem : c₂ ∈ G.neighborFinset h₁ ∩ P :=
        Finset.mem_inter.mpr ⟨h ▸ hx, by simp [hPdef]⟩
      have hc1mem : c₁ ∈ G.neighborFinset h₁ ∩ P :=
        Finset.mem_inter.mpr ⟨hc1N1, by simp [hPdef]⟩
      have hsub : ({c₁, c₂} : Finset (Fin 20)) ⊆ G.neighborFinset h₁ ∩ P := by
        intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl
        · exact hc1mem
        · exact hmem
      have hcard2 : ({c₁, c₂} : Finset (Fin 20)).card = 2 := by
        rw [Finset.card_insert_of_notMem (by simp [G.ne_of_adj hc12]), Finset.card_singleton]
      have := Finset.card_le_card hsub; rw [hcard2, hcinc1'] at this; omega
    · exfalso
      have hmem : L₂ ∈ G.neighborFinset h₁ ∩ P :=
        Finset.mem_inter.mpr ⟨h ▸ hx, by simp [hPdef]⟩
      have hc1mem : c₁ ∈ G.neighborFinset h₁ ∩ P :=
        Finset.mem_inter.mpr ⟨hc1N1, by simp [hPdef]⟩
      have hne : c₁ ≠ L₂ := Ne.symm hL2nc1
      have hsub : ({c₁, L₂} : Finset (Fin 20)) ⊆ G.neighborFinset h₁ ∩ P := by
        intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl
        · exact hc1mem
        · exact hmem
      have hcard2 : ({c₁, L₂} : Finset (Fin 20)).card = 2 := by
        rw [Finset.card_insert_of_notMem (by simp [hne]), Finset.card_singleton]
      have := Finset.card_le_card hsub; rw [hcard2, hcinc1'] at this; omega
    · exact Or.inr h
  have hindep1 : ∀ x ∈ G.neighborFinset h₁, ∀ y ∈ G.neighborFinset h₁, x ≠ y → ¬G.Adj x y := by
    intro x hx y hy hxy hadj
    rcases hN1char x hx with hxc | hxI
    · rcases hN1char y hy with hyc | hyI
      · exact hxy (hxc.trans hyc.symm)
      · exact hIso_nadj y hyI x (hxc ▸ hc1deg) hadj.symm
    · exact hIso_nadj x hxI y (hdeg3N1 y hy) hadj
  -- **Case-`I`/`II` dichotomy.**
  by_cases hCaseI : ∃ k : Fin 20, k ∈ Dᶜ ∧ k ≠ h₁ ∧ G.degree k = 4
      ∧ (G.neighborFinset k ∩ Dᶜ).card ≤ 1
  · obtain ⟨k, hkDc, hkne, hkd, hkint⟩ := hCaseI
    exact iso1_d9_caseI_hardc11 G D Iso h₁ k hmemD hIsoprop hth hC4 hh1d hh1iso hindep1
      (by rw [hisoinc3]) hkDc hkne hkd hkint
  · push Not at hCaseI
    have hCaseII : ∀ k : Fin 20, k ∈ Dᶜ → k ≠ h₁ → G.degree k = 4 →
        2 ≤ (G.neighborFinset k ∩ Dᶜ).card := by
      intro k hkDc hkne hkd
      have := hCaseI k hkDc hkne hkd; omega
    have hubD_ne : ∀ h : Fin 20, h ∈ Dᶜ → h ≠ L₁ ∧ h ≠ c₁ ∧ h ≠ c₂ ∧ h ≠ L₂ := by
      intro h hh
      have hhD : h ∉ D := Finset.mem_compl.mp hh
      exact ⟨fun he => hhD (he ▸ hL1D), fun he => hhD (he ▸ hc1D),
        fun he => hhD (he ▸ hc2D), fun he => hhD (he ▸ hL2D)⟩
    have hNoTT : ∀ h : Fin 20, h ∈ Dᶜ → (G.neighborFinset h ∩ P).card = 0 →
        (G.neighborFinset h ∩ Iso).card ≤ 1 := by
      intro h hh hcinc0
      by_contra hgt
      push Not at hgt
      have hPempty : G.neighborFinset h ∩ P = ∅ := Finset.card_eq_zero.mp hcinc0
      have hnadjP : ∀ w : Fin 20, w ∈ P → ¬G.Adj h w := by
        intro w hw hadj
        have : w ∈ G.neighborFinset h ∩ P :=
          Finset.mem_inter.mpr ⟨(G.mem_neighborFinset h w).mpr hadj, hw⟩
        rw [hPempty] at this; exact absurd this (Finset.notMem_empty w)
      obtain ⟨hnL1, hnc1, hnc2, hnL2⟩ := hubD_ne h hh
      exact htt (twotwin_of_centre_twenty G Iso h L₁ c₁ c₂ hIsoprop hL1deg hc1deg hc2deg
        (hdeg5 h hh) hac1L1.symm hc12
        (hnadjP L₁ (by simp [hPdef])) (hnadjP c₁ (by simp [hPdef])) (hnadjP c₂ (by simp [hPdef]))
        hL1nIso hc1nIso hc2nIso hnL1 hnc1 hnc2
        (G.ne_of_adj hac1L1).symm (G.ne_of_adj hc12) hL1nc2 (by omega))
    -- **Per-hub `Iso`-cap ledger.**  `B h₁ = 3`, `B h₅ = 3` (`h₅` open), `B other = 1`.
    set B : Fin 20 → ℕ := fun h => if h = h₁ then 3 else if h = h₅ then 3 else 1 with hBdef
    have hbound : ∀ h : Fin 20, h ∈ Dᶜ → (G.neighborFinset h ∩ Iso).card ≤ B h := by
      intro h hh
      have hdec := hper h hh
      by_cases hh1 : h = h₁
      · have hBh : B h = 3 := by simp only [hBdef, if_pos hh1]
        rw [hBh, hh1, hisoinc3]
      · by_cases hh5 : h = h₅
        · have hBh : B h = 3 := by simp only [hBdef, if_neg hh1, if_pos hh5]
          rw [hBh]
          have hdh : G.degree h = 5 := by rw [hh5]; exact hh5d
          have hint : 1 ≤ (G.neighborFinset h ∩ Dᶜ).card := by rw [hh5]; exact hdeg5int
          rw [hdh] at hdec
          by_cases hc0 : (G.neighborFinset h ∩ P).card = 0
          · have := hNoTT h hh hc0; omega
          · omega
        · have hBh : B h = 1 := by simp only [hBdef, if_neg hh1, if_neg hh5]
          rw [hBh]
          have hd4 := hdegOth h hh hh1 hh5
          rw [hd4] at hdec
          have hint2 := hCaseII h hh hh1 hd4
          by_cases hc0 : (G.neighborFinset h ∩ P).card = 0
          · have := hNoTT h hh hc0; omega
          · omega
    have hsumB : ∑ h ∈ Dᶜ, B h = 15 := by
      have hpt : ∀ h, B h = 1 + ((if h = h₁ then 2 else 0) + (if h = h₅ then 2 else 0)) := by
        intro h
        by_cases hh1 : h = h₁
        · subst hh1; simp [hBdef, hne15]
        · by_cases hh5 : h = h₅
          · subst hh5; simp [hBdef, hh1]
          · simp [hBdef, hh1, hh5]
      simp only [hpt, Finset.sum_add_distrib, Finset.sum_const, hHub11, smul_eq_mul,
        Finset.sum_ite_eq' Dᶜ h₁ (fun _ => (2 : ℕ)),
        Finset.sum_ite_eq' Dᶜ h₅ (fun _ => (2 : ℕ)), hh1Dc, hh5Dc, if_pos]
      omega
    -- **Deficit `0` ⟹ every hub sits at its cap.**
    have hdsum : ∑ h ∈ Dᶜ, (B h - (G.neighborFinset h ∩ Iso).card) = 0 := by
      have hsplit : ∑ h ∈ Dᶜ, ((G.neighborFinset h ∩ Iso).card
          + (B h - (G.neighborFinset h ∩ Iso).card)) = ∑ h ∈ Dᶜ, B h :=
        Finset.sum_congr rfl (fun h hh => Nat.add_sub_cancel' (hbound h hh))
      rw [Finset.sum_add_distrib, hsumIso15, hsumB] at hsplit
      omega
    have hcap : ∀ h : Fin 20, h ∈ Dᶜ → B h - (G.neighborFinset h ∩ Iso).card = 0 :=
      fun h hh => (Finset.sum_eq_zero_iff.mp hdsum) h hh
    have hOthiso1 : ∀ h : Fin 20, h ∈ Dᶜ → h ≠ h₁ → h ≠ h₅ →
        (G.neighborFinset h ∩ Iso).card = 1 := by
      intro h hh hh1 hh5
      have hBh : B h = 1 := by simp only [hBdef, if_neg hh1, if_neg hh5]
      have hz := hcap h hh
      have hle := hbound h hh
      rw [hBh] at hz hle; omega
    -- **The finisher.**  `c₁`'s lone hub-neighbour is `h₁`; collect `≥ 6` cherry-`P₃`-avoiders.
    have hNc1Dc : G.neighborFinset c₁ ∩ Dᶜ = {h₁} := by
      have h1mem : h₁ ∈ G.neighborFinset c₁ ∩ Dᶜ :=
        Finset.mem_inter.mpr ⟨(G.mem_neighborFinset c₁ h₁).mpr hRc1.symm, hh1Dc⟩
      exact (Finset.eq_of_subset_of_card_le
        (by intro x hx; rw [Finset.mem_singleton] at hx; exact hx ▸ h1mem)
        (by rw [hc1hub, Finset.card_singleton])).symm
    have hpurec1 : ∀ x : Fin 20, x ∈ Dᶜ → x ≠ h₁ → ¬G.Adj x c₁ := by
      intro x hxDc hxne1 ha
      have hmem : x ∈ G.neighborFinset c₁ ∩ Dᶜ :=
        Finset.mem_inter.mpr ⟨(G.mem_neighborFinset c₁ x).mpr ha.symm, hxDc⟩
      rw [hNc1Dc, Finset.mem_singleton] at hmem; exact hxne1 hmem
    have hdeg4ne3 : ∀ u w : Fin 20, G.degree u = 4 → G.degree w = 3 → u ≠ w := by
      intro u w hu hw he; rw [he] at hu; omega
    have hIsone : ∀ u w : Fin 20, u ∈ Iso → w ∉ Iso → u ≠ w :=
      fun u w hu hw he => hw (he ▸ hu)
    have hpurecard : ∀ x : Fin 20, ¬G.Adj x L₁ → ¬G.Adj x c₁ → ¬G.Adj x c₂ →
        (G.neighborFinset x ∩ ({L₁, c₁, c₂} : Finset (Fin 20))).card = 0 := by
      intro x hxL1 hxc1 hxc2
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro w hw; rw [Finset.mem_inter] at hw
      obtain ⟨hwN, hwm⟩ := hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hwm
      have hadj := (G.mem_neighborFinset x w).mp hwN
      rcases hwm with rfl | rfl | rfl
      · exact hxL1 hadj
      · exact hxc1 hadj
      · exact hxc2 hadj
    have hScard : 6 ≤ (Dᶜ.filter
        (fun h => h ≠ h₁ ∧ h ≠ h₅ ∧ ¬G.Adj h L₁ ∧ ¬G.Adj h c₂)).card := by
      have hcover : Dᶜ ⊆ (Dᶜ.filter
          (fun h => h ≠ h₁ ∧ h ≠ h₅ ∧ ¬G.Adj h L₁ ∧ ¬G.Adj h c₂))
          ∪ (({h₁, h₅} : Finset (Fin 20)) ∪
              ((G.neighborFinset L₁ ∩ Dᶜ) ∪ (G.neighborFinset c₂ ∩ Dᶜ))) := by
        intro x hx
        by_cases hp : x ≠ h₁ ∧ x ≠ h₅ ∧ ¬G.Adj x L₁ ∧ ¬G.Adj x c₂
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hx, hp⟩)
        · refine Finset.mem_union_right _ ?_
          by_cases hx1 : x = h₁
          · exact Finset.mem_union_left _ (by simp [hx1])
          · by_cases hx5 : x = h₅
            · exact Finset.mem_union_left _ (by simp [hx5])
            · by_cases hxL1 : G.Adj x L₁
              · exact Finset.mem_union_right _ (Finset.mem_union_left _
                  (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset L₁ x).mpr hxL1.symm, hx⟩))
              · by_cases hxc2 : G.Adj x c₂
                · exact Finset.mem_union_right _ (Finset.mem_union_right _
                    (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset c₂ x).mpr hxc2.symm, hx⟩))
                · exact absurd ⟨hx1, hx5, hxL1, hxc2⟩ hp
      have hcard2 : ({h₁, h₅} : Finset (Fin 20)).card ≤ 2 := by
        have := Finset.card_insert_le h₁ ({h₅} : Finset (Fin 20))
        rw [Finset.card_singleton] at this; omega
      have hunionR2 : ((G.neighborFinset L₁ ∩ Dᶜ) ∪ (G.neighborFinset c₂ ∩ Dᶜ)).card ≤ 3 := by
        have := Finset.card_union_le (G.neighborFinset L₁ ∩ Dᶜ) (G.neighborFinset c₂ ∩ Dᶜ)
        rw [hL1hub, hc2hub] at this; omega
      have hunionR : (({h₁, h₅} : Finset (Fin 20)) ∪
          ((G.neighborFinset L₁ ∩ Dᶜ) ∪ (G.neighborFinset c₂ ∩ Dᶜ))).card ≤ 5 := by
        have := Finset.card_union_le ({h₁, h₅} : Finset (Fin 20))
          ((G.neighborFinset L₁ ∩ Dᶜ) ∪ (G.neighborFinset c₂ ∩ Dᶜ))
        omega
      have hcov := Finset.card_le_card hcover
      have hunion := Finset.card_union_le
        (Dᶜ.filter (fun h => h ≠ h₁ ∧ h ≠ h₅ ∧ ¬G.Adj h L₁ ∧ ¬G.Adj h c₂))
        (({h₁, h₅} : Finset (Fin 20)) ∪
          ((G.neighborFinset L₁ ∩ Dᶜ) ∪ (G.neighborFinset c₂ ∩ Dᶜ)))
      rw [hHub11] at hcov; omega
    set f : Fin 20 → Fin 20 :=
      fun x => if hx : (G.neighborFinset x ∩ Iso).Nonempty then hx.choose else x
      with hfdef
    have hftwin : ∀ h ∈ Dᶜ.filter (fun h => h ≠ h₁ ∧ h ≠ h₅ ∧ ¬G.Adj h L₁ ∧ ¬G.Adj h c₂),
        G.Adj h (f h) ∧ f h ∈ Iso := by
      intro h hh
      rw [Finset.mem_filter] at hh
      obtain ⟨hhDc, hh1, hh5, _, _⟩ := hh
      have hne : (G.neighborFinset h ∩ Iso).Nonempty :=
        Finset.card_pos.mp (by rw [hOthiso1 h hhDc hh1 hh5]; norm_num)
      have hmem : f h ∈ G.neighborFinset h ∩ Iso := by
        simp only [hfdef, dif_pos hne]; exact hne.choose_spec
      obtain ⟨hN, hI⟩ := Finset.mem_inter.mp hmem
      exact ⟨(G.mem_neighborFinset h (f h)).mp hN, hI⟩
    obtain ⟨F, hFS, F', hF'S, hFF', hff⟩ :=
      Finset.exists_ne_map_eq_of_card_lt_of_maps_to
        (s := Dᶜ.filter (fun h => h ≠ h₁ ∧ h ≠ h₅ ∧ ¬G.Adj h L₁ ∧ ¬G.Adj h c₂))
        (t := Iso) (f := f) (by rw [hIsocard]; omega)
        (by
          intro h hh
          rw [Finset.mem_coe] at hh
          exact Finset.mem_coe.mpr (hftwin h hh).2)
    have htwI : f F ∈ Iso := (hftwin F hFS).2
    have hAFt : G.Adj F (f F) := (hftwin F hFS).1
    have hAF't : G.Adj F' (f F) := by
      have h := (hftwin F' hF'S).1; rwa [← hff] at h
    rw [Finset.mem_filter] at hFS hF'S
    obtain ⟨hFDc, hFne1, hFne5, hFnL1, hFnc2⟩ := hFS
    obtain ⟨hF'Dc, hF'ne1, hF'ne5, hF'nL1, hF'nc2⟩ := hF'S
    have hdF : G.degree F = 4 := hdegOth F hFDc hFne1 hFne5
    have hdF' : G.degree F' = 4 := hdegOth F' hF'Dc hF'ne1 hF'ne5
    have hdegfF : G.degree (f F) = 3 := (hIsoprop (f F) htwI).1
    by_cases hadjFF' : G.Adj F F'
    · exact hT ⟨F, F', f F, hFF', hdeg4ne3 F' (f F) hdF' hdegfF,
        hdeg4ne3 F (f F) hdF hdegfF, hadjFF', hAF't, hAFt, by omega⟩
    · refine hsv ⟨f F, F, F', L₁, c₁, c₂, hdegfF, hL1deg, hc1deg, hc2deg,
        hAFt.symm, hAF't.symm, hac1L1.symm, hc12, fun h => hnc2L1 h.symm, ?_,
        hFF', hIsone (f F) L₁ htwI hL1nIso, hIsone (f F) c₁ htwI hc1nIso,
        hIsone (f F) c₂ htwI hc2nIso, hdeg4ne3 F L₁ hdF hL1deg,
        hdeg4ne3 F c₁ hdF hc1deg, hdeg4ne3 F c₂ hdF hc2deg,
        hdeg4ne3 F' L₁ hdF' hL1deg, hdeg4ne3 F' c₁ hdF' hc1deg,
        hdeg4ne3 F' c₂ hdF' hc2deg, (G.ne_of_adj hac1L1).symm,
        G.ne_of_adj hc12, hL1nc2⟩
      have hsum0 : (∑ p ∈ ({f F, F, F'} : Finset (Fin 20)),
          (G.neighborFinset p ∩ ({L₁, c₁, c₂} : Finset (Fin 20))).card) = 0 := by
        apply Finset.sum_eq_zero
        intro p hp
        simp only [Finset.mem_insert, Finset.mem_singleton] at hp
        rcases hp with rfl | hpF | hpF'
        · exact hpurecard (f F) (hIso_nadj (f F) htwI L₁ hL1deg)
            (hIso_nadj (f F) htwI c₁ hc1deg) (hIso_nadj (f F) htwI c₂ hc2deg)
        · rw [hpF]
          exact hpurecard F hFnL1 (hpurec1 F hFDc hFne1) hFnc2
        · rw [hpF']
          exact hpurecard F' hF'nL1 (hpurec1 F' hF'Dc hF'ne1) hF'nc2
      rw [hsum0, if_neg hadjFF']; omega

end N20

end ACMax
