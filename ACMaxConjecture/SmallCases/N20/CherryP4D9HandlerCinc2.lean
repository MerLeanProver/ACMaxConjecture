import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N20.Core
import ACMaxConjecture.SmallCases.StarCertificates
import ACMaxConjecture.SmallCases.N20.BipartiteAvoiderTwoHub
import ACMaxConjecture.SmallCases.N20.CherryP4HubTriangleForceD9FF4

/-!
# `n = 20` dense-cherry `|D| = 9` (`11` hubs) ISO1 hard-`c` subcase — the `cinc h₁ ≥ 2`,
`h₅`-closed world

Companion to `iso1_dichotomy_to_false` (the `h₅`-*open* handler, `1 ≤ intdeg h₅`): here the
degree-`5` hub `h₅` is *internally isolated* (`intdeg h₅ = 0`), so its `Iso`-cap rises to `4`
and the ledger `∑ B = 2 + 4 + 9 = 15 = ∑ isoinc` is **deficit `0`**.  The extra structural input is
`hID4u` — `h₁` is the UNIQUE internally-isolated degree-`4` hub.  With `h₁ ~ L₁, L₂` and no
`c`-contact (`deg4_path_bad_of_two`), the `TwoTwin`/`TwoHub` dichotomy handles the low branches;
in the tie the nine degree-`4` hubs `≠ h₁, h₅` are pinned to `isoinc = 1` and, since `h₁, h₅`
consume `≥ 3` `cinc`-slots, at least `6` hubs are cherry-`P₃`-free — pigeonholing them into the
five `Iso` twins gives a shared pair, hence a triangle (`Σ = 11`, `hT`) or a `SingleVertexConfig`
(`hsv`).
-/

namespace ACMax

open scoped Classical

namespace N20

/-- **`|D| = 9` (`11` hubs) ISO1 hard-`c` subcase, `cinc h₁ ≥ 2`, `h₅`-closed world (deficit `0`).**
The `2 ≤ cinc h₁`, `intdeg h₅ = 0` corner of the `|Dᶜ| = 11` dense-cherry near-`K₅` ISO1 kernel,
where `h₁` is the unique internally-isolated degree-`4` hub (`hID4u`). -/
theorem iso1_cinc2_h5closed_eleven (G : SimpleGraph (Fin 20))
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
    (hh1cinc : 2 ≤ (G.neighborFinset h₁ ∩ ({L₁, c₁, c₂, L₂} : Finset (Fin 20))).card)
    (hh5Dc : h₅ ∈ Dᶜ) (hh5d : G.degree h₅ = 5) (hh5int0 : G.neighborFinset h₅ ∩ Dᶜ = ∅)
    (hne15 : h₁ ≠ h₅)
    (hID4u : ∀ h : Fin 20, h ∈ Dᶜ → G.degree h = 4 → h ≠ h₁ →
      (G.neighborFinset h ∩ Dᶜ).card ≠ 0)
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
  have hT10 : ¬∃ x y z : Fin 20, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10 := by
    rintro ⟨x, y, z, hxy, hyz, hxz, ha, hb, hc, hs⟩
    exact hT ⟨x, y, z, hxy, hyz, hxz, ha, hb, hc, by omega⟩
  -- `Iso` vertices meet no degree-`3` vertex.
  have hIso_nadj : ∀ t : Fin 20, t ∈ Iso → ∀ w : Fin 20, G.degree w = 3 → ¬G.Adj t w :=
    fun t ht w hw hadj => (hIsoprop t ht).2 w hadj hw
  -- `L₁ ≠ L₂` via the good triangle `c₁–c₂–L₁` (using `he : L₁ = L₂`).
  have hL1L2 : L₁ ≠ L₂ := by
    intro he
    exact hT10 ⟨c₁, c₂, L₁, G.ne_of_adj hc12, he.symm ▸ G.ne_of_adj hac2L2,
      G.ne_of_adj hac1L1, hc12, he.symm ▸ hac2L2, hac1L1, by omega⟩
  -- Cherry `P₄` non-adjacencies.
  have hnc1L2 : ¬G.Adj c₁ L₂ := by
    intro hadj
    have hmem : L₂ ∈ G.neighborFinset c₁ ∩ D :=
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset c₁ L₂).mpr hadj, hL2D⟩
    rw [hNc1D] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h
    · exact (G.ne_of_adj hac2L2) h.symm
    · exact hL1L2 h.symm
  have hnc2L1 : ¬G.Adj c₂ L₁ := by
    intro hadj
    have hmem : L₁ ∈ G.neighborFinset c₂ ∩ D :=
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset c₂ L₁).mpr hadj, hL1D⟩
    rw [hNc2D] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h
    · exact (G.ne_of_adj hac1L1) h.symm
    · exact hL1L2 h
  have hPnotIso : ∀ x : Fin 20, x ∈ P → x ∉ Iso := by
    intro x hx hxIso
    simp only [hPdef, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact (hIsoprop x hxIso).2 c₁ hac1L1.symm hc1deg
    · exact (hIsoprop x hxIso).2 c₂ hc12 hc2deg
    · exact (hIsoprop x hxIso).2 c₁ hc12.symm hc1deg
    · exact (hIsoprop x hxIso).2 c₂ hac2L2.symm hc2deg
  -- `h₁`'s neighbourhood: both leaves and no `c`.
  have hbad1 := deg4_path_bad_of_two G L₁ c₁ c₂ L₂ h₁ hT10 hC4 hac1L1 hc12 hac2L2 hnc1L2 hnc2L1
    hL1nc2 hL2nc1 hL1deg hc1deg hc2deg hL2deg hh1d hh1cinc
  obtain ⟨hAdjh1L1, hAdjh1L2, hnh1c1, hnh1c2⟩ := hbad1
  -- `¬ G.Adj L₁ L₂` from the good triangle `h₁–L₁–L₂`.
  have hnL1L2 : ¬G.Adj L₁ L₂ := by
    intro hadj
    exact hT10 ⟨h₁, L₁, L₂, G.ne_of_adj hAdjh1L1, hL1L2, G.ne_of_adj hAdjh1L2,
      hAdjh1L1, hadj, hAdjh1L2, by rw [hh1d, hL1deg, hL2deg]⟩
  -- `L₁`'s / `L₂`'s only degree-`3` neighbour is `c₁` / `c₂`.
  have hL1only : ∀ w : Fin 20, G.Adj L₁ w → G.degree w = 3 → w = c₁ := by
    intro w hadj hw
    have hwD : w ∈ D := (hmemD w).mpr hw
    rcases hclassP w hwD with h | h | h | h | h
    · exact absurd (h ▸ hadj) G.irrefl
    · exact h
    · exact absurd (h ▸ hadj) (fun ha => hnc2L1 ha.symm)
    · exact absurd (h ▸ hadj) hnL1L2
    · exact absurd hadj (fun ha => (hIsoprop w h).2 L₁ ha.symm hL1deg)
  have hL2only : ∀ w : Fin 20, G.Adj L₂ w → G.degree w = 3 → w = c₂ := by
    intro w hadj hw
    have hwD : w ∈ D := (hmemD w).mpr hw
    rcases hclassP w hwD with h | h | h | h | h
    · exact absurd (h ▸ hadj) (fun ha => hnL1L2 ha.symm)
    · exact absurd (h ▸ hadj) (fun ha => hnc1L2 ha.symm)
    · exact h
    · exact absurd (h ▸ hadj) G.irrefl
    · exact absurd hadj (fun ha => (hIsoprop w h).2 L₂ ha.symm hL2deg)
  -- `N h₁ ⊆ D` and its membership characterisation.
  have hN1subD : G.neighborFinset h₁ ⊆ D := by
    intro x hx
    by_contra hxD
    have hmem : x ∈ G.neighborFinset h₁ ∩ Dᶜ :=
      Finset.mem_inter.mpr ⟨hx, Finset.mem_compl.mpr hxD⟩
    rw [hh1iso] at hmem; exact absurd hmem (Finset.notMem_empty x)
  have hN1char : ∀ x : Fin 20, x ∈ G.neighborFinset h₁ → x = L₁ ∨ x = L₂ ∨ x ∈ Iso := by
    intro x hx
    have hadj : G.Adj h₁ x := (G.mem_neighborFinset h₁ x).mp hx
    rcases hclassP x (hN1subD hx) with h | h | h | h | h
    · exact Or.inl h
    · exact absurd (h ▸ hadj) hnh1c1
    · exact absurd (h ▸ hadj) hnh1c2
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  have hdeg3 : ∀ x : Fin 20, x ∈ G.neighborFinset h₁ → G.degree x = 3 :=
    fun x hx => (hmemD x).mp (hN1subD hx)
  have hindep : ∀ x : Fin 20, x ∈ G.neighborFinset h₁ → ∀ y : Fin 20, y ∈ G.neighborFinset h₁ →
      x ≠ y → ¬G.Adj x y := by
    intro x hx y hy hxy hadj
    rcases hN1char x hx with hx1 | hx2 | hxI
    · rcases hN1char y hy with hy1 | hy2 | hyI
      · exact hxy (hx1.trans hy1.symm)
      · exact hnL1L2 (hx1 ▸ hy2 ▸ hadj)
      · exact hIso_nadj y hyI x (hdeg3 x hx) hadj.symm
    · rcases hN1char y hy with hy1 | hy2 | hyI
      · exact hnL1L2 (hy1 ▸ hx2 ▸ hadj.symm)
      · exact hxy (hx2.trans hy2.symm)
      · exact hIso_nadj y hyI x (hdeg3 x hx) hadj.symm
    · exact hIso_nadj x hxI y (hdeg3 y hy) hadj
  -- Apply the counting dichotomy.
  have h1int0 : (G.neighborFinset h₁ ∩ Dᶜ).card = 0 := by rw [hh1iso]; exact Finset.card_empty
  by_cases hD1 : ∃ h : Fin 20, h ∈ Dᶜ ∧
      (G.neighborFinset h ∩ P).card = 0 ∧
      2 ≤ (G.neighborFinset h ∩ Iso).card
  · obtain ⟨hc, hcHub, hccinc0, hcisoge2⟩ := hD1
    obtain ⟨t₁, ht1, t₂, ht2, ht12⟩ := Finset.one_lt_card.mp (by omega : 1 < (G.neighborFinset hc ∩ Iso).card)
    obtain ⟨ht1N, ht1Iso⟩ := Finset.mem_inter.mp ht1
    obtain ⟨ht2N, ht2Iso⟩ := Finset.mem_inter.mp ht2
    have hAdj_ct1 : G.Adj hc t₁ := (G.mem_neighborFinset hc t₁).mp ht1N
    have hAdj_ct2 : G.Adj hc t₂ := (G.mem_neighborFinset hc t₂).mp ht2N
    have hdegt1 : G.degree t₁ = 3 := (hIsoprop t₁ ht1Iso).1
    have hdegt2 : G.degree t₂ = 3 := (hIsoprop t₂ ht2Iso).1
    have hNhP : G.neighborFinset hc ∩ P = ∅ := Finset.card_eq_zero.mp hccinc0
    have hnhc_of : ∀ w : Fin 20, w ∈ P → ¬G.Adj hc w := by
      intro w hw hadj
      have : w ∈ G.neighborFinset hc ∩ P :=
        Finset.mem_inter.mpr ⟨(G.mem_neighborFinset hc w).mpr hadj, hw⟩
      rw [hNhP] at this; exact absurd this (Finset.notMem_empty w)
    have hnhc1 : ¬G.Adj hc c₁ := hnhc_of c₁ (by simp [hPdef])
    have hnhc2 : ¬G.Adj hc c₂ := hnhc_of c₂ (by simp [hPdef])
    have hnhcL2 : ¬G.Adj hc L₂ := hnhc_of L₂ (by simp [hPdef])
    have hc_notD : hc ∉ D := Finset.mem_compl.mp hcHub
    have ht1_neP : ∀ w : Fin 20, w ∈ P → t₁ ≠ w := fun w hw he => hPnotIso w hw (he ▸ ht1Iso)
    have ht2_neP : ∀ w : Fin 20, w ∈ P → t₂ ≠ w := fun w hw he => hPnotIso w hw (he ▸ ht2Iso)
    exact htt ⟨t₁, t₂, hc, c₁, c₂, L₂, hdegt1, hdegt2, hdeg5 hc hcHub, hc1deg, hc2deg, hL2deg,
      hAdj_ct1.symm, hAdj_ct2.symm, hc12, hac2L2,
      (fun ha => hIso_nadj t₁ ht1Iso c₁ hc1deg ha), (fun ha => hIso_nadj t₁ ht1Iso c₂ hc2deg ha),
      (fun ha => hIso_nadj t₁ ht1Iso L₂ hL2deg ha),
      (fun ha => hIso_nadj t₂ ht2Iso c₁ hc1deg ha), (fun ha => hIso_nadj t₂ ht2Iso c₂ hc2deg ha),
      (fun ha => hIso_nadj t₂ ht2Iso L₂ hL2deg ha),
      hnhc1, hnhc2, hnhcL2, ht12,
      ht1_neP c₁ (by simp [hPdef]), ht1_neP c₂ (by simp [hPdef]), ht1_neP L₂ (by simp [hPdef]),
      ht2_neP c₁ (by simp [hPdef]), ht2_neP c₂ (by simp [hPdef]), ht2_neP L₂ (by simp [hPdef]),
      (fun he => hc_notD (he ▸ hc1D)), (fun he => hc_notD (he ▸ hc2D)),
      (fun he => hc_notD (he ▸ hL2D)),
      G.ne_of_adj hc12, G.ne_of_adj hac2L2, hL2nc1.symm⟩
  · by_cases hD2 : ∃ h : Fin 20, h ∈ Dᶜ ∧ h ≠ h₁ ∧ G.degree h = 4 ∧
        (G.neighborFinset h ∩ Dᶜ).card ≤ 1
    · obtain ⟨h₂, hh2Hub, hne2, hh2deg, hh2int⟩ := hD2
      have hnadj12 : ¬G.Adj h₁ h₂ := by
        intro ha
        have : h₂ ∈ G.neighborFinset h₁ ∩ Dᶜ :=
          Finset.mem_inter.mpr ⟨(G.mem_neighborFinset h₁ h₂).mpr ha, hh2Hub⟩
        rw [hh1iso] at this; exact absurd this (Finset.notMem_empty h₂)
      have hshare := isolated_deg4_share_le_one G h₁ h₂ hC4 hh1d hh2deg (Ne.symm hne2) hnadj12
        hdeg3 hindep
      -- `Iso`-neighbours of `h₁`: exactly `2`.
      have hIe2 : (G.neighborFinset h₁ ∩ Iso).card = 2 := by
        have hdech1 := hper h₁ hh1Dc
        -- cinc = 2 (from `hh1cinc` and `deg4_path_bad`), intdeg = 0.
        have hcinc2 : (G.neighborFinset h₁ ∩ P).card = 2 := by
          have hsub : ({L₁, L₂} : Finset (Fin 20)) ⊆ G.neighborFinset h₁ ∩ P := by
            intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl
            · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset h₁ x).mpr hAdjh1L1, by simp [hPdef]⟩
            · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset h₁ x).mpr hAdjh1L2, by simp [hPdef]⟩
          have hle : (G.neighborFinset h₁ ∩ P).card ≤ 2 := by
            have hsubP : G.neighborFinset h₁ ∩ P ⊆ {L₁, L₂} := by
              intro x hx
              obtain ⟨hxN, hxP⟩ := Finset.mem_inter.mp hx
              rcases hN1char x hxN with h | h | h
              · simp [h]
              · simp [h]
              · exact absurd (Finset.mem_inter.mpr ⟨hxN, hxP⟩) (by
                  have := hPnotIso x hxP; exact fun _ => this h)
            have := Finset.card_le_card hsubP
            have h2 : ({L₁, L₂} : Finset (Fin 20)).card = 2 := by
              rw [Finset.card_insert_of_notMem (by simp [hL1L2]), Finset.card_singleton]
            omega
          have := Finset.card_le_card hsub
          have h2 : ({L₁, L₂} : Finset (Fin 20)).card = 2 := by
            rw [Finset.card_insert_of_notMem (by simp [hL1L2]), Finset.card_singleton]
          omega
        rw [hcinc2, h1int0, hh1d] at hdech1; omega
      -- `h₂` has `≥ 3` degree-`3` neighbours.
      have hN2D_card : 3 ≤ (G.neighborFinset h₂ ∩ D).card := by
        have hdisj : Disjoint (G.neighborFinset h₂ ∩ D) (G.neighborFinset h₂ ∩ Dᶜ) := by
          apply Finset.disjoint_left.mpr; intro a ha hb
          exact (Finset.mem_compl.mp (Finset.mem_inter.mp hb).2) (Finset.mem_inter.mp ha).2
        have hunion : (G.neighborFinset h₂ ∩ D) ∪ (G.neighborFinset h₂ ∩ Dᶜ) = G.neighborFinset h₂ := by
          rw [← Finset.inter_union_distrib_left, Finset.union_compl, Finset.inter_univ]
        have hsum : (G.neighborFinset h₂ ∩ D).card + (G.neighborFinset h₂ ∩ Dᶜ).card = G.degree h₂ := by
          rw [← Finset.card_union_of_disjoint hdisj, hunion, G.card_neighborFinset_eq_degree]
        omega
      -- `h₂`'s private degree-`3` neighbours: at least `2`.
      have hQ2card : 2 ≤ ((G.neighborFinset h₂ ∩ D) \ G.neighborFinset h₁).card := by
        have hsplit := Finset.card_sdiff_add_card_inter (G.neighborFinset h₂ ∩ D) (G.neighborFinset h₁)
        have hsub : (G.neighborFinset h₂ ∩ D) ∩ G.neighborFinset h₁
            ⊆ G.neighborFinset h₁ ∩ G.neighborFinset h₂ := by
          intro x hx
          obtain ⟨hxND, hxN1⟩ := Finset.mem_inter.mp hx
          exact Finset.mem_inter.mpr ⟨hxN1, (Finset.mem_inter.mp hxND).1⟩
        have := Finset.card_le_card hsub
        omega
      obtain ⟨c, hcQ, d, hdQ, hcd⟩ := Finset.one_lt_card.mp (by omega : 1 < ((G.neighborFinset h₂ ∩ D) \ G.neighborFinset h₁).card)
      obtain ⟨hcND, hcN1⟩ := Finset.mem_sdiff.mp hcQ
      obtain ⟨hdND, hdN1⟩ := Finset.mem_sdiff.mp hdQ
      obtain ⟨hcN2, hcD⟩ := Finset.mem_inter.mp hcND
      obtain ⟨hdN2, hdD⟩ := Finset.mem_inter.mp hdND
      -- The closing assembly, given a valid `(a, b)` leaf pair for `h₁`.
      have finish : ∀ a b : Fin 20, a ∈ Iso → a ∈ G.neighborFinset h₁ → a ∉ G.neighborFinset h₂ →
          b ∈ G.neighborFinset h₁ → b ∉ G.neighborFinset h₂ → G.degree b = 3 → a ≠ b →
          ¬G.Adj b c → ¬G.Adj b d → False := by
        intro a b haI haN1 haN2 hbN1 hbN2 hbdeg hab hnbc hnbd
        apply hth
        have hdega : G.degree a = 3 := (hIsoprop a haI).1
        have hdegc : G.degree c = 3 := (hmemD c).mp hcD
        have hdegd : G.degree d = 3 := (hmemD d).mp hdD
        have hah1 : G.Adj a h₁ := ((G.mem_neighborFinset h₁ a).mp haN1).symm
        have hbh1 : G.Adj b h₁ := ((G.mem_neighborFinset h₁ b).mp hbN1).symm
        have hch2 : G.Adj c h₂ := ((G.mem_neighborFinset h₂ c).mp hcN2).symm
        have hdh2 : G.Adj d h₂ := ((G.mem_neighborFinset h₂ d).mp hdN2).symm
        have hn_ah2 : ¬G.Adj a h₂ := fun ha => haN2 ((G.mem_neighborFinset h₂ a).mpr ha.symm)
        have hn_bh2 : ¬G.Adj b h₂ := fun ha => hbN2 ((G.mem_neighborFinset h₂ b).mpr ha.symm)
        have hn_h1c : ¬G.Adj h₁ c := fun ha => hcN1 ((G.mem_neighborFinset h₁ c).mpr ha)
        have hn_h1d : ¬G.Adj h₁ d := fun ha => hdN1 ((G.mem_neighborFinset h₁ d).mpr ha)
        have hn_ac : ¬G.Adj a c := fun ha => (hIsoprop a haI).2 c ha hdegc
        have hn_ad : ¬G.Adj a d := fun ha => (hIsoprop a haI).2 d ha hdegd
        have hne_ac : a ≠ c := fun he => haN2 (he.symm ▸ hcN2)
        have hne_ad : a ≠ d := fun he => haN2 (he.symm ▸ hdN2)
        have hne_bc : b ≠ c := fun he => hbN2 (he.symm ▸ hcN2)
        have hne_bd : b ≠ d := fun he => hbN2 (he.symm ▸ hdN2)
        exact two_hub_cherry_pair_twenty G h₁ h₂ a b c d hh1d hh2deg hdega hbdeg hdegc hdegd
          hah1 hbh1 hch2 hdh2 hnadj12 hn_h1c hn_h1d hn_ah2 hn_bh2 hn_ac hn_ad hnbc hnbd
          hab hcd hne_ac hne_ad hne_bc hne_bd
      -- Private `Iso`-neighbours of `h₁`: at least `1`.
      have hpriv_iso : 1 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card := by
        have hsplit := Finset.card_sdiff_add_card_inter (G.neighborFinset h₁ ∩ Iso) (G.neighborFinset h₂)
        have hsub : (G.neighborFinset h₁ ∩ Iso) ∩ G.neighborFinset h₂
            ⊆ G.neighborFinset h₁ ∩ G.neighborFinset h₂ := by
          intro x hx
          obtain ⟨hxNI, hxN2⟩ := Finset.mem_inter.mp hx
          exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hxNI).1, hxN2⟩
        have := Finset.card_le_card hsub
        rw [hIe2] at hsplit
        omega
      by_cases hcaseA : 2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card
      · -- **Case A** — both `Iso`-neighbours of `h₁` are private; both leaves are `Iso`.
        obtain ⟨a, haM, b, hbM, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card)
        obtain ⟨haNI, haN2⟩ := Finset.mem_sdiff.mp haM
        obtain ⟨hbNI, hbN2⟩ := Finset.mem_sdiff.mp hbM
        obtain ⟨haN1, haI⟩ := Finset.mem_inter.mp haNI
        obtain ⟨hbN1, hbI⟩ := Finset.mem_inter.mp hbNI
        have hdegc : G.degree c = 3 := (hmemD c).mp hcD
        have hdegd : G.degree d = 3 := (hmemD d).mp hdD
        exact finish a b haI haN1 haN2 hbN1 hbN2 (hIsoprop b hbI).1 hab
          (fun ha => (hIsoprop b hbI).2 c ha hdegc) (fun ha => (hIsoprop b hbI).2 d ha hdegd)
      · -- **Case B** — one `Iso`-neighbour of `h₁` is shared; `L₁, L₂ ∉ N h₂`; leaf `b ∈ {L₁, L₂}`.
        have hpriv1 : ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card = 1 := by omega
        obtain ⟨a, haM⟩ := Finset.card_eq_one.mp hpriv1
        have haMem : a ∈ (G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂ := by rw [haM]; simp
        obtain ⟨haNI, haN2⟩ := Finset.mem_sdiff.mp haMem
        obtain ⟨haN1, haI⟩ := Finset.mem_inter.mp haNI
        -- `L₁, L₂ ∉ N h₂` (else the share would exceed `1`).
        have hshareIso : 1 ≤ ((G.neighborFinset h₁ ∩ Iso) ∩ G.neighborFinset h₂).card := by
          have hsplit := Finset.card_sdiff_add_card_inter (G.neighborFinset h₁ ∩ Iso) (G.neighborFinset h₂)
          rw [hIe2, hpriv1] at hsplit; omega
        obtain ⟨s, hsMem⟩ := Finset.card_pos.mp (by omega : 0 < ((G.neighborFinset h₁ ∩ Iso) ∩ G.neighborFinset h₂).card)
        obtain ⟨hsNI, hsN2⟩ := Finset.mem_inter.mp hsMem
        obtain ⟨hsN1, hsI⟩ := Finset.mem_inter.mp hsNI
        have hLnotN2 : ∀ L : Fin 20, G.Adj h₁ L → L ∉ Iso → L ∉ G.neighborFinset h₂ := by
          intro L hadjL hLIso hLN2
          have hLN1 : L ∈ G.neighborFinset h₁ := (G.mem_neighborFinset h₁ L).mpr hadjL
          have hne_Ls : L ≠ s := fun he => hLIso (he ▸ hsI)
          have h2mem : ({L, s} : Finset (Fin 20)) ⊆ G.neighborFinset h₁ ∩ G.neighborFinset h₂ := by
            intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl
            · exact Finset.mem_inter.mpr ⟨hLN1, hLN2⟩
            · exact Finset.mem_inter.mpr ⟨hsN1, hsN2⟩
          have hc2 : ({L, s} : Finset (Fin 20)).card = 2 := by
            rw [Finset.card_insert_of_notMem (by simp [hne_Ls]), Finset.card_singleton]
          have := Finset.card_le_card h2mem; omega
        have hL1N2 : L₁ ∉ G.neighborFinset h₂ := hLnotN2 L₁ hAdjh1L1 (fun h => hPnotIso L₁ (by simp [hPdef]) h)
        have hL2N2 : L₂ ∉ G.neighborFinset h₂ := hLnotN2 L₂ hAdjh1L2 (fun h => hPnotIso L₂ (by simp [hPdef]) h)
        have hL1N1 : L₁ ∈ G.neighborFinset h₁ := (G.mem_neighborFinset h₁ L₁).mpr hAdjh1L1
        have hL2N1 : L₂ ∈ G.neighborFinset h₁ := (G.mem_neighborFinset h₁ L₂).mpr hAdjh1L2
        have haL1 : a ≠ L₁ := fun he => hPnotIso L₁ (by simp [hPdef]) (he ▸ haI)
        have haL2 : a ≠ L₂ := fun he => hPnotIso L₂ (by simp [hPdef]) (he ▸ haI)
        -- `h₂` cannot meet both `c₁` and `c₂` (good triangle `h₂–c₁–c₂`).
        have hnotboth : ¬(G.Adj h₂ c₁ ∧ G.Adj h₂ c₂) := by
          rintro ⟨hp, hq⟩
          have hh2c1 : h₂ ≠ c₁ := fun he => (Finset.mem_compl.mp hh2Hub) (he ▸ hc1D)
          have hh2c2 : h₂ ≠ c₂ := fun he => (Finset.mem_compl.mp hh2Hub) (he ▸ hc2D)
          exact hT10 ⟨h₂, c₁, c₂, hh2c1, G.ne_of_adj hc12, hh2c2, hp, hc12, hq, by omega⟩
        by_cases hh2c1 : G.Adj h₂ c₁
        · -- `¬G.Adj h₂ c₂`; use `b = L₂` (`L₂`'s only degree-`3` neighbour is `c₂ ∉ N h₂`).
          have hc2N2 : c₂ ∉ G.neighborFinset h₂ :=
            fun hm => (hnotboth ⟨hh2c1, (G.mem_neighborFinset h₂ c₂).mp hm⟩)
          have hnbc : ¬G.Adj L₂ c := by
            intro ha
            have := hL2only c ha ((hmemD c).mp hcD)
            exact hc2N2 (this ▸ hcN2)
          have hnbd : ¬G.Adj L₂ d := by
            intro ha
            have := hL2only d ha ((hmemD d).mp hdD)
            exact hc2N2 (this ▸ hdN2)
          exact finish a L₂ haI haN1 haN2 hL2N1 hL2N2 hL2deg haL2 hnbc hnbd
        · -- `¬G.Adj h₂ c₁`; use `b = L₁` (`L₁`'s only degree-`3` neighbour is `c₁ ∉ N h₂`).
          have hc1N2 : c₁ ∉ G.neighborFinset h₂ :=
            fun hm => hh2c1 ((G.mem_neighborFinset h₂ c₁).mp hm)
          have hnbc : ¬G.Adj L₁ c := by
            intro ha
            have := hL1only c ha ((hmemD c).mp hcD)
            exact hc1N2 (this ▸ hcN2)
          have hnbd : ¬G.Adj L₁ d := by
            intro ha
            have := hL1only d ha ((hmemD d).mp hdD)
            exact hc1N2 (this ▸ hdN2)
          exact finish a L₁ haI haN1 haN2 hL1N1 hL1N2 hL1deg haL1 hnbc hnbd

    · -- **The deficit-`0` tie.**  Pigeonhole the cherry-`P₃`-free hubs into the five `Iso` twins.
      push Not at hD1 hD2
      have hc1nIso : c₁ ∉ Iso := fun h => (hIsoprop c₁ h).2 L₁ hac1L1 hL1deg
      have hc2nIso : c₂ ∉ Iso := fun h => (hIsoprop c₂ h).2 c₁ hc12.symm hc1deg
      have hL1nIso : L₁ ∉ Iso := fun h => (hIsoprop L₁ h).2 c₁ hac1L1.symm hc1deg
      -- Per-hub `Iso`-cap `B h₁ = 2`, `B h₅ = 4`, `B other = 1` (deficit `0`).
      set B : Fin 20 → ℕ := fun h => if h = h₁ then 2 else if h = h₅ then 4 else 1 with hBdef
      have hbound : ∀ h : Fin 20, h ∈ Dᶜ → (G.neighborFinset h ∩ Iso).card ≤ B h := by
        intro h hh
        have hdec := hper h hh
        by_cases hh1 : h = h₁
        · simp only [hBdef, if_pos hh1]
          have hint0 : (G.neighborFinset h ∩ Dᶜ).card = 0 := by rw [hh1, hh1iso]; exact Finset.card_empty
          have hdh : G.degree h = 4 := by rw [hh1]; exact hh1d
          have hcinc : 2 ≤ (G.neighborFinset h ∩ P).card := by
            rw [hh1]; exact hh1cinc
          rw [hint0, hdh] at hdec; omega
        · by_cases hh5 : h = h₅
          · simp only [hBdef, if_neg hh1, if_pos hh5]
            have hint0 : (G.neighborFinset h ∩ Dᶜ).card = 0 := by
              rw [hh5, hh5int0]; exact Finset.card_empty
            have hdh : G.degree h = 5 := by rw [hh5]; exact hh5d
            rw [hint0, hdh] at hdec
            by_cases hc0 : (G.neighborFinset h ∩ P).card = 0
            · have hlt := hD1 h hh hc0; rw [hc0] at hdec; omega
            · omega
          · simp only [hBdef, if_neg hh1, if_neg hh5]
            have hd4 := hdegOth h hh hh1 hh5
            rw [hd4] at hdec
            have hint2 := hD2 h hh hh1 hd4
            by_cases hc0 : (G.neighborFinset h ∩ P).card = 0
            · have hlt := hD1 h hh hc0; omega
            · omega
      have hsumB : ∑ h ∈ Dᶜ, B h = 15 := by
        have hpt : ∀ h, B h = 1 + ((if h = h₁ then 1 else 0) + (if h = h₅ then 3 else 0)) := by
          intro h
          by_cases hh1 : h = h₁
          · subst hh1; simp [hBdef, hne15]
          · by_cases hh5 : h = h₅
            · subst hh5; simp [hBdef, hh1]
            · simp [hBdef, hh1, hh5]
        simp only [hpt, Finset.sum_add_distrib, Finset.sum_const, hHub11, smul_eq_mul,
          Finset.sum_ite_eq' Dᶜ h₁ (fun _ => (1 : ℕ)),
          Finset.sum_ite_eq' Dᶜ h₅ (fun _ => (3 : ℕ)), hh1Dc, hh5Dc, if_pos]
        omega
      have hdsum : ∑ h ∈ Dᶜ, (B h - (G.neighborFinset h ∩ Iso).card) = 0 := by
        have hsplit : ∑ h ∈ Dᶜ, ((G.neighborFinset h ∩ Iso).card
            + (B h - (G.neighborFinset h ∩ Iso).card)) = ∑ h ∈ Dᶜ, B h :=
          Finset.sum_congr rfl (fun h hh => Nat.add_sub_cancel' (hbound h hh))
        rw [Finset.sum_add_distrib, hsumIso15, hsumB] at hsplit
        omega
      have hcap : ∀ h : Fin 20, h ∈ Dᶜ → B h - (G.neighborFinset h ∩ Iso).card = 0 :=
        fun h hh => (Finset.sum_eq_zero_iff.mp hdsum) h hh
      -- `h₅` sits at cap: `isoinc h₅ = 4`, hence `cinc h₅ = 1`.
      have hBh5 : B h₅ = 4 := by simp [hBdef, Ne.symm hne15]
      have hiso5 : (G.neighborFinset h₅ ∩ Iso).card = 4 := by
        have hz := hcap h₅ hh5Dc; have hle := hbound h₅ hh5Dc; rw [hBh5] at hz hle; omega
      have hcinc5 : (G.neighborFinset h₅ ∩ P).card = 1 := by
        have hdec := hper h₅ hh5Dc
        have hint0 : (G.neighborFinset h₅ ∩ Dᶜ).card = 0 := by rw [hh5int0]; exact Finset.card_empty
        rw [hiso5, hint0, hh5d] at hdec; omega
      -- The `≥ 6` cherry-`P₃`-free hubs (`cinc = 0`), each carrying exactly one `Iso` twin.
      set S : Finset (Fin 20) :=
        Dᶜ.filter (fun h => (G.neighborFinset h ∩ P).card = 0)
        with hSdef
      have hScard : 6 ≤ S.card := by
        set T : Finset (Fin 20) :=
          Dᶜ.filter (fun h =>
            ¬ ((G.neighborFinset h ∩ P).card = 0)) with hTdef
        have hpart : S.card + T.card = 11 := by
          rw [hSdef, hTdef, ← hHub11]
          exact Finset.card_filter_add_card_filter_not
            (fun h => (G.neighborFinset h ∩ P).card = 0)
        have hsumT : ∑ h ∈ T, (G.neighborFinset h ∩ P).card = 6 := by
          rw [hTdef, Finset.sum_filter_of_ne (fun x _ hx => hx), hsumPath]
        have hTcinc1 : ∀ h ∈ T, 1 ≤ (G.neighborFinset h ∩ P).card := by
          intro h hh; rw [hTdef, Finset.mem_filter] at hh; omega
        have hh1T : h₁ ∈ T := by
          rw [hTdef, Finset.mem_filter]; exact ⟨hh1Dc, by have := hh1cinc; omega⟩
        have hsum_erase : ∑ h ∈ T, (G.neighborFinset h ∩ P).card
            = (G.neighborFinset h₁ ∩ P).card
              + ∑ h ∈ T.erase h₁, (G.neighborFinset h ∩ P).card :=
          (Finset.add_sum_erase T _ hh1T).symm
        have hge : (T.erase h₁).card
            ≤ ∑ h ∈ T.erase h₁, (G.neighborFinset h ∩ P).card := by
          have := Finset.card_nsmul_le_sum (T.erase h₁)
            (fun h => (G.neighborFinset h ∩ P).card) 1
            (fun h hh => hTcinc1 h (Finset.mem_of_mem_erase hh))
          simpa using this
        have hTerase : (T.erase h₁).card + 1 = T.card := Finset.card_erase_add_one hh1T
        have hcinc1 : 2 ≤ (G.neighborFinset h₁ ∩ P).card := hh1cinc
        omega
      have hSprop : ∀ h : Fin 20, h ∈ S →
          h ∈ Dᶜ ∧ (G.neighborFinset h ∩ P).card = 0 ∧
          h ≠ h₁ ∧ h ≠ h₅ ∧ G.degree h = 4 ∧ (G.neighborFinset h ∩ Iso).card = 1 := by
        intro h hh
        rw [hSdef, Finset.mem_filter] at hh
        obtain ⟨hhDc, hc0⟩ := hh
        have hne1 : h ≠ h₁ := by intro he; rw [he] at hc0; have := hh1cinc; omega
        have hne5 : h ≠ h₅ := by intro he; rw [he] at hc0; rw [hcinc5] at hc0; exact absurd hc0 (by norm_num)
        have hd4 := hdegOth h hhDc hne1 hne5
        have hBh : B h = 1 := by simp only [hBdef, if_neg hne1, if_neg hne5]
        have hz := hcap h hhDc; have hle := hbound h hhDc; rw [hBh] at hz hle
        exact ⟨hhDc, hc0, hne1, hne5, hd4, by omega⟩
      have hne13 : ∀ u w : Fin 20, G.degree u = 4 → G.degree w = 3 → u ≠ w :=
        fun u w hu hw he => by rw [he, hw] at hu; exact absurd hu (by norm_num)
      have hIsone : ∀ u w : Fin 20, u ∈ Iso → w ∉ Iso → u ≠ w :=
        fun u w hu hw he => hw (he ▸ hu)
      have hpure : ∀ x : Fin 20, x ∈ S →
          (G.neighborFinset x ∩ ({L₁, c₁, c₂} : Finset (Fin 20))).card = 0 := by
        intro x hx
        obtain ⟨_, hxc0, _⟩ := hSprop x hx
        have hsub : G.neighborFinset x ∩ ({L₁, c₁, c₂} : Finset (Fin 20))
            ⊆ G.neighborFinset x ∩ P := by
          intro w hw; obtain ⟨hwN, hwm⟩ := Finset.mem_inter.mp hw
          refine Finset.mem_inter.mpr ⟨hwN, ?_⟩
          simp only [hPdef, Finset.mem_insert, Finset.mem_singleton] at hwm ⊢
          tauto
        have := Finset.card_le_card hsub; rw [hxc0] at this; omega
      set f : Fin 20 → Fin 20 :=
        fun x => if hx : (G.neighborFinset x ∩ Iso).Nonempty then hx.choose else x with hfdef
      have hftwin : ∀ h ∈ S, G.Adj h (f h) ∧ f h ∈ Iso := by
        intro h hh
        obtain ⟨_, _, _, _, _, hiso1⟩ := hSprop h hh
        have hne : (G.neighborFinset h ∩ Iso).Nonempty := Finset.card_pos.mp (by rw [hiso1]; norm_num)
        have hmem : f h ∈ G.neighborFinset h ∩ Iso := by
          simp only [hfdef, dif_pos hne]; exact hne.choose_spec
        obtain ⟨hN, hI⟩ := Finset.mem_inter.mp hmem
        exact ⟨(G.mem_neighborFinset h (f h)).mp hN, hI⟩
      obtain ⟨F, hFS, F', hF'S, hFF', hff⟩ :=
        Finset.exists_ne_map_eq_of_card_lt_of_maps_to (s := S) (t := Iso) (f := f)
          (by rw [hIsocard]; omega)
          (by intro h hh; rw [Finset.mem_coe] at hh; exact Finset.mem_coe.mpr (hftwin h hh).2)
      have htwI : f F ∈ Iso := (hftwin F hFS).2
      have hAFt : G.Adj F (f F) := (hftwin F hFS).1
      have hAF't : G.Adj F' (f F) := by have h := (hftwin F' hF'S).1; rwa [← hff] at h
      obtain ⟨hFDc, hFc0, hFne1, hFne5, hdF, _⟩ := hSprop F hFS
      obtain ⟨hF'Dc, hF'c0, hF'ne1, hF'ne5, hdF', _⟩ := hSprop F' hF'S
      have hdegfF : G.degree (f F) = 3 := (hIsoprop (f F) htwI).1
      by_cases hadjFF' : G.Adj F F'
      · exact hT ⟨F, F', f F, hFF', hne13 F' (f F) hdF' hdegfF, hne13 F (f F) hdF hdegfF,
          hadjFF', hAF't, hAFt, by omega⟩
      · refine hsv ⟨f F, F, F', L₁, c₁, c₂, hdegfF, hL1deg, hc1deg, hc2deg,
          hAFt.symm, hAF't.symm, hac1L1.symm, hc12, fun h => hnc2L1 h.symm, ?_,
          hFF', hIsone (f F) L₁ htwI hL1nIso, hIsone (f F) c₁ htwI hc1nIso,
          hIsone (f F) c₂ htwI hc2nIso, hne13 F L₁ hdF hL1deg, hne13 F c₁ hdF hc1deg,
          hne13 F c₂ hdF hc2deg, hne13 F' L₁ hdF' hL1deg, hne13 F' c₁ hdF' hc1deg,
          hne13 F' c₂ hdF' hc2deg, (G.ne_of_adj hac1L1).symm, G.ne_of_adj hc12, hL1nc2⟩
        have hsum0 : (∑ p ∈ ({f F, F, F'} : Finset (Fin 20)),
            (G.neighborFinset p ∩ ({L₁, c₁, c₂} : Finset (Fin 20))).card) = 0 := by
          apply Finset.sum_eq_zero
          intro p hp
          simp only [Finset.mem_insert, Finset.mem_singleton] at hp
          rcases hp with rfl | hpF | hpF'
          · rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
            intro w hw; obtain ⟨hwN, hwm⟩ := Finset.mem_inter.mp hw
            simp only [Finset.mem_insert, Finset.mem_singleton] at hwm
            have hadj := (G.mem_neighborFinset (f F) w).mp hwN
            rcases hwm with rfl | rfl | rfl
            · exact hIso_nadj (f F) htwI w hL1deg hadj
            · exact hIso_nadj (f F) htwI w hc1deg hadj
            · exact hIso_nadj (f F) htwI w hc2deg hadj
          · rw [hpF]; exact hpure F hFS
          · rw [hpF']; exact hpure F' hF'S
        rw [hsum0, if_neg hadjFF']; omega

end N20

end ACMax
