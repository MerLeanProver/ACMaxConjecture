import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N20.Core
import ACMaxConjecture.SmallCases.StarCertificates
import ACMaxConjecture.SmallCases.N20.Core
import ACMaxConjecture.SmallCases.N20.HubTriangleFF
import ACMaxConjecture.SmallCases.N20.CherryP4HubTriangleWA
import ACMaxConjecture.SmallCases.N20.CherryP4HubTriangleForceD9FF4
import ACMaxConjecture.SmallCases.N20.CherryP4HubTriangleForceD10Clean
import ACMaxConjecture.SmallCases.N20.CherryP4HubTriangleForceD10Exc
import ACMaxConjecture.SmallCases.N20.CherryP4D10HandlerDeg6
import ACMaxConjecture.SmallCases.N20.CherryP4HubTriangleForceD11
import ACMaxConjecture.SmallCases.N20.CherryP4HubTriangleForceHardC11
import ACMaxConjecture.SmallCases.N20.CherryP4D9HandlerH5Open
import ACMaxConjecture.SmallCases.N20.CherryP4D9HandlerCinc2
import ACMaxConjecture.SmallCases.N20.CherryP4D9HandlerAnchorTie
import ACMaxConjecture.SmallCases.N20.BipartiteAvoiderTwoHub

/-!
# `|FF|`-style force for the `n = 19`, `P₄`-cherry `|D| ∈ {9, 10, 11}` hub-triangle core

`iso_rich_force_p4_twenty` is the `|D| ∈ {9, 10, 11}` analog of `iso_rich_force_p4_seventeen`:
under the residual structural counts and the falsity of `TwoTwinConfig`, the assumption that
neither cherry admits a pairwise-adjacent avoider triple of degree sum `≤ 13` (`hntri1`, `hntri2`)
is contradictory.  The three `|D|` values are dispatched separately.

The `n = 19` internal total is `∑ int = 74 − 6|D|` (`20`/`14`/`8` for `|D| = 9`/`10`/`11`), the hub
degree total is `∑ deg = 72 − 3|D|` (`41`/`38`/`35`).

* `|D| = 11` (`8` hubs, `∑ int = 8`, avoiders `≥ 4`): clean counting (`budget_contra_gen`, with
  `budget_contra_exc` absorbing the lone degree-`≥ 6` hub).
* `|D| = 10` (`9` hubs, `∑ int = 14`, avoiders `≥ 5`): clean when all hubs have degree `≤ 5`
  (`3m = 15 > 14`).  A degree-`6` hub `h6` pins the other eight hubs to degree `4` (`38 = 6 + 8·4`);
  the anchor count on the `h6`-erased avoider sets forces `≥ 2` internally-isolated degree-`4`
  hubs, and the isolated-pair `TwoHub` machinery closes.
* `|D| = 9` (`10` hubs, `∑ int = 20`, `∑ deg = 41`, avoiders `≥ 6`): the anchor count forces an
  internally-isolated degree-`4` hub; ISO2 closes via the isolated pair, ISO1 via the `cinc h₁`
  case split (`iso1_dichotomy_to_false`, `iso1_hard_c_subcase_twenty`,
  `twotwin_of_centre_twenty`) — consolidated in the fully-proven `iso1_dense_corner_twenty`.
-/

namespace ACMax

open scoped Classical

namespace N20

/-- **ISO1 dichotomy → `False` (the complete structural assembly, axiom-clean).**
Given the extracted isolated degree-`4` hub `h₁` (with `2 ≤ cinc h₁`) and the unique degree-`5`
hub `h₅` in a `|D| = 9` ISO1 configuration, the sharp counting dichotomy
`iso1_intdeg_dichotomy_twenty` yields either a cherry-free `≥ 2`-`Iso` hub (a `TwoTwinConfig`
centre, contradicting `htt`) or a degree-`4` partner `h₂ ≠ h₁` of internal degree `≤ 1`.  In the
second case the isolated-hub share bound `isolated_deg4_share_le_one` keeps `≥ 3` private leaves on
`h₁` and `≥ 2` private degree-`3` leaves on `h₂`, and the cross non-adjacencies discharge from
`Iso`-isolation together with the `P₄` distance-`2` facts (`¬G.Adj L₁ c₂`, `¬G.Adj L₂ c₁`,
`¬G.Adj L₁ L₂`); the *only* structurally-dangerous cross pair `(L, c)` is avoided using the fact
that `h₂` cannot meet both `c₁` and `c₂` (that would be a good triangle `h₂–c₁–c₂` of degree sum
`10`, excluded by `hT`).  Assembling via `two_hub_cherry_pair_twenty` gives a `TwoHubConfig`,
contradicting `hth`.  This is the axiom-clean realisation of the two structural steps (name-extraction
interface + disjunct assembly); the input `2 ≤ cinc h₁` is supplied by the ISO1 `cinc` dispatch
inside `iso1_dense_corner_twenty`. -/
theorem iso1_dichotomy_to_false (G : SimpleGraph (Fin 20))
    (D Iso : Finset (Fin 20)) (L₁ c₁ c₂ L₂ h₁ h₅ : Fin 20)
    (hmemD : ∀ v : Fin 20, v ∈ D ↔ G.degree v = 3)
    (_hIsoD : Iso ⊆ D)
    (hIsoprop : ∀ v ∈ Iso, G.degree v = 3 ∧ (∀ w : Fin 20, G.Adj v w → G.degree w ≠ 3))
    (hclassP : ∀ x : Fin 20, x ∈ D → x = L₁ ∨ x = c₁ ∨ x = c₂ ∨ x = L₂ ∨ x ∈ Iso)
    (hL1deg : G.degree L₁ = 3) (hc1deg : G.degree c₁ = 3)
    (hc2deg : G.degree c₂ = 3) (hL2deg : G.degree L₂ = 3)
    (hac1L1 : G.Adj c₁ L₁) (hc12 : G.Adj c₁ c₂) (hac2L2 : G.Adj c₂ L₂)
    (hL1nc2 : L₁ ≠ c₂) (hL2nc1 : L₂ ≠ c₁)
    (hNc1D : G.neighborFinset c₁ ∩ D = {c₂, L₁}) (hNc2D : G.neighborFinset c₂ ∩ D = {c₁, L₂})
    (hL1D : L₁ ∈ D) (hc1D : c₁ ∈ D) (hc2D : c₂ ∈ D) (hL2D : L₂ ∈ D)
    (htt : ¬TwoTwinConfig G) (hth : ¬TwoHubConfig G)
    (hT : ¬∃ x y z : Fin 20, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 11)
    (hC4 : ¬∃ a b c d : Fin 20, ({a, b, c, d} : Finset (Fin 20)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (hHub11 : Dᶜ.card = 11)
    (hdeg_up : ∀ h : Fin 20, h ∈ Dᶜ → G.degree h ≤ 5)
    (hdecomp : ∀ h : Fin 20, h ∈ Dᶜ →
      (G.neighborFinset h ∩ ({L₁, c₁, c₂, L₂} : Finset (Fin 20))).card
        + (G.neighborFinset h ∩ Iso).card + (G.neighborFinset h ∩ Dᶜ).card = G.degree h)
    (hsumIso15 : ∑ h ∈ Dᶜ, (G.neighborFinset h ∩ Iso).card = 15)
    (hh1Dc : h₁ ∈ Dᶜ) (hh1d : G.degree h₁ = 4) (hh1iso : G.neighborFinset h₁ ∩ Dᶜ = ∅)
    (hh1cinc : 2 ≤ (G.neighborFinset h₁ ∩ ({L₁, c₁, c₂, L₂} : Finset (Fin 20))).card)
    (hh5Dc : h₅ ∈ Dᶜ) (hh5d : G.degree h₅ = 5) (hne15 : h₁ ≠ h₅)
    (hdeg5int : 1 ≤ (G.neighborFinset h₅ ∩ Dᶜ).card)
    (hdegOth : ∀ h : Fin 20, h ∈ Dᶜ → h ≠ h₁ → h ≠ h₅ → G.degree h = 4) :
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
  have hdich := iso1_intdeg_dichotomy_eleven G Dᶜ Iso P h₁ h₅ hHub11 hh1Dc hh5Dc hne15
    hh1d hh5d hdegOth hdecomp hsumIso15 hh1cinc h1int0 hdeg5int
  rcases hdich with ⟨hc, hcHub, hccinc0, hcisoge2⟩ | ⟨h₂, hh2Hub, hne2, hh2deg, hh2int⟩
  · -- **Disjunct 1** — a cherry-free `≥ 2`-`Iso` hub `hc` is a `TwoTwinConfig` centre.
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
    exact htt ⟨t₁, t₂, hc, c₁, c₂, L₂, hdegt1, hdegt2, hdeg_up hc hcHub, hc1deg, hc2deg, hL2deg,
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
  · -- **Disjunct 2** — a degree-`4` partner `h₂` of internal degree `≤ 1` yields a `TwoHubConfig`.
    have hnadj12 : ¬G.Adj h₁ h₂ := by
      intro ha
      have : h₂ ∈ G.neighborFinset h₁ ∩ Dᶜ :=
        Finset.mem_inter.mpr ⟨(G.mem_neighborFinset h₁ h₂).mpr ha, hh2Hub⟩
      rw [hh1iso] at this; exact absurd this (Finset.notMem_empty h₂)
    have hshare := isolated_deg4_share_le_one G h₁ h₂ hC4 hh1d hh2deg (Ne.symm hne2) hnadj12
      hdeg3 hindep
    -- `Iso`-neighbours of `h₁`: exactly `2`.
    have hIe2 : (G.neighborFinset h₁ ∩ Iso).card = 2 := by
      have hdech1 := hdecomp h₁ hh1Dc
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

set_option maxHeartbeats 1600000 in
/-- **The `n = 19` dense-cherry `|D| ∈ {9, 10}` isolated-hub kernel (fully proven).**

`|D| = 9` (`10` hubs, `∑ int = 20`, `∑ deg = 41 = 5 + 9·4`, avoiders `≥ 6`): the anchor count
`anchor_isolated_count_twenty` yields `≥ 2` internally-isolated hubs, and — with exactly one
degree-`5` hub — an internally-isolated degree-`4` hub always exists.  ISO2 (`≥ 2` such hubs)
closes via `isolated_pair_iso_rich_twenty` + `two_isolated_hub_twohubconfig_d9_ff4` against
`hth`.  ISO1 splits on `cinc h₁`: `cinc h₁ ≥ 2` closes via the counting dichotomy
`iso1_dichotomy_to_false` (`TwoTwin ∨ TwoHub`, both excluded); `cinc h₁ = 1` with the
cherry-neighbour an interior `c`-vertex is the hard near-`K₅` sub-case
`iso1_hard_c_subcase_twenty` (consuming `hntri1`, resp. `hntri2` through the `P₄` reflection
`(L₁, c₁, c₂, L₂) ↦ (L₂, c₂, c₁, L₁)`); otherwise `h₁` is a `TwoTwinConfig` centre avoiding a full
cherry `P₃`, contradicting `htt` (`twotwin_of_centre_twenty`).

`|D| = 10` (`9` hubs, `∑ int = 14`, `∑ deg = 38`, avoiders `≥ 5`): with every hub of degree `≤ 5`
the budget `14 < 3·5` is already contradictory (`budget_contra_gen`).  A degree-`6` hub `h6` pins
the eight other hubs to degree `4` (`38 = 6 + 8·4`), and the anchor applied to the `h6`-erased
avoider sets (`9 + 4 + 4 ≤ 14 + iso`) forces `≥ 3` internally-isolated hubs, hence `≥ 2`
internally-isolated degree-`4` hubs — the ISO2 pair machinery closes, so the degree-`6` ISO1
residual is arithmetically empty and no separate `cinc` kernel is needed there. -/
theorem iso1_dense_corner_twenty (G : SimpleGraph (Fin 20))
    (D Iso : Finset (Fin 20)) (L₁ c₁ c₂ L₂ : Fin 20)
    (h3 : ∀ v : Fin 20, 3 ≤ G.degree v)
    (hmemD : ∀ v : Fin 20, v ∈ D ↔ G.degree v = 3)
    (hIsoprop : ∀ v ∈ Iso, G.degree v = 3 ∧ (∀ w : Fin 20, G.Adj v w → G.degree w ≠ 3))
    (hisochar : ∀ w : Fin 20, w ∈ D → w ≠ L₁ → w ≠ c₁ → w ≠ c₂ → w ≠ L₂ → w ∈ Iso)
    (hL1deg : G.degree L₁ = 3) (hc1deg : G.degree c₁ = 3)
    (hc2deg : G.degree c₂ = 3) (hL2deg : G.degree L₂ = 3)
    (hac1L1 : G.Adj c₁ L₁) (hc12 : G.Adj c₁ c₂) (hac2L2 : G.Adj c₂ L₂)
    (hL1nc2 : L₁ ≠ c₂) (hL2nc1 : L₂ ≠ c₁)
    (hNc1D : G.neighborFinset c₁ ∩ D = {c₂, L₁}) (hNc2D : G.neighborFinset c₂ ∩ D = {c₁, L₂})
    (hL1D : L₁ ∈ D) (hc1D : c₁ ∈ D) (hc2D : c₂ ∈ D) (hL2D : L₂ ∈ D)
    (hd_lb : 9 ≤ D.card) (hd_ub : D.card ≤ 11) (htt : ¬TwoTwinConfig G)
    (hth : ¬TwoHubConfig G) (hsv : ¬SingleVertexConfig G)
    (hT : ¬∃ x y z : Fin 20, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 11)
    (hC4 : ¬∃ a b c d : Fin 20, ({a, b, c, d} : Finset (Fin 20)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (hK23 : ¬∃ a b c d e : Fin 20, ({a, b, c, d, e} : Finset (Fin 20)).card = 5 ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
      G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 19)
    (hDccard : Dᶜ.card = 20 - D.card) (_hIsocard : Iso.card = D.card - 4)
    (hc1hub : (G.neighborFinset c₁ ∩ Dᶜ).card = 1)
    (hc2hub : (G.neighborFinset c₂ ∩ Dᶜ).card = 1)
    (hL1hub : (G.neighborFinset L₁ ∩ Dᶜ).card = 2)
    (hL2hub : (G.neighborFinset L₂ ∩ Dᶜ).card = 2)
    (hsumPath : ∑ g ∈ Dᶜ, (G.neighborFinset g ∩ ({L₁, c₁, c₂, L₂} : Finset (Fin 20))).card = 6)
    (hsumIso : ∑ g ∈ Dᶜ, (G.neighborFinset g ∩ Iso).card = 3 * (D.card - 4))
    (hsumInternal : ∑ g ∈ Dᶜ, (G.neighborFinset g ∩ Dᶜ).card = 78 - 6 * D.card)
    (hper : ∀ g : Fin 20, g ∈ Dᶜ →
      (G.neighborFinset g ∩ ({L₁, c₁, c₂, L₂} : Finset (Fin 20))).card
        + (G.neighborFinset g ∩ Iso).card + (G.neighborFinset g ∩ Dᶜ).card = G.degree g)
    (hntri1 : ¬∃ a b c : Fin 20, a ∈ Dᶜ ∧ b ∈ Dᶜ ∧ c ∈ Dᶜ ∧
      G.Adj a b ∧ G.Adj a c ∧ G.Adj b c ∧
      (¬G.Adj a L₁ ∧ ¬G.Adj a c₁ ∧ ¬G.Adj a c₂) ∧
      (¬G.Adj b L₁ ∧ ¬G.Adj b c₁ ∧ ¬G.Adj b c₂) ∧
      (¬G.Adj c L₁ ∧ ¬G.Adj c c₁ ∧ ¬G.Adj c c₂) ∧
      G.degree a + G.degree b + G.degree c ≤ 13)
    (hntri2 : ¬∃ a b c : Fin 20, a ∈ Dᶜ ∧ b ∈ Dᶜ ∧ c ∈ Dᶜ ∧
      G.Adj a b ∧ G.Adj a c ∧ G.Adj b c ∧
      (¬G.Adj a c₁ ∧ ¬G.Adj a c₂ ∧ ¬G.Adj a L₂) ∧
      (¬G.Adj b c₁ ∧ ¬G.Adj b c₂ ∧ ¬G.Adj b L₂) ∧
      (¬G.Adj c c₁ ∧ ¬G.Adj c c₂ ∧ ¬G.Adj c L₂) ∧
      G.degree a + G.degree b + G.degree c ≤ 13)
    (hcase : D.card = 9 ∨ D.card = 10) :
    False := by
  classical
  set P : Finset (Fin 20) := {L₁, c₁, c₂, L₂} with hPdef
  -- Every hub has degree `≥ 4`.
  have hge4 : ∀ g : Fin 20, g ∈ Dᶜ → 4 ≤ G.degree g := by
    intro g hg
    have hgD : g ∉ D := Finset.mem_compl.mp hg
    have : G.degree g ≠ 3 := fun he => hgD ((hmemD g).mpr he)
    have := h3 g
    omega
  have hT10 : ¬∃ x y z : Fin 20, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10 := by
    rintro ⟨x, y, z, hxy, hyz, hxz, ha, hb, hc, hs⟩
    exact hT ⟨x, y, z, hxy, hyz, hxz, ha, hb, hc, by omega⟩
  -- Hub degree total `∑_{Dᶜ} deg = 72 − 3|D|`.
  have hsumdeg : ∑ g ∈ Dᶜ, G.degree g = 72 - 3 * D.card := by
    have hcong : ∑ g ∈ Dᶜ, ((G.neighborFinset g ∩ P).card
        + (G.neighborFinset g ∩ Iso).card + (G.neighborFinset g ∩ Dᶜ).card)
        = ∑ g ∈ Dᶜ, G.degree g := Finset.sum_congr rfl hper
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hsumPath, hsumIso, hsumInternal] at hcong
    omega
  -- The (W) fact for degree-`≤ 5` hubs.
  have hW := cherry_p4_W_facts_twenty G D Iso L₁ c₁ c₂ L₂ hIsoprop hL1deg hc1deg hc2deg hL2deg
    hac1L1 hc12 hac2L2 hL1nc2 hL2nc1 hL1D hc1D hc2D hL2D htt
  -- Classification of `D`.
  have hclassP : ∀ x : Fin 20, x ∈ D → x = L₁ ∨ x = c₁ ∨ x = c₂ ∨ x = L₂ ∨ x ∈ Iso := by
    intro x hx
    by_cases h1 : x = L₁
    · exact Or.inl h1
    by_cases h2 : x = c₁
    · exact Or.inr (Or.inl h2)
    by_cases h3' : x = c₂
    · exact Or.inr (Or.inr (Or.inl h3'))
    by_cases h4 : x = L₂
    · exact Or.inr (Or.inr (Or.inr (Or.inl h4)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (hisochar x hx h1 h2 h3' h4))))
  -- The two cherry-avoider sets and `FF`.
  set A1 := Dᶜ.filter (fun g => ¬G.Adj g L₁ ∧ ¬G.Adj g c₁ ∧ ¬G.Adj g c₂) with hA1def
  set A2 := Dᶜ.filter (fun g => ¬G.Adj g c₁ ∧ ¬G.Adj g c₂ ∧ ¬G.Adj g L₂) with hA2def
  set FF := A1 ∩ A2 with hFFdef
  have hA1sub : A1 ⊆ Dᶜ := by rw [hA1def]; exact Finset.filter_subset _ _
  have hA2sub : A2 ⊆ Dᶜ := by rw [hA2def]; exact Finset.filter_subset _ _
  have hFFsubA1 : FF ⊆ A1 := by rw [hFFdef]; exact Finset.inter_subset_left
  have hFFsubA2 : FF ⊆ A2 := by rw [hFFdef]; exact Finset.inter_subset_right
  have hFFsub : FF ⊆ Dᶜ := hFFsubA1.trans hA1sub
  -- Avoider counts.
  have hA1card_lb : Dᶜ.card - 4 ≤ A1.card := by
    have := avoiders_ge_gen G D L₁ c₁ c₂ (by rw [hL1hub, hc1hub, hc2hub])
    rwa [← hA1def] at this
  have hA2card_lb : Dᶜ.card - 4 ≤ A2.card := by
    have := avoiders_ge_gen G D c₁ c₂ L₂ (by rw [hc1hub, hc2hub, hL2hub])
    rwa [← hA2def] at this
  -- `hclass` packagers for the internal-degree lemmas.
  have hclassA1 : ∀ g : Fin 20, g ∈ A1 → ∀ x : Fin 20, G.Adj g x → x ∈ D → x = L₂ ∨ x ∈ Iso := by
    intro g hg x hadj hxD
    rw [hA1def, Finset.mem_filter] at hg
    obtain ⟨_, hgL1, hgc1, hgc2⟩ := hg
    rcases hclassP x hxD with h | h | h | h | h
    · exact absurd (h ▸ hadj) hgL1
    · exact absurd (h ▸ hadj) hgc1
    · exact absurd (h ▸ hadj) hgc2
    · exact Or.inl h
    · exact Or.inr h
  have hclassA2 : ∀ g : Fin 20, g ∈ A2 → ∀ x : Fin 20, G.Adj g x → x ∈ D → x = L₁ ∨ x ∈ Iso := by
    intro g hg x hadj hxD
    rw [hA2def, Finset.mem_filter] at hg
    obtain ⟨_, hgc1, hgc2, hgL2⟩ := hg
    rcases hclassP x hxD with h | h | h | h | h
    · exact Or.inl h
    · exact absurd (h ▸ hadj) hgc1
    · exact absurd (h ▸ hadj) hgc2
    · exact absurd (h ▸ hadj) hgL2
    · exact Or.inr h
  have hclassFF : ∀ g : Fin 20, g ∈ FF → ∀ x : Fin 20, G.Adj g x → x ∈ D → x ∈ Iso := by
    intro g hg x hadj hxD
    have hgA1 := hFFsubA1 hg
    have hgA2 := hFFsubA2 hg
    rw [hA1def, Finset.mem_filter] at hgA1
    rw [hA2def, Finset.mem_filter] at hgA2
    obtain ⟨_, hgL1, hgc1, hgc2⟩ := hgA1
    obtain ⟨_, _, _, hgL2⟩ := hgA2
    rcases hclassP x hxD with h | h | h | h | h
    · exact absurd (h ▸ hadj) hgL1
    · exact absurd (h ▸ hadj) hgc1
    · exact absurd (h ▸ hadj) hgc2
    · exact absurd (h ▸ hadj) hgL2
    · exact h
  -- Membership extractors into the avoider predicates.
  have getA2pred : ∀ g : Fin 20, g ∈ A2 →
      ¬G.Adj g c₁ ∧ ¬G.Adj g c₂ ∧ ¬G.Adj g L₂ := by
    intro g hg; rw [hA2def, Finset.mem_filter] at hg; exact hg.2
  have getA1pred : ∀ g : Fin 20, g ∈ A1 →
      ¬G.Adj g L₁ ∧ ¬G.Adj g c₁ ∧ ¬G.Adj g c₂ := by
    intro g hg; rw [hA1def, Finset.mem_filter] at hg; exact hg.2
  -- Cherry non-adjacencies (`L₁ ≠ L₂` plus the cross non-edges).
  have hL1L2 : L₁ ≠ L₂ := by
    intro he
    exact hT10 ⟨c₁, c₂, L₁, G.ne_of_adj hc12, he.symm ▸ G.ne_of_adj hac2L2,
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
  have hnc2L1 : ¬G.Adj c₂ L₁ := by
    intro hadj
    have hmem : L₁ ∈ G.neighborFinset c₂ ∩ D :=
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset c₂ L₁).mpr hadj, hL1D⟩
    rw [hNc2D] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h
    · exact (G.ne_of_adj hac1L1) h.symm
    · exact hL1L2 h
  have hIsoD : Iso ⊆ D := fun v hv => (hmemD v).mpr (hIsoprop v hv).1
  -- `¬ G.Adj L₁ L₂`: `L₁`'s unique `D`-neighbour is `c₁`, and `L₂ ≠ c₁`.
  have hnL1L2 : ¬G.Adj L₁ L₂ := by
    intro hadj
    have hmem : L₂ ∈ G.neighborFinset L₁ ∩ D :=
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset L₁ L₂).mpr hadj, hL2D⟩
    have hc1mem : c₁ ∈ G.neighborFinset L₁ ∩ D :=
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset L₁ c₁).mpr hac1L1.symm, hc1D⟩
    have hdisjDc : Disjoint (G.neighborFinset L₁ ∩ D) (G.neighborFinset L₁ ∩ Dᶜ) := by
      apply Finset.disjoint_left.mpr; intro a ha hb
      exact (Finset.mem_compl.mp (Finset.mem_inter.mp hb).2) (Finset.mem_inter.mp ha).2
    have hunionDc : (G.neighborFinset L₁ ∩ D) ∪ (G.neighborFinset L₁ ∩ Dᶜ)
        = G.neighborFinset L₁ := by
      rw [← Finset.inter_union_distrib_left, Finset.union_compl, Finset.inter_univ]
    have hsplit : (G.neighborFinset L₁ ∩ D).card + (G.neighborFinset L₁ ∩ Dᶜ).card
        = G.degree L₁ := by
      rw [← Finset.card_union_of_disjoint hdisjDc, hunionDc, G.card_neighborFinset_eq_degree]
    rw [hL1deg, hL1hub] at hsplit
    have hone : (G.neighborFinset L₁ ∩ D).card = 1 := by omega
    have hsub : ({c₁, L₂} : Finset (Fin 20)) ⊆ G.neighborFinset L₁ ∩ D := by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hc1mem
      · exact hmem
    have hcard2 : ({c₁, L₂} : Finset (Fin 20)).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simp [Ne.symm hL2nc1]), Finset.card_singleton]
    have := Finset.card_le_card hsub
    rw [hcard2, hone] at this; omega
  -- Dispatch on `|D|` (`hcase`).
  rcases hcase with hD9 | hD10
  · -- **`|D| = 9`** (`11` hubs, `∑ int = 24`, `∑ deg = 45 = 5 + 10·4`, one degree-`5` hub).
    have hDc11 : Dᶜ.card = 11 := by rw [hDccard, hD9]
    have hint24 : ∑ g ∈ Dᶜ, (G.neighborFinset g ∩ Dᶜ).card = 24 := by rw [hsumInternal, hD9]
    have hdeg45 : ∑ g ∈ Dᶜ, G.degree g = 45 := by rw [hsumdeg, hD9]
    have hdeg5 : ∀ g : Fin 20, g ∈ Dᶜ → G.degree g ≤ 5 := by
      intro g hg
      have := hub_deg_upper_pt Dᶜ (fun v => G.degree v) 45 hge4 hdeg45 g hg
      rw [hDc11] at this; omega
    have hsumIso15 : ∑ h ∈ Dᶜ, (G.neighborFinset h ∩ Iso).card = 15 := by rw [hsumIso, hD9]
    -- Exactly one degree-`5` hub in `Dᶜ` (since `∑ deg = 45 = 5 + 10·4`).
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
          + (Dᶜ.filter (fun g => ¬ G.degree g = 5)).card = 11 := by
        rw [Finset.card_filter_add_card_filter_not]; exact hDc11
      rw [hdeg45] at hpart; omega
    -- The unique degree-`5` hub `h₅`.
    obtain ⟨h₅, hf5⟩ := Finset.card_eq_one.mp hdeg5count
    have hh5mem : h₅ ∈ Dᶜ.filter (fun g => G.degree g = 5) := by
      rw [hf5]; exact Finset.mem_singleton_self h₅
    obtain ⟨hh5Dc, hh5d⟩ := Finset.mem_filter.mp hh5mem
    have h5uniq : ∀ h : Fin 20, h ∈ Dᶜ → G.degree h = 5 → h = h₅ := by
      intro h hhDc h5'
      have hm : h ∈ Dᶜ.filter (fun g => G.degree g = 5) := Finset.mem_filter.mpr ⟨hhDc, h5'⟩
      rw [hf5, Finset.mem_singleton] at hm; exact hm
    have hdegOth5 : ∀ h : Fin 20, h ∈ Dᶜ → h ≠ h₅ → G.degree h = 4 := by
      intro h hhDc hh5
      have h4 := hge4 h hhDc; have h5 := hdeg5 h hhDc
      rcases (by omega : G.degree h = 4 ∨ G.degree h = 5) with h4' | h5'
      · exact h4'
      · exact absurd (h5uniq h hhDc h5') hh5
    -- The internally-isolated degree-`4` hubs.
    set ID4 := Dᶜ.filter (fun g => G.degree g = 4 ∧ (G.neighborFinset g ∩ Dᶜ).card = 0)
      with hID4def
    have hID4prop : ∀ g ∈ ID4, g ∈ Dᶜ ∧ G.neighborFinset g ∩ Dᶜ = ∅ ∧ G.degree g = 4 := by
      intro g hg
      rw [hID4def, Finset.mem_filter] at hg
      exact ⟨hg.1, Finset.card_eq_zero.mp hg.2.2, hg.2.1⟩
    by_cases hID4ge2 : 2 ≤ ID4.card
    · -- **ISO2** (`≥ 2` isolated degree-`4` hubs) — the `n = 19` pair machinery ports verbatim.
      obtain ⟨h₁, hh1ID4, h₂, hh2ID4, hne12⟩ := Finset.one_lt_card.mp hID4ge2
      obtain ⟨hh1Dc, hh10, hh1d⟩ := hID4prop h₁ hh1ID4
      obtain ⟨hh2Dc, hh20, hh2d⟩ := hID4prop h₂ hh2ID4
      have hrich := isolated_pair_iso_rich_twenty G D Iso L₁ c₁ c₂ L₂ h₁ h₂ hT10 hC4 hclassP
        hIsoprop hac1L1 hc12 hac2L2 hnc1L2 hnc2L1 hL1nc2 hL2nc1 hL1deg hc1deg hc2deg hL2deg
        hh2Dc hh1d hh2d hh10 hh20 hne12 hnL1L2
      rcases hrich with hrich | hrich
      · exact hth (two_isolated_hub_twohubconfig_d9_ff4 G D Iso L₁ c₁ c₂ L₂ h₁ h₂ hC4 hmemD hIsoD
          hclassP hIsoprop hac1L1 hc12 hac2L2 hc1deg hc2deg hh1Dc hh2Dc hh1d hh2d hh10 hh20
          hne12 hrich)
      · exact hth (two_isolated_hub_twohubconfig_d9_ff4 G D Iso L₁ c₁ c₂ L₂ h₂ h₁ hC4 hmemD hIsoD
          hclassP hIsoprop hac1L1 hc12 hac2L2 hc1deg hc2deg hh2Dc hh1Dc hh2d hh1d hh20 hh10
          hne12.symm hrich)
    · by_cases hID4eq0 : ID4.card = 0
      · -- **`ID4 = 0`** (no internally-isolated degree-`4` hub): the anchor-tie kill.
        have hID40 : ∀ h : Fin 20, h ∈ Dᶜ → G.degree h = 4 →
            (G.neighborFinset h ∩ Dᶜ).card ≠ 0 := by
          intro h hhDc hhd hint0
          have hmem : h ∈ ID4 := by rw [hID4def, Finset.mem_filter]; exact ⟨hhDc, hhd, hint0⟩
          have hempty : ID4 = ∅ := Finset.card_eq_zero.mp hID4eq0
          rw [hempty] at hmem; exact absurd hmem (Finset.notMem_empty h)
        exact iso1_id40_anchor_tie_eleven G D Iso L₁ c₁ c₂ L₂ h₅ hmemD hIsoprop hclassP
          hL1deg hc1deg hc2deg hL2deg hac1L1 hc12 hac2L2 hL1nc2 hL2nc1 hNc1D hNc2D
          hL1D hc1D hc2D hL2D htt hth hsv hT hC4 hDc11 (by rw [_hIsocard, hD9]) hdeg5 hper
          hsumPath hsumIso15 hc1hub hc2hub hL1hub hL2hub hID40 hh5Dc hh5d hdegOth5 hint24 hntri1
      · -- **`ID4 = 1`** (a unique isolated degree-`4` hub `h₁`): the `cinc`/`h₅`-isolation dispatch.
        have hID4eq1 : ID4.card = 1 := by omega
        obtain ⟨h₁, hID4_h1⟩ := Finset.card_eq_one.mp hID4eq1
        have hh1ID4 : h₁ ∈ ID4 := by rw [hID4_h1]; exact Finset.mem_singleton_self h₁
        obtain ⟨hh1Dc, hh1iso, hh1d⟩ := hID4prop h₁ hh1ID4
        have hne15 : h₁ ≠ h₅ :=
          fun he => by rw [he, hh5d] at hh1d; exact absurd hh1d (by norm_num)
        have hdegOth : ∀ h : Fin 20, h ∈ Dᶜ → h ≠ h₁ → h ≠ h₅ → G.degree h = 4 :=
          fun h hhDc _ hh5 => hdegOth5 h hhDc hh5
        have hID4u : ∀ h : Fin 20, h ∈ Dᶜ → G.degree h = 4 → h ≠ h₁ →
            (G.neighborFinset h ∩ Dᶜ).card ≠ 0 := by
          intro h hhDc hhd hh1 hint0
          have hmem : h ∈ ID4 := by rw [hID4def, Finset.mem_filter]; exact ⟨hhDc, hhd, hint0⟩
          rw [hID4_h1, Finset.mem_singleton] at hmem; exact hh1 hmem
        have hc1nIso : c₁ ∉ Iso := fun h => (hIsoprop c₁ h).2 L₁ hac1L1 hL1deg
        have hc2nIso : c₂ ∉ Iso := fun h => (hIsoprop c₂ h).2 c₁ hc12.symm hc1deg
        have hL1nIso : L₁ ∉ Iso := fun h => (hIsoprop L₁ h).2 c₁ hac1L1.symm hc1deg
        have hL2nIso : L₂ ∉ Iso := fun h => (hIsoprop L₂ h).2 c₂ hac2L2.symm hc2deg
        have hh1nc1 : h₁ ≠ c₁ :=
          fun he => by rw [he, hc1deg] at hh1d; exact absurd hh1d (by norm_num)
        have hh1nc2 : h₁ ≠ c₂ :=
          fun he => by rw [he, hc2deg] at hh1d; exact absurd hh1d (by norm_num)
        have hh1nL1 : h₁ ≠ L₁ :=
          fun he => by rw [he, hL1deg] at hh1d; exact absurd hh1d (by norm_num)
        have hh1nL2 : h₁ ≠ L₂ :=
          fun he => by rw [he, hL2deg] at hh1d; exact absurd hh1d (by norm_num)
        by_cases hcinc2 : 2 ≤ (G.neighborFinset h₁ ∩ P).card
        · -- `cinc h₁ ≥ 2`: split on the internal isolation of `h₅`.
          by_cases h5o : G.neighborFinset h₅ ∩ Dᶜ = ∅
          · exact iso1_cinc2_h5closed_eleven G D Iso L₁ c₁ c₂ L₂ h₁ h₅ hmemD hIsoprop hclassP
              hL1deg hc1deg hc2deg hL2deg hac1L1 hc12 hac2L2 hL1nc2 hL2nc1 hNc1D hNc2D
              hL1D hc1D hc2D hL2D htt hth hsv hT hC4 hDc11 (by rw [_hIsocard, hD9]) hdeg5 hper
              hsumPath hsumIso15 hc1hub hc2hub hL1hub hL2hub hh1Dc hh1d hh1iso hcinc2 hh5Dc hh5d
              h5o hne15 hID4u hdegOth hntri1
          · have hdeg5int : 1 ≤ (G.neighborFinset h₅ ∩ Dᶜ).card := by
              rw [Nat.one_le_iff_ne_zero]
              exact fun hz => h5o (Finset.card_eq_zero.mp hz)
            exact iso1_dichotomy_to_false G D Iso L₁ c₁ c₂ L₂ h₁ h₅ hmemD hIsoD hIsoprop hclassP
              hL1deg hc1deg hc2deg hL2deg hac1L1 hc12 hac2L2 hL1nc2 hL2nc1 hNc1D hNc2D
              hL1D hc1D hc2D hL2D htt hth hT hC4 hDc11 hdeg5 hper hsumIso15 hh1Dc hh1d hh1iso
              hcinc2 hh5Dc hh5d hne15 hdeg5int hdegOth
        · -- `cinc h₁ ≤ 1`.
          have hcinc1 :
              (G.neighborFinset h₁ ∩ ({L₁, c₁, c₂, L₂} : Finset (Fin 20))).card ≤ 1 := by
            rw [← hPdef]; omega
          have hh1int0 : (G.neighborFinset h₁ ∩ Dᶜ).card = 0 := by
            rw [hh1iso]; exact Finset.card_empty
          have hisoge2 : 2 ≤ (G.neighborFinset h₁ ∩ Iso).card := by
            have hdec1 := hper h₁ hh1Dc
            rw [hh1int0, hh1d] at hdec1
            omega
          by_cases hRc1 : G.Adj h₁ c₁
          · by_cases h5o : G.neighborFinset h₅ ∩ Dᶜ = ∅
            · exact iso1_hard_c_subcase_eleven G D Iso L₁ c₁ c₂ L₂ h₁ h₅ hmemD hIsoprop hclassP
                hL1deg hc1deg hc2deg hL2deg hac1L1 hc12 hac2L2 hL1nc2 hL2nc1 hNc1D hNc2D
                hL1D hc1D hc2D hL2D htt hth hsv hT hC4 hDc11 (by rw [_hIsocard, hD9]) hdeg5 hper
                hsumPath hsumIso15 hc1hub hc2hub hL1hub hL2hub hh1Dc hh1d hh1iso hRc1 hcinc1
                hh5Dc hh5d h5o hne15 hdegOth hntri1
            · have hdeg5int : 1 ≤ (G.neighborFinset h₅ ∩ Dᶜ).card := by
                rw [Nat.one_le_iff_ne_zero]
                exact fun hz => h5o (Finset.card_eq_zero.mp hz)
              exact iso1_hardc0_h5open_eleven G D Iso L₁ c₁ c₂ L₂ h₁ h₅ hmemD hIsoprop hclassP
                hL1deg hc1deg hc2deg hL2deg hac1L1 hc12 hac2L2 hL1nc2 hL2nc1 hNc1D hNc2D
                hL1D hc1D hc2D hL2D htt hth hsv hT hC4 hDc11 (by rw [_hIsocard, hD9]) hdeg5 hper
                hsumPath hsumIso15 hc1hub hc2hub hL1hub hL2hub hh1Dc hh1d hh1iso hRc1 hcinc1
                hh5Dc hh5d hdeg5int hne15 hdegOth hntri1
          by_cases hRc2 : G.Adj h₁ c₂
          · -- `h₁` meets `c₂`: reflect `(L₁,c₁,c₂,L₂) ↦ (L₂,c₂,c₁,L₁)`.
            have hPeq : ({L₂, c₂, c₁, L₁} : Finset (Fin 20)) = {L₁, c₁, c₂, L₂} := by
              ext x
              simp only [Finset.mem_insert, Finset.mem_singleton]
              constructor <;> rintro (rfl | rfl | rfl | rfl) <;> simp
            have hclassP' : ∀ x : Fin 20, x ∈ D → x = L₂ ∨ x = c₂ ∨ x = c₁ ∨ x = L₁ ∨ x ∈ Iso := by
              intro x hx; rcases hclassP x hx with h | h | h | h | h <;> simp [h]
            have hper' : ∀ h : Fin 20, h ∈ Dᶜ →
                (G.neighborFinset h ∩ ({L₂, c₂, c₁, L₁} : Finset (Fin 20))).card
                  + (G.neighborFinset h ∩ Iso).card + (G.neighborFinset h ∩ Dᶜ).card
                    = G.degree h := by
              intro h hh; rw [hPeq]; exact hper h hh
            have hsumPath' : ∑ g ∈ Dᶜ,
                (G.neighborFinset g ∩ ({L₂, c₂, c₁, L₁} : Finset (Fin 20))).card = 6 := by
              rw [Finset.sum_congr rfl (fun g _ => by rw [hPeq])]; exact hsumPath
            have hntri1' : ¬∃ a b c : Fin 20, a ∈ Dᶜ ∧ b ∈ Dᶜ ∧ c ∈ Dᶜ ∧
                G.Adj a b ∧ G.Adj a c ∧ G.Adj b c ∧
                (¬G.Adj a L₂ ∧ ¬G.Adj a c₂ ∧ ¬G.Adj a c₁) ∧
                (¬G.Adj b L₂ ∧ ¬G.Adj b c₂ ∧ ¬G.Adj b c₁) ∧
                (¬G.Adj c L₂ ∧ ¬G.Adj c c₂ ∧ ¬G.Adj c c₁) ∧
                G.degree a + G.degree b + G.degree c ≤ 13 := by
              rintro ⟨a, b, c, haD, hbD, hcD, hab, hac, hbc,
                ⟨haL2, hac2, hac1⟩, ⟨hbL2, hbc2, hbc1⟩, ⟨hcL2, hcc2, hcc1⟩, hdeg⟩
              exact hntri2 ⟨a, b, c, haD, hbD, hcD, hab, hac, hbc,
                ⟨hac1, hac2, haL2⟩, ⟨hbc1, hbc2, hbL2⟩, ⟨hcc1, hcc2, hcL2⟩, hdeg⟩
            have hcinc1' :
                (G.neighborFinset h₁ ∩ ({L₂, c₂, c₁, L₁} : Finset (Fin 20))).card ≤ 1 := by
              rw [hPeq, ← hPdef]; omega
            by_cases h5o : G.neighborFinset h₅ ∩ Dᶜ = ∅
            · exact iso1_hard_c_subcase_eleven G D Iso L₂ c₂ c₁ L₁ h₁ h₅ hmemD hIsoprop hclassP'
                hL2deg hc2deg hc1deg hL1deg hac2L2 hc12.symm hac1L1 hL2nc1 hL1nc2 hNc2D hNc1D
                hL2D hc2D hc1D hL1D htt hth hsv hT hC4 hDc11 (by rw [_hIsocard, hD9]) hdeg5 hper'
                hsumPath' hsumIso15 hc2hub hc1hub hL2hub hL1hub hh1Dc hh1d hh1iso hRc2 hcinc1'
                hh5Dc hh5d h5o hne15 hdegOth hntri1'
            · have hdeg5int : 1 ≤ (G.neighborFinset h₅ ∩ Dᶜ).card := by
                rw [Nat.one_le_iff_ne_zero]
                exact fun hz => h5o (Finset.card_eq_zero.mp hz)
              exact iso1_hardc0_h5open_eleven G D Iso L₂ c₂ c₁ L₁ h₁ h₅ hmemD hIsoprop hclassP'
                hL2deg hc2deg hc1deg hL1deg hac2L2 hc12.symm hac1L1 hL2nc1 hL1nc2 hNc2D hNc1D
                hL2D hc2D hc1D hL1D htt hth hsv hT hC4 hDc11 (by rw [_hIsocard, hD9]) hdeg5 hper'
                hsumPath' hsumIso15 hc2hub hc1hub hL2hub hL1hub hh1Dc hh1d hh1iso hRc2 hcinc1'
                hh5Dc hh5d hdeg5int hne15 hdegOth hntri1'
          by_cases hRL2 : G.Adj h₁ L₂
          · -- lone cherry-neighbour is `L₂`; `h₁` avoids the cherry `P₃` `L₁–c₁–c₂`.
            have hnL1 : ¬G.Adj h₁ L₁ := by
              intro hL1a
              have hsub : ({L₁, L₂} : Finset (Fin 20)) ⊆ G.neighborFinset h₁ ∩ P := by
                intro w hw
                simp only [Finset.mem_insert, Finset.mem_singleton] at hw
                rcases hw with rfl | rfl
                · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hL1a, by simp [hPdef]⟩
                · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hRL2, by simp [hPdef]⟩
              have hcard : ({L₁, L₂} : Finset (Fin 20)).card = 2 := by
                rw [Finset.card_insert_of_notMem (by simp [hL1L2]), Finset.card_singleton]
              have := Finset.card_le_card hsub; omega
            exact absurd (twotwin_of_centre_twenty G Iso h₁ L₁ c₁ c₂ hIsoprop hL1deg hc1deg hc2deg
              (by omega) hac1L1.symm hc12 hnL1 hRc1 hRc2 hL1nIso hc1nIso hc2nIso
              hh1nL1 hh1nc1 hh1nc2 (G.ne_of_adj hac1L1).symm (G.ne_of_adj hc12) hL1nc2 hisoge2) htt
          · -- `h₁` avoids all of `c₁, c₂, L₂`: `TwoTwinConfig` centre with cherry `P₃` `c₁–c₂–L₂`.
            exact absurd (twotwin_of_centre_twenty G Iso h₁ c₁ c₂ L₂ hIsoprop hc1deg hc2deg hL2deg
              (by omega) hc12 hac2L2 hRc1 hRc2 hRL2 hc1nIso hc2nIso hL2nIso
              hh1nc1 hh1nc2 hh1nL2 (G.ne_of_adj hc12) (G.ne_of_adj hac2L2) hL2nc1.symm hisoge2) htt
  · -- **`|D| = 10`** (`10` hubs, `∑ int = 18`, `∑ deg = 42`, avoiders `≥ 6`).
    have hDc10 : Dᶜ.card = 10 := by rw [hDccard, hD10]
    have hint18 : ∑ g ∈ Dᶜ, (G.neighborFinset g ∩ Dᶜ).card = 18 := by rw [hsumInternal, hD10]
    have hdeg42 : ∑ g ∈ Dᶜ, G.degree g = 42 := by rw [hsumdeg, hD10]
    have hA1c6 : 6 ≤ A1.card := by rw [hDc10] at hA1card_lb; omega
    have hA2c6 : 6 ≤ A2.card := by rw [hDc10] at hA2card_lb; omega
    have hind1 : ¬G.Adj L₁ c₂ := fun h => hnc2L1 h.symm
    by_cases hex6 : ∃ h6 : Fin 20, h6 ∈ Dᶜ ∧ 6 ≤ G.degree h6
    · -- **deg-`6` exceptional.**  `42 = 6 + 9·4` pins every other hub to degree `4`.  If the
      -- degree-`6` hub `h₆` has `≥ 4` `M`-isolated twins, the isofour handler closes; else
      -- `isoinc h₆ ≤ 3` gives the avoider internal bounds and `d10_exc_force_twenty` closes.
      obtain ⟨h6, hh6Dc, hh6deg⟩ := hex6
      have hd6 : G.degree h6 = 6 := by
        have hsplit : G.degree h6 + ∑ x ∈ Dᶜ.erase h6, G.degree x = 42 := by
          have h := Finset.add_sum_erase Dᶜ (fun v => G.degree v) hh6Dc
          rw [hdeg42] at h; exact h
        have hcard9 : (Dᶜ.erase h6).card = 9 := by rw [Finset.card_erase_of_mem hh6Dc, hDc10]
        have hlb : 4 * (Dᶜ.erase h6).card ≤ ∑ x ∈ Dᶜ.erase h6, G.degree x := by
          have := Finset.card_nsmul_le_sum (Dᶜ.erase h6) (fun v => G.degree v) 4
            (fun x hx => hge4 x (Finset.mem_of_mem_erase hx))
          simpa [smul_eq_mul, Nat.mul_comm] using this
        rw [hcard9] at hlb; omega
      have hother4 : ∀ g : Fin 20, g ∈ Dᶜ → g ≠ h6 → G.degree g = 4 := by
        intro g hg hgne
        have hpair_sub : ({h6, g} : Finset (Fin 20)) ⊆ Dᶜ := by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact hh6Dc
          · exact hg
        have hpair_card : ({h6, g} : Finset (Fin 20)).card = 2 := by
          rw [Finset.card_insert_of_notMem (by simp [Ne.symm hgne]), Finset.card_singleton]
        have hsplit : (∑ x ∈ Dᶜ \ ({h6, g} : Finset (Fin 20)), G.degree x)
            + ∑ x ∈ ({h6, g} : Finset (Fin 20)), G.degree x = ∑ x ∈ Dᶜ, G.degree x :=
          Finset.sum_sdiff hpair_sub
        have hpair_sum : ∑ x ∈ ({h6, g} : Finset (Fin 20)), G.degree x
            = G.degree h6 + G.degree g := by
          rw [Finset.sum_insert (by simp [Ne.symm hgne]), Finset.sum_singleton]
        have hrest_card : (Dᶜ \ ({h6, g} : Finset (Fin 20))).card = 8 := by
          rw [Finset.card_sdiff_of_subset hpair_sub, hDc10, hpair_card]
        have hrest_lb : 4 * (Dᶜ \ ({h6, g} : Finset (Fin 20))).card
            ≤ ∑ x ∈ Dᶜ \ ({h6, g} : Finset (Fin 20)), G.degree x := by
          have := Finset.card_nsmul_le_sum (Dᶜ \ ({h6, g} : Finset (Fin 20)))
            (fun x => G.degree x) 4 (fun x hx => hge4 x (Finset.mem_sdiff.mp hx).1)
          simpa [smul_eq_mul, Nat.mul_comm] using this
        have hgge := hge4 g hg
        rw [hdeg42, hpair_sum, hd6] at hsplit
        omega
      by_cases hiso4 : 4 ≤ (G.neighborFinset h6 ∩ Iso).card
      · -- `h₆` has `≥ 4` `M`-isolated twins: the isofour handler closes.
        exact d10_deg6_isofour_handler_twenty G D Iso L₁ c₁ c₂ L₂ h6 hmemD hIsoD hIsoprop hclassP
          hL1deg hc1deg hc2deg hL2deg hac1L1 hc12 hac2L2 hL1nc2 hL2nc1 hNc1D hNc2D hL1D hc1D hc2D
          hL2D htt hth hsv hT hC4 hK23 hDc10 (by rw [_hIsocard, hD10]) hper hsumPath
          (by rw [hsumIso, hD10]) hc1hub hc2hub hL1hub hL2hub hh6Dc hd6 hiso4 hother4
      · -- `isoinc h₆ ≤ 3`: the avoider internal bounds hold at `h₆`, so the saturation kill closes.
        have hisoLe3 : (G.neighborFinset h6 ∩ Iso).card ≤ 3 := by omega
        have hA1int : ∀ g ∈ A1, 2 ≤ (G.neighborFinset g ∩ Dᶜ).card := by
          intro g hg
          by_cases hgh6 : g = h6
          · rw [hgh6] at hg ⊢
            obtain ⟨hnL1, hnc1, hnc2⟩ := getA1pred h6 hg
            have hcincLe1 : (G.neighborFinset h6 ∩ P).card ≤ 1 := by
              have hsub : G.neighborFinset h6 ∩ P ⊆ {L₂} := by
                intro x hx
                simp only [hPdef, Finset.mem_inter, G.mem_neighborFinset, Finset.mem_insert,
                  Finset.mem_singleton] at hx
                obtain ⟨hxN, hxP⟩ := hx
                rcases hxP with rfl | rfl | rfl | rfl
                · exact absurd hxN hnL1
                · exact absurd hxN hnc1
                · exact absurd hxN hnc2
                · exact Finset.mem_singleton_self _
              calc (G.neighborFinset h6 ∩ P).card ≤ ({L₂} : Finset (Fin 20)).card :=
                    Finset.card_le_card hsub
                _ = 1 := Finset.card_singleton _
            have hdec := hper h6 (hA1sub hg)
            rw [hd6] at hdec
            omega
          · have hgd : G.degree g = 4 := hother4 g (hA1sub hg) hgh6
            exact avoider_internal_ge_two_pt G D Iso g L₂ (hge4 g (hA1sub hg))
              (hW g (hA1sub hg) (by omega) (Or.inl (getA1pred g hg))) (hclassA1 g hg)
        have hA2int : ∀ g ∈ A2, 2 ≤ (G.neighborFinset g ∩ Dᶜ).card := by
          intro g hg
          by_cases hgh6 : g = h6
          · rw [hgh6] at hg ⊢
            obtain ⟨hnc1, hnc2, hnL2⟩ := getA2pred h6 hg
            have hcincLe1 : (G.neighborFinset h6 ∩ P).card ≤ 1 := by
              have hsub : G.neighborFinset h6 ∩ P ⊆ {L₁} := by
                intro x hx
                simp only [hPdef, Finset.mem_inter, G.mem_neighborFinset, Finset.mem_insert,
                  Finset.mem_singleton] at hx
                obtain ⟨hxN, hxP⟩ := hx
                rcases hxP with rfl | rfl | rfl | rfl
                · exact Finset.mem_singleton_self _
                · exact absurd hxN hnc1
                · exact absurd hxN hnc2
                · exact absurd hxN hnL2
              calc (G.neighborFinset h6 ∩ P).card ≤ ({L₁} : Finset (Fin 20)).card :=
                    Finset.card_le_card hsub
                _ = 1 := Finset.card_singleton _
            have hdec := hper h6 (hA2sub hg)
            rw [hd6] at hdec
            omega
          · have hgd : G.degree g = 4 := hother4 g (hA2sub hg) hgh6
            exact avoider_internal_ge_two_pt G D Iso g L₁ (hge4 g (hA2sub hg))
              (hW g (hA2sub hg) (by omega) (Or.inr (getA2pred g hg))) (hclassA2 g hg)
        have hFFint : ∀ g ∈ FF, 3 ≤ (G.neighborFinset g ∩ Dᶜ).card := by
          intro g hg
          by_cases hgh6 : g = h6
          · rw [hgh6] at hg ⊢
            obtain ⟨hnL1, hnc1, hnc2⟩ := getA1pred h6 (hFFsubA1 hg)
            obtain ⟨_, _, hnL2⟩ := getA2pred h6 (hFFsubA2 hg)
            have hcinc0 : (G.neighborFinset h6 ∩ P).card = 0 := by
              rw [Finset.card_eq_zero]
              apply Finset.eq_empty_of_forall_notMem
              intro x hx
              simp only [hPdef, Finset.mem_inter, G.mem_neighborFinset, Finset.mem_insert,
                Finset.mem_singleton] at hx
              obtain ⟨hxN, hxP⟩ := hx
              rcases hxP with rfl | rfl | rfl | rfl
              · exact hnL1 hxN
              · exact hnc1 hxN
              · exact hnc2 hxN
              · exact hnL2 hxN
            have hdec := hper h6 (hFFsub hg)
            rw [hd6] at hdec
            omega
          · have hgd : G.degree g = 4 := hother4 g (hFFsub hg) hgh6
            exact fully_free_internal_ge_three_pt G D Iso g (hge4 g (hFFsub hg))
              (hW g (hFFsub hg) (by omega) (Or.inl (getA1pred g (hFFsubA1 hg)))) (hclassFF g hg)
        exact d10_exc_force_twenty G D Iso L₁ c₁ c₂ L₂ hT10 hC4 hmemD hIsoD hIsoprop hclassP
          hL1deg hc1deg hc2deg hL2deg hac1L1.symm hc12 hac2L2 hind1 hnL1L2 hnc1L2
          hDc10 hint18 hge4 hdeg42 h6 hh6Dc hd6 hA1c6 hA2c6 hA1int hA2int hFFint hth
    · -- **all hubs of degree `≤ 5`** — the saturation kill `d10_clean_force_twenty` closes.
      push Not at hex6
      have hdeg5 : ∀ g : Fin 20, g ∈ Dᶜ → G.degree g ≤ 5 :=
        fun g hg => by have := hex6 g hg; omega
      have hA1int : ∀ g ∈ A1, 2 ≤ (G.neighborFinset g ∩ Dᶜ).card := by
        intro g hg
        exact avoider_internal_ge_two_pt G D Iso g L₂ (hge4 g (hA1sub hg))
          (hW g (hA1sub hg) (hdeg5 g (hA1sub hg)) (Or.inl (getA1pred g hg))) (hclassA1 g hg)
      have hA2int : ∀ g ∈ A2, 2 ≤ (G.neighborFinset g ∩ Dᶜ).card := by
        intro g hg
        exact avoider_internal_ge_two_pt G D Iso g L₁ (hge4 g (hA2sub hg))
          (hW g (hA2sub hg) (hdeg5 g (hA2sub hg)) (Or.inr (getA2pred g hg))) (hclassA2 g hg)
      have hFFint : ∀ g ∈ FF, 3 ≤ (G.neighborFinset g ∩ Dᶜ).card := by
        intro g hg
        exact fully_free_internal_ge_three_pt G D Iso g (hge4 g (hFFsub hg))
          (hW g (hFFsub hg) (hdeg5 g (hFFsub hg))
            (Or.inl (getA1pred g (hFFsubA1 hg)))) (hclassFF g hg)
      exact d10_clean_force_twenty G D Iso L₁ c₁ c₂ L₂ hT10 hC4 hmemD hIsoD hIsoprop hclassP
        hL1deg hc1deg hc2deg hL2deg hac1L1.symm hc12 hac2L2 hind1 hnL1L2 hnc1L2
        hDc10 hint18 hge4 hdeg5 hdeg42 hA1c6 hA2c6 hA1int hA2int hFFint hth

set_option maxHeartbeats 1000000 in
/-- **No degree-`≤ 13` avoider triangle ⇒ contradiction (`n = 19`, `P₄`, `|D| ∈ {9, 10, 11}`).** -/
theorem iso_rich_force_p4_twenty (G : SimpleGraph (Fin 20))
    (D Iso : Finset (Fin 20)) (L₁ c₁ c₂ L₂ : Fin 20)
    (h3 : ∀ v : Fin 20, 3 ≤ G.degree v)
    (hmemD : ∀ v : Fin 20, v ∈ D ↔ G.degree v = 3)
    (hIsoprop : ∀ v ∈ Iso, G.degree v = 3 ∧ (∀ w : Fin 20, G.Adj v w → G.degree w ≠ 3))
    (hisochar : ∀ w : Fin 20, w ∈ D → w ≠ L₁ → w ≠ c₁ → w ≠ c₂ → w ≠ L₂ → w ∈ Iso)
    (hL1deg : G.degree L₁ = 3) (hc1deg : G.degree c₁ = 3)
    (hc2deg : G.degree c₂ = 3) (hL2deg : G.degree L₂ = 3)
    (hac1L1 : G.Adj c₁ L₁) (hc12 : G.Adj c₁ c₂) (hac2L2 : G.Adj c₂ L₂)
    (hL1nc2 : L₁ ≠ c₂) (hL2nc1 : L₂ ≠ c₁)
    (hNc1D : G.neighborFinset c₁ ∩ D = {c₂, L₁}) (hNc2D : G.neighborFinset c₂ ∩ D = {c₁, L₂})
    (hL1D : L₁ ∈ D) (hc1D : c₁ ∈ D) (hc2D : c₂ ∈ D) (hL2D : L₂ ∈ D)
    (hd_lb : 9 ≤ D.card) (hd_ub : D.card ≤ 11) (htt : ¬TwoTwinConfig G)
    (hth : ¬TwoHubConfig G) (hsv : ¬SingleVertexConfig G)
    (hT : ¬∃ x y z : Fin 20, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 11)
    (hC4 : ¬∃ a b c d : Fin 20, ({a, b, c, d} : Finset (Fin 20)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (hK23 : ¬∃ a b c d e : Fin 20, ({a, b, c, d, e} : Finset (Fin 20)).card = 5 ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
      G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 19)
    (hDccard : Dᶜ.card = 20 - D.card) (_hIsocard : Iso.card = D.card - 4)
    (hc1hub : (G.neighborFinset c₁ ∩ Dᶜ).card = 1)
    (hc2hub : (G.neighborFinset c₂ ∩ Dᶜ).card = 1)
    (hL1hub : (G.neighborFinset L₁ ∩ Dᶜ).card = 2)
    (hL2hub : (G.neighborFinset L₂ ∩ Dᶜ).card = 2)
    (hsumPath : ∑ g ∈ Dᶜ, (G.neighborFinset g ∩ ({L₁, c₁, c₂, L₂} : Finset (Fin 20))).card = 6)
    (hsumIso : ∑ g ∈ Dᶜ, (G.neighborFinset g ∩ Iso).card = 3 * (D.card - 4))
    (hsumInternal : ∑ g ∈ Dᶜ, (G.neighborFinset g ∩ Dᶜ).card = 78 - 6 * D.card)
    (hper : ∀ g : Fin 20, g ∈ Dᶜ →
      (G.neighborFinset g ∩ ({L₁, c₁, c₂, L₂} : Finset (Fin 20))).card
        + (G.neighborFinset g ∩ Iso).card + (G.neighborFinset g ∩ Dᶜ).card = G.degree g)
    (hntri1 : ¬∃ a b c : Fin 20, a ∈ Dᶜ ∧ b ∈ Dᶜ ∧ c ∈ Dᶜ ∧
      G.Adj a b ∧ G.Adj a c ∧ G.Adj b c ∧
      (¬G.Adj a L₁ ∧ ¬G.Adj a c₁ ∧ ¬G.Adj a c₂) ∧
      (¬G.Adj b L₁ ∧ ¬G.Adj b c₁ ∧ ¬G.Adj b c₂) ∧
      (¬G.Adj c L₁ ∧ ¬G.Adj c c₁ ∧ ¬G.Adj c c₂) ∧
      G.degree a + G.degree b + G.degree c ≤ 13)
    (hntri2 : ¬∃ a b c : Fin 20, a ∈ Dᶜ ∧ b ∈ Dᶜ ∧ c ∈ Dᶜ ∧
      G.Adj a b ∧ G.Adj a c ∧ G.Adj b c ∧
      (¬G.Adj a c₁ ∧ ¬G.Adj a c₂ ∧ ¬G.Adj a L₂) ∧
      (¬G.Adj b c₁ ∧ ¬G.Adj b c₂ ∧ ¬G.Adj b L₂) ∧
      (¬G.Adj c c₁ ∧ ¬G.Adj c c₂ ∧ ¬G.Adj c L₂) ∧
      G.degree a + G.degree b + G.degree c ≤ 13) :
    False := by
  classical
  have hsumdeg : ∑ g ∈ Dᶜ, G.degree g = 72 - 3 * D.card := by
    have hcong : ∑ g ∈ Dᶜ, ((G.neighborFinset g ∩ ({L₁, c₁, c₂, L₂} : Finset (Fin 20))).card
        + (G.neighborFinset g ∩ Iso).card + (G.neighborFinset g ∩ Dᶜ).card)
        = ∑ g ∈ Dᶜ, G.degree g := Finset.sum_congr rfl hper
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hsumPath, hsumIso, hsumInternal] at hcong
    omega
  rcases (by omega : D.card = 9 ∨ D.card = 10 ∨ D.card = 11) with hD9 | hD10 | hD11
  · exact iso1_dense_corner_twenty G D Iso L₁ c₁ c₂ L₂ h3 hmemD hIsoprop hisochar
      hL1deg hc1deg hc2deg hL2deg hac1L1 hc12 hac2L2 hL1nc2 hL2nc1 hNc1D hNc2D hL1D hc1D hc2D hL2D
      hd_lb hd_ub htt hth hsv hT hC4 hK23 hDccard _hIsocard hc1hub hc2hub hL1hub hL2hub hsumPath
      hsumIso hsumInternal hper hntri1 hntri2 (Or.inl hD9)
  · exact iso1_dense_corner_twenty G D Iso L₁ c₁ c₂ L₂ h3 hmemD hIsoprop hisochar
      hL1deg hc1deg hc2deg hL2deg hac1L1 hc12 hac2L2 hL1nc2 hL2nc1 hNc1D hNc2D hL1D hc1D hc2D hL2D
      hd_lb hd_ub htt hth hsv hT hC4 hK23 hDccard _hIsocard hc1hub hc2hub hL1hub hL2hub hsumPath
      hsumIso hsumInternal hper hntri1 hntri2 (Or.inr hD10)
  · -- **`|D| = 11`** (`Dᶜ.card = 9`, `∑ int = 12`, `∑ deg = 39`): the standalone D11 kill handles
    -- both the clean (`budget_contra_gen`, `12 < 15`) and the degree-`≥ 6` exceptional (forced
    -- `K₄`-in-`FF` hub-triangle of degree sum `12 ≤ 13`) cases internally.
    have hDc9 : Dᶜ.card = 9 := by rw [hDccard, hD11]
    have hsumdeg39 : ∑ g ∈ Dᶜ, G.degree g = 39 := by rw [hsumdeg, hD11]
    have hint12 : ∑ g ∈ Dᶜ, (G.neighborFinset g ∩ Dᶜ).card = 12 := by rw [hsumInternal, hD11]
    exact iso_rich_force_p4_d11_twenty G D Iso L₁ c₁ c₂ L₂ h3 hmemD hIsoprop hisochar
      hL1deg hc1deg hc2deg hL2deg hac1L1 hc12 hac2L2 hL1nc2 hL2nc1 hL1D hc1D hc2D hL2D htt
      hntri1 hDc9 hc1hub hc2hub hL1hub hL2hub hsumdeg39 hint12 hper

end N20

end ACMax
