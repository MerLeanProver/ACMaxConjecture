import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N16.Core
import ACMaxConjecture.SmallCases.Certificates

/-!
# `|FF| = 3` inactive-hub extraction for the `n = 16` hub-triangle iso-rich core

This file closes the last `|FF| = 3` sub-case of `iso_rich_force_sixteen`.  The inclusion–exclusion
budget pins `|A1| = |A2| = 4`, leaving `|B| = 3` *inactive* hubs `B = Dᶜ \ (A1 ∪ A2)` with
`∑_B int ≤ 1` and `∑_B iso ≥ 7`.  From these we construct a `TwoHubConfig G`, contradicting the
standing hypothesis `¬TwoHubConfig G`.

The construction picks
* `h₁` — an inactive hub with `iso = 3` (hence `int = 0`, `path = 1`); it exists because three
  hubs each carrying `iso ≤ 3` cannot sum to `≥ 7` unless one is `3`;
* `h₂ ≠ h₁` — an inactive hub with `int = 0`; it exists because the other two inactive hubs carry
  total internal degree `≤ ∑_B int ≤ 1`, so one is internally isolated;
* `a, b` — two `M`-isolated twins of `h₁` not adjacent to `h₂` (`h₁` has three twins, shares `≤ 1`
  with `h₂`); and
* `c, d` — two degree-`3` neighbours of `h₂` not adjacent to `h₁` (`h₂` has four neighbours all of
  degree `3` since `int(h₂) = 0`, and shares `≤ 1 + path(h₁) = 2` with `h₁`).
All `TwoHubConfig` non-adjacencies follow from `M`-isolation of `Iso` (an independent set whose
neighbours have degree `≠ 3`) together with the share bound `nonadj_hubs_share_le_one_iso`.
-/

namespace ACMax

open scoped Classical

namespace N16

/-- **`|FF| = 3` ⇒ `TwoHubConfig` (hence contradiction).**  From the budget-tight inactive-hub
data (`|B| = 3`, `∑_B int ≤ 1`, `∑_B iso ≥ 7`, with the per-hub split `path + iso + int = 4` and
each inactive hub touching a cherry), construct a `TwoHubConfig G`, contradicting `¬TwoHubConfig`. -/
theorem ff3_extract_twohub (G : SimpleGraph (Fin 16)) (D Iso : Finset (Fin 16))
    (L₁ c₁ c₂ L₂ : Fin 16) (B : Finset (Fin 16))
    (hth : ¬TwoHubConfig G)
    (hC4 : ¬∃ a b c d : Fin 16, ({a, b, c, d} : Finset (Fin 16)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (hIsoD : Iso ⊆ D)
    (hIsoprop : ∀ v ∈ Iso, G.degree v = 3 ∧ (∀ w : Fin 16, G.Adj v w → G.degree w ≠ 3))
    (hdeg4 : ∀ w : Fin 16, w ∈ Dᶜ → G.degree w = 4)
    (hDdeg3 : ∀ v : Fin 16, v ∈ D → G.degree v = 3)
    (hDeq : ({L₁, c₁, c₂, L₂} : Finset (Fin 16)) ∪ Iso = D)
    (hBsub : B ⊆ Dᶜ) (hBcard : B.card = 3)
    (hBint1 : (∑ g ∈ B, (G.neighborFinset g ∩ Dᶜ).card) ≤ 1)
    (hBiso7 : 7 ≤ ∑ g ∈ B, (G.neighborFinset g ∩ Iso).card)
    (hper : ∀ g : Fin 16, g ∈ Dᶜ →
      (G.neighborFinset g ∩ ({L₁, c₁, c₂, L₂} : Finset (Fin 16))).card
        + (G.neighborFinset g ∩ Iso).card + (G.neighborFinset g ∩ Dᶜ).card = 4)
    (hpath1 : ∀ h : Fin 16, h ∈ B →
      1 ≤ (G.neighborFinset h ∩ ({L₁, c₁, c₂, L₂} : Finset (Fin 16))).card) :
    False := by
  classical
  set P : Finset (Fin 16) := {L₁, c₁, c₂, L₂} with hPdef
  -- Each inactive hub carries `iso ≤ 3` (since `path ≥ 1`).
  have hisole3 : ∀ h ∈ B, (G.neighborFinset h ∩ Iso).card ≤ 3 := by
    intro h hh
    have hp := hper h (hBsub hh)
    have hpa := hpath1 h hh
    omega
  -- Extract `h₁ ∈ B` with `iso = 3`.
  have hex1 : ∃ h ∈ B, (G.neighborFinset h ∩ Iso).card = 3 := by
    by_contra hcon
    push Not at hcon
    have hle2 : ∀ h ∈ B, (G.neighborFinset h ∩ Iso).card ≤ 2 := by
      intro h hh
      have h3 := hisole3 h hh
      have hne := hcon h hh
      omega
    have hsum := Finset.sum_le_sum hle2
    rw [Finset.sum_const, hBcard, smul_eq_mul] at hsum
    omega
  obtain ⟨h₁, hh1B, hiso1⟩ := hex1
  have hh1Dc : h₁ ∈ Dᶜ := hBsub hh1B
  have hp1 := hper h₁ hh1Dc
  have hpa1 := hpath1 h₁ hh1B
  have hint1_eq : (G.neighborFinset h₁ ∩ Dᶜ).card = 0 := by omega
  have hpath1_eq : (G.neighborFinset h₁ ∩ P).card = 1 := by omega
  -- Extract `h₂ ∈ B \ {h₁}` with `int = 0`.
  have hex2 : ∃ h ∈ B.erase h₁, (G.neighborFinset h ∩ Dᶜ).card = 0 := by
    by_contra hcon
    push Not at hcon
    have hge : ∀ h ∈ B.erase h₁, 1 ≤ (G.neighborFinset h ∩ Dᶜ).card :=
      fun h hh => Nat.one_le_iff_ne_zero.mpr (hcon h hh)
    have hsub : B.erase h₁ ⊆ B := Finset.erase_subset _ _
    have hsumge : (B.erase h₁).card
        ≤ ∑ g ∈ B.erase h₁, (G.neighborFinset g ∩ Dᶜ).card := by
      calc (B.erase h₁).card = ∑ _g ∈ B.erase h₁, 1 := by
            rw [Finset.sum_const, smul_eq_mul, mul_one]
        _ ≤ _ := Finset.sum_le_sum hge
    have hcarderase : (B.erase h₁).card = 2 := by
      rw [Finset.card_erase_of_mem hh1B, hBcard]
    have hsumle : ∑ g ∈ B.erase h₁, (G.neighborFinset g ∩ Dᶜ).card
        ≤ ∑ g ∈ B, (G.neighborFinset g ∩ Dᶜ).card :=
      Finset.sum_le_sum_of_subset hsub
    omega
  obtain ⟨h₂, hh2erase, hint2⟩ := hex2
  have hh2B : h₂ ∈ B := Finset.mem_of_mem_erase hh2erase
  have hh12 : h₁ ≠ h₂ := (Finset.ne_of_mem_erase hh2erase).symm
  have hh2Dc : h₂ ∈ Dᶜ := hBsub hh2B
  -- `h₁` and `h₂` are non-adjacent (`int(h₁) = 0`).
  have hnadj : ¬G.Adj h₁ h₂ := by
    intro hadj
    have hmem : h₂ ∈ G.neighborFinset h₁ ∩ Dᶜ :=
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hadj, hh2Dc⟩
    rw [Finset.card_eq_zero] at hint1_eq
    rw [hint1_eq] at hmem
    exact (Finset.notMem_empty _) hmem
  -- Share bound: the two non-adjacent hubs share `≤ 1` isolated twin.
  have hshare := nonadj_hubs_share_le_one_iso G D Iso hC4 hIsoD hIsoprop hdeg4
    h₁ h₂ hh1Dc hh2Dc hh12 hnadj
  -- `D`-membership facts.
  have hh1notD : h₁ ∉ D := Finset.mem_compl.mp hh1Dc
  have hh2notD : h₂ ∉ D := Finset.mem_compl.mp hh2Dc
  -- Extract `a, b`: two `Iso`-twins of `h₁` not adjacent to `h₂`.
  have hT1part := Finset.card_sdiff_add_card_inter
    (G.neighborFinset h₁ ∩ Iso) (G.neighborFinset h₂)
  have hT1int : (G.neighborFinset h₁ ∩ Iso) ∩ G.neighborFinset h₂
      = (G.neighborFinset h₁ ∩ G.neighborFinset h₂) ∩ Iso := by
    ext x; simp only [Finset.mem_inter]; tauto
  rw [hT1int, hiso1] at hT1part
  have hT1card : 2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card := by omega
  obtain ⟨a, haT, b, hbT, hab⟩ := Finset.one_lt_card.mp (by omega : 1 <
    ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card)
  have ha_props := Finset.mem_sdiff.mp haT
  have haNI := Finset.mem_inter.mp ha_props.1
  have haNh1 : G.Adj h₁ a := (G.mem_neighborFinset _ _).mp haNI.1
  have haIso : a ∈ Iso := haNI.2
  have ha_nadj_h2 : ¬G.Adj h₂ a :=
    fun hadj => ha_props.2 ((G.mem_neighborFinset _ _).mpr hadj)
  have hb_props := Finset.mem_sdiff.mp hbT
  have hbNI := Finset.mem_inter.mp hb_props.1
  have hbNh1 : G.Adj h₁ b := (G.mem_neighborFinset _ _).mp hbNI.1
  have hbIso : b ∈ Iso := hbNI.2
  have hb_nadj_h2 : ¬G.Adj h₂ b :=
    fun hadj => hb_props.2 ((G.mem_neighborFinset _ _).mpr hadj)
  -- Extract `c, d`: two degree-`3` neighbours of `h₂` not adjacent to `h₁`.
  have hN2D : G.neighborFinset h₂ ⊆ D := by
    intro x hx
    by_contra hxD
    have hmem : x ∈ G.neighborFinset h₂ ∩ Dᶜ :=
      Finset.mem_inter.mpr ⟨hx, Finset.mem_compl.mpr hxD⟩
    rw [Finset.card_eq_zero] at hint2
    rw [hint2] at hmem
    exact (Finset.notMem_empty _) hmem
  have hScard : (G.neighborFinset h₂ ∩ G.neighborFinset h₁).card ≤ 2 := by
    have hSsubD : G.neighborFinset h₂ ∩ G.neighborFinset h₁ ⊆ D :=
      (Finset.inter_subset_left).trans hN2D
    have hSsubPI : G.neighborFinset h₂ ∩ G.neighborFinset h₁ ⊆ P ∪ Iso := by
      rw [hDeq]; exact hSsubD
    have hdecomp : G.neighborFinset h₂ ∩ G.neighborFinset h₁
        = ((G.neighborFinset h₂ ∩ G.neighborFinset h₁) ∩ P)
          ∪ ((G.neighborFinset h₂ ∩ G.neighborFinset h₁) ∩ Iso) := by
      rw [← Finset.inter_union_distrib_left, Finset.inter_eq_left.mpr hSsubPI]
    have hle := Finset.card_union_le
      ((G.neighborFinset h₂ ∩ G.neighborFinset h₁) ∩ P)
      ((G.neighborFinset h₂ ∩ G.neighborFinset h₁) ∩ Iso)
    have hpathpart : ((G.neighborFinset h₂ ∩ G.neighborFinset h₁) ∩ P).card ≤ 1 := by
      have hsub : (G.neighborFinset h₂ ∩ G.neighborFinset h₁) ∩ P
          ⊆ G.neighborFinset h₁ ∩ P := by
        intro x hx
        rw [Finset.mem_inter] at hx ⊢
        exact ⟨(Finset.mem_inter.mp hx.1).2, hx.2⟩
      calc ((G.neighborFinset h₂ ∩ G.neighborFinset h₁) ∩ P).card
          ≤ (G.neighborFinset h₁ ∩ P).card := Finset.card_le_card hsub
        _ = 1 := hpath1_eq
    have hisopart : ((G.neighborFinset h₂ ∩ G.neighborFinset h₁) ∩ Iso).card ≤ 1 := by
      have heq : (G.neighborFinset h₂ ∩ G.neighborFinset h₁) ∩ Iso
          = (G.neighborFinset h₁ ∩ G.neighborFinset h₂) ∩ Iso := by
        rw [Finset.inter_comm (G.neighborFinset h₂) (G.neighborFinset h₁)]
      rw [heq]; exact hshare
    rw [hdecomp]; omega
  have hN2card : (G.neighborFinset h₂).card = 4 := by
    rw [G.card_neighborFinset_eq_degree]; exact hdeg4 h₂ hh2Dc
  have hC2part := Finset.card_sdiff_add_card_inter
    (G.neighborFinset h₂) (G.neighborFinset h₁)
  rw [hN2card] at hC2part
  have hC2card : 2 ≤ (G.neighborFinset h₂ \ G.neighborFinset h₁).card := by omega
  obtain ⟨c, hcC, d, hdC, hcd⟩ := Finset.one_lt_card.mp (by omega : 1 <
    (G.neighborFinset h₂ \ G.neighborFinset h₁).card)
  have hc_props := Finset.mem_sdiff.mp hcC
  have hcNh2 : G.Adj h₂ c := (G.mem_neighborFinset _ _).mp hc_props.1
  have hcnh1 : c ∉ G.neighborFinset h₁ := hc_props.2
  have hc_nadj_h1 : ¬G.Adj h₁ c :=
    fun hadj => hcnh1 ((G.mem_neighborFinset _ _).mpr hadj)
  have hcD : c ∈ D := hN2D hc_props.1
  have hcdeg : G.degree c = 3 := hDdeg3 c hcD
  have hd_props := Finset.mem_sdiff.mp hdC
  have hdNh2 : G.Adj h₂ d := (G.mem_neighborFinset _ _).mp hd_props.1
  have hdnh1 : d ∉ G.neighborFinset h₁ := hd_props.2
  have hd_nadj_h1 : ¬G.Adj h₁ d :=
    fun hadj => hdnh1 ((G.mem_neighborFinset _ _).mpr hadj)
  have hdD : d ∈ D := hN2D hd_props.1
  have hddeg : G.degree d = 3 := hDdeg3 d hdD
  -- Degrees of `a, b`.
  have hadeg : G.degree a = 3 := (hIsoprop a haIso).1
  have hbdeg : G.degree b = 3 := (hIsoprop b hbIso).1
  -- `Iso` is independent of degree-`3` vertices: `a, b ≁ c, d`.
  have ha_nadj_c : ¬G.Adj a c := fun hadj => (hIsoprop a haIso).2 c hadj hcdeg
  have ha_nadj_d : ¬G.Adj a d := fun hadj => (hIsoprop a haIso).2 d hadj hddeg
  have hb_nadj_c : ¬G.Adj b c := fun hadj => (hIsoprop b hbIso).2 c hadj hcdeg
  have hb_nadj_d : ¬G.Adj b d := fun hadj => (hIsoprop b hbIso).2 d hadj hddeg
  -- `D`-membership of `a, b`.
  have haD : a ∈ D := hIsoD haIso
  have hbD : b ∈ D := hIsoD hbIso
  -- Membership for distinctness `a, b ∈ N h₁`, `c, d ∉ N h₁`.
  have haNh1mem : a ∈ G.neighborFinset h₁ := (G.mem_neighborFinset _ _).mpr haNh1
  have hbNh1mem : b ∈ G.neighborFinset h₁ := (G.mem_neighborFinset _ _).mpr hbNh1
  -- Assemble the `TwoHubConfig`.
  exact hth ⟨h₁, h₂, a, b, c, d,
    hdeg4 h₁ hh1Dc, hdeg4 h₂ hh2Dc, hadeg, hbdeg, hcdeg, hddeg,
    haNh1.symm, hbNh1.symm, hcNh2.symm, hdNh2.symm,
    hnadj, hc_nadj_h1, hd_nadj_h1,
    (fun hadj => ha_nadj_h2 hadj.symm), ha_nadj_c, ha_nadj_d,
    (fun hadj => hb_nadj_h2 hadj.symm), hb_nadj_c, hb_nadj_d,
    hh12,
    (fun e => hh1notD (e ▸ haD)), (fun e => hh1notD (e ▸ hbD)),
    (fun e => hh1notD (e ▸ hcD)), (fun e => hh1notD (e ▸ hdD)),
    (fun e => hh2notD (e ▸ haD)), (fun e => hh2notD (e ▸ hbD)),
    (fun e => hh2notD (e ▸ hcD)), (fun e => hh2notD (e ▸ hdD)),
    hab, (fun e => hcnh1 (e ▸ haNh1mem)), (fun e => hdnh1 (e ▸ haNh1mem)),
    (fun e => hcnh1 (e ▸ hbNh1mem)), (fun e => hdnh1 (e ▸ hbNh1mem)), hcd⟩

end N16

end ACMax
