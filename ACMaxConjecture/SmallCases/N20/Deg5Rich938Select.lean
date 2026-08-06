import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N20.TwoHubCornerDeg5ZLeaf
import ACMaxConjecture.SmallCases.N20.TwoHubSelect
import ACMaxConjecture.SmallCases.N20.ZVertex
import ACMaxConjecture.SmallCases.N20.Deg5ZSlots
import ACMaxConjecture.SmallCases.N20.Deg5SameZ
import ACMaxConjecture.SmallCases.N20.Deg5RichCap

/-! # The good-h₂ selector for the rich (9,9,39) Z-leaf extraction (`n = 20`) -/
namespace ACMax
open scoped Classical

namespace N20

set_option maxHeartbeats 1000000 in
/-- With the rich hub `g` (isoDeg ≥ 3), the tight `(9,9,39)` ledger + the iso-cap
(`isoDeg_le_two_of_nonadj_rich_twenty`) produce a degree-`4` `Z`-slot hub `h₂`
of isoDeg `≥ 2`, on a `z` avoided by `g` and non-adjacent to `g`. -/
theorem exists_good_h2z_rich_939_twenty (G : SimpleGraph (Fin 20)) (Hub Iso : Finset (Fin 20))
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdisj : Disjoint Hub Iso) (hsum18 : Hub.card + Iso.card = 18)
    (hdeg3 : ∀ v : Fin 20, 3 ≤ G.degree v) (hisodeg3 : ∀ t ∈ Iso, G.degree t = 3)
    (hleak : ∑ h ∈ Hub, (G.neighborFinset h ∩ (Finset.univ \ (Hub ∪ Iso))).card ≤ 4)
    (hdeg : ∀ h ∈ Hub, 4 ≤ G.degree h) (hdeg5 : ∀ h ∈ Hub, G.degree h ≤ 5)
    (hHub : Hub.card = 9) (hIso : Iso.card = 9) (hdsum : ∑ w ∈ Hub, G.degree w = 39)
    (hT : ¬∃ x y z : Fin 20, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 11)
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hno2hub : ¬∃ h₁ h₂ : Fin 20, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card)
    (g : Fin 20) (hg : g ∈ Hub) (hgd : G.degree g = 4)
    (hgiso : 3 ≤ (G.neighborFinset g ∩ Iso).card) :
    ∃ h₂ z : Fin 20, h₂ ∈ Hub ∧ G.degree h₂ = 4 ∧
      2 ≤ (G.neighborFinset h₂ ∩ Iso).card ∧
      z ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 20)) ∧
      G.Adj z h₂ ∧ ¬G.Adj g z ∧ ¬G.Adj g h₂ := by
  classical
  set Z : Finset (Fin 20) := Finset.univ \ (Hub ∪ Iso) with hZdef
  -- Per-vertex three-way split, folded to `Z`.
  have hnbr : ∀ v : Fin 20, (G.neighborFinset v ∩ Hub).card + (G.neighborFinset v ∩ Iso).card
      + (G.neighborFinset v ∩ Z).card = G.degree v := by
    intro v
    have h := nbr_split_three_twenty G Hub Iso hdisj v
    rw [← hZdef] at h; exact h
  -- Every hub has degree `4` or `5`.
  have hpd : ∀ h ∈ Hub, G.degree h = 4 ∨ G.degree h = 5 := by
    intro h hh; have := hdeg h hh; have := hdeg5 h hh; omega
  -- The deg-4 / deg-5 partition: `|D4| = 6`, `|D5| = 3`.
  set D4 : Finset (Fin 20) := Hub.filter (fun h => G.degree h = 4) with hD4def
  set D5 : Finset (Fin 20) := Hub.filter (fun h => G.degree h = 5) with hD5def
  have hmemD4 : ∀ w, w ∈ D4 ↔ w ∈ Hub ∧ G.degree w = 4 := fun w => by
    rw [hD4def]; exact Finset.mem_filter
  have hmemD5 : ∀ w, w ∈ D5 ↔ w ∈ Hub ∧ G.degree w = 5 := fun w => by
    rw [hD5def]; exact Finset.mem_filter
  have hcover : D4 ∪ D5 = Hub := by
    ext h; rw [Finset.mem_union, hmemD4, hmemD5]
    constructor
    · rintro (⟨hh, _⟩ | ⟨hh, _⟩) <;> exact hh
    · intro hh; rcases hpd h hh with h4 | h5
      · exact Or.inl ⟨hh, h4⟩
      · exact Or.inr ⟨hh, h5⟩
  have hdisj45 : Disjoint D4 D5 := by
    rw [Finset.disjoint_left]; intro h hd4 hd5
    rw [hmemD4] at hd4; rw [hmemD5] at hd5; omega
  have hcardsum : D4.card + D5.card = 9 := by
    rw [← hHub, ← hcover, Finset.card_union_of_disjoint hdisj45]
  have hdegsum : ∑ w ∈ Hub, G.degree w = 4 * D4.card + 5 * D5.card := by
    rw [← hcover, Finset.sum_union hdisj45]
    have e4 : ∑ w ∈ D4, G.degree w = 4 * D4.card := by
      have h1 : ∑ w ∈ D4, G.degree w = ∑ _w ∈ D4, 4 :=
        Finset.sum_congr rfl (fun w hw => ((hmemD4 w).mp hw).2)
      rw [h1, Finset.sum_const, smul_eq_mul, mul_comm]
    have e5 : ∑ w ∈ D5, G.degree w = 5 * D5.card := by
      have h1 : ∑ w ∈ D5, G.degree w = ∑ _w ∈ D5, 5 :=
        Finset.sum_congr rfl (fun w hw => ((hmemD5 w).mp hw).2)
      rw [h1, Finset.sum_const, smul_eq_mul, mul_comm]
    rw [e4, e5]
  have h39 : 4 * D4.card + 5 * D5.card = 39 := by rw [← hdegsum]; exact hdsum
  have hD4card : D4.card = 6 := by omega
  -- Ledger: total iso-incidence over hubs is `27`.
  have hledger : ∑ h ∈ Hub, (G.neighborFinset h ∩ Iso).card = 27 := by
    have hc : ∑ w ∈ Iso, (G.neighborFinset w ∩ Hub).card = ∑ _w ∈ Iso, 3 :=
      Finset.sum_congr rfl (fun w hw => hiso3 w hw)
    rw [cross_count_twenty G Hub Iso, hc, Finset.sum_const, hIso, smul_eq_mul]
  -- The `(hubDeg + zDeg)` ledger sums to `12`.
  have hssum : ∑ h ∈ Hub, ((G.neighborFinset h ∩ Hub).card + (G.neighborFinset h ∩ Z).card)
      = 12 := by
    have key : ∑ h ∈ Hub, (((G.neighborFinset h ∩ Hub).card + (G.neighborFinset h ∩ Z).card)
        + (G.neighborFinset h ∩ Iso).card) = ∑ h ∈ Hub, G.degree h := by
      apply Finset.sum_congr rfl
      intro h _; have := hnbr h; omega
    rw [Finset.sum_add_distrib, hledger, hdsum] at key
    omega
  -- The rich-hub iso-cap on deg-4 hubs off `g`.
  have hcapf : ∀ h ∈ Hub, h ≠ g → G.degree h = 4 → ¬G.Adj g h →
      (G.neighborFinset h ∩ Iso).card ≤ 2 := by
    intro h hh hne h4 hnadj
    exact isoDeg_le_two_of_nonadj_rich_twenty G Hub Iso hshare hno2hub g h hg hh hgd h4
      (fun e => hne e.symm) hnadj hgiso
  -- `g`'s profile: `hubDeg g + zDeg g ≤ 1`.
  have hgsp := hnbr g
  have hgprofile : (G.neighborFinset g ∩ Hub).card + (G.neighborFinset g ∩ Z).card ≤ 1 := by
    rw [hgd] at hgsp; omega
  -- Suppose no good `h₂`.
  by_contra hcon
  have hnogood : ∀ h z : Fin 20, h ∈ Hub → G.degree h = 4 →
      2 ≤ (G.neighborFinset h ∩ Iso).card → z ∈ Z → G.Adj z h → ¬G.Adj g z → ¬G.Adj g h →
      False := by
    intro h z hh h4 h2 hzZ hzh hgz hgh
    exact hcon ⟨h, z, hh, h4, h2, hzZ, hzh, hgz, hgh⟩
  -- The two `M`-endpoints and their hub-slots.
  have zslots : ∀ z, z ∈ Z → ∃ p q : Fin 20, p ∈ Hub ∧ q ∈ Hub ∧ p ≠ q ∧
      G.Adj z p ∧ G.Adj z q := by
    intro z hz
    obtain ⟨_, hzhub2, _⟩ :=
      zfacts_deg5_twenty G Hub Iso hiso3 hdisj hsum18 hdeg3 hisodeg3 hleak z
        (by rw [← hZdef]; exact hz)
    obtain ⟨p, q, hpqne, hpqEq⟩ := Finset.card_eq_two.mp hzhub2
    have hpM : p ∈ G.neighborFinset z ∩ Hub := by rw [hpqEq]; exact Finset.mem_insert_self p {q}
    have hqM : q ∈ G.neighborFinset z ∩ Hub := by
      rw [hpqEq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self q)
    rw [Finset.mem_inter, G.mem_neighborFinset] at hpM hqM
    exact ⟨p, q, hpM.2, hqM.2, hpqne, hpM.1, hqM.1⟩
  -- The avoided-slot set `AV`.
  obtain ⟨AV, hAVsub, hAVcard, hg_notin_AV, hAV_slot⟩ :
      ∃ AV : Finset (Fin 20), AV ⊆ Hub ∧
        AV.card = 4 - 2 * (G.neighborFinset g ∩ Z).card ∧ g ∉ AV ∧
        (∀ h ∈ AV, 1 ≤ (G.neighborFinset h ∩ Z).card ∧
          (G.degree h = 4 → ¬G.Adj g h → (G.neighborFinset h ∩ Iso).card ≤ 1)) := by
    obtain ⟨z₁, z₂, hz12ne, hz₁Z, hz₂Z, hZeq2, hadj12, hnohub⟩ :=
      zslot_skeleton_deg5_twenty G Hub Iso hiso3 hdisj hsum18 hdeg3 hisodeg3 hleak hdeg5 hT
    rw [← hZdef] at hz₁Z hz₂Z hZeq2
    -- The slot property packaged through `hnogood`.
    have slotProp : ∀ (z w : Fin 20), z ∈ Z → ¬G.Adj g z → w ∈ Hub → G.Adj z w →
        1 ≤ (G.neighborFinset w ∩ Z).card ∧
        (G.degree w = 4 → ¬G.Adj g w → (G.neighborFinset w ∩ Iso).card ≤ 1) := by
      intro z w hzZ hgz hwH hzw
      refine ⟨Finset.card_pos.mpr ⟨z, Finset.mem_inter.mpr
        ⟨(G.mem_neighborFinset w z).mpr hzw.symm, hzZ⟩⟩, ?_⟩
      intro hw4 hgw
      by_contra hcon2
      exact hnogood w z hwH hw4 (by omega) hzZ hzw hgz hgw
    rcases Nat.eq_zero_or_pos (G.neighborFinset g ∩ Z).card with hz0 | hzpos
    · -- `zDeg g = 0`: both `M`-endpoints avoided, all four slots.
      have hgz0 : ∀ z, z ∈ Z → ¬G.Adj g z := fun z hzz hadj => by
        have hpos : 0 < (G.neighborFinset g ∩ Z).card :=
          Finset.card_pos.mpr
            ⟨z, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset g z).mpr hadj, hzz⟩⟩
        omega
      obtain ⟨p₁, q₁, hp₁H, hq₁H, hpq₁, hzp₁, hzq₁⟩ := zslots z₁ hz₁Z
      obtain ⟨p₂, q₂, hp₂H, hq₂H, hpq₂, hzp₂, hzq₂⟩ := zslots z₂ hz₂Z
      have hcross : ∀ a b : Fin 20, a ∈ Hub → G.Adj z₁ a → G.Adj z₂ b → a ≠ b := by
        intro a b haH hz1a hz2b hab
        subst hab; exact hnohub a haH ⟨hz1a.symm, hz2b.symm⟩
      refine ⟨{p₁, q₁, p₂, q₂}, ?_, ?_, ?_, ?_⟩
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl | rfl
        exacts [hp₁H, hq₁H, hp₂H, hq₂H]
      · have hc4 : ({p₁, q₁, p₂, q₂} : Finset (Fin 20)).card = 4 :=
          card_four_twenty p₁ q₁ p₂ q₂ hpq₁ (hcross p₁ p₂ hp₁H hzp₁ hzp₂)
            (hcross p₁ q₂ hp₁H hzp₁ hzq₂) (hcross q₁ p₂ hq₁H hzq₁ hzp₂)
            (hcross q₁ q₂ hq₁H hzq₁ hzq₂) hpq₂
        rw [hc4, hz0]
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        refine ⟨?_, ?_, ?_, ?_⟩ <;> intro he
        · exact hgz0 z₁ hz₁Z (he.symm ▸ hzp₁).symm
        · exact hgz0 z₁ hz₁Z (he.symm ▸ hzq₁).symm
        · exact hgz0 z₂ hz₂Z (he.symm ▸ hzp₂).symm
        · exact hgz0 z₂ hz₂Z (he.symm ▸ hzq₂).symm
      · intro h hmem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
        rcases hmem with rfl | rfl | rfl | rfl
        · exact slotProp z₁ h hz₁Z (hgz0 z₁ hz₁Z) hp₁H hzp₁
        · exact slotProp z₁ h hz₁Z (hgz0 z₁ hz₁Z) hq₁H hzq₁
        · exact slotProp z₂ h hz₂Z (hgz0 z₂ hz₂Z) hp₂H hzp₂
        · exact slotProp z₂ h hz₂Z (hgz0 z₂ hz₂Z) hq₂H hzq₂
    · -- `zDeg g = 1`: exactly one `M`-endpoint avoided.
      have hzg1 : (G.neighborFinset g ∩ Z).card = 1 := by omega
      by_cases hadjz1 : G.Adj g z₁
      · -- `z₁` met, `z₂` avoided.
        have hng2 : ¬G.Adj g z₂ := by
          intro hadj2
          have hsub : ({z₁, z₂} : Finset (Fin 20)) ⊆ G.neighborFinset g ∩ Z := by
            intro x hx; rw [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl
            · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset g x).mpr hadjz1, hz₁Z⟩
            · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset g x).mpr hadj2, hz₂Z⟩
          have hcard2 : ({z₁, z₂} : Finset (Fin 20)).card = 2 := Finset.card_pair hz12ne
          have := Finset.card_le_card hsub
          rw [hcard2] at this; omega
        obtain ⟨p₂, q₂, hp₂H, hq₂H, hpq₂, hzp₂, hzq₂⟩ := zslots z₂ hz₂Z
        refine ⟨{p₂, q₂}, ?_, ?_, ?_, ?_⟩
        · intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          exacts [hp₂H, hq₂H]
        · rw [Finset.card_pair hpq₂, hzg1]
        · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          refine ⟨?_, ?_⟩ <;> intro he
          · exact hng2 (he.symm ▸ hzp₂).symm
          · exact hng2 (he.symm ▸ hzq₂).symm
        · intro h hmem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
          rcases hmem with rfl | rfl
          · exact slotProp z₂ h hz₂Z hng2 hp₂H hzp₂
          · exact slotProp z₂ h hz₂Z hng2 hq₂H hzq₂
      · -- `z₁` avoided.
        obtain ⟨p₁, q₁, hp₁H, hq₁H, hpq₁, hzp₁, hzq₁⟩ := zslots z₁ hz₁Z
        refine ⟨{p₁, q₁}, ?_, ?_, ?_, ?_⟩
        · intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          exacts [hp₁H, hq₁H]
        · rw [Finset.card_pair hpq₁, hzg1]
        · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          refine ⟨?_, ?_⟩ <;> intro he
          · exact hadjz1 (he.symm ▸ hzp₁).symm
          · exact hadjz1 (he.symm ▸ hzq₁).symm
        · intro h hmem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
          rcases hmem with rfl | rfl
          · exact slotProp z₁ h hz₁Z hadjz1 hp₁H hzp₁
          · exact slotProp z₁ h hz₁Z hadjz1 hq₁H hzq₁
  -- The deg-4 hubs off `g`, split by adjacency to `g`.
  set FA : Finset (Fin 20) := (D4.erase g).filter (fun h => G.Adj g h) with hFAdef
  set FN : Finset (Fin 20) := (D4.erase g).filter (fun h => ¬G.Adj g h) with hFNdef
  have hFAmem : ∀ h, h ∈ FA ↔ (h ∈ Hub ∧ G.degree h = 4 ∧ h ≠ g ∧ G.Adj g h) := by
    intro h; simp only [hFAdef, hD4def, Finset.mem_filter, Finset.mem_erase]; tauto
  have hFNmem : ∀ h, h ∈ FN ↔ (h ∈ Hub ∧ G.degree h = 4 ∧ h ≠ g ∧ ¬G.Adj g h) := by
    intro h; simp only [hFNdef, hD4def, Finset.mem_filter, Finset.mem_erase]; tauto
  have hFA_sub : FA ⊆ Hub := fun x hx => ((hFAmem x).mp hx).1
  have hFN_sub : FN ⊆ Hub := fun x hx => ((hFNmem x).mp hx).1
  have hFNFA : FN.card + FA.card = 5 := by
    have hg_in_D4 : g ∈ D4 := (hmemD4 g).mpr ⟨hg, hgd⟩
    have hdisjFN : Disjoint FN FA := by
      rw [Finset.disjoint_left]; intro x hxFN hxFA
      rw [hFNmem] at hxFN; rw [hFAmem] at hxFA
      exact hxFN.2.2.2 hxFA.2.2.2
    have hunion : FN ∪ FA = D4.erase g := by
      ext x; rw [Finset.mem_union, hFNmem, hFAmem, Finset.mem_erase]
      constructor
      · rintro (⟨hh, h4, hne, _⟩ | ⟨hh, h4, hne, _⟩) <;> exact ⟨hne, (hmemD4 x).mpr ⟨hh, h4⟩⟩
      · rintro ⟨hne, hxD4⟩
        obtain ⟨hh, h4⟩ := (hmemD4 x).mp hxD4
        by_cases ha : G.Adj g x
        · exact Or.inr ⟨hh, h4, hne, ha⟩
        · exact Or.inl ⟨hh, h4, hne, ha⟩
    have hcu : (FN ∪ FA).card = FN.card + FA.card := Finset.card_union_of_disjoint hdisjFN
    rw [hunion, Finset.card_erase_of_mem hg_in_D4, hD4card] at hcu
    omega
  have hFAle : FA.card ≤ (G.neighborFinset g ∩ Hub).card := by
    apply Finset.card_le_card
    intro h hmem
    obtain ⟨hhub, _, _, hadj⟩ := (hFAmem h).mp hmem
    exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset g h).mpr hadj, hhub⟩
  -- The per-hub lower bound `ℓ`.
  set ℓ : Fin 20 → ℕ := fun h => (if h ∈ FN then 2 else 0) + (if h ∈ FA then 1 else 0)
    + (if h ∈ AV then 1 else 0)
    + (if h ∈ ({g} : Finset (Fin 20)) then (G.neighborFinset g ∩ Z).card else 0) with hℓdef
  have hpt : ∀ h ∈ Hub,
      ℓ h ≤ (G.neighborFinset h ∩ Hub).card + (G.neighborFinset h ∩ Z).card := by
    intro h hh
    have hsp := hnbr h
    simp only [hℓdef]
    by_cases hg' : h = g
    · subst hg'
      have e1 : h ∉ FN := by rw [hFNmem]; rintro ⟨_, _, hne, _⟩; exact hne rfl
      have e2 : h ∉ FA := by rw [hFAmem]; rintro ⟨_, _, hne, _⟩; exact hne rfl
      have e4 : h ∈ ({h} : Finset (Fin 20)) := Finset.mem_singleton_self h
      rw [if_neg e1, if_neg e2, if_neg hg_notin_AV, if_pos e4]; omega
    · rcases hpd h hh with h4 | h5
      · by_cases hadj : G.Adj g h
        · have hFA : h ∈ FA := (hFAmem h).mpr ⟨hh, h4, hg', hadj⟩
          have e1 : h ∉ FN := by rw [hFNmem]; rintro ⟨_, _, _, hnadj⟩; exact hnadj hadj
          have e4 : h ∉ ({g} : Finset (Fin 20)) := by rw [Finset.mem_singleton]; exact hg'
          have hhub1 : 1 ≤ (G.neighborFinset h ∩ Hub).card :=
            Finset.card_pos.mpr ⟨g, Finset.mem_inter.mpr
              ⟨(G.mem_neighborFinset h g).mpr hadj.symm, hg⟩⟩
          by_cases hav : h ∈ AV
          · rw [if_neg e1, if_pos hFA, if_pos hav, if_neg e4]
            have hz1 := (hAV_slot h hav).1; omega
          · rw [if_neg e1, if_pos hFA, if_neg hav, if_neg e4]; omega
        · have hFN : h ∈ FN := (hFNmem h).mpr ⟨hh, h4, hg', hadj⟩
          have e2 : h ∉ FA := by rw [hFAmem]; rintro ⟨_, _, _, ha⟩; exact hadj ha
          have e4 : h ∉ ({g} : Finset (Fin 20)) := by rw [Finset.mem_singleton]; exact hg'
          have hiso2 : (G.neighborFinset h ∩ Iso).card ≤ 2 := hcapf h hh hg' h4 hadj
          by_cases hav : h ∈ AV
          · rw [if_pos hFN, if_neg e2, if_pos hav, if_neg e4]
            have hiso1 : (G.neighborFinset h ∩ Iso).card ≤ 1 := (hAV_slot h hav).2 h4 hadj
            omega
          · rw [if_pos hFN, if_neg e2, if_neg hav, if_neg e4]; omega
      · have e1 : h ∉ FN := by rw [hFNmem]; rintro ⟨_, h4, _, _⟩; omega
        have e2 : h ∉ FA := by rw [hFAmem]; rintro ⟨_, h4, _, _⟩; omega
        have e4 : h ∉ ({g} : Finset (Fin 20)) := by rw [Finset.mem_singleton]; exact hg'
        by_cases hav : h ∈ AV
        · rw [if_neg e1, if_neg e2, if_pos hav, if_neg e4]
          have hz1 := (hAV_slot h hav).1; omega
        · rw [if_neg e1, if_neg e2, if_neg hav, if_neg e4]; omega
  -- Evaluate `∑ ℓ`.
  have s1 : ∑ h ∈ Hub, (if h ∈ FN then (2 : ℕ) else 0) = 2 * FN.card := by
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hFN_sub, Finset.sum_const, smul_eq_mul,
      mul_comm]
  have s2 : ∑ h ∈ Hub, (if h ∈ FA then (1 : ℕ) else 0) = FA.card := by
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hFA_sub, Finset.sum_const, smul_eq_mul,
      mul_one]
  have s3 : ∑ h ∈ Hub, (if h ∈ AV then (1 : ℕ) else 0) = AV.card := by
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hAVsub, Finset.sum_const, smul_eq_mul,
      mul_one]
  have s4 : ∑ h ∈ Hub, (if h ∈ ({g} : Finset (Fin 20)) then (G.neighborFinset g ∩ Z).card else 0)
      = (G.neighborFinset g ∩ Z).card := by
    rw [Finset.sum_ite_mem, Finset.inter_singleton_of_mem hg, Finset.sum_singleton]
  have hℓsum : ∑ h ∈ Hub, ℓ h
      = 2 * FN.card + FA.card + AV.card + (G.neighborFinset g ∩ Z).card := by
    simp only [hℓdef, Finset.sum_add_distrib, s1, s2, s3, s4]
  have hℓle : ∑ h ∈ Hub, ℓ h ≤ 12 := (Finset.sum_le_sum hpt).trans_eq hssum
  rw [hℓsum] at hℓle
  omega

end N20

end ACMax
