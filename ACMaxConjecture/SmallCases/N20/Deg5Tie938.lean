import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N20.TwoHubCornerDeg5ZLeaf
import ACMaxConjecture.SmallCases.N20.R5ResidHelpers
import ACMaxConjecture.SmallCases.N20.Deg5ZSlots
import ACMaxConjecture.SmallCases.N20.Deg5SameZ
import ACMaxConjecture.SmallCases.N20.Deg5Pack

/-! # The `(10,42)` tie-world `Z`-leaf extraction (`n = 20`, deg-5 corner) -/
namespace ACMax
open scoped Classical

namespace N20

set_option maxHeartbeats 1000000 in
/-- **Tie-world `Z`-leaf extraction, deg-`5` profile `(10,8,42)` (`n = 20`).**  Unlike the `n = 19`
profile `(9,8,38)`, whose iso-cap ledger ties exactly (`2·7 + 5·2 = 24 = 3·8`, an empty world),
at `n = 20` the cap total `2·8 + 5·2 = 26` exceeds the iso-ledger `24` by `2`, so the 6-tuple
witness is extracted constructively: either some `M`-end has both hub-neighbours of degree `4`
(the same-`z` pair plus an exclusion count over the `8` deg-`4` hubs, sharpened by the poor
same-`z` hub being itself `z`-adjacent), or both `M`-ends meet deg-`5` hubs — forcing every
deg-`4` hub to iso-degree exactly `2` — and the deg-`4` partner of an `M`-end packs. -/
theorem zleaf_extract_tie_938_twenty (G : SimpleGraph (Fin 20))
    (Hub Iso : Finset (Fin 20))
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdisj : Disjoint Hub Iso) (hsum18 : Hub.card + Iso.card = 18)
    (hdeg3 : ∀ v : Fin 20, 3 ≤ G.degree v) (hisodeg3 : ∀ t ∈ Iso, G.degree t = 3)
    (hleak : ∑ h ∈ Hub, (G.neighborFinset h ∩ (Finset.univ \ (Hub ∪ Iso))).card ≤ 4)
    (hdeg : ∀ h ∈ Hub, 4 ≤ G.degree h) (hdeg5 : ∀ h ∈ Hub, G.degree h ≤ 5)
    (hHub : Hub.card = 10) (hIso : Iso.card = 8)
    (hdsum : ∑ w ∈ Hub, G.degree w = 42)
    (hT : ¬∃ x y z : Fin 20, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 11)
    (hC4 : ¬∃ a b c d : Fin 20, ({a, b, c, d} : Finset (Fin 20)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (_hK23 : ¬∃ a b c d e : Fin 20, ({a, b, c, d, e} : Finset (Fin 20)).card = 5 ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
      G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 19)
    (_hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hno2hub : ¬∃ h₁ h₂ : Fin 20, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card)
    (hnorich : ∀ h ∈ Hub, G.degree h = 4 → (G.neighborFinset h ∩ Iso).card ≤ 2) :
    ∃ h₁ h₂ a b c z : Fin 20, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧ G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧
      a ∈ Iso ∧ b ∈ Iso ∧ c ∈ Iso ∧
      z ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 20)) ∧
      G.Adj a h₁ ∧ G.Adj b h₁ ∧ G.Adj c h₂ ∧ G.Adj z h₂ ∧
      ¬G.Adj h₁ h₂ ∧ ¬G.Adj h₁ c ∧ ¬G.Adj h₁ z ∧
      ¬G.Adj a h₂ ∧ ¬G.Adj b h₂ ∧ a ≠ b := by
  classical
  -- === Degree partition: 8 deg-4 hubs, 2 deg-5 hubs. ===
  have hdeg45 : ∀ h ∈ Hub, G.degree h = 4 ∨ G.degree h = 5 := by
    intro h hh; have h1 := hdeg h hh; have h2 := hdeg5 h hh; omega
  set D4 : Finset (Fin 20) := Hub.filter (fun h => G.degree h = 4) with hD4def
  set D5 : Finset (Fin 20) := Hub.filter (fun h => ¬ G.degree h = 4) with hD5def
  have hD4sub : D4 ⊆ Hub := by rw [hD4def]; exact Finset.filter_subset _ _
  have hD5sub : D5 ⊆ Hub := by rw [hD5def]; exact Finset.filter_subset _ _
  have hD4deg4 : ∀ h ∈ D4, G.degree h = 4 := by
    intro h hh; rw [hD4def, Finset.mem_filter] at hh; exact hh.2
  have hD5deg5 : ∀ h ∈ D5, G.degree h = 5 := by
    intro h hh; rw [hD5def, Finset.mem_filter] at hh
    rcases hdeg45 h hh.1 with h4 | h5
    · exact absurd h4 hh.2
    · exact h5
  have hcardpart : D4.card + D5.card = 10 := by
    rw [hD4def, hD5def, Finset.card_filter_add_card_filter_not]; exact hHub
  have hsumdeg : (∑ h ∈ D4, G.degree h) + (∑ h ∈ D5, G.degree h) = 42 := by
    rw [hD4def, hD5def, Finset.sum_filter_add_sum_filter_not]; exact hdsum
  have hsum4 : (∑ h ∈ D4, G.degree h) = 4 * D4.card := by
    calc (∑ h ∈ D4, G.degree h) = ∑ _h ∈ D4, 4 :=
          Finset.sum_congr rfl fun h hh => hD4deg4 h hh
      _ = 4 * D4.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have hsum5 : (∑ h ∈ D5, G.degree h) = 5 * D5.card := by
    calc (∑ h ∈ D5, G.degree h) = ∑ _h ∈ D5, 5 :=
          Finset.sum_congr rfl fun h hh => hD5deg5 h hh
      _ = 5 * D5.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  rw [hsum4, hsum5] at hsumdeg
  have hD4card : D4.card = 8 := by omega
  have hD5card : D5.card = 2 := by omega
  -- === Iso-degree ledger: `∑_Hub isoDeg = 24`, so `∑_D4 isoDeg ≥ 14`. ===
  have hisosum24 : ∑ h ∈ Hub, (G.neighborFinset h ∩ Iso).card = 24 := by
    have hc : ∑ w ∈ Iso, (G.neighborFinset w ∩ Hub).card = ∑ _w ∈ Iso, 3 :=
      Finset.sum_congr rfl (fun w hw => hiso3 w hw)
    rw [cross_count_twenty G Hub Iso, hc, Finset.sum_const, hIso, smul_eq_mul]
  have hisosplit : (∑ h ∈ D4, (G.neighborFinset h ∩ Iso).card)
      + (∑ h ∈ D5, (G.neighborFinset h ∩ Iso).card) = 24 := by
    rw [hD4def, hD5def, Finset.sum_filter_add_sum_filter_not]; exact hisosum24
  have hD5isole : ∀ h ∈ D5, (G.neighborFinset h ∩ Iso).card ≤ 5 := by
    intro h hh
    calc (G.neighborFinset h ∩ Iso).card ≤ (G.neighborFinset h).card :=
          Finset.card_le_card Finset.inter_subset_left
      _ = G.degree h := G.card_neighborFinset_eq_degree h
      _ = 5 := hD5deg5 h hh
  have hD4isoge : 14 ≤ ∑ h ∈ D4, (G.neighborFinset h ∩ Iso).card := by
    have hle : (∑ h ∈ D5, (G.neighborFinset h ∩ Iso).card) ≤ 10 := by
      calc (∑ h ∈ D5, (G.neighborFinset h ∩ Iso).card) ≤ ∑ _h ∈ D5, 5 :=
            Finset.sum_le_sum hD5isole
        _ = 10 := by rw [Finset.sum_const, hD5card, smul_eq_mul]
    omega
  -- === The iso-poor deg-4 hubs (`isoDeg ≤ 1`): at most two of them. ===
  set poor : Finset (Fin 20) :=
    D4.filter (fun h => (G.neighborFinset h ∩ Iso).card ≤ 1) with hpoordef
  have hpoorcard : poor.card
      = ∑ h ∈ D4, (if (G.neighborFinset h ∩ Iso).card ≤ 1 then 1 else 0) := by
    rw [hpoordef, Finset.card_filter]
  have hkey16 : (∑ h ∈ D4, (G.neighborFinset h ∩ Iso).card) + poor.card ≤ 16 := by
    rw [hpoorcard, ← Finset.sum_add_distrib]
    calc (∑ h ∈ D4, ((G.neighborFinset h ∩ Iso).card
            + if (G.neighborFinset h ∩ Iso).card ≤ 1 then 1 else 0))
          ≤ ∑ _h ∈ D4, 2 := Finset.sum_le_sum fun h hh => by
            by_cases hc : (G.neighborFinset h ∩ Iso).card ≤ 1
            · rw [if_pos hc]; omega
            · rw [if_neg hc]; have := hnorich h (hD4sub hh) (hD4deg4 h hh); omega
      _ = 16 := by rw [Finset.sum_const, hD4card, smul_eq_mul]
  have hm_le2 : poor.card ≤ 2 := by omega
  have hm_of_zero : ∀ a ∈ D4, (G.neighborFinset a ∩ Iso).card = 0 → poor.card ≤ 1 := by
    intro a haD4 hia0
    have hsub : poor ⊆ {a} := by
      intro h' hh'
      rw [Finset.mem_singleton]
      by_contra hne'
      rw [hpoordef, Finset.mem_filter] at hh'
      obtain ⟨hh'D4, hih'1⟩ := hh'
      have hh'Ea : h' ∈ D4.erase a := Finset.mem_erase.mpr ⟨hne', hh'D4⟩
      have hs1 : (G.neighborFinset a ∩ Iso).card
          + (∑ h ∈ D4.erase a, (G.neighborFinset h ∩ Iso).card)
          = ∑ h ∈ D4, (G.neighborFinset h ∩ Iso).card :=
        Finset.add_sum_erase D4 (fun h => (G.neighborFinset h ∩ Iso).card) haD4
      have hs2 : (G.neighborFinset h' ∩ Iso).card
          + (∑ h ∈ (D4.erase a).erase h', (G.neighborFinset h ∩ Iso).card)
          = ∑ h ∈ D4.erase a, (G.neighborFinset h ∩ Iso).card :=
        Finset.add_sum_erase (D4.erase a) (fun h => (G.neighborFinset h ∩ Iso).card) hh'Ea
      have hcard6 : ((D4.erase a).erase h').card = 6 := by
        rw [Finset.card_erase_of_mem hh'Ea, Finset.card_erase_of_mem haD4, hD4card]
      have hrest2 : (∑ h ∈ (D4.erase a).erase h', (G.neighborFinset h ∩ Iso).card) ≤ 12 := by
        calc (∑ h ∈ (D4.erase a).erase h', (G.neighborFinset h ∩ Iso).card)
              ≤ ∑ _h ∈ (D4.erase a).erase h', 2 := Finset.sum_le_sum fun h hh => by
                have hhD4 : h ∈ D4 := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hh)
                exact hnorich h (hD4sub hhD4) (hD4deg4 h hhD4)
          _ = 12 := by rw [Finset.sum_const, hcard6, smul_eq_mul]
      omega
    calc poor.card ≤ ({a} : Finset (Fin 20)).card := Finset.card_le_card hsub
      _ = 1 := Finset.card_singleton a
  -- === The `Z`-slots and their hub pairs. ===
  obtain ⟨z₁, z₂, -, hz1Z, hz2Z, -, -, hnohub⟩ :=
    zslot_skeleton_deg5_twenty G Hub Iso hiso3 hdisj hsum18 hdeg3 hisodeg3 hleak hdeg5 hT
  have hzf := zfacts_deg5_twenty G Hub Iso hiso3 hdisj hsum18 hdeg3 hisodeg3 hleak
  obtain ⟨-, hz1hub2, -⟩ := hzf z₁ hz1Z
  obtain ⟨-, hz2hub2, -⟩ := hzf z₂ hz2Z
  -- === Dichotomy: do both `M`-ends meet a deg-5 hub? ===
  by_cases hbad : (∃ r ∈ Hub, G.degree r = 5 ∧ G.Adj r z₁) ∧
      (∃ r ∈ Hub, G.degree r = 5 ∧ G.Adj r z₂)
  · -- === Case B: both `M`-ends meet deg-5 hubs; all deg-4 hubs have iso-degree exactly 2. ===
    obtain ⟨⟨r₁, hr₁Hub, hr₁5, hr₁z⟩, ⟨r₂, hr₂Hub, hr₂5, hr₂z⟩⟩ := hbad
    have hr12 : r₁ ≠ r₂ := by
      rintro rfl
      exact hnohub r₁ hr₁Hub ⟨hr₁z, hr₂z⟩
    have hr₁D5 : r₁ ∈ D5 := by
      rw [hD5def, Finset.mem_filter]; exact ⟨hr₁Hub, by omega⟩
    have hr₂D5 : r₂ ∈ D5 := by
      rw [hD5def, Finset.mem_filter]; exact ⟨hr₂Hub, by omega⟩
    have hsubD5 : ({r₁, r₂} : Finset (Fin 20)) ⊆ D5 := by
      intro x hx
      rw [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hr₁D5
      · exact hr₂D5
    have hpair2 : ({r₁, r₂} : Finset (Fin 20)).card = 2 := Finset.card_pair hr12
    have hD5eq : D5 = {r₁, r₂} :=
      (Finset.eq_of_subset_of_card_le hsubD5 (by rw [hpair2]; omega)).symm
    -- Each `M`-end-adjacent deg-5 hub loses an iso-slot: `isoDeg ≤ 4`.
    have hziso4 : ∀ r z' : Fin 20, r ∈ Hub → G.degree r = 5 → G.Adj r z' →
        z' ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 20)) →
        (G.neighborFinset r ∩ Iso).card ≤ 4 := by
      intro r z' _hrHub hr5 hrz hz'Z
      have hsp := nbr_split_three_twenty G Hub Iso hdisj r
      have hzmem : z' ∈ G.neighborFinset r ∩ (Finset.univ \ (Hub ∪ Iso)) :=
        Finset.mem_inter.mpr ⟨(G.mem_neighborFinset r z').mpr hrz, hz'Z⟩
      have hz1' : 1 ≤ (G.neighborFinset r ∩ (Finset.univ \ (Hub ∪ Iso))).card :=
        Finset.card_pos.mpr ⟨z', hzmem⟩
      rw [hr5] at hsp
      omega
    have hall2 : ∀ h ∈ D4, (G.neighborFinset h ∩ Iso).card = 2 := by
      intro h hh
      by_contra hne
      have hle1 : (G.neighborFinset h ∩ Iso).card ≤ 1 := by
        have := hnorich h (hD4sub hh) (hD4deg4 h hh); omega
      have hs1 : (G.neighborFinset h ∩ Iso).card
          + (∑ h' ∈ D4.erase h, (G.neighborFinset h' ∩ Iso).card)
          = ∑ h' ∈ D4, (G.neighborFinset h' ∩ Iso).card :=
        Finset.add_sum_erase D4 (fun h' => (G.neighborFinset h' ∩ Iso).card) hh
      have hcard7 : (D4.erase h).card = 7 := by
        rw [Finset.card_erase_of_mem hh, hD4card]
      have hrest : (∑ h' ∈ D4.erase h, (G.neighborFinset h' ∩ Iso).card) ≤ 14 := by
        calc (∑ h' ∈ D4.erase h, (G.neighborFinset h' ∩ Iso).card)
              ≤ ∑ _h' ∈ D4.erase h, 2 := Finset.sum_le_sum fun h' hh' => by
                have hhD4 : h' ∈ D4 := Finset.mem_of_mem_erase hh'
                exact hnorich h' (hD4sub hhD4) (hD4deg4 h' hhD4)
          _ = 14 := by rw [Finset.sum_const, hcard7, smul_eq_mul]
      have hD5sum8 : (∑ h' ∈ D5, (G.neighborFinset h' ∩ Iso).card) ≤ 8 := by
        rw [hD5eq, Finset.sum_pair hr12]
        have h1 := hziso4 r₁ z₁ hr₁Hub hr₁5 hr₁z hz1Z
        have h2 := hziso4 r₂ z₂ hr₂Hub hr₂5 hr₂z hz2Z
        omega
      omega
    -- The second hub-neighbour `p` of `z₁` is deg-4 with iso-degree exactly 2.
    obtain ⟨u, v, huv, huveq⟩ := Finset.card_eq_two.mp hz1hub2
    have hr₁mem : r₁ ∈ G.neighborFinset z₁ ∩ Hub :=
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset z₁ r₁).mpr hr₁z.symm, hr₁Hub⟩
    have hr₁uv : r₁ = u ∨ r₁ = v := by
      rw [huveq, Finset.mem_insert, Finset.mem_singleton] at hr₁mem
      exact hr₁mem
    obtain ⟨p, hpmem, hpr₁⟩ : ∃ p : Fin 20, p ∈ G.neighborFinset z₁ ∩ Hub ∧ p ≠ r₁ := by
      rcases hr₁uv with h | h
      · refine ⟨v, ?_, ?_⟩
        · rw [huveq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self v)
        · rw [← h] at huv; exact huv.symm
      · refine ⟨u, ?_, ?_⟩
        · rw [huveq]; exact Finset.mem_insert_self u {v}
        · rw [← h] at huv; exact huv
    obtain ⟨hpadj', hpHub⟩ := Finset.mem_inter.mp hpmem
    have hpadj : G.Adj z₁ p := (G.mem_neighborFinset z₁ p).mp hpadj'
    have hpdeg : G.degree p = 4 := by
      rcases hdeg45 p hpHub with h4 | h5
      · exact h4
      · exfalso
        have hpD5 : p ∈ D5 := by
          rw [hD5def, Finset.mem_filter]; exact ⟨hpHub, by omega⟩
        rw [hD5eq, Finset.mem_insert, Finset.mem_singleton] at hpD5
        rcases hpD5 with h | h
        · exact hpr₁ h
        · rw [h] at hpadj hpHub
          exact hnohub r₂ hpHub ⟨hpadj.symm, hr₂z⟩
    have hpD4 : p ∈ D4 := by rw [hD4def, Finset.mem_filter]; exact ⟨hpHub, hpdeg⟩
    have hpiso2 : (G.neighborFinset p ∩ Iso).card = 2 := hall2 p hpD4
    have hphub1 : (G.neighborFinset p ∩ Hub).card ≤ 1 := by
      have hsp := nbr_split_three_twenty G Hub Iso hdisj p
      have hzmem : z₁ ∈ G.neighborFinset p ∩ (Finset.univ \ (Hub ∪ Iso)) :=
        Finset.mem_inter.mpr ⟨(G.mem_neighborFinset p z₁).mpr hpadj.symm, hz1Z⟩
      have hz1' : 1 ≤ (G.neighborFinset p ∩ (Finset.univ \ (Hub ∪ Iso))).card :=
        Finset.card_pos.mpr ⟨z₁, hzmem⟩
      rw [hpdeg] at hsp
      omega
    have hB3card : ((G.neighborFinset p ∩ Iso).biUnion
        (fun t => (G.neighborFinset t ∩ Hub).erase p)).card
        ≤ 2 * (G.neighborFinset p ∩ Iso).card := by
      calc ((G.neighborFinset p ∩ Iso).biUnion
            (fun t => (G.neighborFinset t ∩ Hub).erase p)).card
          ≤ ∑ t ∈ G.neighborFinset p ∩ Iso, ((G.neighborFinset t ∩ Hub).erase p).card :=
            Finset.card_biUnion_le
        _ ≤ ∑ t ∈ G.neighborFinset p ∩ Iso, 2 := Finset.sum_le_sum fun t ht => by
              have htIso : t ∈ Iso := (Finset.mem_inter.mp ht).2
              have h3card : (G.neighborFinset t ∩ Hub).card = 3 := hiso3 t htIso
              have ht2 : t ∈ G.neighborFinset p := (Finset.mem_inter.mp ht).1
              have hpt : p ∈ G.neighborFinset t := by
                rw [G.mem_neighborFinset] at ht2 ⊢; exact ht2.symm
              have hpmem' : p ∈ G.neighborFinset t ∩ Hub :=
                Finset.mem_inter.mpr ⟨hpt, hpHub⟩
              have h1 := Finset.card_erase_of_mem hpmem'
              rw [h3card] at h1; omega
        _ = 2 * (G.neighborFinset p ∩ Iso).card := by
              rw [Finset.sum_const, smul_eq_mul, mul_comm]
    set Q : Fin 20 → Prop := fun x => G.Adj x z₁ ∨ G.Adj x p ∨
        (G.neighborFinset x ∩ G.neighborFinset p ∩ Iso) ≠ ∅ ∨
        (G.neighborFinset x ∩ Iso).card ≤ 1 with hQdef
    have hbadsub : D4.filter Q ⊆
        G.neighborFinset z₁ ∩ Hub ∪ G.neighborFinset p ∩ Hub ∪
          (G.neighborFinset p ∩ Iso).biUnion (fun t => (G.neighborFinset t ∩ Hub).erase p) := by
      intro x hx
      rw [Finset.mem_filter] at hx
      obtain ⟨hxD4, hxQ⟩ := hx
      simp only [hQdef] at hxQ
      have hxHub : x ∈ Hub := hD4sub hxD4
      rcases hxQ with h1 | h2 | h3 | h4
      · exact Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset z₁ x).mpr h1.symm, hxHub⟩))
      · exact Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset p x).mpr h2.symm, hxHub⟩))
      · rw [← Finset.nonempty_iff_ne_empty] at h3
        obtain ⟨t, ht⟩ := h3
        rw [Finset.mem_inter, Finset.mem_inter, G.mem_neighborFinset,
          G.mem_neighborFinset] at ht
        obtain ⟨⟨hxt, hpt⟩, htIso⟩ := ht
        by_cases hxp : x = p
        · exact Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_inter.mpr
              ⟨(G.mem_neighborFinset z₁ x).mpr (by rw [hxp]; exact hpadj), hxHub⟩))
        · refine Finset.mem_union_right _ ?_
          refine Finset.mem_biUnion.mpr ⟨t, Finset.mem_inter.mpr
            ⟨(G.mem_neighborFinset p t).mpr hpt, htIso⟩, ?_⟩
          rw [Finset.mem_erase]
          exact ⟨hxp, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset t x).mpr hxt.symm, hxHub⟩⟩
      · exact absurd (hall2 x hxD4) (by omega)
    have hbadcard : (D4.filter Q).card ≤ 7 := by
      have hc := Finset.card_le_card hbadsub
      have hu2 := Finset.card_union_le (G.neighborFinset z₁ ∩ Hub ∪ G.neighborFinset p ∩ Hub)
        ((G.neighborFinset p ∩ Iso).biUnion (fun t => (G.neighborFinset t ∩ Hub).erase p))
      have hu3 := Finset.card_union_le (G.neighborFinset z₁ ∩ Hub) (G.neighborFinset p ∩ Hub)
      omega
    have hcardsum : (D4.filter Q).card + (D4.filter (fun a => ¬ Q a)).card = 8 := by
      rw [Finset.card_filter_add_card_filter_not, hD4card]
    have hgoodne : (D4.filter (fun a => ¬ Q a)).Nonempty := by
      rw [← Finset.card_pos]; omega
    obtain ⟨x, hx⟩ := hgoodne
    rw [Finset.mem_filter] at hx
    obtain ⟨hxD4, hxnQ⟩ := hx
    simp only [hQdef] at hxnQ
    push Not at hxnQ
    obtain ⟨hxnz, hxnp, hxshare, hxiso2⟩ := hxnQ
    have hxHub : x ∈ Hub := hD4sub hxD4
    have hxne : x ≠ p := by
      rintro rfl
      rw [Finset.inter_self, ← Finset.card_eq_zero] at hxshare
      omega
    exact zleaf_pack_share0_twenty G Hub Iso hiso3 hisodeg3 x p z₁ hxHub hpHub
      (hD4deg4 x hxD4) hpdeg hz1Z hxne hxnp (by omega) (by omega) hxshare hpadj hxnz
  · -- === Case A: some `M`-end has both hub-neighbours deg-4. ===
    obtain ⟨z, hzZ, hzhub2, hzall4⟩ :
        ∃ z : Fin 20, z ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 20)) ∧
          (G.neighborFinset z ∩ Hub).card = 2 ∧
          ∀ h ∈ Hub, G.Adj h z → G.degree h = 4 := by
      rw [not_and_or] at hbad
      rcases hbad with h | h
      · push Not at h
        refine ⟨z₁, hz1Z, hz1hub2, fun r hr hrz => ?_⟩
        rcases hdeg45 r hr with h4 | h5
        · exact h4
        · exact absurd hrz (h r hr h5)
      · push Not at h
        refine ⟨z₂, hz2Z, hz2hub2, fun r hr hrz => ?_⟩
        rcases hdeg45 r hr with h4 | h5
        · exact h4
        · exact absurd hrz (h r hr h5)
    obtain ⟨p, q, hpqne, hpqeq⟩ := Finset.card_eq_two.mp hzhub2
    have hpmem : p ∈ G.neighborFinset z ∩ Hub := by
      rw [hpqeq]; exact Finset.mem_insert_self p {q}
    have hqmem : q ∈ G.neighborFinset z ∩ Hub := by
      rw [hpqeq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self q)
    obtain ⟨hpadj', hpHub⟩ := Finset.mem_inter.mp hpmem
    obtain ⟨hqadj', hqHub⟩ := Finset.mem_inter.mp hqmem
    have hpadj : G.Adj z p := (G.mem_neighborFinset z p).mp hpadj'
    have hqadj : G.Adj z q := (G.mem_neighborFinset z q).mp hqadj'
    have hpdeg : G.degree p = 4 := hzall4 p hpHub hpadj.symm
    have hqdeg : G.degree q = 4 := hzall4 q hqHub hqadj.symm
    have hpD4 : p ∈ D4 := by rw [hD4def, Finset.mem_filter]; exact ⟨hpHub, hpdeg⟩
    have hqD4 : q ∈ D4 := by rw [hD4def, Finset.mem_filter]; exact ⟨hqHub, hqdeg⟩
    -- The same-`z` pair: non-adjacent, one iso-poor.
    obtain ⟨-, -, hpoor_or⟩ :=
      same_z_pair_deg5_twenty G Hub Iso hiso3 hdisj hsum18 hdeg3 hisodeg3 hleak hT hC4
        hno2hub z p q hzZ hpHub hqHub hpdeg hqdeg hpqne hpadj hqadj
    have hpq_iso_ge2 :
        2 ≤ (G.neighborFinset p ∩ Iso).card + (G.neighborFinset q ∩ Iso).card := by
      have he1 : (G.neighborFinset p ∩ Iso).card
          + (∑ h ∈ D4.erase p, (G.neighborFinset h ∩ Iso).card)
          = ∑ h ∈ D4, (G.neighborFinset h ∩ Iso).card :=
        Finset.add_sum_erase D4 (fun h => (G.neighborFinset h ∩ Iso).card) hpD4
      have hqEp : q ∈ D4.erase p := Finset.mem_erase.mpr ⟨hpqne.symm, hqD4⟩
      have he2 : (G.neighborFinset q ∩ Iso).card
          + (∑ h ∈ (D4.erase p).erase q, (G.neighborFinset h ∩ Iso).card)
          = ∑ h ∈ D4.erase p, (G.neighborFinset h ∩ Iso).card :=
        Finset.add_sum_erase (D4.erase p) (fun h => (G.neighborFinset h ∩ Iso).card) hqEp
      have hcard6 : ((D4.erase p).erase q).card = 6 := by
        rw [Finset.card_erase_of_mem hqEp, Finset.card_erase_of_mem hpD4, hD4card]
      have hrest : (∑ h ∈ (D4.erase p).erase q, (G.neighborFinset h ∩ Iso).card) ≤ 12 := by
        calc (∑ h ∈ (D4.erase p).erase q, (G.neighborFinset h ∩ Iso).card)
              ≤ ∑ _h ∈ (D4.erase p).erase q, 2 := Finset.sum_le_sum fun h hh => by
                have hhD4 : h ∈ D4 := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hh)
                exact hnorich h (hD4sub hhD4) (hD4deg4 h hhD4)
          _ = 12 := by rw [Finset.sum_const, hcard6, smul_eq_mul]
      omega
    -- Choose `h₂ ∈ {p, q}` with `isoDeg ≥ 1` and `isoDeg + |poor| ≤ 3`; the poor witness
    -- `w ∈ {p, q}` is itself `z`-adjacent, so it is absorbed by the `N(z) ∩ Hub` count.
    have hchoose_of_poor : ∀ a b : Fin 20, a ∈ Hub → b ∈ Hub → G.degree a = 4 →
        G.degree b = 4 → G.Adj z a → G.Adj z b → (G.neighborFinset a ∩ Iso).card ≤ 1 →
        2 ≤ (G.neighborFinset a ∩ Iso).card + (G.neighborFinset b ∩ Iso).card →
        a ∈ D4 → b ∈ D4 →
        ∃ h₂ w : Fin 20, h₂ ∈ Hub ∧ G.degree h₂ = 4 ∧ G.Adj z h₂ ∧
          1 ≤ (G.neighborFinset h₂ ∩ Iso).card ∧ w ∈ poor ∧ G.Adj z w ∧
          (G.neighborFinset h₂ ∩ Iso).card + poor.card ≤ 3 := by
      intro a b haHub hbHub hda hdb hza hzb hia1 hsum2 haD4 _hbD4
      have hapoor : a ∈ poor := by
        rw [hpoordef, Finset.mem_filter]; exact ⟨haD4, hia1⟩
      by_cases hia0 : (G.neighborFinset a ∩ Iso).card = 0
      · have hib2 : (G.neighborFinset b ∩ Iso).card = 2 := by
          have hble := hnorich b hbHub hdb; omega
        have hm1 : poor.card ≤ 1 := hm_of_zero a haD4 hia0
        exact ⟨b, a, hbHub, hdb, hzb, by omega, hapoor, hza, by omega⟩
      · exact ⟨a, a, haHub, hda, hza, by omega, hapoor, hza, by omega⟩
    obtain ⟨h₂, w, hh₂Hub, hh₂deg, hzh₂, hh₂iso1, hwpoor, hzw, hh₂summ⟩ :
        ∃ h₂ w : Fin 20, h₂ ∈ Hub ∧ G.degree h₂ = 4 ∧ G.Adj z h₂ ∧
          1 ≤ (G.neighborFinset h₂ ∩ Iso).card ∧ w ∈ poor ∧ G.Adj z w ∧
          (G.neighborFinset h₂ ∩ Iso).card + poor.card ≤ 3 := by
      rcases hpoor_or with hp1 | hq1
      · exact hchoose_of_poor p q hpHub hqHub hpdeg hqdeg hpadj hqadj hp1 hpq_iso_ge2
          hpD4 hqD4
      · refine hchoose_of_poor q p hqHub hpHub hqdeg hpdeg hqadj hpadj hq1 ?_ hqD4 hpD4
        omega
    -- The exclusion count: a fresh deg-4 hub avoiding `z`, `h₂`, `h₂`'s twins, and `poor`.
    have hzInterZ : z ∈ G.neighborFinset h₂ ∩ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 20)) :=
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset h₂ z).mpr hzh₂.symm, hzZ⟩
    have hzDeg1 :
        1 ≤ (G.neighborFinset h₂ ∩ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 20))).card :=
      Finset.card_pos.mpr ⟨z, hzInterZ⟩
    have hhubDeg : (G.neighborFinset h₂ ∩ Hub).card
        ≤ 3 - (G.neighborFinset h₂ ∩ Iso).card := by
      have h := nbr_split_three_twenty G Hub Iso hdisj h₂
      rw [hh₂deg] at h; omega
    have hB3card : ((G.neighborFinset h₂ ∩ Iso).biUnion
        (fun t => (G.neighborFinset t ∩ Hub).erase h₂)).card
        ≤ 2 * (G.neighborFinset h₂ ∩ Iso).card := by
      calc ((G.neighborFinset h₂ ∩ Iso).biUnion
            (fun t => (G.neighborFinset t ∩ Hub).erase h₂)).card
          ≤ ∑ t ∈ G.neighborFinset h₂ ∩ Iso, ((G.neighborFinset t ∩ Hub).erase h₂).card :=
            Finset.card_biUnion_le
        _ ≤ ∑ t ∈ G.neighborFinset h₂ ∩ Iso, 2 := Finset.sum_le_sum fun t ht => by
              have htIso : t ∈ Iso := (Finset.mem_inter.mp ht).2
              have h3card : (G.neighborFinset t ∩ Hub).card = 3 := hiso3 t htIso
              have ht2 : t ∈ G.neighborFinset h₂ := (Finset.mem_inter.mp ht).1
              have hh₂t : h₂ ∈ G.neighborFinset t := by
                rw [G.mem_neighborFinset] at ht2 ⊢; exact ht2.symm
              have hh₂mem : h₂ ∈ G.neighborFinset t ∩ Hub :=
                Finset.mem_inter.mpr ⟨hh₂t, hh₂Hub⟩
              have h1 := Finset.card_erase_of_mem hh₂mem
              rw [h3card] at h1; omega
        _ = 2 * (G.neighborFinset h₂ ∩ Iso).card := by
              rw [Finset.sum_const, smul_eq_mul, mul_comm]
    set Q : Fin 20 → Prop := fun x => G.Adj x z ∨ G.Adj x h₂ ∨
        (G.neighborFinset x ∩ G.neighborFinset h₂ ∩ Iso) ≠ ∅ ∨
        (G.neighborFinset x ∩ Iso).card ≤ 1 with hQdef
    have hbadsub : D4.filter Q ⊆
        G.neighborFinset z ∩ Hub ∪ G.neighborFinset h₂ ∩ Hub ∪
          (G.neighborFinset h₂ ∩ Iso).biUnion (fun t => (G.neighborFinset t ∩ Hub).erase h₂) ∪
          poor.erase w := by
      intro x hx
      rw [Finset.mem_filter] at hx
      obtain ⟨hxD4, hxQ⟩ := hx
      simp only [hQdef] at hxQ
      have hxHub : x ∈ Hub := hD4sub hxD4
      rcases hxQ with h1 | h2 | h3 | h4
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset z x).mpr h1.symm, hxHub⟩)))
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset h₂ x).mpr h2.symm, hxHub⟩)))
      · rw [← Finset.nonempty_iff_ne_empty] at h3
        obtain ⟨t, ht⟩ := h3
        rw [Finset.mem_inter, Finset.mem_inter, G.mem_neighborFinset,
          G.mem_neighborFinset] at ht
        obtain ⟨⟨hxt, hh₂t⟩, htIso⟩ := ht
        by_cases hxh₂ : x = h₂
        · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_inter.mpr
              ⟨(G.mem_neighborFinset z x).mpr (by rw [hxh₂]; exact hzh₂), hxHub⟩)))
        · refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
          refine Finset.mem_biUnion.mpr ⟨t, Finset.mem_inter.mpr
            ⟨(G.mem_neighborFinset h₂ t).mpr hh₂t, htIso⟩, ?_⟩
          rw [Finset.mem_erase]
          exact ⟨hxh₂, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset t x).mpr hxt.symm, hxHub⟩⟩
      · by_cases hxw : x = w
        · refine Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_inter.mpr ⟨?_, hxHub⟩)))
          rw [G.mem_neighborFinset, hxw]
          exact hzw
        · refine Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hxw, ?_⟩)
          rw [hpoordef, Finset.mem_filter]
          exact ⟨hxD4, h4⟩
    have hwcard : (poor.erase w).card = poor.card - 1 := Finset.card_erase_of_mem hwpoor
    have hpoorpos : 1 ≤ poor.card := Finset.card_pos.mpr ⟨w, hwpoor⟩
    have hbadcard : (D4.filter Q).card ≤ 7 := by
      have hc := Finset.card_le_card hbadsub
      have hu1 := Finset.card_union_le
        (G.neighborFinset z ∩ Hub ∪ G.neighborFinset h₂ ∩ Hub ∪
          (G.neighborFinset h₂ ∩ Iso).biUnion (fun t => (G.neighborFinset t ∩ Hub).erase h₂))
        (poor.erase w)
      have hu2 := Finset.card_union_le (G.neighborFinset z ∩ Hub ∪ G.neighborFinset h₂ ∩ Hub)
        ((G.neighborFinset h₂ ∩ Iso).biUnion (fun t => (G.neighborFinset t ∩ Hub).erase h₂))
      have hu3 := Finset.card_union_le (G.neighborFinset z ∩ Hub) (G.neighborFinset h₂ ∩ Hub)
      omega
    have hcardsum : (D4.filter Q).card + (D4.filter (fun a => ¬ Q a)).card = 8 := by
      rw [Finset.card_filter_add_card_filter_not, hD4card]
    have hgoodne : (D4.filter (fun a => ¬ Q a)).Nonempty := by
      rw [← Finset.card_pos]; omega
    obtain ⟨x, hx⟩ := hgoodne
    rw [Finset.mem_filter] at hx
    obtain ⟨hxD4, hxnQ⟩ := hx
    simp only [hQdef] at hxnQ
    push Not at hxnQ
    obtain ⟨hxnz, hxnh₂, hxshare, hxiso2⟩ := hxnQ
    have hxHub : x ∈ Hub := hD4sub hxD4
    have hxne : x ≠ h₂ := by
      rintro rfl
      rw [Finset.inter_self, ← Finset.card_eq_zero] at hxshare
      omega
    exact zleaf_pack_share0_twenty G Hub Iso hiso3 hisodeg3 x h₂ z hxHub hh₂Hub
      (hD4deg4 x hxD4) hh₂deg hzZ hxne hxnh₂ (by omega) hh₂iso1 hxshare hzh₂ hxnz

end N20

end ACMax
