import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N20.Deg5ZSlots
import ACMaxConjecture.SmallCases.N20.Deg5Pack
import ACMaxConjecture.SmallCases.N20.TwoHubSelect

/-!
# The anchor-saturated `|R| = 4` kill for the `(11,7,45)` deg-5 corner (`n = 20`)

Consumes the right disjunct of `rich_count_1041_twenty`: exactly `4` rich degree-`4` hubs
(isoDeg `≥ 2`), the unique degree-`5` anchor `f` iso-saturated (`isoDeg f = 5`, hence
`N(f) ⊆ Iso`, so `f` avoids every hub and both `M`-ends), and every non-rich degree-`4` hub
of isoDeg exactly `1`.  The rich ledger `∑_R isoDeg = 21 − 5 − 6 = 10` forces a rich hub `g`
of isoDeg `≥ 3`; both `M`-edge endpoints carry two degree-`4` slot hubs (`f` meets no
`Z`-vertex, so `f` is never a slot).

* If a **second** isoDeg-`≥ 3` rich hub `g₃` exists, `hshare + hno2hub` force `g ∼ g₃`, and
  the degree budget locks both (all remaining neighbours in `Iso`).  Any slot hub `s` then
  meets the side conditions for both: a rich `s` feeds `zleaf_pack_rich_twenty` (`h₁ = g`); a
  `1`-poor `s` whose twin avoids `g` (resp. `g₃`) feeds `zleaf_pack_share0_twenty`; a twin met
  by both `g` and `g₃` closes the good triangle `g–g₃–t` at `4 + 4 + 3 ≤ 11`, killed by `hT`.
* Otherwise `g` is the **unique** isoDeg-`≥ 3` rich hub, the ledger pins `isoDeg g = 4`
  (`10 = isoDeg g + 3·2`), and `N(g) ⊆ Iso`.  If every slot were blocked, all four would be
  `1`-poor with their twins inside `T = N(g)`, and the `T`-incidence count reads
  `2 (f, saturation) + 3 (the other rich hubs, one shared twin each via hno2hub) + 4 (slots)
  = 9 > 8 = 2|T|` — impossible, so some slot feeds a packer.

Every branch lands in `two_hub_zleaf_gen_twenty`, producing the `TwoHubConfig` disjunct.
-/

namespace ACMax
open scoped Classical

namespace N20

set_option maxHeartbeats 1000000 in
/-- **The anchor-saturated `|R| = 4` kill for the `(11,7,45)` corner (`n = 20`).**  In the
right-disjunct world of `rich_count_1041_twenty` (four rich deg-`4` hubs, the deg-`5` anchor
`f` iso-saturated, all other deg-`4` hubs of isoDeg `1`), a `Z`-leaf two-hub configuration is
forced: a rich hub of isoDeg `≥ 3` pairs with an `M`-end slot hub through the rich or share-`0`
packer, the blocked branches being killed by `hT`/`hno2hub` and the `N(g)`-incidence count. -/
theorem anchor_sat_kill_twenty (G : SimpleGraph (Fin 20)) (Hub Iso : Finset (Fin 20))
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdisj : Disjoint Hub Iso) (hsum18 : Hub.card + Iso.card = 18)
    (hdeg3 : ∀ v : Fin 20, 3 ≤ G.degree v) (hisodeg3 : ∀ t ∈ Iso, G.degree t = 3)
    (hleak : ∑ h ∈ Hub, (G.neighborFinset h ∩ (Finset.univ \ (Hub ∪ Iso))).card ≤ 4)
    (hdeg : ∀ h ∈ Hub, 4 ≤ G.degree h) (hdeg5 : ∀ h ∈ Hub, G.degree h ≤ 5)
    (hHub : Hub.card = 11) (hIso : Iso.card = 7)
    (hdsum : ∑ w ∈ Hub, G.degree w = 45)
    (hT : ¬∃ x y z : Fin 20, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 11)
    (_hC4 : ¬∃ a b c d : Fin 20, ({a, b, c, d} : Finset (Fin 20)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (_hK23 : ¬∃ a b c d e : Fin 20, ({a, b, c, d, e} : Finset (Fin 20)).card = 5 ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
      G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 19)
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hno2hub : ¬∃ h₁ h₂ : Fin 20, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card)
    (hR4 : (Hub.filter (fun h => G.degree h = 4 ∧
      2 ≤ (G.neighborFinset h ∩ Iso).card)).card = 4)
    (f : Fin 20) (hf : f ∈ Hub) (hfd : G.degree f = 5)
    (hfsat : (G.neighborFinset f ∩ Iso).card = 5)
    (hnonrich : ∀ h ∈ Hub, G.degree h = 4 →
      h ∉ Hub.filter (fun h => G.degree h = 4 ∧ 2 ≤ (G.neighborFinset h ∩ Iso).card) →
      (G.neighborFinset h ∩ Iso).card = 1) :
    SingleVertexConfig G ∨ TwoTwinConfig G ∨ TwoHubConfig G ∨ HubTriangleConfig G := by
  classical
  -- === The saturated anchor sees only twins: `N(f) ⊆ Iso`. ===
  have hNf : G.neighborFinset f ∩ Iso = G.neighborFinset f :=
    Finset.eq_of_subset_of_card_le Finset.inter_subset_left
      (by rw [G.card_neighborFinset_eq_degree, hfd, hfsat])
  have hfadj : ∀ w : Fin 20, G.Adj f w → w ∈ Iso := by
    intro w hw
    have hmem : w ∈ G.neighborFinset f ∩ Iso := by
      rw [hNf]; exact (G.mem_neighborFinset f w).mpr hw
    exact (Finset.mem_inter.mp hmem).2
  -- === Degree partition: `f` is the unique non-degree-4 hub. ===
  have hdeg45 : ∀ h ∈ Hub, G.degree h = 4 ∨ G.degree h = 5 := by
    intro h hh; have h1 := hdeg h hh; have h2 := hdeg5 h hh; omega
  set D4 : Finset (Fin 20) := Hub.filter (fun h => G.degree h = 4) with hD4def
  set D5 : Finset (Fin 20) := Hub.filter (fun h => ¬ G.degree h = 4) with hD5def
  have hD4deg4 : ∀ h ∈ D4, G.degree h = 4 := by
    intro h hh; rw [hD4def, Finset.mem_filter] at hh; exact hh.2
  have hD5deg5 : ∀ h ∈ D5, G.degree h = 5 := by
    intro h hh; rw [hD5def, Finset.mem_filter] at hh
    rcases hdeg45 h hh.1 with h4 | h5
    · exact absurd h4 hh.2
    · exact h5
  have hcardpart : D4.card + D5.card = 11 := by
    rw [hD4def, hD5def, Finset.card_filter_add_card_filter_not]; exact hHub
  have hsumdeg : (∑ h ∈ D4, G.degree h) + (∑ h ∈ D5, G.degree h) = 45 := by
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
  have hD4card : D4.card = 10 := by omega
  have hD5card : D5.card = 1 := by omega
  have hfD5 : f ∈ D5 := by rw [hD5def, Finset.mem_filter]; exact ⟨hf, by omega⟩
  obtain ⟨w5, hw5⟩ := Finset.card_eq_one.mp hD5card
  have hfw5 : f = w5 := by rw [hw5, Finset.mem_singleton] at hfD5; exact hfD5
  have hD5eq : D5 = {f} := by rw [hw5, ← hfw5]
  have huniq : ∀ h ∈ Hub, G.degree h ≠ 4 → h = f := by
    intro h hh hne
    have hmem : h ∈ D5 := by rw [hD5def, Finset.mem_filter]; exact ⟨hh, hne⟩
    rw [hD5eq, Finset.mem_singleton] at hmem; exact hmem
  -- === The iso-degree ledger: the four rich hubs carry `∑_R isoDeg = 10`. ===
  have hisosum21 : ∑ h ∈ Hub, (G.neighborFinset h ∩ Iso).card = 21 := by
    have h := hub_iso_sum_twenty G Hub Iso hiso3; rw [hIso] at h; omega
  have hisosplit : (∑ h ∈ D4, (G.neighborFinset h ∩ Iso).card)
      + (∑ h ∈ D5, (G.neighborFinset h ∩ Iso).card) = 21 := by
    rw [hD4def, hD5def, Finset.sum_filter_add_sum_filter_not]; exact hisosum21
  have hD5isosum : (∑ h ∈ D5, (G.neighborFinset h ∩ Iso).card) = 5 := by
    rw [hD5eq, Finset.sum_singleton, hfsat]
  have hD4isosum : ∑ h ∈ D4, (G.neighborFinset h ∩ Iso).card = 16 := by omega
  set R : Finset (Fin 20) := Hub.filter (fun h => G.degree h = 4 ∧
    2 ≤ (G.neighborFinset h ∩ Iso).card) with hRdef
  have hReq : R = D4.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card) := by
    rw [hRdef, hD4def, Finset.filter_filter]
  have hRmem : ∀ r ∈ R, r ∈ Hub ∧ G.degree r = 4 ∧ 2 ≤ (G.neighborFinset r ∩ Iso).card := by
    intro r hr; rw [hRdef, Finset.mem_filter] at hr; exact ⟨hr.1, hr.2⟩
  have hsplitR : (∑ h ∈ D4.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card),
        (G.neighborFinset h ∩ Iso).card)
      + (∑ h ∈ D4.filter (fun h => ¬ 2 ≤ (G.neighborFinset h ∩ Iso).card),
        (G.neighborFinset h ∩ Iso).card) = 16 := by
    rw [Finset.sum_filter_add_sum_filter_not]; exact hD4isosum
  have hnonrich1 : ∀ h ∈ D4.filter (fun h => ¬ 2 ≤ (G.neighborFinset h ∩ Iso).card),
      (G.neighborFinset h ∩ Iso).card = 1 := by
    intro h hh
    rw [Finset.mem_filter] at hh
    obtain ⟨hhD4, hhnr⟩ := hh
    rw [hD4def, Finset.mem_filter] at hhD4
    refine hnonrich h hhD4.1 hhD4.2 fun hmem => ?_
    rw [hRdef, Finset.mem_filter] at hmem
    exact hhnr hmem.2.2
  have hcardsplitR : (D4.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)).card
      + (D4.filter (fun h => ¬ 2 ≤ (G.neighborFinset h ∩ Iso).card)).card = 10 := by
    rw [Finset.card_filter_add_card_filter_not]; exact hD4card
  have hnrcard : (D4.filter (fun h => ¬ 2 ≤ (G.neighborFinset h ∩ Iso).card)).card = 6 := by
    rw [← hReq] at hcardsplitR; omega
  have hnrsum : (∑ h ∈ D4.filter (fun h => ¬ 2 ≤ (G.neighborFinset h ∩ Iso).card),
      (G.neighborFinset h ∩ Iso).card) = 6 := by
    calc (∑ h ∈ D4.filter (fun h => ¬ 2 ≤ (G.neighborFinset h ∩ Iso).card),
          (G.neighborFinset h ∩ Iso).card)
        = ∑ _h ∈ D4.filter (fun h => ¬ 2 ≤ (G.neighborFinset h ∩ Iso).card), 1 :=
          Finset.sum_congr rfl hnonrich1
      _ = 6 := by rw [Finset.sum_const, smul_eq_mul, mul_one, hnrcard]
  have hRsum : ∑ h ∈ R, (G.neighborFinset h ∩ Iso).card = 10 := by
    rw [hReq]; omega
  have hgex : ∃ g ∈ R, 3 ≤ (G.neighborFinset g ∩ Iso).card := by
    by_contra hcon
    push Not at hcon
    have hle : ∑ h ∈ R, (G.neighborFinset h ∩ Iso).card ≤ ∑ _h ∈ R, 2 :=
      Finset.sum_le_sum fun h hh => by have := hcon h hh; omega
    rw [Finset.sum_const, hR4, smul_eq_mul] at hle
    omega
  -- === The `M`-edge skeleton and the degree-4 slot extraction. ===
  obtain ⟨z₁, z₂, _, hz1Z, hz2Z, _, _, hnohub⟩ :=
    zslot_skeleton_deg5_twenty G Hub Iso hiso3 hdisj hsum18 hdeg3 hisodeg3 hleak hdeg5 hT
  have hzfacts := zfacts_deg5_twenty G Hub Iso hiso3 hdisj hsum18 hdeg3 hisodeg3 hleak
  have hznotIso : ∀ z ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 20)), z ∉ Iso := by
    intro z hz
    rw [Finset.mem_sdiff, Finset.mem_union, not_or] at hz
    exact hz.2.2
  have hznotHub : ∀ z ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 20)), z ∉ Hub := by
    intro z hz
    rw [Finset.mem_sdiff, Finset.mem_union, not_or] at hz
    exact hz.2.1
  have hslotex : ∀ z ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 20)),
      ∃ p q : Fin 20, p ≠ q ∧ p ∈ Hub ∧ q ∈ Hub ∧ G.Adj z p ∧ G.Adj z q ∧
        G.degree p = 4 ∧ G.degree q = 4 := by
    intro z hz
    obtain ⟨_, hhub2, _⟩ := hzfacts z hz
    obtain ⟨p, q, hpq, hpqeq⟩ := Finset.card_eq_two.mp hhub2
    have hpmem : p ∈ G.neighborFinset z ∩ Hub := by
      rw [hpqeq]; exact Finset.mem_insert_self p {q}
    have hqmem : q ∈ G.neighborFinset z ∩ Hub := by
      rw [hpqeq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self q)
    obtain ⟨hpN, hpHub⟩ := Finset.mem_inter.mp hpmem
    obtain ⟨hqN, hqHub⟩ := Finset.mem_inter.mp hqmem
    have hdeg4 : ∀ s ∈ Hub, G.Adj z s → G.degree s = 4 := by
      intro s hs hzs
      by_contra hne4
      have hsf : s = f := huniq s hs hne4
      refine hznotIso z hz (hfadj z ?_)
      rw [← hsf]
      exact hzs.symm
    exact ⟨p, q, hpq, hpHub, hqHub, (G.mem_neighborFinset z p).mp hpN,
      (G.mem_neighborFinset z q).mp hqN,
      hdeg4 p hpHub ((G.mem_neighborFinset z p).mp hpN),
      hdeg4 q hqHub ((G.mem_neighborFinset z q).mp hqN)⟩
  -- === Any packed 6-tuple assembles to the `TwoHubConfig` disjunct. ===
  have hfinish : (∃ h₁ h₂ a b c z : Fin 20, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧ G.degree h₁ = 4 ∧
      G.degree h₂ = 4 ∧ a ∈ Iso ∧ b ∈ Iso ∧ c ∈ Iso ∧
      z ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 20)) ∧
      G.Adj a h₁ ∧ G.Adj b h₁ ∧ G.Adj c h₂ ∧ G.Adj z h₂ ∧
      ¬G.Adj h₁ h₂ ∧ ¬G.Adj h₁ c ∧ ¬G.Adj h₁ z ∧
      ¬G.Adj a h₂ ∧ ¬G.Adj b h₂ ∧ a ≠ b) →
      SingleVertexConfig G ∨ TwoTwinConfig G ∨ TwoHubConfig G ∨ HubTriangleConfig G := by
    rintro ⟨h₁, h₂, a, b, c, z, hh₁, hh₂, hd₁, hd₂, ha, hb, hc, hzZ, ha1, hb1, hc2, hz2,
      hn12, hn1c, hn1z, hna2, hnb2, hab⟩
    obtain ⟨hziso0, _, hzdeg3⟩ := hzfacts z hzZ
    exact Or.inr (Or.inr (Or.inl (two_hub_zleaf_gen_twenty G Hub Iso hiso3 hdisj hisodeg3
      h₁ h₂ a b c z hh₁ hh₂ hd₁ hd₂ ha hb hc hzZ hzdeg3 hziso0 ha1 hb1 hc2 hz2
      hn12 hn1c hn1z hna2 hnb2 hab)))
  obtain ⟨g, hgR, hgiso3⟩ := hgex
  obtain ⟨hgHub, hgd4, _⟩ := hRmem g hgR
  have hgnotIso : g ∉ Iso := fun h => Finset.disjoint_left.mp hdisj hgHub h
  by_cases hg3 : ∃ g₃ ∈ R, g₃ ≠ g ∧ 3 ≤ (G.neighborFinset g₃ ∩ Iso).card
  · -- === Case I: a second isoDeg-`≥ 3` rich hub — both hub-locked, any slot works. ===
    obtain ⟨g₃, hg₃R, hg₃ne, hg₃iso3⟩ := hg3
    obtain ⟨hg₃Hub, hg₃d4, _⟩ := hRmem g₃ hg₃R
    have hgne₃ : g ≠ g₃ := Ne.symm hg₃ne
    have hg₃notIso : g₃ ∉ Iso := fun h => Finset.disjoint_left.mp hdisj hg₃Hub h
    -- `hshare` + `hno2hub` force the two isoDeg-`≥ 3` rich hubs adjacent.
    have hadj : G.Adj g g₃ := by
      by_contra hnadj
      have hsh1 := hshare g hgHub hgd4 g₃ hg₃Hub hg₃d4 hgne₃ hnadj
      have hsh2 := hshare g₃ hg₃Hub hg₃d4 g hgHub hgd4 hg₃ne fun h => hnadj h.symm
      have hpriv1 : 2 ≤ ((G.neighborFinset g ∩ Iso) \ G.neighborFinset g₃).card := by
        have hkey := Finset.card_sdiff_add_card_inter (G.neighborFinset g ∩ Iso)
          (G.neighborFinset g₃)
        have hinter : (G.neighborFinset g ∩ Iso) ∩ G.neighborFinset g₃
            = G.neighborFinset g ∩ G.neighborFinset g₃ ∩ Iso := Finset.inter_right_comm _ _ _
        rw [hinter] at hkey
        omega
      have hpriv2 : 2 ≤ ((G.neighborFinset g₃ ∩ Iso) \ G.neighborFinset g).card := by
        have hkey := Finset.card_sdiff_add_card_inter (G.neighborFinset g₃ ∩ Iso)
          (G.neighborFinset g)
        have hinter : (G.neighborFinset g₃ ∩ Iso) ∩ G.neighborFinset g
            = G.neighborFinset g₃ ∩ G.neighborFinset g ∩ Iso := Finset.inter_right_comm _ _ _
        rw [hinter] at hkey
        omega
      exact hno2hub ⟨g, g₃, hgHub, hg₃Hub, hgd4, hg₃d4, hgne₃, hnadj, hpriv1, hpriv2⟩
    -- Both hubs are locked: all neighbours besides each other lie in `Iso`.
    have hlock : ∀ x y : Fin 20, G.degree x = 4 → 3 ≤ (G.neighborFinset x ∩ Iso).card →
        G.Adj x y → y ∉ Iso → ∀ w : Fin 20, G.Adj x w → w ∈ Iso ∨ w = y := by
      intro x y hxd hxiso hxy hyIso w hxw
      by_contra hcon
      push Not at hcon
      obtain ⟨hwIso, hwy⟩ := hcon
      have hyni : y ∉ G.neighborFinset x ∩ Iso := fun hy =>
        hyIso (Finset.mem_inter.mp hy).2
      have hwni : w ∉ insert y (G.neighborFinset x ∩ Iso) := by
        rw [Finset.mem_insert]
        rintro (rfl | hw)
        · exact hwy rfl
        · exact hwIso (Finset.mem_inter.mp hw).2
      have hsub : insert w (insert y (G.neighborFinset x ∩ Iso)) ⊆ G.neighborFinset x := by
        intro u hu
        rw [Finset.mem_insert, Finset.mem_insert] at hu
        rcases hu with rfl | rfl | hu
        · exact (G.mem_neighborFinset _ _).mpr hxw
        · exact (G.mem_neighborFinset _ _).mpr hxy
        · exact (Finset.mem_inter.mp hu).1
      have hcard := Finset.card_le_card hsub
      rw [Finset.card_insert_of_notMem hwni, Finset.card_insert_of_notMem hyni,
        G.card_neighborFinset_eq_degree, hxd] at hcard
      omega
    have hgnbr : ∀ w : Fin 20, G.Adj g w → w ∈ Iso ∨ w = g₃ :=
      hlock g g₃ hgd4 hgiso3 hadj hg₃notIso
    have hg₃nbr : ∀ w : Fin 20, G.Adj g₃ w → w ∈ Iso ∨ w = g :=
      hlock g₃ g hg₃d4 hg₃iso3 hadj.symm hgnotIso
    obtain ⟨p, _, _, hpHub, _, hzp, _, hpd4, _⟩ := hslotex z₁ hz1Z
    have hngz : ¬G.Adj g z₁ := by
      intro h
      rcases hgnbr z₁ h with h1 | h1
      · exact hznotIso z₁ hz1Z h1
      · exact hznotHub z₁ hz1Z (by rw [h1]; exact hg₃Hub)
    have hng₃z : ¬G.Adj g₃ z₁ := by
      intro h
      rcases hg₃nbr z₁ h with h1 | h1
      · exact hznotIso z₁ hz1Z h1
      · exact hznotHub z₁ hz1Z (by rw [h1]; exact hgHub)
    have hpneg : p ≠ g := by
      rintro rfl
      exact hngz hzp.symm
    have hpne₃ : p ≠ g₃ := by
      rintro rfl
      exact hng₃z hzp.symm
    have hngp : ¬G.Adj g p := by
      intro h
      rcases hgnbr p h with h1 | h1
      · exact Finset.disjoint_left.mp hdisj hpHub h1
      · exact hpne₃ h1
    have hng₃p : ¬G.Adj g₃ p := by
      intro h
      rcases hg₃nbr p h with h1 | h1
      · exact Finset.disjoint_left.mp hdisj hpHub h1
      · exact hpneg h1
    by_cases hp2 : 2 ≤ (G.neighborFinset p ∩ Iso).card
    · exact hfinish (zleaf_pack_rich_twenty G Hub Iso hiso3 hisodeg3 hshare g p z₁ hgHub
        hpHub hgd4 hpd4 hz1Z (Ne.symm hpneg) hngp hgiso3 hp2 hzp hngz)
    · have hp1 : (G.neighborFinset p ∩ Iso).card = 1 := by
        refine hnonrich p hpHub hpd4 fun hmem => ?_
        rw [hRdef, Finset.mem_filter] at hmem
        exact hp2 hmem.2.2
      obtain ⟨c, hceq⟩ := Finset.card_eq_one.mp hp1
      have hcmem : c ∈ G.neighborFinset p ∩ Iso := by
        rw [hceq]; exact Finset.mem_singleton_self c
      obtain ⟨hcN, hcIso⟩ := Finset.mem_inter.mp hcmem
      by_cases hcg : c ∈ G.neighborFinset g
      · by_cases hcg₃ : c ∈ G.neighborFinset g₃
        · -- both meet the twin `c`: good triangle `g–g₃–c` at `4 + 4 + 3 ≤ 11`.
          have hcd3 : G.degree c = 3 := hisodeg3 c hcIso
          refine absurd ⟨g, g₃, c, hgne₃, ?_, ?_, hadj,
            (G.mem_neighborFinset g₃ c).mp hcg₃, (G.mem_neighborFinset g c).mp hcg,
            by omega⟩ hT
          · rintro rfl
            exact hg₃notIso hcIso
          · rintro rfl
            exact hgnotIso hcIso
        · have hsh0 : G.neighborFinset g₃ ∩ G.neighborFinset p ∩ Iso = ∅ := by
            rw [Finset.eq_empty_iff_forall_notMem]
            intro x hx
            rw [Finset.mem_inter, Finset.mem_inter] at hx
            have hxc : x ∈ G.neighborFinset p ∩ Iso := Finset.mem_inter.mpr ⟨hx.1.2, hx.2⟩
            rw [hceq, Finset.mem_singleton] at hxc
            exact hcg₃ (hxc ▸ hx.1.1)
          exact hfinish (zleaf_pack_share0_twenty G Hub Iso hiso3 hisodeg3 g₃ p z₁ hg₃Hub
            hpHub hg₃d4 hpd4 hz1Z (Ne.symm hpne₃) hng₃p (by omega) (by omega) hsh0 hzp
            hng₃z)
      · have hsh0 : G.neighborFinset g ∩ G.neighborFinset p ∩ Iso = ∅ := by
          rw [Finset.eq_empty_iff_forall_notMem]
          intro x hx
          rw [Finset.mem_inter, Finset.mem_inter] at hx
          have hxc : x ∈ G.neighborFinset p ∩ Iso := Finset.mem_inter.mpr ⟨hx.1.2, hx.2⟩
          rw [hceq, Finset.mem_singleton] at hxc
          exact hcg (hxc ▸ hx.1.1)
        exact hfinish (zleaf_pack_share0_twenty G Hub Iso hiso3 hisodeg3 g p z₁ hgHub
          hpHub hgd4 hpd4 hz1Z (Ne.symm hpneg) hngp (by omega) (by omega) hsh0 hzp hngz)
  · -- === Case II: `g` unique with isoDeg ≥ 3 — `isoDeg g = 4` and the `T`-count kills. ===
    push Not at hg3
    have hR2 : ∀ r ∈ R.erase g, (G.neighborFinset r ∩ Iso).card = 2 := by
      intro r hr
      rw [Finset.mem_erase] at hr
      have h1 := hg3 r hr.2 hr.1
      have h2 := (hRmem r hr.2).2.2
      omega
    have hRecard : (R.erase g).card = 3 := by
      rw [Finset.card_erase_of_mem hgR, hR4]
    have hResum : ∑ r ∈ R.erase g, (G.neighborFinset r ∩ Iso).card = 6 := by
      calc ∑ r ∈ R.erase g, (G.neighborFinset r ∩ Iso).card
          = ∑ _r ∈ R.erase g, 2 := Finset.sum_congr rfl hR2
        _ = 6 := by rw [Finset.sum_const, hRecard, smul_eq_mul]
    have hsum_g : (G.neighborFinset g ∩ Iso).card
        + ∑ r ∈ R.erase g, (G.neighborFinset r ∩ Iso).card = 10 := by
      rw [Finset.add_sum_erase R (fun h => (G.neighborFinset h ∩ Iso).card) hgR]
      exact hRsum
    have hgiso4 : (G.neighborFinset g ∩ Iso).card = 4 := by omega
    have hNgIso : G.neighborFinset g ∩ Iso = G.neighborFinset g :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_left
        (by rw [G.card_neighborFinset_eq_degree, hgd4, hgiso4])
    have hgadjIso : ∀ w : Fin 20, G.Adj g w → w ∈ Iso := by
      intro w hw
      have hmem : w ∈ G.neighborFinset g ∩ Iso := by
        rw [hNgIso]; exact (G.mem_neighborFinset g w).mpr hw
      exact (Finset.mem_inter.mp hmem).2
    by_contra hcon
    -- Every slot hub is `1`-poor with its unique twin inside `N(g)`.
    have hslotkey : ∀ z s : Fin 20, z ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 20)) →
        G.Adj z s → s ∈ Hub → G.degree s = 4 →
        1 ≤ (G.neighborFinset s ∩ (G.neighborFinset g ∩ Iso)).card ∧
          (G.neighborFinset s ∩ Iso).card = 1 := by
      intro z s hzZ hzs hsHub hsd4
      have hngz : ¬G.Adj g z := fun h => hznotIso z hzZ (hgadjIso z h)
      have hngs : ¬G.Adj g s := fun h => Finset.disjoint_left.mp hdisj hsHub (hgadjIso s h)
      have hgs : g ≠ s := by
        rintro rfl
        exact hngz hzs.symm
      by_cases h2 : 2 ≤ (G.neighborFinset s ∩ Iso).card
      · exact absurd (hfinish (zleaf_pack_rich_twenty G Hub Iso hiso3 hisodeg3 hshare g s z
          hgHub hsHub hgd4 hsd4 hzZ hgs hngs (by omega) h2 hzs hngz)) hcon
      · have hs1 : (G.neighborFinset s ∩ Iso).card = 1 := by
          refine hnonrich s hsHub hsd4 fun hmem => ?_
          rw [hRdef, Finset.mem_filter] at hmem
          exact h2 hmem.2.2
        obtain ⟨c, hceq⟩ := Finset.card_eq_one.mp hs1
        have hcmem : c ∈ G.neighborFinset s ∩ Iso := by
          rw [hceq]; exact Finset.mem_singleton_self c
        obtain ⟨hcN, hcIso⟩ := Finset.mem_inter.mp hcmem
        by_cases hcg : c ∈ G.neighborFinset g
        · refine ⟨Finset.card_pos.mpr ⟨c, ?_⟩, hs1⟩
          rw [Finset.mem_inter, Finset.mem_inter]
          exact ⟨hcN, hcg, hcIso⟩
        · have hsh0 : G.neighborFinset g ∩ G.neighborFinset s ∩ Iso = ∅ := by
            rw [Finset.eq_empty_iff_forall_notMem]
            intro x hx
            rw [Finset.mem_inter, Finset.mem_inter] at hx
            have hxc : x ∈ G.neighborFinset s ∩ Iso := Finset.mem_inter.mpr ⟨hx.1.2, hx.2⟩
            rw [hceq, Finset.mem_singleton] at hxc
            exact hcg (hxc ▸ hx.1.1)
          exact absurd (hfinish (zleaf_pack_share0_twenty G Hub Iso hiso3 hisodeg3 g s z
            hgHub hsHub hgd4 hsd4 hzZ hgs hngs (by omega) (by omega) hsh0 hzs hngz)) hcon
    -- The four blocked slots, pairwise distinct.
    obtain ⟨p₁, q₁, hpq1, hp1Hub, hq1Hub, hzp1, hzq1, hp1d4, hq1d4⟩ := hslotex z₁ hz1Z
    obtain ⟨p₂, q₂, hpq2, hp2Hub, hq2Hub, hzp2, hzq2, hp2d4, hq2d4⟩ := hslotex z₂ hz2Z
    obtain ⟨hp1T, hp1poor⟩ := hslotkey z₁ p₁ hz1Z hzp1 hp1Hub hp1d4
    obtain ⟨hq1T, hq1poor⟩ := hslotkey z₁ q₁ hz1Z hzq1 hq1Hub hq1d4
    obtain ⟨hp2T, hp2poor⟩ := hslotkey z₂ p₂ hz2Z hzp2 hp2Hub hp2d4
    obtain ⟨hq2T, hq2poor⟩ := hslotkey z₂ q₂ hz2Z hzq2 hq2Hub hq2d4
    have hp1p2 : p₁ ≠ p₂ := by
      rintro rfl
      exact hnohub _ hp1Hub ⟨hzp1.symm, hzp2.symm⟩
    have hp1q2 : p₁ ≠ q₂ := by
      rintro rfl
      exact hnohub _ hp1Hub ⟨hzp1.symm, hzq2.symm⟩
    have hq1p2 : q₁ ≠ p₂ := by
      rintro rfl
      exact hnohub _ hq1Hub ⟨hzq1.symm, hzp2.symm⟩
    have hq1q2 : q₁ ≠ q₂ := by
      rintro rfl
      exact hnohub _ hq1Hub ⟨hzq1.symm, hzq2.symm⟩
    -- The incidence count on `T = N(g) ∩ Iso`: `2 + 3 + 4 = 9 > 8 = 2·|T|`.
    set S4 : Finset (Fin 20) := {p₁, q₁, p₂, q₂} with hS4def
    set W : Finset (Fin 20) := insert f ((R.erase g) ∪ S4) with hWdef
    have hReD4deg : ∀ r ∈ R.erase g, G.degree r = 4 := fun r hr =>
      (hRmem r (Finset.mem_of_mem_erase hr)).2.1
    have hfnotin : f ∉ (R.erase g) ∪ S4 := by
      intro hmem
      rw [Finset.mem_union] at hmem
      rcases hmem with h | h
      · have h4 := hReD4deg f h
        omega
      · rw [hS4def] at h
        simp only [Finset.mem_insert, Finset.mem_singleton] at h
        rcases h with rfl | rfl | rfl | rfl
        · omega
        · omega
        · omega
        · omega
    have hdisjRS : Disjoint (R.erase g) S4 := by
      rw [Finset.disjoint_left]
      intro a ha hb
      have h2 := hR2 a ha
      rw [hS4def] at hb
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with rfl | rfl | rfl | rfl
      · omega
      · omega
      · omega
      · omega
    have hS4sum : 4 ≤ ∑ s ∈ S4, (G.neighborFinset s ∩ (G.neighborFinset g ∩ Iso)).card := by
      rw [hS4def]
      rw [Finset.sum_insert (by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨hpq1, hp1p2, hp1q2⟩),
        Finset.sum_insert (by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨hq1p2, hq1q2⟩),
        Finset.sum_insert (by
          simp only [Finset.mem_singleton]
          exact hpq2),
        Finset.sum_singleton]
      omega
    have hResumT :
        3 ≤ ∑ r ∈ R.erase g, (G.neighborFinset r ∩ (G.neighborFinset g ∩ Iso)).card := by
      have hone : ∀ r ∈ R.erase g,
          1 ≤ (G.neighborFinset r ∩ (G.neighborFinset g ∩ Iso)).card := by
        intro r hr
        have hr2 : (G.neighborFinset r ∩ Iso).card = 2 := hR2 r hr
        rw [Finset.mem_erase] at hr
        obtain ⟨hrne, hrR⟩ := hr
        obtain ⟨hrHub, hrd4, _⟩ := hRmem r hrR
        by_contra h0
        push Not at h0
        have hempty : G.neighborFinset r ∩ (G.neighborFinset g ∩ Iso) = ∅ := by
          rw [← Finset.card_eq_zero]
          omega
        have hngr : ¬G.Adj g r := fun h =>
          Finset.disjoint_left.mp hdisj hrHub (hgadjIso r h)
        have hpriv1 : 2 ≤ ((G.neighborFinset g ∩ Iso) \ G.neighborFinset r).card := by
          have hsub : G.neighborFinset g ∩ Iso
              ⊆ (G.neighborFinset g ∩ Iso) \ G.neighborFinset r := by
            intro x hx
            rw [Finset.mem_sdiff]
            refine ⟨hx, fun hxr => ?_⟩
            have hxmem : x ∈ G.neighborFinset r ∩ (G.neighborFinset g ∩ Iso) :=
              Finset.mem_inter.mpr ⟨hxr, hx⟩
            rw [hempty] at hxmem
            exact Finset.notMem_empty x hxmem
          have hc := Finset.card_le_card hsub
          omega
        have hpriv2 : 2 ≤ ((G.neighborFinset r ∩ Iso) \ G.neighborFinset g).card := by
          have hsub : G.neighborFinset r ∩ Iso
              ⊆ (G.neighborFinset r ∩ Iso) \ G.neighborFinset g := by
            intro x hx
            rw [Finset.mem_sdiff]
            refine ⟨hx, fun hxg => ?_⟩
            obtain ⟨hxr, hxI⟩ := Finset.mem_inter.mp hx
            have hxmem : x ∈ G.neighborFinset r ∩ (G.neighborFinset g ∩ Iso) :=
              Finset.mem_inter.mpr ⟨hxr, Finset.mem_inter.mpr ⟨hxg, hxI⟩⟩
            rw [hempty] at hxmem
            exact Finset.notMem_empty x hxmem
          have hc := Finset.card_le_card hsub
          omega
        exact hno2hub ⟨g, r, hgHub, hrHub, hgd4, hrd4, Ne.symm hrne, hngr, hpriv1, hpriv2⟩
      have hns := Finset.card_nsmul_le_sum (R.erase g)
        (fun r => (G.neighborFinset r ∩ (G.neighborFinset g ∩ Iso)).card) 1 hone
      rw [hRecard] at hns
      simpa using hns
    have hfT : 2 ≤ (G.neighborFinset f ∩ (G.neighborFinset g ∩ Iso)).card := by
      have hkey := Finset.card_union_add_card_inter (G.neighborFinset f ∩ Iso)
        (G.neighborFinset g ∩ Iso)
      have hUle : ((G.neighborFinset f ∩ Iso) ∪ (G.neighborFinset g ∩ Iso)).card ≤ 7 := by
        have hsubU : (G.neighborFinset f ∩ Iso) ∪ (G.neighborFinset g ∩ Iso) ⊆ Iso :=
          Finset.union_subset Finset.inter_subset_right Finset.inter_subset_right
        have hc := Finset.card_le_card hsubU
        omega
      have hsubI : (G.neighborFinset f ∩ Iso) ∩ (G.neighborFinset g ∩ Iso)
          ⊆ G.neighborFinset f ∩ (G.neighborFinset g ∩ Iso) := by
        intro x hx
        rw [Finset.mem_inter, Finset.mem_inter] at hx
        exact Finset.mem_inter.mpr ⟨hx.1.1, hx.2⟩
      have hc2 := Finset.card_le_card hsubI
      omega
    have hgW : g ∉ W := by
      rw [hWdef, Finset.mem_insert]
      rintro (rfl | hmem)
      · omega
      · rw [Finset.mem_union] at hmem
        rcases hmem with h | h
        · exact Finset.notMem_erase g R h
        · rw [hS4def] at h
          simp only [Finset.mem_insert, Finset.mem_singleton] at h
          rcases h with rfl | rfl | rfl | rfl
          · exact hznotIso z₁ hz1Z (hgadjIso z₁ hzp1.symm)
          · exact hznotIso z₁ hz1Z (hgadjIso z₁ hzq1.symm)
          · exact hznotIso z₂ hz2Z (hgadjIso z₂ hzp2.symm)
          · exact hznotIso z₂ hz2Z (hgadjIso z₂ hzq2.symm)
    have htW2 : ∀ t ∈ G.neighborFinset g ∩ Iso, (G.neighborFinset t ∩ W).card ≤ 2 := by
      intro t ht
      obtain ⟨htN, htIso⟩ := Finset.mem_inter.mp ht
      have hgt : g ∈ G.neighborFinset t := by
        rw [G.mem_neighborFinset] at htN ⊢
        exact htN.symm
      have hsub : G.neighborFinset t ∩ W ⊆ (G.neighborFinset t).erase g := by
        intro x hx
        obtain ⟨hxN, hxW⟩ := Finset.mem_inter.mp hx
        refine Finset.mem_erase.mpr ⟨fun hxg => ?_, hxN⟩
        rw [hxg] at hxW
        exact hgW hxW
      have hcard : ((G.neighborFinset t).erase g).card = 2 := by
        rw [Finset.card_erase_of_mem hgt, G.card_neighborFinset_eq_degree,
          hisodeg3 t htIso]
      exact le_trans (Finset.card_le_card hsub) (le_of_eq hcard)
    have hupper : ∑ v ∈ W, (G.neighborFinset v ∩ (G.neighborFinset g ∩ Iso)).card ≤ 8 := by
      rw [cross_count_twenty G W (G.neighborFinset g ∩ Iso)]
      calc ∑ t ∈ G.neighborFinset g ∩ Iso, (G.neighborFinset t ∩ W).card
          ≤ ∑ _t ∈ G.neighborFinset g ∩ Iso, 2 := Finset.sum_le_sum htW2
        _ = 8 := by rw [Finset.sum_const, hgiso4, smul_eq_mul]
    have hlower : 9 ≤ ∑ v ∈ W, (G.neighborFinset v ∩ (G.neighborFinset g ∩ Iso)).card := by
      rw [hWdef, Finset.sum_insert hfnotin, Finset.sum_union hdisjRS]
      omega
    omega

end N20

end ACMax
