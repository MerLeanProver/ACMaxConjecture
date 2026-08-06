import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N19.TwoHubCornerDeg5ZLeaf
import ACMaxConjecture.SmallCases.N19.TwoHubSelect
import ACMaxConjecture.SmallCases.N19.ZVertex
import ACMaxConjecture.SmallCases.N19.Deg5ZSlots
import ACMaxConjecture.SmallCases.N19.Deg5SameZ
import ACMaxConjecture.SmallCases.N19.Deg5RichCap

/-! # The good z-hub existence for the rich (10,7,41) Z-leaf extraction (`n = 19`) -/
namespace ACMax
open scoped Classical

namespace N19

/-- **The rich-hub saturation bound.**  For a rich degree-`4` hub `g` (`isoDeg g ≥ 3`), every
degree-`4` hub `h ≠ g` non-adjacent to `g` with `isoDeg h ≥ 2` must share a twin with `g` (else
`hno2hub` fires), so it is adjacent to one of `g`'s twins.  Each of `g`'s `isoDeg g` twins has
degree `3` and already meets `g`, so it hosts at most `2` such hubs.  Double counting gives at most
`2·isoDeg g` such hubs. -/
theorem sat_bound_rich_nineteen (G : SimpleGraph (Fin 19)) (Hub Iso : Finset (Fin 19))
    (hisodeg3 : ∀ t ∈ Iso, G.degree t = 3)
    (hno2hub : ¬∃ h₁ h₂ : Fin 19, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card)
    (g : Fin 19) (hg : g ∈ Hub) (hgd : G.degree g = 4)
    (hgiso : 3 ≤ (G.neighborFinset g ∩ Iso).card) :
    (Hub.filter (fun h => G.degree h = 4 ∧ h ≠ g ∧ ¬G.Adj g h ∧
      2 ≤ (G.neighborFinset h ∩ Iso).card)).card
      ≤ 2 * (G.neighborFinset g ∩ Iso).card := by
  classical
  set S : Finset (Fin 19) := Hub.filter (fun h => G.degree h = 4 ∧ h ≠ g ∧ ¬G.Adj g h ∧
    2 ≤ (G.neighborFinset h ∩ Iso).card) with hSdef
  set T : Finset (Fin 19) := G.neighborFinset g ∩ Iso with hTdef
  -- Each hub `h ∈ S` is adjacent to at least one of `g`'s twins.
  have hstep1 : ∀ h ∈ S, 1 ≤ (G.neighborFinset h ∩ T).card := by
    intro h hh
    rw [hSdef, Finset.mem_filter] at hh
    obtain ⟨hhHub, hhd, hne, hnadj, hhiso⟩ := hh
    by_contra hcon
    push Not at hcon
    have hzero : (G.neighborFinset h ∩ T).card = 0 := by omega
    rw [Finset.card_eq_zero] at hzero
    -- `N h ∩ N g ∩ Iso = ∅`.
    have hempty : G.neighborFinset h ∩ G.neighborFinset g ∩ Iso = ∅ := by
      rw [Finset.inter_assoc]; exact hzero
    have hg3 : 3 ≤ (G.neighborFinset g ∩ Iso).card := hTdef ▸ hgiso
    -- private twins of `g` off `h`: all of them, `≥ 3`.
    have hgpriv : 2 ≤ ((G.neighborFinset g ∩ Iso) \ G.neighborFinset h).card := by
      have hkey := Finset.card_sdiff_add_card_inter (G.neighborFinset g ∩ Iso)
        (G.neighborFinset h)
      have hinter : (G.neighborFinset g ∩ Iso) ∩ G.neighborFinset h
          = G.neighborFinset h ∩ G.neighborFinset g ∩ Iso := by
        rw [Finset.inter_right_comm, Finset.inter_comm (G.neighborFinset g) (G.neighborFinset h)]
      rw [hinter, hempty] at hkey
      simp only [Finset.card_empty] at hkey
      omega
    -- private twins of `h` off `g`: all of them, `≥ 2`.
    have hhpriv : 2 ≤ ((G.neighborFinset h ∩ Iso) \ G.neighborFinset g).card := by
      have hkey := Finset.card_sdiff_add_card_inter (G.neighborFinset h ∩ Iso)
        (G.neighborFinset g)
      have hinter : (G.neighborFinset h ∩ Iso) ∩ G.neighborFinset g
          = G.neighborFinset h ∩ G.neighborFinset g ∩ Iso := Finset.inter_right_comm _ _ _
      rw [hinter, hempty] at hkey
      simp only [Finset.card_empty] at hkey
      omega
    exact hno2hub ⟨g, h, hg, hhHub, hgd, hhd, fun he => hne he.symm, hnadj, hgpriv, hhpriv⟩
  -- Each twin `t ∈ T` hosts at most `2` hubs of `S` (it already meets `g ∉ S`).
  have hstep2 : ∀ t ∈ T, (G.neighborFinset t ∩ S).card ≤ 2 := by
    intro t ht
    rw [hTdef, Finset.mem_inter, G.mem_neighborFinset] at ht
    obtain ⟨htadj, htIso⟩ := ht
    have hgmem : g ∈ G.neighborFinset t := by
      rw [G.mem_neighborFinset]; exact htadj.symm
    have hsub : G.neighborFinset t ∩ S ⊆ G.neighborFinset t \ {g} := by
      intro v hv
      rw [Finset.mem_inter] at hv
      obtain ⟨hvt, hvS⟩ := hv
      rw [Finset.mem_sdiff, Finset.mem_singleton]
      refine ⟨hvt, ?_⟩
      rw [hSdef, Finset.mem_filter] at hvS
      exact hvS.2.2.1
    calc (G.neighborFinset t ∩ S).card ≤ (G.neighborFinset t \ {g}).card :=
          Finset.card_le_card hsub
      _ = (G.neighborFinset t).card - 1 := by
          rw [Finset.sdiff_singleton_eq_erase, Finset.card_erase_of_mem hgmem]
      _ = 2 := by rw [G.card_neighborFinset_eq_degree, hisodeg3 t htIso]
  -- Double count.
  have hswap : ∑ h ∈ S, (G.neighborFinset h ∩ T).card
      = ∑ t ∈ T, (G.neighborFinset t ∩ S).card := cross_count_nineteen G S T
  have hlow : S.card ≤ ∑ h ∈ S, (G.neighborFinset h ∩ T).card := by
    calc S.card = ∑ _h ∈ S, 1 := by rw [Finset.sum_const, smul_eq_mul, mul_one]
      _ ≤ ∑ h ∈ S, (G.neighborFinset h ∩ T).card := Finset.sum_le_sum hstep1
  have hhigh : ∑ t ∈ T, (G.neighborFinset t ∩ S).card ≤ 2 * T.card := by
    calc ∑ t ∈ T, (G.neighborFinset t ∩ S).card ≤ ∑ _t ∈ T, 2 := Finset.sum_le_sum hstep2
      _ = 2 * T.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  rw [hswap] at hlow
  calc S.card ≤ 2 * T.card := le_trans hlow hhigh
    _ = 2 * (G.neighborFinset g ∩ Iso).card := by rw [hTdef]

set_option maxHeartbeats 1000000 in
/-- With the rich hub `g` (isoDeg ≥ 3), the `(10,7,41)` ledger + the iso-cap
produce a degree-`4` `Z`-slot hub `h₂` of isoDeg `≥ 1`, on a `z` avoided by `g`
and non-adjacent to `g`. -/
theorem good_zhub_1041_nineteen (G : SimpleGraph (Fin 19)) (Hub Iso : Finset (Fin 19))
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdisj : Disjoint Hub Iso) (hsum17 : Hub.card + Iso.card = 17)
    (hdeg3 : ∀ v : Fin 19, 3 ≤ G.degree v) (hisodeg3 : ∀ t ∈ Iso, G.degree t = 3)
    (hleak : ∑ h ∈ Hub, (G.neighborFinset h ∩ (Finset.univ \ (Hub ∪ Iso))).card ≤ 4)
    (hdeg : ∀ h ∈ Hub, 4 ≤ G.degree h) (hdeg5 : ∀ h ∈ Hub, G.degree h ≤ 5)
    (hHub : Hub.card = 10) (hIso : Iso.card = 7) (hdsum : ∑ w ∈ Hub, G.degree w = 41)
    (hT : ¬∃ x y z : Fin 19, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 11)
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hno2hub : ¬∃ h₁ h₂ : Fin 19, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card)
    (g : Fin 19) (hg : g ∈ Hub) (hgd : G.degree g = 4)
    (hgiso : 3 ≤ (G.neighborFinset g ∩ Iso).card) :
    ∃ h₂ z : Fin 19, h₂ ∈ Hub ∧ G.degree h₂ = 4 ∧
      z ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 19)) ∧
      G.Adj z h₂ ∧ ¬G.Adj g z ∧ ¬G.Adj g h₂ ∧ g ≠ h₂ ∧
      1 ≤ (G.neighborFinset h₂ ∩ Iso).card := by
  classical
  -- Abbreviation for the `Z`-layer.
  set Z : Finset (Fin 19) := Finset.univ \ (Hub ∪ Iso) with hZdef
  -- Degrees are `4` or `5`; the profile splits `10` hubs into `9` of degree `4` and one of `5`.
  have hpd : ∀ h ∈ Hub, G.degree h = 4 ∨ G.degree h = 5 := fun h hh => by
    have := hdeg h hh; have := hdeg5 h hh; omega
  set D4 : Finset (Fin 19) := Hub.filter (fun h => G.degree h = 4) with hD4def
  set D5 : Finset (Fin 19) := Hub.filter (fun h => G.degree h = 5) with hD5def
  have hmemD4 : ∀ w, w ∈ D4 ↔ w ∈ Hub ∧ G.degree w = 4 := fun w => by
    rw [hD4def]; exact Finset.mem_filter
  have hmemD5 : ∀ w, w ∈ D5 ↔ w ∈ Hub ∧ G.degree w = 5 := fun w => by
    rw [hD5def]; exact Finset.mem_filter
  have hcover : D4 ∪ D5 = Hub := by
    ext h; rw [Finset.mem_union, hmemD4, hmemD5]
    refine ⟨fun h' => h'.elim (·.1) (·.1), fun hh => ?_⟩
    rcases hpd h hh with h4 | h5
    · exact Or.inl ⟨hh, h4⟩
    · exact Or.inr ⟨hh, h5⟩
  have hdisj45 : Disjoint D4 D5 := by
    rw [Finset.disjoint_left]; intro h hd4 hd5
    rw [hmemD4] at hd4; rw [hmemD5] at hd5; omega
  have hcardsum : D4.card + D5.card = 10 := by
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
  have h41 : 4 * D4.card + 5 * D5.card = 41 := by rw [← hdegsum]; exact hdsum
  have hD4card : D4.card = 9 := by omega
  have hD5card : D5.card = 1 := by omega
  -- The single degree-`5` hub.
  obtain ⟨d5, hd5eq⟩ := Finset.card_eq_one.mp hD5card
  have hd5mem : d5 ∈ D5 := by rw [hd5eq]; exact Finset.mem_singleton_self d5
  have hd5Hub : d5 ∈ Hub := ((hmemD5 d5).mp hd5mem).1
  have hd5deg : G.degree d5 = 5 := ((hmemD5 d5).mp hd5mem).2
  -- The iso-incidence ledger: `∑_Hub isoDeg = 3·|Iso| = 21`.
  have hledger : ∑ h ∈ Hub, (G.neighborFinset h ∩ Iso).card = 21 := by
    have := hub_iso_sum_nineteen G Hub Iso hiso3; rw [hIso] at this; omega
  -- The rich-hub iso-cap, packaged per hub.
  have hcap : ∀ h ∈ Hub, G.degree h = 4 → g ≠ h → ¬G.Adj g h →
      (G.neighborFinset h ∩ Iso).card ≤ 2 := fun h hh h4 hgh hnadj =>
    isoDeg_le_two_of_nonadj_rich_nineteen G Hub Iso hshare hno2hub g h hg hh hgd h4 hgh hnadj hgiso
  -- The saturation bound, packaged.
  have hsat : (Hub.filter (fun h => G.degree h = 4 ∧ h ≠ g ∧ ¬G.Adj g h ∧
      2 ≤ (G.neighborFinset h ∩ Iso).card)).card ≤ 2 * (G.neighborFinset g ∩ Iso).card :=
    sat_bound_rich_nineteen G Hub Iso hisodeg3 hno2hub g hg hgd hgiso
  -- `g`'s three-way split: `hubDeg g + zDeg g ≤ 1` (rich, degree `4`).
  have hgsplit := nbr_split_three_nineteen G Hub Iso hdisj g
  rw [← hZdef] at hgsplit
  have hg_le1 : (G.neighborFinset g ∩ Hub).card
      + (G.neighborFinset g ∩ Z).card ≤ 1 := by rw [hgd] at hgsplit; omega
  -- The `Z`-skeleton.
  obtain ⟨z₁, z₂, hz12ne, hz₁Z, hz₂Z, hZeqpair, hadj12, hnob⟩ :=
    zslot_skeleton_deg5_nineteen G Hub Iso hiso3 hdisj hsum17 hdeg3 hisodeg3 hleak hdeg5 hT
  rw [← hZdef] at hz₁Z hz₂Z
  by_contra hcon
  push Not at hcon
  -- `∑_{D4} isoDeg = 21 − isoDeg d5`, and `isoDeg d5 ≤ 5`.
  have hD4sum : ∑ h ∈ D4, (G.neighborFinset h ∩ Iso).card
      = 21 - (G.neighborFinset d5 ∩ Iso).card := by
    have hpart : ∑ h ∈ D4, (G.neighborFinset h ∩ Iso).card
        + ∑ h ∈ D5, (G.neighborFinset h ∩ Iso).card = 21 := by
      rw [← Finset.sum_union hdisj45, hcover]; exact hledger
    rw [hd5eq, Finset.sum_singleton] at hpart
    omega
  have hd5le5 : (G.neighborFinset d5 ∩ Iso).card ≤ 5 := by
    calc (G.neighborFinset d5 ∩ Iso).card ≤ (G.neighborFinset d5).card :=
          Finset.card_le_card Finset.inter_subset_left
      _ = 5 := by rw [G.card_neighborFinset_eq_degree, hd5deg]
  have hgD4 : g ∈ D4 := (hmemD4 g).mpr ⟨hg, hgd⟩
  -- Uniform bound on a degree-`4` sub-family avoiding `g`: each hub is `≤ 2` (cap) with a `+1`
  -- bonus only for the (at most `hubDeg g`) hubs adjacent to `g`.
  have restBound : ∀ R : Finset (Fin 19), R ⊆ D4 → g ∉ R →
      ∑ x ∈ R, (G.neighborFinset x ∩ Iso).card ≤ 2 * R.card + (G.neighborFinset g ∩ Hub).card := by
    intro R hRsub hgR
    have hpt : ∀ x ∈ R, (G.neighborFinset x ∩ Iso).card ≤ 2 + (if G.Adj g x then 1 else 0) := by
      intro x hx
      have hxH : x ∈ Hub := ((hmemD4 x).mp (hRsub hx)).1
      have hx4 : G.degree x = 4 := ((hmemD4 x).mp (hRsub hx)).2
      have hxg : g ≠ x := fun he => hgR (he ▸ hx)
      by_cases hax : G.Adj g x
      · rw [if_pos hax]
        have hsp := nbr_split_three_nineteen G Hub Iso hdisj x
        have hxin : g ∈ G.neighborFinset x ∩ Hub :=
          Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hax.symm, hg⟩
        have hpos : 1 ≤ (G.neighborFinset x ∩ Hub).card := Finset.card_pos.mpr ⟨g, hxin⟩
        rw [hx4] at hsp; omega
      · rw [if_neg hax]; exact hcap x hxH hx4 hxg hax
    have hfilt : ∑ x ∈ R, (if G.Adj g x then 1 else 0)
        ≤ (G.neighborFinset g ∩ Hub).card := by
      rw [Finset.sum_boole]
      apply Finset.card_le_card
      intro x hx
      rw [Finset.mem_filter] at hx
      exact Finset.mem_inter.mpr
        ⟨(G.mem_neighborFinset _ _).mpr hx.2, ((hmemD4 x).mp (hRsub hx.1)).1⟩
    calc ∑ x ∈ R, (G.neighborFinset x ∩ Iso).card
        ≤ ∑ x ∈ R, (2 + (if G.Adj g x then 1 else 0)) := Finset.sum_le_sum hpt
      _ = 2 * R.card + ∑ x ∈ R, (if G.Adj g x then 1 else 0) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ 2 * R.card + (G.neighborFinset g ∩ Hub).card := by omega
  -- The `g`-meets-`Z` (hard) case, reusable for either endpoint.
  have keyB : ∀ za zb : Fin 19, za ∈ Z → zb ∈ Z → G.Adj g za → ¬G.Adj g zb → False := by
    intro za zb hzaZ hzbZ hgza hgzb
    -- `g` meets `za`, so `zDeg g ≥ 1`, forcing `hubDeg g = 0`, `isoDeg g = 3`.
    have hza_in : za ∈ G.neighborFinset g ∩ Z :=
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hgza, hzaZ⟩
    have hzdeg_pos : 1 ≤ (G.neighborFinset g ∩ Z).card := Finset.card_pos.mpr ⟨za, hza_in⟩
    have hhubg0 : (G.neighborFinset g ∩ Hub).card = 0 := by omega
    have hgiso3 : (G.neighborFinset g ∩ Iso).card = 3 := by
      have hgs := hgsplit; rw [hgd] at hgs; omega
    have hgnohub : ∀ h ∈ Hub, ¬G.Adj g h := by
      intro h hh hadj
      have hmem : h ∈ G.neighborFinset g ∩ Hub :=
        Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hadj, hh⟩
      rw [Finset.card_eq_zero.mp hhubg0] at hmem
      exact absurd hmem (Finset.notMem_empty h)
    -- The two hubs of the avoided `zb`.
    obtain ⟨_, hzb2, _⟩ :=
      zfacts_deg5_nineteen G Hub Iso hiso3 hdisj hsum17 hdeg3 hisodeg3 hleak zb hzbZ
    obtain ⟨p, q, hpqne, hpqeq⟩ := Finset.card_eq_two.mp hzb2
    have hpmem : p ∈ G.neighborFinset zb ∩ Hub := by rw [hpqeq]; exact Finset.mem_insert_self _ _
    have hqmem : q ∈ G.neighborFinset zb ∩ Hub := by
      rw [hpqeq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    rw [Finset.mem_inter, G.mem_neighborFinset] at hpmem hqmem
    obtain ⟨hzbp, hpHub⟩ := hpmem
    obtain ⟨hzbq, hqHub⟩ := hqmem
    have hgp : ¬G.Adj g p := hgnohub p hpHub
    have hgq : ¬G.Adj g q := hgnohub q hqHub
    have hgpne : g ≠ p := by rintro rfl; exact hgzb hzbp.symm
    have hgqne : g ≠ q := by rintro rfl; exact hgzb hzbq.symm
    have hfp : G.degree p = 4 → (G.neighborFinset p ∩ Iso).card = 0 := fun h4 => by
      have := hcon p zb hpHub h4 hzbZ hzbp hgzb hgp hgpne; omega
    have hfq : G.degree q = 4 → (G.neighborFinset q ∩ Iso).card = 0 := fun h4 => by
      have := hcon q zb hqHub h4 hzbZ hzbq hgzb hgq hgqne; omega
    -- The saturation kill: a degree-`4` forced-`0` hub with `d5` on the avoided `zb`.
    have satKill : ∀ p0 : Fin 19, p0 ∈ Hub → G.degree p0 = 4 → g ≠ p0 → ¬G.Adj g p0 →
        (G.neighborFinset p0 ∩ Iso).card = 0 → G.Adj d5 zb → False := by
      intro p0 hp0Hub hp0deg hgp0ne hgp0 hp0iso0 hd5zb
      have hd5le4 : (G.neighborFinset d5 ∩ Iso).card ≤ 4 := by
        have hsp := nbr_split_three_nineteen G Hub Iso hdisj d5
        rw [← hZdef] at hsp
        have hzin : zb ∈ G.neighborFinset d5 ∩ Z :=
          Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hd5zb, hzbZ⟩
        have hpos : 1 ≤ (G.neighborFinset d5 ∩ Z).card := Finset.card_pos.mpr ⟨zb, hzin⟩
        rw [hd5deg] at hsp; omega
      have hp0D4 : p0 ∈ D4 := (hmemD4 p0).mpr ⟨hp0Hub, hp0deg⟩
      have hp0erase : p0 ∈ D4.erase g := Finset.mem_erase.mpr ⟨fun h => hgp0ne h.symm, hp0D4⟩
      have hsum_split : (G.neighborFinset g ∩ Iso).card + ((G.neighborFinset p0 ∩ Iso).card
          + ∑ h ∈ (D4.erase g).erase p0, (G.neighborFinset h ∩ Iso).card)
          = ∑ h ∈ D4, (G.neighborFinset h ∩ Iso).card := by
        have e1 := Finset.add_sum_erase D4 (fun x => (G.neighborFinset x ∩ Iso).card) hgD4
        have e2 := Finset.add_sum_erase (D4.erase g)
          (fun x => (G.neighborFinset x ∩ Iso).card) hp0erase
        omega
      have hT7card : ((D4.erase g).erase p0).card = 7 := by
        rw [Finset.card_erase_of_mem hp0erase, Finset.card_erase_of_mem hgD4, hD4card]
      have hT7sub : (D4.erase g).erase p0 ⊆ D4 :=
        (Finset.erase_subset _ _).trans (Finset.erase_subset _ _)
      have hT7memg : ∀ h ∈ (D4.erase g).erase p0, h ≠ g := fun h hh =>
        (Finset.mem_erase.mp (Finset.mem_of_mem_erase hh)).1
      have hT7ge : 14 ≤ ∑ h ∈ (D4.erase g).erase p0, (G.neighborFinset h ∩ Iso).card := by
        rw [hgiso3, hp0iso0] at hsum_split; omega
      have hT7cap : ∀ h ∈ (D4.erase g).erase p0, (G.neighborFinset h ∩ Iso).card ≤ 2 := by
        intro h hh
        have hhHub : h ∈ Hub := ((hmemD4 h).mp (hT7sub hh)).1
        have hh4 : G.degree h = 4 := ((hmemD4 h).mp (hT7sub hh)).2
        exact hcap h hhHub hh4 (hT7memg h hh).symm (hgnohub h hhHub)
      have hT7ge2 : ∀ h ∈ (D4.erase g).erase p0, 2 ≤ (G.neighborFinset h ∩ Iso).card := by
        intro h0 hh0
        by_contra hlt; push Not at hlt
        have hsp := Finset.add_sum_erase ((D4.erase g).erase p0)
          (fun x => (G.neighborFinset x ∩ Iso).card) hh0
        have hb : ∑ x ∈ ((D4.erase g).erase p0).erase h0, (G.neighborFinset x ∩ Iso).card ≤ 12 := by
          have hle := Finset.sum_le_card_nsmul (((D4.erase g).erase p0).erase h0)
            (fun x => (G.neighborFinset x ∩ Iso).card) 2
            (fun x hx => hT7cap x (Finset.mem_of_mem_erase hx))
          rw [Finset.card_erase_of_mem hh0, hT7card] at hle
          simpa using hle
        omega
      have hT7fil : (D4.erase g).erase p0 ⊆ Hub.filter (fun h => G.degree h = 4 ∧ h ≠ g ∧
          ¬G.Adj g h ∧ 2 ≤ (G.neighborFinset h ∩ Iso).card) := by
        intro h hh
        have hhHub : h ∈ Hub := ((hmemD4 h).mp (hT7sub hh)).1
        have hh4 : G.degree h = 4 := ((hmemD4 h).mp (hT7sub hh)).2
        exact Finset.mem_filter.mpr
          ⟨hhHub, hh4, hT7memg h hh, hgnohub h hhHub, hT7ge2 h hh⟩
      have hfin : 7 ≤ 2 * (G.neighborFinset g ∩ Iso).card :=
        calc 7 = ((D4.erase g).erase p0).card := hT7card.symm
          _ ≤ _ := Finset.card_le_card hT7fil
          _ ≤ 2 * (G.neighborFinset g ∩ Iso).card := hsat
      rw [hgiso3] at hfin; omega
    -- Dispatch on the degrees of the two hubs of `zb`.
    rcases hpd p hpHub with hp4 | hp5
    · rcases hpd q hqHub with hq4 | hq5
      · -- Both degree `4`: both forced to iso-degree `0`; the direct count gives `∑ D4 ≤ 15 < 16`.
        have hpD4 : p ∈ D4 := (hmemD4 p).mpr ⟨hpHub, hp4⟩
        have hqD4 : q ∈ D4 := (hmemD4 q).mpr ⟨hqHub, hq4⟩
        have hperase : p ∈ D4.erase g := Finset.mem_erase.mpr ⟨fun h => hgpne h.symm, hpD4⟩
        have hqerase2 : q ∈ (D4.erase g).erase p := Finset.mem_erase.mpr
          ⟨hpqne.symm, Finset.mem_erase.mpr ⟨fun h => hgqne h.symm, hqD4⟩⟩
        have hsum6 : (G.neighborFinset g ∩ Iso).card + ((G.neighborFinset p ∩ Iso).card
            + ((G.neighborFinset q ∩ Iso).card
              + ∑ h ∈ ((D4.erase g).erase p).erase q, (G.neighborFinset h ∩ Iso).card))
            = ∑ h ∈ D4, (G.neighborFinset h ∩ Iso).card := by
          have e1 := Finset.add_sum_erase D4 (fun x => (G.neighborFinset x ∩ Iso).card) hgD4
          have e2 := Finset.add_sum_erase (D4.erase g)
            (fun x => (G.neighborFinset x ∩ Iso).card) hperase
          have e3 := Finset.add_sum_erase ((D4.erase g).erase p)
            (fun x => (G.neighborFinset x ∩ Iso).card) hqerase2
          omega
        have hR6card : (((D4.erase g).erase p).erase q).card = 6 := by
          rw [Finset.card_erase_of_mem hqerase2, Finset.card_erase_of_mem hperase,
            Finset.card_erase_of_mem hgD4, hD4card]
        have hR6sub : ((D4.erase g).erase p).erase q ⊆ D4 :=
          ((Finset.erase_subset _ _).trans (Finset.erase_subset _ _)).trans (Finset.erase_subset _ _)
        have hR6bound : ∑ h ∈ ((D4.erase g).erase p).erase q, (G.neighborFinset h ∩ Iso).card
            ≤ 12 := by
          have hle := Finset.sum_le_card_nsmul (((D4.erase g).erase p).erase q)
            (fun x => (G.neighborFinset x ∩ Iso).card) 2 (fun x hx => by
              have hxHub : x ∈ Hub := ((hmemD4 x).mp (hR6sub hx)).1
              have hx4 : G.degree x = 4 := ((hmemD4 x).mp (hR6sub hx)).2
              have hxg : x ≠ g :=
                (Finset.mem_erase.mp (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx))).1
              exact hcap x hxHub hx4 hxg.symm (hgnohub x hxHub))
          rw [hR6card] at hle; simpa using hle
        have hle15 : ∑ h ∈ D4, (G.neighborFinset h ∩ Iso).card ≤ 15 := by
          rw [hgiso3, hfp hp4, hfq hq4] at hsum6; omega
        omega
      · -- `q = d5` (degree `5`); saturation-kill `p`.
        have hqd5 : q = d5 := by
          have hmem : q ∈ D5 := (hmemD5 q).mpr ⟨hqHub, hq5⟩
          rw [hd5eq, Finset.mem_singleton] at hmem; exact hmem
        exact satKill p hpHub hp4 hgpne hgp (hfp hp4) (by rw [← hqd5]; exact hzbq.symm)
    · -- `p = d5` (degree `5`); `q` is degree `4`; saturation-kill `q`.
      have hpd5 : p = d5 := by
        have hmem : p ∈ D5 := (hmemD5 p).mpr ⟨hpHub, hp5⟩
        rw [hd5eq, Finset.mem_singleton] at hmem; exact hmem
      have hq4 : G.degree q = 4 := by
        rcases hpd q hqHub with h | h5
        · exact h
        · exfalso
          have hqd5 : q = d5 := by
            have hmem : q ∈ D5 := (hmemD5 q).mpr ⟨hqHub, h5⟩
            rw [hd5eq, Finset.mem_singleton] at hmem; exact hmem
          exact hpqne (hpd5.trans hqd5.symm)
      exact satKill q hqHub hq4 hgqne hgq (hfq hq4) (by rw [← hpd5]; exact hzbp.symm)
  -- Dispatch on which `Z`-vertices `g` meets.
  by_cases hgz₁ : G.Adj g z₁
  · by_cases hgz₂ : G.Adj g z₂
    · exact hnob g hg ⟨hgz₁, hgz₂⟩
    · exact keyB z₁ z₂ hz₁Z hz₂Z hgz₁ hgz₂
  · by_cases hgz₂ : G.Adj g z₂
    · exact keyB z₂ z₁ hz₂Z hz₁Z hgz₂ hgz₁
    · -- `g` meets no `Z`-vertex (CASE A).  Both `z₁, z₂` are avoided; count over `D4`.
      have hzg0 : (G.neighborFinset g ∩ Z).card = 0 := by
        rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
        intro x hx
        rw [Finset.mem_inter, G.mem_neighborFinset] at hx
        have hxpair : x ∈ ({z₁, z₂} : Finset (Fin 19)) := by rw [← hZeqpair, ← hZdef]; exact hx.2
        rw [Finset.mem_insert, Finset.mem_singleton] at hxpair
        rcases hxpair with rfl | rfl
        · exact hgz₁ hx.1
        · exact hgz₂ hx.1
      have hiso_hub : (G.neighborFinset g ∩ Iso).card + (G.neighborFinset g ∩ Hub).card = 4 := by
        have hgs := hgsplit; rw [hgd] at hgs; omega
      have hhub_le1 : (G.neighborFinset g ∩ Hub).card ≤ 1 := by omega
      -- The four `Z`-slot hubs.
      obtain ⟨_, hz1hub2, _⟩ :=
        zfacts_deg5_nineteen G Hub Iso hiso3 hdisj hsum17 hdeg3 hisodeg3 hleak z₁ hz₁Z
      obtain ⟨_, hz2hub2, _⟩ :=
        zfacts_deg5_nineteen G Hub Iso hiso3 hdisj hsum17 hdeg3 hisodeg3 hleak z₂ hz₂Z
      set ZH : Finset (Fin 19) := (G.neighborFinset z₁ ∩ Hub) ∪ (G.neighborFinset z₂ ∩ Hub)
        with hZHdef
      have hZHdisj : Disjoint (G.neighborFinset z₁ ∩ Hub) (G.neighborFinset z₂ ∩ Hub) := by
        rw [Finset.disjoint_left]; intro h h1 h2
        rw [Finset.mem_inter, G.mem_neighborFinset] at h1 h2
        exact hnob h h1.2 ⟨h1.1.symm, h2.1.symm⟩
      have hZHcard : ZH.card = 4 := by
        rw [hZHdef, Finset.card_union_of_disjoint hZHdisj, hz1hub2, hz2hub2]
      have hZHsubHub : ZH ⊆ Hub := by
        rw [hZHdef]; intro h hh
        rcases Finset.mem_union.mp hh with h1 | h1 <;> exact (Finset.mem_inter.mp h1).2
      set F : Finset (Fin 19) := ZH.filter (fun h => G.degree h = 4 ∧ ¬G.Adj g h) with hFdef
      have hFsubZH : F ⊆ ZH := Finset.filter_subset _ _
      have hFsubD4 : F ⊆ D4 := by
        intro h hh; rw [hFdef, Finset.mem_filter] at hh
        exact (hmemD4 h).mpr ⟨hZHsubHub hh.1, hh.2.1⟩
      have hgnotZH : g ∉ ZH := by
        rw [hZHdef, Finset.mem_union]; rintro (h1 | h1) <;>
          rw [Finset.mem_inter, G.mem_neighborFinset] at h1
        · exact hgz₁ h1.1.symm
        · exact hgz₂ h1.1.symm
      have hgnotF : g ∉ F := fun hh => hgnotZH (hFsubZH hh)
      -- Every hub in `F` is forced to iso-degree `0`.
      have hFforced : ∀ h ∈ F, (G.neighborFinset h ∩ Iso).card = 0 := by
        intro h hh
        rw [hFdef, Finset.mem_filter] at hh
        obtain ⟨hhZH, hh4, hhna⟩ := hh
        have hhHub : h ∈ Hub := hZHsubHub hhZH
        rw [hZHdef, Finset.mem_union] at hhZH
        rcases hhZH with h1 | h1
        · rw [Finset.mem_inter, G.mem_neighborFinset] at h1
          have hgh : g ≠ h := by rintro rfl; exact hgz₁ h1.1.symm
          have := hcon h z₁ hhHub hh4 hz₁Z h1.1 hgz₁ hhna hgh; omega
        · rw [Finset.mem_inter, G.mem_neighborFinset] at h1
          have hgh : g ≠ h := by rintro rfl; exact hgz₂ h1.1.symm
          have := hcon h z₂ hhHub hh4 hz₂Z h1.1 hgz₂ hhna hgh; omega
      have hFsum0 : ∑ h ∈ F, (G.neighborFinset h ∩ Iso).card = 0 := Finset.sum_eq_zero hFforced
      -- Decompose the `D4` iso-sum.
      have hsd := Finset.sum_sdiff (f := fun x => (G.neighborFinset x ∩ Iso).card) hFsubD4
      have hgD4F : g ∈ D4 \ F := Finset.mem_sdiff.mpr ⟨hgD4, hgnotF⟩
      have hsplitA := Finset.add_sum_erase (D4 \ F)
        (fun x => (G.neighborFinset x ∩ Iso).card) hgD4F
      have hRbound := restBound ((D4 \ F).erase g)
        ((Finset.erase_subset _ _).trans Finset.sdiff_subset) (Finset.notMem_erase g _)
      have hRcard : ((D4 \ F).erase g).card = (D4 \ F).card - 1 := Finset.card_erase_of_mem hgD4F
      have hDFcard : (D4 \ F).card = 9 - F.card := by
        rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hFsubD4, hD4card]
      -- `|ZH \ F| ≤ |ZH ∩ {d5}| + hubDeg g`, and `|F| + |ZH \ F| = 4`.
      have hZHFsub : ZH \ F ⊆ (ZH ∩ {d5}) ∪ (G.neighborFinset g ∩ Hub) := by
        intro h hh
        rw [Finset.mem_sdiff] at hh
        obtain ⟨hhZH, hhnF⟩ := hh
        have hhHub : h ∈ Hub := hZHsubHub hhZH
        by_cases hd4 : G.degree h = 4
        · have hadj : G.Adj g h := by
            by_contra hna; exact hhnF (Finset.mem_filter.mpr ⟨hhZH, hd4, hna⟩)
          exact Finset.mem_union_right _
            (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hadj, hhHub⟩)
        · have hd5' : G.degree h = 5 := by
            rcases hpd h hhHub with h4 | h5
            · exact absurd h4 hd4
            · exact h5
          have hhd5 : h = d5 := by
            have : h ∈ D5 := (hmemD5 h).mpr ⟨hhHub, hd5'⟩
            rw [hd5eq, Finset.mem_singleton] at this; exact this
          exact Finset.mem_union_left _
            (Finset.mem_inter.mpr ⟨hhZH, Finset.mem_singleton.mpr hhd5⟩)
      have hZHFcard : (ZH \ F).card
          ≤ (ZH ∩ {d5}).card + (G.neighborFinset g ∩ Hub).card :=
        (Finset.card_le_card hZHFsub).trans (Finset.card_union_le _ _)
      have hFle4 : F.card ≤ 4 := hZHcard ▸ Finset.card_le_card hFsubZH
      have hFZH : F.card + (ZH \ F).card = 4 := by
        rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hFsubZH, hZHcard]; omega
      have hzc1 : (ZH ∩ {d5}).card ≤ 1 :=
        (Finset.card_le_card Finset.inter_subset_right).trans (by rw [Finset.card_singleton])
      have hzi : (ZH ∩ {d5}).card = 0 ∨ (G.neighborFinset d5 ∩ Iso).card ≤ 4 := by
        by_cases hd5ZH : d5 ∈ ZH
        · right
          rw [hZHdef, Finset.mem_union] at hd5ZH
          have hd5zpos : 1 ≤ (G.neighborFinset d5 ∩ Z).card := by
            rcases hd5ZH with h1 | h1
            · rw [Finset.mem_inter, G.mem_neighborFinset] at h1
              exact Finset.card_pos.mpr
                ⟨z₁, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr h1.1.symm, hz₁Z⟩⟩
            · rw [Finset.mem_inter, G.mem_neighborFinset] at h1
              exact Finset.card_pos.mpr
                ⟨z₂, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr h1.1.symm, hz₂Z⟩⟩
          have hsp := nbr_split_three_nineteen G Hub Iso hdisj d5
          rw [← hZdef, hd5deg] at hsp; omega
        · left
          rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
          intro x hx
          rw [Finset.mem_inter, Finset.mem_singleton] at hx
          exact hd5ZH (hx.2 ▸ hx.1)
      omega

end N19

end ACMax
