import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N19.TwoHubCornerDeg5ZLeaf
import ACMaxConjecture.SmallCases.N19.TwoHubSelect
import ACMaxConjecture.SmallCases.N19.ZVertex
import ACMaxConjecture.SmallCases.N19.Deg5RichCap
import ACMaxConjecture.SmallCases.N19.Deg5Rich1041Count
import ACMaxConjecture.SmallCases.N19.Deg5Rich1041Blocker
import ACMaxConjecture.SmallCases.N19.Deg5Rich1041K23
import ACMaxConjecture.SmallCases.N19.Deg5Rich1041OctaPoorCounts
import ACMaxConjecture.SmallCases.N19.Deg5Rich1041BothPoorBudget

import ACMaxConjecture.SmallCases.N19.R5Octahedron

/-! # CASE C both-poor, profile A: `isoDeg g = 3` (`n = 19`) -/
namespace ACMax
open scoped Classical

namespace N19

set_option maxHeartbeats 1000000 in
/-- **Both-poor profile A.** -/
theorem octahedron_both_poor_profile_a_1041_nineteen (G : SimpleGraph (Fin 19))
    (Hub Iso : Finset (Fin 19))
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdisj : Disjoint Hub Iso) (hsum17 : Hub.card + Iso.card = 17)
    (hdeg3 : ∀ v : Fin 19, 3 ≤ G.degree v) (hisodeg3 : ∀ t ∈ Iso, G.degree t = 3)
    (hleak : ∑ h ∈ Hub, (G.neighborFinset h ∩ (Finset.univ \ (Hub ∪ Iso))).card ≤ 4)
    (hdeg : ∀ h ∈ Hub, 4 ≤ G.degree h) (hdeg5 : ∀ h ∈ Hub, G.degree h ≤ 5)
    (hHub : Hub.card = 10) (hIso : Iso.card = 7) (hdsum : ∑ w ∈ Hub, G.degree w = 41)
    (hT : ¬∃ x y z : Fin 19, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 11)
    (hC4 : ¬∃ a b c d : Fin 19, ({a, b, c, d} : Finset (Fin 19)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (_hK23 : ¬∃ a b c d e : Fin 19, ({a, b, c, d, e} : Finset (Fin 19)).card = 5 ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
      G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 19)
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hno2hub : ¬∃ h₁ h₂ : Fin 19, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card)
    (g : Fin 19) (hg : g ∈ Hub) (hgd : G.degree g = 4)
    (hgiso : 3 ≤ (G.neighborFinset g ∩ Iso).card)
    (h₂ z : Fin 19) (hh₂ : h₂ ∈ Hub) (hd₂ : G.degree h₂ = 4)
    (hzZ : z ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 19)))
    (hz2 : G.Adj z h₂) (hgz : ¬G.Adj g z) (hg2 : ¬G.Adj g h₂)
    (hpoor : (G.neighborFinset h₂ ∩ Iso).card = 1)
    (hshared : (G.neighborFinset g ∩ G.neighborFinset h₂ ∩ Iso).card = 1)
    (hblock : ∀ x : Fin 19, x ∈ Hub → G.degree x = 4 →
      2 ≤ (G.neighborFinset x ∩ Iso).card →
      G.neighborFinset x ∩ G.neighborFinset h₂ ∩ Iso ≠ ∅ ∨ G.Adj x h₂ ∨ G.Adj x z)
    (f x : Fin 19) (hfHub : f ∈ Hub) (hfd : G.degree f = 5)
    (hfiso5 : (G.neighborFinset f ∩ Iso).card = 5)
    (_hxHub : x ∈ Hub) (_hxd : G.degree x = 4)
    (_hxiso3 : 3 ≤ (G.neighborFinset x ∩ Iso).card) (_hxf : x ≠ f)
    (_hnadj : ¬G.Adj x f)
    (_hsh : ¬ 3 ≤ (G.neighborFinset x ∩ G.neighborFinset f ∩ Iso).card)
    (hstruct : ∃ c r_t r_z a b : Fin 19,
      Hub.filter (fun h => G.degree h = 4 ∧ 2 ≤ (G.neighborFinset h ∩ Iso).card)
        = ({g, r_t, r_z, a, b} : Finset (Fin 19)) ∧
      ({g, r_t, r_z, a, b} : Finset (Fin 19)).card = 5 ∧
      c ∈ Iso ∧ G.Adj g c ∧ G.Adj h₂ c ∧ G.Adj r_t c ∧
      G.neighborFinset c ∩ Hub = ({h₂, g, r_t} : Finset (Fin 19)) ∧
      G.neighborFinset z ∩ Hub = ({h₂, r_z} : Finset (Fin 19)) ∧
      G.neighborFinset h₂ ∩ Hub = ({a, b} : Finset (Fin 19)) ∧
      G.Adj r_z z ∧ G.Adj a h₂ ∧ G.Adj b h₂ ∧
      r_t ∈ Hub ∧ G.degree r_t = 4 ∧ r_z ∈ Hub ∧ G.degree r_z = 4 ∧
      a ∈ Hub ∧ G.degree a = 4 ∧ b ∈ Hub ∧ G.degree b = 4)
    (z' p q : Fin 19)
    (_hz'Z : z' ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 19)))
    (_hzz' : G.Adj z z') (_hz'deg3 : G.degree z' = 3)
    (_hz'iso0 : (G.neighborFinset z' ∩ Iso).card = 0)
    (_hNz'eq : G.neighborFinset z' ∩ Hub = ({p, q} : Finset (Fin 19)))
    (_hp : p ∈ Hub) (_hq : q ∈ Hub) (_hdp : G.degree p = 4) (_hdq : G.degree q = 4)
    (_hpq : p ≠ q) (_hz'p : G.Adj z' p) (_hz'q : G.Adj z' q)
    (_hnpq : ¬G.Adj p q)
    (_hshare0 : (G.neighborFinset p ∩ G.neighborFinset q ∩ Iso).card = 0)
    (_hppoor : (G.neighborFinset p ∩ Iso).card ≤ 1)
    (_hqpoor : (G.neighborFinset q ∩ Iso).card ≤ 1)
    (_hph₂ : p ≠ h₂) (_hqh₂ : q ≠ h₂)
    (w : Fin 19) (_hwHub : w ∈ Hub) (_hwh₂ : w ≠ h₂) (_hwp : w ≠ p) (_hwq : w ≠ q)
    (_hwf : w ≠ f) (_hwd : G.degree w = 4) (_hwiso : (G.neighborFinset w ∩ Iso).card = 1)
    (_hpworqw : G.Adj p w ∨ G.Adj q w) (_hzdeg : G.degree z = 3)
    (_heRR : (∑ r ∈ Hub.filter (fun h => G.degree h = 4 ∧ 2 ≤ (G.neighborFinset h ∩ Iso).card),
      (G.neighborFinset r ∩ Hub.filter
        (fun h => G.degree h = 4 ∧ 2 ≤ (G.neighborFinset h ∩ Iso).card)).card) ≤ 2)
    (hg3 : (G.neighborFinset g ∩ Iso).card = 3) :
    False := by
  classical
  obtain ⟨c, r_t, r_z, a, b, hRfilter, hRcard5, hcIso, hgc, _hh₂c, hr_tc, hNc, _hNz, _hNh₂,
    hr_zz, hah₂, hbh₂, hr_tHub, hr_td, hr_zHub, hr_zd, haHub, had, hbHub, hbd⟩ := hstruct
  -- === Basic membership / degree facts. ===
  have hcdeg : G.degree c = 3 := hisodeg3 c hcIso
  have hc_notHub : c ∉ Hub := Finset.disjoint_right.mp hdisj hcIso
  have hz_notHub : z ∉ Hub := fun hc => (Finset.mem_sdiff.mp hzZ).2 (Finset.mem_union_left _ hc)
  have hz_notIso : z ∉ Iso := fun hc => (Finset.mem_sdiff.mp hzZ).2 (Finset.mem_union_right _ hc)
  have hgnotIso : g ∉ Iso := Finset.disjoint_left.mp hdisj hg
  have hz_ne_g : z ≠ g := by intro h; subst h; exact hz_notHub hg
  have hh₂_ne_g : h₂ ≠ g := by intro h; have hp := hpoor; rw [h] at hp; omega
  -- === Distinctness `g ≠ r_t, r_z, a, b`. ===
  have pair_le : ∀ y1 y2 : Fin 19, ({y1, y2} : Finset (Fin 19)).card ≤ 2 := by
    intro y1 y2
    have := Finset.card_insert_le y1 ({y2} : Finset (Fin 19))
    simp only [Finset.card_singleton] at this; omega
  have card3_ne : ∀ y1 y2 y3 : Fin 19, ({y1, y2, y3} : Finset (Fin 19)).card = 3 →
      y1 ≠ y2 ∧ y1 ≠ y3 ∧ y2 ≠ y3 := by
    intro y1 y2 y3 hc
    refine ⟨?_, ?_, ?_⟩
    · rintro rfl
      rw [Finset.insert_idem] at hc; have := pair_le y1 y3; omega
    · rintro rfl
      rw [Finset.insert_eq_self.mpr (show y1 ∈ ({y2, y1} : Finset (Fin 19)) by simp)] at hc
      have := pair_le y2 y1; omega
    · rintro rfl
      rw [Finset.insert_eq_self.mpr (show y2 ∈ ({y2} : Finset (Fin 19)) by simp)] at hc
      have := pair_le y1 y2; omega
  have hc3card : ({h₂, g, r_t} : Finset (Fin 19)).card = 3 := hNc ▸ hiso3 c hcIso
  obtain ⟨_, _, hg_rt⟩ := card3_ne h₂ g r_t hc3card
  have hg_rz : g ≠ r_z := fun h => hgz (h ▸ hr_zz)
  have hg_a : g ≠ a := fun h => hg2 (h ▸ hah₂)
  have hg_b : g ≠ b := fun h => hg2 (h ▸ hbh₂)
  -- === `¬Adj g r_t` (triangle `{g, r_t, c}`, `Σ = 4 + 4 + 3 = 11`). ===
  have tri : ∀ u v w : Fin 19, u ≠ v → v ≠ w → u ≠ w →
      G.Adj u v → G.Adj v w → G.Adj u w →
      G.degree u + G.degree v + G.degree w ≤ 11 → False :=
    fun u v w huv hvw huw auv avw auw hd => hT ⟨u, v, w, huv, hvw, huw, auv, avw, auw, hd⟩
  have hngrt : ¬ G.Adj g r_t := fun hadj =>
    tri g r_t c hg_rt (fun h => hc_notHub (h ▸ hr_tHub))
      (fun h => hc_notHub (h ▸ hg)) hadj hr_tc hgc (by rw [hgd, hr_td, hcdeg])
  -- === Saturation: an isoDeg-`3` rich hub adjacent to `g` has `N = 3` twins `+ g`. ===
  have satn : ∀ r : Fin 19, G.degree r = 4 → 3 ≤ (G.neighborFinset r ∩ Iso).card →
      G.Adj g r → ∀ y : Fin 19, G.Adj r y → y ∈ Iso ∨ y = g := by
    intro r hdr hriso hgr y hry
    have hgN : g ∈ G.neighborFinset r := (G.mem_neighborFinset r g).mpr hgr.symm
    have hsub : (G.neighborFinset r ∩ Iso) ∪ ({g} : Finset (Fin 19)) ⊆ G.neighborFinset r :=
      Finset.union_subset Finset.inter_subset_left (Finset.singleton_subset_iff.mpr hgN)
    have hdisjAg : Disjoint (G.neighborFinset r ∩ Iso) ({g} : Finset (Fin 19)) :=
      Finset.disjoint_singleton_right.mpr (fun hm => hgnotIso (Finset.mem_inter.mp hm).2)
    have hcardU : ((G.neighborFinset r ∩ Iso) ∪ ({g} : Finset (Fin 19))).card
        = (G.neighborFinset r ∩ Iso).card + 1 := by
      rw [Finset.card_union_of_disjoint hdisjAg, Finset.card_singleton]
    have hNrcard : (G.neighborFinset r).card = 4 := by
      rw [G.card_neighborFinset_eq_degree, hdr]
    have hNreq : (G.neighborFinset r ∩ Iso) ∪ ({g} : Finset (Fin 19)) = G.neighborFinset r :=
      Finset.eq_of_subset_of_card_le hsub (by rw [hNrcard, hcardU]; omega)
    have hyN : y ∈ G.neighborFinset r := (G.mem_neighborFinset r y).mpr hry
    rw [← hNreq, Finset.mem_union, Finset.mem_singleton] at hyN
    rcases hyN with hyI | hyg
    · exact Or.inl (Finset.mem_inter.mp hyI).2
    · exact Or.inr hyg
  -- === Node-2 counting: `∑_R isoDeg = 12`. ===
  have hRiso12 : (∑ r ∈ ({g, r_t, r_z, a, b} : Finset (Fin 19)),
      (G.neighborFinset r ∩ Iso).card) = 12 := by
    have h := (octahedron_poor_counts_share2_1041_nineteen G Hub Iso hiso3 hdisj hsum17 hdeg3
      hisodeg3 hleak hdeg hdeg5 hHub hIso hdsum hshare hno2hub hC4 hT g hg hgd hgiso h₂ z hh₂ hd₂
      hzZ hz2 hgz hg2 hpoor hshared hblock f hfHub hfd hfiso5).2.2
    rwa [hRfilter] at h
  -- === The other four rich hubs sum to `9`, so one has isoDeg `≥ 3`. ===
  have hgS : g ∈ ({g, r_t, r_z, a, b} : Finset (Fin 19)) := by simp
  have hcardErase : (({g, r_t, r_z, a, b} : Finset (Fin 19)).erase g).card = 4 := by
    rw [Finset.card_erase_of_mem hgS, hRcard5]
  have hsumErase : (∑ r ∈ (({g, r_t, r_z, a, b} : Finset (Fin 19)).erase g),
      (G.neighborFinset r ∩ Iso).card) = 9 := by
    have h : (G.neighborFinset g ∩ Iso).card
        + (∑ r ∈ (({g, r_t, r_z, a, b} : Finset (Fin 19)).erase g),
          (G.neighborFinset r ∩ Iso).card) = 12 := by
      rw [← hRiso12]
      exact Finset.add_sum_erase _ (fun r => (G.neighborFinset r ∩ Iso).card) hgS
    omega
  have hex : ∃ rs ∈ (({g, r_t, r_z, a, b} : Finset (Fin 19)).erase g),
      3 ≤ (G.neighborFinset rs ∩ Iso).card := by
    by_contra hcon
    push Not at hcon
    have hle : (∑ rs ∈ (({g, r_t, r_z, a, b} : Finset (Fin 19)).erase g),
        (G.neighborFinset rs ∩ Iso).card)
        ≤ (({g, r_t, r_z, a, b} : Finset (Fin 19)).erase g).card • 2 :=
      Finset.sum_le_card_nsmul _ _ 2 (fun rs hrs => by have := hcon rs hrs; omega)
    rw [hcardErase, smul_eq_mul] at hle
    omega
  obtain ⟨rs, hrsErase, hrsiso⟩ := hex
  have hrsg : rs ≠ g := Finset.ne_of_mem_erase hrsErase
  have hrsmem : rs ∈ ({g, r_t, r_z, a, b} : Finset (Fin 19)) := Finset.mem_of_mem_erase hrsErase
  simp only [Finset.mem_insert, Finset.mem_singleton] at hrsmem
  -- === Each candidate for the second isoDeg-`3` hub is impossible. ===
  rcases hrsmem with heq | heq | heq | heq | heq
  · exact hrsg heq
  · rw [heq] at hrsiso
    exact hngrt (rich_isodeg3_pair_adj_r5_nineteen G Hub Iso hshare hno2hub g r_t hg hr_tHub hgd
      hr_td hg_rt hgiso hrsiso)
  · rw [heq] at hrsiso
    rcases satn r_z hr_zd hrsiso (rich_isodeg3_pair_adj_r5_nineteen G Hub Iso hshare hno2hub g r_z
      hg hr_zHub hgd hr_zd hg_rz hgiso hrsiso) z hr_zz with h | h
    · exact hz_notIso h
    · exact hz_ne_g h
  · rw [heq] at hrsiso
    rcases satn a had hrsiso (rich_isodeg3_pair_adj_r5_nineteen G Hub Iso hshare hno2hub g a
      hg haHub hgd had hg_a hgiso hrsiso) h₂ hah₂ with h | h
    · exact (Finset.disjoint_left.mp hdisj hh₂) h
    · exact hh₂_ne_g h
  · rw [heq] at hrsiso
    rcases satn b hbd hrsiso (rich_isodeg3_pair_adj_r5_nineteen G Hub Iso hshare hno2hub g b
      hg hbHub hgd hbd hg_b hgiso hrsiso) h₂ hbh₂ with h | h
    · exact (Finset.disjoint_left.mp hdisj hh₂) h
    · exact hh₂_ne_g h

end N19

end ACMax
