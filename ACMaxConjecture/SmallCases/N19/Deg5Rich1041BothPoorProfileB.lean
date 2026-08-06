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


/-! # CASE C both-poor, profile B: `isoDeg g = 4` (`n = 19`) -/
namespace ACMax
open scoped Classical

namespace N19

set_option maxHeartbeats 1000000 in
/-- **Both-poor profile B.** -/
theorem octahedron_both_poor_profile_b_1041_nineteen (G : SimpleGraph (Fin 19))
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
    (hK23 : ¬∃ a b c d e : Fin 19, ({a, b, c, d, e} : Finset (Fin 19)).card = 5 ∧
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
    (_hpworqw : G.Adj p w ∨ G.Adj q w) (hzdeg : G.degree z = 3)
    (heRR : (∑ r ∈ Hub.filter (fun h => G.degree h = 4 ∧ 2 ≤ (G.neighborFinset h ∩ Iso).card),
      (G.neighborFinset r ∩ Hub.filter
        (fun h => G.degree h = 4 ∧ 2 ≤ (G.neighborFinset h ∩ Iso).card)).card) ≤ 2)
    (hg4 : (G.neighborFinset g ∩ Iso).card = 4) :
    False := by
  classical
  obtain ⟨c, r_t, r_z, a, b, hRfilter, hRcard, hcIso, hgc, hh₂c, hr_tc, hNc, hNz, hNh₂,
    hr_zz, hah₂, hbh₂, hr_tHub, hr_td, hr_zHub, hr_zd, haHub, had, hbHub, hbd⟩ := hstruct
  have hzf := zfacts_deg5_nineteen G Hub Iso hiso3 hdisj hsum17 hdeg3 hisodeg3 hleak
  have hzhub2 : (G.neighborFinset z ∩ Hub).card = 2 := (hzf z hzZ).2.1
  have hcdeg : G.degree c = 3 := hisodeg3 c hcIso
  have hc_notHub : c ∉ Hub := Finset.disjoint_right.mp hdisj hcIso
  have hz_notHub : z ∉ Hub := fun hc => (Finset.mem_sdiff.mp hzZ).2 (Finset.mem_union_left _ hc)
  have hisoHub : ∀ t ∈ Iso, ∀ w : Fin 19, G.Adj t w → w ∉ Iso := by
    intro t ht w htw hwIso
    have hcard3 : (G.neighborFinset t ∩ Hub).card = 3 := hiso3 t ht
    have hdt : (G.neighborFinset t).card = 3 := by
      rw [G.card_neighborFinset_eq_degree]; exact hisodeg3 t ht
    have heq : G.neighborFinset t ∩ Hub = G.neighborFinset t :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by rw [hcard3, hdt])
    have hwHub : w ∈ Hub := by
      have hm : w ∈ G.neighborFinset t ∩ Hub := by
        rw [heq]; exact (G.mem_neighborFinset t w).mpr htw
      exact (Finset.mem_inter.mp hm).2
    exact Finset.disjoint_left.mp hdisj hwHub hwIso
  have pair_le : ∀ y1 y2 : Fin 19, ({y1, y2} : Finset (Fin 19)).card ≤ 2 := by
    intro y1 y2
    have := Finset.card_insert_le y1 ({y2} : Finset (Fin 19))
    simp only [Finset.card_singleton] at this; omega
  have quad_le : ∀ w x y z2 : Fin 19, ({w, x, y, z2} : Finset (Fin 19)).card ≤ 4 := by
    intro w x y z2
    have h2 := pair_le y z2
    have h3 : ({x, y, z2} : Finset (Fin 19)).card ≤ 3 := by
      have := Finset.card_insert_le x ({y, z2} : Finset (Fin 19)); omega
    have := Finset.card_insert_le w ({x, y, z2} : Finset (Fin 19)); omega
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
  have card2_ne : ∀ y1 y2 : Fin 19, ({y1, y2} : Finset (Fin 19)).card = 2 → y1 ≠ y2 := by
    intro y1 y2 hc he; subst he
    rw [Finset.insert_eq_self.mpr (Finset.mem_singleton_self y1), Finset.card_singleton] at hc
    omega
  have hc3card : ({h₂, g, r_t} : Finset (Fin 19)).card = 3 := hNc ▸ hiso3 c hcIso
  obtain ⟨_, _, hg_rt⟩ := card3_ne h₂ g r_t hc3card
  have hr_z_ne_h₂ : r_z ≠ h₂ := (card2_ne h₂ r_z (by rw [← hNz]; exact hzhub2)).symm
  have hg_rz : g ≠ r_z := by intro h; apply hgz; rw [h]; exact hr_zz
  have hg_a : g ≠ a := by intro h; apply hg2; rw [h]; exact hah₂
  have hg_b : g ≠ b := by intro h; apply hg2; rw [h]; exact hbh₂
  have tri : ∀ u v w : Fin 19, u ≠ v → v ≠ w → u ≠ w →
      G.Adj u v → G.Adj v w → G.Adj u w →
      G.degree u + G.degree v + G.degree w ≤ 11 → False :=
    fun u v w huv hvw huw auv avw auw hd => hT ⟨u, v, w, huv, hvw, huw, auv, avw, auw, hd⟩
  have hnh₂rz : ¬ G.Adj h₂ r_z := fun hadj =>
    tri h₂ r_z z (G.ne_of_adj hadj) (fun h => hz_notHub (h ▸ hr_zHub))
      (fun h => hz_notHub (h ▸ hh₂)) hadj hr_zz hz2.symm (by rw [hd₂, hr_zd, hzdeg])
  have hnh₂rt : ¬ G.Adj h₂ r_t := fun hadj =>
    tri h₂ r_t c (G.ne_of_adj hadj) (fun h => hc_notHub (h ▸ hr_tHub))
      (fun h => hc_notHub (h ▸ hh₂)) hadj hr_tc hh₂c (by rw [hd₂, hr_td, hcdeg])
  have hngrt : ¬ G.Adj g r_t := fun hadj =>
    tri g r_t c hg_rt (fun h => hc_notHub (h ▸ hr_tHub))
      (fun h => hc_notHub (h ▸ hg)) hadj hr_tc hgc (by rw [hgd, hr_td, hcdeg])
  have hrz_a : r_z ≠ a := fun h => hnh₂rz (h ▸ hah₂.symm)
  have hrz_b : r_z ≠ b := fun h => hnh₂rz (h ▸ hbh₂.symm)
  have hrt_a : r_t ≠ a := fun h => hnh₂rt (h ▸ hah₂.symm)
  have hrt_b : r_t ≠ b := fun h => hnh₂rt (h ▸ hbh₂.symm)
  have hrt_rz : r_t ≠ r_z := by
    intro h
    rw [h, Finset.insert_idem] at hRcard
    have := quad_le g r_z a b; omega
  have hab : a ≠ b := by
    intro h
    rw [h, Finset.insert_eq_self.mpr (Finset.mem_singleton_self b)] at hRcard
    have := quad_le g r_t r_z b; omega
  have hrichmem : ∀ w : Fin 19, (w = r_t ∨ w = r_z ∨ w = a ∨ w = b) →
      2 ≤ (G.neighborFinset w ∩ Iso).card := by
    intro w hw
    have hwF : w ∈ Hub.filter (fun h => G.degree h = 4 ∧ 2 ≤ (G.neighborFinset h ∩ Iso).card) := by
      rw [hRfilter]; simp only [Finset.mem_insert, Finset.mem_singleton]
      rcases hw with rfl | rfl | rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
    exact (Finset.mem_filter.mp hwF).2.2
  have hrt2 : 2 ≤ (G.neighborFinset r_t ∩ Iso).card := hrichmem r_t (Or.inl rfl)
  have hrz2 : 2 ≤ (G.neighborFinset r_z ∩ Iso).card := hrichmem r_z (Or.inr (Or.inl rfl))
  have ha2iso : 2 ≤ (G.neighborFinset a ∩ Iso).card := hrichmem a (Or.inr (Or.inr (Or.inl rfl)))
  have hb2iso : 2 ≤ (G.neighborFinset b ∩ Iso).card := hrichmem b (Or.inr (Or.inr (Or.inr rfl)))
  have hsum12 : (G.neighborFinset g ∩ Iso).card + (G.neighborFinset r_t ∩ Iso).card
      + (G.neighborFinset r_z ∩ Iso).card + (G.neighborFinset a ∩ Iso).card
      + (G.neighborFinset b ∩ Iso).card = 12 := by
    have hs := (octahedron_poor_counts_share2_1041_nineteen G Hub Iso hiso3 hdisj hsum17 hdeg3
      hisodeg3 hleak hdeg hdeg5 hHub hIso hdsum hshare hno2hub hC4 hT g hg hgd hgiso h₂ z hh₂ hd₂
      hzZ hz2 hgz hg2 hpoor hshared hblock f hfHub hfd hfiso5).2.2
    rw [hRfilter] at hs
    rw [Finset.sum_insert (by simp [hg_rt, hg_rz, hg_a, hg_b]),
      Finset.sum_insert (by simp [hrt_rz, hrt_a, hrt_b]),
      Finset.sum_insert (by simp [hrz_a, hrz_b]),
      Finset.sum_insert (by simp [hab]), Finset.sum_singleton] at hs
    omega
  have hisole : ∀ w : Fin 19, (G.neighborFinset w ∩ Iso).card ≤ G.degree w := fun w =>
    (Finset.card_le_card Finset.inter_subset_left).trans
      (le_of_eq (G.card_neighborFinset_eq_degree w))
  have hrtiso2 : (G.neighborFinset r_t ∩ Iso).card = 2 := by
    have hrtle := hisole r_t; rw [hr_td] at hrtle; omega
  have hfNIso : G.neighborFinset f ∩ Iso = G.neighborFinset f :=
    Finset.eq_of_subset_of_card_le Finset.inter_subset_left
      (by rw [hfiso5, G.card_neighborFinset_eq_degree, hfd])
  have hnadj_gf : ¬ G.Adj g f := by
    intro hadj
    have hgNf : g ∈ G.neighborFinset f := (G.mem_neighborFinset f g).mpr hadj.symm
    rw [← hfNIso] at hgNf
    exact Finset.disjoint_left.mp hdisj hg (Finset.mem_inter.mp hgNf).2
  have hgfshare : (G.neighborFinset g ∩ G.neighborFinset f ∩ Iso).card ≤ 2 := by
    by_contra hcon
    exact highshare_k23_1041_nineteen G Iso hK23 hisoHub hisodeg3 g f hgd hfd hnadj_gf (by omega)
  have hcInrt : c ∈ G.neighborFinset r_t ∩ Iso :=
    Finset.mem_inter.mpr ⟨(G.mem_neighborFinset r_t c).mpr hr_tc, hcIso⟩
  have hecard : ((G.neighborFinset r_t ∩ Iso).erase c).card = 1 := by
    rw [Finset.card_erase_of_mem hcInrt, hrtiso2]
  obtain ⟨e, he_eq⟩ := Finset.card_eq_one.mp hecard
  have heMem : e ∈ (G.neighborFinset r_t ∩ Iso).erase c := by
    rw [he_eq]; exact Finset.mem_singleton_self e
  have hec : e ≠ c := (Finset.mem_erase.mp heMem).1
  have heInrt : e ∈ G.neighborFinset r_t ∩ Iso := (Finset.mem_erase.mp heMem).2
  have heIso : e ∈ Iso := (Finset.mem_inter.mp heInrt).2
  have hrte : G.Adj r_t e := (G.mem_neighborFinset r_t e).mp (Finset.mem_inter.mp heInrt).1
  have hNrtIso : G.neighborFinset r_t ∩ Iso = {c, e} := by
    have hsub : ({c, e} : Finset (Fin 19)) ⊆ G.neighborFinset r_t ∩ Iso := by
      intro y hy; simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl
      exacts [hcInrt, heInrt]
    have hc2 : ({c, e} : Finset (Fin 19)).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simp [Ne.symm hec]), Finset.card_singleton]
    exact (Finset.eq_of_subset_of_card_le hsub (le_of_eq (hrtiso2.trans hc2.symm))).symm
  have hshare_e : ∀ v : Fin 19, v ∈ Hub → G.degree v = 4 →
      2 ≤ (G.neighborFinset v ∩ Iso).card → ¬ G.Adj r_t v → v ≠ h₂ → v ≠ g → v ≠ r_t →
      G.Adj v e := by
    intro v hvHub hvd hviso hnvadj hvh₂ hvg hvrt
    have hshpos : 1 ≤ (G.neighborFinset r_t ∩ G.neighborFinset v ∩ Iso).card := by
      by_contra h0
      have hs0 : (G.neighborFinset r_t ∩ G.neighborFinset v ∩ Iso).card = 0 := by omega
      apply hno2hub
      refine ⟨r_t, v, hr_tHub, hvHub, hr_td, hvd, Ne.symm hvrt, hnvadj, ?_, ?_⟩
      · have hkey := Finset.card_sdiff_add_card_inter (G.neighborFinset r_t ∩ Iso)
          (G.neighborFinset v)
        have hinter : (G.neighborFinset r_t ∩ Iso) ∩ G.neighborFinset v
            = G.neighborFinset r_t ∩ G.neighborFinset v ∩ Iso := Finset.inter_right_comm _ _ _
        rw [hinter, hs0, hrtiso2] at hkey; omega
      · have hkey := Finset.card_sdiff_add_card_inter (G.neighborFinset v ∩ Iso)
          (G.neighborFinset r_t)
        have hinter : (G.neighborFinset v ∩ Iso) ∩ G.neighborFinset r_t
            = G.neighborFinset r_t ∩ G.neighborFinset v ∩ Iso := by
          rw [Finset.inter_right_comm,
            Finset.inter_comm (G.neighborFinset v) (G.neighborFinset r_t)]
        rw [hinter, hs0] at hkey; omega
    obtain ⟨t, ht⟩ := Finset.card_pos.mp (by omega : 0 <
      (G.neighborFinset r_t ∩ G.neighborFinset v ∩ Iso).card)
    rw [Finset.mem_inter, Finset.mem_inter] at ht
    obtain ⟨⟨htrt, htv⟩, htIso⟩ := ht
    have htInrt : t ∈ G.neighborFinset r_t ∩ Iso := Finset.mem_inter.mpr ⟨htrt, htIso⟩
    rw [hNrtIso] at htInrt
    simp only [Finset.mem_insert, Finset.mem_singleton] at htInrt
    rcases htInrt with heqc | heqe
    · exfalso
      rw [heqc] at htv
      have hvNc : v ∈ G.neighborFinset c ∩ Hub :=
        Finset.mem_inter.mpr
          ⟨(G.mem_neighborFinset c v).mpr ((G.mem_neighborFinset v c).mp htv).symm, hvHub⟩
      rw [hNc] at hvNc; simp only [Finset.mem_insert, Finset.mem_singleton] at hvNc
      rcases hvNc with h | h | h
      exacts [hvh₂ h, hvg h, hvrt h]
    · rw [heqe] at htv; exact (G.mem_neighborFinset v e).mp htv
  have finish2 : ∀ v1 v2 : Fin 19, (v1 = r_z ∨ v1 = a ∨ v1 = b) → (v2 = r_z ∨ v2 = a ∨ v2 = b) →
      v1 ≠ v2 → ¬ G.Adj r_t v1 → ¬ G.Adj r_t v2 → False := by
    intro v1 v2 hv1 hv2 hv12 hnr1 hnr2
    have hv1Hub : v1 ∈ Hub := by rcases hv1 with rfl | rfl | rfl; exacts [hr_zHub, haHub, hbHub]
    have hv2Hub : v2 ∈ Hub := by rcases hv2 with rfl | rfl | rfl; exacts [hr_zHub, haHub, hbHub]
    have hv1d : G.degree v1 = 4 := by rcases hv1 with rfl | rfl | rfl; exacts [hr_zd, had, hbd]
    have hv2d : G.degree v2 = 4 := by rcases hv2 with rfl | rfl | rfl; exacts [hr_zd, had, hbd]
    have hv1iso : 2 ≤ (G.neighborFinset v1 ∩ Iso).card := by
      rcases hv1 with rfl | rfl | rfl; exacts [hrz2, ha2iso, hb2iso]
    have hv2iso : 2 ≤ (G.neighborFinset v2 ∩ Iso).card := by
      rcases hv2 with rfl | rfl | rfl; exacts [hrz2, ha2iso, hb2iso]
    have hv1h₂ : v1 ≠ h₂ := by
      rcases hv1 with rfl | rfl | rfl
      exacts [hr_z_ne_h₂, G.ne_of_adj hah₂, G.ne_of_adj hbh₂]
    have hv2h₂ : v2 ≠ h₂ := by
      rcases hv2 with rfl | rfl | rfl
      exacts [hr_z_ne_h₂, G.ne_of_adj hah₂, G.ne_of_adj hbh₂]
    have hv1g : v1 ≠ g := by rcases hv1 with rfl | rfl | rfl; exacts [hg_rz.symm, hg_a.symm, hg_b.symm]
    have hv2g : v2 ≠ g := by rcases hv2 with rfl | rfl | rfl; exacts [hg_rz.symm, hg_a.symm, hg_b.symm]
    have hv1rt : v1 ≠ r_t := by
      rcases hv1 with rfl | rfl | rfl; exacts [hrt_rz.symm, hrt_a.symm, hrt_b.symm]
    have hv2rt : v2 ≠ r_t := by
      rcases hv2 with rfl | rfl | rfl; exacts [hrt_rz.symm, hrt_a.symm, hrt_b.symm]
    have hv1e : G.Adj v1 e := hshare_e v1 hv1Hub hv1d hv1iso hnr1 hv1h₂ hv1g hv1rt
    have hv2e : G.Adj v2 e := hshare_e v2 hv2Hub hv2d hv2iso hnr2 hv2h₂ hv2g hv2rt
    have hsub3 : ({r_t, v1, v2} : Finset (Fin 19)) ⊆ G.neighborFinset e ∩ Hub := by
      intro y hy; simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl | rfl
      · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset e y).mpr hrte.symm, hr_tHub⟩
      · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset e y).mpr hv1e.symm, hv1Hub⟩
      · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset e y).mpr hv2e.symm, hv2Hub⟩
    have hc3 : ({r_t, v1, v2} : Finset (Fin 19)).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [Ne.symm hv1rt, Ne.symm hv2rt]),
        Finset.card_insert_of_notMem (by simp [hv12]), Finset.card_singleton]
    have hNeHub : (G.neighborFinset e ∩ Hub).card = 3 := hiso3 e heIso
    have hNeEq : G.neighborFinset e ∩ Hub = {r_t, v1, v2} :=
      (Finset.eq_of_subset_of_card_le hsub3 (le_of_eq (hNeHub.trans hc3.symm))).symm
    have hfnotNe : f ∉ G.neighborFinset e := by
      intro hf
      have hm : f ∈ G.neighborFinset e ∩ Hub := Finset.mem_inter.mpr ⟨hf, hfHub⟩
      rw [hNeEq] at hm; simp only [Finset.mem_insert, Finset.mem_singleton] at hm
      rcases hm with h | h | h
      · rw [h, hr_td] at hfd; omega
      · rw [h, hv1d] at hfd; omega
      · rw [h, hv2d] at hfd; omega
    have hgnotNe : e ∉ G.neighborFinset g := by
      intro he
      have hgshare := hshare g hg hgd r_t hr_tHub hr_td hg_rt hngrt
      have hcInshare : c ∈ G.neighborFinset g ∩ G.neighborFinset r_t ∩ Iso :=
        Finset.mem_inter.mpr ⟨Finset.mem_inter.mpr
          ⟨(G.mem_neighborFinset g c).mpr hgc, (G.mem_neighborFinset r_t c).mpr hr_tc⟩, hcIso⟩
      have hemem : e ∈ G.neighborFinset g ∩ G.neighborFinset r_t ∩ Iso :=
        Finset.mem_inter.mpr ⟨Finset.mem_inter.mpr
          ⟨he, (G.mem_neighborFinset r_t e).mpr hrte⟩, heIso⟩
      have hsub2 : ({c, e} : Finset (Fin 19)) ⊆
          G.neighborFinset g ∩ G.neighborFinset r_t ∩ Iso := by
        intro y hy; simp only [Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with rfl | rfl
        exacts [hcInshare, hemem]
      have hc2 : ({c, e} : Finset (Fin 19)).card = 2 := by
        rw [Finset.card_insert_of_notMem (by simp [Ne.symm hec]), Finset.card_singleton]
      have := Finset.card_le_card hsub2; rw [hc2] at this; omega
    have hinter_eq : (G.neighborFinset g ∩ Iso) ∩ (G.neighborFinset f ∩ Iso)
        = G.neighborFinset g ∩ G.neighborFinset f ∩ Iso := by
      ext y; simp only [Finset.mem_inter]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3, _⟩; exact ⟨⟨h1, h3⟩, h2⟩
      · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h1, h3⟩, h2, h3⟩
    have hkey := Finset.card_union_add_card_inter (G.neighborFinset g ∩ Iso)
      (G.neighborFinset f ∩ Iso)
    rw [hinter_eq, hg4, hfiso5] at hkey
    have hunionsubIso : (G.neighborFinset g ∩ Iso) ∪ (G.neighborFinset f ∩ Iso) ⊆ Iso :=
      Finset.union_subset Finset.inter_subset_right Finset.inter_subset_right
    have hunionge : 7 ≤ ((G.neighborFinset g ∩ Iso) ∪ (G.neighborFinset f ∩ Iso)).card := by
      omega
    have hunioneq : (G.neighborFinset g ∩ Iso) ∪ (G.neighborFinset f ∩ Iso) = Iso :=
      Finset.eq_of_subset_of_card_le hunionsubIso (by rw [hIso]; exact hunionge)
    have heInUnion : e ∈ (G.neighborFinset g ∩ Iso) ∪ (G.neighborFinset f ∩ Iso) := by
      rw [hunioneq]; exact heIso
    rw [Finset.mem_union, Finset.mem_inter, Finset.mem_inter] at heInUnion
    rcases heInUnion with ⟨heg, _⟩ | ⟨hef, _⟩
    · exact hgnotNe heg
    · exact hfnotNe ((G.mem_neighborFinset e f).mpr ((G.mem_neighborFinset f e).mp hef).symm)
  -- === Counting: `r_t` is non-adjacent to at least two of `{r_z, a, b}` (via `heRR`). ===
  simp only [hRfilter] at heRR
  rw [Finset.sum_insert (by simp [hg_rt, hg_rz, hg_a, hg_b]),
    Finset.sum_insert (by simp [hrt_rz, hrt_a, hrt_b]),
    Finset.sum_insert (by simp [hrz_a, hrz_b]),
    Finset.sum_insert (by simp [hab]), Finset.sum_singleton] at heRR
  set S := ({g, r_t, r_z, a, b} : Finset (Fin 19)) with hSdef
  have hSsubHub : S ⊆ Hub := by
    rw [hSdef]; intro y hy; simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl
    exacts [hg, hr_tHub, hr_zHub, haHub, hbHub]
  have hgNIso : G.neighborFinset g ∩ Iso = G.neighborFinset g :=
    Finset.eq_of_subset_of_card_le Finset.inter_subset_left
      (by rw [hg4, G.card_neighborFinset_eq_degree, hgd])
  have hgHub0 : G.neighborFinset g ∩ Hub = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro y hy; rw [Finset.mem_inter] at hy
    have hyIso : y ∈ G.neighborFinset g ∩ Iso := by rw [hgNIso]; exact hy.1
    exact Finset.disjoint_left.mp hdisj hy.2 (Finset.mem_inter.mp hyIso).2
  have hgS0 : (G.neighborFinset g ∩ S).card = 0 := by
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro y hy; rw [Finset.mem_inter] at hy
    have hyH : y ∈ G.neighborFinset g ∩ Hub := Finset.mem_inter.mpr ⟨hy.1, hSsubHub hy.2⟩
    rw [hgHub0] at hyH; exact absurd hyH (Finset.notMem_empty _)
  have no_rz_a : ¬(G.Adj r_t r_z ∧ G.Adj r_t a) := by
    rintro ⟨h_rz, h_a⟩
    have hb1 : 2 ≤ (G.neighborFinset r_t ∩ S).card := by
      have hsub : ({r_z, a} : Finset (Fin 19)) ⊆ G.neighborFinset r_t ∩ S := by
        intro y hy; simp only [Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with rfl | rfl
        · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset r_t y).mpr h_rz, by rw [hSdef]; simp⟩
        · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset r_t y).mpr h_a, by rw [hSdef]; simp⟩
      have hc2 : ({r_z, a} : Finset (Fin 19)).card = 2 := by
        rw [Finset.card_insert_of_notMem (by simp [hrz_a]), Finset.card_singleton]
      have := Finset.card_le_card hsub; rw [hc2] at this; exact this
    have hb2 : 1 ≤ (G.neighborFinset r_z ∩ S).card :=
      Finset.card_pos.mpr ⟨r_t, Finset.mem_inter.mpr
        ⟨(G.mem_neighborFinset r_z r_t).mpr h_rz.symm, by rw [hSdef]; simp⟩⟩
    have hb3 : 1 ≤ (G.neighborFinset a ∩ S).card :=
      Finset.card_pos.mpr ⟨r_t, Finset.mem_inter.mpr
        ⟨(G.mem_neighborFinset a r_t).mpr h_a.symm, by rw [hSdef]; simp⟩⟩
    omega
  have no_rz_b : ¬(G.Adj r_t r_z ∧ G.Adj r_t b) := by
    rintro ⟨h_rz, h_b⟩
    have hb1 : 2 ≤ (G.neighborFinset r_t ∩ S).card := by
      have hsub : ({r_z, b} : Finset (Fin 19)) ⊆ G.neighborFinset r_t ∩ S := by
        intro y hy; simp only [Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with rfl | rfl
        · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset r_t y).mpr h_rz, by rw [hSdef]; simp⟩
        · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset r_t y).mpr h_b, by rw [hSdef]; simp⟩
      have hc2 : ({r_z, b} : Finset (Fin 19)).card = 2 := by
        rw [Finset.card_insert_of_notMem (by simp [hrz_b]), Finset.card_singleton]
      have := Finset.card_le_card hsub; rw [hc2] at this; exact this
    have hb2 : 1 ≤ (G.neighborFinset r_z ∩ S).card :=
      Finset.card_pos.mpr ⟨r_t, Finset.mem_inter.mpr
        ⟨(G.mem_neighborFinset r_z r_t).mpr h_rz.symm, by rw [hSdef]; simp⟩⟩
    have hb3 : 1 ≤ (G.neighborFinset b ∩ S).card :=
      Finset.card_pos.mpr ⟨r_t, Finset.mem_inter.mpr
        ⟨(G.mem_neighborFinset b r_t).mpr h_b.symm, by rw [hSdef]; simp⟩⟩
    omega
  have no_a_b : ¬(G.Adj r_t a ∧ G.Adj r_t b) := by
    rintro ⟨h_a, h_b⟩
    have hb1 : 2 ≤ (G.neighborFinset r_t ∩ S).card := by
      have hsub : ({a, b} : Finset (Fin 19)) ⊆ G.neighborFinset r_t ∩ S := by
        intro y hy; simp only [Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with rfl | rfl
        · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset r_t y).mpr h_a, by rw [hSdef]; simp⟩
        · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset r_t y).mpr h_b, by rw [hSdef]; simp⟩
      have hc2 : ({a, b} : Finset (Fin 19)).card = 2 := by
        rw [Finset.card_insert_of_notMem (by simp [hab]), Finset.card_singleton]
      have := Finset.card_le_card hsub; rw [hc2] at this; exact this
    have hb2 : 1 ≤ (G.neighborFinset a ∩ S).card :=
      Finset.card_pos.mpr ⟨r_t, Finset.mem_inter.mpr
        ⟨(G.mem_neighborFinset a r_t).mpr h_a.symm, by rw [hSdef]; simp⟩⟩
    have hb3 : 1 ≤ (G.neighborFinset b ∩ S).card :=
      Finset.card_pos.mpr ⟨r_t, Finset.mem_inter.mpr
        ⟨(G.mem_neighborFinset b r_t).mpr h_b.symm, by rw [hSdef]; simp⟩⟩
    omega
  by_cases h1 : G.Adj r_t r_z
  · exact finish2 a b (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl)) hab
      (fun h => no_rz_a ⟨h1, h⟩) (fun h => no_rz_b ⟨h1, h⟩)
  · by_cases h2 : G.Adj r_t a
    · exact finish2 r_z b (Or.inl rfl) (Or.inr (Or.inr rfl)) hrz_b h1 (fun h => no_a_b ⟨h2, h⟩)
    · exact finish2 r_z a (Or.inl rfl) (Or.inr (Or.inl rfl)) hrz_a h1 h2

end N19

end ACMax
