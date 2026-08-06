import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N19.TwoHubCornerDeg5ZLeaf
import ACMaxConjecture.SmallCases.N19.TwoHubSelect
import ACMaxConjecture.SmallCases.N19.ZVertex
import ACMaxConjecture.SmallCases.N19.Deg5RichCap
import ACMaxConjecture.SmallCases.N19.Deg5Rich1041Count
import ACMaxConjecture.SmallCases.N19.Deg5Rich1041Blocker
import ACMaxConjecture.SmallCases.N19.Deg5Rich1041K23
import ACMaxConjecture.SmallCases.N19.Deg5Rich1041OctaPoorCounts

/-! # CASE C, one-rich regime: `z'` meets one rich (`g`/`r_t`) + one poor hub (`n = 19`)

The `z'`-meets-poor / share-0 residual where exactly one of `z'`'s two hubs
`{p,q}` is rich (`isoDeg ≥ 2`, hence `∈ {g, r_t}` by `hA`) and the other is
poor.  CONSTRUCTION-VERIFIED provable (0 survivors / 4000 seeds): the dense hub
structure (8 hub–hub edges among 9 deg-4 hubs + shared `Iso` twins) forces a
good triangle (`Σ ≤ 11`, dominant), `C₄` (`Σ ≤ 14`), or `K₂,₃` (`Σ ≤ 19`) —
`hT`/`hC4`/`hK23` forbid all, contradiction.  Template:
`octahedron_poor_layer_force_nineteen`. -/

namespace ACMax
open scoped Classical

namespace N19

set_option maxHeartbeats 1000000 in
/-- **CASE C, one-rich regime.** -/
theorem octahedron_one_poor_force_share2_1041_nineteen (G : SimpleGraph (Fin 19))
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
    (hz'Z : z' ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 19)))
    (hzz' : G.Adj z z') (hz'deg3 : G.degree z' = 3)
    (hz'iso0 : (G.neighborFinset z' ∩ Iso).card = 0)
    (hNz'eq : G.neighborFinset z' ∩ Hub = ({p, q} : Finset (Fin 19)))
    (hp : p ∈ Hub) (_hq : q ∈ Hub) (hdp : G.degree p = 4) (_hdq : G.degree q = 4)
    (_hpq : p ≠ q) (hz'p : G.Adj z' p) (hz'q : G.Adj z' q)
    (_hnpq : ¬G.Adj p q)
    (_hshare0 : (G.neighborFinset p ∩ G.neighborFinset q ∩ Iso).card = 0)
    (hrich : 2 ≤ (G.neighborFinset p ∩ Iso).card)
    (hqpoor : (G.neighborFinset q ∩ Iso).card ≤ 1)
    (hph₂ : p ≠ h₂) (_hpr_z : p ≠ r_z) (hqh₂ : q ≠ h₂) (_hqr_z : q ≠ r_z) :
    False := by
  classical
  obtain ⟨c, r_t, r_z, a, b, hRfilter, hRcard, hcIso, hgc, hh₂c, hr_tc, hNc, hNz, hNh₂,
    hr_zz, hah₂, hbh₂, hr_tHub, hr_td, hr_zHub, hr_zd, haHub, had, hbHub, hbd⟩ := hstruct
  -- === Basic membership / degree facts. ===
  have hzf := zfacts_deg5_nineteen G Hub Iso hiso3 hdisj hsum17 hdeg3 hisodeg3 hleak
  have hzdeg : G.degree z = 3 := (hzf z hzZ).2.2
  have hzhub2 : (G.neighborFinset z ∩ Hub).card = 2 := (hzf z hzZ).2.1
  have hcdeg : G.degree c = 3 := hisodeg3 c hcIso
  have hc_notHub : c ∉ Hub := Finset.disjoint_right.mp hdisj hcIso
  have hz_notHub : z ∉ Hub := fun hc => (Finset.mem_sdiff.mp hzZ).2 (Finset.mem_union_left _ hc)
  have hz'_notHub : z' ∉ Hub := fun hc => (Finset.mem_sdiff.mp hz'Z).2 (Finset.mem_union_left _ hc)
  have hz'_notIso : z' ∉ Iso := fun hc => (Finset.mem_sdiff.mp hz'Z).2 (Finset.mem_union_right _ hc)
  have hz_notIso : z ∉ Iso := fun hc => (Finset.mem_sdiff.mp hzZ).2 (Finset.mem_union_right _ hc)
  have hzz'ne : z ≠ z' := G.ne_of_adj hzz'
  -- === `Z = {z, z'}`. ===
  have hZ2 : (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 19)).card = 2 := by
    have huc : (Hub ∪ Iso).card = 17 := by rw [Finset.card_union_of_disjoint hdisj]; exact hsum17
    rw [show (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 19)) = (Hub ∪ Iso)ᶜ from by
        ext w; simp, Finset.card_compl, Fintype.card_fin, huc]
  have hZeq : (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 19)) = {z, z'} := by
    have hsub : ({z, z'} : Finset (Fin 19)) ⊆ Finset.univ \ (Hub ∪ Iso) := by
      intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl
      · exact hzZ
      · exact hz'Z
    have hcard2 : ({z, z'} : Finset (Fin 19)).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simp [hzz'ne]), Finset.card_singleton]
    exact (Finset.eq_of_subset_of_card_le hsub (le_of_eq (hZ2.trans hcard2.symm))).symm
  -- === Iso independence, twin-cover helpers. ===
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
  -- === Distinctness helpers. ===
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
  obtain ⟨hh₂g, hh₂rt, hg_rt⟩ := card3_ne h₂ g r_t hc3card
  have hr_z_ne_h₂ : r_z ≠ h₂ :=
    (card2_ne h₂ r_z (by rw [← hNz]; exact hzhub2)).symm
  have hg_rz : g ≠ r_z := by
    intro h; apply hgz; rw [h]; exact hr_zz
  have hg_a : g ≠ a := by
    intro h; apply hg2; rw [h]; exact hah₂
  have hg_b : g ≠ b := by
    intro h; apply hg2; rw [h]; exact hbh₂
  -- === `¬Adj` facts (triangles `Σ ≤ 11`). ===
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
  -- === `r_z ≠ a, r_z ≠ b, r_t ≠ a, r_t ≠ b` (via the `¬Adj h₂ ·` facts). ===
  have hrz_a : r_z ≠ a := fun h => hnh₂rz (h ▸ hah₂.symm)
  have hrz_b : r_z ≠ b := fun h => hnh₂rz (h ▸ hbh₂.symm)
  have hrt_a : r_t ≠ a := fun h => hnh₂rt (h ▸ hah₂.symm)
  have hrt_b : r_t ≠ b := fun h => hnh₂rt (h ▸ hbh₂.symm)
  -- === `a ≠ b` (via `|N(h₂) ∩ Hub| = 2`). ===
  have hh₂z' : ¬ G.Adj h₂ z' := by
    intro hadj
    have hm : h₂ ∈ G.neighborFinset z' ∩ Hub :=
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset z' h₂).mpr hadj.symm, hh₂⟩
    rw [hNz'eq] at hm; simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with h | h
    · exact hph₂ h.symm
    · exact hqh₂ h.symm
  have hh₂Zcard : (G.neighborFinset h₂ ∩ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 19))).card = 1 := by
    rw [hZeq]
    have hset : G.neighborFinset h₂ ∩ ({z, z'} : Finset (Fin 19)) = {z} := by
      ext w; simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hw, hcase⟩
        rcases hcase with rfl | rfl
        · rfl
        · exact absurd ((G.mem_neighborFinset _ _).mp hw) hh₂z'
      · rintro rfl
        exact ⟨(G.mem_neighborFinset _ _).mpr hz2.symm, Or.inl rfl⟩
    rw [hset, Finset.card_singleton]
  have hh₂HubCard : (G.neighborFinset h₂ ∩ Hub).card = 2 := by
    have hsp := nbr_split_three_nineteen G Hub Iso hdisj h₂
    rw [hd₂, hpoor, hh₂Zcard] at hsp; omega
  have hab : a ≠ b := card2_ne a b (by rw [← hNh₂]; exact hh₂HubCard)
  have hrt_rz : r_t ≠ r_z := by
    intro h
    rw [h, Finset.insert_idem] at hRcard
    have := quad_le g r_z a b; omega
  -- === `p ≠ r_z` (structural): else the triangle `{z, z', r_z}` (`Σ = 10`). ===
  have hp_rz : p ≠ r_z := by
    intro h
    exact tri z z' r_z hzz'ne (fun he => hz'_notHub (he ▸ hr_zHub))
      (fun he => hz_notHub (he ▸ hr_zHub)) hzz' (h ▸ hz'p) hr_zz.symm
      (by omega)
  -- === Rich lower bounds and `∑_R isoDeg = 12`. ===
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
  -- === Iso-degree upper bound. ===
  have hisole : ∀ w : Fin 19, (G.neighborFinset w ∩ Iso).card ≤ G.degree w := fun w =>
    (Finset.card_le_card Finset.inter_subset_left).trans (le_of_eq (G.card_neighborFinset_eq_degree w))
  -- === `p ∈ {g, r_t, a, b}`. ===
  have hpmem : p = g ∨ p = r_t ∨ p = a ∨ p = b := by
    have hpF : p ∈ Hub.filter (fun h => G.degree h = 4 ∧ 2 ≤ (G.neighborFinset h ∩ Iso).card) :=
      Finset.mem_filter.mpr ⟨hp, hdp, hrich⟩
    rw [hRfilter] at hpF
    simp only [Finset.mem_insert, Finset.mem_singleton] at hpF
    rcases hpF with h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact absurd h hp_rz
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  -- === Two-hub kill (a rich hub non-adjacent to `g`). ===
  have twohub_kill : ∀ w : Fin 19, w ∈ Hub → G.degree w = 4 → g ≠ w → ¬ G.Adj g w →
      3 ≤ (G.neighborFinset w ∩ Iso).card → False := by
    intro w hwHub hwd hgw hnadjgw hwiso
    have := isoDeg_le_two_of_nonadj_rich_nineteen G Hub Iso hshare hno2hub g w hg hwHub hgd hwd
      hgw hnadjgw hgiso
    omega
  have c4 : ∀ u v w t : Fin 19, ({u, v, w, t} : Finset (Fin 19)).card = 4 →
      G.Adj u v → G.Adj v w → G.Adj w t → G.Adj t u → ¬ G.Adj u w → ¬ G.Adj v t →
      G.degree u + G.degree v + G.degree w + G.degree t ≤ 14 → False :=
    fun u v w t hc a1 a2 a3 a4 n1 n2 hd => hC4 ⟨u, v, w, t, hc, a1, a2, a3, a4, n1, n2, hd⟩
  have hp_z : p ≠ z := fun h => hz_notHub (h ▸ hp)
  have hp_z' : p ≠ z' := fun h => hz'_notHub (h ▸ hp)
  have hh₂_z : h₂ ≠ z := fun h => hz_notHub (h ▸ hh₂)
  have hh₂_z' : h₂ ≠ z' := fun h => hz'_notHub (h ▸ hh₂)
  have hpnz : ¬ G.Adj p z := by
    intro hadj
    have hm : p ∈ G.neighborFinset z ∩ Hub :=
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset z p).mpr hadj.symm, hp⟩
    rw [hNz] at hm; simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with h | h
    · exact hph₂ h
    · exact hp_rz h
  by_cases hpab : p = a ∨ p = b
  · -- CASE 1: `p ∈ {a, b}`, good `C₄  p–h₂–z–z'`.
    have hph₂adj : G.Adj p h₂ := by
      rcases hpab with h | h
      · rw [h]; exact hah₂
      · rw [h]; exact hbh₂
    have hc4card : ({p, h₂, z, z'} : Finset (Fin 19)).card = 4 := by
      rw [Finset.card_insert_of_notMem (by simp [hph₂, hp_z, hp_z']),
        Finset.card_insert_of_notMem (by simp [hh₂_z, hh₂_z']),
        Finset.card_insert_of_notMem (by simp [hzz'ne]), Finset.card_singleton]
    exact c4 p h₂ z z' hc4card hph₂adj hz2.symm hzz' hz'p hpnz hh₂z' (by omega)
  · have hpgrt : p = g ∨ p = r_t := by
      rcases hpmem with h | h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd (Or.inl h) hpab
      · exact absurd (Or.inr h) hpab
    by_cases hg4 : 4 ≤ (G.neighborFinset g ∩ Iso).card
    · -- CASE 3: `{4,2,2,2,2}` profile, `f`–`g` covering.
      have hgiso4 : (G.neighborFinset g ∩ Iso).card = 4 := by
        have := hisole g; rw [hgd] at this; omega
      -- `f ≁ g`; `|N g ∩ N f ∩ Iso| ≤ 2` (else `K₂,₃`).
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
        exact highshare_k23_1041_nineteen G Iso hK23 hisoHub hisodeg3 g f hgd hfd hnadj_gf
          (by omega)
      -- `p = r_t`, `isoDeg r_t = 2`.
      have hp_g : p ≠ g := by
        intro h
        have hgsp := nbr_split_three_nineteen G Hub Iso hdisj g
        rw [hgd, hgiso4] at hgsp
        have hm : z' ∈ G.neighborFinset g ∩ (Finset.univ \ (Hub ∪ Iso)) :=
          Finset.mem_inter.mpr ⟨(G.mem_neighborFinset g z').mpr (h ▸ hz'p.symm), hz'Z⟩
        have hpos : 1 ≤ (G.neighborFinset g ∩ (Finset.univ \ (Hub ∪ Iso))).card :=
          Finset.card_pos.mpr ⟨z', hm⟩
        omega
      have hpeq : p = r_t := by rcases hpgrt with h | h; exacts [absurd h hp_g, h]
      have hrtz' : G.Adj z' r_t := hpeq ▸ hz'p
      have hrtiso2 : (G.neighborFinset r_t ∩ Iso).card = 2 := by
        have hrtle := hisole r_t; rw [hr_td] at hrtle; omega
      -- Extract `e` (the non-`c` twin of `r_t`).
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
      -- `v ≁ r_t` (rich) forces `v ~ e`.
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
      -- `¬Adj r_t r_z` (good `C₄  r_z–z–z'–r_t`).
      have hnrz_z' : ¬ G.Adj r_z z' := by
        intro hadj
        have hm : r_z ∈ G.neighborFinset z' ∩ Hub :=
          Finset.mem_inter.mpr ⟨(G.mem_neighborFinset z' r_z).mpr hadj.symm, hr_zHub⟩
        rw [hNz'eq] at hm; simp only [Finset.mem_insert, Finset.mem_singleton] at hm
        rcases hm with h | h
        · exact hrt_rz (hpeq.symm.trans h.symm)
        · rw [h] at hrz2; omega
      have hnz_rt : ¬ G.Adj z r_t := by
        intro hadj
        have hm : r_t ∈ G.neighborFinset z ∩ Hub :=
          Finset.mem_inter.mpr ⟨(G.mem_neighborFinset z r_t).mpr hadj, hr_tHub⟩
        rw [hNz] at hm; simp only [Finset.mem_insert, Finset.mem_singleton] at hm
        rcases hm with h | h
        exacts [hh₂rt h.symm, hrt_rz h]
      have hrz_z : r_z ≠ z := fun h => hz_notHub (h ▸ hr_zHub)
      have hrz_z' : r_z ≠ z' := fun h => hz'_notHub (h ▸ hr_zHub)
      have hz_rt : z ≠ r_t := fun h => hz_notHub (h ▸ hr_tHub)
      have hz'_rt : z' ≠ r_t := fun h => hz'_notHub (h ▸ hr_tHub)
      have hnrtrz : ¬ G.Adj r_t r_z := by
        intro hadj
        have hc4card2 : ({r_z, z, z', r_t} : Finset (Fin 19)).card = 4 := by
          rw [Finset.card_insert_of_notMem (by simp [hrz_z, hrz_z', Ne.symm hrt_rz]),
            Finset.card_insert_of_notMem (by simp [hzz'ne, hz_rt]),
            Finset.card_insert_of_notMem (by simp [hz'_rt]),
            Finset.card_singleton]
        exact c4 r_z z z' r_t hc4card2 hr_zz hzz' hrtz' hadj hnrz_z' hnz_rt (by omega)
      have hrze : G.Adj r_z e :=
        hshare_e r_z hr_zHub hr_zd hrz2 hnrtrz hr_z_ne_h₂ hg_rz.symm hrt_rz.symm
      -- The final covering contradiction, given `v2 ∈ {a,b}` with `v2 ~ e`.
      have finish_e : ∀ v2 : Fin 19, (v2 = a ∨ v2 = b) → G.Adj v2 e → False := by
        intro v2 hv2id hv2e
        have hv2Hub : v2 ∈ Hub := by rcases hv2id with rfl | rfl; exacts [haHub, hbHub]
        have hrz_v2 : r_z ≠ v2 := by rcases hv2id with rfl | rfl; exacts [hrz_a, hrz_b]
        have hrt_v2 : r_t ≠ v2 := by rcases hv2id with rfl | rfl; exacts [hrt_a, hrt_b]
        have hsub3 : ({r_t, r_z, v2} : Finset (Fin 19)) ⊆ G.neighborFinset e ∩ Hub := by
          intro y hy; simp only [Finset.mem_insert, Finset.mem_singleton] at hy
          rcases hy with rfl | rfl | rfl
          · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset e y).mpr hrte.symm, hr_tHub⟩
          · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset e y).mpr hrze.symm, hr_zHub⟩
          · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset e y).mpr hv2e.symm, hv2Hub⟩
        have hc3 : ({r_t, r_z, v2} : Finset (Fin 19)).card = 3 := by
          rw [Finset.card_insert_of_notMem (by simp [hrt_rz, hrt_v2]),
            Finset.card_insert_of_notMem (by simp [hrz_v2]), Finset.card_singleton]
        have hNeHub : (G.neighborFinset e ∩ Hub).card = 3 := hiso3 e heIso
        have hNeEq : G.neighborFinset e ∩ Hub = {r_t, r_z, v2} :=
          (Finset.eq_of_subset_of_card_le hsub3 (le_of_eq (hNeHub.trans hc3.symm))).symm
        have hfnotNe : f ∉ G.neighborFinset e := by
          intro hf
          have hm : f ∈ G.neighborFinset e ∩ Hub := Finset.mem_inter.mpr ⟨hf, hfHub⟩
          rw [hNeEq] at hm; simp only [Finset.mem_insert, Finset.mem_singleton] at hm
          rcases hm with h | h | h
          · rw [h, hr_td] at hfd; omega
          · rw [h, hr_zd] at hfd; omega
          · rcases hv2id with rfl | rfl
            · rw [h, had] at hfd; omega
            · rw [h, hbd] at hfd; omega
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
        rw [hinter_eq, hgiso4, hfiso5] at hkey
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
      -- Pick `v2 ∈ {a, b}` with `r_t ≁ v2`.
      have hrt_hub_le : (G.neighborFinset r_t ∩ Hub).card ≤ 1 := by
        have hsp := nbr_split_three_nineteen G Hub Iso hdisj r_t
        rw [hr_td, hrtiso2] at hsp
        have hz'mem : z' ∈ G.neighborFinset r_t ∩ (Finset.univ \ (Hub ∪ Iso)) :=
          Finset.mem_inter.mpr ⟨(G.mem_neighborFinset r_t z').mpr hrtz'.symm, hz'Z⟩
        have hpos : 1 ≤ (G.neighborFinset r_t ∩ (Finset.univ \ (Hub ∪ Iso))).card :=
          Finset.card_pos.mpr ⟨z', hz'mem⟩
        omega
      have hv2 : ¬ G.Adj r_t a ∨ ¬ G.Adj r_t b := by
        by_cases hra : G.Adj r_t a
        · refine Or.inr (fun hrb => ?_)
          have hsub : ({a, b} : Finset (Fin 19)) ⊆ G.neighborFinset r_t ∩ Hub := by
            intro y hy; simp only [Finset.mem_insert, Finset.mem_singleton] at hy
            rcases hy with rfl | rfl
            · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset r_t y).mpr hra, haHub⟩
            · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset r_t y).mpr hrb, hbHub⟩
          have hc2 : ({a, b} : Finset (Fin 19)).card = 2 := by
            rw [Finset.card_insert_of_notMem (by simp [hab]), Finset.card_singleton]
          have := Finset.card_le_card hsub; rw [hc2] at this; omega
        · exact Or.inl hra
      rcases hv2 with hna | hnb
      · exact finish_e a (Or.inl rfl)
          (hshare_e a haHub had ha2iso hna (G.ne_of_adj hah₂) hg_a.symm hrt_a.symm)
      · exact finish_e b (Or.inr rfl)
          (hshare_e b hbHub hbd hb2iso hnb (G.ne_of_adj hbh₂) hg_b.symm hrt_b.symm)
    · -- CASE 2: `{3,3,2,2,2}` profile, two-hub `(g, w)` with a second high hub `w`.
      have hgiso3 : (G.neighborFinset g ∩ Iso).card = 3 := by
        have := hisole g; rw [hgd] at this; omega
      have hnadj_g : ∀ w : Fin 19, (w = r_t ∨ w = r_z ∨ w = a ∨ w = b) →
          3 ≤ (G.neighborFinset w ∩ Iso).card → ¬ G.Adj g w := by
        intro w hwid hwiso hadj
        have hwHub : w ∈ Hub := by
          rcases hwid with rfl | rfl | rfl | rfl
          exacts [hr_tHub, hr_zHub, haHub, hbHub]
        have hwd : G.degree w = 4 := by
          rcases hwid with rfl | rfl | rfl | rfl
          exacts [hr_td, hr_zd, had, hbd]
        have hgsp := nbr_split_three_nineteen G Hub Iso hdisj g
        rw [hgd] at hgsp
        have hgHubpos : 1 ≤ (G.neighborFinset g ∩ Hub).card :=
          Finset.card_pos.mpr ⟨w, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset g w).mpr hadj, hwHub⟩⟩
        have hgZ0 : (G.neighborFinset g ∩ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 19))).card = 0 := by
          omega
        have hgnz' : ¬ G.Adj g z' := by
          intro hgadj
          have hm : z' ∈ G.neighborFinset g ∩ (Finset.univ \ (Hub ∪ Iso)) :=
            Finset.mem_inter.mpr ⟨(G.mem_neighborFinset g z').mpr hgadj, hz'Z⟩
          rw [Finset.card_eq_zero] at hgZ0; rw [hgZ0] at hm; exact absurd hm (Finset.notMem_empty _)
        have hg_p : g ≠ p := by intro h; apply hgnz'; rw [h]; exact hz'p.symm
        have hwsp := nbr_split_three_nineteen G Hub Iso hdisj w
        rw [hwd] at hwsp
        have hwHubpos : 1 ≤ (G.neighborFinset w ∩ Hub).card :=
          Finset.card_pos.mpr ⟨g, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset w g).mpr hadj.symm, hg⟩⟩
        have hwZ0 : (G.neighborFinset w ∩ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 19))).card = 0 := by
          omega
        have hwnz : ¬ G.Adj w z := by
          intro hwadj
          have hm : z ∈ G.neighborFinset w ∩ (Finset.univ \ (Hub ∪ Iso)) :=
            Finset.mem_inter.mpr ⟨(G.mem_neighborFinset w z).mpr hwadj, hzZ⟩
          rw [Finset.card_eq_zero] at hwZ0; rw [hwZ0] at hm; exact absurd hm (Finset.notMem_empty _)
        have hwnz' : ¬ G.Adj w z' := by
          intro hwadj
          have hm : z' ∈ G.neighborFinset w ∩ (Finset.univ \ (Hub ∪ Iso)) :=
            Finset.mem_inter.mpr ⟨(G.mem_neighborFinset w z').mpr hwadj, hz'Z⟩
          rw [Finset.card_eq_zero] at hwZ0; rw [hwZ0] at hm; exact absurd hm (Finset.notMem_empty _)
        have hw_rz : w ≠ r_z := by intro h; apply hwnz; rw [h]; exact hr_zz
        have hw_p : w ≠ p := by intro h; apply hwnz'; rw [h]; exact hz'p.symm
        rcases hwid with rfl | rfl | rfl | rfl
        · rcases hpgrt with hpg | hprt
          · exact hg_p hpg.symm
          · exact hw_p hprt.symm
        · exact hw_rz rfl
        · have h2hub : 2 ≤ (G.neighborFinset w ∩ Hub).card := by
            have hsub : ({g, h₂} : Finset (Fin 19)) ⊆ G.neighborFinset w ∩ Hub := by
              intro y hy; simp only [Finset.mem_insert, Finset.mem_singleton] at hy
              rcases hy with rfl | rfl
              · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset w y).mpr hadj.symm, hg⟩
              · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset w y).mpr hah₂, hh₂⟩
            have hc2 : ({g, h₂} : Finset (Fin 19)).card = 2 := by
              rw [Finset.card_insert_of_notMem (by simp [Ne.symm hh₂g]), Finset.card_singleton]
            exact hc2 ▸ Finset.card_le_card hsub
          omega
        · have h2hub : 2 ≤ (G.neighborFinset w ∩ Hub).card := by
            have hsub : ({g, h₂} : Finset (Fin 19)) ⊆ G.neighborFinset w ∩ Hub := by
              intro y hy; simp only [Finset.mem_insert, Finset.mem_singleton] at hy
              rcases hy with rfl | rfl
              · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset w y).mpr hadj.symm, hg⟩
              · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset w y).mpr hbh₂, hh₂⟩
            have hc2 : ({g, h₂} : Finset (Fin 19)).card = 2 := by
              rw [Finset.card_insert_of_notMem (by simp [Ne.symm hh₂g]), Finset.card_singleton]
            exact hc2 ▸ Finset.card_le_card hsub
          omega
      by_cases h1 : 3 ≤ (G.neighborFinset r_t ∩ Iso).card
      · exact twohub_kill r_t hr_tHub hr_td hg_rt (hnadj_g r_t (Or.inl rfl) h1) h1
      · by_cases h2 : 3 ≤ (G.neighborFinset r_z ∩ Iso).card
        · exact twohub_kill r_z hr_zHub hr_zd hg_rz (hnadj_g r_z (Or.inr (Or.inl rfl)) h2) h2
        · by_cases h3 : 3 ≤ (G.neighborFinset a ∩ Iso).card
          · exact twohub_kill a haHub had hg_a (hnadj_g a (Or.inr (Or.inr (Or.inl rfl))) h3) h3
          · have h4 : 3 ≤ (G.neighborFinset b ∩ Iso).card := by omega
            exact twohub_kill b hbHub hbd hg_b (hnadj_g b (Or.inr (Or.inr (Or.inr rfl))) h4) h4

end N19

end ACMax
