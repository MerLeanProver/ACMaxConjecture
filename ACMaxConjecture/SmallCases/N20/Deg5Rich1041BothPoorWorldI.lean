import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N20.Core
import ACMaxConjecture.SmallCases.N20.ZVertex
import ACMaxConjecture.SmallCases.N20.BipartiteAvoiderTwoHub
import ACMaxConjecture.SmallCases.N20.R5OctahedronWorldI

/-! # CASE C both-poor, world (i): the `(11, 7, 45)` kill at `e_RR ≤ 3` (`n = 20`)

World (i) of the both-poor budget (`|P| = 5`, all five poor hubs at isoDeg `1`,
`∑_R isoDeg = 11`) carries the weakened rich–rich budget `∑_R richDeg ≤ 6`
(`e_RR ≤ 3`).  The compiled leaf `octahedron_world_i_two_hub_r5_twenty` kills
`∑_R richDeg ≤ 2`; the residual `3 ≤ Σ ≤ 6` dies by a twin-profile double count.
Writing `k t = |N t ∩ R|`, the exact share values (non-adjacent rich pairs share
exactly one twin by `hshare`/`hno2hub`, adjacent pairs none by the `Σ ≤ 11`
triangle) give `∑ k = 11` and `∑ k² = 31 − Σ`, so `Σ ∈ {4, 6}` with a rigid
`k`-profile.  Poor-slot counting (`∑_t |N t ∩ P| = 5`, a twin needs `≥ 2 − k`
poor slots, and `c` already consumes one on `h₂`) kills every profile with
`2·#{k=0} + #{k=1} ≥ 5`: all of `Σ = 4` and the `{3,3,2,1,1,1,0}` profile at
`Σ = 6`.  At `Σ = 6` the rich spare slots are exhausted (`e_RP = 2`), so the
poor layer carries `e_PP = 5` internal edges — every pair from `{p, q, w₁, w₂}`
except `{p, q}` is adjacent — and a `k = 0` twin (which exists, `#{k=0} ≥ 1`)
with two poor neighbours yields either the good triangle `{x, y, t}`
(`Σ = 4 + 4 + 3 = 11`, `hT`) or the good `C₄` `p–t–q–z'` (`Σ = 14`, `hC4`). -/

namespace ACMax
open scoped Classical

namespace N20

set_option maxHeartbeats 2000000 in
/-- **World-(i) kill at the weakened rich–rich budget (`n = 20`).**  In the share-2
`(11, 7, 45)` octahedron world with rigid partition `R = {g, r_t, r_z, a, b}`, the
world-(i) poor data (`|P| = 5`, all poor isoDeg `1`, `∑_R isoDeg = 11`) is
impossible even at `∑_R richDeg ≤ 6`. -/
theorem octahedron_both_poor_world_i_1041_twenty (G : SimpleGraph (Fin 20))
    (Hub Iso : Finset (Fin 20))
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdisj : Disjoint Hub Iso) (hsum18 : Hub.card + Iso.card = 18)
    (_hdeg3 : ∀ v : Fin 20, 3 ≤ G.degree v) (hisodeg3 : ∀ t ∈ Iso, G.degree t = 3)
    (_hleak : ∑ h ∈ Hub, (G.neighborFinset h ∩ (Finset.univ \ (Hub ∪ Iso))).card ≤ 4)
    (hdeg : ∀ h ∈ Hub, 4 ≤ G.degree h) (hdeg5 : ∀ h ∈ Hub, G.degree h ≤ 5)
    (hHub : Hub.card = 11) (hIso : Iso.card = 7) (hdsum : ∑ w ∈ Hub, G.degree w = 45)
    (hT : ¬∃ x y z : Fin 20, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 11)
    (hC4 : ¬∃ a b c d : Fin 20, ({a, b, c, d} : Finset (Fin 20)).card = 4 ∧
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
    (g : Fin 20) (_hg : g ∈ Hub) (hgd : G.degree g = 4)
    (_hgiso : 3 ≤ (G.neighborFinset g ∩ Iso).card)
    (h₂ z : Fin 20) (hh₂ : h₂ ∈ Hub) (hd₂ : G.degree h₂ = 4)
    (hzZ : z ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 20)))
    (hz2 : G.Adj z h₂) (hgz : ¬G.Adj g z) (hg2 : ¬G.Adj g h₂)
    (hpoor : (G.neighborFinset h₂ ∩ Iso).card = 1)
    (f : Fin 20) (hfHub : f ∈ Hub) (hfd : G.degree f = 5)
    (hfiso5 : (G.neighborFinset f ∩ Iso).card = 5)
    (c r_t r_z a b : Fin 20)
    (hRfilter : Hub.filter (fun h => G.degree h = 4 ∧ 2 ≤ (G.neighborFinset h ∩ Iso).card)
      = ({g, r_t, r_z, a, b} : Finset (Fin 20)))
    (hRcard5 : ({g, r_t, r_z, a, b} : Finset (Fin 20)).card = 5)
    (hcIso : c ∈ Iso) (_hgc : G.Adj g c) (hh₂c : G.Adj h₂ c) (hr_tc : G.Adj r_t c)
    (hNc : G.neighborFinset c ∩ Hub = ({h₂, g, r_t} : Finset (Fin 20)))
    (hNz : G.neighborFinset z ∩ Hub = ({h₂, r_z} : Finset (Fin 20)))
    (hNh₂ : G.neighborFinset h₂ ∩ Hub = ({a, b} : Finset (Fin 20)))
    (hr_zz : G.Adj r_z z) (hah₂ : G.Adj a h₂) (hbh₂ : G.Adj b h₂)
    (hr_tHub : r_t ∈ Hub) (hr_td : G.degree r_t = 4) (hr_zHub : r_z ∈ Hub)
    (hr_zd : G.degree r_z = 4) (_haHub : a ∈ Hub) (had : G.degree a = 4)
    (_hbHub : b ∈ Hub) (hbd : G.degree b = 4)
    (z' p q : Fin 20)
    (hz'Z : z' ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 20)))
    (hzz' : G.Adj z z') (hz'deg3 : G.degree z' = 3)
    (_hz'iso0 : (G.neighborFinset z' ∩ Iso).card = 0)
    (hNz'eq : G.neighborFinset z' ∩ Hub = ({p, q} : Finset (Fin 20)))
    (hp : p ∈ Hub) (hq : q ∈ Hub) (hdp : G.degree p = 4) (hdq : G.degree q = 4)
    (hpq : p ≠ q) (hz'p : G.Adj z' p) (hz'q : G.Adj z' q) (hnpq : ¬G.Adj p q)
    (_hshare0 : (G.neighborFinset p ∩ G.neighborFinset q ∩ Iso).card = 0)
    (hppoor : (G.neighborFinset p ∩ Iso).card ≤ 1)
    (hqpoor : (G.neighborFinset q ∩ Iso).card ≤ 1)
    (hph₂ : p ≠ h₂) (hpr_z : p ≠ r_z) (hqh₂ : q ≠ h₂) (hqr_z : q ≠ r_z)
    (hP5 : (Hub.filter
      (fun h => G.degree h = 4 ∧ (G.neighborFinset h ∩ Iso).card ≤ 1)).card = 5)
    (hall1 : ∀ x ∈ Hub.filter
      (fun h => G.degree h = 4 ∧ (G.neighborFinset h ∩ Iso).card ≤ 1),
      (G.neighborFinset x ∩ Iso).card = 1)
    (hRiso11 : (∑ r ∈ Hub.filter
      (fun h => G.degree h = 4 ∧ 2 ≤ (G.neighborFinset h ∩ Iso).card),
      (G.neighborFinset r ∩ Iso).card) = 11)
    (_hw : ∃ w : Fin 20, w ∈ Hub ∧ w ≠ h₂ ∧ w ≠ p ∧ w ≠ q ∧ w ≠ f ∧ G.degree w = 4 ∧
      (G.neighborFinset w ∩ Iso).card = 1 ∧ (G.Adj p w ∨ G.Adj q w))
    (hzdeg : G.degree z = 3)
    (heRR : (∑ r ∈ Hub.filter (fun h => G.degree h = 4 ∧ 2 ≤ (G.neighborFinset h ∩ Iso).card),
      (G.neighborFinset r ∩ Hub.filter
        (fun h => G.degree h = 4 ∧ 2 ≤ (G.neighborFinset h ∩ Iso).card)).card) ≤ 6)
    (hg3 : (G.neighborFinset g ∩ Iso).card = 3) :
    False := by
  classical
  set R : Finset (Fin 20) :=
    Hub.filter (fun h => G.degree h = 4 ∧ 2 ≤ (G.neighborFinset h ∩ Iso).card) with hRdef
  set P : Finset (Fin 20) :=
    Hub.filter (fun h => G.degree h = 4 ∧ (G.neighborFinset h ∩ Iso).card ≤ 1) with hPdef
  -- === `R` basics. ===
  have hRsub : R ⊆ Hub := by rw [hRdef]; exact Finset.filter_subset _ _
  have hRdeg4 : ∀ r ∈ R, G.degree r = 4 := by
    intro r hr; rw [hRdef, Finset.mem_filter] at hr; exact hr.2.1
  have hRiso2 : ∀ r ∈ R, 2 ≤ (G.neighborFinset r ∩ Iso).card := by
    intro r hr; rw [hRdef, Finset.mem_filter] at hr; exact hr.2.2
  have hRcard : R.card = 5 := by rw [hRfilter]; exact hRcard5
  -- === Dispatch `Σ ≤ 2` to the compiled world-(i) leaf. ===
  by_cases hle2 : (∑ r ∈ R, (G.neighborFinset r ∩ R).card) ≤ 2
  · exact octahedron_world_i_two_hub_r5_twenty G Hub Iso R hiso3 hshare hno2hub
      hRsub hRdeg4 hRiso2 hRcard hIso hRiso11 hle2
  have hge3 : 3 ≤ (∑ r ∈ R, (G.neighborFinset r ∩ R).card) := by omega
  -- === Pairwise distinctness of `{g, r_t, r_z, a, b}` and small helpers. ===
  have pair_le : ∀ y1 y2 : Fin 20, ({y1, y2} : Finset (Fin 20)).card ≤ 2 := by
    intro y1 y2
    have := Finset.card_insert_le y1 ({y2} : Finset (Fin 20))
    simp only [Finset.card_singleton] at this; omega
  have triple_le : ∀ y1 y2 y3 : Fin 20, ({y1, y2, y3} : Finset (Fin 20)).card ≤ 3 := by
    intro y1 y2 y3
    have h1 := Finset.card_insert_le y1 ({y2, y3} : Finset (Fin 20))
    have h2 := pair_le y2 y3
    omega
  have quad_le : ∀ y0 y1 y2 y3 : Fin 20, ({y0, y1, y2, y3} : Finset (Fin 20)).card ≤ 4 := by
    intro y0 y1 y2 y3
    have h1 := Finset.card_insert_le y0 ({y1, y2, y3} : Finset (Fin 20))
    have h2 := triple_le y1 y2 y3
    omega
  have card3_ne : ∀ y1 y2 y3 : Fin 20, ({y1, y2, y3} : Finset (Fin 20)).card = 3 →
      y1 ≠ y2 ∧ y1 ≠ y3 ∧ y2 ≠ y3 := by
    intro y1 y2 y3 hc
    refine ⟨?_, ?_, ?_⟩
    · rintro rfl
      rw [Finset.insert_idem] at hc; have := pair_le y1 y3; omega
    · rintro rfl
      rw [Finset.insert_eq_self.mpr (show y1 ∈ ({y2, y1} : Finset (Fin 20)) by simp)] at hc
      have := pair_le y2 y1; omega
    · rintro rfl
      rw [Finset.insert_eq_self.mpr (show y2 ∈ ({y2} : Finset (Fin 20)) by simp)] at hc
      have := pair_le y1 y2; omega
  have hcdeg : G.degree c = 3 := hisodeg3 c hcIso
  have hc_notHub : c ∉ Hub := Finset.disjoint_right.mp hdisj hcIso
  have hz_notHub : z ∉ Hub := fun hcon =>
    (Finset.mem_sdiff.mp hzZ).2 (Finset.mem_union_left _ hcon)
  have hc3card : ({h₂, g, r_t} : Finset (Fin 20)).card = 3 := hNc ▸ hiso3 c hcIso
  obtain ⟨_, _, hg_rt⟩ := card3_ne h₂ g r_t hc3card
  have tri : ∀ u v w : Fin 20, u ≠ v → v ≠ w → u ≠ w →
      G.Adj u v → G.Adj v w → G.Adj u w →
      G.degree u + G.degree v + G.degree w ≤ 11 → False :=
    fun u v w huv hvw huw auv avw auw hd => hT ⟨u, v, w, huv, hvw, huw, auv, avw, auw, hd⟩
  have hg_rz : g ≠ r_z := by intro h; apply hgz; rw [h]; exact hr_zz
  have hg_a : g ≠ a := by intro h; apply hg2; rw [h]; exact hah₂
  have hg_b : g ≠ b := by intro h; apply hg2; rw [h]; exact hbh₂
  have hnh₂rz : ¬ G.Adj h₂ r_z := fun hadj =>
    tri h₂ r_z z (G.ne_of_adj hadj) (fun h => hz_notHub (h ▸ hr_zHub))
      (fun h => hz_notHub (h ▸ hh₂)) hadj hr_zz hz2.symm (by rw [hd₂, hr_zd, hzdeg])
  have hnh₂rt : ¬ G.Adj h₂ r_t := fun hadj =>
    tri h₂ r_t c (G.ne_of_adj hadj) (fun h => hc_notHub (h ▸ hr_tHub))
      (fun h => hc_notHub (h ▸ hh₂)) hadj hr_tc hh₂c (by rw [hd₂, hr_td, hcdeg])
  have hrz_a : r_z ≠ a := fun h => hnh₂rz (h ▸ hah₂.symm)
  have hrz_b : r_z ≠ b := fun h => hnh₂rz (h ▸ hbh₂.symm)
  have hrt_a : r_t ≠ a := fun h => hnh₂rt (h ▸ hah₂.symm)
  have hrt_b : r_t ≠ b := fun h => hnh₂rt (h ▸ hbh₂.symm)
  have hrt_rz : r_t ≠ r_z := by
    intro h
    rw [h, Finset.insert_idem] at hRcard5
    have := quad_le g r_z a b; omega
  have hab : a ≠ b := by
    intro h
    rw [h, Finset.insert_eq_self.mpr (Finset.mem_singleton_self b)] at hRcard5
    have := quad_le g r_t r_z b; omega
  -- === Membership of the five rich hubs; exclusions. ===
  have hgR : g ∈ R := by rw [hRfilter]; simp
  have hr_tR : r_t ∈ R := by rw [hRfilter]; simp
  have hr_zR : r_z ∈ R := by rw [hRfilter]; simp
  have haR : a ∈ R := by rw [hRfilter]; simp
  have hbR : b ∈ R := by rw [hRfilter]; simp
  have hh₂notR : h₂ ∉ R := by
    intro hcon
    rw [hRdef, Finset.mem_filter] at hcon
    have := hcon.2.2; omega
  have hpnotR : p ∉ R := by
    intro hcon
    rw [hRdef, Finset.mem_filter] at hcon
    have := hcon.2.2; omega
  have hqnotR : q ∉ R := by
    intro hcon
    rw [hRdef, Finset.mem_filter] at hcon
    have := hcon.2.2; omega
  -- === `P` facts. ===
  have hh₂P : h₂ ∈ P := by
    rw [hPdef, Finset.mem_filter]; exact ⟨hh₂, hd₂, le_of_eq hpoor⟩
  have hpP : p ∈ P := by rw [hPdef, Finset.mem_filter]; exact ⟨hp, hdp, hppoor⟩
  have hqP : q ∈ P := by rw [hPdef, Finset.mem_filter]; exact ⟨hq, hdq, hqpoor⟩
  have hPHub : P ⊆ Hub := by rw [hPdef]; exact Finset.filter_subset _ _
  have hPdeg4 : ∀ u ∈ P, G.degree u = 4 := by
    intro u hu; rw [hPdef, Finset.mem_filter] at hu; exact hu.2.1
  have hrz_notP : r_z ∉ P := by
    intro hcon
    rw [hPdef, Finset.mem_filter] at hcon
    have h1 := hRiso2 r_z hr_zR
    have h2 := hcon.2.2; omega
  have ha_notP : a ∉ P := by
    intro hcon
    rw [hPdef, Finset.mem_filter] at hcon
    have h1 := hRiso2 a haR
    have h2 := hcon.2.2; omega
  have hb_notP : b ∉ P := by
    intro hcon
    rw [hPdef, Finset.mem_filter] at hcon
    have h1 := hRiso2 b hbR
    have h2 := hcon.2.2; omega
  have hRPdisj : Disjoint R P := by
    rw [Finset.disjoint_left]
    intro x hxR hxP
    rw [hRdef, Finset.mem_filter] at hxR
    rw [hPdef, Finset.mem_filter] at hxP
    omega
  have hfnotR : f ∉ R := by
    intro hcon; have := hRdeg4 f hcon; omega
  have hfnotP : f ∉ P := by
    intro hcon; have := hPdeg4 f hcon; omega
  -- === The deg-5 hub is unique, so `Hub` splits as `R ∪ P ∪ {f}`. ===
  have hdeg4' : ∀ v : Fin 20, v ∈ Hub → v ≠ f → G.degree v = 4 := by
    intro v hvHub hvf
    have hvle : G.degree v ≤ 5 := hdeg5 v hvHub
    have hvge : 4 ≤ G.degree v := hdeg v hvHub
    by_contra hne4
    have hv5 : G.degree v = 5 := by omega
    have hsplitf : ∑ w ∈ Hub, G.degree w = G.degree f + ∑ w ∈ Hub.erase f, G.degree w :=
      (Finset.add_sum_erase _ (fun w => G.degree w) hfHub).symm
    have hvef : v ∈ Hub.erase f := Finset.mem_erase.mpr ⟨hvf, hvHub⟩
    have hsplitv : ∑ w ∈ Hub.erase f, G.degree w
        = G.degree v + ∑ w ∈ (Hub.erase f).erase v, G.degree w :=
      (Finset.add_sum_erase _ (fun w => G.degree w) hvef).symm
    have hrest : 4 * ((Hub.erase f).erase v).card
        ≤ ∑ w ∈ (Hub.erase f).erase v, G.degree w := by
      have hb : ∀ x ∈ (Hub.erase f).erase v, 4 ≤ G.degree x := fun x hx =>
        hdeg x (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx))
      have h := Finset.card_nsmul_le_sum ((Hub.erase f).erase v) (fun w => G.degree w) 4 hb
      simpa [smul_eq_mul, mul_comm] using h
    have hcardef : (Hub.erase f).card = Hub.card - 1 := Finset.card_erase_of_mem hfHub
    have hcardefv : ((Hub.erase f).erase v).card = (Hub.erase f).card - 1 :=
      Finset.card_erase_of_mem hvef
    omega
  have hfhub0 : (G.neighborFinset f ∩ Hub).card = 0 := by
    have hs := nbr_split_three_twenty G Hub Iso hdisj f
    rw [hfd, hfiso5] at hs
    omega
  have hfnoHub : ∀ h ∈ Hub, ¬G.Adj f h := by
    intro h hh hadj
    have hmem : h ∈ G.neighborFinset f ∩ Hub :=
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset f h).mpr hadj, hh⟩
    rw [Finset.card_eq_zero.mp hfhub0] at hmem
    exact Finset.notMem_empty h hmem
  have htri : ∀ x ∈ Hub, x ∈ R ∨ x ∈ P ∨ x = f := by
    intro x hx
    by_cases hxf : x = f
    · exact Or.inr (Or.inr hxf)
    · have hx4 : G.degree x = 4 := hdeg4' x hx hxf
      by_cases hxi : 2 ≤ (G.neighborFinset x ∩ Iso).card
      · exact Or.inl (by rw [hRdef, Finset.mem_filter]; exact ⟨hx, hx4, hxi⟩)
      · exact Or.inr (Or.inl (by rw [hPdef, Finset.mem_filter]; exact ⟨hx, hx4, by omega⟩))
  have hfInt0 : ∀ v ∈ Hub, (G.neighborFinset v ∩ ({f} : Finset (Fin 20))).card = 0 := by
    intro v hv
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro x hx
    rw [Finset.mem_inter, Finset.mem_singleton] at hx
    obtain ⟨hxN, heq⟩ := hx
    rw [heq] at hxN
    exact hfnoHub v hv ((G.mem_neighborFinset v f).mp hxN).symm
  -- === Per-vertex split of the hub neighbourhood into `R`, `P`, `{f}`. ===
  have hpart : ∀ v : Fin 20, (G.neighborFinset v ∩ Hub).card
      = (G.neighborFinset v ∩ R).card + (G.neighborFinset v ∩ P).card
        + (G.neighborFinset v ∩ ({f} : Finset (Fin 20))).card := by
    intro v
    have hd1 : Disjoint (G.neighborFinset v ∩ P)
        (G.neighborFinset v ∩ ({f} : Finset (Fin 20))) := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      rw [Finset.mem_inter] at hx1
      rw [Finset.mem_inter, Finset.mem_singleton] at hx2
      exact hfnotP (hx2.2 ▸ hx1.2)
    have hd2 : Disjoint (G.neighborFinset v ∩ R)
        ((G.neighborFinset v ∩ P) ∪ (G.neighborFinset v ∩ ({f} : Finset (Fin 20)))) := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      rw [Finset.mem_inter] at hx1
      rw [Finset.mem_union] at hx2
      rcases hx2 with hx2 | hx2
      · rw [Finset.mem_inter] at hx2
        exact Finset.disjoint_left.mp hRPdisj hx1.2 hx2.2
      · rw [Finset.mem_inter, Finset.mem_singleton] at hx2
        exact hfnotR (hx2.2 ▸ hx1.2)
    have hseteq : G.neighborFinset v ∩ Hub
        = (G.neighborFinset v ∩ R) ∪ ((G.neighborFinset v ∩ P)
          ∪ (G.neighborFinset v ∩ ({f} : Finset (Fin 20)))) := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_singleton]
      constructor
      · rintro ⟨hxN, hxH⟩
        rcases htri x hxH with hxR | hxP | rfl
        · exact Or.inl ⟨hxN, hxR⟩
        · exact Or.inr (Or.inl ⟨hxN, hxP⟩)
        · exact Or.inr (Or.inr ⟨hxN, rfl⟩)
      · rintro (⟨hxN, hxR⟩ | ⟨hxN, hxP⟩ | ⟨hxN, rfl⟩)
        · exact ⟨hxN, hRsub hxR⟩
        · exact ⟨hxN, hPHub hxP⟩
        · exact ⟨hxN, hfHub⟩
    rw [hseteq, Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd1]
    omega
  -- === Each twin needs `≥ 2 − k` poor slots; the poor column sums to `5`. ===
  have hks2 : ∀ t ∈ Iso,
      2 ≤ (G.neighborFinset t ∩ R).card + (G.neighborFinset t ∩ P).card := by
    intro t ht
    have h3 := hiso3 t ht
    have hle1 : (G.neighborFinset t ∩ ({f} : Finset (Fin 20))).card ≤ 1 := by
      calc (G.neighborFinset t ∩ ({f} : Finset (Fin 20))).card
          ≤ ({f} : Finset (Fin 20)).card := Finset.card_le_card Finset.inter_subset_right
        _ = 1 := Finset.card_singleton f
    have := hpart t
    omega
  have hsP5 : (∑ t ∈ Iso, (G.neighborFinset t ∩ P).card) = 5 := by
    rw [cross_count_twenty G Iso P]
    calc (∑ x ∈ P, (G.neighborFinset x ∩ Iso).card)
        = ∑ x ∈ P, 1 := Finset.sum_congr rfl hall1
      _ = P.card := by rw [Finset.sum_const, smul_eq_mul, mul_one]
      _ = 5 := hP5
  have hM1 : (∑ t ∈ Iso, (G.neighborFinset t ∩ R).card) = 11 := by
    rw [cross_count_twenty G Iso R]; exact hRiso11
  -- === Exact share values on rich pairs. ===
  have hshare_adj : ∀ u ∈ R, ∀ v ∈ R, G.Adj u v →
      (G.neighborFinset u ∩ G.neighborFinset v ∩ Iso).card = 0 := by
    intro u hu v hv hadj
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro t ht
    rw [Finset.mem_inter, Finset.mem_inter] at ht
    obtain ⟨⟨htu, htv⟩, htIso⟩ := ht
    exact tri u v t (G.ne_of_adj hadj)
      (fun h => Finset.disjoint_left.mp hdisj (hRsub hv) (h ▸ htIso))
      (fun h => Finset.disjoint_left.mp hdisj (hRsub hu) (h ▸ htIso)) hadj
      ((G.mem_neighborFinset v t).mp htv) ((G.mem_neighborFinset u t).mp htu)
      (by rw [hRdeg4 u hu, hRdeg4 v hv, hisodeg3 t htIso])
  have hshare_nadj : ∀ u ∈ R, ∀ v ∈ R, u ≠ v → ¬G.Adj u v →
      (G.neighborFinset u ∩ G.neighborFinset v ∩ Iso).card = 1 := by
    intro u hu v hv hne hnadj
    have hle : (G.neighborFinset u ∩ G.neighborFinset v ∩ Iso).card ≤ 1 :=
      hshare u (hRsub hu) (hRdeg4 u hu) v (hRsub hv) (hRdeg4 v hv) hne hnadj
    have hge : 1 ≤ (G.neighborFinset u ∩ G.neighborFinset v ∩ Iso).card := by
      by_contra hcon
      rw [not_le, Nat.lt_one_iff] at hcon
      have hpu : ((G.neighborFinset u ∩ Iso) ∩ G.neighborFinset v).card = 0 := by
        rw [Finset.inter_right_comm]; exact hcon
      have hpv : ((G.neighborFinset v ∩ Iso) ∩ G.neighborFinset u).card = 0 := by
        rw [Finset.inter_right_comm,
          Finset.inter_comm (G.neighborFinset v) (G.neighborFinset u)]
        exact hcon
      have hpu2 : 2 ≤ ((G.neighborFinset u ∩ Iso) \ G.neighborFinset v).card := by
        have h := Finset.card_inter_add_card_sdiff (G.neighborFinset u ∩ Iso)
          (G.neighborFinset v)
        have h2 := hRiso2 u hu
        omega
      have hpv2 : 2 ≤ ((G.neighborFinset v ∩ Iso) \ G.neighborFinset u).card := by
        have h := Finset.card_inter_add_card_sdiff (G.neighborFinset v ∩ Iso)
          (G.neighborFinset u)
        have h2 := hRiso2 v hv
        omega
      exact hno2hub ⟨u, v, hRsub hu, hRsub hv, hRdeg4 u hu, hRdeg4 v hv, hne, hnadj,
        hpu2, hpv2⟩
    omega
  -- === Row identity for the shared-twin double count. ===
  have hcardInter : ∀ (u : Fin 20) (S : Finset (Fin 20)),
      (G.neighborFinset u ∩ S).card = ∑ v ∈ S, (if G.Adj u v then (1 : ℕ) else 0) := by
    intro u S
    rw [Finset.inter_comm, ← Finset.filter_mem_eq_inter, Finset.card_filter]
    exact Finset.sum_congr rfl (fun v _ => by simp only [G.mem_neighborFinset])
  have hrow : ∀ u ∈ R,
      (∑ v ∈ R, (G.neighborFinset u ∩ G.neighborFinset v ∩ Iso).card)
        + (G.neighborFinset u ∩ R).card
      = (G.neighborFinset u ∩ Iso).card + 4 := by
    intro u hu
    have hsplit : (∑ v ∈ R, (G.neighborFinset u ∩ G.neighborFinset v ∩ Iso).card)
        = (G.neighborFinset u ∩ Iso).card
          + ∑ v ∈ R.erase u, (G.neighborFinset u ∩ G.neighborFinset v ∩ Iso).card := by
      rw [← Finset.add_sum_erase R _ hu, Finset.inter_self]
    have hpervert : ∀ v ∈ R.erase u,
        (G.neighborFinset u ∩ G.neighborFinset v ∩ Iso).card
          = (if G.Adj u v then (0 : ℕ) else 1) := by
      intro v hv
      by_cases h : G.Adj u v
      · rw [if_pos h]; exact hshare_adj u hu v (Finset.mem_of_mem_erase hv) h
      · rw [if_neg h]
        exact hshare_nadj u hu v (Finset.mem_of_mem_erase hv)
          (Finset.ne_of_mem_erase hv).symm h
    have herase : (∑ v ∈ R.erase u, (G.neighborFinset u ∩ G.neighborFinset v ∩ Iso).card)
        = ∑ v ∈ R.erase u, (if G.Adj u v then (0 : ℕ) else 1) :=
      Finset.sum_congr rfl hpervert
    have hadjcard : (∑ v ∈ R.erase u, (if G.Adj u v then (1 : ℕ) else 0))
        = (G.neighborFinset u ∩ R).card := by
      rw [hcardInter u R,
        ← Finset.sum_erase R
          (by simp [SimpleGraph.irrefl] : (if G.Adj u u then (1 : ℕ) else 0) = 0)]
    have hpt1 : ∀ v ∈ R.erase u, (if G.Adj u v then (0 : ℕ) else 1)
        + (if G.Adj u v then (1 : ℕ) else 0) = 1 := by
      intro v _
      by_cases h : G.Adj u v <;> simp [h]
    have hcompl : (∑ v ∈ R.erase u, ((if G.Adj u v then (0 : ℕ) else 1)
        + (if G.Adj u v then (1 : ℕ) else 0))) = (R.erase u).card := by
      rw [Finset.sum_congr rfl hpt1, Finset.sum_const, smul_eq_mul, mul_one]
    rw [Finset.sum_add_distrib] at hcompl
    have hecard : (R.erase u).card = 4 := by
      rw [Finset.card_erase_of_mem hu, hRcard]
    omega
  -- === `∑ k² + Σ = 31` via `cherry_double_count`. ===
  have hDC31 : (∑ t ∈ Iso, (G.neighborFinset t ∩ R).card * (G.neighborFinset t ∩ R).card)
      + (∑ r ∈ R, (G.neighborFinset r ∩ R).card) = 31 := by
    have hsum : (∑ u ∈ R, ((∑ v ∈ R, (G.neighborFinset u ∩ G.neighborFinset v ∩ Iso).card)
        + (G.neighborFinset u ∩ R).card))
        = ∑ u ∈ R, ((G.neighborFinset u ∩ Iso).card + 4) :=
      Finset.sum_congr rfl hrow
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hRiso11] at hsum
    have hc4 : (∑ _u ∈ R, (4 : ℕ)) = 20 := by
      rw [Finset.sum_const, hRcard]; rfl
    rw [hc4] at hsum
    rw [← cherry_double_count G R Iso]
    omega
  -- === Twin `k`-profile: filter counts and the two moments. ===
  have hk3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ R).card ≤ 3 := by
    intro t ht
    calc (G.neighborFinset t ∩ R).card
        ≤ (G.neighborFinset t ∩ Hub).card :=
          Finset.card_le_card (Finset.inter_subset_inter (Finset.Subset.refl _) hRsub)
      _ = 3 := hiso3 t ht
  have hM7 : (Iso.filter (fun t => (G.neighborFinset t ∩ R).card = 0)).card
      + (Iso.filter (fun t => (G.neighborFinset t ∩ R).card = 1)).card
      + (Iso.filter (fun t => (G.neighborFinset t ∩ R).card = 2)).card
      + (Iso.filter (fun t => (G.neighborFinset t ∩ R).card = 3)).card = 7 := by
    have hpt : ∀ t ∈ Iso, (1 : ℕ)
        = (if (G.neighborFinset t ∩ R).card = 0 then (1 : ℕ) else 0)
          + (if (G.neighborFinset t ∩ R).card = 1 then (1 : ℕ) else 0)
          + (if (G.neighborFinset t ∩ R).card = 2 then (1 : ℕ) else 0)
          + (if (G.neighborFinset t ∩ R).card = 3 then (1 : ℕ) else 0) := by
      intro t ht
      have h3 := hk3 t ht
      rcases (show (G.neighborFinset t ∩ R).card = 0 ∨ (G.neighborFinset t ∩ R).card = 1
          ∨ (G.neighborFinset t ∩ R).card = 2 ∨ (G.neighborFinset t ∩ R).card = 3 by omega)
        with h | h | h | h <;> rw [h] <;> decide
    have hsum := Finset.sum_congr rfl hpt
    rw [Finset.sum_const, smul_eq_mul, mul_one, hIso, Finset.sum_add_distrib,
      Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_boole, Finset.sum_boole,
      Finset.sum_boole, Finset.sum_boole, Nat.cast_id, Nat.cast_id, Nat.cast_id,
      Nat.cast_id] at hsum
    omega
  have hM11 : (Iso.filter (fun t => (G.neighborFinset t ∩ R).card = 1)).card
      + 2 * (Iso.filter (fun t => (G.neighborFinset t ∩ R).card = 2)).card
      + 3 * (Iso.filter (fun t => (G.neighborFinset t ∩ R).card = 3)).card = 11 := by
    have hpt : ∀ t ∈ Iso, (G.neighborFinset t ∩ R).card
        = (if (G.neighborFinset t ∩ R).card = 1 then (1 : ℕ) else 0)
          + 2 * (if (G.neighborFinset t ∩ R).card = 2 then (1 : ℕ) else 0)
          + 3 * (if (G.neighborFinset t ∩ R).card = 3 then (1 : ℕ) else 0) := by
      intro t ht
      have h3 := hk3 t ht
      rcases (show (G.neighborFinset t ∩ R).card = 0 ∨ (G.neighborFinset t ∩ R).card = 1
          ∨ (G.neighborFinset t ∩ R).card = 2 ∨ (G.neighborFinset t ∩ R).card = 3 by omega)
        with h | h | h | h <;> rw [h] <;> decide
    have hsum := Finset.sum_congr rfl hpt
    rw [hM1, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, Finset.sum_boole, Finset.sum_boole, Finset.sum_boole,
      Nat.cast_id, Nat.cast_id, Nat.cast_id] at hsum
    omega
  have hM31 : (Iso.filter (fun t => (G.neighborFinset t ∩ R).card = 1)).card
      + 4 * (Iso.filter (fun t => (G.neighborFinset t ∩ R).card = 2)).card
      + 9 * (Iso.filter (fun t => (G.neighborFinset t ∩ R).card = 3)).card
      + (∑ r ∈ R, (G.neighborFinset r ∩ R).card) = 31 := by
    have hpt : ∀ t ∈ Iso, (G.neighborFinset t ∩ R).card * (G.neighborFinset t ∩ R).card
        = (if (G.neighborFinset t ∩ R).card = 1 then (1 : ℕ) else 0)
          + 4 * (if (G.neighborFinset t ∩ R).card = 2 then (1 : ℕ) else 0)
          + 9 * (if (G.neighborFinset t ∩ R).card = 3 then (1 : ℕ) else 0) := by
      intro t ht
      have h3 := hk3 t ht
      rcases (show (G.neighborFinset t ∩ R).card = 0 ∨ (G.neighborFinset t ∩ R).card = 1
          ∨ (G.neighborFinset t ∩ R).card = 2 ∨ (G.neighborFinset t ∩ R).card = 3 by omega)
        with h | h | h | h <;> rw [h] <;> decide
    have hsum := Finset.sum_congr rfl hpt
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      Finset.sum_boole, Finset.sum_boole, Finset.sum_boole, Nat.cast_id, Nat.cast_id,
      Nat.cast_id] at hsum
    omega
  -- === The twin `c` of `h₂`: `k c = 2`, one poor slot. ===
  have hNcR : G.neighborFinset c ∩ R = ({g, r_t} : Finset (Fin 20)) := by
    have h1 : G.neighborFinset c ∩ R = (G.neighborFinset c ∩ Hub) ∩ R := by
      rw [Finset.inter_assoc, Finset.inter_eq_right.mpr hRsub]
    rw [h1, hNc]
    ext x
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨(rfl | rfl | rfl), hxR⟩
      · exact absurd hxR hh₂notR
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rintro (rfl | rfl)
      · exact ⟨Or.inr (Or.inl rfl), hgR⟩
      · exact ⟨Or.inr (Or.inr rfl), hr_tR⟩
  have hkc : (G.neighborFinset c ∩ R).card = 2 := by
    rw [hNcR]; exact Finset.card_pair hg_rt
  have hNcP : G.neighborFinset c ∩ P = ({h₂} : Finset (Fin 20)) := by
    have h1 : G.neighborFinset c ∩ P = (G.neighborFinset c ∩ Hub) ∩ P := by
      rw [Finset.inter_assoc, Finset.inter_eq_right.mpr hPHub]
    rw [h1, hNc]
    ext x
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨(rfl | rfl | rfl), hxP⟩
      · rfl
      · exfalso
        rw [hPdef, Finset.mem_filter] at hxP
        have := hxP.2.2; omega
      · exfalso
        rw [hPdef, Finset.mem_filter] at hxP
        have h1 := hRiso2 _ hr_tR
        have h2 := hxP.2.2; omega
    · rintro rfl
      exact ⟨Or.inl rfl, hh₂P⟩
  have hsc : (G.neighborFinset c ∩ P).card = 1 := by
    rw [hNcP]; exact Finset.card_singleton h₂
  -- === Profile dispatch: kill A (poor-slot overcount) or `Σ = 6` with a `k = 0` twin. ===
  rcases (show 5 ≤ 2 * (Iso.filter (fun t => (G.neighborFinset t ∩ R).card = 0)).card
        + (Iso.filter (fun t => (G.neighborFinset t ∩ R).card = 1)).card
      ∨ ((∑ r ∈ R, (G.neighborFinset r ∩ R).card) = 6
        ∧ 1 ≤ (Iso.filter (fun t => (G.neighborFinset t ∩ R).card = 0)).card) by omega)
    with hkillA | ⟨hS6, hn0pos⟩
  · -- === KILL A: `∑_t |N t ∩ P| = 5` but the low-`k` twins plus `c` need `≥ 6`. ===
    have hA01 : Disjoint (Iso.filter (fun t => (G.neighborFinset t ∩ R).card = 0))
        (Iso.filter (fun t => (G.neighborFinset t ∩ R).card = 1)) := by
      rw [Finset.disjoint_left]
      intro x hx0 hx1
      rw [Finset.mem_filter] at hx0 hx1
      omega
    have hcnot : c ∉ (Iso.filter (fun t => (G.neighborFinset t ∩ R).card = 0))
        ∪ (Iso.filter (fun t => (G.neighborFinset t ∩ R).card = 1)) := by
      intro hmem
      rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter] at hmem
      rcases hmem with ⟨_, h⟩ | ⟨_, h⟩ <;> omega
    have hsub01 : (Iso.filter (fun t => (G.neighborFinset t ∩ R).card = 0))
        ∪ (Iso.filter (fun t => (G.neighborFinset t ∩ R).card = 1)) ⊆ Iso := by
      intro x hx
      rw [Finset.mem_union] at hx
      rcases hx with hx | hx
      · exact Finset.mem_of_mem_filter x hx
      · exact Finset.mem_of_mem_filter x hx
    have hcs : c ∈ Iso \ ((Iso.filter (fun t => (G.neighborFinset t ∩ R).card = 0))
        ∪ (Iso.filter (fun t => (G.neighborFinset t ∩ R).card = 1))) :=
      Finset.mem_sdiff.mpr ⟨hcIso, hcnot⟩
    have hle : (G.neighborFinset c ∩ P).card
        ≤ ∑ t ∈ Iso \ ((Iso.filter (fun t => (G.neighborFinset t ∩ R).card = 0))
          ∪ (Iso.filter (fun t => (G.neighborFinset t ∩ R).card = 1))),
          (G.neighborFinset t ∩ P).card :=
      Finset.single_le_sum (f := fun t => (G.neighborFinset t ∩ P).card)
        (fun i _ => Nat.zero_le _) hcs
    have h0 : (Iso.filter (fun t => (G.neighborFinset t ∩ R).card = 0)).card * 2
        ≤ ∑ t ∈ Iso.filter (fun t => (G.neighborFinset t ∩ R).card = 0),
          (G.neighborFinset t ∩ P).card := by
      have hb : ∀ t ∈ Iso.filter (fun t => (G.neighborFinset t ∩ R).card = 0),
          2 ≤ (G.neighborFinset t ∩ P).card := by
        intro t ht
        rw [Finset.mem_filter] at ht
        have h1 := hks2 t ht.1
        omega
      have h := Finset.card_nsmul_le_sum
        (Iso.filter (fun t => (G.neighborFinset t ∩ R).card = 0))
        (fun t => (G.neighborFinset t ∩ P).card) 2 hb
      rw [smul_eq_mul] at h
      exact h
    have h1 : (Iso.filter (fun t => (G.neighborFinset t ∩ R).card = 1)).card
        ≤ ∑ t ∈ Iso.filter (fun t => (G.neighborFinset t ∩ R).card = 1),
          (G.neighborFinset t ∩ P).card := by
      have hb : ∀ t ∈ Iso.filter (fun t => (G.neighborFinset t ∩ R).card = 1),
          1 ≤ (G.neighborFinset t ∩ P).card := by
        intro t ht
        rw [Finset.mem_filter] at ht
        have h1 := hks2 t ht.1
        omega
      have h := Finset.card_nsmul_le_sum
        (Iso.filter (fun t => (G.neighborFinset t ∩ R).card = 1))
        (fun t => (G.neighborFinset t ∩ P).card) 1 hb
      rw [smul_eq_mul, mul_one] at h
      exact h
    have hsplit := Finset.sum_sdiff (f := fun t => (G.neighborFinset t ∩ P).card) hsub01
    rw [Finset.sum_union hA01, hsP5] at hsplit
    omega
  · -- === KILL B: `Σ = 6` exhausts the rich spare slots; a `k = 0` twin dies. ===
    -- `Z = {z, z'}`.
    have hzz'ne : z ≠ z' := G.ne_of_adj hzz'
    have hZcard : (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 20)).card = 2 := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
        Fintype.card_fin, Finset.card_union_of_disjoint hdisj, hHub, hIso]
    have hZeq : (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 20))
        = ({z, z'} : Finset (Fin 20)) := by
      have hsub : ({z, z'} : Finset (Fin 20)) ⊆ (Finset.univ \ (Hub ∪ Iso)) := by
        intro x hx
        rw [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact hzZ
        · exact hz'Z
      have hcard2 : ({z, z'} : Finset (Fin 20)).card = 2 := Finset.card_pair hzz'ne
      exact (Finset.eq_of_subset_of_card_le hsub (by omega)).symm
    -- `Z`-degrees of the rich hubs.
    have hZnone : ∀ r : Fin 20, r ∈ R → r ≠ r_z →
        (G.neighborFinset r ∩ (Finset.univ \ (Hub ∪ Iso))).card = 0 := by
      intro r hrR hrne
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro x hx
      rw [Finset.mem_inter] at hx
      obtain ⟨hxN, hxZ⟩ := hx
      rw [hZeq, Finset.mem_insert, Finset.mem_singleton] at hxZ
      rcases hxZ with heq | heq
      · rw [heq] at hxN
        have hadj : G.Adj r z := (G.mem_neighborFinset r z).mp hxN
        have hmem : r ∈ G.neighborFinset z ∩ Hub :=
          Finset.mem_inter.mpr ⟨(G.mem_neighborFinset z r).mpr hadj.symm, hRsub hrR⟩
        rw [hNz, Finset.mem_insert, Finset.mem_singleton] at hmem
        rcases hmem with rfl | rfl
        · exact hh₂notR hrR
        · exact hrne rfl
      · rw [heq] at hxN
        have hadj : G.Adj r z' := (G.mem_neighborFinset r z').mp hxN
        have hmem : r ∈ G.neighborFinset z' ∩ Hub :=
          Finset.mem_inter.mpr ⟨(G.mem_neighborFinset z' r).mpr hadj.symm, hRsub hrR⟩
        rw [hNz'eq, Finset.mem_insert, Finset.mem_singleton] at hmem
        rcases hmem with rfl | rfl
        · exact hpnotR hrR
        · exact hqnotR hrR
    have hZrz : (G.neighborFinset r_z ∩ (Finset.univ \ (Hub ∪ Iso))).card = 1 := by
      have hset : G.neighborFinset r_z ∩ (Finset.univ \ (Hub ∪ Iso))
          = ({z} : Finset (Fin 20)) := by
        ext x
        rw [Finset.mem_inter, Finset.mem_singleton]
        constructor
        · rintro ⟨hxN, hxZ⟩
          rw [hZeq, Finset.mem_insert, Finset.mem_singleton] at hxZ
          rcases hxZ with heq | heq
          · exact heq
          · exfalso
            rw [heq] at hxN
            have hadj : G.Adj r_z z' := (G.mem_neighborFinset r_z z').mp hxN
            have hmem : r_z ∈ G.neighborFinset z' ∩ Hub :=
              Finset.mem_inter.mpr ⟨(G.mem_neighborFinset z' r_z).mpr hadj.symm, hr_zHub⟩
            rw [hNz'eq, Finset.mem_insert, Finset.mem_singleton] at hmem
            rcases hmem with heq' | heq'
            · exact hpr_z heq'.symm
            · exact hqr_z heq'.symm
        · intro heq
          rw [heq]
          exact ⟨(G.mem_neighborFinset r_z z).mpr hr_zz, hzZ⟩
      rw [hset, Finset.card_singleton]
    -- Sum expansion over the explicit five-element `R`.
    have hsumR : ∀ F : Fin 20 → ℕ, (∑ r ∈ R, F r) = F g + F r_t + F r_z + F a + F b := by
      intro F
      rw [hRfilter, Finset.sum_insert (by simp [hg_rt, hg_rz, hg_a, hg_b]),
        Finset.sum_insert (by simp [hrt_rz, hrt_a, hrt_b]),
        Finset.sum_insert (by simp [hrz_a, hrz_b]),
        Finset.sum_insert (by simp [hab]), Finset.sum_singleton]
      ring
    -- Exact iso-degrees of the rich hubs.
    have hisoR : (∑ r ∈ R, (G.neighborFinset r ∩ Iso).card)
        = (G.neighborFinset g ∩ Iso).card + (G.neighborFinset r_t ∩ Iso).card
          + (G.neighborFinset r_z ∩ Iso).card + (G.neighborFinset a ∩ Iso).card
          + (G.neighborFinset b ∩ Iso).card :=
      hsumR (fun r => (G.neighborFinset r ∩ Iso).card)
    have hrt_iso : (G.neighborFinset r_t ∩ Iso).card = 2 := by
      have h1 := hRiso2 r_t hr_tR
      have h2 := hRiso2 r_z hr_zR
      have h3 := hRiso2 a haR
      have h4 := hRiso2 b hbR
      omega
    have hrz_iso : (G.neighborFinset r_z ∩ Iso).card = 2 := by
      have h1 := hRiso2 r_t hr_tR
      have h2 := hRiso2 r_z hr_zR
      have h3 := hRiso2 a haR
      have h4 := hRiso2 b hbR
      omega
    have ha_iso : (G.neighborFinset a ∩ Iso).card = 2 := by
      have h1 := hRiso2 r_t hr_tR
      have h2 := hRiso2 r_z hr_zR
      have h3 := hRiso2 a haR
      have h4 := hRiso2 b hbR
      omega
    have hb_iso : (G.neighborFinset b ∩ Iso).card = 2 := by
      have h1 := hRiso2 r_t hr_tR
      have h2 := hRiso2 r_z hr_zR
      have h3 := hRiso2 a haR
      have h4 := hRiso2 b hbR
      omega
    -- Exact hub-degrees of the rich hubs: `1 + 2 + 1 + 2 + 2 = 8`.
    have hgHub : (G.neighborFinset g ∩ Hub).card = 1 := by
      have h := nbr_split_three_twenty G Hub Iso hdisj g
      have hz0 := hZnone g hgR hg_rz
      rw [hgd] at h
      omega
    have hrtHub : (G.neighborFinset r_t ∩ Hub).card = 2 := by
      have h := nbr_split_three_twenty G Hub Iso hdisj r_t
      have hz0 := hZnone r_t hr_tR hrt_rz
      rw [hr_td] at h
      omega
    have hrzHub : (G.neighborFinset r_z ∩ Hub).card = 1 := by
      have h := nbr_split_three_twenty G Hub Iso hdisj r_z
      rw [hr_zd] at h
      omega
    have haHub2 : (G.neighborFinset a ∩ Hub).card = 2 := by
      have h := nbr_split_three_twenty G Hub Iso hdisj a
      have hz0 := hZnone a haR hrz_a.symm
      rw [had] at h
      omega
    have hbHub2 : (G.neighborFinset b ∩ Hub).card = 2 := by
      have h := nbr_split_three_twenty G Hub Iso hdisj b
      have hz0 := hZnone b hbR hrz_b.symm
      rw [hbd] at h
      omega
    have hHubsum8 : (∑ r ∈ R, (G.neighborFinset r ∩ Hub).card) = 8 := by
      have h : (∑ r ∈ R, (G.neighborFinset r ∩ Hub).card)
          = (G.neighborFinset g ∩ Hub).card + (G.neighborFinset r_t ∩ Hub).card
            + (G.neighborFinset r_z ∩ Hub).card + (G.neighborFinset a ∩ Hub).card
            + (G.neighborFinset b ∩ Hub).card :=
        hsumR (fun r => (G.neighborFinset r ∩ Hub).card)
      omega
    have hfR0 : (∑ r ∈ R, (G.neighborFinset r ∩ ({f} : Finset (Fin 20))).card) = 0 :=
      Finset.sum_eq_zero (fun r hr => hfInt0 r (hRsub hr))
    have heRP : (∑ r ∈ R, (G.neighborFinset r ∩ P).card) = 2 := by
      have h : (∑ r ∈ R, (G.neighborFinset r ∩ Hub).card)
          = (∑ r ∈ R, (G.neighborFinset r ∩ R).card)
            + (∑ r ∈ R, (G.neighborFinset r ∩ P).card)
            + (∑ r ∈ R, (G.neighborFinset r ∩ ({f} : Finset (Fin 20))).card) := by
        rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun r _ => hpart r)
      omega
    -- The poor column: `∑_P |N x ∩ P| = 10`.
    have hPdeg20 : (∑ x ∈ P, G.degree x) = 20 := by
      have h4 : (∑ x ∈ P, G.degree x) = 4 * P.card := by
        rw [Finset.sum_congr rfl hPdeg4, Finset.sum_const, smul_eq_mul, mul_comm]
      rw [h4, hP5]
    have hPiso5sum : (∑ x ∈ P, (G.neighborFinset x ∩ Iso).card) = 5 := by
      calc (∑ x ∈ P, (G.neighborFinset x ∩ Iso).card)
          = ∑ x ∈ P, 1 := Finset.sum_congr rfl hall1
        _ = P.card := by rw [Finset.sum_const, smul_eq_mul, mul_one]
        _ = 5 := hP5
    have hPZ3 : (∑ x ∈ P, (G.neighborFinset x ∩ (Finset.univ \ (Hub ∪ Iso))).card) = 3 := by
      rw [cross_count_twenty G P (Finset.univ \ (Hub ∪ Iso)), hZeq,
        Finset.sum_pair hzz'ne]
      have h1 : G.neighborFinset z ∩ P = ({h₂} : Finset (Fin 20)) := by
        have hh : G.neighborFinset z ∩ P = (G.neighborFinset z ∩ Hub) ∩ P := by
          rw [Finset.inter_assoc, Finset.inter_eq_right.mpr hPHub]
        rw [hh, hNz]
        ext x
        simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨(rfl | rfl), hxP⟩
          · rfl
          · exact absurd hxP hrz_notP
        · rintro rfl
          exact ⟨Or.inl rfl, hh₂P⟩
      have h2 : G.neighborFinset z' ∩ P = ({p, q} : Finset (Fin 20)) := by
        have hh : G.neighborFinset z' ∩ P = (G.neighborFinset z' ∩ Hub) ∩ P := by
          rw [Finset.inter_assoc, Finset.inter_eq_right.mpr hPHub]
        rw [hh, hNz'eq]
        ext x
        simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨hx, _⟩; exact hx
        · rintro (rfl | rfl)
          · exact ⟨Or.inl rfl, hpP⟩
          · exact ⟨Or.inr rfl, hqP⟩
      rw [h1, h2, Finset.card_singleton, Finset.card_pair hpq]
    have hPHubsum : (∑ x ∈ P, (G.neighborFinset x ∩ Hub).card) = 12 := by
      have h : (∑ x ∈ P, ((G.neighborFinset x ∩ Hub).card + (G.neighborFinset x ∩ Iso).card
          + (G.neighborFinset x ∩ (Finset.univ \ (Hub ∪ Iso))).card))
          = ∑ x ∈ P, G.degree x :=
        Finset.sum_congr rfl (fun x _ => nbr_split_three_twenty G Hub Iso hdisj x)
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at h
      omega
    have hPR2 : (∑ x ∈ P, (G.neighborFinset x ∩ R).card) = 2 := by
      rw [← cross_count_twenty G R P]
      exact heRP
    have hPf0 : (∑ x ∈ P, (G.neighborFinset x ∩ ({f} : Finset (Fin 20))).card) = 0 :=
      Finset.sum_eq_zero (fun x hx => hfInt0 x (hPHub hx))
    have hPP10 : (∑ x ∈ P, (G.neighborFinset x ∩ P).card) = 10 := by
      have h : (∑ x ∈ P, (G.neighborFinset x ∩ Hub).card)
          = (∑ x ∈ P, (G.neighborFinset x ∩ R).card)
            + (∑ x ∈ P, (G.neighborFinset x ∩ P).card)
            + (∑ x ∈ P, (G.neighborFinset x ∩ ({f} : Finset (Fin 20))).card) := by
        rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun x _ => hpart x)
      omega
    -- `P = {h₂, p, q, w₁, w₂}`.
    have h₂notpq : h₂ ∉ ({p, q} : Finset (Fin 20)) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hph₂.symm, hqh₂.symm⟩
    have h3sub : ({h₂, p, q} : Finset (Fin 20)) ⊆ P := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact hh₂P
      · exact hpP
      · exact hqP
    have h3card : ({h₂, p, q} : Finset (Fin 20)).card = 3 := by
      rw [Finset.card_insert_of_notMem h₂notpq, Finset.card_pair hpq]
    have hdiffcard : (P \ ({h₂, p, q} : Finset (Fin 20))).card = 2 := by
      rw [Finset.card_sdiff_of_subset h3sub, hP5, h3card]
    obtain ⟨w₁, w₂, hw12ne, hdiffeq⟩ := Finset.card_eq_two.mp hdiffcard
    have hw₁mem : w₁ ∈ P \ ({h₂, p, q} : Finset (Fin 20)) := by
      rw [hdiffeq]; exact Finset.mem_insert_self w₁ {w₂}
    have hw₂mem : w₂ ∈ P \ ({h₂, p, q} : Finset (Fin 20)) := by
      rw [hdiffeq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self w₂)
    have hw₁P : w₁ ∈ P := (Finset.mem_sdiff.mp hw₁mem).1
    have hw₂P : w₂ ∈ P := (Finset.mem_sdiff.mp hw₂mem).1
    have hPeq5 : P = ({h₂, p, q, w₁, w₂} : Finset (Fin 20)) := by
      have h1 : ({h₂, p, q} : Finset (Fin 20)) ∪ (P \ ({h₂, p, q} : Finset (Fin 20))) = P :=
        Finset.union_sdiff_of_subset h3sub
      rw [hdiffeq] at h1
      rw [← h1]
      ext y
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, or_assoc]
    -- `h₂` is `P`-isolated; per-vertex caps on the poor column.
    have hh₂noP : ∀ x ∈ P, ¬ G.Adj h₂ x := by
      intro x hxP hadj
      have hmem : x ∈ G.neighborFinset h₂ ∩ Hub :=
        Finset.mem_inter.mpr ⟨(G.mem_neighborFinset h₂ x).mpr hadj, hPHub hxP⟩
      rw [hNh₂, Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with rfl | rfl
      · exact ha_notP hxP
      · exact hb_notP hxP
    have hth₂ : (G.neighborFinset h₂ ∩ P).card = 0 := by
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro x hx
      rw [Finset.mem_inter] at hx
      exact hh₂noP x hx.2 ((G.mem_neighborFinset h₂ x).mp hx.1)
    have hsubp : G.neighborFinset p ∩ P ⊆ ({w₁, w₂} : Finset (Fin 20)) := by
      intro y hy
      rw [Finset.mem_inter, G.mem_neighborFinset] at hy
      obtain ⟨hadj, hyP⟩ := hy
      have hy5 : y ∈ ({h₂, p, q, w₁, w₂} : Finset (Fin 20)) := by rw [← hPeq5]; exact hyP
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy5 ⊢
      rcases hy5 with rfl | rfl | rfl | rfl | rfl
      · exact absurd hadj.symm (hh₂noP p hpP)
      · exact absurd rfl (G.ne_of_adj hadj)
      · exact absurd hadj hnpq
      · exact Or.inl rfl
      · exact Or.inr rfl
    have hsubq : G.neighborFinset q ∩ P ⊆ ({w₁, w₂} : Finset (Fin 20)) := by
      intro y hy
      rw [Finset.mem_inter, G.mem_neighborFinset] at hy
      obtain ⟨hadj, hyP⟩ := hy
      have hy5 : y ∈ ({h₂, p, q, w₁, w₂} : Finset (Fin 20)) := by rw [← hPeq5]; exact hyP
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy5 ⊢
      rcases hy5 with rfl | rfl | rfl | rfl | rfl
      · exact absurd hadj.symm (hh₂noP q hqP)
      · exact absurd hadj.symm hnpq
      · exact absurd rfl (G.ne_of_adj hadj)
      · exact Or.inl rfl
      · exact Or.inr rfl
    have hsubw₁ : G.neighborFinset w₁ ∩ P ⊆ ({p, q, w₂} : Finset (Fin 20)) := by
      intro y hy
      rw [Finset.mem_inter, G.mem_neighborFinset] at hy
      obtain ⟨hadj, hyP⟩ := hy
      have hy5 : y ∈ ({h₂, p, q, w₁, w₂} : Finset (Fin 20)) := by rw [← hPeq5]; exact hyP
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy5 ⊢
      rcases hy5 with rfl | rfl | rfl | rfl | rfl
      · exact absurd hadj.symm (hh₂noP w₁ hw₁P)
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact absurd rfl (G.ne_of_adj hadj)
      · exact Or.inr (Or.inr rfl)
    have hsubw₂ : G.neighborFinset w₂ ∩ P ⊆ ({p, q, w₁} : Finset (Fin 20)) := by
      intro y hy
      rw [Finset.mem_inter, G.mem_neighborFinset] at hy
      obtain ⟨hadj, hyP⟩ := hy
      have hy5 : y ∈ ({h₂, p, q, w₁, w₂} : Finset (Fin 20)) := by rw [← hPeq5]; exact hyP
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy5 ⊢
      rcases hy5 with rfl | rfl | rfl | rfl | rfl
      · exact absurd hadj.symm (hh₂noP w₂ hw₂P)
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
      · exact absurd rfl (G.ne_of_adj hadj)
    have hcapp : (G.neighborFinset p ∩ P).card ≤ 2 :=
      le_trans (Finset.card_le_card hsubp) (pair_le w₁ w₂)
    have hcapq : (G.neighborFinset q ∩ P).card ≤ 2 :=
      le_trans (Finset.card_le_card hsubq) (pair_le w₁ w₂)
    have hcapw₁ : (G.neighborFinset w₁ ∩ P).card ≤ 3 :=
      le_trans (Finset.card_le_card hsubw₁) (triple_le p q w₂)
    have hcapw₂ : (G.neighborFinset w₂ ∩ P).card ≤ 3 :=
      le_trans (Finset.card_le_card hsubw₂) (triple_le p q w₁)
    have hsumPP : (∑ u ∈ P, (G.neighborFinset u ∩ P).card)
        = (G.neighborFinset h₂ ∩ P).card + (G.neighborFinset p ∩ P).card
          + (G.neighborFinset q ∩ P).card + (G.neighborFinset w₁ ∩ P).card
          + (G.neighborFinset w₂ ∩ P).card := by
      have h1 := Finset.sum_sdiff (f := fun u => (G.neighborFinset u ∩ P).card) h3sub
      rw [hdiffeq] at h1
      simp only [Finset.sum_pair hw12ne, Finset.sum_insert h₂notpq,
        Finset.sum_insert (Finset.notMem_singleton.mpr hpq), Finset.sum_singleton] at h1
      omega
    -- Tightness: all five available poor edges are present.
    have hpcard2 : (G.neighborFinset p ∩ P).card = 2 := by omega
    have hqcard2 : (G.neighborFinset q ∩ P).card = 2 := by omega
    have hw₁card3 : (G.neighborFinset w₁ ∩ P).card = 3 := by omega
    have hNpP : G.neighborFinset p ∩ P = ({w₁, w₂} : Finset (Fin 20)) :=
      Finset.eq_of_subset_of_card_le hsubp (by rw [hpcard2]; exact pair_le w₁ w₂)
    have hNqP : G.neighborFinset q ∩ P = ({w₁, w₂} : Finset (Fin 20)) :=
      Finset.eq_of_subset_of_card_le hsubq (by rw [hqcard2]; exact pair_le w₁ w₂)
    have hNw₁P : G.neighborFinset w₁ ∩ P = ({p, q, w₂} : Finset (Fin 20)) :=
      Finset.eq_of_subset_of_card_le hsubw₁ (by rw [hw₁card3]; exact triple_le p q w₂)
    have hpw₁ : G.Adj p w₁ := by
      have hm : w₁ ∈ G.neighborFinset p ∩ P := by
        rw [hNpP]; exact Finset.mem_insert_self w₁ {w₂}
      exact (G.mem_neighborFinset p w₁).mp (Finset.mem_inter.mp hm).1
    have hpw₂ : G.Adj p w₂ := by
      have hm : w₂ ∈ G.neighborFinset p ∩ P := by
        rw [hNpP]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self w₂)
      exact (G.mem_neighborFinset p w₂).mp (Finset.mem_inter.mp hm).1
    have hqw₁ : G.Adj q w₁ := by
      have hm : w₁ ∈ G.neighborFinset q ∩ P := by
        rw [hNqP]; exact Finset.mem_insert_self w₁ {w₂}
      exact (G.mem_neighborFinset q w₁).mp (Finset.mem_inter.mp hm).1
    have hqw₂ : G.Adj q w₂ := by
      have hm : w₂ ∈ G.neighborFinset q ∩ P := by
        rw [hNqP]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self w₂)
      exact (G.mem_neighborFinset q w₂).mp (Finset.mem_inter.mp hm).1
    have hw₁w₂ : G.Adj w₁ w₂ := by
      have hm : w₂ ∈ G.neighborFinset w₁ ∩ P := by
        rw [hNw₁P]
        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self w₂))
      exact (G.mem_neighborFinset w₁ w₂).mp (Finset.mem_inter.mp hm).1
    -- === Extract a `k = 0` twin and kill it. ===
    obtain ⟨t, ht⟩ := Finset.card_pos.mp (show
      0 < (Iso.filter (fun t => (G.neighborFinset t ∩ R).card = 0)).card by omega)
    rw [Finset.mem_filter] at ht
    obtain ⟨htIso, htk0⟩ := ht
    have htdeg : G.degree t = 3 := hisodeg3 t htIso
    have hts2 : 2 ≤ (G.neighborFinset t ∩ P).card := by
      have h := hks2 t htIso
      omega
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp (show
      1 < (G.neighborFinset t ∩ P).card by omega)
    have hNtHub : G.neighborFinset t ∩ Hub = G.neighborFinset t := by
      have h1 : (G.neighborFinset t).card = 3 := by
        rw [G.card_neighborFinset_eq_degree]; exact htdeg
      exact Finset.eq_of_subset_of_card_le Finset.inter_subset_left
        (by rw [h1, hiso3 t htIso])
    have htz' : ¬ G.Adj t z' := by
      intro hadj
      have hmem : z' ∈ G.neighborFinset t := (G.mem_neighborFinset t z').mpr hadj
      rw [← hNtHub, Finset.mem_inter] at hmem
      exact (Finset.mem_sdiff.mp hz'Z).2 (Finset.mem_union_left _ hmem.2)
    have hxadj : G.Adj t x := (G.mem_neighborFinset t x).mp (Finset.mem_inter.mp hx).1
    have hyadj : G.Adj t y := (G.mem_neighborFinset t y).mp (Finset.mem_inter.mp hy).1
    have hxP : x ∈ P := (Finset.mem_inter.mp hx).2
    have hyP : y ∈ P := (Finset.mem_inter.mp hy).2
    have hxdeg : G.degree x = 4 := hPdeg4 x hxP
    have hydeg : G.degree y = 4 := hPdeg4 y hyP
    have hNh₂Iso : G.neighborFinset h₂ ∩ Iso = ({c} : Finset (Fin 20)) := by
      obtain ⟨u, hu⟩ := Finset.card_eq_one.mp hpoor
      have hcmem : c ∈ G.neighborFinset h₂ ∩ Iso :=
        Finset.mem_inter.mpr ⟨(G.mem_neighborFinset h₂ c).mpr hh₂c, hcIso⟩
      rw [hu] at hcmem ⊢
      rw [Finset.mem_singleton] at hcmem
      rw [hcmem]
    have hxne_h₂ : x ≠ h₂ := by
      intro heq
      rw [heq] at hxadj
      have hmem : t ∈ G.neighborFinset h₂ ∩ Iso :=
        Finset.mem_inter.mpr ⟨(G.mem_neighborFinset h₂ t).mpr hxadj.symm, htIso⟩
      rw [hNh₂Iso, Finset.mem_singleton] at hmem
      rw [hmem] at htk0
      omega
    have hyne_h₂ : y ≠ h₂ := by
      intro heq
      rw [heq] at hyadj
      have hmem : t ∈ G.neighborFinset h₂ ∩ Iso :=
        Finset.mem_inter.mpr ⟨(G.mem_neighborFinset h₂ t).mpr hyadj.symm, htIso⟩
      rw [hNh₂Iso, Finset.mem_singleton] at hmem
      rw [hmem] at htk0
      omega
    have hx4 : x = p ∨ x = q ∨ x = w₁ ∨ x = w₂ := by
      have h5 : x ∈ ({h₂, p, q, w₁, w₂} : Finset (Fin 20)) := by rw [← hPeq5]; exact hxP
      simp only [Finset.mem_insert, Finset.mem_singleton] at h5
      rcases h5 with heq | h5
      · exact absurd heq hxne_h₂
      · exact h5
    have hy4 : y = p ∨ y = q ∨ y = w₁ ∨ y = w₂ := by
      have h5 : y ∈ ({h₂, p, q, w₁, w₂} : Finset (Fin 20)) := by rw [← hPeq5]; exact hyP
      simp only [Finset.mem_insert, Finset.mem_singleton] at h5
      rcases h5 with heq | h5
      · exact absurd heq hyne_h₂
      · exact h5
    have hkillC4 : G.Adj t p → G.Adj t q → False := by
      intro htp htq
      refine hC4 ⟨p, t, q, z', ?_, htp.symm, htq, hz'q.symm, hz'p, hnpq, htz', by omega⟩
      exact card_four_twenty p t q z'
        (fun h => Finset.disjoint_left.mp hdisj (h ▸ hp) htIso) hpq
        (fun h => (Finset.mem_sdiff.mp hz'Z).2 (Finset.mem_union_left _ (h ▸ hp)))
        (fun h => Finset.disjoint_left.mp hdisj hq (h ▸ htIso))
        (fun h => (Finset.mem_sdiff.mp hz'Z).2 (Finset.mem_union_right _ (h ▸ htIso)))
        (fun h => (Finset.mem_sdiff.mp hz'Z).2 (Finset.mem_union_left _ (h ▸ hq)))
    have hadjtab : ∀ u v : Fin 20, u = p ∨ u = q ∨ u = w₁ ∨ u = w₂ →
        v = p ∨ v = q ∨ v = w₁ ∨ v = w₂ → u ≠ v →
        G.Adj u v ∨ ((u = p ∧ v = q) ∨ (u = q ∧ v = p)) := by
      rintro u v (rfl | rfl | rfl | rfl) (rfl | rfl | rfl | rfl) hne
      · exact absurd rfl hne
      · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      · exact Or.inl hpw₁
      · exact Or.inl hpw₂
      · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
      · exact absurd rfl hne
      · exact Or.inl hqw₁
      · exact Or.inl hqw₂
      · exact Or.inl hpw₁.symm
      · exact Or.inl hqw₁.symm
      · exact absurd rfl hne
      · exact Or.inl hw₁w₂
      · exact Or.inl hpw₂.symm
      · exact Or.inl hqw₂.symm
      · exact Or.inl hw₁w₂.symm
      · exact absurd rfl hne
    rcases hadjtab x y hx4 hy4 hxy with hadj | hpqcase
    · exact tri x y t hxy
        (fun h => Finset.disjoint_left.mp hdisj (h ▸ hPHub hyP) htIso)
        (fun h => Finset.disjoint_left.mp hdisj (h ▸ hPHub hxP) htIso)
        hadj hyadj.symm hxadj.symm (by omega)
    · rcases hpqcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hkillC4 hxadj hyadj
      · exact hkillC4 hyadj hxadj

end N20

end ACMax
