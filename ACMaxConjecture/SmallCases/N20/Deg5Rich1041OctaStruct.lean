import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N20.TwoHubCornerDeg5ZLeaf
import ACMaxConjecture.SmallCases.N20.TwoHubSelect
import ACMaxConjecture.SmallCases.N20.ZVertex
import ACMaxConjecture.SmallCases.N20.Deg5RichCap
import ACMaxConjecture.SmallCases.N20.Deg5SameZ
import ACMaxConjecture.SmallCases.N20.Deg5Rich1041Blocker
import ACMaxConjecture.SmallCases.N20.Deg5Rich1041K23

/-! # The rigid octahedron structure for the share-2 (11,7,45) corner (`n = 20`) -/
namespace ACMax
open scoped Classical

namespace N20

set_option maxHeartbeats 1000000 in
/-- **Force the rigid `2+1+2` octahedron partition.**  In the `|R| ≥ 5` world of the
`(11, 7, 45)` rich-count dichotomy (`hR5ge`, supplied by the caller from the left
disjunct of `rich_count_1041_twenty`; the `|R| = 4` world is routed to the anchor-
saturation node), the blocked rich set is exactly `{g, r_t, r_z, a, b}` with `c` the
unique twin of `h₂` (`N c ∩ Hub = {h₂, g, r_t}`, `N z ∩ Hub = {h₂, r_z}`,
`N h₂ ∩ Hub = {a, b}`). -/
theorem octahedron_struct_share2_1041_twenty (G : SimpleGraph (Fin 20))
    (Hub Iso : Finset (Fin 20))
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdisj : Disjoint Hub Iso) (hsum18 : Hub.card + Iso.card = 18)
    (hdeg3 : ∀ v : Fin 20, 3 ≤ G.degree v) (hisodeg3 : ∀ t ∈ Iso, G.degree t = 3)
    (hleak : ∑ h ∈ Hub, (G.neighborFinset h ∩ (Finset.univ \ (Hub ∪ Iso))).card ≤ 4)
    (hdeg : ∀ h ∈ Hub, 4 ≤ G.degree h) (hdeg5 : ∀ h ∈ Hub, G.degree h ≤ 5)
    (hHub : Hub.card = 11) (hIso : Iso.card = 7) (hdsum : ∑ w ∈ Hub, G.degree w = 45)
    (hT : ¬∃ x y z : Fin 20, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 11)
    (hC4 : ¬∃ a b c d : Fin 20, ({a, b, c, d} : Finset (Fin 20)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (hK23 : ¬∃ a b c d e : Fin 20, ({a, b, c, d, e} : Finset (Fin 20)).card = 5 ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
      G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 19)
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hno2hub : ¬∃ h₁ h₂ : Fin 20, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card)
    (g : Fin 20) (hg : g ∈ Hub) (hgd : G.degree g = 4)
    (hgiso : 3 ≤ (G.neighborFinset g ∩ Iso).card)
    (h₂ z : Fin 20) (hh₂ : h₂ ∈ Hub) (hd₂ : G.degree h₂ = 4)
    (hzZ : z ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 20)))
    (hz2 : G.Adj z h₂) (hgz : ¬G.Adj g z) (hg2 : ¬G.Adj g h₂)
    (hpoor : (G.neighborFinset h₂ ∩ Iso).card = 1)
    (hshared : (G.neighborFinset g ∩ G.neighborFinset h₂ ∩ Iso).card = 1)
    (hblock : ∀ x : Fin 20, x ∈ Hub → G.degree x = 4 →
      2 ≤ (G.neighborFinset x ∩ Iso).card →
      G.neighborFinset x ∩ G.neighborFinset h₂ ∩ Iso ≠ ∅ ∨ G.Adj x h₂ ∨ G.Adj x z)
    (hR5ge : 5 ≤ (Hub.filter
      (fun h => G.degree h = 4 ∧ 2 ≤ (G.neighborFinset h ∩ Iso).card)).card) :
    ∃ c r_t r_z a b : Fin 20,
      Hub.filter (fun h => G.degree h = 4 ∧ 2 ≤ (G.neighborFinset h ∩ Iso).card)
        = ({g, r_t, r_z, a, b} : Finset (Fin 20)) ∧
      ({g, r_t, r_z, a, b} : Finset (Fin 20)).card = 5 ∧
      c ∈ Iso ∧ G.Adj g c ∧ G.Adj h₂ c ∧ G.Adj r_t c ∧
      G.neighborFinset c ∩ Hub = ({h₂, g, r_t} : Finset (Fin 20)) ∧
      G.neighborFinset z ∩ Hub = ({h₂, r_z} : Finset (Fin 20)) ∧
      G.neighborFinset h₂ ∩ Hub = ({a, b} : Finset (Fin 20)) ∧
      G.Adj r_z z ∧ G.Adj a h₂ ∧ G.Adj b h₂ ∧
      r_t ∈ Hub ∧ G.degree r_t = 4 ∧ r_z ∈ Hub ∧ G.degree r_z = 4 ∧
      a ∈ Hub ∧ G.degree a = 4 ∧ b ∈ Hub ∧ G.degree b = 4 := by
  classical
  -- === `|R| = 5`. ===
  set R : Finset (Fin 20) :=
    Hub.filter (fun h => G.degree h = 4 ∧ 2 ≤ (G.neighborFinset h ∩ Iso).card) with hRdef
  have hRge : 5 ≤ R.card := hR5ge
  have hRle : 5 ≥ R.card :=
    rich_le_five_blocked_1041_twenty G Hub Iso hiso3 hdisj hsum18 hdeg3 hisodeg3 hleak hdeg
      hdeg5 hHub hIso hdsum hT hC4 hK23 hshare hno2hub g hg hgd hgiso h₂ z hh₂ hd₂ hzZ hz2 hgz
      hg2 hpoor hshared hblock
  have hRcard : R.card = 5 := by omega
  -- === Extract the unique twin `c` of `h₂`; `Adj g c`. ===
  obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hpoor
  have hcmem : c ∈ G.neighborFinset h₂ ∩ Iso := by rw [hc]; exact Finset.mem_singleton_self c
  have hcIso : c ∈ Iso := (Finset.mem_inter.mp hcmem).2
  have hcNh₂ : c ∈ G.neighborFinset h₂ := (Finset.mem_inter.mp hcmem).1
  have hh₂c : G.Adj h₂ c := (G.mem_neighborFinset h₂ c).mp hcNh₂
  have hcHub3 : (G.neighborFinset c ∩ Hub).card = 3 := hiso3 c hcIso
  have hh₂inNc : h₂ ∈ G.neighborFinset c ∩ Hub :=
    Finset.mem_inter.mpr ⟨(G.mem_neighborFinset c h₂).mpr hh₂c.symm, hh₂⟩
  have hgh₂ : g ≠ h₂ := by rintro rfl; omega
  have hshared_eq : G.neighborFinset g ∩ G.neighborFinset h₂ ∩ Iso = {c} := by
    have hsub : G.neighborFinset g ∩ G.neighborFinset h₂ ∩ Iso ⊆ ({c} : Finset (Fin 20)) := by
      intro x hx
      rw [Finset.mem_inter, Finset.mem_inter] at hx
      obtain ⟨⟨_, hxh₂⟩, hxIso⟩ := hx
      have hm : x ∈ G.neighborFinset h₂ ∩ Iso := Finset.mem_inter.mpr ⟨hxh₂, hxIso⟩
      rwa [hc] at hm
    rcases Finset.subset_singleton_iff.mp hsub with h0 | h1
    · rw [h0] at hshared; simp at hshared
    · exact h1
  have hcNg : c ∈ G.neighborFinset g := by
    have hm : c ∈ G.neighborFinset g ∩ G.neighborFinset h₂ ∩ Iso := by
      rw [hshared_eq]; exact Finset.mem_singleton_self c
    exact (Finset.mem_inter.mp (Finset.mem_inter.mp hm).1).1
  have hgc : G.Adj g c := (G.mem_neighborFinset g c).mp hcNg
  have hginNc : g ∈ G.neighborFinset c ∩ Hub :=
    Finset.mem_inter.mpr ⟨(G.mem_neighborFinset c g).mpr hgc.symm, hg⟩
  -- === `z` meets exactly two hubs (`h₂` and one other). ===
  have hzf := zfacts_deg5_twenty G Hub Iso hiso3 hdisj hsum18 hdeg3 hisodeg3 hleak
  obtain ⟨hzIso0, hzHub2, hzdeg3⟩ := hzf z hzZ
  have hh₂inNz : h₂ ∈ G.neighborFinset z ∩ Hub :=
    Finset.mem_inter.mpr ⟨(G.mem_neighborFinset z h₂).mpr hz2, hh₂⟩
  -- === `h₂` meets at most two hubs. ===
  have hh₂Hub2le : (G.neighborFinset h₂ ∩ Hub).card ≤ 2 := by
    have hsplit := nbr_split_three_twenty G Hub Iso hdisj h₂
    rw [hd₂, hpoor] at hsplit
    have hzInZ : z ∈ G.neighborFinset h₂ ∩ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 20)) :=
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset h₂ z).mpr hz2.symm, hzZ⟩
    have hzge : 1 ≤ (G.neighborFinset h₂ ∩ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 20))).card :=
      Finset.card_pos.mpr ⟨z, hzInZ⟩
    omega
  -- === `|N c ∩ Hub ∪ N z ∩ Hub| ≤ 4`. ===
  have hAC : ((G.neighborFinset c ∩ Hub) ∪ (G.neighborFinset z ∩ Hub)).card ≤ 4 := by
    have hkey := Finset.card_union_add_card_inter (G.neighborFinset c ∩ Hub)
      (G.neighborFinset z ∩ Hub)
    have hinter1 : 1 ≤ ((G.neighborFinset c ∩ Hub) ∩ (G.neighborFinset z ∩ Hub)).card :=
      Finset.card_pos.mpr ⟨h₂, Finset.mem_inter.mpr ⟨hh₂inNc, hh₂inNz⟩⟩
    rw [hcHub3, hzHub2] at hkey
    omega
  -- === The blocker union `U`, and the cover `R ⊆ U ∖ {h₂}`. ===
  set U : Finset (Fin 20) :=
    ((G.neighborFinset c ∩ Hub) ∪ (G.neighborFinset z ∩ Hub)) ∪ (G.neighborFinset h₂ ∩ Hub)
    with hUdef
  have hRsub : R ⊆ U.erase h₂ := by
    intro x hx
    rw [hRdef, Finset.mem_filter] at hx
    obtain ⟨hxHub, hxdeg, hxiso⟩ := hx
    have hxne : x ≠ h₂ := by rintro rfl; omega
    rw [Finset.mem_erase]
    refine ⟨hxne, ?_⟩
    rw [hUdef]
    rcases hblock x hxHub hxdeg hxiso with hcase1 | hcase2 | hcase3
    · rw [← Finset.nonempty_iff_ne_empty] at hcase1
      obtain ⟨t, ht⟩ := hcase1
      rw [Finset.mem_inter, Finset.mem_inter] at ht
      obtain ⟨⟨htx, hth₂⟩, htIso⟩ := ht
      have htmem : t ∈ G.neighborFinset h₂ ∩ Iso := Finset.mem_inter.mpr ⟨hth₂, htIso⟩
      rw [hc, Finset.mem_singleton] at htmem
      rw [htmem] at htx
      have hxNc : x ∈ G.neighborFinset c :=
        (G.mem_neighborFinset c x).mpr ((G.mem_neighborFinset x c).mp htx).symm
      exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_inter.mpr ⟨hxNc, hxHub⟩))
    · have hxNh₂ : x ∈ G.neighborFinset h₂ := (G.mem_neighborFinset h₂ x).mpr hcase2.symm
      exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hxNh₂, hxHub⟩)
    · have hxNz : x ∈ G.neighborFinset z := (G.mem_neighborFinset z x).mpr hcase3.symm
      exact Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_inter.mpr ⟨hxNz, hxHub⟩))
  have hh₂U : h₂ ∈ U := by
    rw [hUdef]; exact Finset.mem_union_left _ (Finset.mem_union_left _ hh₂inNc)
  have h5le : 5 ≤ (U.erase h₂).card := by
    have := Finset.card_le_card hRsub; omega
  -- === `|U| = 6`, forcing the rigid partition. ===
  have hUcard6 : U.card = 6 := by
    have hunion := Finset.card_union_le
      ((G.neighborFinset c ∩ Hub) ∪ (G.neighborFinset z ∩ Hub)) (G.neighborFinset h₂ ∩ Hub)
    have hUeraseC : (U.erase h₂).card = U.card - 1 := Finset.card_erase_of_mem hh₂U
    rw [← hUdef] at hunion
    omega
  have hABkey := Finset.card_union_add_card_inter
    ((G.neighborFinset c ∩ Hub) ∪ (G.neighborFinset z ∩ Hub)) (G.neighborFinset h₂ ∩ Hub)
  rw [← hUdef] at hABkey
  have hh₂Hub2 : (G.neighborFinset h₂ ∩ Hub).card = 2 := by omega
  have hABinter0 : (((G.neighborFinset c ∩ Hub) ∪ (G.neighborFinset z ∩ Hub))
      ∩ (G.neighborFinset h₂ ∩ Hub)).card = 0 := by omega
  have hABdisj := Finset.card_eq_zero.mp hABinter0
  have hAcard4 : ((G.neighborFinset c ∩ Hub) ∪ (G.neighborFinset z ∩ Hub)).card = 4 := by omega
  have hCZkey := Finset.card_union_add_card_inter (G.neighborFinset c ∩ Hub)
    (G.neighborFinset z ∩ Hub)
  rw [hcHub3, hzHub2, hAcard4] at hCZkey
  have hCZinter1 : ((G.neighborFinset c ∩ Hub) ∩ (G.neighborFinset z ∩ Hub)).card = 1 := by omega
  have hCZeq : (G.neighborFinset c ∩ Hub) ∩ (G.neighborFinset z ∩ Hub) = {h₂} := by
    obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hCZinter1
    have hh₂w : h₂ = w := by
      have hmem : h₂ ∈ ({w} : Finset (Fin 20)) :=
        hw ▸ Finset.mem_inter.mpr ⟨hh₂inNc, hh₂inNz⟩
      rwa [Finset.mem_singleton] at hmem
    rw [hw, hh₂w]
  -- === Extract `r_t` (the third hub-neighbour of `c`). ===
  have hgSc' : g ∈ (G.neighborFinset c ∩ Hub).erase h₂ := Finset.mem_erase.mpr ⟨hgh₂, hginNc⟩
  have hSc'card : ((G.neighborFinset c ∩ Hub).erase h₂).card = 2 := by
    rw [Finset.card_erase_of_mem hh₂inNc, hcHub3]
  have hSc''card : (((G.neighborFinset c ∩ Hub).erase h₂).erase g).card = 1 := by
    rw [Finset.card_erase_of_mem hgSc', hSc'card]
  obtain ⟨r_t, hr_teq⟩ := Finset.card_eq_one.mp hSc''card
  have hr_tmem : r_t ∈ ((G.neighborFinset c ∩ Hub).erase h₂).erase g := by
    rw [hr_teq]; exact Finset.mem_singleton_self r_t
  have hr_tne_g : r_t ≠ g := (Finset.mem_erase.mp hr_tmem).1
  have hr_tSc' : r_t ∈ (G.neighborFinset c ∩ Hub).erase h₂ := (Finset.mem_erase.mp hr_tmem).2
  have hr_tne_h₂ : r_t ≠ h₂ := (Finset.mem_erase.mp hr_tSc').1
  have hr_tSc : r_t ∈ G.neighborFinset c ∩ Hub := (Finset.mem_erase.mp hr_tSc').2
  have hr_tHub : r_t ∈ Hub := (Finset.mem_inter.mp hr_tSc).2
  have hr_tNc : r_t ∈ G.neighborFinset c := (Finset.mem_inter.mp hr_tSc).1
  have hr_tc : G.Adj r_t c := ((G.mem_neighborFinset c r_t).mp hr_tNc).symm
  -- === Extract `r_z` (the second hub-neighbour of `z`). ===
  have hr_zcard : ((G.neighborFinset z ∩ Hub).erase h₂).card = 1 := by
    rw [Finset.card_erase_of_mem hh₂inNz, hzHub2]
  obtain ⟨r_z, hr_zeq⟩ := Finset.card_eq_one.mp hr_zcard
  have hr_zmem : r_z ∈ (G.neighborFinset z ∩ Hub).erase h₂ := by
    rw [hr_zeq]; exact Finset.mem_singleton_self r_z
  have hr_zne_h₂ : r_z ≠ h₂ := (Finset.mem_erase.mp hr_zmem).1
  have hr_zSz : r_z ∈ G.neighborFinset z ∩ Hub := (Finset.mem_erase.mp hr_zmem).2
  have hr_zHub : r_z ∈ Hub := (Finset.mem_inter.mp hr_zSz).2
  have hr_zNz : r_z ∈ G.neighborFinset z := (Finset.mem_inter.mp hr_zSz).1
  have hr_zz : G.Adj r_z z := ((G.mem_neighborFinset z r_z).mp hr_zNz).symm
  -- === Extract `a, b` (the two hub-neighbours of `h₂`). ===
  obtain ⟨a, b, hab, hNh₂eq⟩ := Finset.card_eq_two.mp hh₂Hub2
  have haNh₂Hub : a ∈ G.neighborFinset h₂ ∩ Hub := by
    rw [hNh₂eq]; exact Finset.mem_insert_self a {b}
  have hbNh₂Hub : b ∈ G.neighborFinset h₂ ∩ Hub := by
    rw [hNh₂eq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self b)
  have haNh₂ : a ∈ G.neighborFinset h₂ := (Finset.mem_inter.mp haNh₂Hub).1
  have haHub : a ∈ Hub := (Finset.mem_inter.mp haNh₂Hub).2
  have hbNh₂ : b ∈ G.neighborFinset h₂ := (Finset.mem_inter.mp hbNh₂Hub).1
  have hbHub : b ∈ Hub := (Finset.mem_inter.mp hbNh₂Hub).2
  have ha2 : G.Adj a h₂ := ((G.mem_neighborFinset h₂ a).mp haNh₂).symm
  have hb2 : G.Adj b h₂ := ((G.mem_neighborFinset h₂ b).mp hbNh₂).symm
  have ha_ne_h₂ : a ≠ h₂ := G.ne_of_adj ha2
  have hb_ne_h₂ : b ≠ h₂ := G.ne_of_adj hb2
  -- === Pairwise distinctness of `g, r_t, r_z, a, b`. ===
  have hg_ne_rt : g ≠ r_t := Ne.symm hr_tne_g
  have hg_ne_rz : g ≠ r_z := by
    intro h
    have hgNz : g ∈ G.neighborFinset z := by rw [h]; exact hr_zNz
    exact hgz ((G.mem_neighborFinset z g).mp hgNz).symm
  have hg_ne_a : g ≠ a := by
    intro h
    have hgNh₂ : g ∈ G.neighborFinset h₂ := by rw [h]; exact haNh₂
    exact hg2 ((G.mem_neighborFinset h₂ g).mp hgNh₂).symm
  have hg_ne_b : g ≠ b := by
    intro h
    have hgNh₂ : g ∈ G.neighborFinset h₂ := by rw [h]; exact hbNh₂
    exact hg2 ((G.mem_neighborFinset h₂ g).mp hgNh₂).symm
  have hrt_ne_rz : r_t ≠ r_z := by
    intro h
    have hmem : r_z ∈ (G.neighborFinset c ∩ Hub) ∩ (G.neighborFinset z ∩ Hub) :=
      Finset.mem_inter.mpr ⟨h ▸ hr_tSc, hr_zSz⟩
    rw [hCZeq, Finset.mem_singleton] at hmem
    exact hr_zne_h₂ hmem
  have hrt_ne_a : r_t ≠ a := by
    intro h
    have hrtA : r_t ∈ (G.neighborFinset c ∩ Hub) ∪ (G.neighborFinset z ∩ Hub) :=
      Finset.mem_union_left _ hr_tSc
    have hmem : a ∈ ((G.neighborFinset c ∩ Hub) ∪ (G.neighborFinset z ∩ Hub))
        ∩ (G.neighborFinset h₂ ∩ Hub) := Finset.mem_inter.mpr ⟨h ▸ hrtA, haNh₂Hub⟩
    rw [hABdisj] at hmem; simp at hmem
  have hrt_ne_b : r_t ≠ b := by
    intro h
    have hrtA : r_t ∈ (G.neighborFinset c ∩ Hub) ∪ (G.neighborFinset z ∩ Hub) :=
      Finset.mem_union_left _ hr_tSc
    have hmem : b ∈ ((G.neighborFinset c ∩ Hub) ∪ (G.neighborFinset z ∩ Hub))
        ∩ (G.neighborFinset h₂ ∩ Hub) := Finset.mem_inter.mpr ⟨h ▸ hrtA, hbNh₂Hub⟩
    rw [hABdisj] at hmem; simp at hmem
  have hrz_ne_a : r_z ≠ a := by
    intro h
    have hrzA : r_z ∈ (G.neighborFinset c ∩ Hub) ∪ (G.neighborFinset z ∩ Hub) :=
      Finset.mem_union_right _ hr_zSz
    have hmem : a ∈ ((G.neighborFinset c ∩ Hub) ∪ (G.neighborFinset z ∩ Hub))
        ∩ (G.neighborFinset h₂ ∩ Hub) := Finset.mem_inter.mpr ⟨h ▸ hrzA, haNh₂Hub⟩
    rw [hABdisj] at hmem; simp at hmem
  have hrz_ne_b : r_z ≠ b := by
    intro h
    have hrzA : r_z ∈ (G.neighborFinset c ∩ Hub) ∪ (G.neighborFinset z ∩ Hub) :=
      Finset.mem_union_right _ hr_zSz
    have hmem : b ∈ ((G.neighborFinset c ∩ Hub) ∪ (G.neighborFinset z ∩ Hub))
        ∩ (G.neighborFinset h₂ ∩ Hub) := Finset.mem_inter.mpr ⟨h ▸ hrzA, hbNh₂Hub⟩
    rw [hABdisj] at hmem; simp at hmem
  have h5card : ({g, r_t, r_z, a, b} : Finset (Fin 20)).card = 5 :=
    card_five_twenty g r_t r_z a b hg_ne_rt hg_ne_rz hg_ne_a hg_ne_b hrt_ne_rz hrt_ne_a
      hrt_ne_b hrz_ne_a hrz_ne_b hab
  -- === The three neighbourhood set equalities. ===
  have hcard3set : ({h₂, g, r_t} : Finset (Fin 20)).card = 3 :=
    Finset.card_eq_three.mpr ⟨h₂, g, r_t, hgh₂.symm, Ne.symm hr_tne_h₂, Ne.symm hr_tne_g, rfl⟩
  have hsub3 : ({h₂, g, r_t} : Finset (Fin 20)) ⊆ G.neighborFinset c ∩ Hub := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact hh₂inNc
    · exact hginNc
    · exact hr_tSc
  have hNceq : G.neighborFinset c ∩ Hub = ({h₂, g, r_t} : Finset (Fin 20)) :=
    (Finset.eq_of_subset_of_card_le hsub3 (le_of_eq (hcHub3.trans hcard3set.symm))).symm
  have hcard2z : ({h₂, r_z} : Finset (Fin 20)).card = 2 :=
    Finset.card_eq_two.mpr ⟨h₂, r_z, Ne.symm hr_zne_h₂, rfl⟩
  have hsub2z : ({h₂, r_z} : Finset (Fin 20)) ⊆ G.neighborFinset z ∩ Hub := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hh₂inNz
    · exact hr_zSz
  have hNzeq : G.neighborFinset z ∩ Hub = ({h₂, r_z} : Finset (Fin 20)) :=
    (Finset.eq_of_subset_of_card_le hsub2z (le_of_eq (hzHub2.trans hcard2z.symm))).symm
  -- === `R = {g, r_t, r_z, a, b}` via the cover `R ⊆ U ∖ {h₂}`. ===
  have hRsub5 : R ⊆ ({g, r_t, r_z, a, b} : Finset (Fin 20)) := by
    intro x hx
    have hxU := hRsub hx
    rw [Finset.mem_erase] at hxU
    obtain ⟨hxne, hxU'⟩ := hxU
    rw [hUdef, Finset.mem_union, Finset.mem_union] at hxU'
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases hxU' with (hxc | hxz) | hxh
    · rw [hNceq, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hxc
      rcases hxc with rfl | rfl | rfl
      · exact absurd rfl hxne
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
    · rw [hNzeq, Finset.mem_insert, Finset.mem_singleton] at hxz
      rcases hxz with rfl | rfl
      · exact absurd rfl hxne
      · exact Or.inr (Or.inr (Or.inl rfl))
    · rw [hNh₂eq, Finset.mem_insert, Finset.mem_singleton] at hxh
      rcases hxh with rfl | rfl
      · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
  have hR5 : R = ({g, r_t, r_z, a, b} : Finset (Fin 20)) :=
    Finset.eq_of_subset_of_card_le hRsub5 (le_of_eq (h5card.trans hRcard.symm))
  -- === The four residual hubs are degree `4` (they lie in `R`). ===
  have hr_tR : r_t ∈ R := by rw [hR5]; simp
  have hr_td4 : G.degree r_t = 4 := by rw [hRdef, Finset.mem_filter] at hr_tR; exact hr_tR.2.1
  have hr_zR : r_z ∈ R := by rw [hR5]; simp
  have hr_zd4 : G.degree r_z = 4 := by rw [hRdef, Finset.mem_filter] at hr_zR; exact hr_zR.2.1
  have haR : a ∈ R := by rw [hR5]; simp
  have had4 : G.degree a = 4 := by rw [hRdef, Finset.mem_filter] at haR; exact haR.2.1
  have hbR : b ∈ R := by rw [hR5]; simp
  have hbd4 : G.degree b = 4 := by rw [hRdef, Finset.mem_filter] at hbR; exact hbR.2.1
  exact ⟨c, r_t, r_z, a, b, hR5, h5card, hcIso, hgc, hh₂c, hr_tc, hNceq, hNzeq, hNh₂eq, hr_zz,
    ha2, hb2, hr_tHub, hr_td4, hr_zHub, hr_zd4, haHub, had4, hbHub, hbd4⟩

end N20

end ACMax
