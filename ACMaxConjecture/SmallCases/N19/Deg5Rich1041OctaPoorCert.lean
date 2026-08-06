import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N19.TwoHubCornerDeg5ZLeaf
import ACMaxConjecture.SmallCases.N19.TwoHubSelect
import ACMaxConjecture.SmallCases.N19.ZVertex
import ACMaxConjecture.SmallCases.N19.Deg5RichCap
import ACMaxConjecture.SmallCases.N19.Deg5SameZ
import ACMaxConjecture.SmallCases.N19.Deg5Rich1041Count
import ACMaxConjecture.SmallCases.N19.Deg5Rich1041Blocker
import ACMaxConjecture.SmallCases.N19.Deg5Rich1041K23
import ACMaxConjecture.SmallCases.N19.Deg5Rich1041OctaStruct
import ACMaxConjecture.SmallCases.N19.Deg5Rich1041SecondMend
import ACMaxConjecture.SmallCases.N19.Deg5Rich1041OctaPoorCounts
import ACMaxConjecture.SmallCases.N19.Deg5Rich1041ZPoorOneRich
import ACMaxConjecture.SmallCases.N19.Deg5Rich1041ZPoorBothPoor

/-! # The poor/Z certificate for the share-2 (10,7,41) octahedron (`n = 19`) -/
namespace ACMax
open scoped Classical

namespace N19

set_option maxHeartbeats 1000000 in
/-- **The poor/`Z`-layer kill.**  From the rigid `2+1+2` octahedron structure,
the deg-`5`-aware poor/`Z` handshake forces a good triangle (`hT`), `K₂,₃`
(`hK23`), or `C₄` (`hC4`).  Deg-`5` analog of the proven `(11,6,44)`
`octahedron_poor_counts`/`low_twin_poor` + the `n = 18` `octahedron_poor_cert`. -/
theorem octahedron_poor_cert_share2_1041_nineteen (G : SimpleGraph (Fin 19))
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
    (hxHub : x ∈ Hub) (hxd : G.degree x = 4)
    (hxiso3 : 3 ≤ (G.neighborFinset x ∩ Iso).card) (hxf : x ≠ f)
    (hnadj : ¬G.Adj x f)
    (hsh : ¬ 3 ≤ (G.neighborFinset x ∩ G.neighborFinset f ∩ Iso).card)
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
      a ∈ Hub ∧ G.degree a = 4 ∧ b ∈ Hub ∧ G.degree b = 4) :
    False := by
  classical
  -- Structure: `z` meets `{h₂, r_z}`; `h₂` meets hubs `{a, b}`; the rich set is
  -- `{g, r_t, r_z, a, b}`.  Only the pieces needed below are named.
  obtain ⟨_, _, r_z, a, b, _, _, _, _, _, _, _, hNz, _, _, ha2, hb2, _, _, hr_zHub, _,
    haHub, had, hbHub, hbd⟩ := id hstruct
  obtain ⟨_, _, hzdeg3⟩ :=
    zfacts_deg5_nineteen G Hub Iso hiso3 hdisj hsum17 hdeg3 hisodeg3 hleak z hzZ
  -- Node 1: the second `M`-endpoint `z'` and its two degree-`4` hubs `{p, q}`.
  obtain ⟨z', p, q, hz'Z, hz'ne, hzz', hz'deg3, hz'iso0, hNz'eq, hp, hq, hdp, hdq, hpq,
    hz'p, hz'q, hph₂, hpr_z, hqh₂, hqr_z, hnpq, hisopoor⟩ :=
    octahedron_second_mend_share2_1041_nineteen G Hub Iso hiso3 hdisj hsum17 hdeg3 hisodeg3
      hleak hdeg hdeg5 hHub hIso hdsum hT hC4 hno2hub f hfHub hfd hfiso5 z h₂ r_z hh₂ hr_zHub
      hzZ hNz
  have hzNotHub : z ∉ Hub := fun hc => (Finset.mem_sdiff.mp hzZ).2 (Finset.mem_union_left _ hc)
  have hz'NotHub : z' ∉ Hub :=
    fun hc => (Finset.mem_sdiff.mp hz'Z).2 (Finset.mem_union_left _ hc)
  have hz'NotIso : z' ∉ Iso :=
    fun hc => (Finset.mem_sdiff.mp hz'Z).2 (Finset.mem_union_right _ hc)
  by_cases hA : p = a ∨ p = b ∨ q = a ∨ q = b
  · -- **CASE A**: `p` or `q` is `a`/`b`.  Good `C₄`  `m–h₂–z–z'`.
    obtain ⟨m, hmHub, hmh₂adj, hz'm, hmd, hmrz, hmh₂ne⟩ :
        ∃ m : Fin 19, m ∈ Hub ∧ G.Adj m h₂ ∧ G.Adj z' m ∧ G.degree m = 4 ∧
          m ≠ r_z ∧ m ≠ h₂ := by
      rcases hA with h | h | h | h
      · exact ⟨a, haHub, ha2, h ▸ hz'p, had, h ▸ hpr_z, h ▸ hph₂⟩
      · exact ⟨b, hbHub, hb2, h ▸ hz'p, hbd, h ▸ hpr_z, h ▸ hph₂⟩
      · exact ⟨a, haHub, ha2, h ▸ hz'q, had, h ▸ hqr_z, h ▸ hqh₂⟩
      · exact ⟨b, hbHub, hb2, h ▸ hz'q, hbd, h ▸ hqr_z, h ▸ hqh₂⟩
    apply hC4
    refine ⟨m, h₂, z, z', ?_, hmh₂adj, hz2.symm, hzz', hz'm, ?_, ?_, ?_⟩
    · rw [Finset.card_eq_four]
      exact ⟨m, h₂, z, z', hmh₂ne, fun h => hzNotHub (h ▸ hmHub),
        fun h => hz'NotHub (h ▸ hmHub), fun h => hzNotHub (h ▸ hh₂),
        fun h => hz'NotHub (h ▸ hh₂), hz'ne.symm, rfl⟩
    · intro hmz
      have hmem : m ∈ G.neighborFinset z ∩ Hub :=
        Finset.mem_inter.mpr ⟨(G.mem_neighborFinset z m).mpr hmz.symm, hmHub⟩
      rw [hNz] at hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with h | h
      · exact hmh₂ne h
      · exact hmrz h
    · intro hh₂z'
      have hmem : h₂ ∈ G.neighborFinset z' ∩ Hub :=
        Finset.mem_inter.mpr ⟨(G.mem_neighborFinset z' h₂).mpr hh₂z'.symm, hh₂⟩
      rw [hNz'eq] at hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with h | h
      · exact hph₂ h.symm
      · exact hqh₂ h.symm
    · rw [hmd, hd₂, hzdeg3, hz'deg3]
  · by_cases htwin : 1 ≤ (G.neighborFinset p ∩ G.neighborFinset q ∩ Iso).card
    · -- **CASE A′**: `p, q` share an `Iso` twin `t`.  Good `C₄`  `p–z'–q–t`.
      obtain ⟨t, ht⟩ := Finset.card_pos.mp htwin
      rw [Finset.mem_inter, Finset.mem_inter] at ht
      obtain ⟨⟨htp, htq⟩, htIso⟩ := ht
      have hAdjpt : G.Adj p t := (G.mem_neighborFinset p t).mp htp
      have hAdjqt : G.Adj q t := (G.mem_neighborFinset q t).mp htq
      have hpt : p ≠ t := fun h => Finset.disjoint_left.mp hdisj hp (h ▸ htIso)
      have hqt : q ≠ t := fun h => Finset.disjoint_left.mp hdisj hq (h ▸ htIso)
      apply hC4
      refine ⟨p, z', q, t, ?_, hz'p.symm, hz'q, hAdjqt, hAdjpt.symm, hnpq, ?_, ?_⟩
      · rw [Finset.card_eq_four]
        exact ⟨p, z', q, t, fun h => hz'NotHub (h ▸ hp), hpq, hpt,
          Ne.symm (fun h => hz'NotHub (h ▸ hq)),
          Ne.symm (fun h => hz'NotIso (h ▸ htIso)), hqt, rfl⟩
      · intro hz't
        have hmem : t ∈ G.neighborFinset z' ∩ Iso :=
          Finset.mem_inter.mpr ⟨(G.mem_neighborFinset z' t).mpr hz't, htIso⟩
        rw [Finset.card_eq_zero.mp hz'iso0] at hmem
        simp at hmem
      · rw [hdp, hz'deg3, hdq, hisodeg3 t htIso]
    · -- **CASE C** (escalated): `p, q ∉ {a, b}` and `p, q` share no `Iso` twin —
      -- the `z'`-meets-poor residual, routed to the two proven regime lemmas.
      have hshare0 : (G.neighborFinset p ∩ G.neighborFinset q ∩ Iso).card = 0 := by omega
      rcases hisopoor with hpp | hqp
      · -- `p` poor.
        by_cases hqr : 2 ≤ (G.neighborFinset q ∩ Iso).card
        · -- `q` rich → one-rich with `p, q` swapped (rich hub must be first).
          have hNz'eqS : G.neighborFinset z' ∩ Hub = ({q, p} : Finset (Fin 19)) := by
            rw [hNz'eq]; exact Finset.pair_comm p q
          have hshare0S : (G.neighborFinset q ∩ G.neighborFinset p ∩ Iso).card = 0 := by
            rw [Finset.inter_comm (G.neighborFinset q) (G.neighborFinset p)]; exact hshare0
          exact octahedron_one_poor_force_share2_1041_nineteen G Hub Iso hiso3 hdisj hsum17
            hdeg3 hisodeg3 hleak hdeg hdeg5 hHub hIso hdsum hT hC4 hK23 hshare hno2hub g hg hgd
            hgiso h₂ z hh₂ hd₂ hzZ hz2 hgz hg2 hpoor hshared hblock f x hfHub hfd hfiso5 hxHub
            hxd hxiso3 hxf hnadj hsh hstruct z' q p hz'Z hzz' hz'deg3 hz'iso0 hNz'eqS hq hp hdq
            hdp hpq.symm hz'q hz'p (fun h => hnpq h.symm) hshare0S hqr hpp hqh₂ hqr_z hph₂ hpr_z
        · -- both poor.
          have hqpoor : (G.neighborFinset q ∩ Iso).card ≤ 1 := by omega
          exact octahedron_both_poor_force_share2_1041_nineteen G Hub Iso hiso3 hdisj hsum17
            hdeg3 hisodeg3 hleak hdeg hdeg5 hHub hIso hdsum hT hC4 hK23 hshare hno2hub g hg hgd
            hgiso h₂ z hh₂ hd₂ hzZ hz2 hgz hg2 hpoor hshared hblock f x hfHub hfd hfiso5 hxHub
            hxd hxiso3 hxf hnadj hsh hstruct z' p q hz'Z hzz' hz'deg3 hz'iso0 hNz'eq hp hq hdp
            hdq hpq hz'p hz'q hnpq hshare0 hpp hqpoor hph₂ hpr_z hqh₂ hqr_z
      · -- `q` poor.
        by_cases hpr : 2 ≤ (G.neighborFinset p ∩ Iso).card
        · -- `p` rich → one-rich directly.
          exact octahedron_one_poor_force_share2_1041_nineteen G Hub Iso hiso3 hdisj hsum17
            hdeg3 hisodeg3 hleak hdeg hdeg5 hHub hIso hdsum hT hC4 hK23 hshare hno2hub g hg hgd
            hgiso h₂ z hh₂ hd₂ hzZ hz2 hgz hg2 hpoor hshared hblock f x hfHub hfd hfiso5 hxHub
            hxd hxiso3 hxf hnadj hsh hstruct z' p q hz'Z hzz' hz'deg3 hz'iso0 hNz'eq hp hq hdp
            hdq hpq hz'p hz'q hnpq hshare0 hpr hqp hph₂ hpr_z hqh₂ hqr_z
        · -- both poor.
          have hppoor : (G.neighborFinset p ∩ Iso).card ≤ 1 := by omega
          exact octahedron_both_poor_force_share2_1041_nineteen G Hub Iso hiso3 hdisj hsum17
            hdeg3 hisodeg3 hleak hdeg hdeg5 hHub hIso hdsum hT hC4 hK23 hshare hno2hub g hg hgd
            hgiso h₂ z hh₂ hd₂ hzZ hz2 hgz hg2 hpoor hshared hblock f x hfHub hfd hfiso5 hxHub
            hxd hxiso3 hxf hnadj hsh hstruct z' p q hz'Z hzz' hz'deg3 hz'iso0 hNz'eq hp hq hdp
            hdq hpq hz'p hz'q hnpq hshare0 hppoor hqp hph₂ hpr_z hqh₂ hqr_z

end N19

end ACMax
