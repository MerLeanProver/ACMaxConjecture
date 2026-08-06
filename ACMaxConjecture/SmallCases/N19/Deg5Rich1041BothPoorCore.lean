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
import ACMaxConjecture.SmallCases.N19.Deg5Rich1041BothPoorProfileA
import ACMaxConjecture.SmallCases.N19.Deg5Rich1041BothPoorProfileB

/-! # CASE C both-poor: the config kill (`n = 19`)

The hard core of the both-poor regime.  Given the budget (4th poor hub `w`,
`deg z = 3`, `e_RR ≤ 1`), the profile split — `{2,2,2,3,3}` (rich rigidity
forces the single rich edge) vs `{2,2,2,2,4}` (`g` hub-isolated) — plus the
poor/`Z` layer forces a good triangle (`Σ ≤ 11`), `C₄` (`Σ ≤ 14`), `K₂,₃`
(`Σ ≤ 19`), or a two-hub config (`hno2hub`).  CONSTRUCTION-VERIFIED (0
survivors).  Template: `octahedron_poor_force_b_or_c_nineteen`. -/

namespace ACMax
open scoped Classical

namespace N19

set_option maxHeartbeats 1000000 in
/-- **CASE C both-poor config kill.** -/
theorem octahedron_both_poor_core_1041_nineteen (G : SimpleGraph (Fin 19))
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
      a ∈ Hub ∧ G.degree a = 4 ∧ b ∈ Hub ∧ G.degree b = 4)
    (z' p q : Fin 19)
    (hz'Z : z' ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 19)))
    (hzz' : G.Adj z z') (hz'deg3 : G.degree z' = 3)
    (hz'iso0 : (G.neighborFinset z' ∩ Iso).card = 0)
    (hNz'eq : G.neighborFinset z' ∩ Hub = ({p, q} : Finset (Fin 19)))
    (hp : p ∈ Hub) (hq : q ∈ Hub) (hdp : G.degree p = 4) (hdq : G.degree q = 4)
    (hpq : p ≠ q) (hz'p : G.Adj z' p) (hz'q : G.Adj z' q)
    (hnpq : ¬G.Adj p q)
    (hshare0 : (G.neighborFinset p ∩ G.neighborFinset q ∩ Iso).card = 0)
    (hppoor : (G.neighborFinset p ∩ Iso).card ≤ 1)
    (hqpoor : (G.neighborFinset q ∩ Iso).card ≤ 1)
    (hph₂ : p ≠ h₂) (hqh₂ : q ≠ h₂)
    (w : Fin 19) (hwHub : w ∈ Hub) (hwh₂ : w ≠ h₂) (hwp : w ≠ p) (hwq : w ≠ q)
    (hwf : w ≠ f) (hwd : G.degree w = 4) (hwiso : (G.neighborFinset w ∩ Iso).card = 1)
    (hpworqw : G.Adj p w ∨ G.Adj q w) (hzdeg : G.degree z = 3)
    (heRR : (∑ r ∈ Hub.filter (fun h => G.degree h = 4 ∧ 2 ≤ (G.neighborFinset h ∩ Iso).card),
      (G.neighborFinset r ∩ Hub.filter
        (fun h => G.degree h = 4 ∧ 2 ≤ (G.neighborFinset h ∩ Iso).card)).card) ≤ 2) :
    False := by
  classical
  have hgle : (G.neighborFinset g ∩ Iso).card ≤ 4 := by
    calc (G.neighborFinset g ∩ Iso).card ≤ (G.neighborFinset g).card :=
          Finset.card_le_card Finset.inter_subset_left
      _ = 4 := by rw [G.card_neighborFinset_eq_degree]; exact hgd
  rcases (show (G.neighborFinset g ∩ Iso).card = 3 ∨ (G.neighborFinset g ∩ Iso).card = 4 by
      omega) with hg3 | hg4
  · exact octahedron_both_poor_profile_a_1041_nineteen G Hub Iso hiso3 hdisj hsum17 hdeg3 hisodeg3 hleak hdeg hdeg5 hHub hIso hdsum hT hC4 hK23 hshare hno2hub g hg hgd hgiso h₂ z hh₂ hd₂ hzZ hz2 hgz hg2 hpoor hshared hblock f x hfHub hfd hfiso5 hxHub hxd hxiso3 hxf hnadj hsh hstruct z' p q hz'Z hzz' hz'deg3 hz'iso0 hNz'eq hp hq hdp hdq hpq hz'p hz'q hnpq hshare0 hppoor hqpoor hph₂ hqh₂ w hwHub hwh₂ hwp hwq hwf hwd hwiso hpworqw hzdeg heRR hg3
  · exact octahedron_both_poor_profile_b_1041_nineteen G Hub Iso hiso3 hdisj hsum17 hdeg3 hisodeg3 hleak hdeg hdeg5 hHub hIso hdsum hT hC4 hK23 hshare hno2hub g hg hgd hgiso h₂ z hh₂ hd₂ hzZ hz2 hgz hg2 hpoor hshared hblock f x hfHub hfd hfiso5 hxHub hxd hxiso3 hxf hnadj hsh hstruct z' p q hz'Z hzz' hz'deg3 hz'iso0 hNz'eq hp hq hdp hdq hpq hz'p hz'q hnpq hshare0 hppoor hqpoor hph₂ hqh₂ w hwHub hwh₂ hwp hwq hwf hwd hwiso hpworqw hzdeg heRR hg4

end N19

end ACMax
