import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N20.TwoHubCornerDeg5ZLeaf
import ACMaxConjecture.SmallCases.N20.R5ResidHelpers

/-! # The same-`z` hub pair (`n = 20`, deg-5 corner): non-adjacent, share-free, one is iso-poor -/
namespace ACMax
open scoped Classical

namespace N20

set_option maxHeartbeats 1000000 in
/-- Two deg-4 hubs on one `z`: non-adjacent (`hT`), twin-share `∅` (`hC4`), and one has
`isoDeg ≤ 1` (`hno2hub`). -/
theorem same_z_pair_deg5_twenty (G : SimpleGraph (Fin 20)) (Hub Iso : Finset (Fin 20))
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdisj : Disjoint Hub Iso) (hsum18 : Hub.card + Iso.card = 18)
    (hdeg3 : ∀ v : Fin 20, 3 ≤ G.degree v) (hisodeg3 : ∀ t ∈ Iso, G.degree t = 3)
    (hleak : ∑ h ∈ Hub, (G.neighborFinset h ∩ (Finset.univ \ (Hub ∪ Iso))).card ≤ 4)
    (hT : ¬∃ x y z : Fin 20, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 11)
    (hC4 : ¬∃ a b c d : Fin 20, ({a, b, c, d} : Finset (Fin 20)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (hno2hub : ¬∃ h₁ h₂ : Fin 20, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card)
    (z p q : Fin 20) (hz : z ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 20)))
    (hp : p ∈ Hub) (hq : q ∈ Hub) (hdp : G.degree p = 4) (hdq : G.degree q = 4)
    (hpq : p ≠ q) (hzp : G.Adj z p) (hzq : G.Adj z q) :
    ¬G.Adj p q ∧ G.neighborFinset p ∩ G.neighborFinset q ∩ Iso = ∅ ∧
      ((G.neighborFinset p ∩ Iso).card ≤ 1 ∨ (G.neighborFinset q ∩ Iso).card ≤ 1) := by
  classical
  obtain ⟨hziso0, _, hzdeg3⟩ :=
    zfacts_deg5_twenty G Hub Iso hiso3 hdisj hsum18 hdeg3 hisodeg3 hleak z hz
  have hzUnion : z ∉ Hub ∪ Iso := (Finset.mem_sdiff.mp hz).2
  have hznotHub : z ∉ Hub := fun hc => hzUnion (Finset.mem_union_left _ hc)
  have hznotIso : z ∉ Iso := fun hc => hzUnion (Finset.mem_union_right _ hc)
  have hzp_ne : z ≠ p := fun h => hznotHub (h ▸ hp)
  have hzq_ne : z ≠ q := fun h => hznotHub (h ▸ hq)
  have hzisoEmpty : G.neighborFinset z ∩ Iso = ∅ := Finset.card_eq_zero.mp hziso0
  -- PART 1: `p` and `q` are non-adjacent (the triangle `z–p–q` is too light for `hT`).
  have hnpq : ¬G.Adj p q := by
    intro hpq_adj
    exact hT ⟨z, p, q, hzp_ne, hpq, hzq_ne, hzp, hpq_adj, hzq, by omega⟩
  -- PART 2: `p` and `q` share no twin (the `C₄` `z–p–t–q` is too light for `hC4`).
  have hshare : G.neighborFinset p ∩ G.neighborFinset q ∩ Iso = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro t ht
    rw [Finset.mem_inter, Finset.mem_inter] at ht
    obtain ⟨⟨htp, htq⟩, htIso⟩ := ht
    have hApt : G.Adj p t := (G.mem_neighborFinset _ _).mp htp
    have hAqt : G.Adj q t := (G.mem_neighborFinset _ _).mp htq
    have hnzt : ¬G.Adj z t := by
      intro hzt_adj
      have hmem : t ∈ G.neighborFinset z ∩ Iso :=
        Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hzt_adj, htIso⟩
      rw [hzisoEmpty] at hmem
      exact absurd hmem (Finset.notMem_empty t)
    have htp_ne : t ≠ p := by rintro rfl; exact Finset.disjoint_left.mp hdisj hp htIso
    have htq_ne : t ≠ q := by rintro rfl; exact Finset.disjoint_left.mp hdisj hq htIso
    have hzt_ne : z ≠ t := fun h => hznotIso (h ▸ htIso)
    have htdeg : G.degree t = 3 := hisodeg3 t htIso
    exact hC4 ⟨z, p, t, q,
      card_four_twenty z p t q hzp_ne hzt_ne hzq_ne htp_ne.symm hpq htq_ne,
      hzp, hApt, hAqt.symm, hzq.symm, hnzt, hnpq, by omega⟩
  -- PART 3: at least one of `p`, `q` is iso-poor (else `hno2hub` fires).
  refine ⟨hnpq, hshare, ?_⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨hp2, hq2⟩ := hcon
  have hdisjp : Disjoint (G.neighborFinset p ∩ Iso) (G.neighborFinset q) := by
    rw [Finset.disjoint_left]
    intro v hv hvq
    obtain ⟨hvp, hvIso⟩ := Finset.mem_inter.mp hv
    have hmem : v ∈ G.neighborFinset p ∩ G.neighborFinset q ∩ Iso :=
      Finset.mem_inter.mpr ⟨Finset.mem_inter.mpr ⟨hvp, hvq⟩, hvIso⟩
    rw [hshare] at hmem
    exact absurd hmem (Finset.notMem_empty v)
  have hdisjq : Disjoint (G.neighborFinset q ∩ Iso) (G.neighborFinset p) := by
    rw [Finset.disjoint_left]
    intro v hv hvp
    obtain ⟨hvq, hvIso⟩ := Finset.mem_inter.mp hv
    have hmem : v ∈ G.neighborFinset p ∩ G.neighborFinset q ∩ Iso :=
      Finset.mem_inter.mpr ⟨Finset.mem_inter.mpr ⟨hvp, hvq⟩, hvIso⟩
    rw [hshare] at hmem
    exact absurd hmem (Finset.notMem_empty v)
  have hp2' : 2 ≤ ((G.neighborFinset p ∩ Iso) \ G.neighborFinset q).card := by
    rw [Finset.sdiff_eq_self_iff_disjoint.mpr hdisjp]; omega
  have hq2' : 2 ≤ ((G.neighborFinset q ∩ Iso) \ G.neighborFinset p).card := by
    rw [Finset.sdiff_eq_self_iff_disjoint.mpr hdisjq]; omega
  exact hno2hub ⟨p, q, hp, hq, hdp, hdq, hpq, hnpq, hp2', hq2'⟩

end N20

end ACMax
