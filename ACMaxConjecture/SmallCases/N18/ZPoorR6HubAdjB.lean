import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N18.Core
import ACMaxConjecture.SmallCases.N18.TwoHubSelect
import ACMaxConjecture.SmallCases.N18.StarTriangleStruct
import ACMaxConjecture.SmallCases.N18.RichCount
import ACMaxConjecture.SmallCases.N18.Align8Helpers
import ACMaxConjecture.SmallCases.N18.ZPoorN3
import ACMaxConjecture.SmallCases.N18.ZPoorR7
import ACMaxConjecture.SmallCases.N18.ZVertex
import ACMaxConjecture.SmallCases.N18.ZPoorSat
import ACMaxConjecture.SmallCases.N18.ZPoorR6Dist
import ACMaxConjecture.SmallCases.N18.ZPoorR6Sat
import ACMaxConjecture.SmallCases.N18.ZPoorR6Poor
import ACMaxConjecture.SmallCases.N18.ZPoorR6HubAdj
import ACMaxConjecture.SmallCases.N18.ZPoorR6HubAdjBStruct
import ACMaxConjecture.SmallCases.N18.ZPoorR6CooccurB
import ACMaxConjecture.SmallCases.N18.ZPoorR6S23B
import ACMaxConjecture.SmallCases.N18.ZPoorR6S4B

/-!
# Design B (`{3,3,2,2,2,2}`) for the `r = 6`, `S = 14` no-apex core (`n = 18`)

This file closes the design-`B` half of the hub-adjacency core `G.Adj d₁ d₂` of
`apex_or_good_triangle_S14`: under the `r = 6`, `S = 14` structure with `hshare`, `hno2hub`,
no-apex, no-twin-cherry, `hcodeg0` and `¬Adj d₁ d₂`, the rich iso-degree multiset
`{3,3,2,2,2,2}` (two rich hubs `w₁, w₂` of iso-degree `3` and four of iso-degree `2`) is
impossible.

The two iso-degree-`3` hubs `w₁, w₂` are mutually adjacent and otherwise hub-isolated
(`designB_w_structure_S14`); every twin meets exactly one of them and each rich-`2` hub shares one
twin with each (`designB_rich_cooccur_S14`).  Writing `s = isoDeg d₁ + isoDeg d₂ ∈ {2, 3, 4}` (the
hub-neighbours `d₁, d₂` of the `M`-partner `zp` are poor or rich-`2`, never `w₁, w₂`), the subcase
`s ≤ 3` is `designB_s2s3_false_S14` (from the cut identities and rich co-occurrence) and the subcase
`s = 4` is `designB_s4_false_S14` (which needs `hcodeg0`: it forces `hg₁, hg₂` onto a common twin).
-/

namespace ACMax

open scoped Classical

namespace N18

/-- **Design B (`{3,3,2,2,2,2}`) is impossible in the no-apex core.**  With the `r = 6`, `S = 14`
structure, `hshare`, `hno2hub`, no-apex (`hapex`), no-twin-cherry (`hcherry`), `hcodeg0` and
`¬Adj d₁ d₂`, a rich iso-degree distribution with two hubs `w₁, w₂` of iso-degree `3` is
contradictory.  The iso-degree subcases `s = isoDeg d₁ + isoDeg d₂ ∈ {2, 3, 4}` are dispatched to
`designB_s2s3_false_S14` (`s ≤ 3`) and `designB_s4_false_S14` (`s = 4`, using `hcodeg0`). -/
theorem forced_designB_false_S14 (G : SimpleGraph (Fin 18)) (Hub Iso : Finset (Fin 18))
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdisj : Disjoint Hub Iso) (hHub : Hub.card = 10) (hIso : Iso.card = 6)
    (hdsum : ∑ w ∈ Hub, G.degree w = 40)
    (hdeg3 : ∀ v : Fin 18, 3 ≤ G.degree v) (hisodeg3 : ∀ t ∈ Iso, G.degree t = 3)
    (hleak : ∑ h ∈ Hub, (G.neighborFinset h ∩ (Finset.univ \ (Hub ∪ Iso))).card ≤ 4)
    (hdeg4 : ∀ h ∈ Hub, G.degree h = 4)
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hno2hub : ¬∃ h₁ h₂ : Fin 18, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card)
    (hcherry : ¬∃ t ∈ Iso, ∃ a b : Fin 18, a ∈ G.neighborFinset t ∧ b ∈ G.neighborFinset t ∧
      a ≠ b ∧ G.Adj a b)
    (w1 w2 z zp hg1 hg2 d1 d2 : Fin 18)
    (hw1Hub : w1 ∈ Hub) (hw2Hub : w2 ∈ Hub) (hw1w2ne : w1 ≠ w2)
    (hw13 : (G.neighborFinset w1 ∩ Iso).card = 3) (hw23 : (G.neighborFinset w2 ∩ Iso).card = 3)
    (hother2 : ∀ r ∈ Hub, r ≠ w1 → r ≠ w2 → 2 ≤ (G.neighborFinset r ∩ Iso).card →
      (G.neighborFinset r ∩ Iso).card = 2)
    (hzZ : z ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 18)))
    (hzpZ : zp ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 18)))
    (hg1Hub : hg1 ∈ Hub) (hg2Hub : hg2 ∈ Hub) (hd1Hub : d1 ∈ Hub) (hd2Hub : d2 ∈ Hub)
    (hg1z : G.Adj hg1 z) (hg2z : G.Adj hg2 z) (hd1zp : G.Adj d1 zp) (hd2zp : G.Adj d2 zp)
    (hg1zp : ¬G.Adj hg1 zp) (hg2zp : ¬G.Adj hg2 zp)
    (hg1g2 : hg1 ≠ hg2) (hd1d2 : d1 ≠ d2)
    (hnadj : ¬G.Adj hg1 hg2) (hd1d2nadj : ¬G.Adj d1 d2)
    (hapex : ¬∃ x : Fin 18, x ∈ Hub ∧ x ≠ hg1 ∧ x ≠ hg2 ∧ G.Adj zp x ∧ (G.Adj hg1 x ∨ G.Adj hg2 x))
    (hg1iso1 : (G.neighborFinset hg1 ∩ Iso).card = 1)
    (hg2iso1 : (G.neighborFinset hg2 ∩ Iso).card = 1)
    (hcodeg0 : (G.neighborFinset hg1 ∩ G.neighborFinset hg2 ∩ Iso).card = 0)
    (hd1iso : (G.neighborFinset d1 ∩ Iso).card = 1 ∨ (G.neighborFinset d1 ∩ Iso).card = 2)
    (hd2iso : (G.neighborFinset d2 ∩ Iso).card = 1 ∨ (G.neighborFinset d2 ∩ Iso).card = 2) :
    False := by
  classical
  -- Subcase split on `s = isoDeg d₁ + isoDeg d₂ ∈ {2, 3, 4}`.
  rcases hd1iso with h1 | h1 <;> rcases hd2iso with h2 | h2
  · exact designB_s2s3_false_S14 G Hub Iso hiso3 hdisj hHub hIso hdsum hdeg3 hisodeg3 hleak hdeg4
      hshare hno2hub hcherry w1 w2 z zp hg1 hg2 d1 d2 hw1Hub hw2Hub hw1w2ne hw13 hw23 hother2 hzZ
      hzpZ hg1Hub hg2Hub hd1Hub hd2Hub hg1z hg2z hd1zp hd2zp hg1zp hg2zp hg1g2 hd1d2 hnadj
      hd1d2nadj hapex hg1iso1 hg2iso1 hcodeg0 (by omega)
  · exact designB_s2s3_false_S14 G Hub Iso hiso3 hdisj hHub hIso hdsum hdeg3 hisodeg3 hleak hdeg4
      hshare hno2hub hcherry w1 w2 z zp hg1 hg2 d1 d2 hw1Hub hw2Hub hw1w2ne hw13 hw23 hother2 hzZ
      hzpZ hg1Hub hg2Hub hd1Hub hd2Hub hg1z hg2z hd1zp hd2zp hg1zp hg2zp hg1g2 hd1d2 hnadj
      hd1d2nadj hapex hg1iso1 hg2iso1 hcodeg0 (by omega)
  · exact designB_s2s3_false_S14 G Hub Iso hiso3 hdisj hHub hIso hdsum hdeg3 hisodeg3 hleak hdeg4
      hshare hno2hub hcherry w1 w2 z zp hg1 hg2 d1 d2 hw1Hub hw2Hub hw1w2ne hw13 hw23 hother2 hzZ
      hzpZ hg1Hub hg2Hub hd1Hub hd2Hub hg1z hg2z hd1zp hd2zp hg1zp hg2zp hg1g2 hd1d2 hnadj
      hd1d2nadj hapex hg1iso1 hg2iso1 hcodeg0 (by omega)
  · exact designB_s4_false_S14 G Hub Iso hiso3 hdisj hHub hIso hdsum hdeg3 hisodeg3 hleak hdeg4
      hshare hno2hub hcherry w1 w2 z zp hg1 hg2 d1 d2 hw1Hub hw2Hub hw1w2ne hw13 hw23 hother2 hzZ
      hzpZ hg1Hub hg2Hub hd1Hub hd2Hub hg1z hg2z hd1zp hd2zp hg1zp hg2zp hg1g2 hd1d2 hnadj
      hd1d2nadj hapex hg1iso1 hg2iso1 hcodeg0 h1 h2

end N18

end ACMax
