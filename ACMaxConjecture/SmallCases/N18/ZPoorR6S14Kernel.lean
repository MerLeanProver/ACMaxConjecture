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
import ACMaxConjecture.SmallCases.N18.ZPoorR6Hard

/-!
# The `r = 6`, `S = 14` `M`-partner common-neighbour kernel (`n = 18`)

This file isolates the design-independent existence of the good-`C₄` apex `x` for the tight
`e(M) = 1`, all-degree-`4`, `(|Hub|, |Iso|) = (10, 6)` profile with six rich hubs and rich
iso-incidence sum `S = 14`.
-/

namespace ACMax

open scoped Classical

namespace N18

/-- **The `r = 6`, `S = 14` `M`-partner common-neighbour kernel (apex `C₄` *or* good triangle).**
An `M`-edge endpoint `z` (degree `3`) meets two **non-adjacent** poor hubs `hg₁, hg₂` (iso-degree
`≤ 1`, `hnadj`, `hcodeg0 = 0`); its `M`-partner `zp` (`z ~ zp`) meets two hubs, neither `hg₁` nor
`hg₂` (`hd1, hd2`).  Then either there is an **apex** hub `x ∉ {hg₁, hg₂}` adjacent to `zp` and to
one of `hg₁, hg₂` (the apex of the good `C₄`  `hgᵢ – x – zp – z`), or there is a **good triangle** of
degree sum `≤ 11`.

**Why a disjunction (the original "apex always exists" claim is false).**  An earlier plan asserted
the apex always exists.  Direct randomized construction refutes this: there are configurations
satisfying every hypothesis below (`hdeg4`, `hiso3`, `hdsum = 40`, `hleak`, `hr6 = 6`, `hS14 = 14`,
`hshare`, `hno2hub`, `hnadj`, `hcodeg0 = 0`, `hd1`, `hd2`) with **no apex**, killed instead by a
good triangle (`{zp, d₁, d₂}` when `zp`'s hubs are adjacent, or a twin-cherry).  The disjunction is
the true statement; it is delegated to `apex_or_good_triangle_S14` (the documented crux). -/
theorem mpartner_common_poor_nbr_S14 (G : SimpleGraph (Fin 18)) (Hub Iso : Finset (Fin 18))
    (hdeg4 : ∀ h ∈ Hub, G.degree h = 4)
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdisj : Disjoint Hub Iso) (hHub : Hub.card = 10) (hIso : Iso.card = 6)
    (hdeg3 : ∀ v : Fin 18, 3 ≤ G.degree v) (hisodeg3 : ∀ t ∈ Iso, G.degree t = 3)
    (hdsum : ∑ w ∈ Hub, G.degree w = 40)
    (hleak : ∑ h ∈ Hub, (G.neighborFinset h ∩ (Finset.univ \ (Hub ∪ Iso))).card ≤ 4)
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hno2hub : ¬∃ h₁ h₂ : Fin 18, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card)
    (_hC4 : ¬∃ a b c d : Fin 18, ({a, b, c, d} : Finset (Fin 18)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (_hK23 : ¬∃ a b c d e : Fin 18, ({a, b, c, d, e} : Finset (Fin 18)).card = 5 ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
      G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 19)
    (_hT : ¬∃ x y z : Fin 18, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧
      G.degree x + G.degree y + G.degree z ≤ 10)
    (hr6 : (Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)).card = 6)
    (hS14 : ∑ r ∈ Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card),
        (G.neighborFinset r ∩ Iso).card = 14)
    (z zp hg1 hg2 : Fin 18)
    (hz : z ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 18)))
    (hzpZ : zp ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 18)))
    (hzpz : zp ≠ z) (hzzp : G.Adj z zp)
    (hg1ne : hg1 ≠ hg2)
    (hg1mem : hg1 ∈ G.neighborFinset z ∩ Hub) (hg2mem : hg2 ∈ G.neighborFinset z ∩ Hub)
    (hg1poor : (G.neighborFinset hg1 ∩ Iso).card ≤ 1)
    (hg2poor : (G.neighborFinset hg2 ∩ Iso).card ≤ 1)
    (hd1 : ¬G.Adj hg1 zp) (hd2 : ¬G.Adj hg2 zp)
    (hnadj : ¬G.Adj hg1 hg2)
    (hcodeg0 : (G.neighborFinset hg1 ∩ G.neighborFinset hg2 ∩ Iso).card = 0) :
    (∃ x : Fin 18, x ∈ Hub ∧ x ≠ hg1 ∧ x ≠ hg2 ∧ G.Adj zp x ∧
        (G.Adj hg1 x ∨ G.Adj hg2 x)) ∨
    (∃ a b c : Fin 18, a ≠ b ∧ b ≠ c ∧ a ≠ c ∧
        G.Adj a b ∧ G.Adj b c ∧ G.Adj a c ∧
        G.degree a + G.degree b + G.degree c ≤ 11) := by
  classical
  -- The disjunction is the structural crux, isolated (with the single documented `sorry`) in
  -- `apex_or_good_triangle_S14`.  The earlier "apex always exists" form is provably false.
  exact apex_or_good_triangle_S14 G Hub Iso hdeg4 hiso3 hdisj hHub hIso hdeg3 hisodeg3 hdsum hleak
    hshare hno2hub hr6 hS14 z zp hg1 hg2 hz hzpZ hzpz hzzp hg1ne hg1mem hg2mem hg1poor hg2poor
    hd1 hd2 hnadj hcodeg0

end N18

end ACMax
