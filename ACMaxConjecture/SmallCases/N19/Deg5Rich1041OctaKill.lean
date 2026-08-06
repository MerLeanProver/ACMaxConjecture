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
import ACMaxConjecture.SmallCases.N19.Deg5Rich1041OctaPoorCert

/-!
# The share-2 octahedron kill for the (10,7,41) corner (`n = 19`)

The residual of the rigid-tie kill: the degree-`5` hub `f` (isoDeg `5`, hence
adjacent to no hub) and the degree-`4` iso-rich hub `x` share `≤ 2` `Iso`
twins.  The ledger pins the profile (`|R| = 5`: two isoDeg-`3`, three
isoDeg-`2`, four isoDeg-`1` degree-`4` hubs), `hblock` pins the rigid `2+1+2`
blocker partition of the rich hubs around `{t₀, z, h₂}`, and the `M`-set
covering-design (`f`'s two missed twins) plus the poor/`Z` layer force a good
triangle (`Σ ≤ 11`, `hT`) ∨ `K₂,₃` (`Σ ≤ 19`, `hK23`) ∨ `C₄` (`Σ ≤ 14`,
`hC4`).  The deg-`5` analog of the proven `(11,6,44)` octahedron poor-cert
(`TwinCert19OctahedronPoorForce2` / `TwinCert19R5Octahedron`) and the `n = 18`
`octahedron_poor_cert_eighteen`.
-/

namespace ACMax

open scoped Classical

namespace N19

set_option maxHeartbeats 1000000 in
/-- **The share-2 octahedron kill.**  The rigid `(10,7,41)` tie with `f` of
isoDeg `5` and `x` sharing `≤ 2` twins with `f` is contradictory. -/
theorem octahedron_share2_kill_1041_nineteen (G : SimpleGraph (Fin 19))
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
    (hsh : ¬ 3 ≤ (G.neighborFinset x ∩ G.neighborFinset f ∩ Iso).card) :
    False :=
  octahedron_poor_cert_share2_1041_nineteen G Hub Iso hiso3 hdisj hsum17 hdeg3 hisodeg3
    hleak hdeg hdeg5 hHub hIso hdsum hT hC4 hK23 hshare hno2hub g hg hgd hgiso h₂ z hh₂ hd₂
    hzZ hz2 hgz hg2 hpoor hshared hblock f x hfHub hfd hfiso5 hxHub hxd hxiso3 hxf hnadj hsh
    (octahedron_struct_share2_1041_nineteen G Hub Iso hiso3 hdisj hsum17 hdeg3 hisodeg3
      hleak hdeg hdeg5 hHub hIso hdsum hT hC4 hK23 hshare hno2hub g hg hgd hgiso h₂ z hh₂
      hd₂ hzZ hz2 hgz hg2 hpoor hshared hblock)

end N19

end ACMax
