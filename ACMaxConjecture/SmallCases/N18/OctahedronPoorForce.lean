import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N18.Core
import ACMaxConjecture.SmallCases.N18.OctahedronStruct
import ACMaxConjecture.SmallCases.N18.OctahedronPoorForce2

/-!
# Octahedron poor-layer force (`n = 18`, HARD CRUX)

The rigid octahedron (six rich hubs `R`, four poor hubs `Hub \ R`, four high `M`-isolated twins,
two low twins, two adjacent `M`-edge endpoints `Z`) is killed by a good cert that depends on the
poor/`Z` layout.  This file isolates the genuine three-way split as a single forcing lemma.

`octahedron_poor_layer_force_eighteen` derives the poor-layer structure (`octahedron_struct_eighteen`)
and the `Z`-layer rigidity (`octahedron_Z_rigid_eighteen`), then performs the finite case analysis on
the poor + `Z` layer.  Tracking the rich/poor handshake `2·E(R, R) + E(R, P) = 8` over the two low
twins (each meeting two poor) and the two `Z`-vertices (each meeting two hubs through the `M`-edge),
exactly one of three configurations occurs (verified against the two no-two-hub octahedron isomorphism
classes — config-model sampling is unreliable here, so each branch was checked by direct construction
in `octa.py`/`octa2.py`):

* **(a)** two adjacent poor hubs share a low twin (a good triangle `4 + 4 + 3 = 11`);
* **(b)** the four poor hubs form a `C₄` whose one diagonal pair is the two poor a low twin meets (a
  good `K₂,₃` of degree sum `4 + 4 + 4 + 4 + 3 = 19`);
* **(c)** the two `M`-edge endpoints attach to two matched rich hubs (a good `C₄`
  `rich–Z–Z–rich` of degree sum `4 + 3 + 3 + 4 = 14`).

The bipartite-poor witness (no poor edge inside a low-twin pair) has **no** triangle, so the split is
genuine.  Branch (c) (mass `4`) is in fact vacuous — every mass-`4` rigid octahedron contains a
forbidden two-hub pair — so the whole force is now `sorry`-free.
-/

namespace ACMax

open scoped Classical

namespace N18

/-- **Octahedron poor-layer three-way force (HARD CRUX).**  See the module docstring.  The output is
cert-ready: branch (a) yields a triangle, branch (b) a `K₂,₃`, branch (c) a `C₄`. -/
theorem octahedron_poor_layer_force_eighteen (G : SimpleGraph (Fin 18))
    (Hub Iso R : Finset (Fin 18))
    (hReq : R = Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card))
    (hdeg4 : ∀ h ∈ Hub, G.degree h = 4)
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdisj : Disjoint Hub Iso) (hHub : Hub.card = 10) (hIso : Iso.card = 6)
    (hisodeg3 : ∀ t ∈ Iso, G.degree t = 3) (hdeg3 : ∀ v : Fin 18, 3 ≤ G.degree v)
    (hdsum : ∑ w ∈ Hub, G.degree w = 40)
    (hleak : ∑ h ∈ Hub, (G.neighborFinset h ∩ (Finset.univ \ (Hub ∪ Iso))).card ≤ 4)
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hno2hub : ¬∃ h₁ h₂ : Fin 18, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card)
    (hC4 : ¬∃ a b c d : Fin 18, ({a, b, c, d} : Finset (Fin 18)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (hK23 : ¬∃ a b c d e : Fin 18, ({a, b, c, d, e} : Finset (Fin 18)).card = 5 ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
      G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 19)
    (hT : ¬∃ x y z : Fin 18, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧
      G.degree x + G.degree y + G.degree z ≤ 11)
    (hnozero : ∀ h ∈ Hub, 1 ≤ (G.neighborFinset h ∩ Iso).card)
    (hRcard : R.card = 6)
    (hmass : (∑ r ∈ R, (G.neighborFinset r ∩ R).card) = 4 ∨
      (∑ r ∈ R, (G.neighborFinset r ∩ R).card) = 6)
    (hhigh4 : 4 ≤ (Iso.filter (fun t => (G.neighborFinset t ∩ R).card = 3)).card)
    (htle3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ R).card ≤ 3) :
    (∃ g₁ g₂ t : Fin 18, g₁ ∈ Hub ∧ g₂ ∈ Hub ∧ t ∈ Iso ∧ g₁ ≠ g₂ ∧
      G.Adj g₁ g₂ ∧ G.Adj g₁ t ∧ G.Adj g₂ t) ∨
    (∃ a b c d t : Fin 18, a ∈ Hub ∧ b ∈ Hub ∧ c ∈ Hub ∧ d ∈ Hub ∧ t ∈ Iso ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a t ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b t ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c t ∧ ¬G.Adj d t ∧
      a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d) ∨
    (∃ r₁ r₂ z₁ z₂ : Fin 18, r₁ ∈ Hub ∧ r₂ ∈ Hub ∧
      z₁ ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 18)) ∧
      z₂ ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 18)) ∧
      G.degree z₁ = 3 ∧ G.degree z₂ = 3 ∧
      G.Adj r₁ z₁ ∧ G.Adj z₁ z₂ ∧ G.Adj z₂ r₂ ∧ G.Adj r₂ r₁ ∧
      ¬G.Adj r₁ z₂ ∧ ¬G.Adj z₁ r₂ ∧ r₁ ≠ r₂ ∧ z₁ ≠ z₂) := by
  classical
  -- The finite case analysis on the poor + `Z` layer via the handshake `2·E(R,R) + E(R,P) = 8`,
  -- verified branch-by-branch against the two no-two-hub octahedron classes (`octa.py`/`octa2.py`).
  exact octahedron_poor_force_b_or_c_eighteen G Hub Iso R hReq hdeg4 hiso3 hdisj hHub hIso hisodeg3
    hdeg3 hdsum hleak hshare hno2hub hC4 hK23 hT hnozero hRcard hmass hhigh4 htle3

end N18

end ACMax
