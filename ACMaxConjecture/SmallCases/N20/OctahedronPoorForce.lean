import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N20.Core
import ACMaxConjecture.SmallCases.N20.OctahedronStruct
import ACMaxConjecture.SmallCases.N20.OctahedronPoorForce2
import ACMaxConjecture.SmallCases.N20.OctahedronMassFour

/-!
# Octahedron poor-layer force (`n = 20`, `|Hub| = 12`, HARD CRUX wrapper)

Port of the `n = 19` `TwinCert19OctahedronPoorForce` cert wrapper to the NEW `n = 20` `|Hub| = 12`
regime.  The rigid octahedron (six rich hubs `R`, **six** poor hubs `Hub \ R`, four high
`M`-isolated twins, two low twins, two adjacent `M`-edge endpoints `Z`) must yield a good cert
sub-configuration — a good triangle (a), a good `K₂,₃` (b), or a good `C₄` (c) — or a
`ZPoorCutConfig`.

## Foundation status (this layer)

The cross-layer **counting foundation is ported and axiom-clean** (see
`TwinCert20OctahedronPoorForce2`):

* `octahedron_poor_counts_twenty` — `E(R, Z) = 2`, `E(P, Z) = 2`, `E(R, P) + E(R, R) = 10`,
  `E(P, P) = E(R, R) + 6`, every poor hub has three neighbours in `R ∪ P ∪ Z`.
* `octahedron_low_twin_poor_twenty` — the two low twins carry the six poor incidences, splitting
  exactly `3 + 3`, disjointly covering `Hub \ R`.

## The DEEP packing (CLOSED, axiom-clean)

The genuinely-new `|Hub| = 12` content — the force itself — is **proved**
(`octahedron_poor_force_b_or_c_twenty` in `TwinCert20OctahedronMassFour`), structurally
**different** from `n = 19`:

* **Six poor hubs, not five.**  The poor layer carries ordered mass `E(P, P) = E(R, R) + 6`.  The
  trace integrality (`octahedron_trace_saturate_twenty` with `∑_t |N t ∩ R| = 12`) kills the value
  `4` outright (`n₁ + n₂ + 13 = 12` over `ℕ`), so `E(R, R) = 6` and `E(P, P) = 12`: the six poor
  form a six-edge bipartite layer on the `3 + 3` low-twin sides.
* **Branch (b) changes.**  At `n = 19` the five poor split `2 + 3` and the size-`2` side forces the
  `K₂,₃` by pure counting (`5 > 3`).  At `n = 20` the `3 + 3` split only yields the `K₂,₃` from a
  same-side pair of poor-degree sum `≥ 5`; the residual `2`-regular (`C₆`) poor layer genuinely
  TIES and is absorbed instead by a `TwoHubConfig` with one `Z`-leaf (rich hub avoiding `Z` + its
  two twins vs the `Z`-slotted poor hub + its low twin + `z₀`) — the `ZPoorCutConfig` disjunct.
* **Branch (a)/(c)** carry over in shape (low twin meeting two adjacent poor → triangle; matched-`Z`
  rich `C₄`), with (c) vacuous since mass `4` never occurs.
-/

namespace ACMax

open scoped Classical

namespace N20

/-- **Octahedron poor-layer force (HARD CRUX wrapper, axiom-clean).**  Output is
cert-ready: branch (a) yields a triangle, branch (b) a `K₂,₃`, branch (c) a `C₄`, and the
residual `C₆` poor layer lands in `ZPoorCutConfig`.  Delegates to
`octahedron_poor_force_b_or_c_twenty`; the six-poor packing is fully proved (see
`TwinCert20OctahedronMassFour`). -/
theorem octahedron_poor_layer_force_twenty (G : SimpleGraph (Fin 20))
    (Hub Iso R : Finset (Fin 20))
    (hReq : R = Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card))
    (hdeg4 : ∀ h ∈ Hub, G.degree h = 4)
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdisj : Disjoint Hub Iso) (hHub : Hub.card = 12) (hIso : Iso.card = 6)
    (hisodeg3 : ∀ t ∈ Iso, G.degree t = 3) (hdeg3 : ∀ v : Fin 20, 3 ≤ G.degree v)
    (hdsum : ∑ w ∈ Hub, G.degree w = 48)
    (hleak : ∑ h ∈ Hub, (G.neighborFinset h ∩ (Finset.univ \ (Hub ∪ Iso))).card ≤ 4)
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hno2hub : ¬∃ h₁ h₂ : Fin 20, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card)
    (hC4 : ¬∃ a b c d : Fin 20, ({a, b, c, d} : Finset (Fin 20)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (hK23 : ¬∃ a b c d e : Fin 20, ({a, b, c, d, e} : Finset (Fin 20)).card = 5 ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
      G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 19)
    (hT : ¬∃ x y z : Fin 20, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧
      G.degree x + G.degree y + G.degree z ≤ 11)
    (hnozero : ∀ h ∈ Hub, 1 ≤ (G.neighborFinset h ∩ Iso).card)
    (hRcard : R.card = 6)
    (hmass : (∑ r ∈ R, (G.neighborFinset r ∩ R).card) = 4 ∨
      (∑ r ∈ R, (G.neighborFinset r ∩ R).card) = 6)
    (hhigh4 : 4 ≤ (Iso.filter (fun t => (G.neighborFinset t ∩ R).card = 3)).card)
    (htle3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ R).card ≤ 3) :
    ((∃ g₁ g₂ t : Fin 20, g₁ ∈ Hub ∧ g₂ ∈ Hub ∧ t ∈ Iso ∧ g₁ ≠ g₂ ∧
      G.Adj g₁ g₂ ∧ G.Adj g₁ t ∧ G.Adj g₂ t) ∨
    (∃ a b c d t : Fin 20, a ∈ Hub ∧ b ∈ Hub ∧ c ∈ Hub ∧ d ∈ Hub ∧ t ∈ Iso ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a t ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b t ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c t ∧ ¬G.Adj d t ∧
      a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d) ∨
    (∃ r₁ r₂ z₁ z₂ : Fin 20, r₁ ∈ Hub ∧ r₂ ∈ Hub ∧
      z₁ ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 20)) ∧
      z₂ ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 20)) ∧
      G.degree z₁ = 3 ∧ G.degree z₂ = 3 ∧
      G.Adj r₁ z₁ ∧ G.Adj z₁ z₂ ∧ G.Adj z₂ r₂ ∧ G.Adj r₂ r₁ ∧
      ¬G.Adj r₁ z₂ ∧ ¬G.Adj z₁ r₂ ∧ r₁ ≠ r₂ ∧ z₁ ≠ z₂)) ∨ ZPoorCutConfig G := by
  classical
  -- The six-poor packing (`mRR = 6`, `E(P, P) = 12`): mass `4` is killed outright
  -- (`octahedron_mass_four_absurd_twenty`); mass `6` makes the six poor carry six cross edges —
  -- a heavy same-side pair shares `≥ 2` common neighbours on the size-`3` far side (a good
  -- `K₂,₃`), and the residual `2`-regular `C₆` layer realises a `TwoHubConfig` with one `Z`-leaf.
  exact octahedron_poor_force_b_or_c_twenty G Hub Iso R hReq hdeg4 hiso3 hdisj hHub hIso hisodeg3
    hdeg3 hdsum hleak hshare hno2hub hC4 hK23 hT hnozero hRcard hmass hhigh4 htle3

end N20

end ACMax
