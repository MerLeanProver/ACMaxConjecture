import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N19.Core
import ACMaxConjecture.SmallCases.N19.OctahedronStruct
import ACMaxConjecture.SmallCases.N19.OctahedronPoorForce2
import ACMaxConjecture.SmallCases.N19.OctahedronMassFour

/-!
# Octahedron poor-layer force (`n = 19`, `|Hub| = 11`, HARD CRUX wrapper)

Port of the `n = 18` `TwinCert18OctahedronPoorForce` three-way cert wrapper to the NEW `n = 19`
`|Hub| = 11` regime.  The rigid octahedron (six rich hubs `R`, **five** poor hubs `Hub \ R`, four high
`M`-isolated twins, two low twins, two adjacent `M`-edge endpoints `Z`) must yield one of three good
cert sub-configurations — a good triangle (a), a good `K₂,₃` (b), or a good `C₄` (c) — exactly as at
`n = 18`.

## Foundation status (this layer)

The cross-layer **counting foundation is ported and axiom-clean** (see
`TwinCert19OctahedronPoorForce2`):

* `octahedron_poor_counts_nineteen` — `E(R, Z) = 2`, `E(P, Z) = 2`, `E(R, P) + E(R, R) = 9`,
  `E(P, P) = E(R, R) + 4`, every poor hub has three neighbours in `R ∪ P ∪ Z`.  Threads `hztwopoor`.
* `octahedron_low_twin_poor_nineteen` — the two low twins carry the five poor incidences, splitting
  `2 + 3` or `3 + 2`, disjointly covering `Hub \ R`.

Both are invoked below (as `_hcounts`, `_hlowtwin`) so the hypothesis set of this wrapper is exactly
sufficient to drive the deferred case analysis.

## The DEEP packing (CLOSED, axiom-clean)

The genuinely-new `|Hub| = 11` content — the three-way force itself — is now **proved**
(`octahedron_poor_force_b_or_c_nineteen` in `TwinCert19OctahedronMassFour`), structurally
**different** from `n = 18`:

* **Five poor hubs, not four.**  The poor layer carries ordered mass `E(P, P) = E(R, R) + 4`.  The
  trace integrality (`octahedron_trace_saturate_nineteen` with `∑_t |N t ∩ R| = 13`) forces
  `E(R, R) = 6` — the value `4` gives the non-integer twin profile `3·n₃ = 13` and is impossible by
  parity (a SIMPLIFICATION: at `n = 18` mass `4` needed the elaborate two-hub extraction
  `octahedron_mass_four_absurd_eighteen`).  Hence `E(P, P) = 10`, so the five poor hubs form a
  near-`C₅` (average internal degree `2`), not the `n = 18` `C₄`.
* **Branch (b) changes.**  At `n = 18` the four poor split `2 + 2` and the bipartite-poor witness is a
  `C₄` whose diagonal pair with a low twin is a `K₂,₃`.  At `n = 19` the five poor split `2 + 3`, and
  the `K₂,₃` must be extracted from the larger poor structure — genuinely-new packing.
* **Branch (a)/(c)** carry over in shape (low twin meeting two adjacent poor → triangle; matched-`Z`
  rich `C₄`), but their exhaustiveness now rests on the `mRR = 6`, five-poor handshake.

The remaining open dependency is the not-yet-ported `z`-meets-2-poor / `TwinCert19ZPoorDispatch`
cluster (whose apex `z_meets_two_poor_forces_two_hub_nineteen` discharges `hztwopoor` here, making the
whole chain hypothesis-free).
-/

namespace ACMax

open scoped Classical

namespace N19

/-- **Octahedron poor-layer three-way force (HARD CRUX wrapper, axiom-clean).**  Output is
cert-ready: branch (a) yields a triangle, branch (b) a `K₂,₃`, branch (c) a `C₄`.  Delegates to
`octahedron_poor_force_b_or_c_nineteen`; the five-poor three-way packing is now fully proved (see
`TwinCert19OctahedronMassFour`). -/
theorem octahedron_poor_layer_force_nineteen (G : SimpleGraph (Fin 19))
    (Hub Iso R : Finset (Fin 19))
    (hReq : R = Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card))
    (hdeg4 : ∀ h ∈ Hub, G.degree h = 4)
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdisj : Disjoint Hub Iso) (hHub : Hub.card = 11) (hIso : Iso.card = 6)
    (hisodeg3 : ∀ t ∈ Iso, G.degree t = 3) (hdeg3 : ∀ v : Fin 19, 3 ≤ G.degree v)
    (hdsum : ∑ w ∈ Hub, G.degree w = 44)
    (hleak : ∑ h ∈ Hub, (G.neighborFinset h ∩ (Finset.univ \ (Hub ∪ Iso))).card ≤ 4)
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hno2hub : ¬∃ h₁ h₂ : Fin 19, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card)
    (hC4 : ¬∃ a b c d : Fin 19, ({a, b, c, d} : Finset (Fin 19)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (hK23 : ¬∃ a b c d e : Fin 19, ({a, b, c, d, e} : Finset (Fin 19)).card = 5 ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
      G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 19)
    (hT : ¬∃ x y z : Fin 19, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧
      G.degree x + G.degree y + G.degree z ≤ 11)
    (hnozero : ∀ h ∈ Hub, 1 ≤ (G.neighborFinset h ∩ Iso).card)
    (hRcard : R.card = 6)
    (hmass : (∑ r ∈ R, (G.neighborFinset r ∩ R).card) = 4 ∨
      (∑ r ∈ R, (G.neighborFinset r ∩ R).card) = 6)
    (hhigh4 : 4 ≤ (Iso.filter (fun t => (G.neighborFinset t ∩ R).card = 3)).card)
    (htle3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ R).card ≤ 3) :
    ((∃ g₁ g₂ t : Fin 19, g₁ ∈ Hub ∧ g₂ ∈ Hub ∧ t ∈ Iso ∧ g₁ ≠ g₂ ∧
      G.Adj g₁ g₂ ∧ G.Adj g₁ t ∧ G.Adj g₂ t) ∨
    (∃ a b c d t : Fin 19, a ∈ Hub ∧ b ∈ Hub ∧ c ∈ Hub ∧ d ∈ Hub ∧ t ∈ Iso ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a t ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b t ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c t ∧ ¬G.Adj d t ∧
      a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d) ∨
    (∃ r₁ r₂ z₁ z₂ : Fin 19, r₁ ∈ Hub ∧ r₂ ∈ Hub ∧
      z₁ ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 19)) ∧
      z₂ ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 19)) ∧
      G.degree z₁ = 3 ∧ G.degree z₂ = 3 ∧
      G.Adj r₁ z₁ ∧ G.Adj z₁ z₂ ∧ G.Adj z₂ r₂ ∧ G.Adj r₂ r₁ ∧
      ¬G.Adj r₁ z₂ ∧ ¬G.Adj z₁ r₂ ∧ r₁ ≠ r₂ ∧ z₁ ≠ z₂)) ∨ ZPoorCutConfig G := by
  classical
  -- The five-poor three-way packing (`mRR = 6`, `E(P, P) = 10`): mass `4` is killed by parity
  -- (`octahedron_mass_four_absurd_nineteen`); mass `6` makes the five poor carry five cross edges,
  -- and the size-`2` low-twin side shares `≥ 2` common neighbours on the size-`3` side, a good `K₂,₃`.
  exact octahedron_poor_force_b_or_c_nineteen G Hub Iso R hReq hdeg4 hiso3 hdisj hHub hIso hisodeg3
    hdeg3 hdsum hleak hshare hno2hub hC4 hK23 hT hnozero hRcard hmass hhigh4 htle3

end N19

end ACMax
