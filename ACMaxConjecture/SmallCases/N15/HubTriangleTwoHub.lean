import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N15.Core
import ACMaxConjecture.SmallCases.Certificates
import ACMaxConjecture.SmallCases.N15.HubTriangleStruct
import ACMaxConjecture.SmallCases.N15.HubTriangleFF
import ACMaxConjecture.SmallCases.N15.HubTriangleIsoRich

/-!
# The no-avoider-triangle contradiction for the `n = 15` hub-triangle corner

This file discharges the single hard combinatorial core of `exists_hub_triangle_config_residual`:
when neither cherry has a triangle of avoiding hubs, the residual configuration is contradictory.
The contradiction is obtained directly by *forcing* a cherry-`{c₁,c₂,L₂}` avoider triangle
(`hub_triangle_from_structure` in `TwinCert15HubTriangleIsoRich`), contradicting `htri2`; the
`TwoHubConfig` route and the negation `hth` turn out to be superfluous.
-/

namespace ACMax

open scoped Classical

namespace N15

/-- **No avoider triangle ⇒ contradiction (the two-hub core).**  Under all the residual
hypotheses, the assumption `htri2` that cherry `{c₁,c₂,L₂}` admits no triangle of
pairwise-adjacent avoiding hubs is contradictory: such a triangle is forced by the seven-hub
incidence structure (`hub_triangle_from_structure`). -/
theorem core_triangle_force_twohub (G : SimpleGraph (Fin 15))
    (D Iso : Finset (Fin 15)) (L₁ c₁ c₂ L₂ : Fin 15)
    (_hT : ¬∃ x y z : Fin 15, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    (_hC4 : ¬∃ a b c d : Fin 15, ({a, b, c, d} : Finset (Fin 15)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 13)
    (_hK23 : ¬∃ a b c d e : Fin 15, ({a, b, c, d, e} : Finset (Fin 15)).card = 5 ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
      G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 18)
    (_hmemD : ∀ v : Fin 15, v ∈ D ↔ G.degree v = 3)
    (hIsodef : Iso = D.filter (fun v => (G.neighborFinset v ∩ D).card = 0))
    (hIsoprop : ∀ v ∈ Iso, G.degree v = 3 ∧ (∀ w : Fin 15, G.Adj v w → G.degree w ≠ 3))
    (hisochar : ∀ w : Fin 15, w ∈ D → w ≠ L₁ → w ≠ c₁ → w ≠ c₂ → w ≠ L₂ → w ∈ Iso)
    (_hcov : ∀ p q : Fin 15, p ∈ D → q ∈ D → G.Adj p q →
      p = c₁ ∨ p = c₂ ∨ q = c₁ ∨ q = c₂)
    (_hNc1D : G.neighborFinset c₁ ∩ D = {c₂, L₁}) (_hNc2D : G.neighborFinset c₂ ∩ D = {c₁, L₂})
    (_hc1deg : G.degree c₁ = 3) (_hc2deg : G.degree c₂ = 3)
    (_hL1deg : G.degree L₁ = 3) (_hL2deg : G.degree L₂ = 3)
    (hac1L1 : G.Adj c₁ L₁) (hc12 : G.Adj c₁ c₂) (hac2L2 : G.Adj c₂ L₂)
    (_hnL1c2 : ¬G.Adj L₁ c₂) (hnc1L2 : ¬G.Adj c₁ L₂)
    (hL1nc2 : L₁ ≠ c₂) (hL2nc1 : L₂ ≠ c₁)
    (hdeg4 : ∀ w : Fin 15, w ∈ Dᶜ → G.degree w = 4)
    (_hD8 : D.card = 8) (_hth : ¬TwoHubConfig G)
    (hL1D : L₁ ∈ D) (hc1D : c₁ ∈ D) (hc2D : c₂ ∈ D) (hL2D : L₂ ∈ D)
    (hW : ∀ g : Fin 15, g ∈ Dᶜ →
      ((¬G.Adj g L₁ ∧ ¬G.Adj g c₁ ∧ ¬G.Adj g c₂) ∨
        (¬G.Adj g c₁ ∧ ¬G.Adj g c₂ ∧ ¬G.Adj g L₂)) →
      (G.neighborFinset g ∩ Iso).card ≤ 1)
    (_hA : ∀ t : Fin 15, t ∈ Iso → ∀ p q : Fin 15, p ≠ q →
      G.Adj t p → G.Adj t q →
      ¬((¬G.Adj p L₁ ∧ ¬G.Adj p c₁ ∧ ¬G.Adj p c₂ ∧
          ¬G.Adj q L₁ ∧ ¬G.Adj q c₁ ∧ ¬G.Adj q c₂) ∨
        (¬G.Adj p c₁ ∧ ¬G.Adj p c₂ ∧ ¬G.Adj p L₂ ∧
          ¬G.Adj q c₁ ∧ ¬G.Adj q c₂ ∧ ¬G.Adj q L₂)))
    (hDc7 : Dᶜ.card = 7) (hIso4 : Iso.card = 4)
    (hcard_c1 : (G.neighborFinset c₁ ∩ Dᶜ).card = 1)
    (hcard_c2 : (G.neighborFinset c₂ ∩ Dᶜ).card = 1)
    (hcard_L1 : (G.neighborFinset L₁ ∩ Dᶜ).card = 2)
    (hcard_L2 : (G.neighborFinset L₂ ∩ Dᶜ).card = 2)
    (hSum10 : ∑ w ∈ Dᶜ, (G.neighborFinset w ∩ Dᶜ).card = 10)
    (_htri1 : ¬∃ a b c : Fin 15, a ∈ Dᶜ ∧ b ∈ Dᶜ ∧ c ∈ Dᶜ ∧
      G.Adj a b ∧ G.Adj a c ∧ G.Adj b c ∧
      (¬G.Adj a L₁ ∧ ¬G.Adj a c₁ ∧ ¬G.Adj a c₂) ∧
      (¬G.Adj b L₁ ∧ ¬G.Adj b c₁ ∧ ¬G.Adj b c₂) ∧
      (¬G.Adj c L₁ ∧ ¬G.Adj c c₁ ∧ ¬G.Adj c c₂))
    (htri2 : ¬∃ a b c : Fin 15, a ∈ Dᶜ ∧ b ∈ Dᶜ ∧ c ∈ Dᶜ ∧
      G.Adj a b ∧ G.Adj a c ∧ G.Adj b c ∧
      (¬G.Adj a c₁ ∧ ¬G.Adj a c₂ ∧ ¬G.Adj a L₂) ∧
      (¬G.Adj b c₁ ∧ ¬G.Adj b c₂ ∧ ¬G.Adj b L₂) ∧
      (¬G.Adj c c₁ ∧ ¬G.Adj c c₂ ∧ ¬G.Adj c L₂)) :
    False := by
  classical
  -- **Combinatorial core.**  Under the residual hypotheses, the assumption `htri2` that cherry
  -- `{c₁, c₂, L₂}` has no triangle of pairwise-adjacent avoiding hubs is contradictory: the
  -- seven-hub incidence structure forces such a triangle (case split on the number of fully-free
  -- hubs).  This is the `TwoHubConfig`-free route worked out in `TwinCert15HubTriangleIsoRich`; the
  -- `TwoHubConfig` negation `hth` and the other-cherry hypotheses become superfluous.
  exact hub_triangle_from_structure G D Iso L₁ c₁ c₂ L₂ hIsodef hIsoprop hisochar hL1D hc1D hc2D
    hL2D hac1L1 hc12 hac2L2 hnc1L2 hdeg4 hDc7 hIso4 hcard_c1 hcard_c2 hcard_L1 hcard_L2 hSum10
    hL1nc2 hL2nc1 hW htri2

end N15

end ACMax
