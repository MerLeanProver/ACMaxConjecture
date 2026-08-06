import ACMaxConjecture.Base
import ACMaxConjecture.Spectral.AlgConn
import ACMaxConjecture.Cuts.SignedCut
import ACMaxConjecture.SmallCases.N15.Core
import ACMaxConjecture.SmallCases.Certificates
import ACMaxConjecture.SmallCases.N15.Align

/-!
# Existence of a twin signed-cut certificate for `n = 15` (structural assembly)

This file assembles the `n = 15` twin signed-cut certificate from the proved boundary
certificates (`TwinCert15Cert`) and the structural-alignment dichotomies (`TwinCert15Align`),
mirroring the proved `n = 14` `exists_twin_signed_cert_fourteen`.

In the sparse-hub residual (`δ ≥ 3`, no good triangle, an isolated degree-`3` vertex, no induced
`2K₂` on degree-`3` vertices, no good `C₄`, no good `K_{2,3}`) one produces an explicit signed cut
`P, N` with `4·e(P,N) + e(P,Z) + e(N,Z) ≤ 4·|P|`, fed to `algConn_le_two_of_signed`.

The assembly case-splits on `s := ∑_{v∈D}|N v ∩ D| = 2·e(M)` (`D` the degree-`3` set), which
`eM_le_five` bounds by `10` and `eM_even` shows even, so `s ∈ {0, 2, 4, 6, 8, 10}`.  Each branch
dispatches to one of the four alignment dichotomies and then to the corresponding `_to_cut`
certificate.  The four alignment dichotomies are the only remaining open pieces; their proofs are
isolated as documented `sorry`s in `TwinCert15Align`.
-/

namespace ACMax

open scoped Classical

namespace N15

/-- **Twin signed-cut existence for `n = 15` (structural assembly).**  In the sparse-hub residual
(`δ ≥ 3`, no good triangle, no induced `2K₂` on degree-3 vertices, no good `C₄`, no good `K_{2,3}`,
with an `M`-isolated degree-3 vertex) there is a signed cut `P, N` with
`4·e(P,N) + e(P,Z) + e(N,Z) ≤ 4·|P|`.  Assembled by case-splitting on `s = 2·e(M)` and
dispatching each branch to its alignment dichotomy (`TwinCert15Align`) and `_to_cut` certificate
(`TwinCert15Cert`). -/
theorem exists_twin_signed_cert_fifteen (G : SimpleGraph (Fin 15))
    (hm : G.edgeFinset.card = 26) (h3 : ∀ v : Fin 15, 3 ≤ G.degree v)
    (hT : ¬∃ x y z : Fin 15, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    (h2k2 : ¬∃ a b c d : Fin 15, ({a, b, c, d} : Finset (Fin 15)).card = 4 ∧
      G.degree a = 3 ∧ G.degree b = 3 ∧ G.degree c = 3 ∧ G.degree d = 3 ∧
      G.Adj a b ∧ G.Adj c d ∧ ¬G.Adj a c ∧ ¬G.Adj a d ∧ ¬G.Adj b c ∧ ¬G.Adj b d)
    (hC4 : ¬∃ a b c d : Fin 15, ({a, b, c, d} : Finset (Fin 15)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 13)
    (hK23 : ¬∃ a b c d e : Fin 15, ({a, b, c, d, e} : Finset (Fin 15)).card = 5 ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
      G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 18)
    (hiso : ∃ t : Fin 15, G.degree t = 3 ∧ ∀ w : Fin 15, G.Adj t w → G.degree w ≠ 3) :
    ∃ P N : Finset (Fin 15), Disjoint P N ∧ P.card = N.card ∧ 0 < P.card ∧
      4 * (∑ p ∈ P, (G.neighborFinset p ∩ N).card)
        + (∑ p ∈ P, (G.neighborFinset p \ (P ∪ N)).card)
        + (∑ q ∈ N, (G.neighborFinset q \ (P ∪ N)).card)
      ≤ 4 * P.card := by
  classical
  set D : Finset (Fin 15) := Finset.univ.filter (fun w => G.degree w = 3) with hDdef
  have hmemD : ∀ v : Fin 15, v ∈ D ↔ G.degree v = 3 := by intro v; rw [hDdef]; simp
  set s : ℕ := ∑ v ∈ D, (G.neighborFinset v ∩ D).card with hsdef
  have heven : Even s := by rw [hsdef]; exact eM_even G D
  have hle10 : s ≤ 10 := by rw [hsdef]; exact eM_le_five G D hmemD hT hC4 h2k2
  rcases Nat.lt_or_ge s 4 with hlt4 | hge4
  · -- `e(M) ≤ 1` (`s < 4`, sharpened to `s ≤ 2` by evenness): two-hub opposite-twin cut.
    have hle2 : s ≤ 2 := by obtain ⟨k, hk⟩ := heven; omega
    exact twoHubConfig_to_cut G (two_hub_config_fifteen G hm h3 hT h2k2 hC4 hK23 hiso hle2)
  · -- `e(M) ≥ 2` (`s ≥ 4`): three-way alignment dichotomy, split by the value of `e(M)`.
    by_cases hle4 : s ≤ 4
    · -- `e(M) = 2` (`s = 4`).
      have hs4 : s = 4 := by omega
      have halign : SingleVertexConfig G ∨ TwoTwinConfig G ∨ TwoHubConfig G :=
        exists_align_four_config_fifteen G hm h3 hT h2k2 hC4 hK23 hiso hs4
      rcases halign with hsv | htt | hth
      · exact singleVertexConfig_to_cut G hsv
      · exact twoTwinConfig_to_cut G htt
      · exact twoHubConfig_to_cut G hth
    · by_cases hle6 : s ≤ 6
      · -- `e(M) = 3` (`s = 6`).
        have hs6 : s = 6 := by obtain ⟨k, hk⟩ := heven; omega
        have halign : SingleVertexConfig G ∨ TwoTwinConfig G ∨ TwoHubConfig G ∨
            HubTriangleConfig G :=
          exists_align_six_config_fifteen G hm h3 hT h2k2 hC4 hK23 hiso hs6
        rcases halign with hsv | htt | hth | hht
        · exact singleVertexConfig_to_cut G hsv
        · exact twoTwinConfig_to_cut G htt
        · exact twoHubConfig_to_cut G hth
        · exact hubTriangleConfig_to_cut G hht
      · -- `e(M) ≥ 4` (`s ≥ 8`).
        have hge8 : 8 ≤ s := by obtain ⟨k, hk⟩ := heven; omega
        have halign : SingleVertexConfig G ∨ TwoTwinConfig G ∨ TwoHubConfig G :=
          halign8_fifteen G hm h3 hT h2k2 hC4 hK23 hiso hge8
        rcases halign with hsv | htt | hth
        · exact singleVertexConfig_to_cut G hsv
        · exact twoTwinConfig_to_cut G htt
        · exact twoHubConfig_to_cut G hth

end N15

end ACMax
