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

/-!
# The `r = 6`, `S = 14` poor-hub handshake (`n = 18`)

For the tight `e(M) = 1`, all-degree-`4`, `(|Hub|, |Iso|) = (10, 6)` profile with six rich hubs and
rich iso-incidence sum `S = 14`, the poor iso-incidence mass `18 - 14 = 4` is spread over the four
poor hubs (each iso-degree `≤ 1`), so by an averaging argument each poor hub has iso-degree exactly
`1`.  This file isolates that fact (`poor_handshake_S14`).
-/

namespace ACMax

open scoped Classical

namespace N18

/-- **Each poor hub has iso-degree exactly `1` (LEAF).**  The total hub–iso incidence is
`3 · |Iso| = 18`; the six rich hubs carry `14`, leaving `4` for the four poor hubs.  Each poor hub
has iso-degree `≤ 1` (it is not rich), and four values `≤ 1` summing to `4` are all `1`. -/
theorem poor_handshake_S14 (G : SimpleGraph (Fin 18)) (Hub Iso : Finset (Fin 18))
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hIso : Iso.card = 6) (hHub : Hub.card = 10)
    (hr6 : (Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)).card = 6)
    (hS14 : ∑ r ∈ Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card),
        (G.neighborFinset r ∩ Iso).card = 14) :
    ∀ p ∈ Hub.filter (fun h => ¬ 2 ≤ (G.neighborFinset h ∩ Iso).card),
      (G.neighborFinset p ∩ Iso).card = 1 := by
  classical
  set R : Finset (Fin 18) := Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card) with hRdef
  set P : Finset (Fin 18) := Hub.filter (fun h => ¬ 2 ≤ (G.neighborFinset h ∩ Iso).card) with hPdef
  -- Total hub–iso incidence is `18`.
  have hsumHub : ∑ h ∈ Hub, (G.neighborFinset h ∩ Iso).card = 18 := by
    have := hub_iso_sum_eighteen G Hub Iso hiso3; rw [hIso] at this; omega
  -- Split `Hub = R ⊔ P`.
  have hsplit : ∑ h ∈ R, (G.neighborFinset h ∩ Iso).card
      + ∑ h ∈ P, (G.neighborFinset h ∩ Iso).card = 18 := by
    rw [hRdef, hPdef, Finset.sum_filter_add_sum_filter_not Hub
      (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)]
    exact hsumHub
  -- So `∑_P isoDeg = 4`.
  have hPsum : ∑ p ∈ P, (G.neighborFinset p ∩ Iso).card = 4 := by
    omega
  -- `|P| = 4`.
  have hPcard : P.card = 4 := by
    have hc := Finset.card_filter_add_card_filter_not (s := Hub)
      (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)
    rw [← hRdef, ← hPdef, hHub, hr6] at hc; omega
  -- Each poor hub has iso-degree `≤ 1`.
  have hle1 : ∀ p ∈ P, (G.neighborFinset p ∩ Iso).card ≤ 1 := by
    intro p hp; rw [hPdef, Finset.mem_filter] at hp; omega
  -- An averaging argument: each value is exactly `1`.
  intro p hp
  have hpP : p ∈ P := hp
  have hpeel := Finset.add_sum_erase P (fun x => (G.neighborFinset x ∩ Iso).card) hpP
  have hrest : ∑ x ∈ P.erase p, (G.neighborFinset x ∩ Iso).card ≤ 3 := by
    calc ∑ x ∈ P.erase p, (G.neighborFinset x ∩ Iso).card
        ≤ ∑ _x ∈ P.erase p, 1 :=
          Finset.sum_le_sum (fun x hx => hle1 x (Finset.mem_of_mem_erase hx))
      _ = 3 := by
          rw [Finset.sum_const, Finset.card_erase_of_mem hpP, hPcard, smul_eq_mul]
  have := hle1 p hpP
  omega

end N18

end ACMax
