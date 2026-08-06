import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N18.Core
import ACMaxConjecture.SmallCases.N18.TwoHubSelect
import ACMaxConjecture.SmallCases.N18.StarTriangleStruct

/-!
# Degree-split and rich-mass counting for the `(9, 7, 37)` tight profile (`n = 18`)

For the tight `e(M) = 1` profile `(|Hub|, |Iso|, ∑deg) = (9, 7, 37)` every hub has degree `4` or
`5`, so `∑deg = 37 = 4·9 + 1` forces exactly **one** degree-`5` hub and **eight** degree-`4` hubs.
Each `M`-isolated twin meets exactly three hubs, so the total iso-incidence sum is `3·7 = 21`.

The headline fact assembled here is `deg5_iso_ge_three_nine_seven`: under the no-good-two-hub
hypothesis the degree-`4` iso-mass is capped at `2·8 + 2 = 18` (the threshold/clique bound
`deg4_sum_le_eighteen`), so the lone degree-`5` hub absorbs iso-degree `≥ 3`.  This rules out the
"degree-`5` hub is poor" branch entirely: the absorber is always **rich**.
-/

namespace ACMax

open scoped Classical

namespace N18

/-- **Each hub has degree `4` or `5`.**  Immediate from `4 ≤ deg ≤ 5`. -/
theorem hub_deg45_nine_seven (G : SimpleGraph (Fin 18)) (Hub : Finset (Fin 18))
    (hdeg : ∀ h ∈ Hub, 4 ≤ G.degree h) (hdeg5 : ∀ h ∈ Hub, G.degree h ≤ 5) :
    ∀ h ∈ Hub, G.degree h = 4 ∨ G.degree h = 5 := by
  intro h hh
  have := hdeg h hh
  have := hdeg5 h hh
  omega

/-- **Exactly eight degree-`4` hubs.**  With nine hubs all of degree `4` or `5` and `∑deg = 37`, the
count of degree-`5` hubs is `37 − 4·9 = 1`, so the degree-`4` hubs number `8`. -/
theorem deg4_card_nine_seven (G : SimpleGraph (Fin 18)) (Hub : Finset (Fin 18))
    (hdeg : ∀ h ∈ Hub, 4 ≤ G.degree h) (hdeg5 : ∀ h ∈ Hub, G.degree h ≤ 5)
    (hHub : Hub.card = 9) (hdsum : ∑ w ∈ Hub, G.degree w = 37) :
    (Hub.filter (fun h => G.degree h = 4)).card = 8 := by
  classical
  set T : Finset (Fin 18) := Hub.filter (fun h => G.degree h = 4) with hT
  set R : Finset (Fin 18) := Hub.filter (fun h => ¬ G.degree h = 4) with hR
  have hcard : T.card + R.card = 9 := by
    rw [hT, hR, Finset.card_filter_add_card_filter_not, hHub]
  have hRdeg5 : ∀ v ∈ R, G.degree v = 5 := by
    intro v hv; rw [hR, Finset.mem_filter] at hv
    rcases hub_deg45_nine_seven G Hub hdeg hdeg5 v hv.1 with h4 | h5
    · exact absurd h4 hv.2
    · exact h5
  have hTdeg4 : ∀ v ∈ T, G.degree v = 4 := by
    intro v hv; rw [hT, Finset.mem_filter] at hv; exact hv.2
  have hsplit : ∑ v ∈ T, G.degree v + ∑ v ∈ R, G.degree v = ∑ w ∈ Hub, G.degree w := by
    rw [hT, hR]; exact Finset.sum_filter_add_sum_filter_not Hub _ _
  have hTsum : ∑ v ∈ T, G.degree v = 4 * T.card := by
    rw [Finset.sum_congr rfl hTdeg4, Finset.sum_const, smul_eq_mul, mul_comm]
  have hRsum : ∑ v ∈ R, G.degree v = 5 * R.card := by
    rw [Finset.sum_congr rfl hRdeg5, Finset.sum_const, smul_eq_mul, mul_comm]
  rw [hTsum, hRsum, hdsum] at hsplit
  omega

/-- **The lone degree-`5` hub is rich (iso-degree `≥ 3`).**  The total iso-incidence sum is
`∑_{Hub}|N∩Iso| = 3·7 = 21`.  Under the no-good-two-hub hypothesis the degree-`4` hubs carry at most
`2·8 + 2 = 18` of it (`deg4_sum_le_eighteen`, via the strong-hub clique bound), so the degree-`5`
hubs carry iso-degree `≥ 3`.  Since there is exactly one degree-`5` hub, *it* has iso-degree `≥ 3`. -/
theorem deg5_iso_ge_three_nine_seven (G : SimpleGraph (Fin 18)) (Hub Iso : Finset (Fin 18))
    (hdeg : ∀ h ∈ Hub, 4 ≤ G.degree h) (hdeg5 : ∀ h ∈ Hub, G.degree h ≤ 5)
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdisj : Disjoint Hub Iso) (hHub : Hub.card = 9) (hIso : Iso.card = 7)
    (hdsum : ∑ w ∈ Hub, G.degree w = 37)
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hno2hub : ¬∃ h₁ h₂ : Fin 18, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card) :
    3 ≤ ∑ v ∈ Hub.filter (fun h => ¬ G.degree h = 4), (G.neighborFinset v ∩ Iso).card := by
  classical
  have key := nogood_of_not_select_eighteen G Hub Iso hno2hub
  have hmf := strong_deg4_count_le_two_deg5_eighteen G Hub Iso hdisj hshare key
  have hTsum_le := deg4_sum_le_eighteen G Hub Iso hmf
  have hdeg4card := deg4_card_nine_seven G Hub hdeg hdeg5 hHub hdsum
  have hisoSum := hub_iso_sum_eighteen G Hub Iso hiso3
  rw [hIso] at hisoSum
  have hpart : ∑ v ∈ Hub.filter (fun h => G.degree h = 4), (G.neighborFinset v ∩ Iso).card
      + ∑ v ∈ Hub.filter (fun h => ¬ G.degree h = 4), (G.neighborFinset v ∩ Iso).card
      = ∑ v ∈ Hub, (G.neighborFinset v ∩ Iso).card :=
    Finset.sum_filter_add_sum_filter_not Hub (fun h => G.degree h = 4) _
  rw [hdeg4card] at hTsum_le
  omega

end N18

end ACMax
