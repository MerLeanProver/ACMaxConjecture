import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N17.Core
import ACMaxConjecture.SmallCases.Certificates
import ACMaxConjecture.SmallCases.N17.TwoHubSelect

/-!
# Degree-`6`-aware two-hub corner selection for `n = 17` (`|D| = 10` regime)

This file supplies `two_hub_deg6_select_seventeen`, the hub-pair *selection* lemma for the one
two-hub `e(M) ≤ 1` corner that the degree-`5`-restricted selector
(`two_hub_corner_select_deg5_seventeen`) misses: `|D| = 10`, `|Hub| = 7`, `∑_{Hub} deg = 30`, with a
single **degree-`6`** hub (excess `2`, so `hdeg5` — degree `≤ 5` — fails).

The good-`C₄` share bound `nonadj_hubs_share_le_one_iso` fails for a pair touching a degree-`≥ 5`
hub, so as in the degree-`5` file we route the selection through the **degree-`4`-restricted** share
(`hshare`), feeding the shared `strong_deg4_count_le_two_deg5_seventeen` / `deg4_sum_le_seventeen`
engine.  The degree-`6` hub is absorbed by bounding the residual hubs `R = {h ∈ Hub : deg ≠ 4}`
*directly by their degree* (`∑_R isoDeg ≤ ∑_R deg`) rather than via the `deg = 5` shape used in
`residual_arith`.  Since every `R`-hub has degree `≥ 5`, the constraint `5·|R| ≤ ∑_R deg = 30 − 4·|T|`
forces `|T| ≥ 5`, whence
`3·|Iso| = ∑_{Hub} isoDeg ≤ (2·|T| + 2) + ∑_R deg = 32 − 2·|T| ≤ 22`, i.e. `|Iso| ≤ 7`, contradicting
both corner values `|Iso| ∈ {8, 10}`.  The selection therefore cannot be refuted. -/

namespace ACMax

open scoped Classical

namespace N17

/-- **Hub-pair selection for the `n = 17` degree-`6` two-hub corner.**  In the `|Hub| = 7`,
`∑deg = 30` corner with `|Iso| ∈ {8, 10}` (the regime where one hub may have degree `6`, so `hdeg6`
replaces the degree-`5` cap), with each `M`-isolated twin meeting exactly three hubs (`hiso3`) and
the good-`C₄` share `≤ 1` for **degree-`4`** hub pairs (`hshare`), there exist two non-adjacent
degree-`4` hubs each retaining `≥ 2` private `M`-isolated twins.  Routes around the degree-`6` hub by
bounding the residual hubs by their degree. -/
theorem two_hub_deg6_select_seventeen (G : SimpleGraph (Fin 17)) (Hub Iso : Finset (Fin 17))
    (hdeg : ∀ h ∈ Hub, 4 ≤ G.degree h) (hdeg6 : ∀ h ∈ Hub, G.degree h ≤ 6)
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hdisj : Disjoint Hub Iso)
    (hregime :
      (Hub.card = 7 ∧ Iso.card = 10 ∧ ∑ w ∈ Hub, G.degree w = 30) ∨
      (Hub.card = 7 ∧ Iso.card = 8 ∧ ∑ w ∈ Hub, G.degree w = 30)) :
    ∃ h₁ h₂ : Fin 17, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card := by
  classical
  by_contra hcon
  have key := nogood_of_not_select_seventeen G Hub Iso hcon
  have hmf := strong_deg4_count_le_two_deg5_seventeen G Hub Iso hdisj hshare key
  have hisoSum := hub_iso_sum_seventeen G Hub Iso hiso3
  have hTsum_le := deg4_sum_le_seventeen G Hub Iso hmf
  set T : Finset (Fin 17) := Hub.filter (fun h => G.degree h = 4) with hT
  set R : Finset (Fin 17) := Hub.filter (fun h => ¬ G.degree h = 4) with hR
  have hpartIso : ∑ v ∈ T, (G.neighborFinset v ∩ Iso).card
      + ∑ v ∈ R, (G.neighborFinset v ∩ Iso).card = ∑ v ∈ Hub, (G.neighborFinset v ∩ Iso).card :=
    Finset.sum_filter_add_sum_filter_not Hub (fun h => G.degree h = 4) _
  have hRdeg5ge : ∀ v ∈ R, 5 ≤ G.degree v := by
    intro v hv; rw [hR, Finset.mem_filter] at hv
    have := hdeg v hv.1; omega
  have hRiso_le : ∑ v ∈ R, (G.neighborFinset v ∩ Iso).card ≤ ∑ v ∈ R, G.degree v := by
    apply Finset.sum_le_sum
    intro v _
    rw [← G.card_neighborFinset_eq_degree]; exact Finset.card_le_card Finset.inter_subset_left
  have hpartDeg : ∑ v ∈ T, G.degree v + ∑ v ∈ R, G.degree v = ∑ v ∈ Hub, G.degree v :=
    Finset.sum_filter_add_sum_filter_not Hub (fun h => G.degree h = 4) _
  have hTdeg : ∑ v ∈ T, G.degree v = 4 * T.card := by
    rw [Finset.sum_congr rfl (fun x hx => (Finset.mem_filter.mp hx).2), Finset.sum_const,
      smul_eq_mul, mul_comm]
  have hRdeg_ge : 5 * R.card ≤ ∑ v ∈ R, G.degree v := by
    calc 5 * R.card = ∑ _v ∈ R, 5 := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ ∑ v ∈ R, G.degree v := Finset.sum_le_sum (fun v hv => hRdeg5ge v hv)
  have hRdeg_le : ∑ v ∈ R, G.degree v ≤ 6 * R.card := by
    have hle6 : ∀ v ∈ R, G.degree v ≤ 6 := by
      intro v hv; rw [hR, Finset.mem_filter] at hv; exact hdeg6 v hv.1
    calc ∑ v ∈ R, G.degree v ≤ ∑ _v ∈ R, 6 := Finset.sum_le_sum hle6
      _ = 6 * R.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have hcard : T.card + R.card = Hub.card :=
    Finset.card_filter_add_card_filter_not (fun h => G.degree h = 4)
  rcases hregime with ⟨hHub, hIso, hdsum⟩ | ⟨hHub, hIso, hdsum⟩ <;> omega

end N17

end ACMax
