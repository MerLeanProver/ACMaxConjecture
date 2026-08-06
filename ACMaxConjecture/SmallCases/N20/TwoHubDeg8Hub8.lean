import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N20.Core
import ACMaxConjecture.SmallCases.N20.Core
import ACMaxConjecture.SmallCases.StarCertificates
import ACMaxConjecture.SmallCases.N20.TwoHubSelect

/-!
# Degree-`≥ 6`-aware two-hub corner selection for `n = 20` (`|Hub| = 8` regime)

This file supplies `two_hub_deg8_select_hub8_twenty`, the hub-pair *selection* lemma for the
two-hub `s ≤ 2` corner with `|Hub| = 8`, `∑_{Hub} deg = 36` and a **degree-`≥ 6`** hub (excess
`4`; the all-degree-`≤ 5` sub-corner is dispatched by the degree-`5` selector, so here a
degree-`≥ 6` hub is guaranteed by `hex6`).  With `hdeg8` capping degrees at `8`, the splits with a
degree-`≥ 6` hub are `8+7·4`, `7+5+6·4`, `6+6+6·4`, `6+5+5+5·4` (all excess `4`).

As in `two_hub_deg6_select_hub8_nineteen` we route the selection through the **degree-`4`-restricted**
share (`hshare`), feeding the shared `strong_deg4_count_le_two_deg5_twenty` / `deg4_sum_le_twenty`
engine, and bound the residual hubs `R = {h ∈ Hub : deg ≠ 4}` directly by their degree
(`∑_R isoDeg ≤ ∑_R deg`).  The excess-`4` budget with the **witnessed** degree-`≥ 6` hub pins `R`
down: `∑_R deg = 36 − 4·|T|`, while the witness forces `∑_R deg ≥ 6 + 5·(|R| − 1)`, whence
`|T| ≥ 5` (equivalently `|R| ≤ 3`).  Meanwhile the counting
`3·|Iso| = ∑_{Hub} isoDeg ≤ (2·|T| + 2) + ∑_R deg = 38 − 2·|T|` caps `|T| ≤ 4` when `|Iso| = 10`
and `|T| ≤ 1` when `|Iso| = 12`, both contradicting `|T| ≥ 5`.  The selection therefore cannot be
refuted, and the good degree-`4` pair (the first disjunct) exists. -/

namespace ACMax

open scoped Classical

namespace N20

/-- **Hub-pair selection for the `n = 20` degree-`≥ 6` `|Hub| = 8` two-hub corner.**  In the
`|Hub| = 8`, `∑deg = 36` corner with `|Iso| ∈ {10, 12}` and a witnessed degree-`≥ 6` hub
(`hex6`), each `M`-isolated twin meeting exactly three hubs (`hiso3`) and the good-`C₄` share
`≤ 1` for **degree-`4`** hub pairs (`hshare`), there exist two non-adjacent degree-`4` hubs each
retaining `≥ 2` private `M`-isolated twins.  Routes around the fat hub by bounding the residual
hubs by their degree and pinning `|T| ≥ 5` via the degree-`≥ 6` witness; the config disjuncts
remain unused because the pair argument closes by a pure counting contradiction. -/
theorem two_hub_deg8_select_hub8_twenty (G : SimpleGraph (Fin 20)) (Hub Iso : Finset (Fin 20))
    (hdeg : ∀ h ∈ Hub, 4 ≤ G.degree h) (_hdeg8 : ∀ h ∈ Hub, G.degree h ≤ 8)
    (hex6 : ∃ h ∈ Hub, 6 ≤ G.degree h)
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hdisj : Disjoint Hub Iso)
    (hregime :
      (Hub.card = 8 ∧ Iso.card = 12 ∧ ∑ w ∈ Hub, G.degree w = 36) ∨
      (Hub.card = 8 ∧ Iso.card = 10 ∧ ∑ w ∈ Hub, G.degree w = 36)) :
    (∃ h₁ h₂ : Fin 20, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card) ∨
      SingleVertexConfig G ∨ TwoTwinConfig G ∨ TwoHubConfig G ∨ HubTriangleConfig G := by
  classical
  refine Or.inl ?_
  by_contra hcon
  have key := nogood_of_not_select_twenty G Hub Iso hcon
  have hmf := strong_deg4_count_le_two_deg5_twenty G Hub Iso hdisj hshare key
  have hisoSum := hub_iso_sum_twenty G Hub Iso hiso3
  have hTsum_le := deg4_sum_le_twenty G Hub Iso hmf
  set T : Finset (Fin 20) := Hub.filter (fun h => G.degree h = 4) with hT
  set R : Finset (Fin 20) := Hub.filter (fun h => ¬ G.degree h = 4) with hR
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
  have hcard : T.card + R.card = Hub.card :=
    Finset.card_filter_add_card_filter_not (fun h => G.degree h = 4)
  obtain ⟨w, hwHub, hwge⟩ := hex6
  have hwR : w ∈ R := by rw [hR, Finset.mem_filter]; exact ⟨hwHub, by omega⟩
  have hRpos : 1 ≤ R.card := Finset.card_pos.mpr ⟨w, hwR⟩
  have herase := Finset.add_sum_erase R (fun v => G.degree v) hwR
  have hEcard : (R.erase w).card = R.card - 1 := Finset.card_erase_of_mem hwR
  have hEge : 5 * (R.erase w).card ≤ ∑ v ∈ R.erase w, G.degree v := by
    calc 5 * (R.erase w).card = ∑ _v ∈ R.erase w, 5 := by
          rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ ∑ v ∈ R.erase w, G.degree v :=
          Finset.sum_le_sum (fun v hv => hRdeg5ge v (Finset.mem_of_mem_erase hv))
  rcases hregime with ⟨hHub, hIso, hdsum⟩ | ⟨hHub, hIso, hdsum⟩ <;> omega

end N20

end ACMax
