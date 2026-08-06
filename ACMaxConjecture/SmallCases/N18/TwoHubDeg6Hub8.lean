import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N18.Core
import ACMaxConjecture.SmallCases.Certificates
import ACMaxConjecture.SmallCases.N18.TwoHubSelect

/-!
# Degree-`6`-aware two-hub corner selection for `n = 18` (`|D| = 10`, `|Hub| = 8` regime)

This file supplies `two_hub_deg6_select_hub8_eighteen`, the hub-pair *selection* lemma for the
two-hub `e(M) ≤ 1` corner with `|D| = 10`, `|Hub| = 8`, `∑_{Hub} deg = 34` and a single
**degree-`6`** hub (excess `2`; the degree-`≤ 5` sub-corner is dispatched by the degree-`5`
selector, so here `hdeg5` fails and a degree-`6` hub is guaranteed by `hdeg6ex`).

As in `two_hub_deg6_select_eighteen` we route the selection through the **degree-`4`-restricted**
share (`hshare`), feeding the shared `strong_deg4_count_le_two_deg5_eighteen` /
`deg4_sum_le_eighteen` engine, and bound the residual hubs `R = {h ∈ Hub : deg ≠ 4}` directly by
their degree (`∑_R isoDeg ≤ ∑_R deg`).  The excess-`2` budget with the **witnessed** degree-`6` hub
pins `R` down: `∑_R deg = 34 − 4·|T| = 2 + 4·|R|`, while the degree-`6` witness forces
`∑_R deg ≥ 6 + 5·(|R| − 1)`, whence `|R| ≤ 1`, so `|R| = 1` and `∑_R deg = 6`.  Then
`3·|Iso| = ∑_{Hub} isoDeg ≤ (2·|T| + 2) + ∑_R deg = 22`, i.e. `|Iso| ≤ 7`, contradicting both corner
values `|Iso| ∈ {8, 10}`.  The selection therefore cannot be refuted. -/

namespace ACMax

open scoped Classical

namespace N18

/-- **Hub-pair selection for the `n = 18` degree-`6` `|Hub| = 8` two-hub corner.**  In the
`|Hub| = 8`, `∑deg = 34` corner with `|Iso| ∈ {8, 10}` and a witnessed degree-`6` hub
(`hdeg6ex`), each `M`-isolated twin meeting exactly three hubs (`hiso3`) and the good-`C₄` share
`≤ 1` for **degree-`4`** hub pairs (`hshare`), there exist two non-adjacent degree-`4` hubs each
retaining `≥ 2` private `M`-isolated twins.  Routes around the degree-`6` hub by bounding the
residual hubs by their degree and pinning `|R| = 1` via the witness. -/
theorem two_hub_deg6_select_hub8_eighteen (G : SimpleGraph (Fin 18)) (Hub Iso : Finset (Fin 18))
    (hdeg : ∀ h ∈ Hub, 4 ≤ G.degree h) (_hdeg6 : ∀ h ∈ Hub, G.degree h ≤ 6)
    (hdeg6ex : ∃ h ∈ Hub, G.degree h = 6)
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hdisj : Disjoint Hub Iso)
    (hregime :
      (Hub.card = 8 ∧ Iso.card = 10 ∧ ∑ w ∈ Hub, G.degree w = 34) ∨
      (Hub.card = 8 ∧ Iso.card = 8 ∧ ∑ w ∈ Hub, G.degree w = 34)) :
    ∃ h₁ h₂ : Fin 18, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card := by
  classical
  by_contra hcon
  have key := nogood_of_not_select_eighteen G Hub Iso hcon
  have hmf := strong_deg4_count_le_two_deg5_eighteen G Hub Iso hdisj hshare key
  have hisoSum := hub_iso_sum_eighteen G Hub Iso hiso3
  have hTsum_le := deg4_sum_le_eighteen G Hub Iso hmf
  set T : Finset (Fin 18) := Hub.filter (fun h => G.degree h = 4) with hT
  set R : Finset (Fin 18) := Hub.filter (fun h => ¬ G.degree h = 4) with hR
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
  obtain ⟨w, hwHub, hwdeg⟩ := hdeg6ex
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

end N18

end ACMax
