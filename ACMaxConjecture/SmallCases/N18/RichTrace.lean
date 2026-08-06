import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N18.Core
import ACMaxConjecture.SmallCases.N18.TwoHubSelect
import ACMaxConjecture.SmallCases.N18.StarTriangleStruct

/-!
# Trace-counting foundations for the `r ≠ 7` rich-count argument (`n = 18`)

For the tight `e(M) = 1`, all-degree-`4`, `(|Hub|, |Iso|) = (10, 6)` profile, the *rich* hubs are
those meeting `≥ 2` `M`-isolated twins.  The crux fact `rich_count_ne_seven_eighteen` rules out
`|R| = 7`.  This file isolates the genuinely-clean counting facts that feed that argument:

* `rich_iso_sum_ge_fifteen_eighteen` — with `|R| = 7` the rich iso-incidence sum is `≥ 15`: the
  three poor hubs carry iso-degree `≤ 1` each, so they absorb `≤ 3` of the `18` total incidences.
* `two_iso_four_hubs_impossible_eighteen` — two distinct degree-`4` hubs each with *all four*
  neighbours among the `M`-isolated twins (iso-degree `4`) and sharing `≤ 1` twin would force
  `≥ 7` twins, impossible when `|Iso| = 6`.  This closes the densest `∑_R isoDeg = 18` sub-profile
  of the `r = 7` analysis.

These are the load-bearing clean steps; the remaining tight sub-profiles
(`∑_R isoDeg ∈ {15, 16, 17}`) require the trace–`C₄` extraction that resists the abstract budget.
-/

namespace ACMax

open scoped Classical

namespace N18

/-- **`r = 7 ⟹ ∑_R isoDeg ≥ 15`.**  The total iso-incidence sum over the ten hubs is
`3·|Iso| = 18`.  The three *poor* hubs (`Hub \ R`, each with iso-degree `< 2`, hence `≤ 1`) absorb at
most `3`, so the seven rich hubs carry `≥ 15`. -/
theorem rich_iso_sum_ge_fifteen_eighteen (G : SimpleGraph (Fin 18)) (Hub Iso : Finset (Fin 18))
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hHub : Hub.card = 10) (hIso : Iso.card = 6)
    (hr7 : (Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)).card = 7) :
    15 ≤ ∑ r ∈ Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card),
          (G.neighborFinset r ∩ Iso).card := by
  classical
  set R : Finset (Fin 18) := Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card) with hRdef
  set P : Finset (Fin 18) := Hub.filter (fun h => ¬ 2 ≤ (G.neighborFinset h ∩ Iso).card) with hPdef
  have hsum18 : ∑ h ∈ Hub, (G.neighborFinset h ∩ Iso).card = 18 := by
    have := hub_iso_sum_eighteen G Hub Iso hiso3; rw [hIso] at this; omega
  have hsplit : ∑ a ∈ R, (G.neighborFinset a ∩ Iso).card
      + ∑ a ∈ P, (G.neighborFinset a ∩ Iso).card = 18 := by
    rw [hRdef, hPdef,
      Finset.sum_filter_add_sum_filter_not Hub (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)]
    exact hsum18
  have hPcard : P.card = 3 := by
    have := Finset.card_filter_add_card_filter_not
      (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card) (s := Hub)
    rw [← hRdef, ← hPdef, hHub, hr7] at this; omega
  have hpoorle : ∑ a ∈ P, (G.neighborFinset a ∩ Iso).card ≤ 3 := by
    calc ∑ a ∈ P, (G.neighborFinset a ∩ Iso).card ≤ ∑ _a ∈ P, 1 := by
          apply Finset.sum_le_sum
          intro a ha; rw [hPdef, Finset.mem_filter] at ha; omega
      _ = 3 := by rw [Finset.sum_const, hPcard, smul_eq_mul, mul_one]
  omega

/-- **Two iso-degree-`4` hubs are impossible (`|Iso| = 6`).**  If two distinct degree-`4` hubs
`a, b` each meet *all four* of their neighbours inside `Iso` (iso-degree `4`) and share at most one
`M`-isolated twin, then `|N(a) ∩ Iso ∪ N(b) ∩ Iso| ≥ 4 + 4 − 1 = 7`, exceeding `|Iso| = 6`.  This
rules out the densest `∑_R isoDeg = 18` sub-profile of the `r = 7` analysis (two iso-degree-`4`
rich hubs). -/
theorem two_iso_four_hubs_impossible_eighteen (G : SimpleGraph (Fin 18)) (Iso : Finset (Fin 18))
    (hIso : Iso.card = 6) (a b : Fin 18)
    (ha4 : (G.neighborFinset a ∩ Iso).card = 4) (hb4 : (G.neighborFinset b ∩ Iso).card = 4)
    (hshare : (G.neighborFinset a ∩ G.neighborFinset b ∩ Iso).card ≤ 1) :
    False := by
  classical
  -- Both iso-traces live in `Iso`; their union therefore has `≤ 6` elements.
  have hunionsub : (G.neighborFinset a ∩ Iso) ∪ (G.neighborFinset b ∩ Iso) ⊆ Iso := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx <;> exact (Finset.mem_inter.mp hx).2
  have hunionle : ((G.neighborFinset a ∩ Iso) ∪ (G.neighborFinset b ∩ Iso)).card ≤ 6 := by
    calc ((G.neighborFinset a ∩ Iso) ∪ (G.neighborFinset b ∩ Iso)).card
        ≤ Iso.card := Finset.card_le_card hunionsub
      _ = 6 := hIso
  -- Inclusion–exclusion with the shared-twin bound forces the union to be `≥ 7`.
  have hinter : (G.neighborFinset a ∩ Iso) ∩ (G.neighborFinset b ∩ Iso)
      = G.neighborFinset a ∩ G.neighborFinset b ∩ Iso := by
    ext x; simp only [Finset.mem_inter]; tauto
  have hIE := Finset.card_union_add_card_inter
    (G.neighborFinset a ∩ Iso) (G.neighborFinset b ∩ Iso)
  rw [hinter] at hIE
  omega

end N18

end ACMax
