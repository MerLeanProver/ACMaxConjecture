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
import ACMaxConjecture.SmallCases.N18.ZPoorR6Poor
import ACMaxConjecture.SmallCases.N18.ZPoorR6HubAdj

/-!
# Design A (`{4,2,2,2,2,2}`) subcase counting bridge for the `r = 6`, `S = 14` core (`n = 18`)

A single reusable counting inequality bridging the within-`Rich` hub-edge mass (the engine output)
to the `e(Hub, Hub) = 9` within-`O` cut (`O = Hub \ T`): for any `Rich ⊆ Hub` and any `T`, the
ordered within-`Rich` degree sum is bounded by the within-`O` cut plus twice the hub-degrees of the
`Rich`-vertices that lie in `T`.  Instantiated per subcase (`T = {hg₁, hg₂, d₁, d₂}`) this collides
with the engine bound `≥ 8`.
-/

namespace ACMax

open scoped Classical

namespace N18

/-- **Rich-internal mass is bounded by the `O`-cut plus the in-`T` rich hub-degrees.**  For
`Rich ⊆ Hub` and any `T`, with `O = Hub \ T`, the ordered within-`Rich` degree sum is at most the
within-`O` degree sum plus twice the hub-degrees of the `Rich`-vertices inside `T`. -/
theorem rich_internal_le_cut (G : SimpleGraph (Fin 18)) (Hub Rich T : Finset (Fin 18))
    (hRsubHub : Rich ⊆ Hub) :
    ∑ r ∈ Rich, (G.neighborFinset r ∩ Rich).card
      ≤ (∑ v ∈ Hub \ T, (G.neighborFinset v ∩ (Hub \ T)).card)
        + 2 * ∑ d ∈ Rich ∩ T, (G.neighborFinset d ∩ Hub).card := by
  classical
  set O : Finset (Fin 18) := Hub \ T with hO
  have hper : ∀ r ∈ Rich, (G.neighborFinset r ∩ Rich).card
      ≤ (G.neighborFinset r ∩ O).card + (G.neighborFinset r ∩ (Rich ∩ T)).card := by
    intro r _
    have hsub : G.neighborFinset r ∩ Rich
        ⊆ (G.neighborFinset r ∩ O) ∪ (G.neighborFinset r ∩ (Rich ∩ T)) := by
      intro x hx
      rw [Finset.mem_inter] at hx
      obtain ⟨hxN, hxR⟩ := hx
      rw [Finset.mem_union, Finset.mem_inter, Finset.mem_inter]
      by_cases hxT : x ∈ T
      · exact Or.inr ⟨hxN, Finset.mem_inter.mpr ⟨hxR, hxT⟩⟩
      · exact Or.inl ⟨hxN, by rw [hO, Finset.mem_sdiff]; exact ⟨hRsubHub hxR, hxT⟩⟩
    calc (G.neighborFinset r ∩ Rich).card
        ≤ ((G.neighborFinset r ∩ O) ∪ (G.neighborFinset r ∩ (Rich ∩ T))).card :=
          Finset.card_le_card hsub
      _ ≤ (G.neighborFinset r ∩ O).card + (G.neighborFinset r ∩ (Rich ∩ T)).card :=
          Finset.card_union_le _ _
  have hA : ∑ r ∈ Rich, (G.neighborFinset r ∩ O).card
      ≤ (∑ v ∈ O, (G.neighborFinset v ∩ O).card)
        + ∑ d ∈ Rich ∩ T, (G.neighborFinset d ∩ Hub).card := by
    have hsub : Rich ⊆ O ∪ (Rich ∩ T) := by
      intro r hr
      rw [Finset.mem_union]
      by_cases hrT : r ∈ T
      · exact Or.inr (Finset.mem_inter.mpr ⟨hr, hrT⟩)
      · exact Or.inl (by rw [hO, Finset.mem_sdiff]; exact ⟨hRsubHub hr, hrT⟩)
    have h1 : ∑ r ∈ Rich, (G.neighborFinset r ∩ O).card
        ≤ ∑ r ∈ O ∪ (Rich ∩ T), (G.neighborFinset r ∩ O).card :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)
    have hui := Finset.sum_union_inter (s₁ := O) (s₂ := Rich ∩ T)
      (f := fun r => (G.neighborFinset r ∩ O).card)
    have h2 : ∑ d ∈ Rich ∩ T, (G.neighborFinset d ∩ O).card
        ≤ ∑ d ∈ Rich ∩ T, (G.neighborFinset d ∩ Hub).card :=
      Finset.sum_le_sum (fun d _ => Finset.card_le_card
        (Finset.inter_subset_inter subset_rfl (hO ▸ Finset.sdiff_subset)))
    omega
  have hB : ∑ r ∈ Rich, (G.neighborFinset r ∩ (Rich ∩ T)).card
      ≤ ∑ d ∈ Rich ∩ T, (G.neighborFinset d ∩ Hub).card := by
    rw [cross_count G Rich (Rich ∩ T)]
    exact Finset.sum_le_sum (fun d _ => Finset.card_le_card
      (Finset.inter_subset_inter subset_rfl hRsubHub))
  calc ∑ r ∈ Rich, (G.neighborFinset r ∩ Rich).card
      ≤ ∑ r ∈ Rich, ((G.neighborFinset r ∩ O).card + (G.neighborFinset r ∩ (Rich ∩ T)).card) :=
        Finset.sum_le_sum hper
    _ = (∑ r ∈ Rich, (G.neighborFinset r ∩ O).card)
        + ∑ r ∈ Rich, (G.neighborFinset r ∩ (Rich ∩ T)).card := Finset.sum_add_distrib
    _ ≤ _ := by omega

end N18

end ACMax
