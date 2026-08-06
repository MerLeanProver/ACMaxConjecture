import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N18.Core
import ACMaxConjecture.SmallCases.N18.TwoHubSelect
import ACMaxConjecture.SmallCases.N18.StarTriangleStruct
import ACMaxConjecture.SmallCases.N18.RichCount
import ACMaxConjecture.SmallCases.N18.Align8Helpers
import ACMaxConjecture.SmallCases.N18.ZPoorN3
import ACMaxConjecture.SmallCases.N18.ZPoorR7
import ACMaxConjecture.SmallCases.N18.ZVertex
import ACMaxConjecture.SmallCases.N18.ZPoorR6Dist

/-!
# The `r = 6`, `S = 14` rich-neighbour saturation of the `M`-partner (`n = 18`)

For the tight `e(M) = 1`, all-degree-`4`, `(|Hub|, |Iso|) = (10, 6)` profile with six rich hubs and
rich iso-incidence sum `S = 14`, a rich hub `a` adjacent to an `M`-edge endpoint `zp` (and not to its
partner `z`) has iso-degree exactly `2` and exactly one hub-neighbour.  This rules out a rich
neighbour of `zp` carrying iso-degree `3` (it would either not exist, in the `{4,2,2,2,2,2}` design,
or be forced adjacent to the second iso-degree-`3` hub by the `R₃`-clique, exceeding degree `4`).
-/

namespace ACMax

open scoped Classical

namespace N18

/-- **A rich neighbour of an `M`-endpoint is saturated to iso-degree `2`.**  Let `a` be a rich hub
(iso-degree `≥ 2`, degree `4`) adjacent to the `M`-endpoint `zp` but not to its partner `z`.  Then
`a`'s only `M`-endpoint neighbour is `zp`, so `|N(a) ∩ Hub| + |N(a) ∩ Iso| = 3`.  The `R₃`-clique
distribution forces `|N(a) ∩ Iso| = 2`, hence `|N(a) ∩ Hub| = 1`. -/
theorem rich_inA_saturated_S14 (G : SimpleGraph (Fin 18)) (Hub Iso : Finset (Fin 18))
    (hdeg4 : ∀ h ∈ Hub, G.degree h = 4) (hdisj : Disjoint Hub Iso)
    (hHub : Hub.card = 10) (hIso : Iso.card = 6)
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hno2hub : ¬∃ h₁ h₂ : Fin 18, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card)
    (hr6 : (Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)).card = 6)
    (hS14 : ∑ r ∈ Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card),
        (G.neighborFinset r ∩ Iso).card = 14)
    (z zp : Fin 18) (hz : z ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 18)))
    (hzp : zp ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 18))) (hzzp : z ≠ zp)
    (a : Fin 18) (haHub : a ∈ Hub) (harich : 2 ≤ (G.neighborFinset a ∩ Iso).card)
    (hza : ¬G.Adj z a) (hzpa : G.Adj zp a) :
    (G.neighborFinset a ∩ Iso).card = 2 ∧ (G.neighborFinset a ∩ Hub).card = 1 := by
  classical
  set Z : Finset (Fin 18) := Finset.univ \ (Hub ∪ Iso) with hZdef
  set R : Finset (Fin 18) := Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card) with hRdef
  have hRHub : R ⊆ Hub := Finset.filter_subset _ _
  have hRrich : ∀ x ∈ R, 2 ≤ (G.neighborFinset x ∩ Iso).card := by
    intro x hx; rw [hRdef, Finset.mem_filter] at hx; exact hx.2
  have haR : a ∈ R := by rw [hRdef, Finset.mem_filter]; exact ⟨haHub, harich⟩
  -- `Z = {z, zp}`.
  have hZcard : Z.card = 2 := z_card_two_eighteen Hub Iso hdisj hHub hIso
  have hzZ : z ∈ Z := hz
  have hzpZ : zp ∈ Z := hzp
  have hZpair : Z = {z, zp} := by
    refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hzZ
      · rw [Finset.mem_singleton] at hx; subst hx; exact hzpZ
    · rw [hZcard, Finset.card_insert_of_notMem (by simp [hzzp]), Finset.card_singleton]
  -- `N(a) ∩ Z = {zp}`.
  have hZpart : (G.neighborFinset a ∩ Z).card = 1 := by
    have hsub : G.neighborFinset a ∩ Z ⊆ {zp} := by
      intro x hx
      rw [Finset.mem_inter] at hx
      have hxZ : x ∈ Z := hx.2
      rw [hZpair, Finset.mem_insert, Finset.mem_singleton] at hxZ
      rw [Finset.mem_singleton]
      rcases hxZ with rfl | rfl
      · exfalso
        exact hza ((G.mem_neighborFinset a x).mp hx.1).symm
      · rfl
    have hzpin : zp ∈ G.neighborFinset a ∩ Z :=
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset a zp).mpr hzpa.symm, hzpZ⟩
    have h1 : 1 ≤ (G.neighborFinset a ∩ Z).card := Finset.card_pos.mpr ⟨zp, hzpin⟩
    have h2 : (G.neighborFinset a ∩ Z).card ≤ 1 := by
      have := Finset.card_le_card hsub; rw [Finset.card_singleton] at this; exact this
    omega
  -- Degree split: hub + iso + Z = 4.
  have hsplit := nbr_split_three_eighteen G Hub Iso hdisj a
  rw [← hZdef, hZpart, hdeg4 a haHub] at hsplit
  -- So `iso(a) + hub(a) = 3`, with `iso(a) ≥ 2`, hence `iso(a) ∈ {2, 3}`.
  -- Exclude `iso(a) = 3` via the `R₃`-clique distribution.
  have hiso2 : (G.neighborFinset a ∩ Iso).card = 2 := by
    by_contra hne
    have ha3 : 3 ≤ (G.neighborFinset a ∩ Iso).card := by omega
    have hhub0 : (G.neighborFinset a ∩ Hub).card = 0 := by omega
    -- `a` has no hub-neighbour; but the distribution forces an iso-degree-`3` hub to have one.
    rcases rich_isodeg_dist_six_S14 G Hub Iso R hdeg4 hRHub hRrich hr6 hS14 with
      ⟨w, hwR, hw4, hwoth⟩ | ⟨w₁, hw1R, w₂, hw2R, hw12, hw13, hw23, hwoth⟩
    · -- Design `{4,2,2,2,2,2}`: every rich hub other than `w` has iso-degree `2`, none has `3`.
      by_cases haw : a = w
      · subst haw; omega
      · have := hwoth a haR haw; omega
    · -- Design `{3,3,2,2,2,2}`: `a` is one of `w₁, w₂` (iso-deg `3`), adjacent to the other.
      have haIs3 : a = w₁ ∨ a = w₂ := by
        by_contra hcon
        push Not at hcon
        have := hwoth a haR hcon.1 hcon.2; omega
      have hother : ∃ b ∈ R, b ≠ a ∧ 3 ≤ (G.neighborFinset b ∩ Iso).card := by
        rcases haIs3 with rfl | rfl
        · exact ⟨w₂, hw2R, fun he => hw12 he.symm, by omega⟩
        · exact ⟨w₁, hw1R, hw12, by omega⟩
      obtain ⟨b, hbR, hba, hb3⟩ := hother
      have hadj : G.Adj a b := rich3_clique_S14 G Hub Iso hdeg4 hshare hno2hub a b haHub
        (hRHub hbR) (Ne.symm hba) ha3 hb3
      -- `b` is a hub-neighbour of `a`, contradicting `hub(a) = 0`.
      have hbin : b ∈ G.neighborFinset a ∩ Hub :=
        Finset.mem_inter.mpr ⟨(G.mem_neighborFinset a b).mpr hadj, hRHub hbR⟩
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem] at hhub0
      exact hhub0 b hbin
  exact ⟨hiso2, by omega⟩

end N18

end ACMax
