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

/-!
# The `r = 6`, `S = 14` rich iso-degree distribution and `R₃`-clique (`n = 18`)

For the tight `e(M) = 1`, all-degree-`4`, `(|Hub|, |Iso|) = (10, 6)` profile with six rich hubs and
rich iso-incidence sum `S = 14`, the rich iso-degrees carry excess `2` over the base `2`, so the
multiset of the six rich iso-degrees is either `{4, 2, 2, 2, 2, 2}` or `{3, 3, 2, 2, 2, 2}`.  This
file isolates that dichotomy together with the `R₃`-clique structure of the iso-degree-`≥ 3` rich
hubs.
-/

namespace ACMax

open scoped Classical

namespace N18

/-- **The six rich iso-degrees at `r = 6`, `S = 14` (LEAF).**  Each rich hub has iso-degree in
`[2, 4]` (degree `4`, at least two `M`-isolated twins), and the six values sum to `14`, i.e. carry
total excess `2` over the base `2`.  Hence the multiset of rich iso-degrees is either
`{4, 2, 2, 2, 2, 2}` (one hub with excess `2`) or `{3, 3, 2, 2, 2, 2}` (two hubs with excess `1`). -/
theorem rich_isodeg_dist_six_S14 (G : SimpleGraph (Fin 18)) (Hub Iso R : Finset (Fin 18))
    (hdeg4 : ∀ h ∈ Hub, G.degree h = 4) (hRHub : R ⊆ Hub)
    (hRrich : ∀ a ∈ R, 2 ≤ (G.neighborFinset a ∩ Iso).card)
    (hr6 : R.card = 6) (hS14 : ∑ r ∈ R, (G.neighborFinset r ∩ Iso).card = 14) :
    (∃ w ∈ R, (G.neighborFinset w ∩ Iso).card = 4 ∧
        ∀ r ∈ R, r ≠ w → (G.neighborFinset r ∩ Iso).card = 2) ∨
    (∃ w₁ ∈ R, ∃ w₂ ∈ R, w₁ ≠ w₂ ∧ (G.neighborFinset w₁ ∩ Iso).card = 3 ∧
        (G.neighborFinset w₂ ∩ Iso).card = 3 ∧
        ∀ r ∈ R, r ≠ w₁ → r ≠ w₂ → (G.neighborFinset r ∩ Iso).card = 2) := by
  classical
  -- Iso-degree is at most `4` (bounded by the degree).
  have hle4 : ∀ r ∈ R, (G.neighborFinset r ∩ Iso).card ≤ 4 := by
    intro r hr
    have hsub : G.neighborFinset r ∩ Iso ⊆ G.neighborFinset r := Finset.inter_subset_left
    have := Finset.card_le_card hsub
    rw [G.card_neighborFinset_eq_degree, hdeg4 r (hRHub hr)] at this
    exact this
  -- The excess sum is `2`.
  have hexcess : ∑ r ∈ R, ((G.neighborFinset r ∩ Iso).card - 2) = 2 := by
    have hback : ∑ r ∈ R, (((G.neighborFinset r ∩ Iso).card - 2) + 2)
        = ∑ r ∈ R, (G.neighborFinset r ∩ Iso).card := by
      apply Finset.sum_congr rfl
      intro r hr; have := hRrich r hr; omega
    rw [Finset.sum_add_distrib, Finset.sum_const, hr6, smul_eq_mul] at hback
    omega
  by_cases hfour : ∃ w ∈ R, (G.neighborFinset w ∩ Iso).card = 4
  · -- A hub with iso-degree `4`: the rest are `2`.
    obtain ⟨w, hwR, hw4⟩ := hfour
    left
    refine ⟨w, hwR, hw4, ?_⟩
    intro r hrR hrw
    have hsplit := Finset.add_sum_erase R
      (fun x => (G.neighborFinset x ∩ Iso).card - 2) hwR
    have hwexc : (G.neighborFinset w ∩ Iso).card - 2 = 2 := by rw [hw4]
    have hrest0 : ∑ x ∈ R.erase w, ((G.neighborFinset x ∩ Iso).card - 2) = 0 := by omega
    have hrmem : r ∈ R.erase w := Finset.mem_erase.mpr ⟨hrw, hrR⟩
    have hr0 : (G.neighborFinset r ∩ Iso).card - 2 = 0 :=
      (Finset.sum_eq_zero_iff.mp hrest0) r hrmem
    have := hRrich r hrR; omega
  · -- No iso-degree-`4` hub: all rich iso-degrees are `≤ 3`, excess `≤ 1`, sum `2`, so two `3`s.
    right
    push Not at hfour
    have hle1 : ∀ r ∈ R, (G.neighborFinset r ∩ Iso).card - 2 ≤ 1 := by
      intro r hr; have := hle4 r hr; have := hfour r hr; omega
    -- First excess-`1` hub `w₁`.
    have hpos1 : ∃ w ∈ R, (G.neighborFinset w ∩ Iso).card - 2 = 1 := by
      by_contra hcon
      push Not at hcon
      have hzero : ∑ r ∈ R, ((G.neighborFinset r ∩ Iso).card - 2) = 0 := by
        apply Finset.sum_eq_zero
        intro r hr; have := hcon r hr; have := hle1 r hr; omega
      omega
    obtain ⟨w₁, hw1R, hw1⟩ := hpos1
    -- Remaining excess on `R.erase w₁` is `1`.
    have hsplit1 := Finset.add_sum_erase R
      (fun x => (G.neighborFinset x ∩ Iso).card - 2) hw1R
    have hrest1 : ∑ x ∈ R.erase w₁, ((G.neighborFinset x ∩ Iso).card - 2) = 1 := by omega
    -- Second excess-`1` hub `w₂` in `R.erase w₁`.
    have hpos2 : ∃ w ∈ R.erase w₁, (G.neighborFinset w ∩ Iso).card - 2 = 1 := by
      by_contra hcon
      push Not at hcon
      have hzero : ∑ r ∈ R.erase w₁, ((G.neighborFinset r ∩ Iso).card - 2) = 0 := by
        apply Finset.sum_eq_zero
        intro r hr
        have := hcon r hr
        have := hle1 r (Finset.mem_of_mem_erase hr)
        omega
      omega
    obtain ⟨w₂, hw2e, hw2⟩ := hpos2
    obtain ⟨hw2ne, hw2R⟩ := Finset.mem_erase.mp hw2e
    refine ⟨w₁, hw1R, w₂, hw2R, fun he => hw2ne he.symm, by omega, by omega, ?_⟩
    intro r hrR hrw1 hrw2
    -- Excess on `(R.erase w₁).erase w₂` is `0`, so `r` has iso-degree `2`.
    have hsplit2 := Finset.add_sum_erase (R.erase w₁)
      (fun x => (G.neighborFinset x ∩ Iso).card - 2) hw2e
    have hrest2 : ∑ x ∈ (R.erase w₁).erase w₂, ((G.neighborFinset x ∩ Iso).card - 2) = 0 := by
      omega
    have hrmem : r ∈ (R.erase w₁).erase w₂ :=
      Finset.mem_erase.mpr ⟨hrw2, Finset.mem_erase.mpr ⟨hrw1, hrR⟩⟩
    have hr0 : (G.neighborFinset r ∩ Iso).card - 2 = 0 :=
      (Finset.sum_eq_zero_iff.mp hrest2) r hrmem
    have := hRrich r hrR; omega

/-- **The iso-degree-`≥ 3` rich hubs form a clique (`R₃`-clique).**  Two distinct iso-degree-`≥ 3`
hubs `a, b` (degree `4`) that were non-adjacent would share `≤ 1` twin (`hshare`), leaving
`≥ 3 - 1 = 2` private twins on each side — a two-hub configuration excluded by `hno2hub`.  Hence any
two such hubs are adjacent. -/
theorem rich3_clique_S14 (G : SimpleGraph (Fin 18)) (Hub Iso : Finset (Fin 18))
    (hdeg4 : ∀ h ∈ Hub, G.degree h = 4)
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hno2hub : ¬∃ h₁ h₂ : Fin 18, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card)
    (a b : Fin 18) (haHub : a ∈ Hub) (hbHub : b ∈ Hub) (hab : a ≠ b)
    (ha3 : 3 ≤ (G.neighborFinset a ∩ Iso).card) (hb3 : 3 ≤ (G.neighborFinset b ∩ Iso).card) :
    G.Adj a b := by
  classical
  by_contra hnadj
  apply hno2hub
  have hsh := hshare a haHub (hdeg4 a haHub) b hbHub (hdeg4 b hbHub) hab hnadj
  refine ⟨a, b, haHub, hbHub, hdeg4 a haHub, hdeg4 b hbHub, hab, hnadj, ?_, ?_⟩
  · have hcs := Finset.card_sdiff_add_card_inter (G.neighborFinset a ∩ Iso) (G.neighborFinset b)
    have hinter : (G.neighborFinset a ∩ Iso) ∩ G.neighborFinset b
        = G.neighborFinset a ∩ G.neighborFinset b ∩ Iso := by
      ext x; simp only [Finset.mem_inter]; tauto
    rw [hinter] at hcs
    omega
  · have hcs := Finset.card_sdiff_add_card_inter (G.neighborFinset b ∩ Iso) (G.neighborFinset a)
    have hinter : (G.neighborFinset b ∩ Iso) ∩ G.neighborFinset a
        = G.neighborFinset a ∩ G.neighborFinset b ∩ Iso := by
      ext x; simp only [Finset.mem_inter]; tauto
    rw [hinter] at hcs
    omega

end N18

end ACMax
