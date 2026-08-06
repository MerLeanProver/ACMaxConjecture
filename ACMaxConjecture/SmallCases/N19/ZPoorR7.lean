import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N19.Core
import ACMaxConjecture.SmallCases.N19.TwoHubSelect
import ACMaxConjecture.SmallCases.N19.StarTriangleStruct
import ACMaxConjecture.SmallCases.N19.RichCount
import ACMaxConjecture.SmallCases.N19.Align8Helpers

/-!
# Node A — the `r = 7` rich-count impossibility under the two-poor hypothesis (`n = 18`)

For the tight `e(M) = 1`, all-degree-`4`, `(|Hub|, |Iso|) = (11, 6)` profile, the *rich* hubs are
`R = {h : 2 ≤ |N(h) ∩ Iso|}`.  When an `M`-edge endpoint `z` meets two *poor* hubs the global rich
count cannot be `7`.  Writing `S := ∑_R |N ∩ Iso|` and `A₃ := {r ∈ R : 3 ≤ |N(r) ∩ Iso|}` (the
*high* rich hubs), the iso-incidence handshake `∑_{A₃} isoDeg + 2·|R \ A₃| = S` together with
`|A₃| ≤ 2` (`N2`, `rich_a3_count_le_two`) and `15 ≤ S ≤ 18` pins the high profile:

* `S = 18` ⟹ `|A₃| = 2` with both iso-degree `4`;
* `S = 17` ⟹ `|A₃| = 2` with iso-degrees `{3, 4}`.

In both `S ≥ 17` cases there is an iso-degree-`4` rich hub `w₁` (`N(w₁) ⊆ Iso`, hence non-adjacent
to every hub) and a second iso-degree-`≥ 3` rich hub `w₂`; these are two non-adjacent degree-`4`
hubs each retaining `≥ 2` private `M`-isolated twins (share `≤ 1`), contradicting `hno2hub`.

DOCUMENTED `sorry`: the residual `S ∈ {15, 16}` covering case (equivalently `n₃ = 5`).  Here the
high profile is either a single iso-degree-`4`/`3` hub or two iso-degree-`3` hubs that may be
adjacent, so the abstract `N2` budget no longer forces a non-adjacent pair; closing it needs the
two-poor `z`-layout fed through `hC4`/`hK23`.  It is isolated here as the single residual.
-/

namespace ACMax

open scoped Classical

namespace N19

/-- **Private-twin split.**  The `M`-isolated twins of `w₁` partition (with the shared twins) into
those missed by `w₂` and the shared ones `N(w₁) ∩ N(w₂) ∩ Iso`. -/
theorem private_twin_card_nineteen (G : SimpleGraph (Fin 19)) (Iso : Finset (Fin 19))
    (w1 w2 : Fin 19) :
    ((G.neighborFinset w1 ∩ Iso) \ G.neighborFinset w2).card
      + (G.neighborFinset w1 ∩ G.neighborFinset w2 ∩ Iso).card
      = (G.neighborFinset w1 ∩ Iso).card := by
  have hc := Finset.card_sdiff_add_card_inter (G.neighborFinset w1 ∩ Iso) (G.neighborFinset w2)
  have hint : (G.neighborFinset w1 ∩ Iso) ∩ G.neighborFinset w2
      = G.neighborFinset w1 ∩ G.neighborFinset w2 ∩ Iso := Finset.inter_right_comm _ _ _
  rw [hint] at hc; exact hc

/-- **An iso-degree-`4` hub is non-adjacent to every hub.**  If `w₁` is a degree-`4` hub meeting
all four of its neighbours inside `Iso`, then `N(w₁) ⊆ Iso`, which is disjoint from `Hub`; hence
`w₁` is adjacent to no hub. -/
theorem iso_deg_four_nonadj_hub_nineteen (G : SimpleGraph (Fin 19)) (Hub Iso : Finset (Fin 19))
    (hdisj : Disjoint Hub Iso) (hdeg4 : ∀ h ∈ Hub, G.degree h = 4)
    (w1 w2 : Fin 19) (hw1 : w1 ∈ Hub) (hw2 : w2 ∈ Hub)
    (hw14 : (G.neighborFinset w1 ∩ Iso).card = 4) : ¬G.Adj w1 w2 := by
  have hd4 : (G.neighborFinset w1).card = 4 := by
    rw [G.card_neighborFinset_eq_degree, hdeg4 w1 hw1]
  have hsub : G.neighborFinset w1 ⊆ Iso := by
    have heq : G.neighborFinset w1 ∩ Iso = G.neighborFinset w1 :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by rw [hd4, hw14])
    rw [← heq]; exact Finset.inter_subset_right
  intro hadj
  have hw2N : w2 ∈ G.neighborFinset w1 := (G.mem_neighborFinset w1 w2).mpr hadj
  exact Finset.disjoint_left.mp hdisj hw2 (hsub hw2N)

/-- **Two non-adjacent high hubs contradict `hno2hub`.**  Two distinct non-adjacent degree-`4` hubs
each with iso-degree `≥ 3` share at most one `M`-isolated twin (`hshare`), so each retains `≥ 2`
private twins — exactly the configuration excluded by `hno2hub`. -/
theorem two_nonadj_hubs_contra_nineteen (G : SimpleGraph (Fin 19)) (Hub Iso : Finset (Fin 19))
    (hdeg4 : ∀ h ∈ Hub, G.degree h = 4)
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hno2hub : ¬∃ h₁ h₂ : Fin 19, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card)
    (w1 w2 : Fin 19) (hw1 : w1 ∈ Hub) (hw2 : w2 ∈ Hub) (hw12 : w1 ≠ w2)
    (hnadj : ¬G.Adj w1 w2)
    (h1ge : 3 ≤ (G.neighborFinset w1 ∩ Iso).card)
    (h2ge : 3 ≤ (G.neighborFinset w2 ∩ Iso).card) :
    False := by
  have hsh := hshare w1 hw1 (hdeg4 w1 hw1) w2 hw2 (hdeg4 w2 hw2) hw12 hnadj
  have hp1 := private_twin_card_nineteen G Iso w1 w2
  have hp2 := private_twin_card_nineteen G Iso w2 w1
  have hsymm : G.neighborFinset w2 ∩ G.neighborFinset w1 ∩ Iso
      = G.neighborFinset w1 ∩ G.neighborFinset w2 ∩ Iso := by
    ext x; simp only [Finset.mem_inter]; tauto
  rw [hsymm] at hp2
  exact hno2hub ⟨w1, w2, hw1, hw2, hdeg4 w1 hw1, hdeg4 w2 hw2, hw12, hnadj, by omega, by omega⟩

/-- **Two high hubs with iso-degree sum `≥ 7` contradict `hno2hub`.**  Two distinct degree-`4` hubs
each with iso-degree `≥ 3` and total iso-degree `≥ 7` must include one of iso-degree `4`, which has
`N ⊆ Iso` and is therefore non-adjacent to the other; the pair then contradicts `hno2hub`. -/
theorem two_high_hubs_sum_ge_seven_contra_nineteen (G : SimpleGraph (Fin 19))
    (Hub Iso : Finset (Fin 19)) (hdisj : Disjoint Hub Iso) (hdeg4 : ∀ h ∈ Hub, G.degree h = 4)
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hno2hub : ¬∃ h₁ h₂ : Fin 19, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card)
    (w1 w2 : Fin 19) (hw1 : w1 ∈ Hub) (hw2 : w2 ∈ Hub) (hw12 : w1 ≠ w2)
    (h1ge : 3 ≤ (G.neighborFinset w1 ∩ Iso).card)
    (h2ge : 3 ≤ (G.neighborFinset w2 ∩ Iso).card)
    (hsum7 : 7 ≤ (G.neighborFinset w1 ∩ Iso).card + (G.neighborFinset w2 ∩ Iso).card) :
    False := by
  have hw1le : (G.neighborFinset w1 ∩ Iso).card ≤ 4 := by
    calc (G.neighborFinset w1 ∩ Iso).card ≤ (G.neighborFinset w1).card :=
          Finset.card_le_card Finset.inter_subset_left
      _ = 4 := by rw [G.card_neighborFinset_eq_degree, hdeg4 w1 hw1]
  have hw2le : (G.neighborFinset w2 ∩ Iso).card ≤ 4 := by
    calc (G.neighborFinset w2 ∩ Iso).card ≤ (G.neighborFinset w2).card :=
          Finset.card_le_card Finset.inter_subset_left
      _ = 4 := by rw [G.card_neighborFinset_eq_degree, hdeg4 w2 hw2]
  by_cases h1is4 : (G.neighborFinset w1 ∩ Iso).card = 4
  · have hnadj := iso_deg_four_nonadj_hub_nineteen G Hub Iso hdisj hdeg4 w1 w2 hw1 hw2 h1is4
    exact two_nonadj_hubs_contra_nineteen G Hub Iso hdeg4 hshare hno2hub w1 w2 hw1 hw2 hw12
      hnadj h1ge h2ge
  · have h2is4 : (G.neighborFinset w2 ∩ Iso).card = 4 := by omega
    have hnadj := iso_deg_four_nonadj_hub_nineteen G Hub Iso hdisj hdeg4 w2 w1 hw2 hw1 h2is4
    exact two_nonadj_hubs_contra_nineteen G Hub Iso hdeg4 hshare hno2hub w2 w1 hw2 hw1
      (Ne.symm hw12) hnadj h2ge h1ge

end N19

end ACMax
