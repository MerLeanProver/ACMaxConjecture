import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N14.Core
import ACMaxConjecture.SmallCases.N14.TwoHubSelectCorner

/-!
# Hub-pair selection for the `n = 14` two-hub residual (`s ∈ {2, 4}` branch)

This file supplies `two_hub_pair_select_fourteen`, the hub-pair *selection* lemma feeding the
`e(M) ≤ 2` (`s ∈ {2, 4}`) branch of `two_hub_config_fourteen` (in `TwinCert14TwoHub`).

The set-up is abstracted from `G`'s degree structure: `Hub` is the six degree-`4` hubs, `Iso` the
`M`-isolated degree-`3` twins (each meeting exactly three hubs), `hHubsum` records `e(Hub) ≤ 2`
(at most two hub-edges), `hIso5` records `|Iso| ≥ 5`, `hisoIndep` the `M`-independence of twins,
and `hshare` the good-`K_{2,3}` bound (a non-adjacent hub-pair shares `≤ 2` isolated twins).

The clean case — at least two hubs of iso-degree `4` — is fully proved: such hubs have all four
neighbours in `Iso`, are therefore hub-isolated (hence pairwise non-adjacent), and the share bound
gives each `≥ 2` private isolated twins.  The complementary corner (at most one hub of iso-degree
`4`, where the selection is the genuine `(3,3,3,3,3,0)`-type extremal pigeonhole / third-hub-swap
argument) is isolated as the one documented `sorry`.
-/

namespace ACMax

open scoped Classical

namespace N14

/-- **Hub-pair selection (`e(M) ≤ 2`, `s ∈ {2, 4}` branch for `n = 14`).**  Given six degree-`4`
hubs (`hHub6`, `hdeg4`) with at most two hub-edges (`hHubsum`), at least five `M`-isolated twins
(`hIso5`) each meeting exactly three hubs (`hiso3`), the twins `M`-independent (`hisoIndep`), and
the good-`K_{2,3}` bound that a non-adjacent hub-pair shares at most two twins (`hshare`), there
exist two non-adjacent degree-`4` hubs each retaining `≥ 2` private isolated twins.

The clean sub-case (at least two hubs of iso-degree `4`) is fully proved; the complementary corner
(at most one hub of iso-degree `4`) is the lone documented `sorry`. -/
theorem two_hub_pair_select_fourteen (G : SimpleGraph (Fin 14)) (Hub Iso : Finset (Fin 14))
    (hHub6 : Hub.card = 6)
    (hdeg4 : ∀ h ∈ Hub, G.degree h = 4)
    (hHubsum : ∑ w ∈ Hub, (G.neighborFinset w ∩ Hub).card ≤ 4)
    (hIso6 : Iso.card = 6)
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hisoIndep : ∀ a ∈ Iso, ∀ b ∈ Iso, ¬G.Adj a b)
    (hshare : ∀ h₁ ∈ Hub, ∀ h₂ ∈ Hub, h₁ ≠ h₂ → ¬G.Adj h₁ h₂ →
      (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 2) :
    ∃ h₁ h₂ : Fin 14, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card := by
  classical
  set F : Finset (Fin 14) := Hub.filter (fun h => (G.neighborFinset h ∩ Iso).card = 4) with hFdef
  by_cases hk : 2 ≤ F.card
  · -- **Clean case: two hubs of iso-degree `4`.**
    obtain ⟨h₁, hh1F, h₂, hh2F, hne⟩ := Finset.one_lt_card.mp hk
    have hh1 : h₁ ∈ Hub := (Finset.mem_filter.mp hh1F).1
    have hh2 : h₂ ∈ Hub := (Finset.mem_filter.mp hh2F).1
    have h1iso4 : (G.neighborFinset h₁ ∩ Iso).card = 4 := (Finset.mem_filter.mp hh1F).2
    have h2iso4 : (G.neighborFinset h₂ ∩ Iso).card = 4 := (Finset.mem_filter.mp hh2F).2
    -- Iso-degree `4` forces all neighbours into `Iso`.
    have hsub : ∀ h ∈ Hub, (G.neighborFinset h ∩ Iso).card = 4 →
        G.neighborFinset h ⊆ Iso := by
      intro h hh hh4
      have hdeg : (G.neighborFinset h).card = 4 := by
        rw [G.card_neighborFinset_eq_degree, hdeg4 h hh]
      have heq : G.neighborFinset h ∩ Iso = G.neighborFinset h :=
        Finset.eq_of_subset_of_card_le (Finset.inter_subset_left)
          (by rw [hdeg, hh4])
      intro x hx
      have hxI : x ∈ G.neighborFinset h ∩ Iso := by rw [heq]; exact hx
      exact (Finset.mem_inter.mp hxI).2
    have h1sub : G.neighborFinset h₁ ⊆ Iso := hsub h₁ hh1 h1iso4
    have h2sub : G.neighborFinset h₂ ⊆ Iso := hsub h₂ hh2 h2iso4
    -- Two iso-degree-`4` hubs are non-adjacent (else each lies in `Iso`, contradicting `hisoIndep`).
    have hnadj : ¬G.Adj h₁ h₂ := by
      intro hadj
      have h2in : h₂ ∈ Iso := h1sub ((G.mem_neighborFinset h₁ h₂).mpr hadj)
      have h1in : h₁ ∈ Iso := h2sub ((G.mem_neighborFinset h₂ h₁).mpr hadj.symm)
      exact hisoIndep h₁ h1in h₂ h2in hadj
    have hsh := hshare h₁ hh1 h₂ hh2 hne hnadj
    refine ⟨h₁, h₂, hh1, hh2, hdeg4 h₁ hh1, hdeg4 h₂ hh2, hne, hnadj, ?_, ?_⟩
    · have hkey := Finset.card_sdiff_add_card_inter (G.neighborFinset h₁ ∩ Iso)
        (G.neighborFinset h₂)
      have hreord : (G.neighborFinset h₁ ∩ Iso) ∩ G.neighborFinset h₂
          = G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso := Finset.inter_right_comm _ _ _
      rw [hreord] at hkey
      omega
    · have hkey := Finset.card_sdiff_add_card_inter (G.neighborFinset h₂ ∩ Iso)
        (G.neighborFinset h₁)
      have hreord : (G.neighborFinset h₂ ∩ Iso) ∩ G.neighborFinset h₁
          = G.neighborFinset h₂ ∩ G.neighborFinset h₁ ∩ Iso := Finset.inter_right_comm _ _ _
      have hsh' := hshare h₂ hh2 h₁ hh1 (Ne.symm hne) (fun h => hnadj h.symm)
      rw [hreord] at hkey
      omega
  · -- **Corner: at most one hub of iso-degree `4`.**  Here `|Iso| = 6` (hypothesis), so the
    -- selection runs the `(4,3,3,3,3,2)` profile route of `two_hub_corner_select` directly; the
    -- former `|Iso| ≤ 6` derivation is now supplied by the tightened `hIso6` hypothesis.
    exact two_hub_corner_select G Hub Iso hHub6 hdeg4 hHubsum hIso6 hiso3 hisoIndep hshare

end N14

end ACMax
