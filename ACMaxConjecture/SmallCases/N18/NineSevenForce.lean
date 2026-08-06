import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N18.Core
import ACMaxConjecture.SmallCases.N18.TwoHubSelect
import ACMaxConjecture.SmallCases.N18.StarTriangleStruct

/-!
# Rich-mass pinning for the `(9, 7, 37)` rich-absorber residual (`n = 18`)

For the tight `e(M) = 1` profile `(|Hub|, |Iso|, ∑deg) = (9, 7, 37)` write `S` for the *rich*
degree-`4` hubs (degree `4` and iso-degree `≥ 2`), `s := |S|`, `M := ∑_{a∈S}|N(a)∩Iso|`, and let `d`
be the lone degree-`5` hub with iso-degree `i := |N(d)∩Iso|`.

Two clean counting leaves pin the residual to a single configuration:

* `ninesev_rich_mass_le` — `M ≤ 2·s + 2`.  Each rich hub has iso-degree `2 + 1_{≥3} + 1_{≥4}`, and
  the count of degree-`4` hubs of iso-degree `≥ 3` (with multiplicity for `≥ 4`) is `≤ 2` by the
  strong-hub bound `strong_deg4_count_le_two_deg5_eighteen`.
* `ninesev_mass_lower` — `13 + s ≤ M + i`.  The total iso-incidence sum is `3·7 = 21`; the `8 − s`
  *poor* degree-`4` hubs each carry iso-degree `≤ 1`, so they absorb `≤ 8 − s`, leaving
  `M + i ≥ 21 − (8 − s) = 13 + s`.

Combining with `s ≤ 6` and `i ≤ 5` (degree-`5` absorber) and `i ≥ 3`
(`deg5_iso_ge_three_nine_seven`) forces the **single** boundary config `i = 5, s = 6, M = 14`.
-/

namespace ACMax

open scoped Classical

namespace N18

/-- **The degree-`5` absorber is isolated from the hubs and `M`-ends.**  When the lone degree-`5`
hub `d` has iso-degree `5` its entire neighbourhood is `M`-isolated twins (`|N(d)| = 5 = |N(d)∩Iso|`,
so `N(d) ⊆ Iso`).  In particular `d` is non-adjacent to every hub and to every `M`-edge endpoint. -/
theorem ninesev_rich_isolated_from_d (G : SimpleGraph (Fin 18)) (Iso : Finset (Fin 18))
    (d : Fin 18) (hdeg_d5 : G.degree d = 5)
    (hi5 : (G.neighborFinset d ∩ Iso).card = 5) :
    G.neighborFinset d ⊆ Iso := by
  classical
  have hd5 : (G.neighborFinset d).card = 5 := by
    rw [G.card_neighborFinset_eq_degree, hdeg_d5]
  have heq : G.neighborFinset d ∩ Iso = G.neighborFinset d :=
    Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by rw [hd5, hi5])
  rw [← heq]; exact Finset.inter_subset_right

/-- **Rich-mass upper bound `M ≤ 2·s + 2`.**  Each rich degree-`4` hub `a` has
`|N(a)∩Iso| = 2 + 1_{≥3}(a) + 1_{≥4}(a)` (iso-degree between `2` and `4`).  Summing, the rich mass is
`2·|S| + #{a∈S : |N(a)∩Iso| ≥ 3} + #{a∈S : |N(a)∩Iso| ≥ 4}`, and the two threshold counts add to
`≤ 2` over *all* degree-`4` hubs by the strong-hub clique bound. -/
theorem ninesev_rich_mass_le (G : SimpleGraph (Fin 18)) (Hub Iso S : Finset (Fin 18))
    (hSsub : S ⊆ Hub) (hSdeg4 : ∀ a ∈ S, G.degree a = 4)
    (hSrich : ∀ a ∈ S, 2 ≤ (G.neighborFinset a ∩ Iso).card)
    (hdisj : Disjoint Hub Iso)
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hno2hub : ¬∃ h₁ h₂ : Fin 18, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card) :
    ∑ a ∈ S, (G.neighborFinset a ∩ Iso).card ≤ 2 * S.card + 2 := by
  classical
  have hkey := strong_deg4_count_le_two_deg5_eighteen G Hub Iso hdisj hshare
    (nogood_of_not_select_eighteen G Hub Iso hno2hub)
  -- Iso-degree of a rich hub is `≤ 4`.
  have hle4 : ∀ a ∈ S, (G.neighborFinset a ∩ Iso).card ≤ 4 := by
    intro a ha
    calc (G.neighborFinset a ∩ Iso).card ≤ (G.neighborFinset a).card :=
          Finset.card_le_card Finset.inter_subset_left
      _ = G.degree a := G.card_neighborFinset_eq_degree a
      _ = 4 := hSdeg4 a ha
  -- Pointwise: `iso-deg a ≤ 2 + 1_{≥3} + 1_{≥4}`.
  have hpt : ∀ a ∈ S, (G.neighborFinset a ∩ Iso).card
      ≤ 2 + (if 3 ≤ (G.neighborFinset a ∩ Iso).card then 1 else 0)
        + (if 4 ≤ (G.neighborFinset a ∩ Iso).card then 1 else 0) := by
    intro a ha
    have h2 := hSrich a ha
    have h4 := hle4 a ha
    split_ifs <;> omega
  -- Sum the pointwise bound.
  have hsum : ∑ a ∈ S, (G.neighborFinset a ∩ Iso).card
      ≤ 2 * S.card + (S.filter (fun a => 3 ≤ (G.neighborFinset a ∩ Iso).card)).card
        + (S.filter (fun a => 4 ≤ (G.neighborFinset a ∩ Iso).card)).card := by
    calc ∑ a ∈ S, (G.neighborFinset a ∩ Iso).card
        ≤ ∑ a ∈ S, (2 + (if 3 ≤ (G.neighborFinset a ∩ Iso).card then 1 else 0)
            + (if 4 ≤ (G.neighborFinset a ∩ Iso).card then 1 else 0)) := Finset.sum_le_sum hpt
      _ = 2 * S.card + (S.filter (fun a => 3 ≤ (G.neighborFinset a ∩ Iso).card)).card
            + (S.filter (fun a => 4 ≤ (G.neighborFinset a ∩ Iso).card)).card := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul,
            mul_comm, Finset.card_filter, Finset.card_filter]
  -- The two threshold counts embed into the `Hub` versions.
  have hsub3 : S.filter (fun a => 3 ≤ (G.neighborFinset a ∩ Iso).card)
      ⊆ Hub.filter (fun h => G.degree h = 4 ∧ 3 ≤ (G.neighborFinset h ∩ Iso).card) := by
    intro a ha
    rw [Finset.mem_filter] at ha ⊢
    exact ⟨hSsub ha.1, hSdeg4 a ha.1, ha.2⟩
  have hsub4 : S.filter (fun a => 4 ≤ (G.neighborFinset a ∩ Iso).card)
      ⊆ Hub.filter (fun h => G.degree h = 4 ∧ 4 ≤ (G.neighborFinset h ∩ Iso).card) := by
    intro a ha
    rw [Finset.mem_filter] at ha ⊢
    exact ⟨hSsub ha.1, hSdeg4 a ha.1, ha.2⟩
  have hc3 := Finset.card_le_card hsub3
  have hc4 := Finset.card_le_card hsub4
  omega

/-- **Rich-mass lower bound `13 + s ≤ M + i`.**  The total iso-incidence sum over the nine hubs is
`3·|Iso| = 21`.  Removing the rich hubs `S`, the remaining `9 − s` hubs are the lone degree-`5` hub
`d` (iso-degree `i`) and `8 − s` *poor* degree-`4` hubs (each iso-degree `≤ 1`).  Hence
`21 = M + i + (poor mass) ≤ M + i + (8 − s)`, i.e. `13 + s ≤ M + i`. -/
theorem ninesev_mass_lower (G : SimpleGraph (Fin 18)) (Hub Iso S : Finset (Fin 18))
    (hSsub : S ⊆ Hub)
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hHub : Hub.card = 9) (hIso : Iso.card = 7)
    (hSmem : ∀ a, a ∈ S ↔ a ∈ Hub ∧ G.degree a = 4 ∧ 2 ≤ (G.neighborFinset a ∩ Iso).card)
    (d : Fin 18) (hdHub : d ∈ Hub) (hdS : d ∉ S)
    (hother : ∀ a ∈ Hub, a ≠ d → G.degree a = 4) :
    13 + S.card ≤ ∑ a ∈ S, (G.neighborFinset a ∩ Iso).card
      + (G.neighborFinset d ∩ Iso).card := by
  classical
  have htot : ∑ a ∈ Hub, (G.neighborFinset a ∩ Iso).card = 21 := by
    have := hub_iso_sum_eighteen G Hub Iso hiso3; rw [hIso] at this; omega
  -- Split off the rich hubs.
  have hsdiff : ∑ a ∈ Hub \ S, (G.neighborFinset a ∩ Iso).card
      + ∑ a ∈ S, (G.neighborFinset a ∩ Iso).card = 21 := by
    rw [Finset.sum_sdiff hSsub]; exact htot
  -- `d ∈ Hub \ S`.
  have hdHS : d ∈ Hub \ S := Finset.mem_sdiff.mpr ⟨hdHub, hdS⟩
  -- Poor hubs (the rest of `Hub \ S`) have iso-degree `≤ 1`.
  have hpoor : ∀ a ∈ (Hub \ S).erase d, (G.neighborFinset a ∩ Iso).card ≤ 1 := by
    intro a ha
    have hane : a ≠ d := Finset.ne_of_mem_erase ha
    have haHS : a ∈ Hub \ S := Finset.mem_of_mem_erase ha
    obtain ⟨haHub, haS⟩ := Finset.mem_sdiff.mp haHS
    have hd4 : G.degree a = 4 := hother a haHub hane
    by_contra hgt
    push Not at hgt
    exact haS ((hSmem a).mpr ⟨haHub, hd4, by omega⟩)
  -- The non-`d` part of `Hub \ S` is bounded by its cardinality.
  have herase : ∑ a ∈ (Hub \ S).erase d, (G.neighborFinset a ∩ Iso).card
      ≤ ((Hub \ S).erase d).card := by
    calc ∑ a ∈ (Hub \ S).erase d, (G.neighborFinset a ∩ Iso).card
        ≤ ∑ _a ∈ (Hub \ S).erase d, 1 := Finset.sum_le_sum hpoor
      _ = ((Hub \ S).erase d).card := by rw [Finset.sum_const, smul_eq_mul, mul_one]
  -- Re-expose the `d` term.
  have hsplit : ∑ a ∈ Hub \ S, (G.neighborFinset a ∩ Iso).card
      = (G.neighborFinset d ∩ Iso).card
        + ∑ a ∈ (Hub \ S).erase d, (G.neighborFinset a ∩ Iso).card :=
    (Finset.add_sum_erase (Hub \ S) _ hdHS).symm
  -- Cardinalities.
  have hSle : S.card ≤ 9 := by rw [← hHub]; exact Finset.card_le_card hSsub
  have hHSadd : (Hub \ S).card + S.card = Hub.card :=
    Finset.card_sdiff_add_card_eq_card hSsub
  rw [hHub] at hHSadd
  have heraseC : ((Hub \ S).erase d).card = (Hub \ S).card - 1 :=
    Finset.card_erase_of_mem hdHS
  have hHSpos : 1 ≤ (Hub \ S).card := Finset.card_pos.mpr ⟨d, hdHS⟩
  omega

end N18

end ACMax
