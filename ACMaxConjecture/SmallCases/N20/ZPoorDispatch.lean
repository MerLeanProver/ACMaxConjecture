import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N20.Core
import ACMaxConjecture.SmallCases.N20.TwoHubSelect
import ACMaxConjecture.SmallCases.N20.StarTriangleStruct
import ACMaxConjecture.SmallCases.N20.RichCount
import ACMaxConjecture.SmallCases.N20.Align8Helpers
import ACMaxConjecture.SmallCases.N20.ZVertex
import ACMaxConjecture.SmallCases.N20.ZPoorR7
import ACMaxConjecture.SmallCases.N20.ZPoorSat
import ACMaxConjecture.SmallCases.N20.ZPoorS16
import ACMaxConjecture.SmallCases.N20.R5Resid
import ACMaxConjecture.SmallCases.N20.AllPoorOne

/-!
# The two-poor-hub dispatcher for the rigid `n = 20` no-two-hub partition (top layer)

Port of `TwinCert19ZPoorDispatch` to the NEW `n = 20` `|Hub| = 12` regime.  For the tight
`e(M) = 1`, all-degree-`4`, `(|Hub|, |Iso|) = (12, 6)` profile, an `M`-edge endpoint
`z = univ \ (Hub ∪ Iso)` meets exactly two hubs.  This file closes the headline obstruction — both of
those hubs cannot be *poor* (iso-degree `≤ 1`) — by dispatching the rich-count regime to the
axiom-clean regime provers.

The rich count `r := |R|` lies in `{6, 7}` (`rich_count_ge_six_twenty` / `rich_count_le_seven`),
and `S := ∑_R |N ∩ Iso|` is the rich iso-incidence sum.  The `n = 20` regime table (DERIVED;
`|Iso| = 6`, `|Hub \ R| = 12 − r` poor hubs each carrying `≤ 1` iso-incidence, total iso-incidence
`18`, and `S ≥ 2r` since every rich hub carries `≥ 2`):

| `r` | `S` | prover |
|`7`|`14`| `z`-side cut (`z_side_poor_cut_twenty`, `∑_P = 4 > 3 = |P| − 2`) ✓ |
|`7`|`15`| `mpartner_meets_poor_twenty` (`z`-side cut, `TwinCert20ZPoorSat`) ✓ |
|`7`|`16`| `rich_seven_S16_two_poor_false_twenty` (`z'`-side cut via saturation, `TwinCert20ZPoorS16`) ✓ |
|`7`|`≥17`| clean `two_high_hubs_sum_ge_seven_contra_twenty` ✓ |
|`6`|`12`| `z`-side cut (`z_side_poor_cut_twenty`, `∑_P = 6 > 4 = |P| − 2`) ✓ |
|`6`|`13`| `z`-side cut (`z_side_poor_cut_twenty`, `∑_P = 5 > 4 = |P| − 2`) ✓ |
|`6`|`14`| **NEW at `n = 20`**: `rich_six_S14_two_poor_false_twenty` (`M`-partner kill) ✓ |
|`6`|`≥15`| clean `two_high_hubs_sum_ge_seven_contra_twenty` ✓ |

(The `r = 7, S = 13` row of the naive `|P| = 5` recount is VACUOUS: seven rich hubs force
`S ≥ 14`.  The genuinely new `n = 20` regime is `r = 6, S = 14`, where the `z`-side pigeonhole
collapses — `∑_P = 4` no longer exceeds `|P| − 2 = 4`.)

**The reusable cut (BYPASSES the n = 18 saturation/design packing).**  An `M`-edge endpoint `z`
meets two poor hubs `hg1, hg2`.  Whenever the poor-incidence sum `∑_P = 18 − S` exceeds the
capacity `|P| − 2` of the *other* poor hubs (i.e. `S < r + 8`), at least one of `hg1, hg2` carries a
private twin, and the `r ∈ {6,7}` rich pool (`|R| ≥ 5`) supplies a `TwoHubConfig` with a `Z`-leaf
`d = z` (invisible to the `Iso`-only `hno2hub`) via the pigeonhole
`two_poor_zleaf_pigeonhole_twenty` — contradicting `hnocut`.  The exceptions where `hg1, hg2` may
both be twinless are `r = 7, S ∈ {15, 16}` (the recompiled `TwinCert20ZPoorSat` /
`TwinCert20ZPoorS16` provers) and the new `r = 6, S = 14` regime, closed here by routing through the
`M`-partner `z'`: its two hub-neighbours avoid `hg1, hg2` (`no_hub_adj_both_mends_twenty`), a poor
one carries exactly one twin (the four remaining poor hubs absorb `∑_P = 4` one each) and fires the
`z'`-side pigeonhole cut, while a rich one is assembled into a `Z`-leaf `TwoHubConfig` against an
iso-degree-`≥ 3` partner extracted from the `{2,2,2,2,3,3}` / `{2,2,2,2,2,4}` designs.  The clean
`S ≥ 17 / S ≥ 15` sub-cases assemble two non-adjacent degree-`4` hubs each retaining `≥ 2` private
twins (`two_high_hubs_sum_ge_seven_contra_twenty`), contradicting `hno2hub`.

The apex `z_meets_two_poor_forces_two_hub_twenty` is now fully proved (axiom-clean,
`[propext, Classical.choice, Quot.sound]`); it threads `hnocut : ¬ ZPoorCutConfig G` (introduced by
`by_contra`) down to the regime branches, each of which builds the cut and closes the branch.  Once
`RichZdeg` imports this file it discharges `hztwopoor` library-wide.
-/

namespace ACMax

open scoped Classical

namespace N20

/-- **The `r = 6`, `S = 14` kill (the genuinely NEW `n = 20` regime).**  At `|Hub| = 12` the
`r = 6` poor side widens to `|P| = 6`, and at `S = 14` the `z`-side pigeonhole collapses
(`∑_P = 4 = |P| − 2`): both of `z`'s poor hubs may be twinless.  The kill routes through the
`M`-partner `z'`.  Its two hub-neighbours `g₃, g₄` are distinct from `hg1, hg2`
(`no_hub_adj_both_mends_twenty`), so in the twinless residual a *poor* `z'`-hub carries exactly
one twin — the four remaining poor hubs absorb `∑_P = 4` one each — and fires the `z'`-side
pigeonhole cut (`two_poor_zleaf_pigeonhole_twenty`).  A *rich* `z'`-hub `g` is assembled into a
`Z`-leaf `TwoHubConfig` (`two_hub_zleaf_twenty`, fourth leaf `d = z'`) against an
iso-degree-`≥ 3` partner `h₁ ≁ g, z'` read off the two `S = 14` designs: in `{2,2,2,2,2,4}` the
iso-degree-`4` hub is non-adjacent to every hub and to `z'`; in `{2,2,2,2,3,3}` an *adjacent*
`3,3`-pair pins each member's neighbourhood to its three twins plus the partner (so both avoid
`g` and `z'`), while a *non-adjacent* `3,3`-pair contradicts `hno2hub` outright. -/
theorem rich_six_S14_two_poor_false_twenty (G : SimpleGraph (Fin 20)) (Hub Iso : Finset (Fin 20))
    (hdeg4 : ∀ h ∈ Hub, G.degree h = 4)
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdisj : Disjoint Hub Iso) (hHub : Hub.card = 12) (hIso : Iso.card = 6)
    (hdeg3 : ∀ v : Fin 20, 3 ≤ G.degree v) (hisodeg3 : ∀ t ∈ Iso, G.degree t = 3)
    (hdsum : ∑ w ∈ Hub, G.degree w = 48)
    (hleak : ∑ h ∈ Hub, (G.neighborFinset h ∩ (Finset.univ \ (Hub ∪ Iso))).card ≤ 4)
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hno2hub : ¬∃ h₁ h₂ : Fin 20, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card)
    (hT : ¬∃ x y z : Fin 20, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧
      G.degree x + G.degree y + G.degree z ≤ 11)
    (hnocut : ¬ ZPoorCutConfig G)
    (z : Fin 20) (hz : z ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 20)))
    (hg1 : Fin 20) (hg2 : Fin 20) (hg1ne : hg1 ≠ hg2)
    (hg1mem : hg1 ∈ G.neighborFinset z ∩ Hub) (hg2mem : hg2 ∈ G.neighborFinset z ∩ Hub)
    (hg1poor : (G.neighborFinset hg1 ∩ Iso).card ≤ 1)
    (hg2poor : (G.neighborFinset hg2 ∩ Iso).card ≤ 1)
    (hr6 : (Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)).card = 6)
    (hS14 : ∑ r ∈ Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card),
        (G.neighborFinset r ∩ Iso).card = 14) :
    False := by
  classical
  set R : Finset (Fin 20) := Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card) with hRdef
  set P : Finset (Fin 20) := Hub.filter (fun h => ¬ 2 ≤ (G.neighborFinset h ∩ Iso).card) with hPdef
  have hRsubHub : R ⊆ Hub := Finset.filter_subset _ _
  have hsum18 : ∑ a ∈ Hub, (G.neighborFinset a ∩ Iso).card = 18 := by
    have := hub_iso_sum_twenty G Hub Iso hiso3; rw [hIso] at this; omega
  have hPcard : P.card = 6 := by
    have := Finset.card_filter_add_card_filter_not (s := Hub)
      (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)
    rw [← hRdef, ← hPdef, hHub] at this; omega
  have hPsum : ∑ g ∈ P, (G.neighborFinset g ∩ Iso).card = 4 := by
    have hsp : (∑ r ∈ R, (G.neighborFinset r ∩ Iso).card)
        + ∑ g ∈ P, (G.neighborFinset g ∩ Iso).card = 18 := by
      rw [hRdef, hPdef,
        Finset.sum_filter_add_sum_filter_not Hub (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)]
      exact hsum18
    rw [hS14] at hsp; omega
  have hPle1 : ∀ g ∈ P, (G.neighborFinset g ∩ Iso).card ≤ 1 := by
    intro g hg; rw [hPdef, Finset.mem_filter] at hg; omega
  have hg1Hub : hg1 ∈ Hub := (Finset.mem_inter.mp hg1mem).2
  have hg2Hub : hg2 ∈ Hub := (Finset.mem_inter.mp hg2mem).2
  have hg1P : hg1 ∈ P := by rw [hPdef, Finset.mem_filter]; exact ⟨hg1Hub, by omega⟩
  have hg2P : hg2 ∈ P := by rw [hPdef, Finset.mem_filter]; exact ⟨hg2Hub, by omega⟩
  -- `N(z) ∩ Hub = {hg1, hg2}` — both poor.
  obtain ⟨_, hzhub2, _⟩ :=
    z_two_hub_nbrs_twenty G Hub Iso hiso3 hdisj hHub hIso hdsum hdeg3 hisodeg3 hleak z hz
  have hNz : G.neighborFinset z ∩ Hub = {hg1, hg2} := by
    refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
    · intro x hx; rw [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hg1mem
      · exact hg2mem
    · rw [hzhub2, Finset.card_insert_of_notMem (by simp [hg1ne]), Finset.card_singleton]
  have hzpoorall : ∀ h ∈ G.neighborFinset z ∩ Hub, h ∉ R := by
    intro h hh; rw [hNz, Finset.mem_insert, Finset.mem_singleton] at hh
    rw [hRdef, Finset.mem_filter]
    rcases hh with rfl | rfl
    · rintro ⟨_, h2⟩; omega
    · rintro ⟨_, h2⟩; omega
  -- A `z`-side twin fires the reusable pigeonhole cut.
  by_cases h1 : 1 ≤ (G.neighborFinset hg1 ∩ Iso).card
  · have h1eq : (G.neighborFinset hg1 ∩ Iso).card = 1 := by omega
    obtain ⟨cstar, hcs⟩ := Finset.card_eq_one.mp h1eq
    exact hnocut (Or.inl (two_poor_zleaf_pigeonhole_twenty G Hub Iso hdeg4 hiso3 hdisj hHub hIso
      hdsum hdeg3 hisodeg3 hleak R hRdef hg1 z cstar hg1Hub hz
      ((G.mem_neighborFinset z hg1).mp (Finset.mem_inter.mp hg1mem).1) hcs hzpoorall (by omega)))
  by_cases h2 : 1 ≤ (G.neighborFinset hg2 ∩ Iso).card
  · have h2eq : (G.neighborFinset hg2 ∩ Iso).card = 1 := by omega
    obtain ⟨cstar, hcs⟩ := Finset.card_eq_one.mp h2eq
    exact hnocut (Or.inl (two_poor_zleaf_pigeonhole_twenty G Hub Iso hdeg4 hiso3 hdisj hHub hIso
      hdsum hdeg3 hisodeg3 hleak R hRdef hg2 z cstar hg2Hub hz
      ((G.mem_neighborFinset z hg2).mp (Finset.mem_inter.mp hg2mem).1) hcs hzpoorall (by omega)))
  push Not at h1 h2
  have h1z : (G.neighborFinset hg1 ∩ Iso).card = 0 := by omega
  have h2z : (G.neighborFinset hg2 ∩ Iso).card = 0 := by omega
  -- Every other poor hub carries exactly one twin (`∑_P = 4` over the four remaining poor hubs).
  have hpoor1 : ∀ g ∈ P, g ≠ hg1 → g ≠ hg2 → (G.neighborFinset g ∩ Iso).card = 1 := by
    intro g hgP hne1 hne2
    have e1 := Finset.add_sum_erase P (fun a => (G.neighborFinset a ∩ Iso).card) hg1P
    have hg2er : hg2 ∈ P.erase hg1 := Finset.mem_erase.mpr ⟨Ne.symm hg1ne, hg2P⟩
    have e2 := Finset.add_sum_erase (P.erase hg1) (fun a => (G.neighborFinset a ∩ Iso).card) hg2er
    have hger : g ∈ (P.erase hg1).erase hg2 :=
      Finset.mem_erase.mpr ⟨hne2, Finset.mem_erase.mpr ⟨hne1, hgP⟩⟩
    have e3 := Finset.add_sum_erase ((P.erase hg1).erase hg2)
      (fun a => (G.neighborFinset a ∩ Iso).card) hger
    have hrest : ∑ a ∈ ((P.erase hg1).erase hg2).erase g, (G.neighborFinset a ∩ Iso).card ≤ 3 := by
      have hcardE : (((P.erase hg1).erase hg2).erase g).card = 3 := by
        rw [Finset.card_erase_of_mem hger, Finset.card_erase_of_mem hg2er,
          Finset.card_erase_of_mem hg1P, hPcard]
      calc ∑ a ∈ ((P.erase hg1).erase hg2).erase g, (G.neighborFinset a ∩ Iso).card
          ≤ ∑ _a ∈ ((P.erase hg1).erase hg2).erase g, 1 :=
            Finset.sum_le_sum (fun a ha => hPle1 a
              (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase ha))))
        _ = (((P.erase hg1).erase hg2).erase g).card := by
            rw [Finset.sum_const, smul_eq_mul, mul_one]
        _ = 3 := hcardE
    have hgle := hPle1 g hgP
    omega
  -- The `M`-partner `zp` and its two hub-neighbours `g3, g4`.
  have hZcard : (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 20)).card = 2 :=
    z_card_two_twenty Hub Iso hdisj hHub hIso
  have hzer : ((Finset.univ \ (Hub ∪ Iso) : Finset (Fin 20)).erase z).card = 1 := by
    rw [Finset.card_erase_of_mem hz, hZcard]
  obtain ⟨zp, hzp⟩ := Finset.card_eq_one.mp hzer
  have hzpZe : zp ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 20)).erase z := by
    rw [hzp]; exact Finset.mem_singleton_self _
  have hzpZ : zp ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 20)) := Finset.mem_of_mem_erase hzpZe
  have hzpz : zp ≠ z := (Finset.mem_erase.mp hzpZe).1
  have hzpnotHub : zp ∉ Hub := by
    have h := hzpZ; rw [Finset.mem_sdiff, Finset.mem_union, not_or] at h; exact h.2.1
  have hzpnotIso : zp ∉ Iso := by
    have h := hzpZ; rw [Finset.mem_sdiff, Finset.mem_union, not_or] at h; exact h.2.2
  obtain ⟨_, hzphub2, _⟩ :=
    z_two_hub_nbrs_twenty G Hub Iso hiso3 hdisj hHub hIso hdsum hdeg3 hisodeg3 hleak zp hzpZ
  obtain ⟨g3, g4, hg34, hNzp⟩ := Finset.card_eq_two.mp hzphub2
  have hg3mem : g3 ∈ G.neighborFinset zp ∩ Hub := by rw [hNzp]; exact Finset.mem_insert_self _ _
  have hg4mem : g4 ∈ G.neighborFinset zp ∩ Hub := by
    rw [hNzp]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hg3Hub : g3 ∈ Hub := (Finset.mem_inter.mp hg3mem).2
  have hg4Hub : g4 ∈ Hub := (Finset.mem_inter.mp hg4mem).2
  have hzpg3 : G.Adj zp g3 := (G.mem_neighborFinset zp g3).mp (Finset.mem_inter.mp hg3mem).1
  have hzpg4 : G.Adj zp g4 := (G.mem_neighborFinset zp g4).mp (Finset.mem_inter.mp hg4mem).1
  -- **The rich-`Z`-hub kill:** any rich hub meeting `zp` yields a `Z`-leaf `TwoHubConfig`.
  have main : ∀ g : Fin 20, g ∈ Hub → G.Adj zp g →
      2 ≤ (G.neighborFinset g ∩ Iso).card → False := by
    intro g hgHub hzpg hgiso2
    -- The iso-degree-`≥ 3` pool `A3` satisfies `∑_{A3} = 2 + 2|A3|`, forcing `|A3| ∈ {1, 2}`.
    set A3 : Finset (Fin 20) := R.filter (fun h => 3 ≤ (G.neighborFinset h ∩ Iso).card)
      with hA3def
    have hA3subR : A3 ⊆ R := Finset.filter_subset _ _
    have hA3le2 : A3.card ≤ 2 := by
      have heq : A3
          = Hub.filter (fun h => G.degree h = 4 ∧ 3 ≤ (G.neighborFinset h ∩ Iso).card) := by
        rw [hA3def, hRdef, Finset.filter_filter]
        apply Finset.filter_congr
        intro a ha; constructor
        · rintro ⟨_, h3⟩; exact ⟨hdeg4 a ha, h3⟩
        · rintro ⟨_, h3⟩; exact ⟨by omega, h3⟩
      rw [heq]; exact rich_a3_count_le_two_twenty G Hub Iso hdisj hshare hno2hub
    set B : Finset (Fin 20) := R.filter (fun h => ¬ 3 ≤ (G.neighborFinset h ∩ Iso).card)
      with hBdef
    have hAsplit : (∑ r ∈ A3, (G.neighborFinset r ∩ Iso).card)
        + ∑ r ∈ B, (G.neighborFinset r ∩ Iso).card = 14 := by
      rw [hA3def, hBdef,
        Finset.sum_filter_add_sum_filter_not R (fun h => 3 ≤ (G.neighborFinset h ∩ Iso).card)]
      exact hS14
    have hBval : ∑ r ∈ B, (G.neighborFinset r ∩ Iso).card = 2 * B.card := by
      rw [Finset.sum_congr rfl (fun r hr => ?_), Finset.sum_const, smul_eq_mul, mul_comm]
      rw [hBdef, Finset.mem_filter] at hr
      have h2 : 2 ≤ (G.neighborFinset r ∩ Iso).card := by
        have hrR := hr.1; rw [hRdef, Finset.mem_filter] at hrR; exact hrR.2
      omega
    have hcards : A3.card + B.card = 6 := by
      have := Finset.card_filter_add_card_filter_not (s := R)
        (fun h => 3 ≤ (G.neighborFinset h ∩ Iso).card)
      rw [← hA3def, ← hBdef, hr6] at this; exact this
    have hTge : 3 * A3.card ≤ ∑ r ∈ A3, (G.neighborFinset r ∩ Iso).card := by
      calc 3 * A3.card = ∑ _r ∈ A3, 3 := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
        _ ≤ ∑ r ∈ A3, (G.neighborFinset r ∩ Iso).card := by
            apply Finset.sum_le_sum; intro r hr
            rw [hA3def, Finset.mem_filter] at hr; exact hr.2
    have hTle : ∑ r ∈ A3, (G.neighborFinset r ∩ Iso).card ≤ 4 * A3.card := by
      calc ∑ r ∈ A3, (G.neighborFinset r ∩ Iso).card ≤ ∑ _r ∈ A3, 4 := by
            apply Finset.sum_le_sum; intro r hr
            calc (G.neighborFinset r ∩ Iso).card ≤ (G.neighborFinset r).card :=
                  Finset.card_le_card Finset.inter_subset_left
              _ = 4 := by
                  rw [G.card_neighborFinset_eq_degree, hdeg4 r (hRsubHub (hA3subR hr))]
        _ = 4 * A3.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    have hA3cases : A3.card = 1 ∨ A3.card = 2 := by omega
    rcases hA3cases with h1c | h2c
    · -- `{2,2,2,2,2,4}`: the lone `A3` hub has iso-degree `4`, non-adjacent to every hub and `zp`.
      obtain ⟨astar, hA3eq⟩ := Finset.card_eq_one.mp h1c
      have hastarA3 : astar ∈ A3 := by rw [hA3eq]; exact Finset.mem_singleton_self _
      have hastarHub : astar ∈ Hub := hRsubHub (hA3subR hastarA3)
      have hastar4 : (G.neighborFinset astar ∩ Iso).card = 4 := by
        have hTsum : ∑ r ∈ A3, (G.neighborFinset r ∩ Iso).card
            = (G.neighborFinset astar ∩ Iso).card := by rw [hA3eq, Finset.sum_singleton]
        omega
      have hNastar : G.neighborFinset astar ⊆ Iso := by
        have hd4 : (G.neighborFinset astar).card = 4 := by
          rw [G.card_neighborFinset_eq_degree, hdeg4 astar hastarHub]
        have heq : G.neighborFinset astar ∩ Iso = G.neighborFinset astar :=
          Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by rw [hd4, hastar4])
        rw [← heq]; exact Finset.inter_subset_right
      have hnzp : ¬G.Adj astar zp := fun h =>
        hzpnotIso (hNastar ((G.mem_neighborFinset astar zp).mpr h))
      have hastarg : astar ≠ g := fun he => hnzp (by rw [he]; exact hzpg.symm)
      have hnadjg : ¬G.Adj astar g :=
        iso_deg_four_nonadj_hub_twenty G Hub Iso hdisj hdeg4 astar g hastarHub hgHub hastar4
      obtain ⟨a, b, haIso, hbIso, hab, ha1, hb1, hna2, hnb2⟩ :=
        exists_two_private_twins_twenty G Hub Iso hshare astar g hastarHub hgHub
          (hdeg4 astar hastarHub) (hdeg4 g hgHub) hastarg hnadjg (by omega)
      obtain ⟨c, hcIso, hcg, hcastar⟩ :=
        exists_one_private_twin_twenty G Hub Iso hshare g astar hgHub hastarHub
          (hdeg4 g hgHub) (hdeg4 astar hastarHub) hastarg hnadjg hgiso2
      exact hnocut (Or.inl (two_hub_zleaf_twenty G Hub Iso hiso3 hdisj hHub hIso hdsum hdeg3
        hisodeg3 hleak astar g a b c zp hastarHub hgHub (hdeg4 astar hastarHub) (hdeg4 g hgHub)
        haIso hbIso hcIso hzpZ ha1 hb1 hcg hzpg hnadjg hcastar hnzp hna2 hnb2 hab))
    · -- `{2,2,2,2,3,3}`: the two `A3` hubs have iso-degree exactly `3`.
      obtain ⟨w1, w2, hw12ne, hA3eq⟩ := Finset.card_eq_two.mp h2c
      have hw1A3 : w1 ∈ A3 := by rw [hA3eq]; exact Finset.mem_insert_self _ _
      have hw2A3 : w2 ∈ A3 := by
        rw [hA3eq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      have hw1Hub : w1 ∈ Hub := hRsubHub (hA3subR hw1A3)
      have hw2Hub : w2 ∈ Hub := hRsubHub (hA3subR hw2A3)
      have hw1ge : 3 ≤ (G.neighborFinset w1 ∩ Iso).card := by
        have h := hw1A3; rw [hA3def, Finset.mem_filter] at h; exact h.2
      have hw2ge : 3 ≤ (G.neighborFinset w2 ∩ Iso).card := by
        have h := hw2A3; rw [hA3def, Finset.mem_filter] at h; exact h.2
      have hTpair : (G.neighborFinset w1 ∩ Iso).card + (G.neighborFinset w2 ∩ Iso).card
          = ∑ r ∈ A3, (G.neighborFinset r ∩ Iso).card := by
        rw [hA3eq, Finset.sum_pair hw12ne]
      have hw1eq3 : (G.neighborFinset w1 ∩ Iso).card = 3 := by omega
      by_cases hw12adj : G.Adj w1 w2
      · -- Adjacent pair: `N(w1) = 3` twins `∪ {w2}`, so `w1 ≁ zp, g` — assemble on `(w1, g)`.
        have hw1sd_eq : (G.neighborFinset w1) \ Iso = {w2} := by
          have hw1d4 : (G.neighborFinset w1).card = 4 := by
            rw [G.card_neighborFinset_eq_degree, hdeg4 w1 hw1Hub]
          have hw1sd1 : ((G.neighborFinset w1) \ Iso).card = 1 := by
            have := Finset.card_sdiff_add_card_inter (G.neighborFinset w1) Iso
            omega
          obtain ⟨u, hu⟩ := Finset.card_eq_one.mp hw1sd1
          have hw2m : w2 ∈ (G.neighborFinset w1) \ Iso := Finset.mem_sdiff.mpr
            ⟨(G.mem_neighborFinset w1 w2).mpr hw12adj, Finset.disjoint_left.mp hdisj hw2Hub⟩
          rw [hu] at hw2m ⊢
          rw [Finset.mem_singleton] at hw2m
          rw [hw2m]
        have hw1only : ∀ x : Fin 20, G.Adj w1 x → x ∉ Iso → x = w2 := by
          intro x hx hxI
          have hmem : x ∈ (G.neighborFinset w1) \ Iso :=
            Finset.mem_sdiff.mpr ⟨(G.mem_neighborFinset w1 x).mpr hx, hxI⟩
          rw [hw1sd_eq, Finset.mem_singleton] at hmem; exact hmem
        have hw2sd_eq : (G.neighborFinset w2) \ Iso = {w1} := by
          have hw2d4 : (G.neighborFinset w2).card = 4 := by
            rw [G.card_neighborFinset_eq_degree, hdeg4 w2 hw2Hub]
          have hw2eq3 : (G.neighborFinset w2 ∩ Iso).card = 3 := by omega
          have hw2sd1 : ((G.neighborFinset w2) \ Iso).card = 1 := by
            have := Finset.card_sdiff_add_card_inter (G.neighborFinset w2) Iso
            omega
          obtain ⟨u, hu⟩ := Finset.card_eq_one.mp hw2sd1
          have hw1m : w1 ∈ (G.neighborFinset w2) \ Iso := Finset.mem_sdiff.mpr
            ⟨(G.mem_neighborFinset w2 w1).mpr hw12adj.symm, Finset.disjoint_left.mp hdisj hw1Hub⟩
          rw [hu] at hw1m ⊢
          rw [Finset.mem_singleton] at hw1m
          rw [hw1m]
        have hw2only : ∀ x : Fin 20, G.Adj w2 x → x ∉ Iso → x = w1 := by
          intro x hx hxI
          have hmem : x ∈ (G.neighborFinset w2) \ Iso :=
            Finset.mem_sdiff.mpr ⟨(G.mem_neighborFinset w2 x).mpr hx, hxI⟩
          rw [hw2sd_eq, Finset.mem_singleton] at hmem; exact hmem
        have hw1nzp : ¬G.Adj w1 zp := fun h =>
          hzpnotHub (by rw [hw1only zp h hzpnotIso]; exact hw2Hub)
        have hgnotIso : g ∉ Iso := Finset.disjoint_left.mp hdisj hgHub
        have hgne2 : g ≠ w2 := by
          rintro rfl
          exact hzpnotHub (by rw [hw2only zp hzpg.symm hzpnotIso]; exact hw1Hub)
        have hw1neg : w1 ≠ g := by
          rintro rfl
          exact hzpnotHub (by rw [hw1only zp hzpg.symm hzpnotIso]; exact hw2Hub)
        have hw1ng : ¬G.Adj w1 g := fun h => hgne2 (hw1only g h hgnotIso)
        obtain ⟨a, b, haIso, hbIso, hab, ha1, hb1, hna2, hnb2⟩ :=
          exists_two_private_twins_twenty G Hub Iso hshare w1 g hw1Hub hgHub
            (hdeg4 w1 hw1Hub) (hdeg4 g hgHub) hw1neg hw1ng (by omega)
        obtain ⟨c, hcIso, hcg, hcw1⟩ :=
          exists_one_private_twin_twenty G Hub Iso hshare g w1 hgHub hw1Hub
            (hdeg4 g hgHub) (hdeg4 w1 hw1Hub) hw1neg hw1ng hgiso2
        exact hnocut (Or.inl (two_hub_zleaf_twenty G Hub Iso hiso3 hdisj hHub hIso hdsum hdeg3
          hisodeg3 hleak w1 g a b c zp hw1Hub hgHub (hdeg4 w1 hw1Hub) (hdeg4 g hgHub)
          haIso hbIso hcIso hzpZ ha1 hb1 hcg hzpg hw1ng hcw1 hw1nzp hna2 hnb2 hab))
      · -- Non-adjacent pair: two iso-degree-`3` hubs contradict `hno2hub` directly.
        exact two_nonadj_hubs_contra_twenty G Hub Iso hdeg4 hshare hno2hub w1 w2 hw1Hub hw2Hub
          hw12ne hw12adj hw1ge hw2ge
  by_cases hg3rich : 2 ≤ (G.neighborFinset g3 ∩ Iso).card
  · exact main g3 hg3Hub hzpg3 hg3rich
  by_cases hg4rich : 2 ≤ (G.neighborFinset g4 ∩ Iso).card
  · exact main g4 hg4Hub hzpg4 hg4rich
  -- Both `zp`-hubs poor: `g3 ∉ {hg1, hg2}` carries exactly one twin — the `zp`-side cut fires.
  have hzppoorall : ∀ h ∈ G.neighborFinset zp ∩ Hub, h ∉ R := by
    intro h hh; rw [hNzp, Finset.mem_insert, Finset.mem_singleton] at hh
    rw [hRdef, Finset.mem_filter]
    rcases hh with rfl | rfl
    · rintro ⟨_, hcon⟩; exact hg3rich hcon
    · rintro ⟨_, hcon⟩; exact hg4rich hcon
  have hg3P : g3 ∈ P := by rw [hPdef, Finset.mem_filter]; exact ⟨hg3Hub, hg3rich⟩
  have hnb1 := no_hub_adj_both_mends_twenty G Hub Iso hdeg4 hiso3 hdisj hHub hIso hdsum hdeg3
    hisodeg3 hleak hT hg1 hg1Hub z hz zp hzpZ (Ne.symm hzpz)
  have hnb2 := no_hub_adj_both_mends_twenty G Hub Iso hdeg4 hiso3 hdisj hHub hIso hdsum hdeg3
    hisodeg3 hleak hT hg2 hg2Hub z hz zp hzpZ (Ne.symm hzpz)
  have hg3ne1 : g3 ≠ hg1 := by
    rintro rfl
    exact hnb1 ⟨((G.mem_neighborFinset z g3).mp (Finset.mem_inter.mp hg1mem).1).symm, hzpg3.symm⟩
  have hg3ne2 : g3 ≠ hg2 := by
    rintro rfl
    exact hnb2 ⟨((G.mem_neighborFinset z g3).mp (Finset.mem_inter.mp hg2mem).1).symm, hzpg3.symm⟩
  have hg3one : (G.neighborFinset g3 ∩ Iso).card = 1 := hpoor1 g3 hg3P hg3ne1 hg3ne2
  obtain ⟨cstar, hcs⟩ := Finset.card_eq_one.mp hg3one
  exact hnocut (Or.inl (two_poor_zleaf_pigeonhole_twenty G Hub Iso hdeg4 hiso3 hdisj hHub hIso
    hdsum hdeg3 hisodeg3 hleak R hRdef g3 zp cstar hg3Hub hzpZ hzpg3 hcs hzppoorall (by omega)))

/-- **The low-density rich residual (`S ≤ 16`) — dispatched to the regime provers.**
The rich-hub count `r := |R|` is `6` or `7` (`hr67`) and the rich iso-incidence sum
`S := ∑_R |N ∩ Iso|` satisfies (the `12 − r` poor hubs absorb at most one iso-incidence each,
and every rich hub carries `≥ 2`):

* `r = 7` ⟹ `S ∈ {14, 15, 16}`: `S = 14 → ` `z`-side cut; `S = 15 → mpartner_meets_poor`;
  `S = 16 → rich_seven_S16_two_poor_false`;
* `r = 6` ⟹ `S ∈ {12, 13, 14, 15, 16}`: `S ∈ {12, 13} → ` `z`-side cut; `S = 14 → ` the NEW
  `rich_six_S14_two_poor_false_twenty`; `S ≥ 15` assembles two non-adjacent high hubs
  (`two_high_hubs_sum_ge_seven_contra`). -/
theorem low_rich_iso_residual_twenty (G : SimpleGraph (Fin 20)) (Hub Iso : Finset (Fin 20))
    (hdeg4 : ∀ h ∈ Hub, G.degree h = 4)
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdisj : Disjoint Hub Iso) (hHub : Hub.card = 12) (hIso : Iso.card = 6)
    (hdeg3 : ∀ v : Fin 20, 3 ≤ G.degree v) (hisodeg3 : ∀ t ∈ Iso, G.degree t = 3)
    (hdsum : ∑ w ∈ Hub, G.degree w = 48)
    (hleak : ∑ h ∈ Hub, (G.neighborFinset h ∩ (Finset.univ \ (Hub ∪ Iso))).card ≤ 4)
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hno2hub : ¬∃ h₁ h₂ : Fin 20, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card)
    (hC4 : ¬∃ a b c d : Fin 20, ({a, b, c, d} : Finset (Fin 20)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (hK23 : ¬∃ a b c d e : Fin 20, ({a, b, c, d, e} : Finset (Fin 20)).card = 5 ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
      G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 19)
    (hT : ¬∃ x y z : Fin 20, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧
      G.degree x + G.degree y + G.degree z ≤ 11)
    (hnocut : ¬ ZPoorCutConfig G)
    (z : Fin 20) (hz : z ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 20)))
    (hg1 : Fin 20) (hg2 : Fin 20) (hg1ne : hg1 ≠ hg2)
    (hg1mem : hg1 ∈ G.neighborFinset z ∩ Hub) (hg2mem : hg2 ∈ G.neighborFinset z ∩ Hub)
    (hg1poor : (G.neighborFinset hg1 ∩ Iso).card ≤ 1)
    (hg2poor : (G.neighborFinset hg2 ∩ Iso).card ≤ 1)
    (hres : G.Adj hg1 hg2 ∨ (G.neighborFinset hg1 ∩ G.neighborFinset hg2 ∩ Iso).card = 0)
    (hr67 : (Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)).card = 6 ∨
      (Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)).card = 7)
    (hSlo : ∑ r ∈ Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card),
        (G.neighborFinset r ∩ Iso).card ≤ 16) :
    False := by
  classical
  set R : Finset (Fin 20) := Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card) with hRdef
  set P : Finset (Fin 20) := Hub.filter (fun h => ¬ 2 ≤ (G.neighborFinset h ∩ Iso).card) with hPdef
  have hRsubHub : R ⊆ Hub := Finset.filter_subset _ _
  have hRmem : ∀ a, a ∈ R ↔ a ∈ Hub ∧ 2 ≤ (G.neighborFinset a ∩ Iso).card := by
    intro a; rw [hRdef, Finset.mem_filter]
  set S : ℕ := ∑ r ∈ R, (G.neighborFinset r ∩ Iso).card with hSdef
  -- Total iso-incidence sum is `18`.
  have hsum18 : ∑ a ∈ Hub, (G.neighborFinset a ∩ Iso).card = 18 := by
    have := hub_iso_sum_twenty G Hub Iso hiso3; rw [hIso] at this; omega
  -- Split over `R` and the poor complement `P`.
  have hsplitRP : S + ∑ g ∈ P, (G.neighborFinset g ∩ Iso).card = 18 := by
    rw [hSdef, hRdef, hPdef,
      Finset.sum_filter_add_sum_filter_not Hub (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)]
    exact hsum18
  have hRPcard : R.card + P.card = 12 := by
    have := Finset.card_filter_add_card_filter_not (s := Hub)
      (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)
    rw [← hRdef, ← hPdef, hHub] at this; exact this
  have hPle : ∑ g ∈ P, (G.neighborFinset g ∩ Iso).card ≤ P.card := by
    calc ∑ g ∈ P, (G.neighborFinset g ∩ Iso).card ≤ ∑ _g ∈ P, 1 := by
          apply Finset.sum_le_sum; intro g hg
          rw [hPdef, Finset.mem_filter] at hg; omega
      _ = P.card := by rw [Finset.sum_const, smul_eq_mul, mul_one]
  -- Every rich hub carries `≥ 2` iso-incidences, so `S ≥ 2r`.
  have hS2r : 2 * R.card ≤ S := by
    rw [hSdef]
    calc 2 * R.card = ∑ _r ∈ R, 2 := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ ∑ r ∈ R, (G.neighborFinset r ∩ Iso).card :=
          Finset.sum_le_sum (fun r hr => ((hRmem r).mp hr).2)
  -- `N2`: at most two rich hubs have iso-degree `≥ 3` (shared infrastructure for the clean branch).
  have clean_two_hubs : ∀ (k : ℕ), R.card = k → 7 ≤ S - 2 * (k - 2) → 2 ≤ k → False := by
    intro k hrk hge hk2
    set A3 : Finset (Fin 20) := R.filter (fun h => 3 ≤ (G.neighborFinset h ∩ Iso).card)
      with hA3def
    have hN2 : A3.card ≤ 2 := by
      have heq : A3 = Hub.filter (fun h => G.degree h = 4 ∧ 3 ≤ (G.neighborFinset h ∩ Iso).card) := by
        rw [hA3def, hRdef, Finset.filter_filter]
        apply Finset.filter_congr
        intro a ha; constructor
        · rintro ⟨_, h3⟩; exact ⟨hdeg4 a ha, h3⟩
        · rintro ⟨_, h3⟩; exact ⟨by omega, h3⟩
      rw [heq]; exact rich_a3_count_le_two_twenty G Hub Iso hdisj hshare hno2hub
    set B : Finset (Fin 20) := R.filter (fun h => ¬ 3 ≤ (G.neighborFinset h ∩ Iso).card)
      with hBdef
    set T : ℕ := ∑ r ∈ A3, (G.neighborFinset r ∩ Iso).card with hTdef
    have hAsplit : T + ∑ r ∈ B, (G.neighborFinset r ∩ Iso).card = S := by
      rw [hTdef, hSdef, hA3def, hBdef]
      exact Finset.sum_filter_add_sum_filter_not R _ _
    have hBval : ∑ r ∈ B, (G.neighborFinset r ∩ Iso).card = 2 * B.card := by
      rw [Finset.sum_congr rfl (fun r hr => ?_), Finset.sum_const, smul_eq_mul, mul_comm]
      rw [hBdef, Finset.mem_filter] at hr
      have h2 := ((hRmem r).mp hr.1).2
      omega
    have hcardk : A3.card + B.card = k := by
      have := Finset.card_filter_add_card_filter_not (s := R)
        (fun h => 3 ≤ (G.neighborFinset h ∩ Iso).card)
      rw [← hA3def, ← hBdef, hrk] at this; exact this
    have hTge : 3 * A3.card ≤ T := by
      rw [hTdef]
      calc 3 * A3.card = ∑ _r ∈ A3, 3 := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
        _ ≤ ∑ r ∈ A3, (G.neighborFinset r ∩ Iso).card := by
            apply Finset.sum_le_sum; intro r hr
            rw [hA3def, Finset.mem_filter] at hr; exact hr.2
    have hTle : T ≤ 4 * A3.card := by
      rw [hTdef]
      calc ∑ r ∈ A3, (G.neighborFinset r ∩ Iso).card ≤ ∑ _r ∈ A3, 4 := by
            apply Finset.sum_le_sum; intro r hr
            rw [hA3def, Finset.mem_filter] at hr
            have hrHub : r ∈ Hub := hRsubHub hr.1
            calc (G.neighborFinset r ∩ Iso).card ≤ (G.neighborFinset r).card :=
                  Finset.card_le_card Finset.inter_subset_left
              _ = 4 := by rw [G.card_neighborFinset_eq_degree, hdeg4 r hrHub]
        _ = 4 * A3.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    -- `S = T + 2·|B|`, `|A3| + |B| = k`, so `T = S − 2(k − |A3|)`; with `T ≤ 4|A3|`, `|A3| ≤ 2`
    -- and `7 ≤ S − 2(k − 2)`, force `|A3| = 2`.
    have hk2card : A3.card = 2 := by rw [hBval] at hAsplit; omega
    obtain ⟨w1, w2, hw12, hA3eq⟩ := Finset.card_eq_two.mp hk2card
    have hw1A3 : w1 ∈ A3 := by rw [hA3eq]; exact Finset.mem_insert_self _ _
    have hw2A3 : w2 ∈ A3 := by
      rw [hA3eq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    have hw1Hub : w1 ∈ Hub := hRsubHub (Finset.mem_of_mem_filter _ hw1A3)
    have hw2Hub : w2 ∈ Hub := hRsubHub (Finset.mem_of_mem_filter _ hw2A3)
    have hw1ge : 3 ≤ (G.neighborFinset w1 ∩ Iso).card := (Finset.mem_filter.mp hw1A3).2
    have hw2ge : 3 ≤ (G.neighborFinset w2 ∩ Iso).card := (Finset.mem_filter.mp hw2A3).2
    have hTpair : (G.neighborFinset w1 ∩ Iso).card + (G.neighborFinset w2 ∩ Iso).card = T := by
      rw [hTdef, hA3eq, Finset.sum_pair hw12]
    have hsum7 : 7 ≤ (G.neighborFinset w1 ∩ Iso).card + (G.neighborFinset w2 ∩ Iso).card := by
      rw [hBval] at hAsplit; omega
    exact two_high_hubs_sum_ge_seven_contra_twenty G Hub Iso hdisj hdeg4 hshare hno2hub w1 w2
      hw1Hub hw2Hub hw12 hw1ge hw2ge hsum7
  -- Shared `z`-side cut infrastructure: `hg1, hg2` are poor hubs in `P`; whenever the poor-incidence
  -- sum `∑_P = 18 − S` exceeds the capacity `|P| − 2` of the *other* poor hubs, at least one of
  -- `hg1, hg2` carries a private twin (`hbothpoor`), feeding `z_side_poor_cut_twenty`.
  have hg1Hub : hg1 ∈ Hub := (Finset.mem_inter.mp hg1mem).2
  have hg2Hub : hg2 ∈ Hub := (Finset.mem_inter.mp hg2mem).2
  have hg1P : hg1 ∈ P := by rw [hPdef, Finset.mem_filter]; exact ⟨hg1Hub, by omega⟩
  have hg2P : hg2 ∈ P := by rw [hPdef, Finset.mem_filter]; exact ⟨hg2Hub, by omega⟩
  have hPle1 : ∀ g ∈ P, (G.neighborFinset g ∩ Iso).card ≤ 1 := by
    intro g hg; rw [hPdef, Finset.mem_filter] at hg; omega
  have hbothpoor : (G.neighborFinset hg1 ∩ Iso).card = 0 → (G.neighborFinset hg2 ∩ Iso).card = 0 →
      ∑ g ∈ P, (G.neighborFinset g ∩ Iso).card ≤ P.card - 2 := by
    intro _h1z _h2z
    have hg2er : hg2 ∈ P.erase hg1 := Finset.mem_erase.mpr ⟨Ne.symm hg1ne, hg2P⟩
    have he1 := Finset.add_sum_erase P (fun g => (G.neighborFinset g ∩ Iso).card) hg1P
    have he2 := Finset.add_sum_erase (P.erase hg1) (fun g => (G.neighborFinset g ∩ Iso).card) hg2er
    have hcardE : ((P.erase hg1).erase hg2).card = P.card - 2 := by
      rw [Finset.card_erase_of_mem hg2er, Finset.card_erase_of_mem hg1P]; omega
    have hrestle : ∑ g ∈ (P.erase hg1).erase hg2, (G.neighborFinset g ∩ Iso).card
        ≤ ((P.erase hg1).erase hg2).card := by
      calc ∑ g ∈ (P.erase hg1).erase hg2, (G.neighborFinset g ∩ Iso).card
          ≤ ∑ _g ∈ (P.erase hg1).erase hg2, 1 :=
            Finset.sum_le_sum (fun g hg => hPle1 g
              (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hg)))
        _ = ((P.erase hg1).erase hg2).card := by rw [Finset.sum_const, smul_eq_mul, mul_one]
    rw [hcardE] at hrestle; omega
  rcases hr67 with hr6 | hr7
  · -- `r = 6`: `P.card = 6`, so `S ≥ 12` (both from `∑_P ≤ |P|` and from `S ≥ 2r`).
    have hPcard : P.card = 6 := by omega
    have hS12ge : 12 ≤ S := by omega
    rcases (by omega : S = 12 ∨ S = 13 ∨ S = 14 ∨ 15 ≤ S) with hS12 | hS13 | hS14 | hS15
    · -- `r = 6`, `S = 12`: closed by the reusable `z`-side cut (`∑_P = 6 > 4 = |P| − 2`).
      refine hnocut (Or.inl (z_side_poor_cut_twenty G Hub Iso hdeg4 hiso3 hdisj hHub hIso hdsum
        hdeg3 hisodeg3 hleak z hz hg1 hg2 hg1ne hg1mem hg2mem hg1poor hg2poor ?_ (by rw [← hRdef]; omega)))
      by_contra hcon; push Not at hcon
      have hle := hbothpoor (by omega) (by omega); omega
    · -- `r = 6`, `S = 13`: closed by the reusable `z`-side cut (`∑_P = 5 > 4 = |P| − 2`).
      refine hnocut (Or.inl (z_side_poor_cut_twenty G Hub Iso hdeg4 hiso3 hdisj hHub hIso hdsum
        hdeg3 hisodeg3 hleak z hz hg1 hg2 hg1ne hg1mem hg2mem hg1poor hg2poor ?_ (by rw [← hRdef]; omega)))
      by_contra hcon; push Not at hcon
      have hle := hbothpoor (by omega) (by omega); omega
    · -- `r = 6`, `S = 14`: the NEW `n = 20` regime — the `M`-partner / rich-`Z`-hub kill.
      exact rich_six_S14_two_poor_false_twenty G Hub Iso hdeg4 hiso3 hdisj hHub hIso hdeg3
        hisodeg3 hdsum hleak hshare hno2hub hT hnocut z hz hg1 hg2 hg1ne hg1mem hg2mem hg1poor
        hg2poor hr6 hS14
    · -- `r = 6`, `S ≥ 15`: clean two non-adjacent high hubs.
      exact clean_two_hubs 6 hr6 (by omega) (by omega)
  · -- `r = 7`: `P.card = 5` and `S ≥ 2·7 = 14`.
    have hPcard : P.card = 5 := by omega
    have hS14ge : 14 ≤ S := by omega
    rcases (by omega : S = 14 ∨ S = 15 ∨ S = 16) with hS14 | hS15 | hS16
    · -- `r = 7`, `S = 14`: closed by the reusable `z`-side cut (`∑_P = 4 > 3 = |P| − 2`).
      refine hnocut (Or.inl (z_side_poor_cut_twenty G Hub Iso hdeg4 hiso3 hdisj hHub hIso hdsum
        hdeg3 hisodeg3 hleak z hz hg1 hg2 hg1ne hg1mem hg2mem hg1poor hg2poor ?_ (by rw [← hRdef]; omega)))
      by_contra hcon; push Not at hcon
      have hle := hbothpoor (by omega) (by omega); omega
    · -- `r = 7`, `S = 15`: the `M`-partner kill via the reusable cut.
      exact mpartner_meets_poor_twenty G Hub Iso hdeg4 hiso3 hdisj hHub hIso hdeg3 hisodeg3
        hdsum hleak hshare hno2hub hC4 hK23 hT hnocut z hz hg1 hg2 hg1ne hg1mem hg2mem hg1poor
        hg2poor hres hr7 hS15
    · -- `r = 7`, `S = 16`: the saturation kill via the reusable cut.
      exact rich_seven_S16_two_poor_false_twenty G Hub Iso hdeg4 hiso3 hdisj hHub hIso hdeg3
        hisodeg3 hdsum hleak hshare hno2hub hC4 hK23 hT hnocut z hz hg1 hg2 hg1ne hg1mem hg2mem
        hg1poor hg2poor hres hr7 hS16

/-- **Node A — `r = 7` under two poor hubs.**  The clean `S ≥ 17` sub-cases assemble a non-adjacent
degree-`4` pair (`two_high_hubs_sum_ge_seven_contra`); the `S ≤ 16` residual is dispatched through
`low_rich_iso_residual_twenty`. -/
theorem rich_seven_two_poor_false_twenty (G : SimpleGraph (Fin 20)) (Hub Iso : Finset (Fin 20))
    (hdeg4 : ∀ h ∈ Hub, G.degree h = 4)
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdisj : Disjoint Hub Iso) (hHub : Hub.card = 12) (hIso : Iso.card = 6)
    (hdeg3 : ∀ v : Fin 20, 3 ≤ G.degree v) (hisodeg3 : ∀ t ∈ Iso, G.degree t = 3)
    (hdsum : ∑ w ∈ Hub, G.degree w = 48)
    (hleak : ∑ h ∈ Hub, (G.neighborFinset h ∩ (Finset.univ \ (Hub ∪ Iso))).card ≤ 4)
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hno2hub : ¬∃ h₁ h₂ : Fin 20, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card)
    (hC4 : ¬∃ a b c d : Fin 20, ({a, b, c, d} : Finset (Fin 20)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (hK23 : ¬∃ a b c d e : Fin 20, ({a, b, c, d, e} : Finset (Fin 20)).card = 5 ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
      G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 19)
    (hT : ¬∃ x y z : Fin 20, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧
      G.degree x + G.degree y + G.degree z ≤ 11)
    (hnocut : ¬ ZPoorCutConfig G)
    (z : Fin 20) (hz : z ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 20)))
    (hg1 : Fin 20) (hg2 : Fin 20) (hg1ne : hg1 ≠ hg2)
    (hg1mem : hg1 ∈ G.neighborFinset z ∩ Hub) (hg2mem : hg2 ∈ G.neighborFinset z ∩ Hub)
    (hg1poor : (G.neighborFinset hg1 ∩ Iso).card ≤ 1)
    (hg2poor : (G.neighborFinset hg2 ∩ Iso).card ≤ 1)
    (hres : G.Adj hg1 hg2 ∨ (G.neighborFinset hg1 ∩ G.neighborFinset hg2 ∩ Iso).card = 0)
    (hr7 : (Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)).card = 7) :
    False := by
  classical
  set R : Finset (Fin 20) := Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card) with hRdef
  have hRsubHub : R ⊆ Hub := Finset.filter_subset _ _
  set S : ℕ := ∑ r ∈ R, (G.neighborFinset r ∩ Iso).card with hSdef
  have hsum18 : ∑ a ∈ Hub, (G.neighborFinset a ∩ Iso).card = 18 := by
    have := hub_iso_sum_twenty G Hub Iso hiso3; rw [hIso] at this; omega
  have hS18 : S ≤ 18 := by
    rw [hSdef]
    calc ∑ r ∈ R, (G.neighborFinset r ∩ Iso).card
        ≤ ∑ a ∈ Hub, (G.neighborFinset a ∩ Iso).card := Finset.sum_le_sum_of_subset hRsubHub
      _ = 18 := hsum18
  by_cases hSlo : S ≤ 16
  · exact low_rich_iso_residual_twenty G Hub Iso hdeg4 hiso3 hdisj hHub hIso hdeg3 hisodeg3
      hdsum hleak hshare hno2hub hC4 hK23 hT hnocut z hz hg1 hg2 hg1ne hg1mem hg2mem hg1poor hg2poor
      hres (Or.inr hr7) hSlo
  · -- `S ≥ 17`: clean two-hub assembly (`A3.card = 2`, sum `≥ 7`).
    have hS17 : 17 ≤ S := by omega
    set A3 : Finset (Fin 20) := R.filter (fun h => 3 ≤ (G.neighborFinset h ∩ Iso).card) with hA3def
    have hN2 : A3.card ≤ 2 := by
      have heq : A3 = Hub.filter (fun h => G.degree h = 4 ∧ 3 ≤ (G.neighborFinset h ∩ Iso).card) := by
        rw [hA3def, hRdef, Finset.filter_filter]
        apply Finset.filter_congr
        intro a ha; constructor
        · rintro ⟨_, h3⟩; exact ⟨hdeg4 a ha, h3⟩
        · rintro ⟨_, h3⟩; exact ⟨by omega, h3⟩
      rw [heq]; exact rich_a3_count_le_two_twenty G Hub Iso hdisj hshare hno2hub
    set B : Finset (Fin 20) := R.filter (fun h => ¬ 3 ≤ (G.neighborFinset h ∩ Iso).card) with hBdef
    set T : ℕ := ∑ r ∈ A3, (G.neighborFinset r ∩ Iso).card with hTdef
    have hRmem : ∀ a, a ∈ R ↔ a ∈ Hub ∧ 2 ≤ (G.neighborFinset a ∩ Iso).card := by
      intro a; rw [hRdef, Finset.mem_filter]
    have hAsplit : T + ∑ r ∈ B, (G.neighborFinset r ∩ Iso).card = S := by
      rw [hTdef, hSdef, hA3def, hBdef]
      exact Finset.sum_filter_add_sum_filter_not R _ _
    have hBval : ∑ r ∈ B, (G.neighborFinset r ∩ Iso).card = 2 * B.card := by
      rw [Finset.sum_congr rfl (fun r hr => ?_), Finset.sum_const, smul_eq_mul, mul_comm]
      rw [hBdef, Finset.mem_filter] at hr
      have h2 := ((hRmem r).mp hr.1).2
      omega
    have hcard7 : A3.card + B.card = 7 := by
      have := Finset.card_filter_add_card_filter_not (s := R)
        (fun h => 3 ≤ (G.neighborFinset h ∩ Iso).card)
      rw [← hA3def, ← hBdef, hr7] at this; exact this
    have hTle : T ≤ 4 * A3.card := by
      rw [hTdef]
      calc ∑ r ∈ A3, (G.neighborFinset r ∩ Iso).card ≤ ∑ _r ∈ A3, 4 := by
            apply Finset.sum_le_sum; intro r hr
            rw [hA3def, Finset.mem_filter] at hr
            have hrHub : r ∈ Hub := hRsubHub hr.1
            calc (G.neighborFinset r ∩ Iso).card ≤ (G.neighborFinset r).card :=
                  Finset.card_le_card Finset.inter_subset_left
              _ = 4 := by rw [G.card_neighborFinset_eq_degree, hdeg4 r hrHub]
        _ = 4 * A3.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    have hk2 : A3.card = 2 := by rw [hBval] at hAsplit; omega
    obtain ⟨w1, w2, hw12, hA3eq⟩ := Finset.card_eq_two.mp hk2
    have hw1A3 : w1 ∈ A3 := by rw [hA3eq]; exact Finset.mem_insert_self _ _
    have hw2A3 : w2 ∈ A3 := by
      rw [hA3eq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    have hw1Hub : w1 ∈ Hub := hRsubHub (Finset.mem_of_mem_filter _ hw1A3)
    have hw2Hub : w2 ∈ Hub := hRsubHub (Finset.mem_of_mem_filter _ hw2A3)
    have hw1ge : 3 ≤ (G.neighborFinset w1 ∩ Iso).card := (Finset.mem_filter.mp hw1A3).2
    have hw2ge : 3 ≤ (G.neighborFinset w2 ∩ Iso).card := (Finset.mem_filter.mp hw2A3).2
    have hTpair : (G.neighborFinset w1 ∩ Iso).card + (G.neighborFinset w2 ∩ Iso).card = T := by
      rw [hTdef, hA3eq, Finset.sum_pair hw12]
    have hsum7 : 7 ≤ (G.neighborFinset w1 ∩ Iso).card + (G.neighborFinset w2 ∩ Iso).card := by
      rw [hBval] at hAsplit; omega
    exact two_high_hubs_sum_ge_seven_contra_twenty G Hub Iso hdisj hdeg4 hshare hno2hub w1 w2
      hw1Hub hw2Hub hw12 hw1ge hw2ge hsum7

/-- **Node B — `r = 6` under two poor hubs.**  The clean `S ≥ 15` sub-cases assemble a non-adjacent
degree-`4` pair; the `S ≤ 16` residual (which for `r = 6` is the entire range) is dispatched through
`low_rich_iso_residual_twenty`. -/
theorem rich_six_two_poor_false_twenty (G : SimpleGraph (Fin 20)) (Hub Iso : Finset (Fin 20))
    (hdeg4 : ∀ h ∈ Hub, G.degree h = 4)
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdisj : Disjoint Hub Iso) (hHub : Hub.card = 12) (hIso : Iso.card = 6)
    (hdeg3 : ∀ v : Fin 20, 3 ≤ G.degree v) (hisodeg3 : ∀ t ∈ Iso, G.degree t = 3)
    (hdsum : ∑ w ∈ Hub, G.degree w = 48)
    (hleak : ∑ h ∈ Hub, (G.neighborFinset h ∩ (Finset.univ \ (Hub ∪ Iso))).card ≤ 4)
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hno2hub : ¬∃ h₁ h₂ : Fin 20, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card)
    (hC4 : ¬∃ a b c d : Fin 20, ({a, b, c, d} : Finset (Fin 20)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (hK23 : ¬∃ a b c d e : Fin 20, ({a, b, c, d, e} : Finset (Fin 20)).card = 5 ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
      G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 19)
    (hT : ¬∃ x y z : Fin 20, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧
      G.degree x + G.degree y + G.degree z ≤ 11)
    (hnocut : ¬ ZPoorCutConfig G)
    (z : Fin 20) (hz : z ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 20)))
    (hg1 : Fin 20) (hg2 : Fin 20) (hg1ne : hg1 ≠ hg2)
    (hg1mem : hg1 ∈ G.neighborFinset z ∩ Hub) (hg2mem : hg2 ∈ G.neighborFinset z ∩ Hub)
    (hg1poor : (G.neighborFinset hg1 ∩ Iso).card ≤ 1)
    (hg2poor : (G.neighborFinset hg2 ∩ Iso).card ≤ 1)
    (hres : G.Adj hg1 hg2 ∨ (G.neighborFinset hg1 ∩ G.neighborFinset hg2 ∩ Iso).card = 0)
    (hr6 : (Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)).card = 6) :
    False := by
  classical
  set R : Finset (Fin 20) := Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card) with hRdef
  have hRsubHub : R ⊆ Hub := Finset.filter_subset _ _
  set S : ℕ := ∑ r ∈ R, (G.neighborFinset r ∩ Iso).card with hSdef
  have hsum18 : ∑ a ∈ Hub, (G.neighborFinset a ∩ Iso).card = 18 := by
    have := hub_iso_sum_twenty G Hub Iso hiso3; rw [hIso] at this; omega
  have hRmem : ∀ a, a ∈ R ↔ a ∈ Hub ∧ 2 ≤ (G.neighborFinset a ∩ Iso).card := by
    intro a; rw [hRdef, Finset.mem_filter]
  -- For `r = 6`, `S ≤ 16`: each rich hub has iso-degree `∈ [2, 4]` and at most two (`N2`) have
  -- iso-degree `≥ 3`, so `S ≤ 2·6 + 2·2 = 16`.  Hence the residual dispatcher always applies.
  have hS16 : S ≤ 16 := by
    have hN2 : (R.filter (fun h => 3 ≤ (G.neighborFinset h ∩ Iso).card)).card ≤ 2 := by
      have heq : R.filter (fun h => 3 ≤ (G.neighborFinset h ∩ Iso).card)
          = Hub.filter (fun h => G.degree h = 4 ∧ 3 ≤ (G.neighborFinset h ∩ Iso).card) := by
        rw [hRdef, Finset.filter_filter]; apply Finset.filter_congr
        intro a ha; constructor
        · rintro ⟨_, h3⟩; exact ⟨hdeg4 a ha, h3⟩
        · rintro ⟨_, h3⟩; exact ⟨by omega, h3⟩
      rw [heq]; exact rich_a3_count_le_two_twenty G Hub Iso hdisj hshare hno2hub
    have hbound : S ≤ ∑ a ∈ R, (2 + 2 * (if 3 ≤ (G.neighborFinset a ∩ Iso).card then 1 else 0)) := by
      rw [hSdef]
      apply Finset.sum_le_sum
      intro a ha
      have h2 := ((hRmem a).mp ha).2
      have h4 : (G.neighborFinset a ∩ Iso).card ≤ 4 := by
        calc (G.neighborFinset a ∩ Iso).card ≤ (G.neighborFinset a).card :=
              Finset.card_le_card Finset.inter_subset_left
          _ = 4 := by rw [G.card_neighborFinset_eq_degree, hdeg4 a (hRsubHub ha)]
      split_ifs with h3 <;> omega
    rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, ← Finset.mul_sum,
      ← Finset.card_filter] at hbound
    rw [hr6] at hbound
    omega
  exact low_rich_iso_residual_twenty G Hub Iso hdeg4 hiso3 hdisj hHub hIso hdeg3 hisodeg3
    hdsum hleak hshare hno2hub hC4 hK23 hT hnocut z hz hg1 hg2 hg1ne hg1mem hg2mem hg1poor hg2poor
    hres (Or.inl hr6) hS16

/-- **Two poor hubs through one `M`-edge endpoint force a contradiction (GLOBAL CORE).**  An
`M`-edge endpoint `z` meets exactly two hubs `g₁, g₂`; suppose both are *poor* (iso-degree `≤ 1`) and
we are in the residual regime where `g₁, g₂` are adjacent or share no `M`-isolated twin (`hres`).
The rich count lies in `{6, 7}` (`rich_count_ge_six` / `le_seven`); each branch dispatches to the
corresponding node prover.  The `rich_count_ge_six_twenty` call is supplied its threaded `r = 5`
octahedron residual `hoct5` by the axiom-clean `r5_resid_twenty` (the `|Hub| = 12`, `r = 5`,
`S = 12` regime, `TwinCert20R5Resid`).

This is the unfolded `ZMeetsTwoPoorResidual G Hub Iso` witness statement: once `RichZdeg` imports
this file it discharges `hztwopoor` library-wide. -/
theorem z_meets_two_poor_forces_two_hub_twenty (G : SimpleGraph (Fin 20))
    (Hub Iso : Finset (Fin 20))
    (hdeg4 : ∀ h ∈ Hub, G.degree h = 4)
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdisj : Disjoint Hub Iso) (hHub : Hub.card = 12) (hIso : Iso.card = 6)
    (hdeg3 : ∀ v : Fin 20, 3 ≤ G.degree v) (hisodeg3 : ∀ t ∈ Iso, G.degree t = 3)
    (hdsum : ∑ w ∈ Hub, G.degree w = 48)
    (hleak : ∑ h ∈ Hub, (G.neighborFinset h ∩ (Finset.univ \ (Hub ∪ Iso))).card ≤ 4)
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hno2hub : ¬∃ h₁ h₂ : Fin 20, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card)
    (hC4 : ¬∃ a b c d : Fin 20, ({a, b, c, d} : Finset (Fin 20)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (hK23 : ¬∃ a b c d e : Fin 20, ({a, b, c, d, e} : Finset (Fin 20)).card = 5 ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
      G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 19)
    (hT : ¬∃ x y z : Fin 20, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧
      G.degree x + G.degree y + G.degree z ≤ 11) :
    ∀ (z : Fin 20), z ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 20)) →
      ∀ (hg1 hg2 : Fin 20), hg1 ≠ hg2 →
        hg1 ∈ G.neighborFinset z ∩ Hub → hg2 ∈ G.neighborFinset z ∩ Hub →
        (G.neighborFinset hg1 ∩ Iso).card ≤ 1 → (G.neighborFinset hg2 ∩ Iso).card ≤ 1 →
        (G.Adj hg1 hg2 ∨ (G.neighborFinset hg1 ∩ G.neighborFinset hg2 ∩ Iso).card = 0) →
        ZPoorCutConfig G := by
  classical
  intro z hz hg1 hg2 hg1ne hg1mem hg2mem hg1poor hg2poor hres
  by_contra hnocut
  -- The rich count lies in `{6, 7}`.  `rich_count_ge_six_twenty` needs its threaded `r = 5`
  -- octahedron residual `hoct5`, discharged by `r5_resid_twenty` (the `r = 5`, `S = 12` residual;
  -- see `TwinCert20R5Resid`, which reduces it to the two iso-degree multisets and their
  -- octahedron-poor / star-triangle packing).
  have hoct5 := r5_resid_twenty G Hub Iso hdeg4 hiso3 hdisj hHub hIso hdeg3 hisodeg3 hdsum hleak
    hshare hno2hub hC4 hK23 hT
  have hpoor1 := all_poor_one_resid_twenty G Hub Iso hdeg4 hiso3 hdisj hHub hIso hdeg3
    hisodeg3 hdsum hleak hshare hno2hub hT
  -- `rich_count_ge_six_twenty` now yields `6 ≤ |R| ∨ ZPoorCutConfig G`: either the rich count is
  -- `≥ 6` (then the `r ∈ {6,7}` dispatch closes the two-poor regime by contradiction) or the `r = 5`
  -- octahedron residual directly supplies the boundary cut (`ZPoorCutConfig G`).
  rcases rich_count_ge_six_twenty G Hub Iso hdeg4 hiso3 hdisj hHub hIso hshare hno2hub hoct5
      hpoor1 with hge | hcut
  · have hle : (Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)).card ≤ 7 :=
      rich_count_le_seven_twenty G Hub Iso hdeg4 hiso3 hdisj hHub hIso hshare hno2hub
    have hcases : (Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)).card = 6 ∨
        (Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)).card = 7 := by omega
    rcases hcases with h6 | h7
    · exact rich_six_two_poor_false_twenty G Hub Iso hdeg4 hiso3 hdisj hHub hIso hdeg3 hisodeg3
        hdsum hleak hshare hno2hub hC4 hK23 hT hnocut z hz hg1 hg2 hg1ne hg1mem hg2mem hg1poor hg2poor
        hres h6
    · exact rich_seven_two_poor_false_twenty G Hub Iso hdeg4 hiso3 hdisj hHub hIso hdeg3 hisodeg3
        hdsum hleak hshare hno2hub hC4 hK23 hT hnocut z hz hg1 hg2 hg1ne hg1mem hg2mem hg1poor hg2poor
        hres h7
  · exact hnocut hcut

end N20

end ACMax
