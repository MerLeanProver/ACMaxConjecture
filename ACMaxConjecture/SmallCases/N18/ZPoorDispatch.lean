import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N18.Core
import ACMaxConjecture.SmallCases.N18.TwoHubSelect
import ACMaxConjecture.SmallCases.N18.StarTriangleStruct
import ACMaxConjecture.SmallCases.N18.RichCount
import ACMaxConjecture.SmallCases.N18.Align8Helpers
import ACMaxConjecture.SmallCases.N18.ZVertex
import ACMaxConjecture.SmallCases.N18.ZPoorR7
import ACMaxConjecture.SmallCases.N18.ZPoorSat
import ACMaxConjecture.SmallCases.N18.ZPoorS16
import ACMaxConjecture.SmallCases.N18.ZPoorR6S14

/-!
# The two-poor-hub dispatcher for the rigid `n = 18` no-two-hub partition (top layer)

For the tight `e(M) = 1`, all-degree-`4`, `(|Hub|, |Iso|) = (10, 6)` profile, an `M`-edge endpoint
`z = univ \ (Hub ∪ Iso)` meets exactly two hubs.  This file closes the headline obstruction — both of
those hubs cannot be *poor* (iso-degree `≤ 1`) — by dispatching the rich-count regime to the three
axiom-clean regime provers:

* `r = 7, S = 15` → `mpartner_meets_poor_eighteen` (`TwinCert18ZPoorSat`);
* `r = 7, S = 16` → `rich_seven_S16_two_poor_false_eighteen` (`TwinCert18ZPoorS16`);
* `r = 6, S = 14` → `rich_six_S14_two_poor_false_eighteen` (`TwinCert18ZPoorR6S14`);

where `r := |R|` is the rich-hub count (`6 ≤ r ≤ 7`, `rich_count_ge_six/le_seven`) and
`S := ∑_R |N ∩ Iso|` the rich iso-incidence sum.  The remaining clean sub-cases — `r = 7, S ≥ 17`
and `r = 6, S ≥ 15` — assemble two non-adjacent degree-`4` hubs each retaining `≥ 2` private twins
(`two_high_hubs_sum_ge_seven_contra`), contradicting `hno2hub`.

This file sits *above* the regime provers (and `ZVertex`); `RichZdeg` imports it for the
`z`-poor extraction (`z_meets_two_poor_forces_two_hub_eighteen`).  The regime provers import only the
basic `Z`-vertex layer `ZVertex`, breaking the former `RichZdeg → … → ZPoorR7` import cycle.
-/

namespace ACMax

open scoped Classical

namespace N18

/-- **The low-density rich residual (`S ≤ 16`) — dispatched to the three axiom-clean regime
provers.**  From the structural hypotheses the rich-hub count `r := |R|` is `6` or `7`
(`rich_count_ge_six/le_seven`) and the rich iso-incidence sum `S := ∑_R |N ∩ Iso|` satisfies
`8 + r ≤ S ≤ 16` (the `10 − r` poor hubs absorb at most one iso-incidence each).  Hence:

* `r = 7` ⟹ `S ∈ {15, 16}`: `S = 15 → mpartner_meets_poor`, `S = 16 → rich_seven_S16_two_poor_false`;
* `r = 6` ⟹ `S ∈ {14, 15, 16}`: `S = 14 → rich_six_S14_two_poor_false`; `S ≥ 15` assembles two
  non-adjacent high hubs (`two_high_hubs_sum_ge_seven_contra`).

The good-triangle threshold `hT ≤ 11` is threaded down to the regime provers (bridged to `≤ 10` for
the two `r = 7` provers). -/
theorem low_rich_iso_residual_eighteen (G : SimpleGraph (Fin 18)) (Hub Iso : Finset (Fin 18))
    (hdeg4 : ∀ h ∈ Hub, G.degree h = 4)
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdisj : Disjoint Hub Iso) (hHub : Hub.card = 10) (hIso : Iso.card = 6)
    (hdeg3 : ∀ v : Fin 18, 3 ≤ G.degree v) (hisodeg3 : ∀ t ∈ Iso, G.degree t = 3)
    (hdsum : ∑ w ∈ Hub, G.degree w = 40)
    (hleak : ∑ h ∈ Hub, (G.neighborFinset h ∩ (Finset.univ \ (Hub ∪ Iso))).card ≤ 4)
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hno2hub : ¬∃ h₁ h₂ : Fin 18, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card)
    (hC4 : ¬∃ a b c d : Fin 18, ({a, b, c, d} : Finset (Fin 18)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (hK23 : ¬∃ a b c d e : Fin 18, ({a, b, c, d, e} : Finset (Fin 18)).card = 5 ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
      G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 19)
    (hT : ¬∃ x y z : Fin 18, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧
      G.degree x + G.degree y + G.degree z ≤ 11)
    (z : Fin 18) (hz : z ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 18)))
    (hg1 : Fin 18) (hg2 : Fin 18) (hg1ne : hg1 ≠ hg2)
    (hg1mem : hg1 ∈ G.neighborFinset z ∩ Hub) (hg2mem : hg2 ∈ G.neighborFinset z ∩ Hub)
    (hg1poor : (G.neighborFinset hg1 ∩ Iso).card ≤ 1)
    (hg2poor : (G.neighborFinset hg2 ∩ Iso).card ≤ 1)
    (hres : G.Adj hg1 hg2 ∨ (G.neighborFinset hg1 ∩ G.neighborFinset hg2 ∩ Iso).card = 0)
    (hSlo : ∑ r ∈ Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card),
        (G.neighborFinset r ∩ Iso).card ≤ 16) :
    False := by
  classical
  set R : Finset (Fin 18) := Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card) with hRdef
  set P : Finset (Fin 18) := Hub.filter (fun h => ¬ 2 ≤ (G.neighborFinset h ∩ Iso).card) with hPdef
  have hRsubHub : R ⊆ Hub := Finset.filter_subset _ _
  have hRmem : ∀ a, a ∈ R ↔ a ∈ Hub ∧ 2 ≤ (G.neighborFinset a ∩ Iso).card := by
    intro a; rw [hRdef, Finset.mem_filter]
  set S : ℕ := ∑ r ∈ R, (G.neighborFinset r ∩ Iso).card with hSdef
  -- Total iso-incidence sum is `18`.
  have hsum18 : ∑ a ∈ Hub, (G.neighborFinset a ∩ Iso).card = 18 := by
    have := hub_iso_sum_eighteen G Hub Iso hiso3; rw [hIso] at this; omega
  -- Split over `R` and the poor complement `P`.
  have hsplitRP : S + ∑ g ∈ P, (G.neighborFinset g ∩ Iso).card = 18 := by
    rw [hSdef, hRdef, hPdef,
      Finset.sum_filter_add_sum_filter_not Hub (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)]
    exact hsum18
  have hRPcard : R.card + P.card = 10 := by
    have := Finset.card_filter_add_card_filter_not (s := Hub)
      (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)
    rw [← hRdef, ← hPdef, hHub] at this; exact this
  have hPle : ∑ g ∈ P, (G.neighborFinset g ∩ Iso).card ≤ P.card := by
    calc ∑ g ∈ P, (G.neighborFinset g ∩ Iso).card ≤ ∑ _g ∈ P, 1 := by
          apply Finset.sum_le_sum; intro g hg
          rw [hPdef, Finset.mem_filter] at hg; omega
      _ = P.card := by rw [Finset.sum_const, smul_eq_mul, mul_one]
  -- Rich count `r = |R| ∈ {6, 7}`.
  have hge6 := rich_count_ge_six_eighteen G Hub Iso hdeg4 hiso3 hdisj hHub hIso hshare hno2hub
  have hle7 := rich_count_le_seven_eighteen G Hub Iso hdeg4 hiso3 hdisj hHub hIso hshare hno2hub
  rw [← hRdef] at hge6 hle7
  have hrcases : R.card = 6 ∨ R.card = 7 := by omega
  rcases hrcases with hr6 | hr7
  · -- `r = 6`: `P.card = 4`, so `S ≥ 14`.
    have hPcard : P.card = 4 := by omega
    have hS14ge : 14 ≤ S := by omega
    by_cases hS14 : S = 14
    · exact rich_six_S14_two_poor_false_eighteen G Hub Iso hdeg4 hiso3 hdisj hHub hIso hdeg3
        hisodeg3 hdsum hleak hshare hno2hub hC4 hK23 hT z hz hg1 hg2 hg1ne hg1mem hg2mem hg1poor
        hg2poor hres hr6 hS14
    · -- `S ∈ {15, 16}`: clean two non-adjacent high hubs.
      have hS15 : 15 ≤ S := by omega
      set A3 : Finset (Fin 18) := R.filter (fun h => 3 ≤ (G.neighborFinset h ∩ Iso).card)
        with hA3def
      have hN2 : A3.card ≤ 2 := by
        have heq : A3 =
            Hub.filter (fun h => G.degree h = 4 ∧ 3 ≤ (G.neighborFinset h ∩ Iso).card) := by
          rw [hA3def, hRdef, Finset.filter_filter]
          apply Finset.filter_congr
          intro a ha; constructor
          · rintro ⟨_, h3⟩; exact ⟨hdeg4 a ha, h3⟩
          · rintro ⟨_, h3⟩; exact ⟨by omega, h3⟩
        rw [heq]; exact rich_a3_count_le_two_eighteen G Hub Iso hdisj hshare hno2hub
      set B : Finset (Fin 18) := R.filter (fun h => ¬ 3 ≤ (G.neighborFinset h ∩ Iso).card)
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
      have hcard6 : A3.card + B.card = 6 := by
        have := Finset.card_filter_add_card_filter_not (s := R)
          (fun h => 3 ≤ (G.neighborFinset h ∩ Iso).card)
        rw [← hA3def, ← hBdef, hr6] at this; exact this
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
      have hk2 : A3.card = 2 := by omega
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
        omega
      exact two_high_hubs_sum_ge_seven_contra_eighteen G Hub Iso hdisj hdeg4 hshare hno2hub w1 w2
        hw1Hub hw2Hub hw12 hw1ge hw2ge hsum7
  · -- `r = 7`: `P.card = 3`, so `S ≥ 15`.
    have hPcard : P.card = 3 := by omega
    have hS15ge : 15 ≤ S := by omega
    -- Bridge `hT ≤ 11` down to `hT ≤ 10` for the two `r = 7` regime provers.
    have hT10 : ¬∃ x y z : Fin 18, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
        G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10 := by
      rintro ⟨x, y, w, hxy, hyw, hxw, hax, hay, haw, hle⟩
      exact hT ⟨x, y, w, hxy, hyw, hxw, hax, hay, haw, by omega⟩
    by_cases hS15 : S = 15
    · exact mpartner_meets_poor_eighteen G Hub Iso hdeg4 hiso3 hdisj hHub hIso hdeg3 hisodeg3
        hdsum hleak hshare hno2hub hC4 hK23 hT10 z hz hg1 hg2 hg1ne hg1mem hg2mem hg1poor hg2poor
        hres hr7 hS15
    · have hS16 : S = 16 := by omega
      exact rich_seven_S16_two_poor_false_eighteen G Hub Iso hdeg4 hiso3 hdisj hHub hIso hdeg3
        hisodeg3 hdsum hleak hshare hno2hub hC4 hK23 hT10 z hz hg1 hg2 hg1ne hg1mem hg2mem hg1poor
        hg2poor hres hr7 hS16

/-- **Node A — `r = 7` under two poor hubs.**  An `M`-edge endpoint `z` meets two poor hubs; then
the rich count `|R|` cannot be `7`.  The clean `S ≥ 17` sub-cases assemble a non-adjacent
degree-`4` pair (`two_high_hubs_sum_ge_seven_contra`); the `S ≤ 16` residual is dispatched through
`low_rich_iso_residual_eighteen` to the regime provers. -/
theorem rich_seven_two_poor_false_eighteen (G : SimpleGraph (Fin 18)) (Hub Iso : Finset (Fin 18))
    (hdeg4 : ∀ h ∈ Hub, G.degree h = 4)
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdisj : Disjoint Hub Iso) (hHub : Hub.card = 10) (hIso : Iso.card = 6)
    (hdeg3 : ∀ v : Fin 18, 3 ≤ G.degree v) (hisodeg3 : ∀ t ∈ Iso, G.degree t = 3)
    (hdsum : ∑ w ∈ Hub, G.degree w = 40)
    (hleak : ∑ h ∈ Hub, (G.neighborFinset h ∩ (Finset.univ \ (Hub ∪ Iso))).card ≤ 4)
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hno2hub : ¬∃ h₁ h₂ : Fin 18, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card)
    (hC4 : ¬∃ a b c d : Fin 18, ({a, b, c, d} : Finset (Fin 18)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (hK23 : ¬∃ a b c d e : Fin 18, ({a, b, c, d, e} : Finset (Fin 18)).card = 5 ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
      G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 19)
    (hT : ¬∃ x y z : Fin 18, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧
      G.degree x + G.degree y + G.degree z ≤ 11)
    (z : Fin 18) (hz : z ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 18)))
    (hg1 : Fin 18) (hg2 : Fin 18) (hg1ne : hg1 ≠ hg2)
    (hg1mem : hg1 ∈ G.neighborFinset z ∩ Hub) (hg2mem : hg2 ∈ G.neighborFinset z ∩ Hub)
    (hg1poor : (G.neighborFinset hg1 ∩ Iso).card ≤ 1)
    (hg2poor : (G.neighborFinset hg2 ∩ Iso).card ≤ 1)
    (hres : G.Adj hg1 hg2 ∨ (G.neighborFinset hg1 ∩ G.neighborFinset hg2 ∩ Iso).card = 0)
    (hr7 : (Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)).card = 7) :
    False := by
  classical
  set R : Finset (Fin 18) := Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card) with hRdef
  have hRsubHub : R ⊆ Hub := Finset.filter_subset _ _
  have hRmem : ∀ a, a ∈ R ↔ a ∈ Hub ∧ 2 ≤ (G.neighborFinset a ∩ Iso).card := by
    intro a; rw [hRdef, Finset.mem_filter]
  set S : ℕ := ∑ r ∈ R, (G.neighborFinset r ∩ Iso).card with hSdef
  -- Total iso-incidence sum is `18`.
  have hsum18 : ∑ a ∈ Hub, (G.neighborFinset a ∩ Iso).card = 18 := by
    have := hub_iso_sum_eighteen G Hub Iso hiso3; rw [hIso] at this; omega
  -- `S ≤ 18`.
  have hS18 : S ≤ 18 := by
    rw [hSdef]
    calc ∑ r ∈ R, (G.neighborFinset r ∩ Iso).card
        ≤ ∑ a ∈ Hub, (G.neighborFinset a ∩ Iso).card := Finset.sum_le_sum_of_subset hRsubHub
      _ = 18 := hsum18
  -- Residual branch.
  by_cases hSlo : S ≤ 16
  · exact low_rich_iso_residual_eighteen G Hub Iso hdeg4 hiso3 hdisj hHub hIso hdeg3 hisodeg3
      hdsum hleak hshare hno2hub hC4 hK23 hT z hz hg1 hg2 hg1ne hg1mem hg2mem hg1poor hg2poor hres
      hSlo
  · -- `S ≥ 17`: clean two-hub assembly.
    have hS17 : 17 ≤ S := by omega
    set A3 : Finset (Fin 18) := R.filter (fun h => 3 ≤ (G.neighborFinset h ∩ Iso).card) with hA3def
    have hN2 : A3.card ≤ 2 := by
      have heq : A3 = Hub.filter (fun h => G.degree h = 4 ∧ 3 ≤ (G.neighborFinset h ∩ Iso).card) := by
        rw [hA3def, hRdef, Finset.filter_filter]
        apply Finset.filter_congr
        intro a ha; constructor
        · rintro ⟨_, h3⟩; exact ⟨hdeg4 a ha, h3⟩
        · rintro ⟨_, h3⟩; exact ⟨by omega, h3⟩
      rw [heq]; exact rich_a3_count_le_two_eighteen G Hub Iso hdisj hshare hno2hub
    set B : Finset (Fin 18) := R.filter (fun h => ¬ 3 ≤ (G.neighborFinset h ∩ Iso).card) with hBdef
    set T : ℕ := ∑ r ∈ A3, (G.neighborFinset r ∩ Iso).card with hTdef
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
    have hk2 : A3.card = 2 := by omega
    obtain ⟨w1, w2, hw12, hA3eq⟩ := Finset.card_eq_two.mp hk2
    have hw1A3 : w1 ∈ A3 := by rw [hA3eq]; exact Finset.mem_insert_self _ _
    have hw2A3 : w2 ∈ A3 := by
      rw [hA3eq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    have hw1Hub : w1 ∈ Hub := hRsubHub (Finset.mem_of_mem_filter _ hw1A3)
    have hw2Hub : w2 ∈ Hub := hRsubHub (Finset.mem_of_mem_filter _ hw2A3)
    have hw1ge : 3 ≤ (G.neighborFinset w1 ∩ Iso).card :=
      (Finset.mem_filter.mp hw1A3).2
    have hw2ge : 3 ≤ (G.neighborFinset w2 ∩ Iso).card :=
      (Finset.mem_filter.mp hw2A3).2
    have hTpair : (G.neighborFinset w1 ∩ Iso).card + (G.neighborFinset w2 ∩ Iso).card = T := by
      rw [hTdef, hA3eq, Finset.sum_pair hw12]
    have hsum7 : 7 ≤ (G.neighborFinset w1 ∩ Iso).card + (G.neighborFinset w2 ∩ Iso).card := by
      omega
    exact two_high_hubs_sum_ge_seven_contra_eighteen G Hub Iso hdisj hdeg4 hshare hno2hub w1 w2
      hw1Hub hw2Hub hw12 hw1ge hw2ge hsum7

/-- **Node B — `r = 6` under two poor hubs.**  With six rich hubs and an `M`-edge endpoint meeting
two poor hubs, the clean `S ≥ 15` sub-cases assemble a non-adjacent degree-`4` pair
(`two_high_hubs_sum_ge_seven_contra`); the `S = 14` residual is dispatched through
`low_rich_iso_residual_eighteen`. -/
theorem rich_six_two_poor_false_eighteen (G : SimpleGraph (Fin 18)) (Hub Iso : Finset (Fin 18))
    (hdeg4 : ∀ h ∈ Hub, G.degree h = 4)
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdisj : Disjoint Hub Iso) (hHub : Hub.card = 10) (hIso : Iso.card = 6)
    (hdeg3 : ∀ v : Fin 18, 3 ≤ G.degree v) (hisodeg3 : ∀ t ∈ Iso, G.degree t = 3)
    (hdsum : ∑ w ∈ Hub, G.degree w = 40)
    (hleak : ∑ h ∈ Hub, (G.neighborFinset h ∩ (Finset.univ \ (Hub ∪ Iso))).card ≤ 4)
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hno2hub : ¬∃ h₁ h₂ : Fin 18, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card)
    (hC4 : ¬∃ a b c d : Fin 18, ({a, b, c, d} : Finset (Fin 18)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (hK23 : ¬∃ a b c d e : Fin 18, ({a, b, c, d, e} : Finset (Fin 18)).card = 5 ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
      G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 19)
    (hT : ¬∃ x y z : Fin 18, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧
      G.degree x + G.degree y + G.degree z ≤ 11)
    (z : Fin 18) (hz : z ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 18)))
    (hg1 : Fin 18) (hg2 : Fin 18) (hg1ne : hg1 ≠ hg2)
    (hg1mem : hg1 ∈ G.neighborFinset z ∩ Hub) (hg2mem : hg2 ∈ G.neighborFinset z ∩ Hub)
    (hg1poor : (G.neighborFinset hg1 ∩ Iso).card ≤ 1)
    (hg2poor : (G.neighborFinset hg2 ∩ Iso).card ≤ 1)
    (hres : G.Adj hg1 hg2 ∨ (G.neighborFinset hg1 ∩ G.neighborFinset hg2 ∩ Iso).card = 0)
    (hr6 : (Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)).card = 6) :
    False := by
  classical
  set R : Finset (Fin 18) := Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card) with hRdef
  set P : Finset (Fin 18) := Hub.filter (fun h => ¬ 2 ≤ (G.neighborFinset h ∩ Iso).card) with hPdef
  have hRsubHub : R ⊆ Hub := Finset.filter_subset _ _
  have hRmem : ∀ a, a ∈ R ↔ a ∈ Hub ∧ 2 ≤ (G.neighborFinset a ∩ Iso).card := by
    intro a; rw [hRdef, Finset.mem_filter]
  set S : ℕ := ∑ r ∈ R, (G.neighborFinset r ∩ Iso).card with hSdef
  -- Total iso-incidence sum is `18`.
  have hsum18 : ∑ a ∈ Hub, (G.neighborFinset a ∩ Iso).card = 18 := by
    have := hub_iso_sum_eighteen G Hub Iso hiso3; rw [hIso] at this; omega
  -- Split over `R` and `P`.
  have hsplitRP : S + ∑ g ∈ P, (G.neighborFinset g ∩ Iso).card = 18 := by
    rw [hSdef, hRdef, hPdef,
      Finset.sum_filter_add_sum_filter_not Hub (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)]
    exact hsum18
  have hPcard : P.card = 4 := by
    have := Finset.card_filter_add_card_filter_not (s := Hub)
      (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)
    rw [← hRdef, ← hPdef, hHub, hr6] at this; omega
  have hPle : ∑ g ∈ P, (G.neighborFinset g ∩ Iso).card ≤ 4 := by
    calc ∑ g ∈ P, (G.neighborFinset g ∩ Iso).card ≤ ∑ _g ∈ P, 1 := by
          apply Finset.sum_le_sum; intro g hg
          rw [hPdef, Finset.mem_filter] at hg; omega
      _ = 4 := by rw [Finset.sum_const, hPcard, smul_eq_mul, mul_one]
  have hS14 : 14 ≤ S := by omega
  -- Residual branch.
  by_cases hSlo : S ≤ 14
  · exact low_rich_iso_residual_eighteen G Hub Iso hdeg4 hiso3 hdisj hHub hIso hdeg3 hisodeg3
      hdsum hleak hshare hno2hub hC4 hK23 hT z hz hg1 hg2 hg1ne hg1mem hg2mem hg1poor hg2poor hres
      (le_trans hSlo (by norm_num))
  · -- `S ≥ 15`: clean two-hub assembly.
    have hS15 : 15 ≤ S := by omega
    set A3 : Finset (Fin 18) := R.filter (fun h => 3 ≤ (G.neighborFinset h ∩ Iso).card) with hA3def
    have hN2 : A3.card ≤ 2 := by
      have heq : A3 = Hub.filter (fun h => G.degree h = 4 ∧ 3 ≤ (G.neighborFinset h ∩ Iso).card) := by
        rw [hA3def, hRdef, Finset.filter_filter]
        apply Finset.filter_congr
        intro a ha; constructor
        · rintro ⟨_, h3⟩; exact ⟨hdeg4 a ha, h3⟩
        · rintro ⟨_, h3⟩; exact ⟨by omega, h3⟩
      rw [heq]; exact rich_a3_count_le_two_eighteen G Hub Iso hdisj hshare hno2hub
    set B : Finset (Fin 18) := R.filter (fun h => ¬ 3 ≤ (G.neighborFinset h ∩ Iso).card) with hBdef
    set T : ℕ := ∑ r ∈ A3, (G.neighborFinset r ∩ Iso).card with hTdef
    have hAsplit : T + ∑ r ∈ B, (G.neighborFinset r ∩ Iso).card = S := by
      rw [hTdef, hSdef, hA3def, hBdef]
      exact Finset.sum_filter_add_sum_filter_not R _ _
    have hBval : ∑ r ∈ B, (G.neighborFinset r ∩ Iso).card = 2 * B.card := by
      rw [Finset.sum_congr rfl (fun r hr => ?_), Finset.sum_const, smul_eq_mul, mul_comm]
      rw [hBdef, Finset.mem_filter] at hr
      have h2 := ((hRmem r).mp hr.1).2
      omega
    have hcard6 : A3.card + B.card = 6 := by
      have := Finset.card_filter_add_card_filter_not (s := R)
        (fun h => 3 ≤ (G.neighborFinset h ∩ Iso).card)
      rw [← hA3def, ← hBdef, hr6] at this; exact this
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
    have hk2 : A3.card = 2 := by omega
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
      omega
    exact two_high_hubs_sum_ge_seven_contra_eighteen G Hub Iso hdisj hdeg4 hshare hno2hub w1 w2
      hw1Hub hw2Hub hw12 hw1ge hw2ge hsum7

/-- **Two poor hubs through one `M`-edge endpoint force a contradiction (GLOBAL CORE).**  An
`M`-edge endpoint `z` meets exactly two hubs `g₁, g₂`; suppose both are *poor* (iso-degree `≤ 1`) and
we are in the residual regime where `g₁, g₂` are adjacent or share no `M`-isolated twin (`hres`).
The rich count lies in `{6, 7}` (`rich_count_ge_six/le_seven`); each branch dispatches to the
corresponding node prover. -/
theorem z_meets_two_poor_forces_two_hub_eighteen (G : SimpleGraph (Fin 18))
    (Hub Iso : Finset (Fin 18))
    (hdeg4 : ∀ h ∈ Hub, G.degree h = 4)
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdisj : Disjoint Hub Iso) (hHub : Hub.card = 10) (hIso : Iso.card = 6)
    (hdeg3 : ∀ v : Fin 18, 3 ≤ G.degree v) (hisodeg3 : ∀ t ∈ Iso, G.degree t = 3)
    (hdsum : ∑ w ∈ Hub, G.degree w = 40)
    (hleak : ∑ h ∈ Hub, (G.neighborFinset h ∩ (Finset.univ \ (Hub ∪ Iso))).card ≤ 4)
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hno2hub : ¬∃ h₁ h₂ : Fin 18, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card)
    (hC4 : ¬∃ a b c d : Fin 18, ({a, b, c, d} : Finset (Fin 18)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (hK23 : ¬∃ a b c d e : Fin 18, ({a, b, c, d, e} : Finset (Fin 18)).card = 5 ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
      G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 19)
    (hT : ¬∃ x y z : Fin 18, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧
      G.degree x + G.degree y + G.degree z ≤ 11)
    (z : Fin 18) (hz : z ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 18)))
    (hg1 : Fin 18) (hg2 : Fin 18) (hg1ne : hg1 ≠ hg2)
    (hg1mem : hg1 ∈ G.neighborFinset z ∩ Hub) (hg2mem : hg2 ∈ G.neighborFinset z ∩ Hub)
    (hg1poor : (G.neighborFinset hg1 ∩ Iso).card ≤ 1)
    (hg2poor : (G.neighborFinset hg2 ∩ Iso).card ≤ 1)
    (hres : G.Adj hg1 hg2 ∨ (G.neighborFinset hg1 ∩ G.neighborFinset hg2 ∩ Iso).card = 0) :
    False := by
  classical
  -- The rich count lies in `{6, 7}` (`rich_count_ge_six`/`le_seven`).
  have hge : 6 ≤ (Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)).card :=
    rich_count_ge_six_eighteen G Hub Iso hdeg4 hiso3 hdisj hHub hIso hshare hno2hub
  have hle : (Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)).card ≤ 7 :=
    rich_count_le_seven_eighteen G Hub Iso hdeg4 hiso3 hdisj hHub hIso hshare hno2hub
  have hcases : (Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)).card = 6 ∨
      (Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)).card = 7 := by omega
  rcases hcases with h6 | h7
  · -- `r = 6`: Node B.
    exact rich_six_two_poor_false_eighteen G Hub Iso hdeg4 hiso3 hdisj hHub hIso hdeg3 hisodeg3
      hdsum hleak hshare hno2hub hC4 hK23 hT z hz hg1 hg2 hg1ne hg1mem hg2mem hg1poor hg2poor hres h6
  · -- `r = 7`: Node A.
    exact rich_seven_two_poor_false_eighteen G Hub Iso hdeg4 hiso3 hdisj hHub hIso hdeg3 hisodeg3
      hdsum hleak hshare hno2hub hC4 hK23 hT z hz hg1 hg2 hg1ne hg1mem hg2mem hg1poor hg2poor hres h7

end N18

end ACMax
