import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N18.Core
import ACMaxConjecture.SmallCases.N18.TwoHubSelect
import ACMaxConjecture.SmallCases.N18.StarTriangleStruct
import ACMaxConjecture.SmallCases.N18.RichCount
import ACMaxConjecture.SmallCases.N18.RichEdge

/-!
# No iso-isolated hub in the rigid `n = 18` partition

For the tight `e(M) = 1`, all-degree-`4`, `(|Hub|, |Iso|) = (10, 6)` profile, every hub meets at
least one `M`-isolated twin.  Equivalently, no hub has iso-degree `0`.  This rules out the
`(7, 2, 1)`-shaped survivor in which a degree-`4` hub with all four neighbours among the other hubs
and the two `M`-edge endpoints coexists with the rich hubs; the no-good-two-hub hypothesis together
with the good-`C₄`/`K₂₃` exclusions kills it.
-/

namespace ACMax

open scoped Classical

namespace N18

/-- **An iso-degree-`4` hub excludes every other iso-degree-`≥ 3` hub.**  If a degree-`4` hub `w`
meets all four of its neighbours in `Iso` (iso-degree `4`), then `N(w) ⊆ Iso`, so `w` is
non-adjacent to every other hub.  Any second hub `b ≠ w` with iso-degree `≥ 3` would, via the
share-`≤ 1` bound, keep `≥ 3` (resp. `≥ 2`) private `M`-isolated twins — a good two-hub pair,
contradicting `hno2hub`.  Hence every other hub has iso-degree `≤ 2`. -/
theorem iso_deg_four_excludes_three_eighteen (G : SimpleGraph (Fin 18)) (Hub Iso : Finset (Fin 18))
    (hdeg4 : ∀ h ∈ Hub, G.degree h = 4) (hdisj : Disjoint Hub Iso)
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hno2hub : ¬∃ h₁ h₂ : Fin 18, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card)
    (w : Fin 18) (hw : w ∈ Hub) (hw4 : (G.neighborFinset w ∩ Iso).card = 4)
    (b : Fin 18) (hb : b ∈ Hub) (hbw : b ≠ w) :
    (G.neighborFinset b ∩ Iso).card ≤ 2 := by
  classical
  by_contra hcon
  push Not at hcon
  have hb3 : 3 ≤ (G.neighborFinset b ∩ Iso).card := hcon
  have hwdeg : (G.neighborFinset w).card = 4 := by
    rw [G.card_neighborFinset_eq_degree, hdeg4 w hw]
  have hNwIso : G.neighborFinset w ⊆ Iso := by
    have heq : G.neighborFinset w ∩ Iso = G.neighborFinset w :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by rw [hwdeg, hw4])
    rw [← heq]; exact Finset.inter_subset_right
  have hnadj : ¬G.Adj w b := by
    intro hadj
    have hbNw : b ∈ G.neighborFinset w := (G.mem_neighborFinset _ _).mpr hadj
    exact Finset.disjoint_left.mp hdisj hb (hNwIso hbNw)
  have hsh : (G.neighborFinset w ∩ G.neighborFinset b ∩ Iso).card ≤ 1 :=
    hshare w hw (hdeg4 w hw) b hb (hdeg4 b hb) (Ne.symm hbw) hnadj
  have hpw : 2 ≤ ((G.neighborFinset w ∩ Iso) \ G.neighborFinset b).card := by
    have hk := Finset.card_sdiff_add_card_inter (G.neighborFinset w ∩ Iso) (G.neighborFinset b)
    have hi : (G.neighborFinset w ∩ Iso) ∩ G.neighborFinset b
        = G.neighborFinset w ∩ G.neighborFinset b ∩ Iso := Finset.inter_right_comm _ _ _
    rw [hi] at hk; rw [hw4] at hk; omega
  have hpb : 2 ≤ ((G.neighborFinset b ∩ Iso) \ G.neighborFinset w).card := by
    have hk := Finset.card_sdiff_add_card_inter (G.neighborFinset b ∩ Iso) (G.neighborFinset w)
    have hi : (G.neighborFinset b ∩ Iso) ∩ G.neighborFinset w
        = G.neighborFinset w ∩ G.neighborFinset b ∩ Iso := by
      rw [Finset.inter_right_comm, Finset.inter_comm (G.neighborFinset b) (G.neighborFinset w)]
    rw [hi] at hk; omega
  exact hno2hub ⟨w, b, hw, hb, hdeg4 w hw, hdeg4 b hb, Ne.symm hbw, hnadj, hpw, hpb⟩

/-- **No hub has iso-degree `0` (`|Hub| = 10`, `|Iso| = 6`, all degree `4`).**  Every hub meets at
least one `M`-isolated twin.  Pinning the rich count to `6` (`rich_count_le_seven`,
`rich_count_ge_six`, `rich_count_ne_seven`), the rich incidence sum is `≤ 14` (`N2` plus the
iso-degree-`4` exclusion bound `2|H₄| + |H₃ᵐ| ≤ 2`), so the four poor hubs absorb `≥ 4` of the
`18` incidences; each poor hub carries `≤ 1`, so each carries exactly `1`.  An iso-degree-`0` hub is
therefore impossible. -/
theorem no_iso_zero_hub_eighteen (G : SimpleGraph (Fin 18)) (Hub Iso : Finset (Fin 18))
    (hdeg4 : ∀ h ∈ Hub, G.degree h = 4)
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdisj : Disjoint Hub Iso) (hHub : Hub.card = 10) (hIso : Iso.card = 6)
    (_hdeg3 : ∀ v : Fin 18, 3 ≤ G.degree v) (hisodeg3 : ∀ t ∈ Iso, G.degree t = 3)
    (_hdsum : ∑ w ∈ Hub, G.degree w = 40)
    (_hleak : ∑ h ∈ Hub, (G.neighborFinset h ∩ (Finset.univ \ (Hub ∪ Iso))).card ≤ 4)
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hno2hub : ¬∃ h₁ h₂ : Fin 18, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card)
    (hC4 : ¬∃ a b c d : Fin 18, ({a, b, c, d} : Finset (Fin 18)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (_hK23 : ¬∃ a b c d e : Fin 18, ({a, b, c, d, e} : Finset (Fin 18)).card = 5 ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
      G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 19)
    (hT : ¬∃ x y z : Fin 18, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧
      G.degree x + G.degree y + G.degree z ≤ 11) :
    ∀ h ∈ Hub, 1 ≤ (G.neighborFinset h ∩ Iso).card := by
  classical
  -- Pin the rich count to `6`.
  have hle7 := rich_count_le_seven_eighteen G Hub Iso hdeg4 hiso3 hdisj hHub hIso hshare hno2hub
  have hge6 := rich_count_ge_six_eighteen G Hub Iso hdeg4 hiso3 hdisj hHub hIso hshare hno2hub
  have hne7 := rich_count_ne_seven_eighteen G Hub Iso hdeg4 hiso3 hdisj hHub hIso hisodeg3
    _hdeg3 _hdsum _hleak hshare hno2hub hC4 _hK23 hT
  set R : Finset (Fin 18) := Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card) with hRdef
  set P : Finset (Fin 18) := Hub.filter (fun h => ¬ 2 ≤ (G.neighborFinset h ∩ Iso).card) with hPdef
  have hr6 : R.card = 6 := by omega
  have hPcard : P.card = 4 := by
    have hsplit := Finset.card_filter_add_card_filter_not
      (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card) (s := Hub)
    rw [← hRdef, ← hPdef, hHub] at hsplit; omega
  -- Total iso incidences `= 18`, split over `R` and `P`.
  have hsum18 : ∑ h ∈ Hub, (G.neighborFinset h ∩ Iso).card = 18 := by
    have := hub_iso_sum_eighteen G Hub Iso hiso3; rw [hIso] at this; omega
  have hsumsplit : ∑ h ∈ R, (G.neighborFinset h ∩ Iso).card
      + ∑ h ∈ P, (G.neighborFinset h ∩ Iso).card = 18 := by
    rw [hRdef, hPdef,
      Finset.sum_filter_add_sum_filter_not Hub (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)]
    exact hsum18
  -- `N2`: at most two hubs have iso-degree `≥ 3`.
  set H3 : Finset (Fin 18) := Hub.filter (fun h => 3 ≤ (G.neighborFinset h ∩ Iso).card) with hH3def
  have hN2 : H3.card ≤ 2 := by
    have hkey := rich_a3_count_le_two_eighteen G Hub Iso hdisj hshare hno2hub
    have heq : Hub.filter (fun h => G.degree h = 4 ∧ 3 ≤ (G.neighborFinset h ∩ Iso).card) = H3 := by
      rw [hH3def]; apply Finset.filter_congr
      intro h hh; exact ⟨fun x => x.2, fun x => ⟨hdeg4 h hh, x⟩⟩
    rw [heq] at hkey; exact hkey
  -- The `a − 2` excess sum over `H3` is `≤ 2`.
  have hH3sub : H3 ⊆ R := by
    intro h hh; rw [hH3def, Finset.mem_filter] at hh; rw [hRdef, Finset.mem_filter]
    exact ⟨hh.1, by omega⟩
  have hH3sum : ∑ h ∈ H3, ((G.neighborFinset h ∩ Iso).card - 2) ≤ 2 := by
    by_cases hex : ∃ w ∈ H3, (G.neighborFinset w ∩ Iso).card = 4
    · obtain ⟨w, hwH3, hw4⟩ := hex
      have hwHub : w ∈ Hub := (Finset.mem_filter.mp hwH3).1
      have hsub : H3 ⊆ {w} := by
        intro h hh
        rw [Finset.mem_singleton]
        by_contra hhw
        have hhHub : h ∈ Hub := (Finset.mem_filter.mp hh).1
        have hh3 : 3 ≤ (G.neighborFinset h ∩ Iso).card := (Finset.mem_filter.mp hh).2
        have hle2 := iso_deg_four_excludes_three_eighteen G Hub Iso hdeg4 hdisj hshare hno2hub
          w hwHub hw4 h hhHub hhw
        omega
      calc ∑ h ∈ H3, ((G.neighborFinset h ∩ Iso).card - 2)
          ≤ ∑ h ∈ ({w} : Finset (Fin 18)), ((G.neighborFinset h ∩ Iso).card - 2) :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)
        _ = (G.neighborFinset w ∩ Iso).card - 2 := Finset.sum_singleton _ _
        _ = 2 := by rw [hw4]
    · push Not at hex
      have hall1 : ∀ h ∈ H3, (G.neighborFinset h ∩ Iso).card - 2 = 1 := by
        intro h hh
        have hhHub : h ∈ Hub := (Finset.mem_filter.mp hh).1
        have hh3 : 3 ≤ (G.neighborFinset h ∩ Iso).card := (Finset.mem_filter.mp hh).2
        have hle4 : (G.neighborFinset h ∩ Iso).card ≤ 4 := by
          calc (G.neighborFinset h ∩ Iso).card ≤ (G.neighborFinset h).card :=
                Finset.card_le_card Finset.inter_subset_left
            _ = 4 := by rw [G.card_neighborFinset_eq_degree, hdeg4 h hhHub]
        have hne4 := hex h hh
        omega
      calc ∑ h ∈ H3, ((G.neighborFinset h ∩ Iso).card - 2)
          = ∑ _h ∈ H3, 1 := Finset.sum_congr rfl hall1
        _ = H3.card := by rw [Finset.sum_const, smul_eq_mul, mul_one]
        _ ≤ 2 := hN2
  -- Rich incidence sum `≤ 14`.
  have hrichle : ∑ h ∈ R, (G.neighborFinset h ∩ Iso).card ≤ 14 := by
    have hpt : ∀ h ∈ R, (G.neighborFinset h ∩ Iso).card
        = 2 + ((G.neighborFinset h ∩ Iso).card - 2) := by
      intro h hh; rw [hRdef, Finset.mem_filter] at hh; omega
    have hexcess : ∑ h ∈ R, ((G.neighborFinset h ∩ Iso).card - 2)
        = ∑ h ∈ H3, ((G.neighborFinset h ∩ Iso).card - 2) := by
      refine (Finset.sum_subset hH3sub ?_).symm
      intro h hhR hhH3
      rw [hRdef, Finset.mem_filter] at hhR
      rw [hH3def, Finset.mem_filter, not_and] at hhH3
      have := hhH3 hhR.1
      omega
    calc ∑ h ∈ R, (G.neighborFinset h ∩ Iso).card
        = ∑ h ∈ R, (2 + ((G.neighborFinset h ∩ Iso).card - 2)) := Finset.sum_congr rfl hpt
      _ = ∑ _h ∈ R, 2 + ∑ h ∈ R, ((G.neighborFinset h ∩ Iso).card - 2) := Finset.sum_add_distrib
      _ ≤ 12 + 2 := by
          rw [Finset.sum_const, hr6, smul_eq_mul, hexcess]; omega
      _ = 14 := by norm_num
  -- Poor incidences `≥ 4`.
  have hpoorge : 4 ≤ ∑ h ∈ P, (G.neighborFinset h ∩ Iso).card := by omega
  -- Conclude every hub meets `≥ 1` twin.
  intro h hh
  by_cases hR : 2 ≤ (G.neighborFinset h ∩ Iso).card
  · omega
  · have hhP : h ∈ P := by rw [hPdef, Finset.mem_filter]; exact ⟨hh, hR⟩
    by_contra hlt
    push Not at hlt
    have h0 : (G.neighborFinset h ∩ Iso).card = 0 := by omega
    have hpoorle3 : ∑ g ∈ P, (G.neighborFinset g ∩ Iso).card ≤ 3 := by
      have hpe : ∑ g ∈ P, (G.neighborFinset g ∩ Iso).card
          = (G.neighborFinset h ∩ Iso).card
            + ∑ g ∈ P.erase h, (G.neighborFinset g ∩ Iso).card :=
        (Finset.add_sum_erase P _ hhP).symm
      have herase : ∑ g ∈ P.erase h, (G.neighborFinset g ∩ Iso).card ≤ 3 := by
        calc ∑ g ∈ P.erase h, (G.neighborFinset g ∩ Iso).card
            ≤ ∑ _g ∈ P.erase h, 1 := by
              apply Finset.sum_le_sum
              intro g hg
              have hgP : g ∈ P := Finset.mem_of_mem_erase hg
              rw [hPdef, Finset.mem_filter] at hgP; omega
          _ = (P.erase h).card := by rw [Finset.sum_const, smul_eq_mul, mul_one]
          _ = 3 := by rw [Finset.card_erase_of_mem hhP, hPcard]
      rw [hpe, h0]; omega
    omega

end N18

end ACMax
