import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N20.TwoHubSelect
import ACMaxConjecture.SmallCases.N20.TwoHubTight96

/-!
# The `e(M) = 0` deg-`5` profile `(11, 9, 45)` two-hub kill (`n = 20`)

At `n = 20` (`m = 36`, `∑deg = 72`, excess `12`) the deg-`5`-containing `e(M) = 0` two-hub
profiles are `(|Hub|, |Iso|, ∑_Hub deg) ∈ {(8,12,36), (9,11,39), (10,10,42), (11,9,45)}`
(`#{deg-5 hubs} = 12 − |Hub|`, `Hub ∪ Iso` partitioning all `20` vertices).  The first three are
refuted outright by the residual master inequality `3·|Iso| + 10·|Hub| ≤ 3·∑deg + 2`
(`residual_arith_twenty`), but `(11, 9, 45)` **TIES** (`137 = 137`) — the first `e(M) = 0` tie in
the family — so it needs its own kill, supplied here by the **off-diagonal cover count**.

## The kill (margin `18`)

Suppose no good two-hub opposite-twin pair exists.  Splitting `Hub` into the `d₄ = 10` degree-`4`
hubs `T` and the single degree-`5` hub, the tie forces **all-at-cap**: the total iso-degree is
`3·|Iso| = 27` (`hub_iso_sum_twenty`), the deg-`5` hub absorbs `≤ 5`, and the threshold/clique
bound (`deg4_sum_le_twenty`) caps `∑_T isoDeg ≤ 2·10 + 2 = 22`, so `∑_T isoDeg = 22` exactly and
the indicator decomposition (`c₁ + c₂ + c₃ + c₄ = 22`, `c₁, c₂ ≤ 10`, `c₃ + c₄ ≤ 2`) forces
**every** degree-`4` hub to iso-degree `≥ 2`.  With the refuted selection
(`nogood_of_not_select_twenty`), every non-adjacent degree-`4` pair then shares an `Iso` twin, so
`T` is covered and `cover_offDiag_ineq_twenty` applies:
`100 = |T|² ≤ |T| + ∑_{a∈T} |N(a) ∩ T| + ∑_{t∈Iso} x_t(x_t − 1) ≤ 10 + 18 + 54 = 82`, a
contradiction — the hub-side term is `≤ 4·10 − 22 = 18` (`hub_neighbor_le_twenty`) and each
`M`-isolated twin meets exactly `3` hubs (`x_t ≤ 3`, so `x_t(x_t − 1) ≤ 6` over `|Iso| = 9`).
-/

namespace ACMax

open scoped Classical

namespace N20

/-- **The `(11, 9, 45)` `e(M) = 0` deg-`5` two-hub kill (`n = 20`).**  In the `e(M) = 0` residual
corner with `11` hubs of degree `4`/`5`, `9` `M`-isolated twins each meeting exactly three hubs,
hub degree-sum `45` (so `10` degree-`4` hubs and one degree-`5` hub) and the
degree-`4`-restricted share `≤ 1`, a good two-hub opposite-twin pair exists: the counting tie
`3·9 + 10·11 = 3·45 + 2` forces every degree-`4` hub to iso-degree `≥ 2`, and the off-diagonal
cover count `100 ≤ 10 + 18 + 54 = 82` refutes the no-good-pair hypothesis with margin `18`. -/
theorem two_hub_e0_deg5_hub11_twenty (G : SimpleGraph (Fin 20)) (Hub Iso : Finset (Fin 20))
    (hdeg : ∀ h ∈ Hub, 4 ≤ G.degree h) (hdeg5 : ∀ h ∈ Hub, G.degree h ≤ 5)
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdisj : Disjoint Hub Iso)
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hHub : Hub.card = 11) (hIso : Iso.card = 9)
    (hdsum : ∑ w ∈ Hub, G.degree w = 45) :
    ∃ h₁ h₂ : Fin 20, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card := by
  classical
  by_contra hcon
  have hdeg45 : ∀ h ∈ Hub, G.degree h = 4 ∨ G.degree h = 5 := by
    intro h hh; have := hdeg h hh; have := hdeg5 h hh; omega
  set T : Finset (Fin 20) := Hub.filter (fun h => G.degree h = 4) with hTdef
  set R : Finset (Fin 20) := Hub.filter (fun h => ¬ G.degree h = 4) with hRdef
  have hTsubHub : T ⊆ Hub := by rw [hTdef]; exact Finset.filter_subset _ _
  have key := nogood_of_not_select_twenty G Hub Iso hcon
  have hmf := strong_deg4_count_le_two_deg5_twenty G Hub Iso hdisj hshare key
  have hTisoLe := deg4_sum_le_twenty G Hub Iso hmf
  have hisoSum := hub_iso_sum_twenty G Hub Iso hiso3
  have hisoLeDeg : ∀ a : Fin 20, (G.neighborFinset a ∩ Iso).card ≤ G.degree a := by
    intro a; rw [← G.card_neighborFinset_eq_degree]
    exact Finset.card_le_card Finset.inter_subset_left
  have hTdeg4 : ∀ a ∈ T, G.degree a = 4 := by
    intro a ha; rw [hTdef, Finset.mem_filter] at ha; exact ha.2
  have hRdeg5 : ∀ v ∈ R, G.degree v = 5 := by
    intro v hv; rw [hRdef, Finset.mem_filter] at hv
    rcases hdeg45 v hv.1 with h | h
    · exact absurd h hv.2
    · exact h
  -- cardinalities: `|T| = 10`, `|R| = 1`.
  have hcard : T.card + R.card = Hub.card := by
    rw [hTdef, hRdef]; exact Finset.card_filter_add_card_filter_not (fun h => G.degree h = 4)
  have hdegsplit : ∑ v ∈ T, G.degree v + ∑ v ∈ R, G.degree v = ∑ w ∈ Hub, G.degree w := by
    rw [hTdef, hRdef]; exact Finset.sum_filter_add_sum_filter_not Hub (fun h => G.degree h = 4) _
  have hTdeg : ∑ v ∈ T, G.degree v = 4 * T.card := by
    rw [Finset.sum_congr rfl (fun x hx => hTdeg4 x hx), Finset.sum_const, smul_eq_mul, mul_comm]
  have hRdegsum : ∑ v ∈ R, G.degree v = 5 * R.card := by
    rw [Finset.sum_congr rfl (fun x hx => hRdeg5 x hx), Finset.sum_const, smul_eq_mul, mul_comm]
  have hTcard : T.card = 10 := by
    rw [hHub] at hcard; rw [hTdeg, hRdegsum, hdsum] at hdegsplit; omega
  have hRcard : R.card = 1 := by
    rw [hHub] at hcard; rw [hTdeg, hRdegsum, hdsum] at hdegsplit; omega
  -- iso-degree sums: the tie forces `∑_T isoDeg = 22`.
  have hpartIso : ∑ v ∈ T, (G.neighborFinset v ∩ Iso).card
      + ∑ v ∈ R, (G.neighborFinset v ∩ Iso).card = ∑ v ∈ Hub, (G.neighborFinset v ∩ Iso).card := by
    rw [hTdef, hRdef]; exact Finset.sum_filter_add_sum_filter_not Hub (fun h => G.degree h = 4) _
  have hRisoLe : ∑ v ∈ R, (G.neighborFinset v ∩ Iso).card ≤ 5 * R.card := by
    calc ∑ v ∈ R, (G.neighborFinset v ∩ Iso).card ≤ ∑ _v ∈ R, 5 :=
          Finset.sum_le_sum (fun v hv => by
            have := hisoLeDeg v; rw [hRdeg5 v hv] at this; exact this)
      _ = 5 * R.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have hHubiso27 : ∑ v ∈ Hub, (G.neighborFinset v ∩ Iso).card = 27 := by rw [hisoSum, hIso]
  have hsum27 : ∑ v ∈ T, (G.neighborFinset v ∩ Iso).card
      + ∑ v ∈ R, (G.neighborFinset v ∩ Iso).card = 27 := by rw [hpartIso, hHubiso27]
  have hTisoLe' : ∑ v ∈ T, (G.neighborFinset v ∩ Iso).card ≤ 2 * T.card + 2 := hTisoLe
  have hTiso : ∑ v ∈ T, (G.neighborFinset v ∩ Iso).card = 22 := by
    rw [hTcard] at hTisoLe'; rw [hRcard] at hRisoLe; omega
  -- all degree-`4` hubs have iso-degree `≥ 2` (all-at-cap).
  have hiso_le4 : ∀ a ∈ T, (G.neighborFinset a ∩ Iso).card ≤ 4 := by
    intro a ha; have := hisoLeDeg a; rw [hTdeg4 a ha] at this; exact this
  have hdecomp : ∀ a ∈ T, (G.neighborFinset a ∩ Iso).card
      = (if 1 ≤ (G.neighborFinset a ∩ Iso).card then 1 else 0)
        + (if 2 ≤ (G.neighborFinset a ∩ Iso).card then 1 else 0)
        + (if 3 ≤ (G.neighborFinset a ∩ Iso).card then 1 else 0)
        + (if 4 ≤ (G.neighborFinset a ∩ Iso).card then 1 else 0) := by
    intro a ha; have := hiso_le4 a ha; split_ifs <;> omega
  have hcong : ∑ a ∈ T, (G.neighborFinset a ∩ Iso).card
      = ∑ a ∈ T, ((if 1 ≤ (G.neighborFinset a ∩ Iso).card then 1 else 0)
        + (if 2 ≤ (G.neighborFinset a ∩ Iso).card then 1 else 0)
        + (if 3 ≤ (G.neighborFinset a ∩ Iso).card then 1 else 0)
        + (if 4 ≤ (G.neighborFinset a ∩ Iso).card then 1 else 0)) := Finset.sum_congr rfl hdecomp
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.card_filter, ← Finset.card_filter, ← Finset.card_filter, ← Finset.card_filter] at hcong
  have hc3 : T.filter (fun h => 3 ≤ (G.neighborFinset h ∩ Iso).card)
      = Hub.filter (fun h => G.degree h = 4 ∧ 3 ≤ (G.neighborFinset h ∩ Iso).card) := by
    rw [hTdef, Finset.filter_filter]
  have hc4 : T.filter (fun h => 4 ≤ (G.neighborFinset h ∩ Iso).card)
      = Hub.filter (fun h => G.degree h = 4 ∧ 4 ≤ (G.neighborFinset h ∩ Iso).card) := by
    rw [hTdef, Finset.filter_filter]
  have hc1le : (T.filter (fun h => 1 ≤ (G.neighborFinset h ∩ Iso).card)).card ≤ T.card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  have hc2le : (T.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)).card ≤ T.card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  rw [hc3, hc4] at hcong
  have hc2eq : (T.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)).card = 10 := by
    rw [hTiso] at hcong; rw [hTcard] at hc1le hc2le; omega
  have hTfilter2 : T.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card) = T :=
    Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
      (le_of_eq (hTcard.trans hc2eq.symm))
  have hTiso2 : ∀ a ∈ T, 2 ≤ (G.neighborFinset a ∩ Iso).card := by
    intro a ha
    have hmem : a ∈ T.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card) := by
      rw [hTfilter2]; exact ha
    exact (Finset.mem_filter.mp hmem).2
  -- the cover hypothesis on `T`.
  have hcov : ∀ a ∈ T, ∀ b ∈ T, a ≠ b → G.Adj a b ∨
      (G.neighborFinset a ∩ G.neighborFinset b ∩ Iso).Nonempty := by
    intro a ha b hb hab
    by_cases hadj : G.Adj a b
    · exact Or.inl hadj
    · refine Or.inr ?_
      have hk := key a (hTsubHub ha) b (hTsubHub hb) (hTdeg4 a ha) (hTdeg4 b hb) hab hadj
      have h2 : 2 ≤ min ((G.neighborFinset a ∩ Iso).card) ((G.neighborFinset b ∩ Iso).card) :=
        le_min (hTiso2 a ha) (hTiso2 b hb)
      rw [← Finset.card_pos]; omega
  -- the hub-side term: `∑_{a∈T} |N(a) ∩ T| ≤ 4·10 − 22 = 18`.
  have hEbound : (∑ a ∈ T, (G.neighborFinset a ∩ T).card) + 22 ≤ 40 := by
    have hpt : ∀ a ∈ T, (G.neighborFinset a ∩ T).card + (G.neighborFinset a ∩ Iso).card ≤ 4 := by
      intro a ha
      have hsub : (G.neighborFinset a ∩ T).card ≤ (G.neighborFinset a ∩ Hub).card :=
        Finset.card_le_card (Finset.inter_subset_inter (Finset.Subset.refl _) hTsubHub)
      have hnb := hub_neighbor_le_twenty G Hub Iso hdisj a (hTdeg4 a ha)
      omega
    have hsumpt := Finset.sum_le_sum hpt
    rw [Finset.sum_add_distrib, hTiso, Finset.sum_const, smul_eq_mul, hTcard] at hsumpt
    omega
  -- the twin-side term: each `M`-isolated twin meets `≤ 3` hubs, so `x(x−1) ≤ 6` over `|Iso| = 9`.
  have hQpt : ∀ t ∈ Iso, (G.neighborFinset t ∩ T).card * (G.neighborFinset t ∩ T).card
      - (G.neighborFinset t ∩ T).card ≤ 6 := by
    intro t ht
    set x : ℕ := (G.neighborFinset t ∩ T).card with hxdef
    have hx : x ≤ 3 := by
      have hsub : x ≤ (G.neighborFinset t ∩ Hub).card := by
        rw [hxdef]
        exact Finset.card_le_card (Finset.inter_subset_inter (Finset.Subset.refl _) hTsubHub)
      rw [hiso3 t ht] at hsub
      exact hsub
    have hmul : x * x ≤ 3 * x := Nat.mul_le_mul hx le_rfl
    calc x * x - x ≤ 3 * x - x := Nat.sub_le_sub_right hmul x
      _ ≤ 6 := by omega
  have hQ : ∑ t ∈ Iso, ((G.neighborFinset t ∩ T).card * (G.neighborFinset t ∩ T).card
      - (G.neighborFinset t ∩ T).card) ≤ 54 := by
    calc ∑ t ∈ Iso, ((G.neighborFinset t ∩ T).card * (G.neighborFinset t ∩ T).card
          - (G.neighborFinset t ∩ T).card) ≤ ∑ _t ∈ Iso, 6 := Finset.sum_le_sum hQpt
      _ = 54 := by rw [Finset.sum_const, smul_eq_mul, hIso]
  -- the cover inequality: `100 ≤ 10 + 18 + 54 = 82`, contradiction.
  have hCI := cover_offDiag_ineq_twenty G Iso T hcov
  rw [hTcard] at hCI
  omega

end N20

end ACMax
