import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N20.BipartiteAvoiderTwoHub

/-!
# The `n = 20` deg-5 corner `(10, 8, 42)` rich double-count kill

The `n = 20` `(10, 8, 42)` deg-5 corner, in the no-two-hub octahedron world, has a set `R` of five
*rich* degree-`4` hubs, each meeting the eight-vertex `M`-isolated twin set `Iso` (whose vertices
have degree exactly `3`) in `2` or `3` places.  Writing `SUM = ∑_R isoDeg` and
`ERR = ∑_R |N r ∩ R|` (twice the number of rich-rich edges), the corner supplies the combined
bound `SUM + ERR ≤ 13`.  This is impossible.

The proof is the shared-twin double count (`cherry_double_count`).  Writing
`share u v = |N u ∩ N v ∩ Iso|` and `k t = |N t ∩ R|`, we have
`∑_{u,v ∈ R} share u v = ∑_{t ∈ Iso} k t ^ 2 =: D`.  The no-two-hub hypothesis forces every
non-adjacent rich pair to share **at least one** twin, so the master row bound gives
`SUM + 20 ≤ D + ERR`; the pointwise square bound gives `D ≤ 2·SUM + 3 a` where `a` counts the
`k = 3` twins.  With `SUM + ERR ≤ 13` these force `a ≥ 3`; three `3`-subsets of the five-element
`R` must share a rich pair `{p, q}` in two twins.  If `{p, q}` is non-adjacent this contradicts the
good-`C₄` share-≤-`1` bound; if adjacent, that pair together with a common twin is a triangle of
degree sum `4 + 4 + 3 = 11`, killed by `hT`.
-/

namespace ACMax

open SimpleGraph Finset

open scoped Classical

namespace N20

/-- **The `n = 20` deg-5 corner `(10, 8, 42)` rich double-count kill.**  There is no graph on
`Fin 20` carrying the octahedron-world rich configuration `R` (five non-two-hub degree-`4` hubs
meeting the eight degree-`3` twins with `∑ isoDeg + ∑ |N r ∩ R| ≤ 13`). -/
theorem rich_doublecount_kill_1042_twenty (G : SimpleGraph (Fin 20))
    (Hub Iso R : Finset (Fin 20))
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hIsoDeg3 : ∀ t ∈ Iso, G.degree t = 3)
    (hT : ¬∃ x y z : Fin 20, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧ G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧
      G.degree x + G.degree y + G.degree z ≤ 11)
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hno2hub : ¬∃ h₁ h₂ : Fin 20, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧ G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧
      h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧ 2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card)
    (hRsub : R ⊆ Hub) (hRdeg4 : ∀ r ∈ R, G.degree r = 4)
    (hRiso2 : ∀ r ∈ R, 2 ≤ (G.neighborFinset r ∩ Iso).card) (hRcard : R.card = 5)
    (hRiso : (∑ r ∈ R, (G.neighborFinset r ∩ Iso).card)
        + (∑ r ∈ R, (G.neighborFinset r ∩ R).card) ≤ 13) :
    False := by
  classical
  -- Card of `N u ∩ S` as a sum of adjacency indicators over `S`.
  have hcardInter : ∀ (u : Fin 20) (S : Finset (Fin 20)),
      (G.neighborFinset u ∩ S).card = ∑ v ∈ S, (if G.Adj u v then (1 : ℕ) else 0) := by
    intro u S
    rw [Finset.inter_comm, ← Finset.filter_mem_eq_inter, Finset.card_filter]
    exact Finset.sum_congr rfl (fun v _ => by simp only [G.mem_neighborFinset])
  -- Incidence double count `Iso`–`R`.
  have hksum : (∑ t ∈ Iso, (G.neighborFinset t ∩ R).card)
      = ∑ r ∈ R, (G.neighborFinset r ∩ Iso).card := by
    calc (∑ t ∈ Iso, (G.neighborFinset t ∩ R).card)
        = ∑ t ∈ Iso, ∑ r ∈ R, (if G.Adj t r then (1 : ℕ) else 0) := by
          exact Finset.sum_congr rfl (fun t _ => hcardInter t R)
      _ = ∑ r ∈ R, ∑ t ∈ Iso, (if G.Adj t r then (1 : ℕ) else 0) := Finset.sum_comm
      _ = ∑ r ∈ R, ∑ t ∈ Iso, (if G.Adj r t then (1 : ℕ) else 0) :=
          Finset.sum_congr rfl (fun r _ =>
            Finset.sum_congr rfl (fun t _ => by rw [SimpleGraph.adj_comm]))
      _ = ∑ r ∈ R, (G.neighborFinset r ∩ Iso).card :=
          Finset.sum_congr rfl (fun r _ => (hcardInter r Iso).symm)
  -- Each twin meets `R` in at most `3` (since `R ⊆ Hub` and `|N t ∩ Hub| = 3`).
  have hk3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ R).card ≤ 3 := by
    intro t ht
    calc (G.neighborFinset t ∩ R).card
        ≤ (G.neighborFinset t ∩ Hub).card :=
          Finset.card_le_card (Finset.inter_subset_inter (Finset.Subset.refl _) hRsub)
      _ = 3 := hiso3 t ht
  -- Non-adjacent rich pairs share at least one twin (else `hno2hub` fires).
  have hshare_ge1 : ∀ u ∈ R, ∀ v ∈ R, u ≠ v → ¬G.Adj u v →
      1 ≤ (G.neighborFinset u ∩ G.neighborFinset v ∩ Iso).card := by
    intro u hu v hv hne hnadj
    by_contra hcon
    rw [not_le, Nat.lt_one_iff] at hcon
    have hpu : ((G.neighborFinset u ∩ Iso) ∩ G.neighborFinset v).card = 0 := by
      rw [Finset.inter_right_comm]; exact hcon
    have hpv : ((G.neighborFinset v ∩ Iso) ∩ G.neighborFinset u).card = 0 := by
      rw [Finset.inter_right_comm, Finset.inter_comm (G.neighborFinset v) (G.neighborFinset u)]
      exact hcon
    have hpu2 : 2 ≤ ((G.neighborFinset u ∩ Iso) \ G.neighborFinset v).card := by
      have := Finset.card_inter_add_card_sdiff (G.neighborFinset u ∩ Iso) (G.neighborFinset v)
      rw [hpu] at this
      have h2 := hRiso2 u hu
      omega
    have hpv2 : 2 ≤ ((G.neighborFinset v ∩ Iso) \ G.neighborFinset u).card := by
      have := Finset.card_inter_add_card_sdiff (G.neighborFinset v ∩ Iso) (G.neighborFinset u)
      rw [hpv] at this
      have h2 := hRiso2 v hv
      omega
    exact hno2hub ⟨u, v, hRsub hu, hRsub hv, hRdeg4 u hu, hRdeg4 v hv, hne, hnadj, hpu2, hpv2⟩
  -- Per-row lower bound: the row `u` contributes `isoDeg u + 4` plus its retained adjacent shares.
  have hrow : ∀ u ∈ R,
      (G.neighborFinset u ∩ Iso).card + 4
        + (∑ v ∈ R.erase u,
            (if G.Adj u v then (G.neighborFinset u ∩ G.neighborFinset v ∩ Iso).card else 0))
      ≤ (∑ v ∈ R, (G.neighborFinset u ∩ G.neighborFinset v ∩ Iso).card)
          + (G.neighborFinset u ∩ R).card := by
    intro u hu
    have hsplit : (∑ v ∈ R, (G.neighborFinset u ∩ G.neighborFinset v ∩ Iso).card)
        = (G.neighborFinset u ∩ Iso).card
          + ∑ v ∈ R.erase u, (G.neighborFinset u ∩ G.neighborFinset v ∩ Iso).card := by
      rw [← Finset.add_sum_erase R _ hu, Finset.inter_self]
    have hadjcard : (∑ v ∈ R.erase u, (if G.Adj u v then (1 : ℕ) else 0))
        = (G.neighborFinset u ∩ R).card := by
      rw [hcardInter u R,
        ← Finset.sum_erase R
          (by simp [SimpleGraph.irrefl] : (if G.Adj u u then (1 : ℕ) else 0) = 0)]
    have hNN4 : (∑ v ∈ R.erase u, (if ¬G.Adj u v then (1 : ℕ) else 0))
        + (G.neighborFinset u ∩ R).card = 4 := by
      have hpt : ∀ v : Fin 20,
          (if ¬G.Adj u v then (1 : ℕ) else 0) + (if G.Adj u v then (1 : ℕ) else 0) = 1 := by
        intro v; by_cases h : G.Adj u v <;> simp [h]
      have hsum1 : (∑ v ∈ R.erase u,
          ((if ¬G.Adj u v then (1 : ℕ) else 0) + (if G.Adj u v then (1 : ℕ) else 0)))
          = (R.erase u).card := by
        rw [Finset.sum_congr rfl (fun v _ => hpt v), Finset.sum_const, smul_eq_mul, mul_one]
      rw [Finset.sum_add_distrib, hadjcard, Finset.card_erase_of_mem hu, hRcard] at hsum1
      omega
    have hge : (∑ v ∈ R.erase u, (if ¬G.Adj u v then (1 : ℕ) else 0))
        + (∑ v ∈ R.erase u,
            (if G.Adj u v then (G.neighborFinset u ∩ G.neighborFinset v ∩ Iso).card else 0))
        ≤ ∑ v ∈ R.erase u, (G.neighborFinset u ∩ G.neighborFinset v ∩ Iso).card := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro v hv
      have hvR : v ∈ R := Finset.mem_of_mem_erase hv
      have hvu : u ≠ v := (Finset.ne_of_mem_erase hv).symm
      by_cases h : G.Adj u v
      · rw [if_neg (not_not_intro h), if_pos h]; omega
      · rw [if_pos h, if_neg h, add_zero]
        exact hshare_ge1 u hu v hvR hvu h
    omega
  -- Sum the rows: `SUM + 20 + (retained adjacent shares) ≤ (double count) + (rich-rich incidences)`.
  have hmaster : (∑ u ∈ R, (G.neighborFinset u ∩ Iso).card) + 20
        + (∑ u ∈ R, ∑ v ∈ R.erase u,
            (if G.Adj u v then (G.neighborFinset u ∩ G.neighborFinset v ∩ Iso).card else 0))
      ≤ (∑ u ∈ R, ∑ v ∈ R, (G.neighborFinset u ∩ G.neighborFinset v ∩ Iso).card)
          + (∑ u ∈ R, (G.neighborFinset u ∩ R).card) := by
    have hsum := Finset.sum_le_sum hrow
    simp only [Finset.sum_add_distrib] at hsum
    have hconst : (∑ _x ∈ R, (4 : ℕ)) = 20 := by
      rw [Finset.sum_const, hRcard]; rfl
    rw [hconst] at hsum
    omega
  -- The shared-twin double count identity.
  have hDC := cherry_double_count G R Iso
  -- Linear-programming upper bound `D ≤ 2·SUM + 3 a`, where `a` counts the `k = 3` twins.
  have hDub : (∑ t ∈ Iso, (G.neighborFinset t ∩ R).card * (G.neighborFinset t ∩ R).card)
      ≤ 2 * (∑ t ∈ Iso, (G.neighborFinset t ∩ R).card)
        + 3 * (Iso.filter (fun t => (G.neighborFinset t ∩ R).card = 3)).card := by
    have hsq : ∀ t ∈ Iso, (G.neighborFinset t ∩ R).card * (G.neighborFinset t ∩ R).card
        ≤ 2 * (G.neighborFinset t ∩ R).card
          + 3 * (if (G.neighborFinset t ∩ R).card = 3 then 1 else 0) := by
      intro t ht
      have hle := hk3 t ht
      rcases (show (G.neighborFinset t ∩ R).card = 0 ∨ (G.neighborFinset t ∩ R).card = 1
          ∨ (G.neighborFinset t ∩ R).card = 2 ∨ (G.neighborFinset t ∩ R).card = 3 by omega)
        with h | h | h | h <;> rw [h] <;> decide
    calc (∑ t ∈ Iso, (G.neighborFinset t ∩ R).card * (G.neighborFinset t ∩ R).card)
        ≤ ∑ t ∈ Iso, (2 * (G.neighborFinset t ∩ R).card
            + 3 * (if (G.neighborFinset t ∩ R).card = 3 then 1 else 0)) := Finset.sum_le_sum hsq
      _ = 2 * (∑ t ∈ Iso, (G.neighborFinset t ∩ R).card)
            + 3 * (∑ t ∈ Iso, (if (G.neighborFinset t ∩ R).card = 3 then (1 : ℕ) else 0)) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      _ = 2 * (∑ t ∈ Iso, (G.neighborFinset t ∩ R).card)
            + 3 * (Iso.filter (fun t => (G.neighborFinset t ∩ R).card = 3)).card := by
          rw [Finset.sum_boole, Nat.cast_id]
  -- At least three twins have `k = 3`.
  have ha3 : 3 ≤ (Iso.filter (fun t => (G.neighborFinset t ∩ R).card = 3)).card := by omega
  -- Two twins sharing two rich neighbours is impossible.
  have hpair : ∀ s ∈ Iso, ∀ w ∈ Iso, s ≠ w →
      2 ≤ ((G.neighborFinset s ∩ R) ∩ (G.neighborFinset w ∩ R)).card → False := by
    intro s hs w hw hsw hcard
    obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp (by omega :
      1 < ((G.neighborFinset s ∩ R) ∩ (G.neighborFinset w ∩ R)).card)
    have hp1 := Finset.mem_inter.mp hp
    have hq1 := Finset.mem_inter.mp hq
    have hpNs := (Finset.mem_inter.mp hp1.1).1
    have hpR := (Finset.mem_inter.mp hp1.1).2
    have hpNw := (Finset.mem_inter.mp hp1.2).1
    have hqNs := (Finset.mem_inter.mp hq1.1).1
    have hqR := (Finset.mem_inter.mp hq1.1).2
    have hqNw := (Finset.mem_inter.mp hq1.2).1
    have hsInpq : s ∈ G.neighborFinset p ∩ G.neighborFinset q ∩ Iso := by
      rw [Finset.mem_inter, Finset.mem_inter]
      refine ⟨⟨?_, ?_⟩, hs⟩
      · rw [G.mem_neighborFinset]; exact ((G.mem_neighborFinset s p).mp hpNs).symm
      · rw [G.mem_neighborFinset]; exact ((G.mem_neighborFinset s q).mp hqNs).symm
    have hwInpq : w ∈ G.neighborFinset p ∩ G.neighborFinset q ∩ Iso := by
      rw [Finset.mem_inter, Finset.mem_inter]
      refine ⟨⟨?_, ?_⟩, hw⟩
      · rw [G.mem_neighborFinset]; exact ((G.mem_neighborFinset w p).mp hpNw).symm
      · rw [G.mem_neighborFinset]; exact ((G.mem_neighborFinset w q).mp hqNw).symm
    have hshare2 : 2 ≤ (G.neighborFinset p ∩ G.neighborFinset q ∩ Iso).card :=
      Finset.one_lt_card.mpr ⟨s, hsInpq, w, hwInpq, hsw⟩
    by_cases hadjpq : G.Adj p q
    · -- The pair `{p, q}` and the common twin `s` form a triangle of degree sum `11`.
      have hAdjps : G.Adj p s := ((G.mem_neighborFinset s p).mp hpNs).symm
      have hAdjqs : G.Adj q s := ((G.mem_neighborFinset s q).mp hqNs).symm
      have hdeg : G.degree p + G.degree q + G.degree s ≤ 11 := by
        have h1 := hRdeg4 p hpR
        have h2 := hRdeg4 q hqR
        have h3 := hIsoDeg3 s hs
        omega
      exact hT ⟨p, q, s, hpq, hAdjqs.ne, hAdjps.ne, hadjpq, hAdjqs, hAdjps, hdeg⟩
    · have := hshare p (hRsub hpR) (hRdeg4 p hpR) q (hRsub hqR) (hRdeg4 q hqR) hpq hadjpq
      omega
  -- Extract three `k = 3` twins and apply the pair obstruction.
  obtain ⟨t₁, t₂, t₃, ht1, ht2, ht3, hne12, hne13, hne23⟩ :=
    Finset.two_lt_card_iff.mp (by omega :
      2 < (Iso.filter (fun t => (G.neighborFinset t ∩ R).card = 3)).card)
  have ht1I := (Finset.mem_filter.mp ht1).1
  have ht2I := (Finset.mem_filter.mp ht2).1
  have ht3I := (Finset.mem_filter.mp ht3).1
  have hA1card : (G.neighborFinset t₁ ∩ R).card = 3 := (Finset.mem_filter.mp ht1).2
  have hA2card : (G.neighborFinset t₂ ∩ R).card = 3 := (Finset.mem_filter.mp ht2).2
  have hA3card : (G.neighborFinset t₃ ∩ R).card = 3 := (Finset.mem_filter.mp ht3).2
  -- Three `3`-subsets of the five-element `R` must share a rich pair in two twins.
  have hdisj : 2 ≤ ((G.neighborFinset t₁ ∩ R) ∩ (G.neighborFinset t₂ ∩ R)).card
      ∨ 2 ≤ ((G.neighborFinset t₁ ∩ R) ∩ (G.neighborFinset t₃ ∩ R)).card
      ∨ 2 ≤ ((G.neighborFinset t₂ ∩ R) ∩ (G.neighborFinset t₃ ∩ R)).card := by
    by_contra hcon
    push Not at hcon
    obtain ⟨hc12, hc13, hc23⟩ := hcon
    have hu12 : (G.neighborFinset t₁ ∩ R) ∪ (G.neighborFinset t₂ ∩ R) = R := by
      apply Finset.eq_of_subset_of_card_le
      · exact Finset.union_subset Finset.inter_subset_right Finset.inter_subset_right
      · have := Finset.card_union_add_card_inter (G.neighborFinset t₁ ∩ R) (G.neighborFinset t₂ ∩ R)
        rw [hA1card, hA2card] at this
        omega
    have hA3sub : G.neighborFinset t₃ ∩ R
        ⊆ (G.neighborFinset t₁ ∩ R) ∪ (G.neighborFinset t₂ ∩ R) := by
      rw [hu12]; exact Finset.inter_subset_right
    have hA3eq : G.neighborFinset t₃ ∩ R
        = (G.neighborFinset t₃ ∩ R) ∩ (G.neighborFinset t₁ ∩ R)
          ∪ (G.neighborFinset t₃ ∩ R) ∩ (G.neighborFinset t₂ ∩ R) := by
      have h := Finset.inter_eq_left.mpr hA3sub
      rw [Finset.inter_union_distrib_left] at h
      exact h.symm
    have hle3 : (G.neighborFinset t₃ ∩ R).card
        ≤ ((G.neighborFinset t₃ ∩ R) ∩ (G.neighborFinset t₁ ∩ R)).card
          + ((G.neighborFinset t₃ ∩ R) ∩ (G.neighborFinset t₂ ∩ R)).card :=
      calc (G.neighborFinset t₃ ∩ R).card
          = ((G.neighborFinset t₃ ∩ R) ∩ (G.neighborFinset t₁ ∩ R)
              ∪ (G.neighborFinset t₃ ∩ R) ∩ (G.neighborFinset t₂ ∩ R)).card :=
            congrArg Finset.card hA3eq
        _ ≤ _ := Finset.card_union_le _ _
    have e13 : ((G.neighborFinset t₃ ∩ R) ∩ (G.neighborFinset t₁ ∩ R)).card
        = ((G.neighborFinset t₁ ∩ R) ∩ (G.neighborFinset t₃ ∩ R)).card := by
      rw [Finset.inter_comm]
    have e23 : ((G.neighborFinset t₃ ∩ R) ∩ (G.neighborFinset t₂ ∩ R)).card
        = ((G.neighborFinset t₂ ∩ R) ∩ (G.neighborFinset t₃ ∩ R)).card := by
      rw [Finset.inter_comm]
    omega
  rcases hdisj with h | h | h
  · exact hpair t₁ ht1I t₂ ht2I hne12 h
  · exact hpair t₁ ht1I t₃ ht3I hne13 h
  · exact hpair t₂ ht2I t₃ ht3I hne23 h

end N20

end ACMax
