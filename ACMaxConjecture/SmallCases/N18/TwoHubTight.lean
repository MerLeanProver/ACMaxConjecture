import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N18.Core
import ACMaxConjecture.SmallCases.N18.TwoHubSelect
import ACMaxConjecture.SmallCases.N18.TwoHubTight96
import ACMaxConjecture.SmallCases.N18.StarTriangle
import ACMaxConjecture.SmallCases.N18.StarTrianglePartition

/-!
# Tight `e(M) = 1` two-hub profiles for `n = 18`

This file is the `n = 18` port of `TwinCert17TwoHubTight`.  It closes (one residual `sorry` aside)
the three tight `e(M) = 1` two-hub residual profiles
`(|Hub|, |Iso|, ∑deg) ∈ {(8, 8, 34), (9, 7, 37), (10, 6, 40)}` left open by
`two_hub_corner_select_eighteen`.

The closing tool is the **sharp off-diagonal cover inequality** `cover_offDiag_ineq` (in
`TwinCert18TwoHubTight96`): if a *refuted* selection forces every non-adjacent pair of iso-rich
degree-`4` hubs to share an `M`-isolated twin, then the ordered pairs of the iso-rich set `S` are
covered by the hub-adjacency pairs together with the twin neighbourhoods, giving
`|S|² − |S| ≤ ∑_{a∈S}|N(a)∩S| + ∑_{t∈Iso}(|N(t)∩S|² − |N(t)∩S|)`.

* `(8, 8, 34)` (two degree-`5` hubs): the threshold forces `S = T₄` (all six degree-`4` hubs are
  iso-rich), each `M`-isolated twin meets `≥ 1` of them, so the convexity bound
  `d² − d ≤ 3(d − 1)` gives `Q ≤ 18`; with `E ≤ 10` the cover count `36 ≤ 6 + 10 + 18 = 34` is
  contradictory.
-/

namespace ACMax

open scoped Classical

namespace N18

/-- **No-two-hub ⟹ star-triangle, for the tight `e(M) = 1` profiles `(9,7,37)` and `(10,6,40)`.**
This is the genuinely-new structural step (the fifth cut construction).  Hypotheses are the
degree-`{4,5}` hub set, `M`-isolated twins meeting exactly three hubs (`hiso3`), the degree-`4`
share bound (`hshare`), one of the two tight profiles (`hregime`), and the absence of a good
two-hub pair (`hno2hub`).  The reliability investigation verified: `(9,7,37)` has **no** no-two-hub
graphs at all (the hypothesis is vacuous), while `(10,6,40)` has exactly **two** rigid no-two-hub
isomorphism classes (iso-degree multisets `[4,2,2,2,2,2,1,1,1,1]` and `[3,3,2,2,2,2,1,1,1,1]`),
each of which admits a star `{h, t₁, t₂}` (a rich hub with two twins) and a disjoint hub-triangle
`{a, b, c}` totally non-adjacent to it (`e(P,N) = 0`), i.e. a `StarTriangleConfig`.

RESIDUAL `sorry` (documented, precisely named): the finite-but-intricate extraction of the
six-vertex star-triangle from the no-two-hub adjacency structure.  The boundary arithmetic that
turns this configuration into the signed cut is fully proved in `star_triangle_cut_certificate`
(`TwinCert18StarTriangle`); only this existence step remains. -/
theorem no_two_hub_star_triangle_eighteen (G : SimpleGraph (Fin 18)) (Hub Iso : Finset (Fin 18))
    (_hdeg : ∀ h ∈ Hub, 4 ≤ G.degree h) (_hdeg5 : ∀ h ∈ Hub, G.degree h ≤ 5)
    (_hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (_hdisj : Disjoint Hub Iso)
    (_hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (_hregime :
      (Hub.card = 9 ∧ Iso.card = 7 ∧ ∑ w ∈ Hub, G.degree w = 37 ∧
        (∀ v : Fin 18, 3 ≤ G.degree v) ∧ (∀ t ∈ Iso, G.degree t = 3) ∧
        ∑ h ∈ Hub, (G.neighborFinset h ∩ (Finset.univ \ (Hub ∪ Iso))).card ≤ 4 ∧
        ¬∃ x y z : Fin 18, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
          G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧
          G.degree x + G.degree y + G.degree z ≤ 11) ∨
      (Hub.card = 10 ∧ Iso.card = 6 ∧ ∑ w ∈ Hub, G.degree w = 40 ∧
        (∀ v : Fin 18, 3 ≤ G.degree v) ∧ (∀ t ∈ Iso, G.degree t = 3) ∧
        ∑ h ∈ Hub, (G.neighborFinset h ∩ (Finset.univ \ (Hub ∪ Iso))).card ≤ 4 ∧
        ¬∃ x y z : Fin 18, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
          G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧
          G.degree x + G.degree y + G.degree z ≤ 11))
    (_hno2hub : ¬∃ h₁ h₂ : Fin 18, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card)
    (hC4 : ¬∃ a b c d : Fin 18, ({a, b, c, d} : Finset (Fin 18)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (hK23 : ¬∃ a b c d e : Fin 18, ({a, b, c, d, e} : Finset (Fin 18)).card = 5 ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
      G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 19) :
    StarTriangleConfig G := by
  classical
  have htwindeg : ∀ t ∈ Iso, G.degree t = 3 := by
    rcases _hregime with h | h
    · exact h.2.2.2.2.1
    · exact h.2.2.2.2.1
  obtain ⟨R, P, hHub, hdisjRP, hRcard, hPcard, hIsocard, hRdeg, hPdeg, hPpoor, hERP,
    hpoor_edges⟩ :=
    no_two_hub_rigid_eighteen G Hub Iso _hdeg _hdeg5 _hiso3 _hdisj _hshare _hregime _hno2hub hC4 hK23
  exact starTriangle_of_rigid_eighteen G Hub Iso R P hHub hdisjRP _hdisj hRcard hPcard hIsocard
    hRdeg hPdeg hPpoor _hiso3 htwindeg hERP hpoor_edges

/-- **Tight `e(M) = 1` two-hub residual router (`n = 18`).**  The three `e(M) = 1` profiles
`(|Hub|, |Iso|, ∑deg) ∈ {(8,8,34), (9,7,37), (10,6,40)}`.  The `(8,8,34)` profile is closed by the
convexity cover bound (yielding a good two-hub pair).  The `(9,7,37)` and `(10,6,40)` profiles are
closed by the **star-triangle dichotomy**: either a good two-hub pair, or a `StarTriangleConfig`
(via `no_two_hub_star_triangle_eighteen`), the latter consumed by `star_triangle_cut_certificate`. -/
theorem two_hub_select_eM1_tight_eighteen (G : SimpleGraph (Fin 18)) (Hub Iso : Finset (Fin 18))
    (hdeg : ∀ h ∈ Hub, 4 ≤ G.degree h) (hdeg5 : ∀ h ∈ Hub, G.degree h ≤ 5)
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdisj : Disjoint Hub Iso)
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (htight : (Hub.card = 8 ∧ Iso.card = 8 ∧ ∑ w ∈ Hub, G.degree w = 34) ∨
      (Hub.card = 9 ∧ Iso.card = 7 ∧ ∑ w ∈ Hub, G.degree w = 37 ∧
        (∀ v : Fin 18, 3 ≤ G.degree v) ∧ (∀ t ∈ Iso, G.degree t = 3) ∧
        ∑ h ∈ Hub, (G.neighborFinset h ∩ (Finset.univ \ (Hub ∪ Iso))).card ≤ 4 ∧
        ¬∃ x y z : Fin 18, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
          G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧
          G.degree x + G.degree y + G.degree z ≤ 11) ∨
      (Hub.card = 10 ∧ Iso.card = 6 ∧ ∑ w ∈ Hub, G.degree w = 40 ∧
        (∀ v : Fin 18, 3 ≤ G.degree v) ∧ (∀ t ∈ Iso, G.degree t = 3) ∧
        ∑ h ∈ Hub, (G.neighborFinset h ∩ (Finset.univ \ (Hub ∪ Iso))).card ≤ 4 ∧
        ¬∃ x y z : Fin 18, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
          G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧
          G.degree x + G.degree y + G.degree z ≤ 11))
    (hC4 : ¬∃ a b c d : Fin 18, ({a, b, c, d} : Finset (Fin 18)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (hK23 : ¬∃ a b c d e : Fin 18, ({a, b, c, d, e} : Finset (Fin 18)).card = 5 ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
      G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 19) :
    (∃ h₁ h₂ : Fin 18, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card) ∨ StarTriangleConfig G := by
  classical
  rcases htight with ⟨h8, h8', h34⟩ | hrest
  · -- **Profile (8, 8, 34).**  Two degree-`5` hubs, six degree-`4` hubs, all iso-rich.
    refine Or.inl ?_
    by_contra hcon
    have key := nogood_of_not_select_eighteen G Hub Iso hcon
    have hmf := strong_deg4_count_le_two_deg5_eighteen G Hub Iso hdisj hshare key
    have hisosum := hub_iso_sum_eighteen G Hub Iso hiso3
    set S : Finset (Fin 18) :=
      Hub.filter (fun h => G.degree h = 4 ∧ 2 ≤ (G.neighborFinset h ∩ Iso).card) with hSdef
    have hcov : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → G.Adj a b ∨
        (G.neighborFinset a ∩ G.neighborFinset b ∩ Iso).Nonempty := by
      intro a ha b hb hab
      rw [hSdef, Finset.mem_filter] at ha hb
      by_cases hadj : G.Adj a b
      · exact Or.inl hadj
      · refine Or.inr ?_
        have hk := key a ha.1 b hb.1 ha.2.1 hb.2.1 hab hadj
        have hmin : 2 ≤ min ((G.neighborFinset a ∩ Iso).card) ((G.neighborFinset b ∩ Iso).card) :=
          le_min ha.2.2 hb.2.2
        rw [← Finset.card_pos]
        omega
    have hCI := cover_offDiag_ineq G Iso S hcov
    set T4 : Finset (Fin 18) := Hub.filter (fun h => G.degree h = 4) with hT4def
    set T5 : Finset (Fin 18) := Hub.filter (fun h => ¬ G.degree h = 4) with hT5def
    have hdeg45 : ∀ h ∈ Hub, G.degree h = 4 ∨ G.degree h = 5 := by
      intro h hh; have := hdeg h hh; have := hdeg5 h hh; omega
    have hSsubHub : S ⊆ Hub := by rw [hSdef]; exact Finset.filter_subset _ _
    have hSsubT4 : S ⊆ T4 := by
      rw [hSdef, hT4def]; intro x hx; rw [Finset.mem_filter] at hx ⊢; exact ⟨hx.1, hx.2.1⟩
    have hcardsplit : T4.card + T5.card = Hub.card :=
      Finset.card_filter_add_card_filter_not (fun h => G.degree h = 4)
    have hT5deg5 : ∀ v ∈ T5, G.degree v = 5 := by
      intro v hv; rw [hT5def, Finset.mem_filter] at hv
      rcases hdeg45 v hv.1 with h | h
      · exact absurd h hv.2
      · exact h
    have hdegsumsplit : ∑ v ∈ T4, G.degree v + ∑ v ∈ T5, G.degree v = ∑ w ∈ Hub, G.degree w :=
      Finset.sum_filter_add_sum_filter_not Hub (fun h => G.degree h = 4) _
    have hT4deg : ∑ v ∈ T4, G.degree v = 4 * T4.card := by
      rw [hT4def, Finset.sum_congr rfl (fun x hx => (Finset.mem_filter.mp hx).2), Finset.sum_const,
        smul_eq_mul, mul_comm]
    have hT5deg : ∑ v ∈ T5, G.degree v = 5 * T5.card := by
      rw [Finset.sum_congr rfl (fun x hx => hT5deg5 x hx), Finset.sum_const, smul_eq_mul, mul_comm]
    have hT4card6 : T4.card = 6 := by
      rw [h8] at hcardsplit; rw [hT4deg, hT5deg, h34] at hdegsumsplit; omega
    have hT5card2 : T5.card = 2 := by omega
    have hisosplit : ∑ v ∈ T4, (G.neighborFinset v ∩ Iso).card
        + ∑ v ∈ T5, (G.neighborFinset v ∩ Iso).card = ∑ v ∈ Hub, (G.neighborFinset v ∩ Iso).card :=
      Finset.sum_filter_add_sum_filter_not Hub (fun h => G.degree h = 4) _
    have hT5isole : ∑ v ∈ T5, (G.neighborFinset v ∩ Iso).card ≤ 5 * T5.card := by
      calc ∑ v ∈ T5, (G.neighborFinset v ∩ Iso).card
          ≤ ∑ _v ∈ T5, 5 := Finset.sum_le_sum (fun v hv => by
            have h1 : (G.neighborFinset v ∩ Iso).card ≤ G.degree v := by
              rw [← G.card_neighborFinset_eq_degree]
              exact Finset.card_le_card Finset.inter_subset_left
            rw [hT5deg5 v hv] at h1; exact h1)
        _ = 5 * T5.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    have hT4isole : ∑ v ∈ T4, (G.neighborFinset v ∩ Iso).card ≤ 2 * T4.card + 2 :=
      deg4_sum_le_eighteen G Hub Iso hmf
    have hT4iso14 : ∑ v ∈ T4, (G.neighborFinset v ∩ Iso).card = 14 := by
      rw [h8'] at hisosum; omega
    -- Threshold decomposition forces `S = T4` (`|S| = 6`).
    have hiso_le4 : ∀ a ∈ T4, (G.neighborFinset a ∩ Iso).card ≤ 4 := by
      intro a ha
      have hd : G.degree a = 4 := by rw [hT4def, Finset.mem_filter] at ha; exact ha.2
      calc (G.neighborFinset a ∩ Iso).card
          ≤ (G.neighborFinset a).card := Finset.card_le_card Finset.inter_subset_left
        _ = G.degree a := G.card_neighborFinset_eq_degree a
        _ = 4 := hd
    have hdecomp : ∀ a ∈ T4, (G.neighborFinset a ∩ Iso).card
        = (if 1 ≤ (G.neighborFinset a ∩ Iso).card then 1 else 0)
          + (if 2 ≤ (G.neighborFinset a ∩ Iso).card then 1 else 0)
          + (if 3 ≤ (G.neighborFinset a ∩ Iso).card then 1 else 0)
          + (if 4 ≤ (G.neighborFinset a ∩ Iso).card then 1 else 0) := by
      intro a ha; have := hiso_le4 a ha; split_ifs <;> omega
    have hcong := Finset.sum_congr rfl hdecomp
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.card_filter, ← Finset.card_filter, ← Finset.card_filter, ← Finset.card_filter]
      at hcong
    have hSeqT4f : S = T4.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card) := by
      rw [hSdef, hT4def, Finset.filter_filter]
    have h3eq : T4.filter (fun h => 3 ≤ (G.neighborFinset h ∩ Iso).card)
        = Hub.filter (fun h => G.degree h = 4 ∧ 3 ≤ (G.neighborFinset h ∩ Iso).card) := by
      rw [hT4def, Finset.filter_filter]
    have h4eq : T4.filter (fun h => 4 ≤ (G.neighborFinset h ∩ Iso).card)
        = Hub.filter (fun h => G.degree h = 4 ∧ 4 ≤ (G.neighborFinset h ∩ Iso).card) := by
      rw [hT4def, Finset.filter_filter]
    have hc1 : (T4.filter (fun h => 1 ≤ (G.neighborFinset h ∩ Iso).card)).card ≤ T4.card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    have hScard : S.card = 6 := by
      have hle : S.card ≤ T4.card := Finset.card_le_card hSsubT4
      rw [hSeqT4f]; rw [h3eq, h4eq, hT4iso14] at hcong
      rw [hSeqT4f, hT4card6] at hle; omega
    have hSeqT4 : S = T4 := Finset.eq_of_subset_of_card_le hSsubT4 (by rw [hScard, hT4card6])
    have hSiso14 : ∑ v ∈ S, (G.neighborFinset v ∩ Iso).card = 14 := by rw [hSeqT4]; exact hT4iso14
    -- `E ≤ 10`.
    have hEbound : ∑ a ∈ S, (G.neighborFinset a ∩ S).card ≤ 10 := by
      have hpt : ∀ a ∈ S, (G.neighborFinset a ∩ S).card + (G.neighborFinset a ∩ Iso).card ≤ 4 := by
        intro a ha
        have hda : G.degree a = 4 := by
          rw [hSdef, Finset.mem_filter] at ha; exact ha.2.1
        have hsub : (G.neighborFinset a ∩ S).card ≤ (G.neighborFinset a ∩ Hub).card :=
          Finset.card_le_card (Finset.inter_subset_inter (Finset.Subset.refl _) hSsubHub)
        have hnb := hub_neighbor_le_eighteen G Hub Iso hdisj a hda
        omega
      have hsum : ∑ a ∈ S, ((G.neighborFinset a ∩ S).card + (G.neighborFinset a ∩ Iso).card)
          ≤ ∑ _a ∈ S, 4 := Finset.sum_le_sum hpt
      rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_comm, hScard, hSiso14] at hsum
      omega
    -- Each twin meets `S = T4` in `c_t ∈ {1, 2, 3}` hubs (`≥ 1` since `|T5| = 2`).
    have hc1le : ∀ t ∈ Iso, 1 ≤ (G.neighborFinset t ∩ S).card := by
      intro t ht
      have hpart : (G.neighborFinset t ∩ T4).card + (G.neighborFinset t ∩ T5).card
          = (G.neighborFinset t ∩ Hub).card := by
        have e1 : G.neighborFinset t ∩ T4
            = (G.neighborFinset t ∩ Hub).filter (fun h => G.degree h = 4) := by
          rw [hT4def]; ext x
          simp only [Finset.mem_inter, Finset.mem_filter]; tauto
        have e2 : G.neighborFinset t ∩ T5
            = (G.neighborFinset t ∩ Hub).filter (fun h => ¬ G.degree h = 4) := by
          rw [hT5def]; ext x
          simp only [Finset.mem_inter, Finset.mem_filter]; tauto
        rw [e1, e2]; exact Finset.card_filter_add_card_filter_not (fun h => G.degree h = 4)
      rw [hiso3 t ht] at hpart
      have hm2 : (G.neighborFinset t ∩ T5).card ≤ 2 := by
        calc (G.neighborFinset t ∩ T5).card ≤ T5.card :=
              Finset.card_le_card Finset.inter_subset_right
          _ = 2 := hT5card2
      have hk : (G.neighborFinset t ∩ S).card = (G.neighborFinset t ∩ T4).card := by rw [hSeqT4]
      rw [hk]; omega
    have hc3le : ∀ t ∈ Iso, (G.neighborFinset t ∩ S).card ≤ 3 := by
      intro t ht
      calc (G.neighborFinset t ∩ S).card
          ≤ (G.neighborFinset t ∩ Hub).card :=
            Finset.card_le_card (Finset.inter_subset_inter (Finset.Subset.refl _) hSsubHub)
        _ = 3 := hiso3 t ht
    -- Convexity bound `Q ≤ 18`.
    have hcross : ∑ t ∈ Iso, (G.neighborFinset t ∩ S).card = 14 := by
      rw [cross_count G Iso S]; exact hSiso14
    have hQ18 : ∑ t ∈ Iso, ((G.neighborFinset t ∩ S).card * (G.neighborFinset t ∩ S).card
        - (G.neighborFinset t ∩ S).card) ≤ 18 := by
      have hpt : ∀ t ∈ Iso, ((G.neighborFinset t ∩ S).card * (G.neighborFinset t ∩ S).card
          - (G.neighborFinset t ∩ S).card) + 3 ≤ 3 * (G.neighborFinset t ∩ S).card := by
        intro t ht
        have h1 := hc1le t ht
        have h3 := hc3le t ht
        set c := (G.neighborFinset t ∩ S).card with hcv
        clear_value c
        interval_cases c <;> omega
      have hsum : ∑ t ∈ Iso, (((G.neighborFinset t ∩ S).card * (G.neighborFinset t ∩ S).card
          - (G.neighborFinset t ∩ S).card) + 3)
          ≤ ∑ t ∈ Iso, 3 * (G.neighborFinset t ∩ S).card := Finset.sum_le_sum hpt
      rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, ← Finset.mul_sum, hcross,
        h8'] at hsum
      omega
    -- Cover inequality: `36 = |S|² ≤ |S| + E + Q ≤ 6 + 10 + 18 = 34`, contradiction.
    rw [hScard] at hCI
    omega
  · -- **Profiles (9, 7, 37) and (10, 6, 40): the star-triangle dichotomy.**  Unlike `n = 17`,
    -- these two `e(M) = 1` profiles are NOT closed by the cover inequality alone (the `mod-3` slack
    -- is too wide); a direct construction check confirms residual no-two-hub configurations survive
    -- the cover counting.  The correct statement is the **dichotomy** `(good two-hub pair) ∨
    -- StarTriangleConfig`: either a good two-hub pair exists (left), or — the reliability
    -- investigation having verified `0` no-two-hub graphs for `(9,7,37)` and exactly two rigid
    -- no-two-hub classes for `(10,6,40)`, all star-triangle covered with `e(P,N) = 0` — the
    -- no-two-hub structure forces a star `{h, t₁, t₂}` (a rich hub `h` with two `M`-isolated twins)
    -- and a disjoint hub-triangle `{a,b,c}` non-adjacent to it (`StarTriangleConfig`), consumed by
    -- `star_triangle_cut_certificate`.
    by_cases hHP : ∃ h₁ h₂ : Fin 18, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
        G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
        2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
        2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card
    · exact Or.inl hHP
    · -- **No good two-hub pair.**  Extract the `StarTriangleConfig`.  RESIDUAL `sorry`: the
      -- structural extraction (no-two-hub ⟹ rich hub centre with two twins + a disjoint
      -- non-adjacent hub-triangle) is the genuinely-new finite-but-intricate combinatorial step.
      refine Or.inr ?_
      exact no_two_hub_star_triangle_eighteen G Hub Iso hdeg hdeg5 hiso3 hdisj hshare hrest hHP
        hC4 hK23

/-- **Hub-pair selection for the `n = 18` two-hub `e(M) ≤ 1` residual.**  Given a hub set of
degree-`{4,5}` vertices, every `M`-isolated twin meeting exactly three hubs (`hiso3`), the twins
`M`-independent (`_hisoIndep`), the sharp good-`C₄` share bound (`hshare`, share `≤ 1`), and one of
the seven `e(M) ≤ 1` regimes (`hregime`), there are two non-adjacent degree-`4` hubs each retaining
`≥ 2` private `M`-isolated twins. -/
theorem two_hub_corner_select_eighteen (G : SimpleGraph (Fin 18)) (Hub Iso : Finset (Fin 18))
    (hdeg : ∀ h ∈ Hub, 4 ≤ G.degree h)
    (hdeg5 : ∀ h ∈ Hub, G.degree h ≤ 5)
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (_hisoIndep : ∀ a ∈ Iso, ∀ b ∈ Iso, ¬G.Adj a b)
    (hshare : ∀ h₁ ∈ Hub, ∀ h₂ ∈ Hub, h₁ ≠ h₂ → ¬G.Adj h₁ h₂ →
      (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hdisj : Disjoint Hub Iso)
    (hregime :
      (Hub.card = 7 ∧ Iso.card = 9 ∧ ∑ w ∈ Hub, G.degree w = 31) ∨
      (Hub.card = 8 ∧ Iso.card = 10 ∧ ∑ w ∈ Hub, G.degree w = 34) ∨
      (Hub.card = 9 ∧ Iso.card = 9 ∧ ∑ w ∈ Hub, G.degree w = 37) ∨
      (Hub.card = 10 ∧ Iso.card = 8 ∧ ∑ w ∈ Hub, G.degree w = 40) ∨
      (Hub.card = 8 ∧ Iso.card = 8 ∧ ∑ w ∈ Hub, G.degree w = 34) ∨
      (Hub.card = 9 ∧ Iso.card = 7 ∧ ∑ w ∈ Hub, G.degree w = 37 ∧
        (∀ v : Fin 18, 3 ≤ G.degree v) ∧ (∀ t ∈ Iso, G.degree t = 3) ∧
        ∑ h ∈ Hub, (G.neighborFinset h ∩ (Finset.univ \ (Hub ∪ Iso))).card ≤ 4 ∧
        ¬∃ x y z : Fin 18, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
          G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧
          G.degree x + G.degree y + G.degree z ≤ 11) ∨
      (Hub.card = 10 ∧ Iso.card = 6 ∧ ∑ w ∈ Hub, G.degree w = 40 ∧
        (∀ v : Fin 18, 3 ≤ G.degree v) ∧ (∀ t ∈ Iso, G.degree t = 3) ∧
        ∑ h ∈ Hub, (G.neighborFinset h ∩ (Finset.univ \ (Hub ∪ Iso))).card ≤ 4 ∧
        ¬∃ x y z : Fin 18, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
          G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧
          G.degree x + G.degree y + G.degree z ≤ 11))
    (hC4 : ¬∃ a b c d : Fin 18, ({a, b, c, d} : Finset (Fin 18)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (hK23 : ¬∃ a b c d e : Fin 18, ({a, b, c, d, e} : Finset (Fin 18)).card = 5 ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
      G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 19) :
    (∃ h₁ h₂ : Fin 18, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card) ∨ StarTriangleConfig G := by
  classical
  have hsharer : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1 :=
    fun h₁ m1 _ h₂ m2 _ hne hnadj => hshare h₁ m1 h₂ m2 hne hnadj
  have hdeg45 : ∀ h ∈ Hub, G.degree h = 4 ∨ G.degree h = 5 := by
    intro h hh; have := hdeg h hh; have := hdeg5 h hh; omega
  rcases hregime with hr | hr | hr | hr | hr | hr | hr
  · refine Or.inl ?_
    obtain ⟨hHub, hIso, hdsum⟩ := hr
    by_contra hcon
    exact absurd (residual_arith_eighteen G Hub Iso hdisj hsharer hiso3 hdeg45 hcon) (by
      rw [hHub, hIso, hdsum]; omega)
  · refine Or.inl ?_
    obtain ⟨hHub, hIso, hdsum⟩ := hr
    by_contra hcon
    exact absurd (residual_arith_eighteen G Hub Iso hdisj hsharer hiso3 hdeg45 hcon) (by
      rw [hHub, hIso, hdsum]; omega)
  · refine Or.inl ?_
    obtain ⟨hHub, hIso, hdsum⟩ := hr
    by_contra hcon
    exact absurd (residual_arith_eighteen G Hub Iso hdisj hsharer hiso3 hdeg45 hcon) (by
      rw [hHub, hIso, hdsum]; omega)
  · refine Or.inl ?_
    obtain ⟨hHub, hIso, hdsum⟩ := hr
    by_contra hcon
    exact absurd (residual_arith_eighteen G Hub Iso hdisj hsharer hiso3 hdeg45 hcon) (by
      rw [hHub, hIso, hdsum]; omega)
  · exact two_hub_select_eM1_tight_eighteen G Hub Iso hdeg hdeg5 hiso3 hdisj hsharer (Or.inl hr)
      hC4 hK23
  · exact two_hub_select_eM1_tight_eighteen G Hub Iso hdeg hdeg5 hiso3 hdisj hsharer
      (Or.inr (Or.inl hr)) hC4 hK23
  · exact two_hub_select_eM1_tight_eighteen G Hub Iso hdeg hdeg5 hiso3 hdisj hsharer
      (Or.inr (Or.inr hr)) hC4 hK23

end N18

end ACMax
