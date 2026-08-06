import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N17.Core
import ACMaxConjecture.SmallCases.N17.TwoHubSelect
import ACMaxConjecture.SmallCases.N17.TwoHubTight96

/-!
# Tight `e(M) = 1` two-hub profiles for `n = 17`

This file closes the two tight `e(M) = 1` two-hub residual profiles
`(|Hub|, |Iso|, ∑deg) ∈ {(8, 7, 33), (9, 6, 36)}` left open by
`two_hub_select_eM1_tight_seventeen` in `TwinCert17TwoHubSelect`.

The closing tool is a **sharp off-diagonal cover inequality**: if a *refuted* selection forces every
non-adjacent pair of "iso-rich" degree-`4` hubs (iso-degree `≥ 2`) to share an `M`-isolated twin,
then the ordered pairs of the iso-rich set `S` are covered by the hub-adjacency pairs together with
the twin neighbourhoods, giving
`|S|² − |S| ≤ ∑_{a∈S}|N(a)∩S| + ∑_{t∈Iso}(|N(t)∩S|² − |N(t)∩S|)`.
Bounding the right side via the degree structure (each twin meets exactly three hubs) refutes both
tight profiles numerically, so no new structural hypothesis is needed.
-/

namespace ACMax

open scoped Classical

namespace N17

/-- **Tight `e(M) = 1` residual.**  The two tight `e(M) = 1` profiles
`(|Hub|, |Iso|, ∑deg) ∈ {(8, 7, 33), (9, 6, 36)}` are closed by the sharp off-diagonal cover
inequality.  In the `(8, 7, 33)` profile the single degree-`5` hub is forced to be isolated from the
other hubs (`isoDeg = 5`), so the seven degree-`4` hubs are all iso-rich and the cover count
`49 ≤ 7 + 12 + 22 = 41` is contradictory; hence a good non-adjacent degree-`4` pair exists. -/
theorem two_hub_select_eM1_tight_seventeen (G : SimpleGraph (Fin 17)) (Hub Iso : Finset (Fin 17))
    (hdeg : ∀ h ∈ Hub, 4 ≤ G.degree h) (hdeg5 : ∀ h ∈ Hub, G.degree h ≤ 5)
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdisj : Disjoint Hub Iso)
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (htight : (Hub.card = 8 ∧ Iso.card = 7 ∧ ∑ w ∈ Hub, G.degree w = 33) ∨
      (Hub.card = 9 ∧ Iso.card = 6 ∧ ∑ w ∈ Hub, G.degree w = 36 ∧
        (∀ v : Fin 17, 3 ≤ G.degree v) ∧ (∀ t ∈ Iso, G.degree t = 3) ∧
        ∑ h ∈ Hub, (G.neighborFinset h ∩ (Finset.univ \ (Hub ∪ Iso))).card ≤ 4 ∧
        ¬∃ x y z : Fin 17, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
          G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧
          G.degree x + G.degree y + G.degree z ≤ 10)) :
    ∃ h₁ h₂ : Fin 17, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card := by
  classical
  by_contra hcon
  have key := nogood_of_not_select_seventeen G Hub Iso hcon
  have hmf := strong_deg4_count_le_two_deg5_seventeen G Hub Iso hdisj hshare key
  have hisosum := hub_iso_sum_seventeen G Hub Iso hiso3
  set S : Finset (Fin 17) :=
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
  set T4 : Finset (Fin 17) := Hub.filter (fun h => G.degree h = 4) with hT4def
  set T5 : Finset (Fin 17) := Hub.filter (fun h => ¬ G.degree h = 4) with hT5def
  have hdeg45 : ∀ h ∈ Hub, G.degree h = 4 ∨ G.degree h = 5 := by
    intro h hh; have := hdeg h hh; have := hdeg5 h hh; omega
  have hSsubT4 : S ⊆ T4 := by
    rw [hSdef, hT4def]; intro x hx; rw [Finset.mem_filter] at hx ⊢; exact ⟨hx.1, hx.2.1⟩
  have hSeq : S = T4.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card) := by
    rw [hSdef, hT4def, Finset.filter_filter]
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
    deg4_sum_le_seventeen G Hub Iso hmf
  rcases htight with ⟨h8, h7, h33⟩ | ⟨h9, h6, h36, h3, hisodeg, hNI, hT⟩
  · -- **Profile (8, 7, 33).**
    have hn4 : T4.card = 7 := by omega
    have hn5 : T5.card = 1 := by omega
    have hT4iso16 : ∑ v ∈ T4, (G.neighborFinset v ∩ Iso).card = 16 := by
      rw [h7] at hisosum; omega
    have hT5iso5 : ∑ v ∈ T5, (G.neighborFinset v ∩ Iso).card = 5 := by
      rw [h7] at hisosum; omega
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
    have h3eq : T4.filter (fun h => 3 ≤ (G.neighborFinset h ∩ Iso).card)
        = Hub.filter (fun h => G.degree h = 4 ∧ 3 ≤ (G.neighborFinset h ∩ Iso).card) := by
      rw [hT4def, Finset.filter_filter]
    have h4eq : T4.filter (fun h => 4 ≤ (G.neighborFinset h ∩ Iso).card)
        = Hub.filter (fun h => G.degree h = 4 ∧ 4 ≤ (G.neighborFinset h ∩ Iso).card) := by
      rw [hT4def, Finset.filter_filter]
    have hc1 : (T4.filter (fun h => 1 ≤ (G.neighborFinset h ∩ Iso).card)).card ≤ T4.card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    have hc2 : (T4.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)).card ≤ T4.card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    have hScard : S.card = 7 := by
      rw [hSeq]; rw [h3eq, h4eq] at hcong; omega
    have hSeqT4 : S = T4 := Finset.eq_of_subset_of_card_le hSsubT4 (by rw [hScard, hn4])
    have hSiso16 : ∑ v ∈ S, (G.neighborFinset v ∩ Iso).card = 16 := by rw [hSeqT4]; exact hT4iso16
    have hEbound : ∑ a ∈ S, (G.neighborFinset a ∩ S).card ≤ 12 := by
      have hpt : ∀ a ∈ S, (G.neighborFinset a ∩ S).card + (G.neighborFinset a ∩ Iso).card ≤ 4 := by
        intro a ha
        have hda : G.degree a = 4 := by
          rw [hSdef, Finset.mem_filter] at ha; exact ha.2.1
        have hsub : (G.neighborFinset a ∩ S).card ≤ (G.neighborFinset a ∩ Hub).card :=
          Finset.card_le_card (Finset.inter_subset_inter (Finset.Subset.refl _)
            (hSsubT4.trans (Finset.filter_subset _ _)))
        have hnb := hub_neighbor_le_seventeen G Hub Iso hdisj a hda
        omega
      have hsum : ∑ a ∈ S, ((G.neighborFinset a ∩ S).card + (G.neighborFinset a ∩ Iso).card)
          ≤ ∑ _a ∈ S, 4 := Finset.sum_le_sum hpt
      rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_comm, hScard, hSiso16] at hsum
      omega
    have hQ : ∑ t ∈ Iso, ((G.neighborFinset t ∩ S).card * (G.neighborFinset t ∩ S).card
        - (G.neighborFinset t ∩ S).card) = 22 := by
      have hpt : ∀ t ∈ Iso, ((G.neighborFinset t ∩ S).card * (G.neighborFinset t ∩ S).card
          - (G.neighborFinset t ∩ S).card) + 4 * (G.neighborFinset t ∩ T5).card = 6 := by
        intro t ht
        have e1 : G.neighborFinset t ∩ T4
            = (G.neighborFinset t ∩ Hub).filter (fun h => G.degree h = 4) := by
          rw [hT4def]; ext x
          simp only [Finset.mem_inter, Finset.mem_filter]; tauto
        have e2 : G.neighborFinset t ∩ T5
            = (G.neighborFinset t ∩ Hub).filter (fun h => ¬ G.degree h = 4) := by
          rw [hT5def]; ext x
          simp only [Finset.mem_inter, Finset.mem_filter]; tauto
        have hpart : (G.neighborFinset t ∩ T4).card + (G.neighborFinset t ∩ T5).card
            = (G.neighborFinset t ∩ Hub).card := by
          rw [e1, e2]; exact Finset.card_filter_add_card_filter_not (fun h => G.degree h = 4)
        rw [hiso3 t ht] at hpart
        have hm1 : (G.neighborFinset t ∩ T5).card ≤ 1 := by
          calc (G.neighborFinset t ∩ T5).card ≤ T5.card :=
                Finset.card_le_card Finset.inter_subset_right
            _ = 1 := hn5
        have hk : (G.neighborFinset t ∩ S).card = (G.neighborFinset t ∩ T4).card := by rw [hSeqT4]
        have hkval : (G.neighborFinset t ∩ S).card = 3 - (G.neighborFinset t ∩ T5).card := by
          rw [hk]; omega
        have hm01 : (G.neighborFinset t ∩ T5).card = 0 ∨ (G.neighborFinset t ∩ T5).card = 1 := by
          omega
        rcases hm01 with hm | hm <;> rw [hkval, hm]
      have hsum : ∑ t ∈ Iso, (((G.neighborFinset t ∩ S).card * (G.neighborFinset t ∩ S).card
          - (G.neighborFinset t ∩ S).card) + 4 * (G.neighborFinset t ∩ T5).card)
          = ∑ _t ∈ Iso, 6 := Finset.sum_congr rfl hpt
      rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_comm, h7] at hsum
      have hcross : ∑ t ∈ Iso, (G.neighborFinset t ∩ T5).card
          = ∑ v ∈ T5, (G.neighborFinset v ∩ Iso).card := cross_count G Iso T5
      rw [← Finset.mul_sum, hcross, hT5iso5] at hsum
      omega
    have h49 : S.card * S.card = 49 := by rw [hScard]
    omega
  · -- **Profile (9, 6, 36).**  All nine hubs have degree `4`.  Closed (modulo one documented
    -- residual `sorry`) by `two_hub_select_eM1_96_tight`, which threads the `M`-edge incidence
    -- bound `hNI` bundled into this profile's disjunct.
    exact hcon (two_hub_select_eM1_96_tight G Hub Iso hdeg hdeg5 hiso3 hdisj hshare h3 hisodeg hT
      h9 h6 h36 hNI)

/-- **Hub-pair selection for the `n = 17` two-hub `e(M) ≤ 1` residual.**  Given a hub set of
degree-`{4,5}` vertices, every `M`-isolated twin meeting exactly three hubs (`hiso3`), the twins
`M`-independent (`_hisoIndep`), the sharp good-`C₄` share bound (`hshare`, share `≤ 1`), and one of
the six `e(M) ≤ 1` regimes (`hregime`), there exist two non-adjacent degree-`4` hubs each retaining
`≥ 2` private `M`-isolated twins.  The four `e(M) = 0` / non-tight profiles close by the unified
threshold/clique arithmetic (`3·|Iso| > 29 − |Hub|`); the two tight `e(M) = 1` profiles `(8,7,33)`,
`(9,6,36)` are routed through `two_hub_select_eM1_tight_seventeen`. -/
theorem two_hub_corner_select_seventeen (G : SimpleGraph (Fin 17)) (Hub Iso : Finset (Fin 17))
    (hdeg : ∀ h ∈ Hub, 4 ≤ G.degree h)
    (hdeg5 : ∀ h ∈ Hub, G.degree h ≤ 5)
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (_hisoIndep : ∀ a ∈ Iso, ∀ b ∈ Iso, ¬G.Adj a b)
    (hshare : ∀ h₁ ∈ Hub, ∀ h₂ ∈ Hub, h₁ ≠ h₂ → ¬G.Adj h₁ h₂ →
      (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hdisj : Disjoint Hub Iso)
    (hregime :
      (Hub.card = 7 ∧ Iso.card = 10 ∧ ∑ w ∈ Hub, G.degree w = 30) ∨
      (Hub.card = 7 ∧ Iso.card = 8 ∧ ∑ w ∈ Hub, G.degree w = 30) ∨
      (Hub.card = 8 ∧ Iso.card = 9 ∧ ∑ w ∈ Hub, G.degree w = 33) ∨
      (Hub.card = 8 ∧ Iso.card = 7 ∧ ∑ w ∈ Hub, G.degree w = 33) ∨
      (Hub.card = 9 ∧ Iso.card = 8 ∧ ∑ w ∈ Hub, G.degree w = 36) ∨
      (Hub.card = 9 ∧ Iso.card = 6 ∧ ∑ w ∈ Hub, G.degree w = 36 ∧
        (∀ v : Fin 17, 3 ≤ G.degree v) ∧ (∀ t ∈ Iso, G.degree t = 3) ∧
        ∑ h ∈ Hub, (G.neighborFinset h ∩ (Finset.univ \ (Hub ∪ Iso))).card ≤ 4 ∧
        ¬∃ x y z : Fin 17, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
          G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧
          G.degree x + G.degree y + G.degree z ≤ 10)) :
    ∃ h₁ h₂ : Fin 17, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card := by
  classical
  have hsharer : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1 :=
    fun h₁ m1 _ h₂ m2 _ hne hnadj => hshare h₁ m1 h₂ m2 hne hnadj
  have hiso_le : ∀ a : Fin 17, (G.neighborFinset a ∩ Iso).card ≤ G.degree a := by
    intro a
    rw [← G.card_neighborFinset_eq_degree]; exact Finset.card_le_card Finset.inter_subset_left
  set F : Finset (Fin 17) :=
    Hub.filter (fun h => G.degree h = 4 ∧ (G.neighborFinset h ∩ Iso).card = 4) with hFdef
  by_cases hk : 2 ≤ F.card
  · obtain ⟨h₁, hh1F, h₂, hh2F, hne⟩ := Finset.one_lt_card.mp hk
    obtain ⟨hh1, hd1, h1iso4⟩ := Finset.mem_filter.mp hh1F
    obtain ⟨hh2, hd2, h2iso4⟩ := Finset.mem_filter.mp hh2F
    have hsub : ∀ h : Fin 17, G.degree h = 4 → (G.neighborFinset h ∩ Iso).card = 4 →
        G.neighborFinset h ⊆ Iso := by
      intro h hdh hh4
      have hdc : (G.neighborFinset h).card = 4 := by rw [G.card_neighborFinset_eq_degree, hdh]
      have heq : G.neighborFinset h ∩ Iso = G.neighborFinset h :=
        Finset.eq_of_subset_of_card_le Finset.inter_subset_left (le_of_eq (by rw [hdc, hh4]))
      rw [← heq]; exact Finset.inter_subset_right
    have h1sub : G.neighborFinset h₁ ⊆ Iso := hsub h₁ hd1 h1iso4
    have hnadj : ¬G.Adj h₁ h₂ := by
      intro hadj
      exact Finset.disjoint_left.mp hdisj hh2 (h1sub ((G.mem_neighborFinset h₁ h₂).mpr hadj))
    have hsh : (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1 :=
      hshare h₁ hh1 h₂ hh2 hne hnadj
    have hsh' : (G.neighborFinset h₂ ∩ G.neighborFinset h₁ ∩ Iso).card ≤ 1 :=
      hshare h₂ hh2 h₁ hh1 (Ne.symm hne) (fun h => hnadj h.symm)
    have hfin := select_finish_seventeen G Iso h₁ h₂ (by omega) (by omega)
    exact ⟨h₁, h₂, hh1, hh2, hd1, hd2, hne, hnadj, hfin.1, hfin.2⟩
  · have hdeg45 : ∀ h ∈ Hub, G.degree h = 4 ∨ G.degree h = 5 := by
      intro h hh; have := hdeg h hh; have := hdeg5 h hh; omega
    rcases hregime with hr | hr | hr | hr | hr | hr
    · obtain ⟨hHub, hIso, hdsum⟩ := hr
      by_contra hcon
      exact absurd (residual_arith G Hub Iso hdisj hsharer hiso3 hdeg45 hcon) (by
        rw [hHub, hIso, hdsum]; omega)
    · obtain ⟨hHub, hIso, hdsum⟩ := hr
      by_contra hcon
      exact absurd (residual_arith G Hub Iso hdisj hsharer hiso3 hdeg45 hcon) (by
        rw [hHub, hIso, hdsum]; omega)
    · obtain ⟨hHub, hIso, hdsum⟩ := hr
      by_contra hcon
      exact absurd (residual_arith G Hub Iso hdisj hsharer hiso3 hdeg45 hcon) (by
        rw [hHub, hIso, hdsum]; omega)
    · obtain ⟨hHub, hIso, hdsum⟩ := hr
      exact two_hub_select_eM1_tight_seventeen G Hub Iso hdeg hdeg5 hiso3 hdisj hsharer
        (Or.inl ⟨hHub, hIso, hdsum⟩)
    · obtain ⟨hHub, hIso, hdsum⟩ := hr
      by_contra hcon
      exact absurd (residual_arith G Hub Iso hdisj hsharer hiso3 hdeg45 hcon) (by
        rw [hHub, hIso, hdsum]; omega)
    · obtain ⟨hHub, hIso, hdsum, h3, hisodeg, hNI, hT⟩ := hr
      exact two_hub_select_eM1_tight_seventeen G Hub Iso hdeg hdeg5 hiso3 hdisj hsharer
        (Or.inr ⟨hHub, hIso, hdsum, h3, hisodeg, hNI, hT⟩)

end N17

end ACMax
