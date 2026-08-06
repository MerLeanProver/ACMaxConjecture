import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N17.Core
import ACMaxConjecture.SmallCases.Certificates
import ACMaxConjecture.SmallCases.N17.HubTriangleStruct
import ACMaxConjecture.SmallCases.N17.Align8Helpers

/-!
# The distinct-twin `TwoHubConfig` assembly for the `n = 17` cherry `|A| = 4` `C₄` corner

This file closes the single remaining `sorry` in `exists_hub_triangle_config_cherry_residual_seventeen`
(`TwinCert17HubTriangleCherry`): the `|A| = 4` distinct-twin branch, where the four cherry-avoiders
form an induced `C₄` (each with internal degree `3` and one private `M`-isolated twin) and the five
non-avoider hubs are pairwise non-adjacent.  The five non-avoiders carry `11` of the `15` isolated-twin
incidences; a double-count of shared twins (`∑ over hub-pairs share = 7`, each `≤ 1` by the good-`C₄`
bound) forces two non-adjacent degree-`4` hubs each with `≥ 2` *private* isolated twins, i.e. a
`TwoHubConfig`.
-/

namespace ACMax

open scoped Classical

namespace N17

/-- **Cherry shared-twin double count.**  For any hub set `S` and twin set `Iso`, the double sum of
pairwise shared twins equals the sum over twins of the square of the twin's `S`-degree. -/
theorem cherry_double_count (G : SimpleGraph (Fin 17)) (S Iso : Finset (Fin 17)) :
    ∑ h ∈ S, ∑ h' ∈ S, (G.neighborFinset h ∩ G.neighborFinset h' ∩ Iso).card
      = ∑ t ∈ Iso, (G.neighborFinset t ∩ S).card * (G.neighborFinset t ∩ S).card := by
  classical
  have hcard : ∀ h h' : Fin 17,
      (G.neighborFinset h ∩ G.neighborFinset h' ∩ Iso).card
        = ∑ t ∈ Iso, (if G.Adj h t ∧ G.Adj h' t then 1 else 0) := by
    intro h h'
    rw [Finset.inter_comm, ← Finset.filter_mem_eq_inter, Finset.card_filter]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    by_cases hh : G.Adj h t ∧ G.Adj h' t
    · simp only [Finset.mem_inter, G.mem_neighborFinset, hh.1, hh.2, and_self, if_pos]
    · rw [if_neg, if_neg hh]
      rw [Finset.mem_inter, G.mem_neighborFinset, G.mem_neighborFinset]
      exact hh
  have hSdeg : ∀ t : Fin 17, (G.neighborFinset t ∩ S).card
      = ∑ h ∈ S, (if G.Adj h t then 1 else 0) := by
    intro t
    rw [Finset.inter_comm, ← Finset.filter_mem_eq_inter, Finset.card_filter]
    exact Finset.sum_congr rfl (fun h _ => by simp only [G.mem_neighborFinset, SimpleGraph.adj_comm])
  simp_rw [hcard]
  have key : ∀ h ∈ S,
      (∑ h' ∈ S, ∑ t ∈ Iso, (if G.Adj h t ∧ G.Adj h' t then 1 else 0))
        = ∑ t ∈ Iso, ∑ h' ∈ S, (if G.Adj h t ∧ G.Adj h' t then 1 else 0) :=
    fun h _ => Finset.sum_comm
  rw [Finset.sum_congr rfl key, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [hSdeg, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl (fun h _ => ?_)
  refine Finset.sum_congr rfl (fun h' _ => ?_)
  by_cases h1 : G.Adj h t <;> by_cases h2 : G.Adj h' t <;> simp [h1, h2]

/-- **Distinct-twin `TwoHubConfig` assembly.**  The `|A| = 4` `C₄` corner with four pairwise-disjoint
private twins: the five non-avoider hubs (`Dᶜ \ A`, pairwise non-adjacent, `hindep`) carry `11` of the
`15` twin incidences; either two of them have iso-degree `≥ 3` (so the good-`C₄` share bound leaves
`≥ 2` private twins each), or all five have iso-degree `≥ 2` and a shared-twin double count
(`∑ pair-shares = 7 < 10`) yields a non-sharing pair — both routes assemble a `TwoHubConfig`. -/
theorem cherry_C4_distinct_twin_twoHub (G : SimpleGraph (Fin 17))
    (D Iso : Finset (Fin 17)) (A : Finset (Fin 17))
    (hIsodef : Iso = D.filter (fun v => (G.neighborFinset v ∩ D).card = 0))
    (hIsoprop : ∀ v ∈ Iso, G.degree v = 3 ∧ (∀ w : Fin 17, G.Adj v w → G.degree w ≠ 3))
    (hIsoD : Iso ⊆ D)
    (hdeg4 : ∀ w : Fin 17, w ∈ Dᶜ → G.degree w = 4)
    (hC4 : ¬∃ a b c d : Fin 17, ({a, b, c, d} : Finset (Fin 17)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (hAsub : A ⊆ Dᶜ) (hcard4 : A.card = 4)
    (hiso1 : ∀ g ∈ A, (G.neighborFinset g ∩ Iso).card = 1)
    (hdist : ∀ g₁ ∈ A, ∀ g₂ ∈ A, g₁ ≠ g₂ →
      Disjoint (G.neighborFinset g₁ ∩ Iso) (G.neighborFinset g₂ ∩ Iso))
    (hindep : ∀ p ∈ Dᶜ \ A, ∀ q ∈ Dᶜ \ A, ¬G.Adj p q)
    (hIso5 : Iso.card = 5) (hDc9 : Dᶜ.card = 9)
    (hisoSumDc : ∑ g ∈ Dᶜ, (G.neighborFinset g ∩ Iso).card = 15)
    (hisole3 : ∀ h ∈ Dᶜ \ A, (G.neighborFinset h ∩ Iso).card ≤ 3) :
    TwoHubConfig G := by
  classical
  set nonA : Finset (Fin 17) := Dᶜ \ A with hnonAdef
  have hnonAsub : nonA ⊆ Dᶜ := by rw [hnonAdef]; exact Finset.sdiff_subset
  have hnonAcard : nonA.card = 5 := by
    have h := Finset.card_sdiff_add_card_inter Dᶜ A
    rw [Finset.inter_eq_right.mpr hAsub, hDc9, hcard4] at h
    rw [hnonAdef]; omega
  -- Twin incidences carried by the five non-avoider hubs.
  have hAiso : ∑ g ∈ A, (G.neighborFinset g ∩ Iso).card = 4 := by
    rw [Finset.sum_congr rfl hiso1, Finset.sum_const, hcard4, smul_eq_mul, Nat.mul_one]
  have hnonAiso11 : ∑ h ∈ nonA, (G.neighborFinset h ∩ Iso).card = 11 := by
    have hs := Finset.sum_sdiff (f := fun g => (G.neighborFinset g ∩ Iso).card) hAsub
    rw [hnonAdef]; rw [hAiso, hisoSumDc] at hs; omega
  -- Sharp `sdiff` bound: private twins of `p` against `q`.
  have hsd : ∀ p q : Fin 17, (G.neighborFinset p ∩ Iso).card
      - (G.neighborFinset p ∩ G.neighborFinset q ∩ Iso).card
      ≤ ((G.neighborFinset p ∩ Iso) \ G.neighborFinset q).card := by
    intro p q
    have heq : (G.neighborFinset p ∩ Iso) ∩ G.neighborFinset q
        = G.neighborFinset p ∩ G.neighborFinset q ∩ Iso := by
      ext w; simp only [Finset.mem_inter]; tauto
    have h2 := Finset.card_sdiff_add_card_inter (G.neighborFinset p ∩ Iso) (G.neighborFinset q)
    rw [heq] at h2; omega
  -- The good-`C₄` share bound on non-avoider hub pairs.
  have hshare1 : ∀ p ∈ nonA, ∀ q ∈ nonA, p ≠ q →
      (G.neighborFinset p ∩ G.neighborFinset q ∩ Iso).card ≤ 1 := by
    intro p hp q hq hpq
    exact nonadj_hubs_share_le_one_iso G D Iso hC4 hIsoD hIsoprop hdeg4 p q
      (hnonAsub hp) (hnonAsub hq) hpq (hindep p hp q hq)
  set R : Finset (Fin 17) := nonA.filter (fun h => 3 ≤ (G.neighborFinset h ∩ Iso).card) with hRdef
  -- The combinatorial extraction of a good non-adjacent hub pair.
  have hpair : ∃ h₁ ∈ nonA, ∃ h₂ ∈ nonA, h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card := by
    by_cases hRcase : 2 ≤ R.card
    · -- Two iso-degree-`≥ 3` hubs.
      obtain ⟨h₁, hh1R, h₂, hh2R, hne⟩ := Finset.one_lt_card.mp hRcase
      have hh1n : h₁ ∈ nonA := Finset.mem_of_mem_filter _ hh1R
      have hh2n : h₂ ∈ nonA := Finset.mem_of_mem_filter _ hh2R
      have hi1 : 3 ≤ (G.neighborFinset h₁ ∩ Iso).card := (Finset.mem_filter.mp hh1R).2
      have hi2 : 3 ≤ (G.neighborFinset h₂ ∩ Iso).card := (Finset.mem_filter.mp hh2R).2
      have hs12 := hshare1 h₁ hh1n h₂ hh2n hne
      have hs21 := hshare1 h₂ hh2n h₁ hh1n (Ne.symm hne)
      refine ⟨h₁, hh1n, h₂, hh2n, hne, hindep h₁ hh1n h₂ hh2n, ?_, ?_⟩
      · have := hsd h₁ h₂; omega
      · have := hsd h₂ h₁; omega
    · -- All five hubs have iso-degree `≥ 2`.
      have hall2 : ∀ h ∈ nonA, 2 ≤ (G.neighborFinset h ∩ Iso).card := by
        by_contra hcon
        push Not at hcon
        obtain ⟨h0, hh0, hlt⟩ := hcon
        have hsplit := Finset.sum_filter_add_sum_filter_not nonA
          (fun h => 3 ≤ (G.neighborFinset h ∩ Iso).card) (fun h => (G.neighborFinset h ∩ Iso).card)
        rw [← hRdef] at hsplit
        set NR : Finset (Fin 17) :=
          nonA.filter (fun h => ¬3 ≤ (G.neighborFinset h ∩ Iso).card) with hNRdef
        rw [hnonAiso11] at hsplit
        have hRsum : ∑ h ∈ R, (G.neighborFinset h ∩ Iso).card ≤ 3 * R.card := by
          calc ∑ h ∈ R, (G.neighborFinset h ∩ Iso).card ≤ ∑ _h ∈ R, 3 :=
                Finset.sum_le_sum (fun h hh => hisole3 h (Finset.mem_of_mem_filter _ hh))
            _ = 3 * R.card := by rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
        have hh0NR : h0 ∈ NR := Finset.mem_filter.mpr ⟨hh0, by omega⟩
        have hNRpos : 1 ≤ NR.card := Finset.card_pos.mpr ⟨h0, hh0NR⟩
        have hNRsum : ∑ h ∈ NR, (G.neighborFinset h ∩ Iso).card ≤ 1 + 2 * (NR.card - 1) := by
          rw [← Finset.add_sum_erase NR _ hh0NR]
          have hbound : ∑ h ∈ NR.erase h0, (G.neighborFinset h ∩ Iso).card
              ≤ 2 * (NR.erase h0).card := by
            calc ∑ h ∈ NR.erase h0, (G.neighborFinset h ∩ Iso).card ≤ ∑ _h ∈ NR.erase h0, 2 :=
                  Finset.sum_le_sum (fun h hh => by
                    have := (Finset.mem_filter.mp (Finset.mem_of_mem_erase hh)).2; omega)
              _ = 2 * (NR.erase h0).card := by rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
          rw [Finset.card_erase_of_mem hh0NR] at hbound
          omega
        have hcardRNR : R.card + NR.card = nonA.card :=
          Finset.card_filter_add_card_filter_not _
        rw [hnonAcard] at hcardRNR
        omega
      -- Shared-twin double count over the five non-avoider hubs.
      have hdnval : ∀ t ∈ Iso,
          (G.neighborFinset t ∩ nonA).card = 2 ∨ (G.neighborFinset t ∩ nonA).card = 3 := by
        intro t ht
        have h3 := (iso_three_hub_nbrs G D Iso hIsodef hIsoprop t ht).2
        have hle1 : (G.neighborFinset t ∩ A).card ≤ 1 := by
          rw [Finset.card_le_one]
          intro g1 hg1 g2 hg2
          by_contra hne
          rw [Finset.mem_inter, G.mem_neighborFinset] at hg1 hg2
          exact Finset.disjoint_left.mp (hdist g1 hg1.2 g2 hg2.2 hne)
            (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hg1.1.symm, ht⟩)
            (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hg2.1.symm, ht⟩)
        have hpart : (G.neighborFinset t ∩ A).card + (G.neighborFinset t ∩ nonA).card
            = (G.neighborFinset t ∩ Dᶜ).card := by
          rw [hnonAdef, ← Finset.card_union_of_disjoint, ← Finset.inter_union_distrib_left,
            Finset.union_sdiff_of_subset hAsub]
          apply Finset.disjoint_left.mpr
          intro w hw hw'
          rw [Finset.mem_inter] at hw hw'
          exact (Finset.mem_sdiff.mp hw'.2).2 hw.2
        omega
      have hdnsq : ∑ t ∈ Iso,
          (G.neighborFinset t ∩ nonA).card * (G.neighborFinset t ∩ nonA).card = 25 := by
        have hcross : ∑ t ∈ Iso, (G.neighborFinset t ∩ nonA).card = 11 := by
          rw [cross_count G Iso nonA]; exact hnonAiso11
        have hper : ∀ t ∈ Iso,
            (G.neighborFinset t ∩ nonA).card * (G.neighborFinset t ∩ nonA).card + 6
              = 5 * (G.neighborFinset t ∩ nonA).card := by
          intro t ht; rcases hdnval t ht with h | h <;> rw [h]
        have hsumeq : ∑ t ∈ Iso,
            ((G.neighborFinset t ∩ nonA).card * (G.neighborFinset t ∩ nonA).card + 6)
              = ∑ t ∈ Iso, 5 * (G.neighborFinset t ∩ nonA).card := Finset.sum_congr rfl hper
        rw [Finset.sum_add_distrib, Finset.sum_const, hIso5, smul_eq_mul, ← Finset.mul_sum,
          hcross] at hsumeq
        omega
      have hdiag : ∑ h ∈ nonA, (G.neighborFinset h ∩ G.neighborFinset h ∩ Iso).card = 11 := by
        rw [Finset.sum_congr rfl (fun h _ => by rw [Finset.inter_self])]; exact hnonAiso11
      have hbig : ∑ h ∈ nonA, ∑ h' ∈ nonA,
          (G.neighborFinset h ∩ G.neighborFinset h' ∩ Iso).card = 25 := by
        rw [cherry_double_count G nonA Iso, hdnsq]
      have hex : ∃ p ∈ nonA, ∃ q ∈ nonA, p ≠ q ∧
          (G.neighborFinset p ∩ G.neighborFinset q ∩ Iso).card = 0 := by
        by_contra hcon
        push Not at hcon
        have hge1 : ∀ p ∈ nonA, ∀ q ∈ nonA, p ≠ q →
            1 ≤ (G.neighborFinset p ∩ G.neighborFinset q ∩ Iso).card := by
          intro p hp q hq hpq; have := hcon p hp q hq hpq; omega
        have hrow : ∀ h ∈ nonA, (G.neighborFinset h ∩ G.neighborFinset h ∩ Iso).card + 4
            ≤ ∑ h' ∈ nonA, (G.neighborFinset h ∩ G.neighborFinset h' ∩ Iso).card := by
          intro h hh
          rw [← Finset.add_sum_erase nonA _ hh]
          have h4 : 4 ≤ ∑ h' ∈ nonA.erase h,
              (G.neighborFinset h ∩ G.neighborFinset h' ∩ Iso).card := by
            calc (4 : ℕ) = ∑ _h' ∈ nonA.erase h, 1 := by
                    rw [Finset.sum_const, Finset.card_erase_of_mem hh, hnonAcard, smul_eq_mul,
                      Nat.mul_one]
              _ ≤ _ := Finset.sum_le_sum (fun h' hh' => hge1 h hh h' (Finset.mem_of_mem_erase hh')
                    (Finset.ne_of_mem_erase hh').symm)
          omega
        have hlow : 31 ≤ ∑ h ∈ nonA, ∑ h' ∈ nonA,
            (G.neighborFinset h ∩ G.neighborFinset h' ∩ Iso).card := by
          calc (31 : ℕ) = ∑ h ∈ nonA,
                  ((G.neighborFinset h ∩ G.neighborFinset h ∩ Iso).card + 4) := by
                rw [Finset.sum_add_distrib, Finset.sum_const, hnonAcard, hdiag, smul_eq_mul]
            _ ≤ _ := Finset.sum_le_sum hrow
        omega
      obtain ⟨p, hp, q, hq, hpq, hs0⟩ := hex
      have hcomm : (G.neighborFinset q ∩ G.neighborFinset p ∩ Iso).card = 0 := by
        rw [show G.neighborFinset q ∩ G.neighborFinset p
          = G.neighborFinset p ∩ G.neighborFinset q from Finset.inter_comm _ _]
        exact hs0
      refine ⟨p, hp, q, hq, hpq, hindep p hp q hq, ?_, ?_⟩
      · have := hsd p q; have := hall2 p hp; omega
      · have := hsd q p; have := hall2 q hq; omega
  -- Common extraction of the `TwoHubConfig` from the good hub pair.
  obtain ⟨h₁, hh1n, h₂, hh2n, hne, hnadj, hp1, hp2⟩ := hpair
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hp1
  obtain ⟨c, hc, d, hd, hcd⟩ := Finset.one_lt_card.mp hp2
  have getmem : ∀ w u v : Fin 17, w ∈ (G.neighborFinset u ∩ Iso) \ G.neighborFinset v →
      G.Adj u w ∧ w ∈ Iso ∧ ¬G.Adj v w := by
    intro w u v hw
    rw [Finset.mem_sdiff, Finset.mem_inter, G.mem_neighborFinset] at hw
    exact ⟨hw.1.1, hw.1.2, fun hadj => hw.2 ((G.mem_neighborFinset _ _).mpr hadj)⟩
  obtain ⟨ha1, haI, ha2⟩ := getmem a h₁ h₂ ha
  obtain ⟨hb1, hbI, hb2⟩ := getmem b h₁ h₂ hb
  obtain ⟨hc1, hcI, hc2⟩ := getmem c h₂ h₁ hc
  obtain ⟨hd1, hdI, hd2⟩ := getmem d h₂ h₁ hd
  have hdh1 : G.degree h₁ = 4 := hdeg4 h₁ (hnonAsub hh1n)
  have hdh2 : G.degree h₂ = 4 := hdeg4 h₂ (hnonAsub hh2n)
  refine dense_two_hub_assemble G h₁ h₂ a b c d hdh1 hdh2 (hIsoprop a haI).1 (hIsoprop b hbI).1
    (hIsoprop c hcI).1 (hIsoprop d hdI).1 ha1.symm hb1.symm hc1.symm hd1.symm hnadj
    hc2 hd2 (fun hadj => ha2 hadj.symm) (fun hadj => hb2 hadj.symm)
    (hIsoprop a haI).2 (hIsoprop b hbI).2 hab hcd

end N17

end ACMax
