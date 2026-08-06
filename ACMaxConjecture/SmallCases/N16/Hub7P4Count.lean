import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N16.Core
import ACMaxConjecture.SmallCases.Certificates
import ACMaxConjecture.SmallCases.N16.Dense

/-!
# `n = 16`, `|D| = 9`, `|Hub| = 7`, `e(M) = 3` `P₄` cherry-avoider existence count

This file closes the cherry-avoiding-hub *existence* (`hwin`) for the genuinely new `P₄` corner of
the `e(M) = 3` dominating-edge branch (`L₁–c₁–c₂–L₂` with both endpoints in-`M`-degree `2`,
`|D| = 9`, `|Hub| = 7`).

The argument is the hub-internal `P/Q/R` count of the `|D| = 10` sibling, sharpened for `|D| = 9`.
With `|D| = 9` we have `|Dᶜ| = 7` and `∑_{Dᶜ} deg = 29`, so *every* hub has degree `≤ 5` (a
degree-`6` hub would force `∑ ≥ 30`).  Writing `P`/`Q` for the degree-`≤ 5` hubs avoiding the
cherry `L₁–c₁–c₂` / `c₁–c₂–L₂` and `R = P ∪ Q`, the assumption that every cherry-avoiding hub
carries `≤ 1` `M`-isolated twin gives, per hub, the indicator bound `[P] + [Q] + [R] ≤ |N ∩ Dᶜ|`
(a cherry-avoiding hub with `≤ 1` twin has all but `≤ 1` of its `D`-neighbours hub-internal).
Summing, `|P| + |Q| + |R| ≤ ∑_{Dᶜ}|N ∩ Dᶜ| = 62 − 6·9 = 8`.  But the non-`P` hubs lie in
`{deg ≥ 6} ∪ N(L₁) ∪ N(c₁) ∪ N(c₂)`, whose `Dᶜ`-trace has size `≤ 0 + 2 + 1 + 1 = 4`, so
`|P| ≥ 7 − 4 = 3`; symmetrically `|Q| ≥ 3`; and `|R| ≥ |P| ≥ 3`.  Thus `|P| + |Q| + |R| ≥ 9 > 8`,
a contradiction, which produces the desired cherry-avoiding degree-`≤ 5` hub with `≥ 2` twins.
-/

namespace ACMax

open scoped Classical

namespace N16

/-- **`P₄` cherry-avoiding degree-`≤ 5` hub with two `M`-isolated twins (`n = 16`, `|D| = 9`).**
For the `e(M) = 3` dominating-edge `P₄` corner `L₁–c₁–c₂–L₂` (both endpoints in-`M`-degree `2`,
`|D| = 9`, hence `|Hub| = 7`), there is a degree-`≤ 5` hub `g ∈ Dᶜ` that avoids one of the two
`P₄` cherries `{L₁, c₁, c₂}` / `{c₁, c₂, L₂}` and carries `≥ 2` `M`-isolated twins.  Proved by the
hub-internal `P/Q/R` count: `|P| + |Q| + |R| ≤ ∑_{Dᶜ}|N ∩ Dᶜ| = 8` contradicts `|P|, |Q|, |R| ≥ 3`. -/
theorem p4_hub4_cherry_avoider_sixteen (G : SimpleGraph (Fin 16))
    (hm : G.edgeFinset.card = 28) (h3 : ∀ v : Fin 16, 3 ≤ G.degree v)
    (L₁ c₁ c₂ L₂ : Fin 16) (D Iso : Finset (Fin 16))
    (hmemD : ∀ v : Fin 16, v ∈ D ↔ G.degree v = 3)
    (hisochar : ∀ w : Fin 16, w ∈ D → w ≠ L₁ → w ≠ c₁ → w ≠ c₂ → w ≠ L₂ → w ∈ Iso)
    (hL1deg : G.degree L₁ = 3) (hL2deg : G.degree L₂ = 3)
    (hac1L1 : G.Adj c₁ L₁) (hac2L2 : G.Adj c₂ L₂) (hc1D : c₁ ∈ D) (hc2D : c₂ ∈ D)
    (hin1 : (G.neighborFinset c₁ ∩ D).card = 2)
    (hin2 : (G.neighborFinset c₂ ∩ D).card = 2)
    (hs6 : ∑ v ∈ D, (G.neighborFinset v ∩ D).card = 6)
    (hD9 : D.card = 9) :
    ∃ g : Fin 16, g ∈ Dᶜ ∧ G.degree g ≤ 5 ∧
      ((¬G.Adj g L₁ ∧ ¬G.Adj g c₁ ∧ ¬G.Adj g c₂) ∨
        (¬G.Adj g c₁ ∧ ¬G.Adj g c₂ ∧ ¬G.Adj g L₂)) ∧
      2 ≤ (G.neighborFinset g ∩ Iso).card := by
  classical
  have hdegD : ∀ v : Fin 16, v ∈ D → G.degree v = 3 := fun v hv => (hmemD v).mp hv
  have hsum56 : ∑ v : Fin 16, G.degree v = 56 := by
    rw [SimpleGraph.sum_degrees_eq_twice_card_edges, hm]
  have hsumDt : ∑ v ∈ D, G.degree v = 3 * D.card := by
    rw [Finset.sum_congr rfl (fun v hv => hdegD v hv), Finset.sum_const, smul_eq_mul, mul_comm]
  have hcc : D.card + Dᶜ.card = 16 := by
    have h := Finset.card_add_card_compl D; simp only [Fintype.card_fin] at h; exact h
  have hsumsplit : ∑ v ∈ D, G.degree v + ∑ v ∈ Dᶜ, G.degree v = 56 := by
    rw [Finset.sum_add_sum_compl]; exact hsum56
  have hDcdeg : ∀ w ∈ Dᶜ, 4 ≤ G.degree w := by
    intro w hw; rw [Finset.mem_compl, hmemD] at hw; have := h3 w; omega
  have hsumDcdeg : ∑ w ∈ Dᶜ, G.degree w = 56 - 3 * D.card := by
    rw [hsumDt] at hsumsplit; omega
  have hDc7 : Dᶜ.card = 7 := by omega
  have hsum29 : ∑ w ∈ Dᶜ, G.degree w = 29 := by rw [hsumDcdeg, hD9]
  have hdegsplit : ∀ v : Fin 16,
      (G.neighborFinset v ∩ D).card + (G.neighborFinset v ∩ Dᶜ).card = G.degree v := by
    intro v
    have hdisj : Disjoint (G.neighborFinset v ∩ D) (G.neighborFinset v ∩ Dᶜ) := by
      apply Finset.disjoint_left.mpr
      intro a ha ha'
      rw [Finset.mem_inter] at ha ha'
      exact (Finset.mem_compl.mp ha'.2) ha.2
    have hun : (G.neighborFinset v ∩ D) ∪ (G.neighborFinset v ∩ Dᶜ) = G.neighborFinset v := by
      rw [← Finset.inter_union_distrib_left, Finset.union_compl, Finset.inter_univ]
    rw [← Finset.card_union_of_disjoint hdisj, hun, G.card_neighborFinset_eq_degree]
  have hcross : ∑ v ∈ D, (G.neighborFinset v ∩ Dᶜ).card
      = ∑ w ∈ Dᶜ, (G.neighborFinset w ∩ D).card := cross_count G D Dᶜ
  have hsumD_NHub : ∑ v ∈ D, (G.neighborFinset v ∩ Dᶜ).card = 3 * D.card - 6 := by
    have hcong : ∑ v ∈ D,
        ((G.neighborFinset v ∩ D).card + (G.neighborFinset v ∩ Dᶜ).card) = ∑ v ∈ D, G.degree v :=
      Finset.sum_congr rfl (fun v _ => hdegsplit v)
    rw [Finset.sum_add_distrib, hs6, hsumDt] at hcong
    omega
  have hSumHubInt : ∑ w ∈ Dᶜ, (G.neighborFinset w ∩ Dᶜ).card = 62 - 6 * D.card := by
    have hcong : ∑ w ∈ Dᶜ,
        ((G.neighborFinset w ∩ D).card + (G.neighborFinset w ∩ Dᶜ).card) = ∑ w ∈ Dᶜ, G.degree w :=
      Finset.sum_congr rfl (fun w _ => hdegsplit w)
    rw [Finset.sum_add_distrib, ← hcross, hsumD_NHub, hsumDcdeg] at hcong
    omega
  -- Every hub has degree `≤ 5`: a degree-`6` hub forces `∑_{Dᶜ} deg ≥ 6 + 4·6 = 30 > 29`.
  have hub5 : ∀ w ∈ Dᶜ, G.degree w ≤ 5 := by
    intro w hw
    by_contra hw6
    have hw6' : 6 ≤ G.degree w := by omega
    have hspl := Finset.add_sum_erase Dᶜ (fun v => G.degree v) hw
    have hrest : 4 * (Dᶜ.erase w).card ≤ ∑ v ∈ Dᶜ.erase w, G.degree v := by
      have hb : ∀ i ∈ Dᶜ.erase w, 4 ≤ G.degree i :=
        fun i hi => hDcdeg i (Finset.mem_of_mem_erase hi)
      have := Finset.card_nsmul_le_sum (Dᶜ.erase w) (fun v => G.degree v) 4 hb
      simpa [smul_eq_mul, mul_comm] using this
    have hec : (Dᶜ.erase w).card = Dᶜ.card - 1 := Finset.card_erase_of_mem hw
    rw [hsum29] at hspl
    omega
  have hfilter6 : (Dᶜ.filter (fun w => 6 ≤ G.degree w)).card = 0 := by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro w hw; have := hub5 w hw; omega
  have hcc1 : (G.neighborFinset c₁ ∩ Dᶜ).card = 1 := by
    have := hdegsplit c₁; rw [hdegD c₁ hc1D, hin1] at this; omega
  have hcc2 : (G.neighborFinset c₂ ∩ Dᶜ).card = 1 := by
    have := hdegsplit c₂; rw [hdegD c₂ hc2D, hin2] at this; omega
  have hcL1 : (G.neighborFinset L₁ ∩ Dᶜ).card ≤ 2 := by
    have hp := hdegsplit L₁
    have hpos : 1 ≤ (G.neighborFinset L₁ ∩ D).card := Finset.card_pos.mpr
      ⟨c₁, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hac1L1.symm, hc1D⟩⟩
    rw [hL1deg] at hp; omega
  have hcL2 : (G.neighborFinset L₂ ∩ Dᶜ).card ≤ 2 := by
    have hp := hdegsplit L₂
    have hpos : 1 ≤ (G.neighborFinset L₂ ∩ D).card := Finset.card_pos.mpr
      ⟨c₂, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hac2L2.symm, hc2D⟩⟩
    rw [hL2deg] at hp; omega
  -- Cherry-avoiding degree-`≤ 5` hubs with `≤ 1` twin have many hub-internal neighbours.
  have hint3 : ∀ g : Fin 16, g ∈ Dᶜ →
      (G.neighborFinset g ∩ D ⊆ G.neighborFinset g ∩ Iso) →
      (G.neighborFinset g ∩ Iso).card ≤ 1 → 3 ≤ (G.neighborFinset g ∩ Dᶜ).card := by
    intro g hg hsub htw
    have hc := le_trans (Finset.card_le_card hsub) htw
    have hds := hdegsplit g
    have hdg := hDcdeg g hg
    omega
  have hint2 : ∀ (g a : Fin 16), g ∈ Dᶜ →
      (G.neighborFinset g ∩ D ⊆ insert a (G.neighborFinset g ∩ Iso)) →
      (G.neighborFinset g ∩ Iso).card ≤ 1 → 2 ≤ (G.neighborFinset g ∩ Dᶜ).card := by
    intro g a hg hsub htw
    have hc := Finset.card_le_card hsub
    have hc2 := Finset.card_insert_le a (G.neighborFinset g ∩ Iso)
    have hds := hdegsplit g
    have hdg := hDcdeg g hg
    omega
  have hwin : ∃ g : Fin 16, g ∈ Dᶜ ∧ G.degree g ≤ 5 ∧
      ((¬G.Adj g L₁ ∧ ¬G.Adj g c₁ ∧ ¬G.Adj g c₂) ∨
        (¬G.Adj g c₁ ∧ ¬G.Adj g c₂ ∧ ¬G.Adj g L₂)) ∧
      2 ≤ (G.neighborFinset g ∩ Iso).card := by
    by_contra hcon
    have htwle : ∀ g : Fin 16, g ∈ Dᶜ → G.degree g ≤ 5 →
        ((¬G.Adj g L₁ ∧ ¬G.Adj g c₁ ∧ ¬G.Adj g c₂) ∨
          (¬G.Adj g c₁ ∧ ¬G.Adj g c₂ ∧ ¬G.Adj g L₂)) →
        (G.neighborFinset g ∩ Iso).card ≤ 1 := by
      intro g hg hg5 hav
      by_contra hcard
      exact hcon ⟨g, hg, hg5, hav, by omega⟩
    have hsub1 : ∀ g : Fin 16, ¬G.Adj g L₁ → ¬G.Adj g c₁ → ¬G.Adj g c₂ →
        G.neighborFinset g ∩ D ⊆ insert L₂ (G.neighborFinset g ∩ Iso) := by
      intro g hgL1 hgc1 hgc2 w hw
      rw [Finset.mem_inter, G.mem_neighborFinset] at hw
      obtain ⟨hgw, hwD⟩ := hw
      by_cases hwL2 : w = L₂
      · rw [hwL2]; exact Finset.mem_insert_self _ _
      · have hwL1 : w ≠ L₁ := fun e => hgL1 (e ▸ hgw)
        have hwc1 : w ≠ c₁ := fun e => hgc1 (e ▸ hgw)
        have hwc2 : w ≠ c₂ := fun e => hgc2 (e ▸ hgw)
        exact Finset.mem_insert_of_mem (Finset.mem_inter.mpr
          ⟨(G.mem_neighborFinset _ _).mpr hgw, hisochar w hwD hwL1 hwc1 hwc2 hwL2⟩)
    have hsub1' : ∀ g : Fin 16, ¬G.Adj g c₁ → ¬G.Adj g c₂ → ¬G.Adj g L₂ →
        G.neighborFinset g ∩ D ⊆ insert L₁ (G.neighborFinset g ∩ Iso) := by
      intro g hgc1 hgc2 hgL2 w hw
      rw [Finset.mem_inter, G.mem_neighborFinset] at hw
      obtain ⟨hgw, hwD⟩ := hw
      by_cases hwL1 : w = L₁
      · rw [hwL1]; exact Finset.mem_insert_self _ _
      · have hwc1 : w ≠ c₁ := fun e => hgc1 (e ▸ hgw)
        have hwc2 : w ≠ c₂ := fun e => hgc2 (e ▸ hgw)
        have hwL2 : w ≠ L₂ := fun e => hgL2 (e ▸ hgw)
        exact Finset.mem_insert_of_mem (Finset.mem_inter.mpr
          ⟨(G.mem_neighborFinset _ _).mpr hgw, hisochar w hwD hwL1 hwc1 hwc2 hwL2⟩)
    have hsub2 : ∀ g : Fin 16, ¬G.Adj g L₁ → ¬G.Adj g c₁ → ¬G.Adj g c₂ → ¬G.Adj g L₂ →
        G.neighborFinset g ∩ D ⊆ G.neighborFinset g ∩ Iso := by
      intro g hgL1 hgc1 hgc2 hgL2 w hw
      rw [Finset.mem_inter, G.mem_neighborFinset] at hw
      obtain ⟨hgw, hwD⟩ := hw
      have hwL1 : w ≠ L₁ := fun e => hgL1 (e ▸ hgw)
      have hwc1 : w ≠ c₁ := fun e => hgc1 (e ▸ hgw)
      have hwc2 : w ≠ c₂ := fun e => hgc2 (e ▸ hgw)
      have hwL2 : w ≠ L₂ := fun e => hgL2 (e ▸ hgw)
      exact Finset.mem_inter.mpr
        ⟨(G.mem_neighborFinset _ _).mpr hgw, hisochar w hwD hwL1 hwc1 hwc2 hwL2⟩
    set P : Finset (Fin 16) := Dᶜ.filter
      (fun g => G.degree g ≤ 5 ∧ ¬G.Adj g L₁ ∧ ¬G.Adj g c₁ ∧ ¬G.Adj g c₂) with hPdef
    set Q : Finset (Fin 16) := Dᶜ.filter
      (fun g => G.degree g ≤ 5 ∧ ¬G.Adj g c₁ ∧ ¬G.Adj g c₂ ∧ ¬G.Adj g L₂) with hQdef
    set R : Finset (Fin 16) := P ∪ Q with hRdef
    have hpt : ∀ g ∈ Dᶜ,
        (if (G.degree g ≤ 5 ∧ ¬G.Adj g L₁ ∧ ¬G.Adj g c₁ ∧ ¬G.Adj g c₂) then (1 : ℕ) else 0)
          + (if (G.degree g ≤ 5 ∧ ¬G.Adj g c₁ ∧ ¬G.Adj g c₂ ∧ ¬G.Adj g L₂) then (1 : ℕ) else 0)
          + (if ((G.degree g ≤ 5 ∧ ¬G.Adj g L₁ ∧ ¬G.Adj g c₁ ∧ ¬G.Adj g c₂) ∨
                (G.degree g ≤ 5 ∧ ¬G.Adj g c₁ ∧ ¬G.Adj g c₂ ∧ ¬G.Adj g L₂)) then (1 : ℕ) else 0)
          ≤ (G.neighborFinset g ∩ Dᶜ).card := by
      intro g hg
      by_cases ha1 : (G.degree g ≤ 5 ∧ ¬G.Adj g L₁ ∧ ¬G.Adj g c₁ ∧ ¬G.Adj g c₂) <;>
        by_cases ha2 : (G.degree g ≤ 5 ∧ ¬G.Adj g c₁ ∧ ¬G.Adj g c₂ ∧ ¬G.Adj g L₂)
      · rw [if_pos ha1, if_pos ha2, if_pos (Or.inl ha1)]
        obtain ⟨hg5, hgL1, hgc1, hgc2⟩ := ha1
        obtain ⟨_, _, _, hgL2⟩ := ha2
        have hi3 := hint3 g hg (hsub2 g hgL1 hgc1 hgc2 hgL2)
          (htwle g hg hg5 (Or.inl ⟨hgL1, hgc1, hgc2⟩))
        omega
      · rw [if_pos ha1, if_neg ha2, if_pos (Or.inl ha1)]
        obtain ⟨hg5, hgL1, hgc1, hgc2⟩ := ha1
        have hi2 := hint2 g L₂ hg (hsub1 g hgL1 hgc1 hgc2)
          (htwle g hg hg5 (Or.inl ⟨hgL1, hgc1, hgc2⟩))
        omega
      · rw [if_neg ha1, if_pos ha2, if_pos (Or.inr ha2)]
        obtain ⟨hg5, hgc1, hgc2, hgL2⟩ := ha2
        have hi2 := hint2 g L₁ hg (hsub1' g hgc1 hgc2 hgL2)
          (htwle g hg hg5 (Or.inr ⟨hgc1, hgc2, hgL2⟩))
        omega
      · rw [if_neg ha1, if_neg ha2, if_neg (not_or.mpr ⟨ha1, ha2⟩)]
        omega
    have hP6 : P.card = ∑ g ∈ Dᶜ,
        (if (G.degree g ≤ 5 ∧ ¬G.Adj g L₁ ∧ ¬G.Adj g c₁ ∧ ¬G.Adj g c₂) then (1 : ℕ) else 0) := by
      rw [hPdef, Finset.card_filter]
    have hQ6 : Q.card = ∑ g ∈ Dᶜ,
        (if (G.degree g ≤ 5 ∧ ¬G.Adj g c₁ ∧ ¬G.Adj g c₂ ∧ ¬G.Adj g L₂) then (1 : ℕ) else 0) := by
      rw [hQdef, Finset.card_filter]
    have hR6 : R.card = ∑ g ∈ Dᶜ,
        (if ((G.degree g ≤ 5 ∧ ¬G.Adj g L₁ ∧ ¬G.Adj g c₁ ∧ ¬G.Adj g c₂) ∨
              (G.degree g ≤ 5 ∧ ¬G.Adj g c₁ ∧ ¬G.Adj g c₂ ∧ ¬G.Adj g L₂)) then (1 : ℕ) else 0) := by
      rw [hRdef, ← Finset.filter_or, Finset.card_filter]
    have hPQR6 : P.card + Q.card + R.card ≤ 62 - 6 * D.card := by
      rw [hP6, hQ6, hR6, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      calc ∑ g ∈ Dᶜ, _ ≤ ∑ g ∈ Dᶜ, (G.neighborFinset g ∩ Dᶜ).card := Finset.sum_le_sum hpt
        _ = 62 - 6 * D.card := hSumHubInt
    have hPcard : 3 ≤ P.card := by
      have hsubP : Dᶜ \ P ⊆ (Dᶜ.filter (fun w => 6 ≤ G.degree w))
          ∪ (G.neighborFinset L₁ ∩ Dᶜ) ∪ (G.neighborFinset c₁ ∩ Dᶜ)
          ∪ (G.neighborFinset c₂ ∩ Dᶜ) := by
        intro g hg
        obtain ⟨hgDc, hgnP⟩ := Finset.mem_sdiff.mp hg
        rw [hPdef] at hgnP
        have hnav : ¬(G.degree g ≤ 5 ∧ ¬G.Adj g L₁ ∧ ¬G.Adj g c₁ ∧ ¬G.Adj g c₂) :=
          fun hpred => hgnP (Finset.mem_filter.mpr ⟨hgDc, hpred⟩)
        by_cases hg6 : 6 ≤ G.degree g
        · exact Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hgDc, hg6⟩)))
        · have hg5 : G.degree g ≤ 5 := by omega
          have hor : G.Adj g L₁ ∨ G.Adj g c₁ ∨ G.Adj g c₂ := by
            by_contra hc; push Not at hc; exact hnav ⟨hg5, hc.1, hc.2.1, hc.2.2⟩
          rcases hor with h | h | h
          · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _
              (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr h.symm, hgDc⟩)))
          · exact Finset.mem_union_left _ (Finset.mem_union_right _
              (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr h.symm, hgDc⟩))
          · exact Finset.mem_union_right _
              (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr h.symm, hgDc⟩)
      have hubcard : (Dᶜ \ P).card ≤ 4 := by
        refine le_trans (Finset.card_le_card hsubP) ?_
        refine le_trans (Finset.card_union_le _ _) ?_
        have h1 := Finset.card_union_le ((Dᶜ.filter (fun w => 6 ≤ G.degree w))
          ∪ (G.neighborFinset L₁ ∩ Dᶜ)) (G.neighborFinset c₁ ∩ Dᶜ)
        have h2 := Finset.card_union_le (Dᶜ.filter (fun w => 6 ≤ G.degree w))
          (G.neighborFinset L₁ ∩ Dᶜ)
        omega
      have hle := Finset.card_le_card_sdiff_add_card (s := Dᶜ) (t := P)
      omega
    have hQcard : 3 ≤ Q.card := by
      have hsubQ : Dᶜ \ Q ⊆ (Dᶜ.filter (fun w => 6 ≤ G.degree w))
          ∪ (G.neighborFinset c₁ ∩ Dᶜ) ∪ (G.neighborFinset c₂ ∩ Dᶜ)
          ∪ (G.neighborFinset L₂ ∩ Dᶜ) := by
        intro g hg
        obtain ⟨hgDc, hgnQ⟩ := Finset.mem_sdiff.mp hg
        rw [hQdef] at hgnQ
        have hnav : ¬(G.degree g ≤ 5 ∧ ¬G.Adj g c₁ ∧ ¬G.Adj g c₂ ∧ ¬G.Adj g L₂) :=
          fun hpred => hgnQ (Finset.mem_filter.mpr ⟨hgDc, hpred⟩)
        by_cases hg6 : 6 ≤ G.degree g
        · exact Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hgDc, hg6⟩)))
        · have hg5 : G.degree g ≤ 5 := by omega
          have hor : G.Adj g c₁ ∨ G.Adj g c₂ ∨ G.Adj g L₂ := by
            by_contra hc; push Not at hc; exact hnav ⟨hg5, hc.1, hc.2.1, hc.2.2⟩
          rcases hor with h | h | h
          · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _
              (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr h.symm, hgDc⟩)))
          · exact Finset.mem_union_left _ (Finset.mem_union_right _
              (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr h.symm, hgDc⟩))
          · exact Finset.mem_union_right _
              (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr h.symm, hgDc⟩)
      have hubcard : (Dᶜ \ Q).card ≤ 4 := by
        refine le_trans (Finset.card_le_card hsubQ) ?_
        refine le_trans (Finset.card_union_le _ _) ?_
        have h1 := Finset.card_union_le ((Dᶜ.filter (fun w => 6 ≤ G.degree w))
          ∪ (G.neighborFinset c₁ ∩ Dᶜ)) (G.neighborFinset c₂ ∩ Dᶜ)
        have h2 := Finset.card_union_le (Dᶜ.filter (fun w => 6 ≤ G.degree w))
          (G.neighborFinset c₁ ∩ Dᶜ)
        omega
      have hle := Finset.card_le_card_sdiff_add_card (s := Dᶜ) (t := Q)
      omega
    have hPleR : P.card ≤ R.card :=
      Finset.card_le_card (by rw [hRdef]; exact Finset.subset_union_left)
    omega
  exact hwin

end N16

end ACMax
