import ACMaxConjecture.Base
import ACMaxConjecture.Spectral.AlgConn
import ACMaxConjecture.Cuts.SignedCut
import ACMaxConjecture.SmallCases.N13.Struct
import ACMaxConjecture.SmallCases.N13.Core
import ACMaxConjecture.SmallCases.N13.Align

/-!
# Two-hub opposite-twin signed-cut certificate for `n = 13` (`e(M) = 2` regime)

In the `n = 13` residual the case `e(M) = 2` is special: the degree-3 subgraph `M` is a single
induced `P₃`, every hub touches it, and the alignment used for `e(M) ≥ 3` fails.  In this regime
the degree sequence is forced to be `[4⁵, 3⁸]` (handshake: `e(M) = 2 ⇒ |D| = 8`, `|Hub| = 5`,
`e_H = 0`, every hub has degree exactly `4`), the hubs are pairwise non-adjacent, and there are
`≥ 5` `M`-isolated degree-3 twins.

We pick two hubs `h₁ ≠ h₂` and four `M`-isolated twins `a, b` (adjacent to `h₁` but not `h₂`),
`c, d` (adjacent to `h₂` but not `h₁`), all six distinct, and form the **two-hub opposite-twin
cut** `P = {h₁, a, b}`, `N = {h₂, c, d}`.  The cross term `e(P, N)` vanishes (`h₁ ≁ h₂`; the
twins avoid the opposite hub; twins are `M`-isolated so non-adjacent to one another), and the
boundary counts give
`4·e(P,N) + e(P,Z) + e(N,Z) ≤ 0 + (deg h₁ + 2) + (deg h₂ + 2) = deg h₁ + deg h₂ + 4 = 12`,
so `algConn G ≤ 2`.
-/

namespace ACMax

open scoped Classical

namespace N13

/-- **Two-hub opposite-twin cut assembly (boundary arithmetic, fully proved).**  Given two
distinct degree-4 hubs `h₁, h₂` with `h₁ ≁ h₂`, and four distinct degree-3 `M`-isolated twins
`a, b` adjacent to `h₁` but not `h₂`, and `c, d` adjacent to `h₂` but not `h₁`, with all six
vertices distinct and the twins pairwise non-adjacent to the opposite hub and to one another's
"column", the two-hub cut `P = {h₁, a, b}`, `N = {h₂, c, d}` satisfies
`4·e(P,N) + e(P,Z) + e(N,Z) ≤ 4·|P|`.  The cross term vanishes and the boundary counts give
`0 + (2 + 2 + (deg h₁ − 2)) + (2 + 2 + (deg h₂ − 2)) = deg h₁ + deg h₂ + 4 = 12`. -/
theorem two_hub_opposite_twin_cert (G : SimpleGraph (Fin 13)) (h₁ h₂ a b c d : Fin 13)
    (hdegh₁ : G.degree h₁ = 4) (hdegh₂ : G.degree h₂ = 4)
    (hdega : G.degree a = 3) (hdegb : G.degree b = 3)
    (hdegc : G.degree c = 3) (hdegd : G.degree d = 3)
    (hadj_ah₁ : G.Adj a h₁) (hadj_bh₁ : G.Adj b h₁)
    (hadj_ch₂ : G.Adj c h₂) (hadj_dh₂ : G.Adj d h₂)
    (hn_h₁h₂ : ¬G.Adj h₁ h₂) (hn_h₁c : ¬G.Adj h₁ c) (hn_h₁d : ¬G.Adj h₁ d)
    (hn_ah₂ : ¬G.Adj a h₂) (hn_ac : ¬G.Adj a c) (hn_ad : ¬G.Adj a d)
    (hn_bh₂ : ¬G.Adj b h₂) (hn_bc : ¬G.Adj b c) (hn_bd : ¬G.Adj b d)
    (ne_h₁h₂ : h₁ ≠ h₂)
    (ne_h₁a : h₁ ≠ a) (ne_h₁b : h₁ ≠ b) (ne_h₁c : h₁ ≠ c) (ne_h₁d : h₁ ≠ d)
    (ne_h₂a : h₂ ≠ a) (ne_h₂b : h₂ ≠ b) (ne_h₂c : h₂ ≠ c) (ne_h₂d : h₂ ≠ d)
    (ne_ab : a ≠ b) (ne_ac : a ≠ c) (ne_ad : a ≠ d)
    (ne_bc : b ≠ c) (ne_bd : b ≠ d) (ne_cd : c ≠ d) :
    ∃ P N : Finset (Fin 13), Disjoint P N ∧ P.card = N.card ∧ 0 < P.card ∧
      4 * (∑ p ∈ P, (G.neighborFinset p ∩ N).card)
        + (∑ p ∈ P, (G.neighborFinset p \ (P ∪ N)).card)
        + (∑ q ∈ N, (G.neighborFinset q \ (P ∪ N)).card)
      ≤ 4 * P.card := by
  classical
  have hPcard : ({h₁, a, b} : Finset (Fin 13)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [ne_h₁a, ne_h₁b]),
        Finset.card_insert_of_notMem (by simp [ne_ab]), Finset.card_singleton]
  have hNcard : ({h₂, c, d} : Finset (Fin 13)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [ne_h₂c, ne_h₂d]),
        Finset.card_insert_of_notMem (by simp [ne_cd]), Finset.card_singleton]
  have hdisjPN : Disjoint ({h₁, a, b} : Finset (Fin 13)) ({h₂, c, d} : Finset (Fin 13)) := by
    rw [Finset.disjoint_left]
    intro w hw hw'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw hw'
    rcases hw with rfl | rfl | rfl <;> rcases hw' with rfl | rfl | rfl <;>
      first
      | exact ne_h₁h₂ rfl | exact ne_h₁c rfl | exact ne_h₁d rfl
      | exact ne_h₂a rfl.symm | exact ne_ac rfl | exact ne_ad rfl
      | exact ne_h₂b rfl.symm | exact ne_bc rfl | exact ne_bd rfl
  -- Cross term `e(P, N) = 0`.
  have hPN_h₁ : (G.neighborFinset h₁ ∩ ({h₂, c, d} : Finset (Fin 13))).card = 0 := by
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro w hw
    rw [Finset.mem_inter, G.mem_neighborFinset] at hw
    obtain ⟨hadj, hmem⟩ := hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with rfl | rfl | rfl
    · exact hn_h₁h₂ hadj
    · exact hn_h₁c hadj
    · exact hn_h₁d hadj
  have hPN_a : (G.neighborFinset a ∩ ({h₂, c, d} : Finset (Fin 13))).card = 0 := by
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro w hw
    rw [Finset.mem_inter, G.mem_neighborFinset] at hw
    obtain ⟨hadj, hmem⟩ := hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with rfl | rfl | rfl
    · exact hn_ah₂ hadj
    · exact hn_ac hadj
    · exact hn_ad hadj
  have hPN_b : (G.neighborFinset b ∩ ({h₂, c, d} : Finset (Fin 13))).card = 0 := by
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro w hw
    rw [Finset.mem_inter, G.mem_neighborFinset] at hw
    obtain ⟨hadj, hmem⟩ := hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with rfl | rfl | rfl
    · exact hn_bh₂ hadj
    · exact hn_bc hadj
    · exact hn_bd hadj
  -- Boundary `\` bounds.  `h₁` has two neighbours (`a, b`) inside `P ∪ N`.
  have hh₁_le : (G.neighborFinset h₁ \
      (({h₁, a, b} : Finset (Fin 13)) ∪ {h₂, c, d})).card ≤ 2 := by
    have hsub : ({a, b} : Finset (Fin 13)) ⊆
        G.neighborFinset h₁ ∩ (({h₁, a, b} : Finset (Fin 13)) ∪ {h₂, c, d}) := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rw [Finset.mem_inter, G.mem_neighborFinset]
      rcases hw with rfl | rfl
      · exact ⟨hadj_ah₁.symm, by simp⟩
      · exact ⟨hadj_bh₁.symm, by simp⟩
    have hge : 2 ≤ (G.neighborFinset h₁ ∩
        (({h₁, a, b} : Finset (Fin 13)) ∪ {h₂, c, d})).card := by
      have h2 : ({a, b} : Finset (Fin 13)).card = 2 := by
        rw [Finset.card_insert_of_notMem (by simp [ne_ab]), Finset.card_singleton]
      calc 2 = ({a, b} : Finset (Fin 13)).card := h2.symm
        _ ≤ _ := Finset.card_le_card hsub
    have hsd := Finset.card_sdiff_add_card_inter (G.neighborFinset h₁)
      (({h₁, a, b} : Finset (Fin 13)) ∪ {h₂, c, d})
    rw [G.card_neighborFinset_eq_degree, hdegh₁] at hsd
    omega
  have hh₂_le : (G.neighborFinset h₂ \
      (({h₁, a, b} : Finset (Fin 13)) ∪ {h₂, c, d})).card ≤ 2 := by
    have hsub : ({c, d} : Finset (Fin 13)) ⊆
        G.neighborFinset h₂ ∩ (({h₁, a, b} : Finset (Fin 13)) ∪ {h₂, c, d}) := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rw [Finset.mem_inter, G.mem_neighborFinset]
      rcases hw with rfl | rfl
      · exact ⟨hadj_ch₂.symm, by simp⟩
      · exact ⟨hadj_dh₂.symm, by simp⟩
    have hge : 2 ≤ (G.neighborFinset h₂ ∩
        (({h₁, a, b} : Finset (Fin 13)) ∪ {h₂, c, d})).card := by
      have h2 : ({c, d} : Finset (Fin 13)).card = 2 := by
        rw [Finset.card_insert_of_notMem (by simp [ne_cd]), Finset.card_singleton]
      calc 2 = ({c, d} : Finset (Fin 13)).card := h2.symm
        _ ≤ _ := Finset.card_le_card hsub
    have hsd := Finset.card_sdiff_add_card_inter (G.neighborFinset h₂)
      (({h₁, a, b} : Finset (Fin 13)) ∪ {h₂, c, d})
    rw [G.card_neighborFinset_eq_degree, hdegh₂] at hsd
    omega
  have ha_le : (G.neighborFinset a \
      (({h₁, a, b} : Finset (Fin 13)) ∪ {h₂, c, d})).card ≤ 2 := by
    have hsub : ({h₁} : Finset (Fin 13)) ⊆
        G.neighborFinset a ∩ (({h₁, a, b} : Finset (Fin 13)) ∪ {h₂, c, d}) := by
      intro w hw
      rw [Finset.mem_singleton] at hw; subst hw
      rw [Finset.mem_inter, G.mem_neighborFinset]
      exact ⟨hadj_ah₁, by simp⟩
    have hge : 1 ≤ (G.neighborFinset a ∩
        (({h₁, a, b} : Finset (Fin 13)) ∪ {h₂, c, d})).card := by
      calc 1 = ({h₁} : Finset (Fin 13)).card := (Finset.card_singleton h₁).symm
        _ ≤ _ := Finset.card_le_card hsub
    have hsd := Finset.card_sdiff_add_card_inter (G.neighborFinset a)
      (({h₁, a, b} : Finset (Fin 13)) ∪ {h₂, c, d})
    rw [G.card_neighborFinset_eq_degree, hdega] at hsd
    omega
  have hb_le : (G.neighborFinset b \
      (({h₁, a, b} : Finset (Fin 13)) ∪ {h₂, c, d})).card ≤ 2 := by
    have hsub : ({h₁} : Finset (Fin 13)) ⊆
        G.neighborFinset b ∩ (({h₁, a, b} : Finset (Fin 13)) ∪ {h₂, c, d}) := by
      intro w hw
      rw [Finset.mem_singleton] at hw; subst hw
      rw [Finset.mem_inter, G.mem_neighborFinset]
      exact ⟨hadj_bh₁, by simp⟩
    have hge : 1 ≤ (G.neighborFinset b ∩
        (({h₁, a, b} : Finset (Fin 13)) ∪ {h₂, c, d})).card := by
      calc 1 = ({h₁} : Finset (Fin 13)).card := (Finset.card_singleton h₁).symm
        _ ≤ _ := Finset.card_le_card hsub
    have hsd := Finset.card_sdiff_add_card_inter (G.neighborFinset b)
      (({h₁, a, b} : Finset (Fin 13)) ∪ {h₂, c, d})
    rw [G.card_neighborFinset_eq_degree, hdegb] at hsd
    omega
  have hc_le : (G.neighborFinset c \
      (({h₁, a, b} : Finset (Fin 13)) ∪ {h₂, c, d})).card ≤ 2 := by
    have hsub : ({h₂} : Finset (Fin 13)) ⊆
        G.neighborFinset c ∩ (({h₁, a, b} : Finset (Fin 13)) ∪ {h₂, c, d}) := by
      intro w hw
      rw [Finset.mem_singleton] at hw; subst hw
      rw [Finset.mem_inter, G.mem_neighborFinset]
      exact ⟨hadj_ch₂, by simp⟩
    have hge : 1 ≤ (G.neighborFinset c ∩
        (({h₁, a, b} : Finset (Fin 13)) ∪ {h₂, c, d})).card := by
      calc 1 = ({h₂} : Finset (Fin 13)).card := (Finset.card_singleton h₂).symm
        _ ≤ _ := Finset.card_le_card hsub
    have hsd := Finset.card_sdiff_add_card_inter (G.neighborFinset c)
      (({h₁, a, b} : Finset (Fin 13)) ∪ {h₂, c, d})
    rw [G.card_neighborFinset_eq_degree, hdegc] at hsd
    omega
  have hd_le : (G.neighborFinset d \
      (({h₁, a, b} : Finset (Fin 13)) ∪ {h₂, c, d})).card ≤ 2 := by
    have hsub : ({h₂} : Finset (Fin 13)) ⊆
        G.neighborFinset d ∩ (({h₁, a, b} : Finset (Fin 13)) ∪ {h₂, c, d}) := by
      intro w hw
      rw [Finset.mem_singleton] at hw; subst hw
      rw [Finset.mem_inter, G.mem_neighborFinset]
      exact ⟨hadj_dh₂, by simp⟩
    have hge : 1 ≤ (G.neighborFinset d ∩
        (({h₁, a, b} : Finset (Fin 13)) ∪ {h₂, c, d})).card := by
      calc 1 = ({h₂} : Finset (Fin 13)).card := (Finset.card_singleton h₂).symm
        _ ≤ _ := Finset.card_le_card hsub
    have hsd := Finset.card_sdiff_add_card_inter (G.neighborFinset d)
      (({h₁, a, b} : Finset (Fin 13)) ∪ {h₂, c, d})
    rw [G.card_neighborFinset_eq_degree, hdegd] at hsd
    omega
  refine ⟨({h₁, a, b} : Finset (Fin 13)), ({h₂, c, d} : Finset (Fin 13)), hdisjPN,
    (by rw [hPcard, hNcard]), (by rw [hPcard]; norm_num), ?_⟩
  have e1 : ∑ p ∈ ({h₁, a, b} : Finset (Fin 13)),
      (G.neighborFinset p ∩ ({h₂, c, d} : Finset (Fin 13))).card
      = (G.neighborFinset h₁ ∩ ({h₂, c, d} : Finset (Fin 13))).card
        + (G.neighborFinset a ∩ ({h₂, c, d} : Finset (Fin 13))).card
        + (G.neighborFinset b ∩ ({h₂, c, d} : Finset (Fin 13))).card := by
    rw [Finset.sum_insert (by simp [ne_h₁a, ne_h₁b]),
        Finset.sum_insert (by simp [ne_ab]), Finset.sum_singleton]
    ring
  have e2 : ∑ p ∈ ({h₁, a, b} : Finset (Fin 13)),
      (G.neighborFinset p \ (({h₁, a, b} : Finset (Fin 13)) ∪ {h₂, c, d})).card
      = (G.neighborFinset h₁ \ (({h₁, a, b} : Finset (Fin 13)) ∪ {h₂, c, d})).card
        + (G.neighborFinset a \ (({h₁, a, b} : Finset (Fin 13)) ∪ {h₂, c, d})).card
        + (G.neighborFinset b \ (({h₁, a, b} : Finset (Fin 13)) ∪ {h₂, c, d})).card := by
    rw [Finset.sum_insert (by simp [ne_h₁a, ne_h₁b]),
        Finset.sum_insert (by simp [ne_ab]), Finset.sum_singleton]
    ring
  have e3 : ∑ q ∈ ({h₂, c, d} : Finset (Fin 13)),
      (G.neighborFinset q \ (({h₁, a, b} : Finset (Fin 13)) ∪ {h₂, c, d})).card
      = (G.neighborFinset h₂ \ (({h₁, a, b} : Finset (Fin 13)) ∪ {h₂, c, d})).card
        + (G.neighborFinset c \ (({h₁, a, b} : Finset (Fin 13)) ∪ {h₂, c, d})).card
        + (G.neighborFinset d \ (({h₁, a, b} : Finset (Fin 13)) ∪ {h₂, c, d})).card := by
    rw [Finset.sum_insert (by simp [ne_h₂c, ne_h₂d]),
        Finset.sum_insert (by simp [ne_cd]), Finset.sum_singleton]
    ring
  rw [e1, e2, e3, hPcard, hPN_h₁, hPN_a, hPN_b]
  omega

/-- **`e(M) ≥ 2` in the residual (handshake, fully proved).**  With `22` edges, minimum degree
`3` and `8 ≤ |D|`, the in-`M` incidence sum `∑_{v∈D}|N v ∩ D| = 2·e(M)` is at least `4`.  The
`D→Hub` edge count `∑_{v∈D}|N v \ D| = 3|D| − 2 e(M)` is at most the total hub degree
`∑_{w∉D} deg w = 44 − 3|D|` (cross-count `cross_count_thirteen`), so `2 e(M) ≥ 6|D| − 44 ≥ 4`. -/
theorem eM_ge_four (G : SimpleGraph (Fin 13)) (hm : G.edgeFinset.card = 22)
    (D : Finset (Fin 13))
    (hmemD : ∀ v : Fin 13, v ∈ D ↔ G.degree v = 3) (hD8 : 8 ≤ D.card) :
    4 ≤ ∑ v ∈ D, (G.neighborFinset v ∩ D).card := by
  classical
  have hsum : ∑ v : Fin 13, G.degree v = 44 := by
    rw [SimpleGraph.sum_degrees_eq_twice_card_edges, hm]
  set Dc : Finset (Fin 13) := Dᶜ with hDcdef
  -- `∑_{v∈D} deg v = 3 |D|`.
  have hsumD : ∑ v ∈ D, G.degree v = 3 * D.card := by
    rw [Finset.sum_congr rfl (fun v hv => (hmemD v).mp hv), Finset.sum_const, smul_eq_mul,
      mul_comm]
  -- `∑_{w∈Dᶜ} deg w = 44 − 3 |D|`.
  have hsumDc : ∑ w ∈ Dc, G.degree w = 44 - 3 * D.card := by
    have hpart : ∑ v ∈ D, G.degree v + ∑ w ∈ Dc, G.degree w = 44 := by
      rw [hDcdef, Finset.sum_add_sum_compl D (fun v => G.degree v)]; exact hsum
    omega
  -- Per-vertex split: for `v ∈ D`, `|N v ∩ D| + |N v ∩ Dᶜ| = deg v = 3`.
  have hsplitv : ∀ v ∈ D, (G.neighborFinset v ∩ D).card
      + (G.neighborFinset v ∩ Dc).card = 3 := by
    intro v hv
    have hdeg : (G.neighborFinset v).card = 3 := by
      rw [G.card_neighborFinset_eq_degree, (hmemD v).mp hv]
    have hinterunion : (G.neighborFinset v ∩ D) ∪ (G.neighborFinset v ∩ Dc)
        = G.neighborFinset v := by
      rw [← Finset.inter_union_distrib_left, hDcdef, Finset.union_compl, Finset.inter_univ]
    have hdisj : Disjoint (G.neighborFinset v ∩ D) (G.neighborFinset v ∩ Dc) := by
      rw [hDcdef]
      exact Finset.disjoint_left.mpr (fun a ha hb =>
        (Finset.mem_compl.mp (Finset.mem_inter.mp hb).2) (Finset.mem_inter.mp ha).2)
    have hc := Finset.card_union_of_disjoint hdisj
    rw [hinterunion, hdeg] at hc
    omega
  -- Sum the split over `D`.
  have hSsum : ∑ v ∈ D, (G.neighborFinset v ∩ D).card
      + ∑ v ∈ D, (G.neighborFinset v ∩ Dc).card = 3 * D.card := by
    rw [← Finset.sum_add_distrib, Finset.sum_congr rfl hsplitv, Finset.sum_const, smul_eq_mul,
      mul_comm]
  -- Cross-count: `∑_{v∈D}|N v ∩ Dᶜ| = ∑_{w∈Dᶜ}|N w ∩ D| ≤ ∑_{w∈Dᶜ} deg w`.
  have hcross : ∑ v ∈ D, (G.neighborFinset v ∩ Dc).card
      = ∑ w ∈ Dc, (G.neighborFinset w ∩ D).card := cross_count_thirteen G D Dc
  have hcrossle : ∑ w ∈ Dc, (G.neighborFinset w ∩ D).card ≤ ∑ w ∈ Dc, G.degree w := by
    apply Finset.sum_le_sum
    intro w _
    calc (G.neighborFinset w ∩ D).card ≤ (G.neighborFinset w).card :=
          Finset.card_le_card Finset.inter_subset_left
      _ = G.degree w := G.card_neighborFinset_eq_degree w
  rw [hcross] at hSsum
  omega

/-- **`∑_{v∈D}|N v ∩ D|` is even (handshake on `M = G[D]`).**  This sum is `2·e(M)`, twice the
edge count of the induced degree-3 subgraph. -/
theorem eM_even (G : SimpleGraph (Fin 13)) (D : Finset (Fin 13)) :
    Even (∑ v ∈ D, (G.neighborFinset v ∩ D).card) := by
  classical
  set M : SimpleGraph (Fin 13) :=
    { Adj := fun a b => G.Adj a b ∧ a ∈ D ∧ b ∈ D
      symm := ⟨fun a b h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
      loopless := ⟨fun a h => G.irrefl h.1⟩ } with hMdef
  have hMadj : ∀ a b : Fin 13, M.Adj a b ↔ G.Adj a b ∧ a ∈ D ∧ b ∈ D := fun _ _ => Iff.rfl
  have hMdeg : ∀ v : Fin 13,
      M.degree v = if v ∈ D then (G.neighborFinset v ∩ D).card else 0 := by
    intro v
    have hd : M.degree v = (M.neighborFinset v).card := rfl
    rw [hd]
    by_cases hvD : v ∈ D
    · simp only [hvD, if_true]
      congr 1
      ext w
      rw [SimpleGraph.mem_neighborFinset, hMadj, Finset.mem_inter, G.mem_neighborFinset]
      exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hvD, h.2⟩⟩
    · simp only [hvD, if_false]
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro w hw
      rw [SimpleGraph.mem_neighborFinset, hMadj] at hw
      exact hvD hw.2.1
  have hsumM : ∑ v : Fin 13, M.degree v = ∑ v ∈ D, (G.neighborFinset v ∩ D).card := by
    simp_rw [hMdeg]
    rw [← Finset.sum_filter]
    congr 1
    ext v
    simp
  rw [← hsumM]
  exact ⟨M.edgeFinset.card, by rw [M.sum_degrees_eq_twice_card_edges]; ring⟩

/-- **Forced degree sequence in the `e(M) = 2` regime (handshake, fully proved).**  With `22`
edges, minimum degree `3`, `8 ≤ |D|` and `∑_{v∈D}|N v ∩ D| = 4` (so `e(M) = 2`), the degree
sequence is forced to `[4⁵, 3⁸]`: `|D| = 8`, `|Hub| = 5`, every hub has degree exactly `4`, and
every hub's neighbours all lie in `D` (so the hubs are pairwise non-adjacent). -/
theorem eM2_forced_structure (G : SimpleGraph (Fin 13))
    (hm : G.edgeFinset.card = 22) (h3 : ∀ v : Fin 13, 3 ≤ G.degree v)
    (D Hub : Finset (Fin 13))
    (hmemD : ∀ v : Fin 13, v ∈ D ↔ G.degree v = 3)
    (hmemHub : ∀ v : Fin 13, v ∈ Hub ↔ 4 ≤ G.degree v)
    (hD8 : 8 ≤ D.card)
    (heM2 : ∑ v ∈ D, (G.neighborFinset v ∩ D).card = 4) :
    D.card = 8 ∧ Hub.card = 5 ∧ (∀ w ∈ Hub, G.degree w = 4) ∧
      (∀ w ∈ Hub, G.neighborFinset w ⊆ D) := by
  classical
  have hsum : ∑ v : Fin 13, G.degree v = 44 := by
    rw [SimpleGraph.sum_degrees_eq_twice_card_edges, hm]
  have hDH : ∀ v : Fin 13, v ∈ D ∨ v ∈ Hub := fun v => by
    rcases Nat.lt_or_ge (G.degree v) 4 with h | h
    · exact Or.inl ((hmemD v).mpr (by have := h3 v; omega))
    · exact Or.inr ((hmemHub v).mpr h)
  have hdisj : Disjoint D Hub := by
    rw [Finset.disjoint_left]; intro v hv hv'
    have := (hmemD v).mp hv; have := (hmemHub v).mp hv'; omega
  have hunion : D ∪ Hub = Finset.univ := by
    ext v; simp only [Finset.mem_union, Finset.mem_univ, iff_true]; exact hDH v
  have hcard13 : D.card + Hub.card = 13 := by
    have h := Finset.card_union_of_disjoint hdisj
    rw [hunion, Finset.card_univ, Fintype.card_fin] at h; omega
  have hsumD : ∑ v ∈ D, G.degree v = 3 * D.card := by
    rw [Finset.sum_congr rfl (fun v hv => (hmemD v).mp hv), Finset.sum_const, smul_eq_mul,
      mul_comm]
  have hsumpart : ∑ v ∈ D, G.degree v + ∑ v ∈ Hub, G.degree v = 44 := by
    rw [← Finset.sum_union hdisj, hunion]; exact hsum
  have hsplitD : ∀ v ∈ D, (G.neighborFinset v ∩ D).card + (G.neighborFinset v ∩ Hub).card = 3 := by
    intro v hv
    have hdeg : (G.neighborFinset v).card = 3 := by
      rw [G.card_neighborFinset_eq_degree, (hmemD v).mp hv]
    have hu : (G.neighborFinset v ∩ D) ∪ (G.neighborFinset v ∩ Hub) = G.neighborFinset v := by
      rw [← Finset.inter_union_distrib_left, hunion, Finset.inter_univ]
    have hdj : Disjoint (G.neighborFinset v ∩ D) (G.neighborFinset v ∩ Hub) :=
      Finset.disjoint_left.mpr (fun a ha hb =>
        (Finset.disjoint_left.mp hdisj) (Finset.mem_inter.mp ha).2 (Finset.mem_inter.mp hb).2)
    have hc := Finset.card_union_of_disjoint hdj
    rw [hu, hdeg] at hc; omega
  have hsplitHub : ∀ w ∈ Hub, (G.neighborFinset w ∩ D).card + (G.neighborFinset w ∩ Hub).card
      = G.degree w := by
    intro w hw
    have hdeg : (G.neighborFinset w).card = G.degree w := G.card_neighborFinset_eq_degree w
    have hu : (G.neighborFinset w ∩ D) ∪ (G.neighborFinset w ∩ Hub) = G.neighborFinset w := by
      rw [← Finset.inter_union_distrib_left, hunion, Finset.inter_univ]
    have hdj : Disjoint (G.neighborFinset w ∩ D) (G.neighborFinset w ∩ Hub) :=
      Finset.disjoint_left.mpr (fun a ha hb =>
        (Finset.disjoint_left.mp hdisj) (Finset.mem_inter.mp ha).2 (Finset.mem_inter.mp hb).2)
    have hc := Finset.card_union_of_disjoint hdj
    rw [hu, hdeg] at hc; omega
  have hSsumD : ∑ v ∈ D, (G.neighborFinset v ∩ D).card
      + ∑ v ∈ D, (G.neighborFinset v ∩ Hub).card = 3 * D.card := by
    rw [← Finset.sum_add_distrib, Finset.sum_congr rfl hsplitD, Finset.sum_const, smul_eq_mul,
      mul_comm]
  have hSsumHub : ∑ w ∈ Hub, (G.neighborFinset w ∩ D).card
      + ∑ w ∈ Hub, (G.neighborFinset w ∩ Hub).card = ∑ w ∈ Hub, G.degree w := by
    rw [← Finset.sum_add_distrib, Finset.sum_congr rfl hsplitHub]
  have hcross : ∑ v ∈ D, (G.neighborFinset v ∩ Hub).card
      = ∑ w ∈ Hub, (G.neighborFinset w ∩ D).card := cross_count_thirteen G D Hub
  -- Solve the linear system: `|D| = 8`, `eHsum = 0`, `∑_Hub deg = 20`, `|Hub| = 5`.
  have hHub5 : Hub.card = 5 := by omega
  have hsumHubdeg : ∑ w ∈ Hub, G.degree w = 20 := by omega
  have heHsum0 : ∑ w ∈ Hub, (G.neighborFinset w ∩ Hub).card = 0 := by omega
  have hD8eq : D.card = 8 := by omega
  -- Every hub has degree exactly `4`.
  have hdeg4 : ∀ w ∈ Hub, G.degree w = 4 := by
    intro w hw
    have hge := (hmemHub w).mp hw
    have hiso := Finset.add_sum_erase Hub (fun v => G.degree v) hw
    have herase : 4 * (Hub.erase w).card ≤ ∑ v ∈ Hub.erase w, G.degree v := by
      have hb : ∀ x ∈ Hub.erase w, 4 ≤ G.degree x := fun i hi =>
        (hmemHub i).mp (Finset.mem_of_mem_erase hi)
      have h := Finset.card_nsmul_le_sum (Hub.erase w) (fun v => G.degree v) 4 hb
      simpa [smul_eq_mul, mul_comm] using h
    have hec : (Hub.erase w).card = Hub.card - 1 := Finset.card_erase_of_mem hw
    omega
  -- Every hub's neighbours all lie in `D`.
  have hnbhd : ∀ w ∈ Hub, G.neighborFinset w ⊆ D := by
    intro w hw
    have hzero : (G.neighborFinset w ∩ Hub).card = 0 :=
      Finset.sum_eq_zero_iff.mp heHsum0 w hw
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem] at hzero
    intro u hu
    rcases hDH u with hD | hH
    · exact hD
    · exact absurd (Finset.mem_inter.mpr ⟨hu, hH⟩) (hzero u)
  exact ⟨hD8eq, hHub5, hdeg4, hnbhd⟩

/-- **The `e(M) = 2` subgraph is a single induced `P₃` (structural).**  With `∑_{v∈D}|N v ∩ D|
= 4` (so `e(M) = 2`), triangle-free and `2K₂`-free, the degree-3 subgraph `M = G[D]` is a single
induced path `u – v – w`; in particular every other `D`-vertex is `M`-isolated. -/
theorem eM2_p3 (G : SimpleGraph (Fin 13)) (D : Finset (Fin 13))
    (hmemD : ∀ v : Fin 13, v ∈ D ↔ G.degree v = 3)
    (hT : ¬∃ x y z : Fin 13, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    (h2k2 : ¬∃ a b c d : Fin 13, ({a, b, c, d} : Finset (Fin 13)).card = 4 ∧
      G.degree a = 3 ∧ G.degree b = 3 ∧ G.degree c = 3 ∧ G.degree d = 3 ∧
      G.Adj a b ∧ G.Adj c d ∧ ¬G.Adj a c ∧ ¬G.Adj a d ∧ ¬G.Adj b c ∧ ¬G.Adj b d)
    (heM2 : ∑ v ∈ D, (G.neighborFinset v ∩ D).card = 4) :
    ∃ u v w : Fin 13, u ∈ D ∧ v ∈ D ∧ w ∈ D ∧
      G.Adj u v ∧ G.Adj v w ∧ ¬G.Adj u w ∧ u ≠ v ∧ v ≠ w ∧ u ≠ w ∧
      ∀ x : Fin 13, x ∈ D → x ≠ u → x ≠ v → x ≠ w → (G.neighborFinset x ∩ D).card = 0 := by
  classical
  have hdeg3 : ∀ x : Fin 13, x ∈ D → G.degree x = 3 := fun x hx => (hmemD x).mp hx
  have hindle : ∀ x : Fin 13, x ∈ D → (G.neighborFinset x ∩ D).card ≤ 3 := by
    intro x hx
    calc (G.neighborFinset x ∩ D).card ≤ (G.neighborFinset x).card :=
          Finset.card_le_card Finset.inter_subset_left
      _ = G.degree x := G.card_neighborFinset_eq_degree x
      _ = 3 := hdeg3 x hx
  have hadjD : ∀ a b : Fin 13, b ∈ G.neighborFinset a ∩ D ↔ G.Adj a b ∧ b ∈ D := by
    intro a b; rw [Finset.mem_inter, G.mem_neighborFinset]
  -- Any sub-collection of `D` has in-`M`-incidence at most `4`.
  have hTsum : ∀ T : Finset (Fin 13), T ⊆ D →
      ∑ x ∈ T, (G.neighborFinset x ∩ D).card ≤ 4 := by
    intro T hsub
    calc ∑ x ∈ T, (G.neighborFinset x ∩ D).card
        ≤ ∑ x ∈ D, (G.neighborFinset x ∩ D).card :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)
      _ = 4 := heM2
  -- Positive-incidence vertices have a `D`-neighbour.
  have hpos : ∀ a : Fin 13, a ∈ D → 1 ≤ (G.neighborFinset a ∩ D).card →
      ∃ b : Fin 13, G.Adj a b ∧ b ∈ D := by
    intro a _ ha
    obtain ⟨b, hb⟩ := Finset.card_pos.mp ha
    exact ⟨b, (hadjD a b).mp hb⟩
  by_cases hc2 : ∃ v : Fin 13, v ∈ D ∧ 2 ≤ (G.neighborFinset v ∩ D).card
  · obtain ⟨v, hvD, hv2⟩ := hc2
    -- `card = 2` (a `3` would force incidence `≥ 6`).
    have hv2' : (G.neighborFinset v ∩ D).card = 2 := by
      rcases Nat.lt_or_ge ((G.neighborFinset v ∩ D).card) 3 with h | h
      · omega
      · exfalso
        have hv3 : (G.neighborFinset v ∩ D).card = 3 := le_antisymm (hindle v hvD) h
        obtain ⟨a, b, c, hab, hac, hbc, hset⟩ := Finset.card_eq_three.mp hv3
        have hmem : ∀ t : Fin 13, t ∈ ({a, b, c} : Finset (Fin 13)) → G.Adj v t ∧ t ∈ D := by
          intro t ht; rw [← hset] at ht; exact (hadjD v t).mp ht
        obtain ⟨hva, haD⟩ := hmem a (by simp)
        obtain ⟨hvb, hbD⟩ := hmem b (by simp)
        obtain ⟨hvc, hcD⟩ := hmem c (by simp)
        have hTsub : ({v, a, b, c} : Finset (Fin 13)) ⊆ D := by
          intro t ht; simp only [Finset.mem_insert, Finset.mem_singleton] at ht
          rcases ht with rfl | rfl | rfl | rfl
          exacts [hvD, haD, hbD, hcD]
        have hva1 : 1 ≤ (G.neighborFinset a ∩ D).card :=
          Finset.card_pos.mpr ⟨v, (hadjD a v).mpr ⟨hva.symm, hvD⟩⟩
        have hvb1 : 1 ≤ (G.neighborFinset b ∩ D).card :=
          Finset.card_pos.mpr ⟨v, (hadjD b v).mpr ⟨hvb.symm, hvD⟩⟩
        have hvc1 : 1 ≤ (G.neighborFinset c ∩ D).card :=
          Finset.card_pos.mpr ⟨v, (hadjD c v).mpr ⟨hvc.symm, hvD⟩⟩
        have hne_va : v ≠ a := G.ne_of_adj hva
        have hne_vb : v ≠ b := G.ne_of_adj hvb
        have hne_vc : v ≠ c := G.ne_of_adj hvc
        have hsumT : ∑ x ∈ ({v, a, b, c} : Finset (Fin 13)), (G.neighborFinset x ∩ D).card
            = (G.neighborFinset v ∩ D).card + (G.neighborFinset a ∩ D).card
              + (G.neighborFinset b ∩ D).card + (G.neighborFinset c ∩ D).card := by
          rw [Finset.sum_insert (by simp [hne_va, hne_vb, hne_vc]),
              Finset.sum_insert (by simp [hab, hac]),
              Finset.sum_insert (by simp [hbc]), Finset.sum_singleton]
          ring
        have := hTsum _ hTsub
        rw [hsumT, hv3] at this
        omega
    obtain ⟨u, w, huw, hset⟩ := Finset.card_eq_two.mp hv2'
    have hu : u ∈ G.neighborFinset v ∩ D := by rw [hset]; simp
    have hw : w ∈ G.neighborFinset v ∩ D := by rw [hset]; simp
    obtain ⟨hvu, huD⟩ := (hadjD v u).mp hu
    obtain ⟨hvw, hwD⟩ := (hadjD v w).mp hw
    have adj_uv : G.Adj u v := hvu.symm
    have adj_vw : G.Adj v w := hvw
    have hne_uv : u ≠ v := (G.ne_of_adj hvu).symm
    have hne_vw : v ≠ w := G.ne_of_adj hvw
    have hnuw : ¬G.Adj u w := by
      intro h
      exact hT ⟨u, v, w, hne_uv, hne_vw, huw, adj_uv, adj_vw, h, by
        rw [hdeg3 u huD, hdeg3 v hvD, hdeg3 w hwD]; omega⟩
    -- Every other `D`-vertex is `M`-isolated.
    have hiso : ∀ x : Fin 13, x ∈ D → x ≠ u → x ≠ v → x ≠ w →
        (G.neighborFinset x ∩ D).card = 0 := by
      have hTsub : ({u, v, w} : Finset (Fin 13)) ⊆ D := by
        intro t ht; simp only [Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl | rfl
        exacts [huD, hvD, hwD]
      have hu1 : 1 ≤ (G.neighborFinset u ∩ D).card :=
        Finset.card_pos.mpr ⟨v, (hadjD u v).mpr ⟨adj_uv, hvD⟩⟩
      have hw1 : 1 ≤ (G.neighborFinset w ∩ D).card :=
        Finset.card_pos.mpr ⟨v, (hadjD w v).mpr ⟨adj_vw.symm, hvD⟩⟩
      have hsumT : ∑ x ∈ ({u, v, w} : Finset (Fin 13)), (G.neighborFinset x ∩ D).card
          = (G.neighborFinset u ∩ D).card + (G.neighborFinset v ∩ D).card
            + (G.neighborFinset w ∩ D).card := by
        rw [Finset.sum_insert (by simp [hne_uv, huw]),
            Finset.sum_insert (by simp [hne_vw]), Finset.sum_singleton]
        ring
      have hsplit := Finset.sum_sdiff hTsub (f := fun x => (G.neighborFinset x ∩ D).card)
      have hTval : ∑ x ∈ ({u, v, w} : Finset (Fin 13)), (G.neighborFinset x ∩ D).card = 4 := by
        rw [hsumT, hv2']; omega
      have hsdiff0 : ∑ x ∈ D \ ({u, v, w} : Finset (Fin 13)),
          (G.neighborFinset x ∩ D).card = 0 := by
        rw [hTval] at hsplit; omega
      intro x hxD hxu hxv hxw
      have hxmem : x ∈ D \ ({u, v, w} : Finset (Fin 13)) := by
        rw [Finset.mem_sdiff]
        exact ⟨hxD, by simp [hxu, hxv, hxw]⟩
      exact Finset.sum_eq_zero_iff.mp hsdiff0 x hxmem
    exact ⟨u, v, w, huD, hvD, hwD, adj_uv, adj_vw, hnuw, hne_uv, hne_vw, huw, hiso⟩
  · -- No in-`M`-degree-`≥ 2` vertex: `M` is a matching, but `e(M) = 2` forces a `2K₂`.
    exfalso
    push Not at hc2
    have hle1 : ∀ v : Fin 13, v ∈ D → (G.neighborFinset v ∩ D).card ≤ 1 := by
      intro v hv; have := hc2 v hv; omega
    have hane : ∃ a : Fin 13, a ∈ D ∧ (G.neighborFinset a ∩ D).card ≠ 0 := by
      by_contra hcon
      push Not at hcon
      have : ∑ x ∈ D, (G.neighborFinset x ∩ D).card = 0 :=
        Finset.sum_eq_zero (fun x hx => hcon x hx)
      omega
    obtain ⟨a0, ha0D, ha0ne⟩ := hane
    have ha0_1 : (G.neighborFinset a0 ∩ D).card = 1 := le_antisymm (hle1 a0 ha0D) (by omega)
    obtain ⟨b0, hb0set⟩ := Finset.card_eq_one.mp ha0_1
    have hb0mem : b0 ∈ G.neighborFinset a0 ∩ D := by rw [hb0set]; simp
    obtain ⟨hab0, hb0D⟩ := (hadjD a0 b0).mp hb0mem
    have ha0uniq : ∀ z : Fin 13, G.Adj a0 z → z ∈ D → z = b0 := by
      intro z hz hzD
      have : z ∈ G.neighborFinset a0 ∩ D := (hadjD a0 z).mpr ⟨hz, hzD⟩
      rw [hb0set, Finset.mem_singleton] at this; exact this
    have hb0_1 : (G.neighborFinset b0 ∩ D).card = 1 :=
      le_antisymm (hle1 b0 hb0D)
        (Finset.card_pos.mpr ⟨a0, (hadjD b0 a0).mpr ⟨hab0.symm, ha0D⟩⟩)
    obtain ⟨a0', hb0set'⟩ := Finset.card_eq_one.mp hb0_1
    have ha0mem : a0 ∈ G.neighborFinset b0 ∩ D := (hadjD b0 a0).mpr ⟨hab0.symm, ha0D⟩
    have ha0eq : a0 = a0' := by rw [hb0set', Finset.mem_singleton] at ha0mem; exact ha0mem
    have hb0uniq : ∀ z : Fin 13, G.Adj b0 z → z ∈ D → z = a0 := by
      intro z hz hzD
      have : z ∈ G.neighborFinset b0 ∩ D := (hadjD b0 z).mpr ⟨hz, hzD⟩
      rw [hb0set', Finset.mem_singleton, ← ha0eq] at this; exact this
    have hane2 : ∃ c : Fin 13, c ∈ D \ ({a0, b0} : Finset (Fin 13)) ∧
        (G.neighborFinset c ∩ D).card ≠ 0 := by
      by_contra hcon
      push Not at hcon
      have hT2sub : ({a0, b0} : Finset (Fin 13)) ⊆ D := by
        intro t ht; simp only [Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl; exacts [ha0D, hb0D]
      have hsplit := Finset.sum_sdiff hT2sub (f := fun x => (G.neighborFinset x ∩ D).card)
      have hsd0 : ∑ x ∈ D \ ({a0, b0} : Finset (Fin 13)),
          (G.neighborFinset x ∩ D).card = 0 :=
        Finset.sum_eq_zero (fun x hx => hcon x hx)
      have hpair : ∑ x ∈ ({a0, b0} : Finset (Fin 13)), (G.neighborFinset x ∩ D).card = 2 := by
        rw [Finset.sum_insert (by simp [G.ne_of_adj hab0]), Finset.sum_singleton, ha0_1, hb0_1]
      rw [hsd0, hpair] at hsplit
      omega
    obtain ⟨c, hcmem, hcne⟩ := hane2
    rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton] at hcmem
    obtain ⟨hcD, hcnot⟩ := hcmem
    push Not at hcnot
    obtain ⟨hca0, hcb0⟩ := hcnot
    obtain ⟨d, hcd, hdD⟩ := hpos c hcD (by omega)
    have hdne_a0 : d ≠ a0 := by
      intro e; subst e; exact hcb0 (ha0uniq c hcd.symm hcD)
    have hdne_b0 : d ≠ b0 := by
      intro e; subst e; exact hca0 (hb0uniq c hcd.symm hcD)
    have hdne_c : d ≠ c := (G.ne_of_adj hcd).symm
    -- `a0–b0` and `c–d` form a `2K₂`.
    have hcard4 : ({a0, b0, c, d} : Finset (Fin 13)).card = 4 := by
      rw [Finset.card_insert_of_notMem (by simp [G.ne_of_adj hab0, Ne.symm hca0, Ne.symm hdne_a0]),
          Finset.card_insert_of_notMem (by simp [Ne.symm hcb0, Ne.symm hdne_b0]),
          Finset.card_insert_of_notMem (by simp [hdne_c.symm]), Finset.card_singleton]
    have hn_a0c : ¬G.Adj a0 c := fun h => hcb0 (ha0uniq c h hcD)
    have hn_a0d : ¬G.Adj a0 d := fun h => hdne_b0 (ha0uniq d h hdD)
    have hn_b0c : ¬G.Adj b0 c := fun h => hca0 (hb0uniq c h hcD)
    have hn_b0d : ¬G.Adj b0 d := fun h => hdne_a0 (hb0uniq d h hdD)
    exact h2k2 ⟨a0, b0, c, d, hcard4, hdeg3 a0 ha0D, hdeg3 b0 hb0D, hdeg3 c hcD, hdeg3 d hdD,
      hab0, hcd, hn_a0c, hn_a0d, hn_b0c, hn_b0d⟩

/-- **Pigeonhole for the two-hub opposite-twin cut (double count).**  Given five degree-4 hubs,
each with `≥ 3` neighbours in a set `Iso` of vertices each having exactly three hub-neighbours,
the double count `∑_{h₁,h₂∈Hub}|N h₁ ∩ N h₂ ∩ Iso| = 9|Iso| ≤ 54 < 55` forces two distinct hubs
to share at most one element of `Iso`. -/
theorem exists_hub_pair_low_share (G : SimpleGraph (Fin 13)) (Hub Iso : Finset (Fin 13))
    (hHub5 : Hub.card = 5) (hdeg4 : ∀ h ∈ Hub, G.degree h = 4)
    (hiso3 : ∀ h ∈ Hub, 3 ≤ (G.neighborFinset h ∩ Iso).card)
    (hNtHub3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3) :
    ∃ h₁ h₂ : Fin 13, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧ h₁ ≠ h₂ ∧
      (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1 := by
  classical
  have hSB : ∑ h ∈ Hub, (G.neighborFinset h ∩ Iso).card = 3 * Iso.card := by
    rw [cross_count_thirteen G Hub Iso,
      Finset.sum_congr rfl (fun t ht => hNtHub3 t ht), Finset.sum_const, smul_eq_mul, mul_comm]
  have hSBle : ∑ h ∈ Hub, (G.neighborFinset h ∩ Iso).card ≤ 20 := by
    calc ∑ h ∈ Hub, (G.neighborFinset h ∩ Iso).card
        ≤ ∑ h ∈ Hub, (G.neighborFinset h).card := by
          apply Finset.sum_le_sum
          intro h _; exact Finset.card_le_card Finset.inter_subset_left
      _ = ∑ h ∈ Hub, G.degree h :=
          Finset.sum_congr rfl (fun h _ => G.card_neighborFinset_eq_degree h)
      _ = ∑ h ∈ Hub, 4 := Finset.sum_congr rfl (fun h hh => hdeg4 h hh)
      _ = 20 := by rw [Finset.sum_const, hHub5, smul_eq_mul]
  have hIso6 : Iso.card ≤ 6 := by omega
  have hinner : ∀ h₁ : Fin 13, h₁ ∈ Hub →
      ∑ h₂ ∈ Hub, (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card
        = 3 * (G.neighborFinset h₁ ∩ Iso).card := by
    intro h₁ _
    have hset : ∀ h₂ : Fin 13, G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso
        = G.neighborFinset h₂ ∩ (G.neighborFinset h₁ ∩ Iso) := by
      intro h₂
      rw [Finset.inter_comm (G.neighborFinset h₁) (G.neighborFinset h₂), Finset.inter_assoc]
    rw [Finset.sum_congr rfl (fun h₂ _ => by rw [hset h₂]),
      cross_count_thirteen G Hub (G.neighborFinset h₁ ∩ Iso)]
    rw [Finset.sum_congr rfl (fun t ht => hNtHub3 t (Finset.mem_inter.mp ht).2),
      Finset.sum_const, smul_eq_mul, mul_comm]
  have hSA : ∑ h₁ ∈ Hub, ∑ h₂ ∈ Hub,
      (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card = 9 * Iso.card := by
    rw [Finset.sum_congr rfl hinner, ← Finset.mul_sum, hSB]; ring
  by_contra hcon
  push Not at hcon
  have hge2 : ∀ h₁ ∈ Hub, ∀ h₂ ∈ Hub, h₁ ≠ h₂ →
      2 ≤ (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card := by
    intro h₁ hh₁ h₂ hh₂ hne; have := hcon h₁ h₂ hh₁ hh₂ hne; omega
  have hper : ∀ h₁ ∈ Hub,
      11 ≤ ∑ h₂ ∈ Hub, (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card := by
    intro h₁ hh₁
    have hdiag : 3 ≤ (G.neighborFinset h₁ ∩ G.neighborFinset h₁ ∩ Iso).card := by
      rw [Finset.inter_self]; exact hiso3 h₁ hh₁
    have hisol := Finset.add_sum_erase Hub
      (fun h₂ => (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card) hh₁
    have herasege : 2 * (Hub.erase h₁).card
        ≤ ∑ h₂ ∈ Hub.erase h₁, (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card := by
      have hb : ∀ h₂ ∈ Hub.erase h₁,
          2 ≤ (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card := by
        intro h₂ hh₂
        exact hge2 h₁ hh₁ h₂ (Finset.mem_of_mem_erase hh₂)
          (Ne.symm (Finset.ne_of_mem_erase hh₂))
      have h := Finset.card_nsmul_le_sum (Hub.erase h₁)
        (fun h₂ => (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card) 2 hb
      simpa [smul_eq_mul, mul_comm] using h
    have hec : (Hub.erase h₁).card = 4 := by
      rw [Finset.card_erase_of_mem hh₁, hHub5]
    omega
  have hSAge : 55 ≤ ∑ h₁ ∈ Hub, ∑ h₂ ∈ Hub,
      (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card := by
    calc 55 = ∑ _h₁ ∈ Hub, 11 := by rw [Finset.sum_const, hHub5, smul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum hper
  omega

/-- **Two-hub opposite-twin configuration in the `e(M) = 2` regime (structural).**  In the
forced `[4⁵, 3⁸]` regime there are five pairwise non-adjacent degree-4 hubs, a single induced
`P₃`, and `M`-isolated degree-3 twins each adjacent to exactly three hubs.  A double count
(`∑_{h₁,h₂∈Hub}|N h₁ ∩ N h₂ ∩ Iso| = 9|Iso| ≤ 54 < 55`) produces two hubs `h₁, h₂` sharing at
most one isolated twin; each hub has `≥ 3` isolated-twin neighbours, so `h₁` (resp. `h₂`) has
`≥ 2` isolated twins not adjacent to `h₂` (resp. `h₁`), yielding the opposite-twin
configuration. -/
theorem node_A_config (G : SimpleGraph (Fin 13))
    (hm : G.edgeFinset.card = 22) (h3 : ∀ v : Fin 13, 3 ≤ G.degree v)
    (hT : ¬∃ x y z : Fin 13, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    (h2k2 : ¬∃ a b c d : Fin 13, ({a, b, c, d} : Finset (Fin 13)).card = 4 ∧
      G.degree a = 3 ∧ G.degree b = 3 ∧ G.degree c = 3 ∧ G.degree d = 3 ∧
      G.Adj a b ∧ G.Adj c d ∧ ¬G.Adj a c ∧ ¬G.Adj a d ∧ ¬G.Adj b c ∧ ¬G.Adj b d)
    (hC4 : ¬∃ a b c d : Fin 13, ({a, b, c, d} : Finset (Fin 13)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 13)
    (heM2 : ∑ v ∈ Finset.univ.filter (fun w => G.degree w = 3),
        (G.neighborFinset v ∩ Finset.univ.filter (fun w => G.degree w = 3)).card = 4) :
    ∃ h₁ h₂ a b c d : Fin 13,
        G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧
        G.degree a = 3 ∧ G.degree b = 3 ∧ G.degree c = 3 ∧ G.degree d = 3 ∧
        G.Adj a h₁ ∧ G.Adj b h₁ ∧ G.Adj c h₂ ∧ G.Adj d h₂ ∧
        ¬G.Adj h₁ h₂ ∧ ¬G.Adj h₁ c ∧ ¬G.Adj h₁ d ∧
        ¬G.Adj a h₂ ∧ ¬G.Adj a c ∧ ¬G.Adj a d ∧
        ¬G.Adj b h₂ ∧ ¬G.Adj b c ∧ ¬G.Adj b d ∧
        h₁ ≠ h₂ ∧ h₁ ≠ a ∧ h₁ ≠ b ∧ h₁ ≠ c ∧ h₁ ≠ d ∧
        h₂ ≠ a ∧ h₂ ≠ b ∧ h₂ ≠ c ∧ h₂ ≠ d ∧
        a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
  classical
  set D : Finset (Fin 13) := Finset.univ.filter (fun w => G.degree w = 3) with hDdef
  set Hub : Finset (Fin 13) := Finset.univ.filter (fun v => 4 ≤ G.degree v) with hHubdef
  have hmemD : ∀ v : Fin 13, v ∈ D ↔ G.degree v = 3 := by intro v; rw [hDdef]; simp
  have hmemHub : ∀ v : Fin 13, v ∈ Hub ↔ 4 ≤ G.degree v := by intro v; rw [hHubdef]; simp
  have hsum44 : ∑ v : Fin 13, G.degree v = 44 := by
    rw [SimpleGraph.sum_degrees_eq_twice_card_edges, hm]
  have hDHpart : ∀ x : Fin 13, x ∈ D ∨ x ∈ Hub := fun x => by
    rcases Nat.lt_or_ge (G.degree x) 4 with h | h
    · exact Or.inl ((hmemD x).mpr (by have := h3 x; omega))
    · exact Or.inr ((hmemHub x).mpr h)
  have hdisjDH : Disjoint D Hub := by
    rw [Finset.disjoint_left]; intro x hx hx'
    have := (hmemD x).mp hx; have := (hmemHub x).mp hx'; omega
  have hunionDH : D ∪ Hub = Finset.univ := by
    ext x; simp only [Finset.mem_union, Finset.mem_univ, iff_true]; exact hDHpart x
  have hcard13 : D.card + Hub.card = 13 := by
    have h := Finset.card_union_of_disjoint hdisjDH
    rw [hunionDH, Finset.card_univ, Fintype.card_fin] at h; omega
  have hD8 : 8 ≤ D.card := by
    have hsumDt : ∑ v ∈ D, G.degree v = 3 * D.card := by
      rw [Finset.sum_congr rfl (fun v hv => (hmemD v).mp hv), Finset.sum_const, smul_eq_mul,
        mul_comm]
    have hsumpart : ∑ v ∈ D, G.degree v + ∑ v ∈ Hub, G.degree v = 44 := by
      rw [← Finset.sum_union hdisjDH, hunionDH]; exact hsum44
    have hHubge : 4 * Hub.card ≤ ∑ v ∈ Hub, G.degree v := by
      have hb : ∀ x ∈ Hub, 4 ≤ G.degree x := fun i hi => (hmemHub i).mp hi
      have h := Finset.card_nsmul_le_sum Hub (fun v => G.degree v) 4 hb
      simpa [smul_eq_mul, mul_comm] using h
    omega
  obtain ⟨hDcard, hHub5, hdeg4, hnbhd⟩ :=
    eM2_forced_structure G hm h3 D Hub hmemD hmemHub hD8 heM2
  obtain ⟨u, v, w, huD, hvD, hwD, adj_uv, adj_vw, hnuw, hne_uv, hne_vw, huw, hisoP⟩ :=
    eM2_p3 G D hmemD hT h2k2 heM2
  -- Partition facts.
  have hHubnotD : ∀ x : Fin 13, x ∈ Hub → x ∉ D := by
    intro x hx hxD; have := (hmemHub x).mp hx; have := (hmemD x).mp hxD; omega
  set Iso : Finset (Fin 13) := D.filter (fun x => (G.neighborFinset x ∩ D).card = 0) with hIsodef
  have hIsomem : ∀ x : Fin 13, x ∈ Iso ↔ x ∈ D ∧ (G.neighborFinset x ∩ D).card = 0 := by
    intro x; rw [hIsodef, Finset.mem_filter]
  -- Each isolated twin has all three neighbours in `Hub`.
  have hNtHub3 : ∀ t : Fin 13, t ∈ Iso → (G.neighborFinset t ∩ Hub).card = 3 := by
    intro t ht
    obtain ⟨htD, htiso⟩ := (hIsomem t).mp ht
    have hsub : G.neighborFinset t ⊆ Hub := by
      intro x hx
      rcases hDHpart x with hxD | hxH
      · exfalso
        rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem] at htiso
        exact htiso x (Finset.mem_inter.mpr ⟨hx, hxD⟩)
      · exact hxH
    rw [Finset.inter_eq_left.mpr hsub, G.card_neighborFinset_eq_degree, (hmemD t).mp htD]
  -- Each hub has `≥ 3` isolated-twin neighbours.
  have hiso3 : ∀ h : Fin 13, h ∈ Hub → 3 ≤ (G.neighborFinset h ∩ Iso).card := by
    intro h hh
    have hNhD : G.neighborFinset h ⊆ D := hnbhd h hh
    have hNh4 : (G.neighborFinset h).card = 4 := by
      rw [G.card_neighborFinset_eq_degree, hdeg4 h hh]
    have hpath := hub_meets_path_le_one G hT hC4 (hdeg4 h hh) ((hmemD u).mp huD)
      ((hmemD v).mp hvD) ((hmemD w).mp hwD) adj_uv adj_vw hnuw hne_uv hne_vw huw
    obtain ⟨hp1, hp2, hp3⟩ := hpath
    have hmeet : (G.neighborFinset h ∩ ({u, v, w} : Finset (Fin 13))).card ≤ 1 := by
      by_contra hgt
      push Not at hgt
      obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp hgt
      rw [Finset.mem_inter, G.mem_neighborFinset] at hp hq
      obtain ⟨hpN, hpS⟩ := hp
      obtain ⟨hqN, hqS⟩ := hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hpS hqS
      rcases hpS with rfl | rfl | rfl <;> rcases hqS with rfl | rfl | rfl <;>
        first
        | exact hpq rfl
        | exact hp1 ⟨hpN, hqN⟩ | exact hp1 ⟨hqN, hpN⟩
        | exact hp2 ⟨hpN, hqN⟩ | exact hp2 ⟨hqN, hpN⟩
        | exact hp3 ⟨hpN, hqN⟩ | exact hp3 ⟨hqN, hpN⟩
    have hsub : G.neighborFinset h \ ({u, v, w} : Finset (Fin 13)) ⊆ G.neighborFinset h ∩ Iso := by
      intro x hx
      rw [Finset.mem_sdiff] at hx
      obtain ⟨hxN, hxnot⟩ := hx
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hxnot
      rw [Finset.mem_inter]
      refine ⟨hxN, (hIsomem x).mpr ⟨hNhD hxN,
        hisoP x (hNhD hxN) hxnot.1 hxnot.2.1 hxnot.2.2⟩⟩
    have hsd := Finset.card_sdiff_add_card_inter (G.neighborFinset h)
      (({u, v, w} : Finset (Fin 13)))
    have hle := Finset.card_le_card hsub
    rw [hNh4] at hsd
    omega
  obtain ⟨h₁, h₂, hh₁, hh₂, hne12, hshare⟩ :=
    exists_hub_pair_low_share G Hub Iso hHub5 hdeg4 hiso3 hNtHub3
  -- Extract two isolated twins on each side.
  set A : Finset (Fin 13) := (G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂ with hAdef
  set B : Finset (Fin 13) := (G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁ with hBdef
  have hAcard : 2 ≤ A.card := by
    have hsd := Finset.card_sdiff_add_card_inter (G.neighborFinset h₁ ∩ Iso)
      (G.neighborFinset h₂)
    have heq : (G.neighborFinset h₁ ∩ Iso) ∩ G.neighborFinset h₂
        = G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso := by
      rw [Finset.inter_assoc, Finset.inter_comm Iso (G.neighborFinset h₂), ← Finset.inter_assoc]
    rw [heq] at hsd
    have h3le := hiso3 h₁ hh₁
    rw [hAdef]; omega
  have hBcard : 2 ≤ B.card := by
    have hsd := Finset.card_sdiff_add_card_inter (G.neighborFinset h₂ ∩ Iso)
      (G.neighborFinset h₁)
    have heq : (G.neighborFinset h₂ ∩ Iso) ∩ G.neighborFinset h₁
        = G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso := by
      rw [Finset.inter_assoc, Finset.inter_comm Iso (G.neighborFinset h₁), ← Finset.inter_assoc,
        Finset.inter_comm (G.neighborFinset h₂) (G.neighborFinset h₁)]
    rw [heq] at hsd
    have h3le := hiso3 h₂ hh₂
    rw [hBdef]; omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hAcard
  obtain ⟨c, hc, d, hd, hcd⟩ := Finset.one_lt_card.mp hBcard
  -- Unpack memberships.
  have hAprop : ∀ x : Fin 13, x ∈ A → G.Adj x h₁ ∧ x ∈ Iso ∧ ¬G.Adj x h₂ := by
    intro x hx
    rw [hAdef, Finset.mem_sdiff, Finset.mem_inter, G.mem_neighborFinset] at hx
    refine ⟨hx.1.1.symm, hx.1.2, ?_⟩
    intro hadj; exact hx.2 ((G.mem_neighborFinset h₂ x).mpr hadj.symm)
  have hBprop : ∀ x : Fin 13, x ∈ B → G.Adj x h₂ ∧ x ∈ Iso ∧ ¬G.Adj x h₁ := by
    intro x hx
    rw [hBdef, Finset.mem_sdiff, Finset.mem_inter, G.mem_neighborFinset] at hx
    refine ⟨hx.1.1.symm, hx.1.2, ?_⟩
    intro hadj; exact hx.2 ((G.mem_neighborFinset h₁ x).mpr hadj.symm)
  obtain ⟨ha_h₁, ha_iso, ha_nh₂⟩ := hAprop a ha
  obtain ⟨hb_h₁, hb_iso, hb_nh₂⟩ := hAprop b hb
  obtain ⟨hc_h₂, hc_iso, hc_nh₁⟩ := hBprop c hc
  obtain ⟨hd_h₂, hd_iso, hd_nh₁⟩ := hBprop d hd
  -- Membership in `D` and the no-`D`-neighbour property of isolated twins.
  have hisoD : ∀ x : Fin 13, x ∈ Iso → x ∈ D := fun x hx => ((hIsomem x).mp hx).1
  have hisoNoD : ∀ x y : Fin 13, x ∈ Iso → y ∈ D → ¬G.Adj x y := by
    intro x y hx hy hadj
    obtain ⟨_, hx0⟩ := (hIsomem x).mp hx
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem] at hx0
    exact hx0 y (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset x y).mpr hadj, hy⟩)
  have haD := hisoD a ha_iso
  have hbD := hisoD b hb_iso
  have hcD := hisoD c hc_iso
  have hdD := hisoD d hd_iso
  -- A hub's neighbours all lie in `D`.
  have hHubNonAdj : ∀ x : Fin 13, x ∈ Hub → ∀ y : Fin 13, G.Adj x y → y ∈ D :=
    fun x hx y hadj => hnbhd x hx ((G.mem_neighborFinset x y).mpr hadj)
  -- Final assembly.
  exact ⟨h₁, h₂, a, b, c, d, hdeg4 h₁ hh₁, hdeg4 h₂ hh₂,
    (hmemD a).mp haD, (hmemD b).mp hbD, (hmemD c).mp hcD, (hmemD d).mp hdD,
    ha_h₁, hb_h₁, hc_h₂, hd_h₂,
    (fun h => hHubnotD h₂ hh₂ (hHubNonAdj h₁ hh₁ h₂ h)),
    (fun h => hc_nh₁ h.symm), (fun h => hd_nh₁ h.symm),
    ha_nh₂, hisoNoD a c ha_iso hcD, hisoNoD a d ha_iso hdD,
    hb_nh₂, hisoNoD b c hb_iso hcD, hisoNoD b d hb_iso hdD,
    hne12,
    (fun e => hHubnotD h₁ hh₁ (by rw [e]; exact haD)),
    (fun e => hHubnotD h₁ hh₁ (by rw [e]; exact hbD)),
    (fun e => hHubnotD h₁ hh₁ (by rw [e]; exact hcD)),
    (fun e => hHubnotD h₁ hh₁ (by rw [e]; exact hdD)),
    (fun e => hHubnotD h₂ hh₂ (by rw [e]; exact haD)),
    (fun e => hHubnotD h₂ hh₂ (by rw [e]; exact hbD)),
    (fun e => hHubnotD h₂ hh₂ (by rw [e]; exact hcD)),
    (fun e => hHubnotD h₂ hh₂ (by rw [e]; exact hdD)),
    hab,
    (fun e => hc_nh₁ (e ▸ ha_h₁)), (fun e => hd_nh₁ (e ▸ ha_h₁)),
    (fun e => hc_nh₁ (e ▸ hb_h₁)), (fun e => hd_nh₁ (e ▸ hb_h₁)),
    hcd⟩

/-- **Two-twin configuration in the `e(M) ≥ 3` regime (fully proved).**  Dispatching on the
keystone dichotomy `dominating_edge_or_induced_C5`, each branch supplies an induced `P₃` cherry
`x–y–z` of `M` together with two `M`-isolated degree-3 twins `t₁, t₂` sharing a degree-`≤ 5` hub
`h` avoiding the cherry, via the alignment leaves of `TwinCert13Align` (`config_from_C5` for the
induced `C₅`; `config_from_fat_dom` for a centre of in-`M`-degree `3`; `config_from_thin_dom` for
the `M = P₄` thin dominating edge).  The twins, being `M`-isolated, are automatically non-adjacent
to and distinct from the cherry.  `hK23` is not needed. -/
theorem node_B_config (G : SimpleGraph (Fin 13))
    (hm : G.edgeFinset.card = 22) (h3 : ∀ v : Fin 13, 3 ≤ G.degree v)
    (hT : ¬∃ x y z : Fin 13, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    (h2k2 : ¬∃ a b c d : Fin 13, ({a, b, c, d} : Finset (Fin 13)).card = 4 ∧
      G.degree a = 3 ∧ G.degree b = 3 ∧ G.degree c = 3 ∧ G.degree d = 3 ∧
      G.Adj a b ∧ G.Adj c d ∧ ¬G.Adj a c ∧ ¬G.Adj a d ∧ ¬G.Adj b c ∧ ¬G.Adj b d)
    (hC4 : ¬∃ a b c d : Fin 13, ({a, b, c, d} : Finset (Fin 13)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 13)
    (_hK23 : ¬∃ a b c d e : Fin 13, ({a, b, c, d, e} : Finset (Fin 13)).card = 5 ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
      G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 18)
    (heM3 : 6 ≤ ∑ v ∈ Finset.univ.filter (fun w => G.degree w = 3),
        (G.neighborFinset v ∩ Finset.univ.filter (fun w => G.degree w = 3)).card) :
    ∃ t₁ t₂ h x y z : Fin 13,
        G.degree t₁ = 3 ∧ G.degree t₂ = 3 ∧ G.degree h ≤ 5 ∧
        G.degree x = 3 ∧ G.degree y = 3 ∧ G.degree z = 3 ∧
        G.Adj t₁ h ∧ G.Adj t₂ h ∧ G.Adj x y ∧ G.Adj y z ∧
        ¬G.Adj t₁ x ∧ ¬G.Adj t₁ y ∧ ¬G.Adj t₁ z ∧
        ¬G.Adj t₂ x ∧ ¬G.Adj t₂ y ∧ ¬G.Adj t₂ z ∧
        ¬G.Adj h x ∧ ¬G.Adj h y ∧ ¬G.Adj h z ∧
        t₁ ≠ t₂ ∧ t₁ ≠ x ∧ t₁ ≠ y ∧ t₁ ≠ z ∧ t₂ ≠ x ∧ t₂ ≠ y ∧ t₂ ≠ z ∧
        h ≠ x ∧ h ≠ y ∧ h ≠ z ∧ x ≠ y ∧ y ≠ z ∧ x ≠ z := by
  classical
  set D : Finset (Fin 13) := Finset.univ.filter (fun w => G.degree w = 3) with hDdef
  have hmemD : ∀ v : Fin 13, v ∈ D ↔ G.degree v = 3 := by intro v; rw [hDdef]; simp
  have hmemHub : ∀ v : Fin 13, v ∈ Finset.univ.filter (fun w => 4 ≤ G.degree w) ↔ 4 ≤ G.degree v :=
    by intro v; simp
  -- `8 ≤ |D|` from the degree budget.
  have hsum44 : ∑ v : Fin 13, G.degree v = 44 := by
    rw [SimpleGraph.sum_degrees_eq_twice_card_edges, hm]
  set Hub : Finset (Fin 13) := Finset.univ.filter (fun w => 4 ≤ G.degree w) with hHubdef
  have hDHpart : ∀ x : Fin 13, x ∈ D ∨ x ∈ Hub := fun x => by
    rcases Nat.lt_or_ge (G.degree x) 4 with h | h
    · exact Or.inl ((hmemD x).mpr (by have := h3 x; omega))
    · exact Or.inr ((hmemHub x).mpr h)
  have hdisjDH : Disjoint D Hub := by
    rw [Finset.disjoint_left]; intro x hx hx'
    have := (hmemD x).mp hx; have := (hmemHub x).mp hx'; omega
  have hunionDH : D ∪ Hub = Finset.univ := by
    ext x; simp only [Finset.mem_union, Finset.mem_univ, iff_true]; exact hDHpart x
  have hcard13 : D.card + Hub.card = 13 := by
    have h := Finset.card_union_of_disjoint hdisjDH
    rw [hunionDH, Finset.card_univ, Fintype.card_fin] at h; omega
  have hD8 : 8 ≤ D.card := by
    have hsumDt : ∑ v ∈ D, G.degree v = 3 * D.card := by
      rw [Finset.sum_congr rfl (fun v hv => (hmemD v).mp hv), Finset.sum_const, smul_eq_mul,
        mul_comm]
    have hsumpart : ∑ v ∈ D, G.degree v + ∑ v ∈ Hub, G.degree v = 44 := by
      rw [← Finset.sum_union hdisjDH, hunionDH]; exact hsum44
    have hHubge : 4 * Hub.card ≤ ∑ v ∈ Hub, G.degree v := by
      have hb : ∀ x ∈ Hub, 4 ≤ G.degree x := fun i hi => (hmemHub i).mp hi
      have h := Finset.card_nsmul_le_sum Hub (fun v => G.degree v) 4 hb
      simpa [smul_eq_mul, mul_comm] using h
    omega
  have heM3' : 6 ≤ ∑ v ∈ D, (G.neighborFinset v ∩ D).card := heM3
  -- The `M`-isolated degree-3 twins.
  set T : Finset (Fin 13) := D.filter (fun v => ∀ w : Fin 13, G.Adj v w → G.degree w ≠ 3)
    with hTdef
  have hTmem : ∀ t : Fin 13, t ∈ T ↔ t ∈ D ∧ ∀ w : Fin 13, G.Adj t w → G.degree w ≠ 3 := by
    intro t; rw [hTdef, Finset.mem_filter]
  have heMle10 : ∑ v ∈ D, (G.neighborFinset v ∩ D).card ≤ 10 :=
    eM_le_five G D hmemD hT hC4 h2k2
  have hTcard : 2 ≤ T.card := two_isolated_twins_thirteen G D hmemD h2k2 hD8 heMle10
  -- Package two `M`-isolated twins.
  have htwins : ∃ t₁ t₂ : Fin 13, t₁ ≠ t₂ ∧ G.degree t₁ = 3 ∧
      (∀ w : Fin 13, G.Adj t₁ w → G.degree w ≠ 3) ∧ G.degree t₂ = 3 ∧
      (∀ w : Fin 13, G.Adj t₂ w → G.degree w ≠ 3) := by
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hTcard
    obtain ⟨haD, haiso⟩ := (hTmem a).mp ha
    obtain ⟨hbD, hbiso⟩ := (hTmem b).mp hb
    exact ⟨a, b, hab, (hmemD a).mp haD, haiso, (hmemD b).mp hbD, hbiso⟩
  -- An `M`-edge exists (`e(M) ≥ 3 > 0`).
  have hne_edge : ∃ a b : Fin 13, a ∈ D ∧ b ∈ D ∧ G.Adj a b := by
    by_contra hcon
    push Not at hcon
    have hzero : ∀ v ∈ D, (G.neighborFinset v ∩ D).card = 0 := by
      intro v hv
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro w hw
      rw [Finset.mem_inter, G.mem_neighborFinset] at hw
      exact hcon v w hv hw.2 hw.1
    have hsum0 : ∑ v ∈ D, (G.neighborFinset v ∩ D).card = 0 := Finset.sum_eq_zero hzero
    omega
  -- **Reusable fat dominating-centre dispatch.**
  have fat : ∀ c : Fin 13, c ∈ D → 3 ≤ (G.neighborFinset c ∩ D).card → TwoTwinConfig G := by
    intro c hcD hge
    have hc3 : G.degree c = 3 := (hmemD c).mp hcD
    have hle : (G.neighborFinset c ∩ D).card ≤ 3 := by
      calc (G.neighborFinset c ∩ D).card ≤ (G.neighborFinset c).card :=
            Finset.card_le_card Finset.inter_subset_left
        _ = G.degree c := G.card_neighborFinset_eq_degree c
        _ = 3 := hc3
    have heq3 : (G.neighborFinset c ∩ D).card = 3 := le_antisymm hle hge
    obtain ⟨n₁, n₂, n₃, hne12, hne13, hne23, hset⟩ := Finset.card_eq_three.mp heq3
    have hcard : (G.neighborFinset c).card = (G.neighborFinset c ∩ D).card := by
      rw [G.card_neighborFinset_eq_degree, hc3, heq3]
    have hNsubeq : G.neighborFinset c ∩ D = G.neighborFinset c :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_left (le_of_eq hcard)
    have hmem_i : ∀ w : Fin 13, w ∈ ({n₁, n₂, n₃} : Finset (Fin 13)) →
        G.Adj c w ∧ w ∈ D := by
      intro w hw
      have hw' : w ∈ G.neighborFinset c ∩ D := hset ▸ hw
      exact ⟨(G.mem_neighborFinset _ _).mp (Finset.mem_inter.mp hw').1,
        (Finset.mem_inter.mp hw').2⟩
    obtain ⟨a1, hn1D⟩ := hmem_i n₁ (by simp)
    obtain ⟨a2, hn2D⟩ := hmem_i n₂ (by simp)
    obtain ⟨a3, hn3D⟩ := hmem_i n₃ (by simp)
    have hcnbhd : ∀ w : Fin 13, G.Adj c w → w = n₁ ∨ w = n₂ ∨ w = n₃ := by
      intro w hw
      have hw' : w ∈ G.neighborFinset c ∩ D := by
        rw [hNsubeq]; exact (G.mem_neighborFinset _ _).mpr hw
      rw [hset] at hw'
      simpa using hw'
    exact config_from_fat_dom G hm h3 hT hC4 htwins c n₁ n₂ n₃ hc3
      ((hmemD n₁).mp hn1D) ((hmemD n₂).mp hn2D) ((hmemD n₃).mp hn3D)
      hne12 hne13 hne23 a1 a2 a3 hcnbhd
  rcases dominating_edge_or_induced_C5 G D hmemD hT hC4 h2k2 hne_edge with hA | hB
  · obtain ⟨c₁, c₂, hc1D, hc2D, hc12, hcov⟩ := hA
    rcases Nat.lt_or_ge (G.neighborFinset c₁ ∩ D).card 3 with hlt1 | hge1
    · rcases Nat.lt_or_ge (G.neighborFinset c₂ ∩ D).card 3 with hlt2 | hge2
      · have hform := thin_eM_formula G D c₁ c₂ hc1D hc2D hc12 hcov
        have hin1 : (G.neighborFinset c₁ ∩ D).card = 2 := by omega
        have hin2 : (G.neighborFinset c₂ ∩ D).card = 2 := by omega
        exact config_from_thin_dom G hm h3 hT D hmemD c₁ c₂ hc1D hc2D hc12 hin1 hin2 hcov
      · exact fat c₂ hc2D hge2
    · exact fat c₁ hc1D hge1
  · obtain ⟨v₁, v₂, v₃, v₄, v₅, hv1, hv2, hv3, hv4, hv5, hcard5,
      e12, e23, e34, e45, e51, n13, n14, n24, n25, n35, _hcov⟩ := hB
    exact config_from_C5 G hm h3 hT hC4 htwins v₁ v₂ v₃ v₄ v₅
      ((hmemD v₁).mp hv1) ((hmemD v₂).mp hv2) ((hmemD v₃).mp hv3) ((hmemD v₄).mp hv4)
      ((hmemD v₅).mp hv5) hcard5 e12 e23 e34 e45 e51 n13 n14 n24 n25 n35

/-- **Structural existence of a signed-cut configuration for the `n = 13` residual (the lone
triangle/`C₄`/`K_{2,3}`, no degree-3 `2K₂`, an isolated degree-3 vertex) one of two explicit
configurations is present:

* a **two-hub opposite-twin** configuration `h₁, h₂, a, b, c, d` (the `e(M) = 2` regime, where
  the degree sequence is forced to `[4⁵, 3⁸]`, all hubs are degree-4 and pairwise non-adjacent,
  and there are `≥ 5` `M`-isolated twins), feeding `two_hub_opposite_twin_cert`; or
* a **two-twin** configuration `t₁, t₂, h, x, y, z` (the `e(M) ≥ 3` regime: a `P₃` `x–y–z` chosen
  first from the keystone `dominating_edge_or_induced_C5`, then two `M`-isolated twins sharing a
  hub `h` avoiding that `P₃`), feeding `two_twin_cut_certificate`.

This existence is the genuine open structural core for `n = 13`, verified only by exhaustive
`nauty` enumeration of the residual graphs; the boundary arithmetic of both cuts is fully proved
(`two_hub_opposite_twin_cert`, `two_twin_cut_certificate`).  `eM_ge_four` rules out `e(M) ≤ 1`. -/
theorem exists_two_hub_or_two_twin_config (G : SimpleGraph (Fin 13))
    (hm : G.edgeFinset.card = 22) (h3 : ∀ v : Fin 13, 3 ≤ G.degree v)
    (hT : ¬∃ x y z : Fin 13, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    (h2k2 : ¬∃ a b c d : Fin 13, ({a, b, c, d} : Finset (Fin 13)).card = 4 ∧
      G.degree a = 3 ∧ G.degree b = 3 ∧ G.degree c = 3 ∧ G.degree d = 3 ∧
      G.Adj a b ∧ G.Adj c d ∧ ¬G.Adj a c ∧ ¬G.Adj a d ∧ ¬G.Adj b c ∧ ¬G.Adj b d)
    (hC4 : ¬∃ a b c d : Fin 13, ({a, b, c, d} : Finset (Fin 13)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 13)
    (hK23 : ¬∃ a b c d e : Fin 13, ({a, b, c, d, e} : Finset (Fin 13)).card = 5 ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
      G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 18)
    (hiso : ∃ t : Fin 13, G.degree t = 3 ∧ ∀ w : Fin 13, G.Adj t w → G.degree w ≠ 3) :
    (∃ h₁ h₂ a b c d : Fin 13,
        G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧
        G.degree a = 3 ∧ G.degree b = 3 ∧ G.degree c = 3 ∧ G.degree d = 3 ∧
        G.Adj a h₁ ∧ G.Adj b h₁ ∧ G.Adj c h₂ ∧ G.Adj d h₂ ∧
        ¬G.Adj h₁ h₂ ∧ ¬G.Adj h₁ c ∧ ¬G.Adj h₁ d ∧
        ¬G.Adj a h₂ ∧ ¬G.Adj a c ∧ ¬G.Adj a d ∧
        ¬G.Adj b h₂ ∧ ¬G.Adj b c ∧ ¬G.Adj b d ∧
        h₁ ≠ h₂ ∧ h₁ ≠ a ∧ h₁ ≠ b ∧ h₁ ≠ c ∧ h₁ ≠ d ∧
        h₂ ≠ a ∧ h₂ ≠ b ∧ h₂ ≠ c ∧ h₂ ≠ d ∧
        a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d)
    ∨ (∃ t₁ t₂ h x y z : Fin 13,
        G.degree t₁ = 3 ∧ G.degree t₂ = 3 ∧ G.degree h ≤ 5 ∧
        G.degree x = 3 ∧ G.degree y = 3 ∧ G.degree z = 3 ∧
        G.Adj t₁ h ∧ G.Adj t₂ h ∧ G.Adj x y ∧ G.Adj y z ∧
        ¬G.Adj t₁ x ∧ ¬G.Adj t₁ y ∧ ¬G.Adj t₁ z ∧
        ¬G.Adj t₂ x ∧ ¬G.Adj t₂ y ∧ ¬G.Adj t₂ z ∧
        ¬G.Adj h x ∧ ¬G.Adj h y ∧ ¬G.Adj h z ∧
        t₁ ≠ t₂ ∧ t₁ ≠ x ∧ t₁ ≠ y ∧ t₁ ≠ z ∧ t₂ ≠ x ∧ t₂ ≠ y ∧ t₂ ≠ z ∧
        h ≠ x ∧ h ≠ y ∧ h ≠ z ∧ x ≠ y ∧ y ≠ z ∧ x ≠ z) := by
  classical
  set D : Finset (Fin 13) := Finset.univ.filter (fun w => G.degree w = 3) with hDdef
  have hmemD : ∀ v : Fin 13, v ∈ D ↔ G.degree v = 3 := by intro v; rw [hDdef]; simp
  rcases Nat.lt_or_ge (∑ v ∈ D, (G.neighborFinset v ∩ D).card) 6 with hlow | hhigh
  · -- `e(M) ≤ 2`; `eM_ge_four` and parity force `e(M) = 2` (`∑ = 4`).
    refine Or.inl ?_
    have hsum44 : ∑ v : Fin 13, G.degree v = 44 := by
      rw [SimpleGraph.sum_degrees_eq_twice_card_edges, hm]
    set Hub : Finset (Fin 13) := Finset.univ.filter (fun w => 4 ≤ G.degree w) with hHubdef
    have hmemHub : ∀ v : Fin 13, v ∈ Hub ↔ 4 ≤ G.degree v := by intro v; rw [hHubdef]; simp
    have hDHpart : ∀ x : Fin 13, x ∈ D ∨ x ∈ Hub := fun x => by
      rcases Nat.lt_or_ge (G.degree x) 4 with h | h
      · exact Or.inl ((hmemD x).mpr (by have := h3 x; omega))
      · exact Or.inr ((hmemHub x).mpr h)
    have hdisjDH : Disjoint D Hub := by
      rw [Finset.disjoint_left]; intro x hx hx'
      have := (hmemD x).mp hx; have := (hmemHub x).mp hx'; omega
    have hunionDH : D ∪ Hub = Finset.univ := by
      ext x; simp only [Finset.mem_union, Finset.mem_univ, iff_true]; exact hDHpart x
    have hcard13 : D.card + Hub.card = 13 := by
      have h := Finset.card_union_of_disjoint hdisjDH
      rw [hunionDH, Finset.card_univ, Fintype.card_fin] at h; omega
    have hD8 : 8 ≤ D.card := by
      have hsumDt : ∑ v ∈ D, G.degree v = 3 * D.card := by
        rw [Finset.sum_congr rfl (fun v hv => (hmemD v).mp hv), Finset.sum_const, smul_eq_mul,
          mul_comm]
      have hsumpart : ∑ v ∈ D, G.degree v + ∑ v ∈ Hub, G.degree v = 44 := by
        rw [← Finset.sum_union hdisjDH, hunionDH]; exact hsum44
      have hHubge : 4 * Hub.card ≤ ∑ v ∈ Hub, G.degree v := by
        have hb : ∀ x ∈ Hub, 4 ≤ G.degree x := fun i hi => (hmemHub i).mp hi
        have h := Finset.card_nsmul_le_sum Hub (fun v => G.degree v) 4 hb
        simpa [smul_eq_mul, mul_comm] using h
      omega
    have hge4 : 4 ≤ ∑ v ∈ D, (G.neighborFinset v ∩ D).card := eM_ge_four G hm D hmemD hD8
    obtain ⟨r, hr⟩ := eM_even G D
    have heq4 : ∑ v ∈ D, (G.neighborFinset v ∩ D).card = 4 := by omega
    exact node_A_config G hm h3 hT h2k2 hC4 (hDdef ▸ heq4)
  · exact Or.inr (node_B_config G hm h3 hT h2k2 hC4 hK23 (hDdef ▸ hhigh))

end N13

end ACMax
