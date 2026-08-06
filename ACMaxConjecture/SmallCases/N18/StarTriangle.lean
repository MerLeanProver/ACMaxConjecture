import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N18.Core

/-!
# The star-triangle signed-cut certificate for `n = 18`

This file supplies the **fifth cut construction** for the `n = 18` development (the first genuinely
new construction since the `n = 15` hub-triangle): the *star-triangle* cut.  The negative side `P`
is a **star** `{h, t₁, t₂}` (a degree-`4` hub `h` together with two of its `M`-isolated degree-`3`
twins `t₁, t₂`), the positive side `N` is a **hub-triangle** `{a, b, c}` (three mutually-adjacent
degree-`4` hubs), with the two sides non-adjacent (`e(P, N) = 0`).

The boundary arithmetic is local: `e(P, N) = 0`, the star contributes
`leak(P) = (deg h − 2) + (deg t₁ − 1) + (deg t₂ − 1) = 2 + 2 + 2 = 6` (the hub `h` keeps its two
twin edges inside `P`; each twin keeps its single `h`-edge inside `P`), the triangle contributes
`leak(N) = ∑_{N}(deg − 2) = 3 · 2 = 6` (each triangle hub keeps its two triangle edges inside `N`),
so the total boundary is `4 · 0 + 6 + 6 = 12 ≤ 4 · 3`.  Mirrors `hub_triangle_cut_certificate` in
`TwinCert18Cert`.
-/

namespace ACMax

open scoped Classical

namespace N18

/-- **The star-triangle signed-cut configuration** for the `e(M) = 1`, `|Hub| = 10` corner: a
degree-`4` hub `h` with two `M`-isolated degree-`3` twins `t₁, t₂` (the *star* `P = {h, t₁, t₂}`),
against three mutually-adjacent degree-`4` hubs `a, b, c` (the *triangle* `N = {a, b, c}`), with the
two sides totally non-adjacent (`e(P, N) = 0`) and the six vertices distinct.  Consumed by
`star_triangle_cut_certificate`. -/
def StarTriangleConfig (G : SimpleGraph (Fin 18)) : Prop :=
  ∃ h t₁ t₂ a b c : Fin 18,
    G.degree h = 4 ∧ G.degree t₁ = 3 ∧ G.degree t₂ = 3 ∧
    G.degree a = 4 ∧ G.degree b = 4 ∧ G.degree c = 4 ∧
    G.Adj h t₁ ∧ G.Adj h t₂ ∧
    G.Adj a b ∧ G.Adj a c ∧ G.Adj b c ∧
    ¬G.Adj h a ∧ ¬G.Adj h b ∧ ¬G.Adj h c ∧
    ¬G.Adj t₁ a ∧ ¬G.Adj t₁ b ∧ ¬G.Adj t₁ c ∧
    ¬G.Adj t₂ a ∧ ¬G.Adj t₂ b ∧ ¬G.Adj t₂ c ∧
    t₁ ≠ t₂ ∧
    h ≠ a ∧ h ≠ b ∧ h ≠ c ∧ t₁ ≠ a ∧ t₁ ≠ b ∧ t₁ ≠ c ∧ t₂ ≠ a ∧ t₂ ≠ b ∧ t₂ ≠ c

/-- **Star-triangle cut assembly (boundary arithmetic, fully proved).**  A degree-`4` hub `h` with
two distinct twins `t₁, t₂` (`Adj h t₁`, `Adj h t₂`), three mutually-adjacent degree-`4` hubs
`a, b, c`, the two sides non-adjacent and the six vertices distinct.  The star-triangle cut
`P = {h, t₁, t₂}`, `N = {a, b, c}` satisfies `4·e(P,N) + e(P,Z) + e(N,Z) ≤ 4·|P|`.  The cross term
vanishes; the star keeps `2 + 1 + 1` internal edges so `e(P,Z) ≤ deg h + deg t₁ + deg t₂ − 4 = 6`,
and the triangle keeps `2` each so `e(N,Z) ≤ 6`, giving `12 ≤ 12`. -/
theorem star_triangle_cut_certificate (G : SimpleGraph (Fin 18)) (h t₁ t₂ a b c : Fin 18)
    (hdegh : G.degree h = 4) (hdegt1 : G.degree t₁ = 3) (hdegt2 : G.degree t₂ = 3)
    (hdega : G.degree a = 4) (hdegb : G.degree b = 4) (hdegc : G.degree c = 4)
    (hAht1 : G.Adj h t₁) (hAht2 : G.Adj h t₂)
    (hAab : G.Adj a b) (hAac : G.Adj a c) (hAbc : G.Adj b c)
    (hnha : ¬G.Adj h a) (hnhb : ¬G.Adj h b) (hnhc : ¬G.Adj h c)
    (hnt1a : ¬G.Adj t₁ a) (hnt1b : ¬G.Adj t₁ b) (hnt1c : ¬G.Adj t₁ c)
    (hnt2a : ¬G.Adj t₂ a) (hnt2b : ¬G.Adj t₂ b) (hnt2c : ¬G.Adj t₂ c)
    (ne_t12 : t₁ ≠ t₂)
    (ne_ha : h ≠ a) (ne_hb : h ≠ b) (ne_hc : h ≠ c)
    (ne_t1a : t₁ ≠ a) (ne_t1b : t₁ ≠ b) (ne_t1c : t₁ ≠ c)
    (ne_t2a : t₂ ≠ a) (ne_t2b : t₂ ≠ b) (ne_t2c : t₂ ≠ c) :
    ∃ P N : Finset (Fin 18), Disjoint P N ∧ P.card = N.card ∧ 0 < P.card ∧
      4 * (∑ p ∈ P, (G.neighborFinset p ∩ N).card)
        + (∑ p ∈ P, (G.neighborFinset p \ (P ∪ N)).card)
        + (∑ q ∈ N, (G.neighborFinset q \ (P ∪ N)).card)
      ≤ 4 * P.card := by
  classical
  have ne_ht1 : h ≠ t₁ := G.ne_of_adj hAht1
  have ne_ht2 : h ≠ t₂ := G.ne_of_adj hAht2
  have ne_ab : a ≠ b := G.ne_of_adj hAab
  have ne_ac : a ≠ c := G.ne_of_adj hAac
  have ne_bc : b ≠ c := G.ne_of_adj hAbc
  have hPcard : ({h, t₁, t₂} : Finset (Fin 18)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [ne_ht1, ne_ht2]),
        Finset.card_insert_of_notMem (by simp [ne_t12]), Finset.card_singleton]
  have hNcard : ({a, b, c} : Finset (Fin 18)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [ne_ab, ne_ac]),
        Finset.card_insert_of_notMem (by simp [ne_bc]), Finset.card_singleton]
  have hdisjPN : Disjoint ({h, t₁, t₂} : Finset (Fin 18)) ({a, b, c} : Finset (Fin 18)) := by
    rw [Finset.disjoint_left]
    intro w hw hw'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw hw'
    rcases hw with rfl | rfl | rfl <;> rcases hw' with rfl | rfl | rfl <;>
      first
      | exact ne_ha rfl | exact ne_hb rfl | exact ne_hc rfl
      | exact ne_t1a rfl | exact ne_t1b rfl | exact ne_t1c rfl
      | exact ne_t2a rfl | exact ne_t2b rfl | exact ne_t2c rfl
  -- `e(P, N) = 0`: each star vertex has no neighbour in the triangle.
  have hPN_h : (G.neighborFinset h ∩ ({a, b, c} : Finset (Fin 18))).card = 0 := by
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro w hw
    rw [Finset.mem_inter, G.mem_neighborFinset] at hw
    obtain ⟨hadj, hmem⟩ := hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with rfl | rfl | rfl
    · exact hnha hadj
    · exact hnhb hadj
    · exact hnhc hadj
  have hPN_t1 : (G.neighborFinset t₁ ∩ ({a, b, c} : Finset (Fin 18))).card = 0 := by
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro w hw
    rw [Finset.mem_inter, G.mem_neighborFinset] at hw
    obtain ⟨hadj, hmem⟩ := hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with rfl | rfl | rfl
    · exact hnt1a hadj
    · exact hnt1b hadj
    · exact hnt1c hadj
  have hPN_t2 : (G.neighborFinset t₂ ∩ ({a, b, c} : Finset (Fin 18))).card = 0 := by
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro w hw
    rw [Finset.mem_inter, G.mem_neighborFinset] at hw
    obtain ⟨hadj, hmem⟩ := hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with rfl | rfl | rfl
    · exact hnt2a hadj
    · exact hnt2b hadj
    · exact hnt2c hadj
  -- Star-side leaks: `h` keeps `2` edges (to `t₁, t₂`), each twin keeps `1` edge (to `h`).
  have hh_le : (G.neighborFinset h \
      (({h, t₁, t₂} : Finset (Fin 18)) ∪ {a, b, c})).card + 2 ≤ G.degree h := by
    have hsub : ({t₁, t₂} : Finset (Fin 18)) ⊆
        G.neighborFinset h ∩ (({h, t₁, t₂} : Finset (Fin 18)) ∪ {a, b, c}) := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rw [Finset.mem_inter, G.mem_neighborFinset]
      rcases hw with rfl | rfl
      · exact ⟨hAht1, by simp⟩
      · exact ⟨hAht2, by simp⟩
    have hge : 2 ≤ (G.neighborFinset h ∩
        (({h, t₁, t₂} : Finset (Fin 18)) ∪ {a, b, c})).card := by
      have h2 : ({t₁, t₂} : Finset (Fin 18)).card = 2 := by
        rw [Finset.card_insert_of_notMem (by simp [ne_t12]), Finset.card_singleton]
      calc 2 = ({t₁, t₂} : Finset (Fin 18)).card := h2.symm
        _ ≤ _ := Finset.card_le_card hsub
    have hsd := Finset.card_sdiff_add_card_inter (G.neighborFinset h)
      (({h, t₁, t₂} : Finset (Fin 18)) ∪ {a, b, c})
    rw [G.card_neighborFinset_eq_degree] at hsd
    omega
  have ht1_le : (G.neighborFinset t₁ \
      (({h, t₁, t₂} : Finset (Fin 18)) ∪ {a, b, c})).card + 1 ≤ G.degree t₁ := by
    have hsub : ({h} : Finset (Fin 18)) ⊆
        G.neighborFinset t₁ ∩ (({h, t₁, t₂} : Finset (Fin 18)) ∪ {a, b, c}) := by
      intro w hw
      rw [Finset.mem_singleton] at hw; subst hw
      rw [Finset.mem_inter, G.mem_neighborFinset]
      exact ⟨hAht1.symm, by simp⟩
    have hge : 1 ≤ (G.neighborFinset t₁ ∩
        (({h, t₁, t₂} : Finset (Fin 18)) ∪ {a, b, c})).card := by
      calc 1 = ({h} : Finset (Fin 18)).card := (Finset.card_singleton h).symm
        _ ≤ _ := Finset.card_le_card hsub
    have hsd := Finset.card_sdiff_add_card_inter (G.neighborFinset t₁)
      (({h, t₁, t₂} : Finset (Fin 18)) ∪ {a, b, c})
    rw [G.card_neighborFinset_eq_degree] at hsd
    omega
  have ht2_le : (G.neighborFinset t₂ \
      (({h, t₁, t₂} : Finset (Fin 18)) ∪ {a, b, c})).card + 1 ≤ G.degree t₂ := by
    have hsub : ({h} : Finset (Fin 18)) ⊆
        G.neighborFinset t₂ ∩ (({h, t₁, t₂} : Finset (Fin 18)) ∪ {a, b, c}) := by
      intro w hw
      rw [Finset.mem_singleton] at hw; subst hw
      rw [Finset.mem_inter, G.mem_neighborFinset]
      exact ⟨hAht2.symm, by simp⟩
    have hge : 1 ≤ (G.neighborFinset t₂ ∩
        (({h, t₁, t₂} : Finset (Fin 18)) ∪ {a, b, c})).card := by
      calc 1 = ({h} : Finset (Fin 18)).card := (Finset.card_singleton h).symm
        _ ≤ _ := Finset.card_le_card hsub
    have hsd := Finset.card_sdiff_add_card_inter (G.neighborFinset t₂)
      (({h, t₁, t₂} : Finset (Fin 18)) ∪ {a, b, c})
    rw [G.card_neighborFinset_eq_degree] at hsd
    omega
  -- Triangle-side leaks: each triangle hub keeps `2` edges inside `N`.
  have ha_le : (G.neighborFinset a \
      (({h, t₁, t₂} : Finset (Fin 18)) ∪ {a, b, c})).card + 2 ≤ G.degree a := by
    have hsub : ({b, c} : Finset (Fin 18)) ⊆
        G.neighborFinset a ∩ (({h, t₁, t₂} : Finset (Fin 18)) ∪ {a, b, c}) := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rw [Finset.mem_inter, G.mem_neighborFinset]
      rcases hw with rfl | rfl
      · exact ⟨hAab, by simp⟩
      · exact ⟨hAac, by simp⟩
    have hge : 2 ≤ (G.neighborFinset a ∩
        (({h, t₁, t₂} : Finset (Fin 18)) ∪ {a, b, c})).card := by
      have h2 : ({b, c} : Finset (Fin 18)).card = 2 := by
        rw [Finset.card_insert_of_notMem (by simp [ne_bc]), Finset.card_singleton]
      calc 2 = ({b, c} : Finset (Fin 18)).card := h2.symm
        _ ≤ _ := Finset.card_le_card hsub
    have hsd := Finset.card_sdiff_add_card_inter (G.neighborFinset a)
      (({h, t₁, t₂} : Finset (Fin 18)) ∪ {a, b, c})
    rw [G.card_neighborFinset_eq_degree] at hsd
    omega
  have hb_le : (G.neighborFinset b \
      (({h, t₁, t₂} : Finset (Fin 18)) ∪ {a, b, c})).card + 2 ≤ G.degree b := by
    have hsub : ({a, c} : Finset (Fin 18)) ⊆
        G.neighborFinset b ∩ (({h, t₁, t₂} : Finset (Fin 18)) ∪ {a, b, c}) := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rw [Finset.mem_inter, G.mem_neighborFinset]
      rcases hw with rfl | rfl
      · exact ⟨hAab.symm, by simp⟩
      · exact ⟨hAbc, by simp⟩
    have hge : 2 ≤ (G.neighborFinset b ∩
        (({h, t₁, t₂} : Finset (Fin 18)) ∪ {a, b, c})).card := by
      have h2 : ({a, c} : Finset (Fin 18)).card = 2 := by
        rw [Finset.card_insert_of_notMem (by simp [ne_ac]), Finset.card_singleton]
      calc 2 = ({a, c} : Finset (Fin 18)).card := h2.symm
        _ ≤ _ := Finset.card_le_card hsub
    have hsd := Finset.card_sdiff_add_card_inter (G.neighborFinset b)
      (({h, t₁, t₂} : Finset (Fin 18)) ∪ {a, b, c})
    rw [G.card_neighborFinset_eq_degree] at hsd
    omega
  have hc_le : (G.neighborFinset c \
      (({h, t₁, t₂} : Finset (Fin 18)) ∪ {a, b, c})).card + 2 ≤ G.degree c := by
    have hsub : ({a, b} : Finset (Fin 18)) ⊆
        G.neighborFinset c ∩ (({h, t₁, t₂} : Finset (Fin 18)) ∪ {a, b, c}) := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rw [Finset.mem_inter, G.mem_neighborFinset]
      rcases hw with rfl | rfl
      · exact ⟨hAac.symm, by simp⟩
      · exact ⟨hAbc.symm, by simp⟩
    have hge : 2 ≤ (G.neighborFinset c ∩
        (({h, t₁, t₂} : Finset (Fin 18)) ∪ {a, b, c})).card := by
      have h2 : ({a, b} : Finset (Fin 18)).card = 2 := by
        rw [Finset.card_insert_of_notMem (by simp [ne_ab]), Finset.card_singleton]
      calc 2 = ({a, b} : Finset (Fin 18)).card := h2.symm
        _ ≤ _ := Finset.card_le_card hsub
    have hsd := Finset.card_sdiff_add_card_inter (G.neighborFinset c)
      (({h, t₁, t₂} : Finset (Fin 18)) ∪ {a, b, c})
    rw [G.card_neighborFinset_eq_degree] at hsd
    omega
  refine ⟨({h, t₁, t₂} : Finset (Fin 18)), ({a, b, c} : Finset (Fin 18)), hdisjPN,
    (by rw [hPcard, hNcard]), (by rw [hPcard]; norm_num), ?_⟩
  have e1 : ∑ p ∈ ({h, t₁, t₂} : Finset (Fin 18)),
      (G.neighborFinset p ∩ ({a, b, c} : Finset (Fin 18))).card
      = (G.neighborFinset h ∩ ({a, b, c} : Finset (Fin 18))).card
        + (G.neighborFinset t₁ ∩ ({a, b, c} : Finset (Fin 18))).card
        + (G.neighborFinset t₂ ∩ ({a, b, c} : Finset (Fin 18))).card := by
    rw [Finset.sum_insert (by simp [ne_ht1, ne_ht2]),
        Finset.sum_insert (by simp [ne_t12]), Finset.sum_singleton]
    ring
  have e2 : ∑ p ∈ ({h, t₁, t₂} : Finset (Fin 18)),
      (G.neighborFinset p \ (({h, t₁, t₂} : Finset (Fin 18)) ∪ {a, b, c})).card
      = (G.neighborFinset h \ (({h, t₁, t₂} : Finset (Fin 18)) ∪ {a, b, c})).card
        + (G.neighborFinset t₁ \ (({h, t₁, t₂} : Finset (Fin 18)) ∪ {a, b, c})).card
        + (G.neighborFinset t₂ \ (({h, t₁, t₂} : Finset (Fin 18)) ∪ {a, b, c})).card := by
    rw [Finset.sum_insert (by simp [ne_ht1, ne_ht2]),
        Finset.sum_insert (by simp [ne_t12]), Finset.sum_singleton]
    ring
  have e3 : ∑ q ∈ ({a, b, c} : Finset (Fin 18)),
      (G.neighborFinset q \ (({h, t₁, t₂} : Finset (Fin 18)) ∪ {a, b, c})).card
      = (G.neighborFinset a \ (({h, t₁, t₂} : Finset (Fin 18)) ∪ {a, b, c})).card
        + (G.neighborFinset b \ (({h, t₁, t₂} : Finset (Fin 18)) ∪ {a, b, c})).card
        + (G.neighborFinset c \ (({h, t₁, t₂} : Finset (Fin 18)) ∪ {a, b, c})).card := by
    rw [Finset.sum_insert (by simp [ne_ab, ne_ac]),
        Finset.sum_insert (by simp [ne_bc]), Finset.sum_singleton]
    ring
  rw [e1, e2, e3, hPcard, hPN_h, hPN_t1, hPN_t2]
  omega

/-- **Star-triangle config yields the signed cut.**  Unpacks a `StarTriangleConfig` and feeds it to
`star_triangle_cut_certificate`. -/
theorem starTriangleConfig_to_cut (G : SimpleGraph (Fin 18)) (h : StarTriangleConfig G) :
    ∃ P N : Finset (Fin 18), Disjoint P N ∧ P.card = N.card ∧ 0 < P.card ∧
      4 * (∑ p ∈ P, (G.neighborFinset p ∩ N).card)
        + (∑ p ∈ P, (G.neighborFinset p \ (P ∪ N)).card)
        + (∑ q ∈ N, (G.neighborFinset q \ (P ∪ N)).card)
      ≤ 4 * P.card := by
  obtain ⟨h, t₁, t₂, a, b, c, hdegh, hdegt1, hdegt2, hdega, hdegb, hdegc,
    hAht1, hAht2, hAab, hAac, hAbc, hnha, hnhb, hnhc, hnt1a, hnt1b, hnt1c,
    hnt2a, hnt2b, hnt2c, ne_t12, ne_ha, ne_hb, ne_hc, ne_t1a, ne_t1b, ne_t1c,
    ne_t2a, ne_t2b, ne_t2c⟩ := h
  exact star_triangle_cut_certificate G h t₁ t₂ a b c hdegh hdegt1 hdegt2 hdega hdegb hdegc
    hAht1 hAht2 hAab hAac hAbc hnha hnhb hnhc hnt1a hnt1b hnt1c hnt2a hnt2b hnt2c ne_t12
    ne_ha ne_hb ne_hc ne_t1a ne_t1b ne_t1c ne_t2a ne_t2b ne_t2c

end N18

end ACMax
