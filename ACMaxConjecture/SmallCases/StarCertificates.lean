import ACMaxConjecture.SmallCases.Certificates

/-!
# Generic star-triangle certificates

The maximal-hub star/triangle configuration and its boundary calculation do not
depend on the graph order.
-/

namespace ACMax

open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **The star-triangle signed-cut configuration** (the `e(M) = 1`, maximal-hub corner): a degree-`4`
hub `h` with two `M`-isolated degree-`3` twins `t₁, t₂` (star `P = {h, t₁, t₂}`), against three
mutually-adjacent degree-`4` hubs `a, b, c` (triangle `N = {a, b, c}`), the two sides totally
non-adjacent.  It applies uniformly at the maximal-hub frontier. -/
def StarTriangleConfig (G : SimpleGraph (V)) : Prop :=
  ∃ h t₁ t₂ a b c : V,
    G.degree h = 4 ∧ G.degree t₁ = 3 ∧ G.degree t₂ = 3 ∧
    G.degree a = 4 ∧ G.degree b = 4 ∧ G.degree c = 4 ∧
    G.Adj h t₁ ∧ G.Adj h t₂ ∧
    G.Adj a b ∧ G.Adj a c ∧ G.Adj b c ∧
    ¬G.Adj h a ∧ ¬G.Adj h b ∧ ¬G.Adj h c ∧
    ¬G.Adj t₁ a ∧ ¬G.Adj t₁ b ∧ ¬G.Adj t₁ c ∧
    ¬G.Adj t₂ a ∧ ¬G.Adj t₂ b ∧ ¬G.Adj t₂ c ∧
    t₁ ≠ t₂ ∧
    h ≠ a ∧ h ≠ b ∧ h ≠ c ∧ t₁ ≠ a ∧ t₁ ≠ b ∧ t₁ ≠ c ∧ t₂ ≠ a ∧ t₂ ≠ b ∧ t₂ ≠ c

/-- **The boundary-cut outcome for the `e(M) = 1`, maximal-hub z-meets-2-poor regime.**  The two
maximal-hub signed-cut configurations available at the `|D| = 8` frontier: a two-hub opposite-twin
cut (`TwoHubConfig`, the leaves may be `M`-isolated twins **or** `M`-edge endpoints) or the
star-triangle cut (`StarTriangleConfig`).  STRUCTURED-construction MCMC over the `r = 5`,
`∑_R isoDeg = 12`, `{4,2,2,2,2}` z-meets-2-poor survivors (every realisation passing
`hshare ∧ hno2hub` with no good triangle/`C₄`/`K₂,₃`) confirms **every** such graph realises this
disjunction — most via `TwoHubConfig` using one `Z`-leaf (which the `Iso`-only `hno2hub` does not see),
the rest via `StarTriangleConfig`. -/
def ZPoorCutConfig (G : SimpleGraph (V)) : Prop :=
  TwoHubConfig G ∨ StarTriangleConfig G

/-- **Star-triangle cut assembly (boundary arithmetic, fully proved).**  A degree-`4` hub `h` with
two distinct twins `t₁, t₂` (`Adj h t₁`, `Adj h t₂`), three mutually-adjacent degree-`4` hubs
`a, b, c`, the two sides non-adjacent and the six vertices distinct.  The star-triangle cut
`P = {h, t₁, t₂}`, `N = {a, b, c}` satisfies `4·e(P,N) + e(P,Z) + e(N,Z) ≤ 4·|P|`.  The cross term
vanishes; the star keeps `2 + 1 + 1` internal edges so `e(P,Z) ≤ deg h + deg t₁ + deg t₂ − 4 = 6`,
and the triangle keeps `2` each so `e(N,Z) ≤ 6`, giving `12 ≤ 12`. -/
theorem star_triangle_cut_certificate (G : SimpleGraph (V)) (h t₁ t₂ a b c : V)
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
    ∃ P N : Finset (V), Disjoint P N ∧ P.card = N.card ∧ 0 < P.card ∧
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
  have hPcard : ({h, t₁, t₂} : Finset (V)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [ne_ht1, ne_ht2]),
        Finset.card_insert_of_notMem (by simp [ne_t12]), Finset.card_singleton]
  have hNcard : ({a, b, c} : Finset (V)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [ne_ab, ne_ac]),
        Finset.card_insert_of_notMem (by simp [ne_bc]), Finset.card_singleton]
  have hdisjPN : Disjoint ({h, t₁, t₂} : Finset (V)) ({a, b, c} : Finset (V)) := by
    rw [Finset.disjoint_left]
    intro w hw hw'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw hw'
    rcases hw with rfl | rfl | rfl <;> rcases hw' with rfl | rfl | rfl <;>
      first
      | exact ne_ha rfl | exact ne_hb rfl | exact ne_hc rfl
      | exact ne_t1a rfl | exact ne_t1b rfl | exact ne_t1c rfl
      | exact ne_t2a rfl | exact ne_t2b rfl | exact ne_t2c rfl
  -- `e(P, N) = 0`: each star vertex has no neighbour in the triangle.
  have hPN_h : (G.neighborFinset h ∩ ({a, b, c} : Finset (V))).card = 0 := by
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro w hw
    rw [Finset.mem_inter, G.mem_neighborFinset] at hw
    obtain ⟨hadj, hmem⟩ := hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with rfl | rfl | rfl
    · exact hnha hadj
    · exact hnhb hadj
    · exact hnhc hadj
  have hPN_t1 : (G.neighborFinset t₁ ∩ ({a, b, c} : Finset (V))).card = 0 := by
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro w hw
    rw [Finset.mem_inter, G.mem_neighborFinset] at hw
    obtain ⟨hadj, hmem⟩ := hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with rfl | rfl | rfl
    · exact hnt1a hadj
    · exact hnt1b hadj
    · exact hnt1c hadj
  have hPN_t2 : (G.neighborFinset t₂ ∩ ({a, b, c} : Finset (V))).card = 0 := by
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
      (({h, t₁, t₂} : Finset (V)) ∪ {a, b, c})).card + 2 ≤ G.degree h := by
    have hsub : ({t₁, t₂} : Finset (V)) ⊆
        G.neighborFinset h ∩ (({h, t₁, t₂} : Finset (V)) ∪ {a, b, c}) := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rw [Finset.mem_inter, G.mem_neighborFinset]
      rcases hw with rfl | rfl
      · exact ⟨hAht1, by simp⟩
      · exact ⟨hAht2, by simp⟩
    have hge : 2 ≤ (G.neighborFinset h ∩
        (({h, t₁, t₂} : Finset (V)) ∪ {a, b, c})).card := by
      have h2 : ({t₁, t₂} : Finset (V)).card = 2 := by
        rw [Finset.card_insert_of_notMem (by simp [ne_t12]), Finset.card_singleton]
      calc 2 = ({t₁, t₂} : Finset (V)).card := h2.symm
        _ ≤ _ := Finset.card_le_card hsub
    have hsd := Finset.card_sdiff_add_card_inter (G.neighborFinset h)
      (({h, t₁, t₂} : Finset (V)) ∪ {a, b, c})
    rw [G.card_neighborFinset_eq_degree] at hsd
    omega
  have ht1_le : (G.neighborFinset t₁ \
      (({h, t₁, t₂} : Finset (V)) ∪ {a, b, c})).card + 1 ≤ G.degree t₁ := by
    have hsub : ({h} : Finset (V)) ⊆
        G.neighborFinset t₁ ∩ (({h, t₁, t₂} : Finset (V)) ∪ {a, b, c}) := by
      intro w hw
      rw [Finset.mem_singleton] at hw; subst hw
      rw [Finset.mem_inter, G.mem_neighborFinset]
      exact ⟨hAht1.symm, by simp⟩
    have hge : 1 ≤ (G.neighborFinset t₁ ∩
        (({h, t₁, t₂} : Finset (V)) ∪ {a, b, c})).card := by
      calc 1 = ({h} : Finset (V)).card := (Finset.card_singleton h).symm
        _ ≤ _ := Finset.card_le_card hsub
    have hsd := Finset.card_sdiff_add_card_inter (G.neighborFinset t₁)
      (({h, t₁, t₂} : Finset (V)) ∪ {a, b, c})
    rw [G.card_neighborFinset_eq_degree] at hsd
    omega
  have ht2_le : (G.neighborFinset t₂ \
      (({h, t₁, t₂} : Finset (V)) ∪ {a, b, c})).card + 1 ≤ G.degree t₂ := by
    have hsub : ({h} : Finset (V)) ⊆
        G.neighborFinset t₂ ∩ (({h, t₁, t₂} : Finset (V)) ∪ {a, b, c}) := by
      intro w hw
      rw [Finset.mem_singleton] at hw; subst hw
      rw [Finset.mem_inter, G.mem_neighborFinset]
      exact ⟨hAht2.symm, by simp⟩
    have hge : 1 ≤ (G.neighborFinset t₂ ∩
        (({h, t₁, t₂} : Finset (V)) ∪ {a, b, c})).card := by
      calc 1 = ({h} : Finset (V)).card := (Finset.card_singleton h).symm
        _ ≤ _ := Finset.card_le_card hsub
    have hsd := Finset.card_sdiff_add_card_inter (G.neighborFinset t₂)
      (({h, t₁, t₂} : Finset (V)) ∪ {a, b, c})
    rw [G.card_neighborFinset_eq_degree] at hsd
    omega
  -- Triangle-side leaks: each triangle hub keeps `2` edges inside `N`.
  have ha_le : (G.neighborFinset a \
      (({h, t₁, t₂} : Finset (V)) ∪ {a, b, c})).card + 2 ≤ G.degree a := by
    have hsub : ({b, c} : Finset (V)) ⊆
        G.neighborFinset a ∩ (({h, t₁, t₂} : Finset (V)) ∪ {a, b, c}) := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rw [Finset.mem_inter, G.mem_neighborFinset]
      rcases hw with rfl | rfl
      · exact ⟨hAab, by simp⟩
      · exact ⟨hAac, by simp⟩
    have hge : 2 ≤ (G.neighborFinset a ∩
        (({h, t₁, t₂} : Finset (V)) ∪ {a, b, c})).card := by
      have h2 : ({b, c} : Finset (V)).card = 2 := by
        rw [Finset.card_insert_of_notMem (by simp [ne_bc]), Finset.card_singleton]
      calc 2 = ({b, c} : Finset (V)).card := h2.symm
        _ ≤ _ := Finset.card_le_card hsub
    have hsd := Finset.card_sdiff_add_card_inter (G.neighborFinset a)
      (({h, t₁, t₂} : Finset (V)) ∪ {a, b, c})
    rw [G.card_neighborFinset_eq_degree] at hsd
    omega
  have hb_le : (G.neighborFinset b \
      (({h, t₁, t₂} : Finset (V)) ∪ {a, b, c})).card + 2 ≤ G.degree b := by
    have hsub : ({a, c} : Finset (V)) ⊆
        G.neighborFinset b ∩ (({h, t₁, t₂} : Finset (V)) ∪ {a, b, c}) := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rw [Finset.mem_inter, G.mem_neighborFinset]
      rcases hw with rfl | rfl
      · exact ⟨hAab.symm, by simp⟩
      · exact ⟨hAbc, by simp⟩
    have hge : 2 ≤ (G.neighborFinset b ∩
        (({h, t₁, t₂} : Finset (V)) ∪ {a, b, c})).card := by
      have h2 : ({a, c} : Finset (V)).card = 2 := by
        rw [Finset.card_insert_of_notMem (by simp [ne_ac]), Finset.card_singleton]
      calc 2 = ({a, c} : Finset (V)).card := h2.symm
        _ ≤ _ := Finset.card_le_card hsub
    have hsd := Finset.card_sdiff_add_card_inter (G.neighborFinset b)
      (({h, t₁, t₂} : Finset (V)) ∪ {a, b, c})
    rw [G.card_neighborFinset_eq_degree] at hsd
    omega
  have hc_le : (G.neighborFinset c \
      (({h, t₁, t₂} : Finset (V)) ∪ {a, b, c})).card + 2 ≤ G.degree c := by
    have hsub : ({a, b} : Finset (V)) ⊆
        G.neighborFinset c ∩ (({h, t₁, t₂} : Finset (V)) ∪ {a, b, c}) := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rw [Finset.mem_inter, G.mem_neighborFinset]
      rcases hw with rfl | rfl
      · exact ⟨hAac.symm, by simp⟩
      · exact ⟨hAbc.symm, by simp⟩
    have hge : 2 ≤ (G.neighborFinset c ∩
        (({h, t₁, t₂} : Finset (V)) ∪ {a, b, c})).card := by
      have h2 : ({a, b} : Finset (V)).card = 2 := by
        rw [Finset.card_insert_of_notMem (by simp [ne_ab]), Finset.card_singleton]
      calc 2 = ({a, b} : Finset (V)).card := h2.symm
        _ ≤ _ := Finset.card_le_card hsub
    have hsd := Finset.card_sdiff_add_card_inter (G.neighborFinset c)
      (({h, t₁, t₂} : Finset (V)) ∪ {a, b, c})
    rw [G.card_neighborFinset_eq_degree] at hsd
    omega
  refine ⟨({h, t₁, t₂} : Finset (V)), ({a, b, c} : Finset (V)), hdisjPN,
    (by rw [hPcard, hNcard]), (by rw [hPcard]; norm_num), ?_⟩
  have e1 : ∑ p ∈ ({h, t₁, t₂} : Finset (V)),
      (G.neighborFinset p ∩ ({a, b, c} : Finset (V))).card
      = (G.neighborFinset h ∩ ({a, b, c} : Finset (V))).card
        + (G.neighborFinset t₁ ∩ ({a, b, c} : Finset (V))).card
        + (G.neighborFinset t₂ ∩ ({a, b, c} : Finset (V))).card := by
    rw [Finset.sum_insert (by simp [ne_ht1, ne_ht2]),
        Finset.sum_insert (by simp [ne_t12]), Finset.sum_singleton]
    ring
  have e2 : ∑ p ∈ ({h, t₁, t₂} : Finset (V)),
      (G.neighborFinset p \ (({h, t₁, t₂} : Finset (V)) ∪ {a, b, c})).card
      = (G.neighborFinset h \ (({h, t₁, t₂} : Finset (V)) ∪ {a, b, c})).card
        + (G.neighborFinset t₁ \ (({h, t₁, t₂} : Finset (V)) ∪ {a, b, c})).card
        + (G.neighborFinset t₂ \ (({h, t₁, t₂} : Finset (V)) ∪ {a, b, c})).card := by
    rw [Finset.sum_insert (by simp [ne_ht1, ne_ht2]),
        Finset.sum_insert (by simp [ne_t12]), Finset.sum_singleton]
    ring
  have e3 : ∑ q ∈ ({a, b, c} : Finset (V)),
      (G.neighborFinset q \ (({h, t₁, t₂} : Finset (V)) ∪ {a, b, c})).card
      = (G.neighborFinset a \ (({h, t₁, t₂} : Finset (V)) ∪ {a, b, c})).card
        + (G.neighborFinset b \ (({h, t₁, t₂} : Finset (V)) ∪ {a, b, c})).card
        + (G.neighborFinset c \ (({h, t₁, t₂} : Finset (V)) ∪ {a, b, c})).card := by
    rw [Finset.sum_insert (by simp [ne_ab, ne_ac]),
        Finset.sum_insert (by simp [ne_bc]), Finset.sum_singleton]
    ring
  rw [e1, e2, e3, hPcard, hPN_h, hPN_t1, hPN_t2]
  omega

end ACMax
