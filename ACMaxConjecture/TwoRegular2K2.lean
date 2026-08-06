import ACMaxConjecture.Base

/-!
# A 2-regular triangle-free graph on `≥ 6` vertices has an induced `2K₂`

If every vertex of `s` has exactly two neighbours inside `s`, `s` induces a triangle-free graph,
and `|s| ≥ 6`, then `s` contains an induced `2K₂` (two disjoint edges with no edges between them).

The induced subgraph on `s` is a disjoint union of cycles, each of length `≥ 4` (triangle-free);
with `≥ 6` vertices it is either a single cycle `C_n` (`n ≥ 6`), which has two "opposite" edges
forming an induced `2K₂`, or has `≥ 2` cycles, giving an induced `2K₂` across components.
-/

namespace ACMax

open scoped Classical

/-- A 2-regular (within `s`) triangle-free graph on `≥ 6` vertices has an induced `2K₂`. -/
theorem exists_2K2_of_two_regular_triangleFree {V : Type*} [Fintype V] (G : SimpleGraph V)
    (s : Finset V)
    (htri : ∀ a ∈ s, ∀ b ∈ s, ∀ c ∈ s, ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj a c))
    (hreg : ∀ v ∈ s, (G.neighborFinset v ∩ s).card = 2)
    (hcard : 6 ≤ s.card) :
    ∃ a ∈ s, ∃ b ∈ s, ∃ c ∈ s, ∃ d ∈ s,
      ({a, b, c, d} : Finset V).card = 4 ∧
      G.Adj a b ∧ G.Adj c d ∧
      ¬ G.Adj a c ∧ ¬ G.Adj a d ∧ ¬ G.Adj b c ∧ ¬ G.Adj b d := by
  classical
  -- Card of an explicit 4-element set with pairwise-distinct entries.
  have card4 : ∀ p q r u : V, p ≠ q → p ≠ r → p ≠ u → q ≠ r → q ≠ u → r ≠ u →
      ({p, q, r, u} : Finset V).card = 4 := by
    intro p q r u hpq hpr hpu hqr hqu hru
    rw [Finset.card_insert_of_notMem (by simp [hpq, hpr, hpu]),
        Finset.card_insert_of_notMem (by simp [hqr, hqu]),
        Finset.card_insert_of_notMem (by simp [hru]), Finset.card_singleton]
  -- Card of an explicit 5-element set with pairwise-distinct entries.
  have card5 : ∀ p q r u w : V, p ≠ q → p ≠ r → p ≠ u → p ≠ w →
      q ≠ r → q ≠ u → q ≠ w → r ≠ u → r ≠ w → u ≠ w →
      ({p, q, r, u, w} : Finset V).card = 5 := by
    intro p q r u w hpq hpr hpu hpw hqr hqu hqw hru hrw huw
    rw [Finset.card_insert_of_notMem (by simp [hpq, hpr, hpu, hpw]),
        Finset.card_insert_of_notMem (by simp [hqr, hqu, hqw]),
        Finset.card_insert_of_notMem (by simp [hru, hrw]),
        Finset.card_insert_of_notMem (by simp [huw]), Finset.card_singleton]
  -- Extract the two `s`-neighbours of a vertex, with the triangle-free non-edge and the
  -- "only neighbours" characterisation.
  have getNbr : ∀ v ∈ s, ∃ x y : V, x ≠ y ∧ x ∈ s ∧ y ∈ s ∧
      G.Adj v x ∧ G.Adj v y ∧ ¬ G.Adj x y ∧
      (∀ z ∈ s, G.Adj v z → z = x ∨ z = y) := by
    intro v hv
    obtain ⟨x, y, hxy, hxyeq⟩ := Finset.card_eq_two.mp (hreg v hv)
    have hmem : ∀ z, z ∈ G.neighborFinset v ∩ s ↔ G.Adj v z ∧ z ∈ s := by
      intro z; rw [Finset.mem_inter, G.mem_neighborFinset]
    have hx : G.Adj v x ∧ x ∈ s := (hmem x).mp (by rw [hxyeq]; simp)
    have hy : G.Adj v y ∧ y ∈ s := (hmem y).mp (by rw [hxyeq]; simp)
    refine ⟨x, y, hxy, hx.2, hy.2, hx.1, hy.1, ?_, ?_⟩
    · exact fun h => htri v hv x hx.2 y hy.2 ⟨hx.1, h, hy.1⟩
    · intro z hz hadj
      have hin : z ∈ G.neighborFinset v ∩ s := (hmem z).mpr ⟨hadj, hz⟩
      rw [hxyeq, Finset.mem_insert, Finset.mem_singleton] at hin
      exact hin
  -- Two distinct `s`-neighbours of `v` are ALL of `v`'s `s`-neighbours.
  have charFromTwo : ∀ v ∈ s, ∀ p q : V, p ≠ q → p ∈ s → q ∈ s →
      G.Adj v p → G.Adj v q → ∀ z ∈ s, G.Adj v z → z = p ∨ z = q := by
    intro v hv p q hpq hps hqs hvp hvq z hzs hvz
    have hmem : ∀ w, w ∈ G.neighborFinset v ∩ s ↔ G.Adj v w ∧ w ∈ s := by
      intro w; rw [Finset.mem_inter, G.mem_neighborFinset]
    have hsub : ({p, q} : Finset V) ⊆ G.neighborFinset v ∩ s := by
      intro w hw
      rw [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl
      · exact (hmem w).mpr ⟨hvp, hps⟩
      · exact (hmem w).mpr ⟨hvq, hqs⟩
    have hcard2 : ({p, q} : Finset V).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simp [hpq]), Finset.card_singleton]
    have heqset : ({p, q} : Finset V) = G.neighborFinset v ∩ s :=
      Finset.eq_of_subset_of_card_le hsub (le_of_eq (by rw [hreg v hv, hcard2]))
    have hin : z ∈ G.neighborFinset v ∩ s := (hmem z).mpr ⟨hvz, hzs⟩
    rw [← heqset, Finset.mem_insert, Finset.mem_singleton] at hin
    exact hin
  -- Given a known neighbour `u` of `v`, produce the OTHER neighbour `w`.
  have otherNbr : ∀ v ∈ s, ∀ u ∈ s, G.Adj v u →
      ∃ w : V, w ≠ u ∧ w ∈ s ∧ G.Adj v w ∧ ¬ G.Adj u w ∧
        (∀ z ∈ s, G.Adj v z → z = u ∨ z = w) := by
    intro v hv u hu hvu
    obtain ⟨x, y, hxy, hxs, hys, hvx, hvy, hnxy, hchar⟩ := getNbr v hv
    rcases hchar u hu hvu with hux | huy
    · refine ⟨y, ?_, hys, hvy, ?_, ?_⟩
      · rw [hux]; exact hxy.symm
      · rw [hux]; exact hnxy
      · intro z hz hvz
        rcases hchar z hz hvz with h | h
        · exact Or.inl (h.trans hux.symm)
        · exact Or.inr h
    · refine ⟨x, ?_, hxs, hvx, ?_, ?_⟩
      · rw [huy]; exact hxy
      · rw [huy]; exact fun h => hnxy h.symm
      · intro z hz hvz
        rcases hchar z hz hvz with h | h
        · exact Or.inr h
        · exact Or.inl (h.trans huy.symm)
  -- "Escape from a saturated set": no edge leaves `T`, `|T| < |s|`, plus an edge inside `T`,
  -- gives an induced `2K₂` (the inside edge and an edge touching `s \ T`).
  have escape : ∀ T : Finset V, T ⊆ s → T.card < s.card →
      (∀ t ∈ T, ∀ z ∈ s, G.Adj t z → z ∈ T) →
      ∀ p ∈ T, ∀ q ∈ T, G.Adj p q →
      ∃ a ∈ s, ∃ b ∈ s, ∃ c ∈ s, ∃ d ∈ s,
        ({a, b, c, d} : Finset V).card = 4 ∧
        G.Adj a b ∧ G.Adj c d ∧
        ¬ G.Adj a c ∧ ¬ G.Adj a d ∧ ¬ G.Adj b c ∧ ¬ G.Adj b d := by
    intro T hTsub hTcard hTclosed p hp q hq hpadj
    have hwne : (s \ T).Nonempty := by
      rw [← Finset.card_pos, Finset.card_sdiff, Finset.inter_eq_left.mpr hTsub]; omega
    obtain ⟨w, hw⟩ := hwne
    rw [Finset.mem_sdiff] at hw
    obtain ⟨hws, hwT⟩ := hw
    obtain ⟨w₁, _, _, hw1s, _, hww1, _, _, _⟩ := getNbr w hws
    have hw1T : w₁ ∉ T := fun hc => hwT (hTclosed w₁ hc w hws hww1.symm)
    have hpw : ¬ G.Adj p w := fun h => hwT (hTclosed p hp w hws h)
    have hpw1 : ¬ G.Adj p w₁ := fun h => hw1T (hTclosed p hp w₁ hw1s h)
    have hqw : ¬ G.Adj q w := fun h => hwT (hTclosed q hq w hws h)
    have hqw1 : ¬ G.Adj q w₁ := fun h => hw1T (hTclosed q hq w₁ hw1s h)
    have hpwne : p ≠ w := fun h => hwT (h ▸ hp)
    have hpw1ne : p ≠ w₁ := fun h => hw1T (h ▸ hp)
    have hqwne : q ≠ w := fun h => hwT (h ▸ hq)
    have hqw1ne : q ≠ w₁ := fun h => hw1T (h ▸ hq)
    exact ⟨p, hTsub hp, q, hTsub hq, w, hws, w₁, hw1s,
      card4 p q w w₁ hpadj.ne hpwne hpw1ne hqwne hqw1ne hww1.ne,
      hpadj, hww1, hpw, hpw1, hqw, hqw1⟩
  -- Pick a vertex `v` and its two `s`-neighbours `a, b`.
  obtain ⟨v, hv⟩ : s.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨a, b, hab, has, hbs, hva, hvb, hnab, hvchar⟩ := getNbr v hv
  obtain ⟨a₂, ha₂v, ha₂s, haa₂, _, hachar⟩ := otherNbr a has v hv hva.symm
  obtain ⟨b₂, hb₂v, hb₂s, hbb₂, _, hbchar⟩ := otherNbr b hbs v hv hvb.symm
  have ha₂b : a₂ ≠ b := fun h => hnab (h ▸ haa₂)
  have hb₂a : b₂ ≠ a := fun h => hnab ((h ▸ hbb₂).symm)
  have hvane : v ≠ a := hva.ne
  have hvbne : v ≠ b := hvb.ne
  by_cases heq : a₂ = b₂
  · -- Case 1: `a₂ = b₂`.  `{v, a, b, a₂}` is a closed 4-cycle; escape.
    have hba₂adj : G.Adj b a₂ := by rw [heq]; exact hbb₂
    have hba₂ : b ≠ a₂ := hba₂adj.ne
    have ha₂char : ∀ z ∈ s, G.Adj a₂ z → z = a ∨ z = b :=
      charFromTwo a₂ ha₂s a b hab has hbs haa₂.symm hba₂adj.symm
    refine escape ({v, a, b, a₂} : Finset V) ?_ ?_ ?_ v (by simp) a (by simp) hva
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact hv
      · exact has
      · exact hbs
      · exact ha₂s
    · rw [card4 v a b a₂ hvane hvbne (Ne.symm ha₂v) hab haa₂.ne hba₂]
      omega
    · intro t ht z hz hadj
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl | rfl
      · rcases hvchar z hz hadj with rfl | rfl <;> simp
      · rcases hachar z hz hadj with rfl | rfl <;> simp
      · rcases hbchar z hz hadj with rfl | rfl
        · simp
        · rw [← heq]; simp
      · rcases ha₂char z hz hadj with rfl | rfl <;> simp
  · -- Case 2: `a₂ ≠ b₂`.
    by_cases h2 : G.Adj a₂ b
    · -- 2a: `a₂ ~ b` forces `b₂ = a₂`, contradicting `a₂ ≠ b₂`.
      rcases hbchar a₂ ha₂s h2.symm with h | h
      · exact absurd h ha₂v
      · exact absurd h heq
    · by_cases h3 : G.Adj a₂ b₂
      · -- 2c: `{v, a, a₂, b₂, b}` is a closed 5-cycle; escape.
        have ha₂char' : ∀ z ∈ s, G.Adj a₂ z → z = a ∨ z = b₂ :=
          charFromTwo a₂ ha₂s a b₂ (Ne.symm hb₂a) has hb₂s haa₂.symm h3
        have hb₂char : ∀ z ∈ s, G.Adj b₂ z → z = b ∨ z = a₂ :=
          charFromTwo b₂ hb₂s b a₂ (Ne.symm ha₂b) hbs ha₂s hbb₂.symm h3.symm
        refine escape ({v, a, a₂, b₂, b} : Finset V) ?_ ?_ ?_ v (by simp) a (by simp) hva
        · intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl | rfl | rfl | rfl
          · exact hv
          · exact has
          · exact ha₂s
          · exact hb₂s
          · exact hbs
        · rw [card5 v a a₂ b₂ b hvane (Ne.symm ha₂v) (Ne.symm hb₂v) hvbne haa₂.ne
              (Ne.symm hb₂a) hab heq ha₂b (Ne.symm hbb₂.ne)]
          omega
        · intro t ht z hz hadj
          simp only [Finset.mem_insert, Finset.mem_singleton] at ht
          rcases ht with rfl | rfl | rfl | rfl | rfl
          · rcases hvchar z hz hadj with rfl | rfl <;> simp
          · rcases hachar z hz hadj with rfl | rfl <;> simp
          · rcases ha₂char' z hz hadj with rfl | rfl <;> simp
          · rcases hb₂char z hz hadj with rfl | rfl <;> simp
          · rcases hbchar z hz hadj with rfl | rfl <;> simp
      · -- 2b: `{a, a₂}` and `{b, b₂}` form an induced `2K₂` directly.
        have hnab₂ : ¬ G.Adj a b₂ := by
          intro h
          rcases hachar b₂ hb₂s h with hbv | hba₂
          · exact hb₂v hbv
          · exact heq hba₂.symm
        exact ⟨a, has, a₂, ha₂s, b, hbs, b₂, hb₂s,
          card4 a a₂ b b₂ haa₂.ne hab (Ne.symm hb₂a) ha₂b heq hbb₂.ne,
          haa₂, hbb₂, hnab, hnab₂, h2, h3⟩

end ACMax
