import ACMaxConjecture.Base
import ACMaxConjecture.Spectral.AlgConn

/-!
# Every cubic graph on 8 vertices has a sparse balanced cut

For a 3-regular graph on `Fin 8`, there is a 4-vertex set `A` whose cut to the
complement has at most `4` edges (equivalently, `A` induces at least `4` edges, since
for a cubic graph `cut(A) = 12 − 2·e(A)`).

Proof: pick a vertex `v` with neighbours `{a,b,c}`. If two neighbours are adjacent,
the closed neighbourhood `{v,a,b,c}` induces the three star edges plus that edge
(`≥ 4`). Otherwise `{a,b,c}` is independent, so the `6` edges from `{a,b,c}` to the
other `4` vertices force (pigeonhole) some outside vertex `d` adjacent to two of them,
giving the 4-cycle `v–a–d–b` and the dense set `{v,a,b,d}`.
-/

namespace ACMax

open scoped Classical

/-- A 3-regular graph on `Fin 8` has a balanced 4-set with cut at most `4`. -/
theorem cubic8_balanced_cut_exists (G : SimpleGraph (Fin 8))
    (hreg : ∀ v : Fin 8, G.degree v = 3) :
    ∃ A : Finset (Fin 8),
      A.card = 4 ∧ 2 * (∑ a ∈ A, (G.neighborFinset a \ A).card) ≤ 8 := by
  classical
  -- Central reduction: if `A` (a 4-set) induces at least `8 = 2·e(A)` internal
  -- incidences, then its cut has at most `4` edges, so `2·cut ≤ 8`.
  have key : ∀ A : Finset (Fin 8), A.card = 4 →
      8 ≤ ∑ a ∈ A, (G.neighborFinset a ∩ A).card →
      2 * (∑ a ∈ A, (G.neighborFinset a \ A).card) ≤ 8 := by
    intro A hA hge
    have hsum : (∑ a ∈ A, (G.neighborFinset a \ A).card)
        + (∑ a ∈ A, (G.neighborFinset a ∩ A).card) = 12 := by
      rw [← Finset.sum_add_distrib]
      have hterm : ∀ a ∈ A,
          (G.neighborFinset a \ A).card + (G.neighborFinset a ∩ A).card = 3 := by
        intro a _
        rw [Finset.card_sdiff_add_card_inter, G.card_neighborFinset_eq_degree, hreg a]
      rw [Finset.sum_congr rfl hterm, Finset.sum_const, hA]
      rfl
    omega
  -- Expand a sum over an explicit 4-element set.
  have expand : ∀ (w x y z : Fin 8) (f : Fin 8 → ℕ),
      w ≠ x → w ≠ y → w ≠ z → x ≠ y → x ≠ z → y ≠ z →
      ∑ a ∈ ({w, x, y, z} : Finset (Fin 8)), f a = f w + f x + f y + f z := by
    intro w x y z f hwx hwy hwz hxy hxz hyz
    rw [Finset.sum_insert (by simp [hwx, hwy, hwz]),
        Finset.sum_insert (by simp [hxy, hxz]),
        Finset.sum_insert (by simp [hyz]), Finset.sum_singleton]
    ring
  -- Card of an explicit 4-element set with distinct entries.
  have card4 : ∀ (w x y z : Fin 8),
      w ≠ x → w ≠ y → w ≠ z → x ≠ y → x ≠ z → y ≠ z →
      ({w, x, y, z} : Finset (Fin 8)).card = 4 := by
    intro w x y z hwx hwy hwz hxy hxz hyz
    rw [Finset.card_insert_of_notMem (by simp [hwx, hwy, hwz]),
        Finset.card_insert_of_notMem (by simp [hxy, hxz]),
        Finset.card_insert_of_notMem (by simp [hyz]), Finset.card_singleton]
  -- A subset of `A` whose members are all neighbours of `p` lower-bounds the term.
  have inter_ge : ∀ (p : Fin 8) (A S : Finset (Fin 8)), S ⊆ A →
      (∀ s ∈ S, G.Adj p s) → S.card ≤ (G.neighborFinset p ∩ A).card := by
    intro p A S hSA hAdj
    refine Finset.card_le_card (Finset.subset_inter (fun s hs => ?_) hSA)
    exact (G.mem_neighborFinset p s).mpr (hAdj s hs)
  -- A term lower bound from an explicit `k`-element neighbour subset.
  have termAdj : ∀ (x : Fin 8) (A S : Finset (Fin 8)) (k : ℕ),
      S.card = k → S ⊆ A → (∀ s ∈ S, G.Adj x s) →
      k ≤ (G.neighborFinset x ∩ A).card := by
    intro x A S k hk hSA hAdj
    rw [← hk]; exact inter_ge x A S hSA hAdj
  -- Decompose the neighbourhood of vertex `0`.
  set v : Fin 8 := 0 with hv
  have hv3 : (G.neighborFinset v).card = 3 := by
    rw [G.card_neighborFinset_eq_degree]; exact hreg v
  obtain ⟨a, b, c, hab, hac, hbc, hN⟩ := Finset.card_eq_three.mp hv3
  have hva : G.Adj v a := (G.mem_neighborFinset v a).mp (by rw [hN]; simp)
  have hvb : G.Adj v b := (G.mem_neighborFinset v b).mp (by rw [hN]; simp)
  have hvc : G.Adj v c := (G.mem_neighborFinset v c).mp (by rw [hN]; simp)
  have hva' : v ≠ a := hva.ne
  have hvb' : v ≠ b := hvb.ne
  have hvc' : v ≠ c := hvc.ne
  -- Case 1 bound: an adjacent pair `p,q` among the neighbours yields a dense 4-set.
  have case1bound : ∀ (p q r : Fin 8), G.Adj v p → G.Adj v q → G.Adj v r →
      G.Adj p q → p ≠ q → p ≠ r → q ≠ r → v ≠ p → v ≠ q → v ≠ r →
      8 ≤ ∑ x ∈ ({v, p, q, r} : Finset (Fin 8)),
            (G.neighborFinset x ∩ {v, p, q, r}).card := by
    intro p q r hvp hvq hvr hpq hpq' hpr hqr hvp' hvq' hvr'
    rw [expand v p q r _ hvp' hvq' hvr' hpq' hpr hqr]
    have tv : 3 ≤ (G.neighborFinset v ∩ {v, p, q, r}).card := by
      refine termAdj v {v, p, q, r} {p, q, r} 3 ?_ (by simp) ?_
      · rw [Finset.card_insert_of_notMem (by simp [hpq', hpr]), Finset.card_pair hqr]
      · intro s hs
        simp only [Finset.mem_insert, Finset.mem_singleton] at hs
        rcases hs with rfl | rfl | rfl
        · exact hvp
        · exact hvq
        · exact hvr
    have tp : 2 ≤ (G.neighborFinset p ∩ {v, p, q, r}).card := by
      refine termAdj p {v, p, q, r} {v, q} 2 (Finset.card_pair hvq') (by simp) ?_
      intro s hs
      simp only [Finset.mem_insert, Finset.mem_singleton] at hs
      rcases hs with rfl | rfl
      · exact hvp.symm
      · exact hpq
    have tq : 2 ≤ (G.neighborFinset q ∩ {v, p, q, r}).card := by
      refine termAdj q {v, p, q, r} {v, p} 2 (Finset.card_pair hvp') (by simp) ?_
      intro s hs
      simp only [Finset.mem_insert, Finset.mem_singleton] at hs
      rcases hs with rfl | rfl
      · exact hvq.symm
      · exact hpq.symm
    have tr : 1 ≤ (G.neighborFinset r ∩ {v, p, q, r}).card := by
      refine termAdj r {v, p, q, r} {v} 1 (Finset.card_singleton v) (by simp) ?_
      intro s hs
      simp only [Finset.mem_singleton] at hs
      subst hs
      exact hvr.symm
    omega
  -- Dispatch on whether some pair of neighbours is adjacent.
  by_cases hab2 : G.Adj a b
  · exact ⟨{v, a, b, c}, card4 v a b c hva' hvb' hvc' hab hac hbc,
      key _ (card4 v a b c hva' hvb' hvc' hab hac hbc)
        (case1bound a b c hva hvb hvc hab2 hab hac hbc hva' hvb' hvc')⟩
  by_cases hac2 : G.Adj a c
  · exact ⟨{v, a, c, b}, card4 v a c b hva' hvc' hvb' hac hab (Ne.symm hbc),
      key _ (card4 v a c b hva' hvc' hvb' hac hab (Ne.symm hbc))
        (case1bound a c b hva hvc hvb hac2 hac hab (Ne.symm hbc) hva' hvc' hvb')⟩
  by_cases hbc2 : G.Adj b c
  · exact ⟨{v, b, c, a}, card4 v b c a hvb' hvc' hva' hbc (Ne.symm hab) (Ne.symm hac),
      key _ (card4 v b c a hvb' hvc' hva' hbc (Ne.symm hab) (Ne.symm hac))
        (case1bound b c a hvb hvc hva hbc2 hbc (Ne.symm hab) (Ne.symm hac) hvb' hvc' hva')⟩
  -- Case 2: `a, b, c` are pairwise non-adjacent.
  set Out : Finset (Fin 8) := Finset.univ \ ({v, a, b, c} : Finset (Fin 8)) with hOut
  have hOutcard : Out.card = 4 := by
    rw [hOut, Finset.card_sdiff, Finset.inter_univ,
        card4 v a b c hva' hvb' hvc' hab hac hbc]
    simp
  have hOutinter : ∀ s : Finset (Fin 8),
      s ∩ Out = s \ ({v, a, b, c} : Finset (Fin 8)) := by
    intro s
    rw [hOut]
    ext y
    simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_univ, true_and]
  -- Each of `a, b, c` has exactly two neighbours outside `{v, a, b, c}`.
  have outdeg : ∀ x : Fin 8, G.Adj x v →
      (∀ y, y ∈ ({a, b, c} : Finset (Fin 8)) → ¬ G.Adj x y) →
      (G.neighborFinset x ∩ Out).card = 2 := by
    intro x hxv hxnon
    have hvinter : G.neighborFinset x ∩ ({v, a, b, c} : Finset (Fin 8)) = {v} := by
      ext y
      simp only [Finset.mem_inter, G.mem_neighborFinset, Finset.mem_insert,
        Finset.mem_singleton]
      constructor
      · rintro ⟨hxy, rfl | rfl | rfl | rfl⟩
        · rfl
        · exact absurd hxy (hxnon _ (by simp))
        · exact absurd hxy (hxnon _ (by simp))
        · exact absurd hxy (hxnon _ (by simp))
      · rintro rfl
        exact ⟨hxv, Or.inl rfl⟩
    have h2 : (G.neighborFinset x ∩ ({v, a, b, c} : Finset (Fin 8))).card
        + (G.neighborFinset x ∩ Out).card = 3 := by
      rw [hOutinter, Finset.card_inter_add_card_sdiff,
          G.card_neighborFinset_eq_degree, hreg x]
    rw [hvinter, Finset.card_singleton] at h2
    omega
  have ha2 : (G.neighborFinset a ∩ Out).card = 2 := by
    refine outdeg a hva.symm ?_
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl
    · exact G.irrefl
    · exact hab2
    · exact hac2
  have hb2 : (G.neighborFinset b ∩ Out).card = 2 := by
    refine outdeg b hvb.symm ?_
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl
    · exact fun h => hab2 h.symm
    · exact G.irrefl
    · exact hbc2
  have hc2 : (G.neighborFinset c ∩ Out).card = 2 := by
    refine outdeg c hvc.symm ?_
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl
    · exact fun h => hac2 h.symm
    · exact fun h => hbc2 h.symm
    · exact G.irrefl
  -- Count edges between `{a,b,c}` and `Out` as a sum of indicators.
  have indic : ∀ (s : Finset (Fin 8)) (w : Fin 8),
      (G.neighborFinset w ∩ s).card = ∑ y ∈ s, (if G.Adj w y then (1 : ℕ) else 0) := by
    intro s w
    rw [Finset.inter_comm, ← Finset.filter_mem_eq_inter, Finset.card_filter]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    simp only [G.mem_neighborFinset]
  have hcount : ∑ d ∈ Out,
      (G.neighborFinset d ∩ ({a, b, c} : Finset (Fin 8))).card = 6 := by
    have e2 : ∀ x ∈ ({a, b, c} : Finset (Fin 8)),
        ∑ d ∈ Out, (if G.Adj d x then (1 : ℕ) else 0)
        = (G.neighborFinset x ∩ Out).card := by
      intro x _
      rw [indic Out x]
      refine Finset.sum_congr rfl (fun d _ => ?_)
      by_cases h : G.Adj x d
      · rw [if_pos h.symm, if_pos h]
      · rw [if_neg (fun h' => h h'.symm), if_neg h]
    rw [Finset.sum_congr rfl (fun d _ => indic ({a, b, c} : Finset (Fin 8)) d),
        Finset.sum_comm, Finset.sum_congr rfl e2,
        Finset.sum_insert (by simp [hab, hac]), Finset.sum_insert (by simp [hbc]),
        Finset.sum_singleton, ha2, hb2, hc2]
    rfl
  -- Pigeonhole: some outside vertex is adjacent to two of `{a,b,c}`.
  have hpigeon : ∃ d ∈ Out,
      2 ≤ (G.neighborFinset d ∩ ({a, b, c} : Finset (Fin 8))).card := by
    by_contra hcon
    simp only [not_exists, not_and, not_le] at hcon
    have hle : ∑ d ∈ Out, (G.neighborFinset d ∩ ({a, b, c} : Finset (Fin 8))).card
        ≤ ∑ _d ∈ Out, 1 := by
      refine Finset.sum_le_sum (fun d hd => ?_)
      have := hcon d hd
      omega
    rw [Finset.sum_const, hOutcard, smul_eq_mul] at hle
    omega
  obtain ⟨d, hd, hdcard⟩ := hpigeon
  obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp (by omega :
    1 < (G.neighborFinset d ∩ ({a, b, c} : Finset (Fin 8))).card)
  have hp_tri : p ∈ ({a, b, c} : Finset (Fin 8)) := (Finset.mem_inter.mp hp).2
  have hq_tri : q ∈ ({a, b, c} : Finset (Fin 8)) := (Finset.mem_inter.mp hq).2
  have hdp : G.Adj d p := (G.mem_neighborFinset d p).mp (Finset.mem_inter.mp hp).1
  have hdq : G.Adj d q := (G.mem_neighborFinset d q).mp (Finset.mem_inter.mp hq).1
  have hvp_adj : G.Adj v p := (G.mem_neighborFinset v p).mp (by rw [hN]; exact hp_tri)
  have hvq_adj : G.Adj v q := (G.mem_neighborFinset v q).mp (by rw [hN]; exact hq_tri)
  have hdnot : d ∉ ({v, a, b, c} : Finset (Fin 8)) := by
    have h := hd
    rw [hOut, Finset.mem_sdiff] at h
    exact h.2
  have hvp' : v ≠ p := hvp_adj.ne
  have hvq' : v ≠ q := hvq_adj.ne
  have hvd' : v ≠ d := by rintro rfl; exact hdnot (by simp)
  have hpd' : p ≠ d := by rintro rfl; exact hdnot (Finset.mem_insert_of_mem hp_tri)
  have hqd' : q ≠ d := by rintro rfl; exact hdnot (Finset.mem_insert_of_mem hq_tri)
  refine ⟨{v, p, q, d}, card4 v p q d hvp' hvq' hvd' hpq hpd' hqd',
    key _ (card4 v p q d hvp' hvq' hvd' hpq hpd' hqd') ?_⟩
  rw [expand v p q d _ hvp' hvq' hvd' hpq hpd' hqd']
  have tv : 2 ≤ (G.neighborFinset v ∩ {v, p, q, d}).card := by
    refine termAdj v {v, p, q, d} {p, q} 2 (Finset.card_pair hpq)
      (by simp [Finset.insert_subset_iff]) ?_
    intro s hs
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl
    · exact hvp_adj
    · exact hvq_adj
  have tp : 2 ≤ (G.neighborFinset p ∩ {v, p, q, d}).card := by
    refine termAdj p {v, p, q, d} {v, d} 2 (Finset.card_pair hvd') (by simp) ?_
    intro s hs
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl
    · exact hvp_adj.symm
    · exact hdp.symm
  have tq : 2 ≤ (G.neighborFinset q ∩ {v, p, q, d}).card := by
    refine termAdj q {v, p, q, d} {v, d} 2 (Finset.card_pair hvd') (by simp) ?_
    intro s hs
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl
    · exact hvq_adj.symm
    · exact hdq.symm
  have td : 2 ≤ (G.neighborFinset d ∩ {v, p, q, d}).card := by
    refine termAdj d {v, p, q, d} {p, q} 2 (Finset.card_pair hpq)
      (by simp [Finset.insert_subset_iff]) ?_
    intro s hs
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl
    · exact hdp
    · exact hdq
  omega

end ACMax
