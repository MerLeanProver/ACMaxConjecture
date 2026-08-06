import ACMaxConjecture.Base

/-!
# Structural core lemmas for the `n = 12` twin certificate

This file isolates the combinatorial heart of the `n = 12` ACMAX residual.  In that regime the
graph has degree sequence `[4,4,4,4,3⁸]`: four degree-4 *hubs* and eight degree-3 vertices `D`,
with `M = G[D]` triangle-free, `C₄`-free, `2K₂`-free of max-degree `≤ 3` and `e(M) ∈ {4,5}`.

We prove:
* `M_edges_joined` — two disjoint `M`-edges must be joined (`2K₂`-freeness, contrapositive);
* `eM_five_extract` — in the `e(M)=5` regime with an in-`M`-degree-3 vertex, `M` is the double
  star, and we extract the twin certificate;
* `eM_five_C5_no_residual` / `eM_four_no_residual` — the `C₅` and `e(M)=4` regimes are excluded.
-/

namespace ACMax

open scoped Classical

namespace N12

/-- **`2K₂`-freeness, joined form.**  Two disjoint `M`-edges `a–b`, `c–d` (degree-3 vertices,
four distinct) must have a crossing edge. -/
theorem M_edges_joined (G : SimpleGraph (Fin 12))
    (h2k2 : ¬∃ a b c d : Fin 12, ({a, b, c, d} : Finset (Fin 12)).card = 4 ∧
      G.degree a = 3 ∧ G.degree b = 3 ∧ G.degree c = 3 ∧ G.degree d = 3 ∧
      G.Adj a b ∧ G.Adj c d ∧ ¬G.Adj a c ∧ ¬G.Adj a d ∧ ¬G.Adj b c ∧ ¬G.Adj b d)
    (a b c d : Fin 12) (hcard : ({a, b, c, d} : Finset (Fin 12)).card = 4)
    (ha : G.degree a = 3) (hb : G.degree b = 3) (hc : G.degree c = 3) (hd : G.degree d = 3)
    (hab : G.Adj a b) (hcd : G.Adj c d) :
    G.Adj a c ∨ G.Adj a d ∨ G.Adj b c ∨ G.Adj b d := by
  by_contra h
  push Not at h
  obtain ⟨hac, had, hbc, hbd⟩ := h
  exact h2k2 ⟨a, b, c, d, hcard, ha, hb, hc, hd, hab, hcd, hac, had, hbc, hbd⟩

/-- **Good `C₄` witness.**  An induced 4-cycle `a–b–c–d–a` whose degree-sum is `≤ 13`
contradicts `hC4`. -/
theorem good_C4_of_witnesses (G : SimpleGraph (Fin 12))
    (hC4 : ¬∃ a b c d : Fin 12, ({a, b, c, d} : Finset (Fin 12)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 13)
    (a b c d : Fin 12) (hcard : ({a, b, c, d} : Finset (Fin 12)).card = 4)
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) (hda : G.Adj d a)
    (hac : ¬G.Adj a c) (hbd : ¬G.Adj b d)
    (hsum : G.degree a + G.degree b + G.degree c + G.degree d ≤ 13) : False :=
  hC4 ⟨a, b, c, d, hcard, hab, hbc, hcd, hda, hac, hbd, hsum⟩

/-- **Induced `2K₂` witness.**  Two disjoint edges `a–b`, `c–d` of degree-3 vertices with no
crossing edges contradict `h2k2`. -/
theorem good_2K2_of_witnesses (G : SimpleGraph (Fin 12))
    (h2k2 : ¬∃ a b c d : Fin 12, ({a, b, c, d} : Finset (Fin 12)).card = 4 ∧
      G.degree a = 3 ∧ G.degree b = 3 ∧ G.degree c = 3 ∧ G.degree d = 3 ∧
      G.Adj a b ∧ G.Adj c d ∧ ¬G.Adj a c ∧ ¬G.Adj a d ∧ ¬G.Adj b c ∧ ¬G.Adj b d)
    (a b c d : Fin 12) (hcard : ({a, b, c, d} : Finset (Fin 12)).card = 4)
    (ha : G.degree a = 3) (hb : G.degree b = 3) (hc : G.degree c = 3) (hd : G.degree d = 3)
    (hab : G.Adj a b) (hcd : G.Adj c d) (hac : ¬G.Adj a c) (had : ¬G.Adj a d)
    (hbc : ¬G.Adj b c) (hbd : ¬G.Adj b d) : False :=
  h2k2 ⟨a, b, c, d, hcard, ha, hb, hc, hd, hab, hcd, hac, had, hbc, hbd⟩

/-- Common hypotheses of the residual regime, packaged for reuse in the case lemmas. -/
structure Residual (G : SimpleGraph (Fin 12)) (D Hub : Finset (Fin 12)) : Prop where
  /-- `D` is exactly the degree-3 set. -/
  hDmem : ∀ v : Fin 12, v ∈ D ↔ G.degree v = 3
  /-- `Hub` is exactly the degree-4 set. -/
  hHmem : ∀ v : Fin 12, v ∈ Hub ↔ G.degree v = 4
  /-- `D ∪ Hub` is everything. -/
  hpart : ∀ v : Fin 12, v ∈ D ∨ v ∈ Hub
  /-- `|D| = 8`. -/
  hDcard : D.card = 8
  /-- `|Hub| = 4`. -/
  hHcard : Hub.card = 4

/-- A degree-4 vertex's degree-3 neighbours are pairwise non-adjacent (else a forbidden
triangle of degree-sum `4 + 3 + 3 = 10 ≤ 10`). -/
theorem hub_nbrs_nonadj (G : SimpleGraph (Fin 12))
    (hT : ¬∃ x y z : Fin 12, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    {g x y : Fin 12} (hg : G.degree g = 4) (hx : G.degree x = 3) (hy : G.degree y = 3)
    (hxy : x ≠ y) (hgx : G.Adj g x) (hgy : G.Adj g y) : ¬G.Adj x y := by
  intro hxyadj
  refine hT ⟨g, x, y, ?_, hxy, ?_, hgx, hxyadj, hgy, by omega⟩
  · rintro rfl; omega
  · rintro rfl; omega

/-- **Disjoint edge finder.**  In a max-in-`D`-degree-`≤ 2` graph with `∑_{v∈D}|N v ∩ D| = 8`,
any `D`-edge `a–b` admits a second `D`-edge `c–d` vertex-disjoint from `{a, b}`. -/
theorem exists_disjoint_edge (G : SimpleGraph (Fin 12)) (D : Finset (Fin 12))
    (hsum : ∑ v ∈ D, (G.neighborFinset v ∩ D).card = 8)
    (hle2 : ∀ v ∈ D, (G.neighborFinset v ∩ D).card ≤ 2)
    (a b : Fin 12) (haD : a ∈ D) (hbD : b ∈ D) (hab : G.Adj a b) :
    ∃ c d : Fin 12, c ∈ D ∧ d ∈ D ∧ c ≠ a ∧ c ≠ b ∧ d ≠ a ∧ d ≠ b ∧ G.Adj c d := by
  classical
  set S : Finset (Fin 12) := D \ {a, b} with hSdef
  -- Double count: `∑_{v∈D} |N v ∩ S| = ∑_{w∈S} |N w ∩ D|`.
  have hdouble : ∑ v ∈ D, (G.neighborFinset v ∩ S).card
      = ∑ w ∈ S, (G.neighborFinset w ∩ D).card := by
    have hL : ∀ v : Fin 12, (G.neighborFinset v ∩ S).card
        = ∑ w ∈ S, (if G.Adj v w then 1 else 0) := by
      intro v
      rw [Finset.inter_comm, ← Finset.filter_mem_eq_inter, Finset.card_filter]
      exact Finset.sum_congr rfl (fun w _ => by simp only [G.mem_neighborFinset])
    have hR' : ∀ w : Fin 12, (G.neighborFinset w ∩ D).card
        = ∑ v ∈ D, (if G.Adj v w then 1 else 0) := by
      intro w
      rw [Finset.inter_comm, ← Finset.filter_mem_eq_inter, Finset.card_filter]
      exact Finset.sum_congr rfl (fun v _ => by simp only [G.mem_neighborFinset, SimpleGraph.adj_comm])
    simp_rw [hL, hR']
    exact Finset.sum_comm
  -- `∑_{w∈S} |N w ∩ D| = 8 - inMdeg a - inMdeg b`.
  have hssub : ({a, b} : Finset (Fin 12)) ⊆ D := by
    intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl; exacts [haD, hbD]
  have hSsum : ∑ w ∈ S, (G.neighborFinset w ∩ D).card
      = 8 - ((G.neighborFinset a ∩ D).card + (G.neighborFinset b ∩ D).card) := by
    have h := Finset.sum_sdiff (f := fun w => (G.neighborFinset w ∩ D).card) hssub
    rw [← hSdef, hsum] at h
    have hpair : ∑ w ∈ ({a, b} : Finset (Fin 12)), (G.neighborFinset w ∩ D).card
        = (G.neighborFinset a ∩ D).card + (G.neighborFinset b ∩ D).card := by
      rw [Finset.sum_insert (by simp [hab.ne]), Finset.sum_singleton]
    rw [hpair] at h; omega
  -- Split `∑_{v∈D} = ∑_{v∈S} + (a,b)`; the `a,b` terms are `≤ inMdeg − 1`.
  have hsplitD : ∑ v ∈ D, (G.neighborFinset v ∩ S).card
      = ∑ v ∈ S, (G.neighborFinset v ∩ S).card
        + ((G.neighborFinset a ∩ S).card + (G.neighborFinset b ∩ S).card) := by
    have h := Finset.sum_sdiff (f := fun v => (G.neighborFinset v ∩ S).card) hssub
    rw [← hSdef] at h
    have hpair : ∑ v ∈ ({a, b} : Finset (Fin 12)), (G.neighborFinset v ∩ S).card
        = (G.neighborFinset a ∩ S).card + (G.neighborFinset b ∩ S).card := by
      rw [Finset.sum_insert (by simp [hab.ne]), Finset.sum_singleton]
    rw [hpair] at h; omega
  have haS : (G.neighborFinset a ∩ S).card ≤ (G.neighborFinset a ∩ D).card - 1 := by
    have hb : b ∈ (G.neighborFinset a ∩ D).erase a := by
      rw [Finset.mem_erase, Finset.mem_inter, G.mem_neighborFinset]
      exact ⟨hab.ne', hab, hbD⟩
    have hsub : G.neighborFinset a ∩ S ⊆ (G.neighborFinset a ∩ D).erase b := by
      intro w hw
      rw [Finset.mem_inter, hSdef, Finset.mem_sdiff] at hw
      obtain ⟨hwa, hwD, hwab⟩ := hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hwab
      push Not at hwab
      rw [Finset.mem_erase, Finset.mem_inter]
      exact ⟨hwab.2, hwa, hwD⟩
    calc (G.neighborFinset a ∩ S).card ≤ ((G.neighborFinset a ∩ D).erase b).card :=
          Finset.card_le_card hsub
      _ = (G.neighborFinset a ∩ D).card - 1 := by
          rw [Finset.card_erase_of_mem]
          rw [Finset.mem_inter, G.mem_neighborFinset]; exact ⟨hab, hbD⟩
  have hbS : (G.neighborFinset b ∩ S).card ≤ (G.neighborFinset b ∩ D).card - 1 := by
    have hsub : G.neighborFinset b ∩ S ⊆ (G.neighborFinset b ∩ D).erase a := by
      intro w hw
      rw [Finset.mem_inter, hSdef, Finset.mem_sdiff] at hw
      obtain ⟨hwb, hwD, hwab⟩ := hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hwab
      push Not at hwab
      rw [Finset.mem_erase, Finset.mem_inter]
      exact ⟨hwab.1, hwb, hwD⟩
    calc (G.neighborFinset b ∩ S).card ≤ ((G.neighborFinset b ∩ D).erase a).card :=
          Finset.card_le_card hsub
      _ = (G.neighborFinset b ∩ D).card - 1 := by
          rw [Finset.card_erase_of_mem]
          rw [Finset.mem_inter, G.mem_neighborFinset]; exact ⟨hab.symm, haD⟩
  -- Conclude `∑_{v∈S} |N v ∩ S| ≥ 2 > 0`, so some `S`-vertex has an `S`-neighbour.
  have hale := hle2 a haD
  have hble := hle2 b hbD
  have hpos : ∑ v ∈ S, (G.neighborFinset v ∩ S).card ≠ 0 := by
    rw [hdouble, hSsum] at hsplitD; omega
  obtain ⟨c, hcS, hcne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hpos
  obtain ⟨d, hd⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hcne)
  rw [Finset.mem_inter, G.mem_neighborFinset] at hd
  obtain ⟨hcd, hdS⟩ := hd
  rw [hSdef, Finset.mem_sdiff] at hcS hdS
  simp only [Finset.mem_insert, Finset.mem_singleton] at hcS hdS
  push Not at hcS hdS
  exact ⟨c, d, hcS.1, hdS.1, hcS.2.1, hcS.2.2, hdS.2.1, hdS.2.2, hcd⟩

/-- Cardinality of an explicit 4-element set with pairwise-distinct entries. -/
theorem card_four {V : Type*} [DecidableEq V] (a b c d : V)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    ({a, b, c, d} : Finset V).card = 4 := by
  rw [Finset.card_insert_of_notMem (by simp [hab, hac, had]),
      Finset.card_insert_of_notMem (by simp [hbc, hbd]),
      Finset.card_insert_of_notMem (by simp [hcd]), Finset.card_singleton]

/-- Cardinality of an explicit 5-element set with pairwise-distinct entries. -/
theorem card_five {V : Type*} [DecidableEq V] (a b c d e : V)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e) (hbc : b ≠ c) (hbd : b ≠ d)
    (hbe : b ≠ e) (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e) :
    ({a, b, c, d, e} : Finset V).card = 5 := by
  rw [Finset.card_insert_of_notMem (by simp [hab, hac, had, hae]),
      Finset.card_insert_of_notMem (by simp [hbc, hbd, hbe]),
      Finset.card_insert_of_notMem (by simp [hcd, hce]),
      Finset.card_insert_of_notMem (by simp [hde]), Finset.card_singleton]

/-- **Five-vertex overflow.**  Five distinct `D`-vertices of in-`M`-degree `≥ 2` give
`∑_{v∈D}|N v ∩ D| ≥ 10`, contradicting the value `8`. -/
theorem inMdeg_five_overflow (G : SimpleGraph (Fin 12)) (D : Finset (Fin 12))
    (hsum : ∑ v ∈ D, (G.neighborFinset v ∩ D).card = 8)
    (a b c d e : Fin 12) (ha : a ∈ D) (hb : b ∈ D) (hc : c ∈ D) (hd : d ∈ D) (he : e ∈ D)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e) (hbc : b ≠ c) (hbd : b ≠ d)
    (hbe : b ≠ e) (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e)
    (ca : 2 ≤ (G.neighborFinset a ∩ D).card) (cb : 2 ≤ (G.neighborFinset b ∩ D).card)
    (cc : 2 ≤ (G.neighborFinset c ∩ D).card) (cd : 2 ≤ (G.neighborFinset d ∩ D).card)
    (ce : 2 ≤ (G.neighborFinset e ∩ D).card) : False := by
  classical
  have hsub : ({a, b, c, d, e} : Finset (Fin 12)) ⊆ D := by
    intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    exacts [ha, hb, hc, hd, he]
  have hT : ∑ x ∈ ({a, b, c, d, e} : Finset (Fin 12)), (G.neighborFinset x ∩ D).card
      = (G.neighborFinset a ∩ D).card + (G.neighborFinset b ∩ D).card
        + (G.neighborFinset c ∩ D).card + (G.neighborFinset d ∩ D).card
        + (G.neighborFinset e ∩ D).card := by
    rw [Finset.sum_insert (by simp [hab, hac, had, hae]),
        Finset.sum_insert (by simp [hbc, hbd, hbe]),
        Finset.sum_insert (by simp [hcd, hce]),
        Finset.sum_insert (by simp [hde]), Finset.sum_singleton]
    ring
  have hle : ∑ x ∈ ({a, b, c, d, e} : Finset (Fin 12)), (G.neighborFinset x ∩ D).card ≤ 8 := by
    rw [← hsum]; exact Finset.sum_le_sum_of_subset hsub
  rw [hT] at hle; omega

/-- **Cross-kill, auxiliary.**  In the `e(M)=4` max-degree-`≤ 2` regime with two crossing edges
`p–q`, `r–s`, `p–r` (`p, r` saturated) and an extra edge `q–y` (`y ∉ {p,r}`), one gets either an
induced `2K₂` `r–s | q–y` or a five-vertex overflow. -/
theorem cross_kill_aux (G : SimpleGraph (Fin 12)) (D : Finset (Fin 12))
    (h2k2 : ¬∃ a b c d : Fin 12, ({a, b, c, d} : Finset (Fin 12)).card = 4 ∧
      G.degree a = 3 ∧ G.degree b = 3 ∧ G.degree c = 3 ∧ G.degree d = 3 ∧
      G.Adj a b ∧ G.Adj c d ∧ ¬G.Adj a c ∧ ¬G.Adj a d ∧ ¬G.Adj b c ∧ ¬G.Adj b d)
    (hsum : ∑ v ∈ D, (G.neighborFinset v ∩ D).card = 8)
    (hle2 : ∀ v ∈ D, (G.neighborFinset v ∩ D).card ≤ 2)
    (hdeg3 : ∀ v ∈ D, G.degree v = 3)
    (p q r s y : Fin 12)
    (hpD : p ∈ D) (hqD : q ∈ D) (hrD : r ∈ D) (hsD : s ∈ D) (hyD : y ∈ D)
    (hpq : p ≠ q) (hpr : p ≠ r) (hps : p ≠ s) (hqr : q ≠ r) (hqs : q ≠ s) (hrs : r ≠ s)
    (hApq : G.Adj p q) (hArs : G.Adj r s) (hApr : G.Adj p r) (hnqs : ¬G.Adj q s)
    (hyp : y ≠ p) (hyr : y ≠ r) (hAqy : G.Adj q y) : False := by
  classical
  have hmemND : ∀ v z : Fin 12, z ∈ G.neighborFinset v ∩ D ↔ G.Adj v z ∧ z ∈ D := by
    intro v z; rw [Finset.mem_inter, G.mem_neighborFinset]
  -- `r` is saturated: its `D`-neighbours are exactly `{s, p}`.
  have hrfull : G.neighborFinset r ∩ D = {s, p} := by
    have hsub : ({s, p} : Finset (Fin 12)) ⊆ G.neighborFinset r ∩ D := by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact (hmemND r x).mpr ⟨hArs, hsD⟩
      · exact (hmemND r x).mpr ⟨hApr.symm, hpD⟩
    have hc2 : ({s, p} : Finset (Fin 12)).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simp [Ne.symm hps]), Finset.card_singleton]
    exact (Finset.eq_of_subset_of_card_le hsub (by rw [hc2]; exact hle2 r hrD)).symm
  have hrchar : ∀ w : Fin 12, G.Adj r w → w ∈ D → w = s ∨ w = p := by
    intro w hrw hwD
    have hw : w ∈ ({s, p} : Finset (Fin 12)) := hrfull ▸ (hmemND r w).mpr ⟨hrw, hwD⟩
    simpa using hw
  have hnqr : ¬G.Adj q r := by
    intro h; rcases hrchar q h.symm hqD with h' | h'
    · exact hqs h'
    · exact hpq.symm h'
  have hyne : y ≠ q := hAqy.ne'
  have hys : y ≠ s := by intro h; subst h; exact hnqs hAqy
  have hnry : ¬G.Adj r y := by
    intro h; rcases hrchar y h hyD with h' | h'
    · exact hys h'
    · exact hyp h'
  by_cases hsy : G.Adj s y
  · -- Five-vertex overflow.
    have two : ∀ v x₁ x₂ : Fin 12, x₁ ≠ x₂ → G.Adj v x₁ → G.Adj v x₂ → x₁ ∈ D → x₂ ∈ D →
        2 ≤ (G.neighborFinset v ∩ D).card := by
      intro v x₁ x₂ hx hx1 hx2 hx1D hx2D
      have hsub : ({x₁, x₂} : Finset (Fin 12)) ⊆ G.neighborFinset v ∩ D := by
        intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl
        · exact (hmemND v z).mpr ⟨hx1, hx1D⟩
        · exact (hmemND v z).mpr ⟨hx2, hx2D⟩
      have hc := Finset.card_le_card hsub
      rwa [Finset.card_insert_of_notMem (by simp [hx]), Finset.card_singleton] at hc
    exact inMdeg_five_overflow G D hsum p q r s y hpD hqD hrD hsD hyD
      hpq hpr hps (Ne.symm hyp) hqr hqs (Ne.symm hyne) hrs (Ne.symm hyr) (Ne.symm hys)
      (two p q r hqr hApq hApr hqD hrD)
      (two q p y (Ne.symm hyp) hApq.symm hAqy hpD hyD)
      (two r s p (Ne.symm hps) hArs hApr.symm hsD hpD)
      (two s r y (Ne.symm hyr) hArs.symm hsy hrD hyD)
      (two y q s hqs hAqy.symm hsy.symm hqD hsD)
  · -- Induced `2K₂` on `{r, s, q, y}`.
    exact good_2K2_of_witnesses G h2k2 r s q y
      (card_four r s q y hrs (Ne.symm hqr) (Ne.symm hyr) (Ne.symm hqs) (Ne.symm hys) (Ne.symm hyne))
      (hdeg3 r hrD) (hdeg3 s hsD) (hdeg3 q hqD) (hdeg3 y hyD)
      hArs hAqy (fun h => hnqr h.symm) hnry (fun h => hnqs h.symm) hsy

/-- **Cross-kill.**  Two disjoint `D`-edges `p–q`, `r–s` with a crossing edge `p–r`
contradict the `e(M)=4` max-degree-`≤ 2` regime (good `C₄`, induced `2K₂`, or overflow). -/
theorem cross_kill (G : SimpleGraph (Fin 12)) (D : Finset (Fin 12))
    (h2k2 : ¬∃ a b c d : Fin 12, ({a, b, c, d} : Finset (Fin 12)).card = 4 ∧
      G.degree a = 3 ∧ G.degree b = 3 ∧ G.degree c = 3 ∧ G.degree d = 3 ∧
      G.Adj a b ∧ G.Adj c d ∧ ¬G.Adj a c ∧ ¬G.Adj a d ∧ ¬G.Adj b c ∧ ¬G.Adj b d)
    (hC4 : ¬∃ a b c d : Fin 12, ({a, b, c, d} : Finset (Fin 12)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 13)
    (hsum : ∑ v ∈ D, (G.neighborFinset v ∩ D).card = 8)
    (hle2 : ∀ v ∈ D, (G.neighborFinset v ∩ D).card ≤ 2)
    (hdeg3 : ∀ v ∈ D, G.degree v = 3)
    (p q r s : Fin 12)
    (hpD : p ∈ D) (hqD : q ∈ D) (hrD : r ∈ D) (hsD : s ∈ D)
    (hpq : p ≠ q) (hpr : p ≠ r) (hps : p ≠ s) (hqr : q ≠ r) (hqs : q ≠ s) (hrs : r ≠ s)
    (hApq : G.Adj p q) (hArs : G.Adj r s) (hApr : G.Adj p r) : False := by
  classical
  have hmemND : ∀ v z : Fin 12, z ∈ G.neighborFinset v ∩ D ↔ G.Adj v z ∧ z ∈ D := by
    intro v z; rw [Finset.mem_inter, G.mem_neighborFinset]
  have hpfull : G.neighborFinset p ∩ D = {q, r} := by
    have hsub : ({q, r} : Finset (Fin 12)) ⊆ G.neighborFinset p ∩ D := by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact (hmemND p x).mpr ⟨hApq, hqD⟩
      · exact (hmemND p x).mpr ⟨hApr, hrD⟩
    have hc2 : ({q, r} : Finset (Fin 12)).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simp [hqr]), Finset.card_singleton]
    exact (Finset.eq_of_subset_of_card_le hsub (by rw [hc2]; exact hle2 p hpD)).symm
  have hpchar : ∀ w : Fin 12, G.Adj p w → w ∈ D → w = q ∨ w = r := by
    intro w hpw hwD
    have hw : w ∈ ({q, r} : Finset (Fin 12)) := hpfull ▸ (hmemND p w).mpr ⟨hpw, hwD⟩
    simpa using hw
  have hrfull : G.neighborFinset r ∩ D = {s, p} := by
    have hsub : ({s, p} : Finset (Fin 12)) ⊆ G.neighborFinset r ∩ D := by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact (hmemND r x).mpr ⟨hArs, hsD⟩
      · exact (hmemND r x).mpr ⟨hApr.symm, hpD⟩
    have hc2 : ({s, p} : Finset (Fin 12)).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simp [Ne.symm hps]), Finset.card_singleton]
    exact (Finset.eq_of_subset_of_card_le hsub (by rw [hc2]; exact hle2 r hrD)).symm
  have hrchar : ∀ w : Fin 12, G.Adj r w → w ∈ D → w = s ∨ w = p := by
    intro w hrw hwD
    have hw : w ∈ ({s, p} : Finset (Fin 12)) := hrfull ▸ (hmemND r w).mpr ⟨hrw, hwD⟩
    simpa using hw
  have hnps : ¬G.Adj p s := by
    intro h; rcases hpchar s h hsD with h' | h'
    · exact hqs h'.symm
    · exact hrs h'.symm
  have hnqr : ¬G.Adj q r := by
    intro h; rcases hrchar q h.symm hqD with h' | h'
    · exact hqs h'
    · exact hpq.symm h'
  by_cases hqs2 : G.Adj q s
  · -- Good `C₄` `p–q–s–r`.
    exact good_C4_of_witnesses G hC4 p q s r
      (card_four p q s r hpq hps hpr hqs hqr (Ne.symm hrs))
      hApq hqs2 hArs.symm hApr.symm hnps hnqr
      (by have := hdeg3 p hpD; have := hdeg3 q hqD; have := hdeg3 s hsD; have := hdeg3 r hrD; omega)
  · obtain ⟨e, f, heD, hfD, hep, her, hfp, hfr, hef⟩ :=
      exists_disjoint_edge G D hsum hle2 p r hpD hrD hApr
    by_cases heq : e = q
    · exact cross_kill_aux G D h2k2 hsum hle2 hdeg3 p q r s f
        hpD hqD hrD hsD hfD hpq hpr hps hqr hqs hrs hApq hArs hApr hqs2 hfp hfr (heq ▸ hef)
    · by_cases hes : e = s
      · exact cross_kill_aux G D h2k2 hsum hle2 hdeg3 r s p q f
          hrD hsD hpD hqD hfD hrs (Ne.symm hpr) (Ne.symm hqr) (Ne.symm hps) (Ne.symm hqs) hpq
          hArs hApq hApr.symm (fun h => hqs2 h.symm) hfr hfp (hes ▸ hef)
      · by_cases hfq : f = q
        · exact cross_kill_aux G D h2k2 hsum hle2 hdeg3 p q r s e
            hpD hqD hrD hsD heD hpq hpr hps hqr hqs hrs hApq hArs hApr hqs2 hep her
            ((hfq ▸ hef).symm)
        · by_cases hfs : f = s
          · exact cross_kill_aux G D h2k2 hsum hle2 hdeg3 r s p q e
              hrD hsD hpD hqD heD hrs (Ne.symm hpr) (Ne.symm hqr) (Ne.symm hps) (Ne.symm hqs) hpq
              hArs hApq hApr.symm (fun h => hqs2 h.symm) her hep ((hfs ▸ hef).symm)
          · -- Induced `2K₂` on `{p, r, e, f}`.
            have hnpe : ¬G.Adj p e := by
              intro h; rcases hpchar e h heD with h' | h'
              exacts [heq h', her h']
            have hnpf : ¬G.Adj p f := by
              intro h; rcases hpchar f h hfD with h' | h'
              exacts [hfq h', hfr h']
            have hnre : ¬G.Adj r e := by
              intro h; rcases hrchar e h heD with h' | h'
              exacts [hes h', hep h']
            have hnrf : ¬G.Adj r f := by
              intro h; rcases hrchar f h hfD with h' | h'
              exacts [hfs h', hfp h']
            exact good_2K2_of_witnesses G h2k2 p r e f
              (card_four p r e f hpr (Ne.symm hep) (Ne.symm hfp) (Ne.symm her) (Ne.symm hfr) hef.ne)
              (hdeg3 p hpD) (hdeg3 r hrD) (hdeg3 e heD) (hdeg3 f hfD)
              hApr hef hnpe hnpf hnre hnrf

/-- **Bipartite double count.**  For any two vertex sets, the number of `X→Y` incidences equals
the number of `Y→X` incidences. -/
theorem cross_count (G : SimpleGraph (Fin 12)) (X Y : Finset (Fin 12)) :
    ∑ v ∈ X, (G.neighborFinset v ∩ Y).card = ∑ w ∈ Y, (G.neighborFinset w ∩ X).card := by
  have hL : ∀ v : Fin 12, (G.neighborFinset v ∩ Y).card
      = ∑ w ∈ Y, (if G.Adj v w then 1 else 0) := by
    intro v
    rw [Finset.inter_comm, ← Finset.filter_mem_eq_inter, Finset.card_filter]
    exact Finset.sum_congr rfl (fun w _ => by simp only [G.mem_neighborFinset])
  have hR : ∀ w : Fin 12, (G.neighborFinset w ∩ X).card
      = ∑ v ∈ X, (if G.Adj v w then 1 else 0) := by
    intro w
    rw [Finset.inter_comm, ← Finset.filter_mem_eq_inter, Finset.card_filter]
    exact Finset.sum_congr rfl
      (fun v _ => by simp only [G.mem_neighborFinset, SimpleGraph.adj_comm])
  simp_rw [hL, hR]
  exact Finset.sum_comm

/-- **No in-`M`-degree-1 vertex.**  In the `e(M)=5` max-in-`M`-degree-`≤ 2` regime, a degree-1
endpoint `p` (with unique `M`-neighbour `q`) makes `{q} ∪ N q` a vertex cover of `M`, forcing
`∑_{v∈D}|N v ∩ D| ≤ 4·|N q ∩ D| ≤ 8 < 10`, a contradiction. -/
theorem no_inMdeg_one (G : SimpleGraph (Fin 12)) (D : Finset (Fin 12))
    (h2k2 : ¬∃ a b c d : Fin 12, ({a, b, c, d} : Finset (Fin 12)).card = 4 ∧
      G.degree a = 3 ∧ G.degree b = 3 ∧ G.degree c = 3 ∧ G.degree d = 3 ∧
      G.Adj a b ∧ G.Adj c d ∧ ¬G.Adj a c ∧ ¬G.Adj a d ∧ ¬G.Adj b c ∧ ¬G.Adj b d)
    (hsum : ∑ v ∈ D, (G.neighborFinset v ∩ D).card = 10)
    (hle2 : ∀ v ∈ D, (G.neighborFinset v ∩ D).card ≤ 2)
    (hdeg3 : ∀ v ∈ D, G.degree v = 3)
    (p : Fin 12) (hpD : p ∈ D) (hp1 : (G.neighborFinset p ∩ D).card = 1) : False := by
  classical
  have hmemND : ∀ v z : Fin 12, z ∈ G.neighborFinset v ∩ D ↔ G.Adj v z ∧ z ∈ D := by
    intro v z; rw [Finset.mem_inter, G.mem_neighborFinset]
  obtain ⟨q, hq⟩ := Finset.card_eq_one.mp hp1
  have hqmem : q ∈ G.neighborFinset p ∩ D := by rw [hq]; exact Finset.mem_singleton_self q
  have hpq : G.Adj p q := ((hmemND p q).mp hqmem).1
  have hqD : q ∈ D := ((hmemND p q).mp hqmem).2
  have hpchar : ∀ w : Fin 12, G.Adj p w → w ∈ D → w = q := by
    intro w hpw hwD
    have hw : w ∈ G.neighborFinset p ∩ D := (hmemND p w).mpr ⟨hpw, hwD⟩
    rw [hq, Finset.mem_singleton] at hw; exact hw
  have hqnotin : q ∉ G.neighborFinset q ∩ D := by
    rw [hmemND]; exact fun h => G.irrefl h.1
  have hAsubD : insert q (G.neighborFinset q ∩ D) ⊆ D := by
    intro x hx
    rw [Finset.mem_insert] at hx
    rcases hx with rfl | hx
    · exact hqD
    · exact (Finset.mem_inter.mp hx).2
  have hpA : p ∈ insert q (G.neighborFinset q ∩ D) :=
    Finset.mem_insert_of_mem ((hmemND q p).mpr ⟨hpq.symm, hpD⟩)
  -- `{q} ∪ N q` is a vertex cover of `M`.
  have hcover : ∀ v w : Fin 12, v ∈ D → w ∈ D → G.Adj v w →
      v ∈ insert q (G.neighborFinset q ∩ D) ∨ w ∈ insert q (G.neighborFinset q ∩ D) := by
    intro v w hvD hwD hvw
    by_contra hcon
    push Not at hcon
    obtain ⟨hvA, hwA⟩ := hcon
    have hvq : v ≠ q := fun h => hvA (h ▸ Finset.mem_insert_self _ _)
    have hwq : w ≠ q := fun h => hwA (h ▸ Finset.mem_insert_self _ _)
    have hnqv : ¬G.Adj q v := fun h =>
      hvA (Finset.mem_insert_of_mem ((hmemND q v).mpr ⟨h, hvD⟩))
    have hnqw : ¬G.Adj q w := fun h =>
      hwA (Finset.mem_insert_of_mem ((hmemND q w).mpr ⟨h, hwD⟩))
    have hvp : v ≠ p := fun h => hvA (h ▸ hpA)
    have hwp : w ≠ p := fun h => hwA (h ▸ hpA)
    have hcard4 : ({p, q, v, w} : Finset (Fin 12)).card = 4 :=
      card_four p q v w hpq.ne (Ne.symm hvp) (Ne.symm hwp) (Ne.symm hvq) (Ne.symm hwq) hvw.ne
    rcases M_edges_joined G h2k2 p q v w hcard4 (hdeg3 p hpD) (hdeg3 q hqD) (hdeg3 v hvD)
        (hdeg3 w hwD) hpq hvw with h | h | h | h
    · exact hvq (hpchar v h hvD)
    · exact hwq (hpchar w h hwD)
    · exact hnqv h
    · exact hnqw h
  -- Split the in-`M`-degree sum over the cover and its complement.
  have hpart : insert q (G.neighborFinset q ∩ D) ∪ (D \ insert q (G.neighborFinset q ∩ D)) = D :=
    Finset.union_sdiff_of_subset hAsubD
  have hDsplit : ∑ v ∈ insert q (G.neighborFinset q ∩ D), (G.neighborFinset v ∩ D).card
      + ∑ v ∈ D \ insert q (G.neighborFinset q ∩ D), (G.neighborFinset v ∩ D).card
      = ∑ v ∈ D, (G.neighborFinset v ∩ D).card := by
    rw [← Finset.sum_union Finset.disjoint_sdiff, hpart]
  -- On the complement, every `D`-neighbour lies in the cover.
  have hcventer : ∀ v ∈ D \ insert q (G.neighborFinset q ∩ D),
      (G.neighborFinset v ∩ D).card = (G.neighborFinset v ∩ insert q (G.neighborFinset q ∩ D)).card
      := by
    intro v hv
    rw [Finset.mem_sdiff] at hv
    obtain ⟨hvD, hvA⟩ := hv
    congr 1
    apply Finset.Subset.antisymm
    · intro w hw
      rw [Finset.mem_inter] at hw ⊢
      obtain ⟨hwN, hwD⟩ := hw
      refine ⟨hwN, ?_⟩
      have hvw : G.Adj v w := (G.mem_neighborFinset v w).mp hwN
      rcases hcover v w hvD hwD hvw with h | h
      · exact absurd h hvA
      · exact h
    · intro w hw
      rw [Finset.mem_inter] at hw ⊢
      exact ⟨hw.1, hAsubD hw.2⟩
  have hsumDA : ∑ v ∈ D \ insert q (G.neighborFinset q ∩ D), (G.neighborFinset v ∩ D).card
      = ∑ v ∈ D \ insert q (G.neighborFinset q ∩ D),
        (G.neighborFinset v ∩ insert q (G.neighborFinset q ∩ D)).card :=
    Finset.sum_congr rfl hcventer
  have hcc : ∑ v ∈ D \ insert q (G.neighborFinset q ∩ D),
        (G.neighborFinset v ∩ insert q (G.neighborFinset q ∩ D)).card
      = ∑ w ∈ insert q (G.neighborFinset q ∩ D),
        (G.neighborFinset w ∩ (D \ insert q (G.neighborFinset q ∩ D))).card :=
    cross_count G (D \ insert q (G.neighborFinset q ∩ D)) (insert q (G.neighborFinset q ∩ D))
  have hwsplit : ∀ w ∈ insert q (G.neighborFinset q ∩ D),
      (G.neighborFinset w ∩ insert q (G.neighborFinset q ∩ D)).card
      + (G.neighborFinset w ∩ (D \ insert q (G.neighborFinset q ∩ D))).card
      = (G.neighborFinset w ∩ D).card := by
    intro w _
    rw [← Finset.card_union_of_disjoint
      ((Finset.disjoint_sdiff).mono Finset.inter_subset_right Finset.inter_subset_right)]
    congr 1
    rw [← Finset.inter_union_distrib_left, hpart]
  have hAsum : ∑ w ∈ insert q (G.neighborFinset q ∩ D),
        (G.neighborFinset w ∩ insert q (G.neighborFinset q ∩ D)).card
      + ∑ w ∈ insert q (G.neighborFinset q ∩ D),
        (G.neighborFinset w ∩ (D \ insert q (G.neighborFinset q ∩ D))).card
      = ∑ w ∈ insert q (G.neighborFinset q ∩ D), (G.neighborFinset w ∩ D).card := by
    rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl hwsplit
  -- Bound the cover sum by `3·|N q ∩ D|`.
  have hsumA_eq : ∑ w ∈ insert q (G.neighborFinset q ∩ D), (G.neighborFinset w ∩ D).card
      = (G.neighborFinset q ∩ D).card
        + ∑ w ∈ G.neighborFinset q ∩ D, (G.neighborFinset w ∩ D).card := by
    rw [Finset.sum_insert hqnotin]
  have hRbound : ∑ w ∈ G.neighborFinset q ∩ D, (G.neighborFinset w ∩ D).card
      ≤ (G.neighborFinset q ∩ D).card * 2 := by
    calc ∑ w ∈ G.neighborFinset q ∩ D, (G.neighborFinset w ∩ D).card
        ≤ ∑ _w ∈ G.neighborFinset q ∩ D, 2 :=
          Finset.sum_le_sum (fun w hw => hle2 w (Finset.mem_inter.mp hw).2)
      _ = (G.neighborFinset q ∩ D).card * 2 := by rw [Finset.sum_const, smul_eq_mul]
  -- Bound the within-cover sum below by `2·|N q ∩ D|`.
  have hNqA : G.neighborFinset q ∩ insert q (G.neighborFinset q ∩ D) = G.neighborFinset q ∩ D := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_insert, G.mem_neighborFinset]
    constructor
    · rintro ⟨hx, rfl | hx2⟩
      · exact (G.irrefl hx).elim
      · exact ⟨hx, hx2.2⟩
    · rintro ⟨hx, hxD⟩
      exact ⟨hx, Or.inr ⟨hx, hxD⟩⟩
  have hsumAA_eq : ∑ w ∈ insert q (G.neighborFinset q ∩ D),
        (G.neighborFinset w ∩ insert q (G.neighborFinset q ∩ D)).card
      = (G.neighborFinset q ∩ D).card
        + ∑ w ∈ G.neighborFinset q ∩ D,
          (G.neighborFinset w ∩ insert q (G.neighborFinset q ∩ D)).card := by
    rw [Finset.sum_insert hqnotin, hNqA]
  have hlow : ∀ w ∈ G.neighborFinset q ∩ D,
      1 ≤ (G.neighborFinset w ∩ insert q (G.neighborFinset q ∩ D)).card := by
    intro w hw
    obtain ⟨hwN, hwD⟩ := Finset.mem_inter.mp hw
    have hwq : G.Adj w q := ((G.mem_neighborFinset q w).mp hwN).symm
    apply Finset.card_pos.mpr
    exact ⟨q, by
      rw [Finset.mem_inter, G.mem_neighborFinset]
      exact ⟨hwq, Finset.mem_insert_self _ _⟩⟩
  have hRlow : (G.neighborFinset q ∩ D).card
      ≤ ∑ w ∈ G.neighborFinset q ∩ D,
        (G.neighborFinset w ∩ insert q (G.neighborFinset q ∩ D)).card := by
    calc (G.neighborFinset q ∩ D).card = ∑ _w ∈ G.neighborFinset q ∩ D, 1 := by
          rw [Finset.sum_const, smul_eq_mul, mul_one]
      _ ≤ _ := Finset.sum_le_sum hlow
  have hcqle : (G.neighborFinset q ∩ D).card ≤ 2 := hle2 q hqD
  have hcc2 : ∑ v ∈ D \ insert q (G.neighborFinset q ∩ D), (G.neighborFinset v ∩ D).card
      = ∑ w ∈ insert q (G.neighborFinset q ∩ D),
        (G.neighborFinset w ∩ (D \ insert q (G.neighborFinset q ∩ D))).card := hsumDA.trans hcc
  omega

/-- **`e(M)=5` extraction.**  When `e(M)=5` (so `∑_{v∈D}|N v ∩ D| = 10`) and some `D`-vertex has
all three neighbours in `D`, `M` is the double star and we extract the twin certificate. -/
theorem eM_five_extract (G : SimpleGraph (Fin 12)) (D Hub : Finset (Fin 12))
    (hR : Residual G D Hub)
    (hT : ¬∃ x y z : Fin 12, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    (h2k2 : ¬∃ a b c d : Fin 12, ({a, b, c, d} : Finset (Fin 12)).card = 4 ∧
      G.degree a = 3 ∧ G.degree b = 3 ∧ G.degree c = 3 ∧ G.degree d = 3 ∧
      G.Adj a b ∧ G.Adj c d ∧ ¬G.Adj a c ∧ ¬G.Adj a d ∧ ¬G.Adj b c ∧ ¬G.Adj b d)
    (hC4 : ¬∃ a b c d : Fin 12, ({a, b, c, d} : Finset (Fin 12)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 13)
    (_hK23 : ¬∃ a b c d e : Fin 12, ({a, b, c, d, e} : Finset (Fin 12)).card = 5 ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
      G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 17)
    (heM5 : ∑ v ∈ D, (G.neighborFinset v ∩ D).card = 10)
    (heH1 : ∑ v ∈ Hub, (G.neighborFinset v ∩ Hub).card = 2)
    (hu : ∃ u ∈ D, (G.neighborFinset u ∩ D).card = 3) :
    ∃ c₁ c₂ leaf tw₁ tw₂ g₁ g₂ : Fin 12,
      G.degree c₁ = 3 ∧ G.degree c₂ = 3 ∧ G.Adj c₁ c₂ ∧
        (∀ w : Fin 12, G.Adj c₁ w → G.degree w = 3) ∧
        (∀ w : Fin 12, G.Adj c₂ w → G.degree w = 3) ∧
        G.degree leaf = 3 ∧ G.Adj c₁ leaf ∧ leaf ≠ c₂ ∧
        G.Adj leaf g₁ ∧ G.Adj leaf g₂ ∧ g₁ ≠ g₂ ∧ ¬G.Adj g₁ g₂ ∧
        G.degree g₁ = 4 ∧ G.degree g₂ = 4 ∧
        (∀ w : Fin 12, G.Adj leaf w → G.degree w = 4 → w = g₁ ∨ w = g₂) ∧
        G.degree tw₁ = 3 ∧ G.degree tw₂ = 3 ∧ tw₁ ≠ tw₂ ∧
        (∀ w : Fin 12, G.Adj tw₁ w → G.degree w = 4) ∧
        (∀ w : Fin 12, G.Adj tw₂ w → G.degree w = 4) := by
  classical
  obtain ⟨u, huD, hu3⟩ := hu
  have hmemND : ∀ v z : Fin 12, z ∈ G.neighborFinset v ∩ D ↔ G.Adj v z ∧ z ∈ D := by
    intro v z; rw [Finset.mem_inter, G.mem_neighborFinset]
  have hdeg3 : ∀ v ∈ D, G.degree v = 3 := fun v hv => (hR.hDmem v).mp hv
  have hHdeg4 : ∀ g ∈ Hub, G.degree g = 4 := fun g hg => (hR.hHmem g).mp hg
  have hDHdisj : Disjoint D Hub := by
    rw [Finset.disjoint_left]
    intro v hvD hvH
    have := (hR.hDmem v).mp hvD; have := (hR.hHmem v).mp hvH; omega
  have hdegle : ∀ v : Fin 12, G.degree v ≤ 4 := by
    intro v; rcases hR.hpart v with h | h
    · have := (hR.hDmem v).mp h; omega
    · have := (hR.hHmem v).mp h; omega
  have hudeg : G.degree u = 3 := hdeg3 u huD
  have hNuD : G.neighborFinset u ⊆ D := by
    have hsub : G.neighborFinset u ∩ D ⊆ G.neighborFinset u := Finset.inter_subset_left
    have hcle : (G.neighborFinset u).card ≤ (G.neighborFinset u ∩ D).card := by
      rw [hu3, G.card_neighborFinset_eq_degree, hudeg]
    exact Finset.inter_eq_left.mp (Finset.eq_of_subset_of_card_le hsub hcle)
  obtain ⟨w1, w2, w3, hw12, hw13, hw23, hset⟩ := Finset.card_eq_three.mp hu3
  have hm1 : G.Adj u w1 ∧ w1 ∈ D := (hmemND u w1).mp (by rw [hset]; simp)
  have hm2 : G.Adj u w2 ∧ w2 ∈ D := (hmemND u w2).mp (by rw [hset]; simp)
  have hm3 : G.Adj u w3 ∧ w3 ∈ D := (hmemND u w3).mp (by rw [hset]; simp)
  obtain ⟨hua1, hw1D⟩ := hm1
  obtain ⟨hua2, hw2D⟩ := hm2
  obtain ⟨hua3, hw3D⟩ := hm3
  have huw1 : u ≠ w1 := hua1.ne
  have huw2 : u ≠ w2 := hua2.ne
  have huw3 : u ≠ w3 := hua3.ne
  have hd1 : G.degree w1 = 3 := hdeg3 w1 hw1D
  have hd2 : G.degree w2 = 3 := hdeg3 w2 hw2D
  have hd3 : G.degree w3 = 3 := hdeg3 w3 hw3D
  have hn12 : ¬G.Adj w1 w2 := fun h => hT ⟨u, w1, w2, huw1, hw12, huw2, hua1, h, hua2, by omega⟩
  have hn13 : ¬G.Adj w1 w3 := fun h => hT ⟨u, w1, w3, huw1, hw13, huw3, hua1, h, hua3, by omega⟩
  have hn23 : ¬G.Adj w2 w3 := fun h => hT ⟨u, w2, w3, huw2, hw23, huw3, hua2, h, hua3, by omega⟩
  -- The "rest" set `R = D \ {u, w1, w2, w3}`.
  set R : Finset (Fin 12) := D \ insert u {w1, w2, w3} with hRdef
  have hmemNR : ∀ v z : Fin 12, z ∈ G.neighborFinset v ∩ R ↔ G.Adj v z ∧ z ∈ R := by
    intro v z; rw [Finset.mem_inter, G.mem_neighborFinset]
  have huW : u ∉ ({w1, w2, w3} : Finset (Fin 12)) := by
    intro h
    have : u ∈ G.neighborFinset u ∩ D := by rw [hset]; exact h
    exact G.irrefl ((hmemND u u).mp this).1
  have hinsubD : insert u ({w1, w2, w3} : Finset (Fin 12)) ⊆ D := by
    intro x hx
    rw [Finset.mem_insert] at hx
    rcases hx with rfl | hx
    · exact huD
    · have : x ∈ G.neighborFinset u ∩ D := by rw [hset]; exact hx
      exact ((hmemND u x).mp this).2
  have hURD : insert u ({w1, w2, w3} : Finset (Fin 12)) ∪ R = D :=
    Finset.union_sdiff_of_subset hinsubD
  have hURdisj : Disjoint (insert u ({w1, w2, w3} : Finset (Fin 12))) R := Finset.disjoint_sdiff
  have hnuR : ∀ z ∈ R, ¬G.Adj u z := by
    intro z hz hadj
    rw [hRdef, Finset.mem_sdiff] at hz
    have hzD := hz.1
    have hzNu : z ∈ G.neighborFinset u ∩ D := (hmemND u z).mpr ⟨hadj, hzD⟩
    rw [hset] at hzNu
    exact hz.2 (Finset.mem_insert_of_mem hzNu)
  -- Per-vertex split `|N v ∩ D| = |N v ∩ (insert u W)| + |N v ∩ R|`.
  have hsplitD : ∀ v : Fin 12, (G.neighborFinset v ∩ D).card
      = (G.neighborFinset v ∩ insert u ({w1, w2, w3} : Finset (Fin 12))).card
        + (G.neighborFinset v ∩ R).card := by
    intro v
    rw [← Finset.card_union_of_disjoint
      (hURdisj.mono Finset.inter_subset_right Finset.inter_subset_right),
      ← Finset.inter_union_distrib_left, hURD]
  -- Each `wᵢ` meets `insert u W` only at `u`.
  have e1 : G.neighborFinset w1 ∩ insert u ({w1, w2, w3} : Finset (Fin 12)) = {u} := by
    ext z
    simp only [Finset.mem_inter, G.mem_neighborFinset, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hz, rfl | rfl | rfl | rfl⟩
      · rfl
      · exact (G.irrefl hz).elim
      · exact (hn12 hz).elim
      · exact (hn13 hz).elim
    · rintro rfl; exact ⟨hua1.symm, Or.inl rfl⟩
  have e2 : G.neighborFinset w2 ∩ insert u ({w1, w2, w3} : Finset (Fin 12)) = {u} := by
    ext z
    simp only [Finset.mem_inter, G.mem_neighborFinset, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hz, rfl | rfl | rfl | rfl⟩
      · rfl
      · exact (hn12 hz.symm).elim
      · exact (G.irrefl hz).elim
      · exact (hn23 hz).elim
    · rintro rfl; exact ⟨hua2.symm, Or.inl rfl⟩
  have e3 : G.neighborFinset w3 ∩ insert u ({w1, w2, w3} : Finset (Fin 12)) = {u} := by
    ext z
    simp only [Finset.mem_inter, G.mem_neighborFinset, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hz, rfl | rfl | rfl | rfl⟩
      · rfl
      · exact (hn13 hz.symm).elim
      · exact (hn23 hz.symm).elim
      · exact (G.irrefl hz).elim
    · rintro rfl; exact ⟨hua3.symm, Or.inl rfl⟩
  have hWcard : ({w1, w2, w3} : Finset (Fin 12)).card = 3 := by
    rw [← hset]; exact hu3
  -- The counting identity `2·S + RR = 4`.
  have hc2u : (G.neighborFinset u ∩ R).card = 0 := by
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro v hv
    obtain ⟨hvN, hvR⟩ := (hmemNR u v).mp hv
    exact hnuR v hvR hvN
  have hSWexp : ∑ w ∈ ({w1, w2, w3} : Finset (Fin 12)), (G.neighborFinset w ∩ D).card
      = 3 + ((G.neighborFinset w1 ∩ R).card + (G.neighborFinset w2 ∩ R).card
        + (G.neighborFinset w3 ∩ R).card) := by
    rw [Finset.sum_insert (by simp [hw12, hw13]), Finset.sum_insert (by simp [hw23]),
      Finset.sum_singleton, hsplitD w1, hsplitD w2, hsplitD w3, e1, e2, e3]
    simp only [Finset.card_singleton]
    ring
  have hSRexp : ∑ v ∈ R, (G.neighborFinset v ∩ D).card
      = ((G.neighborFinset w1 ∩ R).card + (G.neighborFinset w2 ∩ R).card
        + (G.neighborFinset w3 ∩ R).card) + ∑ v ∈ R, (G.neighborFinset v ∩ R).card := by
    have hcc : ∑ v ∈ R, (G.neighborFinset v ∩ insert u ({w1, w2, w3} : Finset (Fin 12))).card
        = ∑ w ∈ insert u ({w1, w2, w3} : Finset (Fin 12)), (G.neighborFinset w ∩ R).card :=
      cross_count G R (insert u {w1, w2, w3})
    have hins : ∑ w ∈ insert u ({w1, w2, w3} : Finset (Fin 12)), (G.neighborFinset w ∩ R).card
        = (G.neighborFinset w1 ∩ R).card + (G.neighborFinset w2 ∩ R).card
          + (G.neighborFinset w3 ∩ R).card := by
      rw [Finset.sum_insert huW, Finset.sum_insert (by simp [hw12, hw13]),
        Finset.sum_insert (by simp [hw23]), Finset.sum_singleton, hc2u]
      ring
    rw [Finset.sum_congr rfl (fun v _ => hsplitD v), Finset.sum_add_distrib, hcc, hins]
  have hcount : ∑ v ∈ D, (G.neighborFinset v ∩ D).card
      = 3 + (∑ w ∈ ({w1, w2, w3} : Finset (Fin 12)), (G.neighborFinset w ∩ D).card)
        + ∑ v ∈ R, (G.neighborFinset v ∩ D).card := by
    have hsu := Finset.sum_union (f := fun v => (G.neighborFinset v ∩ D).card) hURdisj
    rw [hURD] at hsu
    rw [hsu, Finset.sum_insert huW, hu3]
  set Sa : ℕ := (G.neighborFinset w1 ∩ R).card with hSa
  set Sb : ℕ := (G.neighborFinset w2 ∩ R).card with hSb
  set Sc : ℕ := (G.neighborFinset w3 ∩ R).card with hSc
  set RR : ℕ := ∑ v ∈ R, (G.neighborFinset v ∩ R).card with hRR
  have hkey : 2 * (Sa + Sb + Sc) + RR = 4 := by
    rw [heM5] at hcount
    omega
  have hsingle : ∀ x ∈ R, (G.neighborFinset x ∩ R).card ≤ RR := by
    intro x hx
    rw [hRR]
    exact Finset.single_le_sum (f := fun v => (G.neighborFinset v ∩ R).card)
      (fun _ _ => Nat.zero_le _) hx
  -- `noCommon`: no vertex (other than `u`) is joined to two distinct `wᵢ`.
  have noCommon : ∀ z a b : Fin 12, z ≠ u → ¬G.Adj u z → G.Adj u a → G.Adj u b →
      a ∈ D → b ∈ D → ¬G.Adj a b → a ≠ b → G.Adj z a → G.Adj z b → False := by
    intro z a b hzu hnuz hua hub haD hbD hnab hab hza hzb
    have hcard : ({u, a, z, b} : Finset (Fin 12)).card = 4 :=
      card_four u a z b hua.ne (Ne.symm hzu) hub.ne hza.ne' hab hzb.ne
    refine good_C4_of_witnesses G hC4 u a z b hcard hua hza.symm hzb hub.symm hnuz hnab ?_
    have := hdeg3 a haD; have := hdeg3 b hbD; have := hdegle z; omega
  -- No edge inside `R` (forces `RR = 0`): an `R`-edge would join all three `wᵢ` to its two ends.
  have hRR0 : RR = 0 := by
    by_contra hne
    obtain ⟨v, hvR, hvne⟩ := Finset.exists_ne_zero_of_sum_ne_zero (by rw [← hRR]; exact hne)
    obtain ⟨x, hx⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hvne)
    obtain ⟨hvx, hxR⟩ := (hmemNR v x).mp hx
    have hvsd : v ∈ D \ insert u ({w1, w2, w3} : Finset (Fin 12)) := by rw [← hRdef]; exact hvR
    have hxsd : x ∈ D \ insert u ({w1, w2, w3} : Finset (Fin 12)) := by rw [← hRdef]; exact hxR
    have hvD : v ∈ D := (Finset.mem_sdiff.mp hvsd).1
    have hxD : x ∈ D := (Finset.mem_sdiff.mp hxsd).1
    have hvu : v ≠ u := fun e => (Finset.mem_sdiff.mp hvsd).2 (e ▸ Finset.mem_insert_self _ _)
    have hxu : x ≠ u := fun e => (Finset.mem_sdiff.mp hxsd).2 (e ▸ Finset.mem_insert_self _ _)
    have hnuv : ¬G.Adj u v := hnuR v hvR
    have hnux : ¬G.Adj u x := hnuR x hxR
    have hjoin : ∀ w : Fin 12, G.Adj u w → w ∈ D → G.Adj w v ∨ G.Adj w x := by
      intro w huw hwD
      have hwv : w ≠ v := fun e => hnuv (e ▸ huw)
      have hwx : w ≠ x := fun e => hnux (e ▸ huw)
      have hcard : ({u, w, v, x} : Finset (Fin 12)).card = 4 :=
        card_four u w v x huw.ne (Ne.symm hvu) (Ne.symm hxu) hwv hwx hvx.ne
      rcases M_edges_joined G h2k2 u w v x hcard hudeg (hdeg3 w hwD) (hdeg3 v hvD) (hdeg3 x hxD)
          huw hvx with h | h | h | h
      · exact absurd h hnuv
      · exact absurd h hnux
      · exact Or.inl h
      · exact Or.inr h
    rcases hjoin w1 hua1 hw1D with j1 | j1 <;> rcases hjoin w2 hua2 hw2D with j2 | j2 <;>
      rcases hjoin w3 hua3 hw3D with j3 | j3
    · exact noCommon v w1 w2 hvu hnuv hua1 hua2 hw1D hw2D hn12 hw12 j1.symm j2.symm
    · exact noCommon v w1 w2 hvu hnuv hua1 hua2 hw1D hw2D hn12 hw12 j1.symm j2.symm
    · exact noCommon v w1 w3 hvu hnuv hua1 hua3 hw1D hw3D hn13 hw13 j1.symm j3.symm
    · exact noCommon x w2 w3 hxu hnux hua2 hua3 hw2D hw3D hn23 hw23 j2.symm j3.symm
    · exact noCommon v w2 w3 hvu hnuv hua2 hua3 hw2D hw3D hn23 hw23 j2.symm j3.symm
    · exact noCommon x w1 w3 hxu hnux hua1 hua3 hw1D hw3D hn13 hw13 j1.symm j3.symm
    · exact noCommon x w1 w2 hxu hnux hua1 hua2 hw1D hw2D hn12 hw12 j1.symm j2.symm
    · exact noCommon x w1 w2 hxu hnux hua1 hua2 hw1D hw2D hn12 hw12 j1.symm j2.symm
  have hnoRedge : ∀ x ∈ R, ∀ y ∈ R, ¬G.Adj x y := by
    intro x hxR y hyR hxy
    have hmem : y ∈ G.neighborFinset x ∩ R := (hmemNR x y).mpr ⟨hxy, hyR⟩
    have hpos : 0 < (G.neighborFinset x ∩ R).card := Finset.card_pos.mpr ⟨y, hmem⟩
    have := hsingle x hxR
    omega
  have hSsum : Sa + Sb + Sc = 2 := by omega
  -- Two distinct `wᵢ` cannot both have an `R`-neighbour.
  have notboth : ∀ a b : Fin 12, G.Adj u a → G.Adj u b → a ∈ D → b ∈ D → ¬G.Adj a b → a ≠ b →
      (G.neighborFinset a ∩ R).card = 0 ∨ (G.neighborFinset b ∩ R).card = 0 := by
    intro a b hua hub haD hbD hnab hab
    by_contra hc
    push Not at hc
    obtain ⟨ha0, hb0⟩ := hc
    obtain ⟨x, hx⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero ha0)
    obtain ⟨y, hy⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hb0)
    obtain ⟨hax, hxR⟩ := (hmemNR a x).mp hx
    obtain ⟨hby, hyR⟩ := (hmemNR b y).mp hy
    have hxsd : x ∈ D \ insert u ({w1, w2, w3} : Finset (Fin 12)) := by rw [← hRdef]; exact hxR
    have hysd : y ∈ D \ insert u ({w1, w2, w3} : Finset (Fin 12)) := by rw [← hRdef]; exact hyR
    have hxD : x ∈ D := (Finset.mem_sdiff.mp hxsd).1
    have hyD : y ∈ D := (Finset.mem_sdiff.mp hysd).1
    have hxu : x ≠ u := fun e => (Finset.mem_sdiff.mp hxsd).2 (e ▸ Finset.mem_insert_self _ _)
    have hyu : y ≠ u := fun e => (Finset.mem_sdiff.mp hysd).2 (e ▸ Finset.mem_insert_self _ _)
    have hnux : ¬G.Adj u x := hnuR x hxR
    have hnuy : ¬G.Adj u y := hnuR y hyR
    by_cases hxy : x = y
    · subst hxy
      exact noCommon x a b hxu hnux hua hub haD hbD hnab hab hax.symm hby.symm
    · have haW : a ∈ insert u ({w1, w2, w3} : Finset (Fin 12)) :=
        Finset.mem_insert_of_mem (by rw [← hset]; exact (hmemND u a).mpr ⟨hua, haD⟩)
      have hbW : b ∈ insert u ({w1, w2, w3} : Finset (Fin 12)) :=
        Finset.mem_insert_of_mem (by rw [← hset]; exact (hmemND u b).mpr ⟨hub, hbD⟩)
      have hay : a ≠ y := fun h => (Finset.disjoint_left.mp hURdisj haW) (h ▸ hyR)
      have hxb : x ≠ b := fun h => (Finset.disjoint_left.mp hURdisj hbW) (h ▸ hxR)
      have hcard : ({a, x, b, y} : Finset (Fin 12)).card = 4 :=
        card_four a x b y hax.ne hab hay hxb hxy hby.ne
      rcases M_edges_joined G h2k2 a x b y hcard (hdeg3 a haD) (hdeg3 x hxD) (hdeg3 b hbD)
          (hdeg3 y hyD) hax hby with h | h | h | h
      · exact hnab h
      · exact noCommon y a b hyu hnuy hua hub haD hbD hnab hab h.symm hby.symm
      · exact noCommon x a b hxu hnux hua hub haD hbD hnab hab hax.symm h
      · exact hnoRedge x hxR y hyR h
  -- `W` is an independent set.
  have hWindep : ∀ a b : Fin 12, a ∈ ({w1, w2, w3} : Finset (Fin 12)) →
      b ∈ ({w1, w2, w3} : Finset (Fin 12)) → a ≠ b → ¬G.Adj a b := by
    intro a b ha hb hab
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
      first
        | exact (hab rfl).elim
        | exact hn12
        | exact hn13
        | exact hn23
        | exact fun h => hn12 h.symm
        | exact fun h => hn13 h.symm
        | exact fun h => hn23 h.symm
  -- Any `W`-vertex meets `insert u W` only at `u`.
  have hWins : ∀ w : Fin 12, w ∈ ({w1, w2, w3} : Finset (Fin 12)) →
      G.neighborFinset w ∩ insert u ({w1, w2, w3} : Finset (Fin 12)) = {u} := by
    intro w hwW
    have huw : G.Adj u w := by
      have hmem : w ∈ G.neighborFinset u ∩ D := by rw [hset]; exact hwW
      exact ((hmemND u w).mp hmem).1
    ext z
    simp only [Finset.mem_inter, G.mem_neighborFinset, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hz, rfl | hzW⟩
      · rfl
      · by_cases hwz : w = z
        · exact (G.irrefl (hwz ▸ hz)).elim
        · exact (hWindep w z hwW (by
            simp only [Finset.mem_insert, Finset.mem_singleton]; exact hzW) hwz hz).elim
    · rintro rfl; exact ⟨huw.symm, Or.inl rfl⟩
  -- Locate the second centre `c₂`.
  have hc2ex : ∃ c : Fin 12, G.Adj u c ∧ c ∈ D ∧ (G.neighborFinset c ∩ R).card = 2 ∧
      ∀ w : Fin 12, G.Adj u w → w ∈ D → w ≠ c → (G.neighborFinset w ∩ R).card = 0 := by
    have nb12 := notboth w1 w2 hua1 hua2 hw1D hw2D hn12 hw12
    have nb13 := notboth w1 w3 hua1 hua3 hw1D hw3D hn13 hw13
    have nb23 := notboth w2 w3 hua2 hua3 hw2D hw3D hn23 hw23
    have hmemw : ∀ w : Fin 12, G.Adj u w → w ∈ D → w = w1 ∨ w = w2 ∨ w = w3 := by
      intro w huw hwD
      have hmem : w ∈ ({w1, w2, w3} : Finset (Fin 12)) := by
        rw [← hset]; exact (hmemND u w).mpr ⟨huw, hwD⟩
      simpa [Finset.mem_insert, Finset.mem_singleton] using hmem
    rcases Nat.eq_zero_or_pos Sa with ha0 | hapos
    · rcases Nat.eq_zero_or_pos Sb with hb0 | hbpos
      · refine ⟨w3, hua3, hw3D, by omega, ?_⟩
        intro w huw hwD hwne
        rcases hmemw w huw hwD with rfl | rfl | rfl
        · exact ha0
        · exact hb0
        · exact absurd rfl hwne
      · have hc0 : Sc = 0 := nb23.resolve_left (by omega)
        refine ⟨w2, hua2, hw2D, by omega, ?_⟩
        intro w huw hwD hwne
        rcases hmemw w huw hwD with rfl | rfl | rfl
        · exact ha0
        · exact absurd rfl hwne
        · exact hc0
    · have hb0 : Sb = 0 := nb12.resolve_left (by omega)
      have hc0 : Sc = 0 := nb13.resolve_left (by omega)
      refine ⟨w1, hua1, hw1D, by omega, ?_⟩
      intro w huw hwD hwne
      rcases hmemw w huw hwD with rfl | rfl | rfl
      · exact absurd rfl hwne
      · exact hb0
      · exact hc0
  obtain ⟨c₂, hc2adj, hc2D, hc2R2, hc2other⟩ := hc2ex
  have hc2W : c₂ ∈ ({w1, w2, w3} : Finset (Fin 12)) := by
    rw [← hset]; exact (hmemND u c₂).mpr ⟨hc2adj, hc2D⟩
  -- `c₂` has in-`M`-degree 3, so all its neighbours are degree-3.
  have hc2deg3 : (G.neighborFinset c₂ ∩ D).card = 3 := by
    rw [hsplitD c₂, hWins c₂ hc2W, hc2R2]; simp
  have hc2NsubD : G.neighborFinset c₂ ⊆ D := by
    have hsub : G.neighborFinset c₂ ∩ D ⊆ G.neighborFinset c₂ := Finset.inter_subset_left
    have hcle : (G.neighborFinset c₂).card ≤ (G.neighborFinset c₂ ∩ D).card := by
      rw [hc2deg3, G.card_neighborFinset_eq_degree, hdeg3 c₂ hc2D]
    exact Finset.inter_eq_left.mp (Finset.eq_of_subset_of_card_le hsub hcle)
  -- A `W`-vertex with no `R`-neighbour has in-`M`-degree 1.
  have hinMdeg : ∀ w : Fin 12, w ∈ ({w1, w2, w3} : Finset (Fin 12)) →
      (G.neighborFinset w ∩ R).card = 0 → (G.neighborFinset w ∩ D).card = 1 := by
    intro w hwW hwR0
    rw [hsplitD w, hWins w hwW, hwR0]; simp
  -- A neighbour of `c₂` inside `R` meets `insert u W` only at `c₂`.
  have hc2leaf_ins : ∀ t : Fin 12, t ∈ G.neighborFinset c₂ ∩ R →
      G.neighborFinset t ∩ insert u ({w1, w2, w3} : Finset (Fin 12)) = {c₂} := by
    intro t ht
    obtain ⟨htc2, htR⟩ := (hmemNR c₂ t).mp ht
    ext z
    simp only [Finset.mem_inter, G.mem_neighborFinset, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨htz, rfl | hzW⟩
      · exact absurd htz.symm (hnuR t htR)
      · have hzW' : z ∈ ({w1, w2, w3} : Finset (Fin 12)) := by
          simp only [Finset.mem_insert, Finset.mem_singleton]; exact hzW
        have huz : G.Adj u z := ((hmemND u z).mp (by rw [hset]; exact hzW')).1
        have hzD : z ∈ D := ((hmemND u z).mp (by rw [hset]; exact hzW')).2
        by_cases hzc2 : z = c₂
        · exact hzc2
        · have hz0 := hc2other z huz hzD hzc2
          have htmem : t ∈ G.neighborFinset z ∩ R := (hmemNR z t).mpr ⟨htz.symm, htR⟩
          rw [Finset.card_eq_zero] at hz0
          rw [hz0] at htmem
          exact absurd htmem (Finset.notMem_empty t)
    · rintro rfl
      refine ⟨htc2.symm, Or.inr ?_⟩
      have := hc2W; simp only [Finset.mem_insert, Finset.mem_singleton] at this; exact this
  have hc2leaf_inMdeg : ∀ t ∈ G.neighborFinset c₂ ∩ R, (G.neighborFinset t ∩ D).card = 1 := by
    intro t ht
    have htR : t ∈ R := (Finset.mem_inter.mp ht).2
    have hR0 : (G.neighborFinset t ∩ R).card = 0 := by
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro z hz
      obtain ⟨htz, hzR⟩ := (hmemNR t z).mp hz
      exact hnoRedge t htR z hzR htz
    rw [hsplitD t, hc2leaf_ins t ht, hR0]; simp
  -- Twins: `R`-vertices not adjacent to `c₂` are in-`M`-isolated.
  have htins : ∀ t : Fin 12, t ∈ R \ (G.neighborFinset c₂ ∩ R) →
      G.neighborFinset t ∩ insert u ({w1, w2, w3} : Finset (Fin 12)) = ∅ := by
    intro t ht
    rw [Finset.mem_sdiff] at ht
    obtain ⟨htR, htn⟩ := ht
    rw [Finset.eq_empty_iff_forall_notMem]
    intro z hz
    rw [Finset.mem_inter, G.mem_neighborFinset, Finset.mem_insert] at hz
    obtain ⟨htz, hzcase⟩ := hz
    rcases hzcase with rfl | hzW
    · exact hnuR t htR htz.symm
    · have huz : G.Adj u z := ((hmemND u z).mp (by rw [hset]; exact hzW)).1
      have hzD : z ∈ D := ((hmemND u z).mp (by rw [hset]; exact hzW)).2
      have htmem : t ∈ G.neighborFinset z ∩ R := (hmemNR z t).mpr ⟨htz.symm, htR⟩
      by_cases hzc2 : z = c₂
      · subst hzc2; exact htn htmem
      · have hz0 := hc2other z huz hzD hzc2
        rw [Finset.card_eq_zero] at hz0
        rw [hz0] at htmem
        exact absurd htmem (Finset.notMem_empty t)
  have htwin0 : ∀ t : Fin 12, t ∈ R \ (G.neighborFinset c₂ ∩ R) →
      (G.neighborFinset t ∩ D).card = 0 := by
    intro t ht
    have htR : t ∈ R := (Finset.mem_sdiff.mp ht).1
    have hR0 : (G.neighborFinset t ∩ R).card = 0 := by
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro z hz
      obtain ⟨htz, hzR⟩ := (hmemNR t z).mp hz
      exact hnoRedge t htR z hzR htz
    rw [hsplitD t, htins t ht, hR0, Finset.card_empty]
  have htwhub : ∀ t : Fin 12, (G.neighborFinset t ∩ D).card = 0 →
      ∀ w : Fin 12, G.Adj t w → G.degree w = 4 := by
    intro t ht0 w htw
    have hwND : w ∉ D := by
      intro hwD
      have hmem : w ∈ G.neighborFinset t ∩ D := (hmemND t w).mpr ⟨htw, hwD⟩
      rw [Finset.card_eq_zero] at ht0
      rw [ht0] at hmem
      exact Finset.notMem_empty w hmem
    rcases hR.hpart w with h | h
    · exact absurd h hwND
    · exact (hR.hHmem w).mp h
  -- Degree split into `D` and `Hub` neighbours (for leaf hub counts).
  have hcover : D ∪ Hub = Finset.univ := by
    rw [Finset.eq_univ_iff_forall]; intro v
    rcases hR.hpart v with h | h
    · exact Finset.mem_union_left _ h
    · exact Finset.mem_union_right _ h
  have hsplit : ∀ v : Fin 12,
      (G.neighborFinset v ∩ D).card + (G.neighborFinset v ∩ Hub).card = G.degree v := by
    intro v
    have hdisj : Disjoint (G.neighborFinset v ∩ D) (G.neighborFinset v ∩ Hub) :=
      hDHdisj.mono Finset.inter_subset_right Finset.inter_subset_right
    have huni : (G.neighborFinset v ∩ D) ∪ (G.neighborFinset v ∩ Hub) = G.neighborFinset v := by
      rw [← Finset.inter_union_distrib_left, hcover, Finset.inter_univ]
    rw [← Finset.card_union_of_disjoint hdisj, huni, G.card_neighborFinset_eq_degree]
  have hmemNHub : ∀ a z : Fin 12, z ∈ G.neighborFinset a ∩ Hub ↔ G.Adj a z ∧ z ∈ Hub := by
    intro a z; rw [Finset.mem_inter, G.mem_neighborFinset]
  -- The two twins.
  have hRcard : R.card = 4 := by
    have hi : insert u ({w1, w2, w3} : Finset (Fin 12)) ∩ D = insert u {w1, w2, w3} :=
      Finset.inter_eq_left.mpr hinsubD
    have h2 : (insert u ({w1, w2, w3} : Finset (Fin 12))).card = 4 := by
      rw [Finset.card_insert_of_notMem huW, hWcard]
    rw [hRdef, Finset.card_sdiff, hi, h2, hR.hDcard]
  have hTWcard : (R \ (G.neighborFinset c₂ ∩ R)).card = 2 := by
    have hi : (G.neighborFinset c₂ ∩ R) ∩ R = G.neighborFinset c₂ ∩ R :=
      Finset.inter_eq_left.mpr Finset.inter_subset_right
    rw [Finset.card_sdiff, hi, hRcard, hc2R2]
  obtain ⟨tw1, tw2, htw12ne, hTWset⟩ := Finset.card_eq_two.mp hTWcard
  have htw1mem : tw1 ∈ R \ (G.neighborFinset c₂ ∩ R) := by rw [hTWset]; simp
  have htw2mem : tw2 ∈ R \ (G.neighborFinset c₂ ∩ R) := by rw [hTWset]; simp
  have htw1D : tw1 ∈ D :=
    (Finset.mem_sdiff.mp (hRdef ▸ (Finset.mem_sdiff.mp htw1mem).1)).1
  have htw2D : tw2 ∈ D :=
    (Finset.mem_sdiff.mp (hRdef ▸ (Finset.mem_sdiff.mp htw2mem).1)).1
  have htw1deg : G.degree tw1 = 3 := hdeg3 tw1 htw1D
  have htw2deg : G.degree tw2 = 3 := hdeg3 tw2 htw2D
  have htw1hub : ∀ w : Fin 12, G.Adj tw1 w → G.degree w = 4 := htwhub tw1 (htwin0 tw1 htw1mem)
  have htw2hub : ∀ w : Fin 12, G.Adj tw2 w → G.degree w = 4 := htwhub tw2 (htwin0 tw2 htw2mem)
  -- The unique hub–hub edge `h–h'`.
  obtain ⟨h, hhHub, hhne⟩ := Finset.exists_ne_zero_of_sum_ne_zero
    (show (∑ g ∈ Hub, (G.neighborFinset g ∩ Hub).card) ≠ 0 by rw [heH1]; norm_num)
  obtain ⟨h', hh'mem⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hhne)
  have hhh' : G.Adj h h' := ((hmemNHub h h').mp hh'mem).1
  have hh'Hub : h' ∈ Hub := ((hmemNHub h h').mp hh'mem).2
  have hsupp : ∀ a : Fin 12, a ∈ Hub → a ≠ h → a ≠ h' →
      (G.neighborFinset a ∩ Hub).card = 0 := by
    intro a haHub hah hah'
    have hsub : ({h, h', a} : Finset (Fin 12)) ⊆ Hub := by
      intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl
      exacts [hhHub, hh'Hub, haHub]
    have hsum3 : ∑ x ∈ ({h, h', a} : Finset (Fin 12)), (G.neighborFinset x ∩ Hub).card
        = (G.neighborFinset h ∩ Hub).card + (G.neighborFinset h' ∩ Hub).card
          + (G.neighborFinset a ∩ Hub).card := by
      rw [Finset.sum_insert (by simp [hhh'.ne, Ne.symm hah]),
          Finset.sum_insert (by simp [Ne.symm hah']), Finset.sum_singleton]
      ring
    have hle : ∑ x ∈ ({h, h', a} : Finset (Fin 12)), (G.neighborFinset x ∩ Hub).card ≤ 2 := by
      rw [← heH1]; exact Finset.sum_le_sum_of_subset hsub
    have hhge : 1 ≤ (G.neighborFinset h ∩ Hub).card := Finset.card_pos.mpr ⟨h', hh'mem⟩
    have hh'ge : 1 ≤ (G.neighborFinset h' ∩ Hub).card :=
      Finset.card_pos.mpr ⟨h, (hmemNHub h' h).mpr ⟨hhh'.symm, hhHub⟩⟩
    rw [hsum3] at hle
    omega
  have huniq : ∀ a : Fin 12, a ∈ Hub → (G.neighborFinset a ∩ Hub).card ≠ 0 → a = h ∨ a = h' := by
    intro a haHub hane
    by_contra hcon
    push Not at hcon
    exact hane (hsupp a haHub hcon.1 hcon.2)
  have hbadh : ∀ ℓ g₁ g₂ : Fin 12, g₁ ∈ Hub → g₂ ∈ Hub → g₁ ≠ g₂ →
      G.Adj ℓ g₁ → G.Adj ℓ g₂ → G.Adj g₁ g₂ → G.Adj ℓ h := by
    intro ℓ g₁ g₂ hg1 hg2 hgne ha1 ha2 hadj
    have hg1ne : (G.neighborFinset g₁ ∩ Hub).card ≠ 0 :=
      (Finset.card_pos.mpr ⟨g₂, (hmemNHub g₁ g₂).mpr ⟨hadj, hg2⟩⟩).ne'
    have hg2ne : (G.neighborFinset g₂ ∩ Hub).card ≠ 0 :=
      (Finset.card_pos.mpr ⟨g₁, (hmemNHub g₂ g₁).mpr ⟨hadj.symm, hg1⟩⟩).ne'
    rcases huniq g₁ hg1 hg1ne with rfl | rfl
    · exact ha1
    · rcases huniq g₂ hg2 hg2ne with rfl | hbad
      · exact ha2
      · exact (hgne hbad.symm).elim
  -- Each in-`M`-degree-1 leaf has exactly two hub neighbours.
  have hleafhubs : ∀ ℓ : Fin 12, ℓ ∈ D → (G.neighborFinset ℓ ∩ D).card = 1 →
      ∃ g₁ g₂ : Fin 12, g₁ ≠ g₂ ∧ G.Adj ℓ g₁ ∧ G.Adj ℓ g₂ ∧ g₁ ∈ Hub ∧ g₂ ∈ Hub ∧
        (∀ w : Fin 12, G.Adj ℓ w → G.degree w = 4 → w = g₁ ∨ w = g₂) := by
    intro ℓ hℓD hℓ1
    have hℓhub2 : (G.neighborFinset ℓ ∩ Hub).card = 2 := by
      have hs := hsplit ℓ; rw [hℓ1, hdeg3 ℓ hℓD] at hs; omega
    obtain ⟨g₁, g₂, hg12, hgset⟩ := Finset.card_eq_two.mp hℓhub2
    have hg1mem : g₁ ∈ G.neighborFinset ℓ ∩ Hub := by rw [hgset]; simp
    have hg2mem : g₂ ∈ G.neighborFinset ℓ ∩ Hub := by rw [hgset]; simp
    refine ⟨g₁, g₂, hg12, ((hmemNHub ℓ g₁).mp hg1mem).1, ((hmemNHub ℓ g₂).mp hg2mem).1,
      ((hmemNHub ℓ g₁).mp hg1mem).2, ((hmemNHub ℓ g₂).mp hg2mem).2, ?_⟩
    intro w hℓw hwdeg
    have hwHub : w ∈ Hub := (hR.hHmem w).mpr hwdeg
    have hwmem : w ∈ G.neighborFinset ℓ ∩ Hub := (hmemNHub ℓ w).mpr ⟨hℓw, hwHub⟩
    rw [hgset] at hwmem; simpa using hwmem
  -- The four leaves.
  have hLcard : (({w1, w2, w3} : Finset (Fin 12)) \ {c₂}).card = 2 := by
    have hi : ({c₂} : Finset (Fin 12)) ∩ {w1, w2, w3} = {c₂} :=
      Finset.inter_eq_left.mpr (Finset.singleton_subset_iff.mpr hc2W)
    rw [Finset.card_sdiff, hi, hWcard, Finset.card_singleton]
  obtain ⟨la, lb, hlab, hLset⟩ := Finset.card_eq_two.mp hLcard
  have hla_mem : la ∈ ({w1, w2, w3} : Finset (Fin 12)) \ {c₂} := by rw [hLset]; simp
  have hlb_mem : lb ∈ ({w1, w2, w3} : Finset (Fin 12)) \ {c₂} := by rw [hLset]; simp
  have hlaW : la ∈ ({w1, w2, w3} : Finset (Fin 12)) := (Finset.mem_sdiff.mp hla_mem).1
  have hlbW : lb ∈ ({w1, w2, w3} : Finset (Fin 12)) := (Finset.mem_sdiff.mp hlb_mem).1
  have hlac2 : la ≠ c₂ := by have := (Finset.mem_sdiff.mp hla_mem).2; simpa using this
  have hlbc2 : lb ≠ c₂ := by have := (Finset.mem_sdiff.mp hlb_mem).2; simpa using this
  have hula : G.Adj u la := ((hmemND u la).mp (by rw [hset]; exact hlaW)).1
  have hulb : G.Adj u lb := ((hmemND u lb).mp (by rw [hset]; exact hlbW)).1
  have hlaD : la ∈ D := ((hmemND u la).mp (by rw [hset]; exact hlaW)).2
  have hlbD : lb ∈ D := ((hmemND u lb).mp (by rw [hset]; exact hlbW)).2
  have hla1 : (G.neighborFinset la ∩ D).card = 1 := hinMdeg la hlaW (hc2other la hula hlaD hlac2)
  have hlb1 : (G.neighborFinset lb ∩ D).card = 1 := hinMdeg lb hlbW (hc2other lb hulb hlbD hlbc2)
  obtain ⟨l3, l4, hl34ne, hl34set⟩ := Finset.card_eq_two.mp hc2R2
  have hl3mem : l3 ∈ G.neighborFinset c₂ ∩ R := by rw [hl34set]; simp
  have hl4mem : l4 ∈ G.neighborFinset c₂ ∩ R := by rw [hl34set]; simp
  have hl3R : l3 ∈ R := (Finset.mem_inter.mp hl3mem).2
  have hl4R : l4 ∈ R := (Finset.mem_inter.mp hl4mem).2
  have hl3D : l3 ∈ D := (Finset.mem_sdiff.mp (hRdef ▸ hl3R)).1
  have hl4D : l4 ∈ D := (Finset.mem_sdiff.mp (hRdef ▸ hl4R)).1
  have hc2l3 : G.Adj c₂ l3 := ((hmemNR c₂ l3).mp hl3mem).1
  have hc2l4 : G.Adj c₂ l4 := ((hmemNR c₂ l4).mp hl4mem).1
  have hl3u : l3 ≠ u := fun e =>
    (Finset.mem_sdiff.mp (hRdef ▸ hl3R)).2 (e ▸ Finset.mem_insert_self _ _)
  have hl4u : l4 ≠ u := fun e =>
    (Finset.mem_sdiff.mp (hRdef ▸ hl4R)).2 (e ▸ Finset.mem_insert_self _ _)
  have hl31 : (G.neighborFinset l3 ∩ D).card = 1 := hc2leaf_inMdeg l3 hl3mem
  have hl41 : (G.neighborFinset l4 ∩ D).card = 1 := hc2leaf_inMdeg l4 hl4mem
  obtain ⟨ga1, ga2, gane, gaa1, gaa2, gah1, gah2, gaall⟩ := hleafhubs la hlaD hla1
  obtain ⟨gb1, gb2, gbne, gba1, gba2, gbh1, gbh2, gball⟩ := hleafhubs lb hlbD hlb1
  obtain ⟨gc1, gc2, gcne, gca1, gca2, gch1, gch2, gcall⟩ := hleafhubs l3 hl3D hl31
  obtain ⟨gd1, gd2, gdne, gda1, gda2, gdh1, gdh2, gdall⟩ := hleafhubs l4 hl4D hl41
  -- At least one leaf has non-adjacent hubs (else `h` would have degree ≥ 5).
  have hgood : ¬G.Adj ga1 ga2 ∨ ¬G.Adj gb1 gb2 ∨ ¬G.Adj gc1 gc2 ∨ ¬G.Adj gd1 gd2 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨hba, hbb, hbc, hbd⟩ := hcon
    have hlah : G.Adj la h := hbadh la ga1 ga2 gah1 gah2 gane gaa1 gaa2 hba
    have hlbh : G.Adj lb h := hbadh lb gb1 gb2 gbh1 gbh2 gbne gba1 gba2 hbb
    have hl3h : G.Adj l3 h := hbadh l3 gc1 gc2 gch1 gch2 gcne gca1 gca2 hbc
    have hl4h : G.Adj l4 h := hbadh l4 gd1 gd2 gdh1 gdh2 gdne gda1 gda2 hbd
    have e_h'la : h' ≠ la := by rintro rfl; exact (Finset.disjoint_left.mp hDHdisj hlaD) hh'Hub
    have e_h'lb : h' ≠ lb := by rintro rfl; exact (Finset.disjoint_left.mp hDHdisj hlbD) hh'Hub
    have e_h'l3 : h' ≠ l3 := by rintro rfl; exact (Finset.disjoint_left.mp hDHdisj hl3D) hh'Hub
    have e_h'l4 : h' ≠ l4 := by rintro rfl; exact (Finset.disjoint_left.mp hDHdisj hl4D) hh'Hub
    have e_lal3 : la ≠ l3 := by
      rintro rfl
      exact (Finset.disjoint_left.mp hURdisj (Finset.mem_insert_of_mem hlaW)) hl3R
    have e_lal4 : la ≠ l4 := by
      rintro rfl
      exact (Finset.disjoint_left.mp hURdisj (Finset.mem_insert_of_mem hlaW)) hl4R
    have e_lbl3 : lb ≠ l3 := by
      rintro rfl
      exact (Finset.disjoint_left.mp hURdisj (Finset.mem_insert_of_mem hlbW)) hl3R
    have e_lbl4 : lb ≠ l4 := by
      rintro rfl
      exact (Finset.disjoint_left.mp hURdisj (Finset.mem_insert_of_mem hlbW)) hl4R
    have h5card : ({h', la, lb, l3, l4} : Finset (Fin 12)).card = 5 :=
      card_five h' la lb l3 l4 e_h'la e_h'lb e_h'l3 e_h'l4 hlab e_lal3 e_lal4 e_lbl3 e_lbl4 hl34ne
    have h5sub : ({h', la, lb, l3, l4} : Finset (Fin 12)) ⊆ G.neighborFinset h := by
      intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with hz | hz | hz | hz | hz
      · rw [hz]; exact (G.mem_neighborFinset h h').mpr hhh'
      · rw [hz]; exact (G.mem_neighborFinset h la).mpr hlah.symm
      · rw [hz]; exact (G.mem_neighborFinset h lb).mpr hlbh.symm
      · rw [hz]; exact (G.mem_neighborFinset h l3).mpr hl3h.symm
      · rw [hz]; exact (G.mem_neighborFinset h l4).mpr hl4h.symm
    have hle := Finset.card_le_card h5sub
    rw [h5card, G.card_neighborFinset_eq_degree, hHdeg4 h hhHub] at hle
    omega
  -- Assemble the certificate from a good leaf and its centre.
  have assemble : ∀ cc cc' ℓ : Fin 12, G.degree cc = 3 → G.degree cc' = 3 → G.Adj cc cc' →
      G.neighborFinset cc ⊆ D → G.neighborFinset cc' ⊆ D → G.Adj cc ℓ → ℓ ≠ cc' →
      (G.neighborFinset ℓ ∩ D).card = 1 →
      (∃ g₁ g₂ : Fin 12, g₁ ≠ g₂ ∧ G.Adj ℓ g₁ ∧ G.Adj ℓ g₂ ∧ ¬G.Adj g₁ g₂ ∧
        G.degree g₁ = 4 ∧ G.degree g₂ = 4 ∧
        (∀ w : Fin 12, G.Adj ℓ w → G.degree w = 4 → w = g₁ ∨ w = g₂)) →
      ∃ c₁ c₂ leaf tw₁ tw₂ g₁ g₂ : Fin 12,
        G.degree c₁ = 3 ∧ G.degree c₂ = 3 ∧ G.Adj c₁ c₂ ∧
          (∀ w : Fin 12, G.Adj c₁ w → G.degree w = 3) ∧
          (∀ w : Fin 12, G.Adj c₂ w → G.degree w = 3) ∧
          G.degree leaf = 3 ∧ G.Adj c₁ leaf ∧ leaf ≠ c₂ ∧
          G.Adj leaf g₁ ∧ G.Adj leaf g₂ ∧ g₁ ≠ g₂ ∧ ¬G.Adj g₁ g₂ ∧
          G.degree g₁ = 4 ∧ G.degree g₂ = 4 ∧
          (∀ w : Fin 12, G.Adj leaf w → G.degree w = 4 → w = g₁ ∨ w = g₂) ∧
          G.degree tw₁ = 3 ∧ G.degree tw₂ = 3 ∧ tw₁ ≠ tw₂ ∧
          (∀ w : Fin 12, G.Adj tw₁ w → G.degree w = 4) ∧
          (∀ w : Fin 12, G.Adj tw₂ w → G.degree w = 4) := by
    rintro cc cc' ℓ hccd hcc'd hcccc' hccsub hcc'sub hccℓ hℓcc' hℓ1
      ⟨g₁, g₂, hg12, hℓg1, hℓg2, hgnadj, hgd1, hgd2, hgall⟩
    exact ⟨cc, cc', ℓ, tw1, tw2, g₁, g₂, hccd, hcc'd, hcccc',
      fun w hw => hdeg3 w (hccsub ((G.mem_neighborFinset cc w).mpr hw)),
      fun w hw => hdeg3 w (hcc'sub ((G.mem_neighborFinset cc' w).mpr hw)),
      hdeg3 ℓ (hccsub ((G.mem_neighborFinset cc ℓ).mpr hccℓ)), hccℓ, hℓcc',
      hℓg1, hℓg2, hg12, hgnadj, hgd1, hgd2, hgall,
      htw1deg, htw2deg, htw12ne, htw1hub, htw2hub⟩
  rcases hgood with hg | hg | hg | hg
  · exact assemble u c₂ la hudeg (hdeg3 c₂ hc2D) hc2adj hNuD hc2NsubD hula hlac2 hla1
      ⟨ga1, ga2, gane, gaa1, gaa2, hg, hHdeg4 ga1 gah1, hHdeg4 ga2 gah2, gaall⟩
  · exact assemble u c₂ lb hudeg (hdeg3 c₂ hc2D) hc2adj hNuD hc2NsubD hulb hlbc2 hlb1
      ⟨gb1, gb2, gbne, gba1, gba2, hg, hHdeg4 gb1 gbh1, hHdeg4 gb2 gbh2, gball⟩
  · exact assemble c₂ u l3 (hdeg3 c₂ hc2D) hudeg hc2adj.symm hc2NsubD hNuD hc2l3 hl3u hl31
      ⟨gc1, gc2, gcne, gca1, gca2, hg, hHdeg4 gc1 gch1, hHdeg4 gc2 gch2, gcall⟩
  · exact assemble c₂ u l4 (hdeg3 c₂ hc2D) hudeg hc2adj.symm hc2NsubD hNuD hc2l4 hl4u hl41
      ⟨gd1, gd2, gdne, gda1, gda2, hg, hHdeg4 gd1 gdh1, hHdeg4 gd2 gdh2, gdall⟩

/-- **`C₅` exclusion.**  When `e(M)=5` but no `D`-vertex has in-`M`-degree 3 (the `C₅` regime),
the three in-`M`-degree-0 twins force a good `K_{2,3}`, a contradiction. -/
theorem eM_five_C5_no_residual (G : SimpleGraph (Fin 12)) (D Hub : Finset (Fin 12))
    (hR : Residual G D Hub)
    (hT : ¬∃ x y z : Fin 12, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    (h2k2 : ¬∃ a b c d : Fin 12, ({a, b, c, d} : Finset (Fin 12)).card = 4 ∧
      G.degree a = 3 ∧ G.degree b = 3 ∧ G.degree c = 3 ∧ G.degree d = 3 ∧
      G.Adj a b ∧ G.Adj c d ∧ ¬G.Adj a c ∧ ¬G.Adj a d ∧ ¬G.Adj b c ∧ ¬G.Adj b d)
    (hC4 : ¬∃ a b c d : Fin 12, ({a, b, c, d} : Finset (Fin 12)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 13)
    (_hK23 : ¬∃ a b c d e : Fin 12, ({a, b, c, d, e} : Finset (Fin 12)).card = 5 ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
      G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 17)
    (heM5 : ∑ v ∈ D, (G.neighborFinset v ∩ D).card = 10)
    (_heH1 : ∑ v ∈ Hub, (G.neighborFinset v ∩ Hub).card = 2)
    (hno3 : ∀ v ∈ D, (G.neighborFinset v ∩ D).card ≤ 2) : False := by
  classical
  have hdeg3 : ∀ v ∈ D, G.degree v = 3 := fun v hv => (hR.hDmem v).mp hv
  have hHdeg4 : ∀ g ∈ Hub, G.degree g = 4 := fun g hg => (hR.hHmem g).mp hg
  have hDHdisj : Disjoint D Hub := by
    rw [Finset.disjoint_left]
    intro v hvD hvH
    have := (hR.hDmem v).mp hvD; have := (hR.hHmem v).mp hvH; omega
  have hcover : D ∪ Hub = Finset.univ := by
    rw [Finset.eq_univ_iff_forall]; intro v
    rcases hR.hpart v with h | h
    · exact Finset.mem_union_left _ h
    · exact Finset.mem_union_right _ h
  have hsplit : ∀ v : Fin 12,
      (G.neighborFinset v ∩ D).card + (G.neighborFinset v ∩ Hub).card = G.degree v := by
    intro v
    have hdisj : Disjoint (G.neighborFinset v ∩ D) (G.neighborFinset v ∩ Hub) :=
      hDHdisj.mono Finset.inter_subset_right Finset.inter_subset_right
    have huni : (G.neighborFinset v ∩ D) ∪ (G.neighborFinset v ∩ Hub) = G.neighborFinset v := by
      rw [← Finset.inter_union_distrib_left, hcover, Finset.inter_univ]
    rw [← Finset.card_union_of_disjoint hdisj, huni, G.card_neighborFinset_eq_degree]
  -- Step 1: no in-`M`-degree-1 vertex.
  have hne1 : ∀ v ∈ D, (G.neighborFinset v ∩ D).card ≠ 1 := by
    intro v hv h
    exact no_inMdeg_one G D h2k2 heM5 hno3 hdeg3 v hv h
  -- Step 2: the in-`M`-degree-2 set `C` has five elements.
  set C : Finset (Fin 12) := D.filter (fun v => (G.neighborFinset v ∩ D).card = 2) with hCdef
  have hCsubD : C ⊆ D := Finset.filter_subset _ _
  have hCval : ∀ c ∈ C, (G.neighborFinset c ∩ D).card = 2 := fun c hc =>
    (Finset.mem_filter.mp hc).2
  have hCmem : ∀ w ∈ D, 1 ≤ (G.neighborFinset w ∩ D).card → w ∈ C := by
    intro w hwD hpos
    rw [hCdef, Finset.mem_filter]
    refine ⟨hwD, ?_⟩
    have := hne1 w hwD
    have := hno3 w hwD
    omega
  have hCcard : C.card = 5 := by
    have hsplitf := Finset.sum_filter_add_sum_filter_not D
      (fun v => (G.neighborFinset v ∩ D).card = 2) (fun v => (G.neighborFinset v ∩ D).card)
    rw [← hCdef] at hsplitf
    have hC2 : ∑ v ∈ C, (G.neighborFinset v ∩ D).card = 2 * C.card := by
      rw [Finset.sum_congr rfl (fun v hv => hCval v hv), Finset.sum_const, smul_eq_mul, mul_comm]
    have hNC0 : ∑ v ∈ D.filter (fun v => ¬(G.neighborFinset v ∩ D).card = 2),
        (G.neighborFinset v ∩ D).card = 0 := by
      apply Finset.sum_eq_zero
      intro v hv
      rw [Finset.mem_filter] at hv
      obtain ⟨hvD, hne⟩ := hv
      have := hne1 v hvD
      have := hno3 v hvD
      omega
    rw [hC2, hNC0, heM5] at hsplitf
    omega
  -- Step 3: each `C`-vertex has exactly one hub neighbour.
  have hHub1 : ∀ c ∈ C, (G.neighborFinset c ∩ Hub).card = 1 := by
    intro c hc
    have hcD := hCsubD hc
    have hs := hsplit c
    have hd := hdeg3 c hcD
    have hc2 := hCval c hc
    omega
  -- Step 4: pigeonhole the five single hubs over four hubs.
  have hsum5 : ∑ g ∈ Hub, (G.neighborFinset g ∩ C).card = 5 := by
    rw [← cross_count G C Hub]
    calc ∑ c ∈ C, (G.neighborFinset c ∩ Hub).card
        = ∑ _c ∈ C, 1 := Finset.sum_congr rfl hHub1
      _ = C.card := by rw [Finset.sum_const, smul_eq_mul, mul_one]
      _ = 5 := hCcard
  have hg2 : ∃ g ∈ Hub, 2 ≤ (G.neighborFinset g ∩ C).card := by
    by_contra hcon
    push Not at hcon
    have hle : ∑ g ∈ Hub, (G.neighborFinset g ∩ C).card ≤ Hub.card := by
      calc ∑ g ∈ Hub, (G.neighborFinset g ∩ C).card
          ≤ ∑ _g ∈ Hub, 1 := Finset.sum_le_sum (fun g hg => by have := hcon g hg; omega)
        _ = Hub.card := by rw [Finset.sum_const, smul_eq_mul, mul_one]
    rw [hR.hHcard] at hle
    omega
  -- Step 5: two `C`-vertices share a hub `g`.
  obtain ⟨g, hgHub, hgcard⟩ := hg2
  obtain ⟨a, haGC, b, hbGC, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < (G.neighborFinset g ∩ C).card)
  have hga : G.Adj g a := (G.mem_neighborFinset g a).mp (Finset.mem_inter.mp haGC).1
  have hgb : G.Adj g b := (G.mem_neighborFinset g b).mp (Finset.mem_inter.mp hbGC).1
  have haC : a ∈ C := (Finset.mem_inter.mp haGC).2
  have hbC : b ∈ C := (Finset.mem_inter.mp hbGC).2
  have haD : a ∈ D := hCsubD haC
  have hbD : b ∈ D := hCsubD hbC
  have hgdeg : G.degree g = 4 := hHdeg4 g hgHub
  have hadeg : G.degree a = 3 := hdeg3 a haD
  have hbdeg : G.degree b = 3 := hdeg3 b hbD
  -- `a, b` non-adjacent (else a forbidden triangle through `g`).
  have hnab : ¬G.Adj a b := hub_nbrs_nonadj G hT hgdeg hadeg hbdeg hab hga hgb
  -- Step 6: `a, b` have a common `M`-neighbour `mid` (cardinality of `C`).
  have hNsubC : ∀ x ∈ C, G.neighborFinset x ∩ D ⊆ C := by
    intro x hx w hw
    obtain ⟨hwN, hwD⟩ := Finset.mem_inter.mp hw
    apply hCmem w hwD
    apply Finset.card_pos.mpr
    exact ⟨x, by
      rw [Finset.mem_inter, G.mem_neighborFinset]
      exact ⟨((G.mem_neighborFinset x w).mp hwN).symm, hCsubD hx⟩⟩
  have ha_na : a ∉ G.neighborFinset a ∩ D := fun h =>
    G.irrefl ((G.mem_neighborFinset a a).mp (Finset.mem_inter.mp h).1)
  have hb_na : b ∉ G.neighborFinset a ∩ D := fun h =>
    hnab ((G.mem_neighborFinset a b).mp (Finset.mem_inter.mp h).1)
  have ha_nb : a ∉ G.neighborFinset b ∩ D := fun h =>
    hnab (((G.mem_neighborFinset b a).mp (Finset.mem_inter.mp h).1).symm)
  have hb_nb : b ∉ G.neighborFinset b ∩ D := fun h =>
    G.irrefl ((G.mem_neighborFinset b b).mp (Finset.mem_inter.mp h).1)
  have hmid : ((G.neighborFinset a ∩ D) ∩ (G.neighborFinset b ∩ D)).Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty, ← Finset.disjoint_iff_inter_eq_empty] at hemp
    have hsubC : (G.neighborFinset a ∩ D) ∪ (G.neighborFinset b ∩ D) ∪ {a, b} ⊆ C := by
      apply Finset.union_subset (Finset.union_subset (hNsubC a haC) (hNsubC b hbC))
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact haC
      · exact hbC
    have hdA : Disjoint (G.neighborFinset a ∩ D) ({a, b} : Finset (Fin 12)) := by
      rw [Finset.disjoint_right]
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact ha_na
      · exact hb_na
    have hdB : Disjoint (G.neighborFinset b ∩ D) ({a, b} : Finset (Fin 12)) := by
      rw [Finset.disjoint_right]
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact ha_nb
      · exact hb_nb
    have hdisjAB : Disjoint ((G.neighborFinset a ∩ D) ∪ (G.neighborFinset b ∩ D))
        ({a, b} : Finset (Fin 12)) := Finset.disjoint_union_left.mpr ⟨hdA, hdB⟩
    have hcardab : ({a, b} : Finset (Fin 12)).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simp [hab]), Finset.card_singleton]
    have hcardU : ((G.neighborFinset a ∩ D) ∪ (G.neighborFinset b ∩ D) ∪ {a, b}).card = 6 := by
      rw [Finset.card_union_of_disjoint hdisjAB, Finset.card_union_of_disjoint hemp,
        hCval a haC, hCval b hbC, hcardab]
    have hle := Finset.card_le_card hsubC
    rw [hcardU, hCcard] at hle
    omega
  obtain ⟨mid, hmidmem⟩ := hmid
  rw [Finset.mem_inter] at hmidmem
  obtain ⟨hmidA, hmidB⟩ := hmidmem
  have hamid : G.Adj a mid := (G.mem_neighborFinset a mid).mp (Finset.mem_inter.mp hmidA).1
  have hbmid : G.Adj b mid := (G.mem_neighborFinset b mid).mp (Finset.mem_inter.mp hmidB).1
  have hmidD : mid ∈ D := (Finset.mem_inter.mp hmidA).2
  have hmiddeg : G.degree mid = 3 := hdeg3 mid hmidD
  -- Step 7: triangle (if `g ~ mid`) or good `C₄` (otherwise).
  have hgmidne : g ≠ mid := by intro h; subst h; omega
  by_cases hgmid : G.Adj g mid
  · exact hT ⟨g, a, mid, hga.ne, hamid.ne, hgmidne, hga, hamid, hgmid, by omega⟩
  · have hcard4 : ({g, a, mid, b} : Finset (Fin 12)).card = 4 :=
      card_four g a mid b hga.ne hgmidne hgb.ne hamid.ne hab hbmid.ne'
    exact good_C4_of_witnesses G hC4 g a mid b hcard4 hga hamid hbmid.symm hgb.symm hgmid hnab
      (by omega)

/-- **`e(M)=4` exclusion.**  When `e(M)=4` (so `∑_{v∈D}|N v ∩ D| = 8`, no hub–hub edge), the
hub–`D` incidence count and pigeonhole force a good `K_{2,3}` or good `C₄`, a contradiction. -/
theorem eM_four_no_residual (G : SimpleGraph (Fin 12)) (D Hub : Finset (Fin 12))
    (hR : Residual G D Hub)
    (hT : ¬∃ x y z : Fin 12, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    (h2k2 : ¬∃ a b c d : Fin 12, ({a, b, c, d} : Finset (Fin 12)).card = 4 ∧
      G.degree a = 3 ∧ G.degree b = 3 ∧ G.degree c = 3 ∧ G.degree d = 3 ∧
      G.Adj a b ∧ G.Adj c d ∧ ¬G.Adj a c ∧ ¬G.Adj a d ∧ ¬G.Adj b c ∧ ¬G.Adj b d)
    (hC4 : ¬∃ a b c d : Fin 12, ({a, b, c, d} : Finset (Fin 12)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 13)
    (_hK23 : ¬∃ a b c d e : Fin 12, ({a, b, c, d, e} : Finset (Fin 12)).card = 5 ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
      G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 17)
    (heM4 : ∑ v ∈ D, (G.neighborFinset v ∩ D).card = 8)
    (_heH0 : ∑ v ∈ Hub, (G.neighborFinset v ∩ Hub).card = 0) : False := by
  classical
  have hmemND : ∀ v z : Fin 12, z ∈ G.neighborFinset v ∩ D ↔ G.Adj v z ∧ z ∈ D := by
    intro v z; rw [Finset.mem_inter, G.mem_neighborFinset]
  have hDHdisj : Disjoint D Hub := by
    rw [Finset.disjoint_left]
    intro v hvD hvH
    have := (hR.hDmem v).mp hvD; have := (hR.hHmem v).mp hvH; omega
  have hcover : D ∪ Hub = Finset.univ := by
    rw [Finset.eq_univ_iff_forall]; intro v
    rcases hR.hpart v with h | h
    · exact Finset.mem_union_left _ h
    · exact Finset.mem_union_right _ h
  have hsplit : ∀ v : Fin 12,
      (G.neighborFinset v ∩ D).card + (G.neighborFinset v ∩ Hub).card = G.degree v := by
    intro v
    have hdisj : Disjoint (G.neighborFinset v ∩ D) (G.neighborFinset v ∩ Hub) :=
      hDHdisj.mono Finset.inter_subset_right Finset.inter_subset_right
    have huni : (G.neighborFinset v ∩ D) ∪ (G.neighborFinset v ∩ Hub) = G.neighborFinset v := by
      rw [← Finset.inter_union_distrib_left, hcover, Finset.inter_univ]
    rw [← Finset.card_union_of_disjoint hdisj, huni, G.card_neighborFinset_eq_degree]
  by_cases hu : ∃ u ∈ D, (G.neighborFinset u ∩ D).card = 3
  · -- **Case A: an in-`M`-degree-3 vertex `u`.**
    obtain ⟨u, huD, hu3⟩ := hu
    have hudeg : G.degree u = 3 := (hR.hDmem u).mp huD
    have hNuD : G.neighborFinset u ⊆ D := by
      have hsub : G.neighborFinset u ∩ D ⊆ G.neighborFinset u := Finset.inter_subset_left
      have hcle : (G.neighborFinset u).card ≤ (G.neighborFinset u ∩ D).card := by
        rw [hu3, G.card_neighborFinset_eq_degree, hudeg]
      exact Finset.inter_eq_left.mp (Finset.eq_of_subset_of_card_le hsub hcle)
    obtain ⟨y, z, w, hyz, hyw, hzw, hset⟩ := Finset.card_eq_three.mp hu3
    have hymem : G.Adj u y ∧ y ∈ D := (hmemND u y).mp (by rw [hset]; simp)
    have hzmem : G.Adj u z ∧ z ∈ D := (hmemND u z).mp (by rw [hset]; simp)
    have hwmem : G.Adj u w ∧ w ∈ D := (hmemND u w).mp (by rw [hset]; simp)
    obtain ⟨huy, hyD⟩ := hymem
    obtain ⟨huz, hzD⟩ := hzmem
    obtain ⟨huw, hwD⟩ := hwmem
    have hydeg : G.degree y = 3 := (hR.hDmem y).mp hyD
    have hzdeg : G.degree z = 3 := (hR.hDmem z).mp hzD
    have hwdeg : G.degree w = 3 := (hR.hDmem w).mp hwD
    have huny : u ≠ y := huy.ne
    have hunz : u ≠ z := huz.ne
    have hunw : u ≠ w := huw.ne
    -- The three neighbours are pairwise non-adjacent (else a good triangle through `u`).
    have hnyz : ¬G.Adj y z := fun h =>
      hT ⟨u, y, z, huny, hyz, hunz, huy, h, huz, by omega⟩
    have hnyw : ¬G.Adj y w := fun h =>
      hT ⟨u, y, w, huny, hyw, hunw, huy, h, huw, by omega⟩
    have hnzw : ¬G.Adj z w := fun h =>
      hT ⟨u, z, w, hunz, hzw, hunw, huz, h, huw, by omega⟩
    -- `u`'s neighbours are not hubs (its whole neighbourhood is inside `D`).
    have hunhub : ∀ g : Fin 12, g ∈ Hub → ¬G.Adj u g := by
      intro g hg hadj
      have : g ∈ D := hNuD ((G.mem_neighborFinset u g).mpr hadj)
      exact (Finset.disjoint_left.mp hDHdisj this) hg
    -- A good `C₄` `g–p–u–q` from any hub `g` joined to two of `{y,z,w}`.
    have mkC4 : ∀ p q : Fin 12, p ∈ D → q ∈ D → G.Adj u p → G.Adj u q → p ≠ q →
        ¬G.Adj p q → ∀ g : Fin 12, g ∈ Hub → G.Adj p g → G.Adj q g → False := by
      intro p q hpD hqD hup huq hpq hnpq g hg hpg hqg
      have hgdeg : G.degree g = 4 := (hR.hHmem g).mp hg
      have hpdeg : G.degree p = 3 := (hR.hDmem p).mp hpD
      have hqdeg : G.degree q = 3 := (hR.hDmem q).mp hqD
      have hgu : ¬G.Adj g u := fun h => hunhub g hg h.symm
      have hgp : g ≠ p := fun h => by rw [h] at hgdeg; omega
      have hgq : g ≠ q := fun h => by rw [h] at hgdeg; omega
      have hgu' : g ≠ u := fun h => by rw [h] at hgdeg; omega
      have hcard : ({g, p, u, q} : Finset (Fin 12)).card = 4 := by
        rw [Finset.card_insert_of_notMem (by simp [hgp, hgu', hgq]),
            Finset.card_insert_of_notMem (by simp [hup.ne', hpq]),
            Finset.card_insert_of_notMem (by simp [huq.ne]), Finset.card_singleton]
      exact good_C4_of_witnesses G hC4 g p u q hcard hpg.symm hup.symm huq hqg hgu
        hnpq (by omega)
    -- The in-`M`-degree of `y,z,w` equals `3` minus the number of hub-neighbours.
    have hinM : ∀ p : Fin 12, G.degree p = 3 →
        (G.neighborFinset p ∩ D).card + (G.neighborFinset p ∩ Hub).card = 3 := by
      intro p hp; rw [hsplit p, hp]
    -- Overflow lemma: a vertex among `{y,z,w}` with in-`M`-degree `≥ 2` yields a contradiction
    -- once `inMdeg y + inMdeg z + inMdeg w ≥ 5`.
    have overflow : (G.neighborFinset y ∩ D).card + (G.neighborFinset z ∩ D).card
          + (G.neighborFinset w ∩ D).card ≥ 5 →
        ∀ v0 : Fin 12, (v0 = y ∨ v0 = z ∨ v0 = w) →
          2 ≤ (G.neighborFinset v0 ∩ D).card → False := by
      intro hge5 v0 hv0 hv0deg
      have hv0u : u ∈ G.neighborFinset v0 ∩ D := by
        rcases hv0 with rfl | rfl | rfl
        · exact (hmemND v0 u).mpr ⟨huy.symm, huD⟩
        · exact (hmemND v0 u).mpr ⟨huz.symm, huD⟩
        · exact (hmemND v0 u).mpr ⟨huw.symm, huD⟩
      have hne : ((G.neighborFinset v0 ∩ D).erase u).Nonempty := by
        rw [← Finset.card_pos, Finset.card_erase_of_mem hv0u]; omega
      obtain ⟨m, hm⟩ := hne
      rw [Finset.mem_erase] at hm
      obtain ⟨hmu, hmmem⟩ := hm
      rw [hmemND] at hmmem
      obtain ⟨hv0m, hmD⟩ := hmmem
      have hmnotyzw : m ≠ y ∧ m ≠ z ∧ m ≠ w := by
        refine ⟨?_, ?_, ?_⟩ <;> rintro rfl <;> rcases hv0 with rfl | rfl | rfl
        · exact G.irrefl hv0m
        · exact hnyz hv0m.symm
        · exact hnyw hv0m.symm
        · exact hnyz hv0m
        · exact G.irrefl hv0m
        · exact hnzw hv0m.symm
        · exact hnyw hv0m
        · exact hnzw hv0m
        · exact G.irrefl hv0m
      obtain ⟨hmy, hmz, hmw⟩ := hmnotyzw
      have hT5 : ({u, y, z, w, m} : Finset (Fin 12)) ⊆ D := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl
        · exact huD
        · exact hyD
        · exact hzD
        · exact hwD
        · exact hmD
      have hTsum : ∑ x ∈ ({u, y, z, w, m} : Finset (Fin 12)), (G.neighborFinset x ∩ D).card
          = (G.neighborFinset u ∩ D).card + (G.neighborFinset y ∩ D).card
            + (G.neighborFinset z ∩ D).card + (G.neighborFinset w ∩ D).card
            + (G.neighborFinset m ∩ D).card := by
        rw [Finset.sum_insert (by simp [huny, hunz, hunw, Ne.symm hmu]),
            Finset.sum_insert (by simp [hyz, hyw, Ne.symm hmy]),
            Finset.sum_insert (by simp [hzw, Ne.symm hmz]),
            Finset.sum_insert (by simp [Ne.symm hmw]), Finset.sum_singleton]
        ring
      have hle8 : ∑ x ∈ ({u, y, z, w, m} : Finset (Fin 12)), (G.neighborFinset x ∩ D).card ≤ 8 := by
        rw [← heM4]; exact Finset.sum_le_sum_of_subset hT5
      have hmpos : 1 ≤ (G.neighborFinset m ∩ D).card :=
        Finset.card_pos.mpr ⟨v0, (hmemND m v0).mpr ⟨hv0m.symm, by
          rcases hv0 with rfl | rfl | rfl; exacts [hyD, hzD, hwD]⟩⟩
      rw [hTsum] at hle8; omega
    -- Two of the hub-neighbourhoods `Ny, Nz, Nw` intersect, else overflow.
    have hshare : (¬Disjoint (G.neighborFinset y ∩ Hub) (G.neighborFinset z ∩ Hub)) ∨
        (¬Disjoint (G.neighborFinset y ∩ Hub) (G.neighborFinset w ∩ Hub)) ∨
        (¬Disjoint (G.neighborFinset z ∩ Hub) (G.neighborFinset w ∩ Hub)) := by
      by_contra hcon
      push Not at hcon
      obtain ⟨hdYZ, hdYW, hdZW⟩ := hcon
      have hunionsub : (G.neighborFinset y ∩ Hub) ∪ (G.neighborFinset z ∩ Hub)
          ∪ (G.neighborFinset w ∩ Hub) ⊆ Hub := by
        apply Finset.union_subset (Finset.union_subset _ _) _ <;> exact Finset.inter_subset_right
      have hcardsum : (G.neighborFinset y ∩ Hub).card + (G.neighborFinset z ∩ Hub).card
          + (G.neighborFinset w ∩ Hub).card ≤ 4 := by
        have h1 : ((G.neighborFinset y ∩ Hub) ∪ (G.neighborFinset z ∩ Hub)).card
            = (G.neighborFinset y ∩ Hub).card + (G.neighborFinset z ∩ Hub).card :=
          Finset.card_union_of_disjoint hdYZ
        have h2 : Disjoint ((G.neighborFinset y ∩ Hub) ∪ (G.neighborFinset z ∩ Hub))
            (G.neighborFinset w ∩ Hub) := Finset.disjoint_union_left.mpr ⟨hdYW, hdZW⟩
        have h3 : (((G.neighborFinset y ∩ Hub) ∪ (G.neighborFinset z ∩ Hub))
            ∪ (G.neighborFinset w ∩ Hub)).card
            = (G.neighborFinset y ∩ Hub).card + (G.neighborFinset z ∩ Hub).card
              + (G.neighborFinset w ∩ Hub).card := by
          rw [Finset.card_union_of_disjoint h2, h1]
        have h4 := Finset.card_le_card hunionsub
        rw [h3, hR.hHcard] at h4; exact h4
      have hy3 := hinM y hydeg
      have hz3 := hinM z hzdeg
      have hw3 := hinM w hwdeg
      have hge5 : (G.neighborFinset y ∩ D).card + (G.neighborFinset z ∩ D).card
          + (G.neighborFinset w ∩ D).card ≥ 5 := by omega
      have : 2 ≤ (G.neighborFinset y ∩ D).card ∨ 2 ≤ (G.neighborFinset z ∩ D).card
          ∨ 2 ≤ (G.neighborFinset w ∩ D).card := by omega
      rcases this with h | h | h
      · exact overflow hge5 y (Or.inl rfl) h
      · exact overflow hge5 z (Or.inr (Or.inl rfl)) h
      · exact overflow hge5 w (Or.inr (Or.inr rfl)) h
    -- Extract the shared hub and build the good `C₄`.
    rcases hshare with h | h | h
    · obtain ⟨g, hgy, hgz⟩ := Finset.not_disjoint_iff.mp h
      rw [Finset.mem_inter, G.mem_neighborFinset] at hgy hgz
      exact mkC4 y z hyD hzD huy huz hyz hnyz g hgy.2 hgy.1 hgz.1
    · obtain ⟨g, hgy, hgw⟩ := Finset.not_disjoint_iff.mp h
      rw [Finset.mem_inter, G.mem_neighborFinset] at hgy hgw
      exact mkC4 y w hyD hwD huy huw hyw hnyw g hgy.2 hgy.1 hgw.1
    · obtain ⟨g, hgz, hgw⟩ := Finset.not_disjoint_iff.mp h
      rw [Finset.mem_inter, G.mem_neighborFinset] at hgz hgw
      exact mkC4 z w hzD hwD huz huw hzw hnzw g hgz.2 hgz.1 hgw.1
  · -- **Case B: all in-`M`-degrees `≤ 2`.**
    push Not at hu
    have hle2 : ∀ v ∈ D, (G.neighborFinset v ∩ D).card ≤ 2 := by
      intro v hv
      have hne : (G.neighborFinset v ∩ D).card ≠ 3 := hu v hv
      have hdeg : (G.neighborFinset v ∩ D).card ≤ G.degree v := by
        rw [← G.card_neighborFinset_eq_degree]; exact Finset.card_le_card Finset.inter_subset_left
      have : G.degree v = 3 := (hR.hDmem v).mp hv
      omega
    have hdeg3 : ∀ v ∈ D, G.degree v = 3 := fun v hv => (hR.hDmem v).mp hv
    have hne0 : ∑ v ∈ D, (G.neighborFinset v ∩ D).card ≠ 0 := by rw [heM4]; norm_num
    obtain ⟨a, haD, hane⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne0
    obtain ⟨b, hb⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hane)
    rw [hmemND] at hb
    obtain ⟨hab, hbD⟩ := hb
    obtain ⟨c, d, hcD, hdD, hca, hcb, hda, hdb, hcd⟩ :=
      exists_disjoint_edge G D heM4 hle2 a b haD hbD hab
    have hcard4 : ({a, b, c, d} : Finset (Fin 12)).card = 4 :=
      card_four a b c d hab.ne (Ne.symm hca) (Ne.symm hda) (Ne.symm hcb) (Ne.symm hdb) hcd.ne
    rcases M_edges_joined G h2k2 a b c d hcard4 (hdeg3 a haD) (hdeg3 b hbD) (hdeg3 c hcD)
        (hdeg3 d hdD) hab hcd with h | h | h | h
    · exact cross_kill G D h2k2 hC4 heM4 hle2 hdeg3 a b c d haD hbD hcD hdD
        hab.ne (Ne.symm hca) (Ne.symm hda) (Ne.symm hcb) (Ne.symm hdb) hcd.ne hab hcd h
    · exact cross_kill G D h2k2 hC4 heM4 hle2 hdeg3 a b d c haD hbD hdD hcD
        hab.ne (Ne.symm hda) (Ne.symm hca) (Ne.symm hdb) (Ne.symm hcb) (Ne.symm hcd.ne)
        hab hcd.symm h
    · exact cross_kill G D h2k2 hC4 heM4 hle2 hdeg3 b a c d hbD haD hcD hdD
        (Ne.symm hab.ne) (Ne.symm hcb) (Ne.symm hdb) (Ne.symm hca) (Ne.symm hda) hcd.ne
        hab.symm hcd h
    · exact cross_kill G D h2k2 hC4 heM4 hle2 hdeg3 b a d c hbD haD hdD hcD
        (Ne.symm hab.ne) (Ne.symm hdb) (Ne.symm hcb) (Ne.symm hda) (Ne.symm hca) (Ne.symm hcd.ne)
        hab.symm hcd.symm h

end N12

end ACMax
