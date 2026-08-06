import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N13.Struct

/-!
# Structural core lemmas for the `n = 13` twin certificate

This file isolates rigorously-provable combinatorial building blocks for the `n = 13` ACMAX
residual.  In that regime the graph has `22` edges, minimum degree `3`, and (by
`residual_hub_card_le_five`) the hub set `Hub = filter (4 ≤ deg)` has `Hub.card ≤ 5` while the
degree-3 set `D = filter (deg = 3)` has `8 ≤ D.card`.

We prove here the genuinely *local*, axiom-clean fact that feeds the witness assembly:

* `hub_meets_path_le_one` — a **degree-4** hub `h` is adjacent to at most one vertex of any
  induced `P₃` `x–y–z` of degree-3 vertices (two adjacent hits give a good triangle via `hT`;
  the two endpoints give a good `C₄` via `hC4`).
-/

namespace ACMax

open scoped Classical

namespace N13

/-- **No-`C₄`/triangle hub bound.**  A degree-4 hub `h` meets at most one vertex of any induced
`P₃` `x–y–z` of degree-3 vertices: two adjacent hits (`h~x ∧ h~y` or `h~y ∧ h~z`) form a good
triangle of degree-sum `10` (`hT`); the two endpoints (`h~x ∧ h~z`) form a good induced `C₄`
`h–x–y–z–h` of degree-sum `13` (`hC4`), the diagonal `h~y` reducing to the triangle case. -/
theorem hub_meets_path_le_one (G : SimpleGraph (Fin 13))
    (hT : ¬∃ x y z : Fin 13, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    (hC4 : ¬∃ a b c d : Fin 13, ({a, b, c, d} : Finset (Fin 13)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 13)
    {h x y z : Fin 13} (hh : G.degree h = 4)
    (hx : G.degree x = 3) (hy : G.degree y = 3) (hz : G.degree z = 3)
    (hxy : G.Adj x y) (hyz : G.Adj y z) (hxz : ¬G.Adj x z)
    (hne_xy : x ≠ y) (hne_yz : y ≠ z) (hne_xz : x ≠ z) :
    ¬(G.Adj h x ∧ G.Adj h y) ∧ ¬(G.Adj h y ∧ G.Adj h z) ∧ ¬(G.Adj h x ∧ G.Adj h z) := by
  have hne_hx : h ≠ x := by intro e; subst e; omega
  have hne_hy : h ≠ y := by intro e; subst e; omega
  have hne_hz : h ≠ z := by intro e; subst e; omega
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨hhx, hhy⟩
    exact hT ⟨h, x, y, hne_hx, hne_xy, hne_hy, hhx, hxy, hhy, by omega⟩
  · rintro ⟨hhy, hhz⟩
    exact hT ⟨h, y, z, hne_hy, hne_yz, hne_hz, hhy, hyz, hhz, by omega⟩
  · rintro ⟨hhx, hhz⟩
    by_cases hhy : G.Adj h y
    · exact hT ⟨h, x, y, hne_hx, hne_xy, hne_hy, hhx, hxy, hhy, by omega⟩
    · exact hC4 ⟨h, x, y, z,
        card_four_thirteen h x y z hne_hx hne_hy hne_hz hne_xy hne_xz hne_yz,
        hhx, hxy, hyz, hhz.symm, hhy, hxz, by omega⟩

/-- **Bipartite double count.**  For any two vertex sets, the number of `X→Y` incidences equals
the number of `Y→X` incidences. -/
theorem cross_count_thirteen (G : SimpleGraph (Fin 13)) (X Y : Finset (Fin 13)) :
    ∑ v ∈ X, (G.neighborFinset v ∩ Y).card = ∑ w ∈ Y, (G.neighborFinset w ∩ X).card := by
  have hL : ∀ v : Fin 13, (G.neighborFinset v ∩ Y).card
      = ∑ w ∈ Y, (if G.Adj v w then 1 else 0) := by
    intro v
    rw [Finset.inter_comm, ← Finset.filter_mem_eq_inter, Finset.card_filter]
    exact Finset.sum_congr rfl (fun w _ => by simp only [G.mem_neighborFinset])
  have hR : ∀ w : Fin 13, (G.neighborFinset w ∩ X).card
      = ∑ v ∈ X, (if G.Adj v w then 1 else 0) := by
    intro w
    rw [Finset.inter_comm, ← Finset.filter_mem_eq_inter, Finset.card_filter]
    exact Finset.sum_congr rfl
      (fun v _ => by simp only [G.mem_neighborFinset, SimpleGraph.adj_comm])
  simp_rw [hL, hR]
  exact Finset.sum_comm

/-- **NODE 1 — edge bound for `M = G[D]` (structural).**  The degree-3 subgraph `M` is
triangle-free (`hT`), `C₄`-free (`hC4`) and `2K₂`-free (`h2k2`) with max in-`M`-degree `≤ 3`
(every `D`-vertex has degree `3`).  A `2K₂`-free graph has all its edges in one component; with
girth `≥ 5` (triangle + `C₄`-free) and max-degree `≤ 3` that component is a double-star (`≤ 5`
edges) or `C₅` (`5` edges), so `e(M) ≤ 5`, i.e. `∑_{v∈D}|N v ∩ D| = 2·e(M) ≤ 10`. -/
theorem eM_le_five (G : SimpleGraph (Fin 13)) (D : Finset (Fin 13))
    (hmemD : ∀ v : Fin 13, v ∈ D ↔ G.degree v = 3)
    (hT : ¬∃ x y z : Fin 13, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    (hC4 : ¬∃ a b c d : Fin 13, ({a, b, c, d} : Finset (Fin 13)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 13)
    (h2k2 : ¬∃ a b c d : Fin 13, ({a, b, c, d} : Finset (Fin 13)).card = 4 ∧
      G.degree a = 3 ∧ G.degree b = 3 ∧ G.degree c = 3 ∧ G.degree d = 3 ∧
      G.Adj a b ∧ G.Adj c d ∧ ¬G.Adj a c ∧ ¬G.Adj a d ∧ ¬G.Adj b c ∧ ¬G.Adj b d) :
    ∑ v ∈ D, (G.neighborFinset v ∩ D).card ≤ 10 := by
  classical
  have hindle : ∀ x : Fin 13, x ∈ D → (G.neighborFinset x ∩ D).card ≤ 3 := by
    intro x hx
    calc (G.neighborFinset x ∩ D).card ≤ (G.neighborFinset x).card :=
          Finset.card_le_card Finset.inter_subset_left
      _ = G.degree x := G.card_neighborFinset_eq_degree x
      _ = 3 := (hmemD x).mp hx
  by_cases hne : ∃ a b : Fin 13, a ∈ D ∧ b ∈ D ∧ G.Adj a b
  · rcases dominating_edge_or_induced_C5 G D hmemD hT hC4 h2k2 hne with hA | hB
    · -- **Dominating edge.**
      obtain ⟨c₁, c₂, hc1D, hc2D, hc12, hcov⟩ := hA
      have hsub : ({c₁, c₂} : Finset (Fin 13)) ⊆ D := by
        intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl; exacts [hc1D, hc2D]
      have hsplit :
          ∑ v ∈ D \ ({c₁, c₂} : Finset (Fin 13)), (G.neighborFinset v ∩ D).card
            + ∑ v ∈ ({c₁, c₂} : Finset (Fin 13)), (G.neighborFinset v ∩ D).card
          = ∑ v ∈ D, (G.neighborFinset v ∩ D).card :=
        Finset.sum_sdiff hsub
      have hpair : ∑ v ∈ ({c₁, c₂} : Finset (Fin 13)), (G.neighborFinset v ∩ D).card
          = (G.neighborFinset c₁ ∩ D).card + (G.neighborFinset c₂ ∩ D).card := by
        rw [Finset.sum_insert (by simp [hc12.ne]), Finset.sum_singleton]
      have hScong :
          ∑ v ∈ D \ ({c₁, c₂} : Finset (Fin 13)), (G.neighborFinset v ∩ D).card
            = ∑ v ∈ D \ ({c₁, c₂} : Finset (Fin 13)),
              (G.neighborFinset v ∩ ({c₁, c₂} : Finset (Fin 13))).card := by
        apply Finset.sum_congr rfl
        intro v hv
        rw [Finset.mem_sdiff] at hv
        obtain ⟨hvD, hvnot⟩ := hv
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hvnot
        congr 1
        apply Finset.Subset.antisymm
        · intro w hw
          obtain ⟨hwN, hwD⟩ := Finset.mem_inter.mp hw
          have hvw : G.Adj v w := (G.mem_neighborFinset _ _).mp hwN
          rcases hcov v w hvD hwD hvw with e | e | e | e
          · exact absurd e hvnot.1
          · exact absurd e hvnot.2
          · exact Finset.mem_inter.mpr ⟨hwN, by rw [e]; simp⟩
          · exact Finset.mem_inter.mpr ⟨hwN, by rw [e]; simp⟩
        · intro w hw
          obtain ⟨hwN, hwm⟩ := Finset.mem_inter.mp hw
          exact Finset.mem_inter.mpr ⟨hwN, hsub hwm⟩
      rw [hScong,
        cross_count_thirteen G (D \ ({c₁, c₂} : Finset (Fin 13)))
          ({c₁, c₂} : Finset (Fin 13))] at hsplit
      have hpair2 : ∑ w ∈ ({c₁, c₂} : Finset (Fin 13)),
            (G.neighborFinset w ∩ (D \ ({c₁, c₂} : Finset (Fin 13)))).card
          = (G.neighborFinset c₁ ∩ (D \ ({c₁, c₂} : Finset (Fin 13)))).card
            + (G.neighborFinset c₂ ∩ (D \ ({c₁, c₂} : Finset (Fin 13)))).card := by
        rw [Finset.sum_insert (by simp [hc12.ne]), Finset.sum_singleton]
      have hb1 : (G.neighborFinset c₁ ∩ (D \ ({c₁, c₂} : Finset (Fin 13)))).card ≤ 2 := by
        have hss : G.neighborFinset c₁ ∩ (D \ ({c₁, c₂} : Finset (Fin 13)))
            ⊆ (G.neighborFinset c₁ ∩ D).erase c₂ := by
          intro w hw
          obtain ⟨hwN, hwS⟩ := Finset.mem_inter.mp hw
          rw [Finset.mem_sdiff] at hwS
          obtain ⟨hwD, hwnot⟩ := hwS
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hwnot
          rw [Finset.mem_erase]
          exact ⟨hwnot.2, Finset.mem_inter.mpr ⟨hwN, hwD⟩⟩
        have hc2mem : c₂ ∈ G.neighborFinset c₁ ∩ D :=
          Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hc12, hc2D⟩
        calc (G.neighborFinset c₁ ∩ (D \ ({c₁, c₂} : Finset (Fin 13)))).card
            ≤ ((G.neighborFinset c₁ ∩ D).erase c₂).card := Finset.card_le_card hss
          _ = (G.neighborFinset c₁ ∩ D).card - 1 := Finset.card_erase_of_mem hc2mem
          _ ≤ 2 := by have := hindle c₁ hc1D; omega
      have hb2 : (G.neighborFinset c₂ ∩ (D \ ({c₁, c₂} : Finset (Fin 13)))).card ≤ 2 := by
        have hss : G.neighborFinset c₂ ∩ (D \ ({c₁, c₂} : Finset (Fin 13)))
            ⊆ (G.neighborFinset c₂ ∩ D).erase c₁ := by
          intro w hw
          obtain ⟨hwN, hwS⟩ := Finset.mem_inter.mp hw
          rw [Finset.mem_sdiff] at hwS
          obtain ⟨hwD, hwnot⟩ := hwS
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hwnot
          rw [Finset.mem_erase]
          exact ⟨hwnot.1, Finset.mem_inter.mpr ⟨hwN, hwD⟩⟩
        have hc1mem : c₁ ∈ G.neighborFinset c₂ ∩ D :=
          Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hc12.symm, hc1D⟩
        calc (G.neighborFinset c₂ ∩ (D \ ({c₁, c₂} : Finset (Fin 13)))).card
            ≤ ((G.neighborFinset c₂ ∩ D).erase c₁).card := Finset.card_le_card hss
          _ = (G.neighborFinset c₂ ∩ D).card - 1 := Finset.card_erase_of_mem hc1mem
          _ ≤ 2 := by have := hindle c₂ hc2D; omega
      have hi1 := hindle c₁ hc1D
      have hi2 := hindle c₂ hc2D
      rw [hpair2, hpair] at hsplit
      omega
    · -- **Induced `C₅` carrying all edges.**
      obtain ⟨v₁, v₂, v₃, v₄, v₅, hv1, hv2, hv3, hv4, hv5, hcard5,
        e12, e23, e34, e45, e51, n13, n14, n24, n25, n35, hcov⟩ := hB
      have nbhd : ∀ u na nb o1 o2 : Fin 13, ¬G.Adj u o1 → ¬G.Adj u o2 →
          (∀ w : Fin 13, w ∈ D → G.Adj u w →
            w = u ∨ w = na ∨ w = nb ∨ w = o1 ∨ w = o2) →
          (G.neighborFinset u ∩ D).card ≤ 2 := by
        intro u na nb o1 o2 hno1 hno2 hucov
        have hss : G.neighborFinset u ∩ D ⊆ ({na, nb} : Finset (Fin 13)) := by
          intro w hw
          obtain ⟨hwN, hwD⟩ := Finset.mem_inter.mp hw
          have huw : G.Adj u w := (G.mem_neighborFinset _ _).mp hwN
          rcases hucov w hwD huw with e | e | e | e | e
          · exact absurd (e ▸ huw) G.irrefl
          · rw [e]; simp
          · rw [e]; simp
          · exact absurd (e ▸ huw) hno1
          · exact absurd (e ▸ huw) hno2
        calc (G.neighborFinset u ∩ D).card ≤ ({na, nb} : Finset (Fin 13)).card :=
              Finset.card_le_card hss
          _ ≤ 2 := (Finset.card_insert_le _ _).trans (by simp)
      have hbound : ∀ v ∈ ({v₁, v₂, v₃, v₄, v₅} : Finset (Fin 13)),
          (G.neighborFinset v ∩ D).card ≤ 2 := by
        intro v hv
        simp only [Finset.mem_insert, Finset.mem_singleton] at hv
        rcases hv with rfl | rfl | rfl | rfl | rfl
        · exact nbhd v v₂ v₅ v₃ v₄ n13 n14
            (fun w hwD hvw => by have := hcov w v hwD hv1 hvw.symm; tauto)
        · exact nbhd v v₁ v₃ v₄ v₅ n24 n25
            (fun w hwD hvw => by have := hcov w v hwD hv2 hvw.symm; tauto)
        · exact nbhd v v₂ v₄ v₁ v₅ (fun h => n13 h.symm) n35
            (fun w hwD hvw => by have := hcov w v hwD hv3 hvw.symm; tauto)
        · exact nbhd v v₃ v₅ v₁ v₂ (fun h => n14 h.symm) (fun h => n24 h.symm)
            (fun w hwD hvw => by have := hcov w v hwD hv4 hvw.symm; tauto)
        · exact nbhd v v₄ v₁ v₂ v₃ (fun h => n25 h.symm) (fun h => n35 h.symm)
            (fun w hwD hvw => by have := hcov w v hwD hv5 hvw.symm; tauto)
      have hC5sub : ({v₁, v₂, v₃, v₄, v₅} : Finset (Fin 13)) ⊆ D := by
        intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl | rfl | rfl | rfl
        exacts [hv1, hv2, hv3, hv4, hv5]
      have hsplit :
          ∑ v ∈ D \ ({v₁, v₂, v₃, v₄, v₅} : Finset (Fin 13)), (G.neighborFinset v ∩ D).card
            + ∑ v ∈ ({v₁, v₂, v₃, v₄, v₅} : Finset (Fin 13)), (G.neighborFinset v ∩ D).card
          = ∑ v ∈ D, (G.neighborFinset v ∩ D).card :=
        Finset.sum_sdiff hC5sub
      have hiso : ∑ v ∈ D \ ({v₁, v₂, v₃, v₄, v₅} : Finset (Fin 13)),
          (G.neighborFinset v ∩ D).card = 0 := by
        apply Finset.sum_eq_zero
        intro v hv
        rw [Finset.mem_sdiff] at hv
        obtain ⟨hvD, hvnot⟩ := hv
        rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
        intro w hw
        obtain ⟨hwN, hwD⟩ := Finset.mem_inter.mp hw
        have hvw : G.Adj v w := (G.mem_neighborFinset _ _).mp hwN
        have hin := hcov v w hvD hwD hvw
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hvnot
        rcases hin with e | e | e | e | e
        exacts [hvnot.1 e, hvnot.2.1 e, hvnot.2.2.1 e, hvnot.2.2.2.1 e, hvnot.2.2.2.2 e]
      have hC5sum : ∑ v ∈ ({v₁, v₂, v₃, v₄, v₅} : Finset (Fin 13)),
          (G.neighborFinset v ∩ D).card ≤ 10 := by
        have h1 := Finset.sum_le_sum hbound
        rw [Finset.sum_const, smul_eq_mul, hcard5] at h1
        omega
      rw [hiso, zero_add] at hsplit
      omega
  · -- **No edge.**
    push Not at hne
    have hzero : ∀ v : Fin 13, v ∈ D → (G.neighborFinset v ∩ D).card = 0 := by
      intro v hv
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro w hw
      rw [Finset.mem_inter, G.mem_neighborFinset] at hw
      exact hne v w hv hw.2 hw.1
    calc ∑ v ∈ D, (G.neighborFinset v ∩ D).card
        = ∑ _v ∈ D, 0 := Finset.sum_congr rfl (fun v hv => hzero v hv)
      _ ≤ 10 := by simp

/-- **NODE 2 — two `M`-isolated twins.**  With `8 ≤ |D|`, `e(M) ≤ 5` (`heM`) and `M` `2K₂`-free,
the non-isolated vertices of `M` lie in a single connected component, so they number at most
`e(M) + 1 ≤ 6`; hence at least `8 − 6 = 2` degree-3 vertices are `M`-isolated. -/
theorem two_isolated_twins_thirteen (G : SimpleGraph (Fin 13)) (D : Finset (Fin 13))
    (hmemD : ∀ v : Fin 13, v ∈ D ↔ G.degree v = 3)
    (h2k2 : ¬∃ a b c d : Fin 13, ({a, b, c, d} : Finset (Fin 13)).card = 4 ∧
      G.degree a = 3 ∧ G.degree b = 3 ∧ G.degree c = 3 ∧ G.degree d = 3 ∧
      G.Adj a b ∧ G.Adj c d ∧ ¬G.Adj a c ∧ ¬G.Adj a d ∧ ¬G.Adj b c ∧ ¬G.Adj b d)
    (hD8 : 8 ≤ D.card)
    (heM : ∑ v ∈ D, (G.neighborFinset v ∩ D).card ≤ 10) :
    2 ≤ (D.filter (fun v => ∀ w : Fin 13, G.Adj v w → G.degree w ≠ 3)).card := by
  classical
  -- The non-isolated set `S` (positive in-`M`-degree).
  set S : Finset (Fin 13) := D.filter (fun v => ¬ (G.neighborFinset v ∩ D).card = 0) with hSdef
  -- For `v ∈ D`, being `M`-isolated is the same as having empty `D`-neighbourhood.
  have hiso_iff : ∀ v ∈ D, (∀ w : Fin 13, G.Adj v w → G.degree w ≠ 3)
      ↔ (G.neighborFinset v ∩ D).card = 0 := by
    intro v _
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    constructor
    · intro hp w hw
      rw [Finset.mem_inter, G.mem_neighborFinset] at hw
      exact hp w hw.1 ((hmemD w).mp hw.2)
    · intro hempty w hadj hw3
      exact hempty w (by rw [Finset.mem_inter, G.mem_neighborFinset]; exact ⟨hadj, (hmemD w).mpr hw3⟩)
  -- The isolated set equals `D` filtered by empty `D`-neighbourhood.
  have hfilter_eq : D.filter (fun v => ∀ w : Fin 13, G.Adj v w → G.degree w ≠ 3)
      = D.filter (fun v => (G.neighborFinset v ∩ D).card = 0) := by
    apply Finset.filter_congr
    intro v hv
    simp only [hiso_iff v hv]
  -- `S` is the complementary filter, so `|isolated| + |S| = |D|`.
  have hpartition : (D.filter (fun v => (G.neighborFinset v ∩ D).card = 0)).card + S.card
      = D.card := by
    rw [hSdef]
    exact Finset.card_filter_add_card_filter_not
      (s := D) (p := fun v => (G.neighborFinset v ∩ D).card = 0)
  -- Crux (`2K₂`-free single-component bound): the non-isolated set `S` is, by `2K₂`-freeness,
  -- a single connected component of `M = G[D]`; a connected graph on `S` has at most `e(M) + 1`
  -- vertices, and `2·e(M) = ∑_{v∈D}|N v ∩ D| ≤ 10` gives `e(M) ≤ 5`, so `|S| ≤ 6`.
  have hScard : S.card ≤ 6 := by
    classical
    -- The internal degree-3 graph `M = G[D]`.
    set M : SimpleGraph (Fin 13) :=
      { Adj := fun a b => G.Adj a b ∧ a ∈ D ∧ b ∈ D
        symm := ⟨fun a b h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
        loopless := ⟨fun a h => G.irrefl h.1⟩ } with hMdef
    have hMadj : ∀ a b : Fin 13, M.Adj a b ↔ G.Adj a b ∧ a ∈ D ∧ b ∈ D := fun _ _ => Iff.rfl
    -- Membership in the non-isolated set `S`.
    have hSmem : ∀ v : Fin 13, v ∈ S ↔ v ∈ D ∧ ∃ w : Fin 13, G.Adj v w ∧ w ∈ D := by
      intro v
      rw [hSdef, Finset.mem_filter]
      refine and_congr_right (fun _ => ?_)
      rw [← ne_eq, Finset.card_ne_zero]
      simp only [Finset.Nonempty, Finset.mem_inter, G.mem_neighborFinset]
    -- `M.support = ↑S`.
    have hsupp : M.support = (↑S : Set (Fin 13)) := by
      ext v
      rw [SimpleGraph.mem_support, Finset.mem_coe, hSmem]
      constructor
      · rintro ⟨w, hadj, hvD, hwD⟩; exact ⟨hvD, w, hadj, hwD⟩
      · rintro ⟨hvD, w, hadj, hwD⟩; exact ⟨w, hadj, hvD, hwD⟩
    -- `M`-degree of a vertex.
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
    -- Handshake: `2 e(M) = ∑_{v ∈ D} |N v ∩ D| ≤ 10`, so `e(M) ≤ 5`.
    have hsumM : ∑ v : Fin 13, M.degree v = ∑ v ∈ D, (G.neighborFinset v ∩ D).card := by
      simp_rw [hMdeg]
      rw [← Finset.sum_filter]
      congr 1
      ext v
      simp
    have hEM : M.edgeFinset.card ≤ 5 := by
      have hh := M.sum_degrees_eq_twice_card_edges
      rw [hsumM] at hh
      omega
    -- Connectivity of the induced subgraph on the support, via `2K₂`-freeness.
    rcases S.eq_empty_or_nonempty with hSe | hSne
    · rw [hSe]; simp
    · have hVne : Nonempty ↥M.support := by
        obtain ⟨x, hx⟩ := hSne
        exact ⟨⟨x, by rw [hsupp]; exact Finset.mem_coe.mpr hx⟩⟩
      have radj : ∀ {a b : Fin 13} (ha : a ∈ M.support) (hb : b ∈ M.support),
          M.Adj a b → (M.induce M.support).Reachable ⟨a, ha⟩ ⟨b, hb⟩ := by
        intro a b ha hb hab
        exact (SimpleGraph.induce_adj.mpr hab).reachable
      have hpre : (M.induce M.support).Preconnected := by
        intro u v
        set a : Fin 13 := (↑u : Fin 13) with hadef
        set b : Fin 13 := (↑v : Fin 13) with hbdef
        obtain ⟨a', haa'⟩ := u.2
        obtain ⟨b', hbb'⟩ := v.2
        replace haa' : M.Adj a a' := haa'
        replace hbb' : M.Adj b b' := hbb'
        have ha'supp : a' ∈ M.support := haa'.mem_support_right
        have hb'supp : b' ∈ M.support := hbb'.mem_support_right
        have hA := (hMadj a a').mp haa'
        have hB := (hMadj b b').mp hbb'
        have haD : a ∈ D := hA.2.1
        have ha'D : a' ∈ D := hA.2.2
        have hbD : b ∈ D := hB.2.1
        have hb'D : b' ∈ D := hB.2.2
        by_cases hab : a = b
        · have huv : u = v := Subtype.ext hab
          rw [huv]
        by_cases hab' : a = b'
        · have hadj : M.Adj a b := by
            rw [← hab'] at hbb'; exact hbb'.symm
          exact radj u.2 v.2 hadj
        by_cases ha'b : a' = b
        · have hadj : M.Adj a b := by rw [ha'b] at haa'; exact haa'
          exact radj u.2 v.2 hadj
        by_cases ha'b' : a' = b'
        · have hUV : (⟨a', ha'supp⟩ : ↥M.support) = ⟨b', hb'supp⟩ := Subtype.ext ha'b'
          exact (radj u.2 ha'supp haa').trans (hUV ▸ (radj v.2 hb'supp hbb').symm)
        · have hcard4 : ({a, a', b, b'} : Finset (Fin 13)).card = 4 :=
            card_four_thirteen a a' b b' haa'.ne hab hab' ha'b ha'b' hbb'.ne
          have hcross : G.Adj a b ∨ G.Adj a b' ∨ G.Adj a' b ∨ G.Adj a' b' := by
            by_contra hc
            simp only [not_or] at hc
            exact h2k2 ⟨a, a', b, b', hcard4,
              (hmemD a).mp haD, (hmemD a').mp ha'D, (hmemD b).mp hbD, (hmemD b').mp hb'D,
              hA.1, hB.1, hc.1, hc.2.1, hc.2.2.1, hc.2.2.2⟩
          rcases hcross with h | h | h | h
          · exact radj u.2 v.2 ((hMadj a b).mpr ⟨h, haD, hbD⟩)
          · exact (radj u.2 hb'supp ((hMadj a b').mpr ⟨h, haD, hb'D⟩)).trans
              (radj v.2 hb'supp hbb').symm
          · exact (radj u.2 ha'supp haa').trans
              (radj ha'supp v.2 ((hMadj a' b).mpr ⟨h, ha'D, hbD⟩))
          · exact ((radj u.2 ha'supp haa').trans
              (radj ha'supp hb'supp ((hMadj a' b').mpr ⟨h, ha'D, hb'D⟩))).trans
              (radj v.2 hb'supp hbb').symm
      have hconn : (M.induce M.support).Connected := by
        have := hVne
        exact ⟨hpre⟩
      have hbound := hconn.card_vert_le_card_edgeSet_add_one
      have hns : Nat.card ↥M.support = S.card := by
        rw [hsupp, Nat.card_coe_set_eq, Set.ncard_coe_finset]
      have hes : Nat.card (M.induce M.support).edgeSet = M.edgeFinset.card := by
        rw [Nat.card_eq_fintype_card, SimpleGraph.card_edgeSet,
          SimpleGraph.card_edgeFinset_induce_support]
      rw [hns, hes] at hbound
      omega
  rw [hfilter_eq]
  omega

/-- **Degree-partition bound for the `n = 13` residual (fully proved).**  With `22` edges and
minimum degree `3`, the hub set `Hub = filter (4 ≤ deg)` has `Hub.card ≤ 5` and the degree-3 set
`D = filter (deg = 3)` has `8 ≤ D.card` (handshake: `4·|Hub| ≤ ∑_{Hub} deg = 5 + 3·|Hub|`). -/
theorem residual_hub_card_le_five (G : SimpleGraph (Fin 13)) (hm : G.edgeFinset.card = 22)
    (h3 : ∀ v : Fin 13, 3 ≤ G.degree v) :
    (Finset.univ.filter (fun v => 4 ≤ G.degree v)).card ≤ 5 ∧
      8 ≤ (Finset.univ.filter (fun w => G.degree w = 3)).card := by
  classical
  have hsum : ∑ v : Fin 13, G.degree v = 44 := by
    rw [SimpleGraph.sum_degrees_eq_twice_card_edges, hm]
  set D : Finset (Fin 13) := Finset.univ.filter (fun w => G.degree w = 3) with hDdef
  set Hub : Finset (Fin 13) := Finset.univ.filter (fun v => 4 ≤ G.degree v) with hHubdef
  have hmemD : ∀ v : Fin 13, v ∈ D ↔ G.degree v = 3 := by intro v; rw [hDdef]; simp
  have hmemHub : ∀ v : Fin 13, v ∈ Hub ↔ 4 ≤ G.degree v := by intro v; rw [hHubdef]; simp
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
  have hHubge : 4 * Hub.card ≤ ∑ v ∈ Hub, G.degree v := by
    have hb : ∀ x ∈ Hub, 4 ≤ G.degree x := fun i hi => (hmemHub i).mp hi
    have h := Finset.card_nsmul_le_sum Hub (fun v => G.degree v) 4 hb
    simpa [smul_eq_mul, mul_comm] using h
  rw [hsumD] at hsumpart
  omega

/-- **Shared degree-4 hub for two twins (uniform pigeonhole, fully proved).**  Two degree-3
vertices `t₁ ≠ t₂` whose neighbours are all hubs (degree `≥ 4`) have a common neighbour of
degree exactly `4`.  Uniform incidence/excess count: the shared hubs number
`≥ 6 − |Hub|` (inclusion–exclusion, both neighbourhoods lie in `Hub`), while the hubs of degree
`≥ 5` number `≤ 5 − |Hub|` (the total degree-excess over `4` is `∑_Hub deg − 4|Hub| =
(5 + 3|Hub|) − 4|Hub| = 5 − |Hub|`); subtracting gives `≥ 1` shared degree-4 hub, independently
of `|Hub|`. -/
theorem exists_shared_deg4_hub (G : SimpleGraph (Fin 13))
    (hm : G.edgeFinset.card = 22) (h3 : ∀ v : Fin 13, 3 ≤ G.degree v)
    (t₁ t₂ : Fin 13) (ht₁3 : G.degree t₁ = 3) (ht₂3 : G.degree t₂ = 3)
    (ht₁iso : ∀ w : Fin 13, G.Adj t₁ w → 4 ≤ G.degree w)
    (ht₂iso : ∀ w : Fin 13, G.Adj t₂ w → 4 ≤ G.degree w) :
    ∃ h : Fin 13, G.degree h = 4 ∧ G.Adj t₁ h ∧ G.Adj t₂ h := by
  classical
  have hsum44 : ∑ v : Fin 13, G.degree v = 44 := by
    rw [SimpleGraph.sum_degrees_eq_twice_card_edges, hm]
  set D : Finset (Fin 13) := Finset.univ.filter (fun w => G.degree w = 3) with hDdef
  set Hub : Finset (Fin 13) := Finset.univ.filter (fun w => 4 ≤ G.degree w) with hHubdef
  set Hub5 : Finset (Fin 13) := Finset.univ.filter (fun w => 5 ≤ G.degree w) with hHub5def
  have hmemD : ∀ v : Fin 13, v ∈ D ↔ G.degree v = 3 := by intro v; rw [hDdef]; simp
  have hmemHub : ∀ v : Fin 13, v ∈ Hub ↔ 4 ≤ G.degree v := by intro v; rw [hHubdef]; simp
  have hmemHub5 : ∀ v : Fin 13, v ∈ Hub5 ↔ 5 ≤ G.degree v := by intro v; rw [hHub5def]; simp
  -- Partition `univ = D ∪ Hub`.
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
  have hsumD : ∑ v ∈ D, G.degree v = 3 * D.card := by
    rw [Finset.sum_congr rfl (fun v hv => (hmemD v).mp hv), Finset.sum_const, smul_eq_mul,
      mul_comm]
  have hsumHub : ∑ v ∈ Hub, G.degree v = 5 + 3 * Hub.card := by
    have hsumpart : ∑ v ∈ D, G.degree v + ∑ v ∈ Hub, G.degree v = 44 := by
      rw [← Finset.sum_union hdisjDH, hunionDH]; exact hsum44
    rw [hsumD] at hsumpart; omega
  -- `Hub5 ⊆ Hub` and the degree-excess bound `Hub5.card + Hub.card ≤ 5`.
  have hHub5sub : Hub5 ⊆ Hub := by
    intro v hv; exact (hmemHub v).mpr (by have := (hmemHub5 v).mp hv; omega)
  have hexcess : 4 * Hub.card + Hub5.card ≤ ∑ v ∈ Hub, G.degree v := by
    have hsplit := Finset.sum_sdiff hHub5sub (f := fun v => G.degree v)
    have hlo : 5 * Hub5.card ≤ ∑ v ∈ Hub5, G.degree v := by
      have hb : ∀ v ∈ Hub5, 5 ≤ G.degree v := fun v hv => (hmemHub5 v).mp hv
      have h := Finset.card_nsmul_le_sum Hub5 (fun v => G.degree v) 5 hb
      simpa [smul_eq_mul, mul_comm] using h
    have hlo2 : 4 * (Hub \ Hub5).card ≤ ∑ v ∈ Hub \ Hub5, G.degree v := by
      have hb : ∀ v ∈ Hub \ Hub5, 4 ≤ G.degree v := fun v hv =>
        (hmemHub v).mp (Finset.mem_sdiff.mp hv).1
      have h := Finset.card_nsmul_le_sum (Hub \ Hub5) (fun v => G.degree v) 4 hb
      simpa [smul_eq_mul, mul_comm] using h
    have hcardsplit : (Hub \ Hub5).card + (Hub ∩ Hub5).card = Hub.card :=
      Finset.card_sdiff_add_card_inter Hub Hub5
    have hinter_eq : Hub ∩ Hub5 = Hub5 := Finset.inter_eq_right.mpr hHub5sub
    rw [hinter_eq] at hcardsplit
    omega
  have hHub5le : Hub5.card + Hub.card ≤ 5 := by rw [hsumHub] at hexcess; omega
  -- Neighbourhoods of the twins lie in `Hub`; the shared deg-4 hub.
  have hNt₁sub : G.neighborFinset t₁ ⊆ Hub := by
    intro w hw; exact (hmemHub w).mpr (ht₁iso w ((G.mem_neighborFinset _ _).mp hw))
  have hNt₂sub : G.neighborFinset t₂ ⊆ Hub := by
    intro w hw; exact (hmemHub w).mpr (ht₂iso w ((G.mem_neighborFinset _ _).mp hw))
  set S : Finset (Fin 13) := G.neighborFinset t₁ ∩ G.neighborFinset t₂ with hSdef
  have hNt₁ : (G.neighborFinset t₁).card = 3 := by
    rw [G.card_neighborFinset_eq_degree, ht₁3]
  have hNt₂ : (G.neighborFinset t₂).card = 3 := by
    rw [G.card_neighborFinset_eq_degree, ht₂3]
  have hunion_le : (G.neighborFinset t₁ ∪ G.neighborFinset t₂).card ≤ Hub.card :=
    Finset.card_le_card (Finset.union_subset hNt₁sub hNt₂sub)
  have hincl : (G.neighborFinset t₁).card + (G.neighborFinset t₂).card
      = (G.neighborFinset t₁ ∪ G.neighborFinset t₂).card + S.card :=
    (Finset.card_union_add_card_inter _ _).symm
  -- Discard the deg-`≥5` shared hubs.
  have hSsplit : (S \ Hub5).card + (S ∩ Hub5).card = S.card :=
    Finset.card_sdiff_add_card_inter S Hub5
  have hSinter_le : (S ∩ Hub5).card ≤ Hub5.card :=
    Finset.card_le_card Finset.inter_subset_right
  have hpos : 0 < (S \ Hub5).card := by omega
  obtain ⟨h, hh⟩ := Finset.card_pos.mp hpos
  rw [Finset.mem_sdiff, hSdef, Finset.mem_inter, G.mem_neighborFinset, G.mem_neighborFinset] at hh
  obtain ⟨⟨ha₁, ha₂⟩, hnot5⟩ := hh
  have hhHub : h ∈ Hub := hNt₁sub ((G.mem_neighborFinset _ _).mpr ha₁)
  have hdeg4 : G.degree h = 4 := by
    have h4 := (hmemHub h).mp hhHub
    have hn5 : ¬ 5 ≤ G.degree h := fun h5 => hnot5 ((hmemHub5 h).mpr h5)
    omega
  exact ⟨h, hdeg4, ha₁, ha₂⟩

end N13

end ACMax
