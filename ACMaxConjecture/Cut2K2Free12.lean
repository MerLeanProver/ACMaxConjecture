import ACMaxConjecture.Base
import ACMaxConjecture.Spectral.AlgConn
import ACMaxConjecture.Cuts.WeightedCut
import ACMaxConjecture.Cuts.TriangleFree2K2
import ACMaxConjecture.InternalEdgesEven
import ACMaxConjecture.TwoRegular2K2

/-!
# The no-`2K₂` cut certificate for `n = 12`, dense-degree-3-subgraph case

Analogue of `Cut2K2Free.lean` (n=11) for `n = 12`.  For a connected, no-good-triangle graph on
`Fin 12` with `δ ≥ 3`, `∑ deg = 40` (degree sequence `[4,4,4,4,3⁸]` or `[5,4,4,3⁹]`) whose
degree-3 subgraph contains **no** induced `2K₂`, the weighted cut
`A = (degree-≥4 vertices) ∪ (degree-3 vertices adjacent to ≥ 2 degree-≥4 vertices)` certifies
`algConn G ≤ 2` **provided** the degree-3 subgraph has at least `6` internal edges (`e(D) ≥ 6`,
which holds for `[5,4,4,3⁹]` and for `[4,4,4,4,3⁸]` with `≥ 2` hub-hub edges).

Density reduction (mirrors n=11): with `t = |Aᶜ|`, `S = ∑_{v∈Aᶜ}|N v ∩ Aᶜ|`, `cut = 3t − S`, the
goal `12·cut ≤ 2|A||Aᶜ|` becomes `12t + 2t² ≤ 12S`.  Key facts: `t ≤ 7` (apply
`exists_induced_2K2_of_triangleFree_smalldeg` to `Aᶜ`); `S ≥ 2t` (vertex-cover, needs `e(D) ≥ 6`);
`t = 7` needs `S ≥ 2t+2` via `sum_inDegree_even` + `exists_2K2_of_two_regular_triangleFree`.
-/

namespace ACMax

open scoped Classical

/-- No-`2K₂` residual cut certificate for `n = 12`, when the degree-3 subgraph has `≥ 6` internal
edges. -/
theorem algConn_le_two_of_2K2free_cut_twelve (G : SimpleGraph (Fin 12))
    (hm : G.edgeFinset.card = 20) (h3 : ∀ v : Fin 12, 3 ≤ G.degree v)
    (hT : ¬ ∃ x y z : Fin 12, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    (hno2k2 : ¬ ∃ a b c d : Fin 12, ({a, b, c, d} : Finset (Fin 12)).card = 4 ∧
      G.degree a = 3 ∧ G.degree b = 3 ∧ G.degree c = 3 ∧ G.degree d = 3 ∧
      G.Adj a b ∧ G.Adj c d ∧ ¬ G.Adj a c ∧ ¬ G.Adj a d ∧ ¬ G.Adj b c ∧ ¬ G.Adj b d)
    (heD : 12 ≤ ∑ v ∈ Finset.univ.filter (fun w => G.degree w = 3),
              (G.neighborFinset v ∩ Finset.univ.filter (fun w => G.degree w = 3)).card) :
    algConn G ≤ 2 := by
  let : DecidableEq (Fin 12) := fun a b => Classical.propDecidable (a = b)
  -- `∑ deg = 40` from `m = 20`.
  have hsum : ∑ v : Fin 12, G.degree v = 40 := by
    rw [SimpleGraph.sum_degrees_eq_twice_card_edges, hm]
  -- The hubs (degree `≥ 4`) and the cut set `A`.
  set Hub : Finset (Fin 12) :=
    Finset.univ.filter (fun v => 4 ≤ G.degree v) with hHubdef
  set A : Finset (Fin 12) :=
    Hub ∪ Finset.univ.filter
      (fun v => G.degree v = 3 ∧ 2 ≤ (G.neighborFinset v ∩ Hub).card) with hAdef
  -- Membership characterizations.
  have hmemHub : ∀ v : Fin 12, v ∈ Hub ↔ 4 ≤ G.degree v := by
    intro v; rw [hHubdef]; simp
  have hmemA : ∀ v : Fin 12, v ∈ A ↔
      (4 ≤ G.degree v) ∨ (G.degree v = 3 ∧ 2 ≤ (G.neighborFinset v ∩ Hub).card) := by
    intro v; rw [hAdef, Finset.mem_union, hmemHub]; simp [hHubdef]
  have hmemAc : ∀ v : Fin 12, v ∈ Aᶜ ↔
      G.degree v = 3 ∧ (G.neighborFinset v ∩ Hub).card ≤ 1 := by
    intro v
    rw [Finset.mem_compl, hmemA]
    have hd := h3 v
    constructor
    · intro hv
      push Not at hv
      obtain ⟨h1, h2⟩ := hv
      have : G.degree v = 3 := by omega
      exact ⟨this, by have := h2 this; omega⟩
    · rintro ⟨hdeg, hk⟩
      push Not
      refine ⟨by omega, fun _ => by omega⟩
  -- Every vertex of `Aᶜ` has degree exactly `3`.
  have hAcdeg : ∀ v : Fin 12, v ∈ Aᶜ → G.degree v = 3 := fun v hv => ((hmemAc v).mp hv).1
  -- Degree-3 vertices are exactly the non-hubs.
  have hnotHubDeg : ∀ v : Fin 12, v ∉ Hub → G.degree v = 3 := by
    intro v hv
    rw [hmemHub] at hv
    have := h3 v; omega
  have hHubcompl : Hub.card + Hubᶜ.card = 12 := by
    have h := Finset.card_add_card_compl Hub; rwa [Fintype.card_fin] at h
  have hHubc : ∑ v ∈ Hubᶜ, G.degree v = 3 * Hubᶜ.card := by
    rw [Finset.sum_congr rfl (fun v hv => hnotHubDeg v (Finset.mem_compl.mp hv)),
      Finset.sum_const, smul_eq_mul, mul_comm]
  have hHubpart : ∑ v ∈ Hub, G.degree v + ∑ v ∈ Hubᶜ, G.degree v = 40 := by
    rw [Finset.sum_add_sum_compl]; exact hsum
  have hHubge : 4 * Hub.card ≤ ∑ v ∈ Hub, G.degree v := by
    have hb : ∀ x ∈ Hub, 4 ≤ G.degree x := fun i hi => (hmemHub i).mp hi
    have h := Finset.card_nsmul_le_sum Hub (fun v => G.degree v) 4 hb
    simpa [smul_eq_mul, mul_comm] using h
  -- `∑_{Hub} deg = 4 + 3·|Hub|`, hence `1 ≤ |Hub| ≤ 4`.
  have hHubsum : ∑ v ∈ Hub, G.degree v = 4 + 3 * Hub.card := by omega
  have hHubcard : Hub.card ≤ 4 := by omega
  have hHubpos : 1 ≤ Hub.card := by
    rcases Nat.eq_zero_or_pos Hub.card with h0 | h1
    · rw [h0] at hHubsum
      have : ∑ v ∈ Hub, G.degree v = 0 := by
        rw [Finset.card_eq_zero.mp h0]; simp
      omega
    · exact h1
  -- Indicator form of an in-set neighbourhood count.
  have hcardInter : ∀ (a : Fin 12) (C : Finset (Fin 12)),
      (G.neighborFinset a ∩ C).card = ∑ c ∈ C, (if G.Adj a c then 1 else 0) := by
    intro a C
    rw [Finset.inter_comm, ← Finset.filter_mem_eq_inter, Finset.card_filter]
    exact Finset.sum_congr rfl (fun c _ => by simp only [SimpleGraph.mem_neighborFinset])
  -- Symmetric cross-count between two sets.
  have hcross : ∀ (B C : Finset (Fin 12)),
      ∑ a ∈ B, (G.neighborFinset a ∩ C).card
        = ∑ c ∈ C, (G.neighborFinset c ∩ B).card := by
    intro B C
    simp_rw [hcardInter]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl
      (fun a _ => by rw [SimpleGraph.adj_comm]))
  -- The cut equals the `Aᶜ`-side count of cross edges.
  set t : ℕ := Aᶜ.card with htdef
  set S : ℕ := ∑ v ∈ Aᶜ, (G.neighborFinset v ∩ Aᶜ).card with hSdef
  set cut : ℕ := ∑ a ∈ A, (G.neighborFinset a \ A).card with hcutdef
  have hcutAc : cut = ∑ v ∈ Aᶜ, (G.neighborFinset v ∩ A).card := by
    rw [hcutdef]
    have hsd : ∀ a ∈ A, (G.neighborFinset a \ A).card = (G.neighborFinset a ∩ Aᶜ).card := by
      intro a _; rw [Finset.sdiff_eq_inter_compl]
    rw [Finset.sum_congr rfl hsd]
    exact hcross A Aᶜ
  -- `cut + S = 3 t`: each `Aᶜ` vertex has degree 3, split between `A` and `Aᶜ`.
  have hcutS : cut + S = 3 * t := by
    have hterm : ∀ v ∈ Aᶜ,
        (G.neighborFinset v ∩ A).card + (G.neighborFinset v ∩ Aᶜ).card = 3 := by
      intro v hv
      have hpart := Finset.card_inter_add_card_sdiff (G.neighborFinset v) A
      rw [Finset.sdiff_eq_inter_compl] at hpart
      rw [hpart, SimpleGraph.card_neighborFinset_eq_degree, hAcdeg v hv]
    rw [hcutAc, hSdef, ← Finset.sum_add_distrib, Finset.sum_congr rfl hterm,
      Finset.sum_const, smul_eq_mul, htdef, mul_comm]
  -- `D = Hubᶜ` is exactly the degree-3 vertex set.
  have hmemD : ∀ v : Fin 12, v ∈ Hubᶜ ↔ G.degree v = 3 := by
    intro v
    rw [Finset.mem_compl, hmemHub]
    have := h3 v; omega
  -- In-`D` degrees are at most `3` (since total degree is `3`).
  have hDmax : ∀ a ∈ Hubᶜ, (G.neighborFinset a ∩ Hubᶜ).card ≤ 3 := by
    intro a ha
    calc (G.neighborFinset a ∩ Hubᶜ).card
        ≤ (G.neighborFinset a).card := Finset.card_le_card Finset.inter_subset_left
      _ = G.degree a := G.card_neighborFinset_eq_degree a
      _ = 3 := (hmemD a).mp ha
  -- `D` is triangle-free: a triangle of degree-3 vertices has degree-sum `9 ≤ 10`.
  have hDtri : ∀ a ∈ Hubᶜ, ∀ b ∈ Hubᶜ, ∀ c ∈ Hubᶜ,
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj a c) := by
    rintro a ha b hb c hc ⟨hab, hbc, hac⟩
    refine hT ⟨a, b, c, G.ne_of_adj hab, G.ne_of_adj hbc, G.ne_of_adj hac,
      hab, hbc, hac, ?_⟩
    have da := (hmemD a).mp ha
    have db := (hmemD b).mp hb
    have dc := (hmemD c).mp hc
    omega
  -- `Aᶜ ⊆ Hubᶜ` (every `Aᶜ` vertex has degree 3).
  have hAcsubD : Aᶜ ⊆ Hubᶜ := by
    intro x hx
    rw [Finset.mem_compl, hmemHub]
    have := (hmemAc x).mp hx; omega
  -- `Hubᶜ` is exactly `{v | deg v = 3}`, so the hypothesis `heD` gives the in-`D` degree sum.
  have hDeq : Hubᶜ = Finset.univ.filter (fun w => G.degree w = 3) := by
    ext v; rw [Finset.mem_filter]
    simp only [Finset.mem_univ, true_and]
    exact hmemD v
  have hSatleast12 : 12 ≤ ∑ w ∈ Hubᶜ, (G.neighborFinset w ∩ Hubᶜ).card := by
    refine le_trans heD (le_of_eq ?_)
    rw [hDeq]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    congr 1
    ext x; simp
  -- Every `Aᶜ` vertex has `≥ 2` neighbours inside `Aᶜ`.  Suppose not: then `v` has a degree-3
  -- "leaf" neighbour `u` (`≥ 2` hubs, only `D`-neighbour `v`), and `C = insert v (N v ∩ D)`
  -- is a vertex cover of the degree-3 subgraph (any uncovered edge would extend `{v,u}` to an
  -- induced `2K₂`).  Counting `∑_{D} deg_D` against this cover yields `≤ 11 < 12`, contradiction.
  have hperv : ∀ v ∈ Aᶜ, 2 ≤ (G.neighborFinset v ∩ Aᶜ).card := by
    intro v hv
    by_contra hlt
    push Not at hlt
    have hv3 : G.degree v = 3 := ((hmemAc v).mp hv).1
    have hvHub : (G.neighborFinset v ∩ Hub).card ≤ 1 := ((hmemAc v).mp hv).2
    have hvD : v ∈ Hubᶜ := hAcsubD hv
    have hvsplit : (G.neighborFinset v ∩ Hub).card
        + (G.neighborFinset v ∩ Hubᶜ).card = 3 := by
      have hpart := Finset.card_inter_add_card_sdiff (G.neighborFinset v) Hub
      rw [Finset.sdiff_eq_inter_compl] at hpart
      rw [hpart, SimpleGraph.card_neighborFinset_eq_degree, hv3]
    have hdv3 : (G.neighborFinset v ∩ Hubᶜ).card ≤ 3 := hDmax v hvD
    have hZeq : (G.neighborFinset v ∩ Hubᶜ) ∩ Aᶜ = G.neighborFinset v ∩ Aᶜ := by
      rw [Finset.inter_assoc, Finset.inter_eq_right.mpr hAcsubD]
    -- A degree-3 vertex `p` adjacent to `v` with `≥ 2` hub-neighbours has only `v` inside `D`.
    have hleaf : ∀ p, p ∈ G.neighborFinset v ∩ Hubᶜ → p ∉ Aᶜ →
        G.neighborFinset p ∩ Hubᶜ = {v} := by
      intro p hp hpAc
      rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset] at hp
      obtain ⟨hvp, hpD⟩ := hp
      have hpA : p ∈ A := by
        by_contra h; exact hpAc (Finset.mem_compl.mpr h)
      have hp2hub : 2 ≤ (G.neighborFinset p ∩ Hub).card := by
        rcases (hmemA p).mp hpA with h4 | ⟨_, h2⟩
        · have := (hmemD p).mp hpD; omega
        · exact h2
      have hpsplit : (G.neighborFinset p ∩ Hub).card
          + (G.neighborFinset p ∩ Hubᶜ).card = 3 := by
        have hpart := Finset.card_inter_add_card_sdiff (G.neighborFinset p) Hub
        rw [Finset.sdiff_eq_inter_compl] at hpart
        rw [hpart, SimpleGraph.card_neighborFinset_eq_degree, (hmemD p).mp hpD]
      have hvin : v ∈ G.neighborFinset p ∩ Hubᶜ := by
        rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
        exact ⟨hvp.symm, hvD⟩
      have hcard1 : (G.neighborFinset p ∩ Hubᶜ).card = 1 := by
        have hpos := Finset.card_pos.mpr ⟨v, hvin⟩
        omega
      obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcard1
      rw [ha] at hvin ⊢
      rw [Finset.mem_singleton] at hvin
      rw [hvin]
    -- A leaf neighbour `u` of `v` exists (since `< 2` of `v`'s `≥ 2` `D`-neighbours are in `Aᶜ`).
    have hUne : 0 < ((G.neighborFinset v ∩ Hubᶜ) \ Aᶜ).card := by
      have hcardsd := Finset.card_inter_add_card_sdiff (G.neighborFinset v ∩ Hubᶜ) Aᶜ
      rw [hZeq] at hcardsd
      omega
    obtain ⟨u, hu⟩ := Finset.card_pos.mp hUne
    rw [Finset.mem_sdiff] at hu
    obtain ⟨huNvD, huAc⟩ := hu
    have hu_leaf : G.neighborFinset u ∩ Hubᶜ = {v} := hleaf u huNvD huAc
    have huNv : G.Adj v u := by
      have := (Finset.mem_inter.mp huNvD).1
      rwa [SimpleGraph.mem_neighborFinset] at this
    have huD : u ∈ Hubᶜ := (Finset.mem_inter.mp huNvD).2
    set C : Finset (Fin 12) := insert v (G.neighborFinset v ∩ Hubᶜ) with hCdef
    have hmemC : ∀ x, x ∈ C ↔ x = v ∨ x ∈ G.neighborFinset v ∩ Hubᶜ := by
      intro x; rw [hCdef, Finset.mem_insert]
    have hCsub : C ⊆ Hubᶜ := by
      intro x hx
      rcases (hmemC x).mp hx with h | h
      · exact h ▸ hvD
      · exact (Finset.mem_inter.mp h).2
    have huC : u ∈ C := (hmemC u).mpr (Or.inr huNvD)
    -- `C` is a vertex cover of the degree-3 subgraph.
    have hcover : ∀ x, x ∈ Hubᶜ → ∀ y, y ∈ Hubᶜ → G.Adj x y → x ∈ C ∨ y ∈ C := by
      intro x hxD y hyD hxy
      by_contra hcon
      push Not at hcon
      obtain ⟨hxC, hyC⟩ := hcon
      have hxv : x ≠ v := fun h => hxC ((hmemC x).mpr (Or.inl h))
      have hyv : y ≠ v := fun h => hyC ((hmemC y).mpr (Or.inl h))
      have hxnv : ¬ G.Adj v x := fun h => hxC ((hmemC x).mpr (Or.inr (by
        rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset]; exact ⟨h, hxD⟩)))
      have hynv : ¬ G.Adj v y := fun h => hyC ((hmemC y).mpr (Or.inr (by
        rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset]; exact ⟨h, hyD⟩)))
      have hxu : ¬ G.Adj u x := by
        intro h
        have hxin : x ∈ G.neighborFinset u ∩ Hubᶜ := by
          rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset]; exact ⟨h, hxD⟩
        rw [hu_leaf, Finset.mem_singleton] at hxin
        exact hxv hxin
      have hyu : ¬ G.Adj u y := by
        intro h
        have hyin : y ∈ G.neighborFinset u ∩ Hubᶜ := by
          rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset]; exact ⟨h, hyD⟩
        rw [hu_leaf, Finset.mem_singleton] at hyin
        exact hyv hyin
      have hcard4 : ({v, u, x, y} : Finset (Fin 12)).card = 4 := by
        have e1 : v ≠ u := G.ne_of_adj huNv
        have e2 : v ≠ x := fun h => hxv h.symm
        have e3 : v ≠ y := fun h => hyv h.symm
        have e4 : u ≠ x := fun h => hxC ((hmemC x).mpr (Or.inr (h ▸ huNvD)))
        have e5 : u ≠ y := fun h => hyC ((hmemC y).mpr (Or.inr (h ▸ huNvD)))
        have e6 : x ≠ y := G.ne_of_adj hxy
        rw [Finset.card_insert_of_notMem (by simp [e1, e2, e3]),
            Finset.card_insert_of_notMem (by simp [e4, e5]),
            Finset.card_insert_of_notMem (by simp [e6]), Finset.card_singleton]
      refine hno2k2 ⟨v, u, x, y, ?_, hv3, (hmemD u).mp huD, (hmemD x).mp hxD,
        (hmemD y).mp hyD, huNv, hxy, hxnv, hynv, hxu, hyu⟩
      convert hcard4 using 2
      ext z; simp
    -- Refined cover: an uncovered vertex's `D`-neighbours lie in `N v ∩ Aᶜ`.
    have hcover2 : ∀ w, w ∈ Hubᶜ → w ∉ C →
        G.neighborFinset w ∩ Hubᶜ ⊆ G.neighborFinset v ∩ Aᶜ := by
      intro w hwD hwC z hz
      rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset] at hz
      obtain ⟨hwz, hzD⟩ := hz
      have hzC : z ∈ C := (hcover w hwD z hzD hwz).resolve_left hwC
      have hzv : z ≠ v := by
        rintro rfl
        exact hwC ((hmemC w).mpr (Or.inr (by
          rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset]; exact ⟨hwz.symm, hwD⟩)))
      have hzNv : z ∈ G.neighborFinset v ∩ Hubᶜ := ((hmemC z).mp hzC).resolve_left hzv
      have hzAc : z ∈ Aᶜ := by
        by_contra hzAc
        have hl := hleaf z hzNv hzAc
        have hwin : w ∈ G.neighborFinset z ∩ Hubᶜ := by
          rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset]; exact ⟨hwz.symm, hwD⟩
        rw [hl, Finset.mem_singleton] at hwin
        exact hwC ((hmemC w).mpr (Or.inl hwin))
      rw [Finset.mem_inter]
      exact ⟨(Finset.mem_inter.mp hzNv).1, hzAc⟩
    -- Counting the in-`D` degree sum against the cover.
    have hout : ∑ w ∈ Hubᶜ \ C, (G.neighborFinset w ∩ Hubᶜ).card
        ≤ 3 * (G.neighborFinset v ∩ Aᶜ).card := by
      have hcong : ∀ w ∈ Hubᶜ \ C,
          (G.neighborFinset w ∩ Hubᶜ).card
            = (G.neighborFinset w ∩ (G.neighborFinset v ∩ Aᶜ)).card := by
        intro w hw
        rw [Finset.mem_sdiff] at hw
        congr 1
        apply Finset.Subset.antisymm
        · intro z hz
          rw [Finset.mem_inter]
          exact ⟨(Finset.mem_inter.mp hz).1, hcover2 w hw.1 hw.2 hz⟩
        · intro z hz
          rw [Finset.mem_inter] at hz ⊢
          exact ⟨hz.1, hAcsubD (Finset.mem_inter.mp hz.2).2⟩
      rw [Finset.sum_congr rfl hcong]
      calc ∑ w ∈ Hubᶜ \ C, (G.neighborFinset w ∩ (G.neighborFinset v ∩ Aᶜ)).card
          ≤ ∑ w ∈ Hubᶜ, (G.neighborFinset w ∩ (G.neighborFinset v ∩ Aᶜ)).card :=
            Finset.sum_le_sum_of_subset Finset.sdiff_subset
        _ = ∑ z ∈ G.neighborFinset v ∩ Aᶜ, (G.neighborFinset z ∩ Hubᶜ).card :=
            hcross Hubᶜ (G.neighborFinset v ∩ Aᶜ)
        _ ≤ ∑ _z ∈ G.neighborFinset v ∩ Aᶜ, 3 :=
            Finset.sum_le_sum (fun z hz => hDmax z (hAcsubD (Finset.mem_inter.mp hz).2))
        _ = 3 * (G.neighborFinset v ∩ Aᶜ).card := by
            rw [Finset.sum_const, smul_eq_mul, mul_comm]
    have hvnotin : v ∉ G.neighborFinset v ∩ Hubᶜ := fun h => by
      have hAdj : G.Adj v v := by
        have := (Finset.mem_inter.mp h).1
        rwa [SimpleGraph.mem_neighborFinset] at this
      exact hAdj.ne rfl
    have hinner : ∑ w ∈ G.neighborFinset v ∩ Hubᶜ, (G.neighborFinset w ∩ Hubᶜ).card
        ≤ (G.neighborFinset v ∩ Hubᶜ).card + 2 * (G.neighborFinset v ∩ Aᶜ).card := by
      rw [← Finset.sum_inter_add_sum_sdiff (G.neighborFinset v ∩ Hubᶜ) Aᶜ
            (fun w => (G.neighborFinset w ∩ Hubᶜ).card)]
      have hAcpart : ∑ w ∈ (G.neighborFinset v ∩ Hubᶜ) ∩ Aᶜ,
          (G.neighborFinset w ∩ Hubᶜ).card ≤ 3 * (G.neighborFinset v ∩ Aᶜ).card := by
        calc ∑ w ∈ (G.neighborFinset v ∩ Hubᶜ) ∩ Aᶜ, (G.neighborFinset w ∩ Hubᶜ).card
            ≤ ∑ _w ∈ (G.neighborFinset v ∩ Hubᶜ) ∩ Aᶜ, 3 :=
              Finset.sum_le_sum (fun w hw =>
                hDmax w (Finset.mem_inter.mp (Finset.mem_inter.mp hw).1).2)
          _ = 3 * (G.neighborFinset v ∩ Aᶜ).card := by
              rw [Finset.sum_const, smul_eq_mul, mul_comm, hZeq]
      have hleafpart : ∑ w ∈ (G.neighborFinset v ∩ Hubᶜ) \ Aᶜ,
          (G.neighborFinset w ∩ Hubᶜ).card = ((G.neighborFinset v ∩ Hubᶜ) \ Aᶜ).card := by
        rw [Finset.card_eq_sum_ones]
        refine Finset.sum_congr rfl (fun w hw => ?_)
        rw [Finset.mem_sdiff] at hw
        rw [hleaf w hw.1 hw.2, Finset.card_singleton]
      have hcards := Finset.card_inter_add_card_sdiff (G.neighborFinset v ∩ Hubᶜ) Aᶜ
      rw [hZeq] at hcards
      rw [hleafpart]
      omega
    have hinC : ∑ w ∈ C, (G.neighborFinset w ∩ Hubᶜ).card
        ≤ 2 * (G.neighborFinset v ∩ Hubᶜ).card + 2 * (G.neighborFinset v ∩ Aᶜ).card := by
      rw [hCdef, Finset.sum_insert hvnotin]
      linarith [hinner]
    have hsplitsum : ∑ w ∈ Hubᶜ \ C, (G.neighborFinset w ∩ Hubᶜ).card
        + ∑ w ∈ C, (G.neighborFinset w ∩ Hubᶜ).card
        = ∑ w ∈ Hubᶜ, (G.neighborFinset w ∩ Hubᶜ).card :=
      Finset.sum_sdiff hCsub
    omega
  -- `t ≤ 7`: if `8 ≤ |Aᶜ|`, then `Aᶜ` is a triangle-free graph with min in-degree `≥ 1`
  -- (from `hperv`) and max in-degree `≤ 3`, so it contains an induced `2K₂` on degree-3
  -- vertices, contradicting `hno2k2`.
  have htle : t ≤ 7 := by
    by_contra hcon
    push Not at hcon
    have hcard8 : 8 ≤ Aᶜ.card := by rw [← htdef]; omega
    have htri : ∀ a ∈ Aᶜ, ∀ b ∈ Aᶜ, ∀ c ∈ Aᶜ, ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj a c) :=
      fun a ha b hb c hc => hDtri a (hAcsubD ha) b (hAcsubD hb) c (hAcsubD hc)
    have hmin : ∀ a ∈ Aᶜ, 1 ≤ (G.neighborFinset a ∩ Aᶜ).card :=
      fun a ha => by have := hperv a ha; omega
    have hmax : ∀ a ∈ Aᶜ, (G.neighborFinset a ∩ Aᶜ).card ≤ 3 := by
      intro a ha
      calc (G.neighborFinset a ∩ Aᶜ).card
          ≤ (G.neighborFinset a).card := Finset.card_le_card Finset.inter_subset_left
        _ = G.degree a := G.card_neighborFinset_eq_degree a
        _ = 3 := hAcdeg a ha
    obtain ⟨a, ha, b, hb, c, hc, d, hd, hcard4, hab, hcd, hac, had, hbc, hbd⟩ :=
      exists_induced_2K2_of_triangleFree_smalldeg G Aᶜ htri hmin hmax hcard8
    refine hno2k2 ⟨a, b, c, d, ?_, hAcdeg a ha, hAcdeg b hb, hAcdeg c hc, hAcdeg d hd,
      hab, hcd, hac, had, hbc, hbd⟩
    convert hcard4 using 2
    ext x; simp
  -- `S ≥ 2t` from the per-vertex bound.
  have hSge : 2 * t ≤ S := by
    rw [hSdef, htdef]
    have h := Finset.card_nsmul_le_sum Aᶜ
      (fun v => (G.neighborFinset v ∩ Aᶜ).card) 2 hperv
    simpa [smul_eq_mul, mul_comm] using h
  -- The edge-density bound `12t + 2t² ≤ 12S` over `t ≤ 7`.
  have hdensity : 12 * t + 2 * t * t ≤ 12 * S := by
    rcases Nat.lt_or_ge t 7 with htlt | htge
    · -- `t ≤ 6`: `12t + 2t² ≤ 24t ≤ 12S` from `S ≥ 2t`.
      have htle6 : t ≤ 6 := by omega
      have hsq : t * t ≤ 6 * t := Nat.mul_le_mul htle6 (le_refl t)
      rw [mul_assoc]
      generalize hq : t * t = q at hsq ⊢
      omega
    · -- `t = 7`: need one extra internal edge `S ≥ 2t + 2`.  `S = 2t + N₃` with `N₃` even
      -- (`sum_inDegree_even`); if `N₃ = 0` then `Aᶜ` is `2`-regular triangle-free on `7 ≥ 6`
      -- vertices, giving an induced `2K₂` barred by `hno2k2`; hence `N₃ ≥ 2`.
      have hSge2 : 2 * t + 2 ≤ S := by
        have hSeven : Even S := by rw [hSdef]; exact ACMax.sum_inDegree_even G Aᶜ
        by_contra hcon
        push Not at hcon
        obtain ⟨k, hk⟩ := hSeven
        have hSeq : S = 2 * t := by omega
        have hle : ∀ v ∈ Aᶜ, (G.neighborFinset v ∩ Aᶜ).card ≤ 2 := by
          intro v₀ hv₀
          by_contra hc
          push Not at hc
          have hsplit : S = (G.neighborFinset v₀ ∩ Aᶜ).card
              + ∑ v ∈ Aᶜ.erase v₀, (G.neighborFinset v ∩ Aᶜ).card := by
            rw [hSdef]; exact (Finset.add_sum_erase Aᶜ _ hv₀).symm
          have hlow : 2 * (Aᶜ.erase v₀).card
              ≤ ∑ v ∈ Aᶜ.erase v₀, (G.neighborFinset v ∩ Aᶜ).card := by
            have h := Finset.card_nsmul_le_sum (Aᶜ.erase v₀)
              (fun v => (G.neighborFinset v ∩ Aᶜ).card) 2
              (fun v hv => hperv v (Finset.mem_of_mem_erase hv))
            simpa [smul_eq_mul, mul_comm] using h
          have hcard_erase : (Aᶜ.erase v₀).card = t - 1 := by
            rw [htdef]; exact Finset.card_erase_of_mem hv₀
          omega
        have hreg : ∀ v ∈ Aᶜ, (G.neighborFinset v ∩ Aᶜ).card = 2 :=
          fun v hv => le_antisymm (hle v hv) (hperv v hv)
        have hActri : ∀ a ∈ Aᶜ, ∀ b ∈ Aᶜ, ∀ c ∈ Aᶜ,
            ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj a c) :=
          fun a ha b hb c hc => hDtri a (hAcsubD ha) b (hAcsubD hb) c (hAcsubD hc)
        have htge' : 6 ≤ Aᶜ.card := by rw [← htdef]; omega
        obtain ⟨a, ha, b, hb, c, hc, d, hd, hcard4, hab, hcd, hac, had, hbc, hbd⟩ :=
          ACMax.exists_2K2_of_two_regular_triangleFree G Aᶜ hActri hreg htge'
        refine hno2k2 ⟨a, b, c, d, ?_, hAcdeg a ha, hAcdeg b hb, hAcdeg c hc,
          hAcdeg d hd, hab, hcd, hac, had, hbc, hbd⟩
        convert hcard4 using 2
        ext x; simp
      have hq : t * t ≤ 7 * t := Nat.mul_le_mul htle (le_refl t)
      rw [mul_assoc]
      generalize t * t = q at hq ⊢
      omega
  -- `A` is nonempty: it contains every hub.
  have hA : A.Nonempty := by
    obtain ⟨u, hu⟩ := Finset.card_pos.mp hHubpos
    exact ⟨u, by rw [hmemA]; exact Or.inl ((hmemHub u).mp hu)⟩
  -- `Aᶜ` is nonempty: otherwise every degree-3 vertex has `≥ 2` hub-neighbours, hence `≤ 1`
  -- in-`D` neighbour, so `∑_{D} deg_D ≤ |D| ≤ 11 < 12`, contradicting `heD`.
  have hAcne : Aᶜ.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    have hge : ∀ v ∈ Hubᶜ, 2 ≤ (G.neighborFinset v ∩ Hub).card := by
      intro v hv
      have hdeg := hnotHubDeg v (Finset.mem_compl.mp hv)
      have hvnotAc : v ∉ Aᶜ := by rw [hempty]; exact Finset.notMem_empty v
      rw [hmemAc] at hvnotAc
      push Not at hvnotAc
      have := hvnotAc hdeg; omega
    have hle1 : ∀ v ∈ Hubᶜ, (G.neighborFinset v ∩ Hubᶜ).card ≤ 1 := by
      intro v hv
      have hdeg := hnotHubDeg v (Finset.mem_compl.mp hv)
      have hvsplit : (G.neighborFinset v ∩ Hub).card
          + (G.neighborFinset v ∩ Hubᶜ).card = 3 := by
        have hpart := Finset.card_inter_add_card_sdiff (G.neighborFinset v) Hub
        rw [Finset.sdiff_eq_inter_compl] at hpart
        rw [hpart, SimpleGraph.card_neighborFinset_eq_degree, hdeg]
      have := hge v hv; omega
    have hupper : ∑ v ∈ Hubᶜ, (G.neighborFinset v ∩ Hubᶜ).card ≤ Hubᶜ.card := by
      calc ∑ v ∈ Hubᶜ, (G.neighborFinset v ∩ Hubᶜ).card
          ≤ ∑ _v ∈ Hubᶜ, 1 := Finset.sum_le_sum hle1
        _ = Hubᶜ.card := by rw [Finset.sum_const, smul_eq_mul, mul_one]
    omega
  refine algConn_le_two_of_weighted_cut G A hA hAcne ?_
  rw [Fintype.card_fin]
  have hpt : A.card + t = 12 := by
    rw [htdef]
    have h := Finset.card_add_card_compl A; rwa [Fintype.card_fin] at h
  have hkey : A.card * t + t * t = 12 * t := by
    have h := congrArg (· * t) hpt
    simpa [add_mul] using h
  -- Arithmetic: `12·cut ≤ 2·|A|·t` from `cut + S = 3t`, density and `|A| + t = 12`.
  show 12 * cut ≤ 2 * (A.card * t)
  linarith [hcutS, hdensity, hkey]

end ACMax
