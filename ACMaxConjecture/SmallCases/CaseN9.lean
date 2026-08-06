import ACMaxConjecture.Base
import ACMaxConjecture.Spectral.AlgConn
import ACMaxConjecture.Cuts.LowDegreeVertex
import ACMaxConjecture.Spectral.AlgConnK2
import ACMaxConjecture.Cuts.WeightedCut
import ACMaxConjecture.Cuts.Ind2K2

/-!
# The ACMAX conjecture for `n = 9` — where the elementary method stops

For `n ≤ 8` the upper bound `λ₂ ≤ 2` is provable by exhibiting an explicit *test
vector* `x ⊥ 𝟙` with `xᵀ L x ≤ 2‖x‖²`: a single low-degree vertex (`δ ≤ 2`), or — for
the `δ ≥ 3` graphs that only occur at `n ≥ 8` — a `±1` (balanced/weighted) **cut**
vector.  At `n = 9` the cut method **provably fails**.

The `δ ≤ 2` branch below is proved via `algConn_le_two_of_low_degree_vertex`.  The
`δ ≥ 3` branch — where the cut method provably fails — is nonetheless closed here by a
purely structural argument: every `δ ≥ 3` graph on `Fin 9` with `14` edges either
contains a triangle (a sparse weighted cut) or, being triangle-free, has degree
sequence `[4,3⁸]` and contains an induced `2K₂` on four degree-3 vertices, which
certifies `algConn ≤ 2` via `algConn_le_two_of_ind_2K2`.

**Why the cut method cannot reach `n = 9` (concrete obstruction).** The triangle-free
graph on `Fin 9` with adjacency
```
0:{2,3,4}  1:{2,3,5,6}  2:{0,1,7}  3:{0,1,8}  4:{0,5,6}
5:{1,4,7}  6:{1,4,8}    7:{2,5,8}  8:{3,6,7}
```
has degree sequence `[4,3⁸]`, exactly `14` edges and minimum degree `3`, and its
Laplacian spectrum is `[0,2,2,2,3,3,5,5,6]`, so `algConn = 2` is *attained*.  An
exhaustive check over all `2⁹` vertex subsets shows **no** bipartition `A` satisfies the
cut certificate `9·(∑_{a∈A}|N(a)\A|) ≤ 2·|A|·|Aᶜ|` (the minimum cut for `|A| ∈ {3,4,5}`
is `5`, giving `45 > 40`).  The value `λ₂ = 2` is realised by a genuine Fiedler
eigenvector that is **not** a `±1` indicator, so no vertex-bipartition certificate —
the engine behind every `n ≤ 8` proof — can cover this graph.  Closing `n = 9`
therefore requires an eigenvector / extremal-structure (spectral) argument, i.e. the
genuine content of the open conjecture (Kolokolnikov, Conj. 1.5, arXiv:1412.6147).
-/

namespace ACMax

open scoped Classical

/-- Upper bound clause for `n = 9`: every graph on `Fin 9` with `14` edges has
`algConn ≤ 2`.  The `δ ≤ 2` case uses a low-degree test vector; the `δ ≥ 3` case splits
on a triangle (sparse weighted cut) versus the triangle-free `[4,3⁸]` structure, which
always yields an induced `2K₂` on four degree-3 vertices (see the module docstring for
why no `±1` cut certificate suffices here). -/
theorem upperBound_nine (G : SimpleGraph (Fin 9)) (hm : G.edgeFinset.card = 14) :
    algConn G ≤ 2 := by
  rcases Classical.em (∃ v : Fin 9, G.degree v ≤ 2) with hlow | hlow
  · -- `δ ≤ 2`: a low-degree vertex gives the test vector `|T|·e_u − 𝟙_T`.
    let : DecidableEq (Fin 9) := fun a b => Classical.propDecidable (a = b)
    obtain ⟨u, hdeg⟩ := hlow
    refine algConn_le_two_of_low_degree_vertex G u hdeg ?_
    rw [← Finset.card_pos, Finset.card_sdiff, Finset.inter_univ]
    have hcard : (insert u (G.neighborFinset u)).card ≤ 3 := by
      calc (insert u (G.neighborFinset u)).card
          ≤ (G.neighborFinset u).card + 1 := Finset.card_insert_le _ _
        _ = G.degree u + 1 := by rw [SimpleGraph.card_neighborFinset_eq_degree]
        _ ≤ 3 := by omega
    have huniv : (Finset.univ : Finset (Fin 9)).card = 9 := by simp
    omega
  · -- `δ ≥ 3`: every degree is `≥ 3`.  Split on whether `G` contains a triangle.
    let : DecidableEq (Fin 9) := fun a b => Classical.propDecidable (a = b)
    simp only [not_exists, not_le] at hlow
    have h3 : ∀ v : Fin 9, 3 ≤ G.degree v := fun v => by have := hlow v; omega
    have hsum : ∑ v : Fin 9, G.degree v = 28 := by
      rw [SimpleGraph.sum_degrees_eq_twice_card_edges, hm]
    -- Any two distinct vertices have degree sum `≤ 7` (since the other seven contribute `≥ 21`).
    have hpair : ∀ u w : Fin 9, u ≠ w → G.degree u + G.degree w ≤ 7 := by
      intro u w huw
      have hsplit : ∑ v ∈ ({u, w} : Finset (Fin 9)), G.degree v
          + ∑ v ∈ ({u, w} : Finset (Fin 9))ᶜ, G.degree v = 28 := by
        rw [Finset.sum_add_sum_compl]; exact hsum
      rw [Finset.sum_pair huw] at hsplit
      have hcc : (({u, w} : Finset (Fin 9))ᶜ).card = 7 := by
        rw [Finset.card_compl, Finset.card_pair huw, Fintype.card_fin]
      have hge : 21 ≤ ∑ v ∈ ({u, w} : Finset (Fin 9))ᶜ, G.degree v := by
        have hle : ∑ _v ∈ ({u, w} : Finset (Fin 9))ᶜ, (3 : ℕ)
            ≤ ∑ v ∈ ({u, w} : Finset (Fin 9))ᶜ, G.degree v :=
          Finset.sum_le_sum (fun v _ => h3 v)
        rw [Finset.sum_const, hcc, smul_eq_mul] at hle
        omega
      omega
    by_cases hT : ∃ x y z : Fin 9, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
        G.Adj x y ∧ G.Adj y z ∧ G.Adj x z
    · -- Triangle sub-case: the closed triangle `{x,y,z}` is a sparse weighted cut.
      obtain ⟨x, y, z, hxy_ne, hyz_ne, hxz_ne, hxy, hyz, hxz⟩ := hT
      have hAcard : ({x, y, z} : Finset (Fin 9)).card = 3 := by
        rw [Finset.card_insert_of_notMem (by simp [hxy_ne, hxz_ne]),
            Finset.card_insert_of_notMem (by simp [hyz_ne]), Finset.card_singleton]
      have hAccard : (({x, y, z} : Finset (Fin 9))ᶜ).card = 6 := by
        rw [Finset.card_compl, hAcard, Fintype.card_fin]
      have hA : ({x, y, z} : Finset (Fin 9)).Nonempty := ⟨x, by simp⟩
      have hAc : (({x, y, z} : Finset (Fin 9))ᶜ).Nonempty :=
        Finset.card_pos.mp (by rw [hAccard]; norm_num)
      -- Each vertex of the triangle meets the triangle in exactly its two partners.
      have triErase : ∀ a : Fin 9, a ∈ ({x, y, z} : Finset (Fin 9)) →
          (∀ b ∈ ({x, y, z} : Finset (Fin 9)), b ≠ a → G.Adj a b) →
          G.neighborFinset a ∩ ({x, y, z} : Finset (Fin 9))
            = ({x, y, z} : Finset (Fin 9)).erase a := by
        intro a _ hadj
        ext w
        simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset, Finset.mem_erase]
        constructor
        · rintro ⟨haw, hw⟩
          refine ⟨?_, hw⟩
          rintro rfl
          exact G.irrefl haw
        · rintro ⟨hwa, hw⟩
          exact ⟨hadj w hw hwa, hw⟩
      have interCardEq : ∀ a : Fin 9, a ∈ ({x, y, z} : Finset (Fin 9)) →
          (∀ b ∈ ({x, y, z} : Finset (Fin 9)), b ≠ a → G.Adj a b) →
          (G.neighborFinset a ∩ ({x, y, z} : Finset (Fin 9))).card = 2 := by
        intro a ha hadj
        rw [triErase a ha hadj, Finset.card_erase_of_mem ha, hAcard]
      have adjX : ∀ b ∈ ({x, y, z} : Finset (Fin 9)), b ≠ x → G.Adj x b := by
        intro b hb hbx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hb
        rcases hb with rfl | rfl | rfl
        · exact absurd rfl hbx
        · exact hxy
        · exact hxz
      have adjY : ∀ b ∈ ({x, y, z} : Finset (Fin 9)), b ≠ y → G.Adj y b := by
        intro b hb hby
        simp only [Finset.mem_insert, Finset.mem_singleton] at hb
        rcases hb with rfl | rfl | rfl
        · exact hxy.symm
        · exact absurd rfl hby
        · exact hyz
      have adjZ : ∀ b ∈ ({x, y, z} : Finset (Fin 9)), b ≠ z → G.Adj z b := by
        intro b hb hbz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hb
        rcases hb with rfl | rfl | rfl
        · exact hxz.symm
        · exact hyz.symm
        · exact absurd rfl hbz
      have interX : (G.neighborFinset x ∩ ({x, y, z} : Finset (Fin 9))).card = 2 :=
        interCardEq x (by simp) adjX
      have interY : (G.neighborFinset y ∩ ({x, y, z} : Finset (Fin 9))).card = 2 :=
        interCardEq y (by simp) adjY
      have interZ : (G.neighborFinset z ∩ ({x, y, z} : Finset (Fin 9))).card = 2 :=
        interCardEq z (by simp) adjZ
      -- Hence each triangle vertex sends `deg − 2` edges out of the triangle.
      have sdX : (G.neighborFinset x \ ({x, y, z} : Finset (Fin 9))).card + 2 = G.degree x := by
        have h := Finset.card_sdiff_add_card_inter (G.neighborFinset x)
          ({x, y, z} : Finset (Fin 9))
        rw [interX, G.card_neighborFinset_eq_degree] at h
        exact h
      have sdY : (G.neighborFinset y \ ({x, y, z} : Finset (Fin 9))).card + 2 = G.degree y := by
        have h := Finset.card_sdiff_add_card_inter (G.neighborFinset y)
          ({x, y, z} : Finset (Fin 9))
        rw [interY, G.card_neighborFinset_eq_degree] at h
        exact h
      have sdZ : (G.neighborFinset z \ ({x, y, z} : Finset (Fin 9))).card + 2 = G.degree z := by
        have h := Finset.card_sdiff_add_card_inter (G.neighborFinset z)
          ({x, y, z} : Finset (Fin 9))
        rw [interZ, G.card_neighborFinset_eq_degree] at h
        exact h
      -- The triangle's degree sum is `≤ 10` (at most one vertex has degree `4`).
      have degSumA : G.degree x + G.degree y + G.degree z ≤ 10 := by
        have h1 := hpair x y hxy_ne
        have h2 := hpair x z hxz_ne
        have h4 := hpair y z hyz_ne
        omega
      have cutEq : ∑ a ∈ ({x, y, z} : Finset (Fin 9)),
          (G.neighborFinset a \ ({x, y, z} : Finset (Fin 9))).card
          = (G.neighborFinset x \ ({x, y, z} : Finset (Fin 9))).card
            + (G.neighborFinset y \ ({x, y, z} : Finset (Fin 9))).card
            + (G.neighborFinset z \ ({x, y, z} : Finset (Fin 9))).card := by
        rw [Finset.sum_insert (by simp [hxy_ne, hxz_ne]),
            Finset.sum_insert (by simp [hyz_ne]), Finset.sum_singleton]
        ring
      have cutLe : ∑ a ∈ ({x, y, z} : Finset (Fin 9)),
          (G.neighborFinset a \ ({x, y, z} : Finset (Fin 9))).card ≤ 4 := by
        rw [cutEq]; omega
      refine algConn_le_two_of_weighted_cut G ({x, y, z} : Finset (Fin 9)) hA hAc ?_
      rw [hAcard, hAccard, Fintype.card_fin]
      omega
    · -- Triangle-free sub-case: produce an induced `2K₂` on four degree-3 vertices and apply
      -- the certificate `algConn_le_two_of_ind_2K2`.
      -- Every triangle-free graph on `Fin 9` with degree sequence `[4,3⁸]` has an induced `2K₂`
      -- on four degree-3 vertices.  The degree-3 vertices split as `N(w)` (independent, `w` the
      -- degree-4 vertex) and `M` (`|M| = 4`, inducing exactly 2 edges); each `N(w)`-vertex has
      -- exactly 2 neighbours in `M` and each `M`-vertex ≥ 1 neighbour in `N(w)`.  A per-vertex
      -- pigeonhole plus the fact that at most one `M`-vertex is `M`-isolated yields two
      -- `N(w)`-vertices with disjoint `M`-neighbourhoods, and a cross non-edge completes the `2K₂`.
      have hex : ∃ a b c d : Fin 9, ({a, b, c, d} : Finset (Fin 9)).card = 4 ∧
          G.degree a = 3 ∧ G.degree b = 3 ∧ G.degree c = 3 ∧ G.degree d = 3 ∧
          G.Adj a b ∧ G.Adj c d ∧
          ¬ G.Adj a c ∧ ¬ G.Adj a d ∧ ¬ G.Adj b c ∧ ¬ G.Adj b d := by
        -- triangle-freeness as a usable fact
        have htf : ∀ x y z : Fin 9, G.Adj x y → G.Adj y z → G.Adj x z → False := by
          intro x y z hxy hyz hxz
          exact hT ⟨x, y, z, hxy.ne, hyz.ne, hxz.ne, hxy, hyz, hxz⟩
        -- every degree is at most 4
        have hub : ∀ v : Fin 9, G.degree v ≤ 4 := by
          intro v
          obtain ⟨u, hu⟩ := exists_ne v
          have := hpair u v hu
          have := h3 u
          omega
        -- exactly one vertex `w` has degree 4
        obtain ⟨w, hw4⟩ : ∃ w : Fin 9, G.degree w = 4 := by
          by_contra h
          push Not at h
          have hall : ∀ v : Fin 9, G.degree v = 3 := fun v => by
            have := h3 v; have := hub v; have := h v; omega
          have : ∑ v : Fin 9, G.degree v = 27 := by
            rw [Finset.sum_congr rfl (fun v _ => hall v)]; simp
          omega
        have hw3 : ∀ v : Fin 9, v ≠ w → G.degree v = 3 := by
          intro v hv
          by_contra hne
          have hv4 : G.degree v = 4 := by have := h3 v; have := hub v; omega
          have := hpair v w hv
          omega
        -- the neighbourhood of `w` and the residual set `M`
        set Nw : Finset (Fin 9) := G.neighborFinset w with hNw
        have hmemNw : ∀ x : Fin 9, x ∈ Nw ↔ G.Adj w x := fun x => by
          rw [hNw, G.mem_neighborFinset]
        have hNwcard : Nw.card = 4 := by rw [hNw, G.card_neighborFinset_eq_degree, hw4]
        have hwNw : w ∉ Nw := by rw [hmemNw]; exact G.irrefl
        set M : Finset (Fin 9) := Finset.univ \ insert w Nw with hM
        have hmemM : ∀ m : Fin 9, m ∈ M ↔ (m ≠ w ∧ m ∉ Nw) := by
          intro m
          rw [hM, Finset.mem_sdiff, Finset.mem_insert]
          simp only [Finset.mem_univ, true_and, not_or]
        have hMcard : M.card = 4 := by
          rw [hM, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ,
              Fintype.card_fin, Finset.card_insert_of_notMem hwNw, hNwcard]
        -- FACT 1: `Nw` is independent (else a triangle with `w`).
        have hind : ∀ x ∈ Nw, ∀ y ∈ Nw, x ≠ y → ¬ G.Adj x y := by
          intro x hx y hy _ hadj
          exact htf w x y ((hmemNw x).mp hx) hadj ((hmemNw y).mp hy)
        -- Membership of `M`: not `w`, not adjacent to `w`.
        have hMnotw : ∀ m ∈ M, ¬ G.Adj w m := by
          intro m hm
          rw [← hmemNw]; exact ((hmemM m).mp hm).2
        -- FACT 2: each `Nw`-vertex has exactly two neighbours in `M`.
        have hScard : ∀ n ∈ Nw, (G.neighborFinset n ∩ M).card = 2 := by
          intro n hnNw
          have hnw : n ≠ w := fun h => hwNw (h ▸ hnNw)
          have hwn : G.Adj w n := (hmemNw n).mp hnNw
          have hStar : G.neighborFinset n ∩ insert w Nw = {w} := by
            ext y
            simp only [Finset.mem_inter, G.mem_neighborFinset, Finset.mem_insert,
              Finset.mem_singleton]
            constructor
            · rintro ⟨hny, rfl | hyNw⟩
              · rfl
              · exact absurd hny (hind n hnNw y hyNw hny.ne)
            · rintro rfl
              exact ⟨hwn.symm, Or.inl rfl⟩
          have hMeq : G.neighborFinset n ∩ M = G.neighborFinset n \ insert w Nw := by
            rw [hM]
            ext y
            simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_univ, true_and]
          have hcard := Finset.card_inter_add_card_sdiff (G.neighborFinset n) (insert w Nw)
          rw [hStar, Finset.card_singleton, ← hMeq, G.card_neighborFinset_eq_degree,
              hw3 n hnw] at hcard
          omega
        -- indicator form for counting incidences
        have indic : ∀ (s : Finset (Fin 9)) (v : Fin 9),
            (G.neighborFinset v ∩ s).card
              = ∑ y ∈ s, (if G.Adj v y then (1 : ℕ) else 0) := by
          intro s v
          rw [Finset.inter_comm, ← Finset.filter_mem_eq_inter, Finset.card_filter]
          exact Finset.sum_congr rfl (fun y _ => by simp only [G.mem_neighborFinset])
        -- double counting `Nw`–`M` incidences
        have hDC : ∑ n ∈ Nw, (G.neighborFinset n ∩ M).card
            = ∑ m ∈ M, (G.neighborFinset m ∩ Nw).card := by
          have e2 : ∀ m ∈ M, (G.neighborFinset m ∩ Nw).card
              = ∑ n ∈ Nw, (if G.Adj n m then (1 : ℕ) else 0) := by
            intro m _
            rw [indic Nw m]
            exact Finset.sum_congr rfl (fun n _ => by rw [G.adj_comm])
          rw [Finset.sum_congr rfl (fun n _ => indic M n), Finset.sum_congr rfl e2]
          exact Finset.sum_comm
        have hsum8 : ∑ n ∈ Nw, (G.neighborFinset n ∩ M).card = 8 := by
          rw [Finset.sum_congr rfl hScard]; simp [hNwcard]
        -- per-`M`-vertex split of degree 3 into `Nw`- and `M`-neighbours
        have hMrel : ∀ m ∈ M,
            (G.neighborFinset m ∩ Nw).card + (G.neighborFinset m ∩ M).card = 3 := by
          intro m hm
          have hmw : m ≠ w := ((hmemM m).mp hm).1
          have hInsEq : G.neighborFinset m ∩ insert w Nw = G.neighborFinset m ∩ Nw := by
            ext y
            simp only [Finset.mem_inter, G.mem_neighborFinset, Finset.mem_insert]
            constructor
            · rintro ⟨hmy, rfl | hyNw⟩
              · exact absurd hmy.symm (hMnotw m hm)
              · exact ⟨hmy, hyNw⟩
            · rintro ⟨hmy, hyNw⟩; exact ⟨hmy, Or.inr hyNw⟩
          have hMeq : G.neighborFinset m ∩ M = G.neighborFinset m \ insert w Nw := by
            rw [hM]; ext y
            simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_univ, true_and]
          have hcard := Finset.card_inter_add_card_sdiff (G.neighborFinset m) (insert w Nw)
          rw [hInsEq, ← hMeq, G.card_neighborFinset_eq_degree, hw3 m hmw] at hcard
          exact hcard
        have hNwM8 : ∑ m ∈ M, (G.neighborFinset m ∩ Nw).card = 8 := by
          rw [← hDC]; exact hsum8
        have heM : ∑ m ∈ M, (G.neighborFinset m ∩ M).card = 4 := by
          have h12 : ∑ m ∈ M, ((G.neighborFinset m ∩ Nw).card
              + (G.neighborFinset m ∩ M).card) = 12 := by
            rw [Finset.sum_congr rfl hMrel]; simp [hMcard]
          rw [Finset.sum_add_distrib, hNwM8] at h12
          omega
        -- FACT 3: each `M`-vertex has at least one neighbour in `Nw`.
        have hFact3 : ∀ m ∈ M, 1 ≤ (G.neighborFinset m ∩ Nw).card := by
          intro m hm
          by_contra hlt
          push Not at hlt
          have ht3 : (G.neighborFinset m ∩ M).card = 3 := by have := hMrel m hm; omega
          have hsub : G.neighborFinset m ∩ M ⊆ M.erase m := by
            intro y hy
            rw [Finset.mem_erase]
            refine ⟨?_, (Finset.mem_inter.mp hy).2⟩
            rintro rfl
            exact G.irrefl ((G.mem_neighborFinset y y).mp (Finset.mem_inter.mp hy).1)
          have hcardErase : (M.erase m).card = 3 := by
            rw [Finset.card_erase_of_mem hm, hMcard]
          have heq : G.neighborFinset m ∩ M = M.erase m :=
            Finset.eq_of_subset_of_card_le hsub (by rw [ht3, hcardErase])
          have hge : ∀ m' ∈ M.erase m, 1 ≤ (G.neighborFinset m' ∩ M).card := by
            intro m' hm'
            have hmem : m' ∈ G.neighborFinset m ∩ M := heq ▸ hm'
            have hadj : G.Adj m m' :=
              (G.mem_neighborFinset m m').mp (Finset.mem_inter.mp hmem).1
            have hmem2 : m ∈ G.neighborFinset m' ∩ M :=
              Finset.mem_inter.mpr ⟨(G.mem_neighborFinset m' m).mpr hadj.symm, hm⟩
            exact Finset.card_pos.mpr ⟨m, hmem2⟩
          have hsplit : (G.neighborFinset m ∩ M).card
              + ∑ m' ∈ M.erase m, (G.neighborFinset m' ∩ M).card
              = ∑ m' ∈ M, (G.neighborFinset m' ∩ M).card :=
            Finset.add_sum_erase M (fun m => (G.neighborFinset m ∩ M).card) hm
          rw [ht3, heM] at hsplit
          have hbig : 3 ≤ ∑ m' ∈ M.erase m, (G.neighborFinset m' ∩ M).card := by
            calc 3 = ∑ _m' ∈ M.erase m, 1 := by rw [Finset.sum_const, hcardErase]; simp
              _ ≤ _ := Finset.sum_le_sum hge
          omega
        -- helper: card of an explicit 4-element set with distinct entries
        have card4 : ∀ p q r s : Fin 9, p ≠ q → p ≠ r → p ≠ s → q ≠ r → q ≠ s → r ≠ s →
            ({p, q, r, s} : Finset (Fin 9)).card = 4 := by
          intro p q r s hpq hpr hps hqr hqs hrs
          rw [Finset.card_insert_of_notMem (by simp [hpq, hpr, hps]),
              Finset.card_insert_of_notMem (by simp [hqr, hqs]),
              Finset.card_insert_of_notMem (by simp [hrs]), Finset.card_singleton]
        -- FACT C: at most one `M`-vertex has all three of its neighbours in `Nw`.
        have hFactC : ∀ m1 ∈ M, ∀ m2 ∈ M, m1 ≠ m2 →
            (G.neighborFinset m1 ∩ Nw).card = 3 →
            (G.neighborFinset m2 ∩ Nw).card = 3 → False := by
          intro m1 hm1 m2 hm2 h12 hr1 hr2
          have hM1 : G.neighborFinset m1 ∩ M = ∅ := by
            rw [← Finset.card_eq_zero]; have := hMrel m1 hm1; omega
          have hM2 : G.neighborFinset m2 ∩ M = ∅ := by
            rw [← Finset.card_eq_zero]; have := hMrel m2 hm2; omega
          have hiso1 : ∀ x ∈ M, ¬ G.Adj m1 x := by
            intro x hx hadj
            have hmem : x ∈ G.neighborFinset m1 ∩ M :=
              Finset.mem_inter.mpr ⟨(G.mem_neighborFinset m1 x).mpr hadj, hx⟩
            rw [hM1] at hmem; exact Finset.notMem_empty x hmem
          have hiso2 : ∀ x ∈ M, ¬ G.Adj m2 x := by
            intro x hx hadj
            have hmem : x ∈ G.neighborFinset m2 ∩ M :=
              Finset.mem_inter.mpr ⟨(G.mem_neighborFinset m2 x).mpr hadj, hx⟩
            rw [hM2] at hmem; exact Finset.notMem_empty x hmem
          have hbd : ∀ m ∈ M, m ≠ m1 → m ≠ m2 →
              (G.neighborFinset m ∩ M).card ≤ 1 := by
            intro m hmM hmm1 hmm2
            have hsub : G.neighborFinset m ∩ M ⊆ M \ {m, m1, m2} := by
              intro y hy
              have hadjmy : G.Adj m y := (G.mem_neighborFinset m y).mp (Finset.mem_inter.mp hy).1
              rw [Finset.mem_sdiff]
              refine ⟨(Finset.mem_inter.mp hy).2, ?_⟩
              simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
              refine ⟨?_, ?_, ?_⟩
              · rintro rfl; exact G.irrefl hadjmy
              · rintro rfl; exact hiso1 m hmM hadjmy.symm
              · rintro rfl; exact hiso2 m hmM hadjmy.symm
            have hssub : ({m, m1, m2} : Finset (Fin 9)) ⊆ M := by
              intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
              rcases hz with rfl | rfl | rfl
              exacts [hmM, hm1, hm2]
            have hc3 : ({m, m1, m2} : Finset (Fin 9)).card = 3 := by
              rw [Finset.card_insert_of_notMem (by simp [hmm1, hmm2]),
                  Finset.card_insert_of_notMem (by simp [h12]), Finset.card_singleton]
            have heq : ({m, m1, m2} : Finset (Fin 9)) ∩ M = {m, m1, m2} :=
              Finset.inter_eq_left.mpr hssub
            have hcard1 : (M \ {m, m1, m2}).card = 1 := by
              rw [Finset.card_sdiff, heq, hMcard, hc3]
            have := Finset.card_le_card hsub
            omega
          have hm2' : m2 ∈ M.erase m1 := Finset.mem_erase.mpr ⟨(Ne.symm h12), hm2⟩
          have e1 : (G.neighborFinset m1 ∩ M).card
              + ∑ m ∈ M.erase m1, (G.neighborFinset m ∩ M).card
              = ∑ m ∈ M, (G.neighborFinset m ∩ M).card :=
            Finset.add_sum_erase M (fun m => (G.neighborFinset m ∩ M).card) hm1
          have e2 : (G.neighborFinset m2 ∩ M).card
              + ∑ m ∈ (M.erase m1).erase m2, (G.neighborFinset m ∩ M).card
              = ∑ m ∈ M.erase m1, (G.neighborFinset m ∩ M).card :=
            Finset.add_sum_erase (M.erase m1) (fun m => (G.neighborFinset m ∩ M).card) hm2'
          have hcardErase2 : ((M.erase m1).erase m2).card = 2 := by
            rw [Finset.card_erase_of_mem hm2', Finset.card_erase_of_mem hm1, hMcard]
          have hsmall : ∑ m ∈ (M.erase m1).erase m2, (G.neighborFinset m ∩ M).card ≤ 2 := by
            calc ∑ m ∈ (M.erase m1).erase m2, (G.neighborFinset m ∩ M).card
                ≤ ∑ _m ∈ (M.erase m1).erase m2, 1 := Finset.sum_le_sum (fun m hm =>
                    hbd m (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hm))
                      (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hm))
                      (Finset.ne_of_mem_erase hm))
              _ = 2 := by rw [Finset.sum_const, hcardErase2]; simp
          have hM1c : (G.neighborFinset m1 ∩ M).card = 0 := by rw [hM1]; simp
          have hM2c : (G.neighborFinset m2 ∩ M).card = 0 := by rw [hM2]; simp
          omega
        -- STEP A (crux): two `Nw`-vertices with disjoint `M`-neighbourhoods.
        have hStepA : ∃ n1 ∈ Nw, ∃ n2 ∈ Nw, n1 ≠ n2 ∧
            Disjoint (G.neighborFinset n1 ∩ M) (G.neighborFinset n2 ∩ M) := by
          by_contra hcon
          push Not at hcon
          have hint : ∀ a ∈ Nw, ∀ b ∈ Nw, a ≠ b →
              (G.neighborFinset a ∩ M ∩ (G.neighborFinset b ∩ M)).Nonempty := by
            intro a ha b hb hab
            rw [← Finset.not_disjoint_iff_nonempty_inter]
            exact hcon a ha b hb hab
          -- per-vertex pigeonhole: each `Nw`-vertex shares an `M`-vertex of `Nw`-degree 3.
          have hThree : ∀ n ∈ Nw, ∃ p ∈ M, (G.neighborFinset p ∩ Nw).card = 3
              ∧ p ∈ G.neighborFinset n ∩ M := by
            intro n hn
            let f : Fin 9 → Fin 9 := fun n' =>
              if h : (G.neighborFinset n ∩ M ∩ (G.neighborFinset n' ∩ M)).Nonempty
              then h.choose else n
            have hf_mem : ∀ n' ∈ Nw.erase n,
                f n' ∈ G.neighborFinset n ∩ M ∩ (G.neighborFinset n' ∩ M) := by
              intro n' hn'
              have hne' : (G.neighborFinset n ∩ M ∩ (G.neighborFinset n' ∩ M)).Nonempty :=
                hint n hn n' (Finset.mem_of_mem_erase hn')
                  (Ne.symm (Finset.ne_of_mem_erase hn'))
              simp only [f, dif_pos hne']
              exact hne'.choose_spec
            have hmaps : ∀ n' ∈ Nw.erase n, f n' ∈ G.neighborFinset n ∩ M :=
              fun n' hn' => (Finset.mem_inter.mp (hf_mem n' hn')).1
            have hcard_lt : (G.neighborFinset n ∩ M).card < (Nw.erase n).card := by
              rw [hScard n hn, Finset.card_erase_of_mem hn, hNwcard]; omega
            obtain ⟨a, ha, b, hb, hab, hfeq⟩ :=
              Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard_lt hmaps
            have hpn : f a ∈ G.neighborFinset n ∩ M := hmaps a ha
            have hpa : f a ∈ G.neighborFinset a ∩ M := (Finset.mem_inter.mp (hf_mem a ha)).2
            have hpb : f a ∈ G.neighborFinset b ∩ M := by
              rw [hfeq]; exact (Finset.mem_inter.mp (hf_mem b hb)).2
            have ha_mem : a ∈ Nw := Finset.mem_of_mem_erase ha
            have hb_mem : b ∈ Nw := Finset.mem_of_mem_erase hb
            have han : a ≠ n := Finset.ne_of_mem_erase ha
            have hbn : b ≠ n := Finset.ne_of_mem_erase hb
            have hAdjnp : G.Adj n (f a) :=
              (G.mem_neighborFinset n (f a)).mp (Finset.mem_inter.mp hpn).1
            have hAdjap : G.Adj a (f a) :=
              (G.mem_neighborFinset a (f a)).mp (Finset.mem_inter.mp hpa).1
            have hAdjbp : G.Adj b (f a) :=
              (G.mem_neighborFinset b (f a)).mp (Finset.mem_inter.mp hpb).1
            refine ⟨f a, (Finset.mem_inter.mp hpn).2, ?_, hpn⟩
            have hsub3 : ({n, a, b} : Finset (Fin 9)) ⊆ G.neighborFinset (f a) ∩ Nw := by
              rw [Finset.insert_subset_iff, Finset.insert_subset_iff,
                  Finset.singleton_subset_iff]
              refine ⟨?_, ?_, ?_⟩
              · exact Finset.mem_inter.mpr
                  ⟨(G.mem_neighborFinset (f a) n).mpr hAdjnp.symm, hn⟩
              · exact Finset.mem_inter.mpr
                  ⟨(G.mem_neighborFinset (f a) a).mpr hAdjap.symm, ha_mem⟩
              · exact Finset.mem_inter.mpr
                  ⟨(G.mem_neighborFinset (f a) b).mpr hAdjbp.symm, hb_mem⟩
            have hc3 : ({n, a, b} : Finset (Fin 9)).card = 3 := by
              rw [Finset.card_insert_of_notMem (by simp [Ne.symm han, Ne.symm hbn]),
                  Finset.card_insert_of_notMem (by simp [hab]), Finset.card_singleton]
            have hge3 : 3 ≤ (G.neighborFinset (f a) ∩ Nw).card := by
              rw [← hc3]; exact Finset.card_le_card hsub3
            have hle3 : (G.neighborFinset (f a) ∩ Nw).card ≤ 3 := by
              have := hMrel (f a) (Finset.mem_inter.mp hpn).2; omega
            omega
          obtain ⟨n0, hn0⟩ : Nw.Nonempty := Finset.card_pos.mp (by rw [hNwcard]; norm_num)
          obtain ⟨p, hpM, hpr, hpn0⟩ := hThree n0 hn0
          have hss : G.neighborFinset p ∩ Nw ⊂ Nw := by
            rw [Finset.ssubset_iff_subset_ne]
            exact ⟨Finset.inter_subset_right, by intro h; rw [h, hNwcard] at hpr; omega⟩
          obtain ⟨nk, hnkNw, hnknp⟩ := Finset.exists_of_ssubset hss
          have hnk_notadj : ¬ G.Adj p nk := fun hadj =>
            hnknp (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset p nk).mpr hadj, hnkNw⟩)
          obtain ⟨p', hp'M, hp'r, hp'nk⟩ := hThree nk hnkNw
          have hpp' : p ≠ p' := by
            rintro rfl
            exact hnk_notadj
              ((G.mem_neighborFinset nk p).mp (Finset.mem_inter.mp hp'nk).1).symm
          exact hFactC p hpM p' hp'M hpp' hpr hp'r
        obtain ⟨n1, hn1, n2, hn2, hn12, hdisj⟩ := hStepA
        -- STEP C (assembly), packaged as a function of the chosen cross non-edge.
        have hfin : ∀ a' c' : Fin 9, a' ∈ G.neighborFinset n1 ∩ M →
            c' ∈ G.neighborFinset n2 ∩ M → ¬ G.Adj a' c' →
            ∃ a b c d : Fin 9, ({a, b, c, d} : Finset (Fin 9)).card = 4 ∧
              G.degree a = 3 ∧ G.degree b = 3 ∧ G.degree c = 3 ∧ G.degree d = 3 ∧
              G.Adj a b ∧ G.Adj c d ∧
              ¬ G.Adj a c ∧ ¬ G.Adj a d ∧ ¬ G.Adj b c ∧ ¬ G.Adj b d := by
          intro a' c' ha' hc' hnac
          have hAdj1 : G.Adj n1 a' := (G.mem_neighborFinset n1 a').mp (Finset.mem_inter.mp ha').1
          have ha'M : a' ∈ M := (Finset.mem_inter.mp ha').2
          have hAdj2 : G.Adj n2 c' := (G.mem_neighborFinset n2 c').mp (Finset.mem_inter.mp hc').1
          have hc'M : c' ∈ M := (Finset.mem_inter.mp hc').2
          have hn1w : n1 ≠ w := fun h => hwNw (h ▸ hn1)
          have hn2w : n2 ≠ w := fun h => hwNw (h ▸ hn2)
          have ha'w : a' ≠ w := ((hmemM a').mp ha'M).1
          have hc'w : c' ≠ w := ((hmemM c').mp hc'M).1
          have ha'Nw : a' ∉ Nw := ((hmemM a').mp ha'M).2
          have hc'Nw : c' ∉ Nw := ((hmemM c').mp hc'M).2
          have hne1 : n1 ≠ a' := by intro h; apply ha'Nw; rw [← h]; exact hn1
          have hne2 : n1 ≠ c' := by intro h; apply hc'Nw; rw [← h]; exact hn1
          have hne3 : a' ≠ n2 := by intro h; apply ha'Nw; rw [h]; exact hn2
          have hne4 : n2 ≠ c' := by intro h; apply hc'Nw; rw [← h]; exact hn2
          have ha'notS2 : a' ∉ G.neighborFinset n2 ∩ M := Finset.disjoint_left.mp hdisj ha'
          have hc'notS1 : c' ∉ G.neighborFinset n1 ∩ M :=
            fun h => (Finset.disjoint_left.mp hdisj h) hc'
          have hne5 : a' ≠ c' := by intro h; exact ha'notS2 (by rw [h]; exact hc')
          have hncross1 : ¬ G.Adj n1 n2 := hind n1 hn1 n2 hn2 hn12
          have hncross2 : ¬ G.Adj n1 c' := fun h =>
            hc'notS1 (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset n1 c').mpr h, hc'M⟩)
          have hncross3 : ¬ G.Adj a' n2 := fun h =>
            ha'notS2 (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset n2 a').mpr h.symm, ha'M⟩)
          exact ⟨n1, a', n2, c', card4 n1 a' n2 c' hne1 hn12 hne2 hne3 hne5 hne4,
            hw3 n1 hn1w, hw3 a' ha'w, hw3 n2 hn2w, hw3 c' hc'w,
            hAdj1, hAdj2, hncross1, hncross2, hncross3, hnac⟩
        -- STEP B: among the four cross pairs there is a non-edge (else `M` has ≥4 edges).
        obtain ⟨a, b, hab_ne, hSeq1⟩ := Finset.card_eq_two.mp (hScard n1 hn1)
        obtain ⟨c, d, hcd_ne, hSeq2⟩ := Finset.card_eq_two.mp (hScard n2 hn2)
        have ha : a ∈ G.neighborFinset n1 ∩ M := by rw [hSeq1]; simp
        have hb : b ∈ G.neighborFinset n1 ∩ M := by rw [hSeq1]; simp
        have hc : c ∈ G.neighborFinset n2 ∩ M := by rw [hSeq2]; simp
        have hd : d ∈ G.neighborFinset n2 ∩ M := by rw [hSeq2]; simp
        have aM : a ∈ M := (Finset.mem_inter.mp ha).2
        have bM : b ∈ M := (Finset.mem_inter.mp hb).2
        have cM : c ∈ M := (Finset.mem_inter.mp hc).2
        have dM : d ∈ M := (Finset.mem_inter.mp hd).2
        by_cases hac : G.Adj a c
        · by_cases had : G.Adj a d
          · by_cases hbc : G.Adj b c
            · by_cases hbd : G.Adj b d
              · -- all four cross pairs are edges: contradiction with `e(M) = 2`
                exfalso
                have hac_ne : a ≠ c := by
                  intro h; exact (Finset.disjoint_left.mp hdisj ha) (by rw [h]; exact hc)
                have had_ne : a ≠ d := by
                  intro h; exact (Finset.disjoint_left.mp hdisj ha) (by rw [h]; exact hd)
                have hbc_ne : b ≠ c := by
                  intro h; exact (Finset.disjoint_left.mp hdisj hb) (by rw [h]; exact hc)
                have hbd_ne : b ≠ d := by
                  intro h; exact (Finset.disjoint_left.mp hdisj hb) (by rw [h]; exact hd)
                have hsub : ({a, b, c, d} : Finset (Fin 9)) ⊆ M := by
                  intro x hx
                  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
                  rcases hx with rfl | rfl | rfl | rfl
                  exacts [aM, bM, cM, dM]
                have hMabcd : M = {a, b, c, d} := by
                  refine (Finset.eq_of_subset_of_card_le hsub ?_).symm
                  rw [hMcard, card4 a b c d hab_ne hac_ne had_ne hbc_ne hbd_ne hcd_ne]
                have hexp : ∑ m ∈ ({a, b, c, d} : Finset (Fin 9)),
                    (G.neighborFinset m ∩ M).card
                    = (G.neighborFinset a ∩ M).card + (G.neighborFinset b ∩ M).card
                      + (G.neighborFinset c ∩ M).card + (G.neighborFinset d ∩ M).card := by
                  rw [Finset.sum_insert (by simp [hab_ne, hac_ne, had_ne]),
                      Finset.sum_insert (by simp [hbc_ne, hbd_ne]),
                      Finset.sum_insert (by simp [hcd_ne]), Finset.sum_singleton]
                  ring
                have h4 : (G.neighborFinset a ∩ M).card + (G.neighborFinset b ∩ M).card
                    + (G.neighborFinset c ∩ M).card + (G.neighborFinset d ∩ M).card = 4 := by
                  rw [← hexp, ← Finset.sum_congr hMabcd (fun _ _ => rfl)]; exact heM
                have lb_a : 2 ≤ (G.neighborFinset a ∩ M).card := by
                  have hsubcd : ({c, d} : Finset (Fin 9)) ⊆ G.neighborFinset a ∩ M := by
                    intro x hx
                    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
                    rcases hx with rfl | rfl
                    · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset a x).mpr hac, cM⟩
                    · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset a x).mpr had, dM⟩
                  calc 2 = ({c, d} : Finset (Fin 9)).card := (Finset.card_pair hcd_ne).symm
                    _ ≤ _ := Finset.card_le_card hsubcd
                have lb_b : 2 ≤ (G.neighborFinset b ∩ M).card := by
                  have hsubcd : ({c, d} : Finset (Fin 9)) ⊆ G.neighborFinset b ∩ M := by
                    intro x hx
                    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
                    rcases hx with rfl | rfl
                    · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset b x).mpr hbc, cM⟩
                    · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset b x).mpr hbd, dM⟩
                  calc 2 = ({c, d} : Finset (Fin 9)).card := (Finset.card_pair hcd_ne).symm
                    _ ≤ _ := Finset.card_le_card hsubcd
                have lb_c : 2 ≤ (G.neighborFinset c ∩ M).card := by
                  have hsubab : ({a, b} : Finset (Fin 9)) ⊆ G.neighborFinset c ∩ M := by
                    intro x hx
                    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
                    rcases hx with rfl | rfl
                    · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset c x).mpr hac.symm, aM⟩
                    · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset c x).mpr hbc.symm, bM⟩
                  calc 2 = ({a, b} : Finset (Fin 9)).card := (Finset.card_pair hab_ne).symm
                    _ ≤ _ := Finset.card_le_card hsubab
                have lb_d : 2 ≤ (G.neighborFinset d ∩ M).card := by
                  have hsubab : ({a, b} : Finset (Fin 9)) ⊆ G.neighborFinset d ∩ M := by
                    intro x hx
                    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
                    rcases hx with rfl | rfl
                    · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset d x).mpr had.symm, aM⟩
                    · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset d x).mpr hbd.symm, bM⟩
                  calc 2 = ({a, b} : Finset (Fin 9)).card := (Finset.card_pair hab_ne).symm
                    _ ≤ _ := Finset.card_le_card hsubab
                omega
              · exact hfin b d hb hd hbd
            · exact hfin b c hb hc hbc
          · exact hfin a d ha hd had
        · exact hfin a c ha hc hac
      obtain ⟨a, b, c, d, hdist, hda, hdb, hdc, hdd, hab, hcd, hac, had, hbc, hbd⟩ := hex
      exact algConn_le_two_of_ind_2K2 G a b c d hdist hab hcd hac had hbc hbd (by omega)

/-- The full ACMAX conjecture for `n = 9` (`K_{2,7}` is the maximizer; bound `2`): both the
equality half (`algConn (K_{2,7}) = 2`) and the universal upper bound (via `upperBound_nine`)
are fully proved. -/
theorem acmax_conjecture_nine :
    algConn (completeBipartiteGraph (Fin 2) (Fin 7)) = 2 ∧
      ∀ G : SimpleGraph (Fin 9), G.edgeFinset.card = 14 → algConn G ≤ 2 :=
  ⟨algConn_completeBipartite_two 9 (by norm_num), fun G hm => upperBound_nine G hm⟩

end ACMax
