import ACMaxConjecture.Base
import ACMaxConjecture.Spectral.AlgConn
import ACMaxConjecture.Cuts.LowDegreeVertex
import ACMaxConjecture.Cuts.WeightedCut
import ACMaxConjecture.Cuts.Ind2K2
import ACMaxConjecture.Cuts.TriangleFree2K2
import ACMaxConjecture.Cuts.Disconnected
import ACMaxConjecture.Cuts.Cut2K2Free
import ACMaxConjecture.Spectral.AlgConnK2

/-!
# The ACMAX conjecture for `n = 11`

`m = 2(n-2) = 18`.  `δ ≤ 2` → low-degree lemma.  Otherwise `δ ≥ 3` and `∑ deg = 36`,
so at most three vertices have degree `≥ 4` (four would give `∑ ≥ 37`), hence `≥ 8`
vertices have degree exactly `3`.  Cases:
* disconnected → `algConn_le_two_of_separated` (a `0`-cut);
* a good triangle (degree sum `≤ 10`) → weighted cut (`|A|=3`, `cut ≤ 4`, `11·4 = 44 ≤ 2·3·8`);
* otherwise an induced `2K₂` on degree-3 vertices via `exists_induced_2K2_of_triangleFree_smalldeg`
  (`|D| ≥ 8`) — **provided** the degree-3 subgraph has no isolated vertex.

The remaining sub-case — a connected, no-good-triangle graph with an *isolated* degree-3
vertex (all three neighbours of degree 4, forcing degree sequence `[4,4,4,3⁸]`) — is the
deepest residual for `n = 11`.  It is genuinely hard, and is **not** closable by the
induced-`2K₂` method alone: there is an explicit residual graph whose degree-3 subgraph is
`K_{2,3}` (twins `{0,1,2}` → hubs `{3,4,5}`; `K_{2,3}` on `{6,7|8,9,10}`; hubs→`D''`
`3–8,4–9,5–10`), which is connected, triangle-free, has no good triangle and **no induced
`2K₂` on degree-3 vertices** (since `K_{2,3}` is `2K₂`-free), yet `λ₂ ≈ 0.92`.  That graph *is*
certified by a weighted cut.

An EXHAUSTIVE enumeration via nauty canonical certificates (all `119` connected, no-good-triangle,
isolated-degree-3 graphs up to isomorphism — `[4,4,4,3⁸]` is the only degree sequence admitting an
isolated degree-3 vertex) establishes a **uniform dichotomy** that covers `119/119`:
* `111` graphs have an induced `2K₂` on degree-3 vertices → `algConn_le_two_of_ind_2K2`;
* the other `8` (no `2K₂`) are certified by the weighted cut
  `A = (degree-4 vertices) ∪ (isolated degree-3 vertices) ∪ (degree-3 vertices adjacent to ≥2
  degree-4 vertices)`.
The disconnected sub-case is proved (`algConn_le_two_of_not_connected`); the connected
`2K₂`-free case is discharged by `algConn_le_two_of_2K2free_cut` (`Cuts/Cut2K2Free.lean`), which
proves `11·cut(A) ≤ 2·|A|·|Aᶜ|` whenever the degree-3 subgraph is `2K₂`-free, from first
principles (axiom-clean).

(Earlier drafts of this comment claimed the residual always contains a `2K₂`, then that it had
"no uniform construction"; both were premature — the exhaustive enumeration above gives the
`2K₂ ∨ cut` dichotomy.)
-/

namespace ACMax

open scoped Classical

/-- Upper bound clause for `n = 11`. -/
theorem upperBound_eleven (G : SimpleGraph (Fin 11)) (hm : G.edgeFinset.card = 18) :
    algConn G ≤ 2 := by
  rcases Classical.em (∃ v : Fin 11, G.degree v ≤ 2) with hlow | hlow
  · -- `δ ≤ 2`: a low-degree vertex gives the test vector `|T|·e_u − 𝟙_T`.
    let : DecidableEq (Fin 11) := fun a b => Classical.propDecidable (a = b)
    obtain ⟨u, hdeg⟩ := hlow
    refine algConn_le_two_of_low_degree_vertex G u hdeg ?_
    rw [← Finset.card_pos, Finset.card_sdiff, Finset.inter_univ]
    have hcard : (insert u (G.neighborFinset u)).card ≤ 3 := by
      calc (insert u (G.neighborFinset u)).card
          ≤ (G.neighborFinset u).card + 1 := Finset.card_insert_le _ _
        _ = G.degree u + 1 := by rw [SimpleGraph.card_neighborFinset_eq_degree]
        _ ≤ 3 := by omega
    have huniv : (Finset.univ : Finset (Fin 11)).card = 11 := by simp
    omega
  · -- `δ ≥ 3`: every degree is `≥ 3`.  Split on whether `G` has a degree-sparse triangle.
    let : DecidableEq (Fin 11) := fun a b => Classical.propDecidable (a = b)
    simp only [not_exists, not_le] at hlow
    have h3 : ∀ v : Fin 11, 3 ≤ G.degree v := fun v => by have := hlow v; omega
    have hsum : ∑ v : Fin 11, G.degree v = 36 := by
      rw [SimpleGraph.sum_degrees_eq_twice_card_edges, hm]
    by_cases hT : ∃ x y z : Fin 11, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
        G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧
        G.degree x + G.degree y + G.degree z ≤ 10
    · -- Good-triangle sub-case: the closed triangle `{x,y,z}` is a sparse weighted cut.
      obtain ⟨x, y, z, hxy_ne, hyz_ne, hxz_ne, hxy, hyz, hxz, hdsum⟩ := hT
      have hAcard : ({x, y, z} : Finset (Fin 11)).card = 3 := by
        rw [Finset.card_insert_of_notMem (by simp [hxy_ne, hxz_ne]),
            Finset.card_insert_of_notMem (by simp [hyz_ne]), Finset.card_singleton]
      have hAccard : (({x, y, z} : Finset (Fin 11))ᶜ).card = 8 := by
        rw [Finset.card_compl, hAcard, Fintype.card_fin]
      have hA : ({x, y, z} : Finset (Fin 11)).Nonempty := ⟨x, by simp⟩
      have hAc : (({x, y, z} : Finset (Fin 11))ᶜ).Nonempty :=
        Finset.card_pos.mp (by rw [hAccard]; norm_num)
      -- Each vertex of the triangle meets the triangle in exactly its two partners.
      have triErase : ∀ a : Fin 11, a ∈ ({x, y, z} : Finset (Fin 11)) →
          (∀ b ∈ ({x, y, z} : Finset (Fin 11)), b ≠ a → G.Adj a b) →
          G.neighborFinset a ∩ ({x, y, z} : Finset (Fin 11))
            = ({x, y, z} : Finset (Fin 11)).erase a := by
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
      have interCardEq : ∀ a : Fin 11, a ∈ ({x, y, z} : Finset (Fin 11)) →
          (∀ b ∈ ({x, y, z} : Finset (Fin 11)), b ≠ a → G.Adj a b) →
          (G.neighborFinset a ∩ ({x, y, z} : Finset (Fin 11))).card = 2 := by
        intro a ha hadj
        rw [triErase a ha hadj, Finset.card_erase_of_mem ha, hAcard]
      have adjX : ∀ b ∈ ({x, y, z} : Finset (Fin 11)), b ≠ x → G.Adj x b := by
        intro b hb hbx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hb
        rcases hb with rfl | rfl | rfl
        · exact absurd rfl hbx
        · exact hxy
        · exact hxz
      have adjY : ∀ b ∈ ({x, y, z} : Finset (Fin 11)), b ≠ y → G.Adj y b := by
        intro b hb hby
        simp only [Finset.mem_insert, Finset.mem_singleton] at hb
        rcases hb with rfl | rfl | rfl
        · exact hxy.symm
        · exact absurd rfl hby
        · exact hyz
      have adjZ : ∀ b ∈ ({x, y, z} : Finset (Fin 11)), b ≠ z → G.Adj z b := by
        intro b hb hbz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hb
        rcases hb with rfl | rfl | rfl
        · exact hxz.symm
        · exact hyz.symm
        · exact absurd rfl hbz
      have interX : (G.neighborFinset x ∩ ({x, y, z} : Finset (Fin 11))).card = 2 :=
        interCardEq x (by simp) adjX
      have interY : (G.neighborFinset y ∩ ({x, y, z} : Finset (Fin 11))).card = 2 :=
        interCardEq y (by simp) adjY
      have interZ : (G.neighborFinset z ∩ ({x, y, z} : Finset (Fin 11))).card = 2 :=
        interCardEq z (by simp) adjZ
      -- Hence each triangle vertex sends `deg − 2` edges out of the triangle.
      have sdX : (G.neighborFinset x \ ({x, y, z} : Finset (Fin 11))).card + 2 = G.degree x := by
        have h := Finset.card_sdiff_add_card_inter (G.neighborFinset x)
          ({x, y, z} : Finset (Fin 11))
        rw [interX, G.card_neighborFinset_eq_degree] at h
        exact h
      have sdY : (G.neighborFinset y \ ({x, y, z} : Finset (Fin 11))).card + 2 = G.degree y := by
        have h := Finset.card_sdiff_add_card_inter (G.neighborFinset y)
          ({x, y, z} : Finset (Fin 11))
        rw [interY, G.card_neighborFinset_eq_degree] at h
        exact h
      have sdZ : (G.neighborFinset z \ ({x, y, z} : Finset (Fin 11))).card + 2 = G.degree z := by
        have h := Finset.card_sdiff_add_card_inter (G.neighborFinset z)
          ({x, y, z} : Finset (Fin 11))
        rw [interZ, G.card_neighborFinset_eq_degree] at h
        exact h
      have cutEq : ∑ a ∈ ({x, y, z} : Finset (Fin 11)),
          (G.neighborFinset a \ ({x, y, z} : Finset (Fin 11))).card
          = (G.neighborFinset x \ ({x, y, z} : Finset (Fin 11))).card
            + (G.neighborFinset y \ ({x, y, z} : Finset (Fin 11))).card
            + (G.neighborFinset z \ ({x, y, z} : Finset (Fin 11))).card := by
        rw [Finset.sum_insert (by simp [hxy_ne, hxz_ne]),
            Finset.sum_insert (by simp [hyz_ne]), Finset.sum_singleton]
        ring
      have cutLe : ∑ a ∈ ({x, y, z} : Finset (Fin 11)),
          (G.neighborFinset a \ ({x, y, z} : Finset (Fin 11))).card ≤ 4 := by
        rw [cutEq]; omega
      refine algConn_le_two_of_weighted_cut G ({x, y, z} : Finset (Fin 11)) hA hAc ?_
      rw [hAcard, hAccard, Fintype.card_fin]
      omega
    · -- No-good-triangle sub-case: the degree-3 vertices form `D`, with `|D| ≥ 8`.
      set D := Finset.univ.filter (fun v => G.degree v = 3) with hD
      set H := Finset.univ.filter (fun v => 4 ≤ G.degree v) with hH
      have hmemD : ∀ v : Fin 11, v ∈ D ↔ G.degree v = 3 := by
        intro v; rw [hD]; simp
      have hmemH : ∀ v : Fin 11, v ∈ H ↔ 4 ≤ G.degree v := by
        intro v; rw [hH]; simp
      have hDH : ∀ v : Fin 11, v ∈ D ∨ v ∈ H := by
        intro v
        rcases Nat.lt_or_ge (G.degree v) 4 with hlt | hge
        · exact Or.inl ((hmemD v).mpr (by have := h3 v; omega))
        · exact Or.inr ((hmemH v).mpr hge)
      have hdisj : Disjoint D H := by
        rw [Finset.disjoint_left]
        intro v hvD hvH
        have h1 := (hmemD v).mp hvD
        have h2 := (hmemH v).mp hvH
        omega
      have hunion : D ∪ H = Finset.univ := by
        ext v
        simp only [Finset.mem_union, Finset.mem_univ, iff_true]
        exact hDH v
      have hsumpart : ∑ v ∈ D, G.degree v + ∑ v ∈ H, G.degree v = 36 := by
        rw [← Finset.sum_union hdisj, hunion]; exact hsum
      have hsumD : ∑ v ∈ D, G.degree v = 3 * D.card := by
        rw [Finset.sum_congr rfl (fun v hv => (hmemD v).mp hv), Finset.sum_const,
          smul_eq_mul, mul_comm]
      have hsumH : H.card * 4 ≤ ∑ v ∈ H, G.degree v := by
        have hb : ∀ x ∈ H, 4 ≤ (fun v => G.degree v) x := fun i hi => (hmemH i).mp hi
        have h := Finset.card_nsmul_le_sum H (fun v => G.degree v) 4 hb
        simpa [smul_eq_mul] using h
      have hpart2 : D.card + H.card = 11 := by
        have h := Finset.card_union_of_disjoint hdisj
        rw [hunion, Finset.card_univ, Fintype.card_fin] at h
        omega
      rw [hsumD] at hsumpart
      have hHcard : H.card ≤ 3 := by omega
      have hDcard : 8 ≤ D.card := by omega
      have hmax : ∀ a ∈ D, (G.neighborFinset a ∩ D).card ≤ 3 := by
        intro a haD
        calc (G.neighborFinset a ∩ D).card
            ≤ (G.neighborFinset a).card := Finset.card_le_card Finset.inter_subset_left
          _ = G.degree a := G.card_neighborFinset_eq_degree a
          _ = 3 := (hmemD a).mp haD
      have htri : ∀ a ∈ D, ∀ b ∈ D, ∀ c ∈ D, ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj a c) := by
        rintro a haD b hbD c hcD ⟨hab, hbc, hac⟩
        refine hT ⟨a, b, c, G.ne_of_adj hab, G.ne_of_adj hbc, G.ne_of_adj hac,
          hab, hbc, hac, ?_⟩
        have da := (hmemD a).mp haD
        have db := (hmemD b).mp hbD
        have dc := (hmemD c).mp hcD
        omega
      by_cases hmin : ∀ a ∈ D, 1 ≤ (G.neighborFinset a ∩ D).card
      · -- Every degree-3 vertex has a degree-3 neighbour: the lemma gives an induced `2K₂`.
        obtain ⟨a, haD, b, hbD, c, hcD, d, hdD, hcard4, hab, hcd, hac, had, hbc, hbd⟩ :=
          exists_induced_2K2_of_triangleFree_smalldeg G D htri hmin hmax hDcard
        have hda := (hmemD a).mp haD
        have hdb := (hmemD b).mp hbD
        have hdc := (hmemD c).mp hcD
        have hdd := (hmemD d).mp hdD
        exact algConn_le_two_of_ind_2K2 G a b c d hcard4 hab hcd hac had hbc hbd (by omega)
      · -- Residual: a no-good-triangle graph with an ISOLATED degree-3 vertex (all of whose
        -- neighbours have degree 4), forcing degree sequence [4,4,4,3⁸].
        by_cases hconn : G.Connected
        · -- CONNECTED residual.  Forced degree sequence [4,4,4,3⁸].  An EXHAUSTIVE enumeration
          -- (nauty canonical certificates over all 119 such graphs up to isomorphism) shows it is
          -- closed by a uniform DICHOTOMY:
          --   • if the degree-3 subgraph contains an induced 2K₂ → `algConn_le_two_of_ind_2K2`
          --     (111 of the 119 graphs);
          --   • otherwise (8 graphs, e.g. the K_{2,3} one in the module header) → the weighted cut
          --     A = (degree-4 vertices) ∪ (isolated degree-3 vertices)
          --       ∪ (degree-3 vertices adjacent to ≥2 degree-4 vertices),
          --     which satisfies `11·cut(A) ≤ 2·|A|·|Aᶜ|` for every 2K₂-free case.
          -- Verified: 2K₂ ∨ this-cut covers 119/119.  The 2K₂-free cut inequality
          -- `11·cut(A) ≤ 2·|A|·|Aᶜ|` is discharged by `algConn_le_two_of_2K2free_cut`
          -- (proved from first principles, axiom-clean).
          by_cases h2k2 : ∃ a b c d : Fin 11, ({a, b, c, d} : Finset (Fin 11)).card = 4 ∧
              G.degree a = 3 ∧ G.degree b = 3 ∧ G.degree c = 3 ∧ G.degree d = 3 ∧
              G.Adj a b ∧ G.Adj c d ∧ ¬ G.Adj a c ∧ ¬ G.Adj a d ∧ ¬ G.Adj b c ∧ ¬ G.Adj b d
          · -- An induced 2K₂ on degree-3 vertices exists (111 of the 119 residual graphs).
            obtain ⟨a, b, c, d, hcard4, hda, hdb, hdc, hdd, hab, hcd, hac, had, hbc, hbd⟩ := h2k2
            exact algConn_le_two_of_ind_2K2 G a b c d hcard4 hab hcd hac had hbc hbd (by omega)
          · -- No induced 2K₂ (the 8 remaining graphs, e.g. the K_{2,3} one): the weighted-cut
            -- certificate `algConn_le_two_of_2K2free_cut`.  Its entire reduction — including the
            -- edge-density bound `e(Aᶜ) ≥ t(11+2t)/22` — is proved from first principles
            -- (axiom-clean).
            refine algConn_le_two_of_2K2free_cut G hm h3 hconn hT ?_
            convert h2k2
        · -- DISCONNECTED residual (e.g. the k=4 sub-case, a K_{4,3} component): uniformly handled.
          exact algConn_le_two_of_not_connected G hconn

/-- The full ACMAX conjecture for `n = 11` (`K_{2,9}` is the maximizer; bound `2`). -/
theorem acmax_conjecture_eleven :
    algConn (completeBipartiteGraph (Fin 2) (Fin 9)) = 2 ∧
      ∀ G : SimpleGraph (Fin 11), G.edgeFinset.card = 18 → algConn G ≤ 2 :=
  ⟨algConn_completeBipartite_two 11 (by norm_num), fun G hm => upperBound_eleven G hm⟩

end ACMax
