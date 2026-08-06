import ACMaxConjecture.Base
import ACMaxConjecture.Spectral.AlgConn
import ACMaxConjecture.Cuts.LowDegreeVertex
import ACMaxConjecture.Cuts.WeightedCut
import ACMaxConjecture.Cuts.Ind2K2
import ACMaxConjecture.Spectral.AlgConnK2
import ACMaxConjecture.Cuts.TriangleFree2K2

/-!
# The ACMAX conjecture for `n = 10`

`m = 2(n-2) = 16`.  `δ ≤ 2` is closed by `algConn_le_two_of_low_degree_vertex`.
Otherwise `δ ≥ 3` and `∑ deg = 32 = 3·10 + 2`, forcing degree sequence `[4,4,3⁸]`.
Every such graph has either a triangle of degree sum `≤ 10` (a sparse weighted cut,
`|A|=3`, `cut = ∑deg − 6 ≤ 4`, `10·4 = 40 ≤ 2·3·7`) or an induced `2K₂` on four
degree-3 vertices (`algConn_le_two_of_ind_2K2`).
-/

namespace ACMax

open scoped Classical

/-- Upper bound clause for `n = 10`. -/
theorem upperBound_ten (G : SimpleGraph (Fin 10)) (hm : G.edgeFinset.card = 16) :
    algConn G ≤ 2 := by
  rcases Classical.em (∃ v : Fin 10, G.degree v ≤ 2) with hlow | hlow
  · -- `δ ≤ 2`: a low-degree vertex gives the test vector `|T|·e_u − 𝟙_T`.
    let : DecidableEq (Fin 10) := fun a b => Classical.propDecidable (a = b)
    obtain ⟨u, hdeg⟩ := hlow
    refine algConn_le_two_of_low_degree_vertex G u hdeg ?_
    rw [← Finset.card_pos, Finset.card_sdiff, Finset.inter_univ]
    have hcard : (insert u (G.neighborFinset u)).card ≤ 3 := by
      calc (insert u (G.neighborFinset u)).card
          ≤ (G.neighborFinset u).card + 1 := Finset.card_insert_le _ _
        _ = G.degree u + 1 := by rw [SimpleGraph.card_neighborFinset_eq_degree]
        _ ≤ 3 := by omega
    have huniv : (Finset.univ : Finset (Fin 10)).card = 10 := by simp
    omega
  · -- `δ ≥ 3`: every degree is `≥ 3`.  Split on whether `G` has a degree-sparse triangle.
    let : DecidableEq (Fin 10) := fun a b => Classical.propDecidable (a = b)
    simp only [not_exists, not_le] at hlow
    have h3 : ∀ v : Fin 10, 3 ≤ G.degree v := fun v => by have := hlow v; omega
    have hsum : ∑ v : Fin 10, G.degree v = 32 := by
      rw [SimpleGraph.sum_degrees_eq_twice_card_edges, hm]
    by_cases hT : ∃ x y z : Fin 10, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
        G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧
        G.degree x + G.degree y + G.degree z ≤ 10
    · -- Good-triangle sub-case: the closed triangle `{x,y,z}` is a sparse weighted cut.
      obtain ⟨x, y, z, hxy_ne, hyz_ne, hxz_ne, hxy, hyz, hxz, hdsum⟩ := hT
      have hAcard : ({x, y, z} : Finset (Fin 10)).card = 3 := by
        rw [Finset.card_insert_of_notMem (by simp [hxy_ne, hxz_ne]),
            Finset.card_insert_of_notMem (by simp [hyz_ne]), Finset.card_singleton]
      have hAccard : (({x, y, z} : Finset (Fin 10))ᶜ).card = 7 := by
        rw [Finset.card_compl, hAcard, Fintype.card_fin]
      have hA : ({x, y, z} : Finset (Fin 10)).Nonempty := ⟨x, by simp⟩
      have hAc : (({x, y, z} : Finset (Fin 10))ᶜ).Nonempty :=
        Finset.card_pos.mp (by rw [hAccard]; norm_num)
      -- Each vertex of the triangle meets the triangle in exactly its two partners.
      have triErase : ∀ a : Fin 10, a ∈ ({x, y, z} : Finset (Fin 10)) →
          (∀ b ∈ ({x, y, z} : Finset (Fin 10)), b ≠ a → G.Adj a b) →
          G.neighborFinset a ∩ ({x, y, z} : Finset (Fin 10))
            = ({x, y, z} : Finset (Fin 10)).erase a := by
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
      have interCardEq : ∀ a : Fin 10, a ∈ ({x, y, z} : Finset (Fin 10)) →
          (∀ b ∈ ({x, y, z} : Finset (Fin 10)), b ≠ a → G.Adj a b) →
          (G.neighborFinset a ∩ ({x, y, z} : Finset (Fin 10))).card = 2 := by
        intro a ha hadj
        rw [triErase a ha hadj, Finset.card_erase_of_mem ha, hAcard]
      have adjX : ∀ b ∈ ({x, y, z} : Finset (Fin 10)), b ≠ x → G.Adj x b := by
        intro b hb hbx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hb
        rcases hb with rfl | rfl | rfl
        · exact absurd rfl hbx
        · exact hxy
        · exact hxz
      have adjY : ∀ b ∈ ({x, y, z} : Finset (Fin 10)), b ≠ y → G.Adj y b := by
        intro b hb hby
        simp only [Finset.mem_insert, Finset.mem_singleton] at hb
        rcases hb with rfl | rfl | rfl
        · exact hxy.symm
        · exact absurd rfl hby
        · exact hyz
      have adjZ : ∀ b ∈ ({x, y, z} : Finset (Fin 10)), b ≠ z → G.Adj z b := by
        intro b hb hbz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hb
        rcases hb with rfl | rfl | rfl
        · exact hxz.symm
        · exact hyz.symm
        · exact absurd rfl hbz
      have interX : (G.neighborFinset x ∩ ({x, y, z} : Finset (Fin 10))).card = 2 :=
        interCardEq x (by simp) adjX
      have interY : (G.neighborFinset y ∩ ({x, y, z} : Finset (Fin 10))).card = 2 :=
        interCardEq y (by simp) adjY
      have interZ : (G.neighborFinset z ∩ ({x, y, z} : Finset (Fin 10))).card = 2 :=
        interCardEq z (by simp) adjZ
      -- Hence each triangle vertex sends `deg − 2` edges out of the triangle.
      have sdX : (G.neighborFinset x \ ({x, y, z} : Finset (Fin 10))).card + 2 = G.degree x := by
        have h := Finset.card_sdiff_add_card_inter (G.neighborFinset x)
          ({x, y, z} : Finset (Fin 10))
        rw [interX, G.card_neighborFinset_eq_degree] at h
        exact h
      have sdY : (G.neighborFinset y \ ({x, y, z} : Finset (Fin 10))).card + 2 = G.degree y := by
        have h := Finset.card_sdiff_add_card_inter (G.neighborFinset y)
          ({x, y, z} : Finset (Fin 10))
        rw [interY, G.card_neighborFinset_eq_degree] at h
        exact h
      have sdZ : (G.neighborFinset z \ ({x, y, z} : Finset (Fin 10))).card + 2 = G.degree z := by
        have h := Finset.card_sdiff_add_card_inter (G.neighborFinset z)
          ({x, y, z} : Finset (Fin 10))
        rw [interZ, G.card_neighborFinset_eq_degree] at h
        exact h
      have cutEq : ∑ a ∈ ({x, y, z} : Finset (Fin 10)),
          (G.neighborFinset a \ ({x, y, z} : Finset (Fin 10))).card
          = (G.neighborFinset x \ ({x, y, z} : Finset (Fin 10))).card
            + (G.neighborFinset y \ ({x, y, z} : Finset (Fin 10))).card
            + (G.neighborFinset z \ ({x, y, z} : Finset (Fin 10))).card := by
        rw [Finset.sum_insert (by simp [hxy_ne, hxz_ne]),
            Finset.sum_insert (by simp [hyz_ne]), Finset.sum_singleton]
        ring
      have cutLe : ∑ a ∈ ({x, y, z} : Finset (Fin 10)),
          (G.neighborFinset a \ ({x, y, z} : Finset (Fin 10))).card ≤ 4 := by
        rw [cutEq]; omega
      refine algConn_le_two_of_weighted_cut G ({x, y, z} : Finset (Fin 10)) hA hAc ?_
      rw [hAcard, hAccard, Fintype.card_fin]
      omega
    · -- No-good-triangle sub-case: produce an induced `2K₂` on four degree-3 vertices and apply
      -- the certificate `algConn_le_two_of_ind_2K2`.
      -- OPEN (clean finite combinatorial fact, verified true on 12000+ graphs of each degree
      -- sequence [4,4,3⁸] and [5,3⁹]): a graph on `Fin 10` with min degree ≥ 3, 16 edges, and NO
      -- triangle of degree-sum ≤ 10 has an induced `2K₂` on four degree-3 vertices.
      have hex : ∃ a b c d : Fin 10, ({a, b, c, d} : Finset (Fin 10)).card = 4 ∧
          G.degree a = 3 ∧ G.degree b = 3 ∧ G.degree c = 3 ∧ G.degree d = 3 ∧
          G.Adj a b ∧ G.Adj c d ∧
          ¬ G.Adj a c ∧ ¬ G.Adj a d ∧ ¬ G.Adj b c ∧ ¬ G.Adj b d := by
        set D := Finset.univ.filter (fun v => G.degree v = 3) with hD
        set H := Finset.univ.filter (fun v => 4 ≤ G.degree v) with hH
        have hmemD : ∀ v : Fin 10, v ∈ D ↔ G.degree v = 3 := by
          intro v; rw [hD]; simp
        have hmemH : ∀ v : Fin 10, v ∈ H ↔ 4 ≤ G.degree v := by
          intro v; rw [hH]; simp
        have hDH : ∀ v : Fin 10, v ∈ D ∨ v ∈ H := by
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
        have hsumpart : ∑ v ∈ D, G.degree v + ∑ v ∈ H, G.degree v = 32 := by
          rw [← Finset.sum_union hdisj, hunion]; exact hsum
        have hsumD : ∑ v ∈ D, G.degree v = 3 * D.card := by
          rw [Finset.sum_congr rfl (fun v hv => (hmemD v).mp hv), Finset.sum_const,
            smul_eq_mul, mul_comm]
        have hsumH : H.card * 4 ≤ ∑ v ∈ H, G.degree v := by
          have hb : ∀ x ∈ H, 4 ≤ (fun v => G.degree v) x := fun i hi => (hmemH i).mp hi
          have h := Finset.card_nsmul_le_sum H (fun v => G.degree v) 4 hb
          simpa [smul_eq_mul] using h
        have hpart2 : D.card + H.card = 10 := by
          have h := Finset.card_union_of_disjoint hdisj
          rw [hunion, Finset.card_univ, Fintype.card_fin] at h
          omega
        rw [hsumD] at hsumpart
        have hHcard : H.card ≤ 2 := by omega
        have hDcard : 8 ≤ D.card := by omega
        have hmax : ∀ a ∈ D, (G.neighborFinset a ∩ D).card ≤ 3 := by
          intro a haD
          calc (G.neighborFinset a ∩ D).card
              ≤ (G.neighborFinset a).card := Finset.card_le_card Finset.inter_subset_left
            _ = G.degree a := G.card_neighborFinset_eq_degree a
            _ = 3 := (hmemD a).mp haD
        have hmin : ∀ a ∈ D, 1 ≤ (G.neighborFinset a ∩ D).card := by
          intro a haD
          have hcov : G.neighborFinset a ⊆
              (G.neighborFinset a ∩ D) ∪ (G.neighborFinset a ∩ H) := by
            intro w hw
            rcases hDH w with hwD | hwH
            · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hw, hwD⟩)
            · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hw, hwH⟩)
          have h1 := Finset.card_le_card hcov
          have h2 := Finset.card_union_le (G.neighborFinset a ∩ D) (G.neighborFinset a ∩ H)
          have h3' : (G.neighborFinset a ∩ H).card ≤ H.card :=
            Finset.card_le_card Finset.inter_subset_right
          rw [G.card_neighborFinset_eq_degree, (hmemD a).mp haD] at h1
          omega
        have htri : ∀ a ∈ D, ∀ b ∈ D, ∀ c ∈ D, ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj a c) := by
          rintro a haD b hbD c hcD ⟨hab, hbc, hac⟩
          refine hT ⟨a, b, c, G.ne_of_adj hab, G.ne_of_adj hbc, G.ne_of_adj hac,
            hab, hbc, hac, ?_⟩
          have da := (hmemD a).mp haD
          have db := (hmemD b).mp hbD
          have dc := (hmemD c).mp hcD
          omega
        obtain ⟨a, haD, b, hbD, c, hcD, d, hdD, hcard4, hab, hcd, hac, had, hbc, hbd⟩ :=
          exists_induced_2K2_of_triangleFree_smalldeg G D htri hmin hmax hDcard
        exact ⟨a, b, c, d, hcard4, (hmemD a).mp haD, (hmemD b).mp hbD, (hmemD c).mp hcD,
          (hmemD d).mp hdD, hab, hcd, hac, had, hbc, hbd⟩
      obtain ⟨a, b, c, d, hdist, hda, hdb, hdc, hdd, hab, hcd, hac, had, hbc, hbd⟩ := hex
      exact algConn_le_two_of_ind_2K2 G a b c d hdist hab hcd hac had hbc hbd (by omega)

/-- The full ACMAX conjecture for `n = 10` (`K_{2,8}` is the maximizer; bound `2`). -/
theorem acmax_conjecture_ten :
    algConn (completeBipartiteGraph (Fin 2) (Fin 8)) = 2 ∧
      ∀ G : SimpleGraph (Fin 10), G.edgeFinset.card = 16 → algConn G ≤ 2 :=
  ⟨algConn_completeBipartite_two 10 (by norm_num), fun G hm => upperBound_ten G hm⟩

end ACMax
