import ACMaxConjecture.Base
import ACMaxConjecture.Spectral.AlgConn
import ACMaxConjecture.Cuts.LowDegreeVertex
import ACMaxConjecture.Cuts.WeightedCut
import ACMaxConjecture.Cuts.Ind2K2
import ACMaxConjecture.Cuts.TriangleFree2K2
import ACMaxConjecture.Cuts.Disconnected
import ACMaxConjecture.Cuts.GoodC4
import ACMaxConjecture.Cuts.GoodK23
import ACMaxConjecture.Cuts.SignedCut

/-!
# The common dispatcher for the finite cases

For every order in the finite range, the proof before the final structural
certificate is identical.  This module records that argument once.  Its only
inputs are the three degree-sum thresholds and a function producing a signed
cut in the residual case.
-/

namespace ACMax

open scoped Classical

/-- A triangle whose degree sum is small enough for the selected finite case. -/
def HasSparseTriangle {V : Type*} [Fintype V] (G : SimpleGraph V) (bound : ℕ) : Prop :=
  ∃ x y z : V, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
    G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧
    G.degree x + G.degree y + G.degree z ≤ bound

/-- An induced `2K₂` all of whose vertices have degree three. -/
def HasDegreeThree2K2 {V : Type*} [Fintype V] (G : SimpleGraph V) : Prop :=
  ∃ a b c d : V, ({a, b, c, d} : Finset V).card = 4 ∧
    G.degree a = 3 ∧ G.degree b = 3 ∧ G.degree c = 3 ∧ G.degree d = 3 ∧
    G.Adj a b ∧ G.Adj c d ∧
    ¬G.Adj a c ∧ ¬G.Adj a d ∧ ¬G.Adj b c ∧ ¬G.Adj b d

/-- An induced `C₄` whose degree sum is small enough for the selected case. -/
def HasSparseC4 {V : Type*} [Fintype V] (G : SimpleGraph V) (bound : ℕ) : Prop :=
  ∃ a b c d : V, ({a, b, c, d} : Finset V).card = 4 ∧
    G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧
    ¬G.Adj a c ∧ ¬G.Adj b d ∧
    G.degree a + G.degree b + G.degree c + G.degree d ≤ bound

/-- An induced `K₂,₃` whose degree sum is small enough for the selected case. -/
def HasSparseK23 {V : Type*} [Fintype V] (G : SimpleGraph V) (bound : ℕ) : Prop :=
  ∃ a b c d e : V, ({a, b, c, d, e} : Finset V).card = 5 ∧
    G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧
    G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
    ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
    G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ bound

/-- A degree-three vertex with no degree-three neighbor. -/
def HasIsolatedDegreeThree {V : Type*} [Fintype V] (G : SimpleGraph V) : Prop :=
  ∃ t : V, G.degree t = 3 ∧ ∀ w : V, G.Adj t w → G.degree w ≠ 3

/-- The three-valued certificate used to finish every residual case. -/
def HasSignedCut {V : Type*} [Fintype V] (G : SimpleGraph V) : Prop :=
  ∃ P N : Finset V, Disjoint P N ∧ P.card = N.card ∧ 0 < P.card ∧
    4 * (∑ p ∈ P, (G.neighborFinset p ∩ N).card)
      + (∑ p ∈ P, (G.neighborFinset p \ (P ∪ N)).card)
      + (∑ q ∈ N, (G.neighborFinset q \ (P ∪ N)).card)
    ≤ 4 * P.card

/-- Common proof for orders `n ≥ 8`.

The first three arithmetic hypotheses say that the selected triangle, `C₄`,
and `K₂,₃` thresholds really imply the corresponding weighted-cut inequality.
Only `residual` contains order-specific graph structure.  Its conclusion is
the spectral bound itself, so it may use a signed cut or any stronger
case-specific certificate. -/
theorem upperBound_of_residual_signed_cut
    (n triangleMax c4Max k23Max : ℕ)
    [Nonempty (Fin n)]
    (hn : 8 ≤ n)
    (htriangleMin : 9 ≤ triangleMax)
    (htriangle : n * (triangleMax - 6) ≤ 2 * (3 * (n - 3)))
    (hc4 : n * (c4Max - 8) ≤ 2 * (4 * (n - 4)))
    (hk23 : n * (k23Max - 12) ≤ 2 * (5 * (n - 5)))
    (G : SimpleGraph (Fin n)) (hm : G.edgeFinset.card = 2 * (n - 2))
    (residual : (∀ v, 3 ≤ G.degree v) →
      ¬HasSparseTriangle G triangleMax →
      ¬HasDegreeThree2K2 G →
      ¬HasSparseC4 G c4Max →
      ¬HasSparseK23 G k23Max →
      HasIsolatedDegreeThree G →
      algConn G ≤ 2) :
    algConn G ≤ 2 := by
  rcases Classical.em (∃ v : Fin n, G.degree v ≤ 2) with hlow | hlow
  · -- `δ ≤ 2`: a low-degree vertex gives the test vector `|T|·e_u − 𝟙_T`.
    let : DecidableEq (Fin n) := fun a b => Classical.propDecidable (a = b)
    obtain ⟨u, hdeg⟩ := hlow
    refine algConn_le_two_of_low_degree_vertex G u hdeg ?_
    rw [← Finset.card_pos, Finset.card_sdiff, Finset.inter_univ]
    have hcard : (insert u (G.neighborFinset u)).card ≤ 3 := by
      calc (insert u (G.neighborFinset u)).card
          ≤ (G.neighborFinset u).card + 1 := Finset.card_insert_le _ _
        _ = G.degree u + 1 := by rw [SimpleGraph.card_neighborFinset_eq_degree]
        _ ≤ 3 := by omega
    have huniv : (Finset.univ : Finset (Fin n)).card = n := by simp
    omega
  · -- `δ ≥ 3`: every degree is `≥ 3`.  Split on whether `G` has a degree-sparse triangle.
    let : DecidableEq (Fin n) := fun a b => Classical.propDecidable (a = b)
    simp only [not_exists, not_le] at hlow
    have h3 : ∀ v : Fin n, 3 ≤ G.degree v := fun v => by have := hlow v; omega
    have hsum : ∑ v : Fin n, G.degree v = 2 * (2 * (n - 2)) := by
      rw [SimpleGraph.sum_degrees_eq_twice_card_edges, hm]
    by_cases hT : HasSparseTriangle G triangleMax
    · -- Good-triangle sub-case: the closed triangle `{x,y,z}` is a sparse weighted cut.
      obtain ⟨x, y, z, hxy_ne, hyz_ne, hxz_ne, hxy, hyz, hxz, hdsum⟩ := hT
      have hAcard : ({x, y, z} : Finset (Fin n)).card = 3 := by
        rw [Finset.card_insert_of_notMem (by simp [hxy_ne, hxz_ne]),
            Finset.card_insert_of_notMem (by simp [hyz_ne]), Finset.card_singleton]
      have hAccard : (({x, y, z} : Finset (Fin n))ᶜ).card = n - 3 := by
        rw [Finset.card_compl, hAcard, Fintype.card_fin]
      have hA : ({x, y, z} : Finset (Fin n)).Nonempty := ⟨x, by simp⟩
      have hAc : (({x, y, z} : Finset (Fin n))ᶜ).Nonempty :=
        Finset.card_pos.mp (by rw [hAccard]; omega)
      -- Each vertex of the triangle meets the triangle in exactly its two partners.
      have triErase : ∀ a : Fin n, a ∈ ({x, y, z} : Finset (Fin n)) →
          (∀ b ∈ ({x, y, z} : Finset (Fin n)), b ≠ a → G.Adj a b) →
          G.neighborFinset a ∩ ({x, y, z} : Finset (Fin n))
            = ({x, y, z} : Finset (Fin n)).erase a := by
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
      have interCardEq : ∀ a : Fin n, a ∈ ({x, y, z} : Finset (Fin n)) →
          (∀ b ∈ ({x, y, z} : Finset (Fin n)), b ≠ a → G.Adj a b) →
          (G.neighborFinset a ∩ ({x, y, z} : Finset (Fin n))).card = 2 := by
        intro a ha hadj
        rw [triErase a ha hadj, Finset.card_erase_of_mem ha, hAcard]
      have adjX : ∀ b ∈ ({x, y, z} : Finset (Fin n)), b ≠ x → G.Adj x b := by
        intro b hb hbx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hb
        rcases hb with rfl | rfl | rfl
        · exact absurd rfl hbx
        · exact hxy
        · exact hxz
      have adjY : ∀ b ∈ ({x, y, z} : Finset (Fin n)), b ≠ y → G.Adj y b := by
        intro b hb hby
        simp only [Finset.mem_insert, Finset.mem_singleton] at hb
        rcases hb with rfl | rfl | rfl
        · exact hxy.symm
        · exact absurd rfl hby
        · exact hyz
      have adjZ : ∀ b ∈ ({x, y, z} : Finset (Fin n)), b ≠ z → G.Adj z b := by
        intro b hb hbz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hb
        rcases hb with rfl | rfl | rfl
        · exact hxz.symm
        · exact hyz.symm
        · exact absurd rfl hbz
      have interX : (G.neighborFinset x ∩ ({x, y, z} : Finset (Fin n))).card = 2 :=
        interCardEq x (by simp) adjX
      have interY : (G.neighborFinset y ∩ ({x, y, z} : Finset (Fin n))).card = 2 :=
        interCardEq y (by simp) adjY
      have interZ : (G.neighborFinset z ∩ ({x, y, z} : Finset (Fin n))).card = 2 :=
        interCardEq z (by simp) adjZ
      -- Hence each triangle vertex sends `deg − 2` edges out of the triangle.
      have sdX : (G.neighborFinset x \ ({x, y, z} : Finset (Fin n))).card + 2 = G.degree x := by
        have h := Finset.card_sdiff_add_card_inter (G.neighborFinset x)
          ({x, y, z} : Finset (Fin n))
        rw [interX, G.card_neighborFinset_eq_degree] at h
        exact h
      have sdY : (G.neighborFinset y \ ({x, y, z} : Finset (Fin n))).card + 2 = G.degree y := by
        have h := Finset.card_sdiff_add_card_inter (G.neighborFinset y)
          ({x, y, z} : Finset (Fin n))
        rw [interY, G.card_neighborFinset_eq_degree] at h
        exact h
      have sdZ : (G.neighborFinset z \ ({x, y, z} : Finset (Fin n))).card + 2 = G.degree z := by
        have h := Finset.card_sdiff_add_card_inter (G.neighborFinset z)
          ({x, y, z} : Finset (Fin n))
        rw [interZ, G.card_neighborFinset_eq_degree] at h
        exact h
      have cutEq : ∑ a ∈ ({x, y, z} : Finset (Fin n)),
          (G.neighborFinset a \ ({x, y, z} : Finset (Fin n))).card
          = (G.neighborFinset x \ ({x, y, z} : Finset (Fin n))).card
            + (G.neighborFinset y \ ({x, y, z} : Finset (Fin n))).card
            + (G.neighborFinset z \ ({x, y, z} : Finset (Fin n))).card := by
        rw [Finset.sum_insert (by simp [hxy_ne, hxz_ne]),
            Finset.sum_insert (by simp [hyz_ne]), Finset.sum_singleton]
        ring
      have cutLe : ∑ a ∈ ({x, y, z} : Finset (Fin n)),
          (G.neighborFinset a \ ({x, y, z} : Finset (Fin n))).card ≤ triangleMax - 6 := by
        rw [cutEq]; omega
      refine algConn_le_two_of_weighted_cut G ({x, y, z} : Finset (Fin n)) hA hAc ?_
      rw [hAcard, hAccard, Fintype.card_fin]
      exact (Nat.mul_le_mul_left n cutLe).trans htriangle
    · -- No-good-triangle sub-case: the degree-3 vertices form `D`, with `|D| ≥ 8`.
      set D := Finset.univ.filter (fun v => G.degree v = 3) with hD
      set H := Finset.univ.filter (fun v => 4 ≤ G.degree v) with hH
      have hmemD : ∀ v : Fin n, v ∈ D ↔ G.degree v = 3 := by
        intro v; rw [hD]; simp
      have hmemH : ∀ v : Fin n, v ∈ H ↔ 4 ≤ G.degree v := by
        intro v; rw [hH]; simp
      have hDH : ∀ v : Fin n, v ∈ D ∨ v ∈ H := by
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
      have hsumpart : ∑ v ∈ D, G.degree v + ∑ v ∈ H, G.degree v = 2 * (2 * (n - 2)) := by
        rw [← Finset.sum_union hdisj, hunion]; exact hsum
      have hsumD : ∑ v ∈ D, G.degree v = 3 * D.card := by
        rw [Finset.sum_congr rfl (fun v hv => (hmemD v).mp hv), Finset.sum_const,
          smul_eq_mul, mul_comm]
      have hsumH : H.card * 4 ≤ ∑ v ∈ H, G.degree v := by
        have hb : ∀ x ∈ H, 4 ≤ (fun v => G.degree v) x := fun i hi => (hmemH i).mp hi
        have h := Finset.card_nsmul_le_sum H (fun v => G.degree v) 4 hb
        simpa [smul_eq_mul] using h
      have hpart2 : D.card + H.card = n := by
        have h := Finset.card_union_of_disjoint hdisj
        rw [hunion, Finset.card_univ, Fintype.card_fin] at h
        omega
      rw [hsumD] at hsumpart
      have htotal : 2 * (2 * (n - 2)) + 8 = 4 * n := by omega
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
      · -- Residual: a no-good-triangle graph with an ISOLATED degree-3 vertex.
        by_cases hconn : G.Connected
        · -- CONNECTED residual.  Split on the existence of an induced `2K₂` on degree-3 vertices.
          by_cases h2k2 : HasDegreeThree2K2 G
          · -- An induced `2K₂` on degree-3 vertices exists.
            obtain ⟨a, b, c, d, hcard4, hda, hdb, hdc, hdd, hab, hcd, hac, had, hbc, hbd⟩ := h2k2
            exact algConn_le_two_of_ind_2K2 G a b c d hcard4 hab hcd hac had hbc hbd (by omega)
          · -- No induced `2K₂` on degree-3 vertices.  Split on the existence of a good `C₄`.
            by_cases hC4 : HasSparseC4 G c4Max
            · -- A "good C₄" (induced 4-cycle, degree-sum ≤ c4Max) is a sparse weighted cut.
              obtain ⟨a, b, c, d, hcard4, hab, hbc, hcd, hda, hac, hbd, hdeg⟩ := hC4
              refine algConn_le_two_of_good_C4 G a b c d ?_
                (by simp only [Fintype.card_fin]; omega) hab hbc hcd hda hac
                hbd ?_
              · convert hcard4
              · rw [Fintype.card_fin]
                exact (Nat.mul_le_mul_left n (Nat.sub_le_sub_right hdeg 8)).trans hc4
            · -- No good `C₄`.  Split on the existence of a good `K_{2,3}`.
              by_cases hK23 : HasSparseK23 G k23Max
              · -- A good `K_{2,3}` (induced, degree-sum ≤ k23Max) is a sparse weighted cut.
                obtain ⟨a, b, c, d, e, hcard5, hac, had, hae, hbc, hbd, hbe, hab, hcd, hce, hde,
                  hdeg⟩ := hK23
                refine algConn_le_two_of_good_K23 G a b c d e ?_
                  (by simp only [Fintype.card_fin]; omega) hac had hae hbc hbd
                  hbe hab hcd hce hde ?_
                · convert hcard5
                · rw [Fintype.card_fin]
                  exact (Nat.mul_le_mul_left n (Nat.sub_le_sub_right hdeg 12)).trans hk23
              · -- No sparse standard cut remains.  Isolate the degree-three
                -- vertex promised by `¬hmin` and invoke the order-specific hook.
                have hiso : HasIsolatedDegreeThree G := by
                  rw [not_forall] at hmin
                  obtain ⟨a, ha⟩ := hmin
                  rw [Classical.not_imp, not_le] at ha
                  obtain ⟨haD, hlt⟩ := ha
                  refine ⟨a, (hmemD a).mp haD, ?_⟩
                  intro w hadj hw
                  have hwmem : w ∈ G.neighborFinset a ∩ D := by
                    rw [Finset.mem_inter, G.mem_neighborFinset]
                    exact ⟨hadj, (hmemD w).mpr hw⟩
                  have hpos : 0 < (G.neighborFinset a ∩ D).card :=
                    Finset.card_pos.mpr ⟨w, hwmem⟩
                  omega
                exact residual h3 hT h2k2 hC4 hK23 hiso
        · -- DISCONNECTED residual: uniformly handled by the separated-cut lemma.
          exact algConn_le_two_of_not_connected G hconn

end ACMax
