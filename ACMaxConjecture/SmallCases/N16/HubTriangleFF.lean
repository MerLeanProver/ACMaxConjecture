import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N16.Core

/-!
# The `|FF| = 4` Mantel branch for the `n = 16` hub-triangle corner

When the fully-free hub set `FF` (degree-`4` hubs avoiding all four path vertices) has the maximal
size `4`, an edge count forces `e(FF) ≥ 5` among its four vertices: each fully-free hub has
hub-internal degree `≥ 3`, so `∑_{FF} int ≥ 12`, while at most `14 − 12 = 2` of the hub-internal
degree can leak out of `FF`, leaving `2·e(FF) = ∑_{FF}(N ∩ FF) ≥ 10`.  A four-vertex graph with
`≥ 5` edges (equivalently two vertices each adjacent to the other three) contains a triangle
(Mantel), giving three pairwise-adjacent fully-free hubs.
-/

namespace ACMax

open scoped Classical

namespace N16

/-- **A triangle among four high-internal-degree fully-free hubs.**  If `FF ⊆ Dᶜ` has exactly four
vertices, each of hub-internal degree `≥ 3`, and the hub-internal-degree total is `14`, then three
of the four are pairwise adjacent. -/
theorem ff_four_triangle (G : SimpleGraph (Fin 16)) (Dc FF : Finset (Fin 16))
    (hFFsub : FF ⊆ Dc) (hFFcard : FF.card = 4)
    (hFFint : ∀ g ∈ FF, 3 ≤ (G.neighborFinset g ∩ Dc).card)
    (hSum14 : ∑ w ∈ Dc, (G.neighborFinset w ∩ Dc).card = 14) :
    ∃ a b c : Fin 16, a ∈ FF ∧ b ∈ FF ∧ c ∈ FF ∧
      G.Adj a b ∧ G.Adj a c ∧ G.Adj b c := by
  classical
  -- per-hub split `int(g) = (N g ∩ FF) + (N g ∩ (Dᶜ \ FF))`.
  have hsplit : ∀ g : Fin 16, (G.neighborFinset g ∩ Dc).card
      = (G.neighborFinset g ∩ FF).card + (G.neighborFinset g ∩ (Dc \ FF)).card := by
    intro g
    rw [← Finset.card_union_of_disjoint, ← Finset.inter_union_distrib_left,
      Finset.union_sdiff_of_subset hFFsub]
    apply Finset.disjoint_left.mpr
    intro a ha ha'
    rw [Finset.mem_inter] at ha ha'
    exact (Finset.mem_sdiff.mp ha'.2).2 ha.2
  -- `∑_{FF} int ≥ 12`.
  have hFFsum_ge : 12 ≤ ∑ g ∈ FF, (G.neighborFinset g ∩ Dc).card := by
    have := Finset.card_nsmul_le_sum FF (fun g => (G.neighborFinset g ∩ Dc).card) 3 hFFint
    rw [hFFcard, smul_eq_mul] at this; omega
  -- `∑_{Dᶜ\FF} int = 14 − ∑_{FF} int ≤ 2`.
  have hsdiff : (∑ w ∈ Dc \ FF, (G.neighborFinset w ∩ Dc).card)
      + ∑ g ∈ FF, (G.neighborFinset g ∩ Dc).card = 14 := by
    rw [Finset.sum_sdiff hFFsub, hSum14]
  -- leak out of `FF` is `≤ 2` via the cross count.
  have hcross : ∑ g ∈ FF, (G.neighborFinset g ∩ (Dc \ FF)).card
      = ∑ w ∈ Dc \ FF, (G.neighborFinset w ∩ FF).card :=
    cross_count G FF (Dc \ FF)
  have hleak_le : ∑ w ∈ Dc \ FF, (G.neighborFinset w ∩ FF).card
      ≤ ∑ w ∈ Dc \ FF, (G.neighborFinset w ∩ Dc).card := by
    apply Finset.sum_le_sum
    intro w _
    exact Finset.card_le_card (Finset.inter_subset_inter (Finset.Subset.refl _) hFFsub)
  -- `∑_{FF}(N ∩ FF) ≥ 10`.
  have hFFFFsum : (∑ g ∈ FF, (G.neighborFinset g ∩ FF).card)
      + ∑ g ∈ FF, (G.neighborFinset g ∩ (Dc \ FF)).card
      = ∑ g ∈ FF, (G.neighborFinset g ∩ Dc).card := by
    rw [← Finset.sum_add_distrib]
    exact (Finset.sum_congr rfl (fun g _ => (hsplit g).symm))
  have hint_ge10 : 10 ≤ ∑ g ∈ FF, (G.neighborFinset g ∩ FF).card := by omega
  -- each internal degree is `≤ 3`.
  have hdle3 : ∀ g ∈ FF, (G.neighborFinset g ∩ FF).card ≤ 3 := by
    intro g hg
    have hsubg : G.neighborFinset g ∩ FF ⊆ FF.erase g := by
      intro x hx
      rw [Finset.mem_inter, G.mem_neighborFinset] at hx
      exact Finset.mem_erase.mpr ⟨fun e => G.irrefl (e ▸ hx.1), hx.2⟩
    have := Finset.card_le_card hsubg
    rw [Finset.card_erase_of_mem hg, hFFcard] at this; omega
  -- at least two hubs are adjacent to the other three.
  set FF3 := FF.filter (fun g => (G.neighborFinset g ∩ FF).card = 3) with hFF3def
  have hpart := Finset.sum_filter_add_sum_filter_not FF
    (fun g => (G.neighborFinset g ∩ FF).card = 3) (fun g => (G.neighborFinset g ∩ FF).card)
  have hpos : ∑ g ∈ FF3, (G.neighborFinset g ∩ FF).card = 3 * FF3.card := by
    rw [hFF3def, Finset.sum_congr rfl]
    · rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
    · intro g hg; exact (Finset.mem_filter.mp hg).2
  have hneg : ∑ g ∈ FF.filter (fun g => ¬(G.neighborFinset g ∩ FF).card = 3),
      (G.neighborFinset g ∩ FF).card
      ≤ 2 * (FF.filter (fun g => ¬(G.neighborFinset g ∩ FF).card = 3)).card := by
    rw [Nat.mul_comm]
    apply Finset.sum_le_card_nsmul
    intro g hg
    rw [Finset.mem_filter] at hg
    have := hdle3 g hg.1
    omega
  have hcardsum : FF3.card
      + (FF.filter (fun g => ¬(G.neighborFinset g ∩ FF).card = 3)).card = 4 := by
    rw [hFF3def, Finset.card_filter_add_card_filter_not, hFFcard]
  have hFF3ge2 : 2 ≤ FF3.card := by
    rw [hFF3def] at hpos hcardsum ⊢
    omega
  -- extract two distinct full-degree hubs and a third hub.
  obtain ⟨g, hg, a, ha, hga⟩ := Finset.one_lt_card.mp (by omega : 1 < FF3.card)
  have hgFF : g ∈ FF := (Finset.mem_filter.mp hg).1
  have haFF : a ∈ FF := (Finset.mem_filter.mp ha).1
  have hg3 : (G.neighborFinset g ∩ FF).card = 3 := (Finset.mem_filter.mp hg).2
  have ha3 : (G.neighborFinset a ∩ FF).card = 3 := (Finset.mem_filter.mp ha).2
  -- `N g ∩ FF = FF.erase g`, and likewise for `a`.
  have hgerase : G.neighborFinset g ∩ FF = FF.erase g := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      rw [Finset.mem_inter, G.mem_neighborFinset] at hx
      exact Finset.mem_erase.mpr ⟨fun e => G.irrefl (e ▸ hx.1), hx.2⟩
    · rw [Finset.card_erase_of_mem hgFF, hFFcard, hg3]
  have haerase : G.neighborFinset a ∩ FF = FF.erase a := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      rw [Finset.mem_inter, G.mem_neighborFinset] at hx
      exact Finset.mem_erase.mpr ⟨fun e => G.irrefl (e ▸ hx.1), hx.2⟩
    · rw [Finset.card_erase_of_mem haFF, hFFcard, ha3]
  -- a third hub `b ∈ FF \ {g, a}`.
  have hpaircard : ({g, a} : Finset (Fin 16)).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simp [hga]), Finset.card_singleton]
  have hexb : ∃ b : Fin 16, b ∈ FF ∧ b ∉ ({g, a} : Finset (Fin 16)) := by
    by_contra hcon
    push Not at hcon
    have : FF ⊆ ({g, a} : Finset (Fin 16)) := fun b hb => hcon b hb
    have := Finset.card_le_card this
    rw [hFFcard, hpaircard] at this; omega
  obtain ⟨b, hbFF, hbpair⟩ := hexb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hbpair
  push Not at hbpair
  obtain ⟨hbg, hba⟩ := hbpair
  -- adjacencies from the erased-neighbourhood descriptions.
  have hadj_ga : G.Adj g a := by
    have : a ∈ G.neighborFinset g ∩ FF := by rw [hgerase]; exact Finset.mem_erase.mpr ⟨hga.symm, haFF⟩
    rw [Finset.mem_inter, G.mem_neighborFinset] at this; exact this.1
  have hadj_gb : G.Adj g b := by
    have : b ∈ G.neighborFinset g ∩ FF := by rw [hgerase]; exact Finset.mem_erase.mpr ⟨hbg, hbFF⟩
    rw [Finset.mem_inter, G.mem_neighborFinset] at this; exact this.1
  have hadj_ab : G.Adj a b := by
    have : b ∈ G.neighborFinset a ∩ FF := by rw [haerase]; exact Finset.mem_erase.mpr ⟨hba, hbFF⟩
    rw [Finset.mem_inter, G.mem_neighborFinset] at this; exact this.1
  exact ⟨g, a, b, hgFF, haFF, hbFF, hadj_ga, hadj_gb, hadj_ab⟩

end N16

end ACMax
