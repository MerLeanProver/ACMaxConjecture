import ACMaxConjecture.Base

/-!
# Inclusion–exclusion budget for the `n = 20` `P₄`-cherry `|D| = 10`-clean saturation kill

Pure `Finset` counting, no graph content.  Given two `≥ 6`-element avoider families
`A1, A2 ⊆ Dc` inside a `10`-element hub complement `Dc`, together with a `ℕ`-valued weight `f`
that is `≥ 2` on each avoider and `≥ 3` on their common part `FF = A1 ∩ A2`, and total weight
`∑_{g ∈ Dc} f g = 18`, inclusion–exclusion forces `A1 = A2 = FF`, `|FF| = 6`, and `f` to vanish
off `FF`.

Inclusion–exclusion gives `|A1 ∪ A2| = |A1| + |A2| − |FF|` and the weight lower bound
`18 ≥ ∑_{A1 ∪ A2} f ≥ 2·|A1 ∪ A2| + |FF| = |A1 ∪ A2| + (|A1| + |A2|) ≥ |A1 ∪ A2| + 12`, so
`|A1 ∪ A2| ≤ 6`; combined with `|A1 ∪ A2| ≥ |A1| ≥ 6` this pins `|A1 ∪ A2| = |A1| = |A2| = 6`,
hence `A1 = A2 = A1 ∪ A2 = FF` and `|FF| = 6`.  Finally `∑_{FF} f ≥ 3·6 = 18 = ∑_{Dc} f`, so `f`
is zero off `FF`.
-/

namespace ACMax

open scoped Classical

namespace N20

/-- **Saturation budget (`|D| = 10`-clean, `n = 20`).**  Two `≥ 6`-avoider families whose common
part carries weight `≥ 3` and whose total weight over `Dc` is `18` must coincide with their
`6`-element intersection, and the weight vanishes off that intersection.  (`Dc.card = 10` is not
needed for this pure-counting conclusion; it is retained for the caller's convenience.) -/
theorem d10_clean_nonff_isolated (Dc A1 A2 FF : Finset (Fin 20)) (f : Fin 20 → ℕ)
    (hA1sub : A1 ⊆ Dc) (hA2sub : A2 ⊆ Dc) (hFF : FF = A1 ∩ A2) (_hDc : Dc.card = 10)
    (hA1 : 6 ≤ A1.card) (hA2 : 6 ≤ A2.card) (h2 : ∀ g ∈ A1, 2 ≤ f g) (h2' : ∀ g ∈ A2, 2 ≤ f g)
    (h3 : ∀ g ∈ FF, 3 ≤ f g) (hsum : ∑ g ∈ Dc, f g = 18) :
    A1 = FF ∧ A2 = FF ∧ FF.card = 6 ∧ (∀ g ∈ Dc, g ∉ FF → f g = 0) := by
  classical
  have hFFsubA1 : FF ⊆ A1 := by rw [hFF]; exact Finset.inter_subset_left
  have hFFsubU : FF ⊆ A1 ∪ A2 := hFFsubA1.trans Finset.subset_union_left
  have hUsub : A1 ∪ A2 ⊆ Dc := Finset.union_subset hA1sub hA2sub
  have hincl : (A1 ∪ A2).card + FF.card = A1.card + A2.card := by
    have h := Finset.card_union_add_card_inter A1 A2
    rw [← hFF] at h; exact h
  have hpart : ((A1 ∪ A2) \ FF).card + FF.card = (A1 ∪ A2).card := by
    have h := Finset.card_sdiff_add_card_inter (A1 ∪ A2) FF
    rw [Finset.inter_eq_right.mpr hFFsubU] at h; exact h
  have hlbUFF : 2 * ((A1 ∪ A2) \ FF).card ≤ ∑ g ∈ (A1 ∪ A2) \ FF, f g := by
    have := Finset.card_nsmul_le_sum ((A1 ∪ A2) \ FF) f 2 (fun g hg => by
      rcases Finset.mem_union.mp (Finset.mem_sdiff.mp hg).1 with hgA | hgA
      · exact h2 g hgA
      · exact h2' g hgA)
    simpa [smul_eq_mul, Nat.mul_comm] using this
  have hlbFF : 3 * FF.card ≤ ∑ g ∈ FF, f g := by
    have := Finset.card_nsmul_le_sum FF f 3 h3
    simpa [smul_eq_mul, Nat.mul_comm] using this
  have hsplitU : (∑ g ∈ (A1 ∪ A2) \ FF, f g) + ∑ g ∈ FF, f g = ∑ g ∈ A1 ∪ A2, f g :=
    Finset.sum_sdiff hFFsubU
  have hsUle : ∑ g ∈ A1 ∪ A2, f g ≤ 18 := by
    rw [← hsum]; exact Finset.sum_le_sum_of_subset hUsub
  have hA1u : A1.card ≤ (A1 ∪ A2).card := Finset.card_le_card Finset.subset_union_left
  have hA2u : A2.card ≤ (A1 ∪ A2).card := Finset.card_le_card Finset.subset_union_right
  have hff6 : FF.card = 6 := by omega
  have hA1U : A1 = A1 ∪ A2 := Finset.eq_of_subset_of_card_le Finset.subset_union_left (by omega)
  have hA2U : A2 = A1 ∪ A2 := Finset.eq_of_subset_of_card_le Finset.subset_union_right (by omega)
  have hA1eqA2 : A1 = A2 := hA1U.trans hA2U.symm
  have hFFA1 : FF = A1 := by rw [hFF, ← hA1eqA2, Finset.inter_self]
  refine ⟨hFFA1.symm, hA1eqA2.symm.trans hFFA1.symm, hff6, ?_⟩
  have hffsubDc : FF ⊆ Dc := hFFsubA1.trans hA1sub
  have hsplit2 : (∑ g ∈ Dc \ FF, f g) + ∑ g ∈ FF, f g = ∑ g ∈ Dc, f g :=
    Finset.sum_sdiff hffsubDc
  have hFFge : 18 ≤ ∑ g ∈ FF, f g := by rw [hff6] at hlbFF; omega
  have hzero : ∑ g ∈ Dc \ FF, f g = 0 := by omega
  have hall := (Finset.sum_eq_zero_iff).mp hzero
  intro g hgDc hgFF
  exact hall g (Finset.mem_sdiff.mpr ⟨hgDc, hgFF⟩)

end N20

end ACMax
