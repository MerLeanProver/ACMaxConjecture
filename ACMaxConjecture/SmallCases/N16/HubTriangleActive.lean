import ACMaxConjecture.Base

/-!
# Active-hub budget for the `n = 16`, `e(M) = 3`, `|D| = 8` hub-triangle corner

This file isolates the *pure counting* step new to `n = 16`: against the hub-internal-degree
total `∑ int = 14` (vs `10` for `n = 15`), the fully-free hub count `|FF|` is pinned to
`{2, 3, 4}`.  `A1`, `A2` are the two cherry-avoider sets (`≥ 4` each), `FF = A1 ∩ A2` the
fully-free hubs; avoider internal degree is `≥ 2`, fully-free internal degree is `≥ 3`.  An
inclusion–exclusion over `A1 ∪ A2 ⊆ Dᶜ` gives `2|A1| + 2|A2| − |FF| ≤ 14`, hence `|FF| ≥ 2`, while
`3|FF| ≤ ∑_{Dᶜ} int = 14` gives `|FF| ≤ 4`.
-/

namespace ACMax

open scoped Classical

namespace N16

/-- **Fully-free hub budget.**  With avoider internal degree `≥ 2` (`hA1int`, `hA2int`), fully-free
internal degree `≥ 3` (`hFFint`), `|A1|, |A2| ≥ 4`, `FF = A1 ∩ A2`, and the hub-internal-degree
total `∑_{Dᶜ} f = 14`, the fully-free count lies in `{2, 3, 4}`. -/
theorem active_hub_budget_sixteen (Dc A1 A2 FF : Finset (Fin 16)) (f : Fin 16 → ℕ)
    (hA1sub : A1 ⊆ Dc) (hA2sub : A2 ⊆ Dc) (hFF : FF = A1 ∩ A2)
    (hA1card : 4 ≤ A1.card) (hA2card : 4 ≤ A2.card)
    (hA1int : ∀ g ∈ A1, 2 ≤ f g) (hA2int : ∀ g ∈ A2, 2 ≤ f g)
    (hFFint : ∀ g ∈ FF, 3 ≤ f g) (hSum14 : ∑ w ∈ Dc, f w = 14) :
    2 ≤ FF.card ∧ FF.card ≤ 4 := by
  classical
  have hFFsubA1 : FF ⊆ A1 := by rw [hFF]; exact Finset.inter_subset_left
  have hFFsubA2 : FF ⊆ A2 := by rw [hFF]; exact Finset.inter_subset_right
  have hFFsub : FF ⊆ Dc := hFFsubA1.trans hA1sub
  -- `|FF| ≤ 4`: `3|FF| ≤ ∑_{FF} f ≤ ∑_{Dᶜ} f = 14`.
  have hFFsum_le : ∑ g ∈ FF, f g ≤ 14 := by
    rw [← hSum14]
    exact Finset.sum_le_sum_of_subset_of_nonneg hFFsub (fun _ _ _ => Nat.zero_le _)
  have hFFsum_ge3 : 3 * FF.card ≤ ∑ g ∈ FF, f g := by
    have := Finset.card_nsmul_le_sum FF f 3 hFFint
    simpa [smul_eq_mul, Nat.mul_comm] using this
  have hle4 : FF.card ≤ 4 := by omega
  -- `|FF| ≥ 2`: inclusion–exclusion over `A1 ⊔ (A2 \ A1) = A1 ∪ A2 ⊆ Dᶜ`.
  refine ⟨?_, hle4⟩
  have hUsub : A1 ∪ A2 ⊆ Dc := Finset.union_subset hA1sub hA2sub
  have hUsum_le : ∑ g ∈ A1 ∪ A2, f g ≤ 14 := by
    rw [← hSum14]
    exact Finset.sum_le_sum_of_subset_of_nonneg hUsub (fun _ _ _ => Nat.zero_le _)
  -- split the union sum: `∑_{A1∪A2} = ∑_{A1} + ∑_{A2\A1}`.
  have hdisj : Disjoint A1 (A2 \ A1) := Finset.disjoint_sdiff
  have hunion_eq : A1 ∪ (A2 \ A1) = A1 ∪ A2 := by
    rw [Finset.union_sdiff_self_eq_union]
  have hUsplit : ∑ g ∈ A1 ∪ A2, f g = (∑ g ∈ A1, f g) + ∑ g ∈ A2 \ A1, f g := by
    rw [← hunion_eq, Finset.sum_union hdisj]
  -- `∑_{A1} f = ∑_{A1\FF} f + ∑_{FF} f ≥ 2(|A1|-|FF|) + 3|FF|`.
  have hA1split : (∑ g ∈ A1 \ FF, f g) + ∑ g ∈ FF, f g = ∑ g ∈ A1, f g :=
    Finset.sum_sdiff hFFsubA1
  have hA1FFinter : (A1 ∩ FF).card = FF.card := by
    rw [Finset.inter_eq_right.mpr hFFsubA1]
  have hA1mfcard : (A1 \ FF).card + FF.card = A1.card := by
    rw [← hA1FFinter]; exact Finset.card_sdiff_add_card_inter A1 FF
  have hA1mf_ge : 2 * (A1 \ FF).card ≤ ∑ g ∈ A1 \ FF, f g := by
    have := Finset.card_nsmul_le_sum (A1 \ FF) f 2
      (fun g hg => hA1int g ((Finset.mem_sdiff.mp hg).1))
    simpa [smul_eq_mul, Nat.mul_comm] using this
  -- `∑_{A2\A1} f ≥ 2|A2\A1|`, with `|A2\A1| = |A2| - |FF|`.
  have hA2A1FF : (A2 ∩ A1).card = FF.card := by rw [hFF, Finset.inter_comm]
  have hA2mA1 : (A2 \ A1).card + FF.card = A2.card := by
    rw [← hA2A1FF]; exact Finset.card_sdiff_add_card_inter A2 A1
  have hA2mA1_ge : 2 * (A2 \ A1).card ≤ ∑ g ∈ A2 \ A1, f g := by
    have := Finset.card_nsmul_le_sum (A2 \ A1) f 2
      (fun g hg => hA2int g ((Finset.mem_sdiff.mp hg).1))
    simpa [smul_eq_mul, Nat.mul_comm] using this
  -- combine: `16 - |FF| ≤ ∑_{A1∪A2} f ≤ 14`.
  have hFFleA1 : FF.card ≤ A1.card := Finset.card_le_card hFFsubA1
  omega

end N16

end ACMax
