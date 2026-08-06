import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.Certificates
import ACMaxConjecture.SmallCases.N18.Core
import ACMaxConjecture.SmallCases.N18.HubTriangleFF
import ACMaxConjecture.SmallCases.N18.CherryP4HubTriangleWA
import ACMaxConjecture.SmallCases.N18.CherryP4HubTriangleForceD9FF4

/-!
# `|FF|`-style force for the `n = 18`, `P₄`-cherry `|D| ∈ {9, 10, 11}` hub-triangle core

`iso_rich_force_p4_eighteen` is the `|D| ∈ {9, 10, 11}` analog of `iso_rich_force_p4_seventeen`:
under the residual structural counts and the falsity of `TwoTwinConfig`, the assumption that
neither cherry admits a pairwise-adjacent avoider triple of degree sum `≤ 13` (`hntri1`, `hntri2`)
is contradictory.  The three `|D|` values are dispatched separately.

The `n = 18` internal total is `∑ int = 70 − 6|D|` (`16`/`10`/`4` for `|D| = 9`/`10`/`11`), the hub
degree total is `∑ deg = 64 − 3|D|` (`37`/`34`/`31`).

* `|D| = 11` (`7` hubs, `∑ int = 4`, avoiders `≥ 3`): clean counting.  The lone degree-`≥ 6` hub
  costs at most `3` against the ideal budget `3m = 9`, still `> 4`.
* `|D| = 10` (`8` hubs, `∑ int = 10`, avoiders `≥ 4`): clean when all hubs have degree `≤ 5`
  (`3m = 12 > 10`).  The lone degree-`6` hub `h6`: if it lies outside one avoider set, the budget
  forces `|FF| ≥ 4`, so `∑_FF int ≥ 12 > 10`; if `h6 ∈ FF` (fully free), `int h6 ≤ 1` collapses the
  fully-free hubs `FF ∖ {h6}` into a Mantel/edge triangle of degree sum `≤ 13`, contradicting a
  cherry no-triangle hypothesis.
* `|D| = 9` (`9` hubs, `∑ int = 16`, avoiders `≥ 5`, all degree `≤ 5`): the budget forces
  `|A₁| = |A₂| = 5` and `|FF| ∈ {4, 5}`.  `|FF| = 5` Mantel-`5`-forces a triangle; `|FF| = 4` is the
  `K_{3,3}`-minus-matching bipartite-escape corner (documented `sorry`).
-/

namespace ACMax

open scoped Classical

namespace N18

/-- **Mantel triangle on three vertices.**  A `3`-vertex set with in-set edge mass
`∑(N ∩ S) ≥ 6` is a triangle (each vertex must be adjacent to the other two). -/
theorem mantel_three_triangle (G : SimpleGraph (Fin 18)) (S : Finset (Fin 18))
    (hcard : S.card = 3) (hedge : 6 ≤ ∑ g ∈ S, (G.neighborFinset g ∩ S).card) :
    ∃ a b c : Fin 18, a ∈ S ∧ b ∈ S ∧ c ∈ S ∧ G.Adj a b ∧ G.Adj a c ∧ G.Adj b c := by
  classical
  obtain ⟨a, b, c, hab, hac, hbc, hSeq⟩ := Finset.card_eq_three.mp hcard
  have haS : a ∈ S := by rw [hSeq]; simp
  have hbS : b ∈ S := by rw [hSeq]; simp
  have hcS : c ∈ S := by rw [hSeq]; simp
  have hbound : ∀ g : Fin 18, g ∈ S → G.neighborFinset g ∩ S ⊆ S.erase g := by
    intro g _ x hx
    rw [Finset.mem_inter, G.mem_neighborFinset] at hx
    exact Finset.mem_erase.mpr ⟨fun e => G.irrefl (e ▸ hx.1), hx.2⟩
  have hbcard : ∀ g : Fin 18, g ∈ S → (G.neighborFinset g ∩ S).card ≤ 2 := by
    intro g hg
    have := Finset.card_le_card (hbound g hg)
    rwa [Finset.card_erase_of_mem hg, hcard] at this
  have hsum3 : (G.neighborFinset a ∩ S).card + (G.neighborFinset b ∩ S).card
      + (G.neighborFinset c ∩ S).card = ∑ g ∈ S, (G.neighborFinset g ∩ S).card := by
    rw [hSeq, Finset.sum_insert (by simp [hab, hac]), Finset.sum_insert (by simp [hbc]),
      Finset.sum_singleton, add_assoc]
  have hba := hbcard a haS
  have hbb := hbcard b hbS
  have hbc' := hbcard c hcS
  have ha2 : (G.neighborFinset a ∩ S).card = 2 := by omega
  have hb2 : (G.neighborFinset b ∩ S).card = 2 := by omega
  have haeq : G.neighborFinset a ∩ S = S.erase a :=
    Finset.eq_of_subset_of_card_le (hbound a haS)
      (by rw [Finset.card_erase_of_mem haS, hcard, ha2])
  have hbeq : G.neighborFinset b ∩ S = S.erase b :=
    Finset.eq_of_subset_of_card_le (hbound b hbS)
      (by rw [Finset.card_erase_of_mem hbS, hcard, hb2])
  have hAab : G.Adj a b := by
    have : b ∈ G.neighborFinset a ∩ S := by
      rw [haeq]; exact Finset.mem_erase.mpr ⟨(Ne.symm hab), hbS⟩
    rw [Finset.mem_inter, G.mem_neighborFinset] at this; exact this.1
  have hAac : G.Adj a c := by
    have : c ∈ G.neighborFinset a ∩ S := by
      rw [haeq]; exact Finset.mem_erase.mpr ⟨(Ne.symm hac), hcS⟩
    rw [Finset.mem_inter, G.mem_neighborFinset] at this; exact this.1
  have hAbc : G.Adj b c := by
    have : c ∈ G.neighborFinset b ∩ S := by
      rw [hbeq]; exact Finset.mem_erase.mpr ⟨(Ne.symm hbc), hcS⟩
    rw [Finset.mem_inter, G.mem_neighborFinset] at this; exact this.1
  exact ⟨a, b, c, haS, hbS, hcS, hAab, hAac, hAbc⟩

/-- **All-degree-`≤ 5` budget contradiction.**  Two avoider sets `A₁`, `A₂` of size `≥ m` with
internal degree `≥ 2` (and `≥ 3` on `FF = A₁ ∩ A₂`) inside a hub set `Dc` of internal total `S`
force `S ≥ 3m`; if `S < 3m` this is impossible. -/
theorem budget_contra_gen (Dc A1 A2 FF : Finset (Fin 18)) (f : Fin 18 → ℕ) (m S : ℕ)
    (hA1sub : A1 ⊆ Dc) (hA2sub : A2 ⊆ Dc) (hFF : FF = A1 ∩ A2)
    (hA1card : m ≤ A1.card) (hA2card : m ≤ A2.card)
    (hint2 : ∀ g ∈ A1, 2 ≤ f g) (hint2' : ∀ g ∈ A2, 2 ≤ f g) (hFFint : ∀ g ∈ FF, 3 ≤ f g)
    (hsum : ∑ g ∈ Dc, f g = S) (hlt : S < 3 * m) : False := by
  classical
  have hFFsubA1 : FF ⊆ A1 := by rw [hFF]; exact Finset.inter_subset_left
  have hUsub : A1 ∪ A2 ⊆ Dc := Finset.union_subset hA1sub hA2sub
  have hUle : ∑ g ∈ A1 ∪ A2, f g ≤ S := by
    rw [← hsum]; exact Finset.sum_le_sum_of_subset_of_nonneg hUsub (fun _ _ _ => Nat.zero_le _)
  -- `A1 ∪ A2 = A1 ⊔ (A2 \ A1)`.
  have hdisj : Disjoint A1 (A2 \ A1) := Finset.disjoint_sdiff
  have hunion_eq : A1 ∪ (A2 \ A1) = A1 ∪ A2 := Finset.union_sdiff_self_eq_union
  have hUsplit : ∑ g ∈ A1 ∪ A2, f g = (∑ g ∈ A1, f g) + ∑ g ∈ A2 \ A1, f g := by
    rw [← hunion_eq, Finset.sum_union hdisj]
  -- `∑_{A1} f ≥ 2|A1| + |FF|`.
  have hA1split : (∑ g ∈ A1 \ FF, f g) + ∑ g ∈ FF, f g = ∑ g ∈ A1, f g :=
    Finset.sum_sdiff hFFsubA1
  have hA1mf_ge : 2 * (A1 \ FF).card ≤ ∑ g ∈ A1 \ FF, f g := by
    have := Finset.card_nsmul_le_sum (A1 \ FF) f 2
      (fun g hg => hint2 g ((Finset.mem_sdiff.mp hg).1))
    simpa [smul_eq_mul, Nat.mul_comm] using this
  have hFF_ge : 3 * FF.card ≤ ∑ g ∈ FF, f g := by
    have := Finset.card_nsmul_le_sum FF f 3 hFFint
    simpa [smul_eq_mul, Nat.mul_comm] using this
  have hA1mfcard : (A1 \ FF).card + FF.card = A1.card := by
    have := Finset.card_sdiff_add_card_inter A1 FF
    rwa [Finset.inter_eq_right.mpr hFFsubA1] at this
  -- `∑_{A2\A1} f ≥ 2|A2\A1|`, and `|A2\A1| = |A2| - |FF|`.
  have hA2mA1_ge : 2 * (A2 \ A1).card ≤ ∑ g ∈ A2 \ A1, f g := by
    have := Finset.card_nsmul_le_sum (A2 \ A1) f 2
      (fun g hg => hint2' g ((Finset.mem_sdiff.mp hg).1))
    simpa [smul_eq_mul, Nat.mul_comm] using this
  have hA2A1FF : (A2 ∩ A1).card = FF.card := by rw [hFF, Finset.inter_comm]
  have hA2mA1card : (A2 \ A1).card + FF.card = A2.card := by
    rw [← hA2A1FF]; exact Finset.card_sdiff_add_card_inter A2 A1
  have hFFleA1 : FF.card ≤ A1.card := Finset.card_le_card hFFsubA1
  omega

/-- **Exceptional-hub budget contradiction.**  Like `budget_contra_gen`, but the internal-degree
bounds may fail at a single hub `h6`; dropping its contribution costs at most `3`, so the union
sum is `≥ 3m − 3`.  If `S + 3 < 3m` this is impossible. -/
theorem budget_contra_exc (Dc A1 A2 FF : Finset (Fin 18)) (f : Fin 18 → ℕ) (m S : ℕ) (h6 : Fin 18)
    (hA1sub : A1 ⊆ Dc) (hA2sub : A2 ⊆ Dc) (hFF : FF = A1 ∩ A2)
    (hA1card : m ≤ A1.card) (hA2card : m ≤ A2.card)
    (hint2 : ∀ g ∈ A1, g ≠ h6 → 2 ≤ f g) (hint2' : ∀ g ∈ A2, g ≠ h6 → 2 ≤ f g)
    (hFFint : ∀ g ∈ FF, g ≠ h6 → 3 ≤ f g)
    (hsum : ∑ g ∈ Dc, f g = S) (hlt : S + 3 < 3 * m) : False := by
  classical
  have hFFsubA1 : FF ⊆ A1 := by rw [hFF]; exact Finset.inter_subset_left
  have hUsub : A1 ∪ A2 ⊆ Dc := Finset.union_subset hA1sub hA2sub
  set U := A1 ∪ A2 with hUdef
  have hUle : ∑ g ∈ U, f g ≤ S := by
    rw [← hsum]; exact Finset.sum_le_sum_of_subset_of_nonneg hUsub (fun _ _ _ => Nat.zero_le _)
  have hFFsubU : FF ⊆ U := hFFsubA1.trans Finset.subset_union_left
  -- Work on `U.erase h6`, then split off `FF.erase h6`.
  set Ue := U.erase h6 with hUedef
  set FFe := FF.erase h6 with hFFedef
  have hFFeU : FFe ⊆ Ue := by
    rw [hFFedef, hUedef]; exact Finset.erase_subset_erase _ hFFsubU
  have hUeU : Ue ⊆ U := Finset.erase_subset _ _
  have hdrop : ∑ g ∈ Ue, f g ≤ ∑ g ∈ U, f g :=
    Finset.sum_le_sum_of_subset_of_nonneg hUeU (fun _ _ _ => Nat.zero_le _)
  -- Internal bounds on `Ue` and `FFe`.
  have hUe2 : ∀ g ∈ Ue, 2 ≤ f g := by
    intro g hg
    have hgne : g ≠ h6 := Finset.ne_of_mem_erase hg
    have hgU : g ∈ U := hUeU hg
    rcases Finset.mem_union.mp hgU with hg1 | hg2
    · exact hint2 g hg1 hgne
    · exact hint2' g hg2 hgne
  have hFFe3 : ∀ g ∈ FFe, 3 ≤ f g := by
    intro g hg
    exact hFFint g (Finset.mem_of_mem_erase hg) (Finset.ne_of_mem_erase hg)
  have hsplit : (∑ g ∈ Ue \ FFe, f g) + ∑ g ∈ FFe, f g = ∑ g ∈ Ue, f g :=
    Finset.sum_sdiff hFFeU
  have hdiff_ge : 2 * (Ue \ FFe).card ≤ ∑ g ∈ Ue \ FFe, f g := by
    have := Finset.card_nsmul_le_sum (Ue \ FFe) f 2
      (fun g hg => hUe2 g ((Finset.mem_sdiff.mp hg).1))
    simpa [smul_eq_mul, Nat.mul_comm] using this
  have hFFe_ge : 3 * FFe.card ≤ ∑ g ∈ FFe, f g := by
    have := Finset.card_nsmul_le_sum FFe f 3 hFFe3
    simpa [smul_eq_mul, Nat.mul_comm] using this
  -- Card relations.
  have hdiffcard : (Ue \ FFe).card + FFe.card = Ue.card := by
    have := Finset.card_sdiff_add_card_inter Ue FFe
    rwa [Finset.inter_eq_right.mpr hFFeU] at this
  have hUecard : Ue.card + 1 ≥ U.card := by
    rw [hUedef]
    by_cases hh6 : h6 ∈ U
    · rw [Finset.card_erase_of_mem hh6]; omega
    · rw [Finset.erase_eq_of_notMem hh6]; omega
  have hFFecard : FFe.card + 1 ≥ FF.card := by
    rw [hFFedef]
    by_cases hh6 : h6 ∈ FF
    · rw [Finset.card_erase_of_mem hh6]; omega
    · rw [Finset.erase_eq_of_notMem hh6]; omega
  have hUcard : U.card + FF.card = A1.card + A2.card := by
    rw [hUdef, hFF]; exact Finset.card_union_add_card_inter A1 A2
  have hFFleA1 : FF.card ≤ A1.card := Finset.card_le_card hFFsubA1
  have hA1leU : A1.card ≤ U.card := Finset.card_le_card Finset.subset_union_left
  omega

/-- **Budget collapse for `|D| = 9`.**  With `9` hubs, internal-degree total `16`, avoider
internal degree `≥ 2`, fully-free internal degree `≥ 3` and avoider counts `≥ 5`, the avoider sets
have size exactly `5` and `|FF| ∈ {4, 5}`. -/
theorem budget_force_d9 (Dc A1 A2 FF : Finset (Fin 18)) (f : Fin 18 → ℕ)
    (hA1sub : A1 ⊆ Dc) (hA2sub : A2 ⊆ Dc) (hFF : FF = A1 ∩ A2)
    (hA1card : 5 ≤ A1.card) (hA2card : 5 ≤ A2.card)
    (hint2 : ∀ g ∈ A1, 2 ≤ f g) (hint2' : ∀ g ∈ A2, 2 ≤ f g) (hFFint : ∀ g ∈ FF, 3 ≤ f g)
    (hsum : ∑ g ∈ Dc, f g = 16) (hDc9 : Dc.card = 9) :
    A1.card = 5 ∧ A2.card = 5 ∧ (FF.card = 4 ∨ FF.card = 5) := by
  classical
  have hFFsubA1 : FF ⊆ A1 := by rw [hFF]; exact Finset.inter_subset_left
  have hFFsubA2 : FF ⊆ A2 := by rw [hFF]; exact Finset.inter_subset_right
  have hFFsub : FF ⊆ Dc := hFFsubA1.trans hA1sub
  have hUsub : A1 ∪ A2 ⊆ Dc := Finset.union_subset hA1sub hA2sub
  have hUle : ∑ g ∈ A1 ∪ A2, f g ≤ 16 := by
    rw [← hsum]; exact Finset.sum_le_sum_of_subset_of_nonneg hUsub (fun _ _ _ => Nat.zero_le _)
  have hFFle : ∑ g ∈ FF, f g ≤ 16 := by
    rw [← hsum]; exact Finset.sum_le_sum_of_subset_of_nonneg hFFsub (fun _ _ _ => Nat.zero_le _)
  have hdisj : Disjoint A1 (A2 \ A1) := Finset.disjoint_sdiff
  have hunion_eq : A1 ∪ (A2 \ A1) = A1 ∪ A2 := Finset.union_sdiff_self_eq_union
  have hUsplit : ∑ g ∈ A1 ∪ A2, f g = (∑ g ∈ A1, f g) + ∑ g ∈ A2 \ A1, f g := by
    rw [← hunion_eq, Finset.sum_union hdisj]
  have hA1split : (∑ g ∈ A1 \ FF, f g) + ∑ g ∈ FF, f g = ∑ g ∈ A1, f g :=
    Finset.sum_sdiff hFFsubA1
  have hA1mf_ge : 2 * (A1 \ FF).card ≤ ∑ g ∈ A1 \ FF, f g := by
    have := Finset.card_nsmul_le_sum (A1 \ FF) f 2
      (fun g hg => hint2 g ((Finset.mem_sdiff.mp hg).1))
    simpa [smul_eq_mul, Nat.mul_comm] using this
  have hFF_ge : 3 * FF.card ≤ ∑ g ∈ FF, f g := by
    have := Finset.card_nsmul_le_sum FF f 3 hFFint
    simpa [smul_eq_mul, Nat.mul_comm] using this
  have hA1mfcard : (A1 \ FF).card + FF.card = A1.card := by
    have := Finset.card_sdiff_add_card_inter A1 FF
    rwa [Finset.inter_eq_right.mpr hFFsubA1] at this
  have hA2mA1_ge : 2 * (A2 \ A1).card ≤ ∑ g ∈ A2 \ A1, f g := by
    have := Finset.card_nsmul_le_sum (A2 \ A1) f 2
      (fun g hg => hint2' g ((Finset.mem_sdiff.mp hg).1))
    simpa [smul_eq_mul, Nat.mul_comm] using this
  have hA2A1FF : (A2 ∩ A1).card = FF.card := by rw [hFF, Finset.inter_comm]
  have hA2mA1card : (A2 \ A1).card + FF.card = A2.card := by
    rw [← hA2A1FF]; exact Finset.card_sdiff_add_card_inter A2 A1
  have hFFleA1 : FF.card ≤ A1.card := Finset.card_le_card hFFsubA1
  have hUcard_le : (A1 ∪ A2).card ≤ 9 := by rw [← hDc9]; exact Finset.card_le_card hUsub
  have hUcard_eq : A1.card + A2.card = (A1 ∪ A2).card + FF.card := by
    rw [hFF]; exact (Finset.card_union_add_card_inter A1 A2).symm
  refine ⟨?_, ?_, ?_⟩ <;> omega

/-- **Budget pinning for `|D| = 10`, `h6 ∈ FF` (fully free).**  With the lone degree-`6` hub `h6`
fully free and internal total `10`, the avoider set `A2` has size exactly `4` and `|FF| ≥ 3`. -/
theorem budget_force_d10_ff (Dc A1 A2 FF : Finset (Fin 18)) (f : Fin 18 → ℕ) (h6 : Fin 18)
    (hA1sub : A1 ⊆ Dc) (hA2sub : A2 ⊆ Dc) (hFF : FF = A1 ∩ A2) (hh6FF : h6 ∈ FF)
    (hA1card : 4 ≤ A1.card) (hA2card : 4 ≤ A2.card)
    (hint2 : ∀ g ∈ A1, g ≠ h6 → 2 ≤ f g) (hint2' : ∀ g ∈ A2, g ≠ h6 → 2 ≤ f g)
    (hFFint : ∀ g ∈ FF, g ≠ h6 → 3 ≤ f g)
    (hsum : ∑ g ∈ Dc, f g = 10) (hDc8 : Dc.card = 8) :
    A2.card = 4 ∧ 3 ≤ FF.card := by
  classical
  have hFFsubA1 : FF ⊆ A1 := by rw [hFF]; exact Finset.inter_subset_left
  have hFFsubA2 : FF ⊆ A2 := by rw [hFF]; exact Finset.inter_subset_right
  have hFFsub : FF ⊆ Dc := hFFsubA1.trans hA1sub
  have hUsub : A1 ∪ A2 ⊆ Dc := Finset.union_subset hA1sub hA2sub
  have hUle : ∑ g ∈ A1 ∪ A2, f g ≤ 10 := by
    rw [← hsum]; exact Finset.sum_le_sum_of_subset_of_nonneg hUsub (fun _ _ _ => Nat.zero_le _)
  have hFFle : ∑ g ∈ FF, f g ≤ 10 := by
    rw [← hsum]; exact Finset.sum_le_sum_of_subset_of_nonneg hFFsub (fun _ _ _ => Nat.zero_le _)
  have hdisj : Disjoint A1 (A2 \ A1) := Finset.disjoint_sdiff
  have hunion_eq : A1 ∪ (A2 \ A1) = A1 ∪ A2 := Finset.union_sdiff_self_eq_union
  have hUsplit : ∑ g ∈ A1 ∪ A2, f g = (∑ g ∈ A1, f g) + ∑ g ∈ A2 \ A1, f g := by
    rw [← hunion_eq, Finset.sum_union hdisj]
  have hA1split : (∑ g ∈ A1 \ FF, f g) + ∑ g ∈ FF, f g = ∑ g ∈ A1, f g :=
    Finset.sum_sdiff hFFsubA1
  have hA1mf_ge : 2 * (A1 \ FF).card ≤ ∑ g ∈ A1 \ FF, f g := by
    have := Finset.card_nsmul_le_sum (A1 \ FF) f 2 (fun g hg =>
      hint2 g ((Finset.mem_sdiff.mp hg).1)
        (fun e => (Finset.mem_sdiff.mp hg).2 (e ▸ hh6FF)))
    simpa [smul_eq_mul, Nat.mul_comm] using this
  have hA1mfcard : (A1 \ FF).card + FF.card = A1.card := by
    have := Finset.card_sdiff_add_card_inter A1 FF
    rwa [Finset.inter_eq_right.mpr hFFsubA1] at this
  -- `∑_FF f ≥ 3(|FF| − 1)`.
  have hFFerasecard : (FF.erase h6).card = FF.card - 1 := Finset.card_erase_of_mem hh6FF
  have hFFerase_ge : 3 * (FF.erase h6).card ≤ ∑ g ∈ FF.erase h6, f g := by
    have := Finset.card_nsmul_le_sum (FF.erase h6) f 3 (fun g hg =>
      hFFint g (Finset.mem_of_mem_erase hg) (Finset.ne_of_mem_erase hg))
    simpa [smul_eq_mul, Nat.mul_comm] using this
  have hFFerase_le : ∑ g ∈ FF.erase h6, f g ≤ ∑ g ∈ FF, f g :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) (fun _ _ _ => Nat.zero_le _)
  -- `∑_{A2\A1} f ≥ 2|A2\A1|`.
  have hA2mA1_ge : 2 * (A2 \ A1).card ≤ ∑ g ∈ A2 \ A1, f g := by
    have := Finset.card_nsmul_le_sum (A2 \ A1) f 2 (fun g hg =>
      hint2' g (Finset.mem_sdiff.mp hg).1
        (fun e => (Finset.mem_sdiff.mp hg).2 (e ▸ hFFsubA1 hh6FF)))
    simpa [smul_eq_mul, Nat.mul_comm] using this
  have hA2A1FF : (A2 ∩ A1).card = FF.card := by rw [hFF, Finset.inter_comm]
  have hA2mA1card : (A2 \ A1).card + FF.card = A2.card := by
    rw [← hA2A1FF]; exact Finset.card_sdiff_add_card_inter A2 A1
  have hFFleA1 : FF.card ≤ A1.card := Finset.card_le_card hFFsubA1
  have hFFleA2 : FF.card ≤ A2.card := Finset.card_le_card hFFsubA2
  have hUcard_le : (A1 ∪ A2).card ≤ 8 := by rw [← hDc8]; exact Finset.card_le_card hUsub
  have hUcard_eq : A1.card + A2.card = (A1 ∪ A2).card + FF.card := by
    rw [hFF]; exact (Finset.card_union_add_card_inter A1 A2).symm
  have hFFpos : 1 ≤ FF.card := Finset.card_pos.mpr ⟨h6, hh6FF⟩
  refine ⟨?_, ?_⟩ <;> omega

/-- **`|D| = 10` clean-avoider counting contradiction (exceptional hub off `A`).**  If avoider set
`A` (not containing the lone degree-`6` hub `h6`) has internal degree `≥ 2` (`≥ 3` on `FF = A ∩ B`)
and `B` has internal degree `≥ 2` off `h6`, with `|A|, |B| ≥ 4` and internal total `10`, then the
budget forces `|FF| ≥ 4`, whence `∑_FF int ≥ 12 > 10`. -/
theorem d10_exc_clean (Dc A B FF : Finset (Fin 18)) (f : Fin 18 → ℕ) (h6 : Fin 18)
    (hAsub : A ⊆ Dc) (hBsub : B ⊆ Dc) (hFF : FF = A ∩ B)
    (hAint : ∀ g ∈ A, 2 ≤ f g) (hFFint : ∀ g ∈ FF, 3 ≤ f g)
    (hBint : ∀ g ∈ B, g ≠ h6 → 2 ≤ f g) (_hh6A : h6 ∉ A)
    (hAcard : 4 ≤ A.card) (hBcard : 4 ≤ B.card) (hsum : ∑ g ∈ Dc, f g = 10) : False := by
  classical
  have hFFsubA : FF ⊆ A := by rw [hFF]; exact Finset.inter_subset_left
  have hFFsub : FF ⊆ Dc := hFFsubA.trans hAsub
  have hUsub : A ∪ B ⊆ Dc := Finset.union_subset hAsub hBsub
  have hUle : ∑ g ∈ A ∪ B, f g ≤ 10 := by
    rw [← hsum]; exact Finset.sum_le_sum_of_subset_of_nonneg hUsub (fun _ _ _ => Nat.zero_le _)
  have hFFle : ∑ g ∈ FF, f g ≤ 10 := by
    rw [← hsum]; exact Finset.sum_le_sum_of_subset_of_nonneg hFFsub (fun _ _ _ => Nat.zero_le _)
  have hdisj : Disjoint A (B \ A) := Finset.disjoint_sdiff
  have hunion_eq : A ∪ (B \ A) = A ∪ B := Finset.union_sdiff_self_eq_union
  have hUsplit : ∑ g ∈ A ∪ B, f g = (∑ g ∈ A, f g) + ∑ g ∈ B \ A, f g := by
    rw [← hunion_eq, Finset.sum_union hdisj]
  have hAsplit : (∑ g ∈ A \ FF, f g) + ∑ g ∈ FF, f g = ∑ g ∈ A, f g := Finset.sum_sdiff hFFsubA
  have hAmf_ge : 2 * (A \ FF).card ≤ ∑ g ∈ A \ FF, f g := by
    have := Finset.card_nsmul_le_sum (A \ FF) f 2 (fun g hg => hAint g ((Finset.mem_sdiff.mp hg).1))
    simpa [smul_eq_mul, Nat.mul_comm] using this
  have hFF_ge : 3 * FF.card ≤ ∑ g ∈ FF, f g := by
    have := Finset.card_nsmul_le_sum FF f 3 hFFint
    simpa [smul_eq_mul, Nat.mul_comm] using this
  have hAmfcard : (A \ FF).card + FF.card = A.card := by
    have := Finset.card_sdiff_add_card_inter A FF
    rwa [Finset.inter_eq_right.mpr hFFsubA] at this
  -- `∑_{B\A} f ≥ 2|B\A| − 2` (drop `h6`).
  have hBmA_ge : 2 * (B \ A).card ≤ (∑ g ∈ B \ A, f g) + 2 := by
    have hBmAe : (B \ A).erase h6 ⊆ B \ A := Finset.erase_subset _ _
    have hcard : (B \ A).card ≤ ((B \ A).erase h6).card + 1 := by
      by_cases hh6 : h6 ∈ B \ A
      · rw [Finset.card_erase_of_mem hh6]; omega
      · rw [Finset.erase_eq_of_notMem hh6]; omega
    have hge : 2 * ((B \ A).erase h6).card ≤ ∑ g ∈ (B \ A).erase h6, f g := by
      have := Finset.card_nsmul_le_sum ((B \ A).erase h6) f 2 (fun g hg =>
        hBint g ((Finset.mem_sdiff.mp (Finset.mem_of_mem_erase hg)).1) (Finset.ne_of_mem_erase hg))
      simpa [smul_eq_mul, Nat.mul_comm] using this
    have hdrop : ∑ g ∈ (B \ A).erase h6, f g ≤ ∑ g ∈ B \ A, f g :=
      Finset.sum_le_sum_of_subset_of_nonneg hBmAe (fun _ _ _ => Nat.zero_le _)
    omega
  have hBA_FF : (B ∩ A).card = FF.card := by rw [hFF, Finset.inter_comm]
  have hBmAcard : (B \ A).card + FF.card = B.card := by
    rw [← hBA_FF]; exact Finset.card_sdiff_add_card_inter B A
  have hFFleA : FF.card ≤ A.card := Finset.card_le_card hFFsubA
  omega

set_option maxHeartbeats 1000000 in
/-- **No degree-`≤ 13` avoider triangle ⇒ contradiction (`n = 18`, `P₄`, `|D| ∈ {9, 10, 11}`).** -/
theorem iso_rich_force_p4_eighteen (G : SimpleGraph (Fin 18))
    (D Iso : Finset (Fin 18)) (L₁ c₁ c₂ L₂ : Fin 18)
    (h3 : ∀ v : Fin 18, 3 ≤ G.degree v)
    (hmemD : ∀ v : Fin 18, v ∈ D ↔ G.degree v = 3)
    (hIsoprop : ∀ v ∈ Iso, G.degree v = 3 ∧ (∀ w : Fin 18, G.Adj v w → G.degree w ≠ 3))
    (hisochar : ∀ w : Fin 18, w ∈ D → w ≠ L₁ → w ≠ c₁ → w ≠ c₂ → w ≠ L₂ → w ∈ Iso)
    (hL1deg : G.degree L₁ = 3) (hc1deg : G.degree c₁ = 3)
    (hc2deg : G.degree c₂ = 3) (hL2deg : G.degree L₂ = 3)
    (hac1L1 : G.Adj c₁ L₁) (hc12 : G.Adj c₁ c₂) (hac2L2 : G.Adj c₂ L₂)
    (hL1nc2 : L₁ ≠ c₂) (hL2nc1 : L₂ ≠ c₁)
    (hNc1D : G.neighborFinset c₁ ∩ D = {c₂, L₁}) (hNc2D : G.neighborFinset c₂ ∩ D = {c₁, L₂})
    (hL1D : L₁ ∈ D) (hc1D : c₁ ∈ D) (hc2D : c₂ ∈ D) (hL2D : L₂ ∈ D)
    (hd_lb : 9 ≤ D.card) (hd_ub : D.card ≤ 11) (htt : ¬TwoTwinConfig G)
    (hth : ¬TwoHubConfig G)
    (hT : ¬∃ x y z : Fin 18, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    (hC4 : ¬∃ a b c d : Fin 18, ({a, b, c, d} : Finset (Fin 18)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (hDccard : Dᶜ.card = 18 - D.card) (_hIsocard : Iso.card = D.card - 4)
    (hc1hub : (G.neighborFinset c₁ ∩ Dᶜ).card = 1)
    (hc2hub : (G.neighborFinset c₂ ∩ Dᶜ).card = 1)
    (hL1hub : (G.neighborFinset L₁ ∩ Dᶜ).card = 2)
    (hL2hub : (G.neighborFinset L₂ ∩ Dᶜ).card = 2)
    (hsumPath : ∑ g ∈ Dᶜ, (G.neighborFinset g ∩ ({L₁, c₁, c₂, L₂} : Finset (Fin 18))).card = 6)
    (hsumIso : ∑ g ∈ Dᶜ, (G.neighborFinset g ∩ Iso).card = 3 * (D.card - 4))
    (hsumInternal : ∑ g ∈ Dᶜ, (G.neighborFinset g ∩ Dᶜ).card = 70 - 6 * D.card)
    (hper : ∀ g : Fin 18, g ∈ Dᶜ →
      (G.neighborFinset g ∩ ({L₁, c₁, c₂, L₂} : Finset (Fin 18))).card
        + (G.neighborFinset g ∩ Iso).card + (G.neighborFinset g ∩ Dᶜ).card = G.degree g)
    (_hntri1 : ¬∃ a b c : Fin 18, a ∈ Dᶜ ∧ b ∈ Dᶜ ∧ c ∈ Dᶜ ∧
      G.Adj a b ∧ G.Adj a c ∧ G.Adj b c ∧
      (¬G.Adj a L₁ ∧ ¬G.Adj a c₁ ∧ ¬G.Adj a c₂) ∧
      (¬G.Adj b L₁ ∧ ¬G.Adj b c₁ ∧ ¬G.Adj b c₂) ∧
      (¬G.Adj c L₁ ∧ ¬G.Adj c c₁ ∧ ¬G.Adj c c₂) ∧
      G.degree a + G.degree b + G.degree c ≤ 13)
    (hntri2 : ¬∃ a b c : Fin 18, a ∈ Dᶜ ∧ b ∈ Dᶜ ∧ c ∈ Dᶜ ∧
      G.Adj a b ∧ G.Adj a c ∧ G.Adj b c ∧
      (¬G.Adj a c₁ ∧ ¬G.Adj a c₂ ∧ ¬G.Adj a L₂) ∧
      (¬G.Adj b c₁ ∧ ¬G.Adj b c₂ ∧ ¬G.Adj b L₂) ∧
      (¬G.Adj c c₁ ∧ ¬G.Adj c c₂ ∧ ¬G.Adj c L₂) ∧
      G.degree a + G.degree b + G.degree c ≤ 13) :
    False := by
  classical
  set P : Finset (Fin 18) := {L₁, c₁, c₂, L₂} with hPdef
  -- Every hub has degree `≥ 4`.
  have hge4 : ∀ g : Fin 18, g ∈ Dᶜ → 4 ≤ G.degree g := by
    intro g hg
    have hgD : g ∉ D := Finset.mem_compl.mp hg
    have : G.degree g ≠ 3 := fun he => hgD ((hmemD g).mpr he)
    have := h3 g
    omega
  -- Hub degree total `∑_{Dᶜ} deg = 64 − 3|D|`.
  have hsumdeg : ∑ g ∈ Dᶜ, G.degree g = 64 - 3 * D.card := by
    have hcong : ∑ g ∈ Dᶜ, ((G.neighborFinset g ∩ P).card
        + (G.neighborFinset g ∩ Iso).card + (G.neighborFinset g ∩ Dᶜ).card)
        = ∑ g ∈ Dᶜ, G.degree g := Finset.sum_congr rfl hper
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hsumPath, hsumIso, hsumInternal] at hcong
    omega
  -- The (W) fact for degree-`≤ 5` hubs.
  have hW := cherry_p4_W_facts_eighteen G D Iso L₁ c₁ c₂ L₂ hIsoprop hL1deg hc1deg hc2deg hL2deg
    hac1L1 hc12 hac2L2 hL1nc2 hL2nc1 hL1D hc1D hc2D hL2D htt
  -- Classification of `D`.
  have hclassP : ∀ x : Fin 18, x ∈ D → x = L₁ ∨ x = c₁ ∨ x = c₂ ∨ x = L₂ ∨ x ∈ Iso := by
    intro x hx
    by_cases h1 : x = L₁
    · exact Or.inl h1
    by_cases h2 : x = c₁
    · exact Or.inr (Or.inl h2)
    by_cases h3' : x = c₂
    · exact Or.inr (Or.inr (Or.inl h3'))
    by_cases h4 : x = L₂
    · exact Or.inr (Or.inr (Or.inr (Or.inl h4)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (hisochar x hx h1 h2 h3' h4))))
  -- The two cherry-avoider sets and `FF`.
  set A1 := Dᶜ.filter (fun g => ¬G.Adj g L₁ ∧ ¬G.Adj g c₁ ∧ ¬G.Adj g c₂) with hA1def
  set A2 := Dᶜ.filter (fun g => ¬G.Adj g c₁ ∧ ¬G.Adj g c₂ ∧ ¬G.Adj g L₂) with hA2def
  set FF := A1 ∩ A2 with hFFdef
  have hA1sub : A1 ⊆ Dᶜ := by rw [hA1def]; exact Finset.filter_subset _ _
  have hA2sub : A2 ⊆ Dᶜ := by rw [hA2def]; exact Finset.filter_subset _ _
  have hFFsubA1 : FF ⊆ A1 := by rw [hFFdef]; exact Finset.inter_subset_left
  have hFFsubA2 : FF ⊆ A2 := by rw [hFFdef]; exact Finset.inter_subset_right
  have hFFsub : FF ⊆ Dᶜ := hFFsubA1.trans hA1sub
  -- Avoider counts.
  have hA1card_lb : Dᶜ.card - 4 ≤ A1.card := by
    have := avoiders_ge_gen G D L₁ c₁ c₂ (by rw [hL1hub, hc1hub, hc2hub])
    rwa [← hA1def] at this
  have hA2card_lb : Dᶜ.card - 4 ≤ A2.card := by
    have := avoiders_ge_gen G D c₁ c₂ L₂ (by rw [hc1hub, hc2hub, hL2hub])
    rwa [← hA2def] at this
  -- `hclass` packagers for the internal-degree lemmas.
  have hclassA1 : ∀ g : Fin 18, g ∈ A1 → ∀ x : Fin 18, G.Adj g x → x ∈ D → x = L₂ ∨ x ∈ Iso := by
    intro g hg x hadj hxD
    rw [hA1def, Finset.mem_filter] at hg
    obtain ⟨_, hgL1, hgc1, hgc2⟩ := hg
    rcases hclassP x hxD with h | h | h | h | h
    · exact absurd (h ▸ hadj) hgL1
    · exact absurd (h ▸ hadj) hgc1
    · exact absurd (h ▸ hadj) hgc2
    · exact Or.inl h
    · exact Or.inr h
  have hclassA2 : ∀ g : Fin 18, g ∈ A2 → ∀ x : Fin 18, G.Adj g x → x ∈ D → x = L₁ ∨ x ∈ Iso := by
    intro g hg x hadj hxD
    rw [hA2def, Finset.mem_filter] at hg
    obtain ⟨_, hgc1, hgc2, hgL2⟩ := hg
    rcases hclassP x hxD with h | h | h | h | h
    · exact Or.inl h
    · exact absurd (h ▸ hadj) hgc1
    · exact absurd (h ▸ hadj) hgc2
    · exact absurd (h ▸ hadj) hgL2
    · exact Or.inr h
  have hclassFF : ∀ g : Fin 18, g ∈ FF → ∀ x : Fin 18, G.Adj g x → x ∈ D → x ∈ Iso := by
    intro g hg x hadj hxD
    have hgA1 := hFFsubA1 hg
    have hgA2 := hFFsubA2 hg
    rw [hA1def, Finset.mem_filter] at hgA1
    rw [hA2def, Finset.mem_filter] at hgA2
    obtain ⟨_, hgL1, hgc1, hgc2⟩ := hgA1
    obtain ⟨_, _, _, hgL2⟩ := hgA2
    rcases hclassP x hxD with h | h | h | h | h
    · exact absurd (h ▸ hadj) hgL1
    · exact absurd (h ▸ hadj) hgc1
    · exact absurd (h ▸ hadj) hgc2
    · exact absurd (h ▸ hadj) hgL2
    · exact h
  -- Membership extractors into the avoider predicates.
  have getA2pred : ∀ g : Fin 18, g ∈ A2 →
      ¬G.Adj g c₁ ∧ ¬G.Adj g c₂ ∧ ¬G.Adj g L₂ := by
    intro g hg; rw [hA2def, Finset.mem_filter] at hg; exact hg.2
  have getA1pred : ∀ g : Fin 18, g ∈ A1 →
      ¬G.Adj g L₁ ∧ ¬G.Adj g c₁ ∧ ¬G.Adj g c₂ := by
    intro g hg; rw [hA1def, Finset.mem_filter] at hg; exact hg.2
  -- Dispatch on `|D|`.
  rcases (by omega : D.card = 9 ∨ D.card = 10 ∨ D.card = 11) with hD9 | hD10 | hD11
  · -- **`|D| = 9`.**
    have hDc9 : Dᶜ.card = 9 := by rw [hDccard, hD9]
    have hint16 : ∑ g ∈ Dᶜ, (G.neighborFinset g ∩ Dᶜ).card = 16 := by rw [hsumInternal, hD9]
    have hdeg37 : ∑ g ∈ Dᶜ, G.degree g = 37 := by rw [hsumdeg, hD9]
    have hA1c5 : 5 ≤ A1.card := by rw [hDc9] at hA1card_lb; omega
    have hA2c5 : 5 ≤ A2.card := by rw [hDc9] at hA2card_lb; omega
    have hdeg5 : ∀ g : Fin 18, g ∈ Dᶜ → G.degree g ≤ 5 := by
      intro g hg
      have := hub_deg_upper_pt Dᶜ (fun v => G.degree v) 37 hge4 hdeg37 g hg
      rw [hDc9] at this; omega
    have hA1int : ∀ g ∈ A1, 2 ≤ (G.neighborFinset g ∩ Dᶜ).card := by
      intro g hg
      exact avoider_internal_ge_two_pt G D Iso g L₂ (hge4 g (hA1sub hg))
        (hW g (hA1sub hg) (hdeg5 g (hA1sub hg)) (Or.inl (getA1pred g hg))) (hclassA1 g hg)
    have hA2int : ∀ g ∈ A2, 2 ≤ (G.neighborFinset g ∩ Dᶜ).card := by
      intro g hg
      exact avoider_internal_ge_two_pt G D Iso g L₁ (hge4 g (hA2sub hg))
        (hW g (hA2sub hg) (hdeg5 g (hA2sub hg)) (Or.inr (getA2pred g hg))) (hclassA2 g hg)
    have hFFint : ∀ g ∈ FF, 3 ≤ (G.neighborFinset g ∩ Dᶜ).card := by
      intro g hg
      exact fully_free_internal_ge_three_pt G D Iso g (hge4 g (hFFsub hg))
        (hW g (hFFsub hg) (hdeg5 g (hFFsub hg))
          (Or.inl (getA1pred g (hFFsubA1 hg)))) (hclassFF g hg)
    obtain ⟨_hA1c, hA2c, hFFcase⟩ :=
      budget_force_d9 Dᶜ A1 A2 FF (fun g => (G.neighborFinset g ∩ Dᶜ).card)
      hA1sub hA2sub hFFdef hA1c5 hA2c5 hA1int hA2int hFFint hint16 hDc9
    rcases hFFcase with hFF4 | hFF5
    · -- `|FF| = 4`: the six avoiders carry all internal incidences, forcing two isolated
      -- degree-`4` hubs; the `Iso`-rich one pairs into a `TwoHubConfig`, contradicting `hth`.
      have hL1L2 : L₁ ≠ L₂ := by
        intro he
        exact hT ⟨c₁, c₂, L₁, G.ne_of_adj hc12, he.symm ▸ G.ne_of_adj hac2L2,
          G.ne_of_adj hac1L1, hc12, he.symm ▸ hac2L2, hac1L1, by omega⟩
      have hnc1L2 : ¬G.Adj c₁ L₂ := by
        intro hadj
        have hmem : L₂ ∈ G.neighborFinset c₁ ∩ D :=
          Finset.mem_inter.mpr ⟨(G.mem_neighborFinset c₁ L₂).mpr hadj, hL2D⟩
        rw [hNc1D] at hmem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
        rcases hmem with h | h
        · exact (G.ne_of_adj hac2L2) h.symm
        · exact hL1L2 h.symm
      have hnc2L1 : ¬G.Adj c₂ L₁ := by
        intro hadj
        have hmem : L₁ ∈ G.neighborFinset c₂ ∩ D :=
          Finset.mem_inter.mpr ⟨(G.mem_neighborFinset c₂ L₁).mpr hadj, hL1D⟩
        rw [hNc2D] at hmem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
        rcases hmem with h | h
        · exact (G.ne_of_adj hac1L1) h.symm
        · exact hL1L2 h
      have hIsoD : Iso ⊆ D := fun v hv => (hmemD v).mpr (hIsoprop v hv).1
      obtain ⟨h₁, h₂, hh1T, hh2T, hne12, hh1d, hh2d, hh10, hh20⟩ :=
        zero_internal_hubs_d9_ff4 G D A1 A2 FF hA1sub hA2sub hFFdef _hA1c hA2c hFF4
          hA1int hA2int hFFint hint16 hdeg37 hge4 hdeg5 hDc9
      have hh1Dc : h₁ ∈ Dᶜ := (Finset.mem_sdiff.mp hh1T).1
      have hh2Dc : h₂ ∈ Dᶜ := (Finset.mem_sdiff.mp hh2T).1
      -- `L₁` has a hub-neighbour `x₂` distinct from `h₁, h₂` (from `A2 \ FF`).
      have hx2card : 0 < (A2 \ FF).card := by
        have h := Finset.card_sdiff_add_card_inter A2 FF
        rw [Finset.inter_eq_right.mpr hFFsubA2] at h; omega
      obtain ⟨x₂, hx2mem⟩ := Finset.card_pos.mp hx2card
      obtain ⟨hx2A2, hx2notFF⟩ := Finset.mem_sdiff.mp hx2mem
      have hx2A1 : x₂ ∉ A1 := fun hmem =>
        hx2notFF (by rw [hFFdef]; exact Finset.mem_inter.mpr ⟨hmem, hx2A2⟩)
      have hAdjx2L1 : G.Adj x₂ L₁ := by
        by_contra hno
        exact hx2A1 (by rw [hA1def, Finset.mem_filter]
                        exact ⟨hA2sub hx2A2, hno, (getA2pred x₂ hx2A2).1, (getA2pred x₂ hx2A2).2.1⟩)
      have hx2ne1 : x₂ ≠ h₁ := by
        intro he; rw [he] at hx2A2
        exact (Finset.mem_sdiff.mp hh1T).2 (Finset.mem_union_right _ hx2A2)
      have hx2ne2 : x₂ ≠ h₂ := by
        intro he; rw [he] at hx2A2
        exact (Finset.mem_sdiff.mp hh2T).2 (Finset.mem_union_right _ hx2A2)
      have hrich := isolated_hub_iso_rich_d9_ff4 G D Iso L₁ c₁ c₂ L₂ h₁ h₂ hT hC4 hclassP hIsoprop
        hac1L1 hc12 hac2L2 hnc1L2 hnc2L1 hL1nc2 hL2nc1 hL1deg hc1deg hc2deg hL2deg
        hh1Dc hh2Dc hh1d hh2d hh10 hh20 hne12 hL1hub
        ⟨x₂, hA2sub hx2A2, hx2ne1, hx2ne2, hAdjx2L1⟩
      rcases hrich with hrich | hrich
      · exact hth (two_isolated_hub_twohubconfig_d9_ff4 G D Iso L₁ c₁ c₂ L₂ h₁ h₂ hC4 hmemD hIsoD
          hclassP hIsoprop hac1L1 hc12 hac2L2 hc1deg hc2deg hh1Dc hh2Dc hh1d hh2d hh10 hh20
          hne12 hrich)
      · exact hth (two_isolated_hub_twohubconfig_d9_ff4 G D Iso L₁ c₁ c₂ L₂ h₂ h₁ hC4 hmemD hIsoD
          hclassP hIsoprop hac1L1 hc12 hac2L2 hc1deg hc2deg hh2Dc hh1Dc hh2d hh1d hh20 hh10
          hne12.symm hrich)
    · -- `|FF| = 5`: Mantel-`5` triangle inside `FF = A2`.
      have hFFeqA2 : FF = A2 := Finset.eq_of_subset_of_card_le hFFsubA2 (by rw [hFF5, hA2c])
      have hFF_ge : 3 * FF.card ≤ ∑ g ∈ FF, (G.neighborFinset g ∩ Dᶜ).card := by
        have := Finset.card_nsmul_le_sum FF (fun g => (G.neighborFinset g ∩ Dᶜ).card) 3 hFFint
        simpa [smul_eq_mul, Nat.mul_comm] using this
      have hedge : 14 ≤ ∑ g ∈ FF, (G.neighborFinset g ∩ FF).card := by
        have hlb := ff_internal_edge_lb_gen G Dᶜ FF 16 hFFsub hint16
        omega
      obtain ⟨a, b, c, haFF, hbFF, hcFF, hab, hac, hbc⟩ := mantel_five_triangle G FF hFF5 hedge
      have haA2 := hFFeqA2 ▸ haFF
      have hbA2 := hFFeqA2 ▸ hbFF
      have hcA2 := hFFeqA2 ▸ hcFF
      obtain ⟨hac1, hac2, haL2⟩ := getA2pred a haA2
      obtain ⟨hbc1, hbc2, hbL2⟩ := getA2pred b hbA2
      obtain ⟨hcc1, hcc2, hcL2⟩ := getA2pred c hcA2
      have hdsum := hub_deg3_upper Dᶜ (fun v => G.degree v) 37 hge4 hdeg37 a b c
        (hFFsub haFF) (hFFsub hbFF) (hFFsub hcFF)
        (G.ne_of_adj hab) (G.ne_of_adj hac) (G.ne_of_adj hbc)
      rw [hDc9] at hdsum
      exact hntri2 ⟨a, b, c, hFFsub haFF, hFFsub hbFF, hFFsub hcFF, hab, hac, hbc,
        ⟨hac1, hac2, haL2⟩, ⟨hbc1, hbc2, hbL2⟩, ⟨hcc1, hcc2, hcL2⟩, by omega⟩
  · -- **`|D| = 10`.**
    have hDc8 : Dᶜ.card = 8 := by rw [hDccard, hD10]
    have hint10 : ∑ g ∈ Dᶜ, (G.neighborFinset g ∩ Dᶜ).card = 10 := by rw [hsumInternal, hD10]
    have hdeg34 : ∑ g ∈ Dᶜ, G.degree g = 34 := by rw [hsumdeg, hD10]
    have hA1c4 : 4 ≤ A1.card := by rw [hDc8] at hA1card_lb; omega
    have hA2c4 : 4 ≤ A2.card := by rw [hDc8] at hA2card_lb; omega
    by_cases hex6 : ∃ h6 : Fin 18, h6 ∈ Dᶜ ∧ 6 ≤ G.degree h6
    · obtain ⟨h6, hh6Dc, hh6deg⟩ := hex6
      have herase : G.degree h6 + ∑ x ∈ Dᶜ.erase h6, G.degree x = 34 := by
        have h := Finset.add_sum_erase Dᶜ (fun v => G.degree v) hh6Dc
        rw [hdeg34] at h; exact h
      have hcard7 : (Dᶜ.erase h6).card = 7 := by rw [Finset.card_erase_of_mem hh6Dc, hDc8]
      have hother4 : ∀ g : Fin 18, g ∈ Dᶜ → g ≠ h6 → G.degree g = 4 := by
        intro g hg hgne
        have hub := hub_deg_upper_pt (Dᶜ.erase h6) (fun v => G.degree v)
          (∑ x ∈ Dᶜ.erase h6, G.degree x)
          (fun x hx => hge4 x (Finset.mem_of_mem_erase hx)) rfl g (Finset.mem_erase.mpr ⟨hgne, hg⟩)
        rw [hcard7] at hub
        have := hge4 g hg
        omega
      have hother5 : ∀ g : Fin 18, g ∈ Dᶜ → g ≠ h6 → G.degree g ≤ 5 :=
        fun g hg hgne => by have := hother4 g hg hgne; omega
      have hA1int' : ∀ g : Fin 18, g ∈ A1 → g ≠ h6 → 2 ≤ (G.neighborFinset g ∩ Dᶜ).card := by
        intro g hg hgne
        exact avoider_internal_ge_two_pt G D Iso g L₂ (hge4 g (hA1sub hg))
          (hW g (hA1sub hg) (hother5 g (hA1sub hg) hgne) (Or.inl (getA1pred g hg))) (hclassA1 g hg)
      have hA2int' : ∀ g : Fin 18, g ∈ A2 → g ≠ h6 → 2 ≤ (G.neighborFinset g ∩ Dᶜ).card := by
        intro g hg hgne
        exact avoider_internal_ge_two_pt G D Iso g L₁ (hge4 g (hA2sub hg))
          (hW g (hA2sub hg) (hother5 g (hA2sub hg) hgne) (Or.inr (getA2pred g hg))) (hclassA2 g hg)
      have hFFint' : ∀ g : Fin 18, g ∈ FF → g ≠ h6 → 3 ≤ (G.neighborFinset g ∩ Dᶜ).card := by
        intro g hg hgne
        exact fully_free_internal_ge_three_pt G D Iso g (hge4 g (hFFsub hg))
          (hW g (hFFsub hg) (hother5 g (hFFsub hg) hgne)
            (Or.inl (getA1pred g (hFFsubA1 hg)))) (hclassFF g hg)
      by_cases hh6A1 : h6 ∈ A1
      · by_cases hh6A2 : h6 ∈ A2
        · -- `h6 ∈ FF` (fully free): the collapse to an avoider triangle.  Apply the in-set edge
          -- bound to `S = A2 ∖ {h6}` (`|S| = 3`, all in `A2`, all degree `4`): the two fully-free
          -- hubs (internal degree `≥ 3`) plus the third avoider (`≥ 2`) give `∑_S int ≥ 8`, hence
          -- `∑_S (N ∩ S) ≥ 6`, a Mantel-`3` triangle of degree sum `12 ≤ 13` contradicting `hntri2`.
          have hh6FF : h6 ∈ FF := by rw [hFFdef]; exact Finset.mem_inter.mpr ⟨hh6A1, hh6A2⟩
          obtain ⟨hA2c4eq, hFFge3⟩ := budget_force_d10_ff Dᶜ A1 A2 FF
            (fun g => (G.neighborFinset g ∩ Dᶜ).card) h6 hA1sub hA2sub hFFdef hh6FF hA1c4 hA2c4
            hA1int' hA2int' hFFint' hint10 hDc8
          set S := A2.erase h6 with hSdef
          have hSsub : S ⊆ Dᶜ := (Finset.erase_subset _ _).trans hA2sub
          have hScard : S.card = 3 := by rw [hSdef, Finset.card_erase_of_mem hh6A2, hA2c4eq]
          have hFF'subS : FF.erase h6 ⊆ S := by
            rw [hSdef]; exact Finset.erase_subset_erase _ hFFsubA2
          have hSf : 8 ≤ ∑ g ∈ S, (G.neighborFinset g ∩ Dᶜ).card := by
            have hsplit : (∑ g ∈ S \ FF.erase h6, (G.neighborFinset g ∩ Dᶜ).card)
                + ∑ g ∈ FF.erase h6, (G.neighborFinset g ∩ Dᶜ).card
                = ∑ g ∈ S, (G.neighborFinset g ∩ Dᶜ).card := Finset.sum_sdiff hFF'subS
            have hFF'ge : 3 * (FF.erase h6).card
                ≤ ∑ g ∈ FF.erase h6, (G.neighborFinset g ∩ Dᶜ).card := by
              have := Finset.card_nsmul_le_sum (FF.erase h6)
                (fun g => (G.neighborFinset g ∩ Dᶜ).card) 3
                (fun g hg => hFFint' g (Finset.mem_of_mem_erase hg) (Finset.ne_of_mem_erase hg))
              simpa [smul_eq_mul, Nat.mul_comm] using this
            have hSmFFge : 2 * (S \ FF.erase h6).card
                ≤ ∑ g ∈ S \ FF.erase h6, (G.neighborFinset g ∩ Dᶜ).card := by
              have := Finset.card_nsmul_le_sum (S \ FF.erase h6)
                (fun g => (G.neighborFinset g ∩ Dᶜ).card) 2
                (fun g hg => hA2int' g (Finset.mem_of_mem_erase (Finset.mem_sdiff.mp hg).1)
                  (Finset.ne_of_mem_erase (Finset.mem_sdiff.mp hg).1))
              simpa [smul_eq_mul, Nat.mul_comm] using this
            have hcard1 : (FF.erase h6).card = FF.card - 1 := Finset.card_erase_of_mem hh6FF
            have hcard2 : (S \ FF.erase h6).card + (FF.erase h6).card = S.card := by
              have := Finset.card_sdiff_add_card_inter S (FF.erase h6)
              rwa [Finset.inter_eq_right.mpr hFF'subS] at this
            omega
          have hmass : 6 ≤ ∑ g ∈ S, (G.neighborFinset g ∩ S).card := by
            have hlb := ff_internal_edge_lb_gen G Dᶜ S 10 hSsub hint10
            omega
          obtain ⟨a, b, c, haS, hbS, hcS, hab, hac, hbc⟩ := mantel_three_triangle G S hScard hmass
          have haA2 : a ∈ A2 := Finset.mem_of_mem_erase haS
          have hbA2 : b ∈ A2 := Finset.mem_of_mem_erase hbS
          have hcA2 : c ∈ A2 := Finset.mem_of_mem_erase hcS
          obtain ⟨hac1, hac2, haL2⟩ := getA2pred a haA2
          obtain ⟨hbc1, hbc2, hbL2⟩ := getA2pred b hbA2
          obtain ⟨hcc1, hcc2, hcL2⟩ := getA2pred c hcA2
          have hda := hother4 a (hA2sub haA2) (Finset.ne_of_mem_erase haS)
          have hdb := hother4 b (hA2sub hbA2) (Finset.ne_of_mem_erase hbS)
          have hdc := hother4 c (hA2sub hcA2) (Finset.ne_of_mem_erase hcS)
          exact hntri2 ⟨a, b, c, hA2sub haA2, hA2sub hbA2, hA2sub hcA2, hab, hac, hbc,
            ⟨hac1, hac2, haL2⟩, ⟨hbc1, hbc2, hbL2⟩, ⟨hcc1, hcc2, hcL2⟩, by omega⟩
        · -- `h6 ∉ A2`: clean counting with `A = A2`, `B = A1`.
          exact d10_exc_clean Dᶜ A2 A1 FF (fun g => (G.neighborFinset g ∩ Dᶜ).card) h6
            hA2sub hA1sub (by rw [hFFdef, Finset.inter_comm])
            (fun g hg => hA2int' g hg (fun e => hh6A2 (e ▸ hg)))
            (fun g hg => hFFint' g hg (fun e => hh6A2 (e ▸ hFFsubA2 hg)))
            (fun g hg hgne => hA1int' g hg hgne) hh6A2 hA2c4 hA1c4 hint10
      · -- `h6 ∉ A1`: clean counting with `A = A1`, `B = A2`.
        exact d10_exc_clean Dᶜ A1 A2 FF (fun g => (G.neighborFinset g ∩ Dᶜ).card) h6
          hA1sub hA2sub hFFdef
          (fun g hg => hA1int' g hg (fun e => hh6A1 (e ▸ hg)))
          (fun g hg => hFFint' g hg (fun e => hh6A1 (e ▸ hFFsubA1 hg)))
          (fun g hg hgne => hA2int' g hg hgne) hh6A1 hA1c4 hA2c4 hint10
    · push Not at hex6
      have hdeg5 : ∀ g : Fin 18, g ∈ Dᶜ → G.degree g ≤ 5 :=
        fun g hg => by have := hex6 g hg; omega
      have hA1int : ∀ g ∈ A1, 2 ≤ (G.neighborFinset g ∩ Dᶜ).card := by
        intro g hg
        exact avoider_internal_ge_two_pt G D Iso g L₂ (hge4 g (hA1sub hg))
          (hW g (hA1sub hg) (hdeg5 g (hA1sub hg)) (Or.inl (getA1pred g hg))) (hclassA1 g hg)
      have hA2int : ∀ g ∈ A2, 2 ≤ (G.neighborFinset g ∩ Dᶜ).card := by
        intro g hg
        exact avoider_internal_ge_two_pt G D Iso g L₁ (hge4 g (hA2sub hg))
          (hW g (hA2sub hg) (hdeg5 g (hA2sub hg)) (Or.inr (getA2pred g hg))) (hclassA2 g hg)
      have hFFint : ∀ g ∈ FF, 3 ≤ (G.neighborFinset g ∩ Dᶜ).card := by
        intro g hg
        exact fully_free_internal_ge_three_pt G D Iso g (hge4 g (hFFsub hg))
          (hW g (hFFsub hg) (hdeg5 g (hFFsub hg))
            (Or.inl (getA1pred g (hFFsubA1 hg)))) (hclassFF g hg)
      exact budget_contra_gen Dᶜ A1 A2 FF (fun g => (G.neighborFinset g ∩ Dᶜ).card) 4 10
        hA1sub hA2sub hFFdef hA1c4 hA2c4 hA1int hA2int hFFint hint10 (by omega)
  · -- **`|D| = 11`.**
    have hDc7 : Dᶜ.card = 7 := by rw [hDccard, hD11]
    have hint4 : ∑ g ∈ Dᶜ, (G.neighborFinset g ∩ Dᶜ).card = 4 := by rw [hsumInternal, hD11]
    have hdeg31 : ∑ g ∈ Dᶜ, G.degree g = 31 := by rw [hsumdeg, hD11]
    have hA1card3 : 3 ≤ A1.card := by rw [hDc7] at hA1card_lb; omega
    have hA2card3 : 3 ≤ A2.card := by rw [hDc7] at hA2card_lb; omega
    by_cases hex6 : ∃ h6 : Fin 18, h6 ∈ Dᶜ ∧ 6 ≤ G.degree h6
    · obtain ⟨h6, hh6Dc, hh6deg⟩ := hex6
      have herase : G.degree h6 + ∑ x ∈ Dᶜ.erase h6, G.degree x = 31 := by
        have h := Finset.add_sum_erase Dᶜ (fun v => G.degree v) hh6Dc
        rw [hdeg31] at h; exact h
      have hcard6 : (Dᶜ.erase h6).card = 6 := by rw [Finset.card_erase_of_mem hh6Dc, hDc7]
      have hother5 : ∀ g : Fin 18, g ∈ Dᶜ → g ≠ h6 → G.degree g ≤ 5 := by
        intro g hg hgne
        have hub := hub_deg_upper_pt (Dᶜ.erase h6) (fun v => G.degree v)
          (∑ x ∈ Dᶜ.erase h6, G.degree x)
          (fun x hx => hge4 x (Finset.mem_of_mem_erase hx)) rfl g (Finset.mem_erase.mpr ⟨hgne, hg⟩)
        rw [hcard6] at hub
        omega
      refine budget_contra_exc Dᶜ A1 A2 FF (fun g => (G.neighborFinset g ∩ Dᶜ).card) 3 4 h6
        hA1sub hA2sub hFFdef hA1card3 hA2card3 ?_ ?_ ?_ hint4 (by omega)
      · intro g hg hgne
        exact avoider_internal_ge_two_pt G D Iso g L₂ (hge4 g (hA1sub hg))
          (hW g (hA1sub hg) (hother5 g (hA1sub hg) hgne) (Or.inl (getA1pred g hg))) (hclassA1 g hg)
      · intro g hg hgne
        exact avoider_internal_ge_two_pt G D Iso g L₁ (hge4 g (hA2sub hg))
          (hW g (hA2sub hg) (hother5 g (hA2sub hg) hgne) (Or.inr (getA2pred g hg))) (hclassA2 g hg)
      · intro g hg hgne
        exact fully_free_internal_ge_three_pt G D Iso g (hge4 g (hFFsub hg))
          (hW g (hFFsub hg) (hother5 g (hFFsub hg) hgne)
            (Or.inl (getA1pred g (hFFsubA1 hg)))) (hclassFF g hg)
    · push Not at hex6
      have hdeg5 : ∀ g : Fin 18, g ∈ Dᶜ → G.degree g ≤ 5 :=
        fun g hg => by have := hex6 g hg; omega
      have hA1int : ∀ g ∈ A1, 2 ≤ (G.neighborFinset g ∩ Dᶜ).card := by
        intro g hg
        exact avoider_internal_ge_two_pt G D Iso g L₂ (hge4 g (hA1sub hg))
          (hW g (hA1sub hg) (hdeg5 g (hA1sub hg)) (Or.inl (getA1pred g hg))) (hclassA1 g hg)
      have hA2int : ∀ g ∈ A2, 2 ≤ (G.neighborFinset g ∩ Dᶜ).card := by
        intro g hg
        exact avoider_internal_ge_two_pt G D Iso g L₁ (hge4 g (hA2sub hg))
          (hW g (hA2sub hg) (hdeg5 g (hA2sub hg)) (Or.inr (getA2pred g hg))) (hclassA2 g hg)
      have hFFint : ∀ g ∈ FF, 3 ≤ (G.neighborFinset g ∩ Dᶜ).card := by
        intro g hg
        exact fully_free_internal_ge_three_pt G D Iso g (hge4 g (hFFsub hg))
          (hW g (hFFsub hg) (hdeg5 g (hFFsub hg))
            (Or.inl (getA1pred g (hFFsubA1 hg)))) (hclassFF g hg)
      exact budget_contra_gen Dᶜ A1 A2 FF (fun g => (G.neighborFinset g ∩ Dᶜ).card) 3 4
        hA1sub hA2sub hFFdef hA1card3 hA2card3 hA1int hA2int hFFint hint4 (by omega)

end N18

end ACMax
