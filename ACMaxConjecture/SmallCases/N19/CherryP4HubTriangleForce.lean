import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N19.Core
import ACMaxConjecture.SmallCases.StarCertificates
import ACMaxConjecture.SmallCases.N19.Core
import ACMaxConjecture.SmallCases.N19.HubTriangleFF
import ACMaxConjecture.SmallCases.N19.CherryP4HubTriangleWA
import ACMaxConjecture.SmallCases.N19.CherryP4HubTriangleForceD9FF4
import ACMaxConjecture.SmallCases.N19.BipartiteAvoiderTwoHub

/-!
# `|FF|`-style force for the `n = 19`, `P₄`-cherry `|D| ∈ {9, 10, 11}` hub-triangle core

`iso_rich_force_p4_nineteen` is the `|D| ∈ {9, 10, 11}` analog of `iso_rich_force_p4_seventeen`:
under the residual structural counts and the falsity of `TwoTwinConfig`, the assumption that
neither cherry admits a pairwise-adjacent avoider triple of degree sum `≤ 13` (`hntri1`, `hntri2`)
is contradictory.  The three `|D|` values are dispatched separately.

The `n = 19` internal total is `∑ int = 74 − 6|D|` (`20`/`14`/`8` for `|D| = 9`/`10`/`11`), the hub
degree total is `∑ deg = 68 − 3|D|` (`41`/`38`/`35`).

* `|D| = 11` (`8` hubs, `∑ int = 8`, avoiders `≥ 4`): clean counting (`budget_contra_gen`, with
  `budget_contra_exc` absorbing the lone degree-`≥ 6` hub).
* `|D| = 10` (`9` hubs, `∑ int = 14`, avoiders `≥ 5`): clean when all hubs have degree `≤ 5`
  (`3m = 15 > 14`).  A degree-`6` hub `h6` pins the other eight hubs to degree `4` (`38 = 6 + 8·4`);
  the anchor count on the `h6`-erased avoider sets forces `≥ 2` internally-isolated degree-`4`
  hubs, and the isolated-pair `TwoHub` machinery closes.
* `|D| = 9` (`10` hubs, `∑ int = 20`, `∑ deg = 41`, avoiders `≥ 6`): the anchor count forces an
  internally-isolated degree-`4` hub; ISO2 closes via the isolated pair, ISO1 via the `cinc h₁`
  case split (`iso1_dichotomy_to_false`, `iso1_hard_c_subcase_nineteen`,
  `twotwin_of_centre_nineteen`) — consolidated in the fully-proven `iso1_dense_corner_nineteen`.
-/

namespace ACMax

open scoped Classical

namespace N19

/-- **All-degree-`≤ 5` budget contradiction.**  Two avoider sets `A₁`, `A₂` of size `≥ m` with
internal degree `≥ 2` (and `≥ 3` on `FF = A₁ ∩ A₂`) inside a hub set `Dc` of internal total `S`
force `S ≥ 3m`; if `S < 3m` this is impossible. -/
theorem budget_contra_gen (Dc A1 A2 FF : Finset (Fin 19)) (f : Fin 19 → ℕ) (m S : ℕ)
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
theorem budget_contra_exc (Dc A1 A2 FF : Finset (Fin 19)) (f : Fin 19 → ℕ) (m S : ℕ) (h6 : Fin 19)
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

/-- **Anchor (excess-11 isolated-hub budget).**  Abstract counting lemma underlying STEP 1 of the
`|D| ∈ {9, 10}` dense-cherry corners.  If each avoider in `A1 ∪ A2` carries internal mass `≥ 2`
(`≥ 3` for fully-free avoiders `FF = A1 ∩ A2`) and the total internal mass is `S`, then the number of
`f`-isolated non-avoiders is at least `A1.card + A2.card + Dc.card − S`.  Instantiated at `|D| = 9`
(`Dc.card = 10`, `S = ∑ int = 20`, `|A1|, |A2| ≥ 6`) it yields `≥ 2` isolated hubs, hence — since
`∑ deg = 41` forces at most one degree-`5` hub — `≥ 1` internally-isolated degree-`4` hub.  This is
the GEN`= 0` guarantee: there is ALWAYS an isolated degree-`4` hub. -/
theorem anchor_isolated_count_nineteen (Dc A1 A2 FF : Finset (Fin 19)) (f : Fin 19 → ℕ) (S : ℕ)
    (hA1sub : A1 ⊆ Dc) (hA2sub : A2 ⊆ Dc) (hFF : FF = A1 ∩ A2)
    (hA1int : ∀ g ∈ A1, 2 ≤ f g) (hA2int : ∀ g ∈ A2, 2 ≤ f g) (hFFint : ∀ g ∈ FF, 3 ≤ f g)
    (hsum : ∑ g ∈ Dc, f g = S) :
    Dc.card + A1.card + A2.card ≤ S + ((Dc \ (A1 ∪ A2)).filter (fun g => f g = 0)).card := by
  classical
  have hFFsubA1 : FF ⊆ A1 := by rw [hFF]; exact Finset.inter_subset_left
  have hUsub : A1 ∪ A2 ⊆ Dc := Finset.union_subset hA1sub hA2sub
  set U := A1 ∪ A2 with hUdef
  set T := Dc \ U with hTdef
  -- Avoider internal mass lower bound `L = 2|A1∖FF| + 3|FF| + 2|A2∖A1|`.
  have hdisj : Disjoint A1 (A2 \ A1) := Finset.disjoint_sdiff
  have hunion : A1 ∪ (A2 \ A1) = U := by rw [hUdef]; exact Finset.union_sdiff_self_eq_union
  have hsplitU : ∑ g ∈ U, f g = (∑ g ∈ A1, f g) + ∑ g ∈ A2 \ A1, f g := by
    rw [← hunion, Finset.sum_union hdisj]
  have hA1split : (∑ g ∈ A1 \ FF, f g) + ∑ g ∈ FF, f g = ∑ g ∈ A1, f g :=
    Finset.sum_sdiff hFFsubA1
  have hmf : 2 * (A1 \ FF).card ≤ ∑ g ∈ A1 \ FF, f g := by
    have := Finset.card_nsmul_le_sum (A1 \ FF) f 2
      (fun g hg => hA1int g (Finset.mem_sdiff.mp hg).1)
    simpa [smul_eq_mul, Nat.mul_comm] using this
  have hFFlb : 3 * FF.card ≤ ∑ g ∈ FF, f g := by
    have := Finset.card_nsmul_le_sum FF f 3 hFFint
    simpa [smul_eq_mul, Nat.mul_comm] using this
  have hA2A1lb : 2 * (A2 \ A1).card ≤ ∑ g ∈ A2 \ A1, f g := by
    have := Finset.card_nsmul_le_sum (A2 \ A1) f 2
      (fun g hg => hA2int g (Finset.mem_sdiff.mp hg).1)
    simpa [smul_eq_mul, Nat.mul_comm] using this
  have hL : 2 * (A1 \ FF).card + 3 * FF.card + 2 * (A2 \ A1).card ≤ ∑ g ∈ U, f g := by
    rw [hsplitU, ← hA1split]; omega
  -- Card identities.
  have hcardA1 : (A1 \ FF).card + FF.card = A1.card := by
    have h := Finset.card_sdiff_add_card_inter A1 FF
    rwa [Finset.inter_eq_right.mpr hFFsubA1] at h
  have hcardA2 : (A2 \ A1).card + FF.card = A2.card := by
    have h := Finset.card_sdiff_add_card_inter A2 A1
    have hinter : A2 ∩ A1 = FF := by rw [hFF, Finset.inter_comm]
    rwa [hinter] at h
  have hcardU : U.card + FF.card = A1.card + A2.card := by
    have h := Finset.card_union_add_card_inter A1 A2
    rw [← hFF, ← hUdef] at h; omega
  have hUleDc : U.card ≤ Dc.card := Finset.card_le_card hUsub
  have hTcard : T.card = Dc.card - U.card := by
    rw [hTdef]; exact Finset.card_sdiff_of_subset hUsub
  -- Sum split over `Dc = T ∪ U`.
  have hsumsplit : (∑ g ∈ T, f g) + ∑ g ∈ U, f g = ∑ g ∈ Dc, f g := by
    rw [hTdef]; exact Finset.sum_sdiff hUsub
  rw [hsum] at hsumsplit
  -- Isolated / non-isolated split of `T`.
  set iso := T.filter (fun g => f g = 0) with hisodef
  set non := T.filter (fun g => ¬ f g = 0) with hnondef
  have hTfilter : iso.card + non.card = T.card :=
    Finset.card_filter_add_card_filter_not (s := T) (p := fun g => f g = 0)
  have hnonsum : non.card ≤ ∑ g ∈ T, f g := by
    have hcard_eq : non.card = ∑ _g ∈ non, 1 := by
      rw [Finset.sum_const, smul_eq_mul, Nat.mul_one]
    rw [hcard_eq]
    calc ∑ _g ∈ non, 1 ≤ ∑ g ∈ non, f g := by
            apply Finset.sum_le_sum; intro g hg
            rw [hnondef, Finset.mem_filter] at hg; omega
      _ ≤ ∑ g ∈ T, f g := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  omega

/-- **ISO1 dichotomy → `False` (the complete structural assembly, axiom-clean).**
Given the extracted isolated degree-`4` hub `h₁` (with `2 ≤ cinc h₁`) and the unique degree-`5`
hub `h₅` in a `|D| = 9` ISO1 configuration, the sharp counting dichotomy
`iso1_intdeg_dichotomy_nineteen` yields either a cherry-free `≥ 2`-`Iso` hub (a `TwoTwinConfig`
centre, contradicting `htt`) or a degree-`4` partner `h₂ ≠ h₁` of internal degree `≤ 1`.  In the
second case the isolated-hub share bound `isolated_deg4_share_le_one` keeps `≥ 3` private leaves on
`h₁` and `≥ 2` private degree-`3` leaves on `h₂`, and the cross non-adjacencies discharge from
`Iso`-isolation together with the `P₄` distance-`2` facts (`¬G.Adj L₁ c₂`, `¬G.Adj L₂ c₁`,
`¬G.Adj L₁ L₂`); the *only* structurally-dangerous cross pair `(L, c)` is avoided using the fact
that `h₂` cannot meet both `c₁` and `c₂` (that would be a good triangle `h₂–c₁–c₂` of degree sum
`10`, excluded by `hT`).  Assembling via `two_hub_cherry_pair_nineteen` gives a `TwoHubConfig`,
contradicting `hth`.  This is the axiom-clean realisation of the two structural steps (name-extraction
interface + disjunct assembly); the input `2 ≤ cinc h₁` is supplied by the ISO1 `cinc` dispatch
inside `iso1_dense_corner_nineteen`. -/
theorem iso1_dichotomy_to_false (G : SimpleGraph (Fin 19))
    (D Iso : Finset (Fin 19)) (L₁ c₁ c₂ L₂ h₁ h₅ : Fin 19)
    (hmemD : ∀ v : Fin 19, v ∈ D ↔ G.degree v = 3)
    (_hIsoD : Iso ⊆ D)
    (hIsoprop : ∀ v ∈ Iso, G.degree v = 3 ∧ (∀ w : Fin 19, G.Adj v w → G.degree w ≠ 3))
    (hclassP : ∀ x : Fin 19, x ∈ D → x = L₁ ∨ x = c₁ ∨ x = c₂ ∨ x = L₂ ∨ x ∈ Iso)
    (hL1deg : G.degree L₁ = 3) (hc1deg : G.degree c₁ = 3)
    (hc2deg : G.degree c₂ = 3) (hL2deg : G.degree L₂ = 3)
    (hac1L1 : G.Adj c₁ L₁) (hc12 : G.Adj c₁ c₂) (hac2L2 : G.Adj c₂ L₂)
    (hL1nc2 : L₁ ≠ c₂) (hL2nc1 : L₂ ≠ c₁)
    (hNc1D : G.neighborFinset c₁ ∩ D = {c₂, L₁}) (hNc2D : G.neighborFinset c₂ ∩ D = {c₁, L₂})
    (hL1D : L₁ ∈ D) (hc1D : c₁ ∈ D) (hc2D : c₂ ∈ D) (hL2D : L₂ ∈ D)
    (htt : ¬TwoTwinConfig G) (hth : ¬TwoHubConfig G)
    (hT : ¬∃ x y z : Fin 19, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    (hC4 : ¬∃ a b c d : Fin 19, ({a, b, c, d} : Finset (Fin 19)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (hHub10 : Dᶜ.card = 10)
    (hdeg_up : ∀ h : Fin 19, h ∈ Dᶜ → G.degree h ≤ 5)
    (hdecomp : ∀ h : Fin 19, h ∈ Dᶜ →
      (G.neighborFinset h ∩ ({L₁, c₁, c₂, L₂} : Finset (Fin 19))).card
        + (G.neighborFinset h ∩ Iso).card + (G.neighborFinset h ∩ Dᶜ).card = G.degree h)
    (hsumIso15 : ∑ h ∈ Dᶜ, (G.neighborFinset h ∩ Iso).card = 15)
    (hh1Dc : h₁ ∈ Dᶜ) (hh1d : G.degree h₁ = 4) (hh1iso : G.neighborFinset h₁ ∩ Dᶜ = ∅)
    (hh1cinc : 2 ≤ (G.neighborFinset h₁ ∩ ({L₁, c₁, c₂, L₂} : Finset (Fin 19))).card)
    (hh5Dc : h₅ ∈ Dᶜ) (hh5d : G.degree h₅ = 5) (hne15 : h₁ ≠ h₅)
    (hdegOth : ∀ h : Fin 19, h ∈ Dᶜ → h ≠ h₁ → h ≠ h₅ → G.degree h = 4) :
    False := by
  classical
  set P : Finset (Fin 19) := {L₁, c₁, c₂, L₂} with hPdef
  -- `Iso` vertices meet no degree-`3` vertex.
  have hIso_nadj : ∀ t : Fin 19, t ∈ Iso → ∀ w : Fin 19, G.degree w = 3 → ¬G.Adj t w :=
    fun t ht w hw hadj => (hIsoprop t ht).2 w hadj hw
  -- `L₁ ≠ L₂` via the good triangle `c₁–c₂–L₁` (using `he : L₁ = L₂`).
  have hL1L2 : L₁ ≠ L₂ := by
    intro he
    exact hT ⟨c₁, c₂, L₁, G.ne_of_adj hc12, he.symm ▸ G.ne_of_adj hac2L2,
      G.ne_of_adj hac1L1, hc12, he.symm ▸ hac2L2, hac1L1, by omega⟩
  -- Cherry `P₄` non-adjacencies.
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
  have hPnotIso : ∀ x : Fin 19, x ∈ P → x ∉ Iso := by
    intro x hx hxIso
    simp only [hPdef, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact (hIsoprop x hxIso).2 c₁ hac1L1.symm hc1deg
    · exact (hIsoprop x hxIso).2 c₂ hc12 hc2deg
    · exact (hIsoprop x hxIso).2 c₁ hc12.symm hc1deg
    · exact (hIsoprop x hxIso).2 c₂ hac2L2.symm hc2deg
  -- `h₁`'s neighbourhood: both leaves and no `c`.
  have hbad1 := deg4_path_bad_of_two G L₁ c₁ c₂ L₂ h₁ hT hC4 hac1L1 hc12 hac2L2 hnc1L2 hnc2L1
    hL1nc2 hL2nc1 hL1deg hc1deg hc2deg hL2deg hh1d hh1cinc
  obtain ⟨hAdjh1L1, hAdjh1L2, hnh1c1, hnh1c2⟩ := hbad1
  -- `¬ G.Adj L₁ L₂` from the good triangle `h₁–L₁–L₂`.
  have hnL1L2 : ¬G.Adj L₁ L₂ := by
    intro hadj
    exact hT ⟨h₁, L₁, L₂, G.ne_of_adj hAdjh1L1, hL1L2, G.ne_of_adj hAdjh1L2,
      hAdjh1L1, hadj, hAdjh1L2, by rw [hh1d, hL1deg, hL2deg]⟩
  -- `L₁`'s / `L₂`'s only degree-`3` neighbour is `c₁` / `c₂`.
  have hL1only : ∀ w : Fin 19, G.Adj L₁ w → G.degree w = 3 → w = c₁ := by
    intro w hadj hw
    have hwD : w ∈ D := (hmemD w).mpr hw
    rcases hclassP w hwD with h | h | h | h | h
    · exact absurd (h ▸ hadj) G.irrefl
    · exact h
    · exact absurd (h ▸ hadj) (fun ha => hnc2L1 ha.symm)
    · exact absurd (h ▸ hadj) hnL1L2
    · exact absurd hadj (fun ha => (hIsoprop w h).2 L₁ ha.symm hL1deg)
  have hL2only : ∀ w : Fin 19, G.Adj L₂ w → G.degree w = 3 → w = c₂ := by
    intro w hadj hw
    have hwD : w ∈ D := (hmemD w).mpr hw
    rcases hclassP w hwD with h | h | h | h | h
    · exact absurd (h ▸ hadj) (fun ha => hnL1L2 ha.symm)
    · exact absurd (h ▸ hadj) (fun ha => hnc1L2 ha.symm)
    · exact h
    · exact absurd (h ▸ hadj) G.irrefl
    · exact absurd hadj (fun ha => (hIsoprop w h).2 L₂ ha.symm hL2deg)
  -- `N h₁ ⊆ D` and its membership characterisation.
  have hN1subD : G.neighborFinset h₁ ⊆ D := by
    intro x hx
    by_contra hxD
    have hmem : x ∈ G.neighborFinset h₁ ∩ Dᶜ :=
      Finset.mem_inter.mpr ⟨hx, Finset.mem_compl.mpr hxD⟩
    rw [hh1iso] at hmem; exact absurd hmem (Finset.notMem_empty x)
  have hN1char : ∀ x : Fin 19, x ∈ G.neighborFinset h₁ → x = L₁ ∨ x = L₂ ∨ x ∈ Iso := by
    intro x hx
    have hadj : G.Adj h₁ x := (G.mem_neighborFinset h₁ x).mp hx
    rcases hclassP x (hN1subD hx) with h | h | h | h | h
    · exact Or.inl h
    · exact absurd (h ▸ hadj) hnh1c1
    · exact absurd (h ▸ hadj) hnh1c2
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  have hdeg3 : ∀ x : Fin 19, x ∈ G.neighborFinset h₁ → G.degree x = 3 :=
    fun x hx => (hmemD x).mp (hN1subD hx)
  have hindep : ∀ x : Fin 19, x ∈ G.neighborFinset h₁ → ∀ y : Fin 19, y ∈ G.neighborFinset h₁ →
      x ≠ y → ¬G.Adj x y := by
    intro x hx y hy hxy hadj
    rcases hN1char x hx with hx1 | hx2 | hxI
    · rcases hN1char y hy with hy1 | hy2 | hyI
      · exact hxy (hx1.trans hy1.symm)
      · exact hnL1L2 (hx1 ▸ hy2 ▸ hadj)
      · exact hIso_nadj y hyI x (hdeg3 x hx) hadj.symm
    · rcases hN1char y hy with hy1 | hy2 | hyI
      · exact hnL1L2 (hy1 ▸ hx2 ▸ hadj.symm)
      · exact hxy (hx2.trans hy2.symm)
      · exact hIso_nadj y hyI x (hdeg3 x hx) hadj.symm
    · exact hIso_nadj x hxI y (hdeg3 y hy) hadj
  -- Apply the counting dichotomy.
  have h1int0 : (G.neighborFinset h₁ ∩ Dᶜ).card = 0 := by rw [hh1iso]; exact Finset.card_empty
  have hdich := iso1_intdeg_dichotomy_nineteen G Dᶜ Iso P h₁ h₅ hHub10 hh1Dc hh5Dc hne15
    hh1d hh5d hdegOth hdecomp hsumIso15 hh1cinc h1int0
  rcases hdich with ⟨hc, hcHub, hccinc0, hcisoge2⟩ | ⟨h₂, hh2Hub, hne2, hh2deg, hh2int⟩
  · -- **Disjunct 1** — a cherry-free `≥ 2`-`Iso` hub `hc` is a `TwoTwinConfig` centre.
    obtain ⟨t₁, ht1, t₂, ht2, ht12⟩ := Finset.one_lt_card.mp (by omega : 1 < (G.neighborFinset hc ∩ Iso).card)
    obtain ⟨ht1N, ht1Iso⟩ := Finset.mem_inter.mp ht1
    obtain ⟨ht2N, ht2Iso⟩ := Finset.mem_inter.mp ht2
    have hAdj_ct1 : G.Adj hc t₁ := (G.mem_neighborFinset hc t₁).mp ht1N
    have hAdj_ct2 : G.Adj hc t₂ := (G.mem_neighborFinset hc t₂).mp ht2N
    have hdegt1 : G.degree t₁ = 3 := (hIsoprop t₁ ht1Iso).1
    have hdegt2 : G.degree t₂ = 3 := (hIsoprop t₂ ht2Iso).1
    have hNhP : G.neighborFinset hc ∩ P = ∅ := Finset.card_eq_zero.mp hccinc0
    have hnhc_of : ∀ w : Fin 19, w ∈ P → ¬G.Adj hc w := by
      intro w hw hadj
      have : w ∈ G.neighborFinset hc ∩ P :=
        Finset.mem_inter.mpr ⟨(G.mem_neighborFinset hc w).mpr hadj, hw⟩
      rw [hNhP] at this; exact absurd this (Finset.notMem_empty w)
    have hnhc1 : ¬G.Adj hc c₁ := hnhc_of c₁ (by simp [hPdef])
    have hnhc2 : ¬G.Adj hc c₂ := hnhc_of c₂ (by simp [hPdef])
    have hnhcL2 : ¬G.Adj hc L₂ := hnhc_of L₂ (by simp [hPdef])
    have hc_notD : hc ∉ D := Finset.mem_compl.mp hcHub
    have ht1_neP : ∀ w : Fin 19, w ∈ P → t₁ ≠ w := fun w hw he => hPnotIso w hw (he ▸ ht1Iso)
    have ht2_neP : ∀ w : Fin 19, w ∈ P → t₂ ≠ w := fun w hw he => hPnotIso w hw (he ▸ ht2Iso)
    exact htt ⟨t₁, t₂, hc, c₁, c₂, L₂, hdegt1, hdegt2, hdeg_up hc hcHub, hc1deg, hc2deg, hL2deg,
      hAdj_ct1.symm, hAdj_ct2.symm, hc12, hac2L2,
      (fun ha => hIso_nadj t₁ ht1Iso c₁ hc1deg ha), (fun ha => hIso_nadj t₁ ht1Iso c₂ hc2deg ha),
      (fun ha => hIso_nadj t₁ ht1Iso L₂ hL2deg ha),
      (fun ha => hIso_nadj t₂ ht2Iso c₁ hc1deg ha), (fun ha => hIso_nadj t₂ ht2Iso c₂ hc2deg ha),
      (fun ha => hIso_nadj t₂ ht2Iso L₂ hL2deg ha),
      hnhc1, hnhc2, hnhcL2, ht12,
      ht1_neP c₁ (by simp [hPdef]), ht1_neP c₂ (by simp [hPdef]), ht1_neP L₂ (by simp [hPdef]),
      ht2_neP c₁ (by simp [hPdef]), ht2_neP c₂ (by simp [hPdef]), ht2_neP L₂ (by simp [hPdef]),
      (fun he => hc_notD (he ▸ hc1D)), (fun he => hc_notD (he ▸ hc2D)),
      (fun he => hc_notD (he ▸ hL2D)),
      G.ne_of_adj hc12, G.ne_of_adj hac2L2, hL2nc1.symm⟩
  · -- **Disjunct 2** — a degree-`4` partner `h₂` of internal degree `≤ 1` yields a `TwoHubConfig`.
    have hnadj12 : ¬G.Adj h₁ h₂ := by
      intro ha
      have : h₂ ∈ G.neighborFinset h₁ ∩ Dᶜ :=
        Finset.mem_inter.mpr ⟨(G.mem_neighborFinset h₁ h₂).mpr ha, hh2Hub⟩
      rw [hh1iso] at this; exact absurd this (Finset.notMem_empty h₂)
    have hshare := isolated_deg4_share_le_one G h₁ h₂ hC4 hh1d hh2deg (Ne.symm hne2) hnadj12
      hdeg3 hindep
    -- `Iso`-neighbours of `h₁`: exactly `2`.
    have hIe2 : (G.neighborFinset h₁ ∩ Iso).card = 2 := by
      have hdech1 := hdecomp h₁ hh1Dc
      -- cinc = 2 (from `hh1cinc` and `deg4_path_bad`), intdeg = 0.
      have hcinc2 : (G.neighborFinset h₁ ∩ P).card = 2 := by
        have hsub : ({L₁, L₂} : Finset (Fin 19)) ⊆ G.neighborFinset h₁ ∩ P := by
          intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset h₁ x).mpr hAdjh1L1, by simp [hPdef]⟩
          · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset h₁ x).mpr hAdjh1L2, by simp [hPdef]⟩
        have hle : (G.neighborFinset h₁ ∩ P).card ≤ 2 := by
          have hsubP : G.neighborFinset h₁ ∩ P ⊆ {L₁, L₂} := by
            intro x hx
            obtain ⟨hxN, hxP⟩ := Finset.mem_inter.mp hx
            rcases hN1char x hxN with h | h | h
            · simp [h]
            · simp [h]
            · exact absurd (Finset.mem_inter.mpr ⟨hxN, hxP⟩) (by
                have := hPnotIso x hxP; exact fun _ => this h)
          have := Finset.card_le_card hsubP
          have h2 : ({L₁, L₂} : Finset (Fin 19)).card = 2 := by
            rw [Finset.card_insert_of_notMem (by simp [hL1L2]), Finset.card_singleton]
          omega
        have := Finset.card_le_card hsub
        have h2 : ({L₁, L₂} : Finset (Fin 19)).card = 2 := by
          rw [Finset.card_insert_of_notMem (by simp [hL1L2]), Finset.card_singleton]
        omega
      rw [hcinc2, h1int0, hh1d] at hdech1; omega
    -- `h₂` has `≥ 3` degree-`3` neighbours.
    have hN2D_card : 3 ≤ (G.neighborFinset h₂ ∩ D).card := by
      have hdisj : Disjoint (G.neighborFinset h₂ ∩ D) (G.neighborFinset h₂ ∩ Dᶜ) := by
        apply Finset.disjoint_left.mpr; intro a ha hb
        exact (Finset.mem_compl.mp (Finset.mem_inter.mp hb).2) (Finset.mem_inter.mp ha).2
      have hunion : (G.neighborFinset h₂ ∩ D) ∪ (G.neighborFinset h₂ ∩ Dᶜ) = G.neighborFinset h₂ := by
        rw [← Finset.inter_union_distrib_left, Finset.union_compl, Finset.inter_univ]
      have hsum : (G.neighborFinset h₂ ∩ D).card + (G.neighborFinset h₂ ∩ Dᶜ).card = G.degree h₂ := by
        rw [← Finset.card_union_of_disjoint hdisj, hunion, G.card_neighborFinset_eq_degree]
      omega
    -- `h₂`'s private degree-`3` neighbours: at least `2`.
    have hQ2card : 2 ≤ ((G.neighborFinset h₂ ∩ D) \ G.neighborFinset h₁).card := by
      have hsplit := Finset.card_sdiff_add_card_inter (G.neighborFinset h₂ ∩ D) (G.neighborFinset h₁)
      have hsub : (G.neighborFinset h₂ ∩ D) ∩ G.neighborFinset h₁
          ⊆ G.neighborFinset h₁ ∩ G.neighborFinset h₂ := by
        intro x hx
        obtain ⟨hxND, hxN1⟩ := Finset.mem_inter.mp hx
        exact Finset.mem_inter.mpr ⟨hxN1, (Finset.mem_inter.mp hxND).1⟩
      have := Finset.card_le_card hsub
      omega
    obtain ⟨c, hcQ, d, hdQ, hcd⟩ := Finset.one_lt_card.mp (by omega : 1 < ((G.neighborFinset h₂ ∩ D) \ G.neighborFinset h₁).card)
    obtain ⟨hcND, hcN1⟩ := Finset.mem_sdiff.mp hcQ
    obtain ⟨hdND, hdN1⟩ := Finset.mem_sdiff.mp hdQ
    obtain ⟨hcN2, hcD⟩ := Finset.mem_inter.mp hcND
    obtain ⟨hdN2, hdD⟩ := Finset.mem_inter.mp hdND
    -- The closing assembly, given a valid `(a, b)` leaf pair for `h₁`.
    have finish : ∀ a b : Fin 19, a ∈ Iso → a ∈ G.neighborFinset h₁ → a ∉ G.neighborFinset h₂ →
        b ∈ G.neighborFinset h₁ → b ∉ G.neighborFinset h₂ → G.degree b = 3 → a ≠ b →
        ¬G.Adj b c → ¬G.Adj b d → False := by
      intro a b haI haN1 haN2 hbN1 hbN2 hbdeg hab hnbc hnbd
      apply hth
      have hdega : G.degree a = 3 := (hIsoprop a haI).1
      have hdegc : G.degree c = 3 := (hmemD c).mp hcD
      have hdegd : G.degree d = 3 := (hmemD d).mp hdD
      have hah1 : G.Adj a h₁ := ((G.mem_neighborFinset h₁ a).mp haN1).symm
      have hbh1 : G.Adj b h₁ := ((G.mem_neighborFinset h₁ b).mp hbN1).symm
      have hch2 : G.Adj c h₂ := ((G.mem_neighborFinset h₂ c).mp hcN2).symm
      have hdh2 : G.Adj d h₂ := ((G.mem_neighborFinset h₂ d).mp hdN2).symm
      have hn_ah2 : ¬G.Adj a h₂ := fun ha => haN2 ((G.mem_neighborFinset h₂ a).mpr ha.symm)
      have hn_bh2 : ¬G.Adj b h₂ := fun ha => hbN2 ((G.mem_neighborFinset h₂ b).mpr ha.symm)
      have hn_h1c : ¬G.Adj h₁ c := fun ha => hcN1 ((G.mem_neighborFinset h₁ c).mpr ha)
      have hn_h1d : ¬G.Adj h₁ d := fun ha => hdN1 ((G.mem_neighborFinset h₁ d).mpr ha)
      have hn_ac : ¬G.Adj a c := fun ha => (hIsoprop a haI).2 c ha hdegc
      have hn_ad : ¬G.Adj a d := fun ha => (hIsoprop a haI).2 d ha hdegd
      have hne_ac : a ≠ c := fun he => haN2 (he.symm ▸ hcN2)
      have hne_ad : a ≠ d := fun he => haN2 (he.symm ▸ hdN2)
      have hne_bc : b ≠ c := fun he => hbN2 (he.symm ▸ hcN2)
      have hne_bd : b ≠ d := fun he => hbN2 (he.symm ▸ hdN2)
      exact two_hub_cherry_pair_nineteen G h₁ h₂ a b c d hh1d hh2deg hdega hbdeg hdegc hdegd
        hah1 hbh1 hch2 hdh2 hnadj12 hn_h1c hn_h1d hn_ah2 hn_bh2 hn_ac hn_ad hnbc hnbd
        hab hcd hne_ac hne_ad hne_bc hne_bd
    -- Private `Iso`-neighbours of `h₁`: at least `1`.
    have hpriv_iso : 1 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card := by
      have hsplit := Finset.card_sdiff_add_card_inter (G.neighborFinset h₁ ∩ Iso) (G.neighborFinset h₂)
      have hsub : (G.neighborFinset h₁ ∩ Iso) ∩ G.neighborFinset h₂
          ⊆ G.neighborFinset h₁ ∩ G.neighborFinset h₂ := by
        intro x hx
        obtain ⟨hxNI, hxN2⟩ := Finset.mem_inter.mp hx
        exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hxNI).1, hxN2⟩
      have := Finset.card_le_card hsub
      rw [hIe2] at hsplit
      omega
    by_cases hcaseA : 2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card
    · -- **Case A** — both `Iso`-neighbours of `h₁` are private; both leaves are `Iso`.
      obtain ⟨a, haM, b, hbM, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card)
      obtain ⟨haNI, haN2⟩ := Finset.mem_sdiff.mp haM
      obtain ⟨hbNI, hbN2⟩ := Finset.mem_sdiff.mp hbM
      obtain ⟨haN1, haI⟩ := Finset.mem_inter.mp haNI
      obtain ⟨hbN1, hbI⟩ := Finset.mem_inter.mp hbNI
      have hdegc : G.degree c = 3 := (hmemD c).mp hcD
      have hdegd : G.degree d = 3 := (hmemD d).mp hdD
      exact finish a b haI haN1 haN2 hbN1 hbN2 (hIsoprop b hbI).1 hab
        (fun ha => (hIsoprop b hbI).2 c ha hdegc) (fun ha => (hIsoprop b hbI).2 d ha hdegd)
    · -- **Case B** — one `Iso`-neighbour of `h₁` is shared; `L₁, L₂ ∉ N h₂`; leaf `b ∈ {L₁, L₂}`.
      have hpriv1 : ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card = 1 := by omega
      obtain ⟨a, haM⟩ := Finset.card_eq_one.mp hpriv1
      have haMem : a ∈ (G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂ := by rw [haM]; simp
      obtain ⟨haNI, haN2⟩ := Finset.mem_sdiff.mp haMem
      obtain ⟨haN1, haI⟩ := Finset.mem_inter.mp haNI
      -- `L₁, L₂ ∉ N h₂` (else the share would exceed `1`).
      have hshareIso : 1 ≤ ((G.neighborFinset h₁ ∩ Iso) ∩ G.neighborFinset h₂).card := by
        have hsplit := Finset.card_sdiff_add_card_inter (G.neighborFinset h₁ ∩ Iso) (G.neighborFinset h₂)
        rw [hIe2, hpriv1] at hsplit; omega
      obtain ⟨s, hsMem⟩ := Finset.card_pos.mp (by omega : 0 < ((G.neighborFinset h₁ ∩ Iso) ∩ G.neighborFinset h₂).card)
      obtain ⟨hsNI, hsN2⟩ := Finset.mem_inter.mp hsMem
      obtain ⟨hsN1, hsI⟩ := Finset.mem_inter.mp hsNI
      have hLnotN2 : ∀ L : Fin 19, G.Adj h₁ L → L ∉ Iso → L ∉ G.neighborFinset h₂ := by
        intro L hadjL hLIso hLN2
        have hLN1 : L ∈ G.neighborFinset h₁ := (G.mem_neighborFinset h₁ L).mpr hadjL
        have hne_Ls : L ≠ s := fun he => hLIso (he ▸ hsI)
        have h2mem : ({L, s} : Finset (Fin 19)) ⊆ G.neighborFinset h₁ ∩ G.neighborFinset h₂ := by
          intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact Finset.mem_inter.mpr ⟨hLN1, hLN2⟩
          · exact Finset.mem_inter.mpr ⟨hsN1, hsN2⟩
        have hc2 : ({L, s} : Finset (Fin 19)).card = 2 := by
          rw [Finset.card_insert_of_notMem (by simp [hne_Ls]), Finset.card_singleton]
        have := Finset.card_le_card h2mem; omega
      have hL1N2 : L₁ ∉ G.neighborFinset h₂ := hLnotN2 L₁ hAdjh1L1 (fun h => hPnotIso L₁ (by simp [hPdef]) h)
      have hL2N2 : L₂ ∉ G.neighborFinset h₂ := hLnotN2 L₂ hAdjh1L2 (fun h => hPnotIso L₂ (by simp [hPdef]) h)
      have hL1N1 : L₁ ∈ G.neighborFinset h₁ := (G.mem_neighborFinset h₁ L₁).mpr hAdjh1L1
      have hL2N1 : L₂ ∈ G.neighborFinset h₁ := (G.mem_neighborFinset h₁ L₂).mpr hAdjh1L2
      have haL1 : a ≠ L₁ := fun he => hPnotIso L₁ (by simp [hPdef]) (he ▸ haI)
      have haL2 : a ≠ L₂ := fun he => hPnotIso L₂ (by simp [hPdef]) (he ▸ haI)
      -- `h₂` cannot meet both `c₁` and `c₂` (good triangle `h₂–c₁–c₂`).
      have hnotboth : ¬(G.Adj h₂ c₁ ∧ G.Adj h₂ c₂) := by
        rintro ⟨hp, hq⟩
        have hh2c1 : h₂ ≠ c₁ := fun he => (Finset.mem_compl.mp hh2Hub) (he ▸ hc1D)
        have hh2c2 : h₂ ≠ c₂ := fun he => (Finset.mem_compl.mp hh2Hub) (he ▸ hc2D)
        exact hT ⟨h₂, c₁, c₂, hh2c1, G.ne_of_adj hc12, hh2c2, hp, hc12, hq, by omega⟩
      by_cases hh2c1 : G.Adj h₂ c₁
      · -- `¬G.Adj h₂ c₂`; use `b = L₂` (`L₂`'s only degree-`3` neighbour is `c₂ ∉ N h₂`).
        have hc2N2 : c₂ ∉ G.neighborFinset h₂ :=
          fun hm => (hnotboth ⟨hh2c1, (G.mem_neighborFinset h₂ c₂).mp hm⟩)
        have hnbc : ¬G.Adj L₂ c := by
          intro ha
          have := hL2only c ha ((hmemD c).mp hcD)
          exact hc2N2 (this ▸ hcN2)
        have hnbd : ¬G.Adj L₂ d := by
          intro ha
          have := hL2only d ha ((hmemD d).mp hdD)
          exact hc2N2 (this ▸ hdN2)
        exact finish a L₂ haI haN1 haN2 hL2N1 hL2N2 hL2deg haL2 hnbc hnbd
      · -- `¬G.Adj h₂ c₁`; use `b = L₁` (`L₁`'s only degree-`3` neighbour is `c₁ ∉ N h₂`).
        have hc1N2 : c₁ ∉ G.neighborFinset h₂ :=
          fun hm => hh2c1 ((G.mem_neighborFinset h₂ c₁).mp hm)
        have hnbc : ¬G.Adj L₁ c := by
          intro ha
          have := hL1only c ha ((hmemD c).mp hcD)
          exact hc1N2 (this ▸ hcN2)
        have hnbd : ¬G.Adj L₁ d := by
          intro ha
          have := hL1only d ha ((hmemD d).mp hdD)
          exact hc1N2 (this ▸ hdN2)
        exact finish a L₁ haI haN1 haN2 hL1N1 hL1N2 hL1deg haL1 hnbc hnbd

/-- **`|D| = 9` ISO1 hard-`c` subcase, Case I — a low-internal-degree deg-`4` partner ⟹ `TwoHubConfig`.**

The isolated degree-`4` hub `h₁` has an independent degree-`3` neighbourhood (its `4` neighbours are
`c₁` plus `3` `Iso` vertices — `c₁` meets no `Iso` and the `Iso` vertices meet no degree-`3` vertex,
so all pairs are non-adjacent) with `≥ 3` `Iso`-neighbours.  Given ANY other degree-`4` hub `k` of
internal degree `≤ 1`, `isolated_deg4_share_le_one` bounds `|N h₁ ∩ N k| ≤ 1`, so `h₁` keeps `≥ 2`
private `Iso`-neighbours and `k` keeps `≥ 2` private degree-`3` leaves.  Feeding `h₁`'s two private
`Iso`-leaves and `k`'s two private leaves to `two_hub_cherry_pair_nineteen` assembles a
`TwoHubConfig`: every cross non-adjacency is automatic — the `Iso`-leaves meet no degree-`3` vertex
and both private families avoid the opposite hub. -/
theorem iso1_d9_caseI_nineteen (G : SimpleGraph (Fin 19))
    (D Iso : Finset (Fin 19)) (h₁ k : Fin 19)
    (hmemD : ∀ v : Fin 19, v ∈ D ↔ G.degree v = 3)
    (hIsoprop : ∀ v ∈ Iso, G.degree v = 3 ∧ (∀ w : Fin 19, G.Adj v w → G.degree w ≠ 3))
    (hth : ¬TwoHubConfig G)
    (hC4 : ¬∃ a b c d : Fin 19, ({a, b, c, d} : Finset (Fin 19)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (hh1d : G.degree h₁ = 4) (hh1iso : G.neighborFinset h₁ ∩ Dᶜ = ∅)
    (hindep : ∀ x ∈ G.neighborFinset h₁, ∀ y ∈ G.neighborFinset h₁, x ≠ y → ¬G.Adj x y)
    (hisoinc3 : 3 ≤ (G.neighborFinset h₁ ∩ Iso).card)
    (hkDc : k ∈ Dᶜ) (hkne : k ≠ h₁) (hkd : G.degree k = 4)
    (hkint : (G.neighborFinset k ∩ Dᶜ).card ≤ 1) :
    False := by
  classical
  -- `N h₁ ⊆ D` and its vertices have degree `3`.
  have hN1subD : G.neighborFinset h₁ ⊆ D := by
    intro x hx
    by_contra hxD
    have hmem : x ∈ G.neighborFinset h₁ ∩ Dᶜ :=
      Finset.mem_inter.mpr ⟨hx, Finset.mem_compl.mpr hxD⟩
    rw [hh1iso] at hmem; exact absurd hmem (Finset.notMem_empty x)
  have hdeg3 : ∀ x ∈ G.neighborFinset h₁, G.degree x = 3 :=
    fun x hx => (hmemD x).mp (hN1subD hx)
  -- `h₁` is non-adjacent to the hub `k` (it is internally isolated).
  have hnadj1k : ¬G.Adj h₁ k := by
    intro ha
    have : k ∈ G.neighborFinset h₁ ∩ Dᶜ :=
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset h₁ k).mpr ha, hkDc⟩
    rw [hh1iso] at this; exact absurd this (Finset.notMem_empty k)
  -- Shared-neighbour bound.
  have hshare := isolated_deg4_share_le_one G h₁ k hC4 hh1d hkd (Ne.symm hkne) hnadj1k hdeg3 hindep
  -- `k` has `≥ 3` degree-`3` neighbours (`intdeg k ≤ 1`).
  have hkD3 : 3 ≤ (G.neighborFinset k ∩ D).card := by
    have hdisj : Disjoint (G.neighborFinset k ∩ D) (G.neighborFinset k ∩ Dᶜ) := by
      apply Finset.disjoint_left.mpr; intro a ha hb
      exact (Finset.mem_compl.mp (Finset.mem_inter.mp hb).2) (Finset.mem_inter.mp ha).2
    have hunion : (G.neighborFinset k ∩ D) ∪ (G.neighborFinset k ∩ Dᶜ) = G.neighborFinset k := by
      rw [← Finset.inter_union_distrib_left, Finset.union_compl, Finset.inter_univ]
    have hsum : (G.neighborFinset k ∩ D).card + (G.neighborFinset k ∩ Dᶜ).card = G.degree k := by
      rw [← Finset.card_union_of_disjoint hdisj, hunion, G.card_neighborFinset_eq_degree]
    omega
  -- `h₁`'s private `Iso`-neighbours: `≥ 2`.
  have hpriv_iso : 2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset k).card := by
    have hsplit := Finset.card_sdiff_add_card_inter (G.neighborFinset h₁ ∩ Iso) (G.neighborFinset k)
    have hsub : (G.neighborFinset h₁ ∩ Iso) ∩ G.neighborFinset k
        ⊆ G.neighborFinset h₁ ∩ G.neighborFinset k := by
      intro x hx
      obtain ⟨hxNI, hxNk⟩ := Finset.mem_inter.mp hx
      exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hxNI).1, hxNk⟩
    have := Finset.card_le_card hsub
    omega
  -- `k`'s private degree-`3` leaves: `≥ 2`.
  have hpriv_leaf : 2 ≤ ((G.neighborFinset k ∩ D) \ G.neighborFinset h₁).card := by
    have hsplit := Finset.card_sdiff_add_card_inter (G.neighborFinset k ∩ D) (G.neighborFinset h₁)
    have hsub : (G.neighborFinset k ∩ D) ∩ G.neighborFinset h₁
        ⊆ G.neighborFinset h₁ ∩ G.neighborFinset k := by
      intro x hx
      obtain ⟨hxND, hxN1⟩ := Finset.mem_inter.mp hx
      exact Finset.mem_inter.mpr ⟨hxN1, (Finset.mem_inter.mp hxND).1⟩
    have := Finset.card_le_card hsub
    omega
  -- Extract the two private `Iso`-leaves of `h₁` and the two private leaves of `k`.
  obtain ⟨a, haM, b, hbM, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset k).card)
  obtain ⟨haNI, haNk⟩ := Finset.mem_sdiff.mp haM
  obtain ⟨hbNI, hbNk⟩ := Finset.mem_sdiff.mp hbM
  obtain ⟨haN1, haI⟩ := Finset.mem_inter.mp haNI
  obtain ⟨hbN1, hbI⟩ := Finset.mem_inter.mp hbNI
  obtain ⟨c, hcM, d, hdM, hcd⟩ := Finset.one_lt_card.mp (by omega : 1 < ((G.neighborFinset k ∩ D) \ G.neighborFinset h₁).card)
  obtain ⟨hcND, hcN1⟩ := Finset.mem_sdiff.mp hcM
  obtain ⟨hdND, hdN1⟩ := Finset.mem_sdiff.mp hdM
  obtain ⟨hcNk, hcD⟩ := Finset.mem_inter.mp hcND
  obtain ⟨hdNk, hdD⟩ := Finset.mem_inter.mp hdND
  -- Degrees.
  have hdega : G.degree a = 3 := (hIsoprop a haI).1
  have hdegb : G.degree b = 3 := (hIsoprop b hbI).1
  have hdegc : G.degree c = 3 := (hmemD c).mp hcD
  have hdegd : G.degree d = 3 := (hmemD d).mp hdD
  -- Adjacencies.
  have hah1 : G.Adj a h₁ := ((G.mem_neighborFinset h₁ a).mp haN1).symm
  have hbh1 : G.Adj b h₁ := ((G.mem_neighborFinset h₁ b).mp hbN1).symm
  have hck : G.Adj c k := ((G.mem_neighborFinset k c).mp hcNk).symm
  have hdk : G.Adj d k := ((G.mem_neighborFinset k d).mp hdNk).symm
  -- Cross non-adjacencies.
  have hn_h1c : ¬G.Adj h₁ c := fun ha => hcN1 ((G.mem_neighborFinset h₁ c).mpr ha)
  have hn_h1d : ¬G.Adj h₁ d := fun ha => hdN1 ((G.mem_neighborFinset h₁ d).mpr ha)
  have hn_ak : ¬G.Adj a k := fun ha => haNk ((G.mem_neighborFinset k a).mpr ha.symm)
  have hn_bk : ¬G.Adj b k := fun ha => hbNk ((G.mem_neighborFinset k b).mpr ha.symm)
  have hn_ac : ¬G.Adj a c := fun ha => (hIsoprop a haI).2 c ha hdegc
  have hn_ad : ¬G.Adj a d := fun ha => (hIsoprop a haI).2 d ha hdegd
  have hn_bc : ¬G.Adj b c := fun ha => (hIsoprop b hbI).2 c ha hdegc
  have hn_bd : ¬G.Adj b d := fun ha => (hIsoprop b hbI).2 d ha hdegd
  -- Distinctness of the leaf pairs across hubs.
  have hne_ac : a ≠ c := fun he => haNk (he ▸ hcNk)
  have hne_ad : a ≠ d := fun he => haNk (he ▸ hdNk)
  have hne_bc : b ≠ c := fun he => hbNk (he ▸ hcNk)
  have hne_bd : b ≠ d := fun he => hbNk (he ▸ hdNk)
  exact hth (two_hub_cherry_pair_nineteen G h₁ k a b c d hh1d hkd hdega hdegb hdegc hdegd
    hah1 hbh1 hck hdk hnadj1k hn_h1c hn_h1d hn_ak hn_bk hn_ac hn_ad hn_bc hn_bd
    hab hcd hne_ac hne_ad hne_bc hne_bd)

/-- **`|D| = 9` ISO1 hard-`c` subcase (`cinc h₁ = 1`, cherry-neighbour `= c₁`).**

The isolated degree-`4` hub `h₁` meets exactly one cherry vertex, the interior `c₁`; so its `4`
neighbours are `c₁` plus `3` `Iso` vertices (an independent degree-`3` set), and it is the UNIQUE
internally-isolated degree-`4` hub.  There is one degree-`5` hub `h₅` (also internally isolated by
the forcing).  We prove `False`.

Dichotomy on a low-internal-degree degree-`4` partner:
* **Case I** — some degree-`4` hub `k ≠ h₁` has internal degree `≤ 1`: `iso1_d9_caseI_nineteen`.
* **Case II** — every degree-`4` hub `≠ h₁` has internal degree `≥ 2`.  Then (against `htt`) the
  `Iso`-budget forces the tight configuration: `h₁` (iso `3`), `h₅` (iso `4`, `cinc 1`, isolated,
  `~ c₂`), four `A`-hubs (`cinc 1`, one leaf, iso `1`, int `2`) split `2`-on-`L₁` / `2`-on-`L₂`,
  four `F`-hubs (`cinc 0`, iso `1`, int `3`, triangle-free).  A non-adjacent `A`-cross-pair (exists,
  else the `F`-hubs form `K₄` ⟹ avoider triangle) with distinct `Iso`-leaves gives a `TwoHubConfig`;
  the residual (shared `Iso`) is dispatched by pairing an `A`-hub with `h₁` (its `Iso` `∉ N h₁`),
  the last case being impossible by an `F`-edge count. -/
theorem iso1_hard_c_subcase_nineteen (G : SimpleGraph (Fin 19))
    (D Iso : Finset (Fin 19)) (L₁ c₁ c₂ L₂ h₁ h₅ : Fin 19)
    (hmemD : ∀ v : Fin 19, v ∈ D ↔ G.degree v = 3)
    (hIsoprop : ∀ v ∈ Iso, G.degree v = 3 ∧ (∀ w : Fin 19, G.Adj v w → G.degree w ≠ 3))
    (hclassP : ∀ x : Fin 19, x ∈ D → x = L₁ ∨ x = c₁ ∨ x = c₂ ∨ x = L₂ ∨ x ∈ Iso)
    (hL1deg : G.degree L₁ = 3) (hc1deg : G.degree c₁ = 3)
    (hc2deg : G.degree c₂ = 3) (hL2deg : G.degree L₂ = 3)
    (hac1L1 : G.Adj c₁ L₁) (hc12 : G.Adj c₁ c₂) (hac2L2 : G.Adj c₂ L₂)
    (hL1nc2 : L₁ ≠ c₂) (hL2nc1 : L₂ ≠ c₁)
    (hNc1D : G.neighborFinset c₁ ∩ D = {c₂, L₁}) (hNc2D : G.neighborFinset c₂ ∩ D = {c₁, L₂})
    (hL1D : L₁ ∈ D) (hc1D : c₁ ∈ D) (hc2D : c₂ ∈ D) (hL2D : L₂ ∈ D)
    (htt : ¬TwoTwinConfig G) (hth : ¬TwoHubConfig G)
    (hT : ¬∃ x y z : Fin 19, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    (hC4 : ¬∃ a b c d : Fin 19, ({a, b, c, d} : Finset (Fin 19)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (hHub10 : Dᶜ.card = 10) (hIsocard : Iso.card = 5)
    (hdeg5 : ∀ h : Fin 19, h ∈ Dᶜ → G.degree h ≤ 5)
    (hper : ∀ h : Fin 19, h ∈ Dᶜ →
      (G.neighborFinset h ∩ ({L₁, c₁, c₂, L₂} : Finset (Fin 19))).card
        + (G.neighborFinset h ∩ Iso).card + (G.neighborFinset h ∩ Dᶜ).card = G.degree h)
    (hsumPath : ∑ g ∈ Dᶜ, (G.neighborFinset g ∩ ({L₁, c₁, c₂, L₂} : Finset (Fin 19))).card = 6)
    (hsumIso15 : ∑ h ∈ Dᶜ, (G.neighborFinset h ∩ Iso).card = 15)
    (hc1hub : (G.neighborFinset c₁ ∩ Dᶜ).card = 1)
    (hc2hub : (G.neighborFinset c₂ ∩ Dᶜ).card = 1)
    (hL1hub : (G.neighborFinset L₁ ∩ Dᶜ).card = 2)
    (hL2hub : (G.neighborFinset L₂ ∩ Dᶜ).card = 2)
    (hh1Dc : h₁ ∈ Dᶜ) (hh1d : G.degree h₁ = 4) (hh1iso : G.neighborFinset h₁ ∩ Dᶜ = ∅)
    (hRc1 : G.Adj h₁ c₁) (hcinc1 : (G.neighborFinset h₁ ∩ ({L₁, c₁, c₂, L₂} : Finset (Fin 19))).card ≤ 1)
    (hh5Dc : h₅ ∈ Dᶜ) (hh5d : G.degree h₅ = 5) (hne15 : h₁ ≠ h₅)
    (hdegOth : ∀ h : Fin 19, h ∈ Dᶜ → h ≠ h₁ → h ≠ h₅ → G.degree h = 4)
    (hntri1 : ¬∃ a b c : Fin 19, a ∈ Dᶜ ∧ b ∈ Dᶜ ∧ c ∈ Dᶜ ∧
      G.Adj a b ∧ G.Adj a c ∧ G.Adj b c ∧
      (¬G.Adj a L₁ ∧ ¬G.Adj a c₁ ∧ ¬G.Adj a c₂) ∧
      (¬G.Adj b L₁ ∧ ¬G.Adj b c₁ ∧ ¬G.Adj b c₂) ∧
      (¬G.Adj c L₁ ∧ ¬G.Adj c c₁ ∧ ¬G.Adj c c₂) ∧
      G.degree a + G.degree b + G.degree c ≤ 13) :
    False := by
  classical
  set P : Finset (Fin 19) := {L₁, c₁, c₂, L₂} with hPdef
  have hIso_nadj : ∀ t : Fin 19, t ∈ Iso → ∀ w : Fin 19, G.degree w = 3 → ¬G.Adj t w :=
    fun t ht w hw hadj => (hIsoprop t ht).2 w hadj hw
  -- Non-`Iso` cherry vertices.
  have hc1nIso : c₁ ∉ Iso := fun h => (hIsoprop c₁ h).2 L₁ hac1L1 hL1deg
  have hc2nIso : c₂ ∉ Iso := fun h => (hIsoprop c₂ h).2 c₁ hc12.symm hc1deg
  have hL1nIso : L₁ ∉ Iso := fun h => (hIsoprop L₁ h).2 c₁ hac1L1.symm hc1deg
  have hL2nIso : L₂ ∉ Iso := fun h => (hIsoprop L₂ h).2 c₂ hac2L2.symm hc2deg
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
  have hPnotIso : ∀ x : Fin 19, x ∈ P → x ∉ Iso := by
    intro x hx
    simp only [hPdef, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact hL1nIso
    · exact hc1nIso
    · exact hc2nIso
    · exact hL2nIso
  -- `N h₁ ⊆ D`.
  have hN1subD : G.neighborFinset h₁ ⊆ D := by
    intro x hx
    by_contra hxD
    have hmem : x ∈ G.neighborFinset h₁ ∩ Dᶜ :=
      Finset.mem_inter.mpr ⟨hx, Finset.mem_compl.mpr hxD⟩
    rw [hh1iso] at hmem; exact absurd hmem (Finset.notMem_empty x)
  have hdeg3N1 : ∀ x : Fin 19, x ∈ G.neighborFinset h₁ → G.degree x = 3 :=
    fun x hx => (hmemD x).mp (hN1subD hx)
  -- `cinc h₁ = 1`: exactly `{c₁}`, and `isoinc h₁ = 3`.
  have hc1N1 : c₁ ∈ G.neighborFinset h₁ := (G.mem_neighborFinset h₁ c₁).mpr hRc1
  have hcinc1' : (G.neighborFinset h₁ ∩ P).card = 1 := by
    have hc1mem : c₁ ∈ G.neighborFinset h₁ ∩ P :=
      Finset.mem_inter.mpr ⟨hc1N1, by simp [hPdef]⟩
    have hpos : 1 ≤ (G.neighborFinset h₁ ∩ P).card := Finset.card_pos.mpr ⟨c₁, hc1mem⟩
    omega
  have hh1int0 : (G.neighborFinset h₁ ∩ Dᶜ).card = 0 := by rw [hh1iso]; exact Finset.card_empty
  have hisoinc3 : (G.neighborFinset h₁ ∩ Iso).card = 3 := by
    have := hper h₁ hh1Dc
    rw [hcinc1', hh1int0, hh1d] at this; omega
  -- `N h₁` characterisation: every neighbour is `c₁` or an `Iso` vertex.
  have hN1char : ∀ x : Fin 19, x ∈ G.neighborFinset h₁ → x = c₁ ∨ x ∈ Iso := by
    intro x hx
    have hadj : G.Adj h₁ x := (G.mem_neighborFinset h₁ x).mp hx
    rcases hclassP x (hN1subD hx) with h | h | h | h | h
    · -- `x = L₁`: then `L₁ ∈ N h₁ ∩ P`, second element besides `c₁`, contradicting `cinc = 1`.
      exfalso
      have hL1mem : L₁ ∈ G.neighborFinset h₁ ∩ P :=
        Finset.mem_inter.mpr ⟨h ▸ hx, by simp [hPdef]⟩
      have hc1mem : c₁ ∈ G.neighborFinset h₁ ∩ P :=
        Finset.mem_inter.mpr ⟨hc1N1, by simp [hPdef]⟩
      have hsub : ({c₁, L₁} : Finset (Fin 19)) ⊆ G.neighborFinset h₁ ∩ P := by
        intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl
        · exact hc1mem
        · exact hL1mem
      have hcard2 : ({c₁, L₁} : Finset (Fin 19)).card = 2 := by
        rw [Finset.card_insert_of_notMem (by simp [G.ne_of_adj hac1L1]), Finset.card_singleton]
      have := Finset.card_le_card hsub; rw [hcard2, hcinc1'] at this; omega
    · exact Or.inl h
    · -- `x = c₂`: second cherry element.
      exfalso
      have hmem : c₂ ∈ G.neighborFinset h₁ ∩ P :=
        Finset.mem_inter.mpr ⟨h ▸ hx, by simp [hPdef]⟩
      have hc1mem : c₁ ∈ G.neighborFinset h₁ ∩ P :=
        Finset.mem_inter.mpr ⟨hc1N1, by simp [hPdef]⟩
      have hsub : ({c₁, c₂} : Finset (Fin 19)) ⊆ G.neighborFinset h₁ ∩ P := by
        intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl
        · exact hc1mem
        · exact hmem
      have hcard2 : ({c₁, c₂} : Finset (Fin 19)).card = 2 := by
        rw [Finset.card_insert_of_notMem (by simp [G.ne_of_adj hc12]), Finset.card_singleton]
      have := Finset.card_le_card hsub; rw [hcard2, hcinc1'] at this; omega
    · -- `x = L₂`.
      exfalso
      have hmem : L₂ ∈ G.neighborFinset h₁ ∩ P :=
        Finset.mem_inter.mpr ⟨h ▸ hx, by simp [hPdef]⟩
      have hc1mem : c₁ ∈ G.neighborFinset h₁ ∩ P :=
        Finset.mem_inter.mpr ⟨hc1N1, by simp [hPdef]⟩
      have hne : c₁ ≠ L₂ := Ne.symm hL2nc1
      have hsub : ({c₁, L₂} : Finset (Fin 19)) ⊆ G.neighborFinset h₁ ∩ P := by
        intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl
        · exact hc1mem
        · exact hmem
      have hcard2 : ({c₁, L₂} : Finset (Fin 19)).card = 2 := by
        rw [Finset.card_insert_of_notMem (by simp [hne]), Finset.card_singleton]
      have := Finset.card_le_card hsub; rw [hcard2, hcinc1'] at this; omega
    · exact Or.inr h
  -- `N h₁` is an independent set (needed for `isolated_deg4_share_le_one`).
  have hindep1 : ∀ x ∈ G.neighborFinset h₁, ∀ y ∈ G.neighborFinset h₁, x ≠ y → ¬G.Adj x y := by
    intro x hx y hy hxy hadj
    rcases hN1char x hx with hxc | hxI
    · rcases hN1char y hy with hyc | hyI
      · exact hxy (hxc.trans hyc.symm)
      · exact hIso_nadj y hyI x (hxc ▸ hc1deg) hadj.symm
    · exact hIso_nadj x hxI y (hdeg3N1 y hy) hadj
  -- `¬ G.Adj h₁ k` for any hub `k` (h₁ internally isolated).
  have hnadj1hub : ∀ k : Fin 19, k ∈ Dᶜ → ¬G.Adj h₁ k := by
    intro k hk hadj
    have : k ∈ G.neighborFinset h₁ ∩ Dᶜ :=
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset h₁ k).mpr hadj, hk⟩
    rw [hh1iso] at this; exact absurd this (Finset.notMem_empty k)
  -- ===================================================================================
  -- **Case I dichotomy.**
  by_cases hCaseI : ∃ k : Fin 19, k ∈ Dᶜ ∧ k ≠ h₁ ∧ G.degree k = 4
      ∧ (G.neighborFinset k ∩ Dᶜ).card ≤ 1
  · obtain ⟨k, hkDc, hkne, hkd, hkint⟩ := hCaseI
    exact iso1_d9_caseI_nineteen G D Iso h₁ k hmemD hIsoprop hth hC4 hh1d hh1iso hindep1
      (by rw [hisoinc3]) hkDc hkne hkd hkint
  · -- **Case II.**  Every degree-`4` hub `≠ h₁` has internal degree `≥ 2`.
    push Not at hCaseI
    have hCaseII : ∀ k : Fin 19, k ∈ Dᶜ → k ≠ h₁ → G.degree k = 4 →
        2 ≤ (G.neighborFinset k ∩ Dᶜ).card := by
      intro k hkDc hkne hkd
      have := hCaseI k hkDc hkne hkd; omega
    -- Hubs are distinct from all cherry vertices.
    have hubD_ne : ∀ h : Fin 19, h ∈ Dᶜ → h ≠ L₁ ∧ h ≠ c₁ ∧ h ≠ c₂ ∧ h ≠ L₂ := by
      intro h hh
      have hhD : h ∉ D := Finset.mem_compl.mp hh
      exact ⟨fun he => hhD (he ▸ hL1D), fun he => hhD (he ▸ hc1D),
        fun he => hhD (he ▸ hc2D), fun he => hhD (he ▸ hL2D)⟩
    -- **¬TwoTwin fact.**  A cherry-free hub has `≤ 1` `Iso`-neighbour.
    have hNoTT : ∀ h : Fin 19, h ∈ Dᶜ → (G.neighborFinset h ∩ P).card = 0 →
        (G.neighborFinset h ∩ Iso).card ≤ 1 := by
      intro h hh hcinc0
      by_contra hgt
      push Not at hgt
      have hPempty : G.neighborFinset h ∩ P = ∅ := Finset.card_eq_zero.mp hcinc0
      have hnadjP : ∀ w : Fin 19, w ∈ P → ¬G.Adj h w := by
        intro w hw hadj
        have : w ∈ G.neighborFinset h ∩ P :=
          Finset.mem_inter.mpr ⟨(G.mem_neighborFinset h w).mpr hadj, hw⟩
        rw [hPempty] at this; exact absurd this (Finset.notMem_empty w)
      obtain ⟨hnL1, hnc1, hnc2, hnL2⟩ := hubD_ne h hh
      exact htt (twotwin_of_centre_nineteen G Iso h L₁ c₁ c₂ hIsoprop hL1deg hc1deg hc2deg
        (hdeg5 h hh) hac1L1.symm hc12
        (hnadjP L₁ (by simp [hPdef])) (hnadjP c₁ (by simp [hPdef])) (hnadjP c₂ (by simp [hPdef]))
        hL1nIso hc1nIso hc2nIso hnL1 hnc1 hnc2
        (G.ne_of_adj hac1L1).symm (G.ne_of_adj hc12) hL1nc2 (by omega))
    -- **Iso-incidence forcing.**  Pointwise bound `isoinc h ≤ B h`, summing to `15` (tight).
    set B : Fin 19 → ℕ := fun h => if h = h₁ then 3 else if h = h₅ then 4 else 1 with hBdef
    have hbound : ∀ h : Fin 19, h ∈ Dᶜ → (G.neighborFinset h ∩ Iso).card ≤ B h := by
      intro h hh
      have hdec := hper h hh
      by_cases hh1 : h = h₁
      · have hBh : B h = 3 := by simp only [hBdef, if_pos hh1]
        rw [hBh, hh1]; omega
      · by_cases hh5 : h = h₅
        · have hBh : B h = 4 := by simp only [hBdef, if_neg hh1, if_pos hh5]
          rw [hBh]
          have hdh : G.degree h = 5 := by rw [hh5]; exact hh5d
          rw [hdh] at hdec
          by_cases hc0 : (G.neighborFinset h ∩ P).card = 0
          · have := hNoTT h hh hc0; omega
          · omega
        · have hBh : B h = 1 := by simp only [hBdef, if_neg hh1, if_neg hh5]
          rw [hBh]
          have hd4 := hdegOth h hh hh1 hh5
          rw [hd4] at hdec
          have hint2 := hCaseII h hh hh1 hd4
          by_cases hc0 : (G.neighborFinset h ∩ P).card = 0
          · have := hNoTT h hh hc0; omega
          · omega
    have hsumB : ∑ h ∈ Dᶜ, B h = 15 := by
      have hpt : ∀ h, B h = 1 + ((if h = h₁ then 2 else 0) + (if h = h₅ then 3 else 0)) := by
        intro h
        by_cases hh1 : h = h₁
        · subst hh1; simp [hBdef, hne15]
        · by_cases hh5 : h = h₅
          · subst hh5; simp [hBdef, hh1]
          · simp [hBdef, hh1, hh5]
      simp only [hpt, Finset.sum_add_distrib, Finset.sum_const, hHub10, smul_eq_mul,
        Finset.sum_ite_eq' Dᶜ h₁ (fun _ => (2 : ℕ)),
        Finset.sum_ite_eq' Dᶜ h₅ (fun _ => (3 : ℕ)), hh1Dc, hh5Dc, if_pos]
      omega
    have heq : ∀ h : Fin 19, h ∈ Dᶜ → (G.neighborFinset h ∩ Iso).card = B h := by
      intro h hh
      by_contra hne
      have hlt : (G.neighborFinset h ∩ Iso).card < B h := lt_of_le_of_ne (hbound h hh) hne
      have hsum_lt : ∑ g ∈ Dᶜ, (G.neighborFinset g ∩ Iso).card < ∑ g ∈ Dᶜ, B g :=
        Finset.sum_lt_sum hbound ⟨h, hh, hlt⟩
      rw [hsumIso15, hsumB] at hsum_lt; omega
    -- Per-hub consequences of the tight forcing.
    -- `h₅`: iso `4`, `cinc 1`, internally isolated.
    have hBh5 : B h₅ = 4 := by simp [hBdef, Ne.symm hne15]
    have hh5iso4 : (G.neighborFinset h₅ ∩ Iso).card = 4 := by
      have := heq h₅ hh5Dc; rw [hBh5] at this; exact this
    have hh5cinc1 : (G.neighborFinset h₅ ∩ P).card = 1 := by
      have hdec := hper h₅ hh5Dc
      rw [hh5iso4, hh5d] at hdec
      rcases Nat.eq_zero_or_pos (G.neighborFinset h₅ ∩ P).card with h0 | hpos
      · exact absurd (hNoTT h₅ hh5Dc h0) (by omega)
      · omega
    have hh5int0 : (G.neighborFinset h₅ ∩ Dᶜ).card = 0 := by
      have hdec := hper h₅ hh5Dc; rw [hh5iso4, hh5cinc1, hh5d] at hdec; omega
    -- Every degree-`4` hub `≠ h₁, h₅` has iso `1`; hence `cinc + int = 3`, `int ∈ {2,3}`.
    have hOthiso1 : ∀ h : Fin 19, h ∈ Dᶜ → h ≠ h₁ → h ≠ h₅ →
        (G.neighborFinset h ∩ Iso).card = 1 := by
      intro h hh hh1 hh5
      have hBh : B h = 1 := by simp only [hBdef, if_neg hh1, if_neg hh5]
      have := heq h hh; rw [hBh] at this; exact this
    -- **`h₅ ~ c₂`.**  `h₅`'s unique cherry neighbour cannot be `c₁` (whose only hub is `h₁`) nor a
    -- leaf (else `h₅` centres a `TwoTwinConfig`).
    obtain ⟨w5, hw5eq⟩ := Finset.card_eq_one.mp hh5cinc1
    have hw5mem : w5 ∈ G.neighborFinset h₅ ∩ P := by rw [hw5eq]; exact Finset.mem_singleton_self w5
    have hh5w5 : G.Adj h₅ w5 := (G.mem_neighborFinset h₅ w5).mp (Finset.mem_inter.mp hw5mem).1
    have hw5P : w5 ∈ P := (Finset.mem_inter.mp hw5mem).2
    have hh5only : ∀ x : Fin 19, x ∈ P → G.Adj h₅ x → x = w5 := by
      intro x hxP hadj
      have : x ∈ G.neighborFinset h₅ ∩ P :=
        Finset.mem_inter.mpr ⟨(G.mem_neighborFinset h₅ x).mpr hadj, hxP⟩
      rw [hw5eq] at this; exact Finset.mem_singleton.mp this
    have hNc1Dc : G.neighborFinset c₁ ∩ Dᶜ = {h₁} := by
      have h1mem : h₁ ∈ G.neighborFinset c₁ ∩ Dᶜ :=
        Finset.mem_inter.mpr ⟨(G.mem_neighborFinset c₁ h₁).mpr hRc1.symm, hh1Dc⟩
      have hsub : ({h₁} : Finset (Fin 19)) ⊆ G.neighborFinset c₁ ∩ Dᶜ := by
        intro x hx; rw [Finset.mem_singleton] at hx; exact hx ▸ h1mem
      exact (Finset.eq_of_subset_of_card_le hsub (by rw [hc1hub, Finset.card_singleton])).symm
    have hn_h5c1 : ¬G.Adj h₅ c₁ := by
      intro hadj
      have : h₅ ∈ G.neighborFinset c₁ ∩ Dᶜ :=
        Finset.mem_inter.mpr ⟨(G.mem_neighborFinset c₁ h₅).mpr hadj.symm, hh5Dc⟩
      rw [hNc1Dc, Finset.mem_singleton] at this; exact hne15 this.symm
    have hRc2 : G.Adj h₅ c₂ := by
      simp only [hPdef, Finset.mem_insert, Finset.mem_singleton] at hw5P
      rcases hw5P with rfl | rfl | rfl | rfl
      · -- `w5 = L₁`: `TwoTwinConfig` centre `h₅` avoiding `c₁–c₂–L₂`.
        exfalso
        have hn_c1 : ¬G.Adj h₅ c₁ := fun ha => (G.ne_of_adj hac1L1) (hh5only c₁ (by simp [hPdef]) ha)
        have hn_c2 : ¬G.Adj h₅ c₂ := fun ha => (Ne.symm hL1nc2) (hh5only c₂ (by simp [hPdef]) ha)
        have hn_L2 : ¬G.Adj h₅ L₂ := fun ha => hL1L2 (hh5only L₂ (by simp [hPdef]) ha).symm
        obtain ⟨_, hne5c1, hne5c2, hne5L2⟩ := hubD_ne h₅ hh5Dc
        exact htt (twotwin_of_centre_nineteen G Iso h₅ c₁ c₂ L₂ hIsoprop hc1deg hc2deg hL2deg
          (hdeg5 h₅ hh5Dc) hc12 hac2L2 hn_c1 hn_c2 hn_L2 hc1nIso hc2nIso hL2nIso
          hne5c1 hne5c2 hne5L2 (G.ne_of_adj hc12) (G.ne_of_adj hac2L2) (Ne.symm hL2nc1)
          (by rw [hh5iso4]; norm_num))
      · exact absurd hh5w5 hn_h5c1
      · exact hh5w5
      · -- `w5 = L₂`: `TwoTwinConfig` centre `h₅` avoiding `L₁–c₁–c₂`.
        exfalso
        have hn_L1 : ¬G.Adj h₅ L₁ := fun ha => hL1L2 (hh5only L₁ (by simp [hPdef]) ha)
        have hn_c1 : ¬G.Adj h₅ c₁ := fun ha => (Ne.symm hL2nc1) (hh5only c₁ (by simp [hPdef]) ha)
        have hn_c2 : ¬G.Adj h₅ c₂ := fun ha => (G.ne_of_adj hac2L2) (hh5only c₂ (by simp [hPdef]) ha)
        obtain ⟨hne5L1, hne5c1, hne5c2, _⟩ := hubD_ne h₅ hh5Dc
        exact htt (twotwin_of_centre_nineteen G Iso h₅ L₁ c₁ c₂ hIsoprop hL1deg hc1deg hc2deg
          (hdeg5 h₅ hh5Dc) hac1L1.symm hc12 hn_L1 hn_c1 hn_c2 hL1nIso hc1nIso hc2nIso
          hne5L1 hne5c1 hne5c2 (G.ne_of_adj hac1L1).symm (G.ne_of_adj hc12) hL1nc2
          (by rw [hh5iso4]; norm_num))
    -- `c₂`'s unique hub is `h₅`.
    have hNc2Dc : G.neighborFinset c₂ ∩ Dᶜ = {h₅} := by
      have h5mem : h₅ ∈ G.neighborFinset c₂ ∩ Dᶜ :=
        Finset.mem_inter.mpr ⟨(G.mem_neighborFinset c₂ h₅).mpr hRc2.symm, hh5Dc⟩
      have hsub : ({h₅} : Finset (Fin 19)) ⊆ G.neighborFinset c₂ ∩ Dᶜ := by
        intro x hx; rw [Finset.mem_singleton] at hx; exact hx ▸ h5mem
      exact (Finset.eq_of_subset_of_card_le hsub (by rw [hc2hub, Finset.card_singleton])).symm
    -- `¬ G.Adj L₁ L₂`.
    have hnL1L2 : ¬G.Adj L₁ L₂ := by
      intro hadj
      have hdisj : Disjoint (G.neighborFinset L₁ ∩ D) (G.neighborFinset L₁ ∩ Dᶜ) := by
        apply Finset.disjoint_left.mpr; intro a ha hb
        exact (Finset.mem_compl.mp (Finset.mem_inter.mp hb).2) (Finset.mem_inter.mp ha).2
      have hunion : (G.neighborFinset L₁ ∩ D) ∪ (G.neighborFinset L₁ ∩ Dᶜ) = G.neighborFinset L₁ := by
        rw [← Finset.inter_union_distrib_left, Finset.union_compl, Finset.inter_univ]
      have hsplit : (G.neighborFinset L₁ ∩ D).card + (G.neighborFinset L₁ ∩ Dᶜ).card = G.degree L₁ := by
        rw [← Finset.card_union_of_disjoint hdisj, hunion, G.card_neighborFinset_eq_degree]
      rw [hL1deg, hL1hub] at hsplit
      have hone : (G.neighborFinset L₁ ∩ D).card = 1 := by omega
      have hc1mem : c₁ ∈ G.neighborFinset L₁ ∩ D :=
        Finset.mem_inter.mpr ⟨(G.mem_neighborFinset L₁ c₁).mpr hac1L1.symm, hc1D⟩
      have hL2mem : L₂ ∈ G.neighborFinset L₁ ∩ D :=
        Finset.mem_inter.mpr ⟨(G.mem_neighborFinset L₁ L₂).mpr hadj, hL2D⟩
      have hsub : ({c₁, L₂} : Finset (Fin 19)) ⊆ G.neighborFinset L₁ ∩ D := by
        intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact hc1mem
        · exact hL2mem
      have hcard2 : ({c₁, L₂} : Finset (Fin 19)).card = 2 := by
        rw [Finset.card_insert_of_notMem (by simp [Ne.symm hL2nc1]), Finset.card_singleton]
      have := Finset.card_le_card hsub; rw [hcard2, hone] at this; omega
    -- `N h₁ ∩ P = {c₁}`, `N h₅ ∩ P = {c₂}`.
    have hNh1P : G.neighborFinset h₁ ∩ P = {c₁} := by
      have hc1mem : c₁ ∈ G.neighborFinset h₁ ∩ P := Finset.mem_inter.mpr ⟨hc1N1, by simp [hPdef]⟩
      exact (Finset.eq_of_subset_of_card_le (by intro x hx; rw [Finset.mem_singleton] at hx; exact hx ▸ hc1mem)
        (by rw [hcinc1', Finset.card_singleton])).symm
    have hNh5P : G.neighborFinset h₅ ∩ P = {c₂} := by
      have hc2mem : c₂ ∈ G.neighborFinset h₅ ∩ P :=
        Finset.mem_inter.mpr ⟨(G.mem_neighborFinset h₅ c₂).mpr hRc2, by simp [hPdef]⟩
      exact (Finset.eq_of_subset_of_card_le (by intro x hx; rw [Finset.mem_singleton] at hx; exact hx ▸ hc2mem)
        (by rw [hh5cinc1, Finset.card_singleton])).symm
    -- **Leaf-hub structure.**  A hub adjacent to a leaf `Lf ∈ {L₁, L₂}` is an `A`-hub:
    -- degree `4`, internal degree `2`, its only cherry neighbour is `Lf`, and it has a unique
    -- `Iso`-neighbour.
    have leafhub : ∀ a Lf : Fin 19, Lf ∈ P → Lf ≠ c₁ → Lf ≠ c₂ →
        a ∈ G.neighborFinset Lf ∩ Dᶜ →
        a ≠ h₁ ∧ a ≠ h₅ ∧ G.degree a = 4 ∧ (G.neighborFinset a ∩ Dᶜ).card = 2 ∧
        G.neighborFinset a ∩ P = {Lf} ∧ (∃ ι : Fin 19, ι ∈ Iso ∧ G.Adj a ι ∧
          G.neighborFinset a ∩ Iso = {ι}) := by
      intro a Lf hLfP hLfc1 hLfc2 ha
      obtain ⟨haN, haDc⟩ := Finset.mem_inter.mp ha
      have haLf : G.Adj a Lf := ((G.mem_neighborFinset Lf a).mp haN).symm
      have hLfmem : Lf ∈ G.neighborFinset a ∩ P :=
        Finset.mem_inter.mpr ⟨(G.mem_neighborFinset a Lf).mpr haLf, hLfP⟩
      have ha1 : a ≠ h₁ := by
        intro he; subst he
        have : Lf ∈ G.neighborFinset a ∩ P := hLfmem
        rw [hNh1P, Finset.mem_singleton] at this; exact hLfc1 this
      have ha5 : a ≠ h₅ := by
        intro he; subst he
        have : Lf ∈ G.neighborFinset a ∩ P := hLfmem
        rw [hNh5P, Finset.mem_singleton] at this; exact hLfc2 this
      have hd4 := hdegOth a haDc ha1 ha5
      have hiso1 := hOthiso1 a haDc ha1 ha5
      have hcincpos : 1 ≤ (G.neighborFinset a ∩ P).card := Finset.card_pos.mpr ⟨Lf, hLfmem⟩
      have hint2 := hCaseII a haDc ha1 hd4
      have hdec := hper a haDc
      rw [hiso1, hd4] at hdec
      have hcinc1a : (G.neighborFinset a ∩ P).card = 1 := by omega
      have hint2a : (G.neighborFinset a ∩ Dᶜ).card = 2 := by omega
      have hNaP : G.neighborFinset a ∩ P = {Lf} :=
        (Finset.eq_of_subset_of_card_le
          (by intro x hx; rw [Finset.mem_singleton] at hx; exact hx ▸ hLfmem)
          (by rw [hcinc1a, Finset.card_singleton])).symm
      obtain ⟨ι, hιeq⟩ := Finset.card_eq_one.mp hiso1
      have hιmem : ι ∈ G.neighborFinset a ∩ Iso := by rw [hιeq]; exact Finset.mem_singleton_self ι
      obtain ⟨hιN, hιIso⟩ := Finset.mem_inter.mp hιmem
      exact ⟨ha1, ha5, hd4, hint2a, hNaP, ι, hιIso, (G.mem_neighborFinset a ι).mp hιN, hιeq⟩
    -- Extract the four `A`-hubs.
    have hL1c1 : L₁ ≠ c₁ := (G.ne_of_adj hac1L1).symm
    have hL1P : L₁ ∈ P := by simp [hPdef]
    have hL2P : L₂ ∈ P := by simp [hPdef]
    obtain ⟨a1, a2, ha12, haLeq⟩ := Finset.card_eq_two.mp hL1hub
    obtain ⟨b1, b2, hb12, haReq⟩ := Finset.card_eq_two.mp hL2hub
    have hL2c1 : L₂ ≠ c₁ := hL2nc1
    have hL2c2 : L₂ ≠ c₂ := (G.ne_of_adj hac2L2).symm
    have ha1mem : a1 ∈ G.neighborFinset L₁ ∩ Dᶜ := by rw [haLeq]; simp
    have ha2mem : a2 ∈ G.neighborFinset L₁ ∩ Dᶜ := by rw [haLeq]; simp
    have hb1mem : b1 ∈ G.neighborFinset L₂ ∩ Dᶜ := by rw [haReq]; simp
    have hb2mem : b2 ∈ G.neighborFinset L₂ ∩ Dᶜ := by rw [haReq]; simp
    obtain ⟨ha1_1, ha1_5, ha1d, ha1int, ha1NP, ιa1, hιa1I, ha1ι, ha1isoeq⟩ :=
      leafhub a1 L₁ hL1P hL1c1 hL1nc2 ha1mem
    obtain ⟨ha2_1, ha2_5, ha2d, ha2int, ha2NP, ιa2, hιa2I, ha2ι, ha2isoeq⟩ :=
      leafhub a2 L₁ hL1P hL1c1 hL1nc2 ha2mem
    obtain ⟨hb1_1, hb1_5, hb1d, hb1int, hb1NP, ιb1, hιb1I, hb1ι, hb1isoeq⟩ :=
      leafhub b1 L₂ hL2P hL2c1 hL2c2 hb1mem
    obtain ⟨hb2_1, hb2_5, hb2d, hb2int, hb2NP, ιb2, hιb2I, hb2ι, hb2isoeq⟩ :=
      leafhub b2 L₂ hL2P hL2c1 hL2c2 hb2mem
    have ha1Dc : a1 ∈ Dᶜ := (Finset.mem_inter.mp ha1mem).2
    have ha2Dc : a2 ∈ Dᶜ := (Finset.mem_inter.mp ha2mem).2
    have hb1Dc : b1 ∈ Dᶜ := (Finset.mem_inter.mp hb1mem).2
    have hb2Dc : b2 ∈ Dᶜ := (Finset.mem_inter.mp hb2mem).2
    have ha1L1 : G.Adj a1 L₁ := ((G.mem_neighborFinset L₁ a1).mp (Finset.mem_inter.mp ha1mem).1).symm
    have ha2L1 : G.Adj a2 L₁ := ((G.mem_neighborFinset L₁ a2).mp (Finset.mem_inter.mp ha2mem).1).symm
    have hb1L2 : G.Adj b1 L₂ := ((G.mem_neighborFinset L₂ b1).mp (Finset.mem_inter.mp hb1mem).1).symm
    have hb2L2 : G.Adj b2 L₂ := ((G.mem_neighborFinset L₂ b2).mp (Finset.mem_inter.mp hb2mem).1).symm
    -- Non-adjacency helpers.
    have notP : ∀ a Lf : Fin 19, G.neighborFinset a ∩ P = {Lf} →
        ∀ x : Fin 19, x ∈ P → x ≠ Lf → ¬G.Adj a x := by
      intro a Lf hNaP x hxP hxne hadj
      have : x ∈ G.neighborFinset a ∩ P :=
        Finset.mem_inter.mpr ⟨(G.mem_neighborFinset a x).mpr hadj, hxP⟩
      rw [hNaP, Finset.mem_singleton] at this; exact hxne this
    have notIso : ∀ a ι : Fin 19, G.neighborFinset a ∩ Iso = {ι} →
        ∀ t : Fin 19, t ∈ Iso → t ≠ ι → ¬G.Adj a t := by
      intro a ι hNaI t htI htne hadj
      have : t ∈ G.neighborFinset a ∩ Iso :=
        Finset.mem_inter.mpr ⟨(G.mem_neighborFinset a t).mpr hadj, htI⟩
      rw [hNaI, Finset.mem_singleton] at this; exact htne this
    -- **MAIN assembler:** a non-adjacent cross pair with distinct `Iso`-leaves ⟹ `TwoHubConfig`.
    have crossTwoHub : ∀ a b ιa ιb : Fin 19,
        G.degree a = 4 → G.degree b = 4 →
        G.Adj a L₁ → G.Adj b L₂ → G.neighborFinset a ∩ P = {L₁} → G.neighborFinset b ∩ P = {L₂} →
        ιa ∈ Iso → ιb ∈ Iso → G.Adj a ιa → G.Adj b ιb →
        G.neighborFinset a ∩ Iso = {ιa} → G.neighborFinset b ∩ Iso = {ιb} →
        ¬G.Adj a b → ιa ≠ ιb → False := by
      intro a b ιa ιb had hbd haL1 hbL2 hNaP hNbP hιaI hιbI haιa hbιb hNaI hNbI hnab hιne
      have hdιa : G.degree ιa = 3 := (hIsoprop ιa hιaI).1
      have hdιb : G.degree ιb = 3 := (hIsoprop ιb hιbI).1
      have hnbL1 : ¬G.Adj b L₁ := notP b L₂ hNbP L₁ hL1P hL1L2
      have hnaL2 : ¬G.Adj a L₂ := notP a L₁ hNaP L₂ hL2P (Ne.symm hL1L2)
      exact hth (two_hub_cherry_pair_nineteen G a b L₁ ιa L₂ ιb had hbd hL1deg hdιa hL2deg hdιb
        haL1.symm haιa.symm hbL2.symm hbιb.symm hnab hnaL2
        (notIso a ιa hNaI ιb hιbI (Ne.symm hιne))
        (fun h => hnbL1 h.symm)
        (fun h => (notIso b ιb hNbI ιa hιaI hιne) h.symm)
        hnL1L2
        (fun h => hIso_nadj ιb hιbI L₁ hL1deg h.symm)
        (fun h => hIso_nadj ιa hιaI L₂ hL2deg h)
        (fun h => hIso_nadj ιa hιaI ιb hdιb h)
        (fun he => hL1nIso (he ▸ hιaI)) (fun he => hL2nIso (he ▸ hιbI))
        hL1L2 (fun he => hL1nIso (he ▸ hιbI)) (fun he => hL2nIso (he ▸ hιaI)) hιne)
    -- **`h₁`-pair assembler:** an `A`-hub whose `Iso` `∉ N h₁` pairs with `h₁` ⟹ `TwoHubConfig`.
    have h1pairTwoHub : ∀ k Lk ιk : Fin 19, k ∈ Dᶜ → G.degree k = 4 →
        (Lk = L₁ ∨ Lk = L₂) → G.Adj k Lk → ιk ∈ Iso → G.Adj k ιk →
        G.neighborFinset k ∩ Iso = {ιk} → G.neighborFinset k ∩ P = {Lk} →
        ιk ∉ G.neighborFinset h₁ → False := by
      intro k Lk ιk hkDc hkd hLkleaf hkLk hιkI hkιk hNkI hNkP hιk_out
      have hLkP : Lk ∈ P := by rcases hLkleaf with rfl | rfl; exacts [hL1P, hL2P]
      have hLkc1 : Lk ≠ c₁ := by rcases hLkleaf with rfl | rfl; exacts [hL1c1, hL2c1]
      have hLknIso : Lk ∉ Iso := by rcases hLkleaf with rfl | rfl; exacts [hL1nIso, hL2nIso]
      have hLkdeg : G.degree Lk = 3 := by rcases hLkleaf with rfl | rfl; exacts [hL1deg, hL2deg]
      have hdιk : G.degree ιk = 3 := (hIsoprop ιk hιkI).1
      have hkh1 : k ≠ h₁ := by
        intro he
        have : Lk ∈ G.neighborFinset h₁ ∩ P := by
          rw [← he]; exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset k Lk).mpr hkLk, hLkP⟩
        rw [hNh1P, Finset.mem_singleton] at this; exact hLkc1 this
      -- shared-neighbour bound.
      have hshare := isolated_deg4_share_le_one G h₁ k hC4 hh1d hkd (Ne.symm hkh1)
        (hnadj1hub k hkDc) hdeg3N1 hindep1
      -- `h₁`'s private `Iso`-leaves.
      have hpriv : 2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset k).card := by
        have hsplit := Finset.card_sdiff_add_card_inter (G.neighborFinset h₁ ∩ Iso) (G.neighborFinset k)
        have hsub : (G.neighborFinset h₁ ∩ Iso) ∩ G.neighborFinset k
            ⊆ G.neighborFinset h₁ ∩ G.neighborFinset k := by
          intro x hx
          obtain ⟨hxNI, hxNk⟩ := Finset.mem_inter.mp hx
          exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hxNI).1, hxNk⟩
        have := Finset.card_le_card hsub
        rw [hisoinc3] at hsplit; omega
      obtain ⟨p, hpM, q, hqM, hpq⟩ :=
        Finset.one_lt_card.mp (by omega : 1 < ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset k).card)
      obtain ⟨hpNI, hpNk⟩ := Finset.mem_sdiff.mp hpM
      obtain ⟨hqNI, hqNk⟩ := Finset.mem_sdiff.mp hqM
      obtain ⟨hpN1, hpI⟩ := Finset.mem_inter.mp hpNI
      obtain ⟨hqN1, hqI⟩ := Finset.mem_inter.mp hqNI
      have hdp : G.degree p = 3 := (hIsoprop p hpI).1
      have hdq : G.degree q = 3 := (hIsoprop q hqI).1
      have hph1 : G.Adj p h₁ := ((G.mem_neighborFinset h₁ p).mp hpN1).symm
      have hqh1 : G.Adj q h₁ := ((G.mem_neighborFinset h₁ q).mp hqN1).symm
      have hn_h1Lk : ¬G.Adj h₁ Lk := by
        intro ha
        have : Lk ∈ G.neighborFinset h₁ ∩ P :=
          Finset.mem_inter.mpr ⟨(G.mem_neighborFinset h₁ Lk).mpr ha, hLkP⟩
        rw [hNh1P, Finset.mem_singleton] at this; exact hLkc1 this
      have hn_h1ιk : ¬G.Adj h₁ ιk := fun ha => hιk_out ((G.mem_neighborFinset h₁ ιk).mpr ha)
      have hιkNk : ιk ∈ G.neighborFinset k := (G.mem_neighborFinset k ιk).mpr hkιk
      exact hth (two_hub_cherry_pair_nineteen G h₁ k p q Lk ιk hh1d hkd hdp hdq hLkdeg hdιk
        hph1 hqh1 hkLk.symm hkιk.symm (hnadj1hub k hkDc) hn_h1Lk hn_h1ιk
        (fun ha => hpNk ((G.mem_neighborFinset k p).mpr ha.symm))
        (fun ha => hqNk ((G.mem_neighborFinset k q).mpr ha.symm))
        (fun ha => hIso_nadj p hpI Lk hLkdeg ha)
        (fun ha => hIso_nadj p hpI ιk hdιk ha)
        (fun ha => hIso_nadj q hqI Lk hLkdeg ha)
        (fun ha => hIso_nadj q hqI ιk hdιk ha)
        hpq (fun he => hLknIso (he ▸ hιkI))
        (fun he => hLknIso (he ▸ hpI)) (fun he => hpNk (he ▸ hιkNk))
        (fun he => hLknIso (he ▸ hqI)) (fun he => hqNk (he ▸ hιkNk)))
    -- Six distinct hubs.
    have hab11 : a1 ≠ b1 := by
      intro he; exact (notP a1 L₁ ha1NP L₂ hL2P (Ne.symm hL1L2)) (by rw [he]; exact hb1L2)
    have hab12 : a1 ≠ b2 := by
      intro he; exact (notP a1 L₁ ha1NP L₂ hL2P (Ne.symm hL1L2)) (by rw [he]; exact hb2L2)
    have hab21 : a2 ≠ b1 := by
      intro he; exact (notP a2 L₁ ha2NP L₂ hL2P (Ne.symm hL1L2)) (by rw [he]; exact hb1L2)
    have hab22 : a2 ≠ b2 := by
      intro he; exact (notP a2 L₁ ha2NP L₂ hL2P (Ne.symm hL1L2)) (by rw [he]; exact hb2L2)
    -- **The `A` and `F` hub sets.**
    set Aset : Finset (Fin 19) := {a1, a2, b1, b2} with hAsetdef
    set Sset : Finset (Fin 19) := insert h₁ (insert h₅ Aset) with hSsetdef
    set Fset : Finset (Fin 19) := Dᶜ \ Sset with hFsetdef
    have hAcard : Aset.card = 4 := by
      rw [hAsetdef]
      rw [Finset.card_insert_of_notMem (by simp [ha12, hab11, hab12]),
        Finset.card_insert_of_notMem (by simp [hab21, hab22]),
        Finset.card_insert_of_notMem (by simp [hb12]), Finset.card_singleton]
    have hh1nA : h₁ ∉ Aset := by
      simp only [hAsetdef, Finset.mem_insert, Finset.mem_singleton]
      push Not; exact ⟨Ne.symm ha1_1, Ne.symm ha2_1, Ne.symm hb1_1, Ne.symm hb2_1⟩
    have hh5nA : h₅ ∉ Aset := by
      simp only [hAsetdef, Finset.mem_insert, Finset.mem_singleton]
      push Not; exact ⟨Ne.symm ha1_5, Ne.symm ha2_5, Ne.symm hb1_5, Ne.symm hb2_5⟩
    have hScard : Sset.card = 6 := by
      rw [hSsetdef, Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert]; push Not; exact ⟨hne15, hh1nA⟩),
        Finset.card_insert_of_notMem hh5nA, hAcard]
    have hSsubDc : Sset ⊆ Dᶜ := by
      rw [hSsetdef]
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton, hAsetdef] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      exacts [hh1Dc, hh5Dc, ha1Dc, ha2Dc, hb1Dc, hb2Dc]
    have hFcard : Fset.card = 4 := by
      have hcs : (Dᶜ \ Sset).card = Dᶜ.card - Sset.card := Finset.card_sdiff_of_subset hSsubDc
      rw [hFsetdef, hcs, hHub10, hScard]
    -- `F`-hub membership: in `Dᶜ`, not `h₁, h₅`, not an `A`-hub.
    have hFmem : ∀ f : Fin 19, f ∈ Fset ↔ f ∈ Dᶜ ∧ f ≠ h₁ ∧ f ≠ h₅ ∧
        f ≠ a1 ∧ f ≠ a2 ∧ f ≠ b1 ∧ f ≠ b2 := by
      intro f
      rw [hFsetdef, Finset.mem_sdiff, hSsetdef]
      simp only [Finset.mem_insert, Finset.mem_singleton, hAsetdef]
      constructor
      · rintro ⟨hfDc, hf⟩; push Not at hf; exact ⟨hfDc, hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.1,
          hf.2.2.2.2.1, hf.2.2.2.2.2⟩
      · rintro ⟨hfDc, h1, h5, ha1, ha2, hb1, hb2⟩
        exact ⟨hfDc, by push Not; exact ⟨h1, h5, ha1, ha2, hb1, hb2⟩⟩
    -- `F`-hub structure: degree `4`, cherry-free, internal degree `3`.
    have hFprop : ∀ f : Fin 19, f ∈ Fset → G.degree f = 4 ∧ (G.neighborFinset f ∩ Dᶜ).card = 3 ∧
        ¬G.Adj f L₁ ∧ ¬G.Adj f c₁ ∧ ¬G.Adj f c₂ := by
      intro f hf
      obtain ⟨hfDc, hf1, hf5, hfa1, hfa2, hfb1, hfb2⟩ := (hFmem f).mp hf
      have hd4 := hdegOth f hfDc hf1 hf5
      have hiso1 := hOthiso1 f hfDc hf1 hf5
      have hnfL1 : ¬G.Adj f L₁ := by
        intro ha
        have : f ∈ G.neighborFinset L₁ ∩ Dᶜ :=
          Finset.mem_inter.mpr ⟨(G.mem_neighborFinset L₁ f).mpr ha.symm, hfDc⟩
        rw [haLeq, Finset.mem_insert, Finset.mem_singleton] at this
        rcases this with h | h
        exacts [hfa1 h, hfa2 h]
      have hnfL2 : ¬G.Adj f L₂ := by
        intro ha
        have : f ∈ G.neighborFinset L₂ ∩ Dᶜ :=
          Finset.mem_inter.mpr ⟨(G.mem_neighborFinset L₂ f).mpr ha.symm, hfDc⟩
        rw [haReq, Finset.mem_insert, Finset.mem_singleton] at this
        rcases this with h | h
        exacts [hfb1 h, hfb2 h]
      have hnfc1 : ¬G.Adj f c₁ := by
        intro ha
        have : f ∈ G.neighborFinset c₁ ∩ Dᶜ :=
          Finset.mem_inter.mpr ⟨(G.mem_neighborFinset c₁ f).mpr ha.symm, hfDc⟩
        rw [hNc1Dc, Finset.mem_singleton] at this; exact hf1 this
      have hnfc2 : ¬G.Adj f c₂ := by
        intro ha
        have : f ∈ G.neighborFinset c₂ ∩ Dᶜ :=
          Finset.mem_inter.mpr ⟨(G.mem_neighborFinset c₂ f).mpr ha.symm, hfDc⟩
        rw [hNc2Dc, Finset.mem_singleton] at this; exact hf5 this
      -- `cinc f = 0`.
      have hcinc0 : (G.neighborFinset f ∩ P).card = 0 := by
        rw [Finset.card_eq_zero]
        rw [Finset.eq_empty_iff_forall_notMem]
        intro x hx
        obtain ⟨hxN, hxP⟩ := Finset.mem_inter.mp hx
        have hadj : G.Adj f x := (G.mem_neighborFinset f x).mp hxN
        simp only [hPdef, Finset.mem_insert, Finset.mem_singleton] at hxP
        rcases hxP with rfl | rfl | rfl | rfl
        exacts [hnfL1 hadj, hnfc1 hadj, hnfc2 hadj, hnfL2 hadj]
      have hdec := hper f hfDc
      rw [hiso1, hcinc0, hd4] at hdec
      exact ⟨hd4, by omega, hnfL1, hnfc1, hnfc2⟩
    -- Every hub is non-adjacent to the two internally-isolated hubs `h₁, h₅`.
    have hh5isoempty : G.neighborFinset h₅ ∩ Dᶜ = ∅ := Finset.card_eq_zero.mp hh5int0
    have hnh1h5 : ∀ x : Fin 19, x ∈ Dᶜ → ¬G.Adj x h₁ ∧ ¬G.Adj x h₅ := by
      intro x hx
      refine ⟨fun ha => ?_, fun ha => ?_⟩
      · have : x ∈ G.neighborFinset h₁ ∩ Dᶜ :=
          Finset.mem_inter.mpr ⟨(G.mem_neighborFinset h₁ x).mpr ha.symm, hx⟩
        rw [hh1iso] at this; exact absurd this (Finset.notMem_empty x)
      · have : x ∈ G.neighborFinset h₅ ∩ Dᶜ :=
          Finset.mem_inter.mpr ⟨(G.mem_neighborFinset h₅ x).mpr ha.symm, hx⟩
        rw [hh5isoempty] at this; exact absurd this (Finset.notMem_empty x)
    -- `Aset, Fset ⊆ Dᶜ` and disjoint.
    have hAsubS : Aset ⊆ Sset := by
      intro x hx; rw [hSsetdef]; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx)
    have hAsubDc : Aset ⊆ Dᶜ := hAsubS.trans hSsubDc
    have hFsubDc : Fset ⊆ Dᶜ := by rw [hFsetdef]; exact Finset.sdiff_subset
    have hAFdisj : Disjoint Aset Fset := by
      rw [hFsetdef]
      apply Finset.disjoint_left.mpr
      intro x hxA hxF
      exact (Finset.mem_sdiff.mp hxF).2 (hAsubS hxA)
    -- **Per-hub partition** of the internal neighbourhood into `A`- and `F`-parts.
    have hpartition : ∀ h : Fin 19, h ∈ Dᶜ →
        (G.neighborFinset h ∩ Dᶜ).card
          = (G.neighborFinset h ∩ Aset).card + (G.neighborFinset h ∩ Fset).card := by
      intro h hh
      obtain ⟨hnh1, hnh5⟩ := hnh1h5 h hh
      have hunion : G.neighborFinset h ∩ Dᶜ = (G.neighborFinset h ∩ Aset) ∪ (G.neighborFinset h ∩ Fset) := by
        apply Finset.ext; intro x
        simp only [Finset.mem_union, Finset.mem_inter]
        constructor
        · rintro ⟨hxN, hxDc⟩
          have hxSF : x ∈ Sset ∨ x ∈ Fset := by
            rw [hFsetdef]; by_cases hxS : x ∈ Sset
            · exact Or.inl hxS
            · exact Or.inr (Finset.mem_sdiff.mpr ⟨hxDc, hxS⟩)
          rcases hxSF with hxS | hxF
          · rw [hSsetdef, Finset.mem_insert, Finset.mem_insert] at hxS
            rcases hxS with rfl | rfl | hxA
            · exact absurd ((G.mem_neighborFinset h x).mp hxN) hnh1
            · exact absurd ((G.mem_neighborFinset h x).mp hxN) hnh5
            · exact Or.inl ⟨hxN, hxA⟩
          · exact Or.inr ⟨hxN, hxF⟩
        · rintro (⟨hxN, hxA⟩ | ⟨hxN, hxF⟩)
          · exact ⟨hxN, hAsubDc hxA⟩
          · exact ⟨hxN, hFsubDc hxF⟩
      rw [hunion, Finset.card_union_of_disjoint]
      exact Finset.disjoint_left.mpr (fun x hxA hxF =>
        (Finset.disjoint_left.mp hAFdisj) (Finset.mem_inter.mp hxA).2 (Finset.mem_inter.mp hxF).2)
    -- The two internal-degree sums.
    have hsumF12 : ∑ f ∈ Fset, (G.neighborFinset f ∩ Dᶜ).card = 12 := by
      rw [Finset.sum_congr rfl (fun f hf => (hFprop f hf).2.1), Finset.sum_const, smul_eq_mul,
        hFcard]
    have hsumA8 : ∑ a ∈ Aset, (G.neighborFinset a ∩ Dᶜ).card = 8 := by
      have hAint : ∀ a ∈ Aset, (G.neighborFinset a ∩ Dᶜ).card = 2 := by
        intro a ha
        rw [hAsetdef, Finset.mem_insert, Finset.mem_insert, Finset.mem_insert,
          Finset.mem_singleton] at ha
        rcases ha with rfl | rfl | rfl | rfl
        exacts [ha1int, ha2int, hb1int, hb2int]
      rw [Finset.sum_congr rfl hAint, Finset.sum_const, smul_eq_mul, hAcard]
    -- **Bipartite double count** `∑_F |N f ∩ A| = ∑_A |N a ∩ F|`.
    have hbip : ∑ f ∈ Fset, (G.neighborFinset f ∩ Aset).card
        = ∑ a ∈ Aset, (G.neighborFinset a ∩ Fset).card := by
      have key : ∀ s t : Finset (Fin 19), ∑ f ∈ s, (G.neighborFinset f ∩ t).card
          = ∑ f ∈ s, ∑ a ∈ t, (if G.Adj f a then 1 else 0) := by
        intro s t
        apply Finset.sum_congr rfl; intro f _
        rw [Finset.inter_comm, ← Finset.filter_mem_eq_inter, Finset.card_filter]
        apply Finset.sum_congr rfl; intro a _
        simp only [G.mem_neighborFinset]
      rw [key Fset Aset, key Aset Fset, Finset.sum_comm]
      apply Finset.sum_congr rfl; intro a _; apply Finset.sum_congr rfl; intro f _
      simp only [G.adj_comm]
    -- Combine to the master identity.
    have hsumFF : ∑ f ∈ Fset, (G.neighborFinset f ∩ Fset).card
        = 4 + ∑ a ∈ Aset, (G.neighborFinset a ∩ Aset).card := by
      have hF := Finset.sum_congr rfl (fun f (hf : f ∈ Fset) => hpartition f (hFsubDc hf))
      have hA := Finset.sum_congr rfl (fun a (ha : a ∈ Aset) => hpartition a (hAsubDc ha))
      rw [Finset.sum_add_distrib] at hF hA
      rw [hsumF12] at hF; rw [hsumA8] at hA
      omega
    -- **`F`-triangle helper.**  `∑_A |N a ∩ A| ≥ 6` ⟹ contradiction with `hntri1`.
    have Ftri : 6 ≤ ∑ a ∈ Aset, (G.neighborFinset a ∩ Aset).card → False := by
      intro hge6
      have hsumFF10 : 10 ≤ ∑ f ∈ Fset, (G.neighborFinset f ∩ Fset).card := by rw [hsumFF]; omega
      -- Two `F`-hubs are adjacent to all other `F`-hubs.
      set G3 := Fset.filter (fun f => (G.neighborFinset f ∩ Fset).card = 3) with hG3def
      have hFdeg3 : ∀ f ∈ Fset, (G.neighborFinset f ∩ Fset).card ≤ 3 := by
        intro f hf
        have hsub : G.neighborFinset f ∩ Fset ⊆ Fset.erase f := by
          intro x hx
          obtain ⟨hxN, hxF⟩ := Finset.mem_inter.mp hx
          refine Finset.mem_erase.mpr ⟨?_, hxF⟩
          intro he; exact G.irrefl (he ▸ (G.mem_neighborFinset f x).mp hxN)
        calc (G.neighborFinset f ∩ Fset).card ≤ (Fset.erase f).card := Finset.card_le_card hsub
          _ = Fset.card - 1 := Finset.card_erase_of_mem hf
          _ = 3 := by rw [hFcard]
      have hG3card : 2 ≤ G3.card := by
        by_contra hlt
        push Not at hlt
        -- if `≤ 1` full `F`-hub, the sum is `≤ 1·3 + 3·2 = 9 < 10`.
        have hbound : ∀ f ∈ Fset, (G.neighborFinset f ∩ Fset).card
            ≤ (if f ∈ G3 then 3 else 2) := by
          intro f hf
          by_cases hfG3 : f ∈ G3
          · simp only [hfG3, if_true]; exact hFdeg3 f hf
          · simp only [hfG3, if_false]
            have := hFdeg3 f hf
            rcases Nat.lt_or_ge (G.neighborFinset f ∩ Fset).card 3 with h | h
            · omega
            · exact absurd (Finset.mem_filter.mpr ⟨hf, by omega⟩) hfG3
        have hsle : ∑ f ∈ Fset, (G.neighborFinset f ∩ Fset).card
            ≤ ∑ f ∈ Fset, (if f ∈ G3 then 3 else 2) := Finset.sum_le_sum hbound
        have hsval : ∑ f ∈ Fset, (if f ∈ G3 then (3:ℕ) else 2) = 8 + G3.card := by
          have hpt : ∀ f, (if f ∈ G3 then (3:ℕ) else 2) = 2 + (if f ∈ G3 then 1 else 0) := by
            intro f; by_cases h : f ∈ G3 <;> simp [h]
          have hfe : (Fset.filter (fun f => f ∈ G3)).card = G3.card := by
            rw [Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr (Finset.filter_subset _ _)]
          rw [Finset.sum_congr rfl (fun f _ => hpt f), Finset.sum_add_distrib, Finset.sum_const,
            smul_eq_mul, hFcard, ← Finset.card_filter (fun f => f ∈ G3) Fset, hfe]
        omega
      obtain ⟨f1, hf1, f2, hf2, hf12⟩ := Finset.one_lt_card.mp hG3card
      obtain ⟨hf1F, hf1deg⟩ := Finset.mem_filter.mp hf1
      obtain ⟨hf2F, hf2deg⟩ := Finset.mem_filter.mp hf2
      -- `f1, f2` are each adjacent to every other `F`-hub.
      have hfull : ∀ f : Fin 19, (G.neighborFinset f ∩ Fset).card = 3 → f ∈ Fset →
          ∀ g : Fin 19, g ∈ Fset → g ≠ f → G.Adj f g := by
        intro f hfdeg hfF g hgF hgf
        by_contra hnadj
        have hsub : G.neighborFinset f ∩ Fset ⊆ (Fset.erase f).erase g := by
          intro x hx
          obtain ⟨hxN, hxF⟩ := Finset.mem_inter.mp hx
          have hadj := (G.mem_neighborFinset f x).mp hxN
          refine Finset.mem_erase.mpr ⟨?_, Finset.mem_erase.mpr ⟨?_, hxF⟩⟩
          · intro he; exact hnadj (he ▸ hadj)
          · intro he; exact G.irrefl (he ▸ hadj)
        have hc : ((Fset.erase f).erase g).card = 2 := by
          rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hgf, hgF⟩),
            Finset.card_erase_of_mem hfF, hFcard]
        have := Finset.card_le_card hsub; rw [hc, hfdeg] at this; omega
      have h12 : G.Adj f1 f2 := hfull f1 hf1deg hf1F f2 hf2F (Ne.symm hf12)
      -- pick a third `F`-hub `f3`.
      have hf12sub : ({f1, f2} : Finset (Fin 19)) ⊆ Fset := by
        intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl; exacts [hf1F, hf2F]
      have hf12card : ({f1, f2} : Finset (Fin 19)).card = 2 := by
        rw [Finset.card_insert_of_notMem (by simp [hf12]), Finset.card_singleton]
      have hthird : (Fset \ {f1, f2}).Nonempty := by
        rw [← Finset.card_pos, Finset.card_sdiff_of_subset hf12sub, hFcard, hf12card]; omega
      obtain ⟨f3, hf3⟩ := hthird
      obtain ⟨hf3F, hf3ne⟩ := Finset.mem_sdiff.mp hf3
      simp only [Finset.mem_insert, Finset.mem_singleton] at hf3ne
      push Not at hf3ne
      have h13 : G.Adj f1 f3 := hfull f1 hf1deg hf1F f3 hf3F hf3ne.1
      have h23 : G.Adj f2 f3 := hfull f2 hf2deg hf2F f3 hf3F hf3ne.2
      -- The triangle `f1–f2–f3` avoids the cherry, degree sum `12 ≤ 13`.
      obtain ⟨hf1d, _, hf1L1, hf1c1, hf1c2⟩ := hFprop f1 hf1F
      obtain ⟨hf2d, _, hf2L1, hf2c1, hf2c2⟩ := hFprop f2 hf2F
      obtain ⟨hf3d, _, hf3L1, hf3c1, hf3c2⟩ := hFprop f3 hf3F
      exact hntri1 ⟨f1, f2, f3, hFsubDc hf1F, hFsubDc hf2F, hFsubDc hf3F, h12, h13, h23,
        ⟨hf1L1, hf1c1, hf1c2⟩, ⟨hf2L1, hf2c1, hf2c2⟩, ⟨hf3L1, hf3c1, hf3c2⟩, by omega⟩
    -- `h₅` is non-adjacent to an `Iso` vertex whose closed structure is `{h₁, x, y}` with `x, y ≠ h₅`.
    have hNι : ∀ x y ι : Fin 19, x ≠ h₅ → y ≠ h₅ →
        G.neighborFinset ι = {h₁, x, y} → ¬G.Adj h₅ ι := by
      intro x y ι hxh5 hyh5 hNιeq hadj
      have : h₅ ∈ ({h₁, x, y} : Finset (Fin 19)) := by
        rw [← hNιeq]; exact (G.mem_neighborFinset ι h₅).mpr hadj.symm
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with h | h | h
      exacts [hne15 h.symm, hxh5 h.symm, hyh5 h.symm]
    -- The `ι`-neighbourhood identity `N ι = {h₁, x, y}` for an `Iso` vertex met by `h₁, x, y`.
    have hNι_eq : ∀ x y ι : Fin 19, ι ∈ Iso → G.Adj h₁ ι → G.Adj x ι → G.Adj y ι →
        h₁ ≠ x → h₁ ≠ y → x ≠ y → G.neighborFinset ι = {h₁, x, y} := by
      intro x y ι hιI hh1ι hxι hyι hne1x hne1y hxy
      have hcard3 : (G.neighborFinset ι).card = 3 := by
        rw [G.card_neighborFinset_eq_degree]; exact (hIsoprop ι hιI).1
      have hsub : ({h₁, x, y} : Finset (Fin 19)) ⊆ G.neighborFinset ι := by
        intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl | rfl
        · exact (G.mem_neighborFinset ι w).mpr hh1ι.symm
        · exact (G.mem_neighborFinset ι w).mpr hxι.symm
        · exact (G.mem_neighborFinset ι w).mpr hyι.symm
      have hc3 : ({h₁, x, y} : Finset (Fin 19)).card = 3 := by
        rw [Finset.card_insert_of_notMem (by simp [hne1x, hne1y]),
          Finset.card_insert_of_notMem (by simp [hxy]), Finset.card_singleton]
      exact (Finset.eq_of_subset_of_card_le hsub (by rw [hcard3, hc3])).symm
    -- **The fallback:** a shared-`Iso` non-adjacent cross pair ⟹ `False`.
    have hfallback : ∀ a a' b b' ιa ιa' ιb ιb' : Fin 19,
        a ∈ Dᶜ → a' ∈ Dᶜ → b ∈ Dᶜ → b' ∈ Dᶜ →
        a ∈ Aset → a' ∈ Aset → b ∈ Aset → b' ∈ Aset →
        G.degree a = 4 → G.degree a' = 4 → G.degree b = 4 → G.degree b' = 4 →
        a ≠ h₁ → a' ≠ h₁ → b ≠ h₁ →
        G.Adj a L₁ → G.Adj a' L₁ → G.Adj b L₂ → G.Adj b' L₂ →
        G.neighborFinset a ∩ P = {L₁} → G.neighborFinset a' ∩ P = {L₁} →
        G.neighborFinset b ∩ P = {L₂} → G.neighborFinset b' ∩ P = {L₂} →
        ιa ∈ Iso → ιa' ∈ Iso → ιb ∈ Iso → ιb' ∈ Iso →
        G.Adj a ιa → G.Adj a' ιa' → G.Adj b ιb → G.Adj b' ιb' →
        G.neighborFinset a ∩ Iso = {ιa} → G.neighborFinset a' ∩ Iso = {ιa'} →
        G.neighborFinset b ∩ Iso = {ιb} → G.neighborFinset b' ∩ Iso = {ιb'} →
        a ≠ a' → b ≠ b' → a ≠ b → a' ≠ b → a ≠ b' → a' ≠ b' →
        ¬G.Adj a b → ιa = ιb → False := by
      intro a a' b b' ιa ιa' ιb ιb' haDc ha'Dc hbDc hb'Dc haA ha'A hbA hb'A
        had ha'd hbd hb'd hah1 ha'h1 hbh1 haL1 ha'L1 hbL2 hb'L2 haNP ha'NP hbNP hb'NP
        hιaI hιa'I hιbI hιb'I haιa ha'ιa' hbιb hb'ιb' haNI ha'NI hbNI hb'NI
        haa' hbb' hab ha'b hab' ha'b' hnab hιeq
      -- Step A: some `A`-hub's `Iso` is outside `N h₁`.
      by_cases hout : ιa ∉ G.neighborFinset h₁ ∨ ιa' ∉ G.neighborFinset h₁ ∨
          ιb ∉ G.neighborFinset h₁ ∨ ιb' ∉ G.neighborFinset h₁
      · rcases hout with h | h | h | h
        · exact h1pairTwoHub a L₁ ιa haDc had (Or.inl rfl) haL1 hιaI haιa haNI haNP h
        · exact h1pairTwoHub a' L₁ ιa' ha'Dc ha'd (Or.inl rfl) ha'L1 hιa'I ha'ιa' ha'NI ha'NP h
        · exact h1pairTwoHub b L₂ ιb hbDc hbd (Or.inr rfl) hbL2 hιbI hbιb hbNI hbNP h
        · exact h1pairTwoHub b' L₂ ιb' hb'Dc hb'd (Or.inr rfl) hb'L2 hιb'I hb'ιb' hb'NI hb'NP h
      · push Not at hout
        obtain ⟨haN1, ha'N1, hbN1, hb'N1⟩ := hout
        -- Derived distinctness for `b'` and the four hubs vs `h₅`.
        have hb'h1 : b' ≠ h₁ := by
          intro he
          have : L₂ ∈ G.neighborFinset h₁ ∩ P := by
            rw [← he]; exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset b' L₂).mpr hb'L2, hL2P⟩
          rw [hNh1P, Finset.mem_singleton] at this; exact hL2c1 this
        have hleaf_ne_h5 : ∀ x : Fin 19, G.Adj x L₁ ∨ G.Adj x L₂ → x ≠ h₅ := by
          intro x hx he
          rcases hx with hx | hx
          · have : L₁ ∈ G.neighborFinset h₅ ∩ P :=
              Finset.mem_inter.mpr ⟨(G.mem_neighborFinset h₅ L₁).mpr (he ▸ hx), hL1P⟩
            rw [hNh5P, Finset.mem_singleton] at this; exact hL1nc2 this
          · have : L₂ ∈ G.neighborFinset h₅ ∩ P :=
              Finset.mem_inter.mpr ⟨(G.mem_neighborFinset h₅ L₂).mpr (he ▸ hx), hL2P⟩
            rw [hNh5P, Finset.mem_singleton] at this; exact hL2c2 this
        have hah5 : a ≠ h₅ := hleaf_ne_h5 a (Or.inl haL1)
        have ha'h5 : a' ≠ h₅ := hleaf_ne_h5 a' (Or.inl ha'L1)
        have hbh5 : b ≠ h₅ := hleaf_ne_h5 b (Or.inr hbL2)
        have hb'h5 : b' ≠ h₅ := hleaf_ne_h5 b' (Or.inr hb'L2)
        -- `ι := ιa = ιb`; `N ι = {h₁, a, b}`.
        have hh1ιa : G.Adj h₁ ιa := (G.mem_neighborFinset h₁ ιa).mp haN1
        have hbιa : G.Adj b ιa := by rw [hιeq]; exact hbιb
        have hNιa : G.neighborFinset ιa = {h₁, a, b} :=
          hNι_eq a b ιa hιaI hh1ιa haιa hbιa (Ne.symm hah1) (Ne.symm hbh1) hab
        have hn_h5ιa : ¬G.Adj h₅ ιa := hNι a b ιa hah5 hbh5 hNιa
        -- `ιa' ≠ ιa` and `ιb' ≠ ιa` (they are not in the full `N ιa = {h₁, a, b}`).
        have hιa'ne : ιa' ≠ ιa := by
          intro he
          have : a' ∈ ({h₁, a, b} : Finset (Fin 19)) := by
            rw [← hNιa]; exact (G.mem_neighborFinset ιa a').mpr (he ▸ ha'ιa').symm
          simp only [Finset.mem_insert, Finset.mem_singleton] at this
          rcases this with h | h | h
          exacts [ha'h1 h, haa'.symm h, ha'b h]
        have hιb'ne : ιb' ≠ ιa := by
          intro he
          have : b' ∈ ({h₁, a, b} : Finset (Fin 19)) := by
            rw [← hNιa]; exact (G.mem_neighborFinset ιa b').mpr (he ▸ hb'ιb').symm
          simp only [Finset.mem_insert, Finset.mem_singleton] at this
          rcases this with h | h | h
          exacts [hb'h1 h, hab'.symm h, hbb'.symm h]
        -- Rule out the two "half-cross" pairs via `crossTwoHub`, else both are adjacent.
        by_cases hAB' : G.Adj a b'
        · by_cases hA'B : G.Adj a' b
          · -- `a ~ b'` and `a' ~ b`.  Split on `ιa' = ιb'`.
            by_cases hιa'b' : ιa' = ιb'
            · -- Shared `t = ιa' = ιb'`: `h₅` avoids both `ιa` and `ιa'`, but needs `4` `Iso`-nbrs.
              have hh1ιa' : G.Adj h₁ ιa' := (G.mem_neighborFinset h₁ ιa').mp ha'N1
              have hb'ιa' : G.Adj b' ιa' := hιa'b' ▸ hb'ιb'
              have hNιa' : G.neighborFinset ιa' = {h₁, a', b'} :=
                hNι_eq a' b' ιa' hιa'I hh1ιa' ha'ιa' hb'ιa' (Ne.symm ha'h1) (Ne.symm hb'h1) ha'b'
              have hn_h5ιa' : ¬G.Adj h₅ ιa' := hNι a' b' ιa' ha'h5 hb'h5 hNιa'
              have hpair2 : ({ιa, ιa'} : Finset (Fin 19)) ⊆ Iso := by
                intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
                rcases hx with rfl | rfl; exacts [hιaI, hιa'I]
              have hsubT : G.neighborFinset h₅ ∩ Iso ⊆ Iso \ {ιa, ιa'} := by
                intro x hx
                obtain ⟨hxN, hxI⟩ := Finset.mem_inter.mp hx
                refine Finset.mem_sdiff.mpr ⟨hxI, ?_⟩
                simp only [Finset.mem_insert, Finset.mem_singleton]
                push Not
                exact ⟨fun he => hn_h5ιa (he ▸ (G.mem_neighborFinset h₅ x).mp hxN),
                  fun he => hn_h5ιa' (he ▸ (G.mem_neighborFinset h₅ x).mp hxN)⟩
              have hle := Finset.card_le_card hsubT
              rw [hh5iso4, Finset.card_sdiff_of_subset hpair2, hIsocard,
                Finset.card_insert_of_notMem (by simp [Ne.symm hιa'ne]), Finset.card_singleton] at hle
              omega
            · -- Distinct `ιa', ιb'`: `crossTwoHub` on `(a', b')` if non-adjacent, else `F`-triangle.
              by_cases hA'B' : G.Adj a' b'
              · -- Three cross edges `a~b', a'~b, a'~b'` ⟹ `∑_A |N∩A| ≥ 6` ⟹ `Ftri`.
                apply Ftri
                have hAeq : Aset = {a, a', b, b'} := by
                  refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
                  · intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
                    rcases hx with rfl | rfl | rfl | rfl
                    exacts [haA, ha'A, hbA, hb'A]
                  · rw [hAcard, Finset.card_insert_of_notMem (by simp [haa', hab, hab']),
                      Finset.card_insert_of_notMem (by simp [ha'b, ha'b']),
                      Finset.card_insert_of_notMem (by simp [hbb']), Finset.card_singleton]
                have hfa : 1 ≤ (G.neighborFinset a ∩ Aset).card :=
                  Finset.card_pos.mpr ⟨b', Finset.mem_inter.mpr ⟨(G.mem_neighborFinset a b').mpr hAB', hb'A⟩⟩
                have hfb : 1 ≤ (G.neighborFinset b ∩ Aset).card :=
                  Finset.card_pos.mpr ⟨a', Finset.mem_inter.mpr ⟨(G.mem_neighborFinset b a').mpr hA'B.symm, ha'A⟩⟩
                have hfa' : 2 ≤ (G.neighborFinset a' ∩ Aset).card := by
                  apply Finset.one_lt_card.mpr
                  exact ⟨b, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset a' b).mpr hA'B, hbA⟩,
                    b', Finset.mem_inter.mpr ⟨(G.mem_neighborFinset a' b').mpr hA'B', hb'A⟩, hbb'⟩
                have hfb' : 2 ≤ (G.neighborFinset b' ∩ Aset).card := by
                  apply Finset.one_lt_card.mpr
                  exact ⟨a, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset b' a).mpr hAB'.symm, haA⟩,
                    a', Finset.mem_inter.mpr ⟨(G.mem_neighborFinset b' a').mpr hA'B'.symm, ha'A⟩, haa'⟩
                rw [hAeq] at hfa hfb hfa' hfb'
                rw [hAeq, Finset.sum_insert (by simp [haa', hab, hab']),
                  Finset.sum_insert (by simp [ha'b, ha'b']),
                  Finset.sum_insert (by simp [hbb']), Finset.sum_singleton]
                omega
              · exact crossTwoHub a' b' ιa' ιb' ha'd hb'd ha'L1 hb'L2 ha'NP hb'NP hιa'I hιb'I
                  ha'ιa' hb'ιb' ha'NI hb'NI hA'B' hιa'b'
          · exact crossTwoHub a' b ιa' ιb ha'd hbd ha'L1 hbL2 ha'NP hbNP hιa'I hιbI
              ha'ιa' hbιb ha'NI hbNI hA'B (by rw [← hιeq]; exact hιa'ne)
        · exact crossTwoHub a b' ιa ιb' had hb'd haL1 hb'L2 haNP hb'NP hιaI hιb'I
            haιa hb'ιb' haNI hb'NI hAB' (Ne.symm hιb'ne)
    -- `A`-hub memberships.
    have ha1A : a1 ∈ Aset := by rw [hAsetdef]; simp
    have ha2A : a2 ∈ Aset := by rw [hAsetdef]; simp
    have hb1A : b1 ∈ Aset := by rw [hAsetdef]; simp
    have hb2A : b2 ∈ Aset := by rw [hAsetdef]; simp
    -- **Main case split** on cross adjacency.
    by_cases hAA : G.Adj a1 b1 ∧ G.Adj a1 b2 ∧ G.Adj a2 b1 ∧ G.Adj a2 b2
    · -- All four cross pairs adjacent ⟹ `∑_A |N ∩ A| ≥ 8 ≥ 6` ⟹ `Ftri`.
      obtain ⟨h11, h12', h21, h22⟩ := hAA
      apply Ftri
      have hf1 : 2 ≤ (G.neighborFinset a1 ∩ Aset).card := Finset.one_lt_card.mpr
        ⟨b1, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset a1 b1).mpr h11, hb1A⟩,
         b2, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset a1 b2).mpr h12', hb2A⟩, hb12⟩
      have hf2 : 2 ≤ (G.neighborFinset a2 ∩ Aset).card := Finset.one_lt_card.mpr
        ⟨b1, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset a2 b1).mpr h21, hb1A⟩,
         b2, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset a2 b2).mpr h22, hb2A⟩, hb12⟩
      have hf3 : 2 ≤ (G.neighborFinset b1 ∩ Aset).card := Finset.one_lt_card.mpr
        ⟨a1, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset b1 a1).mpr h11.symm, ha1A⟩,
         a2, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset b1 a2).mpr h21.symm, ha2A⟩, ha12⟩
      have hf4 : 2 ≤ (G.neighborFinset b2 ∩ Aset).card := Finset.one_lt_card.mpr
        ⟨a1, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset b2 a1).mpr h12'.symm, ha1A⟩,
         a2, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset b2 a2).mpr h22.symm, ha2A⟩, ha12⟩
      rw [hAsetdef, Finset.sum_insert (by simp [ha12, hab11, hab12]),
        Finset.sum_insert (by simp [hab21, hab22]),
        Finset.sum_insert (by simp [hb12]), Finset.sum_singleton]
      rw [hAsetdef] at hf1 hf2 hf3 hf4
      omega
    · -- Some cross pair is non-adjacent.
      simp only [not_and_or] at hAA
      rcases hAA with h | h | h | h
      · by_cases hιe : ιa1 = ιb1
        · exact hfallback a1 a2 b1 b2 ιa1 ιa2 ιb1 ιb2 ha1Dc ha2Dc hb1Dc hb2Dc ha1A ha2A hb1A hb2A
            ha1d ha2d hb1d hb2d ha1_1 ha2_1 hb1_1 ha1L1 ha2L1 hb1L2 hb2L2 ha1NP ha2NP hb1NP hb2NP
            hιa1I hιa2I hιb1I hιb2I ha1ι ha2ι hb1ι hb2ι ha1isoeq ha2isoeq hb1isoeq hb2isoeq
            ha12 hb12 hab11 hab21 hab12 hab22 h hιe
        · exact crossTwoHub a1 b1 ιa1 ιb1 ha1d hb1d ha1L1 hb1L2 ha1NP hb1NP hιa1I hιb1I
            ha1ι hb1ι ha1isoeq hb1isoeq h hιe
      · by_cases hιe : ιa1 = ιb2
        · exact hfallback a1 a2 b2 b1 ιa1 ιa2 ιb2 ιb1 ha1Dc ha2Dc hb2Dc hb1Dc ha1A ha2A hb2A hb1A
            ha1d ha2d hb2d hb1d ha1_1 ha2_1 hb2_1 ha1L1 ha2L1 hb2L2 hb1L2 ha1NP ha2NP hb2NP hb1NP
            hιa1I hιa2I hιb2I hιb1I ha1ι ha2ι hb2ι hb1ι ha1isoeq ha2isoeq hb2isoeq hb1isoeq
            ha12 (Ne.symm hb12) hab12 hab22 hab11 hab21 h hιe
        · exact crossTwoHub a1 b2 ιa1 ιb2 ha1d hb2d ha1L1 hb2L2 ha1NP hb2NP hιa1I hιb2I
            ha1ι hb2ι ha1isoeq hb2isoeq h hιe
      · by_cases hιe : ιa2 = ιb1
        · exact hfallback a2 a1 b1 b2 ιa2 ιa1 ιb1 ιb2 ha2Dc ha1Dc hb1Dc hb2Dc ha2A ha1A hb1A hb2A
            ha2d ha1d hb1d hb2d ha2_1 ha1_1 hb1_1 ha2L1 ha1L1 hb1L2 hb2L2 ha2NP ha1NP hb1NP hb2NP
            hιa2I hιa1I hιb1I hιb2I ha2ι ha1ι hb1ι hb2ι ha2isoeq ha1isoeq hb1isoeq hb2isoeq
            (Ne.symm ha12) hb12 hab21 hab11 hab22 hab12 h hιe
        · exact crossTwoHub a2 b1 ιa2 ιb1 ha2d hb1d ha2L1 hb1L2 ha2NP hb1NP hιa2I hιb1I
            ha2ι hb1ι ha2isoeq hb1isoeq h hιe
      · by_cases hιe : ιa2 = ιb2
        · exact hfallback a2 a1 b2 b1 ιa2 ιa1 ιb2 ιb1 ha2Dc ha1Dc hb2Dc hb1Dc ha2A ha1A hb2A hb1A
            ha2d ha1d hb2d hb1d ha2_1 ha1_1 hb2_1 ha2L1 ha1L1 hb2L2 hb1L2 ha2NP ha1NP hb2NP hb1NP
            hιa2I hιa1I hιb2I hιb1I ha2ι ha1ι hb2ι hb1ι ha2isoeq ha1isoeq hb2isoeq hb1isoeq
            (Ne.symm ha12) (Ne.symm hb12) hab22 hab12 hab21 hab11 h hιe
        · exact crossTwoHub a2 b2 ιa2 ιb2 ha2d hb2d ha2L1 hb2L2 ha2NP hb2NP hιa2I hιb2I
            ha2ι hb2ι ha2isoeq hb2isoeq h hιe

set_option maxHeartbeats 1600000 in
/-- **The `n = 19` dense-cherry `|D| ∈ {9, 10}` isolated-hub kernel (fully proven).**

`|D| = 9` (`10` hubs, `∑ int = 20`, `∑ deg = 41 = 5 + 9·4`, avoiders `≥ 6`): the anchor count
`anchor_isolated_count_nineteen` yields `≥ 2` internally-isolated hubs, and — with exactly one
degree-`5` hub — an internally-isolated degree-`4` hub always exists.  ISO2 (`≥ 2` such hubs)
closes via `isolated_pair_iso_rich_nineteen` + `two_isolated_hub_twohubconfig_d9_ff4` against
`hth`.  ISO1 splits on `cinc h₁`: `cinc h₁ ≥ 2` closes via the counting dichotomy
`iso1_dichotomy_to_false` (`TwoTwin ∨ TwoHub`, both excluded); `cinc h₁ = 1` with the
cherry-neighbour an interior `c`-vertex is the hard near-`K₅` sub-case
`iso1_hard_c_subcase_nineteen` (consuming `hntri1`, resp. `hntri2` through the `P₄` reflection
`(L₁, c₁, c₂, L₂) ↦ (L₂, c₂, c₁, L₁)`); otherwise `h₁` is a `TwoTwinConfig` centre avoiding a full
cherry `P₃`, contradicting `htt` (`twotwin_of_centre_nineteen`).

`|D| = 10` (`9` hubs, `∑ int = 14`, `∑ deg = 38`, avoiders `≥ 5`): with every hub of degree `≤ 5`
the budget `14 < 3·5` is already contradictory (`budget_contra_gen`).  A degree-`6` hub `h6` pins
the eight other hubs to degree `4` (`38 = 6 + 8·4`), and the anchor applied to the `h6`-erased
avoider sets (`9 + 4 + 4 ≤ 14 + iso`) forces `≥ 3` internally-isolated hubs, hence `≥ 2`
internally-isolated degree-`4` hubs — the ISO2 pair machinery closes, so the degree-`6` ISO1
residual is arithmetically empty and no separate `cinc` kernel is needed there. -/
theorem iso1_dense_corner_nineteen (G : SimpleGraph (Fin 19))
    (D Iso : Finset (Fin 19)) (L₁ c₁ c₂ L₂ : Fin 19)
    (h3 : ∀ v : Fin 19, 3 ≤ G.degree v)
    (hmemD : ∀ v : Fin 19, v ∈ D ↔ G.degree v = 3)
    (hIsoprop : ∀ v ∈ Iso, G.degree v = 3 ∧ (∀ w : Fin 19, G.Adj v w → G.degree w ≠ 3))
    (hisochar : ∀ w : Fin 19, w ∈ D → w ≠ L₁ → w ≠ c₁ → w ≠ c₂ → w ≠ L₂ → w ∈ Iso)
    (hL1deg : G.degree L₁ = 3) (hc1deg : G.degree c₁ = 3)
    (hc2deg : G.degree c₂ = 3) (hL2deg : G.degree L₂ = 3)
    (hac1L1 : G.Adj c₁ L₁) (hc12 : G.Adj c₁ c₂) (hac2L2 : G.Adj c₂ L₂)
    (hL1nc2 : L₁ ≠ c₂) (hL2nc1 : L₂ ≠ c₁)
    (hNc1D : G.neighborFinset c₁ ∩ D = {c₂, L₁}) (hNc2D : G.neighborFinset c₂ ∩ D = {c₁, L₂})
    (hL1D : L₁ ∈ D) (hc1D : c₁ ∈ D) (hc2D : c₂ ∈ D) (hL2D : L₂ ∈ D)
    (hd_lb : 9 ≤ D.card) (hd_ub : D.card ≤ 11) (htt : ¬TwoTwinConfig G)
    (hth : ¬TwoHubConfig G)
    (hT : ¬∃ x y z : Fin 19, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    (hC4 : ¬∃ a b c d : Fin 19, ({a, b, c, d} : Finset (Fin 19)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (hDccard : Dᶜ.card = 19 - D.card) (_hIsocard : Iso.card = D.card - 4)
    (hc1hub : (G.neighborFinset c₁ ∩ Dᶜ).card = 1)
    (hc2hub : (G.neighborFinset c₂ ∩ Dᶜ).card = 1)
    (hL1hub : (G.neighborFinset L₁ ∩ Dᶜ).card = 2)
    (hL2hub : (G.neighborFinset L₂ ∩ Dᶜ).card = 2)
    (hsumPath : ∑ g ∈ Dᶜ, (G.neighborFinset g ∩ ({L₁, c₁, c₂, L₂} : Finset (Fin 19))).card = 6)
    (hsumIso : ∑ g ∈ Dᶜ, (G.neighborFinset g ∩ Iso).card = 3 * (D.card - 4))
    (hsumInternal : ∑ g ∈ Dᶜ, (G.neighborFinset g ∩ Dᶜ).card = 74 - 6 * D.card)
    (hper : ∀ g : Fin 19, g ∈ Dᶜ →
      (G.neighborFinset g ∩ ({L₁, c₁, c₂, L₂} : Finset (Fin 19))).card
        + (G.neighborFinset g ∩ Iso).card + (G.neighborFinset g ∩ Dᶜ).card = G.degree g)
    (hntri1 : ¬∃ a b c : Fin 19, a ∈ Dᶜ ∧ b ∈ Dᶜ ∧ c ∈ Dᶜ ∧
      G.Adj a b ∧ G.Adj a c ∧ G.Adj b c ∧
      (¬G.Adj a L₁ ∧ ¬G.Adj a c₁ ∧ ¬G.Adj a c₂) ∧
      (¬G.Adj b L₁ ∧ ¬G.Adj b c₁ ∧ ¬G.Adj b c₂) ∧
      (¬G.Adj c L₁ ∧ ¬G.Adj c c₁ ∧ ¬G.Adj c c₂) ∧
      G.degree a + G.degree b + G.degree c ≤ 13)
    (hntri2 : ¬∃ a b c : Fin 19, a ∈ Dᶜ ∧ b ∈ Dᶜ ∧ c ∈ Dᶜ ∧
      G.Adj a b ∧ G.Adj a c ∧ G.Adj b c ∧
      (¬G.Adj a c₁ ∧ ¬G.Adj a c₂ ∧ ¬G.Adj a L₂) ∧
      (¬G.Adj b c₁ ∧ ¬G.Adj b c₂ ∧ ¬G.Adj b L₂) ∧
      (¬G.Adj c c₁ ∧ ¬G.Adj c c₂ ∧ ¬G.Adj c L₂) ∧
      G.degree a + G.degree b + G.degree c ≤ 13)
    (hcase : D.card = 9 ∨ D.card = 10) :
    False := by
  classical
  set P : Finset (Fin 19) := {L₁, c₁, c₂, L₂} with hPdef
  -- Every hub has degree `≥ 4`.
  have hge4 : ∀ g : Fin 19, g ∈ Dᶜ → 4 ≤ G.degree g := by
    intro g hg
    have hgD : g ∉ D := Finset.mem_compl.mp hg
    have : G.degree g ≠ 3 := fun he => hgD ((hmemD g).mpr he)
    have := h3 g
    omega
  -- Hub degree total `∑_{Dᶜ} deg = 68 − 3|D|`.
  have hsumdeg : ∑ g ∈ Dᶜ, G.degree g = 68 - 3 * D.card := by
    have hcong : ∑ g ∈ Dᶜ, ((G.neighborFinset g ∩ P).card
        + (G.neighborFinset g ∩ Iso).card + (G.neighborFinset g ∩ Dᶜ).card)
        = ∑ g ∈ Dᶜ, G.degree g := Finset.sum_congr rfl hper
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hsumPath, hsumIso, hsumInternal] at hcong
    omega
  -- The (W) fact for degree-`≤ 5` hubs.
  have hW := cherry_p4_W_facts_nineteen G D Iso L₁ c₁ c₂ L₂ hIsoprop hL1deg hc1deg hc2deg hL2deg
    hac1L1 hc12 hac2L2 hL1nc2 hL2nc1 hL1D hc1D hc2D hL2D htt
  -- Classification of `D`.
  have hclassP : ∀ x : Fin 19, x ∈ D → x = L₁ ∨ x = c₁ ∨ x = c₂ ∨ x = L₂ ∨ x ∈ Iso := by
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
  have hclassA1 : ∀ g : Fin 19, g ∈ A1 → ∀ x : Fin 19, G.Adj g x → x ∈ D → x = L₂ ∨ x ∈ Iso := by
    intro g hg x hadj hxD
    rw [hA1def, Finset.mem_filter] at hg
    obtain ⟨_, hgL1, hgc1, hgc2⟩ := hg
    rcases hclassP x hxD with h | h | h | h | h
    · exact absurd (h ▸ hadj) hgL1
    · exact absurd (h ▸ hadj) hgc1
    · exact absurd (h ▸ hadj) hgc2
    · exact Or.inl h
    · exact Or.inr h
  have hclassA2 : ∀ g : Fin 19, g ∈ A2 → ∀ x : Fin 19, G.Adj g x → x ∈ D → x = L₁ ∨ x ∈ Iso := by
    intro g hg x hadj hxD
    rw [hA2def, Finset.mem_filter] at hg
    obtain ⟨_, hgc1, hgc2, hgL2⟩ := hg
    rcases hclassP x hxD with h | h | h | h | h
    · exact Or.inl h
    · exact absurd (h ▸ hadj) hgc1
    · exact absurd (h ▸ hadj) hgc2
    · exact absurd (h ▸ hadj) hgL2
    · exact Or.inr h
  have hclassFF : ∀ g : Fin 19, g ∈ FF → ∀ x : Fin 19, G.Adj g x → x ∈ D → x ∈ Iso := by
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
  have getA2pred : ∀ g : Fin 19, g ∈ A2 →
      ¬G.Adj g c₁ ∧ ¬G.Adj g c₂ ∧ ¬G.Adj g L₂ := by
    intro g hg; rw [hA2def, Finset.mem_filter] at hg; exact hg.2
  have getA1pred : ∀ g : Fin 19, g ∈ A1 →
      ¬G.Adj g L₁ ∧ ¬G.Adj g c₁ ∧ ¬G.Adj g c₂ := by
    intro g hg; rw [hA1def, Finset.mem_filter] at hg; exact hg.2
  -- Cherry non-adjacencies (`L₁ ≠ L₂` plus the cross non-edges).
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
  -- `¬ G.Adj L₁ L₂`: `L₁`'s unique `D`-neighbour is `c₁`, and `L₂ ≠ c₁`.
  have hnL1L2 : ¬G.Adj L₁ L₂ := by
    intro hadj
    have hmem : L₂ ∈ G.neighborFinset L₁ ∩ D :=
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset L₁ L₂).mpr hadj, hL2D⟩
    have hc1mem : c₁ ∈ G.neighborFinset L₁ ∩ D :=
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset L₁ c₁).mpr hac1L1.symm, hc1D⟩
    have hdisjDc : Disjoint (G.neighborFinset L₁ ∩ D) (G.neighborFinset L₁ ∩ Dᶜ) := by
      apply Finset.disjoint_left.mpr; intro a ha hb
      exact (Finset.mem_compl.mp (Finset.mem_inter.mp hb).2) (Finset.mem_inter.mp ha).2
    have hunionDc : (G.neighborFinset L₁ ∩ D) ∪ (G.neighborFinset L₁ ∩ Dᶜ)
        = G.neighborFinset L₁ := by
      rw [← Finset.inter_union_distrib_left, Finset.union_compl, Finset.inter_univ]
    have hsplit : (G.neighborFinset L₁ ∩ D).card + (G.neighborFinset L₁ ∩ Dᶜ).card
        = G.degree L₁ := by
      rw [← Finset.card_union_of_disjoint hdisjDc, hunionDc, G.card_neighborFinset_eq_degree]
    rw [hL1deg, hL1hub] at hsplit
    have hone : (G.neighborFinset L₁ ∩ D).card = 1 := by omega
    have hsub : ({c₁, L₂} : Finset (Fin 19)) ⊆ G.neighborFinset L₁ ∩ D := by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hc1mem
      · exact hmem
    have hcard2 : ({c₁, L₂} : Finset (Fin 19)).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simp [Ne.symm hL2nc1]), Finset.card_singleton]
    have := Finset.card_le_card hsub
    rw [hcard2, hone] at this; omega
  -- Dispatch on `|D|` (`hcase`).
  rcases hcase with hD9 | hD10
  · -- **`|D| = 9`** (`10` hubs, `∑ int = 20`, `∑ deg = 41 = 5 + 9·4`, avoiders `≥ 6`).
    have hDc10 : Dᶜ.card = 10 := by rw [hDccard, hD9]
    have hint20 : ∑ g ∈ Dᶜ, (G.neighborFinset g ∩ Dᶜ).card = 20 := by rw [hsumInternal, hD9]
    have hdeg41 : ∑ g ∈ Dᶜ, G.degree g = 41 := by rw [hsumdeg, hD9]
    have hA1c6 : 6 ≤ A1.card := by rw [hDc10] at hA1card_lb; omega
    have hA2c6 : 6 ≤ A2.card := by rw [hDc10] at hA2card_lb; omega
    have hdeg5 : ∀ g : Fin 19, g ∈ Dᶜ → G.degree g ≤ 5 := by
      intro g hg
      have := hub_deg_upper_pt Dᶜ (fun v => G.degree v) 41 hge4 hdeg41 g hg
      rw [hDc10] at this; omega
    -- Avoider internal-degree lower bounds.
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
    -- **STEP 1 (anchor).**  `≥ 2` internally-isolated hubs, hence (with `≤ 1` degree-`5` hub) at
    -- least one internally-isolated degree-`4` hub.
    have hanchor := anchor_isolated_count_nineteen Dᶜ A1 A2 FF
      (fun g => (G.neighborFinset g ∩ Dᶜ).card) 20 hA1sub hA2sub hFFdef hA1int hA2int hFFint hint20
    set ISL := (Dᶜ \ (A1 ∪ A2)).filter (fun g => (G.neighborFinset g ∩ Dᶜ).card = 0) with hISLdef
    have hISLsubDc : ISL ⊆ Dᶜ := by
      rw [hISLdef]; exact (Finset.filter_subset _ _).trans Finset.sdiff_subset
    have hISL2 : 2 ≤ ISL.card := by rw [hDc10] at hanchor; omega
    -- Exactly one degree-`5` hub in `Dᶜ` (since `∑ deg = 41 = 5 + 9·4`).
    have hdeg5count : (Dᶜ.filter (fun g => G.degree g = 5)).card = 1 := by
      have hpart := Finset.sum_filter_add_sum_filter_not Dᶜ (fun g => G.degree g = 5)
        (fun g => G.degree g)
      have h4 : ∀ g ∈ Dᶜ.filter (fun g => ¬ G.degree g = 5), G.degree g = 4 := by
        intro g hg
        rw [Finset.mem_filter] at hg
        have := hge4 g hg.1; have := hdeg5 g hg.1; omega
      have h5 : ∀ g ∈ Dᶜ.filter (fun g => G.degree g = 5), G.degree g = 5 := by
        intro g hg; exact (Finset.mem_filter.mp hg).2
      rw [Finset.sum_congr rfl h5, Finset.sum_congr rfl h4, Finset.sum_const, Finset.sum_const,
        smul_eq_mul, smul_eq_mul] at hpart
      have hcc : (Dᶜ.filter (fun g => G.degree g = 5)).card
          + (Dᶜ.filter (fun g => ¬ G.degree g = 5)).card = 10 := by
        rw [Finset.card_filter_add_card_filter_not]; exact hDc10
      rw [hdeg41] at hpart; omega
    -- The internally-isolated degree-`4` hubs.
    set ID4 := ISL.filter (fun g => G.degree g = 4) with hID4def
    have hID4_1 : 1 ≤ ID4.card := by
      have hle5 : (ISL.filter (fun g => G.degree g = 5)).card ≤ 1 := by
        rw [← hdeg5count]
        exact Finset.card_le_card (Finset.filter_subset_filter _ hISLsubDc)
      have hpartISL := Finset.card_filter_add_card_filter_not (s := ISL)
        (p := fun g => G.degree g = 5)
      have h45 : ISL.filter (fun g => ¬ G.degree g = 5) = ID4 := by
        rw [hID4def]; apply Finset.filter_congr
        intro g hg
        have hgDc := hISLsubDc hg
        have := hge4 g hgDc; have := hdeg5 g hgDc
        constructor <;> intro <;> omega
      rw [h45] at hpartISL; omega
    -- Extractor: an `ID4` member is an internally-isolated degree-`4` hub.
    have hID4prop : ∀ g ∈ ID4, g ∈ Dᶜ ∧ G.neighborFinset g ∩ Dᶜ = ∅ ∧ G.degree g = 4 := by
      intro g hg
      rw [hID4def, Finset.mem_filter] at hg
      obtain ⟨hgISL, hgd⟩ := hg
      have hgDc := hISLsubDc hgISL
      rw [hISLdef, Finset.mem_filter] at hgISL
      exact ⟨hgDc, Finset.card_eq_zero.mp hgISL.2, hgd⟩
    -- **STEP 2/3.**  Dichotomy on a *second* internally-isolated degree-`4` hub.
    by_cases hISO2 : 2 ≤ ID4.card
    · -- **ISO2** (`≥ 2` isolated degree-`4` hubs).
      obtain ⟨h₁, hh1ID4, h₂, hh2ID4, hne12⟩ := Finset.one_lt_card.mp hISO2
      obtain ⟨hh1Dc, hh10, hh1d⟩ := hID4prop h₁ hh1ID4
      obtain ⟨hh2Dc, hh20, hh2d⟩ := hID4prop h₂ hh2ID4
      have hrich := isolated_pair_iso_rich_nineteen G D Iso L₁ c₁ c₂ L₂ h₁ h₂ hT hC4 hclassP
        hIsoprop hac1L1 hc12 hac2L2 hnc1L2 hnc2L1 hL1nc2 hL2nc1 hL1deg hc1deg hc2deg hL2deg
        hh2Dc hh1d hh2d hh10 hh20 hne12 hnL1L2
      rcases hrich with hrich | hrich
      · exact hth (two_isolated_hub_twohubconfig_d9_ff4 G D Iso L₁ c₁ c₂ L₂ h₁ h₂ hC4 hmemD hIsoD
          hclassP hIsoprop hac1L1 hc12 hac2L2 hc1deg hc2deg hh1Dc hh2Dc hh1d hh2d hh10 hh20
          hne12 hrich)
      · exact hth (two_isolated_hub_twohubconfig_d9_ff4 G D Iso L₁ c₁ c₂ L₂ h₂ h₁ hC4 hmemD hIsoD
          hclassP hIsoprop hac1L1 hc12 hac2L2 hc1deg hc2deg hh2Dc hh1Dc hh2d hh1d hh20 hh10
          hne12.symm hrich)
    · -- **ISO1** (exactly one isolated degree-`4` hub `h₁`): split on `cinc h₁`.
      have hID4_eq1 : ID4.card = 1 := by omega
      obtain ⟨h₁, hID4_h1⟩ := Finset.card_eq_one.mp hID4_eq1
      have hh1ID4 : h₁ ∈ ID4 := by rw [hID4_h1]; exact Finset.mem_singleton_self h₁
      obtain ⟨hh1Dc, hh1iso, hh1d⟩ := hID4prop h₁ hh1ID4
      obtain ⟨h₅, hf5⟩ := Finset.card_eq_one.mp hdeg5count
      have hh5mem : h₅ ∈ Dᶜ.filter (fun g => G.degree g = 5) := by
        rw [hf5]; exact Finset.mem_singleton_self h₅
      obtain ⟨hh5Dc, hh5d⟩ := Finset.mem_filter.mp hh5mem
      have hne15 : h₁ ≠ h₅ := fun he => by rw [he, hh5d] at hh1d; exact absurd hh1d (by norm_num)
      have hdegOth : ∀ h : Fin 19, h ∈ Dᶜ → h ≠ h₁ → h ≠ h₅ → G.degree h = 4 := by
        intro h hhDc _ hh5
        have h4 := hge4 h hhDc; have h5 := hdeg5 h hhDc
        rcases (by omega : G.degree h = 4 ∨ G.degree h = 5) with h4' | h5'
        · exact h4'
        · exfalso; apply hh5
          have hm : h ∈ Dᶜ.filter (fun g => G.degree g = 5) := Finset.mem_filter.mpr ⟨hhDc, h5'⟩
          rw [hf5, Finset.mem_singleton] at hm; exact hm
      have hHub10 : Dᶜ.card = 10 := hDc10
      have hsumIso15 : ∑ h ∈ Dᶜ, (G.neighborFinset h ∩ Iso).card = 15 := by rw [hsumIso, hD9]
      -- Cherry vertices are non-`Iso`; `h₁ ≠` each cherry vertex.
      have hc1nIso : c₁ ∉ Iso := fun h => (hIsoprop c₁ h).2 L₁ hac1L1 hL1deg
      have hc2nIso : c₂ ∉ Iso := fun h => (hIsoprop c₂ h).2 c₁ hc12.symm hc1deg
      have hL1nIso : L₁ ∉ Iso := fun h => (hIsoprop L₁ h).2 c₁ hac1L1.symm hc1deg
      have hL2nIso : L₂ ∉ Iso := fun h => (hIsoprop L₂ h).2 c₂ hac2L2.symm hc2deg
      have hh1nc1 : h₁ ≠ c₁ := fun he => by rw [he, hc1deg] at hh1d; exact absurd hh1d (by norm_num)
      have hh1nc2 : h₁ ≠ c₂ := fun he => by rw [he, hc2deg] at hh1d; exact absurd hh1d (by norm_num)
      have hh1nL1 : h₁ ≠ L₁ := fun he => by rw [he, hL1deg] at hh1d; exact absurd hh1d (by norm_num)
      have hh1nL2 : h₁ ≠ L₂ := fun he => by rw [he, hL2deg] at hh1d; exact absurd hh1d (by norm_num)
      by_cases hcinc2 : 2 ≤ (G.neighborFinset h₁ ∩ P).card
      · -- **`cinc h₁ ≥ 2`** — the completed counting dichotomy.
        exact iso1_dichotomy_to_false G D Iso L₁ c₁ c₂ L₂ h₁ h₅ hmemD hIsoD hIsoprop hclassP
          hL1deg hc1deg hc2deg hL2deg hac1L1 hc12 hac2L2 hL1nc2 hL2nc1 hNc1D hNc2D hL1D hc1D hc2D
          hL2D htt hth hT hC4 hHub10 hdeg5 hper hsumIso15 hh1Dc hh1d hh1iso hcinc2 hh5Dc hh5d hne15
          hdegOth
      · -- **`cinc h₁ ≤ 1`** — `h₁` avoids a cherry `P₃` unless its lone cherry-neighbour is a `c`.
        have hh1int0 : (G.neighborFinset h₁ ∩ Dᶜ).card = 0 := by rw [hh1iso]; exact Finset.card_empty
        have hisoge2 : 2 ≤ (G.neighborFinset h₁ ∩ Iso).card := by
          have hdec1 := hper h₁ hh1Dc
          rw [hh1int0, hh1d] at hdec1
          omega
        by_cases hRc1 : G.Adj h₁ c₁
        · exact iso1_hard_c_subcase_nineteen G D Iso L₁ c₁ c₂ L₂ h₁ h₅ hmemD hIsoprop hclassP
            hL1deg hc1deg hc2deg hL2deg hac1L1 hc12 hac2L2 hL1nc2 hL2nc1 hNc1D hNc2D
            hL1D hc1D hc2D hL2D htt hth hT hC4 hHub10 (by rw [_hIsocard, hD9]) hdeg5 hper hsumPath
            hsumIso15 hc1hub hc2hub hL1hub hL2hub hh1Dc hh1d hh1iso hRc1 (by rw [← hPdef]; omega)
            hh5Dc hh5d hne15 hdegOth hntri1
        by_cases hRc2 : G.Adj h₁ c₂
        · -- `h₁` meets `c₂`: apply the lemma with `(L₁,c₁,c₂,L₂) ↦ (L₂,c₂,c₁,L₁)`.
          have hPeq : ({L₂, c₂, c₁, L₁} : Finset (Fin 19)) = {L₁, c₁, c₂, L₂} := by
            ext x
            simp only [Finset.mem_insert, Finset.mem_singleton]
            constructor <;> rintro (rfl | rfl | rfl | rfl) <;> simp
          have hclassP' : ∀ x : Fin 19, x ∈ D → x = L₂ ∨ x = c₂ ∨ x = c₁ ∨ x = L₁ ∨ x ∈ Iso := by
            intro x hx; rcases hclassP x hx with h | h | h | h | h <;> simp [h]
          have hper' : ∀ h : Fin 19, h ∈ Dᶜ →
              (G.neighborFinset h ∩ ({L₂, c₂, c₁, L₁} : Finset (Fin 19))).card
                + (G.neighborFinset h ∩ Iso).card + (G.neighborFinset h ∩ Dᶜ).card = G.degree h := by
            intro h hh; rw [hPeq]; exact hper h hh
          have hsumPath' : ∑ g ∈ Dᶜ,
              (G.neighborFinset g ∩ ({L₂, c₂, c₁, L₁} : Finset (Fin 19))).card = 6 := by
            rw [Finset.sum_congr rfl (fun g _ => by rw [hPeq])]; exact hsumPath
          have hntri1' : ¬∃ a b c : Fin 19, a ∈ Dᶜ ∧ b ∈ Dᶜ ∧ c ∈ Dᶜ ∧
              G.Adj a b ∧ G.Adj a c ∧ G.Adj b c ∧
              (¬G.Adj a L₂ ∧ ¬G.Adj a c₂ ∧ ¬G.Adj a c₁) ∧
              (¬G.Adj b L₂ ∧ ¬G.Adj b c₂ ∧ ¬G.Adj b c₁) ∧
              (¬G.Adj c L₂ ∧ ¬G.Adj c c₂ ∧ ¬G.Adj c c₁) ∧
              G.degree a + G.degree b + G.degree c ≤ 13 := by
            rintro ⟨a, b, c, haD, hbD, hcD, hab, hac, hbc,
              ⟨haL2, hac2, hac1⟩, ⟨hbL2, hbc2, hbc1⟩, ⟨hcL2, hcc2, hcc1⟩, hdeg⟩
            exact hntri2 ⟨a, b, c, haD, hbD, hcD, hab, hac, hbc,
              ⟨hac1, hac2, haL2⟩, ⟨hbc1, hbc2, hbL2⟩, ⟨hcc1, hcc2, hcL2⟩, hdeg⟩
          exact iso1_hard_c_subcase_nineteen G D Iso L₂ c₂ c₁ L₁ h₁ h₅ hmemD hIsoprop hclassP'
            hL2deg hc2deg hc1deg hL1deg hac2L2 hc12.symm hac1L1 hL2nc1 hL1nc2 hNc2D hNc1D
            hL2D hc2D hc1D hL1D htt hth hT hC4 hHub10 (by rw [_hIsocard, hD9]) hdeg5 hper' hsumPath'
            hsumIso15 hc2hub hc1hub hL2hub hL1hub hh1Dc hh1d hh1iso hRc2
            (by rw [hPeq, ← hPdef]; omega) hh5Dc hh5d hne15 hdegOth hntri1'
        by_cases hRL2 : G.Adj h₁ L₂
        · -- lone cherry-neighbour is `L₂`; `h₁` avoids the cherry `P₃` `L₁–c₁–c₂`.
          have hnL1 : ¬G.Adj h₁ L₁ := by
            intro hL1a
            have hsub : ({L₁, L₂} : Finset (Fin 19)) ⊆
                G.neighborFinset h₁ ∩ P := by
              intro w hw
              simp only [Finset.mem_insert, Finset.mem_singleton] at hw
              rcases hw with rfl | rfl
              · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hL1a, by simp [hPdef]⟩
              · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hRL2, by simp [hPdef]⟩
            have hcard : ({L₁, L₂} : Finset (Fin 19)).card = 2 := by
              rw [Finset.card_insert_of_notMem (by simp [hL1L2]), Finset.card_singleton]
            have := Finset.card_le_card hsub; omega
          exact absurd (twotwin_of_centre_nineteen G Iso h₁ L₁ c₁ c₂ hIsoprop hL1deg hc1deg hc2deg
            (by omega) hac1L1.symm hc12 hnL1 hRc1 hRc2 hL1nIso hc1nIso hc2nIso
            hh1nL1 hh1nc1 hh1nc2 (G.ne_of_adj hac1L1).symm (G.ne_of_adj hc12) hL1nc2 hisoge2) htt
        · -- `h₁` avoids all of `c₁, c₂, L₂`: `TwoTwinConfig` centre with cherry `P₃` `c₁–c₂–L₂`.
          exact absurd (twotwin_of_centre_nineteen G Iso h₁ c₁ c₂ L₂ hIsoprop hc1deg hc2deg hL2deg
            (by omega) hc12 hac2L2 hRc1 hRc2 hRL2 hc1nIso hc2nIso hL2nIso
            hh1nc1 hh1nc2 hh1nL2 (G.ne_of_adj hc12) (G.ne_of_adj hac2L2) hL2nc1.symm hisoge2) htt
  · -- **`|D| = 10`** (`9` hubs, `∑ int = 14`, `∑ deg = 38`, avoiders `≥ 5`).
    have hDc9 : Dᶜ.card = 9 := by rw [hDccard, hD10]
    have hint14 : ∑ g ∈ Dᶜ, (G.neighborFinset g ∩ Dᶜ).card = 14 := by rw [hsumInternal, hD10]
    have hdeg38 : ∑ g ∈ Dᶜ, G.degree g = 38 := by rw [hsumdeg, hD10]
    have hA1c5 : 5 ≤ A1.card := by rw [hDc9] at hA1card_lb; omega
    have hA2c5 : 5 ≤ A2.card := by rw [hDc9] at hA2card_lb; omega
    by_cases hex6 : ∃ h6 : Fin 19, h6 ∈ Dᶜ ∧ 6 ≤ G.degree h6
    · -- **deg-`6` exceptional.**  `38 = 6 + 8·4` pins every other hub to degree `4`; the anchor on
      -- the `h6`-erased avoider sets (`|A₁'|, |A₂'| ≥ 4`, `∑ int = 14`) yields `≥ 3` internally-
      -- isolated hubs, hence `≥ 2` isolated degree-`4` hubs — the ISO2 pair machinery closes.
      obtain ⟨h6, hh6Dc, hh6deg⟩ := hex6
      have herase : G.degree h6 + ∑ x ∈ Dᶜ.erase h6, G.degree x = 38 := by
        have h := Finset.add_sum_erase Dᶜ (fun v => G.degree v) hh6Dc
        rw [hdeg38] at h; exact h
      have hcard8 : (Dᶜ.erase h6).card = 8 := by rw [Finset.card_erase_of_mem hh6Dc, hDc9]
      have hother4 : ∀ g : Fin 19, g ∈ Dᶜ → g ≠ h6 → G.degree g = 4 := by
        intro g hg hgne
        have hgmem : g ∈ Dᶜ.erase h6 := Finset.mem_erase.mpr ⟨hgne, hg⟩
        have hsplit : G.degree g + ∑ x ∈ (Dᶜ.erase h6).erase g, G.degree x
            = ∑ x ∈ Dᶜ.erase h6, G.degree x :=
          Finset.add_sum_erase (Dᶜ.erase h6) (fun v => G.degree v) hgmem
        have hlb : 4 * ((Dᶜ.erase h6).erase g).card
            ≤ ∑ x ∈ (Dᶜ.erase h6).erase g, G.degree x := by
          have := Finset.card_nsmul_le_sum ((Dᶜ.erase h6).erase g) (fun v => G.degree v) 4
            (fun x hx => hge4 x (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx)))
          simpa [smul_eq_mul, Nat.mul_comm] using this
        have hc7 : ((Dᶜ.erase h6).erase g).card = 7 := by
          rw [Finset.card_erase_of_mem hgmem, hcard8]
        rw [hc7] at hlb
        have := hge4 g hg
        omega
      -- The anchor on the `h6`-erased avoider sets.
      have hA1'sub : A1.erase h6 ⊆ Dᶜ := (Finset.erase_subset _ _).trans hA1sub
      have hA2'sub : A2.erase h6 ⊆ Dᶜ := (Finset.erase_subset _ _).trans hA2sub
      have hA1'int : ∀ g ∈ A1.erase h6, 2 ≤ (G.neighborFinset g ∩ Dᶜ).card := by
        intro g hg
        have hgA1 : g ∈ A1 := Finset.mem_of_mem_erase hg
        have hgd : G.degree g = 4 := hother4 g (hA1sub hgA1) (Finset.ne_of_mem_erase hg)
        exact avoider_internal_ge_two_pt G D Iso g L₂ (hge4 g (hA1sub hgA1))
          (hW g (hA1sub hgA1) (by omega) (Or.inl (getA1pred g hgA1))) (hclassA1 g hgA1)
      have hA2'int : ∀ g ∈ A2.erase h6, 2 ≤ (G.neighborFinset g ∩ Dᶜ).card := by
        intro g hg
        have hgA2 : g ∈ A2 := Finset.mem_of_mem_erase hg
        have hgd : G.degree g = 4 := hother4 g (hA2sub hgA2) (Finset.ne_of_mem_erase hg)
        exact avoider_internal_ge_two_pt G D Iso g L₁ (hge4 g (hA2sub hgA2))
          (hW g (hA2sub hgA2) (by omega) (Or.inr (getA2pred g hgA2))) (hclassA2 g hgA2)
      have hFF'int : ∀ g ∈ A1.erase h6 ∩ A2.erase h6, 3 ≤ (G.neighborFinset g ∩ Dᶜ).card := by
        intro g hg
        obtain ⟨hg1, hg2⟩ := Finset.mem_inter.mp hg
        have hgA1 : g ∈ A1 := Finset.mem_of_mem_erase hg1
        have hgA2 : g ∈ A2 := Finset.mem_of_mem_erase hg2
        have hgFF : g ∈ FF := by rw [hFFdef]; exact Finset.mem_inter.mpr ⟨hgA1, hgA2⟩
        have hgd : G.degree g = 4 := hother4 g (hA1sub hgA1) (Finset.ne_of_mem_erase hg1)
        exact fully_free_internal_ge_three_pt G D Iso g (hge4 g (hFFsub hgFF))
          (hW g (hFFsub hgFF) (by omega) (Or.inl (getA1pred g hgA1))) (hclassFF g hgFF)
      have hanchor := anchor_isolated_count_nineteen Dᶜ (A1.erase h6) (A2.erase h6)
        (A1.erase h6 ∩ A2.erase h6) (fun g => (G.neighborFinset g ∩ Dᶜ).card) 14
        hA1'sub hA2'sub rfl hA1'int hA2'int hFF'int hint14
      set ISL := (Dᶜ \ (A1.erase h6 ∪ A2.erase h6)).filter
        (fun g => (G.neighborFinset g ∩ Dᶜ).card = 0) with hISLdef
      have hISLsubDc : ISL ⊆ Dᶜ := by
        rw [hISLdef]; exact (Finset.filter_subset _ _).trans Finset.sdiff_subset
      have hISL3 : 3 ≤ ISL.card := by
        have hA1'card : 4 ≤ (A1.erase h6).card := by
          have := Finset.pred_card_le_card_erase (s := A1) (a := h6); omega
        have hA2'card : 4 ≤ (A2.erase h6).card := by
          have := Finset.pred_card_le_card_erase (s := A2) (a := h6); omega
        rw [hDc9] at hanchor; omega
      -- Two internally-isolated degree-`4` hubs (dropping `h6`) — the ISO2 machinery closes.
      have hID2 : 2 ≤ (ISL.erase h6).card := by
        have := Finset.pred_card_le_card_erase (s := ISL) (a := h6); omega
      obtain ⟨h₁, hh1M, h₂, hh2M, hne12⟩ := Finset.one_lt_card.mp hID2
      have hprop : ∀ g ∈ ISL.erase h6, g ∈ Dᶜ ∧ G.neighborFinset g ∩ Dᶜ = ∅ ∧ G.degree g = 4 := by
        intro g hg
        have hgne : g ≠ h6 := Finset.ne_of_mem_erase hg
        have hgISL : g ∈ ISL := Finset.mem_of_mem_erase hg
        have hgDc : g ∈ Dᶜ := hISLsubDc hgISL
        rw [hISLdef, Finset.mem_filter] at hgISL
        exact ⟨hgDc, Finset.card_eq_zero.mp hgISL.2, hother4 g hgDc hgne⟩
      obtain ⟨hh1Dc, hh10, hh1d⟩ := hprop h₁ hh1M
      obtain ⟨hh2Dc, hh20, hh2d⟩ := hprop h₂ hh2M
      have hrich := isolated_pair_iso_rich_nineteen G D Iso L₁ c₁ c₂ L₂ h₁ h₂ hT hC4 hclassP
        hIsoprop hac1L1 hc12 hac2L2 hnc1L2 hnc2L1 hL1nc2 hL2nc1 hL1deg hc1deg hc2deg hL2deg
        hh2Dc hh1d hh2d hh10 hh20 hne12 hnL1L2
      rcases hrich with hrich | hrich
      · exact hth (two_isolated_hub_twohubconfig_d9_ff4 G D Iso L₁ c₁ c₂ L₂ h₁ h₂ hC4 hmemD hIsoD
          hclassP hIsoprop hac1L1 hc12 hac2L2 hc1deg hc2deg hh1Dc hh2Dc hh1d hh2d hh10 hh20
          hne12 hrich)
      · exact hth (two_isolated_hub_twohubconfig_d9_ff4 G D Iso L₁ c₁ c₂ L₂ h₂ h₁ hC4 hmemD hIsoD
          hclassP hIsoprop hac1L1 hc12 hac2L2 hc1deg hc2deg hh2Dc hh1Dc hh2d hh1d hh20 hh10
          hne12.symm hrich)
    · -- **all hubs of degree `≤ 5`** — the budget `14 < 3·5` is contradictory.
      push Not at hex6
      have hdeg5 : ∀ g : Fin 19, g ∈ Dᶜ → G.degree g ≤ 5 :=
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
      exact budget_contra_gen Dᶜ A1 A2 FF (fun g => (G.neighborFinset g ∩ Dᶜ).card) 5 14
        hA1sub hA2sub hFFdef hA1c5 hA2c5 hA1int hA2int hFFint hint14 (by omega)

set_option maxHeartbeats 1000000 in
/-- **No degree-`≤ 13` avoider triangle ⇒ contradiction (`n = 19`, `P₄`, `|D| ∈ {9, 10, 11}`).** -/
theorem iso_rich_force_p4_nineteen (G : SimpleGraph (Fin 19))
    (D Iso : Finset (Fin 19)) (L₁ c₁ c₂ L₂ : Fin 19)
    (h3 : ∀ v : Fin 19, 3 ≤ G.degree v)
    (hmemD : ∀ v : Fin 19, v ∈ D ↔ G.degree v = 3)
    (hIsoprop : ∀ v ∈ Iso, G.degree v = 3 ∧ (∀ w : Fin 19, G.Adj v w → G.degree w ≠ 3))
    (hisochar : ∀ w : Fin 19, w ∈ D → w ≠ L₁ → w ≠ c₁ → w ≠ c₂ → w ≠ L₂ → w ∈ Iso)
    (hL1deg : G.degree L₁ = 3) (hc1deg : G.degree c₁ = 3)
    (hc2deg : G.degree c₂ = 3) (hL2deg : G.degree L₂ = 3)
    (hac1L1 : G.Adj c₁ L₁) (hc12 : G.Adj c₁ c₂) (hac2L2 : G.Adj c₂ L₂)
    (hL1nc2 : L₁ ≠ c₂) (hL2nc1 : L₂ ≠ c₁)
    (hNc1D : G.neighborFinset c₁ ∩ D = {c₂, L₁}) (hNc2D : G.neighborFinset c₂ ∩ D = {c₁, L₂})
    (hL1D : L₁ ∈ D) (hc1D : c₁ ∈ D) (hc2D : c₂ ∈ D) (hL2D : L₂ ∈ D)
    (hd_lb : 9 ≤ D.card) (hd_ub : D.card ≤ 11) (htt : ¬TwoTwinConfig G)
    (hth : ¬TwoHubConfig G)
    (hT : ¬∃ x y z : Fin 19, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    (hC4 : ¬∃ a b c d : Fin 19, ({a, b, c, d} : Finset (Fin 19)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (hDccard : Dᶜ.card = 19 - D.card) (_hIsocard : Iso.card = D.card - 4)
    (hc1hub : (G.neighborFinset c₁ ∩ Dᶜ).card = 1)
    (hc2hub : (G.neighborFinset c₂ ∩ Dᶜ).card = 1)
    (hL1hub : (G.neighborFinset L₁ ∩ Dᶜ).card = 2)
    (hL2hub : (G.neighborFinset L₂ ∩ Dᶜ).card = 2)
    (hsumPath : ∑ g ∈ Dᶜ, (G.neighborFinset g ∩ ({L₁, c₁, c₂, L₂} : Finset (Fin 19))).card = 6)
    (hsumIso : ∑ g ∈ Dᶜ, (G.neighborFinset g ∩ Iso).card = 3 * (D.card - 4))
    (hsumInternal : ∑ g ∈ Dᶜ, (G.neighborFinset g ∩ Dᶜ).card = 74 - 6 * D.card)
    (hper : ∀ g : Fin 19, g ∈ Dᶜ →
      (G.neighborFinset g ∩ ({L₁, c₁, c₂, L₂} : Finset (Fin 19))).card
        + (G.neighborFinset g ∩ Iso).card + (G.neighborFinset g ∩ Dᶜ).card = G.degree g)
    (_hntri1 : ¬∃ a b c : Fin 19, a ∈ Dᶜ ∧ b ∈ Dᶜ ∧ c ∈ Dᶜ ∧
      G.Adj a b ∧ G.Adj a c ∧ G.Adj b c ∧
      (¬G.Adj a L₁ ∧ ¬G.Adj a c₁ ∧ ¬G.Adj a c₂) ∧
      (¬G.Adj b L₁ ∧ ¬G.Adj b c₁ ∧ ¬G.Adj b c₂) ∧
      (¬G.Adj c L₁ ∧ ¬G.Adj c c₁ ∧ ¬G.Adj c c₂) ∧
      G.degree a + G.degree b + G.degree c ≤ 13)
    (hntri2 : ¬∃ a b c : Fin 19, a ∈ Dᶜ ∧ b ∈ Dᶜ ∧ c ∈ Dᶜ ∧
      G.Adj a b ∧ G.Adj a c ∧ G.Adj b c ∧
      (¬G.Adj a c₁ ∧ ¬G.Adj a c₂ ∧ ¬G.Adj a L₂) ∧
      (¬G.Adj b c₁ ∧ ¬G.Adj b c₂ ∧ ¬G.Adj b L₂) ∧
      (¬G.Adj c c₁ ∧ ¬G.Adj c c₂ ∧ ¬G.Adj c L₂) ∧
      G.degree a + G.degree b + G.degree c ≤ 13) :
    False := by
  classical
  set P : Finset (Fin 19) := {L₁, c₁, c₂, L₂} with hPdef
  -- Every hub has degree `≥ 4`.
  have hge4 : ∀ g : Fin 19, g ∈ Dᶜ → 4 ≤ G.degree g := by
    intro g hg
    have hgD : g ∉ D := Finset.mem_compl.mp hg
    have : G.degree g ≠ 3 := fun he => hgD ((hmemD g).mpr he)
    have := h3 g
    omega
  -- Hub degree total `∑_{Dᶜ} deg = 64 − 3|D|`.
  have hsumdeg : ∑ g ∈ Dᶜ, G.degree g = 68 - 3 * D.card := by
    have hcong : ∑ g ∈ Dᶜ, ((G.neighborFinset g ∩ P).card
        + (G.neighborFinset g ∩ Iso).card + (G.neighborFinset g ∩ Dᶜ).card)
        = ∑ g ∈ Dᶜ, G.degree g := Finset.sum_congr rfl hper
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hsumPath, hsumIso, hsumInternal] at hcong
    omega
  -- The (W) fact for degree-`≤ 5` hubs.
  have hW := cherry_p4_W_facts_nineteen G D Iso L₁ c₁ c₂ L₂ hIsoprop hL1deg hc1deg hc2deg hL2deg
    hac1L1 hc12 hac2L2 hL1nc2 hL2nc1 hL1D hc1D hc2D hL2D htt
  -- Classification of `D`.
  have hclassP : ∀ x : Fin 19, x ∈ D → x = L₁ ∨ x = c₁ ∨ x = c₂ ∨ x = L₂ ∨ x ∈ Iso := by
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
  have hclassA1 : ∀ g : Fin 19, g ∈ A1 → ∀ x : Fin 19, G.Adj g x → x ∈ D → x = L₂ ∨ x ∈ Iso := by
    intro g hg x hadj hxD
    rw [hA1def, Finset.mem_filter] at hg
    obtain ⟨_, hgL1, hgc1, hgc2⟩ := hg
    rcases hclassP x hxD with h | h | h | h | h
    · exact absurd (h ▸ hadj) hgL1
    · exact absurd (h ▸ hadj) hgc1
    · exact absurd (h ▸ hadj) hgc2
    · exact Or.inl h
    · exact Or.inr h
  have hclassA2 : ∀ g : Fin 19, g ∈ A2 → ∀ x : Fin 19, G.Adj g x → x ∈ D → x = L₁ ∨ x ∈ Iso := by
    intro g hg x hadj hxD
    rw [hA2def, Finset.mem_filter] at hg
    obtain ⟨_, hgc1, hgc2, hgL2⟩ := hg
    rcases hclassP x hxD with h | h | h | h | h
    · exact Or.inl h
    · exact absurd (h ▸ hadj) hgc1
    · exact absurd (h ▸ hadj) hgc2
    · exact absurd (h ▸ hadj) hgL2
    · exact Or.inr h
  have hclassFF : ∀ g : Fin 19, g ∈ FF → ∀ x : Fin 19, G.Adj g x → x ∈ D → x ∈ Iso := by
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
  have getA2pred : ∀ g : Fin 19, g ∈ A2 →
      ¬G.Adj g c₁ ∧ ¬G.Adj g c₂ ∧ ¬G.Adj g L₂ := by
    intro g hg; rw [hA2def, Finset.mem_filter] at hg; exact hg.2
  have getA1pred : ∀ g : Fin 19, g ∈ A1 →
      ¬G.Adj g L₁ ∧ ¬G.Adj g c₁ ∧ ¬G.Adj g c₂ := by
    intro g hg; rw [hA1def, Finset.mem_filter] at hg; exact hg.2
  -- Cherry non-adjacencies (`L₁ ≠ L₂` plus the cross non-edges) for the `TwoHub` extraction.
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
  -- `¬ G.Adj L₁ L₂`: `L₁`'s unique `D`-neighbour is `c₁`, and `L₂ ≠ c₁`.
  have hnL1L2 : ¬G.Adj L₁ L₂ := by
    intro hadj
    have hmem : L₂ ∈ G.neighborFinset L₁ ∩ D :=
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset L₁ L₂).mpr hadj, hL2D⟩
    have hc1mem : c₁ ∈ G.neighborFinset L₁ ∩ D :=
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset L₁ c₁).mpr hac1L1.symm, hc1D⟩
    -- `L₁` has degree 3 = |N ∩ D| + |N ∩ Dᶜ| with |N ∩ Dᶜ| = 2, so |N ∩ D| = 1.
    have hdisjDc : Disjoint (G.neighborFinset L₁ ∩ D) (G.neighborFinset L₁ ∩ Dᶜ) := by
      apply Finset.disjoint_left.mpr; intro a ha hb
      exact (Finset.mem_compl.mp (Finset.mem_inter.mp hb).2) (Finset.mem_inter.mp ha).2
    have hunionDc : (G.neighborFinset L₁ ∩ D) ∪ (G.neighborFinset L₁ ∩ Dᶜ)
        = G.neighborFinset L₁ := by
      rw [← Finset.inter_union_distrib_left, Finset.union_compl, Finset.inter_univ]
    have hsplit : (G.neighborFinset L₁ ∩ D).card + (G.neighborFinset L₁ ∩ Dᶜ).card
        = G.degree L₁ := by
      rw [← Finset.card_union_of_disjoint hdisjDc, hunionDc, G.card_neighborFinset_eq_degree]
    rw [hL1deg, hL1hub] at hsplit
    have hone : (G.neighborFinset L₁ ∩ D).card = 1 := by omega
    have hsub : ({c₁, L₂} : Finset (Fin 19)) ⊆ G.neighborFinset L₁ ∩ D := by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hc1mem
      · exact hmem
    have hcard2 : ({c₁, L₂} : Finset (Fin 19)).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simp [Ne.symm hL2nc1]), Finset.card_singleton]
    have := Finset.card_le_card hsub
    rw [hcard2, hone] at this; omega
  -- Dispatch on `|D|`.
  rcases (by omega : D.card = 9 ∨ D.card = 10 ∨ D.card = 11) with hD9 | hD10 | hD11
  · -- **`|D| = 9`** — the excess-11 corner.  `Dᶜ.card = 10`, `∑ int = 20`, `∑ deg = 41`, so every
    -- hub has degree `∈ {4, 5}` with EXACTLY ONE degree-`5` hub (`41 = 5 + 9·4`).  The anchor count
    -- yields an internally-isolated degree-`4` hub, and the ISO2 / ISO1 dichotomy closes (ISO1 via
    -- the `cinc h₁` case split, mirrored inside `iso1_dense_corner_nineteen`).
    have hDc10 : Dᶜ.card = 10 := by rw [hDccard, hD9]
    have hint20 : ∑ g ∈ Dᶜ, (G.neighborFinset g ∩ Dᶜ).card = 20 := by rw [hsumInternal, hD9]
    have hdeg41 : ∑ g ∈ Dᶜ, G.degree g = 41 := by rw [hsumdeg, hD9]
    have hA1c6 : 6 ≤ A1.card := by rw [hDc10] at hA1card_lb; omega
    have hA2c6 : 6 ≤ A2.card := by rw [hDc10] at hA2card_lb; omega
    have hdeg5 : ∀ g : Fin 19, g ∈ Dᶜ → G.degree g ≤ 5 := by
      intro g hg
      have := hub_deg_upper_pt Dᶜ (fun v => G.degree v) 41 hge4 hdeg41 g hg
      rw [hDc10] at this; omega
    -- Avoider internal-degree lower bounds.
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
    -- **STEP 1 (anchor).**  At least two internally-isolated hubs, hence (≤ 1 degree-`5` hub) at
    -- least one internally-isolated degree-`4` hub.  This proves GEN `= 0` (there is ALWAYS an
    -- isolated degree-`4` hub), reducing the corner to the ISO2 / ISO1 dichotomy.
    have hanchor := anchor_isolated_count_nineteen Dᶜ A1 A2 FF
      (fun g => (G.neighborFinset g ∩ Dᶜ).card) 20 hA1sub hA2sub hFFdef hA1int hA2int hFFint hint20
    set ISL := (Dᶜ \ (A1 ∪ A2)).filter (fun g => (G.neighborFinset g ∩ Dᶜ).card = 0) with hISLdef
    have hISLsubDc : ISL ⊆ Dᶜ := by
      rw [hISLdef]; exact (Finset.filter_subset _ _).trans Finset.sdiff_subset
    have hISL2 : 2 ≤ ISL.card := by rw [hDc10] at hanchor; omega
    -- Exactly one degree-`5` hub in `Dᶜ` (since `∑ deg = 41 = 5 + 9·4`).
    have hdeg5count : (Dᶜ.filter (fun g => G.degree g = 5)).card = 1 := by
      have hpart := Finset.sum_filter_add_sum_filter_not Dᶜ (fun g => G.degree g = 5)
        (fun g => G.degree g)
      have h4 : ∀ g ∈ Dᶜ.filter (fun g => ¬ G.degree g = 5), G.degree g = 4 := by
        intro g hg
        rw [Finset.mem_filter] at hg
        have := hge4 g hg.1; have := hdeg5 g hg.1; omega
      have h5 : ∀ g ∈ Dᶜ.filter (fun g => G.degree g = 5), G.degree g = 5 := by
        intro g hg; exact (Finset.mem_filter.mp hg).2
      rw [Finset.sum_congr rfl h5, Finset.sum_congr rfl h4, Finset.sum_const, Finset.sum_const,
        smul_eq_mul, smul_eq_mul] at hpart
      have hcc : (Dᶜ.filter (fun g => G.degree g = 5)).card
          + (Dᶜ.filter (fun g => ¬ G.degree g = 5)).card = 10 := by
        rw [Finset.card_filter_add_card_filter_not]; exact hDc10
      rw [hdeg41] at hpart; omega
    -- The internally-isolated degree-`4` hubs.
    set ID4 := ISL.filter (fun g => G.degree g = 4) with hID4def
    have hID4_1 : 1 ≤ ID4.card := by
      have hle5 : (ISL.filter (fun g => G.degree g = 5)).card ≤ 1 := by
        rw [← hdeg5count]
        exact Finset.card_le_card (Finset.filter_subset_filter _ hISLsubDc)
      have hpartISL := Finset.card_filter_add_card_filter_not (s := ISL)
        (p := fun g => G.degree g = 5)
      have h45 : ISL.filter (fun g => ¬ G.degree g = 5) = ID4 := by
        rw [hID4def]; apply Finset.filter_congr
        intro g hg
        have hgDc := hISLsubDc hg
        have := hge4 g hgDc; have := hdeg5 g hgDc
        constructor <;> intro <;> omega
      rw [h45] at hpartISL; omega
    -- Extractor: an `ID4` member is an internally-isolated degree-`4` hub.
    have hID4prop : ∀ g ∈ ID4, g ∈ Dᶜ ∧ G.neighborFinset g ∩ Dᶜ = ∅ ∧ G.degree g = 4 := by
      intro g hg
      rw [hID4def, Finset.mem_filter] at hg
      obtain ⟨hgISL, hgd⟩ := hg
      have hgDc := hISLsubDc hgISL
      rw [hISLdef, Finset.mem_filter] at hgISL
      exact ⟨hgDc, Finset.card_eq_zero.mp hgISL.2, hgd⟩
    -- **STEP 2/3.**  Dichotomy on a *second* internally-isolated degree-`4` hub.
    by_cases hISO2 : 2 ≤ ID4.card
    · -- **ISO2** (`≥ 2` isolated degree-`4` hubs; the `1411/1834` majority).
      obtain ⟨h₁, hh1ID4, h₂, hh2ID4, hne12⟩ := Finset.one_lt_card.mp hISO2
      obtain ⟨hh1Dc, hh10, hh1d⟩ := hID4prop h₁ hh1ID4
      obtain ⟨hh2Dc, hh20, hh2d⟩ := hID4prop h₂ hh2ID4
      have hrich := isolated_pair_iso_rich_nineteen G D Iso L₁ c₁ c₂ L₂ h₁ h₂ hT hC4 hclassP
        hIsoprop hac1L1 hc12 hac2L2 hnc1L2 hnc2L1 hL1nc2 hL2nc1 hL1deg hc1deg hc2deg hL2deg
        hh2Dc hh1d hh2d hh10 hh20 hne12 hnL1L2
      rcases hrich with hrich | hrich
      · exact hth (two_isolated_hub_twohubconfig_d9_ff4 G D Iso L₁ c₁ c₂ L₂ h₁ h₂ hC4 hmemD hIsoD
          hclassP hIsoprop hac1L1 hc12 hac2L2 hc1deg hc2deg hh1Dc hh2Dc hh1d hh2d hh10 hh20
          hne12 hrich)
      · exact hth (two_isolated_hub_twohubconfig_d9_ff4 G D Iso L₁ c₁ c₂ L₂ h₂ h₁ hC4 hmemD hIsoD
          hclassP hIsoprop hac1L1 hc12 hac2L2 hc1deg hc2deg hh2Dc hh1Dc hh2d hh1d hh20 hh10
          hne12.symm hrich)
    · -- **ISO1** (exactly one internally-isolated degree-`4` hub `h₁`).  Extract the unique
      -- isolated degree-`4` hub `h₁` (`ID4.card = 1`) and the unique degree-`5` hub `h₅`, then
      -- case-split on `cinc h₁`:
      --   • `cinc h₁ ≥ 2` ⟹ `iso1_dichotomy_to_false` (TwoTwin ∨ TwoHub, both excluded);
      --   • `cinc h₁ = 0` or `cinc h₁ = 1` with the cherry-neighbour a LEAF (`L₁`/`L₂`) ⟹ `h₁` is a
      --     `TwoTwinConfig` centre avoiding the opposite cherry `P₃` (contra `htt`);
      --   • `cinc h₁ = 1` with the cherry-neighbour an INTERIOR `c`-vertex (`c₁`/`c₂`) — the hard
      --     near-`K₅` sub-case, closed by `iso1_hard_c_subcase_nineteen` (`hntri1`, resp. `hntri2`
      --     through the `P₄` reflection).
      have hID4_eq1 : ID4.card = 1 := by omega
      obtain ⟨h₁, hID4_h1⟩ := Finset.card_eq_one.mp hID4_eq1
      have hh1ID4 : h₁ ∈ ID4 := by rw [hID4_h1]; exact Finset.mem_singleton_self h₁
      obtain ⟨hh1Dc, hh1iso, hh1d⟩ := hID4prop h₁ hh1ID4
      obtain ⟨h₅, hf5⟩ := Finset.card_eq_one.mp hdeg5count
      have hh5mem : h₅ ∈ Dᶜ.filter (fun g => G.degree g = 5) := by
        rw [hf5]; exact Finset.mem_singleton_self h₅
      obtain ⟨hh5Dc, hh5d⟩ := Finset.mem_filter.mp hh5mem
      have hne15 : h₁ ≠ h₅ := fun he => by rw [he, hh5d] at hh1d; exact absurd hh1d (by norm_num)
      have hdegOth : ∀ h : Fin 19, h ∈ Dᶜ → h ≠ h₁ → h ≠ h₅ → G.degree h = 4 := by
        intro h hhDc _ hh5
        have h4 := hge4 h hhDc; have h5 := hdeg5 h hhDc
        rcases (by omega : G.degree h = 4 ∨ G.degree h = 5) with h4' | h5'
        · exact h4'
        · exfalso; apply hh5
          have hm : h ∈ Dᶜ.filter (fun g => G.degree g = 5) := Finset.mem_filter.mpr ⟨hhDc, h5'⟩
          rw [hf5, Finset.mem_singleton] at hm; exact hm
      have hHub10 : Dᶜ.card = 10 := hDc10
      have hsumIso15 : ∑ h ∈ Dᶜ, (G.neighborFinset h ∩ Iso).card = 15 := by rw [hsumIso, hD9]
      -- cherry vertices are non-`Iso`; `h₁ ≠` each cherry vertex; `L₁ ≠ L₂`.
      have hc1nIso : c₁ ∉ Iso := fun h => (hIsoprop c₁ h).2 L₁ hac1L1 hL1deg
      have hc2nIso : c₂ ∉ Iso := fun h => (hIsoprop c₂ h).2 c₁ hc12.symm hc1deg
      have hL1nIso : L₁ ∉ Iso := fun h => (hIsoprop L₁ h).2 c₁ hac1L1.symm hc1deg
      have hL2nIso : L₂ ∉ Iso := fun h => (hIsoprop L₂ h).2 c₂ hac2L2.symm hc2deg
      have hh1nc1 : h₁ ≠ c₁ := fun he => by rw [he, hc1deg] at hh1d; exact absurd hh1d (by norm_num)
      have hh1nc2 : h₁ ≠ c₂ := fun he => by rw [he, hc2deg] at hh1d; exact absurd hh1d (by norm_num)
      have hh1nL1 : h₁ ≠ L₁ := fun he => by rw [he, hL1deg] at hh1d; exact absurd hh1d (by norm_num)
      have hh1nL2 : h₁ ≠ L₂ := fun he => by rw [he, hL2deg] at hh1d; exact absurd hh1d (by norm_num)
      have hL1L2 : L₁ ≠ L₂ := by
        intro he
        exact hT ⟨c₁, c₂, L₁, G.ne_of_adj hc12, he.symm ▸ G.ne_of_adj hac2L2,
          G.ne_of_adj hac1L1, hc12, he.symm ▸ hac2L2, hac1L1, by omega⟩
      by_cases hcinc2 : 2 ≤ (G.neighborFinset h₁ ∩ P).card
      · -- **`cinc h₁ ≥ 2`** — the completed counting dichotomy.
        exact iso1_dichotomy_to_false G D Iso L₁ c₁ c₂ L₂ h₁ h₅ hmemD hIsoD hIsoprop hclassP
          hL1deg hc1deg hc2deg hL2deg hac1L1 hc12 hac2L2 hL1nc2 hL2nc1 hNc1D hNc2D hL1D hc1D hc2D
          hL2D htt hth hT hC4 hHub10 hdeg5 hper hsumIso15 hh1Dc hh1d hh1iso hcinc2 hh5Dc hh5d hne15
          hdegOth
      · -- **`cinc h₁ ≤ 1`** — `h₁` avoids a cherry `P₃` unless its lone cherry-neighbour is `c₁`/`c₂`.
        have hh1int0 : (G.neighborFinset h₁ ∩ Dᶜ).card = 0 := by rw [hh1iso]; exact Finset.card_empty
        have hisoge2 : 2 ≤ (G.neighborFinset h₁ ∩ Iso).card := by
          have hdec1 := hper h₁ hh1Dc
          rw [hh1int0, hh1d] at hdec1
          omega
        by_cases hRc1 : G.Adj h₁ c₁
        · exact iso1_hard_c_subcase_nineteen G D Iso L₁ c₁ c₂ L₂ h₁ h₅ hmemD hIsoprop hclassP
            hL1deg hc1deg hc2deg hL2deg hac1L1 hc12 hac2L2 hL1nc2 hL2nc1 hNc1D hNc2D
            hL1D hc1D hc2D hL2D htt hth hT hC4 hHub10 (by rw [_hIsocard, hD9]) hdeg5 hper hsumPath
            hsumIso15 hc1hub hc2hub hL1hub hL2hub hh1Dc hh1d hh1iso hRc1 (by rw [← hPdef]; omega)
            hh5Dc hh5d hne15 hdegOth _hntri1
        by_cases hRc2 : G.Adj h₁ c₂
        · -- `h₁` meets `c₂`: apply the lemma with `(L₁,c₁,c₂,L₂) ↦ (L₂,c₂,c₁,L₁)`.
          have hPeq : ({L₂, c₂, c₁, L₁} : Finset (Fin 19)) = {L₁, c₁, c₂, L₂} := by
            ext x
            simp only [Finset.mem_insert, Finset.mem_singleton]
            constructor <;> rintro (rfl | rfl | rfl | rfl) <;> simp
          have hclassP' : ∀ x : Fin 19, x ∈ D → x = L₂ ∨ x = c₂ ∨ x = c₁ ∨ x = L₁ ∨ x ∈ Iso := by
            intro x hx; rcases hclassP x hx with h | h | h | h | h <;> simp [h]
          have hper' : ∀ h : Fin 19, h ∈ Dᶜ →
              (G.neighborFinset h ∩ ({L₂, c₂, c₁, L₁} : Finset (Fin 19))).card
                + (G.neighborFinset h ∩ Iso).card + (G.neighborFinset h ∩ Dᶜ).card = G.degree h := by
            intro h hh; rw [hPeq]; exact hper h hh
          have hsumPath' : ∑ g ∈ Dᶜ,
              (G.neighborFinset g ∩ ({L₂, c₂, c₁, L₁} : Finset (Fin 19))).card = 6 := by
            rw [Finset.sum_congr rfl (fun g _ => by rw [hPeq])]; exact hsumPath
          have hntri1' : ¬∃ a b c : Fin 19, a ∈ Dᶜ ∧ b ∈ Dᶜ ∧ c ∈ Dᶜ ∧
              G.Adj a b ∧ G.Adj a c ∧ G.Adj b c ∧
              (¬G.Adj a L₂ ∧ ¬G.Adj a c₂ ∧ ¬G.Adj a c₁) ∧
              (¬G.Adj b L₂ ∧ ¬G.Adj b c₂ ∧ ¬G.Adj b c₁) ∧
              (¬G.Adj c L₂ ∧ ¬G.Adj c c₂ ∧ ¬G.Adj c c₁) ∧
              G.degree a + G.degree b + G.degree c ≤ 13 := by
            rintro ⟨a, b, c, haD, hbD, hcD, hab, hac, hbc,
              ⟨haL2, hac2, hac1⟩, ⟨hbL2, hbc2, hbc1⟩, ⟨hcL2, hcc2, hcc1⟩, hdeg⟩
            exact hntri2 ⟨a, b, c, haD, hbD, hcD, hab, hac, hbc,
              ⟨hac1, hac2, haL2⟩, ⟨hbc1, hbc2, hbL2⟩, ⟨hcc1, hcc2, hcL2⟩, hdeg⟩
          exact iso1_hard_c_subcase_nineteen G D Iso L₂ c₂ c₁ L₁ h₁ h₅ hmemD hIsoprop hclassP'
            hL2deg hc2deg hc1deg hL1deg hac2L2 hc12.symm hac1L1 hL2nc1 hL1nc2 hNc2D hNc1D
            hL2D hc2D hc1D hL1D htt hth hT hC4 hHub10 (by rw [_hIsocard, hD9]) hdeg5 hper' hsumPath'
            hsumIso15 hc2hub hc1hub hL2hub hL1hub hh1Dc hh1d hh1iso hRc2
            (by rw [hPeq, ← hPdef]; omega) hh5Dc hh5d hne15 hdegOth hntri1'
        by_cases hRL2 : G.Adj h₁ L₂
        · -- lone cherry-neighbour is `L₂`; `h₁` avoids the cherry `P₃` `L₁–c₁–c₂`.
          have hnL1 : ¬G.Adj h₁ L₁ := by
            intro hL1a
            have hsub : ({L₁, L₂} : Finset (Fin 19)) ⊆
                G.neighborFinset h₁ ∩ P := by
              intro w hw
              simp only [Finset.mem_insert, Finset.mem_singleton] at hw
              rcases hw with rfl | rfl
              · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hL1a, by simp [hPdef]⟩
              · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hRL2, by simp [hPdef]⟩
            have hcard : ({L₁, L₂} : Finset (Fin 19)).card = 2 := by
              rw [Finset.card_insert_of_notMem (by simp [hL1L2]), Finset.card_singleton]
            have := Finset.card_le_card hsub; omega
          exact absurd (twotwin_of_centre_nineteen G Iso h₁ L₁ c₁ c₂ hIsoprop hL1deg hc1deg hc2deg
            (by omega) hac1L1.symm hc12 hnL1 hRc1 hRc2 hL1nIso hc1nIso hc2nIso
            hh1nL1 hh1nc1 hh1nc2 (G.ne_of_adj hac1L1).symm (G.ne_of_adj hc12) hL1nc2 hisoge2) htt
        · -- `h₁` avoids all of `c₁, c₂, L₂`: `TwoTwinConfig` centre with cherry `P₃` `c₁–c₂–L₂`.
          exact absurd (twotwin_of_centre_nineteen G Iso h₁ c₁ c₂ L₂ hIsoprop hc1deg hc2deg hL2deg
            (by omega) hc12 hac2L2 hRc1 hRc2 hRL2 hc1nIso hc2nIso hL2nIso
            hh1nc1 hh1nc2 hh1nL2 (G.ne_of_adj hc12) (G.ne_of_adj hac2L2) hL2nc1.symm hisoge2) htt
  · -- **`|D| = 10`** (`n = 19`: `Dᶜ.card = 9`, `∑ int = 14`, `∑ deg = 38`, avoiders `≥ 5`).
    have hDc9 : Dᶜ.card = 9 := by rw [hDccard, hD10]
    have hint14 : ∑ g ∈ Dᶜ, (G.neighborFinset g ∩ Dᶜ).card = 14 := by rw [hsumInternal, hD10]
    have hdeg38 : ∑ g ∈ Dᶜ, G.degree g = 38 := by rw [hsumdeg, hD10]
    have hA1c5 : 5 ≤ A1.card := by rw [hDc9] at hA1card_lb; omega
    have hA2c5 : 5 ≤ A2.card := by rw [hDc9] at hA2card_lb; omega
    by_cases hex6 : ∃ h6 : Fin 19, h6 ∈ Dᶜ ∧ 6 ≤ G.degree h6
    · -- **deg-`6` exceptional** — same ISO2 / ISO1 dichotomy as `|D| = 9`.
      -- A degree-`6` hub forces all `8` other hubs to degree `4` (`38 = 6 + 8·4`), so every
      -- internally-isolated hub `≠ h6` is degree-`4`.  The shared `two_isolated_hub_*`/
      -- `isolated_pair_iso_rich_nineteen` machinery (budget-free) closes the ISO2 majority verbatim;
      -- the ISO1 residual is dispatched to `iso1_dense_corner_nineteen`, where the anchor count on
      -- the `h6`-erased avoider sets shows it is arithmetically empty.
      obtain ⟨_h6, _hh6Dc, _hh6deg⟩ := hex6
      set ISL := Dᶜ.filter (fun g => (G.neighborFinset g ∩ Dᶜ).card = 0) with hISLdef
      have hISLsubDc : ISL ⊆ Dᶜ := Finset.filter_subset _ _
      set ID4 := ISL.filter (fun g => G.degree g = 4) with hID4def
      have hID4prop : ∀ g ∈ ID4, g ∈ Dᶜ ∧ G.neighborFinset g ∩ Dᶜ = ∅ ∧ G.degree g = 4 := by
        intro g hg
        rw [hID4def, Finset.mem_filter] at hg
        obtain ⟨hgISL, hgd⟩ := hg
        have hgDc := hISLsubDc hgISL
        rw [hISLdef, Finset.mem_filter] at hgISL
        exact ⟨hgDc, Finset.card_eq_zero.mp hgISL.2, hgd⟩
      by_cases hISO2 : 2 ≤ ID4.card
      · -- **ISO2** (`≥ 2` isolated degree-`4` hubs).
        obtain ⟨h₁, hh1ID4, h₂, hh2ID4, hne12⟩ := Finset.one_lt_card.mp hISO2
        obtain ⟨hh1Dc, hh10, hh1d⟩ := hID4prop h₁ hh1ID4
        obtain ⟨hh2Dc, hh20, hh2d⟩ := hID4prop h₂ hh2ID4
        have hrich := isolated_pair_iso_rich_nineteen G D Iso L₁ c₁ c₂ L₂ h₁ h₂ hT hC4 hclassP
          hIsoprop hac1L1 hc12 hac2L2 hnc1L2 hnc2L1 hL1nc2 hL2nc1 hL1deg hc1deg hc2deg hL2deg
          hh2Dc hh1d hh2d hh10 hh20 hne12 hnL1L2
        rcases hrich with hrich | hrich
        · exact hth (two_isolated_hub_twohubconfig_d9_ff4 G D Iso L₁ c₁ c₂ L₂ h₁ h₂ hC4 hmemD
            hIsoD hclassP hIsoprop hac1L1 hc12 hac2L2 hc1deg hc2deg hh1Dc hh2Dc hh1d hh2d hh10 hh20
            hne12 hrich)
        · exact hth (two_isolated_hub_twohubconfig_d9_ff4 G D Iso L₁ c₁ c₂ L₂ h₂ h₁ hC4 hmemD
            hIsoD hclassP hIsoprop hac1L1 hc12 hac2L2 hc1deg hc2deg hh2Dc hh1Dc hh2d hh1d hh20 hh10
            hne12.symm hrich)
      · -- **ISO1** (`≤ 1` isolated degree-`4` hub).  Consolidated with the `|D| = 9` ISO1 corner
        -- into the fully-proven `iso1_dense_corner_nineteen`; at `|D| = 10` the anchor count on the
        -- `h6`-erased avoider sets shows this branch is arithmetically empty.
        exact iso1_dense_corner_nineteen G D Iso L₁ c₁ c₂ L₂ h3 hmemD hIsoprop hisochar
          hL1deg hc1deg hc2deg hL2deg hac1L1 hc12 hac2L2 hL1nc2 hL2nc1 hNc1D hNc2D
          hL1D hc1D hc2D hL2D hd_lb hd_ub htt hth hT hC4 hDccard _hIsocard hc1hub hc2hub
          hL1hub hL2hub hsumPath hsumIso hsumInternal hper _hntri1 hntri2 (Or.inr hD10)
    · push Not at hex6
      have hdeg5 : ∀ g : Fin 19, g ∈ Dᶜ → G.degree g ≤ 5 :=
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
      exact budget_contra_gen Dᶜ A1 A2 FF (fun g => (G.neighborFinset g ∩ Dᶜ).card) 5 14
        hA1sub hA2sub hFFdef hA1c5 hA2c5 hA1int hA2int hFFint hint14 (by omega)
  · -- **`|D| = 11`.**  (`n = 19`: `Dᶜ.card = 8`, `∑ int = 8`, `∑ deg = 35`, avoiders `≥ 4`.)
    have hDc8 : Dᶜ.card = 8 := by rw [hDccard, hD11]
    have hint8 : ∑ g ∈ Dᶜ, (G.neighborFinset g ∩ Dᶜ).card = 8 := by rw [hsumInternal, hD11]
    have hdeg35 : ∑ g ∈ Dᶜ, G.degree g = 35 := by rw [hsumdeg, hD11]
    have hA1card4 : 4 ≤ A1.card := by rw [hDc8] at hA1card_lb; omega
    have hA2card4 : 4 ≤ A2.card := by rw [hDc8] at hA2card_lb; omega
    by_cases hex6 : ∃ h6 : Fin 19, h6 ∈ Dᶜ ∧ 6 ≤ G.degree h6
    · obtain ⟨h6, hh6Dc, hh6deg⟩ := hex6
      have herase : G.degree h6 + ∑ x ∈ Dᶜ.erase h6, G.degree x = 35 := by
        have h := Finset.add_sum_erase Dᶜ (fun v => G.degree v) hh6Dc
        rw [hdeg35] at h; exact h
      have hcard7 : (Dᶜ.erase h6).card = 7 := by rw [Finset.card_erase_of_mem hh6Dc, hDc8]
      have hother5 : ∀ g : Fin 19, g ∈ Dᶜ → g ≠ h6 → G.degree g ≤ 5 := by
        intro g hg hgne
        have hub := hub_deg_upper_pt (Dᶜ.erase h6) (fun v => G.degree v)
          (∑ x ∈ Dᶜ.erase h6, G.degree x)
          (fun x hx => hge4 x (Finset.mem_of_mem_erase hx)) rfl g (Finset.mem_erase.mpr ⟨hgne, hg⟩)
        rw [hcard7] at hub
        omega
      refine budget_contra_exc Dᶜ A1 A2 FF (fun g => (G.neighborFinset g ∩ Dᶜ).card) 4 8 h6
        hA1sub hA2sub hFFdef hA1card4 hA2card4 ?_ ?_ ?_ hint8 (by omega)
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
      have hdeg5 : ∀ g : Fin 19, g ∈ Dᶜ → G.degree g ≤ 5 :=
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
      exact budget_contra_gen Dᶜ A1 A2 FF (fun g => (G.neighborFinset g ∩ Dᶜ).card) 4 8
        hA1sub hA2sub hFFdef hA1card4 hA2card4 hA1int hA2int hFFint hint8 (by omega)

end N19

end ACMax
