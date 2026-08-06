import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N19.Core
import ACMaxConjecture.SmallCases.N19.TwoHubSelect
import ACMaxConjecture.SmallCases.N19.StarTriangleStruct
import ACMaxConjecture.SmallCases.N19.RichCount
import ACMaxConjecture.SmallCases.N19.Align8Helpers
import ACMaxConjecture.SmallCases.N19.ZVertex
import ACMaxConjecture.SmallCases.N19.ZPoorR7
import ACMaxConjecture.SmallCases.N19.ZPoorSat
import ACMaxConjecture.SmallCases.N19.ZPoorS16
import ACMaxConjecture.SmallCases.N19.R5Resid

/-!
# The two-poor-hub dispatcher for the rigid `n = 19` no-two-hub partition (top layer)

Port of `TwinCert18ZPoorDispatch` to the NEW `n = 19` `|Hub| = 11` regime.  For the tight
`e(M) = 1`, all-degree-`4`, `(|Hub|, |Iso|) = (11, 6)` profile, an `M`-edge endpoint
`z = univ \ (Hub ∪ Iso)` meets exactly two hubs.  This file closes the headline obstruction — both of
those hubs cannot be *poor* (iso-degree `≤ 1`) — by dispatching the rich-count regime to the
axiom-clean regime provers.  **ALL deep `|Hub| = 11` regimes are now closed via the reusable
`Z`-leaf cut** (`TwinCert19ZPoorCut`); no design-packing `sorry` remains.

The rich count `r := |R|` lies in `{6, 7}` (`rich_count_ge_six_nineteen` / `rich_count_le_seven`),
and `S := ∑_R |N ∩ Iso|` is the rich iso-incidence sum.  The `n = 19` regime table (DERIVED;
`|Iso| = 6`, `|Hub \ R| = 11 − r` poor hubs each carrying `≤ 1` iso-incidence, total iso-incidence
`18`):

| `r` | `S` | prover |
|`7`|`14`| `z`-side cut (`z_side_poor_cut_nineteen`, `∑_P = 4 > 2 = |P| − 2`) ✓ |
|`7`|`15`| `mpartner_meets_poor_nineteen` (`z`-side cut, `TwinCert19ZPoorSat`) ✓ |
|`7`|`16`| `rich_seven_S16_two_poor_false_nineteen` (`z'`-side cut via saturation, `TwinCert19ZPoorS16`) ✓ |
|`7`|`≥17`| clean `two_high_hubs_sum_ge_seven_contra_nineteen` ✓ |
|`6`|`13`| `z`-side cut (`z_side_poor_cut_nineteen`, `∑_P = 5 > 3 = |P| − 2`) ✓ |
|`6`|`14`| `z`-side cut (`z_side_poor_cut_nineteen`, `∑_P = 4 > 3 = |P| − 2`) ✓ |
|`6`|`≥15`| clean `two_high_hubs_sum_ge_seven_contra_nineteen` ✓ |

**The reusable cut (BYPASSES the n = 18 saturation/design packing).**  An `M`-edge endpoint `z`
meets two poor hubs `hg1, hg2`.  Whenever the poor-incidence sum `∑_P = 18 − S` exceeds the
capacity `|P| − 2` of the *other* poor hubs (i.e. `S < r + 9`, which holds for every regime except
`r = 7, S = 16`), at least one of `hg1, hg2` carries a private twin, and the `r ∈ {6,7}` rich pool
(`|R| ≥ 5`) supplies a `TwoHubConfig` with a `Z`-leaf `d = z` (invisible to the `Iso`-only
`hno2hub`) via the pigeonhole `two_poor_zleaf_pigeonhole_nineteen` — contradicting `hnocut`.  The one
exception `S = 16` (where `hg1, hg2` may both be twinless) is closed via full rich saturation
(`rich_saturated_S16`), which forces all four `Z`-hubs poor `= P` so a twin-bearing `Z`-hub exists on
the `z'` side.  The clean `S ≥ 17 / S ≥ 15` sub-cases assemble two non-adjacent degree-`4` hubs each
retaining `≥ 2` private twins (`two_high_hubs_sum_ge_seven_contra_nineteen`), contradicting `hno2hub`.

The apex `z_meets_two_poor_forces_two_hub_nineteen` is now fully proved (axiom-clean,
`[propext, Classical.choice, Quot.sound]`); it threads `hnocut : ¬ ZPoorCutConfig G` (introduced by
`by_contra`) down to the regime branches, each of which builds the cut and closes the branch.  Once
`RichZdeg` imports this file it discharges `hztwopoor` library-wide.
-/

namespace ACMax

open scoped Classical

namespace N19

/-- **The low-density rich residual (`S ≤ 16`) — dispatched to the regime provers / deep sorries.**
The rich-hub count `r := |R|` is `6` or `7` (`hr67`) and the rich iso-incidence sum
`S := ∑_R |N ∩ Iso|` satisfies (the `11 − r` poor hubs absorb at most one iso-incidence each):

* `r = 7` ⟹ `S ∈ {14, 15, 16}`: `S = 14 → ` deep `sorry`; `S = 15 → mpartner_meets_poor`;
  `S = 16 → rich_seven_S16_two_poor_false`;
* `r = 6` ⟹ `S ∈ {13, 14, 15, 16}`: `S = 13 → ` deep `sorry`; `S = 14 → ` deep `sorry`;
  `S ≥ 15` assembles two non-adjacent high hubs (`two_high_hubs_sum_ge_seven_contra`).

The good-triangle threshold `hT ≤ 11` is bridged to `≤ 10` for the two `r = 7` provers. -/
theorem low_rich_iso_residual_nineteen (G : SimpleGraph (Fin 19)) (Hub Iso : Finset (Fin 19))
    (hdeg4 : ∀ h ∈ Hub, G.degree h = 4)
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdisj : Disjoint Hub Iso) (hHub : Hub.card = 11) (hIso : Iso.card = 6)
    (hdeg3 : ∀ v : Fin 19, 3 ≤ G.degree v) (hisodeg3 : ∀ t ∈ Iso, G.degree t = 3)
    (hdsum : ∑ w ∈ Hub, G.degree w = 44)
    (hleak : ∑ h ∈ Hub, (G.neighborFinset h ∩ (Finset.univ \ (Hub ∪ Iso))).card ≤ 4)
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hno2hub : ¬∃ h₁ h₂ : Fin 19, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card)
    (hC4 : ¬∃ a b c d : Fin 19, ({a, b, c, d} : Finset (Fin 19)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (hK23 : ¬∃ a b c d e : Fin 19, ({a, b, c, d, e} : Finset (Fin 19)).card = 5 ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
      G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 19)
    (hT : ¬∃ x y z : Fin 19, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧
      G.degree x + G.degree y + G.degree z ≤ 11)
    (hnocut : ¬ ZPoorCutConfig G)
    (z : Fin 19) (hz : z ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 19)))
    (hg1 : Fin 19) (hg2 : Fin 19) (hg1ne : hg1 ≠ hg2)
    (hg1mem : hg1 ∈ G.neighborFinset z ∩ Hub) (hg2mem : hg2 ∈ G.neighborFinset z ∩ Hub)
    (hg1poor : (G.neighborFinset hg1 ∩ Iso).card ≤ 1)
    (hg2poor : (G.neighborFinset hg2 ∩ Iso).card ≤ 1)
    (hres : G.Adj hg1 hg2 ∨ (G.neighborFinset hg1 ∩ G.neighborFinset hg2 ∩ Iso).card = 0)
    (hr67 : (Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)).card = 6 ∨
      (Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)).card = 7)
    (hSlo : ∑ r ∈ Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card),
        (G.neighborFinset r ∩ Iso).card ≤ 16) :
    False := by
  classical
  set R : Finset (Fin 19) := Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card) with hRdef
  set P : Finset (Fin 19) := Hub.filter (fun h => ¬ 2 ≤ (G.neighborFinset h ∩ Iso).card) with hPdef
  have hRsubHub : R ⊆ Hub := Finset.filter_subset _ _
  have hRmem : ∀ a, a ∈ R ↔ a ∈ Hub ∧ 2 ≤ (G.neighborFinset a ∩ Iso).card := by
    intro a; rw [hRdef, Finset.mem_filter]
  set S : ℕ := ∑ r ∈ R, (G.neighborFinset r ∩ Iso).card with hSdef
  -- Total iso-incidence sum is `18`.
  have hsum18 : ∑ a ∈ Hub, (G.neighborFinset a ∩ Iso).card = 18 := by
    have := hub_iso_sum_nineteen G Hub Iso hiso3; rw [hIso] at this; omega
  -- Split over `R` and the poor complement `P`.
  have hsplitRP : S + ∑ g ∈ P, (G.neighborFinset g ∩ Iso).card = 18 := by
    rw [hSdef, hRdef, hPdef,
      Finset.sum_filter_add_sum_filter_not Hub (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)]
    exact hsum18
  have hRPcard : R.card + P.card = 11 := by
    have := Finset.card_filter_add_card_filter_not (s := Hub)
      (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)
    rw [← hRdef, ← hPdef, hHub] at this; exact this
  have hPle : ∑ g ∈ P, (G.neighborFinset g ∩ Iso).card ≤ P.card := by
    calc ∑ g ∈ P, (G.neighborFinset g ∩ Iso).card ≤ ∑ _g ∈ P, 1 := by
          apply Finset.sum_le_sum; intro g hg
          rw [hPdef, Finset.mem_filter] at hg; omega
      _ = P.card := by rw [Finset.sum_const, smul_eq_mul, mul_one]
  -- `N2`: at most two rich hubs have iso-degree `≥ 3` (shared infrastructure for the clean branch).
  have clean_two_hubs : ∀ (k : ℕ), R.card = k → 7 ≤ S - 2 * (k - 2) → 2 ≤ k → False := by
    intro k hrk hge hk2
    set A3 : Finset (Fin 19) := R.filter (fun h => 3 ≤ (G.neighborFinset h ∩ Iso).card)
      with hA3def
    have hN2 : A3.card ≤ 2 := by
      have heq : A3 = Hub.filter (fun h => G.degree h = 4 ∧ 3 ≤ (G.neighborFinset h ∩ Iso).card) := by
        rw [hA3def, hRdef, Finset.filter_filter]
        apply Finset.filter_congr
        intro a ha; constructor
        · rintro ⟨_, h3⟩; exact ⟨hdeg4 a ha, h3⟩
        · rintro ⟨_, h3⟩; exact ⟨by omega, h3⟩
      rw [heq]; exact rich_a3_count_le_two_nineteen G Hub Iso hdisj hshare hno2hub
    set B : Finset (Fin 19) := R.filter (fun h => ¬ 3 ≤ (G.neighborFinset h ∩ Iso).card)
      with hBdef
    set T : ℕ := ∑ r ∈ A3, (G.neighborFinset r ∩ Iso).card with hTdef
    have hAsplit : T + ∑ r ∈ B, (G.neighborFinset r ∩ Iso).card = S := by
      rw [hTdef, hSdef, hA3def, hBdef]
      exact Finset.sum_filter_add_sum_filter_not R _ _
    have hBval : ∑ r ∈ B, (G.neighborFinset r ∩ Iso).card = 2 * B.card := by
      rw [Finset.sum_congr rfl (fun r hr => ?_), Finset.sum_const, smul_eq_mul, mul_comm]
      rw [hBdef, Finset.mem_filter] at hr
      have h2 := ((hRmem r).mp hr.1).2
      omega
    have hcardk : A3.card + B.card = k := by
      have := Finset.card_filter_add_card_filter_not (s := R)
        (fun h => 3 ≤ (G.neighborFinset h ∩ Iso).card)
      rw [← hA3def, ← hBdef, hrk] at this; exact this
    have hTge : 3 * A3.card ≤ T := by
      rw [hTdef]
      calc 3 * A3.card = ∑ _r ∈ A3, 3 := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
        _ ≤ ∑ r ∈ A3, (G.neighborFinset r ∩ Iso).card := by
            apply Finset.sum_le_sum; intro r hr
            rw [hA3def, Finset.mem_filter] at hr; exact hr.2
    have hTle : T ≤ 4 * A3.card := by
      rw [hTdef]
      calc ∑ r ∈ A3, (G.neighborFinset r ∩ Iso).card ≤ ∑ _r ∈ A3, 4 := by
            apply Finset.sum_le_sum; intro r hr
            rw [hA3def, Finset.mem_filter] at hr
            have hrHub : r ∈ Hub := hRsubHub hr.1
            calc (G.neighborFinset r ∩ Iso).card ≤ (G.neighborFinset r).card :=
                  Finset.card_le_card Finset.inter_subset_left
              _ = 4 := by rw [G.card_neighborFinset_eq_degree, hdeg4 r hrHub]
        _ = 4 * A3.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    -- `S = T + 2·|B|`, `|A3| + |B| = k`, so `T = S − 2(k − |A3|)`; with `T ≤ 4|A3|`, `|A3| ≤ 2`
    -- and `7 ≤ S − 2(k − 2)`, force `|A3| = 2`.
    have hk2card : A3.card = 2 := by rw [hBval] at hAsplit; omega
    obtain ⟨w1, w2, hw12, hA3eq⟩ := Finset.card_eq_two.mp hk2card
    have hw1A3 : w1 ∈ A3 := by rw [hA3eq]; exact Finset.mem_insert_self _ _
    have hw2A3 : w2 ∈ A3 := by
      rw [hA3eq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    have hw1Hub : w1 ∈ Hub := hRsubHub (Finset.mem_of_mem_filter _ hw1A3)
    have hw2Hub : w2 ∈ Hub := hRsubHub (Finset.mem_of_mem_filter _ hw2A3)
    have hw1ge : 3 ≤ (G.neighborFinset w1 ∩ Iso).card := (Finset.mem_filter.mp hw1A3).2
    have hw2ge : 3 ≤ (G.neighborFinset w2 ∩ Iso).card := (Finset.mem_filter.mp hw2A3).2
    have hTpair : (G.neighborFinset w1 ∩ Iso).card + (G.neighborFinset w2 ∩ Iso).card = T := by
      rw [hTdef, hA3eq, Finset.sum_pair hw12]
    have hsum7 : 7 ≤ (G.neighborFinset w1 ∩ Iso).card + (G.neighborFinset w2 ∩ Iso).card := by
      rw [hBval] at hAsplit; omega
    exact two_high_hubs_sum_ge_seven_contra_nineteen G Hub Iso hdisj hdeg4 hshare hno2hub w1 w2
      hw1Hub hw2Hub hw12 hw1ge hw2ge hsum7
  -- Shared `z`-side cut infrastructure: `hg1, hg2` are poor hubs in `P`; whenever the poor-incidence
  -- sum `∑_P = 18 − S` exceeds the capacity `|P| − 2` of the *other* poor hubs, at least one of
  -- `hg1, hg2` carries a private twin (`hbothpoor`), feeding `z_side_poor_cut_nineteen`.
  have hg1Hub : hg1 ∈ Hub := (Finset.mem_inter.mp hg1mem).2
  have hg2Hub : hg2 ∈ Hub := (Finset.mem_inter.mp hg2mem).2
  have hg1P : hg1 ∈ P := by rw [hPdef, Finset.mem_filter]; exact ⟨hg1Hub, by omega⟩
  have hg2P : hg2 ∈ P := by rw [hPdef, Finset.mem_filter]; exact ⟨hg2Hub, by omega⟩
  have hPle1 : ∀ g ∈ P, (G.neighborFinset g ∩ Iso).card ≤ 1 := by
    intro g hg; rw [hPdef, Finset.mem_filter] at hg; omega
  have hbothpoor : (G.neighborFinset hg1 ∩ Iso).card = 0 → (G.neighborFinset hg2 ∩ Iso).card = 0 →
      ∑ g ∈ P, (G.neighborFinset g ∩ Iso).card ≤ P.card - 2 := by
    intro _h1z _h2z
    have hg2er : hg2 ∈ P.erase hg1 := Finset.mem_erase.mpr ⟨Ne.symm hg1ne, hg2P⟩
    have he1 := Finset.add_sum_erase P (fun g => (G.neighborFinset g ∩ Iso).card) hg1P
    have he2 := Finset.add_sum_erase (P.erase hg1) (fun g => (G.neighborFinset g ∩ Iso).card) hg2er
    have hcardE : ((P.erase hg1).erase hg2).card = P.card - 2 := by
      rw [Finset.card_erase_of_mem hg2er, Finset.card_erase_of_mem hg1P]; omega
    have hrestle : ∑ g ∈ (P.erase hg1).erase hg2, (G.neighborFinset g ∩ Iso).card
        ≤ ((P.erase hg1).erase hg2).card := by
      calc ∑ g ∈ (P.erase hg1).erase hg2, (G.neighborFinset g ∩ Iso).card
          ≤ ∑ _g ∈ (P.erase hg1).erase hg2, 1 :=
            Finset.sum_le_sum (fun g hg => hPle1 g
              (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hg)))
        _ = ((P.erase hg1).erase hg2).card := by rw [Finset.sum_const, smul_eq_mul, mul_one]
    rw [hcardE] at hrestle; omega
  rcases hr67 with hr6 | hr7
  · -- `r = 6`: `P.card = 5`, so `S ≥ 13`.
    have hPcard : P.card = 5 := by omega
    have hS13ge : 13 ≤ S := by omega
    rcases (by omega : S = 13 ∨ S = 14 ∨ 15 ≤ S) with hS13 | hS14 | hS15
    · -- `r = 6`, `S = 13`: closed by the reusable `z`-side cut (`∑_P = 5 > 3 = |P| − 2`).
      refine hnocut (Or.inl (z_side_poor_cut_nineteen G Hub Iso hdeg4 hiso3 hdisj hHub hIso hdsum
        hdeg3 hisodeg3 hleak z hz hg1 hg2 hg1ne hg1mem hg2mem hg1poor hg2poor ?_ (by rw [← hRdef]; omega)))
      by_contra hcon; push Not at hcon
      have hle := hbothpoor (by omega) (by omega); omega
    · -- `r = 6`, `S = 14`: closed by the reusable `z`-side cut (`∑_P = 4 > 3 = |P| − 2`).
      refine hnocut (Or.inl (z_side_poor_cut_nineteen G Hub Iso hdeg4 hiso3 hdisj hHub hIso hdsum
        hdeg3 hisodeg3 hleak z hz hg1 hg2 hg1ne hg1mem hg2mem hg1poor hg2poor ?_ (by rw [← hRdef]; omega)))
      by_contra hcon; push Not at hcon
      have hle := hbothpoor (by omega) (by omega); omega
    · -- `r = 6`, `S ≥ 15`: clean two non-adjacent high hubs.
      exact clean_two_hubs 6 hr6 (by omega) (by omega)
  · -- `r = 7`: `P.card = 4`, so `S ≥ 14`.
    have hPcard : P.card = 4 := by omega
    have hS14ge : 14 ≤ S := by omega
    rcases (by omega : S = 14 ∨ S = 15 ∨ S = 16) with hS14 | hS15 | hS16
    · -- `r = 7`, `S = 14`: closed by the reusable `z`-side cut (`∑_P = 4 > 2 = |P| − 2`).
      refine hnocut (Or.inl (z_side_poor_cut_nineteen G Hub Iso hdeg4 hiso3 hdisj hHub hIso hdsum
        hdeg3 hisodeg3 hleak z hz hg1 hg2 hg1ne hg1mem hg2mem hg1poor hg2poor ?_ (by rw [← hRdef]; omega)))
      by_contra hcon; push Not at hcon
      have hle := hbothpoor (by omega) (by omega); omega
    · -- `r = 7`, `S = 15`: the `M`-partner kill via the reusable cut.
      exact mpartner_meets_poor_nineteen G Hub Iso hdeg4 hiso3 hdisj hHub hIso hdeg3 hisodeg3
        hdsum hleak hshare hno2hub hC4 hK23 hT hnocut z hz hg1 hg2 hg1ne hg1mem hg2mem hg1poor
        hg2poor hres hr7 hS15
    · -- `r = 7`, `S = 16`: the saturation kill via the reusable cut.
      exact rich_seven_S16_two_poor_false_nineteen G Hub Iso hdeg4 hiso3 hdisj hHub hIso hdeg3
        hisodeg3 hdsum hleak hshare hno2hub hC4 hK23 hT hnocut z hz hg1 hg2 hg1ne hg1mem hg2mem
        hg1poor hg2poor hres hr7 hS16

/-- **Node A — `r = 7` under two poor hubs.**  The clean `S ≥ 17` sub-cases assemble a non-adjacent
degree-`4` pair (`two_high_hubs_sum_ge_seven_contra`); the `S ≤ 16` residual is dispatched through
`low_rich_iso_residual_nineteen`. -/
theorem rich_seven_two_poor_false_nineteen (G : SimpleGraph (Fin 19)) (Hub Iso : Finset (Fin 19))
    (hdeg4 : ∀ h ∈ Hub, G.degree h = 4)
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdisj : Disjoint Hub Iso) (hHub : Hub.card = 11) (hIso : Iso.card = 6)
    (hdeg3 : ∀ v : Fin 19, 3 ≤ G.degree v) (hisodeg3 : ∀ t ∈ Iso, G.degree t = 3)
    (hdsum : ∑ w ∈ Hub, G.degree w = 44)
    (hleak : ∑ h ∈ Hub, (G.neighborFinset h ∩ (Finset.univ \ (Hub ∪ Iso))).card ≤ 4)
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hno2hub : ¬∃ h₁ h₂ : Fin 19, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card)
    (hC4 : ¬∃ a b c d : Fin 19, ({a, b, c, d} : Finset (Fin 19)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (hK23 : ¬∃ a b c d e : Fin 19, ({a, b, c, d, e} : Finset (Fin 19)).card = 5 ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
      G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 19)
    (hT : ¬∃ x y z : Fin 19, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧
      G.degree x + G.degree y + G.degree z ≤ 11)
    (hnocut : ¬ ZPoorCutConfig G)
    (z : Fin 19) (hz : z ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 19)))
    (hg1 : Fin 19) (hg2 : Fin 19) (hg1ne : hg1 ≠ hg2)
    (hg1mem : hg1 ∈ G.neighborFinset z ∩ Hub) (hg2mem : hg2 ∈ G.neighborFinset z ∩ Hub)
    (hg1poor : (G.neighborFinset hg1 ∩ Iso).card ≤ 1)
    (hg2poor : (G.neighborFinset hg2 ∩ Iso).card ≤ 1)
    (hres : G.Adj hg1 hg2 ∨ (G.neighborFinset hg1 ∩ G.neighborFinset hg2 ∩ Iso).card = 0)
    (hr7 : (Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)).card = 7) :
    False := by
  classical
  set R : Finset (Fin 19) := Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card) with hRdef
  have hRsubHub : R ⊆ Hub := Finset.filter_subset _ _
  set S : ℕ := ∑ r ∈ R, (G.neighborFinset r ∩ Iso).card with hSdef
  have hsum18 : ∑ a ∈ Hub, (G.neighborFinset a ∩ Iso).card = 18 := by
    have := hub_iso_sum_nineteen G Hub Iso hiso3; rw [hIso] at this; omega
  have hS18 : S ≤ 18 := by
    rw [hSdef]
    calc ∑ r ∈ R, (G.neighborFinset r ∩ Iso).card
        ≤ ∑ a ∈ Hub, (G.neighborFinset a ∩ Iso).card := Finset.sum_le_sum_of_subset hRsubHub
      _ = 18 := hsum18
  by_cases hSlo : S ≤ 16
  · exact low_rich_iso_residual_nineteen G Hub Iso hdeg4 hiso3 hdisj hHub hIso hdeg3 hisodeg3
      hdsum hleak hshare hno2hub hC4 hK23 hT hnocut z hz hg1 hg2 hg1ne hg1mem hg2mem hg1poor hg2poor
      hres (Or.inr hr7) hSlo
  · -- `S ≥ 17`: clean two-hub assembly (`A3.card = 2`, sum `≥ 7`).
    have hS17 : 17 ≤ S := by omega
    set A3 : Finset (Fin 19) := R.filter (fun h => 3 ≤ (G.neighborFinset h ∩ Iso).card) with hA3def
    have hN2 : A3.card ≤ 2 := by
      have heq : A3 = Hub.filter (fun h => G.degree h = 4 ∧ 3 ≤ (G.neighborFinset h ∩ Iso).card) := by
        rw [hA3def, hRdef, Finset.filter_filter]
        apply Finset.filter_congr
        intro a ha; constructor
        · rintro ⟨_, h3⟩; exact ⟨hdeg4 a ha, h3⟩
        · rintro ⟨_, h3⟩; exact ⟨by omega, h3⟩
      rw [heq]; exact rich_a3_count_le_two_nineteen G Hub Iso hdisj hshare hno2hub
    set B : Finset (Fin 19) := R.filter (fun h => ¬ 3 ≤ (G.neighborFinset h ∩ Iso).card) with hBdef
    set T : ℕ := ∑ r ∈ A3, (G.neighborFinset r ∩ Iso).card with hTdef
    have hRmem : ∀ a, a ∈ R ↔ a ∈ Hub ∧ 2 ≤ (G.neighborFinset a ∩ Iso).card := by
      intro a; rw [hRdef, Finset.mem_filter]
    have hAsplit : T + ∑ r ∈ B, (G.neighborFinset r ∩ Iso).card = S := by
      rw [hTdef, hSdef, hA3def, hBdef]
      exact Finset.sum_filter_add_sum_filter_not R _ _
    have hBval : ∑ r ∈ B, (G.neighborFinset r ∩ Iso).card = 2 * B.card := by
      rw [Finset.sum_congr rfl (fun r hr => ?_), Finset.sum_const, smul_eq_mul, mul_comm]
      rw [hBdef, Finset.mem_filter] at hr
      have h2 := ((hRmem r).mp hr.1).2
      omega
    have hcard7 : A3.card + B.card = 7 := by
      have := Finset.card_filter_add_card_filter_not (s := R)
        (fun h => 3 ≤ (G.neighborFinset h ∩ Iso).card)
      rw [← hA3def, ← hBdef, hr7] at this; exact this
    have hTle : T ≤ 4 * A3.card := by
      rw [hTdef]
      calc ∑ r ∈ A3, (G.neighborFinset r ∩ Iso).card ≤ ∑ _r ∈ A3, 4 := by
            apply Finset.sum_le_sum; intro r hr
            rw [hA3def, Finset.mem_filter] at hr
            have hrHub : r ∈ Hub := hRsubHub hr.1
            calc (G.neighborFinset r ∩ Iso).card ≤ (G.neighborFinset r).card :=
                  Finset.card_le_card Finset.inter_subset_left
              _ = 4 := by rw [G.card_neighborFinset_eq_degree, hdeg4 r hrHub]
        _ = 4 * A3.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    have hk2 : A3.card = 2 := by rw [hBval] at hAsplit; omega
    obtain ⟨w1, w2, hw12, hA3eq⟩ := Finset.card_eq_two.mp hk2
    have hw1A3 : w1 ∈ A3 := by rw [hA3eq]; exact Finset.mem_insert_self _ _
    have hw2A3 : w2 ∈ A3 := by
      rw [hA3eq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    have hw1Hub : w1 ∈ Hub := hRsubHub (Finset.mem_of_mem_filter _ hw1A3)
    have hw2Hub : w2 ∈ Hub := hRsubHub (Finset.mem_of_mem_filter _ hw2A3)
    have hw1ge : 3 ≤ (G.neighborFinset w1 ∩ Iso).card := (Finset.mem_filter.mp hw1A3).2
    have hw2ge : 3 ≤ (G.neighborFinset w2 ∩ Iso).card := (Finset.mem_filter.mp hw2A3).2
    have hTpair : (G.neighborFinset w1 ∩ Iso).card + (G.neighborFinset w2 ∩ Iso).card = T := by
      rw [hTdef, hA3eq, Finset.sum_pair hw12]
    have hsum7 : 7 ≤ (G.neighborFinset w1 ∩ Iso).card + (G.neighborFinset w2 ∩ Iso).card := by
      rw [hBval] at hAsplit; omega
    exact two_high_hubs_sum_ge_seven_contra_nineteen G Hub Iso hdisj hdeg4 hshare hno2hub w1 w2
      hw1Hub hw2Hub hw12 hw1ge hw2ge hsum7

/-- **Node B — `r = 6` under two poor hubs.**  The clean `S ≥ 15` sub-cases assemble a non-adjacent
degree-`4` pair; the `S ≤ 16` residual (which for `r = 6` is the entire range) is dispatched through
`low_rich_iso_residual_nineteen`. -/
theorem rich_six_two_poor_false_nineteen (G : SimpleGraph (Fin 19)) (Hub Iso : Finset (Fin 19))
    (hdeg4 : ∀ h ∈ Hub, G.degree h = 4)
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdisj : Disjoint Hub Iso) (hHub : Hub.card = 11) (hIso : Iso.card = 6)
    (hdeg3 : ∀ v : Fin 19, 3 ≤ G.degree v) (hisodeg3 : ∀ t ∈ Iso, G.degree t = 3)
    (hdsum : ∑ w ∈ Hub, G.degree w = 44)
    (hleak : ∑ h ∈ Hub, (G.neighborFinset h ∩ (Finset.univ \ (Hub ∪ Iso))).card ≤ 4)
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hno2hub : ¬∃ h₁ h₂ : Fin 19, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card)
    (hC4 : ¬∃ a b c d : Fin 19, ({a, b, c, d} : Finset (Fin 19)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (hK23 : ¬∃ a b c d e : Fin 19, ({a, b, c, d, e} : Finset (Fin 19)).card = 5 ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
      G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 19)
    (hT : ¬∃ x y z : Fin 19, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧
      G.degree x + G.degree y + G.degree z ≤ 11)
    (hnocut : ¬ ZPoorCutConfig G)
    (z : Fin 19) (hz : z ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 19)))
    (hg1 : Fin 19) (hg2 : Fin 19) (hg1ne : hg1 ≠ hg2)
    (hg1mem : hg1 ∈ G.neighborFinset z ∩ Hub) (hg2mem : hg2 ∈ G.neighborFinset z ∩ Hub)
    (hg1poor : (G.neighborFinset hg1 ∩ Iso).card ≤ 1)
    (hg2poor : (G.neighborFinset hg2 ∩ Iso).card ≤ 1)
    (hres : G.Adj hg1 hg2 ∨ (G.neighborFinset hg1 ∩ G.neighborFinset hg2 ∩ Iso).card = 0)
    (hr6 : (Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)).card = 6) :
    False := by
  classical
  set R : Finset (Fin 19) := Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card) with hRdef
  have hRsubHub : R ⊆ Hub := Finset.filter_subset _ _
  set S : ℕ := ∑ r ∈ R, (G.neighborFinset r ∩ Iso).card with hSdef
  have hsum18 : ∑ a ∈ Hub, (G.neighborFinset a ∩ Iso).card = 18 := by
    have := hub_iso_sum_nineteen G Hub Iso hiso3; rw [hIso] at this; omega
  have hRmem : ∀ a, a ∈ R ↔ a ∈ Hub ∧ 2 ≤ (G.neighborFinset a ∩ Iso).card := by
    intro a; rw [hRdef, Finset.mem_filter]
  -- For `r = 6`, `S ≤ 16`: each rich hub has iso-degree `∈ [2, 4]` and at most two (`N2`) have
  -- iso-degree `≥ 3`, so `S ≤ 2·6 + 2·2 = 16`.  Hence the residual dispatcher always applies.
  have hS16 : S ≤ 16 := by
    have hN2 : (R.filter (fun h => 3 ≤ (G.neighborFinset h ∩ Iso).card)).card ≤ 2 := by
      have heq : R.filter (fun h => 3 ≤ (G.neighborFinset h ∩ Iso).card)
          = Hub.filter (fun h => G.degree h = 4 ∧ 3 ≤ (G.neighborFinset h ∩ Iso).card) := by
        rw [hRdef, Finset.filter_filter]; apply Finset.filter_congr
        intro a ha; constructor
        · rintro ⟨_, h3⟩; exact ⟨hdeg4 a ha, h3⟩
        · rintro ⟨_, h3⟩; exact ⟨by omega, h3⟩
      rw [heq]; exact rich_a3_count_le_two_nineteen G Hub Iso hdisj hshare hno2hub
    have hbound : S ≤ ∑ a ∈ R, (2 + 2 * (if 3 ≤ (G.neighborFinset a ∩ Iso).card then 1 else 0)) := by
      rw [hSdef]
      apply Finset.sum_le_sum
      intro a ha
      have h2 := ((hRmem a).mp ha).2
      have h4 : (G.neighborFinset a ∩ Iso).card ≤ 4 := by
        calc (G.neighborFinset a ∩ Iso).card ≤ (G.neighborFinset a).card :=
              Finset.card_le_card Finset.inter_subset_left
          _ = 4 := by rw [G.card_neighborFinset_eq_degree, hdeg4 a (hRsubHub ha)]
      split_ifs with h3 <;> omega
    rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, ← Finset.mul_sum,
      ← Finset.card_filter] at hbound
    rw [hr6] at hbound
    omega
  exact low_rich_iso_residual_nineteen G Hub Iso hdeg4 hiso3 hdisj hHub hIso hdeg3 hisodeg3
    hdsum hleak hshare hno2hub hC4 hK23 hT hnocut z hz hg1 hg2 hg1ne hg1mem hg2mem hg1poor hg2poor
    hres (Or.inl hr6) hS16

/-- **Two poor hubs through one `M`-edge endpoint force a contradiction (GLOBAL CORE).**  An
`M`-edge endpoint `z` meets exactly two hubs `g₁, g₂`; suppose both are *poor* (iso-degree `≤ 1`) and
we are in the residual regime where `g₁, g₂` are adjacent or share no `M`-isolated twin (`hres`).
The rich count lies in `{6, 7}` (`rich_count_ge_six` / `le_seven`); each branch dispatches to the
corresponding node prover.  The `rich_count_ge_six_nineteen` call supplies its threaded `r = 5`
octahedron residual `hoct5` via a precisely-scoped documented `sorry` (the `|Hub| = 11`,
`r = 5`, `S = 12` deep regime).

This is the unfolded `ZMeetsTwoPoorResidual G Hub Iso` witness statement: once `RichZdeg` imports
this file it discharges `hztwopoor` library-wide. -/
theorem z_meets_two_poor_forces_two_hub_nineteen (G : SimpleGraph (Fin 19))
    (Hub Iso : Finset (Fin 19))
    (hdeg4 : ∀ h ∈ Hub, G.degree h = 4)
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdisj : Disjoint Hub Iso) (hHub : Hub.card = 11) (hIso : Iso.card = 6)
    (hdeg3 : ∀ v : Fin 19, 3 ≤ G.degree v) (hisodeg3 : ∀ t ∈ Iso, G.degree t = 3)
    (hdsum : ∑ w ∈ Hub, G.degree w = 44)
    (hleak : ∑ h ∈ Hub, (G.neighborFinset h ∩ (Finset.univ \ (Hub ∪ Iso))).card ≤ 4)
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hno2hub : ¬∃ h₁ h₂ : Fin 19, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card)
    (hC4 : ¬∃ a b c d : Fin 19, ({a, b, c, d} : Finset (Fin 19)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (hK23 : ¬∃ a b c d e : Fin 19, ({a, b, c, d, e} : Finset (Fin 19)).card = 5 ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
      G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 19)
    (hT : ¬∃ x y z : Fin 19, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧
      G.degree x + G.degree y + G.degree z ≤ 11) :
    ∀ (z : Fin 19), z ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 19)) →
      ∀ (hg1 hg2 : Fin 19), hg1 ≠ hg2 →
        hg1 ∈ G.neighborFinset z ∩ Hub → hg2 ∈ G.neighborFinset z ∩ Hub →
        (G.neighborFinset hg1 ∩ Iso).card ≤ 1 → (G.neighborFinset hg2 ∩ Iso).card ≤ 1 →
        (G.Adj hg1 hg2 ∨ (G.neighborFinset hg1 ∩ G.neighborFinset hg2 ∩ Iso).card = 0) →
        ZPoorCutConfig G := by
  classical
  intro z hz hg1 hg2 hg1ne hg1mem hg2mem hg1poor hg2poor hres
  by_contra hnocut
  -- The rich count lies in `{6, 7}`.  `rich_count_ge_six_nineteen` needs its threaded `r = 5`
  -- octahedron residual `hoct5`, discharged by `r5_resid_nineteen` (the `r = 5`, `S = 12` residual;
  -- see `TwinCert19R5Resid`, which reduces it to the two iso-degree multisets and their
  -- octahedron-poor / star-triangle packing).
  have hoct5 := r5_resid_nineteen G Hub Iso hdeg4 hiso3 hdisj hHub hIso hdeg3 hisodeg3 hdsum hleak
    hshare hno2hub hC4 hK23 hT
  -- `rich_count_ge_six_nineteen` now yields `6 ≤ |R| ∨ ZPoorCutConfig G`: either the rich count is
  -- `≥ 6` (then the `r ∈ {6,7}` dispatch closes the two-poor regime by contradiction) or the `r = 5`
  -- octahedron residual directly supplies the boundary cut (`ZPoorCutConfig G`).
  rcases rich_count_ge_six_nineteen G Hub Iso hdeg4 hiso3 hdisj hHub hIso hshare hno2hub hoct5 with
    hge | hcut
  · have hle : (Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)).card ≤ 7 :=
      rich_count_le_seven_nineteen G Hub Iso hdeg4 hiso3 hdisj hHub hIso hshare hno2hub
    have hcases : (Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)).card = 6 ∨
        (Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)).card = 7 := by omega
    rcases hcases with h6 | h7
    · exact rich_six_two_poor_false_nineteen G Hub Iso hdeg4 hiso3 hdisj hHub hIso hdeg3 hisodeg3
        hdsum hleak hshare hno2hub hC4 hK23 hT hnocut z hz hg1 hg2 hg1ne hg1mem hg2mem hg1poor hg2poor
        hres h6
    · exact rich_seven_two_poor_false_nineteen G Hub Iso hdeg4 hiso3 hdisj hHub hIso hdeg3 hisodeg3
        hdsum hleak hshare hno2hub hC4 hK23 hT hnocut z hz hg1 hg2 hg1ne hg1mem hg2mem hg1poor hg2poor
        hres h7
  · exact hnocut hcut

end N19

end ACMax
