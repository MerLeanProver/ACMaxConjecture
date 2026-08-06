import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N18.Core
import ACMaxConjecture.SmallCases.N18.TwoHubSelect
import ACMaxConjecture.SmallCases.N18.StarTriangleStruct
import ACMaxConjecture.SmallCases.N18.RichCount
import ACMaxConjecture.SmallCases.N18.Align8Helpers
import ACMaxConjecture.SmallCases.N18.ZPoorN3
import ACMaxConjecture.SmallCases.N18.ZPoorR7
import ACMaxConjecture.SmallCases.N18.ZVertex
import ACMaxConjecture.SmallCases.N18.ZPoorSat
import ACMaxConjecture.SmallCases.N18.ZPoorR6Dist
import ACMaxConjecture.SmallCases.N18.ZPoorR6Sat
import ACMaxConjecture.SmallCases.N18.ZPoorR6Poor
import ACMaxConjecture.SmallCases.N18.ZPoorR6HubAdj
import ACMaxConjecture.SmallCases.N18.ZPoorR6HubAdjA
import ACMaxConjecture.SmallCases.N18.ZPoorR6HubAdjB

/-!
# The `r = 6`, `S = 14` non-adjacent two-poor disjunction (`n = 18`)

This file carries the structural crux of the non-adjacent two-poor residual for the tight
`e(M) = 1`, all-degree-`4`, `(|Hub|, |Iso|) = (10, 6)` profile with six rich hubs and rich
iso-incidence sum `S = 14`.

## The disjunction (and why the "apex always exists" lemma is *false*)

An `M`-edge endpoint `z` meets two **non-adjacent** poor hubs `hg₁, hg₂` (`hnadj`) with
`codeg_Iso(hg₁, hg₂) = 0` (`hcodeg0`); its `M`-partner `zp` (`z ~ zp`) meets two hubs, neither
`hg₁` nor `hg₂` (`hd1, hd2`).  An earlier plan asserted that there is **always** an *apex* hub
`x ∉ {hg₁, hg₂}` adjacent to `zp` and to one of `hg₁, hg₂` (the apex of a good `C₄`
`hgᵢ – x – zp – z`).  **This is false**: by direct randomized construction one finds configurations
satisfying *all* of `hdeg4`, `hiso3`, `hdsum = 40`, `hleak`, `hr6 = 6`, `hS14 = 14`, the share /
two-hub hypotheses `hshare`, `hno2hub`, the non-adjacency `hnadj` and `hcodeg0 = 0`, **with no apex
at all** (e.g. design `B` with iso-triple `{0,1,2}` adjacent and a twin-cherry `{0,1,t}` killing the
configuration instead).  In every such no-apex configuration the kill is a **good triangle** of
degree sum `≤ 11` — either `{zp, d₁, d₂}` (when `zp`'s two hub-neighbours `d₁, d₂` are adjacent,
degree sum `3 + 4 + 4 = 11`) or a *twin-cherry* `{t, h₁, h₂}` (a twin whose two hub-neighbours are
adjacent, degree sum `3 + 4 + 4 = 11`).

Consequently the correct, *true* statement is the **disjunction** `apex ∨ (∃ good triangle ≤ 11)`,
established here.  Randomized verification (MCMC over the thin `hshare ∧ hno2hub` manifold,
`hg₁ ≁ hg₂`): every hard configuration is killed by the apex `C₄` or by a good `≤ 11` triangle; no
deep counterexample (no apex and no good triangle) was found.
-/

namespace ACMax

open scoped Classical

namespace N18

/-- **The `r = 6`, `S = 14` non-adjacent two-poor disjunction (apex `C₄` or good triangle).**
In the tight `e(M) = 1`, all-degree-`4`, `(|Hub|, |Iso|) = (10, 6)` profile with six rich hubs and
rich iso-incidence sum `S = 14`, an `M`-edge endpoint `z` meets two non-adjacent poor hubs
`hg₁, hg₂` (`hnadj`, `hcodeg0 = 0`); its `M`-partner `zp` meets two hubs, neither `hg₁` nor `hg₂`
(`hd1, hd2`).  Then either there is an **apex** hub `x ∉ {hg₁, hg₂}` adjacent to `zp` and to one of
`hg₁, hg₂` (the apex of the good `C₄` `hgᵢ – x – zp – z`), or there is a **good triangle** of degree
sum `≤ 11` (the `M`-partner triangle `{zp, d₁, d₂}` or a twin-cherry).

**Status (the single documented `sorry`, now isolated to one hub adjacency).**  The proof here is
complete *except* for one fact: the apex `by_cases`, the twin-cherry good-triangle construction and
the `{zp, d₁, d₂}` assembly are all proved.  The sole remaining step is the **hub-adjacency core**
`G.Adj d₁ d₂` in the *no-apex, no-twin-cherry* branch (`d₁, d₂` are `zp`'s two hub-neighbours).  This
is the excess-`9`, `60 = 3·20` no-slack boundary (`Dadj ≤ 10`, `D ≥ 20`): the clean counting
(`rich_D_dichotomy_S14` + the share-`1` `biUnion` bound) ties at `20` and does *not* close it; one
needs a rigid per-design (`{4,2,2,2,2,2}` / `{3,3,2,2,2,2}`) hub-graph analysis at the
`e(Hub, Hub) = 9` budget with `hshare` and `hno2hub`, forcing the edge `d₁ ~ d₂`.  Randomized search
(MCMC over the thin `hshare ∧ hno2hub` manifold, `hg₁ ≁ hg₂`) confirms this with no counterexample.
This is a multi-subcase sub-development beyond a single leaf and is delegated as the one `sorry`. -/
theorem apex_or_good_triangle_S14 (G : SimpleGraph (Fin 18)) (Hub Iso : Finset (Fin 18))
    (hdeg4 : ∀ h ∈ Hub, G.degree h = 4)
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdisj : Disjoint Hub Iso) (hHub : Hub.card = 10) (hIso : Iso.card = 6)
    (hdeg3 : ∀ v : Fin 18, 3 ≤ G.degree v) (hisodeg3 : ∀ t ∈ Iso, G.degree t = 3)
    (hdsum : ∑ w ∈ Hub, G.degree w = 40)
    (hleak : ∑ h ∈ Hub, (G.neighborFinset h ∩ (Finset.univ \ (Hub ∪ Iso))).card ≤ 4)
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hno2hub : ¬∃ h₁ h₂ : Fin 18, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card)
    (hr6 : (Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)).card = 6)
    (hS14 : ∑ r ∈ Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card),
        (G.neighborFinset r ∩ Iso).card = 14)
    (z zp hg1 hg2 : Fin 18)
    (hz : z ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 18)))
    (hzpZ : zp ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 18)))
    (hzpz : zp ≠ z) (_hzzp : G.Adj z zp)
    (hg1ne : hg1 ≠ hg2)
    (hg1mem : hg1 ∈ G.neighborFinset z ∩ Hub) (hg2mem : hg2 ∈ G.neighborFinset z ∩ Hub)
    (hg1poor : (G.neighborFinset hg1 ∩ Iso).card ≤ 1)
    (hg2poor : (G.neighborFinset hg2 ∩ Iso).card ≤ 1)
    (hd1 : ¬G.Adj hg1 zp) (hd2 : ¬G.Adj hg2 zp)
    (hnadj : ¬G.Adj hg1 hg2)
    (hcodeg0 : (G.neighborFinset hg1 ∩ G.neighborFinset hg2 ∩ Iso).card = 0) :
    (∃ x : Fin 18, x ∈ Hub ∧ x ≠ hg1 ∧ x ≠ hg2 ∧ G.Adj zp x ∧
        (G.Adj hg1 x ∨ G.Adj hg2 x)) ∨
    (∃ a b c : Fin 18, a ≠ b ∧ b ≠ c ∧ a ≠ c ∧
        G.Adj a b ∧ G.Adj b c ∧ G.Adj a c ∧
        G.degree a + G.degree b + G.degree c ≤ 11) := by
  classical
  -- If an apex exists, take the left disjunct.
  by_cases hapex : ∃ x : Fin 18, x ∈ Hub ∧ x ≠ hg1 ∧ x ≠ hg2 ∧ G.Adj zp x ∧
      (G.Adj hg1 x ∨ G.Adj hg2 x)
  · exact Or.inl hapex
  right
  -- `zp` meets exactly two hubs `d₁, d₂` (degree `3`, no twin).
  obtain ⟨hzpiso0, hzphub2, hzpdeg3⟩ := z_two_hub_nbrs_eighteen G Hub Iso hiso3 hdisj hHub hIso hdsum
    hdeg3 hisodeg3 hleak zp hzpZ
  have hzp_notHub : zp ∉ Hub := fun hh =>
    (Finset.mem_sdiff.mp hzpZ).2 (Finset.mem_union_left Iso hh)
  obtain ⟨d1, d2, hd1d2ne, hNzpHub⟩ := Finset.card_eq_two.mp hzphub2
  have hd1in : d1 ∈ G.neighborFinset zp ∩ Hub := by rw [hNzpHub]; simp
  have hd2in : d2 ∈ G.neighborFinset zp ∩ Hub := by rw [hNzpHub]; simp
  have hd1Hub : d1 ∈ Hub := (Finset.mem_inter.mp hd1in).2
  have hd2Hub : d2 ∈ Hub := (Finset.mem_inter.mp hd2in).2
  have hzpd1 : G.Adj zp d1 := (G.mem_neighborFinset zp d1).mp (Finset.mem_inter.mp hd1in).1
  have hzpd2 : G.Adj zp d2 := (G.mem_neighborFinset zp d2).mp (Finset.mem_inter.mp hd2in).1
  have hzpd1ne : zp ≠ d1 := fun he => hzp_notHub (he ▸ hd1Hub)
  have hzpd2ne : zp ≠ d2 := fun he => hzp_notHub (he ▸ hd2Hub)
  -- A *twin-cherry* (a twin with two adjacent hub-neighbours) is itself a good triangle `≤ 11`.
  by_cases hcherry : ∃ t ∈ Iso, ∃ a b : Fin 18, a ∈ G.neighborFinset t ∧ b ∈ G.neighborFinset t ∧
      a ≠ b ∧ G.Adj a b
  · obtain ⟨t, ht, a, b, hat, hbt, hab, habadj⟩ := hcherry
    -- A twin's neighbourhood lies in `Hub`, and the twin has degree `3`.
    have hc3 := hiso3 t ht
    have hdt : (G.neighborFinset t).card = 3 := by
      rw [G.card_neighborFinset_eq_degree, hisodeg3 t ht]
    have heq : G.neighborFinset t ∩ Hub = G.neighborFinset t :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by rw [hc3, hdt])
    have htsubHub : G.neighborFinset t ⊆ Hub := heq ▸ Finset.inter_subset_right
    have haHub : a ∈ Hub := htsubHub hat
    have hbHub : b ∈ Hub := htsubHub hbt
    have hat' : G.Adj t a := (G.mem_neighborFinset t a).mp hat
    have hbt' : G.Adj t b := (G.mem_neighborFinset t b).mp hbt
    have hta_ne : a ≠ t := by rintro rfl; exact Finset.disjoint_left.mp hdisj haHub ht
    have htb_ne : b ≠ t := by rintro rfl; exact Finset.disjoint_left.mp hdisj hbHub ht
    exact ⟨a, b, t, hab, htb_ne, hta_ne, habadj, hbt'.symm, hat'.symm, by
      rw [hdeg4 a haHub, hdeg4 b hbHub, hisodeg3 t ht]⟩
  · -- **The hard core (the single documented `sorry`).**  No apex and no twin-cherry force `zp`'s
    -- two hub-neighbours to be adjacent, giving the good triangle `{zp, d₁, d₂}` of degree sum
    -- `3 + 4 + 4 = 11`.  This is the rigid per-design (`{4,2,2,2,2,2}` / `{3,3,2,2,2,2}`) hub-graph
    -- analysis at the `e(Hub, Hub) = 9` no-slack boundary, using `hshare` and `hno2hub`.
    have hcore : G.Adj d1 d2 := by
      by_contra hnd
      -- Hub membership and adjacency reorientations.
      have hg1Hub : hg1 ∈ Hub := (Finset.mem_inter.mp hg1mem).2
      have hg2Hub : hg2 ∈ Hub := (Finset.mem_inter.mp hg2mem).2
      have hg1z : G.Adj hg1 z :=
        ((G.mem_neighborFinset z hg1).mp (Finset.mem_inter.mp hg1mem).1).symm
      have hg2z : G.Adj hg2 z :=
        ((G.mem_neighborFinset z hg2).mp (Finset.mem_inter.mp hg2mem).1).symm
      have hd1zp : G.Adj d1 zp := hzpd1.symm
      have hd2zp : G.Adj d2 zp := hzpd2.symm
      -- `d₁, d₂` differ from the poor hubs `hg₁, hg₂` (they meet `zp`, which `hgᵢ` avoid).
      have hd1g1 : d1 ≠ hg1 := fun h => hd1 ((h ▸ hzpd1).symm)
      have hd1g2 : d1 ≠ hg2 := fun h => hd2 ((h ▸ hzpd1).symm)
      have hd2g1 : d2 ≠ hg1 := fun h => hd1 ((h ▸ hzpd2).symm)
      have hd2g2 : d2 ≠ hg2 := fun h => hd2 ((h ▸ hzpd2).symm)
      -- The four poor hubs each have iso-degree exactly `1`.
      have hpoor1 := poor_handshake_S14 G Hub Iso hiso3 hIso hHub hr6 hS14
      have hg1iso1 : (G.neighborFinset hg1 ∩ Iso).card = 1 :=
        hpoor1 hg1 (Finset.mem_filter.mpr ⟨hg1Hub, by omega⟩)
      have hg2iso1 : (G.neighborFinset hg2 ∩ Iso).card = 1 :=
        hpoor1 hg2 (Finset.mem_filter.mpr ⟨hg2Hub, by omega⟩)
      -- `z`'s two hub-neighbours are exactly `hg₁, hg₂`.
      obtain ⟨hziso0, hzhub2, hzdeg3⟩ := z_two_hub_nbrs_eighteen G Hub Iso hiso3 hdisj hHub hIso
        hdsum hdeg3 hisodeg3 hleak z hz
      have hzHubeq : G.neighborFinset z ∩ Hub = {hg1, hg2} := by
        refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
        · intro x hx
          rcases Finset.mem_insert.mp hx with rfl | hx
          · exact hg1mem
          · rw [Finset.mem_singleton] at hx; subst hx; exact hg2mem
        · rw [hzhub2]
          have h2 : ({hg1, hg2} : Finset (Fin 18)).card = 2 := by
            rw [Finset.card_insert_of_notMem (by simp [hg1ne]), Finset.card_singleton]
          omega
      -- Hence neither `d₁` nor `d₂` is adjacent to `z`.
      have hzd1 : ¬G.Adj z d1 := by
        intro hadj
        have hmem : d1 ∈ G.neighborFinset z ∩ Hub :=
          Finset.mem_inter.mpr ⟨(G.mem_neighborFinset z d1).mpr hadj, hd1Hub⟩
        rw [hzHubeq, Finset.mem_insert, Finset.mem_singleton] at hmem
        rcases hmem with h | h
        · exact hd1g1 h
        · exact hd1g2 h
      have hzd2 : ¬G.Adj z d2 := by
        intro hadj
        have hmem : d2 ∈ G.neighborFinset z ∩ Hub :=
          Finset.mem_inter.mpr ⟨(G.mem_neighborFinset z d2).mpr hadj, hd2Hub⟩
        rw [hzHubeq, Finset.mem_insert, Finset.mem_singleton] at hmem
        rcases hmem with h | h
        · exact hd2g1 h
        · exact hd2g2 h
      -- `d₁`'s iso-degree is `1` (poor) or `2` (rich, saturated by `rich_inA_saturated_S14`).
      have hd1iso : (G.neighborFinset d1 ∩ Iso).card = 1 ∨ (G.neighborFinset d1 ∩ Iso).card = 2 := by
        by_cases hr : 2 ≤ (G.neighborFinset d1 ∩ Iso).card
        · exact Or.inr (rich_inA_saturated_S14 G Hub Iso hdeg4 hdisj hHub hIso hshare hno2hub hr6
            hS14 z zp hz hzpZ hzpz.symm d1 hd1Hub hr hzd1 hzpd1).1
        · exact Or.inl (hpoor1 d1 (Finset.mem_filter.mpr ⟨hd1Hub, hr⟩))
      have hd2iso : (G.neighborFinset d2 ∩ Iso).card = 1 ∨ (G.neighborFinset d2 ∩ Iso).card = 2 := by
        by_cases hr : 2 ≤ (G.neighborFinset d2 ∩ Iso).card
        · exact Or.inr (rich_inA_saturated_S14 G Hub Iso hdeg4 hdisj hHub hIso hshare hno2hub hr6
            hS14 z zp hz hzpZ hzpz.symm d2 hd2Hub hr hzd2 hzpd2).1
        · exact Or.inl (hpoor1 d2 (Finset.mem_filter.mpr ⟨hd2Hub, hr⟩))
      -- The rich iso-degree dichotomy `{4,2,2,2,2,2}` / `{3,3,2,2,2,2}`.
      rcases rich_isodeg_dist_six_S14 G Hub Iso
          (Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)) hdeg4
          (Finset.filter_subset _ _) (fun a ha => (Finset.mem_filter.mp ha).2) hr6 hS14
          with hA | hB
      · -- Design `A` (`{4,2,2,2,2,2}`) is impossible.
        obtain ⟨w, hwR, hw4, hwrest⟩ := hA
        have hwHub : w ∈ Hub := (Finset.mem_filter.mp hwR).1
        have hother2 : ∀ r ∈ Hub, r ≠ w → 2 ≤ (G.neighborFinset r ∩ Iso).card →
            (G.neighborFinset r ∩ Iso).card = 2 := fun r hrHub hrw hrrich =>
          hwrest r (Finset.mem_filter.mpr ⟨hrHub, hrrich⟩) hrw
        exact forced_designA_false_S14 G Hub Iso hiso3 hdisj hHub hIso hdsum hdeg3 hisodeg3 hleak
          hdeg4 hshare hno2hub hcherry w z zp hg1 hg2 d1 d2 hwHub hw4 hother2 hr6 hz hzpZ hg1Hub
          hg2Hub hd1Hub hd2Hub hg1z hg2z hd1zp hd2zp hd1 hd2 hg1ne hd1d2ne hnadj hnd hcodeg0 hapex
          hg1iso1 hg2iso1 hd1iso hd2iso
      · -- Design `B` (`{3,3,2,2,2,2}`) is impossible.
        obtain ⟨w1, hw1R, w2, hw2R, hw1w2ne, hw13, hw23, hwrest⟩ := hB
        have hw1Hub : w1 ∈ Hub := (Finset.mem_filter.mp hw1R).1
        have hw2Hub : w2 ∈ Hub := (Finset.mem_filter.mp hw2R).1
        have hother2 : ∀ r ∈ Hub, r ≠ w1 → r ≠ w2 → 2 ≤ (G.neighborFinset r ∩ Iso).card →
            (G.neighborFinset r ∩ Iso).card = 2 := fun r hrHub hrw1 hrw2 hrrich =>
          hwrest r (Finset.mem_filter.mpr ⟨hrHub, hrrich⟩) hrw1 hrw2
        exact forced_designB_false_S14 G Hub Iso hiso3 hdisj hHub hIso hdsum hdeg3 hisodeg3 hleak
          hdeg4 hshare hno2hub hcherry w1 w2 z zp hg1 hg2 d1 d2 hw1Hub hw2Hub hw1w2ne hw13 hw23
          hother2 hz hzpZ hg1Hub hg2Hub hd1Hub hd2Hub hg1z hg2z hd1zp hd2zp hd1 hd2 hg1ne hd1d2ne
          hnadj hnd hapex hg1iso1 hg2iso1 hcodeg0 hd1iso hd2iso
    exact ⟨zp, d1, d2, hzpd1ne, hd1d2ne, hzpd2ne, hzpd1, hcore, hzpd2, by
      rw [hzpdeg3, hdeg4 d1 hd1Hub, hdeg4 d2 hd2Hub]⟩

end N18

end ACMax
