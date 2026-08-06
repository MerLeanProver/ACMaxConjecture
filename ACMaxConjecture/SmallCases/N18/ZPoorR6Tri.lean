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
import ACMaxConjecture.SmallCases.N18.ZPoorR6S14Kernel

/-!
# The `r = 6`, `S = 14` non-adjacent two-poor residual (`n = 18`)

For the tight `e(M) = 1`, all-degree-`4`, `(|Hub|, |Iso|) = (10, 6)` profile with six rich hubs and
rich iso-incidence sum `S = 14`, an `M`-edge endpoint `z` meets two poor hubs `hg₁, hg₂`.  The kill
splits on whether `hg₁, hg₂` are adjacent:

* **adjacent** (`hg₁ ~ hg₂`): `{hg₁, hg₂, z}` is a triangle of degree sum `4 + 4 + 3 = 11`, killed
  directly by the triangle certificate `hT` (`≤ 11`).  This is the *`Z`-cherry* kill, proved in full
  in `rich_six_S14_two_poor_false_eighteen` (file `TwinCert18ZPoorR6S14`).
* **non-adjacent** (`hg₁ ≁ hg₂`, hence `codeg_Iso(hg₁, hg₂) = 0` from the residual disjunction): this
  is the genuinely structural residual carried by `rich_six_S14_hard_residual` below.

## Why the original "twin-cherry" route is abandoned (a false lemma)

An earlier plan claimed a *twin*-cherry always exists: some twin `t` (degree `3`) with two adjacent
hub-neighbours, giving a triangle `{h₁, h₂, t}` of degree sum `11`.  This is **false**.  By direct
randomized construction of *no-twin-cherry* configurations (every twin-triple `N(t) ∩ Hub`
independent in the `9`-edge hub graph) one finds valid configs satisfying *all* of `hdeg4`, `hiso3`,
`hdsum = 40`, `hleak`, `hr6 = 6`, `hS14 = 14`, **and** the share/two-hub hypotheses `hshare`,
`hno2hub`, yet with **no twin-cherry at all** (e.g. the design-`{4,2,2,2,2,2}` graph with hub
iso-degrees `[1,1,1,2,2,2,4,2,1,2]`).  Hence the twin-cherry statement is not a theorem; the closing
triangle, when it exists, is a `Z`-cherry `{hg₁, hg₂, z}`, not a twin-cherry — and in the
non-adjacent residual the kill is a good `C₄` (`hC4`), not a triangle at all.

## Status of the residual

`rich_six_S14_hard_residual` is the irreducible structural fact for the non-adjacent two-poor case.
Across all forced designs the four poor hubs and the `M`-partner `zp` admit a good `C₄` of degree sum
`4 + 4 + 3 + 3 = 14` (or, on a sub-family, a good triangle of degree sum `≤ 11`), excluded by `hC4`
/ `hT`.  This is the original `M`-partner extraction (a multi-design structural cluster, no unique
design pinned at the excess-`9` boundary), carried by the single documented `sorry`.
-/

namespace ACMax

open scoped Classical

namespace N18

/-- **The `r = 6`, `S = 14` non-adjacent two-poor residual (the structural core).**  In the tight
`e(M) = 1`, all-degree-`4`, `(|Hub|, |Iso|) = (10, 6)` profile with six rich hubs and rich
iso-incidence sum `S = 14`, an `M`-edge endpoint `z` meets two **non-adjacent** poor hubs
`hg₁, hg₂` (`hnadj`) with `codeg_Iso(hg₁, hg₂) = 0` (`hcodeg0`).  This regime is contradictory.

**Proof (the assembly; the crux is delegated).**  Extract the `M`-partner `zp` (`z`'s unique
`Z`-neighbour) and derive `hg₁ ≁ zp`, `hg₂ ≁ zp` from `no_hub_adj_both_mends` (else a `≤ 10`
triangle).  The disjunction `apex ∨ (∃ good triangle ≤ 11)` is supplied by the kernel lemma
`mpartner_common_poor_nbr_S14`.  In the **apex** branch the hub `x ∉ {hg₁, hg₂}` adjacent to `zp` and
to some `hgᵢ` yields the good `C₄` `hgᵢ – x – zp – z` (degree sum `4 + 4 + 3 + 3 = 14`, diagonals
`hgᵢ ≁ zp` and `x ≁ z` since `N(z) ∩ Hub = {hg₁, hg₂}`), excluded by `hC4`; in the **triangle**
branch the good `≤ 11` triangle is excluded by `hT` directly.

**Status.**  The assembly here is complete and `sorry`-free; the single documented `sorry` is the
structural crux `apex_or_good_triangle_S14` (multi-subcase per-design at the `60 = 3·20` no-slack
boundary, beyond a leaf).  Note the *twin*-cherry and "apex always exists" routes are provably
false (see `TwinCert18ZPoorR6Hard`). -/
theorem rich_six_S14_hard_residual (G : SimpleGraph (Fin 18)) (Hub Iso : Finset (Fin 18))
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
    (hC4 : ¬∃ a b c d : Fin 18, ({a, b, c, d} : Finset (Fin 18)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (hK23 : ¬∃ a b c d e : Fin 18, ({a, b, c, d, e} : Finset (Fin 18)).card = 5 ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
      G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 19)
    (hT : ¬∃ x y z : Fin 18, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧
      G.degree x + G.degree y + G.degree z ≤ 11)
    (z hg1 hg2 : Fin 18) (hz : z ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 18)))
    (hg1ne : hg1 ≠ hg2)
    (hg1mem : hg1 ∈ G.neighborFinset z ∩ Hub) (hg2mem : hg2 ∈ G.neighborFinset z ∩ Hub)
    (hg1poor : (G.neighborFinset hg1 ∩ Iso).card ≤ 1)
    (hg2poor : (G.neighborFinset hg2 ∩ Iso).card ≤ 1)
    (hnadj : ¬G.Adj hg1 hg2)
    (hcodeg0 : (G.neighborFinset hg1 ∩ G.neighborFinset hg2 ∩ Iso).card = 0)
    (hr6 : (Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)).card = 6)
    (hS14 : ∑ r ∈ Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card),
        (G.neighborFinset r ∩ Iso).card = 14) :
    False := by
  classical
  have hg1Hub : hg1 ∈ Hub := (Finset.mem_inter.mp hg1mem).2
  have hg2Hub : hg2 ∈ Hub := (Finset.mem_inter.mp hg2mem).2
  have hzg1 : G.Adj z hg1 := (G.mem_neighborFinset z hg1).mp (Finset.mem_inter.mp hg1mem).1
  have hzg2 : G.Adj z hg2 := (G.mem_neighborFinset z hg2).mp (Finset.mem_inter.mp hg2mem).1
  -- `z` meets exactly two hubs, no twin, and has degree `3`.
  obtain ⟨hziso0, hzhub2, hzdeg3⟩ := z_two_hub_nbrs_eighteen G Hub Iso hiso3 hdisj hHub hIso hdsum
    hdeg3 hisodeg3 hleak z hz
  -- `z` has exactly one `Z`-neighbour, its `M`-partner `zp`.
  have hzZ1 : (G.neighborFinset z ∩ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 18))).card = 1 := by
    have hsp := nbr_split_three_eighteen G Hub Iso hdisj z
    rw [hzhub2, hziso0, hzdeg3] at hsp; omega
  obtain ⟨zp, hzpeq⟩ := Finset.card_eq_one.mp hzZ1
  have hzpmem : zp ∈ G.neighborFinset z ∩ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 18)) := by
    rw [hzpeq]; exact Finset.mem_singleton_self _
  have hzpZ : zp ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 18)) := (Finset.mem_inter.mp hzpmem).2
  have hzzp : G.Adj z zp := (G.mem_neighborFinset z zp).mp (Finset.mem_inter.mp hzpmem).1
  have hzpz : zp ≠ z := (hzzp.ne).symm
  obtain ⟨_, _, hzpdeg3⟩ := z_two_hub_nbrs_eighteen G Hub Iso hiso3 hdisj hHub hIso hdsum hdeg3
    hisodeg3 hleak zp hzpZ
  have hz_notHub : z ∉ Hub := fun hh =>
    (Finset.mem_sdiff.mp hz).2 (Finset.mem_union_left Iso hh)
  have hzp_notHub : zp ∉ Hub := fun hh =>
    (Finset.mem_sdiff.mp hzpZ).2 (Finset.mem_union_left Iso hh)
  -- Promote the triangle certificate `hT (≤ 11)` to the `≤ 10` form for `no_hub_adj_both_mends`.
  have hT10 : ¬∃ x y w : Fin 18, x ≠ y ∧ y ≠ w ∧ x ≠ w ∧
      G.Adj x y ∧ G.Adj y w ∧ G.Adj x w ∧ G.degree x + G.degree y + G.degree w ≤ 10 := by
    rintro ⟨x, y, w, hxy, hyw, hxw, hax, hay, haw, hsum⟩
    exact hT ⟨x, y, w, hxy, hyw, hxw, hax, hay, haw, by omega⟩
  -- `hg₁, hg₂` are not adjacent to `zp`: else `{z, zp, hgᵢ}` is a good triangle of degree sum `10`.
  have hd1 : ¬G.Adj hg1 zp := fun hadj =>
    no_hub_adj_both_mends_eighteen G Hub Iso hdeg4 hiso3 hdisj hHub hIso hdsum hdeg3 hisodeg3 hleak
      hT10 hg1 hg1Hub z hz zp hzpZ hzzp.ne ⟨hzg1.symm, hadj⟩
  have hd2 : ¬G.Adj hg2 zp := fun hadj =>
    no_hub_adj_both_mends_eighteen G Hub Iso hdeg4 hiso3 hdisj hHub hIso hdsum hdeg3 hisodeg3 hleak
      hT10 hg2 hg2Hub z hz zp hzpZ hzzp.ne ⟨hzg2.symm, hadj⟩
  -- The apex-`C₄`-or-good-triangle disjunction.
  rcases mpartner_common_poor_nbr_S14 G Hub Iso hdeg4 hiso3 hdisj hHub hIso hdeg3 hisodeg3 hdsum
      hleak hshare hno2hub hC4 hK23 hT10 hr6 hS14 z zp hg1 hg2 hz hzpZ hzpz hzzp hg1ne hg1mem hg2mem
      hg1poor hg2poor hd1 hd2 hnadj hcodeg0 with happy | htri
  · -- **Apex case.**  Build the good `C₄` `hgᵢ – x – zp – z` and contradict `hC4`.
    obtain ⟨x, hxHub, hxhg1, hxhg2, hzpx, hxadj⟩ := happy
    -- `N(z) ∩ Hub = {hg₁, hg₂}`, so the hub `x ∉ {hg₁, hg₂}` is not adjacent to `z`.
    have hNeq : G.neighborFinset z ∩ Hub = {hg1, hg2} := by
      refine (Finset.eq_of_subset_of_card_le ?_ (le_of_eq ?_)).symm
      · intro y hy
        rcases Finset.mem_insert.mp hy with rfl | hy
        · exact hg1mem
        · rw [Finset.mem_singleton] at hy; subst hy; exact hg2mem
      · rw [Finset.card_insert_of_notMem (by simp [hg1ne]), Finset.card_singleton, hzhub2]
    have hxz_notadj : ¬G.Adj z x := by
      intro hzx
      have hmem : x ∈ G.neighborFinset z ∩ Hub :=
        Finset.mem_inter.mpr ⟨(G.mem_neighborFinset z x).mpr hzx, hxHub⟩
      rw [hNeq, Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with rfl | rfl
      · exact hxhg1 rfl
      · exact hxhg2 rfl
    have hxzp : x ≠ zp := fun he => hzp_notHub (he ▸ hxHub)
    have hxz : x ≠ z := fun he => hz_notHub (he ▸ hxHub)
    have buildC4 : ∀ g : Fin 18, g ∈ Hub → g ≠ x → G.Adj g x → G.Adj z g → ¬G.Adj g zp → False := by
      intro g hgHub hgx hgxadj hzg hdg
      have hgzp : g ≠ zp := fun he => hzp_notHub (he ▸ hgHub)
      have hgz : g ≠ z := fun he => hz_notHub (he ▸ hgHub)
      refine hC4 ⟨g, x, zp, z, ?_, hgxadj, hzpx.symm, hzzp.symm, hzg, hdg,
        fun h => hxz_notadj h.symm, ?_⟩
      · rw [Finset.card_insert_of_notMem (by simp [hgx, hgzp, hgz]),
            Finset.card_insert_of_notMem (by simp [hxzp, hxz]),
            Finset.card_insert_of_notMem (by simp [hzpz]), Finset.card_singleton]
      · rw [hdeg4 g hgHub, hdeg4 x hxHub, hzpdeg3, hzdeg3]
    rcases hxadj with hax | hax
    · exact buildC4 hg1 hg1Hub (fun he => hxhg1 he.symm) hax hzg1 hd1
    · exact buildC4 hg2 hg2Hub (fun he => hxhg2 he.symm) hax hzg2 hd2
  · -- **Good-triangle case.**  The triangle has degree sum `≤ 11`, contradicting `hT`.
    exact hT htri

end N18

end ACMax
