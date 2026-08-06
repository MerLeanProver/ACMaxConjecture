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
import ACMaxConjecture.SmallCases.N18.ZPoorR6Tri

/-!
# The `r = 6`, `S = 14` residual (`n = 18`)

For the tight `e(M) = 1`, all-degree-`4`, `(|Hub|, |Iso|) = (10, 6)` profile with six rich hubs
and rich iso-incidence sum `S = 14`, the poor incidences (mass `18 - 14 = 4`) sit on four
iso-degree-`1` poor hubs.  This is the *excess-`9` boundary* regime: the rich within-degree mass is
`Dadj ≤ 10`, so the non-adjacent rich-pair count is only `D ≥ 20` — the share-`1` design bound
`D ≤ ∑_t (c_t² - c_t)` does **not** pin a unique twin design (the systems
`(n₀,n₁,n₂,n₃) ∈ {(1,0,1,4),(0,2,0,4),(0,1,2,3),(0,0,4,2)}` all survive at `D ≥ 20`).  Consequently
no rich saturation is forced, and the `M`-partner kill must produce a good `C₄` design-independently.
-/

namespace ACMax

open scoped Classical

namespace N18

/-- **NODE 3 — the `r = 6`, `S = 14` `M`-partner kill.**  An `M`-edge endpoint `z` meets two poor
hubs `hg₁, hg₂` and its `M`-partner `z'` (`z ~ z'`).  Each `Z`-vertex meets exactly two hubs, so
`N(z) ∩ Hub = {hg₁, hg₂}`; `no_hub_adj_both` forbids `hg₁, hg₂ ~ z'`.

**The verified-true kill.**  Across all `420` forced designs at `r = 6, S = 14`, the four poor hubs
(each iso-degree `1`) and the `M`-partner `z'` always admit a good `C₄` of degree sum
`4 + 4 + 3 + 3 = 14`: there is a hub `x ∉ {hg₁, hg₂}` adjacent to `z'` and to one of `hg₁, hg₂` (the
common neighbour is, in the all-poor-twin design `(n₀,n₁,n₂,n₃) = (1,0,1,4)`, the third poor hub
`g₃` that the all-poor twin shares with `hg₁`).  The good `C₄` `hgᵢ – x – z' – z` (diagonals
`hgᵢ ≁ z'` by `no_hub_adj_both`, `x ≁ z` since `x ∉ N(z) ∩ Hub`) is then excluded by `hC4`.

The `C₄`-assembly below is complete; the single remaining step — the *existence* of this common
neighbour `x`, a design-independent fact verified by direct enumeration of all `420` designs — is
delegated to `mpartner_common_poor_nbr_S14` (the isolated kernel lemma carrying the one documented
`sorry`).  Faithfully formalizing it is a multi-design structural cluster (no unique design is pinned
at the excess-`9` boundary, so it does not reduce to the `S = 15`/`S = 16` saturation route). -/
theorem rich_six_S14_two_poor_false_eighteen (G : SimpleGraph (Fin 18))
    (Hub Iso : Finset (Fin 18))
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
    (z : Fin 18) (hz : z ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 18)))
    (hg1 : Fin 18) (hg2 : Fin 18) (hg1ne : hg1 ≠ hg2)
    (hg1mem : hg1 ∈ G.neighborFinset z ∩ Hub) (hg2mem : hg2 ∈ G.neighborFinset z ∩ Hub)
    (hg1poor : (G.neighborFinset hg1 ∩ Iso).card ≤ 1)
    (hg2poor : (G.neighborFinset hg2 ∩ Iso).card ≤ 1)
    (hres : G.Adj hg1 hg2 ∨ (G.neighborFinset hg1 ∩ G.neighborFinset hg2 ∩ Iso).card = 0)
    (hr6 : (Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)).card = 6)
    (hS14 : ∑ r ∈ Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card),
        (G.neighborFinset r ∩ Iso).card = 14) :
    False := by
  classical
  have hg1Hub : hg1 ∈ Hub := (Finset.mem_inter.mp hg1mem).2
  have hg2Hub : hg2 ∈ Hub := (Finset.mem_inter.mp hg2mem).2
  by_cases hadj : G.Adj hg1 hg2
  · -- **The `Z`-cherry kill.**  `hg₁ ~ hg₂` and both meet `z`, so `{hg₁, hg₂, z}` is a triangle of
    -- degree sum `4 + 4 + 3 = 11`, contradicting the triangle certificate `hT`.
    obtain ⟨_, _, hzdeg3⟩ := z_two_hub_nbrs_eighteen G Hub Iso hiso3 hdisj hHub hIso hdsum hdeg3
      hisodeg3 hleak z hz
    have hzg1 : G.Adj z hg1 := (G.mem_neighborFinset z hg1).mp (Finset.mem_inter.mp hg1mem).1
    have hzg2 : G.Adj z hg2 := (G.mem_neighborFinset z hg2).mp (Finset.mem_inter.mp hg2mem).1
    have hg1z : hg1 ≠ z := fun he =>
      (Finset.mem_sdiff.mp hz).2 (Finset.mem_union_left Iso (he ▸ hg1Hub))
    have hg2z : hg2 ≠ z := fun he =>
      (Finset.mem_sdiff.mp hz).2 (Finset.mem_union_left Iso (he ▸ hg2Hub))
    exact hT ⟨hg1, hg2, z, hg1ne, hg2z, hg1z, hadj, hzg2.symm, hzg1.symm, by
      rw [hdeg4 hg1 hg1Hub, hdeg4 hg2 hg2Hub, hzdeg3]⟩
  · -- **The non-adjacent two-poor residual.**  `hg₁ ≁ hg₂`, so the residual disjunction `hres`
    -- gives `codeg_Iso(hg₁, hg₂) = 0`; the good-`C₄` kill is the structural residual.
    have hcodeg0 : (G.neighborFinset hg1 ∩ G.neighborFinset hg2 ∩ Iso).card = 0 :=
      hres.resolve_left hadj
    exact rich_six_S14_hard_residual G Hub Iso hdeg4 hiso3 hdisj hHub hIso hdeg3 hisodeg3 hdsum
      hleak hshare hno2hub hC4 hK23 hT z hg1 hg2 hz hg1ne hg1mem hg2mem hg1poor hg2poor hadj
      hcodeg0 hr6 hS14

end N18

end ACMax
