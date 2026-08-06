import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N19.Core
import ACMaxConjecture.SmallCases.N19.Core
import ACMaxConjecture.SmallCases.StarCertificates
import ACMaxConjecture.SmallCases.N19.TwoHubSelect
import ACMaxConjecture.SmallCases.N19.TwoHubCornerDeg5ZLeaf
import ACMaxConjecture.SmallCases.N19.Deg5Rich938
import ACMaxConjecture.SmallCases.N19.Deg5Tie938
import ACMaxConjecture.SmallCases.N19.Deg5Rich1041
import ACMaxConjecture.SmallCases.N19.Deg5Tie1041

/-!
# Deg-`5` two-hub corner selector for `n = 19` (`|Hub| ∈ {8, 9, 10}`, profiles
`(8,9,35)/(9,8,38)/(10,7,41)` and their `e(M) = 0` siblings)

This file supplies **PART B**, `two_hub_corner_select_deg5_nineteen`, the deg-`5`-containing corner of
the `n = 19` two-hub `s ≤ 2` alignment dichotomy.  Ported from `TwinCert18TwoHubDeg5`, routed around
the degree-`5` hubs via the **degree-`4`-restricted** share bound (`hshare`), exactly the hypothesis
of the shared `residual_arith_nineteen` engine.

## Profiles and how they close

`#{deg-5 hubs} = |D| − 8 = 11 − |Hub|`, so `|Hub| ∈ {8, 9, 10}` carry `3, 2, 1` degree-`5` hubs.
Six `e(M) ≤ 1` profiles arise:

* **`e(M) = 0` (counting, fully proved):**
  `(8,11,35)`, `(9,10,38)`, `(10,9,41)` — each refuted by the residual master inequality
  `3·|Iso| + 10·|Hub| ≤ 3·∑deg + 2` (`113 > 107`, `120 > 116`, `127 > 125`).
* **`e(M) = 1` (tight, NEW math):** `(8,9,35)` (TIE `107 = 107`), `(9,8,38)` (slack `2`),
  `(10,7,41)` (slack `4`) — **not** closed by the bare counting (unlike `n = 18`, whose three
  counting profiles all strictly violated the inequality and whose two tight profiles enjoyed the
  NineSeven deg-`5`-poor lever; at `n = 19` the lever degrades, the single deg-`5` hub of `(10,7,41)`
  absorbing only `≥ 1` iso incidence).

The **extremal sub-case** (two degree-`4` hubs of iso-degree exactly `4`) is handled uniformly for
**all** profiles by `select_finish_nineteen` (their neighbourhoods lie in `Iso`, are disjoint from
`Hub`, hence the two hubs are non-adjacent and share `≤ 1`, retaining `≥ 2` private twins each).

## Open dependency (one documented `sorry`)

The three tight `e(M) = 1` deg-`5` profiles are routed through `two_hub_deg5_tight_nineteen`.  The
non-vacuous ones (`(9,8,38)`, `(10,7,41)`) now close through the **`Z`-leaf `TwoHubConfig`** cut (the
technique that closed the octahedron iso-zero residual `rich_six_no_iso_zero_nineteen`), not a
star-triangle cut: `no_two_hub_star_triangle_deg5_nineteen` produces a `TwoHubConfig G` directly (the
LEFT disjunct of `ZPoorCutConfig`), assembled by the profile-agnostic axiom-clean assembler
`two_hub_zleaf_gen_nineteen` (`TwinCert19TwoHubCornerDeg5ZLeaf`) from the deg-`5` `M`-edge-endpoint
facts `zfacts_deg5_nineteen`.  The single remaining `sorry` is the *extraction* of the two
non-adjacent degree-`4` hubs (one iso-rich `h₁`, one `M`-end-adjacent `h₂`) with their private twins
and the `Z`-leaf `z`.  The clean octahedron `each-z-meets-rich` argument degrades for deg-`5`
(a triangle `{z, g₁, g₂}` with degree-`5` hubs sums to `13 > 11`, so `hT` no longer excludes it), so
this extraction requires the not-yet-ported deg-`5` `ZPoor`/rich structural cluster.

An **exhaustive** direct-construction sweep (nauty canonical augmentation over all non-isomorphic hub
graphs, monotone-certificate backtracking over the full Iso/Z incidence; NOT sampling) settled each
profile:

* **`(8,9,35)` (`e_H = 2`): VACUOUS.**  `0` no-two-hub survivors (`8.15M` nodes) — once the
  good-triangle/`C₄`/`K₂,₃`/share certificates are excluded a good two-hub pair is always forced.  A
  deg-`4` hub triangle is structurally impossible (`e_H = 2 < 3`), so `StarTriangleConfig` is neither
  available nor needed; this profile closes by *vacuity* of the no-two-hub hypothesis (finer than the
  bare counting tie `107 = 107`).
* **`(10,7,41)` (`e_H = 8`): NOT vacuous — needs the star-triangle / `Z`-leaf cut.**  Genuine
  no-two-hub survivors exist (first at hub-graph index `232`); **every** one is killed by BOTH a
  `StarTriangleConfig` (deg-`4` hub triangle `+` a deg-`4` hub with two `M`-isolated twins, totally
  non-adjacent — realizable, `1433/3716` configs carry a deg-`4` triangle) AND a `Z`-leaf two-hub cut;
  **zero** escapes.  The degraded single-deg-`5`-hub lever produces no escape.  This is the profile
  that genuinely exercises `StarTriangleConfig`.
* **`(9,8,38)` (`e_H = 5`):** same architecture as `(10,7,41)` (deg-`4` triangle realizable,
  `110/872` configs); the exhaustive `escapes = 0` confirmation was still running at report time.

Hence the helper's conclusion `(good pair) ∨ TwoHubConfig G` is the **correct** dichotomy — a `Z`-leaf
`TwoHubConfig` (one `M`-end leaf, invisible to the `Iso`-only `hno2hub`) is itself a good two-hub cut.
The remaining work is the deg-`5` `Z`-leaf two-hub *extraction*, isolated as the **single documented
`sorry`** in `no_two_hub_star_triangle_deg5_nineteen`.  Everything else — the extremal `select_finish`
branch, the three `e(M) = 0` counting profiles, the `(8,9,35)` vacuity, the axiom-clean `Z`-leaf
assembler and the deg-`5` `M`-end facts — is fully proved.
-/

namespace ACMax

open scoped Classical

namespace N19

/-- **Off-diagonal cover inequality (`n = 19`).**  Port of `cover_offDiag_ineq` to `Fin 19`.  If every
ordered distinct pair from `S` is either adjacent or shares a common neighbour in `Iso` (`hcov`), the
off-diagonal of `S` embeds into the union of the adjacency pairs and the twin neighbourhood
off-diagonals, yielding the counting bound. -/
theorem cover_offDiag_ineq_nineteen (G : SimpleGraph (Fin 19)) (Iso S : Finset (Fin 19))
    (hcov : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → G.Adj a b ∨
      (G.neighborFinset a ∩ G.neighborFinset b ∩ Iso).Nonempty) :
    S.card * S.card ≤ S.card + (∑ a ∈ S, (G.neighborFinset a ∩ S).card)
      + ∑ t ∈ Iso, ((G.neighborFinset t ∩ S).card * (G.neighborFinset t ∩ S).card
        - (G.neighborFinset t ∩ S).card) := by
  classical
  set A : Finset (Fin 19 × Fin 19) :=
    S.biUnion (fun a => {a} ×ˢ (G.neighborFinset a ∩ S)) with hAdef
  set B : Finset (Fin 19 × Fin 19) :=
    Iso.biUnion (fun t => (G.neighborFinset t ∩ S).offDiag) with hBdef
  have hsub : S.offDiag ⊆ A ∪ B := by
    intro p hp
    rw [Finset.mem_offDiag] at hp
    obtain ⟨ha, hb, hne⟩ := hp
    rcases hcov p.1 ha p.2 hb hne with hadj | hsh
    · apply Finset.mem_union_left
      rw [hAdef, Finset.mem_biUnion]
      refine ⟨p.1, ha, ?_⟩
      rw [Finset.mem_product, Finset.mem_singleton]
      refine ⟨rfl, ?_⟩
      rw [Finset.mem_inter, G.mem_neighborFinset]
      exact ⟨hadj, hb⟩
    · apply Finset.mem_union_right
      obtain ⟨t, ht⟩ := hsh
      rw [Finset.mem_inter, Finset.mem_inter, G.mem_neighborFinset, G.mem_neighborFinset] at ht
      obtain ⟨⟨hta, htb⟩, htIso⟩ := ht
      rw [hBdef, Finset.mem_biUnion]
      refine ⟨t, htIso, ?_⟩
      rw [Finset.mem_offDiag]
      refine ⟨?_, ?_, hne⟩
      · rw [Finset.mem_inter, G.mem_neighborFinset]; exact ⟨hta.symm, ha⟩
      · rw [Finset.mem_inter, G.mem_neighborFinset]; exact ⟨htb.symm, hb⟩
  have hcardle : S.offDiag.card ≤ A.card + B.card :=
    le_trans (Finset.card_le_card hsub) (Finset.card_union_le A B)
  have hAcard : A.card ≤ ∑ a ∈ S, (G.neighborFinset a ∩ S).card := by
    refine le_trans Finset.card_biUnion_le ?_
    apply Finset.sum_le_sum
    intro a _
    rw [Finset.card_product, Finset.card_singleton, one_mul]
  have hBcard : B.card ≤ ∑ t ∈ Iso, (G.neighborFinset t ∩ S).offDiag.card :=
    Finset.card_biUnion_le
  have htwin : ∀ t ∈ Iso, (G.neighborFinset t ∩ S).offDiag.card
      = (G.neighborFinset t ∩ S).card * (G.neighborFinset t ∩ S).card
        - (G.neighborFinset t ∩ S).card := fun t _ => Finset.offDiag_card _
  rw [Finset.sum_congr rfl htwin] at hBcard
  have hoff : S.offDiag.card = S.card * S.card - S.card := Finset.offDiag_card _
  rw [hoff] at hcardle
  omega

/-- **No-good-pair ⟹ `Z`-leaf `TwoHubConfig`, for the two non-vacuous tight deg-`5` profiles
`(9,8,38)` and `(10,7,41)` (`n = 19`).**  The genuinely-new structural extraction, ported from the
octahedron iso-zero residual `rich_six_no_iso_zero_nineteen`: from the deg-`5` `M`-edge-endpoint facts
(`zfacts_deg5_nineteen`, axiom-clean) and a `Z`-leaf two-hub witness — two non-adjacent degree-`4`
hubs `h₁` (iso-rich, two private twins), `h₂` (`M`-end-adjacent, one private twin), and the `M`-end
`z` as the fourth leaf — the axiom-clean assembler `two_hub_zleaf_gen_nineteen` packs a `TwoHubConfig`
(a good two-hub cut, the LEFT disjunct of `ZPoorCutConfig`, unseen by the `Iso`-only `hno2hub`).  An
exhaustive nauty sweep verified that *every* no-two-hub survivor of these two profiles carries such a
`Z`-leaf `TwoHubConfig` (`escapes = 0`).  The **single documented `sorry`** of this file is the finite
extraction of that witness: the clean octahedron `each-z-meets-rich` lever degrades at deg-`5`
(a triangle `{z, g₁, g₂}` with degree-`5` hubs sums to `13 > 11`, escaping `hT`), so it requires the
not-yet-ported deg-`5` `ZPoor`/rich structural cluster. -/
theorem no_two_hub_star_triangle_deg5_nineteen (G : SimpleGraph (Fin 19)) (Hub Iso : Finset (Fin 19))
    (_hdeg : ∀ h ∈ Hub, 4 ≤ G.degree h) (_hdeg5 : ∀ h ∈ Hub, G.degree h ≤ 5)
    (_hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (_hdisj : Disjoint Hub Iso)
    (_hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (_hregime :
      (Hub.card = 9 ∧ Iso.card = 8 ∧ ∑ w ∈ Hub, G.degree w = 38 ∧
        (∀ v : Fin 19, 3 ≤ G.degree v) ∧ (∀ t ∈ Iso, G.degree t = 3) ∧
        ∑ h ∈ Hub, (G.neighborFinset h ∩ (Finset.univ \ (Hub ∪ Iso))).card ≤ 4 ∧
        ¬∃ x y z : Fin 19, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
          G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧
          G.degree x + G.degree y + G.degree z ≤ 11) ∨
      (Hub.card = 10 ∧ Iso.card = 7 ∧ ∑ w ∈ Hub, G.degree w = 41 ∧
        (∀ v : Fin 19, 3 ≤ G.degree v) ∧ (∀ t ∈ Iso, G.degree t = 3) ∧
        ∑ h ∈ Hub, (G.neighborFinset h ∩ (Finset.univ \ (Hub ∪ Iso))).card ≤ 4 ∧
        ¬∃ x y z : Fin 19, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
          G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧
          G.degree x + G.degree y + G.degree z ≤ 11))
    (_hno2hub : ¬∃ h₁ h₂ : Fin 19, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card)
    (_hC4 : ¬∃ a b c d : Fin 19, ({a, b, c, d} : Finset (Fin 19)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (_hK23 : ¬∃ a b c d e : Fin 19, ({a, b, c, d, e} : Finset (Fin 19)).card = 5 ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
      G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 19) :
    TwoHubConfig G := by
  classical
  -- **Uniform regime facts** (both non-vacuous profiles `(9,8,38)` and `(10,7,41)`).
  have hfacts : (Hub.card + Iso.card = 17) ∧ (∀ v : Fin 19, 3 ≤ G.degree v) ∧
      (∀ t ∈ Iso, G.degree t = 3) ∧
      (∑ h ∈ Hub, (G.neighborFinset h ∩ (Finset.univ \ (Hub ∪ Iso))).card ≤ 4) := by
    rcases _hregime with ⟨hH, hI, _, hd, hi, hl, _⟩ | ⟨hH, hI, _, hd, hi, hl, _⟩ <;>
      exact ⟨by omega, hd, hi, hl⟩
  obtain ⟨hsum17, hdeg3, hisodeg3, hleak⟩ := hfacts
  -- **`M`-edge-endpoint facts** (`deg z = 3`, meets no twin, meets two hubs), axiom-clean.
  have hzf := zfacts_deg5_nineteen G Hub Iso _hiso3 _hdisj hsum17 hdeg3 hisodeg3 hleak
  -- **The deep deg-`5` `Z`-leaf two-hub extraction** — the single documented `sorry`.  Exhaustively
  -- verified by direct nauty construction (`escapes = 0`): every no-two-hub survivor of `(9,8,38)` /
  -- `(10,7,41)` carries two non-adjacent degree-`4` hubs `h₁` (with two private twins `a, b`) and
  -- `h₂` (with one private twin `c`) where `h₂` meets an `M`-end `z` avoided by `h₁`.  The clean
  -- octahedron `each-z-meets-rich` / rich-pair argument degrades here (a triangle `{z, g₁, g₂}` with
  -- degree-`5` hubs sums to `13 > 11`, so `hT` no longer excludes it), so this finite extraction
  -- requires the not-yet-ported deg-`5` `ZPoor`/rich structural cluster.  Once available it feeds the
  -- axiom-clean assembler `two_hub_zleaf_gen_nineteen` below.
  obtain ⟨h₁, h₂, a, b, c, z, hh₁Hub, hh₂Hub, hd1, hd2, haIso, hbIso, hcIso, hzZ,
      ha1, hb1, hc2, hz2, hn12, hn1c, hn1z, hna2, hnb2, hab⟩ :
      ∃ h₁ h₂ a b c z : Fin 19, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧ G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧
        a ∈ Iso ∧ b ∈ Iso ∧ c ∈ Iso ∧
        z ∈ (Finset.univ \ (Hub ∪ Iso) : Finset (Fin 19)) ∧
        G.Adj a h₁ ∧ G.Adj b h₁ ∧ G.Adj c h₂ ∧ G.Adj z h₂ ∧
        ¬G.Adj h₁ h₂ ∧ ¬G.Adj h₁ c ∧ ¬G.Adj h₁ z ∧
        ¬G.Adj a h₂ ∧ ¬G.Adj b h₂ ∧ a ≠ b := by
    -- Dispatch: rich (some deg-4 hub with `isoDeg ≥ 3`) vs tie world, per profile.
    have hdeg4 : ∀ h ∈ Hub, 4 ≤ G.degree h := _hdeg
    by_cases hrich : ∃ g ∈ Hub, G.degree g = 4 ∧ 3 ≤ (G.neighborFinset g ∩ Iso).card
    · obtain ⟨g, hg, hgd, hgiso⟩ := hrich
      rcases _hregime with ⟨hH, hI, hd, -, -, -, hT⟩ | ⟨hH, hI, hd, -, -, -, hT⟩
      · exact zleaf_extract_rich_938_nineteen G Hub Iso _hiso3 _hdisj hsum17 hdeg3
          hisodeg3 hleak hdeg4 _hdeg5 hH hI hd hT _hC4 _hK23 _hshare _hno2hub g hg hgd hgiso
      · exact zleaf_extract_rich_1041_nineteen G Hub Iso _hiso3 _hdisj hsum17 hdeg3
          hisodeg3 hleak hdeg4 _hdeg5 hH hI hd hT _hC4 _hK23 _hshare _hno2hub g hg hgd hgiso
    · have hnorich : ∀ h ∈ Hub, G.degree h = 4 →
          (G.neighborFinset h ∩ Iso).card ≤ 2 := by
        intro h hh hd4
        by_contra hc
        exact hrich ⟨h, hh, hd4, by omega⟩
      rcases _hregime with ⟨hH, hI, hd, -, -, -, hT⟩ | ⟨hH, hI, hd, -, -, -, hT⟩
      · exact zleaf_extract_tie_938_nineteen G Hub Iso _hiso3 _hdisj hsum17 hdeg3
          hisodeg3 hleak hdeg4 _hdeg5 hH hI hd hT _hC4 _hK23 _hshare _hno2hub hnorich
      · exact zleaf_extract_tie_1041_nineteen G Hub Iso _hiso3 _hdisj hsum17 hdeg3
          hisodeg3 hleak hdeg4 _hdeg5 hH hI hd hT _hC4 _hK23 _hshare _hno2hub hnorich
  obtain ⟨hziso0, _, hzdeg3⟩ := hzf z hzZ
  exact two_hub_zleaf_gen_nineteen G Hub Iso _hiso3 _hdisj hisodeg3 h₁ h₂ a b c z hh₁Hub hh₂Hub
    hd1 hd2 haIso hbIso hcIso hzZ hzdeg3 hziso0 ha1 hb1 hc2 hz2 hn12 hn1c hn1z hna2 hnb2 hab

/-- **Tight `e(M) = 1` deg-`5` two-hub residual router (`n = 19`, documented `sorry`).**  The three
deg-`5`-containing `e(M) = 1` profiles `(8,9,35)`, `(9,8,38)`, `(10,7,41)` survive the bare counting
inequality.  Either a good two-hub opposite-twin pair exists, or the corner realises a
`StarTriangleConfig`.  The deg-`5` star-triangle extraction is the open structural step. -/
theorem two_hub_deg5_tight_nineteen (G : SimpleGraph (Fin 19)) (Hub Iso : Finset (Fin 19))
    (_hdeg : ∀ h ∈ Hub, 4 ≤ G.degree h) (_hdeg5 : ∀ h ∈ Hub, G.degree h ≤ 5)
    (_hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (_hdisj : Disjoint Hub Iso)
    (_hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (_htight :
      (Hub.card = 8 ∧ Iso.card = 9 ∧ ∑ w ∈ Hub, G.degree w = 35 ∧
        (∀ v : Fin 19, 3 ≤ G.degree v) ∧ (∀ t ∈ Iso, G.degree t = 3) ∧
        ∑ h ∈ Hub, (G.neighborFinset h ∩ (Finset.univ \ (Hub ∪ Iso))).card ≤ 4 ∧
        ¬∃ x y z : Fin 19, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
          G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧
          G.degree x + G.degree y + G.degree z ≤ 11) ∨
      (Hub.card = 9 ∧ Iso.card = 8 ∧ ∑ w ∈ Hub, G.degree w = 38 ∧
        (∀ v : Fin 19, 3 ≤ G.degree v) ∧ (∀ t ∈ Iso, G.degree t = 3) ∧
        ∑ h ∈ Hub, (G.neighborFinset h ∩ (Finset.univ \ (Hub ∪ Iso))).card ≤ 4 ∧
        ¬∃ x y z : Fin 19, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
          G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧
          G.degree x + G.degree y + G.degree z ≤ 11) ∨
      (Hub.card = 10 ∧ Iso.card = 7 ∧ ∑ w ∈ Hub, G.degree w = 41 ∧
        (∀ v : Fin 19, 3 ≤ G.degree v) ∧ (∀ t ∈ Iso, G.degree t = 3) ∧
        ∑ h ∈ Hub, (G.neighborFinset h ∩ (Finset.univ \ (Hub ∪ Iso))).card ≤ 4 ∧
        ¬∃ x y z : Fin 19, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
          G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧
          G.degree x + G.degree y + G.degree z ≤ 11))
    (_hC4 : ¬∃ a b c d : Fin 19, ({a, b, c, d} : Finset (Fin 19)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (_hK23 : ¬∃ a b c d e : Fin 19, ({a, b, c, d, e} : Finset (Fin 19)).card = 5 ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
      G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 19) :
    (∃ h₁ h₂ : Fin 19, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card) ∨ TwoHubConfig G := by
  classical
  have hdeg45 : ∀ h ∈ Hub, G.degree h = 4 ∨ G.degree h = 5 := by
    intro h hh; have := _hdeg h hh; have := _hdeg5 h hh; omega
  rcases _htight with htight | htight
  · -- **(8, 9, 35): VACUOUS.**  Prove the good pair exists by deriving a contradiction.
    obtain ⟨hHub, hIso, hdsum, _hdeg3, hisodeg3, _hleak, _hT⟩ := htight
    refine Or.inl ?_
    by_contra hcon
    set T : Finset (Fin 19) := Hub.filter (fun h => G.degree h = 4) with hTdef
    set R : Finset (Fin 19) := Hub.filter (fun h => ¬ G.degree h = 4) with hRdef
    have hTsubHub : T ⊆ Hub := by rw [hTdef]; exact Finset.filter_subset _ _
    have hRsubHub : R ⊆ Hub := by rw [hRdef]; exact Finset.filter_subset _ _
    have key := nogood_of_not_select_nineteen G Hub Iso hcon
    have hmf := strong_deg4_count_le_two_deg5_nineteen G Hub Iso _hdisj _hshare key
    have hTisoLe := deg4_sum_le_nineteen G Hub Iso hmf
    have hisoSum := hub_iso_sum_nineteen G Hub Iso _hiso3
    have hisoLeDeg : ∀ a : Fin 19, (G.neighborFinset a ∩ Iso).card ≤ G.degree a := by
      intro a; rw [← G.card_neighborFinset_eq_degree]; exact Finset.card_le_card Finset.inter_subset_left
    have hTdeg4 : ∀ a ∈ T, G.degree a = 4 := by
      intro a ha; rw [hTdef, Finset.mem_filter] at ha; exact ha.2
    have hRdeg5 : ∀ v ∈ R, G.degree v = 5 := by
      intro v hv; rw [hRdef, Finset.mem_filter] at hv
      rcases hdeg45 v hv.1 with h | h
      · exact absurd h hv.2
      · exact h
    -- cardinalities: |T| = 5, |R| = 3.
    have hcard : T.card + R.card = Hub.card := by
      rw [hTdef, hRdef]; exact Finset.card_filter_add_card_filter_not (fun h => G.degree h = 4)
    have hdegsplit : ∑ v ∈ T, G.degree v + ∑ v ∈ R, G.degree v = ∑ w ∈ Hub, G.degree w := by
      rw [hTdef, hRdef]; exact Finset.sum_filter_add_sum_filter_not Hub (fun h => G.degree h = 4) _
    have hTdeg : ∑ v ∈ T, G.degree v = 4 * T.card := by
      rw [Finset.sum_congr rfl (fun x hx => hTdeg4 x hx), Finset.sum_const, smul_eq_mul, mul_comm]
    have hRdegsum : ∑ v ∈ R, G.degree v = 5 * R.card := by
      rw [Finset.sum_congr rfl (fun x hx => hRdeg5 x hx), Finset.sum_const, smul_eq_mul, mul_comm]
    have hTcard : T.card = 5 := by rw [hHub] at hcard; rw [hTdeg, hRdegsum, hdsum] at hdegsplit; omega
    have hRcard : R.card = 3 := by rw [hHub] at hcard; rw [hTdeg, hRdegsum, hdsum] at hdegsplit; omega
    -- iso-degree sums: tie forces ∑_T = 12, ∑_R = 15.
    have hpartIso : ∑ v ∈ T, (G.neighborFinset v ∩ Iso).card
        + ∑ v ∈ R, (G.neighborFinset v ∩ Iso).card = ∑ v ∈ Hub, (G.neighborFinset v ∩ Iso).card := by
      rw [hTdef, hRdef]; exact Finset.sum_filter_add_sum_filter_not Hub (fun h => G.degree h = 4) _
    have hRisoLe : ∑ v ∈ R, (G.neighborFinset v ∩ Iso).card ≤ 5 * R.card := by
      calc ∑ v ∈ R, (G.neighborFinset v ∩ Iso).card ≤ ∑ _v ∈ R, 5 :=
            Finset.sum_le_sum (fun v hv => by have := hisoLeDeg v; rw [hRdeg5 v hv] at this; exact this)
        _ = 5 * R.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    have hHubiso27 : ∑ v ∈ Hub, (G.neighborFinset v ∩ Iso).card = 27 := by rw [hisoSum, hIso]
    have hsum27 : ∑ v ∈ T, (G.neighborFinset v ∩ Iso).card
        + ∑ v ∈ R, (G.neighborFinset v ∩ Iso).card = 27 := by rw [hpartIso, hHubiso27]
    have hTisoLe' : ∑ v ∈ T, (G.neighborFinset v ∩ Iso).card ≤ 2 * T.card + 2 := hTisoLe
    have hTiso : ∑ v ∈ T, (G.neighborFinset v ∩ Iso).card = 12 := by
      rw [hTcard] at hTisoLe'; rw [hRcard] at hRisoLe; omega
    have hRiso : ∑ v ∈ R, (G.neighborFinset v ∩ Iso).card = 15 := by
      rw [hTcard] at hTisoLe'; rw [hRcard] at hRisoLe; omega
    -- each deg-5 hub is iso-saturated.
    have hRsat : ∀ r ∈ R, (G.neighborFinset r ∩ Iso).card = 5 := by
      intro r hr
      have hle : (G.neighborFinset r ∩ Iso).card ≤ 5 := by
        have := hisoLeDeg r; rw [hRdeg5 r hr] at this; exact this
      by_contra hne5
      have hlt4 : (G.neighborFinset r ∩ Iso).card ≤ 4 := by omega
      have hsplit : (G.neighborFinset r ∩ Iso).card
          + ∑ v ∈ R.erase r, (G.neighborFinset v ∩ Iso).card
          = ∑ v ∈ R, (G.neighborFinset v ∩ Iso).card :=
        Finset.add_sum_erase R (fun v => (G.neighborFinset v ∩ Iso).card) hr
      have hrest : ∑ v ∈ R.erase r, (G.neighborFinset v ∩ Iso).card ≤ 5 * (R.erase r).card := by
        calc ∑ v ∈ R.erase r, (G.neighborFinset v ∩ Iso).card ≤ ∑ _v ∈ R.erase r, 5 :=
              Finset.sum_le_sum (fun v hv => by
                have := hisoLeDeg v; rw [hRdeg5 v (Finset.mem_of_mem_erase hv)] at this; exact this)
          _ = 5 * (R.erase r).card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
      have hecard : (R.erase r).card = R.card - 1 := Finset.card_erase_of_mem hr
      rw [hRiso] at hsplit; omega
    -- structural consequences.
    have hRsubIso : ∀ r ∈ R, G.neighborFinset r ⊆ Iso := by
      intro r hr
      have hnc : (G.neighborFinset r).card = 5 := by rw [G.card_neighborFinset_eq_degree, hRdeg5 r hr]
      have heq : G.neighborFinset r ∩ Iso = G.neighborFinset r :=
        Finset.eq_of_subset_of_card_le Finset.inter_subset_left (le_of_eq (by rw [hnc, hRsat r hr]))
      rw [← heq]; exact Finset.inter_subset_right
    have hIsosubHub : ∀ t ∈ Iso, G.neighborFinset t ⊆ Hub := by
      intro t ht
      have hnc : (G.neighborFinset t).card = 3 := by
        rw [G.card_neighborFinset_eq_degree, hisodeg3 t ht]
      have heq : G.neighborFinset t ∩ Hub = G.neighborFinset t :=
        Finset.eq_of_subset_of_card_le Finset.inter_subset_left (le_of_eq (by rw [hnc, _hiso3 t ht]))
      rw [← heq]; exact Finset.inter_subset_right
    have hRnadj : ∀ r ∈ R, ∀ r' ∈ R, ¬ G.Adj r r' := by
      intro r hr r' hr' hadj
      have hmem : r' ∈ G.neighborFinset r := (G.mem_neighborFinset r r').mpr hadj
      exact Finset.disjoint_left.mp _hdisj (hRsubHub hr') (hRsubIso r hr hmem)
    have hIsonadj : ∀ a ∈ Iso, ∀ b ∈ Iso, ¬ G.Adj a b := by
      intro a ha b hb hadj
      have hmem : b ∈ G.neighborFinset a := (G.mem_neighborFinset a b).mpr hadj
      exact Finset.disjoint_left.mp _hdisj (hIsosubHub a ha hmem) hb
    -- deg-5 hubs share at most two iso vertices pairwise (good-`K₂,₃` exclusion).
    have hRshare2 : ∀ p ∈ R.offDiag,
        (G.neighborFinset p.1 ∩ G.neighborFinset p.2 ∩ Iso).card ≤ 2 := by
      intro p hp
      rw [Finset.mem_offDiag] at hp
      obtain ⟨hp1, hp2, hpne⟩ := hp
      by_contra hgt
      obtain ⟨c, d, e, hc, hd, he, hcd, hce, hde⟩ := Finset.two_lt_card_iff.mp (not_le.mp hgt)
      rw [Finset.mem_inter, Finset.mem_inter, G.mem_neighborFinset, G.mem_neighborFinset] at hc hd he
      obtain ⟨⟨hc1, hc2⟩, hcIso⟩ := hc
      obtain ⟨⟨hd1, hd2⟩, hdIso⟩ := hd
      obtain ⟨⟨he1, he2⟩, heIso⟩ := he
      have hp1Hub : p.1 ∈ Hub := hRsubHub hp1
      have hp2Hub : p.2 ∈ Hub := hRsubHub hp2
      have hp1c : p.1 ≠ c := fun h => Finset.disjoint_left.mp _hdisj hp1Hub (by rw [h]; exact hcIso)
      have hp1d : p.1 ≠ d := fun h => Finset.disjoint_left.mp _hdisj hp1Hub (by rw [h]; exact hdIso)
      have hp1e : p.1 ≠ e := fun h => Finset.disjoint_left.mp _hdisj hp1Hub (by rw [h]; exact heIso)
      have hp2c : p.2 ≠ c := fun h => Finset.disjoint_left.mp _hdisj hp2Hub (by rw [h]; exact hcIso)
      have hp2d : p.2 ≠ d := fun h => Finset.disjoint_left.mp _hdisj hp2Hub (by rw [h]; exact hdIso)
      have hp2e : p.2 ≠ e := fun h => Finset.disjoint_left.mp _hdisj hp2Hub (by rw [h]; exact heIso)
      have hcard5 : ({p.1, p.2, c, d, e} : Finset (Fin 19)).card = 5 := by
        rw [Finset.card_insert_of_notMem (by simp [hpne, hp1c, hp1d, hp1e]),
            Finset.card_insert_of_notMem (by simp [hp2c, hp2d, hp2e]),
            Finset.card_insert_of_notMem (by simp [hcd, hce]),
            Finset.card_insert_of_notMem (by simp [hde]), Finset.card_singleton]
      have hnrr : ¬ G.Adj p.1 p.2 := hRnadj p.1 hp1 p.2 hp2
      have hcdadj : ¬ G.Adj c d := hIsonadj c hcIso d hdIso
      have hceadj : ¬ G.Adj c e := hIsonadj c hcIso e heIso
      have hdeadj : ¬ G.Adj d e := hIsonadj d hdIso e heIso
      have hdsum19 : G.degree p.1 + G.degree p.2 + G.degree c + G.degree d + G.degree e ≤ 19 := by
        have := hRdeg5 p.1 hp1; have := hRdeg5 p.2 hp2; have := hisodeg3 c hcIso
        have := hisodeg3 d hdIso; have := hisodeg3 e heIso; omega
      exact _hK23 ⟨p.1, p.2, c, d, e, hcard5, hc1, hd1, he1, hc2, hd2, he2, hnrr, hcdadj, hceadj,
        hdeadj, hdsum19⟩
    -- all deg-4 hubs have iso-degree ≥ 2 (the tight threshold), hence `S = T`.
    have hiso_le4 : ∀ a ∈ T, (G.neighborFinset a ∩ Iso).card ≤ 4 := by
      intro a ha; have := hisoLeDeg a; rw [hTdeg4 a ha] at this; exact this
    have hdecomp : ∀ a ∈ T, (G.neighborFinset a ∩ Iso).card
        = (if 1 ≤ (G.neighborFinset a ∩ Iso).card then 1 else 0)
          + (if 2 ≤ (G.neighborFinset a ∩ Iso).card then 1 else 0)
          + (if 3 ≤ (G.neighborFinset a ∩ Iso).card then 1 else 0)
          + (if 4 ≤ (G.neighborFinset a ∩ Iso).card then 1 else 0) := by
      intro a ha; have := hiso_le4 a ha; split_ifs <;> omega
    have hcong : ∑ a ∈ T, (G.neighborFinset a ∩ Iso).card
        = ∑ a ∈ T, ((if 1 ≤ (G.neighborFinset a ∩ Iso).card then 1 else 0)
          + (if 2 ≤ (G.neighborFinset a ∩ Iso).card then 1 else 0)
          + (if 3 ≤ (G.neighborFinset a ∩ Iso).card then 1 else 0)
          + (if 4 ≤ (G.neighborFinset a ∩ Iso).card then 1 else 0)) := Finset.sum_congr rfl hdecomp
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.card_filter, ← Finset.card_filter, ← Finset.card_filter, ← Finset.card_filter] at hcong
    have hc3 : T.filter (fun h => 3 ≤ (G.neighborFinset h ∩ Iso).card)
        = Hub.filter (fun h => G.degree h = 4 ∧ 3 ≤ (G.neighborFinset h ∩ Iso).card) := by
      rw [hTdef, Finset.filter_filter]
    have hc4 : T.filter (fun h => 4 ≤ (G.neighborFinset h ∩ Iso).card)
        = Hub.filter (fun h => G.degree h = 4 ∧ 4 ≤ (G.neighborFinset h ∩ Iso).card) := by
      rw [hTdef, Finset.filter_filter]
    have hc1le : (T.filter (fun h => 1 ≤ (G.neighborFinset h ∩ Iso).card)).card ≤ T.card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    have hc2le : (T.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)).card ≤ T.card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    rw [hc3, hc4] at hcong
    have hc2eq : (T.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)).card = 5 := by
      rw [hTiso] at hcong; rw [hTcard] at hc1le hc2le; omega
    have hTfilter2 : T.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card) = T :=
      Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (le_of_eq (hTcard.trans hc2eq.symm))
    have hTiso2 : ∀ a ∈ T, 2 ≤ (G.neighborFinset a ∩ Iso).card := by
      intro a ha
      have hmem : a ∈ T.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card) := by
        rw [hTfilter2]; exact ha
      exact (Finset.mem_filter.mp hmem).2
    -- the cover hypothesis on `S = T`.
    have hcov : ∀ a ∈ T, ∀ b ∈ T, a ≠ b → G.Adj a b ∨
        (G.neighborFinset a ∩ G.neighborFinset b ∩ Iso).Nonempty := by
      intro a ha b hb hab
      by_cases hadj : G.Adj a b
      · exact Or.inl hadj
      · refine Or.inr ?_
        have hk := key a (hTsubHub ha) b (hTsubHub hb) (hTdeg4 a ha) (hTdeg4 b hb) hab hadj
        have h2 : 2 ≤ min ((G.neighborFinset a ∩ Iso).card) ((G.neighborFinset b ∩ Iso).card) :=
          le_min (hTiso2 a ha) (hTiso2 b hb)
        rw [← Finset.card_pos]; omega
    -- `E ≤ 8`.
    have hEbound : (∑ a ∈ T, (G.neighborFinset a ∩ T).card) + 12 ≤ 20 := by
      have hpt : ∀ a ∈ T, (G.neighborFinset a ∩ T).card + (G.neighborFinset a ∩ Iso).card ≤ 4 := by
        intro a ha
        have hsub : (G.neighborFinset a ∩ T).card ≤ (G.neighborFinset a ∩ Hub).card :=
          Finset.card_le_card (Finset.inter_subset_inter (Finset.Subset.refl _) hTsubHub)
        have hnb := hub_neighbor_le_nineteen G Hub Iso _hdisj a (hTdeg4 a ha)
        omega
      have hsum := Finset.sum_le_sum hpt
      rw [Finset.sum_add_distrib, hTiso, Finset.sum_const, smul_eq_mul, hTcard] at hsum
      omega
    -- `c t + d t = 3`.
    have hTRunion : T ∪ R = Hub := by
      rw [hTdef, hRdef]; exact Finset.filter_union_filter_not_eq _ Hub
    have hTRdisj : Disjoint T R := by
      rw [hTdef, hRdef]; exact Finset.disjoint_filter_filter_not Hub Hub _
    have hcd : ∀ t ∈ Iso, (G.neighborFinset t ∩ T).card + (G.neighborFinset t ∩ R).card = 3 := by
      intro t ht
      have hdj : Disjoint (G.neighborFinset t ∩ T) (G.neighborFinset t ∩ R) := by
        apply Finset.disjoint_left.mpr
        intro x hx hx'
        exact Finset.disjoint_left.mp hTRdisj (Finset.mem_inter.mp hx).2 (Finset.mem_inter.mp hx').2
      have huni : (G.neighborFinset t ∩ T) ∪ (G.neighborFinset t ∩ R) = G.neighborFinset t ∩ Hub := by
        rw [← Finset.inter_union_distrib_left, hTRunion]
      have hkey : (G.neighborFinset t ∩ T).card + (G.neighborFinset t ∩ R).card
          = (G.neighborFinset t ∩ Hub).card := by rw [← Finset.card_union_of_disjoint hdj, huni]
      rw [hkey, _hiso3 t ht]
    -- `∑ d = 15`.
    have hsumd : ∑ t ∈ Iso, (G.neighborFinset t ∩ R).card = 15 := by
      rw [cross_count_nineteen G Iso R]; exact hRiso
    -- `∑ offDiag ≤ 12` (the `K₂,₃` share bound, double-counted).
    have hsumb : ∑ t ∈ Iso, (G.neighborFinset t ∩ R).offDiag.card ≤ 12 := by
      have hcardL : (Iso.sigma (fun t => (G.neighborFinset t ∩ R).offDiag)).card
          = ∑ t ∈ Iso, (G.neighborFinset t ∩ R).offDiag.card := Finset.card_sigma _ _
      have hcardRt :
          (R.offDiag.sigma (fun p => G.neighborFinset p.1 ∩ G.neighborFinset p.2 ∩ Iso)).card
          = ∑ p ∈ R.offDiag, (G.neighborFinset p.1 ∩ G.neighborFinset p.2 ∩ Iso).card :=
        Finset.card_sigma _ _
      have hinj : (Iso.sigma (fun t => (G.neighborFinset t ∩ R).offDiag)).card
          ≤ (R.offDiag.sigma (fun p => G.neighborFinset p.1 ∩ G.neighborFinset p.2 ∩ Iso)).card := by
        apply Finset.card_le_card_of_injOn (fun x => (⟨x.2, x.1⟩ : Σ _ : Fin 19 × Fin 19, Fin 19))
        · intro x hx
          rw [Finset.mem_coe, Finset.mem_sigma] at hx
          obtain ⟨htIso, hpp⟩ := hx
          rw [Finset.mem_offDiag] at hpp
          obtain ⟨h1, h2, hne⟩ := hpp
          rw [Finset.mem_inter, G.mem_neighborFinset] at h1 h2
          obtain ⟨ht1, h1R⟩ := h1
          obtain ⟨ht2, h2R⟩ := h2
          rw [Finset.mem_coe, Finset.mem_sigma]
          refine ⟨Finset.mem_offDiag.mpr ⟨h1R, h2R, hne⟩, ?_⟩
          show x.1 ∈ G.neighborFinset x.2.1 ∩ G.neighborFinset x.2.2 ∩ Iso
          rw [Finset.mem_inter, Finset.mem_inter, G.mem_neighborFinset, G.mem_neighborFinset]
          exact ⟨⟨ht1.symm, ht2.symm⟩, htIso⟩
        · intro x _ y _ hxy
          simp only [Sigma.mk.injEq, heq_eq_eq] at hxy
          obtain ⟨h1, h2⟩ := hxy
          exact Sigma.ext h2 (heq_of_eq h1)
      have hRtle : ∑ p ∈ R.offDiag, (G.neighborFinset p.1 ∩ G.neighborFinset p.2 ∩ Iso).card ≤ 12 := by
        have h1 : ∑ p ∈ R.offDiag, (G.neighborFinset p.1 ∩ G.neighborFinset p.2 ∩ Iso).card
            ≤ ∑ _p ∈ R.offDiag, 2 := Finset.sum_le_sum hRshare2
        rw [Finset.sum_const, smul_eq_mul, Finset.offDiag_card, hRcard] at h1
        omega
      omega
    -- the convexity identity: `Q + 60 = (∑ offDiag) + 54`, so `Q ≤ 6`.
    have key_id : ∀ c d : ℕ, c + d = 3 → c * c - c + 4 * d = d * d - d + 6 := by
      intro c d h
      have hc3' : c ≤ 3 := by omega
      have hd3' : d ≤ 3 := by omega
      interval_cases c <;> interval_cases d <;> omega
    have hkeyid : ∀ t ∈ Iso, (G.neighborFinset t ∩ T).card * (G.neighborFinset t ∩ T).card
          - (G.neighborFinset t ∩ T).card + 4 * (G.neighborFinset t ∩ R).card
        = (G.neighborFinset t ∩ R).offDiag.card + 6 := by
      intro t ht
      rw [Finset.offDiag_card]
      exact key_id _ _ (hcd t ht)
    have hcong2 : (∑ t ∈ Iso, ((G.neighborFinset t ∩ T).card * (G.neighborFinset t ∩ T).card
          - (G.neighborFinset t ∩ T).card + 4 * (G.neighborFinset t ∩ R).card))
        = ∑ t ∈ Iso, ((G.neighborFinset t ∩ R).offDiag.card + 6) := Finset.sum_congr rfl hkeyid
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
      smul_eq_mul] at hcong2
    rw [hsumd, hIso] at hcong2
    -- the cover inequality, contradiction.
    have hCI := cover_offDiag_ineq_nineteen G Iso T hcov
    rw [hTcard] at hCI
    omega
  · rcases htight with htight | htight
    · -- **(9, 8, 38): star-triangle dichotomy.**
      by_cases hHP : ∃ h₁ h₂ : Fin 19, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
          G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
          2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
          2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card
      · exact Or.inl hHP
      · exact Or.inr (no_two_hub_star_triangle_deg5_nineteen G Hub Iso _hdeg _hdeg5 _hiso3 _hdisj
          _hshare (Or.inl htight) hHP _hC4 _hK23)
    · -- **(10, 7, 41): star-triangle dichotomy.**
      by_cases hHP : ∃ h₁ h₂ : Fin 19, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
          G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
          2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
          2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card
      · exact Or.inl hHP
      · exact Or.inr (no_two_hub_star_triangle_deg5_nineteen G Hub Iso _hdeg _hdeg5 _hiso3 _hdisj
          _hshare (Or.inr htight) hHP _hC4 _hK23)

/-- **PART B: the deg-`5` two-hub corner selector (`|Hub| ∈ {8, 9, 10}`).**  Either two non-adjacent
degree-`4` hubs each retain `≥ 2` private `M`-isolated twins (a good two-hub opposite-twin pair), or
the corner realises a `StarTriangleConfig`.  Routes around the degree-`5` hubs via the
degree-`4`-restricted share (`hshare`) and the shared `residual_arith_nineteen` engine. -/
theorem two_hub_corner_select_deg5_nineteen (G : SimpleGraph (Fin 19)) (Hub Iso : Finset (Fin 19))
    (hdeg : ∀ h ∈ Hub, 4 ≤ G.degree h) (hdeg5 : ∀ h ∈ Hub, G.degree h ≤ 5)
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hdisj : Disjoint Hub Iso)
    (hregime :
      (Hub.card = 8 ∧ Iso.card = 11 ∧ ∑ w ∈ Hub, G.degree w = 35) ∨
      (Hub.card = 9 ∧ Iso.card = 10 ∧ ∑ w ∈ Hub, G.degree w = 38) ∨
      (Hub.card = 10 ∧ Iso.card = 9 ∧ ∑ w ∈ Hub, G.degree w = 41) ∨
      (Hub.card = 8 ∧ Iso.card = 9 ∧ ∑ w ∈ Hub, G.degree w = 35 ∧
        (∀ v : Fin 19, 3 ≤ G.degree v) ∧ (∀ t ∈ Iso, G.degree t = 3) ∧
        ∑ h ∈ Hub, (G.neighborFinset h ∩ (Finset.univ \ (Hub ∪ Iso))).card ≤ 4 ∧
        ¬∃ x y z : Fin 19, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
          G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧
          G.degree x + G.degree y + G.degree z ≤ 11) ∨
      (Hub.card = 9 ∧ Iso.card = 8 ∧ ∑ w ∈ Hub, G.degree w = 38 ∧
        (∀ v : Fin 19, 3 ≤ G.degree v) ∧ (∀ t ∈ Iso, G.degree t = 3) ∧
        ∑ h ∈ Hub, (G.neighborFinset h ∩ (Finset.univ \ (Hub ∪ Iso))).card ≤ 4 ∧
        ¬∃ x y z : Fin 19, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
          G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧
          G.degree x + G.degree y + G.degree z ≤ 11) ∨
      (Hub.card = 10 ∧ Iso.card = 7 ∧ ∑ w ∈ Hub, G.degree w = 41 ∧
        (∀ v : Fin 19, 3 ≤ G.degree v) ∧ (∀ t ∈ Iso, G.degree t = 3) ∧
        ∑ h ∈ Hub, (G.neighborFinset h ∩ (Finset.univ \ (Hub ∪ Iso))).card ≤ 4 ∧
        ¬∃ x y z : Fin 19, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
          G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧
          G.degree x + G.degree y + G.degree z ≤ 11))
    (hC4 : ¬∃ a b c d : Fin 19, ({a, b, c, d} : Finset (Fin 19)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (hK23 : ¬∃ a b c d e : Fin 19, ({a, b, c, d, e} : Finset (Fin 19)).card = 5 ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
      G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 19) :
    (∃ h₁ h₂ : Fin 19, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card) ∨ TwoHubConfig G := by
  classical
  set F : Finset (Fin 19) :=
    Hub.filter (fun h => G.degree h = 4 ∧ (G.neighborFinset h ∩ Iso).card = 4) with hFdef
  by_cases hk : 2 ≤ F.card
  · -- **Extremal case: two degree-`4` hubs of iso-degree `4`.**
    obtain ⟨h₁, hh1F, h₂, hh2F, hne⟩ := Finset.one_lt_card.mp hk
    obtain ⟨hh1, hd1, h1iso4⟩ := Finset.mem_filter.mp hh1F
    obtain ⟨hh2, hd2, h2iso4⟩ := Finset.mem_filter.mp hh2F
    have hsub : ∀ h : Fin 19, G.degree h = 4 → (G.neighborFinset h ∩ Iso).card = 4 →
        G.neighborFinset h ⊆ Iso := by
      intro h hdh hh4
      have hdc : (G.neighborFinset h).card = 4 := by rw [G.card_neighborFinset_eq_degree, hdh]
      have heq : G.neighborFinset h ∩ Iso = G.neighborFinset h :=
        Finset.eq_of_subset_of_card_le Finset.inter_subset_left (le_of_eq (by rw [hdc, hh4]))
      rw [← heq]; exact Finset.inter_subset_right
    have h1sub : G.neighborFinset h₁ ⊆ Iso := hsub h₁ hd1 h1iso4
    have hnadj : ¬G.Adj h₁ h₂ := by
      intro hadj
      exact Finset.disjoint_left.mp hdisj hh2 (h1sub ((G.mem_neighborFinset h₁ h₂).mpr hadj))
    have hsh : (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1 :=
      hshare h₁ hh1 hd1 h₂ hh2 hd2 hne hnadj
    have hsh' : (G.neighborFinset h₂ ∩ G.neighborFinset h₁ ∩ Iso).card ≤ 1 :=
      hshare h₂ hh2 hd2 h₁ hh1 hd1 (Ne.symm hne) (fun h => hnadj h.symm)
    have hfin := select_finish_nineteen G Iso h₁ h₂ (by omega) (by omega)
    exact Or.inl ⟨h₁, h₂, hh1, hh2, hd1, hd2, hne, hnadj, hfin.1, hfin.2⟩
  · -- **Residual: at most one degree-`4` hub of iso-degree `4`.**
    have hdeg45 : ∀ h ∈ Hub, G.degree h = 4 ∨ G.degree h = 5 := by
      intro h hh; have := hdeg h hh; have := hdeg5 h hh; omega
    rcases hregime with hr | hr | hr | hr | hr | hr
    · refine Or.inl ?_
      obtain ⟨hHub, hIso, hdsum⟩ := hr
      by_contra hcon
      exact absurd (residual_arith_nineteen G Hub Iso hdisj hshare hiso3 hdeg45 hcon) (by
        rw [hHub, hIso, hdsum]; omega)
    · refine Or.inl ?_
      obtain ⟨hHub, hIso, hdsum⟩ := hr
      by_contra hcon
      exact absurd (residual_arith_nineteen G Hub Iso hdisj hshare hiso3 hdeg45 hcon) (by
        rw [hHub, hIso, hdsum]; omega)
    · refine Or.inl ?_
      obtain ⟨hHub, hIso, hdsum⟩ := hr
      by_contra hcon
      exact absurd (residual_arith_nineteen G Hub Iso hdisj hshare hiso3 hdeg45 hcon) (by
        rw [hHub, hIso, hdsum]; omega)
    · -- (8, 9, 35): tight.
      exact two_hub_deg5_tight_nineteen G Hub Iso hdeg hdeg5 hiso3 hdisj hshare
        (Or.inl hr) hC4 hK23
    · -- (9, 8, 38): tight.
      exact two_hub_deg5_tight_nineteen G Hub Iso hdeg hdeg5 hiso3 hdisj hshare
        (Or.inr (Or.inl hr)) hC4 hK23
    · -- (10, 7, 41): tight.
      exact two_hub_deg5_tight_nineteen G Hub Iso hdeg hdeg5 hiso3 hdisj hshare
        (Or.inr (Or.inr hr)) hC4 hK23

end N19

end ACMax
