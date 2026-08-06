import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N19.Core
import ACMaxConjecture.SmallCases.N19.TwoHubSelect
import ACMaxConjecture.SmallCases.N19.StarTriangleStruct
import ACMaxConjecture.SmallCases.N19.OctahedronForce
import ACMaxConjecture.SmallCases.N19.R5Octahedron
import ACMaxConjecture.SmallCases.N19.R5ResidHelpers
import ACMaxConjecture.SmallCases.N19.Core
import ACMaxConjecture.SmallCases.StarCertificates

/-!
# The `r = 5`, `S = 12` octahedron residual (`n = 19`, `|Hub| = 11`)

This file discharges the threaded hypothesis `hoct5` of `rich_count_ge_six_nineteen` (the `r = 5`
exclusion at `|Hub| = 11`): writing `R = {h ∈ Hub : 2 ≤ |N(h) ∩ Iso|}` for the rich hubs, the
profile `|R| = 5` with `∑_{r∈R} |N(r) ∩ Iso| = 12` is the unique residual that the `n = 18`-style
two-hub extraction in `rich_count_ge_six_nineteen` cannot reach.

## The two residual iso-degree multisets

With `|R| = 5`, every rich hub has iso-degree in `{2, 3, 4}` and the `5` values sum to `12`; the
no-two-hub bound (`rich_a3_count_le_two_nineteen`) caps the number of iso-degree-`≥ 3` rich hubs at
`2`.  The only solutions are

* `{2, 2, 2, 3, 3}` — no iso-degree-`4` hub (the *468-survivor family* recorded in
  `TwinCert19OctahedronForce`); and
* `{4, 2, 2, 2, 2}` — one iso-degree-`4` hub `a` (with `N(a) ⊆ Iso`, non-adjacent to every hub) but
  no second iso-degree-`≥ 3` hub.

The poor side `P = Hub \ R` has `6` hubs carrying iso-incidence `18 − 12 = 6`, so **every** poor hub
has iso-degree exactly `1` (`hnozero` below): the `|R| = 5` octahedron is *six*-poor, not five-poor
(contrast the `r = 6` regime in `TwinCert19OctahedronMassFour`).

## Reductions proved here (axiom-clean)

`r5_resid_nineteen` establishes, from `r = 5` and `S = 12`:

* `hnozero`: every hub has iso-degree `≥ 1` (the six poor hubs each carry exactly `1`);
* the **`|R| = 5` trace saturation** (`octahedron_trace_saturate_nineteen`, stated general in `|R|`):
  `(∑_t |N t ∩ R|·(|N t ∩ R| − 1)) + mRR = |R|² − |R| = 20` together with
  `∑_{r∈R} |N r ∩ Iso| = 7 + |R| = 12` — exactly the saturation the task flagged as reusable at
  `|R| = 5`;
* `hRcard : R.card = 5`, `hS12`, and `ha3 : (#rich with iso-degree ≥ 3) ≤ 2` — the precise
  characterisation of the residual.

## The cross-edge `C₄` dispatch (axiom-clean)

The proof extracts the two `M`-edge endpoints `Z = {z, z'}` (`z ∼ z'`) and their hub-neighbours
`g₁, g₂ = N(z) ∩ Hub`, `g₃, g₄ = N(z') ∩ Hub` (all available NON-circularly from
`z_two_hub_nbrs_nineteen` / `z_card_two_nineteen`, no `hztwopoor`), and **case-splits on whether any
cross edge `gᵢ ∼ gⱼ` exists** (`i ∈ {1,2}`, `j ∈ {3,4}`).  If so, the `4`-cycle `z – gᵢ – gⱼ – z'` is
a good `C₄` of degree sum `3 + 4 + 4 + 3 = 14` whose diagonals are forced non-adjacent (no hub meets
both `M`-endpoints — `no_hub_adj_both_mends_nineteen`), contradicting `hC4`
(`cross_z_hub_c4_false_nineteen` in `TwinCert19R5ResidHelpers`).  This **closes the cross-edge case
of BOTH multisets axiom-clean.**

## The no-cross residual — now CLOSED except one narrow `{4,2,2,2,2}` corner

In the no-cross case the four `Z`-hubs form an independent `4`-set.  Let `z_R` be the number of these
four `Z`-hubs that are *rich* (iso-degree `≥ 2`), and let `S = {h ∈ R : iso-degree ≥ 3}`
(`1 ≤ |S| ≤ 2`).  The proof closes the no-cross case by the reusable `Z`-leaf two-hub assembler
`two_hub_zleaf_nineteen` (a `TwoHubConfig` whose fourth leaf `d = z` is an `M`-edge endpoint,
invisible to the `Iso`-only `hno2hub`), in three branches — all but the last fully axiom-clean:

* **`z_R ≥ 1` (any rich `Z`-hub, BOTH multisets) — CLOSED.**  A rich `Z`-hub `h₂` has at most one
  hub-neighbour (`2` twins `+` an `M`-edge `+` `≤ 1` hub fills its degree `4`).  An iso-degree-`≥ 3`
  rich hub `h₁ ≁ h₂` always exists (`hfindh1`: if `|S| = 1` the lone hub is iso-degree-`4` with
  `N ⊆ Iso`, so `≁` every hub; if `|S| = 2` the two iso-degree-`3` hubs are each other's sole
  hub-neighbour, so neither meets the `Z`-hub `h₂`).  Then `hshare` yields two private twins `a, b`
  of `h₁` and one private twin `c` of `h₂`; with `d = z` this is a `TwoHubConfig`.

* **`z_R = 0`, `|S| = 2` (`{2,2,2,3,3}`) — CLOSED.**  The two iso-degree-`3` rich hubs `h, h'` are
  *adjacent* (`rich_isodeg3_pair_adj_r5_nineteen`), so they share **no** twin (the triangle
  `h–h'–t`, degree sum `4 + 4 + 3 = 11`, is excluded by `hT`).  Hence the unique twin `c` of the
  poor `Z`-hub `g₁` is non-adjacent to at least one of `h, h'`; that hub plays `h₁`, `g₁` plays `h₂`,
  `d = z`, giving a `TwoHubConfig`.

* **`z_R = 0`, `|S| = 1` (`{4,2,2,2,2}`) — CLOSED (axiom-clean, no `StarTriangleConfig` needed).**
  The lone iso-degree-`4` hub `a*` has `N(a*) ⊆ Iso` (`≁` every hub and `Z`).  Whenever **some** poor
  `Z`-hub's unique twin `c` is non-adjacent to `a*`, the cut `(h₁, h₂) = (a*, g)`, `c`, `d = z` is a
  `TwoHubConfig`.  The proof tries all four poor `Z`-hubs; the surviving sub-case — **all four** poor
  `Z`-hubs' twins adjacent to `a*` — is closed by the **same `two_hub_zleaf` assembler with a *rich*
  hub `r ∈ R \ {a*}` in the role of `h₁`** (see below).

## Why the all-twins-adjacent corner does NOT need a star-triangle

`two_hub_zleaf_nineteen` only requires `h₁` to carry **two private twins** — it does *not* require
`h₁` to have iso-degree `≥ 3`.  Fix the poor `Z`-hub `g₁` (unique twin `c₁`, `c₁ ∼ a*` in the
corner).  Of the four hubs `R \ {a*}` (each iso-degree exactly `2`): at most `2` are adjacent to `g₁`
(its hub-degree is `≤ 2`, since degree `4 = 1` iso `+ ≥ 1` `Z` `+` hub) and at most `1` carries `c₁`
as a twin (`c₁` has degree `3`, hub-neighbours `a*, g₁, w`).  Hence `4 − 2 − 1 ≥ 1` rich hub `r`
satisfies `r ≁ g₁` and `c₁ ∉ N(r)`; its two twins `a, b` are then both `≁ g₁` (the *only* twin of
`g₁` is `c₁`), giving the `Z`-leaf cut `(h₁, h₂) = (r, g₁)`, leaves `a, b`, opposite twin `c₁`,
fourth leaf `d = z` — a `TwoHubConfig`.  The earlier framing (which expected this corner to require a
forced hub-triangle / `StarTriangleConfig`) was unnecessarily restrictive: the pigeonhole over the
rich pool always supplies a usable `h₁`.  `ZPoorCutConfig` retains `StarTriangleConfig` as a disjunct
purely for interface compatibility; the `r = 5` residual never invokes it. -/

namespace ACMax

open scoped Classical

namespace N19

/-- **The `r = 5`, `S = 12` octahedron residual (`n = 19`, `|Hub| = 11`).**  Supplies the threaded
`hoct5` hypothesis of `rich_count_ge_six_nineteen`.  Everything up to the two-multiset
octahedron/star-triangle packing is reduced and verified here; the residual packing is the single
documented `sorry` (see the module docstring). -/
theorem r5_resid_nineteen (G : SimpleGraph (Fin 19)) (Hub Iso : Finset (Fin 19))
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
    (_hK23 : ¬∃ a b c d e : Fin 19, ({a, b, c, d, e} : Finset (Fin 19)).card = 5 ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
      G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 19)
    (hT : ¬∃ x y z : Fin 19, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧
      G.degree x + G.degree y + G.degree z ≤ 11) :
    (Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)).card = 5 →
      (∑ a ∈ Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card),
          (G.neighborFinset a ∩ Iso).card) = 12 → ZPoorCutConfig G := by
  classical
  intro hr5 hS12
  set R : Finset (Fin 19) := Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card) with hRdef
  have hReq : R = Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card) := hRdef
  have hRsub : R ⊆ Hub := Finset.filter_subset _ _
  -- Total iso-incidence `= 18`.
  have hsum18 : ∑ a ∈ Hub, (G.neighborFinset a ∩ Iso).card = 18 := by
    have := hub_iso_sum_nineteen G Hub Iso hiso3; rw [hIso] at this; omega
  -- The complement (poor side) `P` carries `18 − 12 = 6` incidences over `11 − 5 = 6` hubs.
  set P : Finset (Fin 19) := Hub.filter (fun h => ¬ 2 ≤ (G.neighborFinset h ∩ Iso).card) with hPdef
  have hPcard : P.card = 6 := by
    have := Finset.card_filter_add_card_filter_not (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)
      (s := Hub)
    rw [← hRdef, ← hPdef, hHub, hr5] at this; omega
  have hsplit : (∑ a ∈ R, (G.neighborFinset a ∩ Iso).card)
      + ∑ a ∈ P, (G.neighborFinset a ∩ Iso).card = 18 := by
    rw [hRdef, hPdef, Finset.sum_filter_add_sum_filter_not Hub _]; exact hsum18
  have hPsum : ∑ a ∈ P, (G.neighborFinset a ∩ Iso).card = 6 := by rw [hS12] at hsplit; omega
  -- Each poor hub has iso-degree `≤ 1`; the sum `6` over `6` hubs forces each `= 1`.
  have hPle1 : ∀ g ∈ P, (G.neighborFinset g ∩ Iso).card ≤ 1 := by
    intro g hg; rw [hPdef, Finset.mem_filter] at hg; omega
  have hPpos : ∀ g ∈ P, 1 ≤ (G.neighborFinset g ∩ Iso).card := by
    intro g hg
    by_contra hlt
    push Not at hlt
    have h0 : (G.neighborFinset g ∩ Iso).card = 0 := by omega
    -- One poor hub of iso-degree `0` drops the poor sum below `6 = |P|`.
    have hsub : ∑ a ∈ P, (G.neighborFinset a ∩ Iso).card
        = (G.neighborFinset g ∩ Iso).card
          + ∑ a ∈ P.erase g, (G.neighborFinset a ∩ Iso).card :=
      (Finset.add_sum_erase P _ hg).symm
    have hbound : ∑ a ∈ P.erase g, (G.neighborFinset a ∩ Iso).card ≤ (P.erase g).card := by
      calc ∑ a ∈ P.erase g, (G.neighborFinset a ∩ Iso).card
          ≤ ∑ _a ∈ P.erase g, 1 :=
            Finset.sum_le_sum (fun a ha => hPle1 a (Finset.mem_of_mem_erase ha))
        _ = (P.erase g).card := by rw [Finset.sum_const, smul_eq_mul, mul_one]
    rw [Finset.card_erase_of_mem hg, hPcard] at hbound
    omega
  -- `hnozero`: every hub has iso-degree `≥ 1`.
  have hnozero : ∀ h ∈ Hub, 1 ≤ (G.neighborFinset h ∩ Iso).card := by
    intro h hh
    by_cases hr : 2 ≤ (G.neighborFinset h ∩ Iso).card
    · omega
    · exact hPpos h (by rw [hPdef, Finset.mem_filter]; exact ⟨hh, hr⟩)
  -- **The `|R| = 5` trace saturation** (general-`|R|` leaf): `(∑_t offDiag) + mRR = 20` and
  -- `∑_{r∈R} |N r ∩ Iso| = 7 + 5 = 12`.
  have htrace := octahedron_trace_saturate_nineteen G Hub Iso R hReq hdeg4 hiso3 hdisj hHub hIso
    hisodeg3 hshare hno2hub hT hnozero
  rw [hr5] at htrace
  obtain ⟨hsat, hiso12⟩ := htrace
  -- `hsat : (∑_t |N t ∩ R|.offDiag) + mRR = 5 * 5 - 5 = 20`; `hiso12 : ∑_{r∈R} |N r ∩ Iso| = 12`.
  -- At most two rich hubs have iso-degree `≥ 3` (no-two-hub bound).
  have ha3 : (R.filter (fun h => 3 ≤ (G.neighborFinset h ∩ Iso).card)).card ≤ 2 := by
    have heq : R.filter (fun h => 3 ≤ (G.neighborFinset h ∩ Iso).card)
        = Hub.filter (fun h => G.degree h = 4 ∧ 3 ≤ (G.neighborFinset h ∩ Iso).card) := by
      rw [hRdef, Finset.filter_filter]; apply Finset.filter_congr
      intro a ha; constructor
      · rintro ⟨_, h3⟩; exact ⟨hdeg4 a ha, h3⟩
      · rintro ⟨_, h3⟩; exact ⟨by omega, h3⟩
    rw [heq]; exact rich_a3_count_le_two_nineteen G Hub Iso hdisj hshare hno2hub
  -- **R=5 octahedron poor-layer structure** (axiom-clean, no `hztwopoor`): six poor hubs each of
  -- iso-degree `1`, with `E(R, Iso) = 12` and `E(P, Iso) = 6` (the `R.card = 5` analogue of
  -- `octahedron_struct_nineteen`, here with six poor hubs rather than five).
  have _hstruct := octahedron_struct_r5_nineteen G Hub Iso R hReq hiso3 hHub hIso hnozero hr5
  -- Every poor hub meets exactly one (low) twin; that twin carries the poor incidence.
  have _hlowtwin := octahedron_low_twin_poor_r5_nineteen G Hub Iso R hReq hiso3 hHub hIso hnozero hr5
  -- **R=5 rigidity:** the two iso-degree-`3` rich hubs (in the `{2,2,2,3,3}` multiset) are *adjacent*
  -- (two non-adjacent iso-degree-`≥ 3` hubs would keep `≥ 2` private twins each, contradicting
  -- `hno2hub`).  Each is then degree-`4`-saturated by its three twins plus the other, so it has no
  -- poor / `Z` neighbour.
  have _hr3adj := rich_isodeg3_pair_adj_r5_nineteen G Hub Iso hshare hno2hub
  -- ===== Cross-edge `C₄` dispatch (axiom-clean, non-circular). =====
  -- Extract the two `M`-edge endpoints `Z = {z, z'}` and their hub-neighbours, then case-split on
  -- whether a hub-neighbour of `z` is adjacent to a hub-neighbour of `z'`.  If so, the `4`-cycle
  -- `z – gᵢ – gⱼ – z'` is a good `C₄` (`cross_z_hub_c4_false_nineteen`, degree sum `3+4+4+3 = 14`,
  -- both diagonals forced non-adjacent because no hub meets both `M`-endpoints), contradicting `hC4`
  -- and discharging the goal vacuously.  This closes EVERY graph carrying such a cross edge
  -- (structured enumeration: `5415` of the `8295` in-regime `{2,2,2,3,3}` realisations,
  -- `scratchpad/r5cross.py`/`r5cat.py`).
  set Z : Finset (Fin 19) := Finset.univ \ (Hub ∪ Iso) with hZdef
  have hZcard : Z.card = 2 := z_card_two_nineteen Hub Iso hdisj hHub hIso
  obtain ⟨z, z', hzz', hZpair⟩ := Finset.card_eq_two.mp hZcard
  have hzZ : z ∈ Z := by rw [hZpair]; exact Finset.mem_insert_self _ _
  have hz'Z : z' ∈ Z := by
    rw [hZpair]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  obtain ⟨_, hzhub2, _⟩ :=
    z_two_hub_nbrs_nineteen G Hub Iso hiso3 hdisj hHub hIso hdsum hdeg3 hisodeg3 hleak z hzZ
  obtain ⟨g₁, g₂, _hg₁g₂, hNz⟩ := Finset.card_eq_two.mp hzhub2
  obtain ⟨_, hz'hub2, _⟩ :=
    z_two_hub_nbrs_nineteen G Hub Iso hiso3 hdisj hHub hIso hdsum hdeg3 hisodeg3 hleak z' hz'Z
  obtain ⟨g₃, g₄, _hg₃g₄, hNz'⟩ := Finset.card_eq_two.mp hz'hub2
  -- Hub-memberships and `z`/`z'` adjacencies for the four hub-neighbours.
  have hg₁mem : g₁ ∈ G.neighborFinset z ∩ Hub := by rw [hNz]; exact Finset.mem_insert_self _ _
  have hg₂mem : g₂ ∈ G.neighborFinset z ∩ Hub := by
    rw [hNz]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hg₃mem : g₃ ∈ G.neighborFinset z' ∩ Hub := by rw [hNz']; exact Finset.mem_insert_self _ _
  have hg₄mem : g₄ ∈ G.neighborFinset z' ∩ Hub := by
    rw [hNz']; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hg₁Hub : g₁ ∈ Hub := (Finset.mem_inter.mp hg₁mem).2
  have hg₂Hub : g₂ ∈ Hub := (Finset.mem_inter.mp hg₂mem).2
  have hg₃Hub : g₃ ∈ Hub := (Finset.mem_inter.mp hg₃mem).2
  have hg₄Hub : g₄ ∈ Hub := (Finset.mem_inter.mp hg₄mem).2
  have hzg₁ : G.Adj z g₁ := (G.mem_neighborFinset z g₁).mp (Finset.mem_inter.mp hg₁mem).1
  have hzg₂ : G.Adj z g₂ := (G.mem_neighborFinset z g₂).mp (Finset.mem_inter.mp hg₂mem).1
  have hz'g₃ : G.Adj z' g₃ := (G.mem_neighborFinset z' g₃).mp (Finset.mem_inter.mp hg₃mem).1
  have hz'g₄ : G.Adj z' g₄ := (G.mem_neighborFinset z' g₄).mp (Finset.mem_inter.mp hg₄mem).1
  -- Reusable closer for an arbitrary cross adjacency.
  have hkill : ∀ g g' : Fin 19, g ∈ Hub → g' ∈ Hub → G.Adj z g → G.Adj z' g' → G.Adj g g' →
      ZPoorCutConfig G := fun g g' hg hg' hzg hz'g' hcr =>
    (cross_z_hub_c4_false_nineteen G Hub Iso hdeg4 hiso3 hdisj hHub hIso hdsum hdeg3 hisodeg3 hleak
      hC4 hT z hzZ z' hz'Z hzz' g g' hg hg' hzg hz'g' hcr).elim
  by_cases hcross :
      G.Adj g₁ g₃ ∨ G.Adj g₁ g₄ ∨ G.Adj g₂ g₃ ∨ G.Adj g₂ g₄
  · rcases hcross with h | h | h | h
    · exact hkill g₁ g₃ hg₁Hub hg₃Hub hzg₁ hz'g₃ h
    · exact hkill g₁ g₄ hg₁Hub hg₄Hub hzg₁ hz'g₄ h
    · exact hkill g₂ g₃ hg₂Hub hg₃Hub hzg₂ hz'g₃ h
    · exact hkill g₂ g₄ hg₂Hub hg₄Hub hzg₂ hz'g₄ h
  · -- ===== The no-cross residual (the genuinely-new `R.card = 5` deep crux). =====
    -- Here the four distinct `Z`-hubs `g₁, g₂` (`= N(z) ∩ Hub`) and `g₃, g₄` (`= N(z') ∩ Hub`) carry
    -- NO cross edge, so they form an independent `4`-set (each pair within a side is non-adjacent by
    -- `z_hubs_nonadj_nineteen`, the cross pairs by `hcross`).
    --
    -- **CORRECTION (the no-cross family is NOT empty — disproven by a direct witness).**  An earlier
    -- analysis claimed this family is EMPTY (a good triangle `(poor,poor,Z)`/`(poor,Z,Z)` is forced,
    -- contradicting `hT`).  That claim is FALSE: it rests on `scratchpad/r5cat.py`, which enumerates
    -- only the **canonical** octahedron twin structure, where `hno2hub` happens to force full rich
    -- saturation (rich edges `0-1, 2-3, 2-4, 3-4`), hence `z_R = 0` and a poor over-load (`8` edges
    -- into a capacity-`6` core) — a genuine contradiction *there only*.  But a valid NON-canonical
    -- twin structure exists (a twin meeting **two** poor hubs, e.g. `{0,5,6}`): the good-triangle
    -- avoidance then FORBIDS the rich edge `2-3` (hubs `2,3` share that twin), so rich hubs `2,3` keep
    -- a free slot, connect OUT to the `M`-ends (`z_R = 2`), and the over-load collapses.
    -- `scratchpad/r5_nocross_witness.py` exhibits an explicit fully in-regime no-cross realisation
    -- (`N(z) = {2,5}`, `N(z') = {3,6}`, all degrees `4/3/3`, `hshare ∧ hno2hub`, NO good
    -- triangle/`C₄`/`K₂,₃`).  This validates the project-memory warning that canonical-only
    -- enumeration "LIED"; only direct per-structure construction is trustworthy.
    --
    -- **The correct residual is a `ZPoorCutConfig` PACKING, not an emptiness/`False` proof.**  The
    -- witness is closed by `TwoHubConfig` `(h₁,h₂,a,b,c,d) = (0,2,11,13,14,17)` with the `Z`-leaf
    -- `d = 17 ∈ Z` (an `M`-end, invisible to the `Iso`-only `hno2hub`).
    --
    -- ===== VERIFIED REDUCTION (`scratchpad/r5recipe_verify.py`, reproduces the witness exactly) =====
    -- The packing has a UNIFORM recipe with all side conditions AUTOMATIC.  Take
    --   `h₂ := gᵢ` a `Z`-hub (one of `g₁,g₂,g₃,g₄`), `d := z` (the `M`-end `h₂` meets, so `Adj z h₂`),
    --   `c := ` a twin of `h₂` NOT adjacent to `h₁`,
    --   `h₁ := ` an iso-degree-`≥ 3` rich hub, `a, b := ` two twins of `h₁` not adjacent to `h₂`.
    -- Because **twins meet only hubs** (each twin has degree `3` with all three incidences in `Hub`)
    -- and **`z` meets no twin** (`z_two_hub_nbrs_nineteen`), every leaf–leaf and leaf–`z`
    -- non-adjacency of `TwoHubConfig` (`¬Adj a c`, `¬Adj a d`, `¬Adj b c`, `¬Adj b d`) holds *for
    -- free*; the remaining conditions reduce to: `h₁ ≁ h₂`, `a, b ≁ h₂`, `c, z ≁ h₁`, plus distinctness.
    --
    -- The `h₁` SIDE IS STRUCTURALLY SOLID.  An iso-degree-`≥ 3` rich hub `h₁` is **saturated** (its
    -- `≥ 3` twins plus, in `{2,2,2,3,3}`, the other iso-degree-`3` hub fill degree `4`;
    -- `rich_isodeg3_pair_adj_r5_nineteen`), hence has **no `Z`-neighbour**, so `h₁ ≁` every `Z`-hub
    -- `gᵢ` (each `gᵢ` meets `z`); and `h₁` shares `≤ 1` twin with any non-adjacent hub (`hshare`), so it
    -- retains `≥ 2` private twins `a, b` against any `gᵢ`.  (In `{4,2,2,2,2}` the iso-degree-`4` hub
    -- `a`, with `N(a) ⊆ Iso`, plays `h₁`.)
    --
    -- The remaining gap is the `h₂` side: a `Z`-hub with a twin `c ≁ h₁`.  A **rich** `Z`-hub
    -- (`≥ 2` twins, `≤ 1` shared with `h₁` by `hshare`) ALWAYS supplies `c` — so **`z_R ≥ 1` closes the
    -- no-cross case cleanly** (the witness has `z_R = 2`, `h₂ = 2` a rich `Z`-hub).  The sub-case
    -- **`z_R = 0`** (all four `Z`-hubs poor, each iso-degree `1`) is now ALSO closed (axiom-clean): for
    -- `|S| = 2` via the adjacent iso-degree-`3` pair (they share no twin, so `g₁`'s twin avoids one of
    -- them); for `|S| = 1` (`{4,2,2,2,2}`), even when all four poor twins are adjacent to `a*`, a
    -- pigeonhole over the four rich hubs `R \ {a*}` supplies a *rich* `h₁ = r ≁ g₁` with `c₁ ∉ N(r)`
    -- (`r` has two twins, both private to `g₁`), giving a `two_hub_zleaf` `TwoHubConfig` — no
    -- star-triangle needed.  See the module docstring.
    have _hg₁₃ : ¬G.Adj g₁ g₃ := fun h => hcross (Or.inl h)
    have _hg₁₄ : ¬G.Adj g₁ g₄ := fun h => hcross (Or.inr (Or.inl h))
    have _hg₂₃ : ¬G.Adj g₂ g₃ := fun h => hcross (Or.inr (Or.inr (Or.inl h)))
    have _hg₂₄ : ¬G.Adj g₂ g₄ := fun h => hcross (Or.inr (Or.inr (Or.inr h)))
    -- ===== Structural layer for the iso-degree-`≥ 3` rich hubs `S`. =====
    set S : Finset (Fin 19) := R.filter (fun h => 3 ≤ (G.neighborFinset h ∩ Iso).card) with hSdef
    -- Each rich hub has iso-degree `≥ 2` (definition of `R`).
    have hRrich : ∀ r ∈ R, 2 ≤ (G.neighborFinset r ∩ Iso).card := by
      intro r hr; rw [hRdef, Finset.mem_filter] at hr; exact hr.2
    -- `|S| ≤ 2` (the no-two-hub bound) and `|S| ≥ 1` (the sum `12 > 2·5`).
    have hSle2 : S.card ≤ 2 := ha3
    have hSpos : 1 ≤ S.card := by
      by_contra h
      push Not at h
      have hS0 : S.card = 0 := by omega
      have hSempty : S = ∅ := Finset.card_eq_zero.mp hS0
      -- Every rich hub then has iso-degree `≤ 2`, so the sum is `≤ 10 < 12`.
      have hle2 : ∀ r ∈ R, (G.neighborFinset r ∩ Iso).card ≤ 2 := by
        intro r hr
        by_contra hge
        push Not at hge
        exact (Finset.notMem_empty r) (hSempty ▸ (Finset.mem_filter.mpr ⟨hr, by omega⟩))
      have : (∑ r ∈ R, (G.neighborFinset r ∩ Iso).card) ≤ 10 := by
        calc (∑ r ∈ R, (G.neighborFinset r ∩ Iso).card) ≤ ∑ _r ∈ R, 2 :=
              Finset.sum_le_sum hle2
          _ = 10 := by rw [Finset.sum_const, hr5, smul_eq_mul]
      omega
    -- The three-way neighbour split for every vertex.
    have hpart : ∀ v : Fin 19, (G.neighborFinset v ∩ Hub).card + (G.neighborFinset v ∩ Iso).card
        + (G.neighborFinset v ∩ Z).card = G.degree v := by
      intro v; rw [hZdef]; exact nbr_split_three_nineteen G Hub Iso hdisj v
    -- **Saturation of an iso-degree-`≥ 3` hub adjacent to another hub** (`F1`): its sole hub-neighbour
    -- is that hub and it has no `Z`-neighbour.
    have hF1 : ∀ u v : Fin 19, u ∈ Hub → 3 ≤ (G.neighborFinset u ∩ Iso).card → G.Adj u v →
        v ∈ Hub → (G.neighborFinset u ∩ Hub).card = 1 ∧ (G.neighborFinset u ∩ Z).card = 0 ∧
          v ∈ G.neighborFinset u ∩ Hub := by
      intro u v huHub hu3 huv hvHub
      have hvmem : v ∈ G.neighborFinset u ∩ Hub :=
        Finset.mem_inter.mpr ⟨(G.mem_neighborFinset u v).mpr huv, hvHub⟩
      have hge1 : 1 ≤ (G.neighborFinset u ∩ Hub).card := Finset.card_pos.mpr ⟨v, hvmem⟩
      have hsp := hpart u
      have hdu : G.degree u = 4 := hdeg4 u huHub
      rw [hdu] at hsp
      exact ⟨by omega, by omega, hvmem⟩
    -- **Finder:** for any hub `h₂` that meets a `Z`-vertex `zz`, there is an iso-degree-`≥ 3` rich
    -- hub `h₁` that is non-adjacent to `h₂` and meets no `Z`-vertex.  (`|S| = 1`: the iso-degree-`4`
    -- hub has `N ⊆ Iso`; `|S| = 2`: either iso-degree-`3` hub is saturated by the other, hence has no
    -- `Z`-neighbour, while `h₂` does meet `zz`.)
    have hfindh1 : ∀ h₂ zz : Fin 19, h₂ ∈ Hub → zz ∈ Z → G.Adj zz h₂ →
        ∃ h₁ : Fin 19, h₁ ∈ Hub ∧ G.degree h₁ = 4 ∧ 3 ≤ (G.neighborFinset h₁ ∩ Iso).card ∧
          h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧ (∀ w ∈ Z, ¬G.Adj h₁ w) := by
      intro h₂ zz hh₂Hub hzzZ hzz2
      have hzzmem₂ : zz ∈ G.neighborFinset h₂ ∩ Z :=
        Finset.mem_inter.mpr ⟨(G.mem_neighborFinset h₂ zz).mpr hzz2.symm, hzzZ⟩
      rcases Nat.lt_or_ge S.card 2 with hS1 | hS2
      · -- `|S| = 1`: the single iso-degree-`4` hub `e` with `N(e) ⊆ Iso`.
        have hScard1 : S.card = 1 := by omega
        obtain ⟨e, hSeq⟩ := Finset.card_eq_one.mp hScard1
        have heS : e ∈ S := by rw [hSeq]; exact Finset.mem_singleton_self _
        rw [hSdef, Finset.mem_filter] at heS
        obtain ⟨heR, he3⟩ := heS
        have heHub : e ∈ Hub := hRsub heR
        have hde : G.degree e = 4 := hdeg4 e heHub
        -- `iso-degree(e) = 4`.
        have heiso4 : (G.neighborFinset e ∩ Iso).card = 4 := by
          have hrest : ∑ r ∈ R.erase e, (G.neighborFinset r ∩ Iso).card = 8 := by
            have hcard : (R.erase e).card = 4 := by rw [Finset.card_erase_of_mem heR, hr5]
            have heach : ∀ r ∈ R.erase e, (G.neighborFinset r ∩ Iso).card = 2 := by
              intro r hr
              have hrR : r ∈ R := Finset.mem_of_mem_erase hr
              have hrne : r ≠ e := Finset.ne_of_mem_erase hr
              have hge2 := hRrich r hrR
              have hlt3 : (G.neighborFinset r ∩ Iso).card < 3 := by
                by_contra hge3; push Not at hge3
                have hrS : r ∈ S := by rw [hSdef, Finset.mem_filter]; exact ⟨hrR, hge3⟩
                rw [hSeq, Finset.mem_singleton] at hrS; exact hrne hrS
              omega
            rw [Finset.sum_congr rfl heach, Finset.sum_const, hcard, smul_eq_mul]
          have hae := Finset.add_sum_erase R (fun r => (G.neighborFinset r ∩ Iso).card) heR
          rw [hrest, hiso12] at hae
          omega
        -- `N(e) ⊆ Iso`.
        have heNIso : G.neighborFinset e ⊆ Iso := by
          have hcardN : (G.neighborFinset e).card = 4 := by rw [G.card_neighborFinset_eq_degree, hde]
          have heq : G.neighborFinset e ∩ Iso = G.neighborFinset e :=
            Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by rw [heiso4, hcardN])
          rw [← heq]; exact Finset.inter_subset_right
        refine ⟨e, heHub, hde, by omega, ?_, ?_, ?_⟩
        · intro he
          rw [he] at heNIso
          have hzzIso : zz ∈ Iso := heNIso ((G.mem_neighborFinset h₂ zz).mpr hzz2.symm)
          rw [Finset.mem_sdiff, Finset.mem_union, not_or] at hzzZ
          exact hzzZ.2.2 hzzIso
        · intro hadj
          exact Finset.disjoint_left.mp hdisj hh₂Hub
            (heNIso ((G.mem_neighborFinset e h₂).mpr hadj))
        · intro w hwZ hadj
          have hwIso : w ∈ Iso := heNIso ((G.mem_neighborFinset e w).mpr hadj)
          rw [Finset.mem_sdiff, Finset.mem_union, not_or] at hwZ; exact hwZ.2.2 hwIso
      · -- `|S| = 2`: pick the iso-degree-`3` hub `h` (saturated, no `Z`-neighbour).
        have hScard2 : S.card = 2 := by omega
        obtain ⟨h, h', hhne, hSeq⟩ := Finset.card_eq_two.mp hScard2
        have hhS : h ∈ S := by rw [hSeq]; exact Finset.mem_insert_self _ _
        have hh'S : h' ∈ S := by
          rw [hSeq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
        rw [hSdef, Finset.mem_filter] at hhS hh'S
        obtain ⟨hhR, hh3⟩ := hhS
        obtain ⟨hh'R, hh'3⟩ := hh'S
        have hhHub : h ∈ Hub := hRsub hhR
        have hh'Hub : h' ∈ Hub := hRsub hh'R
        have hadjhh' : G.Adj h h' :=
          rich_isodeg3_pair_adj_r5_nineteen G Hub Iso hshare hno2hub h h' hhHub hh'Hub
            (hdeg4 h hhHub) (hdeg4 h' hh'Hub) hhne hh3 hh'3
        obtain ⟨hHub1, hHubZ0, hh'inNh⟩ := hF1 h h' hhHub hh3 hadjhh' hh'Hub
        -- `h` has no `Z`-neighbour.
        have hhnoZ : ∀ w ∈ Z, ¬G.Adj h w := by
          intro w hwZ hadj
          have : w ∈ G.neighborFinset h ∩ Z :=
            Finset.mem_inter.mpr ⟨(G.mem_neighborFinset h w).mpr hadj, hwZ⟩
          rw [Finset.card_eq_zero] at hHubZ0; rw [hHubZ0] at this; exact Finset.notMem_empty w this
        refine ⟨h, hhHub, hdeg4 h hhHub, hh3, ?_, ?_, hhnoZ⟩
        · intro he; subst he; exact hhnoZ zz hzzZ hzz2.symm
        · intro hadj
          -- `h ~ h₂ ⟹ h₂ = h'` (sole hub-neighbour); but `h'` meets no `Z`, contradicting `h₂ ~ zz`.
          have hh₂in : h₂ ∈ G.neighborFinset h ∩ Hub :=
            Finset.mem_inter.mpr ⟨(G.mem_neighborFinset h h₂).mpr hadj, hh₂Hub⟩
          obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hHub1
          rw [hw, Finset.mem_singleton] at hh₂in hh'inNh
          have heqh₂ : h₂ = h' := hh₂in.trans hh'inNh.symm
          have hzzmem' : zz ∈ G.neighborFinset h' ∩ Z := heqh₂ ▸ hzzmem₂
          obtain ⟨_, h'HubZ0, _⟩ := hF1 h' h hh'Hub hh'3 hadjhh'.symm hhHub
          rw [Finset.card_eq_zero] at h'HubZ0; rw [h'HubZ0] at hzzmem'
          exact Finset.notMem_empty zz hzzmem'
    -- ===== Detect a rich `Z`-hub (the `z_R ≥ 1` regime). =====
    by_cases hzR : 2 ≤ (G.neighborFinset g₁ ∩ Iso).card ∨ 2 ≤ (G.neighborFinset g₂ ∩ Iso).card ∨
        2 ≤ (G.neighborFinset g₃ ∩ Iso).card ∨ 2 ≤ (G.neighborFinset g₄ ∩ Iso).card
    · -- **`z_R ≥ 1`:** a rich `Z`-hub `h₂` (with its `M`-end `zz`) pairs with an iso-degree-`≥ 3`
      -- rich hub `h₁ ≁ h₂` (from `hfindh1`) to give a `TwoHubConfig` `Z`-leaf cut.
      have hcloseR : ∀ h₂ zz : Fin 19, h₂ ∈ Hub → zz ∈ Z → G.Adj zz h₂ →
          2 ≤ (G.neighborFinset h₂ ∩ Iso).card → ZPoorCutConfig G := by
        intro h₂ zz hh₂Hub hzzZ hzz2 hh₂rich
        obtain ⟨h₁, hh₁Hub, hdh₁, hh₁3, hh₁ne, hn1₂, hh₁noZ⟩ := hfindh1 h₂ zz hh₂Hub hzzZ hzz2
        obtain ⟨a, b, haIso, hbIso, hab, ha1, hb1, ha2, hb2⟩ :=
          exists_two_private_twins_nineteen G Hub Iso hshare h₁ h₂ hh₁Hub hh₂Hub hdh₁
            (hdeg4 h₂ hh₂Hub) hh₁ne hn1₂ hh₁3
        obtain ⟨c, hcIso, hc2, hn1c⟩ :=
          exists_one_private_twin_nineteen G Hub Iso hshare h₂ h₁ hh₂Hub hh₁Hub
            (hdeg4 h₂ hh₂Hub) hdh₁ hh₁ne hn1₂ hh₂rich
        exact Or.inl (two_hub_zleaf_nineteen G Hub Iso hiso3 hdisj hHub hIso hdsum hdeg3 hisodeg3
          hleak h₁ h₂ a b c zz hh₁Hub hh₂Hub hdh₁ (hdeg4 h₂ hh₂Hub) haIso hbIso hcIso hzzZ
          ha1 hb1 hc2 hzz2 hn1₂ hn1c (hh₁noZ zz hzzZ) ha2 hb2 hab)
      rcases hzR with hp | hp | hp | hp
      · exact hcloseR g₁ z hg₁Hub hzZ hzg₁ hp
      · exact hcloseR g₂ z hg₂Hub hzZ hzg₂ hp
      · exact hcloseR g₃ z' hg₃Hub hz'Z hz'g₃ hp
      · exact hcloseR g₄ z' hg₄Hub hz'Z hz'g₄ hp
    · -- **`z_R = 0`:** all four `Z`-hubs are poor (iso-degree `1`).
      push Not at hzR
      obtain ⟨hp1, hp2, hp3, hp4⟩ := hzR
      -- `g₁` is poor: iso-degree exactly `1`; extract its unique twin `c`.
      have hg₁iso1 : (G.neighborFinset g₁ ∩ Iso).card = 1 := by
        have := hnozero g₁ hg₁Hub; omega
      rcases Nat.lt_or_ge S.card 2 with hS1 | hS2
      · -- `|S| = 1` ⟹ the `{4, 2, 2, 2, 2}` multiset; the single iso-degree-`4` hub `a* = e` with
        -- `N(a*) ⊆ Iso` (non-adjacent to every hub and `Z`).  Whenever *some* poor `Z`-hub's twin is
        -- non-adjacent to `a*`, the `TwoHubConfig` `Z`-leaf cut (`h₁ = a*`, `h₂` the poor `Z`-hub,
        -- `c` its twin, `d` its `M`-end) closes the case.  Only the residual where **all four** poor
        -- `Z`-hubs' twins are adjacent to `a*` survives — the documented open boundary-packing crux
        -- (closed by `StarTriangleConfig`: centre `a*`, two of its twins, a forced hub-triangle).
        have hScard1 : S.card = 1 := by omega
        obtain ⟨e, hSeq⟩ := Finset.card_eq_one.mp hScard1
        have heS : e ∈ S := by rw [hSeq]; exact Finset.mem_singleton_self _
        rw [hSdef, Finset.mem_filter] at heS
        obtain ⟨heR, he3⟩ := heS
        have heHub : e ∈ Hub := hRsub heR
        have hde : G.degree e = 4 := hdeg4 e heHub
        -- `iso-degree(e) = 4` (the four `R \ {e}` rich hubs each carry exactly `2`).
        have heiso4 : (G.neighborFinset e ∩ Iso).card = 4 := by
          have hrest : ∑ r ∈ R.erase e, (G.neighborFinset r ∩ Iso).card = 8 := by
            have hcard : (R.erase e).card = 4 := by rw [Finset.card_erase_of_mem heR, hr5]
            have heach : ∀ r ∈ R.erase e, (G.neighborFinset r ∩ Iso).card = 2 := by
              intro r hr
              have hrR : r ∈ R := Finset.mem_of_mem_erase hr
              have hrne : r ≠ e := Finset.ne_of_mem_erase hr
              have hge2 := hRrich r hrR
              have hlt3 : (G.neighborFinset r ∩ Iso).card < 3 := by
                by_contra hge3; push Not at hge3
                have hrS : r ∈ S := by rw [hSdef, Finset.mem_filter]; exact ⟨hrR, hge3⟩
                rw [hSeq, Finset.mem_singleton] at hrS; exact hrne hrS
              omega
            rw [Finset.sum_congr rfl heach, Finset.sum_const, hcard, smul_eq_mul]
          have hae := Finset.add_sum_erase R (fun r => (G.neighborFinset r ∩ Iso).card) heR
          rw [hrest, hiso12] at hae
          omega
        have heNIso : G.neighborFinset e ⊆ Iso := by
          have hcardN : (G.neighborFinset e).card = 4 := by rw [G.card_neighborFinset_eq_degree, hde]
          have heq : G.neighborFinset e ∩ Iso = G.neighborFinset e :=
            Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by rw [heiso4, hcardN])
          rw [← heq]; exact Finset.inter_subset_right
        -- Closer for a poor `Z`-hub `g` (`M`-end `zz`) whose twin `c` is non-adjacent to `a* = e`.
        have hpoorclose : ∀ g zz c : Fin 19, g ∈ Hub → zz ∈ Z → G.Adj zz g →
            c ∈ Iso → G.Adj c g → ¬G.Adj e c → ZPoorCutConfig G := by
          intro g zz c hgHub hzzZ hzzg hcIso hcg hnec
          have hn_eg : ¬G.Adj e g := fun h =>
            Finset.disjoint_left.mp hdisj hgHub (heNIso ((G.mem_neighborFinset e g).mpr h))
          have hne_eg : e ≠ g := by intro h; apply hnec; rw [h]; exact hcg.symm
          have hn_ezz : ¬G.Adj e zz := by
            intro h
            have hzzIso : zz ∈ Iso := heNIso ((G.mem_neighborFinset e zz).mpr h)
            rw [Finset.mem_sdiff, Finset.mem_union, not_or] at hzzZ; exact hzzZ.2.2 hzzIso
          obtain ⟨a, b, haIso, hbIso, hab, ha1, hb1, hag, hbg⟩ :=
            exists_two_private_twins_nineteen G Hub Iso hshare e g heHub hgHub hde
              (hdeg4 g hgHub) hne_eg hn_eg (by omega)
          exact Or.inl (two_hub_zleaf_nineteen G Hub Iso hiso3 hdisj hHub hIso hdsum hdeg3 hisodeg3
            hleak e g a b c zz heHub hgHub hde (hdeg4 g hgHub) haIso hbIso hcIso hzzZ
            ha1 hb1 hcg hzzg hn_eg hnec hn_ezz hag hbg hab)
        -- Twin extractor for a poor hub.
        have gettwin : ∀ g : Fin 19, (G.neighborFinset g ∩ Iso).card = 1 →
            ∃ c : Fin 19, c ∈ Iso ∧ G.Adj c g := by
          intro g hg1
          obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hg1
          have hcm : c ∈ G.neighborFinset g ∩ Iso := by rw [hc]; exact Finset.mem_singleton_self _
          rw [Finset.mem_inter, G.mem_neighborFinset] at hcm
          exact ⟨c, hcm.2, hcm.1.symm⟩
        have hg₂iso1 : (G.neighborFinset g₂ ∩ Iso).card = 1 := by have := hnozero g₂ hg₂Hub; omega
        have hg₃iso1 : (G.neighborFinset g₃ ∩ Iso).card = 1 := by have := hnozero g₃ hg₃Hub; omega
        have hg₄iso1 : (G.neighborFinset g₄ ∩ Iso).card = 1 := by have := hnozero g₄ hg₄Hub; omega
        obtain ⟨c₁, hc₁Iso, hc₁g⟩ := gettwin g₁ hg₁iso1
        by_cases h1 : G.Adj e c₁
        · obtain ⟨c₂, hc₂Iso, hc₂g⟩ := gettwin g₂ hg₂iso1
          by_cases h2 : G.Adj e c₂
          · obtain ⟨c₃, hc₃Iso, hc₃g⟩ := gettwin g₃ hg₃iso1
            by_cases h3 : G.Adj e c₃
            · obtain ⟨c₄, hc₄Iso, hc₄g⟩ := gettwin g₄ hg₄iso1
              by_cases h4 : G.Adj e c₄
              · -- **The all-twins-adjacent residual — CLOSED via `TwoHubConfig` with a RICH `h₁`.**
                -- Each poor `Z`-hub's twin being adjacent to `a* = e` only blocks the *`e`*-centred
                -- two-hub cut.  But `two_hub_zleaf_nineteen` only needs `h₁` to carry two private
                -- twins, so a *rich* iso-degree-`2` hub `r ∈ R \ {e}` serves equally well.  `g₁`'s
                -- unique twin is `c₁`.  Of the four hubs `R \ {e}`: at most `2` are adjacent to `g₁`
                -- (since `|N(g₁) ∩ Hub| ≤ 2`) and at most `1` has `c₁` as a twin (`c₁`'s three hub
                -- neighbours are `e, g₁, w`).  Hence some rich `r ≁ g₁` has `c₁ ∉ N(r)`; its two twins
                -- `a, b` are then both `≁ g₁` (the only twin of `g₁` is `c₁`), giving the `Z`-leaf cut
                -- `(h₁, h₂) = (r, g₁)`, leaves `a, b`, opposite twin `c₁`, fourth leaf `d = z`.
                have hne_eg₁ : e ≠ g₁ := fun h => by rw [h] at heiso4; omega
                have hg₁notR : g₁ ∉ R := fun hr => by have := hRrich g₁ hr; omega
                have hg₂notR : g₂ ∉ R := fun hr => by have := hRrich g₂ hr; omega
                -- `N(g₁) ∩ Iso = {c₁}` (poor hub: a single twin).
                have hg₁IsoEq : G.neighborFinset g₁ ∩ Iso = {c₁} := by
                  obtain ⟨c', hc'⟩ := Finset.card_eq_one.mp hg₁iso1
                  have hmem : c₁ ∈ G.neighborFinset g₁ ∩ Iso :=
                    Finset.mem_inter.mpr ⟨(G.mem_neighborFinset g₁ c₁).mpr hc₁g.symm, hc₁Iso⟩
                  rw [hc', Finset.mem_singleton] at hmem; rw [hc', hmem]
                -- `|N(g₁) ∩ Hub| ≤ 2`.
                have hg₁hub_le : (G.neighborFinset g₁ ∩ Hub).card ≤ 2 := by
                  have hpg := hpart g₁
                  have hzmem : z ∈ G.neighborFinset g₁ ∩ Z :=
                    Finset.mem_inter.mpr ⟨(G.mem_neighborFinset g₁ z).mpr hzg₁.symm, hzZ⟩
                  have hZpos : 1 ≤ (G.neighborFinset g₁ ∩ Z).card := Finset.card_pos.mpr ⟨z, hzmem⟩
                  rw [hdeg4 g₁ hg₁Hub, hg₁iso1] at hpg; omega
                -- Pigeonhole: a rich `r ≁ g₁` with `c₁ ∉ N(r)`.
                have hexr : ∃ r ∈ R.erase e, ¬G.Adj g₁ r ∧ ¬G.Adj c₁ r := by
                  by_contra hcon
                  push Not at hcon
                  have hsub : R.erase e ⊆ (G.neighborFinset g₁ ∩ Hub)
                      ∪ ((G.neighborFinset c₁ ∩ Hub) \ {e, g₁}) := by
                    intro r hr
                    have hrR : r ∈ R := Finset.mem_of_mem_erase hr
                    have hrne : r ≠ e := Finset.ne_of_mem_erase hr
                    have hrHub : r ∈ Hub := hRsub hrR
                    by_cases hg : G.Adj g₁ r
                    · exact Finset.mem_union_left _
                        (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset g₁ r).mpr hg, hrHub⟩)
                    · have hc := hcon r hr hg
                      refine Finset.mem_union_right _ (Finset.mem_sdiff.mpr
                        ⟨Finset.mem_inter.mpr ⟨(G.mem_neighborFinset c₁ r).mpr hc, hrHub⟩, ?_⟩)
                      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
                      exact ⟨hrne, fun he => hg₁notR (he ▸ hrR)⟩
                  have hcard := Finset.card_le_card hsub
                  rw [Finset.card_erase_of_mem heR, hr5] at hcard
                  have hu := Finset.card_union_le (G.neighborFinset g₁ ∩ Hub)
                    ((G.neighborFinset c₁ ∩ Hub) \ {e, g₁})
                  have hsdiff_le : ((G.neighborFinset c₁ ∩ Hub) \ {e, g₁}).card ≤ 1 := by
                    have heg₁sub : ({e, g₁} : Finset (Fin 19)) ⊆ G.neighborFinset c₁ ∩ Hub := by
                      intro x hx
                      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
                      rcases hx with rfl | rfl
                      · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr h1.symm, heHub⟩
                      · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hc₁g, hg₁Hub⟩
                    have hcardeg : ({e, g₁} : Finset (Fin 19)).card = 2 := by
                      rw [Finset.card_insert_of_notMem (by simp [hne_eg₁]), Finset.card_singleton]
                    have hcs := Finset.card_sdiff_add_card_inter
                      (G.neighborFinset c₁ ∩ Hub) ({e, g₁} : Finset (Fin 19))
                    have hinter : (G.neighborFinset c₁ ∩ Hub) ∩ ({e, g₁} : Finset (Fin 19))
                        = {e, g₁} := Finset.inter_eq_right.mpr heg₁sub
                    rw [hinter, hcardeg, hiso3 c₁ hc₁Iso] at hcs; omega
                  omega
                obtain ⟨r, hrErase, hnrg₁, hnrc₁⟩ := hexr
                have hrR : r ∈ R := Finset.mem_of_mem_erase hrErase
                have hrHub : r ∈ Hub := hRsub hrR
                have hr2 : 2 ≤ (G.neighborFinset r ∩ Iso).card := hRrich r hrR
                obtain ⟨a, ha, b, hb, hab⟩ :=
                  Finset.one_lt_card.mp (by omega : 1 < (G.neighborFinset r ∩ Iso).card)
                have haIso : a ∈ Iso := (Finset.mem_inter.mp ha).2
                have hbIso : b ∈ Iso := (Finset.mem_inter.mp hb).2
                have ha_r : G.Adj a r := ((G.mem_neighborFinset r a).mp (Finset.mem_inter.mp ha).1).symm
                have hb_r : G.Adj b r := ((G.mem_neighborFinset r b).mp (Finset.mem_inter.mp hb).1).symm
                have hna_g₁ : ¬G.Adj a g₁ := by
                  intro had
                  have hain : a ∈ G.neighborFinset g₁ ∩ Iso :=
                    Finset.mem_inter.mpr ⟨(G.mem_neighborFinset g₁ a).mpr had.symm, haIso⟩
                  rw [hg₁IsoEq, Finset.mem_singleton] at hain
                  rw [hain] at ha_r; exact hnrc₁ ha_r
                have hnb_g₁ : ¬G.Adj b g₁ := by
                  intro had
                  have hbin : b ∈ G.neighborFinset g₁ ∩ Iso :=
                    Finset.mem_inter.mpr ⟨(G.mem_neighborFinset g₁ b).mpr had.symm, hbIso⟩
                  rw [hg₁IsoEq, Finset.mem_singleton] at hbin
                  rw [hbin] at hb_r; exact hnrc₁ hb_r
                have hn_rz : ¬G.Adj r z := by
                  intro had
                  have hrin : r ∈ G.neighborFinset z ∩ Hub :=
                    Finset.mem_inter.mpr ⟨(G.mem_neighborFinset z r).mpr had.symm, hrHub⟩
                  rw [hNz, Finset.mem_insert, Finset.mem_singleton] at hrin
                  rcases hrin with rfl | rfl
                  · exact hg₁notR hrR
                  · exact hg₂notR hrR
                exact Or.inl (two_hub_zleaf_nineteen G Hub Iso hiso3 hdisj hHub hIso hdsum hdeg3
                  hisodeg3 hleak r g₁ a b c₁ z hrHub hg₁Hub (hdeg4 r hrHub) (hdeg4 g₁ hg₁Hub)
                  haIso hbIso hc₁Iso hzZ ha_r hb_r hc₁g hzg₁ (fun h => hnrg₁ h.symm)
                  (fun h => hnrc₁ h.symm) hn_rz hna_g₁ hnb_g₁ hab)
              · exact hpoorclose g₄ z' c₄ hg₄Hub hz'Z hz'g₄ hc₄Iso hc₄g h4
            · exact hpoorclose g₃ z' c₃ hg₃Hub hz'Z hz'g₃ hc₃Iso hc₃g h3
          · exact hpoorclose g₂ z c₂ hg₂Hub hzZ hzg₂ hc₂Iso hc₂g h2
        · exact hpoorclose g₁ z c₁ hg₁Hub hzZ hzg₁ hc₁Iso hc₁g h1
      · -- `|S| = 2` ⟹ the `{2, 2, 2, 3, 3}` multiset: two adjacent iso-degree-`3` rich hubs sharing
        -- no twin, so `g₁`'s twin is non-adjacent to at least one of them.
        have hScard2 : S.card = 2 := by omega
        obtain ⟨h, h', hhne, hSeq⟩ := Finset.card_eq_two.mp hScard2
        have hhS : h ∈ S := by rw [hSeq]; exact Finset.mem_insert_self _ _
        have hh'S : h' ∈ S := by rw [hSeq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
        rw [hSdef, Finset.mem_filter] at hhS hh'S
        obtain ⟨hhR, hh3⟩ := hhS
        obtain ⟨hh'R, hh'3⟩ := hh'S
        have hhHub : h ∈ Hub := hRsub hhR
        have hh'Hub : h' ∈ Hub := hRsub hh'R
        have hdh : G.degree h = 4 := hdeg4 h hhHub
        have hdh' : G.degree h' = 4 := hdeg4 h' hh'Hub
        -- The two iso-degree-`3` hubs are adjacent.
        have hadjhh' : G.Adj h h' :=
          rich_isodeg3_pair_adj_r5_nineteen G Hub Iso hshare hno2hub h h' hhHub hh'Hub hdh hdh'
            hhne hh3 hh'3
        -- Saturation: each one's sole hub-neighbour is the other; no `Z`-neighbour.
        obtain ⟨hHub1, hHubZ0, hh'inNh⟩ := hF1 h h' hhHub hh3 hadjhh' hh'Hub
        obtain ⟨h'Hub1, h'HubZ0, hhinNh'⟩ := hF1 h' h hh'Hub hh'3 hadjhh'.symm hhHub
        -- No shared twin (the good triangle `h–h'–t` of degree sum `11` is excluded).
        have hnoshare : (G.neighborFinset h ∩ G.neighborFinset h' ∩ Iso) = ∅ := by
          rw [Finset.eq_empty_iff_forall_notMem]
          intro t ht
          rw [Finset.mem_inter, Finset.mem_inter, G.mem_neighborFinset, G.mem_neighborFinset] at ht
          obtain ⟨⟨hth, hth'⟩, htIso⟩ := ht
          have htnotHub : t ∉ Hub := fun he => Finset.disjoint_left.mp hdisj he htIso
          have hht : h ≠ t := fun he => htnotHub (he ▸ hhHub)
          have hh't : h' ≠ t := fun he => htnotHub (he ▸ hh'Hub)
          exact hT ⟨h, h', t, hhne, hh't, hht, hadjhh', hth', hth, by
            rw [hdh, hdh', hisodeg3 t htIso]⟩
        -- `g₁`'s unique twin `c`.
        obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hg₁iso1
        have hcmem : c ∈ G.neighborFinset g₁ ∩ Iso := by rw [hc]; exact Finset.mem_singleton_self _
        rw [Finset.mem_inter, G.mem_neighborFinset] at hcmem
        obtain ⟨hcg₁, hcIso⟩ := hcmem
        -- `c` is non-adjacent to at least one of `h, h'`.
        have hcdisj : ¬G.Adj h c ∨ ¬G.Adj h' c := by
          by_contra hcon
          push Not at hcon
          obtain ⟨hch, hch'⟩ := hcon
          have : c ∈ G.neighborFinset h ∩ G.neighborFinset h' ∩ Iso :=
            Finset.mem_inter.mpr ⟨Finset.mem_inter.mpr
              ⟨(G.mem_neighborFinset h c).mpr hch, (G.mem_neighborFinset h' c).mpr hch'⟩, hcIso⟩
          rw [hnoshare] at this; exact Finset.notMem_empty c this
        -- `g₁ ≠ h'` and `g₁ ≠ h` (poor vs rich).
        have hg₁neh : h ≠ g₁ := by intro he; rw [he] at hh3; omega
        have hg₁neh' : h' ≠ g₁ := by intro he; rw [he] at hh'3; omega
        -- `h₁ ≁ g₁` for a hub whose sole hub-neighbour `o ≠ g₁`.
        have hsole_nonadj : ∀ h₁ o : Fin 19, (G.neighborFinset h₁ ∩ Hub).card = 1 →
            o ∈ G.neighborFinset h₁ ∩ Hub → o ≠ g₁ → ¬G.Adj h₁ g₁ := by
          intro h₁ o ho1 homem hog₁ hadj
          have hg₁in : g₁ ∈ G.neighborFinset h₁ ∩ Hub :=
            Finset.mem_inter.mpr ⟨(G.mem_neighborFinset h₁ g₁).mpr hadj, hg₁Hub⟩
          obtain ⟨w, hw⟩ := Finset.card_eq_one.mp ho1
          rw [hw, Finset.mem_singleton] at hg₁in homem
          exact hog₁ (homem.trans hg₁in.symm)
        -- `h₁ ≁ z` for a hub with no `Z`-neighbour.
        have hnoZ_nonadj : ∀ h₁ : Fin 19, (G.neighborFinset h₁ ∩ Z).card = 0 → ¬G.Adj h₁ z := by
          intro h₁ hZ0 hadj
          have : z ∈ G.neighborFinset h₁ ∩ Z :=
            Finset.mem_inter.mpr ⟨(G.mem_neighborFinset h₁ z).mpr hadj, hzZ⟩
          rw [Finset.card_eq_zero] at hZ0; rw [hZ0] at this; exact Finset.notMem_empty z this
        -- Reusable closer for a chosen `h₁ ∈ {h, h'}`.
        have hclose : ∀ h₁ : Fin 19, h₁ ∈ Hub → G.degree h₁ = 4 →
            3 ≤ (G.neighborFinset h₁ ∩ Iso).card → h₁ ≠ g₁ →
            ¬G.Adj h₁ g₁ → ¬G.Adj h₁ z → ¬G.Adj h₁ c → ZPoorCutConfig G := by
          intro h₁ hh₁Hub hdh₁ hh₁3 hh₁g₁ hn1g₁ hn1z hh₁c
          -- Two private twins of `h₁`.
          obtain ⟨a, b, haIso, hbIso, hab, ha1, hb1, hag₁, hbg₁⟩ :=
            exists_two_private_twins_nineteen G Hub Iso hshare h₁ g₁ hh₁Hub hg₁Hub hdh₁
              (hdeg4 g₁ hg₁Hub) hh₁g₁ hn1g₁ hh₁3
          refine Or.inl (two_hub_zleaf_nineteen G Hub Iso hiso3 hdisj hHub hIso hdsum hdeg3 hisodeg3
            hleak h₁ g₁ a b c z hh₁Hub hg₁Hub hdh₁ (hdeg4 g₁ hg₁Hub) haIso hbIso hcIso hzZ
            ha1 hb1 hcg₁.symm hzg₁ hn1g₁ hh₁c hn1z hag₁ hbg₁ hab)
        rcases hcdisj with hch | hch'
        · exact hclose h hhHub hdh hh3 hg₁neh
            (hsole_nonadj h h' hHub1 hh'inNh hg₁neh') (hnoZ_nonadj h hHubZ0) hch
        · exact hclose h' hh'Hub hdh' hh'3 hg₁neh'
            (hsole_nonadj h' h h'Hub1 hhinNh' hg₁neh) (hnoZ_nonadj h' h'HubZ0) hch'


end N19

end ACMax
