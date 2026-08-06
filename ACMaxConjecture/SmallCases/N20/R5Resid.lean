import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N20.Core
import ACMaxConjecture.SmallCases.N20.TwoHubSelect
import ACMaxConjecture.SmallCases.N20.StarTriangleStruct
import ACMaxConjecture.SmallCases.N20.OctahedronForce
import ACMaxConjecture.SmallCases.N20.R5Octahedron
import ACMaxConjecture.SmallCases.N20.R5ResidHelpers
import ACMaxConjecture.SmallCases.N20.Core
import ACMaxConjecture.SmallCases.StarCertificates

/-!
# The `r = 5`, `S = 12` octahedron residual (`n = 20`, `|Hub| = 12`)

This file discharges the threaded hypothesis `hoct5` of `rich_count_ge_six_twenty` (the `r = 5`
exclusion at `|Hub| = 12`): writing `R = {h ∈ Hub : 2 ≤ |N(h) ∩ Iso|}` for the rich hubs, the
profile `|R| = 5` with `∑_{r∈R} |N(r) ∩ Iso| = 12` is a residual that the `n = 18`-style
two-hub extraction in `rich_count_ge_six_twenty` cannot reach.  (At `n = 20` the poor side widens
to `12 − r` hubs, so the extraction's survivor set is larger than at `n = 19`; this file handles
exactly the `(r, S) = (5, 12)` profile threaded as `hoct5`.)

## The two residual iso-degree multisets

With `|R| = 5`, every rich hub has iso-degree in `{2, 3, 4}` and the `5` values sum to `12`; the
no-two-hub bound (`rich_a3_count_le_two_twenty`) caps the number of iso-degree-`≥ 3` rich hubs at
`2`.  The only solutions are

* `{2, 2, 2, 3, 3}` — no iso-degree-`4` hub (the *468-survivor family* recorded in
  `TwinCert20OctahedronForce`); and
* `{4, 2, 2, 2, 2}` — one iso-degree-`4` hub `a` (with `N(a) ⊆ Iso`, non-adjacent to every hub) but
  no second iso-degree-`≥ 3` hub.

The poor side `P = Hub \ R` has `7` hubs carrying iso-incidence `18 − 12 = 6` — the `n = 20` shift:
the `n = 19` exact pigeonhole (`6` incidences over `6` poor hubs, forcing `hnozero`) is gone, and
instead **exactly one** poor hub may be iso-free while the other six carry exactly `1`.  What
survives (and is all the proof needs) is `hnottwo0`: **no two distinct poor hubs are iso-free**
(two zeros would drop the poor sum to `≤ 5 < 6`).

## Reductions proved here (axiom-clean)

`r5_resid_twenty` establishes, from `r = 5` and `S = 12`:

* `hnottwo0`: no two distinct poor hubs are iso-free (so on each `M`-end's two poor hub-neighbours
  at least one has iso-degree exactly `1` — the `n = 20` replacement for the `n = 19` `hnozero`);
* `hRcard : R.card = 5`, `hS12`, and `ha3 : (#rich with iso-degree ≥ 3) ≤ 2` — the precise
  characterisation of the residual.

## The cross-edge `C₄` dispatch (axiom-clean)

The proof extracts the two `M`-edge endpoints `Z = {z, z'}` (`z ∼ z'`) and their hub-neighbours
`g₁, g₂ = N(z) ∩ Hub`, `g₃, g₄ = N(z') ∩ Hub` (all available NON-circularly from
`z_two_hub_nbrs_twenty` / `z_card_two_twenty`, no `hztwopoor`), and **case-splits on whether any
cross edge `gᵢ ∼ gⱼ` exists** (`i ∈ {1,2}`, `j ∈ {3,4}`).  If so, the `4`-cycle `z – gᵢ – gⱼ – z'` is
a good `C₄` of degree sum `3 + 4 + 4 + 3 = 14` whose diagonals are forced non-adjacent (no hub meets
both `M`-endpoints — `no_hub_adj_both_mends_twenty`), contradicting `hC4`
(`cross_z_hub_c4_false_twenty` in `TwinCert20R5ResidHelpers`).  This **closes the cross-edge case
of BOTH multisets axiom-clean.**

## The no-cross residual — CLOSED in three branches

In the no-cross case the four `Z`-hubs form an independent `4`-set.  Let `z_R` be the number of these
four `Z`-hubs that are *rich* (iso-degree `≥ 2`), and let `S = {h ∈ R : iso-degree ≥ 3}`
(`1 ≤ |S| ≤ 2`).  The proof closes the no-cross case by the reusable `Z`-leaf two-hub assembler
`two_hub_zleaf_twenty` (a `TwoHubConfig` whose fourth leaf `d = z` is an `M`-edge endpoint,
invisible to the `Iso`-only `hno2hub`), in three branches — all fully axiom-clean:

* **`z_R ≥ 1` (any rich `Z`-hub, BOTH multisets) — CLOSED.**  A rich `Z`-hub `h₂` has at most one
  hub-neighbour (`2` twins `+` an `M`-edge `+` `≤ 1` hub fills its degree `4`).  An iso-degree-`≥ 3`
  rich hub `h₁ ≁ h₂` always exists (`hfindh1`: if `|S| = 1` the lone hub is iso-degree-`4` with
  `N ⊆ Iso`, so `≁` every hub; if `|S| = 2` the two iso-degree-`3` hubs are each other's sole
  hub-neighbour, so neither meets the `Z`-hub `h₂`).  Then `hshare` yields two private twins `a, b`
  of `h₁` and one private twin `c` of `h₂`; with `d = z` this is a `TwoHubConfig`.

* **`z_R = 0`, `|S| = 2` (`{2,2,2,3,3}`) — CLOSED.**  The two iso-degree-`3` rich hubs `h, h'` are
  *adjacent* (`rich_isodeg3_pair_adj_r5_twenty`), so they share **no** twin (the triangle
  `h–h'–t`, degree sum `4 + 4 + 3 = 11`, is excluded by `hT`).  Hence the unique twin `c` of the
  selected iso-degree-`1` poor `Z`-hub `gsel` (see below) is non-adjacent to at least one of
  `h, h'`; that hub plays `h₁`, `gsel` plays `h₂`, `d = z`, giving a `TwoHubConfig`.

* **`z_R = 0`, `|S| = 1` (`{4,2,2,2,2}`) — CLOSED (axiom-clean, no `StarTriangleConfig` needed).**
  The lone iso-degree-`4` hub `a*` has `N(a*) ⊆ Iso` (`≁` every hub and `Z`).  When `gsel`'s unique
  twin `c` is non-adjacent to `a*`, the cut `(h₁, h₂) = (a*, gsel)`, `c`, `d = z` is a
  `TwoHubConfig`; the surviving twin-adjacent sub-case (`c ∼ a*`) is closed by the **same
  `two_hub_zleaf` assembler with a *rich* hub `r ∈ R \ {a*}` in the role of `h₁`** (see below).

## The `n = 20` `gsel` selection

Both branches of `z_R = 0` need one poor `Z`-hub with a twin.  At `n = 19` every poor hub had one
(`hnozero`); at `n = 20` a single poor hub may be iso-free, but the two `z`-side hubs `g₁, g₂` are
*distinct* poor hubs, so by `hnottwo0` at least one has iso-degree exactly `1` — it is selected as
`gsel` and the whole `z_R = 0` case runs on `(gsel, z)`.

## Why the twin-adjacent corner does NOT need a star-triangle

`two_hub_zleaf_twenty` only requires `h₁` to carry **two private twins** — it does *not* require
`h₁` to have iso-degree `≥ 3`.  Fix `gsel` (unique twin `c₁`, `c₁ ∼ a*` in the corner).  Of the
four hubs `R \ {a*}` (each iso-degree exactly `2`): at most `2` are adjacent to `gsel`
(its hub-degree is `≤ 2`, since degree `4 = 1` iso `+ ≥ 1` `Z` `+` hub) and at most `1` carries
`c₁` as a twin (`c₁` has degree `3`, hub-neighbours `a*, gsel, w`).  Hence `4 − 2 − 1 ≥ 1` rich
hub `r` satisfies `r ≁ gsel` and `c₁ ∉ N(r)`; its two twins `a, b` are then both `≁ gsel` (the
*only* twin of `gsel` is `c₁`), giving the `Z`-leaf cut `(h₁, h₂) = (r, gsel)`, leaves `a, b`,
opposite twin `c₁`, fourth leaf `d = z` — a `TwoHubConfig`.  The earlier framing (which expected
this corner to require a forced hub-triangle / `StarTriangleConfig`) was unnecessarily restrictive:
the pigeonhole over the rich pool always supplies a usable `h₁`.  `ZPoorCutConfig` retains
`StarTriangleConfig` as a disjunct purely for interface compatibility; the `r = 5` residual never
invokes it. -/

namespace ACMax

open scoped Classical

namespace N20

/-- **The `r = 5`, `S = 12` octahedron residual (`n = 20`, `|Hub| = 12`).**  Supplies the threaded
`hoct5` hypothesis of `rich_count_ge_six_twenty`: the `(r, S) = (5, 12)` profile yields a
`ZPoorCutConfig` — the cross-edge case by a good-`C₄` contradiction, the no-cross case by the
`Z`-leaf two-hub assembler (see the module docstring). -/
theorem r5_resid_twenty (G : SimpleGraph (Fin 20)) (Hub Iso : Finset (Fin 20))
    (hdeg4 : ∀ h ∈ Hub, G.degree h = 4)
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hdisj : Disjoint Hub Iso) (hHub : Hub.card = 12) (hIso : Iso.card = 6)
    (hdeg3 : ∀ v : Fin 20, 3 ≤ G.degree v) (hisodeg3 : ∀ t ∈ Iso, G.degree t = 3)
    (hdsum : ∑ w ∈ Hub, G.degree w = 48)
    (hleak : ∑ h ∈ Hub, (G.neighborFinset h ∩ (Finset.univ \ (Hub ∪ Iso))).card ≤ 4)
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hno2hub : ¬∃ h₁ h₂ : Fin 20, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card)
    (hC4 : ¬∃ a b c d : Fin 20, ({a, b, c, d} : Finset (Fin 20)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (_hK23 : ¬∃ a b c d e : Fin 20, ({a, b, c, d, e} : Finset (Fin 20)).card = 5 ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
      G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 19)
    (hT : ¬∃ x y z : Fin 20, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧
      G.degree x + G.degree y + G.degree z ≤ 11) :
    (Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)).card = 5 →
      (∑ a ∈ Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card),
          (G.neighborFinset a ∩ Iso).card) = 12 → ZPoorCutConfig G := by
  classical
  intro hr5 hS12
  set R : Finset (Fin 20) := Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card) with hRdef
  have hRsub : R ⊆ Hub := Finset.filter_subset _ _
  -- Total iso-incidence `= 18`.
  have hsum18 : ∑ a ∈ Hub, (G.neighborFinset a ∩ Iso).card = 18 := by
    have := hub_iso_sum_twenty G Hub Iso hiso3; rw [hIso] at this; omega
  -- The complement (poor side) `P` carries `18 − 12 = 6` incidences over `12 − 5 = 7` hubs.
  set P : Finset (Fin 20) := Hub.filter (fun h => ¬ 2 ≤ (G.neighborFinset h ∩ Iso).card) with hPdef
  have hPcard : P.card = 7 := by
    have := Finset.card_filter_add_card_filter_not (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card)
      (s := Hub)
    rw [← hRdef, ← hPdef, hHub, hr5] at this; omega
  have hsplit : (∑ a ∈ R, (G.neighborFinset a ∩ Iso).card)
      + ∑ a ∈ P, (G.neighborFinset a ∩ Iso).card = 18 := by
    rw [hRdef, hPdef, Finset.sum_filter_add_sum_filter_not Hub _]; exact hsum18
  have hPsum : ∑ a ∈ P, (G.neighborFinset a ∩ Iso).card = 6 := by rw [hS12] at hsplit; omega
  -- Each poor hub has iso-degree `≤ 1`; the sum `6` over the `7` poor hubs allows ONE iso-free
  -- poor hub (the `n = 20` shift: the `n = 19` exact pigeonhole `6 = |P|` forced `hnozero`) — but
  -- never TWO (two zeros would drop the poor sum to `≤ 5 < 6`).
  have hPle1 : ∀ g ∈ P, (G.neighborFinset g ∩ Iso).card ≤ 1 := by
    intro g hg; rw [hPdef, Finset.mem_filter] at hg; omega
  have hnottwo0 : ∀ g ∈ P, ∀ g' ∈ P, g ≠ g' →
      1 ≤ (G.neighborFinset g ∩ Iso).card ∨ 1 ≤ (G.neighborFinset g' ∩ Iso).card := by
    intro g hg g' hg' hne
    by_contra hcon
    push Not at hcon
    obtain ⟨h0, h0'⟩ := hcon
    have hg'e : g' ∈ P.erase g := Finset.mem_erase.mpr ⟨hne.symm, hg'⟩
    have hsub : ∑ a ∈ P, (G.neighborFinset a ∩ Iso).card
        = (G.neighborFinset g ∩ Iso).card
          + ∑ a ∈ P.erase g, (G.neighborFinset a ∩ Iso).card :=
      (Finset.add_sum_erase P _ hg).symm
    have hsub' : ∑ a ∈ P.erase g, (G.neighborFinset a ∩ Iso).card
        = (G.neighborFinset g' ∩ Iso).card
          + ∑ a ∈ (P.erase g).erase g', (G.neighborFinset a ∩ Iso).card :=
      (Finset.add_sum_erase (P.erase g) _ hg'e).symm
    have hbound : ∑ a ∈ (P.erase g).erase g', (G.neighborFinset a ∩ Iso).card
        ≤ ((P.erase g).erase g').card := by
      calc ∑ a ∈ (P.erase g).erase g', (G.neighborFinset a ∩ Iso).card
          ≤ ∑ _a ∈ (P.erase g).erase g', 1 :=
            Finset.sum_le_sum (fun a ha =>
              hPle1 a (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase ha)))
        _ = ((P.erase g).erase g').card := by rw [Finset.sum_const, smul_eq_mul, mul_one]
    rw [Finset.card_erase_of_mem hg'e, Finset.card_erase_of_mem hg, hPcard] at hbound
    omega
  -- At most two rich hubs have iso-degree `≥ 3` (no-two-hub bound).
  have ha3 : (R.filter (fun h => 3 ≤ (G.neighborFinset h ∩ Iso).card)).card ≤ 2 := by
    have heq : R.filter (fun h => 3 ≤ (G.neighborFinset h ∩ Iso).card)
        = Hub.filter (fun h => G.degree h = 4 ∧ 3 ≤ (G.neighborFinset h ∩ Iso).card) := by
      rw [hRdef, Finset.filter_filter]; apply Finset.filter_congr
      intro a ha; constructor
      · rintro ⟨_, h3⟩; exact ⟨hdeg4 a ha, h3⟩
      · rintro ⟨_, h3⟩; exact ⟨by omega, h3⟩
    rw [heq]; exact rich_a3_count_le_two_twenty G Hub Iso hdisj hshare hno2hub
  -- **R=5 rigidity:** the two iso-degree-`3` rich hubs (in the `{2,2,2,3,3}` multiset) are *adjacent*
  -- (two non-adjacent iso-degree-`≥ 3` hubs would keep `≥ 2` private twins each, contradicting
  -- `hno2hub`).  Each is then degree-`4`-saturated by its three twins plus the other, so it has no
  -- poor / `Z` neighbour.
  have _hr3adj := rich_isodeg3_pair_adj_r5_twenty G Hub Iso hshare hno2hub
  -- ===== Cross-edge `C₄` dispatch (axiom-clean, non-circular). =====
  -- Extract the two `M`-edge endpoints `Z = {z, z'}` and their hub-neighbours, then case-split on
  -- whether a hub-neighbour of `z` is adjacent to a hub-neighbour of `z'`.  If so, the `4`-cycle
  -- `z – gᵢ – gⱼ – z'` is a good `C₄` (`cross_z_hub_c4_false_twenty`, degree sum `3+4+4+3 = 14`,
  -- both diagonals forced non-adjacent because no hub meets both `M`-endpoints), contradicting `hC4`
  -- and discharging the goal vacuously.  This closes EVERY graph carrying such a cross edge
  -- (structured enumeration: `5415` of the `8295` in-regime `{2,2,2,3,3}` realisations,
  -- `scratchpad/r5cross.py`/`r5cat.py`).
  set Z : Finset (Fin 20) := Finset.univ \ (Hub ∪ Iso) with hZdef
  have hZcard : Z.card = 2 := z_card_two_twenty Hub Iso hdisj hHub hIso
  obtain ⟨z, z', hzz', hZpair⟩ := Finset.card_eq_two.mp hZcard
  have hzZ : z ∈ Z := by rw [hZpair]; exact Finset.mem_insert_self _ _
  have hz'Z : z' ∈ Z := by
    rw [hZpair]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  obtain ⟨_, hzhub2, _⟩ :=
    z_two_hub_nbrs_twenty G Hub Iso hiso3 hdisj hHub hIso hdsum hdeg3 hisodeg3 hleak z hzZ
  obtain ⟨g₁, g₂, hg₁g₂, hNz⟩ := Finset.card_eq_two.mp hzhub2
  obtain ⟨_, hz'hub2, _⟩ :=
    z_two_hub_nbrs_twenty G Hub Iso hiso3 hdisj hHub hIso hdsum hdeg3 hisodeg3 hleak z' hz'Z
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
  have hkill : ∀ g g' : Fin 20, g ∈ Hub → g' ∈ Hub → G.Adj z g → G.Adj z' g' → G.Adj g g' →
      ZPoorCutConfig G := fun g g' hg hg' hzg hz'g' hcr =>
    (cross_z_hub_c4_false_twenty G Hub Iso hdeg4 hiso3 hdisj hHub hIso hdsum hdeg3 hisodeg3 hleak
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
    -- `z_hubs_nonadj_twenty`, the cross pairs by `hcross`).
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
    -- and **`z` meets no twin** (`z_two_hub_nbrs_twenty`), every leaf–leaf and leaf–`z`
    -- non-adjacency of `TwoHubConfig` (`¬Adj a c`, `¬Adj a d`, `¬Adj b c`, `¬Adj b d`) holds *for
    -- free*; the remaining conditions reduce to: `h₁ ≁ h₂`, `a, b ≁ h₂`, `c, z ≁ h₁`, plus distinctness.
    --
    -- The `h₁` SIDE IS STRUCTURALLY SOLID.  An iso-degree-`≥ 3` rich hub `h₁` is **saturated** (its
    -- `≥ 3` twins plus, in `{2,2,2,3,3}`, the other iso-degree-`3` hub fill degree `4`;
    -- `rich_isodeg3_pair_adj_r5_twenty`), hence has **no `Z`-neighbour**, so `h₁ ≁` every `Z`-hub
    -- `gᵢ` (each `gᵢ` meets `z`); and `h₁` shares `≤ 1` twin with any non-adjacent hub (`hshare`), so it
    -- retains `≥ 2` private twins `a, b` against any `gᵢ`.  (In `{4,2,2,2,2}` the iso-degree-`4` hub
    -- `a`, with `N(a) ⊆ Iso`, plays `h₁`.)
    --
    -- The remaining gap is the `h₂` side: a `Z`-hub with a twin `c ≁ h₁`.  A **rich** `Z`-hub
    -- (`≥ 2` twins, `≤ 1` shared with `h₁` by `hshare`) ALWAYS supplies `c` — so **`z_R ≥ 1` closes the
    -- no-cross case cleanly** (the witness has `z_R = 2`, `h₂ = 2` a rich `Z`-hub).  The sub-case
    -- **`z_R = 0`** (all four `Z`-hubs poor, iso-degree `≤ 1`; at `n = 20` an iso-degree-`1`
    -- `z`-side hub `gsel` is selected via `hnottwo0`) is ALSO closed (axiom-clean): for
    -- `|S| = 2` via the adjacent iso-degree-`3` pair (they share no twin, so `gsel`'s twin avoids one
    -- of them); for `|S| = 1` (`{4,2,2,2,2}`), even when `gsel`'s twin is adjacent to `a*`, a
    -- pigeonhole over the four rich hubs `R \ {a*}` supplies a *rich* `h₁ = r ≁ gsel` with
    -- `c₁ ∉ N(r)` (`r` has two twins, both private to `gsel`), giving a `two_hub_zleaf`
    -- `TwoHubConfig` — no star-triangle needed.  See the module docstring.
    have _hg₁₃ : ¬G.Adj g₁ g₃ := fun h => hcross (Or.inl h)
    have _hg₁₄ : ¬G.Adj g₁ g₄ := fun h => hcross (Or.inr (Or.inl h))
    have _hg₂₃ : ¬G.Adj g₂ g₃ := fun h => hcross (Or.inr (Or.inr (Or.inl h)))
    have _hg₂₄ : ¬G.Adj g₂ g₄ := fun h => hcross (Or.inr (Or.inr (Or.inr h)))
    -- ===== Structural layer for the iso-degree-`≥ 3` rich hubs `S`. =====
    set S : Finset (Fin 20) := R.filter (fun h => 3 ≤ (G.neighborFinset h ∩ Iso).card) with hSdef
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
    have hpart : ∀ v : Fin 20, (G.neighborFinset v ∩ Hub).card + (G.neighborFinset v ∩ Iso).card
        + (G.neighborFinset v ∩ Z).card = G.degree v := by
      intro v; rw [hZdef]; exact nbr_split_three_twenty G Hub Iso hdisj v
    -- **Saturation of an iso-degree-`≥ 3` hub adjacent to another hub** (`F1`): its sole hub-neighbour
    -- is that hub and it has no `Z`-neighbour.
    have hF1 : ∀ u v : Fin 20, u ∈ Hub → 3 ≤ (G.neighborFinset u ∩ Iso).card → G.Adj u v →
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
    have hfindh1 : ∀ h₂ zz : Fin 20, h₂ ∈ Hub → zz ∈ Z → G.Adj zz h₂ →
        ∃ h₁ : Fin 20, h₁ ∈ Hub ∧ G.degree h₁ = 4 ∧ 3 ≤ (G.neighborFinset h₁ ∩ Iso).card ∧
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
          rw [hrest, hS12] at hae
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
          rich_isodeg3_pair_adj_r5_twenty G Hub Iso hshare hno2hub h h' hhHub hh'Hub
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
      have hcloseR : ∀ h₂ zz : Fin 20, h₂ ∈ Hub → zz ∈ Z → G.Adj zz h₂ →
          2 ≤ (G.neighborFinset h₂ ∩ Iso).card → ZPoorCutConfig G := by
        intro h₂ zz hh₂Hub hzzZ hzz2 hh₂rich
        obtain ⟨h₁, hh₁Hub, hdh₁, hh₁3, hh₁ne, hn1₂, hh₁noZ⟩ := hfindh1 h₂ zz hh₂Hub hzzZ hzz2
        obtain ⟨a, b, haIso, hbIso, hab, ha1, hb1, ha2, hb2⟩ :=
          exists_two_private_twins_twenty G Hub Iso hshare h₁ h₂ hh₁Hub hh₂Hub hdh₁
            (hdeg4 h₂ hh₂Hub) hh₁ne hn1₂ hh₁3
        obtain ⟨c, hcIso, hc2, hn1c⟩ :=
          exists_one_private_twin_twenty G Hub Iso hshare h₂ h₁ hh₂Hub hh₁Hub
            (hdeg4 h₂ hh₂Hub) hdh₁ hh₁ne hn1₂ hh₂rich
        exact Or.inl (two_hub_zleaf_twenty G Hub Iso hiso3 hdisj hHub hIso hdsum hdeg3 hisodeg3
          hleak h₁ h₂ a b c zz hh₁Hub hh₂Hub hdh₁ (hdeg4 h₂ hh₂Hub) haIso hbIso hcIso hzzZ
          ha1 hb1 hc2 hzz2 hn1₂ hn1c (hh₁noZ zz hzzZ) ha2 hb2 hab)
      rcases hzR with hp | hp | hp | hp
      · exact hcloseR g₁ z hg₁Hub hzZ hzg₁ hp
      · exact hcloseR g₂ z hg₂Hub hzZ hzg₂ hp
      · exact hcloseR g₃ z' hg₃Hub hz'Z hz'g₃ hp
      · exact hcloseR g₄ z' hg₄Hub hz'Z hz'g₄ hp
    · -- **`z_R = 0`:** all four `Z`-hubs are poor (iso-degree `≤ 1`).  At `n = 20` a single poor
      -- hub may be iso-free, but not two (`hnottwo0`); since the two `z`-side hubs `g₁, g₂` are
      -- distinct poor hubs, at least one has iso-degree exactly `1` — select it as `gsel`.
      push Not at hzR
      obtain ⟨hp1, hp2, -, -⟩ := hzR
      have hg₁P : g₁ ∈ P := by rw [hPdef, Finset.mem_filter]; exact ⟨hg₁Hub, by omega⟩
      have hg₂P : g₂ ∈ P := by rw [hPdef, Finset.mem_filter]; exact ⟨hg₂Hub, by omega⟩
      obtain ⟨gsel, hgselHub, hzgsel, hgseliso1⟩ :
          ∃ g : Fin 20, g ∈ Hub ∧ G.Adj z g ∧ (G.neighborFinset g ∩ Iso).card = 1 := by
        rcases hnottwo0 g₁ hg₁P g₂ hg₂P hg₁g₂ with h | h
        · exact ⟨g₁, hg₁Hub, hzg₁, by omega⟩
        · exact ⟨g₂, hg₂Hub, hzg₂, by omega⟩
      rcases Nat.lt_or_ge S.card 2 with hS1 | hS2
      · -- `|S| = 1` ⟹ the `{4, 2, 2, 2, 2}` multiset; the single iso-degree-`4` hub `a* = e` with
        -- `N(a*) ⊆ Iso` (non-adjacent to every hub and `Z`).  When `gsel`'s twin is non-adjacent
        -- to `a*`, the `TwoHubConfig` `Z`-leaf cut (`h₁ = a*`, `h₂ = gsel`, `c` its twin, `d = z`)
        -- closes the case; otherwise the twin-adjacent corner is closed by a pigeonhole over the
        -- four rich hubs `R \ {a*}` (no `StarTriangleConfig` needed).
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
          rw [hrest, hS12] at hae
          omega
        have heNIso : G.neighborFinset e ⊆ Iso := by
          have hcardN : (G.neighborFinset e).card = 4 := by rw [G.card_neighborFinset_eq_degree, hde]
          have heq : G.neighborFinset e ∩ Iso = G.neighborFinset e :=
            Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by rw [heiso4, hcardN])
          rw [← heq]; exact Finset.inter_subset_right
        -- Closer for a poor `Z`-hub `g` (`M`-end `zz`) whose twin `c` is non-adjacent to `a* = e`.
        have hpoorclose : ∀ g zz c : Fin 20, g ∈ Hub → zz ∈ Z → G.Adj zz g →
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
            exists_two_private_twins_twenty G Hub Iso hshare e g heHub hgHub hde
              (hdeg4 g hgHub) hne_eg hn_eg (by omega)
          exact Or.inl (two_hub_zleaf_twenty G Hub Iso hiso3 hdisj hHub hIso hdsum hdeg3 hisodeg3
            hleak e g a b c zz heHub hgHub hde (hdeg4 g hgHub) haIso hbIso hcIso hzzZ
            ha1 hb1 hcg hzzg hn_eg hnec hn_ezz hag hbg hab)
        -- Twin extractor for a poor hub.
        have gettwin : ∀ g : Fin 20, (G.neighborFinset g ∩ Iso).card = 1 →
            ∃ c : Fin 20, c ∈ Iso ∧ G.Adj c g := by
          intro g hg1
          obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hg1
          have hcm : c ∈ G.neighborFinset g ∩ Iso := by rw [hc]; exact Finset.mem_singleton_self _
          rw [Finset.mem_inter, G.mem_neighborFinset] at hcm
          exact ⟨c, hcm.2, hcm.1.symm⟩
        obtain ⟨c₁, hc₁Iso, hc₁g⟩ := gettwin gsel hgseliso1
        by_cases h1 : G.Adj e c₁
        · -- **The twin-adjacent residual — CLOSED via `TwoHubConfig` with a RICH `h₁`.**
          -- `gsel`'s twin being adjacent to `a* = e` only blocks the *`e`*-centred two-hub cut.
          -- But `two_hub_zleaf_twenty` only needs `h₁` to carry two private twins, so a *rich*
          -- iso-degree-`2` hub `r ∈ R \ {e}` serves equally well.  `gsel`'s unique twin is `c₁`.
          -- Of the four hubs `R \ {e}`: at most `2` are adjacent to `gsel` (since
          -- `|N(gsel) ∩ Hub| ≤ 2`) and at most `1` has `c₁` as a twin (`c₁`'s three hub
          -- neighbours are `e, gsel, w`).  Hence some rich `r ≁ gsel` has `c₁ ∉ N(r)`; its two
          -- twins `a, b` are then both `≁ gsel` (the only twin of `gsel` is `c₁`), giving the
          -- `Z`-leaf cut `(h₁, h₂) = (r, gsel)`, leaves `a, b`, opposite twin `c₁`, `d = z`.
          have hne_egsel : e ≠ gsel := fun h => by rw [h] at heiso4; omega
          have hgselnotR : gsel ∉ R := fun hr => by have := hRrich gsel hr; omega
          have hg₁notR : g₁ ∉ R := fun hr => by have := hRrich g₁ hr; omega
          have hg₂notR : g₂ ∉ R := fun hr => by have := hRrich g₂ hr; omega
          -- `N(gsel) ∩ Iso = {c₁}` (poor hub: a single twin).
          have hgselIsoEq : G.neighborFinset gsel ∩ Iso = {c₁} := by
            obtain ⟨c', hc'⟩ := Finset.card_eq_one.mp hgseliso1
            have hmem : c₁ ∈ G.neighborFinset gsel ∩ Iso :=
              Finset.mem_inter.mpr ⟨(G.mem_neighborFinset gsel c₁).mpr hc₁g.symm, hc₁Iso⟩
            rw [hc', Finset.mem_singleton] at hmem; rw [hc', hmem]
          -- `|N(gsel) ∩ Hub| ≤ 2`.
          have hgselhub_le : (G.neighborFinset gsel ∩ Hub).card ≤ 2 := by
            have hpg := hpart gsel
            have hzmem : z ∈ G.neighborFinset gsel ∩ Z :=
              Finset.mem_inter.mpr ⟨(G.mem_neighborFinset gsel z).mpr hzgsel.symm, hzZ⟩
            have hZpos : 1 ≤ (G.neighborFinset gsel ∩ Z).card := Finset.card_pos.mpr ⟨z, hzmem⟩
            rw [hdeg4 gsel hgselHub, hgseliso1] at hpg; omega
          -- Pigeonhole: a rich `r ≁ gsel` with `c₁ ∉ N(r)`.
          have hexr : ∃ r ∈ R.erase e, ¬G.Adj gsel r ∧ ¬G.Adj c₁ r := by
            by_contra hcon
            push Not at hcon
            have hsub : R.erase e ⊆ (G.neighborFinset gsel ∩ Hub)
                ∪ ((G.neighborFinset c₁ ∩ Hub) \ {e, gsel}) := by
              intro r hr
              have hrR : r ∈ R := Finset.mem_of_mem_erase hr
              have hrne : r ≠ e := Finset.ne_of_mem_erase hr
              have hrHub : r ∈ Hub := hRsub hrR
              by_cases hg : G.Adj gsel r
              · exact Finset.mem_union_left _
                  (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset gsel r).mpr hg, hrHub⟩)
              · have hc := hcon r hr hg
                refine Finset.mem_union_right _ (Finset.mem_sdiff.mpr
                  ⟨Finset.mem_inter.mpr ⟨(G.mem_neighborFinset c₁ r).mpr hc, hrHub⟩, ?_⟩)
                simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
                exact ⟨hrne, fun he => hgselnotR (he ▸ hrR)⟩
            have hcard := Finset.card_le_card hsub
            rw [Finset.card_erase_of_mem heR, hr5] at hcard
            have hu := Finset.card_union_le (G.neighborFinset gsel ∩ Hub)
              ((G.neighborFinset c₁ ∩ Hub) \ {e, gsel})
            have hsdiff_le : ((G.neighborFinset c₁ ∩ Hub) \ {e, gsel}).card ≤ 1 := by
              have hegselsub : ({e, gsel} : Finset (Fin 20)) ⊆ G.neighborFinset c₁ ∩ Hub := by
                intro x hx
                simp only [Finset.mem_insert, Finset.mem_singleton] at hx
                rcases hx with rfl | rfl
                · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr h1.symm, heHub⟩
                · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hc₁g, hgselHub⟩
              have hcardeg : ({e, gsel} : Finset (Fin 20)).card = 2 := by
                rw [Finset.card_insert_of_notMem (by simp [hne_egsel]), Finset.card_singleton]
              have hcs := Finset.card_sdiff_add_card_inter
                (G.neighborFinset c₁ ∩ Hub) ({e, gsel} : Finset (Fin 20))
              have hinter : (G.neighborFinset c₁ ∩ Hub) ∩ ({e, gsel} : Finset (Fin 20))
                  = {e, gsel} := Finset.inter_eq_right.mpr hegselsub
              rw [hinter, hcardeg, hiso3 c₁ hc₁Iso] at hcs; omega
            omega
          obtain ⟨r, hrErase, hnrgsel, hnrc₁⟩ := hexr
          have hrR : r ∈ R := Finset.mem_of_mem_erase hrErase
          have hrHub : r ∈ Hub := hRsub hrR
          have hr2 : 2 ≤ (G.neighborFinset r ∩ Iso).card := hRrich r hrR
          obtain ⟨a, ha, b, hb, hab⟩ :=
            Finset.one_lt_card.mp (by omega : 1 < (G.neighborFinset r ∩ Iso).card)
          have haIso : a ∈ Iso := (Finset.mem_inter.mp ha).2
          have hbIso : b ∈ Iso := (Finset.mem_inter.mp hb).2
          have ha_r : G.Adj a r := ((G.mem_neighborFinset r a).mp (Finset.mem_inter.mp ha).1).symm
          have hb_r : G.Adj b r := ((G.mem_neighborFinset r b).mp (Finset.mem_inter.mp hb).1).symm
          have hna_gsel : ¬G.Adj a gsel := by
            intro had
            have hain : a ∈ G.neighborFinset gsel ∩ Iso :=
              Finset.mem_inter.mpr ⟨(G.mem_neighborFinset gsel a).mpr had.symm, haIso⟩
            rw [hgselIsoEq, Finset.mem_singleton] at hain
            rw [hain] at ha_r; exact hnrc₁ ha_r
          have hnb_gsel : ¬G.Adj b gsel := by
            intro had
            have hbin : b ∈ G.neighborFinset gsel ∩ Iso :=
              Finset.mem_inter.mpr ⟨(G.mem_neighborFinset gsel b).mpr had.symm, hbIso⟩
            rw [hgselIsoEq, Finset.mem_singleton] at hbin
            rw [hbin] at hb_r; exact hnrc₁ hb_r
          have hn_rz : ¬G.Adj r z := by
            intro had
            have hrin : r ∈ G.neighborFinset z ∩ Hub :=
              Finset.mem_inter.mpr ⟨(G.mem_neighborFinset z r).mpr had.symm, hrHub⟩
            rw [hNz, Finset.mem_insert, Finset.mem_singleton] at hrin
            rcases hrin with rfl | rfl
            · exact hg₁notR hrR
            · exact hg₂notR hrR
          exact Or.inl (two_hub_zleaf_twenty G Hub Iso hiso3 hdisj hHub hIso hdsum hdeg3
            hisodeg3 hleak r gsel a b c₁ z hrHub hgselHub (hdeg4 r hrHub) (hdeg4 gsel hgselHub)
            haIso hbIso hc₁Iso hzZ ha_r hb_r hc₁g hzgsel (fun h => hnrgsel h.symm)
            (fun h => hnrc₁ h.symm) hn_rz hna_gsel hnb_gsel hab)
        · exact hpoorclose gsel z c₁ hgselHub hzZ hzgsel hc₁Iso hc₁g h1
      · -- `|S| = 2` ⟹ the `{2, 2, 2, 3, 3}` multiset: two adjacent iso-degree-`3` rich hubs sharing
        -- no twin, so `gsel`'s twin is non-adjacent to at least one of them.
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
          rich_isodeg3_pair_adj_r5_twenty G Hub Iso hshare hno2hub h h' hhHub hh'Hub hdh hdh'
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
        -- `gsel`'s unique twin `c`.
        obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hgseliso1
        have hcmem : c ∈ G.neighborFinset gsel ∩ Iso := by rw [hc]; exact Finset.mem_singleton_self _
        rw [Finset.mem_inter, G.mem_neighborFinset] at hcmem
        obtain ⟨hcgsel, hcIso⟩ := hcmem
        -- `c` is non-adjacent to at least one of `h, h'`.
        have hcdisj : ¬G.Adj h c ∨ ¬G.Adj h' c := by
          by_contra hcon
          push Not at hcon
          obtain ⟨hch, hch'⟩ := hcon
          have : c ∈ G.neighborFinset h ∩ G.neighborFinset h' ∩ Iso :=
            Finset.mem_inter.mpr ⟨Finset.mem_inter.mpr
              ⟨(G.mem_neighborFinset h c).mpr hch, (G.mem_neighborFinset h' c).mpr hch'⟩, hcIso⟩
          rw [hnoshare] at this; exact Finset.notMem_empty c this
        -- `gsel ≠ h'` and `gsel ≠ h` (poor vs rich).
        have hgselneh : h ≠ gsel := by intro he; rw [he] at hh3; omega
        have hgselneh' : h' ≠ gsel := by intro he; rw [he] at hh'3; omega
        -- `h₁ ≁ gsel` for a hub whose sole hub-neighbour `o ≠ gsel`.
        have hsole_nonadj : ∀ h₁ o : Fin 20, (G.neighborFinset h₁ ∩ Hub).card = 1 →
            o ∈ G.neighborFinset h₁ ∩ Hub → o ≠ gsel → ¬G.Adj h₁ gsel := by
          intro h₁ o ho1 homem hogsel hadj
          have hgselin : gsel ∈ G.neighborFinset h₁ ∩ Hub :=
            Finset.mem_inter.mpr ⟨(G.mem_neighborFinset h₁ gsel).mpr hadj, hgselHub⟩
          obtain ⟨w, hw⟩ := Finset.card_eq_one.mp ho1
          rw [hw, Finset.mem_singleton] at hgselin homem
          exact hogsel (homem.trans hgselin.symm)
        -- `h₁ ≁ z` for a hub with no `Z`-neighbour.
        have hnoZ_nonadj : ∀ h₁ : Fin 20, (G.neighborFinset h₁ ∩ Z).card = 0 → ¬G.Adj h₁ z := by
          intro h₁ hZ0 hadj
          have : z ∈ G.neighborFinset h₁ ∩ Z :=
            Finset.mem_inter.mpr ⟨(G.mem_neighborFinset h₁ z).mpr hadj, hzZ⟩
          rw [Finset.card_eq_zero] at hZ0; rw [hZ0] at this; exact Finset.notMem_empty z this
        -- Reusable closer for a chosen `h₁ ∈ {h, h'}`.
        have hclose : ∀ h₁ : Fin 20, h₁ ∈ Hub → G.degree h₁ = 4 →
            3 ≤ (G.neighborFinset h₁ ∩ Iso).card → h₁ ≠ gsel →
            ¬G.Adj h₁ gsel → ¬G.Adj h₁ z → ¬G.Adj h₁ c → ZPoorCutConfig G := by
          intro h₁ hh₁Hub hdh₁ hh₁3 hh₁gsel hn1gsel hn1z hh₁c
          -- Two private twins of `h₁`.
          obtain ⟨a, b, haIso, hbIso, hab, ha1, hb1, hagsel, hbgsel⟩ :=
            exists_two_private_twins_twenty G Hub Iso hshare h₁ gsel hh₁Hub hgselHub hdh₁
              (hdeg4 gsel hgselHub) hh₁gsel hn1gsel hh₁3
          refine Or.inl (two_hub_zleaf_twenty G Hub Iso hiso3 hdisj hHub hIso hdsum hdeg3 hisodeg3
            hleak h₁ gsel a b c z hh₁Hub hgselHub hdh₁ (hdeg4 gsel hgselHub) haIso hbIso hcIso hzZ
            ha1 hb1 hcgsel.symm hzgsel hn1gsel hh₁c hn1z hagsel hbgsel hab)
        rcases hcdisj with hch | hch'
        · exact hclose h hhHub hdh hh3 hgselneh
            (hsole_nonadj h h' hHub1 hh'inNh hgselneh') (hnoZ_nonadj h hHubZ0) hch
        · exact hclose h' hh'Hub hdh' hh'3 hgselneh'
            (hsole_nonadj h' h h'Hub1 hhinNh' hgselneh) (hnoZ_nonadj h' h'HubZ0) hch'


end N20

end ACMax
