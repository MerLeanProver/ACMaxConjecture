import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N19.Core
import ACMaxConjecture.SmallCases.N19.StarTriangleStruct
import ACMaxConjecture.SmallCases.N19.OctahedronForce

/-!
# Octahedron structure layer for `R.card = 5` (`n = 19`, `|Hub| = 11`, the `r = 5` residual)

The `R.card = 6` octahedron layer (`TwinCert19OctahedronStruct` / `PoorForce` / `PoorForce2` /
`MassFour`) is hard-wired to the `(11, 6, 44)` profile with `∑_R isoDeg = 13`, trace saturation `30`,
and **five** poor hubs.  This file re-derives the *structural* (poor-side, non-`Z`) leaves for the
`r = 5` regime: `|R| = 5` rich hubs, `∑_R isoDeg = 12`, trace saturation `|R|² − |R| = 20`, and
**six** poor hubs carrying `18 − 12 = 6` iso-incidences (so each poor hub has iso-degree exactly `1`).

The trace saturation itself (`octahedron_trace_saturate_nineteen`) is already stated *general in `|R|`*
and is reused verbatim with `|R| = 5`.

## Lemmas (axiom-clean, no `hztwopoor`)

* `octahedron_struct_r5_nineteen` — the poor layer: exactly **six** poor hubs `Hub \ R`, each of
  iso-degree `1`; the rich iso-incidence `E(R, Iso) = 12` and poor iso-incidence `E(P, Iso) = 6`.
* `octahedron_low_twin_poor_r5_nineteen` — the low twins (those meeting a poor hub) carry all six
  poor incidences; every poor hub meets exactly one low twin (its unique twin), and the poor
  neighbourhoods of distinct twins are disjoint and partition the six poor hubs.
* `rich_isodeg3_pair_adj_r5_nineteen` — **the new `r = 5` rigidity:** any two rich hubs of
  iso-degree `≥ 3` are *adjacent*.  (Two non-adjacent iso-degree-`≥ 3` hubs share exactly one twin
  (`rich_nonadj_share_eq_one_nineteen`), leaving `≥ 2` private twins on each side — a good two-hub
  pair contradicting `hno2hub`.)  In the `{2,2,2,3,3}` multiset the two iso-degree-`3` rich hubs are
  thus mutually adjacent; since each is degree `4` with three twin neighbours, the adjacency consumes
  its single non-twin slot, so each iso-degree-`3` hub is *saturated* (no poor / `Z` / other-rich
  neighbour).

## Why `{2,2,2,3,3}` does **not** close from these leaves alone

The good triangle / `C₄` / `K₂,₃` for the `{2,2,2,3,3}` residual lives in the **poor + `Z`** layer
(e.g. an `M`-edge endpoint `z` meeting two adjacent poor hubs gives a triangle `3 + 4 + 4 = 11`), not
in branch-(a) of the twin layer: the all-rich-degree-`2` twin profile (`n₂ = 6`, `mRR = 8`) has
*every* twin meeting exactly one poor hub, so no twin meets two poor and branch-(a) is vacuous.
Forcing the poor/`Z` good config needs the cross counts `E(R, Z)`, `E(P, Z)` — i.e. the
`hztwopoor`-threaded `octahedron_poor_counts`-level structure, which is **not** available to
`r5_resid_nineteen` (it is called *inside* `z_meets_two_poor_forces_two_hub_nineteen`, the very
witness for `ZMeetsTwoPoorResidual`).  See `TwinCert19R5Resid` for the precisely-scoped residual.
-/

namespace ACMax

open scoped Classical

namespace N19

/-- **`r = 5` rich iso-degree-`3` rigidity (LEAF, axiom-clean).**  Two distinct rich hubs of
iso-degree `≥ 3` are adjacent.  Non-adjacency would force each to keep `≥ 2` private `M`-isolated
twins (they share exactly one), a good two-hub pair contradicting `hno2hub`. -/
theorem rich_isodeg3_pair_adj_r5_nineteen (G : SimpleGraph (Fin 19)) (Hub Iso : Finset (Fin 19))
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hno2hub : ¬∃ h₁ h₂ : Fin 19, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card)
    (a b : Fin 19) (haHub : a ∈ Hub) (hbHub : b ∈ Hub)
    (hda : G.degree a = 4) (hdb : G.degree b = 4) (hab : a ≠ b)
    (hae : 3 ≤ (G.neighborFinset a ∩ Iso).card) (hbe : 3 ≤ (G.neighborFinset b ∩ Iso).card) :
    G.Adj a b := by
  classical
  by_contra hnadj
  -- They share exactly one twin, so each retains `≥ 2` private twins: a good two-hub pair.
  have hshare1 : (G.neighborFinset a ∩ G.neighborFinset b ∩ Iso).card = 1 :=
    rich_nonadj_share_eq_one_nineteen G Hub Iso hshare hno2hub a b haHub hbHub hda hdb hab hnadj
      (by omega) (by omega)
  -- `|N(a)∩Iso \ N(b)| = |N(a)∩Iso| - |shared| ≥ 3 - 1 = 2`.
  have hAprivate : 2 ≤ ((G.neighborFinset a ∩ Iso) \ G.neighborFinset b).card := by
    have hkey := Finset.card_sdiff_add_card_inter (G.neighborFinset a ∩ Iso) (G.neighborFinset b)
    have hinter : (G.neighborFinset a ∩ Iso) ∩ G.neighborFinset b
        = G.neighborFinset a ∩ G.neighborFinset b ∩ Iso := Finset.inter_right_comm _ _ _
    rw [hinter, hshare1] at hkey
    omega
  have hBprivate : 2 ≤ ((G.neighborFinset b ∩ Iso) \ G.neighborFinset a).card := by
    have hkey := Finset.card_sdiff_add_card_inter (G.neighborFinset b ∩ Iso) (G.neighborFinset a)
    have hinter : (G.neighborFinset b ∩ Iso) ∩ G.neighborFinset a
        = G.neighborFinset b ∩ G.neighborFinset a ∩ Iso := Finset.inter_right_comm _ _ _
    have hcomm : G.neighborFinset b ∩ G.neighborFinset a ∩ Iso
        = G.neighborFinset a ∩ G.neighborFinset b ∩ Iso := by
      rw [Finset.inter_comm (G.neighborFinset b) (G.neighborFinset a)]
    rw [hinter, hcomm, hshare1] at hkey
    omega
  exact hno2hub ⟨a, b, haHub, hbHub, hda, hdb, hab, hnadj, hAprivate, hBprivate⟩

/-- **`r = 5` octahedron poor-layer structure (LEAF, axiom-clean).**  From the `(11, 6)` profile with
`R.card = 5`: there are exactly **six** poor hubs `Hub \ R`, each of iso-degree `1`; the rich
iso-incidence is `E(R, Iso) = 12` and the poor iso-incidence is `E(P, Iso) = 6`. -/
theorem octahedron_struct_r5_nineteen (G : SimpleGraph (Fin 19)) (Hub Iso R : Finset (Fin 19))
    (hReq : R = Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card))
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hHub : Hub.card = 11) (hIso : Iso.card = 6)
    (hnozero : ∀ h ∈ Hub, 1 ≤ (G.neighborFinset h ∩ Iso).card)
    (hRcard : R.card = 5) :
    (Hub \ R).card = 6 ∧
    (∀ g ∈ Hub \ R, (G.neighborFinset g ∩ Iso).card = 1) ∧
    (∑ t ∈ Iso, (G.neighborFinset t ∩ R).card) = 12 ∧
    (∑ t ∈ Iso, (G.neighborFinset t ∩ (Hub \ R)).card) = 6 := by
  classical
  have hRsub : R ⊆ Hub := by rw [hReq]; exact Finset.filter_subset _ _
  -- |Hub \ R| = 6.
  have hPcard : (Hub \ R).card = 6 := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hRsub, hHub, hRcard]
  -- Each poor hub meets exactly one twin.
  have hpoor1 : ∀ g ∈ Hub \ R, (G.neighborFinset g ∩ Iso).card = 1 := by
    intro g hg
    rw [Finset.mem_sdiff] at hg
    obtain ⟨hgHub, hgnR⟩ := hg
    have hge1 : 1 ≤ (G.neighborFinset g ∩ Iso).card := hnozero g hgHub
    have hle1 : (G.neighborFinset g ∩ Iso).card ≤ 1 := by
      by_contra h
      exact hgnR (by rw [hReq, Finset.mem_filter]; exact ⟨hgHub, by omega⟩)
    omega
  -- Per-twin: rich + poor incidences sum to three.
  have hsplit : ∀ t ∈ Iso, (G.neighborFinset t ∩ R).card
      + (G.neighborFinset t ∩ (Hub \ R)).card = 3 := by
    intro t ht
    have h1 : (G.neighborFinset t ∩ Hub) ∩ R = G.neighborFinset t ∩ R := by
      rw [Finset.inter_assoc, Finset.inter_eq_right.mpr hRsub]
    have h2 : (G.neighborFinset t ∩ Hub) \ R = G.neighborFinset t ∩ (Hub \ R) :=
      Finset.inter_sdiff_assoc _ _ _
    have h3 := Finset.card_inter_add_card_sdiff (G.neighborFinset t ∩ Hub) R
    rw [h1, h2, hiso3 t ht] at h3
    exact h3
  -- E(Hub \ R, Iso) = 6.
  have hSP : ∑ t ∈ Iso, (G.neighborFinset t ∩ (Hub \ R)).card = 6 := by
    rw [cross_count_nineteen G Iso (Hub \ R), Finset.sum_congr rfl (fun g hg => hpoor1 g hg),
      Finset.sum_const, hPcard, smul_eq_mul, mul_one]
  -- E(Hub, Iso) = 18, hence E(R, Iso) = 12.
  have hsum18 : (∑ t ∈ Iso, (G.neighborFinset t ∩ R).card)
      + ∑ t ∈ Iso, (G.neighborFinset t ∩ (Hub \ R)).card = 18 := by
    rw [← Finset.sum_add_distrib, Finset.sum_congr rfl (fun t ht => hsplit t ht),
      Finset.sum_const, hIso, smul_eq_mul]
  have hSR : (∑ t ∈ Iso, (G.neighborFinset t ∩ R).card) = 12 := by omega
  exact ⟨hPcard, hpoor1, hSR, hSP⟩

/-- **`r = 5` octahedron low-twin poor incidence (LEAF, axiom-clean).**  Every poor hub
(`P = Hub \ R`) meets exactly one twin; that twin lies in the low-twin set
`L = {t ∈ Iso : 1 ≤ |N(t) ∩ P|}`.  The poor neighbourhoods of distinct low twins are disjoint and
their union is all six poor hubs, so `∑_{t ∈ Iso} |N(t) ∩ P| = 6`. -/
theorem octahedron_low_twin_poor_r5_nineteen (G : SimpleGraph (Fin 19))
    (Hub Iso R : Finset (Fin 19))
    (hReq : R = Hub.filter (fun h => 2 ≤ (G.neighborFinset h ∩ Iso).card))
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hHub : Hub.card = 11) (hIso : Iso.card = 6)
    (hnozero : ∀ h ∈ Hub, 1 ≤ (G.neighborFinset h ∩ Iso).card)
    (hRcard : R.card = 5) :
    (∀ g ∈ Hub \ R, ∃! t : Fin 19, t ∈ Iso ∧ G.Adj g t) ∧
    (∑ t ∈ Iso, (G.neighborFinset t ∩ (Hub \ R)).card) = 6 := by
  classical
  set P : Finset (Fin 19) := Hub \ R with hPdef
  have hRsub : R ⊆ Hub := by rw [hReq]; exact Finset.filter_subset _ _
  obtain ⟨_, hpoor1, _, hSP⟩ :=
    octahedron_struct_r5_nineteen G Hub Iso R hReq hiso3 hHub hIso hnozero hRcard
  refine ⟨?_, hSP⟩
  intro g hg
  have hg1 := hpoor1 g hg
  obtain ⟨t, hteq⟩ := Finset.card_eq_one.mp hg1
  have htmem : t ∈ G.neighborFinset g ∩ Iso := by rw [hteq]; exact Finset.mem_singleton_self _
  rw [Finset.mem_inter, G.mem_neighborFinset] at htmem
  obtain ⟨hgt, htIso⟩ := htmem
  refine ⟨t, ⟨htIso, hgt⟩, ?_⟩
  rintro s ⟨hsIso, hgs⟩
  have hsmem : s ∈ G.neighborFinset g ∩ Iso := by
    rw [Finset.mem_inter, G.mem_neighborFinset]; exact ⟨hgs, hsIso⟩
  have := hteq ▸ hsmem
  rwa [Finset.mem_singleton] at this

end N19

end ACMax
