import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N20.Core
import ACMaxConjecture.SmallCases.N20.StarTriangleStruct
import ACMaxConjecture.SmallCases.N20.OctahedronForce

/-!
# Octahedron structure layer for `R.card = 5` (`n = 19`, `|Hub| = 11`, the `r = 5` residual)

The `R.card = 6` octahedron layer (`TwinCert20OctahedronStruct` / `PoorForce` / `PoorForce2` /
`MassFour`) is hard-wired to the `(11, 6, 44)` profile with `∑_R isoDeg = 13`, trace saturation `30`,
and **five** poor hubs.  This file re-derives the *structural* (poor-side, non-`Z`) leaves for the
`r = 5` regime: `|R| = 5` rich hubs, `∑_R isoDeg = 12`, trace saturation `|R|² − |R| = 20`, and
**six** poor hubs carrying `18 − 12 = 6` iso-incidences (so each poor hub has iso-degree exactly `1`).

The trace saturation itself (`octahedron_trace_saturate_twenty`) is already stated *general in `|R|`*
and is reused verbatim with `|R| = 5`.

## Lemmas (axiom-clean, no `hztwopoor`)

* `rich_isodeg3_pair_adj_r5_twenty` — **the new `r = 5` rigidity:** any two rich hubs of
  iso-degree `≥ 3` are *adjacent*.  (Two non-adjacent iso-degree-`≥ 3` hubs share exactly one twin
  (`rich_nonadj_share_eq_one_twenty`), leaving `≥ 2` private twins on each side — a good two-hub
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
`r5_resid_twenty` (it is called *inside* `z_meets_two_poor_forces_two_hub_twenty`, the very
witness for `ZMeetsTwoPoorResidual`).  See `TwinCert20R5Resid` for the precisely-scoped residual.
-/

namespace ACMax

open scoped Classical

namespace N20

/-- **`r = 5` rich iso-degree-`3` rigidity (LEAF, axiom-clean).**  Two distinct rich hubs of
iso-degree `≥ 3` are adjacent.  Non-adjacency would force each to keep `≥ 2` private `M`-isolated
twins (they share exactly one), a good two-hub pair contradicting `hno2hub`. -/
theorem rich_isodeg3_pair_adj_r5_twenty (G : SimpleGraph (Fin 20)) (Hub Iso : Finset (Fin 20))
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hno2hub : ¬∃ h₁ h₂ : Fin 20, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card)
    (a b : Fin 20) (haHub : a ∈ Hub) (hbHub : b ∈ Hub)
    (hda : G.degree a = 4) (hdb : G.degree b = 4) (hab : a ≠ b)
    (hae : 3 ≤ (G.neighborFinset a ∩ Iso).card) (hbe : 3 ≤ (G.neighborFinset b ∩ Iso).card) :
    G.Adj a b := by
  classical
  by_contra hnadj
  -- They share exactly one twin, so each retains `≥ 2` private twins: a good two-hub pair.
  have hshare1 : (G.neighborFinset a ∩ G.neighborFinset b ∩ Iso).card = 1 :=
    rich_nonadj_share_eq_one_twenty G Hub Iso hshare hno2hub a b haHub hbHub hda hdb hab hnadj
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

end N20

end ACMax
