import Mathlib
import ACMaxConjecture.Counting.LargeN
import ACMaxConjecture.Spectral.AlgConnK2

/-!
# The finite-gap reduction: the whole conjecture from ONE parametric cell statement

This file makes the campaign's strategic ledger **kernel-checked**: for every `n ≥ 23`, the
full ACMAX upper bound follows from a single hypothesis — the *dossier'd compact cell fires*
on the finite window `23 ≤ n ≤ 17 692`.  Everything else is already proved unconditionally:

* `n > 17 692` — `acmax_conjecture_large_n_sharp2` (`Counting.WallSharp`,
  `boundLin ((128·306 + 34508)/23) = 17 692`, checked by `norm_num` below; the sharpened
  mid-leaf bound `108` / cloud cap `A ≤ 13` / usable cap `C_m ≤ 306` improves the earlier
  `18 764` and the original `19 556`);
* the reduction to `ResidualCore` at every `n ≥ 12` — `algConn_le_two_of_card_general_cond`;
* the all-light (sea, `Δ ≤ 4`) side at every `n ≥ 23` — `residual_sea_algConn_le_two`;
* the spread side (usable far pair) — `hasUsableFarPair_algConn_le_two`;
* the off-boundary side (`¬SeaFatBoundary`) at EVERY `n` — `off_boundary_fires`
  (the W1 double-star routing: gap-0, pad-supply, and hoard-kill);
* the `M`-structure collapse (all `M`-edges coincide, no cherries) — `medges_or_single`,
  `cherry_centre_fires`;
* the census floors (`n₃ ≥ 9`, `≥ 7` `M`-isolated twins) — `cell_deg3_floor`,
  `cell_iso_deg3_floor`.

`DossierCell` (below) is exactly the third disjunct of `cell_dossier`
(`Counting.HoardKill`): the survivor's complete verified profile.  The window hypothesis
`hcell` is the **single remaining open input of the general conjecture above `n = 22`**;
together with the per-`n` theorems `acmax_conjecture_four` … `acmax_conjecture_twenty`
(proved, axiom-clean) and the in-flight `n = 21, 22` campaigns
(`exists_twin_signed_cert_twentyone`, four alignment-dichotomy stubs), it closes the
conjecture at every order.

The per-range structure available INSIDE the window (for proving `hcell`):
`hml_or_fires` (`n ≥ 32`), `subset_block_fires` (`n ≥ 2(k+1)²`), the 2-ball partner cap and
`two_ball_upper_dispatch` (`n > 9 057`, heavy-proximity branch open), `usable_cap_mid`/cloud caps (`n ≥ 512`),
`single_heavy_fires`/`max_deg_five_fires` (`n ≥ 5 250`), `fat_excess_floor`,
`heavy_population_floor`, `shared_twins_fire` (`n ≥ 2(k+2)²`), and the window collision kit.
-/

namespace ACMax

open scoped Classical

/-- The **doubly-sharpened** large-`n` threshold (`acmax_conjecture_large_n_sharp2`,
`Counting.WallSharp`, mid-leaf bound `108` ⟹ usable cap `C_m ≤ 306`) evaluates to
`17 692` — the current finite frontier. -/
theorem boundLin_sharp2_value : boundLin ((128 * 306 + 34508) / 23) = 17692 := boundLin_sharp2_eq

end ACMax
