import ACMaxConjecture.Band.Kill
import ACMaxConjecture.Band.SubsetEdge

/-!
# B10 — the band-discharge assembly

This file lands node **B10** of the band discharge: the final assembly that turns the per-cell
Moore side conditions (SUM ∨ EDGE on the low band `64 ≤ n ≤ 122`) into the never-firing starved
census kill, and thence — via `acmax_conjecture_of_starved_only` — into the full ACMAX conjecture.
Everything from `n = 123` up is closed import-free by `starved_dead_ge_123`
(`Counting.V9DischargeSharp`), so this file carries no certificate bands.

**Staging.**  Node B8 (the kernel-`decide` lemma over the low band `64 ≤ n ≤ 122`) is proved
separately in `Band.Decide`, so every theorem here takes the *pinned* B8 statement
`AhlBandLowDecide` as an explicit hypothesis `hdecide`.  The splice file `Band.Final` discharges
`hdecide` with that `decide` lemma, at which point all three conclusions become unconditional.

## Contents

* **`AhlBandLowDecide`** — the pinned B8 proposition (bound, not proved, here).
* **`starved_dead_64_122_of_decide`** — a never-firing starved census on `64 ≤ n ≤ 122` is
  impossible: the region rows (`master_dprime`, hoarding + `giant_le_two`, `t9_window`) feed the
  honest excess `t₉`, and `hdecide` supplies the SUM/EDGE side condition that the tier-`9` kills
  refute.
* **`starved_dead_55_122_of_decide`** — extends the kill down to `55 ≤ n` via `island_band_dead`
  on the Moore-extremal band `55 ≤ n ≤ 63`; its statement matches the `hStarved55` shape verbatim.
* **`acmax_conjecture_of_decide`** — the full conjecture, conditional only on `hdecide`, by feeding
  `starved_dead_55_122_of_decide` to `acmax_conjecture_of_starved_only`.

Everything is `sorry`-free and (given a clean `hdecide`) axiom-clean
(`[propext, Classical.choice, Quot.sound]`).
-/

namespace ACMax

open scoped Classical
open SimpleGraph Finset

/-- **The pinned B8 kernel-`decide` statement** (node B8 of the band discharge).
On the low band `64 ≤ n ≤ 122`, for every degree excess `X` with `3X + 26 ≤ n` and heavy count
`h ≤ X` meeting `MASTER″` (`10X + 7h + 186 ≤ 4n`), the SUM per-cell Moore side condition at
`ℓ = ⌊(n+8)/9⌋/2` OR the EDGE per-cell side condition at `⌊(⌊(n+8)/9⌋+1)/2⌋` holds.  Bound here as
an explicit hypothesis: node B8 is proved by `decide` in `Band.Decide` and spliced in by
`Band.Final`. -/
abbrev AhlBandLowDecide : Prop :=
  ∀ n : ℕ, 64 ≤ n → n ≤ 122 → ∀ X : ℕ, 3 * X + 26 ≤ n → ∀ h : ℕ, h ≤ X →
    10 * X + 7 * h + 186 ≤ 4 * n →
    ((n - 4 - X - 3 * h) * (n - h - 1) * (n - h) ^ ((n + 8) / 9 / 2)
        < (n - h + (n - 4 - X - 3 * h))
          * ((n - h + 2 * (n - 4 - X - 3 * h)) ^ ((n + 8) / 9 / 2)
            - (n - h) ^ ((n + 8) / 9 / 2)))
      ∨ ((n - 4 - X - 3 * h) * (n - h) ^ (((n + 8) / 9 + 1) / 2)
          < (n - h + 2 * (n - 4 - X - 3 * h)) ^ (((n + 8) / 9 + 1) / 2)
            - (n - h) ^ (((n + 8) / 9 + 1) / 2))

/-- **B10 — the `64 ≤ n ≤ 122` starved census is dead** (conditional on `hdecide`).  A never-firing
starved census (`m = 2(n−2)`, `δ ≥ 3`, `hs0`, `¬ algConn ≤ 2`) on `64 ≤ n ≤ 122` is impossible.
Route: derive the region rows `h ≤ X` (`heavy_card_le_excess`), `3X + 26 ≤ n` (`hoarding_law` with
`giant_le_two`), `10X + 7h + 186 ≤ 4n` (`master_dprime`) and the positivity window
`X + 3h + 4 ≤ n` (`t9_window`); with `L = (n+8)/9` (so `6 ≤ L`, `9L ≤ n+8`), `hdecide` supplies the
SUM/EDGE disjunct, refuted via `starved_v9_kill_ahl_sum` / `starved_v9_kill_ahl_edge`.  The
`(v9Set G).card = n − h` bridge (`v9_card_add_compl`) reconciles the `n − h` and `|V₉|`
vocabularies.

Everything above `n = 122` is closed import-free by `starved_dead_ge_123`
(`Counting.V9DischargeSharp`), so no certificate bands are needed here. -/
theorem starved_dead_64_122_of_decide (hdecide : AhlBandLowDecide) {n : ℕ} [Nonempty (Fin n)]
    (G : SimpleGraph (Fin n)) (hn64 : 64 ≤ n) (hn122 : n ≤ 122)
    (hm : G.edgeFinset.card = 2 * (n - 2)) (h3 : ∀ v : Fin n, 3 ≤ G.degree v)
    (hnf : ¬ algConn G ≤ 2)
    (hs0 : ∀ v w : Fin n, G.degree v = 3 → G.degree w = 3 → ¬G.Adj v w) : False := by
  have hh : (v9Set G)ᶜ.card ≤ excessX n G := heavy_card_le_excess G
  have hM : 10 * excessX n G + 7 * (v9Set G)ᶜ.card + 186 ≤ 4 * n := by
    have hmd := master_dprime G (by omega) hm h3 hnf hs0
    omega
  have hoard : 3 * excessX n G + 26 ≤ n := by
    have hho := hoarding_law G (by omega) hm h3 hnf hs0
    have hng := giant_le_two G (by omega) hm h3 hnf hs0
    omega
  have hpos : excessX n G + 3 * (v9Set G)ᶜ.card + 4 ≤ n := t9_window G (by omega) hm h3 hnf hs0
  have hv : (v9Set G).card = n - (v9Set G)ᶜ.card := by
    have := v9_card_add_compl G; omega
  rcases hdecide n (by omega) hn122 (excessX n G) hoard ((v9Set G)ᶜ.card) hh hM with hsum | hedge
  · rw [← hv] at hsum
    exact starved_v9_kill_ahl_sum G (by omega) hm h3 hnf hpos ((n + 8) / 9)
      (by omega) (by omega) hsum
  · rw [← hv] at hedge
    exact starved_v9_kill_ahl_edge G (by omega) hm h3 hnf hpos ((n + 8) / 9)
      (by omega) (by omega) hedge

/-- **B10 — the `55 ≤ n ≤ 122` starved census is dead** (conditional on `hdecide`), in the exact
`hStarved55` shape.  For `n ≤ 63` the Moore-extremal band closes by `island_band_dead` (`48 ≤ n`
holds since `55 ≤ n`); for `n ≥ 64` it is `starved_dead_64_122_of_decide`.  The `m ≠ 62`, `m ≠ 63`
guards are not needed (`island_band_dead` already covers `48 ≤ n ≤ 63`), but are kept to match the
`hStarved55` hypothesis shape consumed by `acmax_conjecture_of_starved_only`. -/
theorem starved_dead_55_122_of_decide (hdecide : AhlBandLowDecide) :
    ∀ (m : ℕ) [Nonempty (Fin m)] (G : SimpleGraph (Fin m)),
        55 ≤ m → m ≤ 122 → m ≠ 62 → m ≠ 63 →
        G.edgeFinset.card = 2 * (m - 2) → (∀ v : Fin m, 3 ≤ G.degree v) →
        ¬ algConn G ≤ 2 →
        (∀ v w : Fin m, G.degree v = 3 → G.degree w = 3 → ¬G.Adj v w) → False := by
  intro m _inst G hm55 hm122 _hm62 _hm63 hedge h3 hnf hs0
  by_cases hle63 : m ≤ 63
  · exact island_band_dead G (by omega) hle63 hedge h3 hnf hs0
  · exact starved_dead_64_122_of_decide hdecide G (by omega) hm122 hedge h3 hnf hs0

/-- **B10 — the ACMAX conjecture from `hdecide` alone.**  Feeding the `hStarved55`-shaped kill
`starved_dead_55_122_of_decide` into `acmax_conjecture_of_starved_only` leaves no residual
hypothesis but `hdecide`: every order `n ≥ 4` satisfies the full conjecture
(`λ₂(K_{2,n−2}) = 2` and `algConn G ≤ 2` for every `2(n−2)`-edge graph). -/
theorem acmax_conjecture_of_decide (hdecide : AhlBandLowDecide) :
    ∀ (n : ℕ) [Nonempty (Fin n)], 4 ≤ n →
      algConn (completeBipartiteGraph (Fin 2) (Fin (n - 2))) = 2 ∧
        ∀ G : SimpleGraph (Fin n), G.edgeFinset.card = 2 * (n - 2) → algConn G ≤ 2 :=
  acmax_conjecture_of_starved_only (starved_dead_55_122_of_decide hdecide)

end ACMax
