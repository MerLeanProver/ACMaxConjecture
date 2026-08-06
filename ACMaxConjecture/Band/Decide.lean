/-!
# The low-band kernel `decide` node — B8 of the band discharge

This file lands node **B8** of the AHL band discharge.  It is pure `ℕ` arithmetic — no imports (the
prelude `decide +kernel`, `omega` and `rcases` suffice), and
in particular no graph theory and no Mathlib olean footprint, keeping the kernel's working set clear
of memory pressure during the exhaustive evaluation.  It discharges the per-cell Alon–Hoory–Linial
kill inequality on the low band `64 ≤ n ≤ 122`.

For each cell `(n, X, h)` of the landed-row region (`h ≤ X`, `3X + 26 ≤ n`,
`10X + 7h + 186 ≤ 4n`), write `L = ⌊(n + 8)/9⌋`, `v = n − h`, `t = n − 4 − X − 3h` (all `Nat`, the
truncated subtraction is faithful since `t ≥ 43` on the region).  The kill certificate is the
disjunction of the **SUM** (vertex-ball, `ℓ = ⌊L/2⌋`) and **EDGE** (even-girth, `s + 1 = ⌊(L+1)/2⌋`)
side conditions

* `t·(v−1)·v^(L/2) < (v+t)·((v+2t)^(L/2) − v^(L/2))`  (SUM), or
* `t·v^((L+1)/2) < (v+2t)^((L+1)/2) − v^((L+1)/2)`     (EDGE).

The content was verified exactly on all 7,743 region cells of `64 ≤ n ≤ 122` (zero failures; the
EDGE disjunct is load-bearing only at `n ∈ 77..81`).  Powers are small, so kernel `Nat` (GMP)
arithmetic is cheap; the band is split into four `decide +kernel` chunks, then reassembled by
`omega`.

**Why the band stops at `122`.**  Every order from `123` up is closed import-free by
`starved_dead_ge_123` (`Counting.V9DischargeSharp`), which runs the tier-9 collision at the
bulk-credited moat radius of `Counting.MoatSharp`.  The band therefore only has to reach the point
where that argument takes over; the region caps `X < 33`, `h < 33` are `omega`-derived from
`3X + 26 ≤ n ≤ 122` (so `X ≤ 32`) and `h ≤ X`.

## Contents

* **`AhlCell`** — the per-cell `SUM ∨ EDGE` kill predicate.
* the four exhaustive `decide +kernel` chunks `band_*` covering `64 ≤ n ≤ 122`.
* **`ahl_band_low_decide`** — the assembled low-band kill in the doc's pinned `let`-form.
-/

set_option maxRecDepth 4000
set_option synthInstance.maxSize 1024

namespace ACMax

/-- The per-cell AHL kill predicate on the low band: the **SUM** (vertex-ball, exponent `L/2`)
disjunct or the **EDGE** (even-girth, exponent `(L+1)/2`) disjunct, with `L = (n+8)/9`, `v = n−h`,
`t = n−4−X−3h` (truncated `Nat` subtraction, faithful since `t ≥ 43` on the region). -/
abbrev AhlCell (n X h : Nat) : Prop :=
  (n - 4 - X - 3 * h) * (n - h - 1) * (n - h) ^ ((n + 8) / 9 / 2) <
      (n - h + (n - 4 - X - 3 * h)) *
        ((n - h + 2 * (n - 4 - X - 3 * h)) ^ ((n + 8) / 9 / 2) - (n - h) ^ ((n + 8) / 9 / 2)) ∨
    (n - 4 - X - 3 * h) * (n - h) ^ (((n + 8) / 9 + 1) / 2) <
      (n - h + 2 * (n - 4 - X - 3 * h)) ^ (((n + 8) / 9 + 1) / 2) -
        (n - h) ^ (((n + 8) / 9 + 1) / 2)

set_option maxHeartbeats 8000000 in
/-- **B8 chunk `64 ≤ n ≤ 79`.**  Every region cell in this sub-band satisfies
`AhlCell`. -/
theorem band_64_79 : ∀ n, n < 80 → 64 ≤ n → ∀ X, X < 33 → 3 * X + 26 ≤ n →
    ∀ h, h < 33 → h ≤ X → 10 * X + 7 * h + 186 ≤ 4 * n → AhlCell n X h := by
  decide +kernel

set_option maxHeartbeats 8000000 in
/-- **B8 chunk `80 ≤ n ≤ 95`.**  Every region cell in this sub-band satisfies
`AhlCell`. -/
theorem band_80_95 : ∀ n, n < 96 → 80 ≤ n → ∀ X, X < 33 → 3 * X + 26 ≤ n →
    ∀ h, h < 33 → h ≤ X → 10 * X + 7 * h + 186 ≤ 4 * n → AhlCell n X h := by
  decide +kernel

set_option maxHeartbeats 8000000 in
/-- **B8 chunk `96 ≤ n ≤ 111`.**  Every region cell in this sub-band satisfies
`AhlCell`. -/
theorem band_96_111 : ∀ n, n < 112 → 96 ≤ n → ∀ X, X < 33 → 3 * X + 26 ≤ n →
    ∀ h, h < 33 → h ≤ X → 10 * X + 7 * h + 186 ≤ 4 * n → AhlCell n X h := by
  decide +kernel

set_option maxHeartbeats 8000000 in
/-- **B8 chunk `112 ≤ n ≤ 122`.**  Every region cell in this sub-band satisfies
`AhlCell`.  This is the top chunk: `starved_dead_ge_123` takes over at `n = 123`. -/
theorem band_112_122 : ∀ n, n < 123 → 112 ≤ n → ∀ X, X < 33 → 3 * X + 26 ≤ n →
    ∀ h, h < 33 → h ≤ X → 10 * X + 7 * h + 186 ≤ 4 * n → AhlCell n X h := by
  decide +kernel

/-- **B8 — the low-band AHL kill.**  On the landed-row band `64 ≤ n ≤ 122`, every
region cell `(n, X, h)` (`h ≤ X`, `3X + 26 ≤ n`, `10X + 7h + 186 ≤ 4n`) satisfies the
`SUM ∨ EDGE` kill inequality, with `L = (n+8)/9`, `v = n−h`, `t = n−4−X−3h`.  Assembled
from the four exhaustive `decide +kernel` chunks by an `omega` band split; the bounds
`X < 33`, `h < 33` are `omega`-derived from the region (`3X ≤ n − 26 ≤ 96`, `h ≤ X`). -/
theorem ahl_band_low_decide : ∀ n, 64 ≤ n → n ≤ 122 → ∀ X, 3 * X + 26 ≤ n → ∀ h, h ≤ X →
    10 * X + 7 * h + 186 ≤ 4 * n →
    (let L := (n + 8) / 9
     let v := n - h
     let t := n - 4 - X - 3 * h
     t * (v - 1) * v ^ (L / 2) < (v + t) * ((v + 2 * t) ^ (L / 2) - v ^ (L / 2)) ∨
       t * v ^ ((L + 1) / 2) < (v + 2 * t) ^ ((L + 1) / 2) - v ^ ((L + 1) / 2)) := by
  intro n hn64 hn122 X hX3 h hhX hmaster
  have hXcap : X < 33 := by omega
  have hhcap : h < 33 := by omega
  rcases (show (64 ≤ n ∧ n ≤ 79) ∨
      (80 ≤ n ∧ n ≤ 95) ∨
      (96 ≤ n ∧ n ≤ 111) ∨
      (112 ≤ n ∧ n ≤ 122) from by omega) with
    ⟨_, _⟩ |
    ⟨_, _⟩ |
    ⟨_, _⟩ |
    ⟨_, _⟩
  · exact band_64_79 n (by omega) (by omega) X hXcap hX3 h hhcap hhX hmaster
  · exact band_80_95 n (by omega) (by omega) X hXcap hX3 h hhcap hhX hmaster
  · exact band_96_111 n (by omega) (by omega) X hXcap hX3 h hhcap hhX hmaster
  · exact band_112_122 n (by omega) (by omega) X hXcap hX3 h hhcap hhX hmaster

end ACMax
