# The ACMAX Conjecture — a complete Lean 4 formalization

**Status: PROVED.** This repository contains a machine-checked proof of the ACMAX conjecture
(T. Kolokolnikov, *Maximizing algebraic connectivity for certain families of graphs*,
Linear Algebra and its Applications 471 (2015) 122–140;
[arXiv:1412.6147](https://arxiv.org/abs/1412.6147), Conjecture 1.5), for **every** `n ≥ 4`:

> Among all simple graphs on `n` vertices with exactly `m = 2(n−2)` edges, the complete
> bipartite graph `K_{2,n−2}` maximizes the algebraic connectivity `λ₂` (the second-smallest
> Laplacian eigenvalue), and its algebraic connectivity is exactly `2`.

The statement was open in general; it had been verified computationally only for `n ≤ 13`.

## The main theorem

The canonical statement lives at the root module, [`ACMaxConjecture.lean`](ACMaxConjecture.lean):

```lean
theorem ACMax.acmax_conjecture (n : ℕ) (hn : 4 ≤ n) [Nonempty (Fin n)] :
    algConn (completeBipartiteGraph (Fin 2) (Fin (n - 2))) = 2 ∧
      ∀ G : SimpleGraph (Fin n), G.edgeFinset.card = 2 * (n - 2) → algConn G ≤ 2
```

`algConn` is the algebraic connectivity, defined directly as the second-smallest eigenvalue of
the graph Laplacian `L(G) = D(G) − A(G)`
([`ACMaxConjecture/Spectral/AlgConn.lean`](ACMaxConjecture/Spectral/AlgConn.lean)) — Mathlib's
sorted spectrum `eigenvalues₀` at index `card V − 2`, which is second-smallest because that
sequence is antitone. The two Courant–Fischer bridges are then proved against it as theorems: an
upper bound from any test vector orthogonal to the constant vector
([`Spectral/RayleighUpper.lean`](ACMaxConjecture/Spectral/RayleighUpper.lean),
[`TestVector.lean`](ACMaxConjecture/Spectral/TestVector.lean)) and the matching lower bound used
for the equality clause ([`Spectral/RayleighLower.lean`](ACMaxConjecture/Spectral/RayleighLower.lean)).


## Building

The toolchain and dependency set are pinned:

| | |
|---|---|
| Lean | `leanprover/lean4:v4.33.0-rc2` (`lean-toolchain`) |
| Mathlib | `1aa85dfb910a0fedb00c60eb8768ee5f781c855d` (`lake-manifest.json`) |

`lakefile.toml` requires Mathlib at `master`; the exact revision above is what
`lake-manifest.json` pins, and it is the revision the proof is checked against. Do **not**
run `lake update` — it would move Mathlib off the pinned commit.

```bash
lake exe cache get   # fetch the Mathlib build cache
lake build           # builds the whole library
```

Expect a long build: the library is ~163k lines across 429 modules, and the kernel `decide`
band is deliberately expensive — each of the four chunks in `Band/Decide.lean` runs under
`set_option maxHeartbeats 8000000`, forty times Lean's default budget. Build with as many
cores and as much memory as you can give it.


## Independent verification (comparator, two kernels)

The proof has additionally been judged by [leanprover/comparator](https://github.com/leanprover/comparator):
[`Challenge.lean`](Challenge.lean) states the conjecture with a `sorry` (importing only Mathlib
and the definitional layer), [`Solution.lean`](Solution.lean) proves it from the library, and
comparator verifies statement equality at the `lean4export` level, enforces the axiom whitelist,
and replays the exported proof closure through **two independent kernels** — the Lean default
kernel and [nanoda](https://github.com/ammkrn/nanoda_lib) (Rust). Both accept:

```
Running nanoda kernel on solution
Nanoda kernel accepts the solution
Running Lean default kernel on solution.
Lean default kernel accepts the solution
Your solution is okay!
```

Reproduce with `landrun`, `lean4export` (built against v4.33.0-rc2, matching `lean-toolchain` —
an exporter built for a different Lean version rejects the oleans with `incompatible header`)
and `nanoda_bin` in `PATH` (or the `COMPARATOR_*` environment variables), then:

```bash
lake env path/to/comparator comparator_config.json           # full conjecture, n ≥ 4
lake env path/to/comparator comparator_config_large_n.json   # large-order artifact, n ≥ 123
```

Both configs whitelist exactly `propext`, `Quot.sound`, `Classical.choice` and enable the
nanoda replay.

## The large-order case as a single file

The large-order half of the conjecture is also provided as a standalone artifact:
[`ACMaxLargeN.lean`](ACMaxLargeN.lean) is a single self-contained file of ~6.7k lines
(importing only Mathlib) proving

```lean
theorem ACMax.acmax_conjecture_large_n (n : ℕ) (hn : 123 ≤ n) [Nonempty (Fin n)] :
    algConn (completeBipartiteGraph (Fin 2) (Fin (n - 2))) = 2 ∧
      ∀ G : SimpleGraph (Fin n), G.edgeFinset.card = 2 * (n - 2) → algConn G ≤ 2
```

with none of the finite-range machinery — no per-order case analysis and no kernel `decide`
bands. It is assembled from the canonical modules under `ACMaxConjecture/` with everything
unreachable from the main theorem pruned away, and organized as a readable document in seven
parts (foundations, cut toolbox, reduction to the residual core, census vocabulary, the moat
certificate, the ball double count, the collision) rather than as a concatenation.

Its threshold is the library's own: `Counting/V9DischargeSharp.lean` closes every `n ≥ 123`
import-free, at the bulk-credited moat radius of `Counting/MoatSharp.lean`, and this file is that
same argument extracted. It is a pruned, reorganized *extract* of the canonical modules — not an
independent development — so it is a second reading of one proof, not a second proof. What it
does buy is independence of the build: it imports only Mathlib, so it can be checked without any
of `ACMaxConjecture/`.

It carries its own comparator harness ([`ChallengeLargeN.lean`](ChallengeLargeN.lean) states
the theorem over Mathlib alone, reproducing the `algConn` definition verbatim;
[`SolutionLargeN.lean`](SolutionLargeN.lean) proves it from the file;
`comparator_config_large_n.json` configures the check), and both kernels accept it.

This is the artifact to read first if you want the mathematics without the bookkeeping: the
`n ≥ 123` argument is the conceptual core, and the rest of the library is what it takes to
close the finitely many smaller orders.

## Architecture of the proof

The final theorem's import cone is the whole library — 429 project modules, ~163k lines. The
tree has been pruned to exactly what the final theorem reaches: every module below is live,
and nothing else is shipped.

| Chapter | Modules | Lines | Content |
|---|---:|---:|---|
| `Spectral/` | 5 | 532 | `algConn`, the two Courant–Fischer bridges, `λ₂(K_{2,n−2}) = 2`, the universal test-vector interface |
| `Cuts/` | 12 | 2,422 | the concrete `algConn ≤ 2` certificates: balanced / weighted / signed cuts, induced-`2K₂`, good-`C₄` and good-`K_{2,3}`, low-degree vertex |
| `Reduction/` | 1 | 43 | the two residual degree-count identities (`cross_count`, `residual_degree_sum`) |
| `Counting/` | 13 | 6,871 | moats (plain and bulk-credited), the starved census, degree classes, far-pair certificates, SQRT girth, the tier-9 discharge at `n ≥ 123`, the window dispatch |
| `SmallCases/` | 374 | 149,515 | the per-order proofs `4 ≤ n ≤ 20` |
| `Islands/` | 3 | 586 | the Moore-extremal band `48 ≤ n ≤ 63` |
| `AHL/` | 6 | 1,134 | the Alon–Hoory–Linial ladder: non-backtracking walks → stationary marginals → weighted AM–GM |
| `Band/` | 9 | 1,456 | the SUM/EDGE Moore band discharge, the kernel `decide` on `64 ≤ n ≤ 122`, the final splice |
| root support | 5 | 893 | `Base` (the pinned Mathlib surface), `UpperBound`, `Cut2K2Free12`, `TwoRegular2K2`, `InternalEdgesEven` (+ `ACMaxConjecture.lean`) |

### Which orders are closed by what

Every `n ≥ 4` is covered. Up to `n = 49` — and on the seven islands — the range is closed
outright; from `n ≥ 55` the dispatch has already stripped away every graph a test vector or a
moat kills, so those rows say what closes the surviving **starved census** (minimum degree 3,
no edge between two degree-3 vertices):

| Orders | Closed by | Method |
|---|---|---|
| `4 ≤ n ≤ 20` | `SmallCases/` | seventeen banked per-order theorems, `acmax_conjecture_four … _twenty` |
| `21 ≤ n ≤ 31` | `Counting/Windows.lean` | moat window: `δ ≤ 2` test vector / `M`-edge moat / `Z1` star-moat forcing |
| `32 ≤ n ≤ 49` | `Counting/Windows.lean` | the widened starved band `starved_band_kill_32_49` (owner-choke rows) |
| `50–54, 62, 63` | `Islands/Dead.lean` | the seven Moore-extremal islands, closed outright by `hIslands_discharged` |
| `55 ≤ n ≤ 63` | `Islands/Dead.lean` | `island_band_dead`, wired in as the low end of `starved_dead_55_122_of_decide` |
| `64 ≤ n ≤ 122` | `Band/Decide.lean` | kernel `decide`, four chunks (`band_64_79`, `_80_95`, `_96_111`, `_112_122`) |
| `n ≥ 123` | `Counting/V9DischargeSharp.lean` | `starved_dead_ge_123`, import-free tier-9 collision at the bulk-credited moat radius |

`island_band_dead` is proved on the full band `48 ≤ n ≤ 63` and used twice: once for the seven
islands, once for `55 ≤ n ≤ 63`.

`SmallCases/` dominates the line count because it is where the irreducible finite work lives:
11 top-level modules (the shared dispatcher, the generic signed-cut and star-triangle
certificates, and the orders `n ≤ 11`) plus one subtree per order `N12`…`N20`. Those subtrees
grow steeply with `n` — 2 modules at `n = 12`, 31 at `n = 17`, 115 at `n = 20` — because the
structural case analysis does. The pruning pass removed the per-order duplicates: the signed-cut
boundary certificates that `n = 15,16,17,18` each carried are now one theorem over an arbitrary
finite vertex type (`SmallCases/Certificates.lean`), and everything order-independent was lifted
into `SmallCases/Dispatcher.lean`, leaving each order's wrapper holding only its three degree-sum
thresholds and its final structural certificate.

### The assembly chain

The proof is spliced together in four steps, each a named theorem you can jump to:

1. **`acmax_conjecture_narrow`** (`Counting/Windows.lean`) — the capstone, stated with two
   explicit residual hypotheses. It dispatches: `n ≤ 20` to the banked per-order theorems;
   `21 ≤ n ≤ 49` to `acmax_conjecture_range_49`; and for `n ≥ 50`, a vertex of degree `≤ 2`
   fires `algConn_le_two_of_low_degree_vertex`, an `M`-edge (two adjacent degree-3 vertices)
   fires `medge_moat_fires`, and what survives is the **starved census** — minimum degree 3,
   no degree-3–degree-3 edge. On that branch `n ≥ 123` dies at `starved_dead_ge_123`,
   leaving `hIslands` (the seven islands) and `hStarved55` (`55 ≤ n ≤ 122`).
2. **`acmax_conjecture_of_starved_only`** (`Islands/Dead.lean`) — discharges `hIslands`.
   `island_band_dead` kills the whole band `48 ≤ n ≤ 63` by splitting on
   `HasUsableFarPair`: the spread branch fires the far-pair certificate, and the compact
   branch collides two counting ledgers (the owner choke against a far-pair cover built on
   the level-sharp 3-ball of `Islands/Ball.lean`) until `omega` finds the system
   integer-infeasible. Only `hStarved55` remains.
3. **`acmax_conjecture_of_decide`** (`Band/Assembly.lean`) — discharges `hStarved55`, modulo
   one pinned arithmetic hypothesis. The `AHL/` ladder (non-backtracking walk counts →
   exact stationary degree marginals → weighted AM–GM → degree convexity) yields two Moore
   bounds: the vertex-ball **SUM** form (`Band/Sum.lean`) and the even-girth **EDGE** form
   (`Band/Edge.lean`, load-bearing exactly on the odd stretch `n ∈ {77,…,81}` that SUM
   misses). Region rows (`Band/Rows.lean`) pin `MASTER″`: `10X + 7h + 186 ≤ 4n`. Then
   `64 ≤ n ≤ 122` needs the pinned `AhlBandLowDecide`, and `55 ≤ n ≤ 63` reuses
   `island_band_dead`. Nothing above `122` reaches this branch — `starved_dead_ge_123` has
   already taken it in step 1.
4. **`acmax_conjecture_general`** (`Band/Final.lean`) — discharges `AhlBandLowDecide` with
   the kernel `decide` lemma of `Band/Decide.lean`, making the conjecture hypothesis-free.
   `UpperBound.lean` and `ACMaxConjecture.lean` then re-expose it as the canonical
   `ACMax.acmax_conjecture`.

The girth argument behind steps 1 and 3 runs on the low-degree population `V₉ = {v : deg v ≤ 4}`
(degree-3 twins and the degree-4 sea together, so the honest excess `t₉ = n − 4 − X − 3h` is
`Θ(n)` rather than `O(1)`): a short `V₉`-cycle fires a certificate cut, so a surviving graph has
large `V₉`-girth, and the derived strip constraint is discharged cell by cell.

What sets the `123` is the moat threshold. `Counting/V9Discharge.lean` carries the tier-9
vocabulary and the girth import; on the plain threshold `9k ≤ n + 8` the admissible ball radius is
`r = ⌊(⌊(n+8)/9⌋ − 1)/2⌋`, which would only close the census from `n ≥ 388`.
`Counting/MoatSharp.lean` sharpens the threshold to `12k + X ≤ 2n` by keeping the bulk excess
`Σ_{S₂}(deg − 3)` that the plain row discards; the radius rises to `r = ⌊(2n − X − 12)/24⌋`, and
`Counting/V9DischargeSharp.lean` runs the same collision at that radius, closing every `n ≥ 123`
import-free. That is why the kernel `decide` band only has to reach `122`. The earlier `n ≥ 388`
and `n ≥ 1100` dispatches were removed once `starved_dead_ge_123` subsumed them.

## Provenance

The formalization was produced by [**MerLean**](https://github.com/MerLeanProver/MerLean), an
autonomous Lean 4 + Mathlib theorem-proving system built as Claude Code skills and subagents over
a plan graph: the goal is decomposed into a dependency graph of lemmas, each node is proved in its
own file by a `compile-fix` subagent, and every landed statement is independently re-verified by a
fresh kernel-level `#print axioms` check before being banked. Every numeric certificate (counting
rows, Moore cells, band constants) was cross-checked by exact big-integer enumeration before
formalization.

The correctness of the result does not rest on any of that: it rests on the Lean kernel, and
on the two-kernel comparator replay above.

**Human review.** The `n ≥ 123` argument has been read and verified by the authors — it is the
mathematics written up in the accompanying paper, and the same argument whether read as
`ACMaxLargeN.lean` or as the library's `Counting/V9DischargeSharp.lean` route. The finite range
`4 ≤ n ≤ 122` has not been human-reviewed; it is the bulk of the artifact by size and rests on
the mechanical guarantees above. [`formalization.yaml`](formalization.yaml) records this split.

## Repository layout

- `ACMaxConjecture/` — the Lean library; [`ACMaxConjecture.lean`](ACMaxConjecture.lean) is the
  root module exposing the canonical theorem.
- `Challenge.lean`, `Solution.lean`, `comparator_config.json` — the comparator verification
  harness for the full conjecture.
- `ACMaxLargeN.lean` — the standalone single-file proof of the large-order case (`n ≥ 123`),
  with its own harness `ChallengeLargeN.lean`, `SolutionLargeN.lean`,
  `comparator_config_large_n.json`.
- `lakefile.toml`, `lake-manifest.json`, `lean-toolchain` — the pinned build configuration.
- [`formalization.yaml`](formalization.yaml) — self-reported provenance, process, and fidelity
  metadata, following the
  [mathlib-initiative `formalization.yaml` v0.3 standard](https://github.com/mathlib-initiative/formalization.yaml).

The campaign's working documents — attack plans, the exact-arithmetic verification scripts and
their outputs for every numeric certificate, and the plan-graph data stores — are **not** shipped
here. This repository is published as a single commit containing the finished artifact. Those
documents are retained separately, in the campaign repository's history (through commit
`509122b`).

## Citing

Please cite the accompanying paper:

> Zeru Zhu, Jinzheng Li, and Yuanjie Ren.
> *Maximizing Algebraic Connectivity with 2(n − 2) Edges: The Large-Order Case.* 2026.
> Forthcoming.

```bibtex
@misc{merlean_acmax_2026,
  title  = {Maximizing Algebraic Connectivity with $2(n-2)$ Edges:
            The Large-Order Case},
  author = {Zhu, Zeru and Li, Jinzheng and Ren, Yuanjie},
  year   = {2026},
  note   = {Forthcoming}
}
```

The system that produced this formalization is
[MerLean](https://github.com/MerLeanProver/MerLean).

## License

Apache License 2.0 — see [`LICENSE`](LICENSE). This matches Mathlib, on which the development
depends.
