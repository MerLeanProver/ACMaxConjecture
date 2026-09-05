# The ACMAX Conjecture

This repository contains a complete Lean 4 proof and a self-contained
mathematical proof of Kolokolnikov's ACMAX conjecture. For every `n >= 4`,
among simple graphs on `n` vertices with exactly `2(n-2)` edges, the complete
bipartite graph `K_{2,n-2}` attains the maximum algebraic connectivity, which
is `2`.

## Main theorem

The canonical statement is `ACMax.acmax_conjecture` in
`ACMaxConjecture.lean`:

```lean
theorem ACMax.acmax_conjecture (n : ℕ) (hn : 4 ≤ n) [Nonempty (Fin n)] :
    algConn (completeBipartiteGraph (Fin 2) (Fin (n - 2))) = 2 ∧
      ∀ G : SimpleGraph (Fin n),
        G.edgeFinset.card = 2 * (n - 2) → algConn G ≤ 2
```

## Repository contents

- `ACMaxConjecture.lean` and `ACMaxConjecture/` form the compact formal proof.
  The root has exactly 62 local module dependencies, recorded in
  `MODULES.txt`.
- `paper/` contains the arXiv v2 manuscript and its exact-arithmetic
  verification scripts.
- `Challenge.lean`, `Solution.lean`, and `comparator_config.json` provide the
  independent-statement harness used with `leanprover/comparator`.
- `SOURCE_COMMIT` records the development-repository commit from which the
  compact formal package was generated.
- `FORMALIZATION_SHA256SUMS` records the exact hashes of the generated Lean
  package and its pinned build files.

The initial 429-module implementation remains available in Git history at
commit `5fc5c7f`. The current tree removes modules that are not imported by the
paper-aligned proof. Historical declarations that share an imported module
with the active proof remain present.

## Building the formal proof

The Lean toolchain and Mathlib revision are pinned by `lean-toolchain` and
`lake-manifest.json`. Do not run `lake update` when reproducing the proof.

```bash
lake exe cache get
lake build ACMaxConjecture
lake env lean Solution.lean
```

The formal proof is `sorry`-free and does not use `native_decide`. An axiom
audit of the root theorem reports only `propext`, `Classical.choice`, and
`Quot.sound`.

## Building the paper

```bash
cd paper
latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=build main.tex
python tools/verify_moore_closure_arithmetic.py
python tools/verify_short_range_arithmetic.py
```

The mathematical proof first reduces a hypothetical counterexample to a graph
with minimum degree at least three and no adjacent degree-three vertices. It
then combines:

- an exact non-backtracking Moore argument for `n >= 48`;
- an incidence argument for `32 <= n <= 49`;
- local sparse-set and cut arguments for `4 <= n <= 31`.

The two upper ranges overlap at orders 48 and 49.

## Provenance

The formal development was generated with
[MerLean](https://github.com/MerLeanProver/MerLean) and checked by the Lean
kernel. The paper reorganizes the formal development into a conventional
mathematical proof. See `formalization.yaml` for scope, fidelity, and review
metadata.

## License

Apache License 2.0. See `LICENSE`.
