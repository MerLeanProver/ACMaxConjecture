# arXiv v2 manuscript

This directory contains the self-contained mathematical proof of the ACMAX
conjecture for every `n >= 4`.

The proof uses three overlapping arguments: an exact Moore argument for
`n >= 48`, an incidence argument for `32 <= n <= 49`, and local sparse-set and
cut arguments for `4 <= n <= 31`. The main source is `main.tex`; longer range
arguments are kept in `sections/`.

Build the paper from this directory with:

```bash
latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=build main.tex
```

Recheck its finite arithmetic with:

```bash
python tools/verify_moore_closure_arithmetic.py
python tools/verify_short_range_arithmetic.py
```

The mathematical human audit is complete. Comments in `main.tex` still mark
project-owner tasks concerning final author attribution, billing figures,
acknowledgments, and an immutable software citation.
