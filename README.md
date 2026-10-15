# Classical bounds for graph Ramsey numbers in Lean 4

Author and maintainer: **Juan Pablo Traverso Gianini**. Licence: Apache-2.0 (see `LICENSE`).

## Results

The Ramsey number `R(s, t)` is the least `n` such that every graph on `n` vertices contains a
clique of size `s` or an independent set of size `t`. This repository formalizes:

1. **`R(3, 3) = 6`** (Greenwood–Gleason, 1955):
   - every graph on six vertices has a triangle or three independent vertices
     (`RamseyGraphs.ramsey_three_three_upper`);
   - the pentagon has neither (`RamseyGraphs.ramsey_three_three_lower`).
2. **Erdős–Szekeres (1935):** `R(s, t) ≤ C(s + t − 2, s − 1)` (`RamseyGraphs.erdos_szekeres`).
3. **Erdős (1947):** for `k ≥ 3` there is a graph on `n = ⌊2^{k/2}⌋` vertices, or fewer, with
   neither `K_k` nor an independent set of size `k`. So `R(k, k) > 2^{k/2}`
   (`RamseyGraphs.erdos_lower_bound`).

In Lean, a graph contains `K_s` when it is not `s`-clique-free (`SimpleGraph.CliqueFree`). It
contains an independent set of size `t` when its complement `Gᶜ` is not `t`-clique-free.

## Files

- [`Challenge.lean`](Challenge.lean): the audited statements. It imports only Mathlib.
- [`Solution.lean`](Solution.lean) and [`RamseyLib/Bounds.lean`](RamseyLib/Bounds.lean): the
  proofs.
- [`comparator.json`](comparator.json): the theorems that are compared.
- [`MATHLIB_DEFINITIONS.md`](MATHLIB_DEFINITIONS.md): verbatim copies of the Mathlib definitions
  used.
- [`formalization.yaml`](formalization.yaml): provenance, sources and process.

## How the proofs go

* **Erdős–Szekeres.** First a Finset version: every vertex set `S` with
  `C(s + t, s) ≤ |S|` contains an `(s+1)`-clique of `G` or a `(t+1)`-clique of `Gᶜ`. The proof is
  by induction. Pick a vertex `v ∈ S` and split the rest of `S` into the neighbours and the
  non-neighbours of `v`. By Pascal's rule one of the two parts is large enough, and induction
  inside it, plus `v`, gives the clique. `R(3, 3) ≤ 6` is the case `s = t = 3`.
* **`R(3, 3) > 5`.** The 5-cycle and its complement, again a 5-cycle, are triangle-free. This is a
  finite check.
* **Erdős's lower bound.** A union bound over the `2^{C(n,2)}` edge sets on `Fin n`. A given
  `k`-set is a clique, or is independent, in `2^{C(n,2) − C(k,2)}` of them. So a good graph
  exists once `2 · C(n,k) < 2^{C(k,2)}`. When `n² ≤ 2^k` this follows from
  `C(n,k) · k! ≤ n^k` and `4 · 2^k < (k!)²` for `k ≥ 3`.

## Sources

* P. Erdős, G. Szekeres, *A combinatorial problem in geometry*, Compositio Math. 2 (1935)
  463–470 (http://www.numdam.org/item/CM_1935__2__463_0/).
* P. Erdős, *Some remarks on the theory of graphs*, Bull. Amer. Math. Soc. 53 (1947) 292–294,
  doi:10.1090/S0002-9904-1947-08785-1.
* R. E. Greenwood, A. M. Gleason, *Combinatorial relations and chromatic graphs*, Canad. J. Math.
  7 (1955) 1–7, doi:10.4153/CJM-1955-001-4.

## Authorship and use of AI

The author chose the results. The statements and proof plans were written with Claude in Claude
Code. Harmonic's Aristotle produced the proofs, which were audited and rebuilt locally. Lean
checks everything mechanically. See `formalization.yaml`.

## Building

Lean `v4.35.0-rc3`, Mathlib `c55e6e786f49471c72fbddbec5415808896aec1e`:

```bash
lake exe cache get
lake build
```
