/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

/-!
# Classical bounds for graph Ramsey numbers

A graph `G` on `n` vertices "contains" `K_s` when it is not `s`-clique-free, and contains an
independent set of size `t` when its complement `Gᶜ` is not `t`-clique-free. The Ramsey number
`R(s, t)` is the least `n` such that every graph on `n` vertices contains `K_s` or an independent
set of size `t`.

* `ramsey_three_three_upper`, `ramsey_three_three_lower`: `R(3, 3) = 6` (Greenwood–Gleason 1955).
* `erdos_szekeres`: `R(s, t) ≤ (s + t - 2).choose (s - 1)` (Erdős–Szekeres 1935).
* `erdos_lower_bound`: `R(k, k) > 2 ^ (k / 2)` for `k ≥ 3` (Erdős 1947).

The Mathlib definitions used in these statements are reproduced verbatim, with file and line at the
pinned Mathlib revision, in `MATHLIB_DEFINITIONS.md` at the root of this repository.
-/

@[expose] public section

open SimpleGraph

namespace RamseyGraphs

/-- **`R(3, 3) ≤ 6`.** Every graph on six vertices contains a triangle or an independent set of
size three. -/
theorem ramsey_three_three_upper (G : SimpleGraph (Fin 6)) :
    ¬ G.CliqueFree 3 ∨ ¬ Gᶜ.CliqueFree 3 := by
  sorry

/-- **`R(3, 3) > 5`.** The pentagon has neither a triangle nor an independent set of size
three. -/
theorem ramsey_three_three_lower :
    ∃ G : SimpleGraph (Fin 5), G.CliqueFree 3 ∧ Gᶜ.CliqueFree 3 := by
  sorry

/-- **Erdős–Szekeres (1935).** Every graph on at least `(s + t - 2).choose (s - 1)` vertices
contains `K_s` or an independent set of size `t`. -/
theorem erdos_szekeres {V : Type*} [Fintype V] (G : SimpleGraph V) (s t : ℕ) (hs : 1 ≤ s)
    (ht : 1 ≤ t) (hV : (s + t - 2).choose (s - 1) ≤ Fintype.card V) :
    ¬ G.CliqueFree s ∨ ¬ Gᶜ.CliqueFree t := by
  sorry

/-- **Erdős (1947).** For `k ≥ 3` and `n ≤ 2 ^ (k / 2)` there is a graph on `n` vertices with
neither `K_k` nor an independent set of size `k`. -/
theorem erdos_lower_bound (k : ℕ) (hk : 3 ≤ k) (n : ℕ) (hn : (n : ℝ) ≤ 2 ^ ((k : ℝ) / 2)) :
    ∃ G : SimpleGraph (Fin n), G.CliqueFree k ∧ Gᶜ.CliqueFree k := by
  sorry

end RamseyGraphs
