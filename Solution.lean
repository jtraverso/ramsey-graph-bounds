/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib
public import RamseyLib.Bounds

/-!
# Proofs of the statements in `Challenge.lean`

The proofs are in `RamseyLib/Bounds.lean`: a Finset form of the Erdős–Szekeres recursion (split
the vertices into the neighbours and the non-neighbours of a vertex, and use Pascal's rule), the
pentagon for `R(3, 3) > 5`, and a union bound over the edge sets of graphs on `Fin n` for Erdős's
lower bound.
-/

@[expose] public section

open SimpleGraph

namespace RamseyGraphs

/-- **`R(3, 3) ≤ 6`.** Every graph on six vertices contains a triangle or an independent set of
size three. -/
theorem ramsey_three_three_upper (G : SimpleGraph (Fin 6)) :
    ¬ G.CliqueFree 3 ∨ ¬ Gᶜ.CliqueFree 3 :=
  RamseyLib.ramsey_three_three_upper G

/-- **`R(3, 3) > 5`.** The pentagon has neither a triangle nor an independent set of size
three. -/
theorem ramsey_three_three_lower :
    ∃ G : SimpleGraph (Fin 5), G.CliqueFree 3 ∧ Gᶜ.CliqueFree 3 :=
  RamseyLib.ramsey_three_three_lower

/-- **Erdős–Szekeres (1935).** Every graph on at least `(s + t - 2).choose (s - 1)` vertices
contains `K_s` or an independent set of size `t`. -/
theorem erdos_szekeres {V : Type*} [Fintype V] (G : SimpleGraph V) (s t : ℕ) (hs : 1 ≤ s)
    (ht : 1 ≤ t) (hV : (s + t - 2).choose (s - 1) ≤ Fintype.card V) :
    ¬ G.CliqueFree s ∨ ¬ Gᶜ.CliqueFree t :=
  RamseyLib.erdos_szekeres G s t hs ht hV

/-- **Erdős (1947).** For `k ≥ 3` and `n ≤ 2 ^ (k / 2)` there is a graph on `n` vertices with
neither `K_k` nor an independent set of size `k`. -/
theorem erdos_lower_bound (k : ℕ) (hk : 3 ≤ k) (n : ℕ) (hn : (n : ℝ) ≤ 2 ^ ((k : ℝ) / 2)) :
    ∃ G : SimpleGraph (Fin n), G.CliqueFree k ∧ Gᶜ.CliqueFree k :=
  RamseyLib.erdos_lower_bound k hk n hn

end RamseyGraphs
