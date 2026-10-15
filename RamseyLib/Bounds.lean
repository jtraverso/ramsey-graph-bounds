/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

/-!
# Classical bounds for graph Ramsey numbers (proofs)

A graph `G` on `n` vertices "contains" `K_s` when it is not `s`-clique-free, and contains an
independent set of size `t` when its complement `Gᶜ` is not `t`-clique-free. The Ramsey number
`R(s, t)` is the least `n` such that every graph on `n` vertices contains `K_s` or an independent
set of size `t`.

* `ramsey_three_three_upper`, `ramsey_three_three_lower`: `R(3, 3) = 6` (Greenwood–Gleason 1955).
* `erdos_szekeres`: `R(s, t) ≤ (s + t - 2).choose (s - 1)` (Erdős–Szekeres 1935).
* `erdos_lower_bound`: `R(k, k) > 2 ^ (k / 2)` for `k ≥ 3` (Erdős 1947).
-/

@[expose] public section

open SimpleGraph

namespace RamseyLib

/-- Finset version of Erdős–Szekeres: every Finset `S` with `(s + t).choose s ≤ |S|` contains an
`(s + 1)`-clique of `G` or a `(t + 1)`-clique of `Gᶜ`. -/
theorem es_finset {V : Type*} (G : SimpleGraph V) :
    ∀ (s t : ℕ) (S : Finset V), (s + t).choose s ≤ S.card →
      (∃ T ⊆ S, G.IsNClique (s + 1) T) ∨ (∃ T ⊆ S, Gᶜ.IsNClique (t + 1) T) := by
  classical
  intro s
  induction s with
  | zero =>
    intro t S hS
    rw [Nat.choose_zero_right, Finset.one_le_card] at hS
    obtain ⟨v, hv⟩ := hS
    exact Or.inl ⟨{v}, by simpa using hv, by simp⟩
  | succ s ihs =>
    intro t
    induction t with
    | zero =>
      intro S hS
      rw [add_zero, Nat.choose_self, Finset.one_le_card] at hS
      obtain ⟨v, hv⟩ := hS
      exact Or.inr ⟨{v}, by simpa using hv, by simp⟩
    | succ t iht =>
      intro S hS
      have hpos : 0 < S.card := lt_of_lt_of_le (Nat.choose_pos (by omega)) hS
      obtain ⟨v, hv⟩ := Finset.card_pos.mp hpos
      set N := (S.erase v).filter (fun w => G.Adj v w) with hN
      set M := (S.erase v).filter (fun w => ¬ G.Adj v w) with hM
      have hcard : N.card + M.card = S.card - 1 := by
        rw [hN, hM, Finset.card_filter_add_card_filter_not, Finset.card_erase_of_mem hv]
      have hpas : (s + 1 + (t + 1)).choose (s + 1) =
          (s + (t + 1)).choose s + (s + 1 + t).choose (s + 1) := by
        rw [show s + 1 + (t + 1) = (s + 1 + t) + 1 by omega, Nat.choose_succ_succ,
          show s + 1 + t = s + (t + 1) by omega]
      have hNS : N ⊆ S := fun x hx => Finset.mem_of_mem_erase (Finset.mem_of_mem_filter _ hx)
      have hMS : M ⊆ S := fun x hx => Finset.mem_of_mem_erase (Finset.mem_of_mem_filter _ hx)
      by_cases hNc : (s + (t + 1)).choose s ≤ N.card
      · rcases ihs (t + 1) N hNc with ⟨T, hT, hc⟩ | ⟨T, hT, hc⟩
        · left
          refine ⟨insert v T, Finset.insert_subset hv (hT.trans hNS), ?_⟩
          refine hc.insert fun b hb => ?_
          exact (Finset.mem_filter.1 (hT hb)).2
        · exact Or.inr ⟨T, hT.trans hNS, hc⟩
      · have hMc : (s + 1 + t).choose (s + 1) ≤ M.card := by omega
        rcases iht M hMc with ⟨T, hT, hc⟩ | ⟨T, hT, hc⟩
        · exact Or.inl ⟨T, hT.trans hMS, hc⟩
        · right
          refine ⟨insert v T, Finset.insert_subset hv (hT.trans hMS), ?_⟩
          refine hc.insert fun b hb => ?_
          have hb' := Finset.mem_filter.1 (hT hb)
          rw [compl_adj]
          exact ⟨fun h => Finset.ne_of_mem_erase hb'.1 h.symm, hb'.2⟩


/-- **`R(3, 3) ≤ 6`.** Every graph on six vertices contains a triangle or an independent set of
size three. -/
theorem ramsey_three_three_upper (G : SimpleGraph (Fin 6)) :
    ¬ G.CliqueFree 3 ∨ ¬ Gᶜ.CliqueFree 3 := by
  classical
  rcases es_finset G 2 2 Finset.univ (by simp [Nat.choose]) with ⟨T, -, hT⟩ | ⟨T, -, hT⟩
  · exact Or.inl fun hf => hf T hT
  · exact Or.inr fun hf => hf T hT

/-- **`R(3, 3) > 5`.** The pentagon has neither a triangle nor an independent set of size
three. -/
theorem ramsey_three_three_lower :
    ∃ G : SimpleGraph (Fin 5), G.CliqueFree 3 ∧ Gᶜ.CliqueFree 3 := by
  refine ⟨SimpleGraph.fromRel (fun i j : Fin 5 => j = i + 1), ?_, ?_⟩
  · rw [← cliqueFinset_eq_empty_iff]; decide
  · rw [← cliqueFinset_eq_empty_iff]; decide

/-- **Erdős–Szekeres (1935).** Every graph on at least `(s + t - 2).choose (s - 1)` vertices
contains `K_s` or an independent set of size `t`. -/
theorem erdos_szekeres {V : Type*} [Fintype V] (G : SimpleGraph V) (s t : ℕ) (hs : 1 ≤ s)
    (ht : 1 ≤ t) (hV : (s + t - 2).choose (s - 1) ≤ Fintype.card V) :
    ¬ G.CliqueFree s ∨ ¬ Gᶜ.CliqueFree t := by
  classical
  obtain ⟨s, rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
  obtain ⟨t, rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  have h : (s + t).choose s ≤ (Finset.univ : Finset V).card := by
    simpa [show s + 1 + (t + 1) - 2 = s + t by omega] using hV
  rcases es_finset G s t _ h with ⟨T, -, hT⟩ | ⟨T, -, hT⟩
  · exact Or.inl fun hf => hf T hT
  · exact Or.inr fun hf => hf T hT

lemma card_offDiag_sym2 {α : Type*} [DecidableEq α] (S : Finset α) :
    (S.sym2.filter (fun e => ¬ e.IsDiag)).card = S.card.choose 2 := by
  have h := Finset.card_filter_add_card_filter_not (s := S.sym2) (p := Sym2.IsDiag)
  have hd : S.sym2.filter Sym2.IsDiag = S.image Sym2.diag := by
    ext e
    induction e using Sym2.ind with
    | _ a b =>
      simp only [Finset.mem_filter, Finset.mk_mem_sym2_iff, Sym2.mk_isDiag_iff, Finset.mem_image]
      constructor
      · rintro ⟨⟨ha, -⟩, rfl⟩; exact ⟨a, ha, rfl⟩
      · rintro ⟨c, hc, hce⟩
        rw [Sym2.diag, Sym2.eq_iff] at hce
        rcases hce with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact ⟨⟨hc, hc⟩, rfl⟩
  have hc : (S.card + 1).choose 2 = S.card + S.card.choose 2 := by
    rw [Nat.choose_succ_left _ _ (by norm_num)]; simp
  rw [hd, Finset.card_image_of_injective _ Sym2.diag_injective, Finset.card_sym2, hc] at h
  omega

lemma two_mul_choose_add (k : ℕ) : 2 * k.choose 2 + k = k ^ 2 := by
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.choose_succ_succ, Nat.choose_one_right]; nlinarith

lemma four_mul_two_pow_lt_factorial_sq (k : ℕ) (hk : 3 ≤ k) : 4 * 2 ^ k < (k.factorial) ^ 2 := by
  induction k, hk using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
    rw [Nat.factorial_succ, pow_succ, mul_pow]
    have h2 : 2 ≤ (k + 1) ^ 2 := by nlinarith
    nlinarith [Nat.mul_le_mul_right (k.factorial ^ 2) h2]

lemma two_mul_choose_lt (k n : ℕ) (hk : 3 ≤ k) (hn : n ^ 2 ≤ 2 ^ k) :
    2 * n.choose k < 2 ^ (k.choose 2) := by
  have h1 : n.choose k * k.factorial ≤ n ^ k := by
    rw [mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose]
    exact Nat.descFactorial_le_pow n k
  have h2 := four_mul_two_pow_lt_factorial_sq k hk
  have h3 := two_mul_choose_add k
  have key : (2 * n.choose k * k.factorial) ^ 2 < (2 ^ (k.choose 2) * k.factorial) ^ 2 := by
    calc (2 * n.choose k * k.factorial) ^ 2 = 4 * (n.choose k * k.factorial) ^ 2 := by ring
      _ ≤ 4 * (n ^ k) ^ 2 := by gcongr
      _ = 4 * (n ^ 2) ^ k := by ring
      _ ≤ 4 * (2 ^ k) ^ k := by gcongr
      _ = 4 * 2 ^ k * 2 ^ (2 * k.choose 2) := by
        rw [← pow_mul, mul_assoc, ← pow_add]; congr 2; nlinarith
      _ < (k.factorial) ^ 2 * 2 ^ (2 * k.choose 2) := by gcongr
      _ = (2 ^ (k.choose 2) * k.factorial) ^ 2 := by ring
  have := lt_of_pow_lt_pow_left₀ 2 (by positivity) key
  exact Nat.lt_of_mul_lt_mul_right this

/-- **Erdős (1947).** For `k ≥ 3` and `n ≤ 2 ^ (k / 2)` there is a graph on `n` vertices with
neither `K_k` nor an independent set of size `k`. -/
theorem erdos_lower_bound (k : ℕ) (hk : 3 ≤ k) (n : ℕ) (hn : (n : ℝ) ≤ 2 ^ ((k : ℝ) / 2)) :
    ∃ G : SimpleGraph (Fin n), G.CliqueFree k ∧ Gᶜ.CliqueFree k := by
  classical
  have hn2 : n ^ 2 ≤ 2 ^ k := by
    have : ((n : ℝ)) ^ 2 ≤ (2 : ℝ) ^ k := by
      calc (n : ℝ) ^ 2 ≤ ((2 : ℝ) ^ ((k : ℝ) / 2)) ^ 2 := pow_le_pow_left₀ (by positivity) hn 2
        _ = 2 ^ k := by
          rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (by norm_num)]
          norm_num
    exact_mod_cast this
  set P : Finset (Fin n) → Finset (Sym2 (Fin n)) :=
    fun S => S.sym2.filter (fun e => ¬ e.IsDiag) with hP
  set E := P Finset.univ with hE
  have hPE : ∀ S, P S ⊆ E := fun S => by
    intro e he
    simp only [hP, hE, Finset.mem_filter] at he ⊢
    exact ⟨Finset.sym2_mono (Finset.subset_univ S) he.1, he.2⟩
  set B := (Finset.univ.powersetCard k).biUnion (fun S =>
    E.powerset.filter (fun X => P S ⊆ X) ∪ E.powerset.filter (fun X => Disjoint (P S) X)) with hB
  have hcount : ∀ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
      (E.powerset.filter (fun X => P S ⊆ X) ∪
        E.powerset.filter (fun X => Disjoint (P S) X)).card ≤
        2 * 2 ^ (n.choose 2 - k.choose 2) := by
    intro S hS
    have hSc : S.card = k := (Finset.mem_powersetCard.1 hS).2
    have hcd : (E \ P S).card = n.choose 2 - k.choose 2 := by
      rw [Finset.card_sdiff_of_subset (hPE S), hE, hP, card_offDiag_sym2, card_offDiag_sym2,
        Finset.card_univ, Fintype.card_fin, hSc]
    have h1 : E.powerset.filter (fun X => P S ⊆ X) ⊆
        (E \ P S).powerset.image (fun Y => Y ∪ P S) := by
      intro X hX
      rw [Finset.mem_filter, Finset.mem_powerset] at hX
      rw [Finset.mem_image]
      exact ⟨X \ P S, Finset.mem_powerset.2 (Finset.sdiff_subset_sdiff hX.1 le_rfl),
        Finset.sdiff_union_of_subset hX.2⟩
    have h2 : E.powerset.filter (fun X => Disjoint (P S) X) ⊆ (E \ P S).powerset := by
      intro X hX
      rw [Finset.mem_filter, Finset.mem_powerset] at hX
      exact Finset.mem_powerset.2 (Finset.subset_sdiff.2 ⟨hX.1, hX.2.symm⟩)
    calc _ ≤ _ := Finset.card_union_le _ _
      _ ≤ ((E \ P S).powerset.image (fun Y => Y ∪ P S)).card + (E \ P S).powerset.card :=
          add_le_add (Finset.card_le_card h1) (Finset.card_le_card h2)
      _ ≤ (E \ P S).powerset.card + (E \ P S).powerset.card :=
          Nat.add_le_add_right Finset.card_image_le _
      _ = 2 * 2 ^ (n.choose 2 - k.choose 2) := by rw [Finset.card_powerset, hcd]; ring
  have hEc : E.card = n.choose 2 := by
    rw [hE, hP, card_offDiag_sym2, Finset.card_univ, Fintype.card_fin]
  have hBlt : B.card < E.powerset.card := by
    rw [Finset.card_powerset, hEc]
    calc B.card ≤ ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
          (E.powerset.filter (fun X => P S ⊆ X) ∪
            E.powerset.filter (fun X => Disjoint (P S) X)).card := Finset.card_biUnion_le
      _ ≤ ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
          2 * 2 ^ (n.choose 2 - k.choose 2) := Finset.sum_le_sum hcount
      _ = n.choose k * (2 * 2 ^ (n.choose 2 - k.choose 2)) := by
          rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
            smul_eq_mul]
      _ < 2 ^ n.choose 2 := by
          rcases lt_or_ge n k with hnk | hnk
          · rw [Nat.choose_eq_zero_of_lt hnk, zero_mul]; positivity
          · have hK : k.choose 2 ≤ n.choose 2 := Nat.choose_le_choose 2 hnk
            have := two_mul_choose_lt k n hk hn2
            calc n.choose k * (2 * 2 ^ (n.choose 2 - k.choose 2))
                = (2 * n.choose k) * 2 ^ (n.choose 2 - k.choose 2) := by ring
              _ < 2 ^ k.choose 2 * 2 ^ (n.choose 2 - k.choose 2) := by gcongr
              _ = 2 ^ n.choose 2 := by rw [← pow_add]; congr 1; omega
  obtain ⟨X, hXE, hXB⟩ := Finset.exists_mem_notMem_of_card_lt_card hBlt
  rw [Finset.mem_powerset] at hXE
  refine ⟨fromEdgeSet (X : Set (Sym2 (Fin n))), ?_, ?_⟩
  · intro S hS
    apply hXB
    rw [hB, Finset.mem_biUnion]
    refine ⟨S, Finset.mem_powersetCard.2 ⟨Finset.subset_univ _, hS.card_eq⟩,
      Finset.mem_union_left _ (Finset.mem_filter.2 ⟨Finset.mem_powerset.2 hXE, ?_⟩)⟩
    intro e he
    induction e using Sym2.ind with
    | _ a b =>
      simp only [hP, Finset.mem_filter, Finset.mk_mem_sym2_iff, Sym2.mk_isDiag_iff] at he
      have := hS.1 (Finset.mem_coe.2 he.1.1) (Finset.mem_coe.2 he.1.2) he.2
      rw [fromEdgeSet_adj] at this
      exact this.1
  · intro S hS
    apply hXB
    rw [hB, Finset.mem_biUnion]
    refine ⟨S, Finset.mem_powersetCard.2 ⟨Finset.subset_univ _, hS.card_eq⟩,
      Finset.mem_union_right _ (Finset.mem_filter.2 ⟨Finset.mem_powerset.2 hXE, ?_⟩)⟩
    rw [Finset.disjoint_left]
    intro e he
    induction e using Sym2.ind with
    | _ a b =>
      simp only [hP, Finset.mem_filter, Finset.mk_mem_sym2_iff, Sym2.mk_isDiag_iff] at he
      have := hS.1 (Finset.mem_coe.2 he.1.1) (Finset.mem_coe.2 he.1.2) he.2
      rw [compl_adj, fromEdgeSet_adj] at this
      exact fun hX => this.2 ⟨hX, he.2⟩

end RamseyLib
