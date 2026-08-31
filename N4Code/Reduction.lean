import N4Code.TwoColumn
import Mathlib.Tactic.IntervalCases

/-!
# Phase E: the main reductions (paper §3.4)

Theorem `thm:even` (Theorem 8) (the 1-bit flip) is the engine behind `cor:twopo` (Corollary 9),
`cor:onepo` (Corollary 10), and `thm:class2` (Lemma 14); together with `thm:odd` (Theorem 11) (`two_bit_flip`,
proved in `TwoColumn.lean`) and `thm:0column` (Theorem 6) it yields `thm:two` (Theorem 1),
`lm:all` (Lemma 15), `thm:nbig3` (Theorem 3), and `thm:condition_optimalcode` (Theorem 4).

The statements are the placeholder stubs in `N4Code/Statements.lean` (§3.4);
prove them here and replace each stub with a comment pointing back (as done
for `thm:0column` (Theorem 6) in `ZeroColumn.lean` and `thm:odd` (Theorem 11) in `TwoColumn.lean`).
-/

namespace N4Code

open scoped BigOperators

/-! ## One-bit flip distance facts (`thm:even` (Theorem 8) prerequisites) -/

/-- Flipping bit t of y changes the row-i distance by ∓1 when the changed
column is type 1 and row i of the column is true. -/
lemma dRow_flip_col1_true {n : ℕ} (C : Code n) (t : Fin n) (y : Word n)
    (hcol : C t = col1) (i : Fin 4) (hb : colBit i col1 = true) :
    (y t = true → dRow C i (flipBit t y) = dRow C i y + 1) ∧
      (y t = false → dRow C i (flipBit t y) = dRow C i y - 1) := by
  rw [dRow_eq_hammingDist, dRow_eq_hammingDist]
  have ht0 : (row C i) t = true := by
    unfold row
    rw [hcol]
    exact hb
  constructor
  · intro hyt
    unfold hammingDist hammingWeight
    have hsplit_new := sum_split_at
      (fun u : Fin n => if bitXor (row C i) (flipBit t y) u = true then 1 else 0) t
    have hsplit_old := sum_split_at
      (fun u : Fin n => if bitXor (row C i) y u = true then 1 else 0) t
    have hS : (∑ u ∈ (Finset.univ.erase t),
        if bitXor (row C i) (flipBit t y) u = true then 1 else 0) =
        ∑ u ∈ (Finset.univ.erase t), if bitXor (row C i) y u = true then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro u hu
      have ht : u ≠ t := (Finset.mem_erase.mp hu).1
      simp [bitXor, flipBit, ht]
    have htnew : (if bitXor (row C i) (flipBit t y) t = true then 1 else 0) = 1 := by
      have : bitXor (row C i) (flipBit t y) t = true := by
        simp [bitXor, flipBit, ht0, hyt]
      simp [this]
    have htold : (if bitXor (row C i) y t = true then 1 else 0) = 0 := by
      have : bitXor (row C i) y t = false := by
        simp [bitXor, ht0, hyt]
      simp [this]
    rw [hsplit_new, hsplit_old, hS, htnew, htold]
  · intro hyt
    unfold hammingDist hammingWeight
    have hsplit_new := sum_split_at
      (fun u : Fin n => if bitXor (row C i) (flipBit t y) u = true then 1 else 0) t
    have hsplit_old := sum_split_at
      (fun u : Fin n => if bitXor (row C i) y u = true then 1 else 0) t
    have hS : (∑ u ∈ (Finset.univ.erase t),
        if bitXor (row C i) (flipBit t y) u = true then 1 else 0) =
        ∑ u ∈ (Finset.univ.erase t), if bitXor (row C i) y u = true then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro u hu
      have ht : u ≠ t := (Finset.mem_erase.mp hu).1
      simp [bitXor, flipBit, ht]
    have htnew : (if bitXor (row C i) (flipBit t y) t = true then 1 else 0) = 0 := by
      have : bitXor (row C i) (flipBit t y) t = false := by
        simp [bitXor, flipBit, ht0, hyt]
      simp [this]
    have htold : (if bitXor (row C i) y t = true then 1 else 0) = 1 := by
      have : bitXor (row C i) y t = true := by
        simp [bitXor, ht0, hyt]
      simp [this]
    rw [hsplit_new, hsplit_old, hS, htnew, htold]
    omega

/-- Flipping bit t of y changes the row-i distance by ∓1 when the changed
column is type 1 and row i of the column is false. -/
lemma dRow_flip_col1_false {n : ℕ} (C : Code n) (t : Fin n) (y : Word n)
    (hcol : C t = col1) (i : Fin 4) (hb : colBit i col1 = false) :
    (y t = true → dRow C i (flipBit t y) = dRow C i y - 1) ∧
      (y t = false → dRow C i (flipBit t y) = dRow C i y + 1) := by
  rw [dRow_eq_hammingDist, dRow_eq_hammingDist]
  have ht0 : (row C i) t = false := by
    unfold row
    rw [hcol]
    exact hb
  constructor
  · intro hyt
    unfold hammingDist hammingWeight
    have hsplit_new := sum_split_at
      (fun u : Fin n => if bitXor (row C i) (flipBit t y) u = true then 1 else 0) t
    have hsplit_old := sum_split_at
      (fun u : Fin n => if bitXor (row C i) y u = true then 1 else 0) t
    have hS : (∑ u ∈ (Finset.univ.erase t),
        if bitXor (row C i) (flipBit t y) u = true then 1 else 0) =
        ∑ u ∈ (Finset.univ.erase t), if bitXor (row C i) y u = true then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro u hu
      have ht : u ≠ t := (Finset.mem_erase.mp hu).1
      simp [bitXor, flipBit, ht]
    have htnew : (if bitXor (row C i) (flipBit t y) t = true then 1 else 0) = 0 := by
      have : bitXor (row C i) (flipBit t y) t = false := by
        simp [bitXor, flipBit, ht0, hyt]
      simp [this]
    have htold : (if bitXor (row C i) y t = true then 1 else 0) = 1 := by
      have : bitXor (row C i) y t = true := by
        simp [bitXor, ht0, hyt]
      simp [this]
    rw [hsplit_new, hsplit_old, hS, htnew, htold]
    omega
  · intro hyt
    unfold hammingDist hammingWeight
    have hsplit_new := sum_split_at
      (fun u : Fin n => if bitXor (row C i) (flipBit t y) u = true then 1 else 0) t
    have hsplit_old := sum_split_at
      (fun u : Fin n => if bitXor (row C i) y u = true then 1 else 0) t
    have hS : (∑ u ∈ (Finset.univ.erase t),
        if bitXor (row C i) (flipBit t y) u = true then 1 else 0) =
        ∑ u ∈ (Finset.univ.erase t), if bitXor (row C i) y u = true then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro u hu
      have ht : u ≠ t := (Finset.mem_erase.mp hu).1
      simp [bitXor, flipBit, ht]
    have htnew : (if bitXor (row C i) (flipBit t y) t = true then 1 else 0) = 1 := by
      have : bitXor (row C i) (flipBit t y) t = true := by
        simp [bitXor, flipBit, ht0, hyt]
      simp [this]
    have htold : (if bitXor (row C i) y t = true then 1 else 0) = 0 := by
      have : bitXor (row C i) y t = false := by
        simp [bitXor, ht0, hyt]
      simp [this]
    rw [hsplit_new, hsplit_old, hS, htnew, htold]

-- native_decide: Mechanical · n=any · checked 2026-08-27
/-- Row 2 of a type-1 column is false; row 3 is true. -/
lemma col1_bit2 : colBit ⟨2, by decide⟩ col1 = false := by native_decide
-- native_decide: Mechanical · n=any · checked 2026-08-27
lemma col1_bit3 : colBit ⟨3, by decide⟩ col1 = true := by native_decide

/-- Flipping bit t changes the row-2 distance by ±1 (changed column is type 1). -/
lemma dRow2_flip_col1 {n : ℕ} (C : Code n) (t : Fin n) (y : Word n)
    (hcol : C t = col1) :
    (y t = true → dRow C 2 (flipBit t y) = dRow C 2 y - 1) ∧
      (y t = false → dRow C 2 (flipBit t y) = dRow C 2 y + 1) := by
  simpa using dRow_flip_col1_false C t y hcol ⟨2, by decide⟩ col1_bit2

/-- Flipping bit t changes the row-3 distance by ∓1 (changed column is type 1). -/
lemma dRow3_flip_col1 {n : ℕ} (C : Code n) (t : Fin n) (y : Word n)
    (hcol : C t = col1) :
    (y t = true → dRow C 3 (flipBit t y) = dRow C 3 y + 1) ∧
      (y t = false → dRow C 3 (flipBit t y) = dRow C 3 y - 1) := by
  simpa using dRow_flip_col1_true C t y hcol ⟨3, by decide⟩ col1_bit3

/-- A row distance is at least one when y disagrees with the row at one position. -/
lemma dRow_ge_one_of_mismatch {n : ℕ} (C : Code n) (j : Fin 4) (t : Fin n) (y : Word n)
    (h : y t ≠ row C j t) : 1 ≤ dRow C j y := by
  rw [dRow_eq_hammingDist]
  unfold hammingDist hammingWeight
  have hsplit := sum_split_at (fun u : Fin n => if bitXor (row C j) y u = true then 1 else 0) t
  rw [hsplit]
  have ht : (if bitXor (row C j) y t = true then 1 else 0) = 1 := by
    have hxor : bitXor (row C j) y t = true := by
      cases hrow : row C j t <;> cases hy : y t <;> simp [bitXor, hrow, hy] at h ⊢
    simp [hxor]
  rw [ht]
  omega

/-- d_P(F_t y) = d_P(y) ∓ 1 for a type-1 changed column: the two branches of
paper Example 7 (s=1→s'=3), eq. (86) (d'_P = d_3 − y_1 + \bar y_1, i.e. d'₁ =
d_3 − 1 when y_t = 1 and d_3 + 1 when y_t = 0). -/
lemma dPp_eq_col1 {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) (hcol : C t = col1) :
    (y t = true → dPp C t y = dP C y - 1) ∧
      (y t = false → dPp C t y = dP C y + 1) := by
  constructor
  · intro hyt
    have h := (dRow2_flip_col1 C t y hcol).1 hyt
    unfold dPp dP
    change dRow C ⟨2, by decide⟩ (flipBit t y) = dRow C ⟨2, by decide⟩ y - 1
    exact h
  · intro hyt
    have h := (dRow2_flip_col1 C t y hcol).2 hyt
    unfold dPp dP
    change dRow C ⟨2, by decide⟩ (flipBit t y) = dRow C ⟨2, by decide⟩ y + 1
    exact h

-- native_decide: Mechanical · n=any · checked 2026-08-27
/-- d_O(F_t y) = min(d₁−1, d₂−1, d₄+1) for a type-1 changed column with
y_t = 1: the y_1 = 1 branch of paper Example 7 (s=1→s'=3), eq. (85)
(formula for d'_O); workhorse for the Class-I Y3/Y5 characterizations
(eqs. (271)-(274)). -/
lemma dOp_eq_min_col1 {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) (hcol : C t = col1)
    (hyt : y t = true) :
    dOp C t y = min (dRow C 0 y - 1) (min (dRow C 1 y - 1) (dRow C 3 y + 1)) := by
  unfold dOp dO
  change min (dRow C ⟨0, by decide⟩ (flipBit t y))
      (min (dRow C ⟨1, by decide⟩ (flipBit t y)) (dRow C ⟨3, by decide⟩ (flipBit t y))) =
    min (dRow C ⟨0, by decide⟩ y - 1) (min (dRow C ⟨1, by decide⟩ y - 1)
      (dRow C ⟨3, by decide⟩ y + 1))
  rw [((dRow_flip_col1_false C t y hcol ⟨0, by decide⟩ (by native_decide)).1 hyt),
    ((dRow_flip_col1_false C t y hcol ⟨1, by decide⟩ (by native_decide)).1 hyt),
    ((dRow_flip_col1_true C t y hcol ⟨3, by decide⟩ col1_bit3).1 hyt)]

/-- y ∈ Y5 forces y_t = true for a type-1 changed column. -/
lemma Y5_implies_htrue {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) (hcol : C t = col1)
    (hy : Y5 C t y) : y t = true := by
  rcases hy with ⟨hpp_eq, hop_eq, hlt⟩
  by_contra hnot
  have hyt : y t = false := Bool.eq_false_of_not_eq_true hnot
  have hdPp : dPp C t y = dP C y + 1 := (dPp_eq_col1 C t y hcol).2 hyt
  have hdO : dO C y = dP C y + 1 := by
    rw [← hpp_eq, hdPp]
  have hlt : dO C y < dP C y := by
    rw [hop_eq] at hlt
    exact hlt
  omega

/-- y ∈ Y5 forces d_P(y) = d₄(y) + 1 for a type-1 changed column. -/
lemma Y5_implies_dP_eq_dRow3_add_one {n : ℕ} (C : Code n) (t : Fin n) (y : Word n)
    (hcol : C t = col1) (hy : Y5 C t y) : dP C y = dRow C 3 y + 1 := by
  rcases hy with ⟨hpp_eq, hop_eq, hlt⟩
  have hyt : y t = true := Y5_implies_htrue C t y hcol ⟨hpp_eq, hop_eq, hlt⟩
  have hdPp : dPp C t y = dP C y - 1 := (dPp_eq_col1 C t y hcol).1 hyt
  have hdO : dO C y = dP C y - 1 := by
    rw [← hpp_eq, hdPp]
  have hdOp : dOp C t y = dP C y := hop_eq
  have hdOp' : dOp C t y = dO C y + 1 := by
    rw [hdOp, hdO]
    have hge : 1 ≤ dP C y := by
      unfold dP
      have hne : y t ≠ row C ⟨2, by decide⟩ t := by
        simp [row, hcol, colBit, col1, hyt]
      exact dRow_ge_one_of_mismatch C ⟨2, by decide⟩ t y hne
    omega
  have hdOp_min : dOp C t y =
      min (dRow C 0 y - 1) (min (dRow C 1 y - 1) (dRow C 3 y + 1)) :=
    dOp_eq_min_col1 C t y hcol hyt
  have hdOp_le0 : dOp C t y ≤ dRow C 0 y - 1 := by
    rw [hdOp_min]
    exact Nat.min_le_left _ _
  have hdOp_le1 : dOp C t y ≤ dRow C 1 y - 1 := by
    rw [hdOp_min]
    exact le_trans (Nat.min_le_right _ _) (Nat.min_le_left _ _)
  have hnot0 : dO C y ≠ dRow C 0 y := by
    intro h
    have hle : dO C y + 1 ≤ dRow C 0 y - 1 := by omega
    have hle' : dRow C 0 y - 1 < dO C y + 1 := by omega
    omega
  have hnot1 : dO C y ≠ dRow C 1 y := by
    intro h
    have hle : dO C y + 1 ≤ dRow C 1 y - 1 := by omega
    omega
  have hdO_eq : dO C y = dRow C 3 y := by
    have hdO_def : dO C y = min (dRow C 0 y) (min (dRow C 1 y) (dRow C 3 y)) := rfl
    by_cases h03 : dRow C 0 y ≤ min (dRow C 1 y) (dRow C 3 y)
    · have hdO0 : dO C y = dRow C 0 y := by
        rw [hdO_def, min_eq_left h03]
      exfalso
      exact hnot0 hdO0
    · have h03' : min (dRow C 1 y) (dRow C 3 y) < dRow C 0 y := lt_of_not_ge h03
      by_cases h13 : dRow C 1 y ≤ dRow C 3 y
      · have hdO1 : dO C y = dRow C 1 y := by
          rw [hdO_def, min_eq_right (le_of_lt h03'), min_eq_left h13]
        exfalso
        exact hnot1 hdO1
      · have h31 : dRow C 3 y < dRow C 1 y := lt_of_not_ge h13
        rw [hdO_def, min_eq_right (le_of_lt h03'), min_eq_right (le_of_lt h31)]
  omega

/-- d₂ + d₃ = w(c₃⊕c₄) + 2·K for some K (paper eq. in the proof of `thm:even` (Theorem 8)). -/
lemma dRow23_sum_decomp {n : ℕ} (C : Code n) (y : Word n) :
    ∃ K : ℕ, dRow C 2 y + dRow C 3 y =
      hammingDist (row2 C) (row3 C) + 2 * K := by
  refine ⟨∑ u : Fin n, if colBit 2 (C u) = colBit 3 (C u) then
    (if Bool.xor (colBit 2 (C u)) (y u) = true then 1 else 0) else 0, ?_⟩
  rw [dRow_eq_indicator_sum, dRow_eq_indicator_sum]
  rw [← Finset.sum_add_distrib]
  rw [hammingDist, hammingWeight]
  rw [show 2 * (∑ u : Fin n, if colBit 2 (C u) = colBit 3 (C u) then
        (if Bool.xor (colBit 2 (C u)) (y u) = true then 1 else 0) else 0) =
      ∑ u : Fin n, 2 * (if colBit 2 (C u) = colBit 3 (C u) then
        (if Bool.xor (colBit 2 (C u)) (y u) = true then 1 else 0) else 0) by
        rw [Finset.mul_sum]]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro u _
  have hper : (if colBit 2 (C u) ≠ y u then 1 else 0) +
        (if colBit 3 (C u) ≠ y u then 1 else 0) =
      (if colBit 2 (C u) ≠ colBit 3 (C u) then 1 else 0) +
        2 * (if colBit 2 (C u) = colBit 3 (C u) then
           (if Bool.xor (colBit 2 (C u)) (y u) = true then 1 else 0) else 0) := by
    cases h2 : colBit 2 (C u) <;> cases h3 : colBit 3 (C u) <;> cases hy : y u <;>
      simp [Bool.xor]
  rw [hper]
  cases h2 : colBit 2 (C u) <;> cases h3 : colBit 3 (C u) <;>
    simp [row, row2, row3, bitXor, Bool.xor, h2, h3]

/-- d_i + d_j = w(c_i⊕c_j) + 2·K for any two rows i,j. -/
lemma dRow23_sum_decomp_general {n : ℕ} (C : Code n) (i j : Fin 4) (y : Word n) :
    ∃ K : ℕ, dRow C i y + dRow C j y =
      hammingDist (row C i) (row C j) + 2 * K := by
  refine ⟨∑ u : Fin n, if colBit i (C u) = colBit j (C u) then
    (if Bool.xor (colBit i (C u)) (y u) = true then 1 else 0) else 0, ?_⟩
  rw [dRow_eq_indicator_sum, dRow_eq_indicator_sum]
  rw [← Finset.sum_add_distrib]
  rw [hammingDist, hammingWeight]
  rw [show 2 * (∑ u : Fin n, if colBit i (C u) = colBit j (C u) then
        (if Bool.xor (colBit i (C u)) (y u) = true then 1 else 0) else 0) =
      ∑ u : Fin n, 2 * (if colBit i (C u) = colBit j (C u) then
        (if Bool.xor (colBit i (C u)) (y u) = true then 1 else 0) else 0) by
        rw [Finset.mul_sum]]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro u _
  have hper : (if colBit i (C u) ≠ y u then 1 else 0) +
        (if colBit j (C u) ≠ y u then 1 else 0) =
      (if colBit i (C u) ≠ colBit j (C u) then 1 else 0) +
        2 * (if colBit i (C u) = colBit j (C u) then
           (if Bool.xor (colBit i (C u)) (y u) = true then 1 else 0) else 0) := by
    cases h2 : colBit i (C u) <;> cases h3 : colBit j (C u) <;> cases hy : y u <;>
      simp [Bool.xor]
  rw [hper]
  cases h2 : colBit i (C u) <;> cases h3 : colBit j (C u) <;>
    simp [row, bitXor, Bool.xor, h2, h3]

/-- d_i + d_j has the parity of w(c_i ⊕ c_j) for any two rows i,j
(paper eq. d_i+d_j = w(c_i⊕c_j) + 2K). -/
lemma dRow_ij_sum_parity {n : ℕ} (C : Code n) (i j : Fin 4) (y : Word n) :
    Even (dRow C i y + dRow C j y) ↔ Even (hammingDist (row C i) (row C j)) := by
  constructor
  · intro heven
    rcases heven with ⟨m, hm⟩
    rcases dRow23_sum_decomp_general C i j y with ⟨K, hK⟩
    have hle : K ≤ m := by
      have hd2 : hammingDist (row C i) (row C j) + 2 * K = 2 * m := by
        rw [← hK, hm]
        omega
      omega
    refine ⟨m - K, ?_⟩
    omega
  · intro heven
    rcases heven with ⟨m, hm⟩
    rcases dRow23_sum_decomp_general C i j y with ⟨K, hK⟩
    refine ⟨m + K, ?_⟩
    rw [hK, hm]
    omega

/-- y ∈ Y3 forces y_t = true for a type-1 changed column. -/
lemma Y3_implies_htrue {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) (hcol : C t = col1)
    (hy : Y3 C t y) : y t = true := by
  rcases hy with ⟨_hpp, hlt, _hdP⟩
  by_contra hnot
  have hyt : y t = false := Bool.eq_false_of_not_eq_true hnot
  have hdPp : dPp C t y = dP C y + 1 := (dPp_eq_col1 C t y hcol).2 hyt
  omega

/-- y ∈ Y3 forces d₂(y) = d₁(y) or d₂(y) = d₂(y) (row 2 equals row 0 or row 1). -/
lemma Y3_implies_dRow2_eq_dRow0_or_dRow1 {n : ℕ} (C : Code n) (t : Fin n) (y : Word n)
    (hcol : C t = col1) (hy : Y3 C t y) :
    dRow C 2 y = dRow C 0 y ∨ dRow C 2 y = dRow C 1 y := by
  rcases hy with ⟨hpp_eq, hlt, hdP_eq⟩
  have hyt : y t = true := Y3_implies_htrue C t y hcol ⟨hpp_eq, hlt, hdP_eq⟩
  have hdPp : dPp C t y = dP C y - 1 := (dPp_eq_col1 C t y hcol).1 hyt
  have hdOp_min : dOp C t y =
      min (dRow C 0 y - 1) (min (dRow C 1 y - 1) (dRow C 3 y + 1)) :=
    dOp_eq_min_col1 C t y hcol hyt
  have hpp_eq' : dP C y - 1 = min (dRow C 0 y - 1) (min (dRow C 1 y - 1) (dRow C 3 y + 1)) := by
    rw [← hdPp, ← hdOp_min]
    exact hpp_eq
  have hd2 : dRow C 2 y = min (dRow C 0 y) (min (dRow C 1 y) (dRow C 3 y)) := by
    unfold dP dO at hdP_eq
    simpa [dRow, row0, row1, row2, row3] using hdP_eq
  by_cases h03 : dRow C 0 y ≤ min (dRow C 1 y) (dRow C 3 y)
  · left
    rw [hd2, min_eq_left h03]
  · right
    have h30 : min (dRow C 1 y) (dRow C 3 y) < dRow C 0 y := lt_of_not_ge h03
    by_cases h13 : dRow C 1 y ≤ dRow C 3 y
    · rw [hd2, min_eq_right (le_of_lt h30), min_eq_left h13]
    · have h31 : dRow C 3 y < dRow C 1 y := lt_of_not_ge h13
      exfalso
      have hd3 : dRow C 2 y = dRow C 3 y := by
        rw [hd2, min_eq_right (le_of_lt h30), min_eq_right (le_of_lt h31)]
      have hdP3 : dP C y = dRow C 3 y := by
        change dRow C 2 y = dRow C 3 y
        exact hd3
      rw [hdP3] at hpp_eq'
      have hlt' : dRow C 3 y - 1 < dRow C 3 y := by
        rw [hdPp] at hlt
        rw [hdP3] at hlt
        exact hlt
      have hmin_ge : dRow C 3 y ≤ min (dRow C 0 y - 1) (min (dRow C 1 y - 1) (dRow C 3 y + 1)) := by
        apply le_min
        · omega
        · apply le_min <;> omega
      omega

/-- The odd-parity version of `dRow_ij_sum_parity`. -/
lemma dRow_ij_sum_parity_odd {n : ℕ} (C : Code n) (i j : Fin 4) (y : Word n) :
    Odd (dRow C i y + dRow C j y) ↔ Odd (hammingDist (row C i) (row C j)) := by
  constructor
  · intro hodd
    exact odd_of_not_even (fun heven =>
      not_even_of_odd hodd ((dRow_ij_sum_parity C i j y).mpr heven))
  · intro hodd
    exact odd_of_not_even (fun heven =>
      not_even_of_odd hodd ((dRow_ij_sum_parity C i j y).mp heven))

/-- `thm:even` (Theorem 8) equality (i): w(c₁⊕c₃) and w(c₂⊕c₃) both odd ⇒ Y3 = ∅. -/
theorem Y3_empty_of_w03_w13_odd {n : ℕ} (C : Code n) (t : Fin n) (hcol : C t = col1)
    (hw0 : Odd (hammingDist (row0 C) (row2 C)))
    (hw1 : Odd (hammingDist (row1 C) (row2 C))) :
    ∀ y : Word n, ¬ Y3 C t y := by
  intro y hy
  rcases Y3_implies_dRow2_eq_dRow0_or_dRow1 C t y hcol hy with hd0 | hd1
  · have hodd : Odd (dRow C 0 y + dRow C 2 y) :=
      (dRow_ij_sum_parity_odd C ⟨0, by decide⟩ ⟨2, by decide⟩ y).mpr hw0
    rw [hd0] at hodd
    rcases hodd with ⟨l, hl⟩
    omega
  · have hodd : Odd (dRow C 1 y + dRow C 2 y) :=
      (dRow_ij_sum_parity_odd C ⟨1, by decide⟩ ⟨2, by decide⟩ y).mpr hw1
    rw [hd1] at hodd
    rcases hodd with ⟨l, hl⟩
    omega

/-- A positive |1| count gives a type-1 column. -/
lemma exists_col1_of_count_pos {n : ℕ} (C : Code n) (h : 1 ≤ count C 1) :
    ∃ t : Fin n, C t = col1 := by
  rcases (count_pos_iff_exists C 1).mp (by omega : count C 1 > 0) with ⟨t, ht⟩
  exact ⟨t, (colVal_eq_one_iff_col1 (C t)).mp ht⟩

/-- If the counts over a type set S sum to n, every column has its type in S. -/
lemma colVal_mem_of_totalCounts {n : ℕ} (C : Code n) (S : Finset ℕ)
    (h : totalCounts C S = n) (t : Fin n) : colVal (C t) ∈ S := by
  by_contra hnot
  have hf : ∀ u : Fin n, u ∈ Finset.univ →
      (if colVal (C u) ∈ S then 1 else 0) ≤ 1 := by
    intro u _
    by_cases hu : colVal (C u) ∈ S <;> simp [hu]
  have hlt0 : (if colVal (C t) ∈ S then 1 else 0) < 1 := by
    simp [hnot]
  have hsumlt : (∑ u : Fin n, if colVal (C u) ∈ S then 1 else 0) <
      ∑ u : Fin n, (1 : ℕ) := by
    exact Finset.sum_lt_sum hf ⟨t, Finset.mem_univ t, hlt0⟩
  have hsum_eq : (∑ u : Fin n, if colVal (C u) ∈ S then 1 else 0) =
      totalCounts C S := by
    rw [show (∑ u : Fin n, if colVal (C u) ∈ S then 1 else 0) =
          ∑ u : Fin n, ∑ i ∈ S, if colVal (C u) = i then 1 else 0 by
          apply Finset.sum_congr rfl
          intro u _
          by_cases hu : colVal (C u) ∈ S
          · rw [Finset.sum_ite_eq]
          · simp [hu]]
    rw [totalCounts]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    unfold count
    rfl
  rw [hsum_eq, h] at hsumlt
  simp at hsumlt

/-- All columns of a {1,3,5,6}-code are in the set {1,3,5,6}. -/
lemma types_1356_of_totalCounts {n : ℕ} (C : Code n)
    (h : totalCounts C {1, 3, 5, 6} = n) (t : Fin n) :
    colVal (C t) = 1 ∨ colVal (C t) = 3 ∨ colVal (C t) = 5 ∨ colVal (C t) = 6 := by
  have hm : colVal (C t) ∈ ({1, 3, 5, 6} : Finset ℕ) :=
    colVal_mem_of_totalCounts C {1, 3, 5, 6} h t
  simp [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with h1 | h3 | h5 | h6
  · exact Or.inl h1
  · exact Or.inr (Or.inl h3)
  · exact Or.inr (Or.inr (Or.inl h5))
  · exact Or.inr (Or.inr (Or.inr h6))

-- native_decide: Mechanical · n=any · checked 2026-08-28
/-- w(c₃⊕c₄) = |1|+|5|+|6| for a code with only types 1,3,5,6. -/
lemma hammingDist_row2_row3_of_types1356 {n : ℕ} (C : Code n)
    (h : ∀ t : Fin n, colVal (C t) = 1 ∨ colVal (C t) = 3 ∨ colVal (C t) = 5 ∨ colVal (C t) = 6) :
    hammingDist (row2 C) (row3 C) = count C 1 + count C 5 + count C 6 := by
  have hS : ∀ t : Fin n, colVal (C t) ∈ ({1, 3, 5, 6} : Finset ℕ) := by
    intro t
    rcases h t with h1 | h3 | h5 | h6
    · simp [h1]
    · simp [h3]
    · simp [h5]
    · simp [h6]
  unfold row2 row3
  rw [hammingDist_rows_of_types C ⟨2, by decide⟩ ⟨3, by decide⟩ ({1, 3, 5, 6} : Finset ℕ) hS]
  have h1a : (1 : ℕ).testBit 1 = false := by native_decide
  have h3a : (3 : ℕ).testBit 1 = true := by native_decide
  have h5a : (5 : ℕ).testBit 1 = false := by native_decide
  have h6a : (6 : ℕ).testBit 1 = true := by native_decide
  simp [Finset.sum_insert, h1a, h3a, h5a, h6a]
  omega

-- native_decide: Mechanical · n=any · checked 2026-08-28
/-- w(c₁⊕c₃) = |3|+|6| for a code with only types 1,3,5,6. -/
lemma hammingDist_row0_row2_of_types1356 {n : ℕ} (C : Code n)
    (h : ∀ t : Fin n, colVal (C t) = 1 ∨ colVal (C t) = 3 ∨ colVal (C t) = 5 ∨ colVal (C t) = 6) :
    hammingDist (row0 C) (row2 C) = count C 3 + count C 6 := by
  have hS : ∀ t : Fin n, colVal (C t) ∈ ({1, 3, 5, 6} : Finset ℕ) := by
    intro t
    rcases h t with h1 | h3 | h5 | h6
    · simp [h1]
    · simp [h3]
    · simp [h5]
    · simp [h6]
  unfold row0 row2
  rw [hammingDist_rows_of_types C ⟨0, by decide⟩ ⟨2, by decide⟩ ({1, 3, 5, 6} : Finset ℕ) hS]
  have h1a : (1 : ℕ).testBit 3 = false := by native_decide
  have h1b : (1 : ℕ).testBit 1 = false := by native_decide
  have h3a : (3 : ℕ).testBit 3 = false := by native_decide
  have h3b : (3 : ℕ).testBit 1 = true := by native_decide
  have h5a : (5 : ℕ).testBit 3 = false := by native_decide
  have h5b : (5 : ℕ).testBit 1 = false := by native_decide
  have h6a : (6 : ℕ).testBit 3 = false := by native_decide
  have h6b : (6 : ℕ).testBit 1 = true := by native_decide
  simp [Finset.sum_insert, h1a, h1b, h3a, h3b, h5a, h5b, h6a, h6b]

-- native_decide: Mechanical · n=any · checked 2026-08-28
/-- w(c₂⊕c₃) = |3|+|5| for a code with only types 1,3,5,6. -/
lemma hammingDist_row1_row2_of_types1356 {n : ℕ} (C : Code n)
    (h : ∀ t : Fin n, colVal (C t) = 1 ∨ colVal (C t) = 3 ∨ colVal (C t) = 5 ∨ colVal (C t) = 6) :
    hammingDist (row1 C) (row2 C) = count C 3 + count C 5 := by
  have hS : ∀ t : Fin n, colVal (C t) ∈ ({1, 3, 5, 6} : Finset ℕ) := by
    intro t
    rcases h t with h1 | h3 | h5 | h6
    · simp [h1]
    · simp [h3]
    · simp [h5]
    · simp [h6]
  unfold row1 row2
  rw [hammingDist_rows_of_types C ⟨1, by decide⟩ ⟨2, by decide⟩ ({1, 3, 5, 6} : Finset ℕ) hS]
  have h1a : (1 : ℕ).testBit 2 = false := by native_decide
  have h1b : (1 : ℕ).testBit 1 = false := by native_decide
  have h3a : (3 : ℕ).testBit 2 = false := by native_decide
  have h3b : (3 : ℕ).testBit 1 = true := by native_decide
  have h5a : (5 : ℕ).testBit 2 = true := by native_decide
  have h5b : (5 : ℕ).testBit 1 = false := by native_decide
  have h6a : (6 : ℕ).testBit 2 = true := by native_decide
  have h6b : (6 : ℕ).testBit 1 = true := by native_decide
  simp [Finset.sum_insert, h1a, h1b, h3a, h3b, h5a, h5b, h6a, h6b]

-- native_decide: Mechanical · n=any · checked 2026-08-28
/-- Replacing a type-1 column by type 3 lowers |1| by one. -/
lemma count_replace_1_3_one {n : ℕ} (C : Code n) (t : Fin n) (ht : C t = col1) :
    count (replaceColumn C t col3) 1 = count C 1 - 1 := by
  exact count_replace_dec C t col3 1 (by rw [ht]; native_decide) (by native_decide)

-- native_decide: Mechanical · n=any · checked 2026-08-28
/-- Replacing a type-1 column by type 3 raises |3| by one. -/
lemma count_replace_1_3_three {n : ℕ} (C : Code n) (t : Fin n) (ht : C t = col1) :
    count (replaceColumn C t col3) 3 = count C 3 + 1 := by
  exact count_replace_inc C t col3 3 (by rw [ht]; native_decide) (by native_decide)

-- native_decide: Mechanical · n=any · checked 2026-08-28
/-- Counts of types other than 1 and 3 are unchanged by the 1→3 replacement. -/
lemma count_replace_1_3_other {n : ℕ} (C : Code n) (t : Fin n) (ht : C t = col1)
    (i : ℕ) (h1 : i ≠ 1) (h3 : i ≠ 3) :
    count (replaceColumn C t col3) i = count C i := by
  exact count_replace_eq C t col3 i
    (by rw [ht]; intro h; exact h1 (h.symm.trans (by native_decide : colVal col1 = 1)))
    (by intro h; exact h3 (h.symm.trans (by native_decide : colVal col3 = 3)))

/-- Two distinct positions of the same type give a count of at least two. -/
lemma count_ge_two_of_two {n : ℕ} (C : Code n) (i : ℕ) (t1 t2 : Fin n)
    (hne : t1 ≠ t2) (h1 : colVal (C t1) = i) (h2 : colVal (C t2) = i) :
    2 ≤ count C i := by
  have hmem1 : t1 ∈ (Finset.univ.filter fun t : Fin n => colVal (C t) = i) := by
    simp [h1]
  have hmem2 : t2 ∈ (Finset.univ.filter fun t : Fin n => colVal (C t) = i) := by
    simp [h2]
  have hpair : ({t1, t2} : Finset (Fin n)) ⊆
      (Finset.univ.filter fun t : Fin n => colVal (C t) = i) := by
    intro t ht
    simp [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl
    · exact hmem1
    · exact hmem2
  have hcard : 2 ≤ (Finset.univ.filter fun t : Fin n => colVal (C t) = i).card := by
    calc
      2 = ({t1, t2} : Finset (Fin n)).card := by
            rw [Finset.card_insert_of_notMem]
            · simp
            · simp [hne]
      _ ≤ (Finset.univ.filter fun t : Fin n => colVal (C t) = i).card :=
        Finset.card_le_card hpair
  simpa [count_eq_card] using hcard

-- native_decide: Mechanical · n=any · checked 2026-08-28
/-- colVal c = 7 iff c is the type-7 column. -/
lemma colVal_eq_seven_iff_col7 (c : Column) : colVal c = 7 ↔ c = col7 := by
  simpa [show colOfNat 7 = col7 by native_decide] using (colVal_eq_iff_colOfNat c 7 (by norm_num))

/-- A positive |7| count gives a type-7 column. -/
lemma exists_col7_of_count_pos {n : ℕ} (C : Code n) (h : 1 ≤ count C 7) :
    ∃ t : Fin n, C t = col7 := by
  rcases (count_pos_iff_exists C 7).mp (by omega : count C 7 > 0) with ⟨t, ht⟩
  exact ⟨t, (colVal_eq_seven_iff_col7 (C t)).mp ht⟩

-- native_decide: Mechanical · n=any · checked 2026-08-28
/-- Columns of a {1,3,5,6,7}-code have row 0 clear. -/
lemma Columns07_of_types_13567 {n : ℕ} (C : Code n)
    (h : totalCounts C {1, 3, 5, 6, 7} = n) : Columns07 C := by
  intro t
  have hm := colVal_mem_of_totalCounts C ({1, 3, 5, 6, 7} : Finset ℕ) h t
  simp [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with h1 | h3 | h5 | h6 | h7
  · change colBit ⟨0, by decide⟩ (C t) = false
    rw [colBit_eq_testBit, h1]
    native_decide
  · change colBit ⟨0, by decide⟩ (C t) = false
    rw [colBit_eq_testBit, h3]
    native_decide
  · change colBit ⟨0, by decide⟩ (C t) = false
    rw [colBit_eq_testBit, h5]
    native_decide
  · change colBit ⟨0, by decide⟩ (C t) = false
    rw [colBit_eq_testBit, h6]
    native_decide
  · change colBit ⟨0, by decide⟩ (C t) = false
    rw [colBit_eq_testBit, h7]
    native_decide

/-- A {1,3,5,6,7}-code has no type-2 or type-4 columns. -/
lemma count_two_four_zero_of_13567 {n : ℕ} (C : Code n)
    (h : totalCounts C {1, 3, 5, 6, 7} = n) :
    count C 2 = 0 ∧ count C 4 = 0 := by
  constructor
  · rw [count_eq_card, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro t ht
    have hcv : colVal (C t) = 2 := (Finset.mem_filter.mp ht).2
    have hm := colVal_mem_of_totalCounts C ({1, 3, 5, 6, 7} : Finset ℕ) h t
    simp [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with h1 | h3 | h5 | h6 | h7
    · rw [h1] at hcv
      norm_num at hcv
    · rw [h3] at hcv
      norm_num at hcv
    · rw [h5] at hcv
      norm_num at hcv
    · rw [h6] at hcv
      norm_num at hcv
    · rw [h7] at hcv
      norm_num at hcv
  · rw [count_eq_card, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro t ht
    have hcv : colVal (C t) = 4 := (Finset.mem_filter.mp ht).2
    have hm := colVal_mem_of_totalCounts C ({1, 3, 5, 6, 7} : Finset ℕ) h t
    simp [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with h1 | h3 | h5 | h6 | h7
    · rw [h1] at hcv
      norm_num at hcv
    · rw [h3] at hcv
      norm_num at hcv
    · rw [h5] at hcv
      norm_num at hcv
    · rw [h6] at hcv
      norm_num at hcv
    · rw [h7] at hcv
      norm_num at hcv

/-- d₂ + d₃ has the parity of w(c₃ ⊕ c₄) (paper eq. before the Y5 argument). -/
lemma dRow23_sum_parity {n : ℕ} (C : Code n) (y : Word n) :
    Even (dRow C 2 y + dRow C 3 y) ↔ Even (hammingDist (row2 C) (row3 C)) := by
  constructor
  · intro heven
    rcases heven with ⟨m, hm⟩
    rcases dRow23_sum_decomp C y with ⟨K, hK⟩
    have hle : K ≤ m := by
      have hd2 : hammingDist (row2 C) (row3 C) + 2 * K = 2 * m := by
        rw [← hK, hm]
        omega
      omega
    refine ⟨m - K, ?_⟩
    omega
  · intro heven
    rcases heven with ⟨m, hm⟩
    rcases dRow23_sum_decomp C y with ⟨K, hK⟩
    refine ⟨m + K, ?_⟩
    rw [hK, hm]
    omega

/-- `thm:even` (Theorem 8) comparison part: w(c₃⊕c₄) even ⇒ Y5 = ∅ (paper §IV-D,
Proof of Theorem 8, p. 154). -/
theorem Y5_empty_of_even_w23 {n : ℕ} (C : Code n) (t : Fin n) (hcol : C t = col1)
    (heven : Even (hammingDist (row2 C) (row3 C))) :
    ∀ y : Word n, ¬ Y5 C t y := by
  intro y hy
  have hdP : dP C y = dRow C 3 y + 1 := Y5_implies_dP_eq_dRow3_add_one C t y hcol hy
  have hd2 : dRow C 2 y = dRow C 3 y + 1 := by
    unfold dP at hdP
    exact hdP
  have heven' : Even (dRow C 2 y + dRow C 3 y) := (dRow23_sum_parity C y).mpr heven
  have hodd : Odd (dRow C 2 y + dRow C 3 y) := by
    rw [hd2]
    exact ⟨dRow C 3 y, by omega⟩
  rcases heven' with ⟨k, hk⟩
  rcases hodd with ⟨l, hl⟩
  omega

/-- `thm:even` (Theorem 8) comparison part: replacing a type-1 column by type 3 is never
worse when w(c₃⊕c₄) is even. -/
theorem one_bit_flip_better {n : ℕ} (C C' : Code n) (t : Fin n)
    (hcol : C t = col1) (hcol' : C' t = col3)
    (hsame : ∀ u : Fin n, u ≠ t → C' u = C u)
    (heven : Even (hammingDist (row2 C) (row3 C))) :
    UniversalBetter C' C := by
  exact (cumulative_no_y5 C C' t hcol hcol' hsame
    (Y5_empty_of_even_w23 C t hcol heven)).1

-- native_decide: Mechanical · n=any · checked 2026-08-28
/-- w(c₁ ⊕ c₃) = |2|+|3|+|6|+|7| for a Columns07 code (paper eq. w2). -/
lemma hammingDist_row0_row2_eq {n : ℕ} (C : Code n) (h07 : Columns07 C) :
    hammingDist (row0 C) (row2 C) = count C 2 + count C 3 + count C 6 + count C 7 := by
  have hS : ∀ t : Fin n, colVal (C t) ∈ Finset.Icc 0 7 := by
    intro t
    rw [Finset.mem_Icc]
    exact ⟨Nat.zero_le _, Columns07_le7 C h07 t⟩
  unfold row0 row2
  rw [hammingDist_rows_of_types C ⟨0, by decide⟩ ⟨2, by decide⟩ (Finset.Icc 0 7) hS, sum_Icc0_7]
  have h20 : (2 : ℕ).testBit 3 = false := by native_decide
  have h21 : (2 : ℕ).testBit 1 = true := by native_decide
  have h30 : (3 : ℕ).testBit 3 = false := by native_decide
  have h31 : (3 : ℕ).testBit 1 = true := by native_decide
  have h60 : (6 : ℕ).testBit 3 = false := by native_decide
  have h61 : (6 : ℕ).testBit 1 = true := by native_decide
  have h70 : (7 : ℕ).testBit 3 = false := by native_decide
  have h71 : (7 : ℕ).testBit 1 = true := by native_decide
  have h00 : (0 : ℕ).testBit 3 = false := by native_decide
  have h01 : (0 : ℕ).testBit 1 = false := by native_decide
  have h10 : (1 : ℕ).testBit 3 = false := by native_decide
  have h11 : (1 : ℕ).testBit 1 = false := by native_decide
  have h40 : (4 : ℕ).testBit 3 = false := by native_decide
  have h41 : (4 : ℕ).testBit 1 = false := by native_decide
  have h50 : (5 : ℕ).testBit 3 = false := by native_decide
  have h51 : (5 : ℕ).testBit 1 = false := by native_decide
  simp [h00, h01, h10, h11, h20, h21, h30, h31, h40, h41, h50, h51, h60, h61, h70, h71]

-- native_decide: Mechanical · n=any · checked 2026-08-28
/-- w(c₃ ⊕ c₄) = |1|+|2|+|5|+|6| for a Columns07 code. -/
lemma hammingDist_row2_row3_eq {n : ℕ} (C : Code n) (h07 : Columns07 C) :
    hammingDist (row2 C) (row3 C) = count C 1 + count C 2 + count C 5 + count C 6 := by
  have hS : ∀ t : Fin n, colVal (C t) ∈ Finset.Icc 0 7 := by
    intro t
    rw [Finset.mem_Icc]
    exact ⟨Nat.zero_le _, Columns07_le7 C h07 t⟩
  unfold row2 row3
  rw [hammingDist_rows_of_types C ⟨2, by decide⟩ ⟨3, by decide⟩ (Finset.Icc 0 7) hS, sum_Icc0_7]
  have h10 : (1 : ℕ).testBit 1 = false := by native_decide
  have h11 : (1 : ℕ).testBit 0 = true := by native_decide
  have h20 : (2 : ℕ).testBit 1 = true := by native_decide
  have h21 : (2 : ℕ).testBit 0 = false := by native_decide
  have h50 : (5 : ℕ).testBit 1 = false := by native_decide
  have h51 : (5 : ℕ).testBit 0 = true := by native_decide
  have h60 : (6 : ℕ).testBit 1 = true := by native_decide
  have h61 : (6 : ℕ).testBit 0 = false := by native_decide
  have h00 : (0 : ℕ).testBit 1 = false := by native_decide
  have h01 : (0 : ℕ).testBit 0 = false := by native_decide
  have h30 : (3 : ℕ).testBit 1 = true := by native_decide
  have h31 : (3 : ℕ).testBit 0 = true := by native_decide
  have h40 : (4 : ℕ).testBit 1 = false := by native_decide
  have h41 : (4 : ℕ).testBit 0 = false := by native_decide
  have h70 : (7 : ℕ).testBit 1 = true := by native_decide
  have h71 : (7 : ℕ).testBit 0 = true := by native_decide
  simp [h00, h01, h10, h11, h20, h21, h30, h31, h40, h41, h50, h51, h60, h61, h70, h71]

/-- y ∈ Y₃ forces d₂ ≤ d₁ and d₂ ≤ d₄ (because d_P = d_O). -/
lemma Y3_implies_dRow2_le_13 {n : ℕ} (C : Code n) (t : Fin n) (y : Word n)
    (hy : Y3 C t y) : dRow C 2 y ≤ dRow C 1 y ∧ dRow C 2 y ≤ dRow C 3 y := by
  have hOle1 : dO C y ≤ dRow C 1 y := by
    unfold dO
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hOle3 : dO C y ≤ dRow C 3 y := by
    unfold dO
    exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hdP : dP C y = dO C y := hy.2.2
  constructor
  · rw [← hdP] at hOle1
    simpa [dP, dRow, row2] using hOle1
  · rw [← hdP] at hOle3
    simpa [dP, dRow, row2] using hOle3

/-- y ∈ Y₃ forces d₂ ≤ d₁ (because d_P = d_O). -/
lemma Y3_implies_dRow2_le_0 {n : ℕ} (C : Code n) (t : Fin n) (y : Word n)
    (hy : Y3 C t y) : dRow C 2 y ≤ dRow C 0 y := by
  have hOle0 : dO C y ≤ dRow C 0 y := by
    unfold dO
    exact min_le_left _ _
  have hdP : dP C y = dO C y := hy.2.2
  rw [← hdP] at hOle0
  simpa [dP, dRow, row2] using hOle0

/-- If y t = true and d₂ = d₀ ≤ d₁, d₄ then y ∈ Y₃ (a Y₃¹ witness). -/
lemma Y3_of_dRow2_eq_dRow0_le {n : ℕ} (C : Code n) (t : Fin n) (y : Word n)
    (hcol : C t = col1) (hyt : y t = true)
    (h20 : dRow C 2 y = dRow C 0 y)
    (h21 : dRow C 2 y ≤ dRow C 1 y)
    (h23 : dRow C 2 y ≤ dRow C 3 y) :
    Y3 C t y := by
  unfold Y3
  have hdP : dP C y = dRow C 2 y := rfl
  have hdO : dO C y = dRow C 2 y := by
    unfold dO
    rw [show hammingDist (row0 C) y = dRow C 0 y by rfl,
      show hammingDist (row1 C) y = dRow C 1 y by rfl,
      show hammingDist (row3 C) y = dRow C 3 y by rfl]
    rw [← h20]
    exact min_eq_left (le_min h21 h23)
  have hdPp : dPp C t y = dRow C 2 y - 1 := by
    simpa [dP, dRow, row2] using (dPp_eq_col1 C t y hcol).1 hyt
  have hdOp : dOp C t y = dRow C 2 y - 1 := by
    rw [dOp_eq_min_col1 C t y hcol hyt]
    rw [← h20]
    apply min_eq_left
    apply le_min
    · exact Nat.sub_le_sub_right h21 1
    · omega
  have hle1 : 1 ≤ dRow C 2 y := by
    have hne : y t ≠ row C ⟨2, by decide⟩ t := by
      simp [row, hcol, colBit, col1, hyt]
    exact dRow_ge_one_of_mismatch C ⟨2, by decide⟩ t y hne
  constructor
  · rw [hdPp, hdOp]
  constructor
  · rw [hdPp, hdP]
    omega
  · rw [hdP, hdO]

/-- If y t = true and d₂ = d₁ ≤ d₀, d₄ then y ∈ Y₃ (a Y₃² witness). -/
lemma Y3_of_dRow2_eq_dRow1_le {n : ℕ} (C : Code n) (t : Fin n) (y : Word n)
    (hcol : C t = col1) (hyt : y t = true)
    (h21eq : dRow C 2 y = dRow C 1 y)
    (h20 : dRow C 2 y ≤ dRow C 0 y)
    (h23 : dRow C 2 y ≤ dRow C 3 y) :
    Y3 C t y := by
  unfold Y3
  have hdP : dP C y = dRow C 2 y := rfl
  have hdO : dO C y = dRow C 2 y := by
    unfold dO
    rw [show hammingDist (row0 C) y = dRow C 0 y by rfl,
      show hammingDist (row1 C) y = dRow C 1 y by rfl,
      show hammingDist (row3 C) y = dRow C 3 y by rfl]
    rw [← h21eq]
    rw [min_eq_left h23]
    exact min_eq_right h20
  have hdPp : dPp C t y = dRow C 2 y - 1 := by
    simpa [dP, dRow, row2] using (dPp_eq_col1 C t y hcol).1 hyt
  have hdOp : dOp C t y = dRow C 2 y - 1 := by
    rw [dOp_eq_min_col1 C t y hcol hyt]
    rw [← h21eq]
    have h23' : dRow C 2 y - 1 ≤ dRow C 3 y + 1 := by omega
    rw [min_eq_left h23']
    exact min_eq_right (Nat.sub_le_sub_right h20 1)
  have hle1 : 1 ≤ dRow C 2 y := by
    have hne : y t ≠ row C ⟨2, by decide⟩ t := by
      simp [row, hcol, colBit, col1, hyt]
    exact dRow_ge_one_of_mismatch C ⟨2, by decide⟩ t y hne
  constructor
  · rw [hdPp, hdOp]
  constructor
  · rw [hdPp, hdP]
    omega
  · rw [hdP, hdO]

/-- The weight form of a Y₃¹ witness (paper eqs. y31–y33, published
(162)–(164)): the three weight conditions force d₂ = d₀ ≤ d₁, d₄. -/
lemma Y3_of_weights_1 {n : ℕ} (C : Code n) (t : Fin n) (y : Word n)
    (hcol : C t = col1) (h07 : Columns07 C) (hyt : y t = true)
    (hEq : 2 * (w_i C 2 y + w_i C 3 y + w_i C 6 y + w_i C 7 y) =
        count C 2 + count C 3 + count C 6 + count C 7)
    (hLe2 : 2 * (w_i C 4 y + w_i C 5 y + w_i C 6 y + w_i C 7 y) ≤
        count C 4 + count C 5 + count C 6 + count C 7)
    (hLe4 : 2 * (w_i C 1 y + w_i C 3 y + w_i C 5 y + w_i C 7 y) ≤
        count C 1 + count C 3 + count C 5 + count C 7) :
    Y3 C t y := by
  rcases dRow03_columns07 C y h07 with ⟨hd0, hd3⟩
  rcases dRow12_columns07 C y h07 with ⟨hd1, hd2⟩
  have hw0 : w_i C 0 y ≤ count C 0 := w_i_le_count C 0 y
  have hw1 : w_i C 1 y ≤ count C 1 := w_i_le_count C 1 y
  have hw2 : w_i C 2 y ≤ count C 2 := w_i_le_count C 2 y
  have hw3 : w_i C 3 y ≤ count C 3 := w_i_le_count C 3 y
  have hw4 : w_i C 4 y ≤ count C 4 := w_i_le_count C 4 y
  have hw5 : w_i C 5 y ≤ count C 5 := w_i_le_count C 5 y
  have hw6 : w_i C 6 y ≤ count C 6 := w_i_le_count C 6 y
  have hw7 : w_i C 7 y ≤ count C 7 := w_i_le_count C 7 y
  have h20 : dRow C 2 y = dRow C 0 y := by
    rw [hd2, hd0]
    omega
  have h21 : dRow C 2 y ≤ dRow C 1 y := by
    rw [hd2, hd1]
    omega
  have h23 : dRow C 2 y ≤ dRow C 3 y := by
    rw [hd2, hd3]
    omega
  exact Y3_of_dRow2_eq_dRow0_le C t y hcol hyt h20 h21 h23

/-- A word with prescribed per-type weights and the fixed bit y t = true,
where t is a type-1 column. -/
lemma exists_goodWord_one {n : ℕ} (C : Code n) (k : ℕ → ℕ) (t : Fin n)
    (ht : colVal (C t) = 1) (hk1 : 1 ≤ k 1)
    (hk : ∀ i ∈ Finset.Icc 0 15, k i ≤ count C i) :
    ∃ y : Word n, y t = true ∧ ∀ i ∈ Finset.Icc 0 15, w_i C i y = k i := by
  have hf1 : t ∈ fiber C 1 := by simp [fiber, ht]
  have hk1le : k 1 - 1 ≤ ((fiber C 1).erase t).card := by
    have h1' : (fiber C 1).card = count C 1 := fiber_card_eq_count C 1
    have hcard : ((fiber C 1).erase t).card = count C 1 - 1 := by
      rw [Finset.card_erase_of_mem hf1, h1']
    have hk1' : k 1 ≤ count C 1 := hk 1 (by simp)
    omega
  let g : Fin 16 → Finset (Fin n) := fun a =>
    if h1a : a.val = 1 then
      insert t (pickSubset ((fiber C 1).erase t) (k 1 - 1) hk1le)
    else
      pickSubset (fiber C a.val) (k a.val) (by
        have hle := hk a.val (by
          have : a.val ≤ 15 := Nat.le_of_lt_succ a.isLt
          simp [Finset.mem_Icc, this])
        rw [fiber_card_eq_count]
        exact hle)
  let y : Word n := tupleWord C g
  have hg1 : g ⟨1, by decide⟩ =
      insert t (pickSubset ((fiber C 1).erase t) (k 1 - 1) hk1le) := by
    simp [g]
  have hg : GoodTuplePred C k g := by
    intro a
    by_cases ha1 : a.val = 1
    · have hg' : g a = insert t (pickSubset ((fiber C 1).erase t) (k 1 - 1) hk1le) := by
        simp [g, ha1]
      rw [hg', ha1]
      rw [Finset.mem_powersetCard]
      refine ⟨?_, ?_⟩
      · intro u hu
        rw [Finset.mem_insert] at hu
        rcases hu with rfl | hu
        · exact hf1
        · have hsub := pickSubset_subset hk1le
          have : u ∈ (fiber C 1).erase t := hsub hu
          exact (Finset.mem_erase.mp this).2
      · have hPcard : (pickSubset ((fiber C 1).erase t) (k 1 - 1) hk1le).card = k 1 - 1 :=
          pickSubset_card hk1le
        have ht' : t ∉ pickSubset ((fiber C 1).erase t) (k 1 - 1) hk1le := by
          intro h
          have hsub := pickSubset_subset hk1le
          have : t ∈ (fiber C 1).erase t := hsub h
          exact (Finset.mem_erase.mp this).1 rfl
        rw [Finset.card_insert_of_notMem ht', hPcard]
        omega
    · have hg' : g a = pickSubset (fiber C a.val) (k a.val)
          (by
            have hle := hk a.val (by
              have : a.val ≤ 15 := Nat.le_of_lt_succ a.isLt
              simp [Finset.mem_Icc, this])
            rw [fiber_card_eq_count]
            exact hle) := by
        simp [g, ha1]
      rw [hg']
      exact pickSubset_mem
        (by
          have hle := hk a.val (by
            have : a.val ≤ 15 := Nat.le_of_lt_succ a.isLt
            simp [Finset.mem_Icc, this])
          rw [fiber_card_eq_count]
          exact hle)
  have hy1 : y t = true := by
    unfold y
    simp [tupleWord]
    have h : t ∈ g ⟨colVal (C t), Nat.lt_succ_of_le (colVal_le_15 (C t))⟩ := by
      have hg1' : g ⟨colVal (C t), Nat.lt_succ_of_le (colVal_le_15 (C t))⟩ =
          insert t (pickSubset ((fiber C 1).erase t) (k 1 - 1) hk1le) := by
        simpa [ht] using hg1
      rw [hg1']
      exact Finset.mem_insert_self t _
    exact h
  have hw : ∀ i ∈ Finset.Icc 0 15, w_i C i y = k i := by
    intro i hi
    have hi' : i < 16 := by
      have : i ≤ 15 := (Finset.mem_Icc.mp hi).2
      omega
    have hones := onesOn_tupleWord C k g hg hi
    rw [w_i_eq_card_onesOn]
    rw [hones]
    by_cases hi1 : i = 1
    · subst i
      rw [hg1]
      have hPcard : (pickSubset ((fiber C 1).erase t) (k 1 - 1) hk1le).card = k 1 - 1 :=
        pickSubset_card hk1le
      have ht' : t ∉ pickSubset ((fiber C 1).erase t) (k 1 - 1) hk1le := by
        intro h
        have hsub := pickSubset_subset hk1le
        have : t ∈ (fiber C 1).erase t := hsub h
        exact (Finset.mem_erase.mp this).1 rfl
      rw [Finset.card_insert_of_notMem ht', hPcard]
      omega
    · have hg' : g ⟨i, hi'⟩ = pickSubset (fiber C i) (k i)
          (by
            have hle := hk i hi
            rw [fiber_card_eq_count]
            exact hle) := by
        simp [g, hi1]
      rw [hg']
      exact pickSubset_card
        (by
          have hle := hk i hi
          rw [fiber_card_eq_count]
          exact hle)
  exact ⟨y, hy1, hw⟩

/-- The Y₃ witness table: weight values at types 1..7, zero elsewhere. -/
def tableY3 (a1 a2 a3 a4 a5 a6 a7 : ℕ) (i : ℕ) : ℕ :=
  if i = 1 then a1 else if i = 2 then a2 else if i = 3 then a3
  else if i = 4 then a4 else if i = 5 then a5 else if i = 6 then a6
  else if i = 7 then a7 else 0

/-- Feasibility of a Y₃ table assignment. -/
lemma tableY3_bounds {n : ℕ} (C : Code n) (a1 a2 a3 a4 a5 a6 a7 : ℕ)
    (h1 : a1 ≤ count C 1) (h2 : a2 ≤ count C 2) (h3 : a3 ≤ count C 3)
    (h4 : a4 ≤ count C 4) (h5 : a5 ≤ count C 5) (h6 : a6 ≤ count C 6)
    (h7 : a7 ≤ count C 7) :
    ∀ i ∈ Finset.Icc 0 15, tableY3 a1 a2 a3 a4 a5 a6 a7 i ≤ count C i := by
  intro i hi
  by_cases hi1 : i = 1
  · subst i
    simp [tableY3, h1]
  · by_cases hi2 : i = 2
    · subst i
      simp [tableY3, h2]
    · by_cases hi3 : i = 3
      · subst i
        simp [tableY3, h3]
      · by_cases hi4 : i = 4
        · subst i
          simp [tableY3, h4]
        · by_cases hi5 : i = 5
          · subst i
            simp [tableY3, h5]
          · by_cases hi6 : i = 6
            · subst i
              simp [tableY3, h6]
            · by_cases hi7 : i = 7
              · subst i
                simp [tableY3, h7]
              · simp [tableY3, hi1, hi2, hi3, hi4, hi5, hi6, hi7]

/-- A Y₃¹ witness from a feasible table assignment satisfying the three
weight conditions (paper eqs. y31–y33, published (162)–(164)). -/
-- native_decide: Mechanical · n=any · checked 2026-08-28
lemma y3_nonempty_of_table {n : ℕ} (C : Code n) (t : Fin n)
    (hcol : C t = col1) (h07 : Columns07 C)
    (a1 a2 a3 a4 a5 a6 a7 : ℕ)
    (ha1 : 1 ≤ a1)
    (hb1 : a1 ≤ count C 1) (hb2 : a2 ≤ count C 2) (hb3 : a3 ≤ count C 3)
    (hb4 : a4 ≤ count C 4) (hb5 : a5 ≤ count C 5) (hb6 : a6 ≤ count C 6)
    (hb7 : a7 ≤ count C 7)
    (hEq : 2 * (a2 + a3 + a6 + a7) = count C 2 + count C 3 + count C 6 + count C 7)
    (hLe2 : 2 * (a4 + a5 + a6 + a7) ≤ count C 4 + count C 5 + count C 6 + count C 7)
    (hLe4 : 2 * (a1 + a3 + a5 + a7) ≤ count C 1 + count C 3 + count C 5 + count C 7) :
    ∃ y : Word n, Y3 C t y := by
  let k : ℕ → ℕ := tableY3 a1 a2 a3 a4 a5 a6 a7
  have hk1 : 1 ≤ k 1 := by simp [k, tableY3, ha1]
  have hkfeas : ∀ i ∈ Finset.Icc 0 15, k i ≤ count C i := by
    apply tableY3_bounds C a1 a2 a3 a4 a5 a6 a7 hb1 hb2 hb3 hb4 hb5 hb6 hb7
  have ht : colVal (C t) = 1 := by rw [hcol]; native_decide
  rcases exists_goodWord_one C k t ht hk1 hkfeas with ⟨y, hy1, hw⟩
  have hw1 : w_i C 1 y = a1 := by
    have := hw 1 (by simp)
    simpa [k, tableY3] using this
  have hw2 : w_i C 2 y = a2 := by
    have := hw 2 (by simp)
    simpa [k, tableY3] using this
  have hw3 : w_i C 3 y = a3 := by
    have := hw 3 (by simp)
    simpa [k, tableY3] using this
  have hw4 : w_i C 4 y = a4 := by
    have := hw 4 (by simp)
    simpa [k, tableY3] using this
  have hw5 : w_i C 5 y = a5 := by
    have := hw 5 (by simp)
    simpa [k, tableY3] using this
  have hw6 : w_i C 6 y = a6 := by
    have := hw 6 (by simp)
    simpa [k, tableY3] using this
  have hw7 : w_i C 7 y = a7 := by
    have := hw 7 (by simp)
    simpa [k, tableY3] using this
  refine ⟨y, ?_⟩
  apply Y3_of_weights_1 C t y hcol h07 hy1
  · rw [hw2, hw3, hw6, hw7]
    omega
  · rw [hw4, hw5, hw6, hw7]
    omega
  · rw [hw1, hw3, hw5, hw7]
    omega

/-- The seven nonempty parity cases of the Y₃¹ witness construction (paper
§IV-D, Proof of Theorem 8, page 154; cases 1)–7) of the (|2|,|3|,|6|,|7|)
parity table, following eqs. (162)–(164)).

The paper states these cases under the assumption that w(c₁⊕c₃) =
|2|+|3|+|6|+|7| (eq. (26)) is even.  That parity condition is not a
hypothesis here because it is implied by `hcase`: each of the seven
disjuncts has an even number of odd counts among (|2|,|3|,|6|,|7|), so
`Even (hammingDist (row0 C) (row2 C))` follows from `hammingDist_row0_row2_eq`
and `h07`.  (The missing eighth pattern, |3|,|6| odd and |2|,|7| even, is the
case handled separately by `y3_nonempty_of_remaining_subcases`.)

The hypothesis `heven` is instead the Theorem 8 assumption that
w(c₃⊕c₄) = |1|+|2|+|5|+|6| (eq. (w4), published (28)) is even.  Its proof
use is to show |1|+|5| ≥ 2 when |2|+|6| is even (lines 1371–1380 below),
which makes w₁ = 1 feasible in each table witness.  Note that in case 1) the
published paper writes "Since w(c₁⊕c₃) = |1|+|2|+|5|+|6| is even..."; that
is a mislabel — |1|+|2|+|5|+|6| is w(c₃⊕c₄), not w(c₁⊕c₃) — and `heven`
carries the correct quantity. -/
-- native_decide: Mechanical · n=any · checked 2026-08-28
theorem y3_nonempty_cases {n : ℕ} (C : Code n) (t : Fin n)
    (hcol : C t = col1) (h07 : Columns07 C)
    (heven : Even (hammingDist (row2 C) (row3 C)))
    (hcase :
      (Even (count C 2) ∧ Even (count C 3) ∧ Even (count C 6) ∧ Even (count C 7)) ∨
      (Odd (count C 2) ∧ Odd (count C 3) ∧ Odd (count C 6) ∧ Odd (count C 7)) ∨
      (Odd (count C 2) ∧ Odd (count C 3) ∧ Even (count C 6) ∧ Even (count C 7)) ∨
      (Odd (count C 2) ∧ Even (count C 3) ∧ Odd (count C 6) ∧ Even (count C 7)) ∨
      (Odd (count C 2) ∧ Even (count C 3) ∧ Even (count C 6) ∧ Odd (count C 7)) ∨
      (Even (count C 2) ∧ Odd (count C 3) ∧ Even (count C 6) ∧ Odd (count C 7)) ∨
      (Even (count C 2) ∧ Even (count C 3) ∧ Odd (count C 6) ∧ Odd (count C 7))) :
    ∃ y : Word n, Y3 C t y := by
  have hc1 : 1 ≤ count C 1 := count_pos_of_colVal C t (by rw [hcol]; native_decide)
  have h156_even : Even (count C 1 + count C 2 + count C 5 + count C 6) := by
    rw [hammingDist_row2_row3_eq C h07] at heven
    exact heven
  have h15_ge2_of_even26sum : Even (count C 2 + count C 6) →
      2 ≤ count C 1 + count C 5 := by
    intro h26e
    have h15e : Even (count C 1 + count C 5) := by
      rcases h156_even with ⟨m, hm⟩
      rcases h26e with ⟨a, ha⟩
      exact ⟨m - a, by omega⟩
    rcases h15e with ⟨k, hk⟩
    omega
  rcases hcase with h1 | h2 | h3 | h4 | h5 | h6 | h7
  · -- case 1: all even
    rcases h1 with ⟨h2e, h3e, h6e, h7e⟩
    rcases h2e with ⟨p2, hp2⟩
    rcases h3e with ⟨p3, hp3⟩
    rcases h6e with ⟨p6, hp6⟩
    rcases h7e with ⟨p7, hp7⟩
    have h15 : 2 ≤ count C 1 + count C 5 := by
      apply h15_ge2_of_even26sum
      exact ⟨p2 + p6, by omega⟩
    refine y3_nonempty_of_table C t hcol h07 1 p2 p3 0 0 p6 p7 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · rw [hp2, hp3, hp6, hp7]
      omega
    · omega
    · rw [hp3, hp7]
      omega
  · -- case 2: all odd
    rcases h2 with ⟨h2o, h3o, h6o, h7o⟩
    rcases h2o with ⟨p2, hp2⟩
    rcases h3o with ⟨p3, hp3⟩
    rcases h6o with ⟨p6, hp6⟩
    rcases h7o with ⟨p7, hp7⟩
    refine y3_nonempty_of_table C t hcol h07 1 (p2 + 1) p3 0 0 (p6 + 1) p7 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · rw [hp2, hp3, hp6, hp7]
      omega
    · omega
    · rw [hp3, hp7]
      omega
  · -- case 3: |2|,|3| odd; |6|,|7| even
    rcases h3 with ⟨h2o, h3o, h6e, h7e⟩
    rcases h2o with ⟨p2, hp2⟩
    rcases h3o with ⟨p3, hp3⟩
    rcases h6e with ⟨p6, hp6⟩
    rcases h7e with ⟨p7, hp7⟩
    refine y3_nonempty_of_table C t hcol h07 1 (p2 + 1) p3 0 0 p6 p7 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · rw [hp2, hp3, hp6, hp7]
      omega
    · omega
    · rw [hp3, hp7]
      omega
  · -- case 4: |2|,|6| odd; |3|,|7| even
    rcases h4 with ⟨h2o, h3e, h6o, h7e⟩
    rcases h2o with ⟨p2, hp2⟩
    rcases h3e with ⟨p3, hp3⟩
    rcases h6o with ⟨p6, hp6⟩
    rcases h7e with ⟨p7, hp7⟩
    have h15 : 2 ≤ count C 1 + count C 5 := by
      apply h15_ge2_of_even26sum
      exact ⟨p2 + p6 + 1, by omega⟩
    refine y3_nonempty_of_table C t hcol h07 1 (p2 + 1) p3 0 0 p6 p7 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · rw [hp2, hp3, hp6, hp7]
      omega
    · omega
    · rw [hp3, hp7]
      omega
  · -- case 5: |2|,|7| odd; |3|,|6| even
    rcases h5 with ⟨h2o, h3e, h6e, h7o⟩
    rcases h2o with ⟨p2, hp2⟩
    rcases h3e with ⟨p3, hp3⟩
    rcases h6e with ⟨p6, hp6⟩
    rcases h7o with ⟨p7, hp7⟩
    refine y3_nonempty_of_table C t hcol h07 1 (p2 + 1) p3 0 0 p6 p7 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · rw [hp2, hp3, hp6, hp7]
      omega
    · omega
    · rw [hp3, hp7]
      omega
  · -- case 6: |3|,|7| odd; |2|,|6| even
    rcases h6 with ⟨h2e, h3o, h6e, h7o⟩
    rcases h2e with ⟨p2, hp2⟩
    rcases h3o with ⟨p3, hp3⟩
    rcases h6e with ⟨p6, hp6⟩
    rcases h7o with ⟨p7, hp7⟩
    have h15 : 2 ≤ count C 1 + count C 5 := by
      apply h15_ge2_of_even26sum
      exact ⟨p2 + p6, by omega⟩
    refine y3_nonempty_of_table C t hcol h07 1 p2 (p3 + 1) 0 0 p6 p7 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · rw [hp2, hp3, hp6, hp7]
      omega
    · omega
    · rw [hp3, hp7]
      omega
  · -- case 7: |6|,|7| odd; |2|,|3| even
    rcases h7 with ⟨h2e, h3e, h6o, h7o⟩
    rcases h2e with ⟨p2, hp2⟩
    rcases h3e with ⟨p3, hp3⟩
    rcases h6o with ⟨p6, hp6⟩
    rcases h7o with ⟨p7, hp7⟩
    refine y3_nonempty_of_table C t hcol h07 1 p2 p3 0 0 (p6 + 1) p7 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · rw [hp2, hp3, hp6, hp7]
      omega
    · omega
    · rw [hp3, hp7]
      omega

/-- The four witness sub-cases of the remaining parity case (paper §IV-D,
Proof of Theorem 8, pp. 154--155; cases 8-1..8-4, with |3|,|6| odd and
|2|,|7| even). -/
-- native_decide: Mechanical · n=any · checked 2026-08-28
theorem y3_nonempty_of_remaining_subcases {n : ℕ} (C : Code n) (t : Fin n)
    (hcol : C t = col1) (h07 : Columns07 C)
    (h2e : Even (count C 2)) (h3o : Odd (count C 3))
    (h6o : Odd (count C 6)) (h7e : Even (count C 7))
    (hsub : (0 < count C 2) ∨ (0 < count C 7) ∨
      (0 < count C 4 + count C 5) ∨ (3 ≤ count C 1)) :
    ∃ y : Word n, Y3 C t y := by
  have hc1 : 1 ≤ count C 1 := count_pos_of_colVal C t (by rw [hcol]; native_decide)
  rcases h2e with ⟨p2, hp2⟩
  rcases h3o with ⟨p3, hp3⟩
  rcases h6o with ⟨p6, hp6⟩
  rcases h7e with ⟨p7, hp7⟩
  rcases hsub with h2pos | h7pos | h45pos | h1ge3
  · -- case 8-1: |2| > 0
    refine y3_nonempty_of_table C t hcol h07 1 (p2 + 1) p3 0 0 p6 p7 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · rw [hp2, hp3, hp6, hp7]
      omega
    · omega
    · omega
  · -- case 8-2: |7| > 0
    refine y3_nonempty_of_table C t hcol h07 1 p2 (p3 + 1) 0 0 (p6 + 1) (p7 - 1) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · rw [hp2, hp3, hp6, hp7]
      omega
    · omega
    · omega
  · -- case 8-3: |4| + |5| > 0
    refine y3_nonempty_of_table C t hcol h07 1 p2 p3 0 0 (p6 + 1) p7 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · rw [hp2, hp3, hp6, hp7]
      omega
    · omega
    · omega
  · -- case 8-4: |1| ≥ 3
    refine y3_nonempty_of_table C t hcol h07 1 p2 (p3 + 1) 0 0 p6 p7 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · rw [hp2, hp3, hp6, hp7]
      omega
    · omega
    · omega

/-- Equality condition (ii) of `thm:even` (Theorem 8) forces Y₃ = ∅ (paper §IV-D,
Proof of Theorem 8, p. 155; the |1|=1, |2|=|4|=|5|=|7|=0, |3| and |6| odd case). -/
-- native_decide: Mechanical · n=any · checked 2026-08-28
lemma Y3_empty_of_cond2 {n : ℕ} (C : Code n) (t : Fin n)
    (hcol : C t = col1) (h07 : Columns07 C)
    (h1 : count C 1 = 1) (h2 : count C 2 = 0) (h4 : count C 4 = 0)
    (h5 : count C 5 = 0) (h7 : count C 7 = 0)
    (h3o : Odd (count C 3)) (_h6o : Odd (count C 6)) :
    ∀ y : Word n, ¬ Y3 C t y := by
  intro y hy
  have hyt : y t = true := Y3_implies_htrue C t y hcol hy
  have hw1 : w_i C 1 y = 1 :=
    w_i_eq_of_single C 1 t y h1 (by rw [hcol]; native_decide) hyt
  have hw2 : w_i C 2 y = 0 := by
    have h := w_i_le_count C 2 y
    omega
  have hw4 : w_i C 4 y = 0 := by
    have h := w_i_le_count C 4 y
    omega
  have hw5 : w_i C 5 y = 0 := by
    have h := w_i_le_count C 5 y
    omega
  have hw7 : w_i C 7 y = 0 := by
    have h := w_i_le_count C 7 y
    omega
  have hw3 : w_i C 3 y ≤ count C 3 := w_i_le_count C 3 y
  have hw6 : w_i C 6 y ≤ count C 6 := w_i_le_count C 6 y
  rcases dRow03_columns07 C y h07 with ⟨hd0, hd3⟩
  rcases dRow12_columns07 C y h07 with ⟨hd1, hd2⟩
  have hsum02 : dRow C 0 y + dRow C 2 y =
      2 * w_i C 0 y + count C 3 + count C 6 + 2 := by
    rw [hd0, hd2]
    omega
  have hsum13 : dRow C 1 y + dRow C 3 y =
      2 * w_i C 0 y + count C 3 + count C 6 + 1 := by
    rw [hd1, hd3]
    omega
  rcases Y3_implies_dRow2_eq_dRow0_or_dRow1 C t y hcol hy with h20 | h21
  · -- Y3^1: d2+d3 ≥ d0+d2 but the exact sums are one apart
    have h21le := (Y3_implies_dRow2_le_13 C t y hy).1
    have h23le := (Y3_implies_dRow2_le_13 C t y hy).2
    have h13ge : dRow C 1 y + dRow C 3 y ≥ dRow C 0 y + dRow C 2 y := by
      rw [h20]
      omega
    rw [hsum02, hsum13] at h13ge
    omega
  · -- Y3^2: parity contradiction (w(c2,c3) = |3| odd)
    have hw12 : hammingDist (row1 C) (row2 C) = count C 3 := by
      rw [hammingDist_row1_row2_eq C h07, h2, h4, h5]
      simp
    have hodd : Odd (hammingDist (row1 C) (row2 C)) := by
      rwa [hw12]
    have hsum12_odd : Odd (dRow C 1 y + dRow C 2 y) :=
      (dRow_ij_sum_parity_odd C ⟨1, by decide⟩ ⟨2, by decide⟩ y).mpr hodd
    have heven : Even (dRow C 1 y + dRow C 2 y) := by
      rw [h21]
      exact ⟨dRow C 2 y, by omega⟩
    rcases hsum12_odd with ⟨l, hl⟩
    rcases heven with ⟨m, hm⟩
    omega

/-- Equality condition (iii) of `thm:even` (Theorem 8) forces Y₃ = ∅ (paper §IV-D,
Proof of Theorem 8, p. 155; the |1|=1, |2|=|4|=|6|=|7|=0, |3| and |5| odd case). -/
-- native_decide: Mechanical · n=any · checked 2026-08-28
lemma Y3_empty_of_cond3 {n : ℕ} (C : Code n) (t : Fin n)
    (hcol : C t = col1) (h07 : Columns07 C)
    (h1 : count C 1 = 1) (h2 : count C 2 = 0) (h4 : count C 4 = 0)
    (h6 : count C 6 = 0) (h7 : count C 7 = 0)
    (h3o : Odd (count C 3)) (_h5o : Odd (count C 5)) :
    ∀ y : Word n, ¬ Y3 C t y := by
  intro y hy
  have hyt : y t = true := Y3_implies_htrue C t y hcol hy
  have hw1 : w_i C 1 y = 1 :=
    w_i_eq_of_single C 1 t y h1 (by rw [hcol]; native_decide) hyt
  have hw2 : w_i C 2 y = 0 := by
    have h := w_i_le_count C 2 y
    omega
  have hw4 : w_i C 4 y = 0 := by
    have h := w_i_le_count C 4 y
    omega
  have hw6 : w_i C 6 y = 0 := by
    have h := w_i_le_count C 6 y
    omega
  have hw7 : w_i C 7 y = 0 := by
    have h := w_i_le_count C 7 y
    omega
  have hw3 : w_i C 3 y ≤ count C 3 := w_i_le_count C 3 y
  have hw5 : w_i C 5 y ≤ count C 5 := w_i_le_count C 5 y
  rcases dRow03_columns07 C y h07 with ⟨hd0, hd3⟩
  rcases dRow12_columns07 C y h07 with ⟨hd1, hd2⟩
  have hsum14 : dRow C 0 y + dRow C 3 y =
      2 * w_i C 0 y + count C 3 + count C 5 + 1 := by
    rw [hd0, hd3]
    omega
  have hsum23 : dRow C 1 y + dRow C 2 y =
      2 * w_i C 0 y + count C 3 + count C 5 + 2 := by
    rw [hd1, hd2]
    omega
  rcases Y3_implies_dRow2_eq_dRow0_or_dRow1 C t y hcol hy with h20 | h21
  · -- Y3^1: parity contradiction (w(c1,c3) = |3| odd)
    have hw02 : hammingDist (row0 C) (row2 C) = count C 3 := by
      rw [hammingDist_row0_row2_eq C h07, h2, h6, h7]
      simp
    have hodd : Odd (hammingDist (row0 C) (row2 C)) := by
      rwa [hw02]
    have hsum02_odd : Odd (dRow C 0 y + dRow C 2 y) :=
      (dRow_ij_sum_parity_odd C ⟨0, by decide⟩ ⟨2, by decide⟩ y).mpr hodd
    have heven : Even (dRow C 0 y + dRow C 2 y) := by
      rw [h20]
      exact ⟨dRow C 2 y, by omega⟩
    rcases hsum02_odd with ⟨l, hl⟩
    rcases heven with ⟨m, hm⟩
    omega
  · -- Y3^2: exact sum contradiction
    have h20le := Y3_implies_dRow2_le_0 C t y hy
    have h23le := (Y3_implies_dRow2_le_13 C t y hy).2
    have h14lt : dRow C 0 y + dRow C 3 y < dRow C 1 y + dRow C 2 y := by
      rw [hsum14, hsum23]
      omega
    have h14ge : dRow C 0 y + dRow C 3 y ≥ dRow C 1 y + dRow C 2 y := by
      rw [h21]
      omega
    omega

/-- The `thm:even` (Theorem 8) equality characterization restricted to the case
w(c₁ ⊕ c₃) even: Y₃ = ∅ iff condition (ii) holds. -/
-- native_decide: Mechanical · n=any · checked 2026-08-28
theorem Y3_empty_iff_cond2 {n : ℕ} (C : Code n) (t : Fin n)
    (hcol : C t = col1) (h07 : Columns07 C)
    (hEven13 : Even (hammingDist (row0 C) (row2 C)))
    (heven : Even (hammingDist (row2 C) (row3 C))) :
    (∀ y : Word n, ¬ Y3 C t y) ↔
      (count C 1 = 1 ∧ count C 2 = 0 ∧ count C 4 = 0 ∧ count C 5 = 0 ∧
        count C 7 = 0 ∧ Odd (count C 3) ∧ Odd (count C 6)) := by
  constructor
  · intro h
    have hEven13c : Even (count C 2 + count C 3 + count C 6 + count C 7) := by
      rw [hammingDist_row0_row2_eq C h07] at hEven13
      exact hEven13
    have c7_even_of : Even (count C 2 + count C 3 + count C 6) → Even (count C 7) := by
      intro h236
      rcases hEven13c with ⟨m, hm⟩
      rcases h236 with ⟨k, hk⟩
      exact ⟨m - k, by omega⟩
    have c7_odd_of : Odd (count C 2 + count C 3 + count C 6) → Odd (count C 7) := by
      intro h236
      rcases hEven13c with ⟨m, hm⟩
      rcases h236 with ⟨k, hk⟩
      refine ⟨m - k - 1, by omega⟩
    have hc1 : 1 ≤ count C 1 := count_pos_of_colVal C t (by rw [hcol]; native_decide)
    by_cases h2e : Even (count C 2)
    · by_cases h3e : Even (count C 3)
      · by_cases h6e : Even (count C 6)
        · -- case 1: all even
          have h7e : Even (count C 7) := by
            apply c7_even_of
            rcases h2e with ⟨a, ha⟩
            rcases h3e with ⟨b, hb⟩
            rcases h6e with ⟨c, hc⟩
            exact ⟨a + b + c, by omega⟩
          rcases y3_nonempty_cases C t hcol h07 heven (Or.inl ⟨h2e, h3e, h6e, h7e⟩) with ⟨y, hy⟩
          exact (h y hy).elim
        · -- case 7: |6|,|7| odd; |2|,|3| even
          have h6o : Odd (count C 6) := Nat.not_even_iff_odd.mp h6e
          have h7o : Odd (count C 7) := by
            apply c7_odd_of
            rcases h2e with ⟨a, ha⟩
            rcases h3e with ⟨b, hb⟩
            rcases h6o with ⟨c, hc⟩
            exact ⟨a + b + c, by omega⟩
          rcases y3_nonempty_cases C t hcol h07 heven
            (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h2e, h3e, h6o, h7o⟩)))))) with ⟨y, hy⟩
          exact (h y hy).elim
      · -- c3 odd
        have h3o : Odd (count C 3) := Nat.not_even_iff_odd.mp h3e
        by_cases h6e : Even (count C 6)
        · -- case 6: |3|,|7| odd; |2|,|6| even
          have h7o : Odd (count C 7) := by
            apply c7_odd_of
            rcases h2e with ⟨a, ha⟩
            rcases h3o with ⟨b, hb⟩
            rcases h6e with ⟨c, hc⟩
            exact ⟨a + b + c, by omega⟩
          rcases y3_nonempty_cases C t hcol h07 heven
            (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h2e, h3o, h6e, h7o⟩)))))) with ⟨y, hy⟩
          exact (h y hy).elim
        · -- remaining: |3|,|6| odd; |2|,|7| even
          have h6o : Odd (count C 6) := Nat.not_even_iff_odd.mp h6e
          have h7e : Even (count C 7) := by
            apply c7_even_of
            rcases h2e with ⟨a, ha⟩
            rcases h3o with ⟨b, hb⟩
            rcases h6o with ⟨c, hc⟩
            exact ⟨a + b + c + 1, by omega⟩
          by_cases hsub : (0 < count C 2) ∨ (0 < count C 7) ∨
              (0 < count C 4 + count C 5) ∨ (3 ≤ count C 1)
          · rcases y3_nonempty_of_remaining_subcases C t hcol h07 h2e h3o h6o h7e hsub
              with ⟨y, hy⟩
            exact (h y hy).elim
          · have hnot2 : ¬ 0 < count C 2 := fun h => hsub (Or.inl h)
            have hnot7 : ¬ 0 < count C 7 := fun h => hsub (Or.inr (Or.inl h))
            have hnot45 : ¬ 0 < count C 4 + count C 5 :=
              fun h => hsub (Or.inr (Or.inr (Or.inl h)))
            have hnot1ge3 : ¬ 3 ≤ count C 1 :=
              fun h => hsub (Or.inr (Or.inr (Or.inr h)))
            have h2 : count C 2 = 0 := by omega
            have h7 : count C 7 = 0 := by omega
            have h45 : count C 4 + count C 5 = 0 := by omega
            have h4 : count C 4 = 0 := by omega
            have h5 : count C 5 = 0 := by omega
            have h1le2 : count C 1 ≤ 2 := by omega
            have h156 : Even (count C 1 + count C 2 + count C 5 + count C 6) := by
              rw [hammingDist_row2_row3_eq C h07] at heven
              exact heven
            have h1odd : Odd (count C 1) := by
              rcases h156 with ⟨m, hm⟩
              rcases h6o with ⟨k, hk⟩
              refine ⟨m - k - 1, by omega⟩
            have h1 : count C 1 = 1 := by
              rcases h1odd with ⟨a, ha⟩
              omega
            exact ⟨h1, h2, h4, h5, h7, h3o, h6o⟩
    · -- c2 odd
      have h2o : Odd (count C 2) := Nat.not_even_iff_odd.mp h2e
      by_cases h3e : Even (count C 3)
      · by_cases h6e : Even (count C 6)
        · -- case 5: |2|,|7| odd; |3|,|6| even
          have h7o : Odd (count C 7) := by
            apply c7_odd_of
            rcases h2o with ⟨a, ha⟩
            rcases h3e with ⟨b, hb⟩
            rcases h6e with ⟨c, hc⟩
            exact ⟨a + b + c, by omega⟩
          rcases y3_nonempty_cases C t hcol h07 heven
            (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h2o, h3e, h6e, h7o⟩))))) with ⟨y, hy⟩
          exact (h y hy).elim
        · -- case 4: |2|,|6| odd; |3|,|7| even
          have h6o : Odd (count C 6) := Nat.not_even_iff_odd.mp h6e
          have h7e : Even (count C 7) := by
            apply c7_even_of
            rcases h2o with ⟨a, ha⟩
            rcases h3e with ⟨b, hb⟩
            rcases h6o with ⟨c, hc⟩
            exact ⟨a + b + c + 1, by omega⟩
          rcases y3_nonempty_cases C t hcol h07 heven
            (Or.inr (Or.inr (Or.inr (Or.inl ⟨h2o, h3e, h6o, h7e⟩)))) with ⟨y, hy⟩
          exact (h y hy).elim
      · -- c3 odd
        have h3o : Odd (count C 3) := Nat.not_even_iff_odd.mp h3e
        by_cases h6e : Even (count C 6)
        · -- case 3: |2|,|3| odd; |6|,|7| even
          have h7e : Even (count C 7) := by
            apply c7_even_of
            rcases h2o with ⟨a, ha⟩
            rcases h3o with ⟨b, hb⟩
            rcases h6e with ⟨c, hc⟩
            exact ⟨a + b + c + 1, by omega⟩
          rcases y3_nonempty_cases C t hcol h07 heven
            (Or.inr (Or.inr (Or.inl ⟨h2o, h3o, h6e, h7e⟩))) with ⟨y, hy⟩
          exact (h y hy).elim
        · -- case 2: all odd
          have h6o : Odd (count C 6) := Nat.not_even_iff_odd.mp h6e
          have h7o : Odd (count C 7) := by
            apply c7_odd_of
            rcases h2o with ⟨a, ha⟩
            rcases h3o with ⟨b, hb⟩
            rcases h6o with ⟨c, hc⟩
            exact ⟨a + b + c + 1, by omega⟩
          rcases y3_nonempty_cases C t hcol h07 heven
            (Or.inr (Or.inl ⟨h2o, h3o, h6o, h7o⟩)) with ⟨y, hy⟩
          exact (h y hy).elim
  · intro hii
    rcases hii with ⟨h1, h2, h4, h5, h7, h3o, h6o⟩
    exact Y3_empty_of_cond2 C t hcol h07 h1 h2 h4 h5 h7 h3o h6o

/-! ## The symmetric `thm:even` (Theorem 8) case (row/column-flip equivalence)

The `w(c₁ ⊕ c₃)`-odd / `w(c₂ ⊕ c₃)`-even case of the Y3-empty
characterization is transported to `Y3_empty_iff_cond2` via the equivalence
that swaps rows 1,2 and flips columns leaving the type-0..7 range. -/

/-- The row permutation swapping rows 1 and 2 (indices 0 and 1). -/
def swap01 : Equiv (Fin 4) (Fin 4) := Equiv.swap (0 : Fin 4) (1 : Fin 4)

/-- The column-type relabelling induced by `swap01` plus the flip of columns
leaving the type-0..7 range. -/
def swapVal01 (i : ℕ) : ℕ :=
  if i = 4 then 7 else if i = 5 then 6 else if i = 6 then 5 else if i = 7 then 4 else i

/-- `swapVal01` is an involution. -/
lemma swapVal01_idem (i : ℕ) : swapVal01 (swapVal01 i) = i := by
  by_cases h4 : i = 4 <;> by_cases h5 : i = 5 <;> by_cases h6 : i = 6 <;>
    by_cases h7 : i = 7 <;> simp [swapVal01, h4, h5, h6, h7]

/-- The flip indicator for the row-1/2 swap equivalence. -/
def swapFlip01 {n : ℕ} (C : Code n) (u : Fin n) : Bool :=
  if 7 < colVal (rowPermute swap01 (C u)) then true else false

/-- The code obtained from C by swapping rows 1,2 and flipping columns whose
swapped type number exceeds 7. -/
def swapRows01Code {n : ℕ} (C : Code n) : Code n :=
  fun u => rowPermute swap01 (if swapFlip01 C u then flipCol (C u) else C u)

/-- The induced self-inverse word flip. -/
def wordFlip01 {n : ℕ} (C : Code n) : Word n → Word n :=
  wordTransform (Equiv.refl (Fin n)) (swapFlip01 C)

-- native_decide: Mechanical · n=any · checked 2026-08-28
lemma swap01_apply0 : swap01 0 = (1 : Fin 4) := by native_decide
-- native_decide: Mechanical · n=any · checked 2026-08-28
lemma swap01_apply1 : swap01 1 = (0 : Fin 4) := by native_decide
-- native_decide: Mechanical · n=any · checked 2026-08-28
lemma swap01_apply2 : swap01 2 = (2 : Fin 4) := by native_decide
-- native_decide: Mechanical · n=any · checked 2026-08-28
lemma swap01_apply3 : swap01 3 = (3 : Fin 4) := by native_decide

/-- The type number of a swapped-and-flipped 0..7 column is `swapVal01` of the
original type number. -/
-- native_decide: Mechanical · n=any · checked 2026-08-28
lemma colVal_swapRows01_of_le7 (v : ℕ) (hv : v ≤ 7) :
    colVal (rowPermute swap01
      (if 7 < colVal (rowPermute swap01 (colOfNat v)) then flipCol (colOfNat v)
        else colOfNat v)) = swapVal01 v := by
  interval_cases v <;> native_decide

/-- The type number of a column of `swapRows01Code` is `swapVal01` of the
original type number (for a Columns07 code). -/
lemma colVal_swapRows01Code {n : ℕ} (C : Code n) (h07 : Columns07 C) (u : Fin n) :
    colVal (swapRows01Code C u) = swapVal01 (colVal (C u)) := by
  have hle : colVal (C u) ≤ 7 := Columns07_le7 C h07 u
  have h := colVal_swapRows01_of_le7 (colVal (C u)) hle
  rw [colOfNat_colVal (C u)] at h
  simpa [swapRows01Code, swapFlip01] using h

-- native_decide: Mechanical · n=any · checked 2026-08-28
/-- A number at most 7 has bit 3 cleared. -/
lemma testBit3_eq_false_of_le7 (v : ℕ) (h : v ≤ 7) : v.testBit 3 = false := by
  interval_cases v <;> native_decide

/-- `swapVal01` maps numbers 0..7 back into 0..7. -/
lemma swapVal01_le7 (v : ℕ) (h : v ≤ 7) : swapVal01 v ≤ 7 := by
  unfold swapVal01
  split_ifs <;> omega

/-- `swapRows01Code` preserves the Columns07 property. -/
lemma swapRows01Code_columns07 {n : ℕ} (C : Code n) (h07 : Columns07 C) :
    Columns07 (swapRows01Code C) := by
  intro u
  change colBit ⟨0, by decide⟩ (swapRows01Code C u) = false
  rw [colBit_eq_testBit]
  norm_num
  rw [colVal_swapRows01Code C h07 u]
  exact testBit3_eq_false_of_le7 (swapVal01 (colVal (C u)))
    (swapVal01_le7 (colVal (C u)) (Columns07_le7 C h07 u))

-- native_decide: Mechanical · n=any · checked 2026-08-28
/-- A type-1 column is fixed by the swap-and-flip equivalence. -/
lemma swapRows01Code_col1 {n : ℕ} (C : Code n) (h07 : Columns07 C) (t : Fin n)
    (hcol : C t = col1) : swapRows01Code C t = col1 := by
  have h1 : colVal (C t) = 1 := by rw [hcol]; native_decide
  have hcv : colVal (swapRows01Code C t) = 1 := by
    rw [colVal_swapRows01Code C h07 t, h1]
    native_decide
  exact (colVal_eq_one_iff_col1 (swapRows01Code C t)).1 hcv

/-- Counts of `swapRows01Code` are the `swapVal01`-relabelled counts of C. -/
lemma count_swapRows01Code {n : ℕ} (C : Code n) (h07 : Columns07 C) (i : ℕ) :
    count (swapRows01Code C) i = count C (swapVal01 i) := by
  exact count_involution_map C (swapRows01Code C) swapVal01
    (colVal_swapRows01Code C h07) swapVal01_idem i

/-- `wordTransform` with the identity permutation agrees with its inverse. -/
lemma wordTransform_refl_inv_eq {n : ℕ} (f : Fin n → Bool) :
    wordTransformInv (Equiv.refl (Fin n)) f = wordTransform (Equiv.refl (Fin n)) f := by
  funext y t
  rfl

/-- `wordFlip01` is self-inverse. -/
lemma wordFlip01_self_inverse {n : ℕ} (C : Code n) (y : Word n) :
    wordFlip01 C (wordFlip01 C y) = y := by
  unfold wordFlip01
  rw [← wordTransform_refl_inv_eq (swapFlip01 C)]
  exact wordTransform_inv_left (Equiv.refl (Fin n)) (swapFlip01 C) y

-- native_decide: Mechanical · n=any · checked 2026-08-28
/-- `wordFlip01` commutes with flipping the type-1 changed column. -/
lemma wordFlip01_flipBit {n : ℕ} (C : Code n) (t : Fin n) (hcol : C t = col1) (y : Word n) :
    wordFlip01 C (flipBit t y) = flipBit t (wordFlip01 C y) := by
  funext u
  unfold wordFlip01 wordTransform flipBit
  by_cases hut : u = t
  · subst u
    have hf : swapFlip01 C t = false := by
      unfold swapFlip01
      rw [hcol]; native_decide
    simp [hf]
  · by_cases hf : swapFlip01 C u = true <;> simp [hf, hut]

/-- Row distances transport through the swap-and-flip equivalence. -/
lemma dRow_swapRows01 {n : ℕ} (C : Code n) (_h07 : Columns07 C) (j : Fin 4) (y : Word n) :
    dRow (swapRows01Code C) j (wordFlip01 C y) = dRow C (swap01 j) y := by
  have hdef : ∀ t : Fin n, swapRows01Code C t =
      rowPermute swap01 (if swapFlip01 C t then flipCol (C t) else C t) := by
    intro t
    rfl
  have h := dRow_equiv C (swapRows01Code C) (ρ := swap01) (p := Equiv.refl (Fin n))
    (f := swapFlip01 C) hdef j (wordFlip01 C y)
  have hself : wordTransform (Equiv.refl (Fin n)) (swapFlip01 C) (wordFlip01 C y) = y := by
    unfold wordFlip01
    rw [← wordTransform_refl_inv_eq (swapFlip01 C)]
    exact wordTransform_inv_left (Equiv.refl (Fin n)) (swapFlip01 C) y
  rw [hself] at h
  simpa using h

/-- Rows of the swapped code are the transformed swapped rows of C. -/
lemma row_swapRows01 {n : ℕ} (C : Code n) (j : Fin 4) :
    row (swapRows01Code C) j = wordTransform (Equiv.refl (Fin n)) (swapFlip01 C) (row C (swap01 j)) := by
  funext u
  unfold row swapRows01Code wordTransform rowPermute flipCol colBit
  by_cases h : swapFlip01 C u = true <;> simp [h]

/-- The identity word transform preserves Hamming distance. -/
lemma wordTransform_refl_hammingDist {n : ℕ} (f : Fin n → Bool) (x y : Word n) :
    hammingDist (wordTransform (Equiv.refl (Fin n)) f x) (wordTransform (Equiv.refl (Fin n)) f y) = hammingDist x y := by
  unfold hammingDist hammingWeight bitXor wordTransform
  apply Finset.sum_congr rfl
  intro t _
  by_cases h : f t <;> simp [h]

/-- w(c₁ ⊕ c₃) of the swapped code is w(c₂ ⊕ c₃) of C. -/
lemma hammingDist_row0_row2_swapRows01 {n : ℕ} (C : Code n) :
    hammingDist (row0 (swapRows01Code C)) (row2 (swapRows01Code C)) =
      hammingDist (row1 C) (row2 C) := by
  change hammingDist (row (swapRows01Code C) 0) (row (swapRows01Code C) 2) = hammingDist (row1 C) (row2 C)
  rw [row_swapRows01 C 0, row_swapRows01 C 2]
  rw [wordTransform_refl_hammingDist (swapFlip01 C) (row C (swap01 0)) (row C (swap01 2))]
  rw [swap01_apply0, swap01_apply2]
  rfl

/-- w(c₃ ⊕ c₄) is preserved by the swap-and-flip equivalence. -/
lemma hammingDist_row2_row3_swapRows01 {n : ℕ} (C : Code n) :
    hammingDist (row2 (swapRows01Code C)) (row3 (swapRows01Code C)) =
      hammingDist (row2 C) (row3 C) := by
  change hammingDist (row (swapRows01Code C) 2) (row (swapRows01Code C) 3) = hammingDist (row2 C) (row3 C)
  rw [row_swapRows01 C 2, row_swapRows01 C 3]
  rw [wordTransform_refl_hammingDist (swapFlip01 C) (row C (swap01 2)) (row C (swap01 3))]
  rw [swap01_apply2, swap01_apply3]
  rfl

/-- d_P transports through the swap-and-flip equivalence. -/
lemma dP_swapRows01 {n : ℕ} (C : Code n) (h07 : Columns07 C) (y : Word n) :
    dP (swapRows01Code C) (wordFlip01 C y) = dP C y := by
  unfold dP
  change dRow (swapRows01Code C) 2 (wordFlip01 C y) = dRow C 2 y
  rw [dRow_swapRows01 C h07 2 y, swap01_apply2]

/-- d_O transports through the swap-and-flip equivalence. -/
lemma dO_swapRows01 {n : ℕ} (C : Code n) (h07 : Columns07 C) (y : Word n) :
    dO (swapRows01Code C) (wordFlip01 C y) = dO C y := by
  unfold dO
  change min (dRow (swapRows01Code C) 0 (wordFlip01 C y))
      (min (dRow (swapRows01Code C) 1 (wordFlip01 C y)) (dRow (swapRows01Code C) 3 (wordFlip01 C y))) =
    min (dRow C 0 y) (min (dRow C 1 y) (dRow C 3 y))
  rw [dRow_swapRows01 C h07 0 y, dRow_swapRows01 C h07 1 y, dRow_swapRows01 C h07 3 y,
    swap01_apply0, swap01_apply1, swap01_apply3]
  ac_rfl

/-- d_P' transports through the swap-and-flip equivalence. -/
lemma dPp_swapRows01 {n : ℕ} (C : Code n) (h07 : Columns07 C) (t : Fin n) (hcol : C t = col1) (y : Word n) :
    dPp (swapRows01Code C) t (wordFlip01 C y) = dPp C t y := by
  unfold dPp dP
  rw [← wordFlip01_flipBit C t hcol y]
  change dRow (swapRows01Code C) 2 (wordFlip01 C (flipBit t y)) = dRow C 2 (flipBit t y)
  rw [dRow_swapRows01 C h07 2 (flipBit t y), swap01_apply2]

/-- d_O' transports through the swap-and-flip equivalence. -/
lemma dOp_swapRows01 {n : ℕ} (C : Code n) (h07 : Columns07 C) (t : Fin n) (hcol : C t = col1) (y : Word n) :
    dOp (swapRows01Code C) t (wordFlip01 C y) = dOp C t y := by
  unfold dOp dO
  rw [← wordFlip01_flipBit C t hcol y]
  change min (dRow (swapRows01Code C) 0 (wordFlip01 C (flipBit t y)))
      (min (dRow (swapRows01Code C) 1 (wordFlip01 C (flipBit t y))) (dRow (swapRows01Code C) 3 (wordFlip01 C (flipBit t y)))) =
    min (dRow C 0 (flipBit t y)) (min (dRow C 1 (flipBit t y)) (dRow C 3 (flipBit t y)))
  rw [dRow_swapRows01 C h07 0 (flipBit t y), dRow_swapRows01 C h07 1 (flipBit t y),
    dRow_swapRows01 C h07 3 (flipBit t y), swap01_apply0, swap01_apply1, swap01_apply3]
  ac_rfl

/-- Y₃ is invariant under the swap-and-flip equivalence. -/
lemma Y3_swapRows01_iff {n : ℕ} (C : Code n) (h07 : Columns07 C) (t : Fin n) (hcol : C t = col1) (y : Word n) :
    Y3 C t y ↔ Y3 (swapRows01Code C) t (wordFlip01 C y) := by
  unfold Y3
  rw [dPp_swapRows01 C h07 t hcol y, dOp_swapRows01 C h07 t hcol y,
    dP_swapRows01 C h07 y, dO_swapRows01 C h07 y]

/-- Y₃-emptiness is invariant under the swap-and-flip equivalence. -/
lemma Y3_empty_swapRows01 {n : ℕ} (C : Code n) (h07 : Columns07 C) (t : Fin n) (hcol : C t = col1) :
    (∀ y : Word n, ¬ Y3 (swapRows01Code C) t y) ↔ (∀ y : Word n, ¬ Y3 C t y) := by
  constructor
  · intro h y hy
    exact h (wordFlip01 C y) ((Y3_swapRows01_iff C h07 t hcol y).1 hy)
  · intro h y hy
    have hy0 : Y3 (swapRows01Code C) t (wordFlip01 C (wordFlip01 C y)) := by
      rw [wordFlip01_self_inverse C y]
      exact hy
    have hyC : Y3 C t (wordFlip01 C y) := (Y3_swapRows01_iff C h07 t hcol (wordFlip01 C y)).2 hy0
    exact h (wordFlip01 C y) hyC

/-- The `thm:even` (Theorem 8) equality characterization restricted to the case
w(c₁ ⊕ c₃) odd and w(c₂ ⊕ c₃) even: Y₃ = ∅ iff condition (iii) holds. -/
theorem Y3_empty_iff_cond3 {n : ℕ} (C : Code n) (t : Fin n) (hcol : C t = col1) (h07 : Columns07 C)
    (_hOdd13 : Odd (hammingDist (row0 C) (row2 C)))
    (hEven12 : Even (hammingDist (row1 C) (row2 C)))
    (heven : Even (hammingDist (row2 C) (row3 C))) :
    (∀ y : Word n, ¬ Y3 C t y) ↔
      (count C 1 = 1 ∧ count C 2 = 0 ∧ count C 4 = 0 ∧ count C 6 = 0 ∧
        count C 7 = 0 ∧ Odd (count C 3) ∧ Odd (count C 5)) := by
  let Ct : Code n := swapRows01Code C
  constructor
  · intro h
    have hcol_t : Ct t = col1 := swapRows01Code_col1 C h07 t hcol
    have h07_t : Columns07 Ct := swapRows01Code_columns07 C h07
    have hEven13_t : Even (hammingDist (row0 Ct) (row2 Ct)) := by
      rw [hammingDist_row0_row2_swapRows01 C]
      exact hEven12
    have heven_t : Even (hammingDist (row2 Ct) (row3 Ct)) := by
      rw [hammingDist_row2_row3_swapRows01 C]
      exact heven
    have hY3 : ∀ y : Word n, ¬ Y3 Ct t y := (Y3_empty_swapRows01 C h07 t hcol).2 h
    have hcond2 := (Y3_empty_iff_cond2 Ct t hcol_t h07_t hEven13_t heven_t).1 hY3
    rcases hcond2 with ⟨hc1, hc2, hc4, hc5, hc7, hc3o, hc6o⟩
    have h1' : count C 1 = 1 := by
      have hEq : count Ct 1 = count C (swapVal01 1) := count_swapRows01Code C h07 1
      rw [hEq] at hc1
      simpa [swapVal01] using hc1
    have h2' : count C 2 = 0 := by
      have hEq : count Ct 2 = count C (swapVal01 2) := count_swapRows01Code C h07 2
      rw [hEq] at hc2
      simpa [swapVal01] using hc2
    have h4' : count C 4 = 0 := by
      have hEq : count Ct 7 = count C (swapVal01 7) := count_swapRows01Code C h07 7
      rw [hEq] at hc7
      simpa [swapVal01] using hc7
    have h6' : count C 6 = 0 := by
      have hEq : count Ct 5 = count C (swapVal01 5) := count_swapRows01Code C h07 5
      rw [hEq] at hc5
      simpa [swapVal01] using hc5
    have h7' : count C 7 = 0 := by
      have hEq : count Ct 4 = count C (swapVal01 4) := count_swapRows01Code C h07 4
      rw [hEq] at hc4
      simpa [swapVal01] using hc4
    have h3o' : Odd (count C 3) := by
      have hEq : count Ct 3 = count C (swapVal01 3) := count_swapRows01Code C h07 3
      rw [hEq] at hc3o
      simpa [swapVal01] using hc3o
    have h5o' : Odd (count C 5) := by
      have hEq : count Ct 6 = count C (swapVal01 6) := count_swapRows01Code C h07 6
      rw [hEq] at hc6o
      simpa [swapVal01] using hc6o
    exact ⟨h1', h2', h4', h6', h7', h3o', h5o'⟩
  · intro hiii
    rcases hiii with ⟨h1, h2, h4, h6, h7, h3o, h5o⟩
    exact Y3_empty_of_cond3 C t hcol h07 h1 h2 h4 h6 h7 h3o h5o

/-- `thm:even` (Theorem 8) equality part: Y3 = ∅ iff one of the three parity conditions
holds (paper §IV-D, Proof of Theorem 8, pp. 154--155).  This is the heavy 16-parity-case analysis of
(|2|,|3|,|6|,|7|) with explicit witness constructions; kept as a stub while
Phase E is in progress. -/
theorem Y3_empty_iff {n : ℕ} (C : Code n) (t : Fin n) (hcol : C t = col1)
    (heven : Even (hammingDist (row2 C) (row3 C))) (h07 : Columns07 C) :
    (∀ y : Word n, ¬ Y3 C t y) ↔
      (Odd (hammingDist (row0 C) (row2 C)) ∧
        Odd (hammingDist (row1 C) (row2 C))) ∨
      (count C 1 = 1 ∧ count C 2 = 0 ∧ count C 4 = 0 ∧ count C 5 = 0 ∧
          count C 7 = 0 ∧ Odd (count C 3) ∧ Odd (count C 6)) ∨
      (count C 1 = 1 ∧ count C 2 = 0 ∧ count C 4 = 0 ∧ count C 6 = 0 ∧
          count C 7 = 0 ∧ Odd (count C 3) ∧ Odd (count C 5)) := by
  constructor
  · intro h
    by_cases hAe : Even (hammingDist (row0 C) (row2 C))
    · right
      left
      exact (Y3_empty_iff_cond2 C t hcol h07 hAe heven).1 h
    · have hAo : Odd (hammingDist (row0 C) (row2 C)) := Nat.not_even_iff_odd.mp hAe
      by_cases hBe : Even (hammingDist (row1 C) (row2 C))
      · right
        right
        exact (Y3_empty_iff_cond3 C t hcol h07 hAo hBe heven).1 h
      · left
        exact ⟨hAo, Nat.not_even_iff_odd.mp hBe⟩
  · intro h
    rcases h with hi | hii | hiii
    · rcases hi with ⟨hw0, hw1⟩
      exact Y3_empty_of_w03_w13_odd C t hcol hw0 hw1
    · rcases hii with ⟨h1, h2, h4, h5, h7, h3o, h6o⟩
      exact Y3_empty_of_cond2 C t hcol h07 h1 h2 h4 h5 h7 h3o h6o
    · rcases hiii with ⟨h1, h2, h4, h6, h7, h3o, h5o⟩
      exact Y3_empty_of_cond3 C t hcol h07 h1 h2 h4 h6 h7 h3o h5o

/-- Theorem `thm:even` (Theorem 8) (1-bit flip): replacing a type-1 column by type 3,
with w(c3 ⊕ c4) even, is never worse; equality iff (i), (ii), or (iii). -/
theorem one_bit_flip {n : ℕ} (C C' : Code n) (t : Fin n)
    (hcol : C t = col1) (hcol' : C' t = col3)
    (hsame : ∀ u : Fin n, u ≠ t → C' u = C u)
    (heven : Even (hammingDist (row2 C) (row3 C)))
    (h07 : Columns07 C) :
    UniversalBetter C' C ∧
      (UniversalEqual C' C ↔
        (Odd (hammingDist (row0 C) (row2 C)) ∧
          Odd (hammingDist (row1 C) (row2 C))) ∨
        (count C 1 = 1 ∧ count C 2 = 0 ∧ count C 4 = 0 ∧ count C 5 = 0 ∧
            count C 7 = 0 ∧ Odd (count C 3) ∧ Odd (count C 6)) ∨
        (count C 1 = 1 ∧ count C 2 = 0 ∧ count C 4 = 0 ∧ count C 6 = 0 ∧
            count C 7 = 0 ∧ Odd (count C 3) ∧ Odd (count C 5))) := by
  constructor
  · exact one_bit_flip_better C C' t hcol hcol' hsame heven
  · have h := (cumulative_no_y5 C C' t hcol hcol' hsame
      (Y5_empty_of_even_w23 C t hcol heven)).2
    rw [h]
    exact Y3_empty_iff C t hcol heven h07

/-- `thm:even` (Theorem 8) strict version: a Y3 word makes the 1→3 flip strictly better at
every crossover probability. -/
theorem one_bit_flip_strict {n : ℕ} (C C' : Code n) (t : Fin n)
    (hcol : C t = col1) (hcol' : C' t = col3)
    (hsame : ∀ u : Fin n, u ≠ t → C' u = C u)
    (heven : Even (hammingDist (row2 C) (row3 C)))
    (hY3 : ∃ y : Word n, Y3 C t y) :
    UniversalStrictBetter C' C := by
  have h5 : ∀ y : Word n, ¬ Y5 C t y := Y5_empty_of_even_w23 C t hcol heven
  let S : Finset (Word n) := Finset.univ.filter (Y3 C t)
  have hgt : ∀ y : Word n, y ∈ S → dCode C y > dCode C' (g1 C t y) := by
    intro y hy
    have h3 : Y3 C t y := (Finset.mem_filter.mp hy).2
    have h := (y_rel_3 C C' t hcol hcol' hsame h3).2
    simp [g1, h3]
    omega
  have heq : ∀ y : Word n, y ∉ S → dCode C y = dCode C' (g1 C t y) := by
    intro y hy
    have h3 : ¬ Y3 C t y := by
      intro h3
      exact hy (Finset.mem_filter.mpr ⟨by simp, h3⟩)
    have hy14 : Y1 C t y ∨ Y2 C t y ∨ Y4 C t y := by
      rcases y_mem C t y with hy' | hy' | hy' | hy' | hy'
      · exact Or.inl hy'
      · exact Or.inr (Or.inl hy')
      · exfalso; exact h3 hy'
      · exact Or.inr (Or.inr hy')
      · exfalso; exact h5 y hy'
    rcases hy14 with hy1 | hy2 | hy4
    · have h := y_rel_1 C C' t hcol hcol' hsame hy1
      simp [g1, hy1, h.1]
    · have h1 : ¬ Y1 C t y := fun hy1 => Y1_Y2_disjoint C t y ⟨hy1, hy2⟩
      have h3' : ¬ Y3 C t y := fun hy3 => Y2_Y3_disjoint C t y ⟨hy2, hy3⟩
      have hg1 : g1 C t y = flipBit t y := by
        simp [g1, h1, h3']
      rw [hg1]
      exact (y_rel_2 C C' t hcol hcol' hsame hy2).1
    · have h1 : ¬ Y1 C t y := fun hy1 => Y1_Y4_disjoint C t y ⟨hy1, hy4⟩
      have h3' : ¬ Y3 C t y := fun hy3 => Y3_Y4_disjoint C t y ⟨hy3, hy4⟩
      have hg1 : g1 C t y = flipBit t y := by
        simp [g1, h1, h3']
      rw [hg1]
      exact (y_rel_4 C C' t hcol hcol' hsame hy4).2.1
  rcases hY3 with ⟨y, hy⟩
  exact compare_bij_strict C C' S (g1Equiv C t) hgt heq
    ⟨y, Finset.mem_filter.mpr ⟨by simp, hy⟩⟩

/-- Lemma `thm:class2` (Lemma 14) (1): a Class-II code is equal to some Class-I code with
|1| one smaller.  (Change a type-1 column to type 3; the two w-parities of
condition (i) of `thm:even` (Theorem 8) hold for both Class-II subclasses.) -/
theorem class2_to_class1 {n : ℕ} (C : Code n) (h : ClassII C) :
    ∃ C' : Code n, ClassI C' ∧ UniversalEqual C' C ∧ count C' 1 = count C 1 - 1 := by
  rcases h with ⟨h1pos, htot, hpar⟩
  have h1ge : 1 ≤ count C 1 := by omega
  rcases exists_col1_of_count_pos C h1ge with ⟨t, ht1⟩
  let C' : Code n := replaceColumn C t col3
  have hcol' : C' t = col3 := by simp [C', replaceColumn]
  have hsame : ∀ u : Fin n, u ≠ t → C' u = C u := by
    intro u hu
    simp [C', replaceColumn, hu]
  have htypes : ∀ t : Fin n, colVal (C t) = 1 ∨ colVal (C t) = 3 ∨
      colVal (C t) = 5 ∨ colVal (C t) = 6 := types_1356_of_totalCounts C htot
  have heven : Even (hammingDist (row2 C) (row3 C)) := by
    rw [hammingDist_row2_row3_of_types1356 C htypes]
    rcases hpar with hIIa | hIIb
    · rcases hIIa with ⟨h1e, _h3e, h5o, h6o⟩
      rcases h1e with ⟨a, ha⟩
      rcases h5o with ⟨b, hb⟩
      rcases h6o with ⟨c, hc⟩
      exact ⟨a + b + c + 1, by omega⟩
    · rcases hIIb with ⟨h1e, _h3o, h5e, h6e⟩
      rcases h1e with ⟨a, ha⟩
      rcases h5e with ⟨b, hb⟩
      rcases h6e with ⟨c, hc⟩
      exact ⟨a + b + c, by omega⟩
  have hw0 : Odd (hammingDist (row0 C) (row2 C)) := by
    rw [hammingDist_row0_row2_of_types1356 C htypes]
    rcases hpar with hIIa | hIIb
    · rcases hIIa with ⟨_h1e, h3e, _h5o, h6o⟩
      rcases h3e with ⟨a, ha⟩
      rcases h6o with ⟨b, hb⟩
      exact ⟨a + b, by omega⟩
    · rcases hIIb with ⟨_h1e, h3o, _h5e, h6e⟩
      rcases h3o with ⟨a, ha⟩
      rcases h6e with ⟨b, hb⟩
      exact ⟨a + b, by omega⟩
  have hw1 : Odd (hammingDist (row1 C) (row2 C)) := by
    rw [hammingDist_row1_row2_of_types1356 C htypes]
    rcases hpar with hIIa | hIIb
    · rcases hIIa with ⟨_h1e, h3e, h5o, _h6o⟩
      rcases h3e with ⟨a, ha⟩
      rcases h5o with ⟨b, hb⟩
      exact ⟨a + b, by omega⟩
    · rcases hIIb with ⟨_h1e, h3o, h5e, _h6e⟩
      rcases h3o with ⟨a, ha⟩
      rcases h5e with ⟨b, hb⟩
      exact ⟨a + b, by omega⟩
  have hflip := cumulative_no_y5 C C' t ht1 hcol' hsame
    (Y5_empty_of_even_w23 C t ht1 heven)
  have heq : UniversalEqual C' C :=
    (hflip.2).mpr (Y3_empty_of_w03_w13_odd C t ht1 hw0 hw1)
  have hc1' : ClassI C' := by
    constructor
    · have hcnt : count C' 1 = count C 1 - 1 := count_replace_1_3_one C t ht1
      rw [hcnt]
      rcases hpar with hIIa | hIIb
      · rcases hIIa with ⟨h1e, _h3e, _h5o, _h6o⟩
        rcases h1e with ⟨a, ha⟩
        exact ⟨a - 1, by omega⟩
      · rcases hIIb with ⟨h1e, _h3o, _h5e, _h6e⟩
        rcases h1e with ⟨a, ha⟩
        exact ⟨a - 1, by omega⟩
    · constructor
      · rcases hpar with hIIa | hIIb
        · rcases hIIa with ⟨_h1e, h3e, h5o, h6o⟩
          right
          constructor
          · rw [count_replace_1_3_three C t ht1]
            rcases h3e with ⟨a, ha⟩
            exact ⟨a, by omega⟩
          · constructor
            · rw [count_replace_1_3_other C t ht1 5 (by norm_num) (by norm_num)]
              exact h5o
            · rw [count_replace_1_3_other C t ht1 6 (by norm_num) (by norm_num)]
              exact h6o
        · rcases hIIb with ⟨_h1e, h3o, h5e, h6e⟩
          left
          constructor
          · rw [count_replace_1_3_three C t ht1]
            rcases h3o with ⟨a, ha⟩
            exact ⟨a + 1, by omega⟩
          · constructor
            · rw [count_replace_1_3_other C t ht1 5 (by norm_num) (by norm_num)]
              exact h5e
            · rw [count_replace_1_3_other C t ht1 6 (by norm_num) (by norm_num)]
              exact h6e
      · rw [totalCounts]
        simp [Finset.sum_insert]
        rw [count_replace_1_3_one C t ht1, count_replace_1_3_three C t ht1,
          count_replace_1_3_other C t ht1 5 (by norm_num) (by norm_num),
          count_replace_1_3_other C t ht1 6 (by norm_num) (by norm_num)]
        rw [totalCounts] at htot
        simp [Finset.sum_insert] at htot
        omega
  exact ⟨C', hc1', heq, count_replace_1_3_one C t ht1⟩


-- native_decide: Mechanical · n=any · checked 2026-08-28
/-- w(c₂ ⊕ c₄) = |1|+|3|+|4|+|6| for a Columns07 code. -/
lemma hammingDist_row1_row3_eq {n : ℕ} (C : Code n) (h07 : Columns07 C) :
    hammingDist (row1 C) (row3 C) = count C 1 + count C 3 + count C 4 + count C 6 := by
  have hS : ∀ t : Fin n, colVal (C t) ∈ Finset.Icc 0 7 := by
    intro t
    rw [Finset.mem_Icc]
    exact ⟨Nat.zero_le _, Columns07_le7 C h07 t⟩
  unfold row1 row3
  rw [hammingDist_rows_of_types C ⟨1, by decide⟩ ⟨3, by decide⟩ (Finset.Icc 0 7) hS, sum_Icc0_7]
  have h10 : (1 : ℕ).testBit 2 = false := by native_decide
  have h11 : (1 : ℕ).testBit 0 = true := by native_decide
  have h30 : (3 : ℕ).testBit 2 = false := by native_decide
  have h31 : (3 : ℕ).testBit 0 = true := by native_decide
  have h40 : (4 : ℕ).testBit 2 = true := by native_decide
  have h41 : (4 : ℕ).testBit 0 = false := by native_decide
  have h60 : (6 : ℕ).testBit 2 = true := by native_decide
  have h61 : (6 : ℕ).testBit 0 = false := by native_decide
  have h00 : (0 : ℕ).testBit 2 = false := by native_decide
  have h01 : (0 : ℕ).testBit 0 = false := by native_decide
  have h20 : (2 : ℕ).testBit 2 = false := by native_decide
  have h21 : (2 : ℕ).testBit 0 = false := by native_decide
  have h50 : (5 : ℕ).testBit 2 = true := by native_decide
  have h51 : (5 : ℕ).testBit 0 = true := by native_decide
  have h70 : (7 : ℕ).testBit 2 = true := by native_decide
  have h71 : (7 : ℕ).testBit 0 = true := by native_decide
  simp [h00, h01, h10, h11, h20, h21, h30, h31, h40, h41, h50, h51, h60, h61, h70, h71]

-- native_decide: Mechanical · n=any · checked 2026-08-28
/-- Columns of types 1..6 are all Columns07 (row 1 bit clear). -/
lemma Columns07_of_types16 {n : ℕ} (C : Code n) (h : totalCounts C {1, 2, 3, 4, 5, 6} = n) :
    Columns07 C := by
  intro t
  have hm := colVal_mem_of_totalCounts C ({1, 2, 3, 4, 5, 6} : Finset ℕ) h t
  simp [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with h1 | h2 | h3 | h4 | h5 | h6
  · change colBit ⟨0, by decide⟩ (C t) = false
    rw [colBit_eq_testBit, h1]; native_decide
  · change colBit ⟨0, by decide⟩ (C t) = false
    rw [colBit_eq_testBit, h2]; native_decide
  · change colBit ⟨0, by decide⟩ (C t) = false
    rw [colBit_eq_testBit, h3]; native_decide
  · change colBit ⟨0, by decide⟩ (C t) = false
    rw [colBit_eq_testBit, h4]; native_decide
  · change colBit ⟨0, by decide⟩ (C t) = false
    rw [colBit_eq_testBit, h5]; native_decide
  · change colBit ⟨0, by decide⟩ (C t) = false
    rw [colBit_eq_testBit, h6]; native_decide

/-- A positive |i| count gives a column of type i. -/
lemma exists_col_of_colVal {n : ℕ} (C : Code n) (i : ℕ) (h : 1 ≤ count C i) :
    ∃ t : Fin n, colVal (C t) = i := by
  have hcard : 1 ≤ (Finset.univ.filter fun t : Fin n => colVal (C t) = i).card := by
    simpa [count_eq_card] using h
  rcases Finset.card_pos.mp (by omega : 0 < (Finset.univ.filter fun t : Fin n => colVal (C t) = i).card) with ⟨t, ht⟩
  exact ⟨t, (Finset.mem_filter.mp ht).2⟩

/-! ## Generalized one-bit flip transport (`thm:even` (Theorem 8) remark rm:code1)

The remark after `thm:even` (Theorem 8) says the 1→3 flip extends to flipping any single
row bit by a row-permutation equivalence.  Here we build that transport and
the two orientations needed for `cor:twopo` (Corollary 9): type 1→5 and type 2→6. -/

/-- Apply a row permutation to every column of a code. -/
def rowPermutedCode {n : ℕ} (ρ : Equiv (Fin 4) (Fin 4)) (C : Code n) : Code n :=
  fun t => rowPermute ρ (C t)

/-- `rowPermutedCode` is an equivalence. -/
lemma rowPermutedCode_equiv {n : ℕ} (ρ : Equiv (Fin 4) (Fin 4)) (C : Code n) :
    Equivalent C (rowPermutedCode ρ C) := by
  refine ⟨ρ, Equiv.refl (Fin n), fun _ => false, ?_⟩
  intro t
  simp [rowPermutedCode]

/-- Rows of a row-permuted code are the permuted rows of the original code. -/
lemma row_rowPermutedCode {n : ℕ} (ρ : Equiv (Fin 4) (Fin 4)) (C : Code n) (j : Fin 4) :
    row (rowPermutedCode ρ C) j = row C (ρ j) := by
  funext t
  simp [row, rowPermutedCode, rowPermute, colBit]

/-- Universal domination transports across equivalent codes. -/
lemma universalBetter_of_equivalent {n : ℕ} (C₁ C₁' C₂ C₂' : Code n)
    (h1 : Equivalent C₁ C₁') (h2 : Equivalent C₂ C₂') (h : UniversalBetter C₁' C₂') :
    UniversalBetter C₁ C₂ := by
  intro ε hε0 hε1
  have hge := h ε hε0 hε1
  have heq1 := lambda_equiv C₁ C₁' h1 ε
  have heq2 := lambda_equiv C₂ C₂' h2 ε
  linarith

/-- Universal equality transports across equivalent codes. -/
lemma universalEqual_of_equivalent' {n : ℕ} (C₁ C₁' C₂ C₂' : Code n)
    (h1 : Equivalent C₁ C₁') (h2 : Equivalent C₂ C₂') (h : UniversalEqual C₁' C₂') :
    UniversalEqual C₁ C₂ := by
  intro ε hε0 hε1
  have heq := h ε hε0 hε1
  have heq1 := lambda_equiv C₁ C₁' h1 ε
  have heq2 := lambda_equiv C₂ C₂' h2 ε
  linarith

/-- The row permutation for the type 1→5 orientation (swap rows 2 and 3). -/
def rho15 : Equiv (Fin 4) (Fin 4) := Equiv.swap (1 : Fin 4) (2 : Fin 4)

-- native_decide: Mechanical · n=any · checked 2026-08-28
lemma rho15_col1 : rowPermute rho15 col1 = col1 := by native_decide
-- native_decide: Mechanical · n=any · checked 2026-08-28
lemma rho15_col5 : rowPermute rho15 col5 = col3 := by native_decide

/-- The row permutation for the type 2→6 orientation. -/
def rho26 : Equiv (Fin 4) (Fin 4) :=
  Equiv.trans (Equiv.swap (1 : Fin 4) (3 : Fin 4)) (Equiv.swap (1 : Fin 4) (2 : Fin 4))

-- native_decide: Mechanical · n=any · checked 2026-08-28
lemma rho26_col2 : rowPermute rho26 (colOfNat 2) = col1 := by native_decide
-- native_decide: Mechanical · n=any · checked 2026-08-28
lemma rho26_col6 : rowPermute rho26 col6 = col3 := by native_decide

/-- `thm:even` (Theorem 8) orientation 1→5: replacing a type-1 column by type 5 is never
worse when w(c₂ ⊕ c₄) is even. -/
-- native_decide: Mechanical · n=any · checked 2026-08-28
theorem one_bit_flip_1_to_5 {n : ℕ} (C C' : Code n) (t : Fin n)
    (hcol : C t = col1) (hcol' : C' t = col5)
    (hsame : ∀ u : Fin n, u ≠ t → C' u = C u)
    (heven : Even (hammingDist (row1 C) (row3 C))) :
    UniversalBetter C' C := by
  let Cρ : Code n := rowPermutedCode rho15 C
  let C'ρ : Code n := rowPermutedCode rho15 C'
  have hcolρ : Cρ t = col1 := by
    unfold Cρ rowPermutedCode
    rw [hcol]
    exact rho15_col1
  have hcol'ρ : C'ρ t = col3 := by
    unfold C'ρ rowPermutedCode
    rw [hcol']
    exact rho15_col5
  have hsameρ : ∀ u : Fin n, u ≠ t → C'ρ u = Cρ u := by
    intro u hu
    unfold C'ρ Cρ rowPermutedCode
    rw [hsame u hu]
  have hC'ρ : C'ρ = replaceColumn Cρ t col3 := by
    funext u
    by_cases hu : u = t
    · subst u
      simp [C'ρ, Cρ, rowPermutedCode, replaceColumn, hcol', rho15_col5]
    · have hsu : C' u = C u := hsame u hu
      simp [C'ρ, Cρ, rowPermutedCode, replaceColumn, hu, hsu]
  have hevenρ : Even (hammingDist (row2 Cρ) (row3 Cρ)) := by
    change Even (hammingDist (row (rowPermutedCode rho15 C) 2) (row (rowPermutedCode rho15 C) 3))
    rw [row_rowPermutedCode rho15 C 2, row_rowPermutedCode rho15 C 3]
    rw [show rho15 2 = (1 : Fin 4) by native_decide, show rho15 3 = (3 : Fin 4) by native_decide]
    exact heven
  have hbetter : UniversalBetter C'ρ Cρ := by
    have h := one_bit_flip_better Cρ (replaceColumn Cρ t col3) t hcolρ (by simp [replaceColumn]) (by
      intro u hu
      simp [replaceColumn, hu]) hevenρ
    simpa [hC'ρ] using h
  exact universalBetter_of_equivalent C' C'ρ C Cρ
    (rowPermutedCode_equiv rho15 C') (rowPermutedCode_equiv rho15 C) hbetter

/-- `thm:even` (Theorem 8) orientation 2→6: replacing a type-2 column by type 6 is never
worse when w(c₂ ⊕ c₃) is even. -/
-- native_decide: Mechanical · n=any · checked 2026-08-28
theorem one_bit_flip_2_to_6 {n : ℕ} (C C' : Code n) (t : Fin n)
    (hcol : C t = colOfNat 2) (hcol' : C' t = col6)
    (hsame : ∀ u : Fin n, u ≠ t → C' u = C u)
    (heven : Even (hammingDist (row1 C) (row2 C))) :
    UniversalBetter C' C := by
  let Cρ : Code n := rowPermutedCode rho26 C
  let C'ρ : Code n := rowPermutedCode rho26 C'
  have hcolρ : Cρ t = col1 := by
    unfold Cρ rowPermutedCode
    rw [hcol]
    exact rho26_col2
  have hcol'ρ : C'ρ t = col3 := by
    unfold C'ρ rowPermutedCode
    rw [hcol']
    exact rho26_col6
  have hsameρ : ∀ u : Fin n, u ≠ t → C'ρ u = Cρ u := by
    intro u hu
    unfold C'ρ Cρ rowPermutedCode
    rw [hsame u hu]
  have hC'ρ : C'ρ = replaceColumn Cρ t col3 := by
    funext u
    by_cases hu : u = t
    · subst u
      simp [C'ρ, Cρ, rowPermutedCode, replaceColumn, hcol', rho26_col6]
    · have hsu : C' u = C u := hsame u hu
      simp [C'ρ, Cρ, rowPermutedCode, replaceColumn, hu, hsu]
  have hevenρ : Even (hammingDist (row2 Cρ) (row3 Cρ)) := by
    change Even (hammingDist (row (rowPermutedCode rho26 C) 2) (row (rowPermutedCode rho26 C) 3))
    rw [row_rowPermutedCode rho26 C 2, row_rowPermutedCode rho26 C 3]
    rw [show rho26 2 = (1 : Fin 4) by native_decide, show rho26 3 = (2 : Fin 4) by native_decide]
    exact heven
  have hbetter : UniversalBetter C'ρ Cρ := by
    have h := one_bit_flip_better Cρ (replaceColumn Cρ t col3) t hcolρ (by simp [replaceColumn]) (by
      intro u hu
      simp [replaceColumn, hu]) hevenρ
    simpa [hC'ρ] using h
  exact universalBetter_of_equivalent C' C'ρ C Cρ
    (rowPermutedCode_equiv rho26 C') (rowPermutedCode_equiv rho26 C) hbetter

/-! ## `cor:twopo` (Corollary 9) descent helpers -/

/-- One of three integers is even when their sum is even. -/
lemma one_of_three_even {a b c : ℕ} (h : Even (a + b + c)) :
    Even a ∨ Even b ∨ Even c := by
  by_cases ha : Even a
  · exact Or.inl ha
  · by_cases hb : Even b
    · exact Or.inr (Or.inl hb)
    · right; right
      have hao : Odd a := Nat.not_even_iff_odd.mp ha
      have hbo : Odd b := Nat.not_even_iff_odd.mp hb
      rcases h with ⟨m, hm⟩
      rcases hao with ⟨p, hp⟩
      rcases hbo with ⟨q, hq⟩
      exact ⟨m - p - q - 1, by omega⟩


/-- `totalCounts` is the number of columns whose type lies in the set. -/
lemma totalCounts_eq_sum_indicator {n : ℕ} (C : Code n) (S : Finset ℕ) :
    totalCounts C S = ∑ u : Fin n, if colVal (C u) ∈ S then 1 else 0 := by
  symm
  rw [show (∑ u : Fin n, if colVal (C u) ∈ S then 1 else 0) =
        ∑ u : Fin n, ∑ i ∈ S, if colVal (C u) = i then 1 else 0 by
        apply Finset.sum_congr rfl
        intro u _
        by_cases hu : colVal (C u) ∈ S
        · rw [Finset.sum_ite_eq]
        · simp [hu]]
  rw [totalCounts]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  unfold count
  rfl

/-- Replacing a column by another whose type is in the same type set preserves
`totalCounts` over that set. -/
lemma totalCounts_replace_eq {n : ℕ} (C : Code n) (t : Fin n) (s' : Column) (S : Finset ℕ)
    (ha : colVal (C t) ∈ S) (hb : colVal s' ∈ S) :
    totalCounts (replaceColumn C t s') S = totalCounts C S := by
  rw [totalCounts_eq_sum_indicator, totalCounts_eq_sum_indicator]
  apply Finset.sum_congr rfl
  intro u _
  by_cases hu : u = t
  · subst u
    simp [replaceColumn, ha, hb]
  · simp [replaceColumn, hu]

/-- The three `thm:even` (Theorem 8) parity weights sum to `2n` for a 1..6-code. -/
lemma sum_weights_even {n : ℕ} (C : Code n) (h : totalCounts C {1,2,3,4,5,6} = n) :
    Even (hammingDist (row1 C) (row2 C) + hammingDist (row2 C) (row3 C) + hammingDist (row1 C) (row3 C)) := by
  have h07 : Columns07 C := Columns07_of_types16 C h
  rw [hammingDist_row1_row2_eq C h07, hammingDist_row2_row3_eq C h07, hammingDist_row1_row3_eq C h07]
  have hcounts := by simpa [totalCounts, Finset.sum_insert] using h
  exact ⟨n, by omega⟩

/-- When |1|>0 and |2|>0, one of the three single-bit flips applies and gives a
better code with strictly smaller |1|+|2|+|4|.

One descent step of the proof of `cor:twopo` (Corollary 9), paper §III-A,
Proof of Corollary 9, p. 144.  With both |1| and |2| positive, one of the three
pairwise weights (paper eqs. (34)--(36))
  w(c₂⊕c₃) = |2|+|3|+|4|+|5|,   w(c₃⊕c₄) = |1|+|2|+|5|+|6|,
  w(c₂⊕c₄) = |1|+|3|+|4|+|6|
is even (`sum_weights_even` + `one_of_three_even`), and the corresponding
`thm:even` (Theorem 8) flip applies: type 2→6, 1→3, or 1→5 (cases a), b), c)
below).

The strict decrease of the measure |1|+|2|+|4| is the Lean counterpart of the
paper's "as long as |1| and |2| are positive, the above step can be repeated";
it makes the descent in `only_types_13456` terminate.  The
|1|>0,|4|>0 and |2|>0,|4|>0 cases are reduced to this one by row
interchanges in `interchange_step_15`/`interchange_step_13`, matching the
paper's "other cases can be converted to this case by interchanging rows". -/
-- native_decide: Mechanical · n=any · checked 2026-08-28
lemma step_12 {n : ℕ} (C : Code n) (h : totalCounts C {1,2,3,4,5,6} = n)
    (h1pos : 0 < count C 1) (h2pos : 0 < count C 2) :
    ∃ C' : Code n, UniversalBetter C' C ∧ totalCounts C' {1,2,3,4,5,6} = n ∧
      count C' 1 + count C' 2 + count C' 4 < count C 1 + count C 2 + count C 4 := by
  have h07 : Columns07 C := Columns07_of_types16 C h
  have hsum := sum_weights_even C h
  have hone := one_of_three_even hsum
  rcases hone with hA | hB | hC
  · -- A even: flip type 2 -> 6
    rcases exists_col_of_colVal C 2 (by omega : 1 ≤ count C 2) with ⟨t, ht2⟩
    let C' : Code n := replaceColumn C t col6
    have hcol : C t = colOfNat 2 := by
      have hc := colOfNat_colVal (C t)
      rw [ht2] at hc
      exact hc.symm
    have hcol' : C' t = col6 := by simp [C', replaceColumn]
    have hsame : ∀ u : Fin n, u ≠ t → C' u = C u := by
      intro u hu; simp [C', replaceColumn, hu]
    have hbetter : UniversalBetter C' C := one_bit_flip_2_to_6 C C' t hcol hcol' hsame hA
    have htot : totalCounts C' {1,2,3,4,5,6} = n := by
      rw [totalCounts_replace_eq C t col6 ({1,2,3,4,5,6} : Finset ℕ) (by simp [ht2]) (by native_decide)]
      exact h
    have hc2 : count C' 2 = count C 2 - 1 := count_replace_dec C t col6 2 ht2 (by native_decide)
    have hc4 : count C' 4 = count C 4 := count_replace_eq C t col6 4 (by intro h4; rw [ht2] at h4; norm_num at h4) (by native_decide)
    have hc1 : count C' 1 = count C 1 := count_replace_eq C t col6 1 (by intro h1; rw [ht2] at h1; norm_num at h1) (by native_decide)
    refine ⟨C', hbetter, htot, ?_⟩
    omega
  · -- B even: flip type 1 -> 3
    rcases exists_col_of_colVal C 1 (by omega : 1 ≤ count C 1) with ⟨t, ht1⟩
    let C' : Code n := replaceColumn C t col3
    have hcol : C t = col1 := (colVal_eq_one_iff_col1 (C t)).1 ht1
    have hcol' : C' t = col3 := by simp [C', replaceColumn]
    have hsame : ∀ u : Fin n, u ≠ t → C' u = C u := by
      intro u hu; simp [C', replaceColumn, hu]
    have hbetter : UniversalBetter C' C := one_bit_flip_better C C' t hcol hcol' hsame hB
    have htot : totalCounts C' {1,2,3,4,5,6} = n := by
      rw [totalCounts_replace_eq C t col3 ({1,2,3,4,5,6} : Finset ℕ) (by simp [ht1]) (by native_decide)]
      exact h
    have hc1 : count C' 1 = count C 1 - 1 := count_replace_dec C t col3 1 ht1 (by native_decide)
    have hc2 : count C' 2 = count C 2 := count_replace_eq C t col3 2 (by intro h2; rw [ht1] at h2; norm_num at h2) (by native_decide)
    have hc4 : count C' 4 = count C 4 := count_replace_eq C t col3 4 (by intro h4; rw [ht1] at h4; norm_num at h4) (by native_decide)
    refine ⟨C', hbetter, htot, ?_⟩
    omega
  · -- C even: flip type 1 -> 5
    rcases exists_col_of_colVal C 1 (by omega : 1 ≤ count C 1) with ⟨t, ht1⟩
    let C' : Code n := replaceColumn C t col5
    have hcol : C t = col1 := (colVal_eq_one_iff_col1 (C t)).1 ht1
    have hcol' : C' t = col5 := by simp [C', replaceColumn]
    have hsame : ∀ u : Fin n, u ≠ t → C' u = C u := by
      intro u hu; simp [C', replaceColumn, hu]
    have hbetter : UniversalBetter C' C := one_bit_flip_1_to_5 C C' t hcol hcol' hsame hC
    have htot : totalCounts C' {1,2,3,4,5,6} = n := by
      rw [totalCounts_replace_eq C t col5 ({1,2,3,4,5,6} : Finset ℕ) (by simp [ht1]) (by native_decide)]
      exact h
    have hc1 : count C' 1 = count C 1 - 1 := count_replace_dec C t col5 1 ht1 (by native_decide)
    have hc2 : count C' 2 = count C 2 := count_replace_eq C t col5 2 (by intro h2; rw [ht1] at h2; norm_num at h2) (by native_decide)
    have hc4 : count C' 4 = count C 4 := count_replace_eq C t col5 4 (by intro h4; rw [ht1] at h4; norm_num at h4) (by native_decide)
    refine ⟨C', hbetter, htot, ?_⟩
    omega

/-- The row permutation swapping rows 2 and 4 (indices 1 and 3). -/
def rho13 : Equiv (Fin 4) (Fin 4) := Equiv.swap (1 : Fin 4) (3 : Fin 4)


/-- Universal equality in the symmetric equivalence direction. -/
lemma universalEqual_symm_of_equiv {n : ℕ} (C C' : Code n) (h : Equivalent C C') :
    UniversalEqual C C' := by
  intro ε h0 h1
  exact (lambda_equiv C C' h ε).symm

/-- Universal domination through an equal left-hand side. -/
lemma universalBetter_of_equal_left {n : ℕ} (C₁ C₂ C₃ : Code n)
    (h12 : UniversalEqual C₁ C₂) (h23 : UniversalBetter C₂ C₃) :
    UniversalBetter C₁ C₃ := by
  intro ε h0 h1
  have h12' := h12 ε h0 h1
  have h23' := h23 ε h0 h1
  linarith

/-- Universal domination through an equal right-hand side. -/
lemma universalBetter_of_equal_right {n : ℕ} (C₁ C₂ C₃ : Code n)
    (h12 : UniversalBetter C₁ C₂) (h23 : UniversalEqual C₂ C₃) :
    UniversalBetter C₁ C₃ := by
  intro ε h0 h1
  have h12' := h12 ε h0 h1
  have h23' := h23 ε h0 h1
  linarith

/-- Count transport for a row permutation mapping 1..6 types by a known rule. -/
lemma count_rowPermutedCode_of {n : ℕ} (ρ : Equiv (Fin 4) (Fin 4)) (C : Code n) (i j : ℕ)
    (hS : ∀ t : Fin n, colVal (C t) ∈ ({1,2,3,4,5,6} : Finset ℕ))
    (h : ∀ v ∈ ({1,2,3,4,5,6} : Finset ℕ), colVal (rowPermute ρ (colOfNat v)) = i ↔ v = j) :
    count (rowPermutedCode ρ C) i = count C j := by
  unfold count rowPermutedCode
  apply Finset.sum_congr rfl
  intro t _
  have hcv : colVal (C t) ∈ ({1,2,3,4,5,6} : Finset ℕ) := hS t
  rw [show rowPermute ρ (C t) = rowPermute ρ (colOfNat (colVal (C t))) by rw [colOfNat_colVal (C t)]]
  have hiff := h (colVal (C t)) hcv
  by_cases hcol : colVal (rowPermute ρ (colOfNat (colVal (C t)))) = i
  · have hj : colVal (C t) = j := hiff.mp hcol
    rw [if_pos hcol, if_pos hj]
  · have hj : ¬ colVal (C t) = j := fun hj => hcol (hiff.mpr hj)
    rw [if_neg hcol, if_neg hj]

-- native_decide: Mechanical · n=any · checked 2026-08-28
lemma count_rho15_1 {n : ℕ} (C : Code n) (h : totalCounts C {1,2,3,4,5,6} = n) :
    count (rowPermutedCode rho15 C) 1 = count C 1 := by
  apply count_rowPermutedCode_of rho15 C 1 1
  · intro t; exact colVal_mem_of_totalCounts C {1,2,3,4,5,6} h t
  · intro v hv
    simp [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with h1 | h2 | h3 | h4 | h5 | h6 <;> subst v <;> native_decide

-- native_decide: Mechanical · n=any · checked 2026-08-28
lemma count_rho15_2 {n : ℕ} (C : Code n) (h : totalCounts C {1,2,3,4,5,6} = n) :
    count (rowPermutedCode rho15 C) 2 = count C 4 := by
  apply count_rowPermutedCode_of rho15 C 2 4
  · intro t; exact colVal_mem_of_totalCounts C {1,2,3,4,5,6} h t
  · intro v hv
    simp [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with h1 | h2 | h3 | h4 | h5 | h6 <;> subst v <;> native_decide

-- native_decide: Mechanical · n=any · checked 2026-08-28
lemma count_rho15_4 {n : ℕ} (C : Code n) (h : totalCounts C {1,2,3,4,5,6} = n) :
    count (rowPermutedCode rho15 C) 4 = count C 2 := by
  apply count_rowPermutedCode_of rho15 C 4 2
  · intro t; exact colVal_mem_of_totalCounts C {1,2,3,4,5,6} h t
  · intro v hv
    simp [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with h1 | h2 | h3 | h4 | h5 | h6 <;> subst v <;> native_decide

-- native_decide: Mechanical · n=any · checked 2026-08-28
lemma count_rho13_1 {n : ℕ} (C : Code n) (h : totalCounts C {1,2,3,4,5,6} = n) :
    count (rowPermutedCode rho13 C) 1 = count C 4 := by
  apply count_rowPermutedCode_of rho13 C 1 4
  · intro t; exact colVal_mem_of_totalCounts C {1,2,3,4,5,6} h t
  · intro v hv
    simp [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with h1 | h2 | h3 | h4 | h5 | h6 <;> subst v <;> native_decide

-- native_decide: Mechanical · n=any · checked 2026-08-28
lemma count_rho13_2 {n : ℕ} (C : Code n) (h : totalCounts C {1,2,3,4,5,6} = n) :
    count (rowPermutedCode rho13 C) 2 = count C 2 := by
  apply count_rowPermutedCode_of rho13 C 2 2
  · intro t; exact colVal_mem_of_totalCounts C {1,2,3,4,5,6} h t
  · intro v hv
    simp [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with h1 | h2 | h3 | h4 | h5 | h6 <;> subst v <;> native_decide

-- native_decide: Mechanical · n=any · checked 2026-08-28
lemma count_rho13_4 {n : ℕ} (C : Code n) (h : totalCounts C {1,2,3,4,5,6} = n) :
    count (rowPermutedCode rho13 C) 4 = count C 1 := by
  apply count_rowPermutedCode_of rho13 C 4 1
  · intro t; exact colVal_mem_of_totalCounts C {1,2,3,4,5,6} h t
  · intro v hv
    simp [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with h1 | h2 | h3 | h4 | h5 | h6 <;> subst v <;> native_decide

/-- `totalCounts` over a permuted type set is preserved by a row permutation. -/
lemma totalCounts_rowPermutedCode_eq {n : ℕ} (ρ : Equiv (Fin 4) (Fin 4)) (C : Code n) (S : Finset ℕ)
    (hS : ∀ t : Fin n, colVal (C t) ∈ S)
    (hperm : ∀ v ∈ S, colVal (rowPermute ρ (colOfNat v)) ∈ S) :
    totalCounts (rowPermutedCode ρ C) S = totalCounts C S := by
  rw [totalCounts_eq_sum_indicator, totalCounts_eq_sum_indicator]
  apply Finset.sum_congr rfl
  intro t _
  have hcv : colVal (C t) ∈ S := hS t
  unfold rowPermutedCode
  rw [show rowPermute ρ (C t) = rowPermute ρ (colOfNat (colVal (C t))) by rw [colOfNat_colVal (C t)]]
  have hmem : colVal (rowPermute ρ (colOfNat (colVal (C t)))) ∈ S := hperm (colVal (C t)) hcv
  simp [hcv, hmem]

-- native_decide: Mechanical · n=any · checked 2026-08-28
lemma totalCounts_rowPermutedCode_rho15 {n : ℕ} (C : Code n) (h : totalCounts C {1,2,3,4,5,6} = n) :
    totalCounts (rowPermutedCode rho15 C) {1,2,3,4,5,6} = n := by
  rw [totalCounts_rowPermutedCode_eq rho15 C {1,2,3,4,5,6}]
  · exact h
  · intro t; exact colVal_mem_of_totalCounts C {1,2,3,4,5,6} h t
  · intro v hv
    simp [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with h1 | h2 | h3 | h4 | h5 | h6 <;> subst v <;> native_decide

-- native_decide: Mechanical · n=any · checked 2026-08-28
lemma totalCounts_rowPermutedCode_rho13 {n : ℕ} (C : Code n) (h : totalCounts C {1,2,3,4,5,6} = n) :
    totalCounts (rowPermutedCode rho13 C) {1,2,3,4,5,6} = n := by
  rw [totalCounts_rowPermutedCode_eq rho13 C {1,2,3,4,5,6}]
  · exact h
  · intro t; exact colVal_mem_of_totalCounts C {1,2,3,4,5,6} h t
  · intro v hv
    simp [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with h1 | h2 | h3 | h4 | h5 | h6 <;> subst v <;> native_decide

/-! ## §3.4 Main reductions -/

/-- `totalCounts` transported into a target type set via a row permutation. -/
lemma totalCounts_rowPermutedCode_into {n : ℕ} (ρ : Equiv (Fin 4) (Fin 4)) (C : Code n) (A B : Finset ℕ)
    (hA : totalCounts C A = n)
    (hcol : ∀ t : Fin n, colVal (C t) ∈ A)
    (hmaps : ∀ v ∈ A, colVal (rowPermute ρ (colOfNat v)) ∈ B) :
    totalCounts (rowPermutedCode ρ C) B = n := by
  rw [totalCounts_eq_sum_indicator]
  rw [totalCounts_eq_sum_indicator] at hA
  trans ∑ u : Fin n, if colVal (C u) ∈ A then 1 else 0
  · apply Finset.sum_congr rfl
    intro t _
    have hcv : colVal (C t) ∈ A := hcol t
    unfold rowPermutedCode
    rw [show rowPermute ρ (C t) = rowPermute ρ (colOfNat (colVal (C t))) by rw [colOfNat_colVal (C t)]]
    have hmem : colVal (rowPermute ρ (colOfNat (colVal (C t)))) ∈ B := hmaps (colVal (C t)) hcv
    simp [hcv, hmem]
  · exact hA

/-- With |1|=|4|=0, every column of a 1..6-code has type in {2,3,5,6}. -/
lemma hcol_mem_2356_of_16 {n : ℕ} (C : Code n) (h : totalCounts C {1,2,3,4,5,6} = n)
    (hc1 : count C 1 = 0) (hc4 : count C 4 = 0) (t : Fin n) :
    colVal (C t) ∈ ({2,3,5,6} : Finset ℕ) := by
  have hm := colVal_mem_of_totalCounts C {1,2,3,4,5,6} h t
  simp [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with h1 | h2 | h3 | h4 | h5 | h6
  · exfalso; have hp := count_pos_of_colVal C t h1; omega
  · simp [h2]
  · simp [h3]
  · exfalso; have hp := count_pos_of_colVal C t h4; omega
  · simp [h5]
  · simp [h6]

/-- With |1|=|2|=0, every column of a 1..6-code has type in {3,4,5,6}. -/
lemma hcol_mem_3456_of_16 {n : ℕ} (C : Code n) (h : totalCounts C {1,2,3,4,5,6} = n)
    (hc1 : count C 1 = 0) (hc2 : count C 2 = 0) (t : Fin n) :
    colVal (C t) ∈ ({3,4,5,6} : Finset ℕ) := by
  have hm := colVal_mem_of_totalCounts C {1,2,3,4,5,6} h t
  simp [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with h1 | h2 | h3 | h4 | h5 | h6
  · exfalso; have hp := count_pos_of_colVal C t h1; omega
  · exfalso; have hp := count_pos_of_colVal C t h2; omega
  · simp [h3]
  · simp [h4]
  · simp [h5]
  · simp [h6]

-- native_decide: Mechanical · n=any · checked 2026-08-28
/-- `rho26` maps types {2,3,5,6} into {1,3,5,6}. -/
lemma hmaps_rho26_2356_to_1356 (v : ℕ) (hv : v ∈ ({2,3,5,6} : Finset ℕ)) :
    colVal (rowPermute rho26 (colOfNat v)) ∈ ({1,3,5,6} : Finset ℕ) := by
  simp [Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with h2 | h3 | h5 | h6 <;> subst v <;> native_decide

-- native_decide: Mechanical · n=any · checked 2026-08-28
/-- `rho13` maps types {3,4,5,6} into {1,3,5,6}. -/
lemma hmaps_rho13_3456_to_1356 (v : ℕ) (hv : v ∈ ({3,4,5,6} : Finset ℕ)) :
    colVal (rowPermute rho13 (colOfNat v)) ∈ ({1,3,5,6} : Finset ℕ) := by
  simp [Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with h3 | h4 | h5 | h6 <;> subst v <;> native_decide

/-- `totalCounts` restricted to {2,3,5,6} equals n when |1|=|4|=0. -/
lemma totalCounts_2356_of_16 {n : ℕ} (C : Code n) (h : totalCounts C {1,2,3,4,5,6} = n)
    (hc1 : count C 1 = 0) (hc4 : count C 4 = 0) :
    totalCounts C {2,3,5,6} = n := by
  simp [totalCounts, Finset.sum_insert] at h ⊢
  omega

/-- `totalCounts` restricted to {3,4,5,6} equals n when |1|=|2|=0. -/
lemma totalCounts_3456_of_16 {n : ℕ} (C : Code n) (h : totalCounts C {1,2,3,4,5,6} = n)
    (hc1 : count C 1 = 0) (hc2 : count C 2 = 0) :
    totalCounts C {3,4,5,6} = n := by
  simp [totalCounts, Finset.sum_insert] at h ⊢
  omega

/-- `totalCounts` restricted to {1,3,5,6} equals n when |2|=|4|=0. -/
lemma totalCounts_1356_of_16 {n : ℕ} (C : Code n) (h : totalCounts C {1,2,3,4,5,6} = n)
    (hc2 : count C 2 = 0) (hc4 : count C 4 = 0) :
    totalCounts C {1,3,5,6} = n := by
  simp [totalCounts, Finset.sum_insert] at h ⊢
  omega

/-- Interchange rows 2,3 plus `step_12` reduces |1|+|2|+|4| when |1|,|4|>0. -/
lemma interchange_step_15 {n : ℕ} (C : Code n) (h : totalCounts C {1,2,3,4,5,6} = n)
    (h1 : 0 < count C 1) (h4 : 0 < count C 4) :
    ∃ C' : Code n, UniversalBetter C' C ∧ totalCounts C' {1,2,3,4,5,6} = n ∧
      count C' 1 + count C' 2 + count C' 4 < count C 1 + count C 2 + count C 4 := by
  let D := rowPermutedCode rho15 C
  have htotD : totalCounts D {1,2,3,4,5,6} = n := totalCounts_rowPermutedCode_rho15 C h
  have h1D : 0 < count D 1 := by rw [count_rho15_1 C h]; exact h1
  have h2D : 0 < count D 2 := by rw [count_rho15_2 C h]; exact h4
  rcases step_12 D htotD h1D h2D with ⟨D₂, hbD, htD, hmD⟩
  let E := rowPermutedCode rho15 D₂
  have htotE : totalCounts E {1,2,3,4,5,6} = n := totalCounts_rowPermutedCode_rho15 D₂ htD
  have hbetterE : UniversalBetter E C := by
    have hEqED : UniversalEqual E D₂ := universalEqual_of_equivalent D₂ E (rowPermutedCode_equiv rho15 D₂)
    have hbetterED : UniversalBetter E D := universalBetter_of_equal_left E D₂ D hEqED hbD
    have hEqDC : UniversalEqual D C := universalEqual_of_equivalent C D (rowPermutedCode_equiv rho15 C)
    exact universalBetter_of_equal_right E D C hbetterED hEqDC
  have hmeasE : count E 1 + count E 2 + count E 4 < count C 1 + count C 2 + count C 4 := by
    rw [count_rho15_1 D₂ htD, count_rho15_2 D₂ htD, count_rho15_4 D₂ htD]
    rw [count_rho15_1 C h, count_rho15_2 C h, count_rho15_4 C h] at hmD
    omega
  exact ⟨E, hbetterE, htotE, hmeasE⟩

/-- Interchange rows 2,4 plus `step_12` reduces |1|+|2|+|4| when |2|,|4|>0. -/
lemma interchange_step_13 {n : ℕ} (C : Code n) (h : totalCounts C {1,2,3,4,5,6} = n)
    (h2 : 0 < count C 2) (h4 : 0 < count C 4) :
    ∃ C' : Code n, UniversalBetter C' C ∧ totalCounts C' {1,2,3,4,5,6} = n ∧
      count C' 1 + count C' 2 + count C' 4 < count C 1 + count C 2 + count C 4 := by
  let D := rowPermutedCode rho13 C
  have htotD : totalCounts D {1,2,3,4,5,6} = n := totalCounts_rowPermutedCode_rho13 C h
  have h1D : 0 < count D 1 := by rw [count_rho13_1 C h]; exact h4
  have h2D : 0 < count D 2 := by rw [count_rho13_2 C h]; exact h2
  rcases step_12 D htotD h1D h2D with ⟨D₂, hbD, htD, hmD⟩
  let E := rowPermutedCode rho13 D₂
  have htotE : totalCounts E {1,2,3,4,5,6} = n := totalCounts_rowPermutedCode_rho13 D₂ htD
  have hbetterE : UniversalBetter E C := by
    have hEqED : UniversalEqual E D₂ := universalEqual_of_equivalent D₂ E (rowPermutedCode_equiv rho13 D₂)
    have hbetterED : UniversalBetter E D := universalBetter_of_equal_left E D₂ D hEqED hbD
    have hEqDC : UniversalEqual D C := universalEqual_of_equivalent C D (rowPermutedCode_equiv rho13 C)
    exact universalBetter_of_equal_right E D C hbetterED hEqDC
  have hmeasE : count E 1 + count E 2 + count E 4 < count C 1 + count C 2 + count C 4 := by
    rw [count_rho13_1 D₂ htD, count_rho13_2 D₂ htD, count_rho13_4 D₂ htD]
    rw [count_rho13_1 C h, count_rho13_2 C h, count_rho13_4 C h] at hmD
    omega
  exact ⟨E, hbetterE, htotE, hmeasE⟩

/-- Corollary `cor:twopo` (Corollary 9): any code with columns 1..6 only has a better code
with columns only from types 1,3,5,6. -/
theorem only_types_13456 {n : ℕ} (C : Code n)
    (h : totalCounts C {1, 2, 3, 4, 5, 6} = n) :
    ∃ C' : Code n, UniversalBetter C' C ∧ totalCounts C' {1, 3, 5, 6} = n := by
  let P : ℕ → Prop := fun m => ∀ C₀ : Code n, totalCounts C₀ {1,2,3,4,5,6} = n →
    count C₀ 1 + count C₀ 2 + count C₀ 4 = m → ∃ C' : Code n, UniversalBetter C' C₀ ∧ totalCounts C' {1,3,5,6} = n
  have hP : ∀ m : ℕ, P m := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro C₀ htot hmeas
      by_cases h12 : 0 < count C₀ 1 ∧ 0 < count C₀ 2
      · rcases step_12 C₀ htot h12.1 h12.2 with ⟨C₁, hb₁, ht₁, hm₁⟩
        have hm₁' : count C₁ 1 + count C₁ 2 + count C₁ 4 < m := by
          rw [hmeas] at hm₁
          exact hm₁
        rcases ih (count C₁ 1 + count C₁ 2 + count C₁ 4) hm₁' C₁ ht₁ rfl with ⟨C', hb', ht'⟩
        exact ⟨C', universalBetter_trans hb' hb₁, ht'⟩
      · by_cases h14 : 0 < count C₀ 1 ∧ 0 < count C₀ 4
        · rcases interchange_step_15 C₀ htot h14.1 h14.2 with ⟨C₁, hb₁, ht₁, hm₁⟩
          have hm₁' : count C₁ 1 + count C₁ 2 + count C₁ 4 < m := by
            rw [hmeas] at hm₁
            exact hm₁
          rcases ih (count C₁ 1 + count C₁ 2 + count C₁ 4) hm₁' C₁ ht₁ rfl with ⟨C', hb', ht'⟩
          exact ⟨C', universalBetter_trans hb' hb₁, ht'⟩
        · by_cases h24 : 0 < count C₀ 2 ∧ 0 < count C₀ 4
          · rcases interchange_step_13 C₀ htot h24.1 h24.2 with ⟨C₁, hb₁, ht₁, hm₁⟩
            have hm₁' : count C₁ 1 + count C₁ 2 + count C₁ 4 < m := by
              rw [hmeas] at hm₁
              exact hm₁
            rcases ih (count C₁ 1 + count C₁ 2 + count C₁ 4) hm₁' C₁ ht₁ rfl with ⟨C', hb', ht'⟩
            exact ⟨C', universalBetter_trans hb' hb₁, ht'⟩
          · by_cases h1 : 0 < count C₀ 1
            · have h2z : count C₀ 2 = 0 := by omega
              have h4z : count C₀ 4 = 0 := by omega
              refine ⟨C₀, universalBetter_refl C₀, ?_⟩
              exact totalCounts_1356_of_16 C₀ htot h2z h4z
            · by_cases h2 : 0 < count C₀ 2
              · have h1z : count C₀ 1 = 0 := by omega
                have h4z : count C₀ 4 = 0 := by omega
                let C' := rowPermutedCode rho26 C₀
                refine ⟨C', ?_, ?_⟩
                · exact universalBetter_of_equal_left C' C₀ C₀ (universalEqual_of_equivalent C₀ C' (rowPermutedCode_equiv rho26 C₀)) (universalBetter_refl C₀)
                · exact totalCounts_rowPermutedCode_into rho26 C₀ {2,3,5,6} {1,3,5,6}
                    (totalCounts_2356_of_16 C₀ htot h1z h4z)
                    (hcol_mem_2356_of_16 C₀ htot h1z h4z) hmaps_rho26_2356_to_1356
              · by_cases h4 : 0 < count C₀ 4
                · have h1z : count C₀ 1 = 0 := by omega
                  have h2z : count C₀ 2 = 0 := by omega
                  let C' := rowPermutedCode rho13 C₀
                  refine ⟨C', ?_, ?_⟩
                  · exact universalBetter_of_equal_left C' C₀ C₀ (universalEqual_of_equivalent C₀ C' (rowPermutedCode_equiv rho13 C₀)) (universalBetter_refl C₀)
                  · exact totalCounts_rowPermutedCode_into rho13 C₀ {3,4,5,6} {1,3,5,6}
                      (totalCounts_3456_of_16 C₀ htot h1z h2z)
                      (hcol_mem_3456_of_16 C₀ htot h1z h2z) hmaps_rho13_3456_to_1356
                · have h1z : count C₀ 1 = 0 := by omega
                  have h2z : count C₀ 2 = 0 := by omega
                  have h4z : count C₀ 4 = 0 := by omega
                  refine ⟨C₀, universalBetter_refl C₀, ?_⟩
                  exact totalCounts_1356_of_16 C₀ htot h2z h4z
  exact hP (count C 1 + count C 2 + count C 4) C h rfl

-- native_decide: Mechanical · n=any · checked 2026-08-28
/-- w(c₁⊕c₄) = |1|+|3|+|5| for a code with only types 1,3,5,6. -/
lemma hammingDist_row0_row3_of_types1356 {n : ℕ} (C : Code n)
    (h : ∀ t : Fin n, colVal (C t) = 1 ∨ colVal (C t) = 3 ∨ colVal (C t) = 5 ∨ colVal (C t) = 6) :
    hammingDist (row0 C) (row3 C) = count C 1 + count C 3 + count C 5 := by
  have hS : ∀ t : Fin n, colVal (C t) ∈ ({1, 3, 5, 6} : Finset ℕ) := by
    intro t
    rcases h t with h1 | h3 | h5 | h6
    · simp [h1]
    · simp [h3]
    · simp [h5]
    · simp [h6]
  unfold row0 row3
  rw [hammingDist_rows_of_types C ⟨0, by decide⟩ ⟨3, by decide⟩ ({1, 3, 5, 6} : Finset ℕ) hS]
  have h1a : (1 : ℕ).testBit 3 = false := by native_decide
  have h3a : (3 : ℕ).testBit 3 = false := by native_decide
  have h5a : (5 : ℕ).testBit 3 = false := by native_decide
  have h6a : (6 : ℕ).testBit 3 = false := by native_decide
  simp [Finset.sum_insert, h1a, h3a, h5a, h6a]
  omega

-- native_decide: Mechanical · n=any · checked 2026-08-28
/-- w(c₂⊕c₄) = |1|+|3|+|6| for a code with only types 1,3,5,6. -/
lemma hammingDist_row1_row3_of_types1356 {n : ℕ} (C : Code n)
    (h : ∀ t : Fin n, colVal (C t) = 1 ∨ colVal (C t) = 3 ∨ colVal (C t) = 5 ∨ colVal (C t) = 6) :
    hammingDist (row1 C) (row3 C) = count C 1 + count C 3 + count C 6 := by
  have hS : ∀ t : Fin n, colVal (C t) ∈ ({1, 3, 5, 6} : Finset ℕ) := by
    intro t
    rcases h t with h1 | h3 | h5 | h6
    · simp [h1]
    · simp [h3]
    · simp [h5]
    · simp [h6]
  unfold row1 row3
  rw [hammingDist_rows_of_types C ⟨1, by decide⟩ ⟨3, by decide⟩ ({1, 3, 5, 6} : Finset ℕ) hS]
  have h1a : (1 : ℕ).testBit 2 = false := by native_decide
  have h3a : (3 : ℕ).testBit 2 = false := by native_decide
  have h5a : (5 : ℕ).testBit 2 = true := by native_decide
  have h6a : (6 : ℕ).testBit 2 = true := by native_decide
  simp [Finset.sum_insert, h1a, h3a, h5a, h6a]
  omega

-- native_decide: Mechanical · n=any · checked 2026-08-28
/-- A {1,3,5,6}-code is a Columns07 code. -/
lemma Columns07_of_types_1356 {n : ℕ} (C : Code n)
    (h : totalCounts C {1, 3, 5, 6} = n) : Columns07 C := by
  intro t
  have hm := colVal_mem_of_totalCounts C ({1, 3, 5, 6} : Finset ℕ) h t
  simp [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with h1 | h3 | h5 | h6
  · change colBit ⟨0, by decide⟩ (C t) = false
    rw [colBit_eq_testBit, h1]; native_decide
  · change colBit ⟨0, by decide⟩ (C t) = false
    rw [colBit_eq_testBit, h3]; native_decide
  · change colBit ⟨0, by decide⟩ (C t) = false
    rw [colBit_eq_testBit, h5]; native_decide
  · change colBit ⟨0, by decide⟩ (C t) = false
    rw [colBit_eq_testBit, h6]; native_decide

/-- `swapRows01Code` is an equivalence. -/
lemma swapRows01Code_equiv {n : ℕ} (C : Code n) : Equivalent C (swapRows01Code C) := by
  refine ⟨swap01, Equiv.refl (Fin n), swapFlip01 C, ?_⟩
  intro t
  rfl

/-- w(c₂⊕c₄) of the swapped code is w(c₁⊕c₄) of C. -/
lemma hammingDist_row1_row3_swapRows01 {n : ℕ} (C : Code n) :
    hammingDist (row1 (swapRows01Code C)) (row3 (swapRows01Code C)) =
      hammingDist (row0 C) (row3 C) := by
  change hammingDist (row (swapRows01Code C) 1) (row (swapRows01Code C) 3) = hammingDist (row0 C) (row3 C)
  rw [row_swapRows01 C 1, row_swapRows01 C 3]
  rw [wordTransform_refl_hammingDist (swapFlip01 C) (row C (swap01 1)) (row C (swap01 3))]
  rw [swap01_apply1, swap01_apply3]
  rfl

/-- `swapRows01Code` preserves `totalCounts` over {1,3,5,6}. -/
lemma totalCounts_swapRows01Code_1356 {n : ℕ} (C : Code n) (h07 : Columns07 C)
    (h : totalCounts C {1,3,5,6} = n) :
    totalCounts (swapRows01Code C) {1,3,5,6} = n := by
  simp [totalCounts, Finset.sum_insert] at h ⊢
  rw [count_swapRows01Code C h07 1, count_swapRows01Code C h07 3,
      count_swapRows01Code C h07 5, count_swapRows01Code C h07 6]
  simp [swapVal01]
  omega

/-- The row permutation swapping rows 1 and 3 (indices 0 and 2). -/
def swap02 : Equiv (Fin 4) (Fin 4) := Equiv.swap (0 : Fin 4) (2 : Fin 4)

/-- The column-type relabelling induced by `swap02` plus the flip of columns
leaving the type-0..7 range: swaps 2↔7 and 3↔6, fixes 1,4,5. -/
def swapVal02 (i : ℕ) : ℕ :=
  if i = 2 then 7 else if i = 7 then 2 else if i = 3 then 6 else if i = 6 then 3 else i

/-- `swapVal02` is an involution. -/
lemma swapVal02_idem (i : ℕ) : swapVal02 (swapVal02 i) = i := by
  by_cases h2 : i = 2 <;> by_cases h7 : i = 7 <;> by_cases h3 : i = 3 <;>
    by_cases h6 : i = 6 <;> simp [swapVal02, h2, h7, h3, h6]

/-- The flip indicator for the row-0/2 swap equivalence. -/
def swapFlip02 {n : ℕ} (C : Code n) (u : Fin n) : Bool :=
  if 7 < colVal (rowPermute swap02 (C u)) then true else false

/-- The code obtained from C by swapping rows 1,3 and flipping columns whose
swapped type number exceeds 7. -/
def swapRows02Code {n : ℕ} (C : Code n) : Code n :=
  fun u => rowPermute swap02 (if swapFlip02 C u then flipCol (C u) else C u)

-- native_decide: Mechanical · n=any · checked 2026-08-28
lemma swap02_apply0 : swap02 0 = (2 : Fin 4) := by native_decide
-- native_decide: Mechanical · n=any · checked 2026-08-28
lemma swap02_apply2 : swap02 2 = (0 : Fin 4) := by native_decide
-- native_decide: Mechanical · n=any · checked 2026-08-28
lemma swap02_apply3 : swap02 3 = (3 : Fin 4) := by native_decide

/-- The type number of a swapped-and-flipped 0..7 column is `swapVal02` of the
original type number. -/
-- native_decide: Mechanical · n=any · checked 2026-08-28
lemma colVal_swapRows02_of_le7 (v : ℕ) (hv : v ≤ 7) :
    colVal (rowPermute swap02
      (if 7 < colVal (rowPermute swap02 (colOfNat v)) then flipCol (colOfNat v)
        else colOfNat v)) = swapVal02 v := by
  interval_cases v <;> native_decide

/-- The type number of a column of `swapRows02Code` is `swapVal02` of the
original type number (for a Columns07 code). -/
lemma colVal_swapRows02Code {n : ℕ} (C : Code n) (h07 : Columns07 C) (u : Fin n) :
    colVal (swapRows02Code C u) = swapVal02 (colVal (C u)) := by
  have hle : colVal (C u) ≤ 7 := Columns07_le7 C h07 u
  have h := colVal_swapRows02_of_le7 (colVal (C u)) hle
  rw [colOfNat_colVal (C u)] at h
  simpa [swapRows02Code, swapFlip02] using h

/-- `swapVal02` maps numbers 0..7 back into 0..7. -/
lemma swapVal02_le7 (v : ℕ) (h : v ≤ 7) : swapVal02 v ≤ 7 := by
  unfold swapVal02
  split_ifs <;> omega

/-- `swapRows02Code` preserves the Columns07 property. -/
lemma swapRows02Code_columns07 {n : ℕ} (C : Code n) (h07 : Columns07 C) :
    Columns07 (swapRows02Code C) := by
  intro u
  change colBit ⟨0, by decide⟩ (swapRows02Code C u) = false
  rw [colBit_eq_testBit]
  norm_num
  rw [colVal_swapRows02Code C h07 u]
  exact testBit3_eq_false_of_le7 (swapVal02 (colVal (C u)))
    (swapVal02_le7 (colVal (C u)) (Columns07_le7 C h07 u))

/-- `swapRows02Code` is an equivalence. -/
lemma swapRows02Code_equiv {n : ℕ} (C : Code n) : Equivalent C (swapRows02Code C) := by
  refine ⟨swap02, Equiv.refl (Fin n), swapFlip02 C, ?_⟩
  intro t
  rfl

/-- Counts of `swapRows02Code` are the `swapVal02`-relabelled counts of C. -/
lemma count_swapRows02Code {n : ℕ} (C : Code n) (h07 : Columns07 C) (i : ℕ) :
    count (swapRows02Code C) i = count C (swapVal02 i) := by
  exact count_involution_map C (swapRows02Code C) swapVal02
    (colVal_swapRows02Code C h07) swapVal02_idem i

/-- Rows of the swapped code are the transformed swapped rows of C. -/
lemma row_swapRows02 {n : ℕ} (C : Code n) (j : Fin 4) :
    row (swapRows02Code C) j = wordTransform (Equiv.refl (Fin n)) (swapFlip02 C) (row C (swap02 j)) := by
  funext u
  unfold row swapRows02Code wordTransform rowPermute flipCol colBit
  by_cases h : swapFlip02 C u = true <;> simp [h]

/-- w(c₃⊕c₄) of the swapped code is w(c₁⊕c₄) of C. -/
lemma hammingDist_row2_row3_swapRows02 {n : ℕ} (C : Code n) :
    hammingDist (row2 (swapRows02Code C)) (row3 (swapRows02Code C)) =
      hammingDist (row0 C) (row3 C) := by
  change hammingDist (row (swapRows02Code C) 2) (row (swapRows02Code C) 3) = hammingDist (row0 C) (row3 C)
  rw [row_swapRows02 C 2, row_swapRows02 C 3]
  rw [wordTransform_refl_hammingDist (swapFlip02 C) (row C (swap02 2)) (row C (swap02 3))]
  rw [swap02_apply2, swap02_apply3]
  rfl

/-- `swapRows02Code` preserves `totalCounts` over {1,3,5,6}. -/
lemma totalCounts_swapRows02Code_1356 {n : ℕ} (C : Code n) (h07 : Columns07 C)
    (h : totalCounts C {1,3,5,6} = n) :
    totalCounts (swapRows02Code C) {1,3,5,6} = n := by
  simp [totalCounts, Finset.sum_insert] at h ⊢
  rw [count_swapRows02Code C h07 1, count_swapRows02Code C h07 3,
      count_swapRows02Code C h07 5, count_swapRows02Code C h07 6]
  simp [swapVal02]
  omega

/-- `totalCounts` over {3,5,6} when there are no type-1 columns. -/
lemma totalCounts_356_of_1356 {n : ℕ} (C : Code n)
    (h : totalCounts C {1,3,5,6} = n) (h1 : count C 1 = 0) :
    totalCounts C {3,5,6} = n := by
  simp [totalCounts, Finset.sum_insert] at h ⊢
  omega

/-- A {1,3,5,6}-code with no type-1 columns and at least two positive linear
types is linear. -/
lemma isLinear_of_count1_zero_1356 {n : ℕ} (C : Code n)
    (h : totalCounts C {1,3,5,6} = n) (h1 : count C 1 = 0)
    (h2pos : (count C 3 > 0 ∧ count C 5 > 0) ∨ (count C 3 > 0 ∧ count C 6 > 0) ∨
      (count C 5 > 0 ∧ count C 6 > 0)) :
    IsLinear C := by
  constructor
  · intro t
    have hm := colVal_mem_of_totalCounts C ({1,3,5,6} : Finset ℕ) h t
    simp [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with hv1 | hv3 | hv5 | hv6
    · exfalso
      have hge : 1 ≤ count C 1 := count_pos_of_colVal C t hv1
      omega
    · right; left; exact hv3
    · right; right; left; exact hv5
    · right; right; right; exact hv6
  · exact h2pos

/-- b is even when a and a+b are even. -/
lemma even_of_even_of_even_add {a b : ℕ} (hab : Even (a + b)) (ha : Even a) : Even b := by
  rcases hab with ⟨k, hk⟩
  rcases ha with ⟨m, hm⟩
  refine ⟨k - m, by omega⟩

/-- b is odd when a+b is even and a is odd. -/
lemma odd_of_even_add_odd {a b : ℕ} (hab : Even (a + b)) (ha : Odd a) : Odd b := by
  rcases hab with ⟨k, hk⟩
  rcases ha with ⟨m, hm⟩
  refine ⟨k - m - 1, by omega⟩

/-- If all three `cor:onepo` (Corollary 10) weights are odd then the code has Class-I parity. -/
lemma not_even_three_weights_imp_class1_parity (c1 c3 c5 c6 : ℕ)
    (hnA : ¬ Even (c1 + c3 + c5)) (hnB : ¬ Even (c1 + c5 + c6)) (hnC : ¬ Even (c1 + c3 + c6)) :
    Odd c1 ∧ ((Even c3 ∧ Even c5 ∧ Even c6) ∨ (Odd c3 ∧ Odd c5 ∧ Odd c6)) := by
  have hAo : Odd (c1 + c3 + c5) := Nat.not_even_iff_odd.mp hnA
  have hBo : Odd (c1 + c5 + c6) := Nat.not_even_iff_odd.mp hnB
  have hCo : Odd (c1 + c3 + c6) := Nat.not_even_iff_odd.mp hnC
  have hA : (Odd c1 ↔ Even (c3 + c5)) := (Nat.odd_add (m := c1) (n := c3 + c5)).mp (by simpa [Nat.add_assoc] using hAo)
  have hB : (Odd c1 ↔ Even (c5 + c6)) := (Nat.odd_add (m := c1) (n := c5 + c6)).mp (by simpa [Nat.add_assoc] using hBo)
  have hC : (Odd c1 ↔ Even (c3 + c6)) := (Nat.odd_add (m := c1) (n := c3 + c6)).mp (by simpa [Nat.add_assoc] using hCo)
  have hc1 : Odd c1 := by
    by_contra hnot
    have h35o : Odd (c3 + c5) := Nat.not_even_iff_odd.mp ((hA.not).mp hnot)
    have h56o : Odd (c5 + c6) := Nat.not_even_iff_odd.mp ((hB.not).mp hnot)
    have h36o : Odd (c3 + c6) := Nat.not_even_iff_odd.mp ((hC.not).mp hnot)
    rcases h35o with ⟨a, ha⟩
    rcases h56o with ⟨b, hb⟩
    rcases h36o with ⟨d, hd⟩
    omega
  constructor
  · exact hc1
  · have h35 : Even (c3 + c5) := hA.mp hc1
    have h56 : Even (c5 + c6) := hB.mp hc1
    have h36 : Even (c3 + c6) := hC.mp hc1
    by_cases h3 : Even c3
    · have h5 : Even c5 := even_of_even_of_even_add h35 h3
      have h6 : Even c6 := even_of_even_of_even_add h56 h5
      exact Or.inl ⟨h3, h5, h6⟩
    · have h3o : Odd c3 := Nat.not_even_iff_odd.mp h3
      have h5o : Odd c5 := odd_of_even_add_odd h35 h3o
      have h6o : Odd c6 := odd_of_even_add_odd h56 h5o
      exact Or.inr ⟨h3o, h5o, h6o⟩

/-- An odd sum has a positive term. -/
lemma pos_of_odd_sum {a b : ℕ} (h : Odd (a + b)) : 0 < a ∨ 0 < b := by
  by_cases ha : 0 < a
  · exact Or.inl ha
  · right
    have ha0 : a = 0 := by omega
    rw [ha0] at h
    rcases h with ⟨k, hk⟩
    omega

/-- Even (1 + a + b) forces a + b odd. -/
lemma odd_sum_of_even_one_add {a b : ℕ} (h : Even (1 + a + b)) : Odd (a + b) := by
  rw [Nat.add_assoc] at h
  have hiff := (Nat.even_add' (m := 1) (n := a + b)).mp h
  exact hiff.mp odd_one

-- native_decide: Mechanical · n=any · checked 2026-08-28
/-- Single descent step of `cor:onepo` (Corollary 10). -/
lemma onepo_step {n : ℕ} (C : Code n)
    (h : totalCounts C {1,3,5,6} = n)
    (hnc1 : ¬ ClassI C) (h1pos : 0 < count C 1) :
    ∃ C₁ : Code n, UniversalBetter C₁ C ∧ totalCounts C₁ {1,3,5,6} = n ∧
      count C₁ 1 = count C 1 - 1 ∧ (count C 1 = 1 → IsLinear C₁) := by
  have htypes : ∀ t : Fin n, colVal (C t) = 1 ∨ colVal (C t) = 3 ∨
      colVal (C t) = 5 ∨ colVal (C t) = 6 := types_1356_of_totalCounts C h
  have h07 : Columns07 C := Columns07_of_types_1356 C h
  have hone : Even (hammingDist (row0 C) (row3 C)) ∨
      Even (hammingDist (row2 C) (row3 C)) ∨
      Even (hammingDist (row1 C) (row3 C)) := by
    by_contra hnot
    have hnA : ¬ Even (hammingDist (row0 C) (row3 C)) := fun hA => hnot (Or.inl hA)
    have hnB : ¬ Even (hammingDist (row2 C) (row3 C)) := fun hB => hnot (Or.inr (Or.inl hB))
    have hnC : ¬ Even (hammingDist (row1 C) (row3 C)) := fun hC => hnot (Or.inr (Or.inr hC))
    have hA' : ¬ Even (count C 1 + count C 3 + count C 5) := by
      rw [hammingDist_row0_row3_of_types1356 C htypes] at hnA
      exact hnA
    have hB' : ¬ Even (count C 1 + count C 5 + count C 6) := by
      rw [hammingDist_row2_row3_of_types1356 C htypes] at hnB
      exact hnB
    have hC' : ¬ Even (count C 1 + count C 3 + count C 6) := by
      rw [hammingDist_row1_row3_of_types1356 C htypes] at hnC
      exact hnC
    have hpar := not_even_three_weights_imp_class1_parity (count C 1) (count C 3) (count C 5) (count C 6) hA' hB' hC'
    exact hnc1 ⟨hpar.1, hpar.2, h⟩
  rcases hone with hA | hB | hC
  · -- wA even: transport via swap-and-flip, then flip type 1 -> 5
    rcases exists_col1_of_count_pos C (by omega : 1 ≤ count C 1) with ⟨t, ht1⟩
    let D : Code n := swapRows01Code C
    let C₁ : Code n := replaceColumn D t col5
    have hcolD : D t = col1 := swapRows01Code_col1 C h07 t ht1
    have hcol₁ : C₁ t = col5 := by simp [C₁, replaceColumn]
    have hsame : ∀ u : Fin n, u ≠ t → C₁ u = D u := by
      intro u hu
      simp [C₁, replaceColumn, hu]
    have hevenD : Even (hammingDist (row1 D) (row3 D)) := by
      rw [hammingDist_row1_row3_swapRows01 C]
      exact hA
    have hbetterD : UniversalBetter C₁ D := one_bit_flip_1_to_5 D C₁ t hcolD hcol₁ hsame hevenD
    have hEqDC : UniversalEqual D C := universalEqual_of_equivalent C D (swapRows01Code_equiv C)
    have hbetter : UniversalBetter C₁ C := universalBetter_of_equal_right C₁ D C hbetterD hEqDC
    have hcvD : colVal (D t) = 1 := by rw [hcolD]; native_decide
    have htot₁ : totalCounts C₁ {1,3,5,6} = n := by
      rw [totalCounts_replace_eq D t col5 ({1,3,5,6} : Finset ℕ) (by simp [hcvD]) (by native_decide)]
      exact totalCounts_swapRows01Code_1356 C h07 h
    have hcnt₁ : count C₁ 1 = count C 1 - 1 := by
      have hd1 : count D 1 = count C 1 := by
        rw [count_swapRows01Code C h07 1]
        rw [show swapVal01 1 = 1 by native_decide]
      rw [count_replace_dec D t col5 1 (by rw [hcolD]; native_decide) (by native_decide), hd1]
    refine ⟨C₁, hbetter, htot₁, hcnt₁, ?_⟩
    intro h1
    have hcnt₀ : count C₁ 1 = 0 := by omega
    apply isLinear_of_count1_zero_1356 C₁ htot₁ hcnt₀
    have hc5 : 0 < count C₁ 5 := by
      have hd5 : count D 5 = count C 6 := by
        rw [count_swapRows01Code C h07 5]
        rw [show swapVal01 5 = 6 by native_decide]
      have hstep : count C₁ 5 = count D 5 + 1 :=
        count_replace_inc D t col5 5 (by rw [hcolD]; native_decide) (by native_decide)
      rw [hstep, hd5]
      omega
    have hpar35 : Odd (count C 3 + count C 5) := by
      have hwA' : Even (count C 1 + count C 3 + count C 5) := by
        rw [hammingDist_row0_row3_of_types1356 C htypes] at hA
        exact hA
      rw [h1] at hwA'
      exact odd_sum_of_even_one_add hwA'
    have h3or5 : 0 < count C 3 ∨ 0 < count C 5 := pos_of_odd_sum hpar35
    rcases h3or5 with h3 | h5
    · left
      constructor
      · have hd3 : count D 3 = count C 3 := by
          rw [count_swapRows01Code C h07 3]
          rw [show swapVal01 3 = 3 by native_decide]
        have hc3 : count C₁ 3 = count D 3 :=
          count_replace_eq D t col5 3 (by rw [hcolD]; native_decide) (by native_decide)
        rw [hc3, hd3]
        exact h3
      · exact hc5
    · right; right
      constructor
      · exact hc5
      · have hd6 : count D 6 = count C 5 := by
          rw [count_swapRows01Code C h07 6]
          rw [show swapVal01 6 = 5 by native_decide]
        have hc6 : count C₁ 6 = count D 6 :=
          count_replace_eq D t col5 6 (by rw [hcolD]; native_decide) (by native_decide)
        rw [hc6, hd6]
        exact h5
  · -- wB even: flip type 1 -> 3
    rcases exists_col1_of_count_pos C (by omega : 1 ≤ count C 1) with ⟨t, ht1⟩
    let C₁ : Code n := replaceColumn C t col3
    have hcol₁ : C₁ t = col3 := by simp [C₁, replaceColumn]
    have hsame : ∀ u : Fin n, u ≠ t → C₁ u = C u := by
      intro u hu; simp [C₁, replaceColumn, hu]
    have hbetter : UniversalBetter C₁ C := one_bit_flip_better C C₁ t ht1 hcol₁ hsame hB
    have hcv : colVal (C t) = 1 := by rw [ht1]; native_decide
    have htot₁ : totalCounts C₁ {1,3,5,6} = n := by
      rw [totalCounts_replace_eq C t col3 ({1,3,5,6} : Finset ℕ) (by simp [hcv]) (by native_decide)]
      exact h
    have hcnt₁ : count C₁ 1 = count C 1 - 1 :=
      count_replace_dec C t col3 1 (by rw [ht1]; native_decide) (by native_decide)
    refine ⟨C₁, hbetter, htot₁, hcnt₁, ?_⟩
    intro h1
    have hcnt₀ : count C₁ 1 = 0 := by omega
    apply isLinear_of_count1_zero_1356 C₁ htot₁ hcnt₀
    have hc3 : 0 < count C₁ 3 := by
      rw [count_replace_inc C t col3 3 (by rw [ht1]; native_decide) (by native_decide)]
      omega
    have hpar56 : Odd (count C 5 + count C 6) := by
      have hwB' : Even (count C 1 + count C 5 + count C 6) := by
        rw [hammingDist_row2_row3_of_types1356 C htypes] at hB
        exact hB
      rw [h1] at hwB'
      exact odd_sum_of_even_one_add hwB'
    have h5or6 : 0 < count C 5 ∨ 0 < count C 6 := pos_of_odd_sum hpar56
    rcases h5or6 with h5 | h6
    · left
      constructor
      · exact hc3
      · rw [count_replace_eq C t col3 5 (by rw [ht1]; native_decide) (by native_decide)]
        exact h5
    · right; left
      constructor
      · exact hc3
      · rw [count_replace_eq C t col3 6 (by rw [ht1]; native_decide) (by native_decide)]
        exact h6
  · -- wC even: flip type 1 -> 5
    rcases exists_col1_of_count_pos C (by omega : 1 ≤ count C 1) with ⟨t, ht1⟩
    let C₁ : Code n := replaceColumn C t col5
    have hcol₁ : C₁ t = col5 := by simp [C₁, replaceColumn]
    have hsame : ∀ u : Fin n, u ≠ t → C₁ u = C u := by
      intro u hu; simp [C₁, replaceColumn, hu]
    have hbetter : UniversalBetter C₁ C := one_bit_flip_1_to_5 C C₁ t ht1 hcol₁ hsame hC
    have hcv : colVal (C t) = 1 := by rw [ht1]; native_decide
    have htot₁ : totalCounts C₁ {1,3,5,6} = n := by
      rw [totalCounts_replace_eq C t col5 ({1,3,5,6} : Finset ℕ) (by simp [hcv]) (by native_decide)]
      exact h
    have hcnt₁ : count C₁ 1 = count C 1 - 1 :=
      count_replace_dec C t col5 1 (by rw [ht1]; native_decide) (by native_decide)
    refine ⟨C₁, hbetter, htot₁, hcnt₁, ?_⟩
    intro h1
    have hcnt₀ : count C₁ 1 = 0 := by omega
    apply isLinear_of_count1_zero_1356 C₁ htot₁ hcnt₀
    have hc5 : 0 < count C₁ 5 := by
      rw [count_replace_inc C t col5 5 (by rw [ht1]; native_decide) (by native_decide)]
      omega
    have hpar36 : Odd (count C 3 + count C 6) := by
      have hwC' : Even (count C 1 + count C 3 + count C 6) := by
        rw [hammingDist_row1_row3_of_types1356 C htypes] at hC
        exact hC
      rw [h1] at hwC'
      exact odd_sum_of_even_one_add hwC'
    have h3or6 : 0 < count C 3 ∨ 0 < count C 6 := pos_of_odd_sum hpar36
    rcases h3or6 with h3 | h6
    · left
      constructor
      · rw [count_replace_eq C t col5 3 (by rw [ht1]; native_decide) (by native_decide)]
        exact h3
      · exact hc5
    · right; right
      constructor
      · exact hc5
      · rw [count_replace_eq C t col5 6 (by rw [ht1]; native_decide) (by native_decide)]
        exact h6

/-- Corollary `cor:onepo` (Corollary 10): a non-Class-I code with columns only from types
1,3,5,6 and a positive type-1 count has a better linear or Class-I code with
strictly smaller |1|.  (`0 < count C 1` is the formalization's stand-in for the
paper's "nonlinear", which implies |1| > 0 for a valid (n,4) code; see
Notation.md §4.) -/
theorem descent_to_linear_or_class1 {n : ℕ} (C : Code n)
    (hnc1 : ¬ ClassI C) (h1pos : 0 < count C 1)
    (h : totalCounts C {1, 3, 5, 6} = n) :
    ∃ C' : Code n, (IsLinear C' ∨ ClassI C') ∧ UniversalBetter C' C ∧
      count C' 1 < count C 1 := by
  let P : ℕ → Prop := fun m => ∀ C₀ : Code n, totalCounts C₀ {1,3,5,6} = n →
      count C₀ 1 = m → 0 < m → ¬ ClassI C₀ →
      ∃ C' : Code n, (IsLinear C' ∨ ClassI C') ∧ UniversalBetter C' C₀ ∧ count C' 1 < count C₀ 1
  have hP : ∀ m : ℕ, P m := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro C₀ htot hmeas hpos hnc
      have hposC₀ : 0 < count C₀ 1 := by rw [hmeas]; exact hpos
      rcases onepo_step C₀ htot hnc hposC₀ with ⟨C₁, hb, ht₁, hm₁, hlin_of_one⟩
      by_cases hlin : IsLinear C₁
      · exact ⟨C₁, Or.inl hlin, hb, by omega⟩
      · by_cases hci : ClassI C₁
        · exact ⟨C₁, Or.inr hci, hb, by omega⟩
        · have hpos₁ : 0 < count C₁ 1 := by
            by_contra hnot
            have hzero : count C₁ 1 = 0 := by omega
            have hm1 : m = 1 := by omega
            have hc1 : count C₀ 1 = 1 := by rw [hmeas, hm1]
            exact hlin (hlin_of_one hc1)
          have hm₁lt : count C₁ 1 < m := by omega
          rcases ih (count C₁ 1) hm₁lt C₁ ht₁ rfl hpos₁ hci with ⟨C', hlc, hb', hlt⟩
          exact ⟨C', hlc, universalBetter_trans hb' hb, by omega⟩
  exact hP (count C 1) C h rfl h1pos hnc1

/-- Lemma `thm:class2` (Lemma 14) (2): a Class-III code is equal to some linear code with
|1| one smaller.  (Subclass a: replace (1,7) by (3,5) and use the equality of
`thm:odd` (Theorem 11).  Subclass b: replace 1 by 3 and use condition (ii) of `thm:even` (Theorem 8);
that special case of the Y3-empty characterization is still a stub.) -/
-- native_decide: Mechanical · n=any · checked 2026-08-28
theorem class3_to_linear {n : ℕ} (C : Code n) (h : ClassIII C) :
    ∃ C' : Code n, IsLinear C' ∧ UniversalEqual C' C ∧ count C' 1 = count C 1 - 1 := by
  rcases h with ⟨htot, hpar⟩
  rcases hpar with hIIIA | hIIIB
  · rcases hIIIA with ⟨h1eq, h7eq, h6eq, h3e, h5o⟩
    have h1ge : 1 ≤ count C 1 := by rw [h1eq]
    rcases exists_col1_of_count_pos C h1ge with ⟨t1, ht1⟩
    have h7ge : 1 ≤ count C 7 := by rw [h7eq]
    rcases exists_col7_of_count_pos C h7ge with ⟨t2, ht7⟩
    have htne : t1 ≠ t2 := by
      intro h
      have hv1 : colVal (C t1) = 1 := by rw [ht1]; native_decide
      have hv7 : colVal (C t2) = 7 := by rw [ht7]; native_decide
      rw [h] at hv1
      omega
    let C1 : Code n := replaceColumn C t1 col3
    let C' : Code n := replaceColumn C1 t2 col5
    have h3' : C' t1 = col3 := by
      simp [C', C1, replaceColumn, htne]
    have h5' : C' t2 = col5 := by
      simp [C', C1, replaceColumn]
    have hsame : ∀ u : Fin n, u ≠ t1 → u ≠ t2 → C' u = C u := by
      intro u hu1 hu2
      simp [C', C1, replaceColumn, hu1, hu2]
    have h07 : Columns07 C := Columns07_of_types_13567 C htot
    have h24 : count C 2 = 0 ∧ count C 4 = 0 := count_two_four_zero_of_13567 C htot
    have hflip := two_bit_flip C C' t1 t2 htne ht1 ht7 h3' h5' hsame h07
    have heq : UniversalEqual C' C :=
      (hflip.2.1).mpr ⟨h1eq, h7eq, h24.1, h24.2, h6eq, Or.inr h5o⟩
    have hlin : IsLinear C' := by
      constructor
      · intro t
        by_cases ht1' : t = t1
        · subst t
          simp [C', C1, replaceColumn, htne]
          have hv3 : colVal col3 = 3 := by native_decide
          rw [hv3]
          norm_num
        · by_cases ht2' : t = t2
          · subst t
            simp [C', C1, replaceColumn]
            have hv5 : colVal col5 = 5 := by native_decide
            rw [hv5]
            norm_num
          · have hcv : colVal (C t) = 1 ∨ colVal (C t) = 3 ∨ colVal (C t) = 5 ∨
                colVal (C t) = 6 ∨ colVal (C t) = 7 := by
              have hm := colVal_mem_of_totalCounts C ({1, 3, 5, 6, 7} : Finset ℕ) htot t
              simp [Finset.mem_insert, Finset.mem_singleton] at hm
              rcases hm with h1 | h3 | h5 | h6 | h7
              · exact Or.inl h1
              · exact Or.inr (Or.inl h3)
              · exact Or.inr (Or.inr (Or.inl h5))
              · exact Or.inr (Or.inr (Or.inr (Or.inl h6)))
              · exact Or.inr (Or.inr (Or.inr (Or.inr h7)))
            rcases hcv with h1 | h3 | h5 | h6 | h7
            · exfalso
              have hge2 : 2 ≤ count C 1 :=
                count_ge_two_of_two C 1 t1 t (Ne.symm ht1') (by rw [ht1]; native_decide) h1
              omega
            · simp [C', C1, replaceColumn, ht1', ht2']
              rw [h3]
              norm_num
            · simp [C', C1, replaceColumn, ht1', ht2']
              rw [h5]
              norm_num
            · simp [C', C1, replaceColumn, ht1', ht2']
              rw [h6]
              norm_num
            · exfalso
              have hge2 : 2 ≤ count C 7 :=
                count_ge_two_of_two C 7 t2 t (Ne.symm ht2') (by rw [ht7]; native_decide) h7
              omega
      · have hc3 : 0 < count C' 3 := by
          have hstep1 : count C' 3 = count C1 3 :=
            count_replace_eq C1 t2 col5 3
              (by
                intro h
                have hc : colVal (C1 t2) = 7 := by
                  have hC1 : C1 t2 = C t2 := by simp [C1, replaceColumn, htne.symm]
                  rw [hC1, ht7]
                  native_decide
                rw [hc] at h
                norm_num at h)
              (by native_decide)
          rw [hstep1]
          have hstep2 : count C1 3 = count C 3 + 1 :=
            count_replace_inc C t1 col3 3 (by rw [ht1]; native_decide) (by native_decide)
          rw [hstep2]
          omega
        have hc5 : 0 < count C' 5 := by
          have hstep1 : count C' 5 = count C1 5 + 1 :=
            count_replace_inc C1 t2 col5 5
              (by
                intro h
                have hc : colVal (C1 t2) = 7 := by
                  have hC1 : C1 t2 = C t2 := by simp [C1, replaceColumn, htne.symm]
                  rw [hC1, ht7]
                  native_decide
                rw [hc] at h
                norm_num at h)
              (by native_decide)
          rw [hstep1]
          have hstep2 : count C1 5 = count C 5 :=
            count_replace_eq C t1 col3 5 (by rw [ht1]; native_decide) (by native_decide)
          rw [hstep2]
          omega
        exact Or.inl ⟨hc3, hc5⟩
    have hcnt : count C' 1 = count C 1 - 1 := by
      have h1a : count C1 1 = count C 1 - 1 :=
        count_replace_dec C t1 col3 1 (by rw [ht1]; native_decide) (by native_decide)
      have h1b : count C' 1 = count C1 1 := by
        apply count_replace_eq C1 t2 col5 1
        · intro h
          have hc : colVal (C1 t2) = 7 := by
            have hC1 : C1 t2 = C t2 := by simp [C1, replaceColumn, htne.symm]
            rw [hC1, ht7]
            native_decide
          rw [hc] at h
          norm_num at h
        · native_decide
      rw [h1b, h1a]
    exact ⟨C', hlin, heq, hcnt⟩
  · -- Class-III-b: replace a type-1 column by type 3; equality by condition (ii)
    -- of `thm:even` (Theorem 8) (`Y3_empty_of_cond2`).
    rcases hIIIB with ⟨h1, h5, h7, h3o, h6o⟩
    have h1ge : 1 ≤ count C 1 := by rw [h1]
    rcases exists_col1_of_count_pos C h1ge with ⟨t1, ht1⟩
    let C' : Code n := replaceColumn C t1 col3
    have hcol' : C' t1 = col3 := by simp [C', replaceColumn]
    have hsame : ∀ u : Fin n, u ≠ t1 → C' u = C u := by
      intro u hu
      simp [C', replaceColumn, hu]
    have h07 : Columns07 C := Columns07_of_types_13567 C htot
    have h24 : count C 2 = 0 ∧ count C 4 = 0 := count_two_four_zero_of_13567 C htot
    have heven : Even (hammingDist (row2 C) (row3 C)) := by
      rw [hammingDist_row2_row3_eq C h07, h1, h24.1, h5]
      rcases h6o with ⟨k, hk⟩
      exact ⟨k + 1, by omega⟩
    have hflip := cumulative_no_y5 C C' t1 ht1 hcol' hsame
      (Y5_empty_of_even_w23 C t1 ht1 heven)
    have heq : UniversalEqual C' C :=
      (hflip.2).mpr (Y3_empty_of_cond2 C t1 ht1 h07 h1 h24.1 h24.2 h5 h7 h3o h6o)
    have hlin : IsLinear C' := by
      constructor
      · intro t
        by_cases ht : t = t1
        · subst t
          have hv3 : colVal col3 = 3 := by native_decide
          simp [C', replaceColumn, hv3]
        · have hcv : colVal (C t) = 3 ∨ colVal (C t) = 6 := by
            have hm := colVal_mem_of_totalCounts C ({1, 3, 5, 6, 7} : Finset ℕ) htot t
            simp [Finset.mem_insert, Finset.mem_singleton] at hm
            rcases hm with hv1 | hv3 | hv5 | hv6 | hv7
            · exfalso
              have hge : 2 ≤ count C 1 :=
                count_ge_two_of_two C 1 t1 t (Ne.symm ht) (by rw [ht1]; native_decide) hv1
              omega
            · exact Or.inl hv3
            · exfalso
              have hp := count_pos_of_colVal C t hv5
              omega
            · exact Or.inr hv6
            · exfalso
              have hp := count_pos_of_colVal C t hv7
              omega
          rcases hcv with hv3 | hv6
          · simp [C', replaceColumn, ht]
            rw [hv3]
            norm_num
          · simp [C', replaceColumn, ht]
            rw [hv6]
            norm_num
      · have hc3 : 0 < count C' 3 := by
          rw [count_replace_1_3_three C t1 ht1]
          rcases h3o with ⟨k, hk⟩
          omega
        have hc6 : 0 < count C' 6 := by
          rw [count_replace_1_3_other C t1 ht1 6 (by norm_num) (by norm_num)]
          rcases h6o with ⟨k, hk⟩
          omega
        exact Or.inr (Or.inl ⟨hc3, hc6⟩)
    have hcnt : count C' 1 = count C 1 - 1 := count_replace_1_3_one C t1 ht1
    exact ⟨C', hlin, heq, hcnt⟩

/-- Replacing a column of a Columns07 code by a column of type ≤ 7 keeps the
Columns07 property. -/
lemma columns07_replace_of_le7 {n : ℕ} (C : Code n) (h07 : Columns07 C) (t : Fin n)
    (s' : Column) (hs' : colVal s' ≤ 7) : Columns07 (replaceColumn C t s') := by
  intro u
  by_cases hu : u = t
  · subst u
    simp [replaceColumn]
    change colBit ⟨0, by decide⟩ s' = false
    rw [colBit_eq_testBit]
    exact testBit3_eq_false_of_le7 (colVal s') hs'
  · have h := h07 u
    simpa [replaceColumn, hu] using h

/-- A Columns07 code has a no-worse code with no type-0 columns (used for
`thm:two` (Theorem 1) normalization; iterates `zero_column`/`zero_column_strict`). -/
-- native_decide: Mechanical · n=any · checked 2026-08-28
lemma remove_type0 {n : ℕ} (C : Code n) (h07 : Columns07 C) :
    ∃ C' : Code n, UniversalBetter C' C ∧ Columns07 C' ∧ count C' 0 = 0 := by
  let P : ℕ → Prop := fun m => ∀ C₀ : Code n, Columns07 C₀ → count C₀ 0 = m →
      ∃ C' : Code n, UniversalBetter C' C₀ ∧ Columns07 C' ∧ count C' 0 = 0
  have hP : ∀ m : ℕ, P m := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro C₀ h07₀ hcnt₀
      by_cases hz : count C₀ 0 = 0
      · exact ⟨C₀, universalBetter_refl C₀, h07₀, hz⟩
      · have hpos : 0 < count C₀ 0 := by omega
        by_cases hC0 : ∃ C0 : Code n, Equivalent C₀ C0 ∧ C0form C0
        · rcases exists_col0_of_count_pos C₀ (by omega : 1 ≤ count C₀ 0) with ⟨t, ht⟩
          let C₁ : Code n := replaceColumn C₀ t col3
          have heq : UniversalEqual C₁ C₀ := zero_column C₀ t ht hC0 col3
          have hbetter : UniversalBetter C₁ C₀ := by
            intro ε hε0 hε1
            exact le_of_eq (heq ε hε0 hε1).symm
          have h07₁ : Columns07 C₁ := columns07_replace_of_le7 C₀ h07₀ t col3 (by native_decide)
          have hcnt₁ : count C₁ 0 = count C₀ 0 - 1 := by
            rw [count_replace_dec C₀ t col3 0 (by rw [ht]; native_decide) (by native_decide)]
          have hlt : count C₁ 0 < m := by omega
          rcases ih (count C₁ 0) hlt C₁ h07₁ rfl with ⟨C', hb, h07', hcnt'⟩
          exact ⟨C', universalBetter_trans hb hbetter, h07', hcnt'⟩
        · rcases zero_column_strict C₀ (by omega : count C₀ 0 ≥ 1) hC0 with
            ⟨t, ht, s', hs', hstrict⟩
          let C₁ : Code n := replaceColumn C₀ t s'
          have hbetter : UniversalBetter C₁ C₀ := by
            intro ε hε0 hε1
            exact le_of_lt (hstrict ε hε0 hε1)
          have hs'_le7 : colVal s' ≤ 7 := by
            rcases hs' with h3 | h5 | h6
            · rw [h3]; norm_num
            · rw [h5]; norm_num
            · rw [h6]; norm_num
          have h07₁ : Columns07 C₁ := columns07_replace_of_le7 C₀ h07₀ t s' hs'_le7
          have hcnt₁ : count C₁ 0 = count C₀ 0 - 1 := by
            rw [count_replace_dec C₀ t s' 0 (by rw [ht]; native_decide) (by
              rcases hs' with h3 | h5 | h6
              · rw [h3]; norm_num
              · rw [h5]; norm_num
              · rw [h6]; norm_num)]
          have hlt : count C₁ 0 < m := by omega
          rcases ih (count C₁ 0) hlt C₁ h07₁ rfl with ⟨C', hb, h07', hcnt'⟩
          exact ⟨C', universalBetter_trans hb hbetter, h07', hcnt'⟩
  exact hP (count C 0) C h07 rfl

def swap23 : Equiv (Fin 4) (Fin 4) := Equiv.swap (2 : Fin 4) (3 : Fin 4)
def swap13 : Equiv (Fin 4) (Fin 4) := Equiv.swap (1 : Fin 4) (3 : Fin 4)
def swap03 : Equiv (Fin 4) (Fin 4) := Equiv.swap (0 : Fin 4) (3 : Fin 4)

lemma count_rowPermutedCode_of_set {n : ℕ} (ρ : Equiv (Fin 4) (Fin 4)) (C : Code n)
    (S : Finset ℕ) (i j : ℕ)
    (hS : ∀ t : Fin n, colVal (C t) ∈ S)
    (hmap : ∀ v ∈ S, colVal (rowPermute ρ (colOfNat v)) = i ↔ v = j) :
    count (rowPermutedCode ρ C) i = count C j := by
  unfold count rowPermutedCode
  apply Finset.sum_congr rfl
  intro t _
  have hcv : colVal (C t) ∈ S := hS t
  rw [show rowPermute ρ (C t) = rowPermute ρ (colOfNat (colVal (C t))) by rw [colOfNat_colVal (C t)]]
  have hiff := hmap (colVal (C t)) hcv
  by_cases hcol : colVal (rowPermute ρ (colOfNat (colVal (C t)))) = i
  · have hj : colVal (C t) = j := hiff.mp hcol
    rw [if_pos hcol, if_pos hj]
  · have hj : ¬ colVal (C t) = j := fun hj => hcol (hiff.mpr hj)
    rw [if_neg hcol, if_neg hj]

-- native_decide: Mechanical · n=any · checked 2026-08-28
lemma hmaps_swap23_2_to_1 (v : ℕ) (hv : v ∈ ({1,2,3,4,5,6,7} : Finset ℕ)) :
    colVal (rowPermute swap23 (colOfNat v)) = 1 ↔ v = 2 := by
  simp [Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with h1 | h2 | h3 | h4 | h5 | h6 | h7 <;> subst v <;> native_decide

-- native_decide: Mechanical · n=any · checked 2026-08-28
lemma hmaps_swap23_7_to_7 (v : ℕ) (hv : v ∈ ({1,2,3,4,5,6,7} : Finset ℕ)) :
    colVal (rowPermute swap23 (colOfNat v)) = 7 ↔ v = 7 := by
  simp [Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with h1 | h2 | h3 | h4 | h5 | h6 | h7 <;> subst v <;> native_decide

-- native_decide: Mechanical · n=any · checked 2026-08-28
lemma hmaps_swap23_0_to_0 (v : ℕ) (hv : v ∈ ({1,2,3,4,5,6,7} : Finset ℕ)) :
    colVal (rowPermute swap23 (colOfNat v)) = 0 ↔ v = 0 := by
  simp [Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with h1 | h2 | h3 | h4 | h5 | h6 | h7 <;> subst v <;> native_decide

-- native_decide: Mechanical · n=any · checked 2026-08-28
lemma hmaps_swap13_4_to_1 (v : ℕ) (hv : v ∈ ({1,2,3,4,5,6,7} : Finset ℕ)) :
    colVal (rowPermute swap13 (colOfNat v)) = 1 ↔ v = 4 := by
  simp [Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with h1 | h2 | h3 | h4 | h5 | h6 | h7 <;> subst v <;> native_decide

-- native_decide: Mechanical · n=any · checked 2026-08-28
lemma hmaps_swap13_7_to_7 (v : ℕ) (hv : v ∈ ({1,2,3,4,5,6,7} : Finset ℕ)) :
    colVal (rowPermute swap13 (colOfNat v)) = 7 ↔ v = 7 := by
  simp [Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with h1 | h2 | h3 | h4 | h5 | h6 | h7 <;> subst v <;> native_decide

-- native_decide: Mechanical · n=any · checked 2026-08-28
lemma hmaps_swap13_0_to_0 (v : ℕ) (hv : v ∈ ({1,2,3,4,5,6,7} : Finset ℕ)) :
    colVal (rowPermute swap13 (colOfNat v)) = 0 ↔ v = 0 := by
  simp [Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with h1 | h2 | h3 | h4 | h5 | h6 | h7 <;> subst v <;> native_decide

lemma columns07_rowPermutedCode_of_fix0 {n : ℕ} (ρ : Equiv (Fin 4) (Fin 4)) (C : Code n)
    (h07 : Columns07 C) (hρ0 : ρ 0 = 0) : Columns07 (rowPermutedCode ρ C) := by
  intro t
  change (rowPermute ρ (C t)) 0 = false
  rw [show rowPermute ρ (C t) 0 = C t (ρ 0) by rfl, hρ0]
  exact h07 t

-- native_decide: Mechanical · n=any · checked 2026-08-28
lemma swap23_0 : swap23 0 = (0 : Fin 4) := by native_decide
-- native_decide: Mechanical · n=any · checked 2026-08-28
lemma swap13_0 : swap13 0 = (0 : Fin 4) := by native_decide

lemma colVal_mem_17_of_columns07_no0 {n : ℕ} (C : Code n) (h07 : Columns07 C)
    (h0 : count C 0 = 0) (t : Fin n) : colVal (C t) ∈ ({1,2,3,4,5,6,7} : Finset ℕ) := by
  have hle : colVal (C t) ≤ 7 := Columns07_le7 C h07 t
  have hne : colVal (C t) ≠ 0 := by
    intro h
    have hp : 1 ≤ count C 0 := count_pos_of_colVal C t h
    omega
  have hge : 1 ≤ colVal (C t) := by omega
  simp [Finset.mem_insert, Finset.mem_singleton]
  interval_cases colVal (C t) <;> omega

lemma totalCounts_16_of_columns07 {n : ℕ} (C : Code n) (h07 : Columns07 C)
    (h0 : count C 0 = 0) (h7 : count C 7 = 0) : totalCounts C {1,2,3,4,5,6} = n := by
  have hsum := Columns07_sum_counts C h07
  rw [sum_Icc0_7 (count C)] at hsum
  simp [totalCounts, Finset.sum_insert]
  omega

def flip357 {n : ℕ} (C : Code n) (t : Fin n) : Bool :=
  decide (colVal (C t) = 3 ∨ colVal (C t) = 5 ∨ colVal (C t) = 7)

def convert7to1Code {n : ℕ} (C : Code n) : Code n :=
  fun t => rowPermute swap03 (if flip357 C t then flipCol (C t) else C t)

lemma convert7to1Code_equiv {n : ℕ} (C : Code n) : Equivalent C (convert7to1Code C) := by
  refine ⟨swap03, Equiv.refl (Fin n), flip357 C, ?_⟩
  intro t
  rfl

-- native_decide: Mechanical · n=any · checked 2026-08-28
lemma colVal_convert7to1Code_mem {n : ℕ} (C : Code n) (t : Fin n)
    (hcol : colVal (C t) = 3 ∨ colVal (C t) = 5 ∨ colVal (C t) = 6 ∨ colVal (C t) = 7) :
    colVal (convert7to1Code C t) ∈ ({1,3,5,6} : Finset ℕ) := by
  rcases hcol with h3 | h5 | h6 | h7
  · have hc : C t = colOfNat 3 := by rw [← colOfNat_colVal (C t), h3]
    unfold convert7to1Code flip357
    rw [hc]; native_decide
  · have hc : C t = colOfNat 5 := by rw [← colOfNat_colVal (C t), h5]
    unfold convert7to1Code flip357
    rw [hc]; native_decide
  · have hc : C t = colOfNat 6 := by rw [← colOfNat_colVal (C t), h6]
    unfold convert7to1Code flip357
    rw [hc]; native_decide
  · have hc : C t = colOfNat 7 := by rw [← colOfNat_colVal (C t), h7]
    unfold convert7to1Code flip357
    rw [hc]; native_decide

lemma colVal_convert7to1Code_of_3567 {n : ℕ} (C : Code n) (h07 : Columns07 C)
    (h0 : count C 0 = 0) (h1 : count C 1 = 0) (h2 : count C 2 = 0) (h4 : count C 4 = 0)
    (t : Fin n) : colVal (convert7to1Code C t) ∈ ({1,3,5,6} : Finset ℕ) := by
  have hcv : colVal (C t) ∈ ({1,2,3,4,5,6,7} : Finset ℕ) := colVal_mem_17_of_columns07_no0 C h07 h0 t
  simp [Finset.mem_insert, Finset.mem_singleton] at hcv
  rcases hcv with hc1 | hc2 | hc3 | hc4 | hc5 | hc6 | hc7
  · exfalso; have hp : 1 ≤ count C 1 := count_pos_of_colVal C t hc1; omega
  · exfalso; have hp : 1 ≤ count C 2 := count_pos_of_colVal C t hc2; omega
  · exact colVal_convert7to1Code_mem C t (Or.inl hc3)
  · exfalso; have hp : 1 ≤ count C 4 := count_pos_of_colVal C t hc4; omega
  · exact colVal_convert7to1Code_mem C t (Or.inr (Or.inl hc5))
  · exact colVal_convert7to1Code_mem C t (Or.inr (Or.inr (Or.inl hc6)))
  · exact colVal_convert7to1Code_mem C t (Or.inr (Or.inr (Or.inr hc7)))

lemma totalCounts_16_of_mem1356 {n : ℕ} (C : Code n)
    (h : ∀ t : Fin n, colVal (C t) ∈ ({1,3,5,6} : Finset ℕ)) :
    totalCounts C {1,2,3,4,5,6} = n := by
  rw [totalCounts_eq_sum_indicator]
  trans ∑ u : Fin n, (1 : ℕ)
  · apply Finset.sum_congr rfl
    intro u _
    have hm := h u
    have h16 : colVal (C u) ∈ ({1,2,3,4,5,6} : Finset ℕ) := by
      simp [Finset.mem_insert, Finset.mem_singleton] at hm ⊢
      rcases hm with h1 | h3 | h5 | h6 <;> simp [*]
    simp [h16]
  · simp

-- native_decide: Mechanical · n=any · checked 2026-08-28
/-- One pair-replacement step in Case 2 of the proof of `thm:two` (Theorem 1):
when |1|>0 and |7|>0, replace a ⟨1⟩ column by type 3 and a ⟨7⟩ column by type 5,
which is never worse (`thm:odd` (Theorem 11), the 2-bit flip), and reduces |7| by one.

Paper §III-B, Proof of Theorem 1, p. 145, Case 2: "by Theorem 11, there exists a
code C₁' with λ_C₁' ≥ λ_C and ∑_{i=1}^6 |i|_{C₁'} = n obtained by replacing,
one-by-one, pairs of columns of types ⟨7⟩ and ⟨2^s⟩ (s = 0, 1, 2)".  This lemma
is the ⟨1⟩,⟨7⟩ instance (s = 0) of that one-by-one replacement; the ⟨2⟩,⟨7⟩ and
⟨4⟩,⟨7⟩ instances are reduced to it by row interchanges (`swap23` and `swap13`) in
`eliminate_type7`, matching the remark after `thm:odd` (Theorem 11).  The strict
decrease of |7| makes the descent in `eliminate_type7` terminate. -/
lemma pair17_step {n : ℕ} (C : Code n) (h07 : Columns07 C) (h1 : 0 < count C 1) (h7 : 0 < count C 7) :
    ∃ C' : Code n, UniversalBetter C' C ∧ Columns07 C' ∧ count C' 0 = count C 0 ∧
      count C' 7 = count C 7 - 1 := by
  rcases exists_col1_of_count_pos C (by omega : 1 ≤ count C 1) with ⟨t₁, ht₁⟩
  rcases exists_col7_of_count_pos C (by omega : 1 ≤ count C 7) with ⟨t₂, ht₂⟩
  have htne : t₁ ≠ t₂ := by
    intro h
    have hv1 : colVal (C t₂) = 1 := by rw [← h, ht₁]; native_decide
    have hv7 : colVal (C t₂) = 7 := by rw [ht₂]; native_decide
    omega
  let C1 : Code n := replaceColumn C t₁ col3
  let C' : Code n := replaceColumn C1 t₂ col5
  have h3 : C' t₁ = col3 := by simp [C', C1, replaceColumn, htne]
  have h5 : C' t₂ = col5 := by simp [C', C1, replaceColumn]
  have hsame : ∀ u : Fin n, u ≠ t₁ → u ≠ t₂ → C' u = C u := by
    intro u hu1 hu2
    simp [C', C1, replaceColumn, hu1, hu2]
  have hbetter : UniversalBetter C' C := (two_bit_flip C C' t₁ t₂ htne ht₁ ht₂ h3 h5 hsame h07).1
  have h07' : Columns07 C' := by
    have h1' : Columns07 C1 := columns07_replace_of_le7 C h07 t₁ col3 (by native_decide)
    exact columns07_replace_of_le7 C1 h1' t₂ col5 (by native_decide)
  have h0' : count C' 0 = count C 0 := by
    have h0c1 : count C1 0 = count C 0 := count_replace_eq C t₁ col3 0 (by rw [ht₁]; native_decide) (by native_decide)
    have h0c' : count C' 0 = count C1 0 := count_replace_eq C1 t₂ col5 0 (by
      have hC1 : C1 t₂ = C t₂ := by simp [C1, replaceColumn, htne.symm]
      rw [hC1, ht₂]; native_decide) (by native_decide)
    rw [h0c', h0c1]
  have h7' : count C' 7 = count C 7 - 1 := by
    have h7c1 : count C1 7 = count C 7 := count_replace_eq C t₁ col3 7 (by rw [ht₁]; native_decide) (by native_decide)
    have h7c' : count C' 7 = count C1 7 - 1 := count_replace_dec C1 t₂ col5 7 (by
      have hC1 : C1 t₂ = C t₂ := by simp [C1, replaceColumn, htne.symm]
      rw [hC1, ht₂]; native_decide) (by native_decide)
    rw [h7c', h7c1]
  exact ⟨C', hbetter, h07', h0', h7'⟩

lemma eliminate_type7 {n : ℕ} (C : Code n) (h07 : Columns07 C) (h0 : count C 0 = 0) :
    ∃ C' : Code n, UniversalBetter C' C ∧ totalCounts C' {1,2,3,4,5,6} = n := by
  let P : ℕ → Prop := fun m => ∀ C₀ : Code n, Columns07 C₀ → count C₀ 0 = 0 → count C₀ 7 = m →
      ∃ C' : Code n, UniversalBetter C' C₀ ∧ totalCounts C' {1,2,3,4,5,6} = n
  have hP : ∀ m : ℕ, P m := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro C₀ h07₀ h0₀ h7₀
      by_cases hz : count C₀ 7 = 0
      · refine ⟨C₀, universalBetter_refl C₀, ?_⟩
        exact totalCounts_16_of_columns07 C₀ h07₀ h0₀ hz
      · have h7pos : 0 < count C₀ 7 := by omega
        by_cases h1 : 0 < count C₀ 1
        · rcases pair17_step C₀ h07₀ h1 h7pos with ⟨C₁, hb, h07₁, h0₁, h7₁⟩
          have h0₁' : count C₁ 0 = 0 := by rw [h0₁, h0₀]
          have hlt : count C₁ 7 < m := by omega
          rcases ih (count C₁ 7) hlt C₁ h07₁ h0₁' rfl with ⟨C', hb', htot⟩
          exact ⟨C', universalBetter_trans hb' hb, htot⟩
        · have h1z : count C₀ 1 = 0 := by omega
          by_cases h2 : 0 < count C₀ 2
          · let D : Code n := rowPermutedCode swap23 C₀
            have hEqDC : UniversalEqual D C₀ := universalEqual_of_equivalent C₀ D (rowPermutedCode_equiv swap23 C₀)
            have hS : ∀ t : Fin n, colVal (C₀ t) ∈ ({1,2,3,4,5,6,7} : Finset ℕ) :=
              colVal_mem_17_of_columns07_no0 C₀ h07₀ h0₀
            have h07D : Columns07 D := columns07_rowPermutedCode_of_fix0 swap23 C₀ h07₀ swap23_0
            have hc0 : count D 0 = count C₀ 0 := count_rowPermutedCode_of_set swap23 C₀ {1,2,3,4,5,6,7} 0 0 hS (hmaps_swap23_0_to_0)
            have hc1 : count D 1 = count C₀ 2 := count_rowPermutedCode_of_set swap23 C₀ {1,2,3,4,5,6,7} 1 2 hS (hmaps_swap23_2_to_1)
            have hc7 : count D 7 = count C₀ 7 := count_rowPermutedCode_of_set swap23 C₀ {1,2,3,4,5,6,7} 7 7 hS (hmaps_swap23_7_to_7)
            have h0D : count D 0 = 0 := by rw [hc0, h0₀]
            have h1D : 0 < count D 1 := by rw [hc1]; exact h2
            have h7D : 0 < count D 7 := by rw [hc7]; exact h7pos
            rcases pair17_step D h07D h1D h7D with ⟨C₁, hb, h07₁, h0₁, h7₁⟩
            have hbC : UniversalBetter C₁ C₀ := universalBetter_of_equal_right C₁ D C₀ hb hEqDC
            have h0₁' : count C₁ 0 = 0 := by rw [h0₁, h0D]
            have hlt : count C₁ 7 < m := by omega
            rcases ih (count C₁ 7) hlt C₁ h07₁ h0₁' rfl with ⟨C', hb', htot⟩
            exact ⟨C', universalBetter_trans hb' hbC, htot⟩
          · by_cases h4 : 0 < count C₀ 4
            · let D : Code n := rowPermutedCode swap13 C₀
              have hEqDC : UniversalEqual D C₀ := universalEqual_of_equivalent C₀ D (rowPermutedCode_equiv swap13 C₀)
              have hS : ∀ t : Fin n, colVal (C₀ t) ∈ ({1,2,3,4,5,6,7} : Finset ℕ) :=
                colVal_mem_17_of_columns07_no0 C₀ h07₀ h0₀
              have h07D : Columns07 D := columns07_rowPermutedCode_of_fix0 swap13 C₀ h07₀ swap13_0
              have hc0 : count D 0 = count C₀ 0 := count_rowPermutedCode_of_set swap13 C₀ {1,2,3,4,5,6,7} 0 0 hS (hmaps_swap13_0_to_0)
              have hc1 : count D 1 = count C₀ 4 := count_rowPermutedCode_of_set swap13 C₀ {1,2,3,4,5,6,7} 1 4 hS (hmaps_swap13_4_to_1)
              have hc7 : count D 7 = count C₀ 7 := count_rowPermutedCode_of_set swap13 C₀ {1,2,3,4,5,6,7} 7 7 hS (hmaps_swap13_7_to_7)
              have h0D : count D 0 = 0 := by rw [hc0, h0₀]
              have h1D : 0 < count D 1 := by rw [hc1]; exact h4
              have h7D : 0 < count D 7 := by rw [hc7]; exact h7pos
              rcases pair17_step D h07D h1D h7D with ⟨C₁, hb, h07₁, h0₁, h7₁⟩
              have hbC : UniversalBetter C₁ C₀ := universalBetter_of_equal_right C₁ D C₀ hb hEqDC
              have h0₁' : count C₁ 0 = 0 := by rw [h0₁, h0D]
              have hlt : count C₁ 7 < m := by omega
              rcases ih (count C₁ 7) hlt C₁ h07₁ h0₁' rfl with ⟨C', hb', htot⟩
              exact ⟨C', universalBetter_trans hb' hbC, htot⟩
            · have h2z : count C₀ 2 = 0 := by omega
              have h4z : count C₀ 4 = 0 := by omega
              let D : Code n := convert7to1Code C₀
              have hEqDC : UniversalEqual D C₀ := universalEqual_of_equivalent C₀ D (convert7to1Code_equiv C₀)
              have htotD : totalCounts D {1,2,3,4,5,6} = n := by
                apply totalCounts_16_of_mem1356 D
                intro t
                exact colVal_convert7to1Code_of_3567 C₀ h07₀ h0₀ h1z h2z h4z t
              refine ⟨D, ?_, htotD⟩
              intro ε hε0 hε1
              exact le_of_eq (hEqDC ε hε0 hε1).symm
  exact hP (count C 7) C h07 h0 rfl

lemma dCode_le_row {n : ℕ} (C : Code n) (j : Fin 4) (y : Word n) :
    dCode C y ≤ hammingDist (row C j) y := by
  unfold dCode
  fin_cases j
  · exact Nat.min_le_left _ _
  · exact (Nat.min_le_right _ _).trans (Nat.min_le_left _ _)
  · exact (Nat.min_le_right _ _).trans ((Nat.min_le_right _ _).trans (Nat.min_le_left _ _))
  · exact (Nat.min_le_right _ _).trans ((Nat.min_le_right _ _).trans (Nat.min_le_right _ _))

lemma le_min4 {x a b c d : ℕ} (h0 : x ≤ a) (h1 : x ≤ b) (h2 : x ≤ c) (h3 : x ≤ d) :
    x ≤ min a (min b (min c d)) := by
  exact le_min h0 (le_min h1 (le_min h2 h3))

lemma dCode_le_of_rows_subset {n : ℕ} (C C' : Code n) (y : Word n)
    (h : ∀ j : Fin 4, ∃ j' : Fin 4, row C j = row C' j') :
    dCode C' y ≤ dCode C y := by
  unfold dCode
  rcases h 0 with ⟨j0', hj0⟩
  rcases h 1 with ⟨j1', hj1⟩
  rcases h 2 with ⟨j2', hj2⟩
  rcases h 3 with ⟨j3', hj3⟩
  have hle0 : dCode C' y ≤ hammingDist (row C 0) y := by rw [hj0]; exact dCode_le_row C' j0' y
  have hle1 : dCode C' y ≤ hammingDist (row C 1) y := by rw [hj1]; exact dCode_le_row C' j1' y
  have hle2 : dCode C' y ≤ hammingDist (row C 2) y := by rw [hj2]; exact dCode_le_row C' j2' y
  have hle3 : dCode C' y ≤ hammingDist (row C 3) y := by rw [hj3]; exact dCode_le_row C' j3' y
  exact le_min4 hle0 hle1 hle2 hle3

lemma universalBetter_of_rows_subset {n : ℕ} (C C' : Code n)
    (h : ∀ j : Fin 4, ∃ j' : Fin 4, row C j = row C' j') :
    UniversalBetter C' C := by
  intro ε hε0 hε1
  have hwle : ∀ y : Word n, weight n ε (dCode C y) ≤ weight n ε (dCode C' y) := by
    intro y
    have hle : dCode C' y ≤ dCode C y := dCode_le_of_rows_subset C C' y h
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact le_of_lt (weight_strictAnti hε0 hε1 hlt)
    · rw [heq]
  have hsum : (∑ y : Word n, weight n ε (dCode C y)) ≤ ∑ y : Word n, weight n ε (dCode C' y) :=
    Finset.sum_le_sum (fun y _ => hwle y)
  have hmul := mul_le_mul_of_nonneg_left hsum (by norm_num : 0 ≤ (1 / 4 : ℝ))
  unfold lambda
  change (1 / 4 : ℝ) * (∑ y : Word n, weight n ε (dCode C' y)) ≥
    (1 / 4 : ℝ) * (∑ y : Word n, weight n ε (dCode C y))
  nlinarith [hmul]

-- native_decide: Mechanical · n=any · checked 2026-08-28
lemma rows_subset_replace_col3_col5 {n : ℕ} (C : Code n) (t : Fin n) (hall : ∀ u, C u = col3) :
    ∀ j : Fin 4, ∃ j' : Fin 4, row C j = row (replaceColumn C t col5) j' := by
  intro j
  fin_cases j
  · refine ⟨0, ?_⟩; funext u; by_cases hu : u = t <;> simp [row, replaceColumn, hu, hall]; native_decide
  · refine ⟨0, ?_⟩; funext u; by_cases hu : u = t <;> simp [row, replaceColumn, hu, hall] <;> native_decide
  · refine ⟨3, ?_⟩; funext u; by_cases hu : u = t <;> simp [row, replaceColumn, hu, hall] <;> native_decide
  · refine ⟨3, ?_⟩; funext u; by_cases hu : u = t <;> simp [row, replaceColumn, hu, hall]; native_decide

-- native_decide: Mechanical · n=any · checked 2026-08-28
lemma rows_subset_replace_col5_col3 {n : ℕ} (C : Code n) (t : Fin n) (hall : ∀ u, C u = col5) :
    ∀ j : Fin 4, ∃ j' : Fin 4, row C j = row (replaceColumn C t col3) j' := by
  intro j
  fin_cases j
  · refine ⟨0, ?_⟩; funext u; by_cases hu : u = t <;> simp [row, replaceColumn, hu, hall]; native_decide
  · refine ⟨3, ?_⟩; funext u; by_cases hu : u = t <;> simp [row, replaceColumn, hu, hall] <;> native_decide
  · refine ⟨0, ?_⟩; funext u; by_cases hu : u = t <;> simp [row, replaceColumn, hu, hall] <;> native_decide
  · refine ⟨3, ?_⟩; funext u; by_cases hu : u = t <;> simp [row, replaceColumn, hu, hall]; native_decide

-- native_decide: Mechanical · n=any · checked 2026-08-28
lemma rows_subset_replace_col6_col3 {n : ℕ} (C : Code n) (t : Fin n) (hall : ∀ u, C u = col6) :
    ∀ j : Fin 4, ∃ j' : Fin 4, row C j = row (replaceColumn C t col3) j' := by
  intro j
  fin_cases j
  · refine ⟨0, ?_⟩; funext u; by_cases hu : u = t <;> simp [row, replaceColumn, hu, hall]; native_decide
  · refine ⟨2, ?_⟩; funext u; by_cases hu : u = t <;> simp [row, replaceColumn, hu, hall] <;> native_decide
  · refine ⟨2, ?_⟩; funext u; by_cases hu : u = t <;> simp [row, replaceColumn, hu, hall]; native_decide
  · refine ⟨0, ?_⟩; funext u; by_cases hu : u = t <;> simp [row, replaceColumn, hu, hall] <;> native_decide


lemma counts_not_two_pos_of_not_linear {n : ℕ} (C : Code n)
    (htypes : ∀ t : Fin n, colVal (C t) = 3 ∨ colVal (C t) = 5 ∨ colVal (C t) = 6)
    (hnlin : ¬ IsLinear C) :
    ¬ ((count C 3 > 0 ∧ count C 5 > 0) ∨ (count C 3 > 0 ∧ count C 6 > 0) ∨
      (count C 5 > 0 ∧ count C 6 > 0)) := by
  intro h2
  apply hnlin
  constructor
  · intro t
    rcases htypes t with hv3 | hv5 | hv6
    · right; left; exact hv3
    · right; right; left; exact hv5
    · right; right; right; exact hv6
  · exact h2

-- native_decide: Mechanical · n=any · checked 2026-08-28
/-- The degenerate corner case of the proof of `thm:two` (Theorem 1): a
nonlinear, non-Class-I code with |1|+|3|+|5|+|6| = n and |1| = 0 has all
columns of a single type in {3,5,6}; replacing one column by another type in
{3,5,6} yields a linear code that is universally better (rows-subset argument
via `universalBetter_of_rows_subset` and the `rows_subset_replace_*` lemmas).

Paper §III-B, Proof of Theorem 1, p. 145, Case 1.  There the |1| > 0 case is
handled by `cor:onepo` (Corollary 10), whose proof starts "Since C is
nonlinear, we have |1| > 0"; the |1| = 0 case cannot occur for a genuine
(n,4) code, as a single positive type among {3,5,6} collapses the four rows to
fewer than four distinct codewords.  Since `Code n` does not enforce distinct
rows, this degenerate case is handled explicitly here. -/
lemma degenerate_to_linear {n : ℕ} (C : Code n) (hn : 2 ≤ n) (h : totalCounts C {1,3,5,6} = n)
    (h1 : count C 1 = 0) (hnlin : ¬ IsLinear C) :
    ∃ C' : Code n, IsLinear C' ∧ UniversalBetter C' C := by
  have htypes : ∀ t : Fin n, colVal (C t) = 3 ∨ colVal (C t) = 5 ∨ colVal (C t) = 6 := by
    intro t
    have hm := colVal_mem_of_totalCounts C ({1,3,5,6} : Finset ℕ) h t
    simp [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with hv1 | hv3 | hv5 | hv6
    · exfalso; have hp : 1 ≤ count C 1 := count_pos_of_colVal C t hv1; omega
    · left; exact hv3
    · right; left; exact hv5
    · right; right; exact hv6
  have hnot2 := counts_not_two_pos_of_not_linear C htypes hnlin
  have hsum : count C 3 + count C 5 + count C 6 = n := by
    simp [totalCounts, Finset.sum_insert] at h
    omega
  by_cases h3pos : 0 < count C 3
  · have h5z : count C 5 = 0 := by
      by_contra hnot; have h5pos : 0 < count C 5 := by omega
      exact hnot2 (Or.inl ⟨h3pos, h5pos⟩)
    have h6z : count C 6 = 0 := by
      by_contra hnot; have h6pos : 0 < count C 6 := by omega
      exact hnot2 (Or.inr (Or.inl ⟨h3pos, h6pos⟩))
    have h3_eq : count C 3 = n := by omega
    have hall3 : ∀ u, C u = col3 := by
      intro u
      rcases htypes u with hv3 | hv5 | hv6
      · exact (colVal_eq_three_iff_col3 (C u)).1 hv3
      · exfalso; have hp : 1 ≤ count C 5 := count_pos_of_colVal C u hv5; omega
      · exfalso; have hp : 1 ≤ count C 6 := count_pos_of_colVal C u hv6; omega
    rcases exists_col_of_colVal C 3 (by omega : 1 ≤ count C 3) with ⟨t, ht3⟩
    let C' : Code n := replaceColumn C t col5
    have hrows := rows_subset_replace_col3_col5 C t hall3
    have hbetter : UniversalBetter C' C := universalBetter_of_rows_subset C C' hrows
    have hlin : IsLinear C' := by
      constructor
      · intro u
        by_cases hu : u = t
        · subst u; simp [C', replaceColumn]; native_decide
        · have hc : C u = col3 := hall3 u
          simp [C', replaceColumn, hu, hc]; native_decide
      · have hc3 : 0 < count C' 3 := by
          rw [count_replace_dec C t col5 3 (by rw [hall3 t]; native_decide) (by native_decide)]
          omega
        have hc5 : 0 < count C' 5 := by
          rw [count_replace_inc C t col5 5 (by rw [hall3 t]; native_decide) (by native_decide)]
          omega
        exact Or.inl ⟨hc3, hc5⟩
    exact ⟨C', hlin, hbetter⟩
  · by_cases h5pos : 0 < count C 5
    · have h3z : count C 3 = 0 := by omega
      have h6z : count C 6 = 0 := by
        by_contra hnot; have h6pos : 0 < count C 6 := by omega
        exact hnot2 (Or.inr (Or.inr ⟨h5pos, h6pos⟩))
      have h5_eq : count C 5 = n := by omega
      have hall5 : ∀ u, C u = col5 := by
        intro u
        rcases htypes u with hv3 | hv5 | hv6
        · exfalso; have hp : 1 ≤ count C 3 := count_pos_of_colVal C u hv3; omega
        · exact (colVal_eq_five_iff_col5 (C u)).1 hv5
        · exfalso; have hp : 1 ≤ count C 6 := count_pos_of_colVal C u hv6; omega
      rcases exists_col_of_colVal C 5 (by omega : 1 ≤ count C 5) with ⟨t, ht5⟩
      let C' : Code n := replaceColumn C t col3
      have hrows := rows_subset_replace_col5_col3 C t hall5
      have hbetter : UniversalBetter C' C := universalBetter_of_rows_subset C C' hrows
      have hlin : IsLinear C' := by
        constructor
        · intro u
          by_cases hu : u = t
          · subst u; simp [C', replaceColumn]; native_decide
          · have hc : C u = col5 := hall5 u
            simp [C', replaceColumn, hu, hc]; native_decide
        · have hc5 : 0 < count C' 5 := by
            rw [count_replace_dec C t col3 5 (by rw [hall5 t]; native_decide) (by native_decide)]
            omega
          have hc3 : 0 < count C' 3 := by
            rw [count_replace_inc C t col3 3 (by rw [hall5 t]; native_decide) (by native_decide)]
            omega
          exact Or.inl ⟨hc3, hc5⟩
      exact ⟨C', hlin, hbetter⟩
    · have h3z : count C 3 = 0 := by omega
      have h5z : count C 5 = 0 := by omega
      have h6pos : 0 < count C 6 := by omega
      have h6_eq : count C 6 = n := by omega
      have hall6 : ∀ u, C u = col6 := by
        intro u
        rcases htypes u with hv3 | hv5 | hv6
        · exfalso; have hp : 1 ≤ count C 3 := count_pos_of_colVal C u hv3; omega
        · exfalso; have hp : 1 ≤ count C 5 := count_pos_of_colVal C u hv5; omega
        · exact (colVal_eq_six_iff_col6 (C u)).1 hv6
      rcases exists_col_of_colVal C 6 (by omega : 1 ≤ count C 6) with ⟨t, ht6⟩
      let C' : Code n := replaceColumn C t col3
      have hrows := rows_subset_replace_col6_col3 C t hall6
      have hbetter : UniversalBetter C' C := universalBetter_of_rows_subset C C' hrows
      have hlin : IsLinear C' := by
        constructor
        · intro u
          by_cases hu : u = t
          · subst u; simp [C', replaceColumn]; native_decide
          · have hc : C u = col6 := hall6 u
            simp [C', replaceColumn, hu, hc]; native_decide
        · have hc6 : 0 < count C' 6 := by
            rw [count_replace_dec C t col3 6 (by rw [hall6 t]; native_decide) (by native_decide)]
            omega
          have hc3 : 0 < count C' 3 := by
            rw [count_replace_inc C t col3 3 (by rw [hall6 t]; native_decide) (by native_decide)]
            omega
          exact Or.inr (Or.inl ⟨hc3, hc6⟩)
      exact ⟨C', hlin, hbetter⟩

/-- Every code is no worse than a linear or Class-I code (the core reduction of
`thm:two` (Theorem 1); `2 ≤ n` matches the paper's standing blocklength assumption). -/
lemma reduce_to_linear_or_class1 {n : ℕ} (hn : 2 ≤ n) (C : Code n) :
    ∃ C' : Code n, (IsLinear C' ∨ ClassI C') ∧ UniversalBetter C' C := by
  rcases even_pair C with ⟨i, j, hij, heven⟩
  let C1 : Code n := normalizeCode C i j
  have hEq1 : UniversalEqual C1 C := universalEqual_of_equivalent C C1 (Equivalent_normalize C i j)
  have h07 : Columns07 C1 := Columns07_normalize C i j hij
  rcases remove_type0 C1 h07 with ⟨C2, hb2, h07_2, h0_2⟩
  have hb2C : UniversalBetter C2 C := universalBetter_of_equal_right C2 C1 C hb2 hEq1
  rcases eliminate_type7 C2 h07_2 h0_2 with ⟨C3, hb3, htot3⟩
  have hb3C : UniversalBetter C3 C := universalBetter_trans hb3 hb2C
  rcases only_types_13456 C3 htot3 with ⟨C4, hb4, htot4⟩
  have hb4C : UniversalBetter C4 C := universalBetter_trans hb4 hb3C
  by_cases hlin : IsLinear C4
  · exact ⟨C4, Or.inl hlin, hb4C⟩
  · by_cases hci : ClassI C4
    · exact ⟨C4, Or.inr hci, hb4C⟩
    · by_cases h1pos : 0 < count C4 1
      · rcases descent_to_linear_or_class1 C4 hci h1pos htot4 with ⟨C5, hlc, hb5, hlt⟩
        exact ⟨C5, hlc, universalBetter_trans hb5 hb4C⟩
      · have h1z : count C4 1 = 0 := by omega
        rcases degenerate_to_linear C4 hn htot4 h1z hlin with ⟨C5, hlin5, hb5⟩
        exact ⟨C5, Or.inl hlin5, universalBetter_trans hb5 hb4C⟩

/-- Flip every column whose type exceeds 7, so an 1..14-code becomes 1..7. -/
def flipHighColumns {n : ℕ} (C : Code n) : Code n :=
  fun t => if decide (7 < colVal (C t)) then flipCol (C t) else C t

lemma flipHighColumns_equiv {n : ℕ} (C : Code n) : Equivalent C (flipHighColumns C) := by
  refine ⟨Equiv.refl (Fin 4), Equiv.refl (Fin n), fun t => decide (7 < colVal (C t)), ?_⟩
  intro t
  rfl

lemma flipHighColumns_mem17 {n : ℕ} (C : Code n)
    (hcols : ∀ t : Fin n, 1 ≤ colVal (C t) ∧ colVal (C t) ≤ 14) (t : Fin n) :
    colVal (flipHighColumns C t) ∈ ({1,2,3,4,5,6,7} : Finset ℕ) := by
  have hc := hcols t
  by_cases h7 : 7 < colVal (C t)
  · have hcv : colVal (flipHighColumns C t) = 15 - colVal (C t) := by
      unfold flipHighColumns
      simp [h7, colVal_flipCol]
    rw [hcv]
    have hle : colVal (C t) ≤ 14 := hc.2
    have hge : 8 ≤ colVal (C t) := by omega
    simp [Finset.mem_insert, Finset.mem_singleton]
    omega
  · have hcv : colVal (flipHighColumns C t) = colVal (C t) := by
      unfold flipHighColumns
      simp [h7]
    rw [hcv]
    have hge : 1 ≤ colVal (C t) := hc.1
    have hle : colVal (C t) ≤ 7 := by omega
    simp [Finset.mem_insert, Finset.mem_singleton]
    omega

/-- A code that is no worse than and not equal to another is strictly better at
some crossover probability. -/
lemma exists_strict_better_of_not_equal {n : ℕ} {D C : Code n}
    (hge : UniversalBetter D C) (hne : ¬ UniversalEqual D C) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 / 2 ∧ lambda D ε > lambda C ε := by
  have hne' : ∃ ε : ℝ, 0 < ε ∧ ε < 1 / 2 ∧ lambda D ε ≠ lambda C ε := by
    by_contra h
    apply hne
    intro ε hε0 hε1
    by_contra hneq
    exact h ⟨ε, hε0, hε1, hneq⟩
  rcases hne' with ⟨ε, hε0, hε1, hneε⟩
  refine ⟨ε, hε0, hε1, ?_⟩
  exact lt_of_le_of_ne (hge ε hε0 hε1) hneε.symm

lemma hammingDist_pos_of_ne {n : ℕ} {x y : Word n} (h : x ≠ y) : 1 ≤ hammingDist x y := by
  have hne : hammingDist x y ≠ 0 := fun h0 => h ((hammingDist_eq_zero_iff x y).mp h0)
  omega

lemma dCode_lt_of_new_row {n : ℕ} (C C' : Code n) (j' : Fin 4)
    (hnew : ∀ j : Fin 4, row C j ≠ row C' j') :
    dCode C' (row C' j') < dCode C (row C' j') := by
  have h0 : dCode C' (row C' j') = 0 := by
    have hle := dCode_le_row C' j' (row C' j')
    rw [hammingDist_self] at hle
    omega
  have h1 : 1 ≤ dCode C (row C' j') := by
    unfold dCode
    apply le_min4
    · exact hammingDist_pos_of_ne (hnew 0)
    · exact hammingDist_pos_of_ne (hnew 1)
    · exact hammingDist_pos_of_ne (hnew 2)
    · exact hammingDist_pos_of_ne (hnew 3)
  omega

lemma universalStrictBetter_of_rows_subset {n : ℕ} (C C' : Code n)
    (hsup : ∀ j : Fin 4, ∃ j' : Fin 4, row C j = row C' j')
    (hnew : ∃ j' : Fin 4, ∀ j : Fin 4, row C j ≠ row C' j') :
    UniversalStrictBetter C' C := by
  intro ε hε0 hε1
  rcases hnew with ⟨j', hne⟩
  have hwle : ∀ y : Word n, weight n ε (dCode C y) ≤ weight n ε (dCode C' y) := by
    intro y
    have hle : dCode C' y ≤ dCode C y := dCode_le_of_rows_subset C C' y hsup
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact le_of_lt (weight_strictAnti hε0 hε1 hlt)
    · rw [heq]
  have hwlt : weight n ε (dCode C (row C' j')) < weight n ε (dCode C' (row C' j')) := by
    exact weight_strictAnti hε0 hε1 (dCode_lt_of_new_row C C' j' hne)
  have hsumlt : (∑ y : Word n, weight n ε (dCode C y)) < ∑ y : Word n, weight n ε (dCode C' y) := by
    refine Finset.sum_lt_sum (fun y _ => hwle y) ?_
    exact ⟨row C' j', Finset.mem_univ (row C' j'), hwlt⟩
  unfold lambda
  change (1 / 4 : ℝ) * (∑ y : Word n, weight n ε (dCode C' y)) >
    (1 / 4 : ℝ) * (∑ y : Word n, weight n ε (dCode C y))
  have hquarter : 0 < (1 / 4 : ℝ) := by norm_num
  nlinarith [mul_lt_mul_of_pos_left hsumlt hquarter]

lemma exists_ne_fin {n : ℕ} (hn : 2 ≤ n) (t : Fin n) : ∃ u : Fin n, u ≠ t := by
  have h0n : 0 < n := by omega
  have h1n : 1 < n := by omega
  by_cases ht : t = ⟨0, h0n⟩
  · refine ⟨⟨1, h1n⟩, ?_⟩
    intro h
    have hv : (⟨1, h1n⟩ : Fin n) = ⟨0, h0n⟩ := by rw [h, ht]
    have hval := congrArg Fin.val hv
    norm_num at hval
  · exact ⟨⟨0, h0n⟩, fun h => ht h.symm⟩

lemma new_row_replace_col3_col5 {n : ℕ} (C : Code n) (t : Fin n) (hn : 2 ≤ n)
    (hall : ∀ u, C u = col3) :
    ∀ j : Fin 4, row C j ≠ row (replaceColumn C t col5) 1 := by
  intro j
  fin_cases j
  · intro h
    have hcon := congrFun h t
    change colBit 0 (C t) = colBit 1 (replaceColumn C t col5 t) at hcon
    rw [hall t] at hcon
    simp [replaceColumn, colBit, col3, col5] at hcon
  · intro h
    have hcon := congrFun h t
    change colBit 1 (C t) = colBit 1 (replaceColumn C t col5 t) at hcon
    rw [hall t] at hcon
    simp [replaceColumn, colBit, col3, col5] at hcon
  · rcases exists_ne_fin hn t with ⟨u, hut⟩
    intro h
    have hcon := congrFun h u
    change colBit 2 (C u) = colBit 1 (replaceColumn C t col5 u) at hcon
    rw [hall u] at hcon
    have hcu : replaceColumn C t col5 u = C u := by simp [replaceColumn, hut]
    rw [hcu, hall u] at hcon
    simp [colBit, col3] at hcon
  · rcases exists_ne_fin hn t with ⟨u, hut⟩
    intro h
    have hcon := congrFun h u
    change colBit 3 (C u) = colBit 1 (replaceColumn C t col5 u) at hcon
    rw [hall u] at hcon
    have hcu : replaceColumn C t col5 u = C u := by simp [replaceColumn, hut]
    rw [hcu, hall u] at hcon
    simp [colBit, col3] at hcon

lemma new_row_replace_col5_col3 {n : ℕ} (C : Code n) (t : Fin n) (hn : 2 ≤ n)
    (hall : ∀ u, C u = col5) :
    ∀ j : Fin 4, row C j ≠ row (replaceColumn C t col3) 2 := by
  intro j
  fin_cases j
  · intro h
    have hcon := congrFun h t
    change colBit 0 (C t) = colBit 2 (replaceColumn C t col3 t) at hcon
    rw [hall t] at hcon
    simp [replaceColumn, colBit, col3, col5] at hcon
  · rcases exists_ne_fin hn t with ⟨u, hut⟩
    intro h
    have hcon := congrFun h u
    change colBit 1 (C u) = colBit 2 (replaceColumn C t col3 u) at hcon
    rw [hall u] at hcon
    have hcu : replaceColumn C t col3 u = C u := by simp [replaceColumn, hut]
    rw [hcu, hall u] at hcon
    simp [colBit, col5] at hcon
  · intro h
    have hcon := congrFun h t
    change colBit 2 (C t) = colBit 2 (replaceColumn C t col3 t) at hcon
    rw [hall t] at hcon
    simp [replaceColumn, colBit, col3, col5] at hcon
  · rcases exists_ne_fin hn t with ⟨u, hut⟩
    intro h
    have hcon := congrFun h u
    change colBit 3 (C u) = colBit 2 (replaceColumn C t col3 u) at hcon
    rw [hall u] at hcon
    have hcu : replaceColumn C t col3 u = C u := by simp [replaceColumn, hut]
    rw [hcu, hall u] at hcon
    simp [colBit, col5] at hcon

lemma new_row_replace_col6_col3 {n : ℕ} (C : Code n) (t : Fin n) (hn : 2 ≤ n)
    (hall : ∀ u, C u = col6) :
    ∀ j : Fin 4, row C j ≠ row (replaceColumn C t col3) 3 := by
  intro j
  fin_cases j
  · intro h
    have hcon := congrFun h t
    change colBit 0 (C t) = colBit 3 (replaceColumn C t col3 t) at hcon
    rw [hall t] at hcon
    simp [replaceColumn, colBit, col3, col6] at hcon
  · rcases exists_ne_fin hn t with ⟨u, hut⟩
    intro h
    have hcon := congrFun h u
    change colBit 1 (C u) = colBit 3 (replaceColumn C t col3 u) at hcon
    rw [hall u] at hcon
    have hcu : replaceColumn C t col3 u = C u := by simp [replaceColumn, hut]
    rw [hcu, hall u] at hcon
    simp [colBit, col6] at hcon
  · rcases exists_ne_fin hn t with ⟨u, hut⟩
    intro h
    have hcon := congrFun h u
    change colBit 2 (C u) = colBit 3 (replaceColumn C t col3 u) at hcon
    rw [hall u] at hcon
    have hcu : replaceColumn C t col3 u = C u := by simp [replaceColumn, hut]
    rw [hcu, hall u] at hcon
    simp [colBit, col6] at hcon
  · intro h
    have hcon := congrFun h t
    change colBit 3 (C t) = colBit 3 (replaceColumn C t col3 t) at hcon
    rw [hall t] at hcon
    simp [replaceColumn, colBit, col3, col6] at hcon

-- native_decide: Mechanical · n=any · checked 2026-08-28
lemma degenerate_to_linear_strict {n : ℕ} (C : Code n) (hn : 2 ≤ n) (h : totalCounts C {1,3,5,6} = n)
    (h1 : count C 1 = 0) (hnlin : ¬ IsLinear C) :
    ∃ C' : Code n, IsLinear C' ∧ UniversalStrictBetter C' C := by
  have htypes : ∀ t : Fin n, colVal (C t) = 3 ∨ colVal (C t) = 5 ∨ colVal (C t) = 6 := by
    intro t
    have hm := colVal_mem_of_totalCounts C ({1,3,5,6} : Finset ℕ) h t
    simp [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with hv1 | hv3 | hv5 | hv6
    · exfalso; have hp : 1 ≤ count C 1 := count_pos_of_colVal C t hv1; omega
    · left; exact hv3
    · right; left; exact hv5
    · right; right; exact hv6
  have hnot2 := counts_not_two_pos_of_not_linear C htypes hnlin
  have hsum : count C 3 + count C 5 + count C 6 = n := by
    simp [totalCounts, Finset.sum_insert] at h
    omega
  by_cases h3pos : 0 < count C 3
  · have h5z : count C 5 = 0 := by
      by_contra hnot; have h5pos : 0 < count C 5 := by omega
      exact hnot2 (Or.inl ⟨h3pos, h5pos⟩)
    have h6z : count C 6 = 0 := by
      by_contra hnot; have h6pos : 0 < count C 6 := by omega
      exact hnot2 (Or.inr (Or.inl ⟨h3pos, h6pos⟩))
    have h3_eq : count C 3 = n := by omega
    have hall3 : ∀ u, C u = col3 := by
      intro u
      rcases htypes u with hv3 | hv5 | hv6
      · exact (colVal_eq_three_iff_col3 (C u)).1 hv3
      · exfalso; have hp : 1 ≤ count C 5 := count_pos_of_colVal C u hv5; omega
      · exfalso; have hp : 1 ≤ count C 6 := count_pos_of_colVal C u hv6; omega
    rcases exists_col_of_colVal C 3 (by omega : 1 ≤ count C 3) with ⟨t, ht3⟩
    let C' : Code n := replaceColumn C t col5
    have hrows := rows_subset_replace_col3_col5 C t hall3
    have hnew : ∃ j' : Fin 4, ∀ j : Fin 4, row C j ≠ row C' j' := ⟨1, new_row_replace_col3_col5 C t hn hall3⟩
    have hstrict : UniversalStrictBetter C' C := universalStrictBetter_of_rows_subset C C' hrows hnew
    have hlin : IsLinear C' := by
      constructor
      · intro u
        by_cases hu : u = t
        · subst u; simp [C', replaceColumn]; native_decide
        · have hc : C u = col3 := hall3 u
          simp [C', replaceColumn, hu, hc]; native_decide
      · have hc3 : 0 < count C' 3 := by
          rw [count_replace_dec C t col5 3 (by rw [hall3 t]; native_decide) (by native_decide)]
          rw [h3_eq]
          omega
        have hc5 : 0 < count C' 5 := by
          rw [count_replace_inc C t col5 5 (by rw [hall3 t]; native_decide) (by native_decide)]
          omega
        exact Or.inl ⟨hc3, hc5⟩
    exact ⟨C', hlin, hstrict⟩
  · by_cases h5pos : 0 < count C 5
    · have h3z : count C 3 = 0 := by omega
      have h6z : count C 6 = 0 := by
        by_contra hnot; have h6pos : 0 < count C 6 := by omega
        exact hnot2 (Or.inr (Or.inr ⟨h5pos, h6pos⟩))
      have h5_eq : count C 5 = n := by omega
      have hall5 : ∀ u, C u = col5 := by
        intro u
        rcases htypes u with hv3 | hv5 | hv6
        · exfalso; have hp : 1 ≤ count C 3 := count_pos_of_colVal C u hv3; omega
        · exact (colVal_eq_five_iff_col5 (C u)).1 hv5
        · exfalso; have hp : 1 ≤ count C 6 := count_pos_of_colVal C u hv6; omega
      rcases exists_col_of_colVal C 5 (by omega : 1 ≤ count C 5) with ⟨t, ht5⟩
      let C' : Code n := replaceColumn C t col3
      have hrows := rows_subset_replace_col5_col3 C t hall5
      have hnew : ∃ j' : Fin 4, ∀ j : Fin 4, row C j ≠ row C' j' := ⟨2, new_row_replace_col5_col3 C t hn hall5⟩
      have hstrict : UniversalStrictBetter C' C := universalStrictBetter_of_rows_subset C C' hrows hnew
      have hlin : IsLinear C' := by
        constructor
        · intro u
          by_cases hu : u = t
          · subst u; simp [C', replaceColumn]; native_decide
          · have hc : C u = col5 := hall5 u
            simp [C', replaceColumn, hu, hc]; native_decide
        · have hc5 : 0 < count C' 5 := by
            rw [count_replace_dec C t col3 5 (by rw [hall5 t]; native_decide) (by native_decide)]
            rw [h5_eq]
            omega
          have hc3 : 0 < count C' 3 := by
            rw [count_replace_inc C t col3 3 (by rw [hall5 t]; native_decide) (by native_decide)]
            omega
          exact Or.inl ⟨hc3, hc5⟩
      exact ⟨C', hlin, hstrict⟩
    · have h3z : count C 3 = 0 := by omega
      have h5z : count C 5 = 0 := by omega
      have h6pos : 0 < count C 6 := by omega
      have h6_eq : count C 6 = n := by omega
      have hall6 : ∀ u, C u = col6 := by
        intro u
        rcases htypes u with hv3 | hv5 | hv6
        · exfalso; have hp : 1 ≤ count C 3 := count_pos_of_colVal C u hv3; omega
        · exfalso; have hp : 1 ≤ count C 5 := count_pos_of_colVal C u hv5; omega
        · exact (colVal_eq_six_iff_col6 (C u)).1 hv6
      rcases exists_col_of_colVal C 6 (by omega : 1 ≤ count C 6) with ⟨t, ht6⟩
      let C' : Code n := replaceColumn C t col3
      have hrows := rows_subset_replace_col6_col3 C t hall6
      have hnew : ∃ j' : Fin 4, ∀ j : Fin 4, row C j ≠ row C' j' := ⟨3, new_row_replace_col6_col3 C t hn hall6⟩
      have hstrict : UniversalStrictBetter C' C := universalStrictBetter_of_rows_subset C C' hrows hnew
      have hlin : IsLinear C' := by
        constructor
        · intro u
          by_cases hu : u = t
          · subst u; simp [C', replaceColumn]; native_decide
          · have hc : C u = col6 := hall6 u
            simp [C', replaceColumn, hu, hc]; native_decide
        · have hc6 : 0 < count C' 6 := by
            rw [count_replace_dec C t col3 6 (by rw [hall6 t]; native_decide) (by native_decide)]
            rw [h6_eq]
            omega
          have hc3 : 0 < count C' 3 := by
            rw [count_replace_inc C t col3 3 (by rw [hall6 t]; native_decide) (by native_decide)]
            omega
          exact Or.inr (Or.inl ⟨hc3, hc6⟩)
      exact ⟨C', hlin, hstrict⟩

lemma class2_parity_of_weights (c1 c3 c5 c6 : ℕ)
    (hw03 : Odd (c3 + c6)) (hw13 : Odd (c3 + c5)) (hw24 : Even (c1 + c5 + c6)) :
    Even c1 ∧ ((Even c3 ∧ Odd c5 ∧ Odd c6) ∨ (Odd c3 ∧ Even c5 ∧ Even c6)) := by
  rcases hw03 with ⟨a, ha⟩
  rcases hw13 with ⟨b, hb⟩
  rcases hw24 with ⟨d, hd⟩
  by_cases h3 : Even c3
  · obtain ⟨e, he⟩ := h3
    have hc6o : Odd c6 := ⟨a - e, by omega⟩
    have hc5o : Odd c5 := ⟨b - e, by omega⟩
    have hc1e : Even c1 := ⟨d - (a - e) - (b - e) - 1, by omega⟩
    exact ⟨hc1e, Or.inl ⟨⟨e, he⟩, hc5o, hc6o⟩⟩
  · have h3o : Odd c3 := Nat.not_even_iff_odd.mp h3
    obtain ⟨e, he⟩ := h3o
    have hc6e : Even c6 := ⟨a - e, by omega⟩
    have hc5e : Even c5 := ⟨b - e, by omega⟩
    have hc1e : Even c1 := ⟨d - (a - e) - (b - e), by omega⟩
    exact ⟨hc1e, Or.inr ⟨⟨e, he⟩, hc5e, hc6e⟩⟩

/-- A {1,3,5,6}-code has no type-2, type-4, or type-7 columns. -/
lemma count_247_zero_of_1356 {n : ℕ} (C : Code n) (h : totalCounts C {1,3,5,6} = n) :
    count C 2 = 0 ∧ count C 4 = 0 ∧ count C 7 = 0 := by
  constructor
  · rw [count_eq_card, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro t ht
    have hcv : colVal (C t) = 2 := (Finset.mem_filter.mp ht).2
    have hm := colVal_mem_of_totalCounts C ({1,3,5,6} : Finset ℕ) h t
    simp [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with hv1 | hv3 | hv5 | hv6
    · rw [hv1] at hcv; norm_num at hcv
    · rw [hv3] at hcv; norm_num at hcv
    · rw [hv5] at hcv; norm_num at hcv
    · rw [hv6] at hcv; norm_num at hcv
  constructor
  · rw [count_eq_card, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro t ht
    have hcv : colVal (C t) = 4 := (Finset.mem_filter.mp ht).2
    have hm := colVal_mem_of_totalCounts C ({1,3,5,6} : Finset ℕ) h t
    simp [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with hv1 | hv3 | hv5 | hv6
    · rw [hv1] at hcv; norm_num at hcv
    · rw [hv3] at hcv; norm_num at hcv
    · rw [hv5] at hcv; norm_num at hcv
    · rw [hv6] at hcv; norm_num at hcv
  · rw [count_eq_card, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro t ht
    have hcv : colVal (C t) = 7 := (Finset.mem_filter.mp ht).2
    have hm := colVal_mem_of_totalCounts C ({1,3,5,6} : Finset ℕ) h t
    simp [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with hv1 | hv3 | hv5 | hv6
    · rw [hv1] at hcv; norm_num at hcv
    · rw [hv3] at hcv; norm_num at hcv
    · rw [hv5] at hcv; norm_num at hcv
    · rw [hv6] at hcv; norm_num at hcv

/-- `lm:all` (Lemma 15) Case-1 (i): odd w(c₁⊕c₃) and w(c₂⊕c₃) with even w(c₃⊕c₄) force
Class-II (paper §III-D, Proof of Lemma 15, p. 148: "[i)] w(c₁⊕c₃) and
w(c₂⊕c₃) are odd.  Otherwise, C is Class-II"). -/
lemma class2_of_w24_even_odd_w03_w13 {n : ℕ} (C : Code n)
    (htot : totalCounts C {1,3,5,6} = n) (h1pos : 0 < count C 1)
    (h03 : Odd (hammingDist (row0 C) (row2 C)))
    (h13 : Odd (hammingDist (row1 C) (row2 C)))
    (h24 : Even (hammingDist (row2 C) (row3 C))) :
    ClassII C := by
  have htypes := types_1356_of_totalCounts C htot
  rw [hammingDist_row0_row2_of_types1356 C htypes] at h03
  rw [hammingDist_row1_row2_of_types1356 C htypes] at h13
  rw [hammingDist_row2_row3_of_types1356 C htypes] at h24
  have hpar := class2_parity_of_weights (count C 1) (count C 3) (count C 5) (count C 6) h03 h13 h24
  constructor
  · exact h1pos
  · constructor
    · exact htot
    · rcases hpar.2 with h2a | h2b
      · exact Or.inl ⟨hpar.1, h2a.1, h2a.2.1, h2a.2.2⟩
      · exact Or.inr ⟨hpar.1, h2b.1, h2b.2.1, h2b.2.2⟩

/-- `lm:all` (Lemma 15) Case-1 (ii): |1|=1, |5|=0, odd |3|,|6| force Class-III-b (paper
§III-D, Proof of Lemma 15, p. 148: "[ii)] |1|=1, |5|=0, |3| and |6| are odd.
Otherwise, C is Class-II-b"). -/
lemma class3_of_cond2 {n : ℕ} (C : Code n)
    (htot : totalCounts C {1,3,5,6} = n)
    (h1 : count C 1 = 1) (h5 : count C 5 = 0)
    (h3o : Odd (count C 3)) (h6o : Odd (count C 6)) :
    ClassIII C := by
  have h247 := count_247_zero_of_1356 C htot
  constructor
  · simp [totalCounts, Finset.sum_insert] at htot ⊢
    omega
  · right
    exact ⟨h1, h5, h247.2.2, h3o, h6o⟩

-- native_decide: Mechanical · n=any · checked 2026-08-28
lemma swapVal01_1 : swapVal01 1 = 1 := by native_decide
-- native_decide: Mechanical · n=any · checked 2026-08-28
lemma swapVal01_3 : swapVal01 3 = 3 := by native_decide
-- native_decide: Mechanical · n=any · checked 2026-08-28
lemma swapVal01_5 : swapVal01 5 = 6 := by native_decide
-- native_decide: Mechanical · n=any · checked 2026-08-28
lemma swapVal01_6 : swapVal01 6 = 5 := by native_decide
-- native_decide: Mechanical · n=any · checked 2026-08-28
lemma swapVal01_7 : swapVal01 7 = 4 := by native_decide

/-- `lm:all` (Lemma 15) Case-1 (iii): |1|=1, |6|=0, odd |3|,|5| makes the code equivalent
to a Class-III-b code (via `swapRows01Code`; paper §III-D, Proof of Lemma 15,
p. 148: "[iii)] |1|=1, |6|=0, |3| and |5| are odd.  Otherwise, C is equivalent
to Class-II-b"). -/
lemma class3_of_cond3 {n : ℕ} (C : Code n) (h07 : Columns07 C)
    (htot : totalCounts C {1,3,5,6} = n)
    (h1 : count C 1 = 1) (h6 : count C 6 = 0)
    (h3o : Odd (count C 3)) (h5o : Odd (count C 5)) :
    ∃ C' : Code n, Equivalent C C' ∧ ClassIII C' := by
  let C' : Code n := swapRows01Code C
  have hEq : Equivalent C C' := swapRows01Code_equiv C
  refine ⟨C', hEq, ?_⟩
  have h247 := count_247_zero_of_1356 C htot  -- count 2=4=7=0
  have htot' : totalCounts C' {1,3,5,6} = n := totalCounts_swapRows01Code_1356 C h07 htot
  have hc1 : count C' 1 = 1 := by
    rw [count_swapRows01Code C h07 1, swapVal01_1]
    exact h1
  have hc5 : count C' 5 = 0 := by
    rw [count_swapRows01Code C h07 5, swapVal01_5]
    exact h6
  have hc7 : count C' 7 = 0 := by
    rw [count_swapRows01Code C h07 7, swapVal01_7]
    exact h247.2.1
  have hc3o : Odd (count C' 3) := by
    rw [count_swapRows01Code C h07 3, swapVal01_3]
    exact h3o
  have hc6o : Odd (count C' 6) := by
    rw [count_swapRows01Code C h07 6, swapVal01_6]
    exact h5o
  constructor
  · -- totalCounts C' {1,3,5,6,7} = n
    simp [totalCounts, Finset.sum_insert] at htot' ⊢
    omega
  · right
    exact ⟨hc1, hc5, hc7, hc3o, hc6o⟩

/-! ## `lm:all` (Lemma 15) proof infrastructure

The n ≥ 2 proof of `lm:all` (Lemma 15) (paper §3.4) mirrors the n = 3 case of
`thm:n8` (Theorem 5) but concludes with a class instead of `InOptimal3`.  It needs:
general-n row-swap reductions keeping columns in {1..7} (rho23/rho13/rho15
fix row 0), the Fig. fig:iwla flip-2,3,6 + rho02 transformation (with the
|7| = 0 caveat: type 7 maps to 13 under rho02), and the `thm:even` (Theorem 8)/`thm:odd` (Theorem 11)
strictness analyses with the class conditions (i)/(ii)/(iii).
-/

/-- Columns with colVal ≤ 7 have row-1 bit 0 (the `Columns07` condition). -/
lemma columns07_of_colVal_le7 {n : ℕ} (C : Code n)
    (hcols : ∀ t : Fin n, colVal (C t) ≤ 7) : Columns07 C := by
  intro t
  by_cases ht : (C t) (0 : Fin 4) = true
  · have hterm : 8 ≤ if (C t) (0 : Fin 4) then 2 ^ (3 - (0 : Fin 4).val) else 0 := by
      simp [ht]
    have hge : 8 ≤ colVal (C t) := by
      unfold colVal
      have hsingle : (if (C t) (0 : Fin 4) then 2 ^ (3 - (0 : Fin 4).val) else 0) ≤
          ∑ j : Fin 4, if (C t) j then 2 ^ (3 - j.val) else 0 := by
        have hnonneg : ∀ j : Fin 4, j ∈ Finset.univ →
            0 ≤ if (C t) j then 2 ^ (3 - j.val) else 0 := by
          intro j _
          by_cases hj : (C t) j <;> simp [hj]
        exact Finset.single_le_sum hnonneg (Finset.mem_univ (0 : Fin 4))
      exact le_trans hterm hsingle
    have hle := hcols t
    omega
  · cases h : (C t) (0 : Fin 4)
    · rfl
    · exfalso; exact ht h

/-- A row permutation fixing row 0 keeps the columns of a {1..7}-code in
{1..7}: bit 0 stays false (value ≤ 7) and the column stays nonzero. -/
-- native_decide: Mechanical · n=any · checked 2026-08-28
lemma rowPermute_fix0_cols17 {n : ℕ} (C : Code n) (ρ : Equiv (Fin 4) (Fin 4))
    (hρ : ρ (0 : Fin 4) = 0)
    (hcols : ∀ t : Fin n, 1 ≤ colVal (C t) ∧ colVal (C t) ≤ 7) :
    ∀ t : Fin n, 1 ≤ colVal (rowPermute ρ (C t)) ∧ colVal (rowPermute ρ (C t)) ≤ 7 := by
  intro t
  rcases hcols t with ⟨hge, hle⟩
  have h07 : Columns07 C := columns07_of_colVal_le7 C (fun u => (hcols u).2)
  have h07' : Columns07 (rowPermutedCode ρ C) := by
    intro u
    unfold rowPermutedCode rowPermute
    rw [hρ]
    exact h07 u
  have hle7 : colVal (rowPermute ρ (C t)) ≤ 7 := Columns07_le7 (rowPermutedCode ρ C) h07' t
  have hne0 : C t ≠ col0 := by
    intro heq
    have hcv : colVal (C t) = 0 := by rw [heq]; native_decide
    omega
  have hge1 : 1 ≤ colVal (rowPermute ρ (C t)) := by
    by_contra hlt
    have hz : colVal (rowPermute ρ (C t)) = 0 := by omega
    have hrow0 : rowPermute ρ (C t) = col0 := (colVal_eq_zero_iff_col0 (rowPermute ρ (C t))).mp hz
    apply hne0
    ext i
    rcases ρ.surjective i with ⟨j, hj⟩
    have hrowj : (rowPermute ρ (C t)) j = false := by
      rw [hrow0]
      rfl
    simpa [rowPermute, col0, hj] using hrowj
  exact ⟨hge1, hle7⟩

/-- The row swap (0,2) (used after flipping types 2,3,6 in `lm:all` (Lemma 15) Case-2). -/
def rho02 : Equiv (Fin 4) (Fin 4) := Equiv.swap (0 : Fin 4) (2 : Fin 4)

/-- Flip exactly the columns of types 2, 3, and 6 (equivalence-preserving). -/
def flip236 {n : ℕ} (C : Code n) : Code n :=
  fun t => if colVal (C t) = 2 ∨ colVal (C t) = 3 ∨ colVal (C t) = 6 then flipCol (C t) else C t

/-- `flip236` is an equivalence (column flips are part of the equivalence
relation). -/
lemma flip236_equiv {n : ℕ} (C : Code n) : Equivalent C (flip236 C) := by
  refine ⟨Equiv.refl (Fin 4), Equiv.refl (Fin n),
    fun t => colVal (C t) = 2 ∨ colVal (C t) = 3 ∨ colVal (C t) = 6, ?_⟩
  intro t
  simp [flip236]
  rfl

/-- A row permutation that fixes type 7 preserves the count of type-7
columns. -/
-- native_decide: Mechanical · n=any · checked 2026-08-28
lemma count_fix7_rowPermute {n : ℕ} (ρ : Equiv (Fin 4) (Fin 4))
    (hρ : rowPermute ρ (colOfNat 7) = colOfNat 7) (C : Code n) :
    count (rowPermutedCode ρ C) 7 = count C 7 := by
  have hfix : ∀ c : Column, colVal (rowPermute ρ c) = 7 ↔ colVal c = 7 := by
    intro c
    constructor
    · intro h
      have hrp : rowPermute ρ c = colOfNat 7 := by
        rw [← colOfNat_colVal (rowPermute ρ c), h]
      have hback : c = rowPermute ρ.symm (colOfNat 7) := by
        have h1 := congrArg (fun x => rowPermute ρ.symm x) hrp
        simpa [rowPermute_left_inv] using h1
      have hcv : colVal c = colVal (rowPermute ρ.symm (colOfNat 7)) := by rw [hback]
      rw [hcv]
      have hrp7 : rowPermute ρ.symm (colOfNat 7) = colOfNat 7 := by
        have h1 := congrArg (fun x => rowPermute ρ.symm x) hρ
        simpa [rowPermute_left_inv] using h1.symm
      rw [hrp7]
      native_decide
    · intro h
      have hrp : c = colOfNat 7 := by rw [← colOfNat_colVal c, h]
      rw [hrp, hρ]
      native_decide
  unfold count
  apply Finset.sum_congr rfl
  intro t _
  simp [rowPermutedCode, hfix (C t)]

/-- Optimality transports across equivalent codes (general n). -/
lemma opt_of_equiv {n : ℕ} {C Ct : Code n} (hopt : ∀ D : Code n, UniversalBetter C D)
    (hEq : Equivalent C Ct) : ∀ D : Code n, UniversalBetter Ct D := by
  intro D ε hε0 hε1
  have hl : lambda C ε = lambda Ct ε := (lambda_equiv C Ct hEq ε).symm
  exact le_trans (hopt D ε hε0 hε1) (le_of_eq hl)

/-- "No strictly better code" transports across equivalent codes. -/
lemma noStrict_of_equiv {n : ℕ} {C Ct : Code n}
    (hnoStrict : ∀ D : Code n, UniversalStrictBetter D C → False)
    (hEq : Equivalent C Ct) : ∀ D : Code n, UniversalStrictBetter D Ct → False := by
  intro D hD
  apply hnoStrict D
  intro ε hε0 hε1
  have hl : lambda Ct ε = lambda C ε := lambda_equiv C Ct hEq ε
  rw [← hl]
  exact hD ε hε0 hε1

/-- Lift a `∃`-result for an equivalent code back to the original code. -/
lemma lm_lift_equiv {n : ℕ} {C Ct : Code n} (hEq : Equivalent C Ct)
    (hres : ∃ C'' : Code n, Equivalent Ct C'' ∧ (IsLinear C'' ∨ ClassI C'' ∨ ClassII C'' ∨ ClassIII C'')) :
    ∃ C' : Code n, Equivalent C C' ∧ (IsLinear C' ∨ ClassI C' ∨ ClassII C' ∨ ClassIII C') := by
  rcases hres with ⟨C'', hEqCt, hIn⟩
  exact ⟨C'', equivalent_trans hEq hEqCt, hIn⟩

-- native_decide: Mechanical · n=any · checked 2026-08-28
/-- w(c₁⊕c₃) = |3|+|7| for a code with only types 1,3,5,7. -/
lemma hammingDist_row0_row2_of_types1357 {n : ℕ} (C : Code n)
    (h : ∀ t : Fin n, colVal (C t) = 1 ∨ colVal (C t) = 3 ∨ colVal (C t) = 5 ∨ colVal (C t) = 7) :
    hammingDist (row0 C) (row2 C) = count C 3 + count C 7 := by
  have hS : ∀ t : Fin n, colVal (C t) ∈ ({1, 3, 5, 7} : Finset ℕ) := by
    intro t
    rcases h t with h1 | h3 | h5 | h7
    · simp [h1]
    · simp [h3]
    · simp [h5]
    · simp [h7]
  unfold row0 row2
  rw [hammingDist_rows_of_types C ⟨0, by decide⟩ ⟨2, by decide⟩ ({1, 3, 5, 7} : Finset ℕ) hS]
  have h1a : (1 : ℕ).testBit 3 = false := by native_decide
  have h1b : (1 : ℕ).testBit 1 = false := by native_decide
  have h3a : (3 : ℕ).testBit 3 = false := by native_decide
  have h3b : (3 : ℕ).testBit 1 = true := by native_decide
  have h5a : (5 : ℕ).testBit 3 = false := by native_decide
  have h5b : (5 : ℕ).testBit 1 = false := by native_decide
  have h7a : (7 : ℕ).testBit 3 = false := by native_decide
  have h7b : (7 : ℕ).testBit 1 = true := by native_decide
  simp [Finset.sum_insert, h1a, h1b, h3a, h3b, h5a, h5b, h7a, h7b]

-- native_decide: Mechanical · n=any · checked 2026-08-28
/-- w(c₂⊕c₃) = |3|+|5| for a code with only types 1,3,5,7. -/
lemma hammingDist_row1_row2_of_types1357 {n : ℕ} (C : Code n)
    (h : ∀ t : Fin n, colVal (C t) = 1 ∨ colVal (C t) = 3 ∨ colVal (C t) = 5 ∨ colVal (C t) = 7) :
    hammingDist (row1 C) (row2 C) = count C 3 + count C 5 := by
  have hS : ∀ t : Fin n, colVal (C t) ∈ ({1, 3, 5, 7} : Finset ℕ) := by
    intro t
    rcases h t with h1 | h3 | h5 | h7
    · simp [h1]
    · simp [h3]
    · simp [h5]
    · simp [h7]
  unfold row1 row2
  rw [hammingDist_rows_of_types C ⟨1, by decide⟩ ⟨2, by decide⟩ ({1, 3, 5, 7} : Finset ℕ) hS]
  have h1a : (1 : ℕ).testBit 2 = false := by native_decide
  have h1b : (1 : ℕ).testBit 1 = false := by native_decide
  have h3a : (3 : ℕ).testBit 2 = false := by native_decide
  have h3b : (3 : ℕ).testBit 1 = true := by native_decide
  have h5a : (5 : ℕ).testBit 2 = true := by native_decide
  have h5b : (5 : ℕ).testBit 1 = false := by native_decide
  have h7a : (7 : ℕ).testBit 2 = true := by native_decide
  have h7b : (7 : ℕ).testBit 1 = true := by native_decide
  simp [Finset.sum_insert, h1a, h1b, h3a, h3b, h5a, h5b, h7a, h7b]

-- native_decide: Mechanical · n=any · checked 2026-08-28
/-- w(c₃⊕c₄) = |1|+|5| for a code with only types 1,3,5,7. -/
lemma hammingDist_row2_row3_of_types1357 {n : ℕ} (C : Code n)
    (h : ∀ t : Fin n, colVal (C t) = 1 ∨ colVal (C t) = 3 ∨ colVal (C t) = 5 ∨ colVal (C t) = 7) :
    hammingDist (row2 C) (row3 C) = count C 1 + count C 5 := by
  have hS : ∀ t : Fin n, colVal (C t) ∈ ({1, 3, 5, 7} : Finset ℕ) := by
    intro t
    rcases h t with h1 | h3 | h5 | h7
    · simp [h1]
    · simp [h3]
    · simp [h5]
    · simp [h7]
  unfold row2 row3
  rw [hammingDist_rows_of_types C ⟨2, by decide⟩ ⟨3, by decide⟩ ({1, 3, 5, 7} : Finset ℕ) hS]
  have h1a : (1 : ℕ).testBit 1 = false := by native_decide
  have h1b : (1 : ℕ).testBit 0 = true := by native_decide
  have h3a : (3 : ℕ).testBit 1 = true := by native_decide
  have h3b : (3 : ℕ).testBit 0 = true := by native_decide
  have h5a : (5 : ℕ).testBit 1 = false := by native_decide
  have h5b : (5 : ℕ).testBit 0 = true := by native_decide
  have h7a : (7 : ℕ).testBit 1 = true := by native_decide
  have h7b : (7 : ℕ).testBit 0 = true := by native_decide
  simp [Finset.sum_insert, h1a, h3a, h5a, h7a]

/-! ## `lm:all` (Lemma 15) Case-1/Case-2 column-type helpers and reductions -/

/-- The row swap (2,3) (maps type 2 to 1 and fixes type 7). -/
def rho23 : Equiv (Fin 4) (Fin 4) := Equiv.swap (2 : Fin 4) (3 : Fin 4)

/-- The row swap (0,3) (maps type 7 to 14, which flips to 1). -/
def rho03 : Equiv (Fin 4) (Fin 4) := Equiv.swap (0 : Fin 4) (3 : Fin 4)

/-- The n columns of a {1..7}-code sum to n over types 1..7. -/
lemma lm_columns17_total (C : Code n)
    (hcols : ∀ t : Fin n, 1 ≤ colVal (C t) ∧ colVal (C t) ≤ 7) :
    totalCounts C ({1, 2, 3, 4, 5, 6, 7} : Finset ℕ) = n := by
  unfold totalCounts count
  rw [Finset.sum_comm]
  calc
    (∑ t : Fin n, ∑ i ∈ ({1, 2, 3, 4, 5, 6, 7} : Finset ℕ), if colVal (C t) = i then 1 else 0)
        = ∑ t : Fin n, (1 : ℕ) := by
          apply Finset.sum_congr rfl
          intro u _
          rcases hcols u with ⟨hge, hle⟩
          interval_cases colVal (C u) <;> simp
    _ = n := by simp

/-- With |1|=|4|=|7|=0, the columns of a {1..7}-code have types in {2,3,5,6}. -/
lemma lm_types_236 (C : Code n)
    (hcols : ∀ t : Fin n, 1 ≤ colVal (C t) ∧ colVal (C t) ≤ 7)
    (h1 : count C 1 = 0) (h4 : count C 4 = 0) (h7 : count C 7 = 0) (t : Fin n) :
    colVal (C t) = 2 ∨ colVal (C t) = 3 ∨ colVal (C t) = 5 ∨ colVal (C t) = 6 := by
  have h17 := lm_columns17_total C hcols
  have htot : totalCounts C ({2, 3, 5, 6} : Finset ℕ) = n := by
    unfold totalCounts
    simp [Finset.sum_insert]
    unfold totalCounts at h17
    simp [Finset.sum_insert] at h17
    omega
  simpa [Finset.mem_insert, Finset.mem_singleton] using
    (colVal_mem_of_totalCounts C ({2, 3, 5, 6} : Finset ℕ) htot t)

/-- With |1|=|2|=|7|=0, the columns of a {1..7}-code have types in {3,4,5,6}. -/
lemma lm_types_346 (C : Code n)
    (hcols : ∀ t : Fin n, 1 ≤ colVal (C t) ∧ colVal (C t) ≤ 7)
    (h1 : count C 1 = 0) (h2 : count C 2 = 0) (h7 : count C 7 = 0) (t : Fin n) :
    colVal (C t) = 3 ∨ colVal (C t) = 4 ∨ colVal (C t) = 5 ∨ colVal (C t) = 6 := by
  have h17 := lm_columns17_total C hcols
  have htot : totalCounts C ({3, 4, 5, 6} : Finset ℕ) = n := by
    unfold totalCounts
    simp [Finset.sum_insert]
    unfold totalCounts at h17
    simp [Finset.sum_insert] at h17
    omega
  simpa [Finset.mem_insert, Finset.mem_singleton] using
    (colVal_mem_of_totalCounts C ({3, 4, 5, 6} : Finset ℕ) htot t)

/-- With |1|=|2|=|4|=0, the columns of a {1..7}-code have types in {3,5,6,7}. -/
lemma lm_types_3567 (C : Code n)
    (hcols : ∀ t : Fin n, 1 ≤ colVal (C t) ∧ colVal (C t) ≤ 7)
    (h1 : count C 1 = 0) (h2 : count C 2 = 0) (h4 : count C 4 = 0) (t : Fin n) :
    colVal (C t) = 3 ∨ colVal (C t) = 5 ∨ colVal (C t) = 6 ∨ colVal (C t) = 7 := by
  have h17 := lm_columns17_total C hcols
  have htot : totalCounts C ({3, 5, 6, 7} : Finset ℕ) = n := by
    unfold totalCounts
    simp [Finset.sum_insert]
    unfold totalCounts at h17
    simp [Finset.sum_insert] at h17
    omega
  simpa [Finset.mem_insert, Finset.mem_singleton] using
    (colVal_mem_of_totalCounts C ({3, 5, 6, 7} : Finset ℕ) htot t)

/-- With |2|=|4|=|7|=0, the columns of a {1..7}-code have types in {1,3,5,6}. -/
lemma lm_types_1356 (C : Code n)
    (hcols : ∀ t : Fin n, 1 ≤ colVal (C t) ∧ colVal (C t) ≤ 7)
    (h2 : count C 2 = 0) (h4 : count C 4 = 0) (h7 : count C 7 = 0) (t : Fin n) :
    colVal (C t) = 1 ∨ colVal (C t) = 3 ∨ colVal (C t) = 5 ∨ colVal (C t) = 6 := by
  have h17 := lm_columns17_total C hcols
  have htot : totalCounts C ({1, 3, 5, 6} : Finset ℕ) = n := by
    unfold totalCounts
    simp [Finset.sum_insert]
    unfold totalCounts at h17
    simp [Finset.sum_insert] at h17
    omega
  simpa [Finset.mem_insert, Finset.mem_singleton] using
    (colVal_mem_of_totalCounts C ({1, 3, 5, 6} : Finset ℕ) htot t)

/-- With |2|=|4|=|6|=0, the columns of a {1..7}-code have types in {1,3,5,7}. -/
lemma lm_types_1357 (C : Code n)
    (hcols : ∀ t : Fin n, 1 ≤ colVal (C t) ∧ colVal (C t) ≤ 7)
    (h2 : count C 2 = 0) (h4 : count C 4 = 0) (h6 : count C 6 = 0) (t : Fin n) :
    colVal (C t) = 1 ∨ colVal (C t) = 3 ∨ colVal (C t) = 5 ∨ colVal (C t) = 7 := by
  have h17 := lm_columns17_total C hcols
  have htot : totalCounts C ({1, 3, 5, 7} : Finset ℕ) = n := by
    unfold totalCounts
    simp [Finset.sum_insert]
    unfold totalCounts at h17
    simp [Finset.sum_insert] at h17
    omega
  simpa [Finset.mem_insert, Finset.mem_singleton] using
    (colVal_mem_of_totalCounts C ({1, 3, 5, 7} : Finset ℕ) htot t)

/-- Case-1 reduction for |2| > 0 in the proof of `lm:all` (Lemma 15): the row
swap (2,3) maps type 2 to 1 (and 5↔6), so the result is an equivalent code
with |1| > 0 and columns only in {1,3,5,6}.

Paper §III-D, Proof of Lemma 15, p. 148, Case 1: "we only argue the case
|1| > 0 and |2| = |4| = |7| = 0 since other cases can be transformed to this
case by interchanging rows".  This lemma performs that row interchange for the
|2| > 0 (|4| = |7| = 0) subcase, after which the Case-1 argument `lm_case1`
applies. -/
-- native_decide: Mechanical · n=any · checked 2026-08-28
lemma lm_caseB_col2_reduce (C : Code n)
    (hcols : ∀ t : Fin n, 1 ≤ colVal (C t) ∧ colVal (C t) ≤ 7)
    (h2 : 0 < count C 2) (h1 : count C 1 = 0) (h4 : count C 4 = 0) (h7 : count C 7 = 0) :
    ∃ Ct : Code n, Equivalent C Ct ∧ 0 < count Ct 1 ∧
      (∀ t : Fin n, colVal (Ct t) = 1 ∨ colVal (Ct t) = 3 ∨ colVal (Ct t) = 5 ∨ colVal (Ct t) = 6) := by
  let Ct : Code n := rowPermutedCode rho23 C
  refine ⟨Ct, rowPermutedCode_equiv rho23 C, ?_, ?_⟩
  · have h2pos : 1 ≤ count C 2 := by omega
    rcases exists_col_of_colVal C 2 h2pos with ⟨t, ht⟩
    have hc : C t = colOfNat 2 := by rw [← colOfNat_colVal (C t), ht]
    have hct : Ct t = col1 := by
      change rowPermute rho23 (C t) = col1
      rw [hc]
      native_decide
    exact count_pos_of_colVal Ct t (by rw [hct]; native_decide)
  · intro t
    rcases lm_types_236 C hcols h1 h4 h7 t with hv2 | hv3 | hv5 | hv6
    · have hc : C t = colOfNat 2 := by rw [← colOfNat_colVal (C t), hv2]
      change colVal (rowPermute rho23 (C t)) = 1 ∨ colVal (rowPermute rho23 (C t)) = 3 ∨
        colVal (rowPermute rho23 (C t)) = 5 ∨ colVal (rowPermute rho23 (C t)) = 6
      rw [hc]
      native_decide
    · have hc : C t = colOfNat 3 := by rw [← colOfNat_colVal (C t), hv3]
      change colVal (rowPermute rho23 (C t)) = 1 ∨ colVal (rowPermute rho23 (C t)) = 3 ∨
        colVal (rowPermute rho23 (C t)) = 5 ∨ colVal (rowPermute rho23 (C t)) = 6
      rw [hc]
      native_decide
    · have hc : C t = colOfNat 5 := by rw [← colOfNat_colVal (C t), hv5]
      change colVal (rowPermute rho23 (C t)) = 1 ∨ colVal (rowPermute rho23 (C t)) = 3 ∨
        colVal (rowPermute rho23 (C t)) = 5 ∨ colVal (rowPermute rho23 (C t)) = 6
      rw [hc]
      native_decide
    · have hc : C t = colOfNat 6 := by rw [← colOfNat_colVal (C t), hv6]
      change colVal (rowPermute rho23 (C t)) = 1 ∨ colVal (rowPermute rho23 (C t)) = 3 ∨
        colVal (rowPermute rho23 (C t)) = 5 ∨ colVal (rowPermute rho23 (C t)) = 6
      rw [hc]
      native_decide

/-- Case-1 reduction for |4| > 0 in the proof of `lm:all` (Lemma 15): the row
swap (1,3) maps type 4 to 1 (and 3↔6), so the result is an equivalent code
with |1| > 0 and columns only in {1,3,5,6}.

Paper §III-D, Proof of Lemma 15, p. 148, Case 1: "we only argue the case
|1| > 0 and |2| = |4| = |7| = 0 since other cases can be transformed to this
case by interchanging rows".  This lemma performs that row interchange for the
|4| > 0 (|2| = |7| = 0) subcase, after which the Case-1 argument `lm_case1`
applies. -/
-- native_decide: Mechanical · n=any · checked 2026-08-28
lemma lm_caseB_col4_reduce (C : Code n)
    (hcols : ∀ t : Fin n, 1 ≤ colVal (C t) ∧ colVal (C t) ≤ 7)
    (h4 : 0 < count C 4) (h1 : count C 1 = 0) (h2 : count C 2 = 0) (h7 : count C 7 = 0) :
    ∃ Ct : Code n, Equivalent C Ct ∧ 0 < count Ct 1 ∧
      (∀ t : Fin n, colVal (Ct t) = 1 ∨ colVal (Ct t) = 3 ∨ colVal (Ct t) = 5 ∨ colVal (Ct t) = 6) := by
  let Ct : Code n := rowPermutedCode rho13 C
  refine ⟨Ct, rowPermutedCode_equiv rho13 C, ?_, ?_⟩
  · have h4pos : 1 ≤ count C 4 := by omega
    rcases exists_col_of_colVal C 4 h4pos with ⟨t, ht⟩
    have hc : C t = colOfNat 4 := by rw [← colOfNat_colVal (C t), ht]
    have hct : Ct t = col1 := by
      change rowPermute rho13 (C t) = col1
      rw [hc]
      native_decide
    exact count_pos_of_colVal Ct t (by rw [hct]; native_decide)
  · intro t
    rcases lm_types_346 C hcols h1 h2 h7 t with hv3 | hv4 | hv5 | hv6
    · have hc : C t = colOfNat 3 := by rw [← colOfNat_colVal (C t), hv3]
      change colVal (rowPermute rho13 (C t)) = 1 ∨ colVal (rowPermute rho13 (C t)) = 3 ∨
        colVal (rowPermute rho13 (C t)) = 5 ∨ colVal (rowPermute rho13 (C t)) = 6
      rw [hc]
      native_decide
    · have hc : C t = colOfNat 4 := by rw [← colOfNat_colVal (C t), hv4]
      change colVal (rowPermute rho13 (C t)) = 1 ∨ colVal (rowPermute rho13 (C t)) = 3 ∨
        colVal (rowPermute rho13 (C t)) = 5 ∨ colVal (rowPermute rho13 (C t)) = 6
      rw [hc]
      native_decide
    · have hc : C t = colOfNat 5 := by rw [← colOfNat_colVal (C t), hv5]
      change colVal (rowPermute rho13 (C t)) = 1 ∨ colVal (rowPermute rho13 (C t)) = 3 ∨
        colVal (rowPermute rho13 (C t)) = 5 ∨ colVal (rowPermute rho13 (C t)) = 6
      rw [hc]
      native_decide
    · have hc : C t = colOfNat 6 := by rw [← colOfNat_colVal (C t), hv6]
      change colVal (rowPermute rho13 (C t)) = 1 ∨ colVal (rowPermute rho13 (C t)) = 3 ∨
        colVal (rowPermute rho13 (C t)) = 5 ∨ colVal (rowPermute rho13 (C t)) = 6
      rw [hc]
      native_decide

/-- Case-1 reduction for |7| > 0 in the proof of `lm:all` (Lemma 15): the row
swap (0,3) maps type 7 to 14, and `flipHighColumns` flips it to 1, so the
result is an equivalent code with |1| > 0 and columns only in {1,3,5,6}.

Paper §III-D, Proof of Lemma 15, p. 148, Case 1: "we only argue the case
|1| > 0 and |2| = |4| = |7| = 0 since other cases can be transformed to this
case by interchanging rows" (with column flipping for the |7| > 0 subcase, as
at the start of the proof where type-i, i > 7, columns are flipped).  This
lemma performs that transformation for the |7| > 0 (|1| = |2| = |4| = 0)
subcase, after which the Case-1 argument `lm_case1` applies. -/
-- native_decide: Mechanical · n=any · checked 2026-08-28
lemma lm_caseB_col7_reduce (C : Code n)
    (hcols : ∀ t : Fin n, 1 ≤ colVal (C t) ∧ colVal (C t) ≤ 7)
    (h7 : 0 < count C 7) (h1 : count C 1 = 0) (h2 : count C 2 = 0) (h4 : count C 4 = 0) :
    ∃ Ct : Code n, Equivalent C Ct ∧ 0 < count Ct 1 ∧
      (∀ t : Fin n, colVal (Ct t) = 1 ∨ colVal (Ct t) = 3 ∨ colVal (Ct t) = 5 ∨ colVal (Ct t) = 6) := by
  let Ct : Code n := flipHighColumns (rowPermutedCode rho03 C)
  have hEq : Equivalent C Ct :=
    equivalent_trans (rowPermutedCode_equiv rho03 C) (flipHighColumns_equiv (rowPermutedCode rho03 C))
  refine ⟨Ct, hEq, ?_, ?_⟩
  · have h7pos : 1 ≤ count C 7 := by omega
    rcases exists_col_of_colVal C 7 h7pos with ⟨t, ht⟩
    have hc : C t = colOfNat 7 := by rw [← colOfNat_colVal (C t), ht]
    have hct : Ct t = col1 := by
      change (if decide (7 < colVal (rowPermute rho03 (C t))) then
          flipCol (rowPermute rho03 (C t)) else rowPermute rho03 (C t)) = col1
      rw [hc]
      native_decide
    exact count_pos_of_colVal Ct t (by rw [hct]; native_decide)
  · intro t
    rcases lm_types_3567 C hcols h1 h2 h4 t with hv3 | hv5 | hv6 | hv7
    · have hc : C t = colOfNat 3 := by rw [← colOfNat_colVal (C t), hv3]
      change colVal (if decide (7 < colVal (rowPermute rho03 (C t))) then
          flipCol (rowPermute rho03 (C t)) else rowPermute rho03 (C t)) = 1 ∨
        colVal (if decide (7 < colVal (rowPermute rho03 (C t))) then
          flipCol (rowPermute rho03 (C t)) else rowPermute rho03 (C t)) = 3 ∨
        colVal (if decide (7 < colVal (rowPermute rho03 (C t))) then
          flipCol (rowPermute rho03 (C t)) else rowPermute rho03 (C t)) = 5 ∨
        colVal (if decide (7 < colVal (rowPermute rho03 (C t))) then
          flipCol (rowPermute rho03 (C t)) else rowPermute rho03 (C t)) = 6
      rw [hc]
      native_decide
    · have hc : C t = colOfNat 5 := by rw [← colOfNat_colVal (C t), hv5]
      change colVal (if decide (7 < colVal (rowPermute rho03 (C t))) then
          flipCol (rowPermute rho03 (C t)) else rowPermute rho03 (C t)) = 1 ∨
        colVal (if decide (7 < colVal (rowPermute rho03 (C t))) then
          flipCol (rowPermute rho03 (C t)) else rowPermute rho03 (C t)) = 3 ∨
        colVal (if decide (7 < colVal (rowPermute rho03 (C t))) then
          flipCol (rowPermute rho03 (C t)) else rowPermute rho03 (C t)) = 5 ∨
        colVal (if decide (7 < colVal (rowPermute rho03 (C t))) then
          flipCol (rowPermute rho03 (C t)) else rowPermute rho03 (C t)) = 6
      rw [hc]
      native_decide
    · have hc : C t = colOfNat 6 := by rw [← colOfNat_colVal (C t), hv6]
      change colVal (if decide (7 < colVal (rowPermute rho03 (C t))) then
          flipCol (rowPermute rho03 (C t)) else rowPermute rho03 (C t)) = 1 ∨
        colVal (if decide (7 < colVal (rowPermute rho03 (C t))) then
          flipCol (rowPermute rho03 (C t)) else rowPermute rho03 (C t)) = 3 ∨
        colVal (if decide (7 < colVal (rowPermute rho03 (C t))) then
          flipCol (rowPermute rho03 (C t)) else rowPermute rho03 (C t)) = 5 ∨
        colVal (if decide (7 < colVal (rowPermute rho03 (C t))) then
          flipCol (rowPermute rho03 (C t)) else rowPermute rho03 (C t)) = 6
      rw [hc]
      native_decide
    · have hc : C t = colOfNat 7 := by rw [← colOfNat_colVal (C t), hv7]
      change colVal (if decide (7 < colVal (rowPermute rho03 (C t))) then
          flipCol (rowPermute rho03 (C t)) else rowPermute rho03 (C t)) = 1 ∨
        colVal (if decide (7 < colVal (rowPermute rho03 (C t))) then
          flipCol (rowPermute rho03 (C t)) else rowPermute rho03 (C t)) = 3 ∨
        colVal (if decide (7 < colVal (rowPermute rho03 (C t))) then
          flipCol (rowPermute rho03 (C t)) else rowPermute rho03 (C t)) = 5 ∨
        colVal (if decide (7 < colVal (rowPermute rho03 (C t))) then
          flipCol (rowPermute rho03 (C t)) else rowPermute rho03 (C t)) = 6
      rw [hc]
      native_decide

/-- Case-2 reduction for |7| > 0 and |2| > 0 in the proof of `lm:all` (Lemma 15):
the row swap (2,3) maps type 2 to 1 and fixes type 7, so the result is an
equivalent code with |1| > 0 ∧ |7| > 0.

Paper §III-D, Proof of Lemma 15, p. 148, Case 2: "the case |7| > 0 and |2| > 0
or |4| > 0 can be transformed to the case |7| > 0 and |1| > 0 by interchanging
rows".  This lemma performs that interchange for the |2| > 0 subcase, after
which the Case-2 core `lm_caseC_17` applies. -/
-- native_decide: Mechanical · n=any · checked 2026-08-28
lemma lm_caseC_2_reduce (C : Code n)
    (hcols : ∀ t : Fin n, 1 ≤ colVal (C t) ∧ colVal (C t) ≤ 7)
    (h2 : 0 < count C 2) (h7 : 0 < count C 7) :
    ∃ Ct : Code n, Equivalent C Ct ∧ 0 < count Ct 1 ∧ 0 < count Ct 7 ∧
      (∀ t : Fin n, 1 ≤ colVal (Ct t) ∧ colVal (Ct t) ≤ 7) := by
  let Ct : Code n := rowPermutedCode rho23 C
  refine ⟨Ct, rowPermutedCode_equiv rho23 C, ?_, ?_⟩
  · have h2pos : 1 ≤ count C 2 := by omega
    rcases exists_col_of_colVal C 2 h2pos with ⟨t, ht⟩
    have hc : C t = colOfNat 2 := by rw [← colOfNat_colVal (C t), ht]
    have hct : Ct t = col1 := by
      change rowPermute rho23 (C t) = col1
      rw [hc]
      native_decide
    exact count_pos_of_colVal Ct t (by rw [hct]; native_decide)
  · constructor
    · have h7pos : 1 ≤ count C 7 := by omega
      rcases exists_col_of_colVal C 7 h7pos with ⟨t, ht⟩
      have hc : C t = colOfNat 7 := by rw [← colOfNat_colVal (C t), ht]
      have hct : Ct t = col7 := by
        change rowPermute rho23 (C t) = col7
        rw [hc]
        native_decide
      exact count_pos_of_colVal Ct t (by rw [hct]; native_decide)
    · intro t
      change 1 ≤ colVal (rowPermute rho23 (C t)) ∧ colVal (rowPermute rho23 (C t)) ≤ 7
      exact rowPermute_fix0_cols17 C rho23 (by native_decide) hcols t

/-- Case-2 reduction for |7| > 0 and |4| > 0 in the proof of `lm:all` (Lemma 15):
the row swap (1,3) maps type 4 to 1 and fixes type 7, so the result is an
equivalent code with |1| > 0 ∧ |7| > 0.

Paper §III-D, Proof of Lemma 15, p. 148, Case 2: "the case |7| > 0 and |2| > 0
or |4| > 0 can be transformed to the case |7| > 0 and |1| > 0 by interchanging
rows".  This lemma performs that interchange for the |4| > 0 subcase, after
which the Case-2 core `lm_caseC_17` applies. -/
-- native_decide: Mechanical · n=any · checked 2026-08-28
lemma lm_caseC_4_reduce (C : Code n)
    (hcols : ∀ t : Fin n, 1 ≤ colVal (C t) ∧ colVal (C t) ≤ 7)
    (h4 : 0 < count C 4) (h7 : 0 < count C 7) :
    ∃ Ct : Code n, Equivalent C Ct ∧ 0 < count Ct 1 ∧ 0 < count Ct 7 ∧
      (∀ t : Fin n, 1 ≤ colVal (Ct t) ∧ colVal (Ct t) ≤ 7) := by
  let Ct : Code n := rowPermutedCode rho13 C
  refine ⟨Ct, rowPermutedCode_equiv rho13 C, ?_, ?_⟩
  · have h4pos : 1 ≤ count C 4 := by omega
    rcases exists_col_of_colVal C 4 h4pos with ⟨t, ht⟩
    have hc : C t = colOfNat 4 := by rw [← colOfNat_colVal (C t), ht]
    have hct : Ct t = col1 := by
      change rowPermute rho13 (C t) = col1
      rw [hc]
      native_decide
    exact count_pos_of_colVal Ct t (by rw [hct]; native_decide)
  · constructor
    · have h7pos : 1 ≤ count C 7 := by omega
      rcases exists_col_of_colVal C 7 h7pos with ⟨t, ht⟩
      have hc : C t = colOfNat 7 := by rw [← colOfNat_colVal (C t), ht]
      have hct : Ct t = col7 := by
        change rowPermute rho13 (C t) = col7
        rw [hc]
        native_decide
      exact count_pos_of_colVal Ct t (by rw [hct]; native_decide)
    · intro t
      change 1 ≤ colVal (rowPermute rho13 (C t)) ∧ colVal (rowPermute rho13 (C t)) ≤ 7
      exact rowPermute_fix0_cols17 C rho13 (by native_decide) hcols t

/-- Case-2 reduction for |1| > 0 and |2| > 0 with |7| = 0 in the proof of
`lm:all` (Lemma 15): flip the columns of types 2,3,6 and swap rows 0,2 (Fig.
fig:iwla).  The transformation maps types 1,2,3,4,5,6 to 1,7,6,4,5,3 (paper's
|1| = |1|_{C'}, |2| = |7|_{C'}, |3| = |6|_{C'}, |4| = |4|_{C'}, |5| = |5|_{C'},
|6| = |3|_{C'}; a type-7 column would map to type 13, which is why the |7| = 0
hypothesis is needed), so |1| and |7| become positive.

Paper §III-D, Proof of Lemma 15, p. 148, Case 2 (last paragraph): "we consider
the case |7| = 0 and at least two of |1|, |2|, |4| are positive... Let C' be
the code obtained by flipping all the columns of type 2, 3, and 6 in C and
then exchanging the third and the first rows".  This lemma realizes that
transformation for the |1|,|2| positive subcase, giving the |7| > 0 ∧ |1| > 0
hypotheses needed by `lm_caseC_17`. -/
-- native_decide: Mechanical · n=any · checked 2026-08-28
lemma lm_caseC_no7_reduce (C : Code n)
    (hcols : ∀ t : Fin n, 1 ≤ colVal (C t) ∧ colVal (C t) ≤ 7)
    (h7z : count C 7 = 0)
    (h1 : 0 < count C 1) (h2 : 0 < count C 2) :
    ∃ Ct : Code n, Equivalent C Ct ∧ 0 < count Ct 1 ∧ 0 < count Ct 7 ∧
      (∀ t : Fin n, 1 ≤ colVal (Ct t) ∧ colVal (Ct t) ≤ 7) := by
  let Ct : Code n := rowPermutedCode rho02 (flip236 C)
  have hEq : Equivalent C Ct :=
    equivalent_trans (flip236_equiv C) (rowPermutedCode_equiv rho02 (flip236 C))
  refine ⟨Ct, hEq, ?_, ?_⟩
  · have h1pos : 1 ≤ count C 1 := by omega
    rcases exists_col_of_colVal C 1 h1pos with ⟨t, ht⟩
    have hc : C t = colOfNat 1 := by rw [← colOfNat_colVal (C t), ht]
    have hct : Ct t = col1 := by
      change rowPermute rho02 (if colVal (C t) = 2 ∨ colVal (C t) = 3 ∨ colVal (C t) = 6 then flipCol (C t) else C t) = col1
      rw [hc]
      native_decide
    exact count_pos_of_colVal Ct t (by rw [hct]; native_decide)
  · constructor
    · have h2pos : 1 ≤ count C 2 := by omega
      rcases exists_col_of_colVal C 2 h2pos with ⟨t, ht⟩
      have hc : C t = colOfNat 2 := by rw [← colOfNat_colVal (C t), ht]
      have hct : Ct t = col7 := by
        change rowPermute rho02 (if colVal (C t) = 2 ∨ colVal (C t) = 3 ∨ colVal (C t) = 6 then flipCol (C t) else C t) = col7
        rw [hc]
        native_decide
      exact count_pos_of_colVal Ct t (by rw [hct]; native_decide)
    · intro t
      rcases hcols t with ⟨hge, hle⟩
      change 1 ≤ colVal (rowPermute rho02
          (if colVal (C t) = 2 ∨ colVal (C t) = 3 ∨ colVal (C t) = 6 then flipCol (C t) else C t)) ∧
        colVal (rowPermute rho02
          (if colVal (C t) = 2 ∨ colVal (C t) = 3 ∨ colVal (C t) = 6 then flipCol (C t) else C t)) ≤ 7
      have hcases : colVal (C t) = 1 ∨ colVal (C t) = 2 ∨ colVal (C t) = 3 ∨ colVal (C t) = 4 ∨
          colVal (C t) = 5 ∨ colVal (C t) = 6 ∨ colVal (C t) = 7 := by omega
      rcases hcases with hv1 | hv2 | hv3 | hv4 | hv5 | hv6 | hv7
      · have hct : C t = colOfNat 1 := by rw [← colOfNat_colVal (C t), hv1]
        rw [hct]
        native_decide
      · have hct : C t = colOfNat 2 := by rw [← colOfNat_colVal (C t), hv2]
        rw [hct]
        native_decide
      · have hct : C t = colOfNat 3 := by rw [← colOfNat_colVal (C t), hv3]
        rw [hct]
        native_decide
      · have hct : C t = colOfNat 4 := by rw [← colOfNat_colVal (C t), hv4]
        rw [hct]
        native_decide
      · have hct : C t = colOfNat 5 := by rw [← colOfNat_colVal (C t), hv5]
        rw [hct]
        native_decide
      · have hct : C t = colOfNat 6 := by rw [← colOfNat_colVal (C t), hv6]
        rw [hct]
        native_decide
      · have h7pos : 1 ≤ count C 7 := count_pos_of_colVal C t hv7
        omega

/-- Case-2 pre-reduction for |1| > 0 and |4| > 0 (|7| = 0) in the proof of
`lm:all` (Lemma 15): the row swap (1,2) maps type 4 to 2 and fixes type 1,
giving |1| > 0 ∧ |2| > 0 for `lm_caseC_no7_reduce`.

Paper §III-D, Proof of Lemma 15, p. 148, Case 2 (last paragraph): the |7| = 0
case is argued for |1| and |2| positive, "and the other cases can be
transformed to this case by interchanging rows".  This lemma performs that
interchange for the |1|,|4| positive subcase. -/
-- native_decide: Mechanical · n=any · checked 2026-08-28
lemma lm_caseC_14_reduce (C : Code n)
    (hcols : ∀ t : Fin n, 1 ≤ colVal (C t) ∧ colVal (C t) ≤ 7)
    (h7z : count C 7 = 0)
    (h1 : 0 < count C 1) (h4 : 0 < count C 4) :
    ∃ Ct : Code n, Equivalent C Ct ∧ 0 < count Ct 1 ∧ 0 < count Ct 2 ∧ count Ct 7 = 0 ∧
      (∀ t : Fin n, 1 ≤ colVal (Ct t) ∧ colVal (Ct t) ≤ 7) := by
  let Ct : Code n := rowPermutedCode rho15 C
  refine ⟨Ct, rowPermutedCode_equiv rho15 C, ?_, ?_⟩
  · have h1pos : 1 ≤ count C 1 := by omega
    rcases exists_col_of_colVal C 1 h1pos with ⟨t, ht⟩
    have hc : C t = colOfNat 1 := by rw [← colOfNat_colVal (C t), ht]
    have hct : Ct t = col1 := by
      change rowPermute rho15 (C t) = col1
      rw [hc]
      native_decide
    exact count_pos_of_colVal Ct t (by rw [hct]; native_decide)
  · constructor
    · have h4pos : 1 ≤ count C 4 := by omega
      rcases exists_col_of_colVal C 4 h4pos with ⟨t, ht⟩
      have hc : C t = colOfNat 4 := by rw [← colOfNat_colVal (C t), ht]
      have hct : Ct t = colOfNat 2 := by
        change rowPermute rho15 (C t) = colOfNat 2
        rw [hc]
        native_decide
      exact count_pos_of_colVal Ct t (by rw [hct]; native_decide)
    · constructor
      · rw [count_fix7_rowPermute rho15 (by native_decide) C, h7z]
      · intro t
        change 1 ≤ colVal (rowPermute rho15 (C t)) ∧ colVal (rowPermute rho15 (C t)) ≤ 7
        exact rowPermute_fix0_cols17 C rho15 (by native_decide) hcols t

/-- Case-2 pre-reduction for |2| > 0 and |4| > 0 (|7| = 0) in the proof of
`lm:all` (Lemma 15): the row swap (1,3) maps type 4 to 1 and fixes type 2,
giving |1| > 0 ∧ |2| > 0 for `lm_caseC_no7_reduce`.

Paper §III-D, Proof of Lemma 15, p. 148, Case 2 (last paragraph): the |7| = 0
case is argued for |1| and |2| positive, "and the other cases can be
transformed to this case by interchanging rows".  This lemma performs that
interchange for the |2|,|4| positive subcase. -/
-- native_decide: Mechanical · n=any · checked 2026-08-28
lemma lm_caseC_24_reduce (C : Code n)
    (hcols : ∀ t : Fin n, 1 ≤ colVal (C t) ∧ colVal (C t) ≤ 7)
    (h7z : count C 7 = 0)
    (h2 : 0 < count C 2) (h4 : 0 < count C 4) :
    ∃ Ct : Code n, Equivalent C Ct ∧ 0 < count Ct 1 ∧ 0 < count Ct 2 ∧ count Ct 7 = 0 ∧
      (∀ t : Fin n, 1 ≤ colVal (Ct t) ∧ colVal (Ct t) ≤ 7) := by
  let Ct : Code n := rowPermutedCode rho13 C
  refine ⟨Ct, rowPermutedCode_equiv rho13 C, ?_, ?_⟩
  · have h4pos : 1 ≤ count C 4 := by omega
    rcases exists_col_of_colVal C 4 h4pos with ⟨t, ht⟩
    have hc : C t = colOfNat 4 := by rw [← colOfNat_colVal (C t), ht]
    have hct : Ct t = col1 := by
      change rowPermute rho13 (C t) = col1
      rw [hc]
      native_decide
    exact count_pos_of_colVal Ct t (by rw [hct]; native_decide)
  · constructor
    · have h2pos : 1 ≤ count C 2 := by omega
      rcases exists_col_of_colVal C 2 h2pos with ⟨t, ht⟩
      have hc : C t = colOfNat 2 := by rw [← colOfNat_colVal (C t), ht]
      have hct : Ct t = colOfNat 2 := by
        change rowPermute rho13 (C t) = colOfNat 2
        rw [hc]
        native_decide
      exact count_pos_of_colVal Ct t (by rw [hct]; native_decide)
    · constructor
      · rw [count_fix7_rowPermute rho13 (by native_decide) C, h7z]
      · intro t
        change 1 ≤ colVal (rowPermute rho13 (C t)) ∧ colVal (rowPermute rho13 (C t)) ≤ 7
        exact rowPermute_fix0_cols17 C rho13 (by native_decide) hcols t

/-- `lm:all` (Lemma 15) Case-1 core: |1| > 0, columns in {1,3,5,6}, w(c₃⊕c₄) even.  The
`thm:even` (Theorem 8) 1→3 flip is never worse; the equality conditions (i)/(ii)/(iii)
map to Class-II / Class-III-b / an equivalent Class-III-b code, and if none
holds the flip is strictly better (contradicting optimality).

Paper §III-D, Proof of Lemma 15, p. 148, Case 1: after the row-interchange
reductions, "we assume w(c₃⊕c₄) is even since other cases can be transformed
to this case by interchanging rows.  Hence, C does not satisfy all the
following conditions: [i)] w(c₁⊕c₃) and w(c₂⊕c₃) are odd (else C is Class-II);
[ii)] |1|=1, |5|=0, |3| and |6| odd (else Class-III-b); [iii)] |1|=1, |6|=0,
|3| and |5| odd (else equivalent to Class-III-b).  Then by Theorem 8, replacing
a column of type 1 of C by 3 can give a strictly better code." -/
lemma lm_case1_wC_even (C : Code n)
    (htot : totalCounts C {1,3,5,6} = n) (h1pos : 0 < count C 1)
    (hwC : Even (hammingDist (row2 C) (row3 C)))
    (hnoStrict : ∀ D : Code n, UniversalStrictBetter D C → False) :
    ∃ C' : Code n, Equivalent C C' ∧ (ClassI C' ∨ ClassII C' ∨ ClassIII C') := by
  have h07 : Columns07 C := Columns07_of_types_1356 C htot
  rcases exists_col1_of_count_pos C (by omega : 1 ≤ count C 1) with ⟨t, ht1⟩
  let C' : Code n := replaceColumn C t col3
  have hcol' : C' t = col3 := by simp [C', replaceColumn]
  have hsame : ∀ u : Fin n, u ≠ t → C' u = C u := by
    intro u hu
    simp [C', replaceColumn, hu]
  have hflip := one_bit_flip C C' t ht1 hcol' hsame hwC h07
  have hbetter : UniversalBetter C' C := hflip.1
  have heqiff : UniversalEqual C' C ↔
      (Odd (hammingDist (row0 C) (row2 C)) ∧ Odd (hammingDist (row1 C) (row2 C))) ∨
      (count C 1 = 1 ∧ count C 2 = 0 ∧ count C 4 = 0 ∧ count C 5 = 0 ∧
          count C 7 = 0 ∧ Odd (count C 3) ∧ Odd (count C 6)) ∨
      (count C 1 = 1 ∧ count C 2 = 0 ∧ count C 4 = 0 ∧ count C 6 = 0 ∧
          count C 7 = 0 ∧ Odd (count C 3) ∧ Odd (count C 5)) := hflip.2
  by_cases hcond : (Odd (hammingDist (row0 C) (row2 C)) ∧ Odd (hammingDist (row1 C) (row2 C))) ∨
      (count C 1 = 1 ∧ count C 2 = 0 ∧ count C 4 = 0 ∧ count C 5 = 0 ∧
          count C 7 = 0 ∧ Odd (count C 3) ∧ Odd (count C 6)) ∨
      (count C 1 = 1 ∧ count C 2 = 0 ∧ count C 4 = 0 ∧ count C 6 = 0 ∧
          count C 7 = 0 ∧ Odd (count C 3) ∧ Odd (count C 5))
  · rcases hcond with hi | hii | hiii
    · rcases hi with ⟨hw03, hw13⟩
      exact ⟨C, equivalent_refl C,
        Or.inr (Or.inl (class2_of_w24_even_odd_w03_w13 C htot h1pos hw03 hw13 hwC))⟩
    · rcases hii with ⟨h1, _h2, _h4, h5z, _h7, h3o, h6o⟩
      exact ⟨C, equivalent_refl C,
        Or.inr (Or.inr (class3_of_cond2 C htot h1 h5z h3o h6o))⟩
    · rcases hiii with ⟨h1, _h2, _h4, h6z, _h7, h3o, h5o⟩
      rcases class3_of_cond3 C h07 htot h1 h6z h3o h5o with ⟨C'', hEq, hC3⟩
      exact ⟨C'', hEq, Or.inr (Or.inr hC3)⟩
  · have hnotempty : ¬ ∀ y : Word n, ¬ Y3 C t y := by
      intro hy
      exact hcond ((Y3_empty_iff C t ht1 hwC h07).mp hy)
    have hY3 : ∃ y : Word n, Y3 C t y := by
      by_contra hnone
      apply hnotempty
      intro y hy
      exact hnone ⟨y, hy⟩
    have hstrict : UniversalStrictBetter C' C :=
      one_bit_flip_strict C C' t ht1 hcol' hsame hwC hY3
    exfalso
    exact hnoStrict C' hstrict

/-- `lm:all` (Lemma 15) Case-1: columns in {1,3,5,6}, |1| > 0.  If the code is Class-I we
are done; otherwise at least one of w(c₁⊕c₄), w(c₂⊕c₄), w(c₃⊕c₄) is even, and
row-swap equivalences (swap02 for 3↔6; rho15 for 3↔5) transport the other two
parity cases to the w(c₃⊕c₄)-even core `lm_case1_wC_even`.

Paper §III-D, Proof of Lemma 15, p. 148, Case 1: "referring to the proof of
Corollary 10, we see that at least one of w(c₁⊕c₄), w(c₂⊕c₄), and w(c₃⊕c₄)
are even due to C is non-Class-I.  Here we assume w(c₃⊕c₄) is even since other
cases can be transformed to this case by interchanging rows." -/
-- native_decide: Mechanical · n=any · checked 2026-08-28
lemma lm_case1 (C : Code n)
    (htot : totalCounts C {1,3,5,6} = n) (h1pos : 0 < count C 1)
    (hnoStrict : ∀ D : Code n, UniversalStrictBetter D C → False) :
    ∃ C' : Code n, Equivalent C C' ∧ (ClassI C' ∨ ClassII C' ∨ ClassIII C') := by
  by_cases hci : ClassI C
  · exact ⟨C, equivalent_refl C, Or.inl hci⟩
  · have hone : Even (hammingDist (row0 C) (row3 C)) ∨
      Even (hammingDist (row2 C) (row3 C)) ∨
      Even (hammingDist (row1 C) (row3 C)) := by
      by_contra hnot
      have hnA : ¬ Even (hammingDist (row0 C) (row3 C)) := fun hA => hnot (Or.inl hA)
      have hnB : ¬ Even (hammingDist (row2 C) (row3 C)) := fun hB => hnot (Or.inr (Or.inl hB))
      have hnC : ¬ Even (hammingDist (row1 C) (row3 C)) := fun hC => hnot (Or.inr (Or.inr hC))
      have htypes : ∀ t : Fin n, colVal (C t) = 1 ∨ colVal (C t) = 3 ∨ colVal (C t) = 5 ∨ colVal (C t) = 6 :=
        types_1356_of_totalCounts C htot
      have hA' : ¬ Even (count C 1 + count C 3 + count C 5) := by
        rw [hammingDist_row0_row3_of_types1356 C htypes] at hnA
        exact hnA
      have hB' : ¬ Even (count C 1 + count C 5 + count C 6) := by
        rw [hammingDist_row2_row3_of_types1356 C htypes] at hnB
        exact hnB
      have hC' : ¬ Even (count C 1 + count C 3 + count C 6) := by
        rw [hammingDist_row1_row3_of_types1356 C htypes] at hnC
        exact hnC
      have hpar := not_even_three_weights_imp_class1_parity (count C 1) (count C 3) (count C 5) (count C 6) hA' hB' hC'
      exact hci ⟨hpar.1, hpar.2, htot⟩
    rcases hone with hA | hB | hC
    · -- w(c₁⊕c₄) even: transport via swap02 (types 3↔6)
      let D : Code n := swapRows02Code C
      have hEq : Equivalent C D := swapRows02Code_equiv C
      have hnoStrictD : ∀ D' : Code n, UniversalStrictBetter D' D → False :=
        noStrict_of_equiv hnoStrict hEq
      have h07C : Columns07 C := Columns07_of_types_1356 C htot
      have htotD : totalCounts D {1,3,5,6} = n := totalCounts_swapRows02Code_1356 C h07C htot
      have h1posD : 0 < count D 1 := by
        rw [count_swapRows02Code C h07C 1]
        simp [swapVal02]
        exact h1pos
      have hwCD : Even (hammingDist (row2 D) (row3 D)) := by
        rw [hammingDist_row2_row3_swapRows02 C]
        exact hA
      rcases lm_case1_wC_even D htotD h1posD hwCD hnoStrictD with ⟨C'', hEqD, hcl⟩
      exact ⟨C'', equivalent_trans hEq hEqD, hcl⟩
    · -- w(c₃⊕c₄) even: direct
      exact lm_case1_wC_even C htot h1pos hB hnoStrict
    · -- w(c₂⊕c₄) even: transport via rho15 (types 3↔5)
      let D : Code n := rowPermutedCode rho15 C
      have hEq : Equivalent C D := rowPermutedCode_equiv rho15 C
      have hnoStrictD : ∀ D' : Code n, UniversalStrictBetter D' D → False :=
        noStrict_of_equiv hnoStrict hEq
      have htotD : totalCounts D {1,3,5,6} = n := by
        exact totalCounts_rowPermutedCode_into rho15 C ({1,3,5,6} : Finset ℕ) ({1,3,5,6} : Finset ℕ) htot
          (fun t => by
            rcases types_1356_of_totalCounts C htot t with h1 | h3 | h5 | h6
            · simp [h1]
            · simp [h3]
            · simp [h5]
            · simp [h6])
          (by
            intro v hv
            simp [Finset.mem_insert, Finset.mem_singleton] at hv
            rcases hv with rfl | rfl | rfl | rfl <;> native_decide)
      have h1posD : 0 < count D 1 := by
        rcases exists_col1_of_count_pos C (by omega : 1 ≤ count C 1) with ⟨t, ht1⟩
        have hc : D t = col1 := by
          change rowPermute rho15 (C t) = col1
          rw [ht1]
          native_decide
        exact count_pos_of_colVal D t (by rw [hc]; native_decide)
      have hwCD : Even (hammingDist (row2 D) (row3 D)) := by
        change Even (hammingDist (row (rowPermutedCode rho15 C) 2) (row (rowPermutedCode rho15 C) 3))
        rw [row_rowPermutedCode rho15 C 2, row_rowPermutedCode rho15 C 3]
        rw [show rho15 2 = (1 : Fin 4) by native_decide, show rho15 3 = (3 : Fin 4) by native_decide]
        exact hC
      rcases lm_case1_wC_even D htotD h1posD hwCD hnoStrictD with ⟨C'', hEqD, hcl⟩
      exact ⟨C'', equivalent_trans hEq hEqD, hcl⟩

/-- A code whose columns all have types in {1,3,5,6} has totalCounts
{1,3,5,6} = n. -/
lemma totalCounts_1356_of_mem {n : ℕ} (C : Code n)
    (htypes : ∀ t : Fin n, colVal (C t) = 1 ∨ colVal (C t) = 3 ∨ colVal (C t) = 5 ∨ colVal (C t) = 6) :
    totalCounts C {1,3,5,6} = n := by
  unfold totalCounts count
  rw [Finset.sum_comm]
  calc
    (∑ t : Fin n, ∑ i ∈ ({1,3,5,6} : Finset ℕ), if colVal (C t) = i then 1 else 0)
        = ∑ t : Fin n, (1 : ℕ) := by
          apply Finset.sum_congr rfl
          intro u _
          rcases htypes u with h1 | h3 | h5 | h6
          · simp [h1]
          · simp [h3]
          · simp [h5]
          · simp [h6]
    _ = n := by simp

/-- Count transport for a row permutation mapping {1,3,5,7} types by a known
rule. -/
lemma count_rowPermutedCode_of_1357 {n : ℕ} (ρ : Equiv (Fin 4) (Fin 4)) (C : Code n) (i j : ℕ)
    (hS : ∀ t : Fin n, colVal (C t) ∈ ({1,3,5,7} : Finset ℕ))
    (h : ∀ v ∈ ({1,3,5,7} : Finset ℕ), colVal (rowPermute ρ (colOfNat v)) = i ↔ v = j) :
    count (rowPermutedCode ρ C) i = count C j := by
  unfold count rowPermutedCode
  apply Finset.sum_congr rfl
  intro t _
  have hcv : colVal (C t) ∈ ({1,3,5,7} : Finset ℕ) := hS t
  rw [show rowPermute ρ (C t) = rowPermute ρ (colOfNat (colVal (C t))) by rw [colOfNat_colVal (C t)]]
  have hiff := h (colVal (C t)) hcv
  by_cases hcol : colVal (rowPermute ρ (colOfNat (colVal (C t)))) = i
  · have hj : colVal (C t) = j := hiff.mp hcol
    rw [if_pos hcol, if_pos hj]
  · have hj : ¬ colVal (C t) = j := fun hj => hcol (hiff.mpr hj)
    rw [if_neg hcol, if_neg hj]

/-- `lm:all` (Lemma 15) Case-2 core: |1| > 0 ∧ |7| > 0, columns in {1..7}.  `thm:odd` (Theorem 11)'s
`two_bit_flip` is never worse; Condition-A (|1|=|7|=1, |2|=|4|=|6|=0, odd |3|
or odd |5|) forces columns in {1,3,5,7}: if |3| even and |5| odd the code is
Class-III-a, if |3| odd and |5| even it is equivalent (rho15, types 3↔5) to a
Class-III-a code, and if |3|,|5| are both odd the `thm:even` (Theorem 8) 1→3 flip is
strictly better (all three w-parities even); if Condition-A fails the two-bit
flip is strictly better.

Paper §III-D, Proof of Lemma 15, p. 148, Case 2: "we first argue the case
|7| > 0 and |1| > 0.  Denote as Condition-A that |1| = |7| = 1, |2| = |4| =
|6| = 0 and at least one of |3| and |5| is odd.  If Condition-A is not
satisfied, by Theorem 11, changing columns 1 and 7 of C to 3 and 5 can give a
strictly better code.  If Condition-A is satisfied, we have |3| and |5| are
both odd since C is not equivalent to a Class-III-a code.  Then we have
w(c₃⊕c₄), w(c₁⊕c₃), and w(c₂⊕c₃) are all even, and hence by Theorem 8,
replacing a column of type 1 of C by 3 gives a strictly better code." -/
-- native_decide: Mechanical · n=any · checked 2026-08-28
lemma lm_caseC_17 (C : Code n)
    (hcols : ∀ t : Fin n, 1 ≤ colVal (C t) ∧ colVal (C t) ≤ 7)
    (h1pos : 0 < count C 1) (h7pos : 0 < count C 7)
    (hnoStrict : ∀ D : Code n, UniversalStrictBetter D C → False) :
    ∃ C' : Code n, Equivalent C C' ∧ (ClassI C' ∨ ClassII C' ∨ ClassIII C') := by
  have h1le : 1 ≤ count C 1 := by omega
  have h7le : 1 ≤ count C 7 := by omega
  rcases exists_col_of_colVal C 1 h1le with ⟨t1, ht1⟩
  rcases exists_col_of_colVal C 7 h7le with ⟨t7, ht7⟩
  have hc1 : C t1 = col1 := (colVal_eq_one_iff_col1 (C t1)).mp ht1
  have hc7 : C t7 = col7 := (colVal_eq_seven_iff_col7 (C t7)).mp ht7
  have htne : t1 ≠ t7 := by
    intro heq
    have hv : colVal (C t1) = 7 := by rw [heq]; exact ht7
    norm_num [ht1] at hv
  let C' : Code n := replaceColumn (replaceColumn C t1 col3) t7 col5
  have hsame : ∀ u : Fin n, u ≠ t1 → u ≠ t7 → C' u = C u := by
    intro u hu1 hu7
    simp [C', replaceColumn, hu1, hu7]
  have h07 : Columns07 C := columns07_of_colVal_le7 C (fun t => (hcols t).2)
  have hb := two_bit_flip C C' t1 t7 htne hc1 hc7 (by simp [C', replaceColumn, htne]) (by simp [C', replaceColumn]) hsame h07
  by_cases hcond : count C 1 = 1 ∧ count C 7 = 1 ∧ count C 2 = 0 ∧ count C 4 = 0 ∧
      count C 6 = 0 ∧ (Odd (count C 3) ∨ Odd (count C 5))
  · rcases hcond with ⟨h1eq, h7eq, h2z, h4z, h6z, h35odd⟩
    have htypes1357 : ∀ u : Fin n, colVal (C u) = 1 ∨ colVal (C u) = 3 ∨ colVal (C u) = 5 ∨ colVal (C u) = 7 :=
      lm_types_1357 C hcols h2z h4z h6z
    have hS1357 : ∀ u : Fin n, colVal (C u) ∈ ({1,3,5,7} : Finset ℕ) := by
      intro u
      rcases htypes1357 u with h1 | h3 | h5 | h7
      · simp [h1]
      · simp [h3]
      · simp [h5]
      · simp [h7]
    by_cases h5o : Odd (count C 5)
    · by_cases h3e : Even (count C 3)
      · -- Class-III-a
        have htot5 : totalCounts C ({1,3,5,6,7} : Finset ℕ) = n := by
          have h17 := lm_columns17_total C hcols
          unfold totalCounts
          simp [Finset.sum_insert, h6z]
          unfold totalCounts at h17
          simp [Finset.sum_insert] at h17
          omega
        exact ⟨C, equivalent_refl C, Or.inr (Or.inr ⟨htot5, Or.inl ⟨h1eq, h7eq, h6z, h3e, h5o⟩⟩)⟩
      · -- |3| odd and |5| odd: the 1→3 flip is strictly better
        have h3o : Odd (count C 3) := Nat.not_even_iff_odd.mp h3e
        rcases exists_col1_of_count_pos C (by omega : 1 ≤ count C 1) with ⟨t, ht1⟩
        let C₁ : Code n := replaceColumn C t col3
        have hcol₁ : C₁ t = col3 := by simp [C₁, replaceColumn]
        have hsame₁ : ∀ u : Fin n, u ≠ t → C₁ u = C u := by
          intro u hu
          simp [C₁, replaceColumn, hu]
        have hwC : Even (hammingDist (row2 C) (row3 C)) := by
          rw [hammingDist_row2_row3_of_types1357 C htypes1357]
          rw [h1eq]
          rcases h5o with ⟨a, ha⟩
          refine ⟨a + 1, by omega⟩
        have hw03 : Even (hammingDist (row0 C) (row2 C)) := by
          rw [hammingDist_row0_row2_of_types1357 C htypes1357]
          rw [h7eq]
          rcases h3o with ⟨a, ha⟩
          refine ⟨a + 1, by omega⟩
        have hw13 : Even (hammingDist (row1 C) (row2 C)) := by
          rw [hammingDist_row1_row2_of_types1357 C htypes1357]
          rcases h3o with ⟨a, ha⟩
          rcases h5o with ⟨b, hb⟩
          refine ⟨a + b + 1, by omega⟩
        have hflip := one_bit_flip C C₁ t ht1 hcol₁ hsame₁ hwC h07
        have hbetter : UniversalBetter C₁ C := hflip.1
        have heqiff : UniversalEqual C₁ C ↔
            (Odd (hammingDist (row0 C) (row2 C)) ∧ Odd (hammingDist (row1 C) (row2 C))) ∨
            (count C 1 = 1 ∧ count C 2 = 0 ∧ count C 4 = 0 ∧ count C 5 = 0 ∧
                count C 7 = 0 ∧ Odd (count C 3) ∧ Odd (count C 6)) ∨
            (count C 1 = 1 ∧ count C 2 = 0 ∧ count C 4 = 0 ∧ count C 6 = 0 ∧
                count C 7 = 0 ∧ Odd (count C 3) ∧ Odd (count C 5)) := hflip.2
        have hne : ¬ UniversalEqual C₁ C := by
          intro heq
          rcases heqiff.mp heq with hi | hii | hiii
          · rcases hi with ⟨hA, hB⟩
            rcases hA with ⟨a, ha⟩
            rcases hw03 with ⟨b, hb⟩
            omega
          · rcases hii with ⟨_h1, _h2, _h4, h5z, _h7, _h3o, _h6o⟩
            rcases h5o with ⟨k, hk⟩
            omega
          · rcases hiii with ⟨_h1, _h2, _h4, _h6, h7z, _h3o, _h5o⟩
            rw [h7eq] at h7z
            norm_num at h7z
        have hnotempty : ¬ ∀ y : Word n, ¬ Y3 C t y := by
          intro hy
          exact hne (heqiff.mpr ((Y3_empty_iff C t ht1 hwC h07).mp hy))
        have hY3 : ∃ y : Word n, Y3 C t y := by
          by_contra hnone
          apply hnotempty
          intro y hy
          exact hnone ⟨y, hy⟩
        have hstrict : UniversalStrictBetter C₁ C :=
          one_bit_flip_strict C C₁ t ht1 hcol₁ hsame₁ hwC hY3
        exfalso
        exact hnoStrict C₁ hstrict
    · -- |5| even: Condition-A forces |3| odd; C is equivalent (rho15, types
      -- 3↔5) to a Class-III-a code
      have h3o : Odd (count C 3) := by
        rcases h35odd with h3o | h5o'
        · exact h3o
        · exact False.elim (h5o h5o')
      have h5e : Even (count C 5) := by
        by_contra hnot
        apply h5o
        exact Nat.not_even_iff_odd.mp hnot
      let D : Code n := rowPermutedCode rho15 C
      have hEq : Equivalent C D := rowPermutedCode_equiv rho15 C
      have hc1D : count D 1 = 1 := by
        rw [count_rowPermutedCode_of_1357 rho15 C 1 1 hS1357 (by
          intro v hv
          simp [Finset.mem_insert, Finset.mem_singleton] at hv
          rcases hv with rfl | rfl | rfl | rfl <;> native_decide)]
        exact h1eq
      have hc7D : count D 7 = 1 := by
        rw [count_rowPermutedCode_of_1357 rho15 C 7 7 hS1357 (by
          intro v hv
          simp [Finset.mem_insert, Finset.mem_singleton] at hv
          rcases hv with rfl | rfl | rfl | rfl <;> native_decide)]
        exact h7eq
      have hc6D : count D 6 = 0 := by
        rw [count_rowPermutedCode_of_1357 rho15 C 6 6 hS1357 (by
          intro v hv
          simp [Finset.mem_insert, Finset.mem_singleton] at hv
          rcases hv with rfl | rfl | rfl | rfl <;> native_decide)]
        exact h6z
      have hc3D : count D 3 = count C 5 := by
        rw [count_rowPermutedCode_of_1357 rho15 C 3 5 hS1357 (by
          intro v hv
          simp [Finset.mem_insert, Finset.mem_singleton] at hv
          rcases hv with rfl | rfl | rfl | rfl <;> native_decide)]
      have hc5D : count D 5 = count C 3 := by
        rw [count_rowPermutedCode_of_1357 rho15 C 5 3 hS1357 (by
          intro v hv
          simp [Finset.mem_insert, Finset.mem_singleton] at hv
          rcases hv with rfl | rfl | rfl | rfl <;> native_decide)]
      have htotD : totalCounts D ({1,3,5,6,7} : Finset ℕ) = n := by
        unfold totalCounts
        simp [Finset.sum_insert, hc6D]
        have htotD1357 : totalCounts D ({1,3,5,7} : Finset ℕ) = n := by
          exact totalCounts_rowPermutedCode_into rho15 C ({1,3,5,7} : Finset ℕ) ({1,3,5,7} : Finset ℕ)
            (by
              have h17 := lm_columns17_total C hcols
              unfold totalCounts
              simp [Finset.sum_insert]
              unfold totalCounts at h17
              simp [Finset.sum_insert] at h17
              omega)
            hS1357
            (by
              intro v hv
              simp [Finset.mem_insert, Finset.mem_singleton] at hv
              rcases hv with rfl | rfl | rfl | rfl <;> native_decide)
        unfold totalCounts at htotD1357
        simp [Finset.sum_insert] at htotD1357
        omega
      exact ⟨D, hEq, Or.inr (Or.inr ⟨htotD,
        Or.inl ⟨hc1D, hc7D, hc6D, by rwa [hc3D], by rwa [hc5D]⟩⟩)⟩
  · have hstrict : UniversalStrictBetter C' C := hb.2.2.mpr hcond
    exfalso
    exact hnoStrict C' hstrict

/-- Lemma `lm:all` (Lemma 15): optimal codes with columns only in types 1..14 are
equivalent to linear, Class-I, Class-II, or Class-III codes (paper §III-D,
p. 148).  (`2 ≤ n` is the
paper's blocklength standing assumption; for `n = 0,1` no linear/Class-I/II/III
code exists and the statement is false.  The `thm:even` (Theorem 8) Case-1 condition (iii)
is handled by the `swapRows01Code` equivalence to Class-III-b, see Notation.md
§4.11.) -/
theorem lm_all (n : ℕ) (hn : 2 ≤ n) (C : Code n)
    (hcols : ∀ t : Fin n, 1 ≤ colVal (C t) ∧ colVal (C t) ≤ 14)
    (hnoStrict : ∀ D : Code n, UniversalStrictBetter D C → False) :
    ∃ C' : Code n, Equivalent C C' ∧
      (IsLinear C' ∨ ClassI C' ∨ ClassII C' ∨ ClassIII C') := by
  let C₁ : Code n := flipHighColumns C
  have hEq1 : Equivalent C C₁ := flipHighColumns_equiv C
  have hnoStrict1 : ∀ D : Code n, UniversalStrictBetter D C₁ → False :=
    noStrict_of_equiv hnoStrict hEq1
  have hcols1 : ∀ t : Fin n, 1 ≤ colVal (C₁ t) ∧ colVal (C₁ t) ≤ 7 := by
    intro t
    have hm := flipHighColumns_mem17 C hcols t
    have hm' : colVal (C₁ t) = 1 ∨ colVal (C₁ t) = 2 ∨ colVal (C₁ t) = 3 ∨ colVal (C₁ t) = 4 ∨
        colVal (C₁ t) = 5 ∨ colVal (C₁ t) = 6 ∨ colVal (C₁ t) = 7 := by
      simpa [Finset.mem_insert, Finset.mem_singleton] using hm
    rcases hm' with hv1 | hv2 | hv3 | hv4 | hv5 | hv6 | hv7 <;> constructor <;> omega
  by_cases hA : count C₁ 1 = 0 ∧ count C₁ 2 = 0 ∧ count C₁ 4 = 0 ∧ count C₁ 7 = 0
  · -- Case 0: |1|=|2|=|4|=|7|=0 → columns in {3,5,6} → linear or strict
    -- contradiction
    have htot1356 : totalCounts C₁ {1,3,5,6} = n :=
      totalCounts_1356_of_mem C₁ (fun t => lm_types_1356 C₁ hcols1 hA.2.1 hA.2.2.1 hA.2.2.2 t)
    by_cases hlin : IsLinear C₁
    · exact ⟨C₁, hEq1, Or.inl hlin⟩
    · rcases degenerate_to_linear_strict C₁ hn htot1356 hA.1 hlin with ⟨D, _hlinD, hstrict⟩
      exfalso
      exact hnoStrict1 D hstrict
  · by_cases hC : (0 < count C₁ 1 ∧ 0 < count C₁ 7) ∨ (0 < count C₁ 2 ∧ 0 < count C₁ 7) ∨
      (0 < count C₁ 4 ∧ 0 < count C₁ 7) ∨ (count C₁ 7 = 0 ∧ 0 < count C₁ 1 ∧ 0 < count C₁ 2) ∨
      (count C₁ 7 = 0 ∧ 0 < count C₁ 1 ∧ 0 < count C₁ 4) ∨
      (count C₁ 7 = 0 ∧ 0 < count C₁ 2 ∧ 0 < count C₁ 4)
    · -- Case 2: at least two of |1|,|2|,|4|,|7| positive
      rcases hC with h17 | h27 | h47 | h12 | h14 | h24
      · rcases lm_caseC_17 C₁ hcols1 h17.1 h17.2 hnoStrict1 with ⟨C', hEq, hcl⟩
        exact ⟨C', equivalent_trans hEq1 hEq, Or.inr hcl⟩
      · rcases lm_caseC_2_reduce C₁ hcols1 h27.1 h27.2 with ⟨Ct, hEqCt, h1', h7', hcolsCt⟩
        rcases lm_caseC_17 Ct hcolsCt h1' h7' (noStrict_of_equiv hnoStrict1 hEqCt) with ⟨C', hEqC', hcl⟩
        exact ⟨C', equivalent_trans hEq1 (equivalent_trans hEqCt hEqC'), Or.inr hcl⟩
      · rcases lm_caseC_4_reduce C₁ hcols1 h47.1 h47.2 with ⟨Ct, hEqCt, h1', h7', hcolsCt⟩
        rcases lm_caseC_17 Ct hcolsCt h1' h7' (noStrict_of_equiv hnoStrict1 hEqCt) with ⟨C', hEqC', hcl⟩
        exact ⟨C', equivalent_trans hEq1 (equivalent_trans hEqCt hEqC'), Or.inr hcl⟩
      · rcases lm_caseC_no7_reduce C₁ hcols1 h12.1 h12.2.1 h12.2.2 with ⟨Ct, hEqCt, h1', h7', hcolsCt⟩
        rcases lm_caseC_17 Ct hcolsCt h1' h7' (noStrict_of_equiv hnoStrict1 hEqCt) with ⟨C', hEqC', hcl⟩
        exact ⟨C', equivalent_trans hEq1 (equivalent_trans hEqCt hEqC'), Or.inr hcl⟩
      · rcases lm_caseC_14_reduce C₁ hcols1 h14.1 h14.2.1 h14.2.2 with ⟨Ct, hEqCt, h1', h2', h7zCt, hcolsCt⟩
        rcases lm_caseC_no7_reduce Ct hcolsCt h7zCt h1' h2' with ⟨Ct2, hEqCt2, h1'', h7'', hcolsCt2⟩
        rcases lm_caseC_17 Ct2 hcolsCt2 h1'' h7''
          (noStrict_of_equiv hnoStrict1 (equivalent_trans hEqCt hEqCt2)) with ⟨C', hEqC', hcl⟩
        exact ⟨C', equivalent_trans hEq1 (equivalent_trans (equivalent_trans hEqCt hEqCt2) hEqC'), Or.inr hcl⟩
      · rcases lm_caseC_24_reduce C₁ hcols1 h24.1 h24.2.1 h24.2.2 with ⟨Ct, hEqCt, h1', h2', h7zCt, hcolsCt⟩
        rcases lm_caseC_no7_reduce Ct hcolsCt h7zCt h1' h2' with ⟨Ct2, hEqCt2, h1'', h7'', hcolsCt2⟩
        rcases lm_caseC_17 Ct2 hcolsCt2 h1'' h7''
          (noStrict_of_equiv hnoStrict1 (equivalent_trans hEqCt hEqCt2)) with ⟨C', hEqC', hcl⟩
        exact ⟨C', equivalent_trans hEq1 (equivalent_trans (equivalent_trans hEqCt hEqCt2) hEqC'), Or.inr hcl⟩
    · -- Case 1: exactly one of |1|,|2|,|4|,|7| positive
      by_cases h7 : 0 < count C₁ 7
      · have h1z : count C₁ 1 = 0 := by
          by_contra hn1
          have h1p : 0 < count C₁ 1 := by omega
          exact hC (Or.inl ⟨h1p, h7⟩)
        have h2z : count C₁ 2 = 0 := by
          by_contra hn2
          have h2p : 0 < count C₁ 2 := by omega
          exact hC (Or.inr (Or.inl ⟨h2p, h7⟩))
        have h4z : count C₁ 4 = 0 := by
          by_contra hn4
          have h4p : 0 < count C₁ 4 := by omega
          exact hC (Or.inr (Or.inr (Or.inl ⟨h4p, h7⟩)))
        rcases lm_caseB_col7_reduce C₁ hcols1 h7 h1z h2z h4z with ⟨Ct, hEqCt, h1', hcolsCt⟩
        have htotCt : totalCounts Ct {1,3,5,6} = n := totalCounts_1356_of_mem Ct hcolsCt
        rcases lm_case1 Ct htotCt h1' (noStrict_of_equiv hnoStrict1 hEqCt) with ⟨C', hEqC', hcl⟩
        exact ⟨C', equivalent_trans hEq1 (equivalent_trans hEqCt hEqC'), Or.inr hcl⟩
      · have h7z : count C₁ 7 = 0 := by omega
        by_cases h1 : 0 < count C₁ 1
        · have h2z : count C₁ 2 = 0 := by
            by_contra hn2
            have h2p : 0 < count C₁ 2 := by omega
            exact hC (Or.inr (Or.inr (Or.inr (Or.inl ⟨h7z, h1, h2p⟩))))
          have h4z : count C₁ 4 = 0 := by
            by_contra hn4
            have h4p : 0 < count C₁ 4 := by omega
            exact hC (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h7z, h1, h4p⟩)))))
          have htot : totalCounts C₁ {1,3,5,6} = n :=
            totalCounts_1356_of_mem C₁ (fun t => lm_types_1356 C₁ hcols1 h2z h4z h7z t)
          rcases lm_case1 C₁ htot h1 hnoStrict1 with ⟨C', hEq, hcl⟩
          exact ⟨C', equivalent_trans hEq1 hEq, Or.inr hcl⟩
        · have h1z : count C₁ 1 = 0 := by omega
          by_cases h2 : 0 < count C₁ 2
          · have h4z : count C₁ 4 = 0 := by
              by_contra hn4
              have h4p : 0 < count C₁ 4 := by omega
              exact hC (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h7z, h2, h4p⟩)))))
            rcases lm_caseB_col2_reduce C₁ hcols1 h2 h1z h4z h7z with ⟨Ct, hEqCt, h1', hcolsCt⟩
            have htotCt : totalCounts Ct {1,3,5,6} = n := totalCounts_1356_of_mem Ct hcolsCt
            rcases lm_case1 Ct htotCt h1' (noStrict_of_equiv hnoStrict1 hEqCt) with ⟨C', hEqC', hcl⟩
            exact ⟨C', equivalent_trans hEq1 (equivalent_trans hEqCt hEqC'), Or.inr hcl⟩
          · have h2z : count C₁ 2 = 0 := by omega
            by_cases h4 : 0 < count C₁ 4
            · rcases lm_caseB_col4_reduce C₁ hcols1 h4 h1z h2z h7z with ⟨Ct, hEqCt, h1', hcolsCt⟩
              have htotCt : totalCounts Ct {1,3,5,6} = n := totalCounts_1356_of_mem Ct hcolsCt
              rcases lm_case1 Ct htotCt h1' (noStrict_of_equiv hnoStrict1 hEqCt) with ⟨C', hEqC', hcl⟩
              exact ⟨C', equivalent_trans hEq1 (equivalent_trans hEqCt hEqC'), Or.inr hcl⟩
            · have h4z : count C₁ 4 = 0 := by omega
              exact False.elim (hA ⟨h1z, h2z, h4z, h7z⟩)

/-- For every ε there is a code maximizing λ at ε (the code space is finite). -/
lemma exists_optimal_code (n : ℕ) (ε : ℝ) : ∃ C : Code n, OptimalAt C ε := by
  rcases Finset.exists_max_image (Finset.univ : Finset (Code n)) (fun C => lambda C ε)
    Finset.univ_nonempty with ⟨C, _, hC⟩
  refine ⟨C, ?_⟩
  intro D
  exact hC D (Finset.mem_univ D)

/-- Every code is equivalent to one whose columns all have type in 0..7. -/
lemma exists_equivalent_columns07 (n : ℕ) (C : Code n) :
    ∃ C' : Code n, Equivalent C C' ∧ Columns07 C' := by
  rcases even_pair C with ⟨i, j, hij, heven⟩
  exact ⟨normalizeCode C i j, Equivalent_normalize C i j, Columns07_normalize C i j hij⟩

/-- Theorem `thm:two` (Theorem 1): for every crossover probability there is an optimal
(n,4) code that is linear or Class-I (paper §2.3, for n ≥ 2). -/
theorem optimal_in_linear_or_class1 (n : ℕ) (hn : 2 ≤ n) :
    ∀ ε : ℝ, 0 < ε → ε < 1 / 2 →
      ∃ C : Code n, (IsLinear C ∨ ClassI C) ∧ OptimalAt C ε := by
  intro ε hε0 hε1
  rcases exists_optimal_code n ε with ⟨Copt, hopt⟩
  rcases reduce_to_linear_or_class1 hn Copt with ⟨C', hlc, hbetter⟩
  refine ⟨C', hlc, ?_⟩
  intro D
  have hb := hbetter ε hε0 hε1
  have ho := hopt D
  linarith

end N4Code
