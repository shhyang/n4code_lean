import N4Code.Reduction
import N4Code.Linear

/-!
# Phase G: Class-I codes (paper §6, `thm:11` (Theorem 16), `thm:301` (Theorem 17))

The analysis of Class-I codes (paper §`sec:classI`): the Y3/Y5
characterizations (eq. c13, eq. c15), the α³(i)/α⁵(i) binomial closed forms
(eq. c1b, eq. y3b, eq. alpha5i), and the cumulative-sum domination arguments
for `thm:11` (Theorem 16) (`class1_one`) and `thm:301` (Theorem 17) (`class1_min`), using
`lemma:cli1` (Lemma 28) (`choose_product_inequality`, proved in `N4Code/Linear.lean`).

The statements are the placeholder stubs in `N4Code/Statements.lean` (§6);
prove them here and replace each stub with a comment pointing back (as done
for the earlier phases).
-/

namespace N4Code

open scoped BigOperators

set_option maxHeartbeats 4000000

/-! ## Characterizations of Y3 and Y5 for a type-1 → type-3 change (eq. c13, c15) -/

/-- eq. c13: y ∈ Y3 iff y₁ = 1, d₄ ≥ d₁∧d₂ and d₁∧d₂ = d₃ (paper §7.1). -/
theorem Y3_iff_col1 {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) (hcol : C t = col1) :
    Y3 C t y ↔ y t = true ∧ dRow C 3 y ≥ min (dRow C 0 y) (dRow C 1 y) ∧
      dRow C 2 y = min (dRow C 0 y) (dRow C 1 y) := by
  constructor
  · intro hy
    have hyt : y t = true := Y3_implies_htrue C t y hcol hy
    have hd2 : dRow C 2 y = min (dRow C 0 y) (min (dRow C 1 y) (dRow C 3 y)) := by
      rcases hy with ⟨_hpp, _hlt, hdP⟩
      unfold dP dO at hdP
      simpa [dRow, row0, row1, row2, row3] using hdP
    rcases Y3_implies_dRow2_eq_dRow0_or_dRow1 C t y hcol hy with hd0 | hd1
    · have hmin : min (dRow C 0 y) (min (dRow C 1 y) (dRow C 3 y)) = dRow C 0 y := by
        rw [← hd2, hd0]
      have hle0 : dRow C 0 y ≤ dRow C 1 y := by
        exact le_trans (min_eq_left_iff.mp hmin) (Nat.min_le_left _ _)
      have hle3 : dRow C 0 y ≤ dRow C 3 y := by
        exact le_trans (min_eq_left_iff.mp hmin) (Nat.min_le_right _ _)
      refine ⟨hyt, ?_, ?_⟩
      · rw [min_eq_left hle0]
        exact hle3
      · rw [min_eq_left hle0]
        exact hd0
    · have hmin : min (dRow C 0 y) (min (dRow C 1 y) (dRow C 3 y)) = dRow C 1 y := by
        rw [← hd2, hd1]
      have hle1 : dRow C 1 y ≤ dRow C 0 y := by
        have hmm := Nat.min_le_left (dRow C 0 y) (min (dRow C 1 y) (dRow C 3 y))
        rw [hmin] at hmm
        exact hmm
      have hle3 : dRow C 1 y ≤ dRow C 3 y := by
        have hmm := Nat.min_le_right (dRow C 0 y) (min (dRow C 1 y) (dRow C 3 y))
        rw [hmin] at hmm
        exact le_trans hmm (Nat.min_le_right _ _)
      refine ⟨hyt, ?_, ?_⟩
      · rw [min_eq_right hle1]
        exact hle3
      · rw [min_eq_right hle1]
        exact hd1
  · intro h
    rcases h with ⟨hyt, hd3ge, hd2min⟩
    constructor
    · have hdPp : dPp C t y = dP C y - 1 := (dPp_eq_col1 C t y hcol).1 hyt
      have hdOp_min : dOp C t y =
          min (dRow C 0 y - 1) (min (dRow C 1 y - 1) (dRow C 3 y + 1)) :=
        dOp_eq_min_col1 C t y hcol hyt
      rw [hdPp, hdOp_min]
      by_cases h01 : dRow C 0 y ≤ dRow C 1 y
      · have hd0 : dRow C 2 y = dRow C 0 y := by
          rw [hd2min, min_eq_left h01]
        have hle0 : dRow C 0 y - 1 ≤ dRow C 1 y - 1 := by omega
        have hle1 : dRow C 0 y - 1 ≤ dRow C 3 y + 1 := by
          have hle : dRow C 0 y ≤ dRow C 3 y := by
            rw [← hd2min, hd0] at hd3ge
            exact hd3ge
          omega
        have hdP0 : dP C y = dRow C 0 y := by
          change dRow C ⟨2, by decide⟩ y = dRow C 0 y
          exact hd0
        rw [hdP0]
        rw [min_eq_left (le_min hle0 hle1)]
      · have h01' : dRow C 1 y < dRow C 0 y := lt_of_not_ge h01
        have hd1 : dRow C 2 y = dRow C 1 y := by
          rw [hd2min, min_eq_right (le_of_lt h01')]
        have hle1 : dRow C 1 y - 1 ≤ dRow C 0 y - 1 := by omega
        have hle2 : dRow C 1 y - 1 ≤ dRow C 3 y + 1 := by
          have hle : dRow C 1 y ≤ dRow C 3 y := by
            rw [← hd2min, hd1] at hd3ge
            exact hd3ge
          omega
        have hdP1 : dP C y = dRow C 1 y := by
          change dRow C ⟨2, by decide⟩ y = dRow C 1 y
          exact hd1
        rw [hdP1]
        have hinner : min (dRow C 1 y - 1) (dRow C 3 y + 1) = dRow C 1 y - 1 :=
          Nat.min_eq_left hle2
        rw [hinner]
        exact (Nat.min_eq_right hle1).symm
    · constructor
      · have hdPp : dPp C t y = dP C y - 1 := (dPp_eq_col1 C t y hcol).1 hyt
        have hdP : dP C y = dRow C 2 y := by
          unfold dP
          rfl
        rw [hdPp, hdP]
        have hge : 1 ≤ dRow C 2 y := by
          unfold dRow
          have hne : y t ≠ row C ⟨2, by decide⟩ t := by
            simp [row, hcol, colBit, col1, hyt]
          exact dRow_ge_one_of_mismatch C ⟨2, by decide⟩ t y hne
        omega
      · have hdP : dP C y = dRow C 2 y := by
          unfold dP
          rfl
        have hdO : dO C y = min (dRow C 0 y) (min (dRow C 1 y) (dRow C 3 y)) := rfl
        rw [hdP, hdO, hd2min]
        rw [← Nat.min_assoc, min_eq_left hd3ge]

/-- eq. c15: y ∈ Y5 iff y₁ = 1, d₁∧d₂ ≥ d₄+2 and d₃ = d₄+1 (paper §7.1). -/
theorem Y5_iff_col1 {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) (hcol : C t = col1) :
    Y5 C t y ↔ y t = true ∧ min (dRow C 0 y) (dRow C 1 y) ≥ dRow C 3 y + 2 ∧
      dRow C 2 y = dRow C 3 y + 1 := by
  constructor
  · intro hy
    rcases hy with ⟨hpp, hop, hlt⟩
    have hyt : y t = true := Y5_implies_htrue C t y hcol ⟨hpp, hop, hlt⟩
    have hdP : dP C y = dRow C 3 y + 1 :=
      Y5_implies_dP_eq_dRow3_add_one C t y hcol ⟨hpp, hop, hlt⟩
    have hdPp : dPp C t y = dP C y - 1 := (dPp_eq_col1 C t y hcol).1 hyt
    have hdO3 : dO C y = dRow C 3 y := by
      rw [← hpp, hdPp, hdP]
      omega
    have hdOp_min : dOp C t y =
        min (dRow C 0 y - 1) (min (dRow C 1 y - 1) (dRow C 3 y + 1)) :=
      dOp_eq_min_col1 C t y hcol hyt
    have hd2 : dRow C 2 y = dRow C 3 y + 1 := by
      unfold dP at hdP
      exact hdP
    have hdO_def : dO C y = min (dRow C 0 y) (min (dRow C 1 y) (dRow C 3 y)) := rfl
    have hm : min (dRow C 0 y) (min (dRow C 1 y) (dRow C 3 y)) = dRow C 3 y := by
      exact hdO_def.symm.trans hdO3
    have hle0 : dRow C 3 y ≤ dRow C 0 y := by
      have hmm := Nat.min_le_left (dRow C 0 y) (min (dRow C 1 y) (dRow C 3 y))
      rw [hm] at hmm
      exact hmm
    have hle1 : dRow C 3 y ≤ dRow C 1 y := by
      have hmm := Nat.min_le_right (dRow C 0 y) (min (dRow C 1 y) (dRow C 3 y))
      rw [hm] at hmm
      exact le_trans hmm (Nat.min_le_left _ _)
    have hge0 : dRow C 3 y + 1 ≤ dRow C 0 y - 1 := by
      have hmm := Nat.min_le_left (dRow C 0 y - 1) (min (dRow C 1 y - 1) (dRow C 3 y + 1))
      rw [← hdOp_min, hop, hdP] at hmm
      exact hmm
    have hge1 : dRow C 3 y + 1 ≤ dRow C 1 y - 1 := by
      have hmm := Nat.min_le_right (dRow C 0 y - 1) (min (dRow C 1 y - 1) (dRow C 3 y + 1))
      rw [← hdOp_min, hop, hdP] at hmm
      exact le_trans hmm (Nat.min_le_left _ _)
    refine ⟨hyt, ?_, hd2⟩
    apply le_min <;> omega
  · intro h
    rcases h with ⟨hyt, hmin, hd2⟩
    have hge0 : dRow C 3 y + 2 ≤ dRow C 0 y := (le_min_iff.mp hmin).1
    have hge1 : dRow C 3 y + 2 ≤ dRow C 1 y := (le_min_iff.mp hmin).2
    have hdO3 : dO C y = dRow C 3 y := by
      rw [show dO C y = min (dRow C 0 y) (min (dRow C 1 y) (dRow C 3 y)) by rfl]
      have h30 : dRow C 3 y ≤ dRow C 0 y := by omega
      have h31 : dRow C 3 y ≤ dRow C 1 y := by omega
      rw [Nat.min_eq_right h31, Nat.min_eq_right h30]
    have hdOp : dOp C t y = dRow C 2 y := by
      rw [dOp_eq_min_col1 C t y hcol hyt]
      have hge0' : dRow C 3 y + 1 ≤ dRow C 0 y - 1 := by omega
      have hge1' : dRow C 3 y + 1 ≤ dRow C 1 y - 1 := by omega
      rw [Nat.min_eq_right hge1', Nat.min_eq_right hge0', hd2]
    constructor
    · have hdPp : dPp C t y = dP C y - 1 := (dPp_eq_col1 C t y hcol).1 hyt
      have hdP : dP C y = dRow C 2 y := by
        unfold dP
        rfl
      rw [hdPp, hdP, hd2, hdO3]
      omega
    · constructor
      · rw [hdOp]
        unfold dP
        rfl
      · rw [hdO3, hdOp]
        omega

/-! ## Distance values on Y3 / Y5 for a type-1 → type-3 change -/

/-- On `Y3`, the old-code distance is attained by row 2 (paper §7.1). -/
lemma dCode_eq_dRow2_of_Y3_col1 {n : ℕ} (C : Code n) (t : Fin n) (y : Word n)
    (hcol : C t = col1) (hy : Y3 C t y) : dCode C y = dRow C 2 y := by
  have h := (Y3_iff_col1 C t y hcol).1 hy
  rcases h with ⟨_hyt, hd3ge, hd2min⟩
  rw [dCode_eq_min_dO_dP C y]
  have hdO : dO C y = dRow C 2 y := by
    change min (dRow C 0 y) (min (dRow C 1 y) (dRow C 3 y)) = dRow C 2 y
    have hminle : min (dRow C 0 y) (dRow C 1 y) ≤ dRow C 3 y := hd3ge
    rw [← min_assoc]
    rw [min_eq_left hminle]
    rw [← hd2min]
  have hdP : dP C y = dRow C 2 y := rfl
  rw [hdO, hdP]
  simp

/-- On `Y5`, the old-code distance is attained by row 3 (paper §7.1). -/
lemma dCode_eq_dRow3_of_Y5_col1 {n : ℕ} (C : Code n) (t : Fin n) (y : Word n)
    (hcol : C t = col1) (hy : Y5 C t y) : dCode C y = dRow C 3 y := by
  have h := (Y5_iff_col1 C t y hcol).1 hy
  rcases h with ⟨_hyt, hmin, hd2⟩
  rw [dCode_eq_min_dO_dP C y]
  have hdO : dO C y = dRow C 3 y := by
    change min (dRow C 0 y) (min (dRow C 1 y) (dRow C 3 y)) = dRow C 3 y
    have hd0 : dRow C 3 y ≤ dRow C 0 y := by
      have h0 : dRow C 3 y + 2 ≤ dRow C 0 y := (le_min_iff.mp hmin).1
      omega
    have hd1 : dRow C 3 y ≤ dRow C 1 y := by
      have h1 : dRow C 3 y + 2 ≤ dRow C 1 y := (le_min_iff.mp hmin).2
      omega
    rw [min_eq_right hd1, min_eq_right hd0]
  have hdP : dP C y = dRow C 3 y + 1 := by
    change dRow C 2 y = dRow C 3 y + 1
    exact hd2
  rw [hdO, hdP]
  exact min_eq_left (Nat.le_succ _)

/-! ## Class-I distance formulas (§7.1)

For a code whose columns all have types in `{1,3,5,6}`, the four row
distances `d₀, d₁, d₂, d₃` are linear forms in the per-type weights
`w₁,w₃,w₅,w₆`.  These are the paper's eqs. (d1)–(d4) instantiated to the
Class-I column set; they are the input to the α³/α⁵ closed forms.
-/

/-- A column type outside `{1,3,5,6}` has count zero when all columns are in
that set. -/
lemma count_eq_zero_of_not_type1356 {n : ℕ} (C : Code n)
    (htypes : ∀ t : Fin n, colVal (C t) = 1 ∨ colVal (C t) = 3 ∨
      colVal (C t) = 5 ∨ colVal (C t) = 6) {i : ℕ}
    (h1 : i ≠ 1) (h3 : i ≠ 3) (h5 : i ≠ 5) (h6 : i ≠ 6) :
    count C i = 0 := by
  by_contra hc
  have hpos : 0 < count C i := Nat.pos_of_ne_zero hc
  rcases (count_pos_iff_exists C i).1 hpos with ⟨t, ht⟩
  have htype : i = 1 ∨ i = 3 ∨ i = 5 ∨ i = 6 := by
    simpa [ht] using htypes t
  rcases htype with hi1 | hi3 | hi5 | hi6
  · exact h1 hi1
  · exact h3 hi3
  · exact h5 hi5
  · exact h6 hi6

/-- The four row distances of a `{1,3,5,6}` code, in terms of the per-type
weights (paper eqs. (d1)–(d4) restricted to Class-I columns). -/
-- native_decide: Mechanical · n=any · checked 2026-08-25
lemma dRow0_of_type1356 {n : ℕ} (C : Code n)
    (htypes : ∀ t : Fin n, colVal (C t) = 1 ∨ colVal (C t) = 3 ∨
      colVal (C t) = 5 ∨ colVal (C t) = 6) (y : Word n) :
    dRow C 0 y = w_i C 1 y + w_i C 3 y + w_i C 5 y + w_i C 6 y := by
  rw [dRow_eq_sum C (0 : Fin 4) y]
  change (∑ i ∈ Finset.Icc 0 15,
      if i.testBit 3 then count C i - w_i C i y else w_i C i y) =
    w_i C 1 y + w_i C 3 y + w_i C 5 y + w_i C 6 y
  have hsub : ({1, 3, 5, 6} : Finset ℕ) ⊆ Finset.Icc 0 15 := by native_decide
  have hzero : ∀ i ∈ Finset.Icc 0 15, i ∉ ({1, 3, 5, 6} : Finset ℕ) →
      (if i.testBit 3 then count C i - w_i C i y else w_i C i y) = 0 := by
    intro i hi hnot
    have h1 : i ≠ 1 := by
      intro h; exact hnot (by simp [h])
    have h3 : i ≠ 3 := by
      intro h; exact hnot (by simp [h])
    have h5 : i ≠ 5 := by
      intro h; exact hnot (by simp [h])
    have h6 : i ≠ 6 := by
      intro h; exact hnot (by simp [h])
    have hc : count C i = 0 := count_eq_zero_of_not_type1356 C htypes h1 h3 h5 h6
    have hw : w_i C i y = 0 := w_i_eq_zero_of_count_zero C i y hc
    by_cases hb : i.testBit 3 <;> simp [hb, hc, hw]
  rw [← Finset.sum_subset hsub hzero]
  simp [Finset.sum_insert, Finset.sum_singleton, Nat.testBit]
  ac_rfl

/-- The four row distances of a `{1,3,5,6}` code, in terms of the per-type
weights (paper eqs. (d1)–(d4) restricted to Class-I columns). -/
-- native_decide: Mechanical · n=any · checked 2026-08-25
lemma dRow1_of_type1356 {n : ℕ} (C : Code n)
    (htypes : ∀ t : Fin n, colVal (C t) = 1 ∨ colVal (C t) = 3 ∨
      colVal (C t) = 5 ∨ colVal (C t) = 6) (y : Word n) :
    dRow C 1 y = w_i C 1 y + w_i C 3 y + (count C 5 - w_i C 5 y) +
      (count C 6 - w_i C 6 y) := by
  rw [dRow_eq_sum C (1 : Fin 4) y]
  change (∑ i ∈ Finset.Icc 0 15,
      if i.testBit 2 then count C i - w_i C i y else w_i C i y) =
    w_i C 1 y + w_i C 3 y + (count C 5 - w_i C 5 y) +
      (count C 6 - w_i C 6 y)
  have hsub : ({1, 3, 5, 6} : Finset ℕ) ⊆ Finset.Icc 0 15 := by native_decide
  have hzero : ∀ i ∈ Finset.Icc 0 15, i ∉ ({1, 3, 5, 6} : Finset ℕ) →
      (if i.testBit 2 then count C i - w_i C i y else w_i C i y) = 0 := by
    intro i hi hnot
    have h1 : i ≠ 1 := by intro h; exact hnot (by simp [h])
    have h3 : i ≠ 3 := by intro h; exact hnot (by simp [h])
    have h5 : i ≠ 5 := by intro h; exact hnot (by simp [h])
    have h6 : i ≠ 6 := by intro h; exact hnot (by simp [h])
    have hc : count C i = 0 := count_eq_zero_of_not_type1356 C htypes h1 h3 h5 h6
    have hw : w_i C i y = 0 := w_i_eq_zero_of_count_zero C i y hc
    by_cases hb : i.testBit 2 <;> simp [hb, hc, hw]
  rw [← Finset.sum_subset hsub hzero]
  simp [Finset.sum_insert, Finset.sum_singleton, Nat.testBit]
  ac_rfl

/-- The four row distances of a `{1,3,5,6}` code, in terms of the per-type
weights (paper eqs. (d1)–(d4) restricted to Class-I columns). -/
-- native_decide: Mechanical · n=any · checked 2026-08-25
lemma dRow2_of_type1356 {n : ℕ} (C : Code n)
    (htypes : ∀ t : Fin n, colVal (C t) = 1 ∨ colVal (C t) = 3 ∨
      colVal (C t) = 5 ∨ colVal (C t) = 6) (y : Word n) :
    dRow C 2 y = w_i C 1 y + (count C 3 - w_i C 3 y) + w_i C 5 y +
      (count C 6 - w_i C 6 y) := by
  rw [dRow_eq_sum C (2 : Fin 4) y]
  change (∑ i ∈ Finset.Icc 0 15,
      if i.testBit 1 then count C i - w_i C i y else w_i C i y) =
    w_i C 1 y + (count C 3 - w_i C 3 y) + w_i C 5 y +
      (count C 6 - w_i C 6 y)
  have hsub : ({1, 3, 5, 6} : Finset ℕ) ⊆ Finset.Icc 0 15 := by native_decide
  have hzero : ∀ i ∈ Finset.Icc 0 15, i ∉ ({1, 3, 5, 6} : Finset ℕ) →
      (if i.testBit 1 then count C i - w_i C i y else w_i C i y) = 0 := by
    intro i hi hnot
    have h1 : i ≠ 1 := by intro h; exact hnot (by simp [h])
    have h3 : i ≠ 3 := by intro h; exact hnot (by simp [h])
    have h5 : i ≠ 5 := by intro h; exact hnot (by simp [h])
    have h6 : i ≠ 6 := by intro h; exact hnot (by simp [h])
    have hc : count C i = 0 := count_eq_zero_of_not_type1356 C htypes h1 h3 h5 h6
    have hw : w_i C i y = 0 := w_i_eq_zero_of_count_zero C i y hc
    by_cases hb : i.testBit 1 <;> simp [hb, hc, hw]
  rw [← Finset.sum_subset hsub hzero]
  simp [Finset.sum_insert, Finset.sum_singleton, Nat.testBit]
  ac_rfl

/-- The four row distances of a `{1,3,5,6}` code, in terms of the per-type
weights (paper eqs. (d1)–(d4) restricted to Class-I columns). -/
-- native_decide: Mechanical · n=any · checked 2026-08-25
lemma dRow3_of_type1356 {n : ℕ} (C : Code n)
    (htypes : ∀ t : Fin n, colVal (C t) = 1 ∨ colVal (C t) = 3 ∨
      colVal (C t) = 5 ∨ colVal (C t) = 6) (y : Word n) :
    dRow C 3 y = (count C 1 - w_i C 1 y) + (count C 3 - w_i C 3 y) +
      (count C 5 - w_i C 5 y) + w_i C 6 y := by
  rw [dRow_eq_sum C (3 : Fin 4) y]
  change (∑ i ∈ Finset.Icc 0 15,
      if i.testBit 0 then count C i - w_i C i y else w_i C i y) =
    (count C 1 - w_i C 1 y) + (count C 3 - w_i C 3 y) +
      (count C 5 - w_i C 5 y) + w_i C 6 y
  have hsub : ({1, 3, 5, 6} : Finset ℕ) ⊆ Finset.Icc 0 15 := by native_decide
  have hzero : ∀ i ∈ Finset.Icc 0 15, i ∉ ({1, 3, 5, 6} : Finset ℕ) →
      (if i.testBit 0 then count C i - w_i C i y else w_i C i y) = 0 := by
    intro i hi hnot
    have h1 : i ≠ 1 := by intro h; exact hnot (by simp [h])
    have h3 : i ≠ 3 := by intro h; exact hnot (by simp [h])
    have h5 : i ≠ 5 := by intro h; exact hnot (by simp [h])
    have h6 : i ≠ 6 := by intro h; exact hnot (by simp [h])
    have hc : count C i = 0 := count_eq_zero_of_not_type1356 C htypes h1 h3 h5 h6
    have hw : w_i C i y = 0 := w_i_eq_zero_of_count_zero C i y hc
    by_cases hb : i.testBit 0 <;> simp [hb, hc, hw]
  rw [← Finset.sum_subset hsub hzero]
  simp [Finset.sum_insert, Finset.sum_singleton, Nat.testBit]
  ac_rfl

/-! ## Binomial fiber counts for `{1,3,5,6}` codes -/

/-- Words with prescribed weights `(1, k3, k5, k6)` on types `(1,3,5,6)` are
counted by the product of the three linear-type binomials. -/
-- native_decide: Mechanical · n=any · checked 2026-08-25
lemma goodWords_card_1356 {n : ℕ} (C : Code n)
    (htypes : ∀ t : Fin n, colVal (C t) = 1 ∨ colVal (C t) = 3 ∨
      colVal (C t) = 5 ∨ colVal (C t) = 6)
    (h1 : count C 1 = 1) (k3 k5 k6 : ℕ) :
    (GoodWords C (fun i => if i = 1 then 1 else if i = 3 then k3 else
      if i = 5 then k5 else if i = 6 then k6 else 0)).card =
      Nat.choose (count C 3) k3 * Nat.choose (count C 5) k5 * Nat.choose (count C 6) k6 := by
  let k : ℕ → ℕ := fun i => if i = 1 then 1 else if i = 3 then k3 else
    if i = 5 then k5 else if i = 6 then k6 else 0
  rw [goodWords_card C k, goodTuples_card C k]
  have hsub : ({1, 3, 5, 6} : Finset ℕ) ⊆ Finset.Icc 0 15 := by native_decide
  have hzero : ∀ i ∈ Finset.Icc 0 15, i ∉ ({1, 3, 5, 6} : Finset ℕ) →
      Nat.choose (count C i) (k i) = 1 := by
    intro i hi hnot
    have h1' : i ≠ 1 := by intro h; exact hnot (by simp [h])
    have h3 : i ≠ 3 := by intro h; exact hnot (by simp [h])
    have h5 : i ≠ 5 := by intro h; exact hnot (by simp [h])
    have h6 : i ≠ 6 := by intro h; exact hnot (by simp [h])
    have hc : count C i = 0 := count_eq_zero_of_not_type1356 C htypes h1' h3 h5 h6
    have hk : k i = 0 := by simp [k, h1', h3, h5, h6]
    simp [hc, hk]
  rw [← Finset.prod_subset hsub hzero]
  change (∏ i ∈ ({1, 3, 5, 6} : Finset ℕ), Nat.choose (count C i) (k i)) =
    Nat.choose (count C 3) k3 * Nat.choose (count C 5) k5 * Nat.choose (count C 6) k6
  simp [Finset.prod_insert, Finset.prod_singleton, k, h1]
  ring

/-- Membership in the type-`(1,3,5,6)` weight fiber is the conjunction of the
four weight equalities; the remaining types vanish because their counts are
zero. -/
-- native_decide: Mechanical · n=any · checked 2026-08-25
lemma goodWord_iff_1356 {n : ℕ} (C : Code n)
    (htypes : ∀ t : Fin n, colVal (C t) = 1 ∨ colVal (C t) = 3 ∨
      colVal (C t) = 5 ∨ colVal (C t) = 6)
    (w3 w5 w6 : ℕ) (y : Word n) :
    y ∈ GoodWords C (fun i => if i = 1 then 1 else if i = 3 then w3 else
      if i = 5 then w5 else if i = 6 then w6 else 0) ↔
      w_i C 1 y = 1 ∧ w_i C 3 y = w3 ∧ w_i C 5 y = w5 ∧ w_i C 6 y = w6 := by
  let k : ℕ → ℕ := fun i => if i = 1 then 1 else if i = 3 then w3 else
    if i = 5 then w5 else if i = 6 then w6 else 0
  rw [goodWord_iff]
  constructor
  · intro h
    refine ⟨h 1 (by native_decide), h 3 (by native_decide), h 5 (by native_decide),
      h 6 (by native_decide)⟩
  · intro h
    rcases h with ⟨h1, h3, h5, h6⟩
    intro i hi
    by_cases hi1 : i = 1
    · subst i
      simpa [k] using h1
    · by_cases hi3 : i = 3
      · subst i
        simpa [k] using h3
      · by_cases hi5 : i = 5
        · subst i
          simpa [k] using h5
        · by_cases hi6 : i = 6
          · subst i
            simpa [k] using h6
          · have hc : count C i = 0 := count_eq_zero_of_not_type1356 C htypes hi1 hi3 hi5 hi6
            have hw : w_i C i y = 0 := w_i_eq_zero_of_count_zero C i y hc
            simpa [k, hi1, hi3, hi5, hi6] using hw

/-! ## Weight characterizations of Y3 and Y5 for |1| = 1 (paper §7.1) -/

/-- `Y5` for a `{1,3,5,6}` code with a single type-1 column, as the weight-form
expansion of the paper's `eq:c15` (published (274)): `Y5 = {y₁ = 1,
d₁∧d₂ ≥ d₄+2 = d₃+1}`.  With |1|=1 (so w₁ = 1), the three distance relations
unfold, via (d1)–(d4), to exactly the three conditions below: `d₂ = d₃+1`
gives `|6|+2w₅ = |5|+2w₆` (paper (293)), while `d₀ ≥ d₃+2` and `d₁ ≥ d₃+2`
give `2(w₃+w₅) ≥ |3|+|5|+1` and `2w₃+|6| ≥ |3|+2w₆+1`.  Eliminating w₆ from
the last two via the first recovers the paper's simplified |1|=1 forms
`w₃+w₆ ≥ (|3|+|6|)/2+1` ((294)) and `w₃−w₆ ≥ (|3|−|6|)/2+1` ((304)); when
those divisions are cleared they read with `+2` on the right, and they agree
with the `+1` forms here exactly under the Class-I parity `|3| ≡ |5| ≡ |6|
(mod 2)`.  That parity is not a hypothesis of this lemma, so the `+1` forms,
which are the ones valid for every `{1,3,5,6}` code with |1|=1, are the ones
stated. -/
-- native_decide: Mechanical · n=any · checked 2026-08-25
lemma Y5_iff_weights_count1 {n : ℕ} (C : Code n) (t : Fin n) (y : Word n)
    (htypes : ∀ u : Fin n, colVal (C u) = 1 ∨ colVal (C u) = 3 ∨
      colVal (C u) = 5 ∨ colVal (C u) = 6)
    (h1 : count C 1 = 1) (hcol : C t = col1) :
    Y5 C t y ↔ y t = true ∧
      count C 6 + 2 * w_i C 5 y = count C 5 + 2 * w_i C 6 y ∧
      count C 3 + count C 5 + 1 ≤ 2 * (w_i C 3 y + w_i C 5 y) ∧
      count C 3 + 2 * w_i C 6 y + 1 ≤ 2 * w_i C 3 y + count C 6 := by
  have hw1 (hyt : y t = true) : w_i C 1 y = 1 := by
    exact w_i_eq_of_single C 1 t y h1 (by rw [hcol]; native_decide) hyt
  have hw3le : w_i C 3 y ≤ count C 3 := w_i_le_count C 3 y
  have hw5le : w_i C 5 y ≤ count C 5 := w_i_le_count C 5 y
  have hw6le : w_i C 6 y ≤ count C 6 := w_i_le_count C 6 y
  rw [Y5_iff_col1 C t y hcol]
  constructor
  · intro h
    rcases h with ⟨hyt, hmin, hd2⟩
    have hw1' : w_i C 1 y = 1 := hw1 hyt
    have hd0 : dRow C 0 y = 1 + w_i C 3 y + w_i C 5 y + w_i C 6 y := by
      rw [dRow0_of_type1356 C htypes y, hw1']
    have hd1 : dRow C 1 y =
        1 + w_i C 3 y + (count C 5 - w_i C 5 y) + (count C 6 - w_i C 6 y) := by
      rw [dRow1_of_type1356 C htypes y, hw1']
    have hd2' : dRow C 2 y =
        1 + (count C 3 - w_i C 3 y) + w_i C 5 y + (count C 6 - w_i C 6 y) := by
      rw [dRow2_of_type1356 C htypes y, hw1']
    have hd3 : dRow C 3 y =
        (count C 3 - w_i C 3 y) + (count C 5 - w_i C 5 y) + w_i C 6 y := by
      rw [dRow3_of_type1356 C htypes y, hw1', h1]
      simp
    rw [hd0, hd1, hd3] at hmin
    rw [hd2', hd3] at hd2
    have hmin0 := (le_min_iff.mp hmin).1
    have hmin1 := (le_min_iff.mp hmin).2
    refine ⟨hyt, ?_, ?_, ?_⟩
    · omega
    · omega
    · omega
  · intro h
    rcases h with ⟨hyt, heq, hge0, hge1⟩
    have hw1' : w_i C 1 y = 1 := hw1 hyt
    refine ⟨hyt, ?_, ?_⟩
    · rw [dRow0_of_type1356 C htypes y, dRow1_of_type1356 C htypes y,
          dRow3_of_type1356 C htypes y, hw1', h1]
      apply le_min <;> omega
    · rw [dRow2_of_type1356 C htypes y, dRow3_of_type1356 C htypes y, hw1', h1]
      omega

/-- `Y3` for a `{1,3,5,6}` code with a single type-1 column, as the weight-form
expansion of the paper's `eq:c13` (published (271)): `Y3 = {y₁ = 1,
d₄ ≥ d₁∧d₂ = d₃}`.  With |1|=1 (so w₁ = 1), the two cases split on which row
attains the minimum `d₀∧d₁ = d₂`.  For `d₀ ≤ d₁` (equivalently
`2(w₅+w₆) ≤ |5|+|6|`) the conditions are the cleared forms of the paper's
`Y₃ᴬ` equations (281) and (282) (`eq:3yc3`, `eq:3yc4`) with the split
inequality (279) relaxed to include the boundary `d₀ = d₁`; for `d₁ < d₀`
they are the cleared forms of (286) and (287) (`eq:3yd3`, `eq:3yd4`) with the
split inequality (284) made strict.  The `i`-dependent equations (280)/(285),
which fix `d_C(y) = i`, are not part of membership and are absent.  The paper
splits `w₅+w₆ < (|5|+|6|)/2` vs `≥`, so it puts the boundary word
`w₅+w₆ = (|5|+|6|)/2` (where `d₀ = d₁`) in the second branch; here that word
is covered by the first.  The two readings agree under the Class-I parity
`|3| ≡ |5| ≡ |6| (mod 2)`.  The `+1` constants in the third condition of each
case are the cleared forms of (281)/(286) with |1|=1; under the same parity
they coincide with `+2` forms, and the `+1` forms are the ones valid for
every `{1,3,5,6}` code with |1|=1. -/
-- native_decide: Mechanical · n=any · checked 2026-08-26
lemma Y3_iff_weights_count1 {n : ℕ} (C : Code n) (t : Fin n) (y : Word n)
    (htypes : ∀ u : Fin n, colVal (C u) = 1 ∨ colVal (C u) = 3 ∨
      colVal (C u) = 5 ∨ colVal (C u) = 6)
    (h1 : count C 1 = 1) (hcol : C t = col1) :
    Y3 C t y ↔ y t = true ∧
      ((count C 5 + count C 6 ≥ 2 * (w_i C 5 y + w_i C 6 y) ∧
          count C 3 + count C 6 = 2 * (w_i C 3 y + w_i C 6 y) ∧
          count C 3 + count C 5 ≥ 2 * (w_i C 3 y + w_i C 5 y) + 1) ∨
        (2 * (w_i C 5 y + w_i C 6 y) ≥ count C 5 + count C 6 + 1 ∧
          count C 3 + 2 * w_i C 5 y = count C 5 + 2 * w_i C 3 y ∧
          count C 3 + 2 * w_i C 6 y ≥ count C 6 + 2 * w_i C 3 y + 1)) := by
  have hw1 (hyt : y t = true) : w_i C 1 y = 1 := by
    exact w_i_eq_of_single C 1 t y h1 (by rw [hcol]; native_decide) hyt
  have hw3le : w_i C 3 y ≤ count C 3 := w_i_le_count C 3 y
  have hw5le : w_i C 5 y ≤ count C 5 := w_i_le_count C 5 y
  have hw6le : w_i C 6 y ≤ count C 6 := w_i_le_count C 6 y
  rw [Y3_iff_col1 C t y hcol]
  constructor
  · intro h
    rcases h with ⟨hyt, hd3ge, hd2min⟩
    have hw1' : w_i C 1 y = 1 := hw1 hyt
    have hd0 : dRow C 0 y = 1 + w_i C 3 y + w_i C 5 y + w_i C 6 y := by
      rw [dRow0_of_type1356 C htypes y, hw1']
    have hd1 : dRow C 1 y =
        1 + w_i C 3 y + (count C 5 - w_i C 5 y) + (count C 6 - w_i C 6 y) := by
      rw [dRow1_of_type1356 C htypes y, hw1']
    have hd2' : dRow C 2 y =
        1 + (count C 3 - w_i C 3 y) + w_i C 5 y + (count C 6 - w_i C 6 y) := by
      rw [dRow2_of_type1356 C htypes y, hw1']
    have hd3 : dRow C 3 y =
        (count C 3 - w_i C 3 y) + (count C 5 - w_i C 5 y) + w_i C 6 y := by
      rw [dRow3_of_type1356 C htypes y, hw1', h1]
      simp
    by_cases h01 : dRow C 0 y ≤ dRow C 1 y
    · refine ⟨hyt, ?_⟩
      left
      rw [min_eq_left h01] at hd2min
      rw [hd0, hd1, hd3] at hd3ge
      rw [hd2'] at hd2min
      rw [hd0] at hd2min
      exact ⟨by omega, by omega, by omega⟩
    · refine ⟨hyt, ?_⟩
      right
      have h10 : dRow C 1 y < dRow C 0 y := lt_of_not_ge h01
      rw [min_eq_right (le_of_lt h10)] at hd2min
      rw [hd0, hd1, hd3] at hd3ge
      rw [hd2'] at hd2min
      rw [hd1] at hd2min
      exact ⟨by omega, by omega, by omega⟩
  · intro h
    rcases h with ⟨hyt, hcases⟩
    have hw1' : w_i C 1 y = 1 := hw1 hyt
    rcases hcases with hleft | hright
    · refine ⟨hyt, ?_, ?_⟩
      · rw [dRow0_of_type1356 C htypes y, dRow1_of_type1356 C htypes y,
            dRow3_of_type1356 C htypes y, hw1', h1]
        have h01arith : 1 + w_i C 3 y + w_i C 5 y + w_i C 6 y ≤
            1 + w_i C 3 y + (count C 5 - w_i C 5 y) + (count C 6 - w_i C 6 y) := by omega
        rw [min_eq_left h01arith]
        omega
      · rw [dRow0_of_type1356 C htypes y, dRow1_of_type1356 C htypes y,
            dRow2_of_type1356 C htypes y, hw1']
        have h01arith : 1 + w_i C 3 y + w_i C 5 y + w_i C 6 y ≤
            1 + w_i C 3 y + (count C 5 - w_i C 5 y) + (count C 6 - w_i C 6 y) := by omega
        rw [min_eq_left h01arith]
        omega
    · refine ⟨hyt, ?_, ?_⟩
      · rw [dRow0_of_type1356 C htypes y, dRow1_of_type1356 C htypes y,
            dRow3_of_type1356 C htypes y, hw1', h1]
        have h10arith : 1 + w_i C 3 y + (count C 5 - w_i C 5 y) + (count C 6 - w_i C 6 y) <
            1 + w_i C 3 y + w_i C 5 y + w_i C 6 y := by omega
        rw [min_eq_right (le_of_lt h10arith)]
        omega
      · rw [dRow0_of_type1356 C htypes y, dRow1_of_type1356 C htypes y,
            dRow2_of_type1356 C htypes y, hw1']
        have h10arith : 1 + w_i C 3 y + (count C 5 - w_i C 5 y) + (count C 6 - w_i C 6 y) <
            1 + w_i C 3 y + w_i C 5 y + w_i C 6 y := by omega
        rw [min_eq_right (le_of_lt h10arith)]
        omega

/-! ## Closed forms of α³ and α⁵ for |1| = 1 (paper eq. c1b, y3b, alpha5i) -/

/-- The three Y5 weight equations/inequalities, in the division-free form of
`Y5_iff_weights_count1`. -/
abbrev Y5WeightCond {n : ℕ} (C : Code n) (w3 w5 w6 : ℕ) : Prop :=
  count C 6 + 2 * w5 = count C 5 + 2 * w6 ∧
  count C 3 + count C 5 + 1 ≤ 2 * (w3 + w5) ∧
  count C 3 + 2 * w6 + 1 ≤ 2 * w3 + count C 6

/-- `dCode y = d` for a word in Y5, written on the weights `(w3,w5,w6)`. -/
abbrev dRow3WeightEq {n : ℕ} (C : Code n) (w3 w5 w6 d : ℕ) : Prop :=
  (count C 3 - w3) + (count C 5 - w5) + w6 = d

/-- Closed form of α⁵(d) for a `{1,3,5,6}` code with a single type-1 column
(paper `eq:alpha5i` with all divisions cleared).  The three weight variables
range over the type counts, and each admissible triple contributes the
binomial product `C(|3|,w3) C(|5|,w5) C(|6|,w6)`. -/
-- native_decide: Mechanical · n=any · checked 2026-08-27
lemma alpha5_closed_count1 {n : ℕ} (C : Code n) (t : Fin n) (d : ℕ)
    (htypes : ∀ u : Fin n, colVal (C u) = 1 ∨ colVal (C u) = 3 ∨
      colVal (C u) = 5 ∨ colVal (C u) = 6)
    (h1 : count C 1 = 1) (hcol : C t = col1) :
    alpha5 C t d =
      ∑ w3 ∈ Finset.Icc 0 (count C 3),
        ∑ w5 ∈ Finset.Icc 0 (count C 5),
          ∑ w6 ∈ Finset.Icc 0 (count C 6),
            if Y5WeightCond C w3 w5 w6 ∧ dRow3WeightEq C w3 w5 w6 d then
              Nat.choose (count C 3) w3 * Nat.choose (count C 5) w5 *
                Nat.choose (count C 6) w6
            else 0 := by
  unfold alpha5
  let F : ℕ × ℕ × ℕ → Finset (Word n) := fun w => GoodWords C
    (fun i => if i = 1 then 1 else if i = 3 then w.1 else if i = 5 then w.2.1 else
      if i = 6 then w.2.2 else 0)
  let S : Finset (ℕ × ℕ × ℕ) :=
    (Finset.Icc 0 (count C 3)) ×ˢ ((Finset.Icc 0 (count C 5)) ×ˢ (Finset.Icc 0 (count C 6)))
  let W : Finset (ℕ × ℕ × ℕ) := S.filter
    (fun w => Y5WeightCond C w.1 w.2.1 w.2.2 ∧ dRow3WeightEq C w.1 w.2.1 w.2.2 d)
  have hA : (Finset.univ.filter fun y : Word n => Y5 C t y ∧ dCode C y = d) = W.biUnion F := by
    ext y
    constructor
    · intro hy
      rcases (Finset.mem_filter.mp hy).2 with ⟨hy5, hd⟩
      let w3 := w_i C 3 y
      let w5 := w_i C 5 y
      let w6 := w_i C 6 y
      have hyt : y t = true := (Y5_iff_col1 C t y hcol).1 hy5 |>.1
      have hw1 : w_i C 1 y = 1 := w_i_eq_of_single C 1 t y h1 (by rw [hcol]; native_decide) hyt
      have hw3le : w3 ≤ count C 3 := w_i_le_count C 3 y
      have hw5le : w5 ≤ count C 5 := w_i_le_count C 5 y
      have hw6le : w6 ≤ count C 6 := w_i_le_count C 6 y
      have hcond : Y5WeightCond C w3 w5 w6 := by
        rcases (Y5_iff_weights_count1 C t y htypes h1 hcol).1 hy5 with ⟨_hyt, heq, hge0, hge1⟩
        exact ⟨heq, hge0, hge1⟩
      have hdrow : dRow3WeightEq C w3 w5 w6 d := by
        have hdCode : dCode C y = d := hd
        have hdrow3 := dCode_eq_dRow3_of_Y5_col1 C t y hcol hy5
        have hdr3 := dRow3_of_type1356 C htypes y
        rw [hdrow3] at hdCode
        rw [hdr3] at hdCode
        rw [hw1, h1] at hdCode
        simp at hdCode
        exact hdCode
      refine Finset.mem_biUnion.mpr ⟨(w3, (w5, w6)), ?_, ?_⟩
      · refine Finset.mem_filter.mpr ⟨?_, ?_⟩
        · refine Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.zero_le w3, hw3le⟩, ?_⟩
          refine Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.zero_le w5, hw5le⟩,
            Finset.mem_Icc.mpr ⟨Nat.zero_le w6, hw6le⟩⟩
        · exact ⟨hcond, hdrow⟩
      · refine Finset.mem_filter.mpr ⟨Finset.mem_univ y, ?_⟩
        have hgood : y ∈ GoodWords C (fun i => if i = 1 then 1 else if i = 3 then w3 else
          if i = 5 then w5 else if i = 6 then w6 else 0) :=
          (goodWord_iff_1356 C htypes w3 w5 w6 y).2 ⟨hw1, rfl, rfl, rfl⟩
        exact (Finset.mem_filter.mp hgood).2
    · intro hy
      rcases Finset.mem_biUnion.mp hy with ⟨w, hw, hyw⟩
      rcases (Finset.mem_filter.mp hw).2 with ⟨hcond, hdrow⟩
      have hygood := (goodWord_iff_1356 C htypes w.1 w.2.1 w.2.2 y).1 hyw
      rcases hygood with ⟨hw1, hw3, hw5, hw6⟩
      have hyt : y t = true := by
        by_contra hf
        have hf' : y t = false := by
          by_cases hb : y t = true
          · exact False.elim (hf hb)
          · exact Bool.eq_false_of_not_eq_true hb
        have hw0 := w_i_eq_zero_of_single_false C 1 t y h1 (by rw [hcol]; native_decide) hf'
        omega
      have hcond' : Y5WeightCond C (w_i C 3 y) (w_i C 5 y) (w_i C 6 y) := by
        simpa [← hw3, ← hw5, ← hw6] using hcond
      have hy5 : Y5 C t y := (Y5_iff_weights_count1 C t y htypes h1 hcol).2 ⟨hyt, hcond'⟩
      have hd : dCode C y = d := by
        have hdrow3 := dCode_eq_dRow3_of_Y5_col1 C t y hcol hy5
        have hdr3 := dRow3_of_type1356 C htypes y
        rw [hdrow3, hdr3]
        rw [hw1, h1]
        simp
        rw [hw3, hw5, hw6]
        exact hdrow
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ y, ⟨hy5, hd⟩⟩
  rw [hA]
  have hdisj : ((W : Set (ℕ × ℕ × ℕ))).PairwiseDisjoint F := by
    intro a ha b hb hab
    change Disjoint (F a) (F b)
    rw [Finset.disjoint_left]
    intro y hya hyb
    have ha' := (goodWord_iff_1356 C htypes a.1 a.2.1 a.2.2 y).1 hya
    have hb' := (goodWord_iff_1356 C htypes b.1 b.2.1 b.2.2 y).1 hyb
    have h3 : w_i C 3 y = a.1 := ha'.2.1
    have h3' : w_i C 3 y = b.1 := hb'.2.1
    have hab1 : a.1 = b.1 := h3.symm.trans h3'
    have h5 : w_i C 5 y = a.2.1 := ha'.2.2.1
    have h5' : w_i C 5 y = b.2.1 := hb'.2.2.1
    have hab2 : a.2.1 = b.2.1 := h5.symm.trans h5'
    have h6 : w_i C 6 y = a.2.2 := ha'.2.2.2
    have h6' : w_i C 6 y = b.2.2 := hb'.2.2.2
    have hab3 : a.2.2 = b.2.2 := h6.symm.trans h6'
    exact hab (Prod.ext hab1 (Prod.ext hab2 hab3))
  rw [Finset.card_biUnion hdisj]
  simp [W, S, F, Finset.sum_filter, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro w3 hw3
  apply Finset.sum_congr rfl
  intro w5 hw5
  apply Finset.sum_congr rfl
  intro w6 hw6
  by_cases hcond : Y5WeightCond C w3 w5 w6 ∧ dRow3WeightEq C w3 w5 w6 d
  · rw [if_pos hcond, if_pos hcond]
    rw [goodWords_card_1356 C htypes h1 w3 w5 w6]
  · rw [if_neg hcond, if_neg hcond]

/-- The two Y3 weight cases, in the division-free form of `Y3_iff_weights_count1`. -/
abbrev Y3WeightCondA {n : ℕ} (C : Code n) (w3 w5 w6 : ℕ) : Prop :=
  count C 5 + count C 6 ≥ 2 * (w5 + w6) ∧
  count C 3 + count C 6 = 2 * (w3 + w6) ∧
  count C 3 + count C 5 ≥ 2 * (w3 + w5) + 1

/-- The second Y3 weight case, in the division-free form of
`Y3_iff_weights_count1`. -/
abbrev Y3WeightCondB {n : ℕ} (C : Code n) (w3 w5 w6 : ℕ) : Prop :=
  2 * (w5 + w6) ≥ count C 5 + count C 6 + 1 ∧
  count C 3 + 2 * w5 = count C 5 + 2 * w3 ∧
  count C 3 + 2 * w6 ≥ count C 6 + 2 * w3 + 1

/-- `dCode y = d` for a word in Y3, written on the weights `(w3,w5,w6)`. -/
abbrev dRow2WeightEq {n : ℕ} (C : Code n) (w3 w5 w6 d : ℕ) : Prop :=
  1 + (count C 3 - w3) + w5 + (count C 6 - w6) = d

/-- Closed form of α³(d) for a `{1,3,5,6}` code with a single type-1 column
(paper `eq:c1b` and `eq:y3b`, with all divisions cleared). -/
-- native_decide: Mechanical · n=any · checked 2026-08-26
lemma alpha3_closed_count1 {n : ℕ} (C : Code n) (t : Fin n) (d : ℕ)
    (htypes : ∀ u : Fin n, colVal (C u) = 1 ∨ colVal (C u) = 3 ∨
      colVal (C u) = 5 ∨ colVal (C u) = 6)
    (h1 : count C 1 = 1) (hcol : C t = col1) :
    alpha3 C t d =
      ∑ w3 ∈ Finset.Icc 0 (count C 3),
        ∑ w5 ∈ Finset.Icc 0 (count C 5),
          ∑ w6 ∈ Finset.Icc 0 (count C 6),
            if (Y3WeightCondA C w3 w5 w6 ∨ Y3WeightCondB C w3 w5 w6) ∧
                dRow2WeightEq C w3 w5 w6 d then
              Nat.choose (count C 3) w3 * Nat.choose (count C 5) w5 *
                Nat.choose (count C 6) w6
            else 0 := by
  unfold alpha3
  let F : ℕ × ℕ × ℕ → Finset (Word n) := fun w => GoodWords C
    (fun i => if i = 1 then 1 else if i = 3 then w.1 else if i = 5 then w.2.1 else
      if i = 6 then w.2.2 else 0)
  let S : Finset (ℕ × ℕ × ℕ) :=
    (Finset.Icc 0 (count C 3)) ×ˢ ((Finset.Icc 0 (count C 5)) ×ˢ (Finset.Icc 0 (count C 6)))
  let W : Finset (ℕ × ℕ × ℕ) := S.filter
    (fun w => (Y3WeightCondA C w.1 w.2.1 w.2.2 ∨ Y3WeightCondB C w.1 w.2.1 w.2.2) ∧
      dRow2WeightEq C w.1 w.2.1 w.2.2 d)
  have hA : (Finset.univ.filter fun y : Word n => Y3 C t y ∧ dCode C y = d) = W.biUnion F := by
    ext y
    constructor
    · intro hy
      rcases (Finset.mem_filter.mp hy).2 with ⟨hy3, hd⟩
      let w3 := w_i C 3 y
      let w5 := w_i C 5 y
      let w6 := w_i C 6 y
      have hyt : y t = true := (Y3_iff_col1 C t y hcol).1 hy3 |>.1
      have hw1 : w_i C 1 y = 1 := w_i_eq_of_single C 1 t y h1 (by rw [hcol]; native_decide) hyt
      have hw3le : w3 ≤ count C 3 := w_i_le_count C 3 y
      have hw5le : w5 ≤ count C 5 := w_i_le_count C 5 y
      have hw6le : w6 ≤ count C 6 := w_i_le_count C 6 y
      have hcond : Y3WeightCondA C w3 w5 w6 ∨ Y3WeightCondB C w3 w5 w6 := by
        rcases (Y3_iff_weights_count1 C t y htypes h1 hcol).1 hy3 with ⟨_hyt, hcases⟩
        rcases hcases with hA | hB
        · left; exact hA
        · right; exact hB
      have hdrow : dRow2WeightEq C w3 w5 w6 d := by
        have hdCode : dCode C y = d := hd
        have hdrow2 := dCode_eq_dRow2_of_Y3_col1 C t y hcol hy3
        have hdr2 := dRow2_of_type1356 C htypes y
        rw [hdrow2] at hdCode
        rw [hdr2] at hdCode
        rw [hw1] at hdCode
        exact hdCode
      refine Finset.mem_biUnion.mpr ⟨(w3, (w5, w6)), ?_, ?_⟩
      · refine Finset.mem_filter.mpr ⟨?_, ?_⟩
        · refine Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.zero_le w3, hw3le⟩, ?_⟩
          refine Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.zero_le w5, hw5le⟩,
            Finset.mem_Icc.mpr ⟨Nat.zero_le w6, hw6le⟩⟩
        · exact ⟨hcond, hdrow⟩
      · refine Finset.mem_filter.mpr ⟨Finset.mem_univ y, ?_⟩
        have hgood : y ∈ GoodWords C (fun i => if i = 1 then 1 else if i = 3 then w3 else
          if i = 5 then w5 else if i = 6 then w6 else 0) :=
          (goodWord_iff_1356 C htypes w3 w5 w6 y).2 ⟨hw1, rfl, rfl, rfl⟩
        exact (Finset.mem_filter.mp hgood).2
    · intro hy
      rcases Finset.mem_biUnion.mp hy with ⟨w, hw, hyw⟩
      rcases (Finset.mem_filter.mp hw).2 with ⟨hcond, hdrow⟩
      have hygood := (goodWord_iff_1356 C htypes w.1 w.2.1 w.2.2 y).1 hyw
      rcases hygood with ⟨hw1, hw3, hw5, hw6⟩
      have hyt : y t = true := by
        by_contra hf
        have hf' : y t = false := by
          by_cases hb : y t = true
          · exact False.elim (hf hb)
          · exact Bool.eq_false_of_not_eq_true hb
        have hw0 := w_i_eq_zero_of_single_false C 1 t y h1 (by rw [hcol]; native_decide) hf'
        omega
      have hcond' : Y3WeightCondA C (w_i C 3 y) (w_i C 5 y) (w_i C 6 y) ∨
          Y3WeightCondB C (w_i C 3 y) (w_i C 5 y) (w_i C 6 y) := by
        rcases hcond with hA | hB
        · left; simpa [← hw3, ← hw5, ← hw6] using hA
        · right; simpa [← hw3, ← hw5, ← hw6] using hB
      have hy3 : Y3 C t y := (Y3_iff_weights_count1 C t y htypes h1 hcol).2 ⟨hyt, hcond'⟩
      have hd : dCode C y = d := by
        have hdrow2 := dCode_eq_dRow2_of_Y3_col1 C t y hcol hy3
        have hdr2 := dRow2_of_type1356 C htypes y
        rw [hdrow2, hdr2]
        rw [hw1]
        rw [hw3, hw5, hw6]
        exact hdrow
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ y, ⟨hy3, hd⟩⟩
  rw [hA]
  have hdisj : ((W : Set (ℕ × ℕ × ℕ))).PairwiseDisjoint F := by
    intro a ha b hb hab
    change Disjoint (F a) (F b)
    rw [Finset.disjoint_left]
    intro y hya hyb
    have ha' := (goodWord_iff_1356 C htypes a.1 a.2.1 a.2.2 y).1 hya
    have hb' := (goodWord_iff_1356 C htypes b.1 b.2.1 b.2.2 y).1 hyb
    have h3 : w_i C 3 y = a.1 := ha'.2.1
    have h3' : w_i C 3 y = b.1 := hb'.2.1
    have hab1 : a.1 = b.1 := h3.symm.trans h3'
    have h5 : w_i C 5 y = a.2.1 := ha'.2.2.1
    have h5' : w_i C 5 y = b.2.1 := hb'.2.2.1
    have hab2 : a.2.1 = b.2.1 := h5.symm.trans h5'
    have h6 : w_i C 6 y = a.2.2 := ha'.2.2.2
    have h6' : w_i C 6 y = b.2.2 := hb'.2.2.2
    have hab3 : a.2.2 = b.2.2 := h6.symm.trans h6'
    exact hab (Prod.ext hab1 (Prod.ext hab2 hab3))
  rw [Finset.card_biUnion hdisj]
  simp [W, S, F, Finset.sum_filter, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro w3 hw3
  apply Finset.sum_congr rfl
  intro w5 hw5
  apply Finset.sum_congr rfl
  intro w6 hw6
  by_cases hcond : (Y3WeightCondA C w3 w5 w6 ∨ Y3WeightCondB C w3 w5 w6) ∧
      dRow2WeightEq C w3 w5 w6 d
  · rw [if_pos hcond, if_pos hcond]
    rw [goodWords_card_1356 C htypes h1 w3 w5 w6]
  · rw [if_neg hcond, if_neg hcond]

/-! ## `argminType` case-splitting helpers -/

-- native_decide: Mechanical · n=any · checked 2026-08-26
/-- The argmin column is always one of the three linear types. -/
lemma argminType_is_type {n : ℕ} (C : Code n) :
    colVal (argminType C) = 3 ∨ colVal (argminType C) = 5 ∨ colVal (argminType C) = 6 := by
  unfold argminType
  by_cases h1 : count C 3 ≤ count C 5 ∧ count C 3 ≤ count C 6
  · simp [h1]
    left
    native_decide
  · by_cases h2 : count C 5 ≤ count C 6
    · simp [h1, h2]
      right; left; native_decide
    · simp [h1, h2]
      right; right; native_decide

/-- When type 3 is a minimizer, `argminType` picks `col3`. -/
lemma argminType_eq_col3 {n : ℕ} (C : Code n)
    (h : count C 3 ≤ count C 5 ∧ count C 3 ≤ count C 6) : argminType C = col3 := by
  simp [argminType, h]

/-- When type 5 is the strict minimizer, `argminType` picks `col5`. -/
lemma argminType_eq_col5 {n : ℕ} (C : Code n)
    (h : ¬ (count C 3 ≤ count C 5 ∧ count C 3 ≤ count C 6)) (h5 : count C 5 ≤ count C 6) :
    argminType C = col5 := by
  simp [argminType, h, h5]

/-- When type 6 is the strict minimizer, `argminType` picks `col6`. -/
lemma argminType_eq_col6 {n : ℕ} (C : Code n)
    (h : ¬ (count C 3 ≤ count C 5 ∧ count C 3 ≤ count C 6)) (h6 : ¬ count C 5 ≤ count C 6) :
    argminType C = col6 := by
  simp [argminType, h, h6]

/-- Swap rows 2 and 3 (indices 1 and 2): maps type 5 ↔ type 3, and fixes the
linear types 6 and the nonlinear type 1. -/
def swap12 : Equiv (Fin 4) (Fin 4) := Equiv.swap (1 : Fin 4) (2 : Fin 4)

-- native_decide: Mechanical · n=any · checked 2026-08-26
/-- `swap12` sends a type-5 column to a type-3 column. -/
lemma rowPermute_swap12_col5 : rowPermute swap12 col5 = col3 := by native_decide

-- native_decide: Mechanical · n=any · checked 2026-08-26
/-- `swap12` sends a type-3 column to a type-5 column. -/
lemma rowPermute_swap12_col3 : rowPermute swap12 col3 = col5 := by native_decide

-- native_decide: Mechanical · n=any · checked 2026-08-26
/-- `swap12` fixes a type-6 column. -/
lemma rowPermute_swap12_col6 : rowPermute swap12 col6 = col6 := by native_decide

-- native_decide: Mechanical · n=any · checked 2026-08-26
/-- `swap12` fixes a type-1 column. -/
lemma rowPermute_swap12_col1 : rowPermute swap12 col1 = col1 := by native_decide

/-- Apply `swap12` to every column. -/
def swap12Code {n : ℕ} (C : Code n) : Code n := fun u => rowPermute swap12 (C u)

/-- `swap12Code C` is equivalent to `C`. -/
lemma Equivalent_swap12Code {n : ℕ} (C : Code n) : Equivalent C (swap12Code C) := by
  refine ⟨swap12, Equiv.refl (Fin n), (fun _ => false), ?_⟩
  intro t
  simp [swap12Code]

-- native_decide: Mechanical · n=any · checked 2026-08-26
/-- `colVal col1 = 1`. -/
lemma colVal_col1 : colVal col1 = 1 := by native_decide

/-- `swap12` turns type-5 columns into type-3 columns, so the counts match. -/
lemma count_swap12Code {n : ℕ} (C : Code n)
    (htypes : ∀ u : Fin n, colVal (C u) = 1 ∨ colVal (C u) = 3 ∨
      colVal (C u) = 5 ∨ colVal (C u) = 6) :
    count (swap12Code C) 3 = count C 5 := by
  unfold count swap12Code
  apply Finset.sum_congr rfl
  intro u _
  rcases htypes u with h1 | h3 | h5 | h6
  · have hc : C u = col1 := (colVal_eq_one_iff_col1 (C u)).1 h1
    simp [hc, rowPermute_swap12_col1, colVal_col1]
  · have hc : C u = col3 := (colVal_eq_three_iff_col3 (C u)).1 h3
    simp [hc, rowPermute_swap12_col3, colVal_col3, colVal_col5]
  · have hc : C u = col5 := (colVal_eq_five_iff_col5 (C u)).1 h5
    simp [hc, rowPermute_swap12_col5, colVal_col3, colVal_col5]
  · have hc : C u = col6 := (colVal_eq_six_iff_col6 (C u)).1 h6
    simp [hc, rowPermute_swap12_col6, colVal_col6]

/-- `swap12` fixes type-1 columns. -/
lemma count_swap12Code_one {n : ℕ} (C : Code n)
    (htypes : ∀ u : Fin n, colVal (C u) = 1 ∨ colVal (C u) = 3 ∨
      colVal (C u) = 5 ∨ colVal (C u) = 6) :
    count (swap12Code C) 1 = count C 1 := by
  unfold count swap12Code
  apply Finset.sum_congr rfl
  intro u _
  rcases htypes u with h1 | h3 | h5 | h6
  · have hc : C u = col1 := (colVal_eq_one_iff_col1 (C u)).1 h1
    simp [hc, rowPermute_swap12_col1, colVal_col1]
  · have hc : C u = col3 := (colVal_eq_three_iff_col3 (C u)).1 h3
    simp [hc, rowPermute_swap12_col3, colVal_col3, colVal_col5]
  · have hc : C u = col5 := (colVal_eq_five_iff_col5 (C u)).1 h5
    simp [hc, rowPermute_swap12_col5, colVal_col3, colVal_col5]
  · have hc : C u = col6 := (colVal_eq_six_iff_col6 (C u)).1 h6
    simp [hc, rowPermute_swap12_col6, colVal_col6]

/-- `swap12` sends type-3 columns to type-5 columns. -/
lemma count_swap12Code_five {n : ℕ} (C : Code n)
    (htypes : ∀ u : Fin n, colVal (C u) = 1 ∨ colVal (C u) = 3 ∨
      colVal (C u) = 5 ∨ colVal (C u) = 6) :
    count (swap12Code C) 5 = count C 3 := by
  unfold count swap12Code
  apply Finset.sum_congr rfl
  intro u _
  rcases htypes u with h1 | h3 | h5 | h6
  · have hc : C u = col1 := (colVal_eq_one_iff_col1 (C u)).1 h1
    simp [hc, rowPermute_swap12_col1, colVal_col1]
  · have hc : C u = col3 := (colVal_eq_three_iff_col3 (C u)).1 h3
    simp [hc, rowPermute_swap12_col3, colVal_col3, colVal_col5]
  · have hc : C u = col5 := (colVal_eq_five_iff_col5 (C u)).1 h5
    simp [hc, rowPermute_swap12_col5, colVal_col3, colVal_col5]
  · have hc : C u = col6 := (colVal_eq_six_iff_col6 (C u)).1 h6
    simp [hc, rowPermute_swap12_col6, colVal_col6]

/-- `swap12` fixes type-6 columns. -/
lemma count_swap12Code_six {n : ℕ} (C : Code n)
    (htypes : ∀ u : Fin n, colVal (C u) = 1 ∨ colVal (C u) = 3 ∨
      colVal (C u) = 5 ∨ colVal (C u) = 6) :
    count (swap12Code C) 6 = count C 6 := by
  unfold count swap12Code
  apply Finset.sum_congr rfl
  intro u _
  rcases htypes u with h1 | h3 | h5 | h6
  · have hc : C u = col1 := (colVal_eq_one_iff_col1 (C u)).1 h1
    simp [hc, rowPermute_swap12_col1, colVal_col1]
  · have hc : C u = col3 := (colVal_eq_three_iff_col3 (C u)).1 h3
    simp [hc, rowPermute_swap12_col3, colVal_col3, colVal_col5]
  · have hc : C u = col5 := (colVal_eq_five_iff_col5 (C u)).1 h5
    simp [hc, rowPermute_swap12_col5, colVal_col3, colVal_col5]
  · have hc : C u = col6 := (colVal_eq_six_iff_col6 (C u)).1 h6
    simp [hc, rowPermute_swap12_col6, colVal_col6]

/-- `swap12Code C` is Class-I whenever `C` is. -/
lemma ClassI_swap12Code {n : ℕ} (C : Code n) (h : ClassI C) : ClassI (swap12Code C) := by
  unfold ClassI
  rcases h with ⟨hodd1, hpar, htotal⟩
  have htypes : ∀ u : Fin n, colVal (C u) = 1 ∨ colVal (C u) = 3 ∨
      colVal (C u) = 5 ∨ colVal (C u) = 6 := by
    intro u
    exact types_1356_of_totalCounts C htotal u
  have hc1 : count (swap12Code C) 1 = count C 1 := count_swap12Code_one C htypes
  have hc3 : count (swap12Code C) 3 = count C 5 := count_swap12Code C htypes
  have hc5 : count (swap12Code C) 5 = count C 3 := count_swap12Code_five C htypes
  have hc6 : count (swap12Code C) 6 = count C 6 := count_swap12Code_six C htypes
  refine ⟨?_, ?_, ?_⟩
  · simpa [hc1] using hodd1
  · rcases hpar with hEven | hOdd
    · left
      exact ⟨by simpa [hc3] using hEven.2.1, by simpa [hc5] using hEven.1, by simpa [hc6] using hEven.2.2⟩
    · right
      exact ⟨by simpa [hc3] using hOdd.2.1, by simpa [hc5] using hOdd.1, by simpa [hc6] using hOdd.2.2⟩
  · unfold totalCounts
    simp [hc1, hc3, hc5, hc6]
    have htot : count C 1 + count C 3 + count C 5 + count C 6 = n := by
      simp [totalCounts] at htotal
      omega
    omega

/-! ## `W5 ⊆ W3'` weight-region sub-proofs (paper `thm:11` (Theorem 16), `n > 4` branch) -/

/-- Division-free form of `𝒲₅(d)` membership (paper `eq:w5prime`): the two
sum/difference constraints are `eq:5yc3` and `eq:5yc5` with all halves
cleared, the third is the `w3` threshold, and the last two are the upper
parts of `0 ≤ w3 ≤ |3|`, `0 ≤ w6 ≤ |6|` (lower bounds are automatic over
`ℕ`). -/
abbrev W5mem {n : ℕ} (C : Code n) (d w3 w6 : ℕ) : Prop :=
  count C 3 + count C 6 + 2 ≤ 2 * (w3 + w6) ∧
  2 * w6 + count C 3 + 2 ≤ 2 * w3 + count C 6 ∧
  n + count C 3 + 1 ≤ 2 * w3 + 2 * d ∧
  w3 ≤ count C 3 ∧ w6 ≤ count C 6

/-- Division-free form of `𝒲₃'(d)` membership (the set displayed immediately
after `eq:113`). -/
abbrev W3primeMem {n : ℕ} (C : Code n) (d w3 w6 : ℕ) : Prop :=
  count C 3 + count C 6 + 2 ≤ 2 * (w3 + w6) ∧
  2 * w6 + count C 3 + 2 ≤ 2 * w3 + count C 6 ∧
  n + count C 3 + 1 ≤ 2 * w3 + 2 * d ∧
  count C 3 ≤ 2 * w3 + count C 6 ∧
  2 * w3 ≤ count C 3 + count C 6 ∧
  count C 6 ≤ 2 * w6 + count C 3 ∧
  2 * w6 ≤ count C 3 + count C 6

/-- Step 1 of `W5 ⊆ W3'`: from `|3| ≤ |6|`, the paper's two preliminary facts
`(|3|-|6|)/2 ≤ 0` and `(|3|+|6|)/2 ≥ |3|`, stated with divisions cleared. -/
lemma class1_W3prime_arith {n : ℕ} (C : Code n) (hle : count C 3 ≤ count C 6) :
    count C 3 ≤ count C 6 ∧ 2 * count C 3 ≤ count C 3 + count C 6 := by
  constructor <;> omega

/-- Step 2 of `W5 ⊆ W3'`: for `(w3,w6) ∈ W5`, isolate the `w6` window
`(|6|-|3|)/2 + 1 ≤ w6 ≤ (|3|+|6|)/2 - 1` (division-free), using `eq:5yc3`,
`eq:5yc5` and `w3 ≤ |3|`. -/
lemma class1_W3prime_w6_window {n : ℕ} (C : Code n) (w3 w6 : ℕ)
    (hsum : count C 3 + count C 6 + 2 ≤ 2 * (w3 + w6))
    (hdiff : 2 * w6 + count C 3 + 2 ≤ 2 * w3 + count C 6)
    (hw3le : w3 ≤ count C 3) :
    count C 6 + 2 ≤ count C 3 + 2 * w6 ∧ 2 * w6 + 2 ≤ count C 3 + count C 6 := by
  constructor <;> omega

/-- Step 3 of `W5 ⊆ W3'`: the `w3` box bounds
`(|3|-|6|)/2 ≤ w3 ≤ (|3|+|6|)/2` (division-free), from `w3 ≤ |3|` and
`|3| ≤ |6|`. -/
lemma class1_W3prime_w3_box {n : ℕ} (C : Code n) (w3 : ℕ)
    (hle : count C 3 ≤ count C 6) (hw3le : w3 ≤ count C 3) :
    count C 3 ≤ 2 * w3 + count C 6 ∧ 2 * w3 ≤ count C 3 + count C 6 := by
  constructor <;> omega

/-- Step 4 of `W5 ⊆ W3'`: the `w6` box bounds
`(|6|-|3|)/2 ≤ w6 ≤ (|3|+|6|)/2` (division-free), from the step-2 window. -/
lemma class1_W3prime_w6_box {n : ℕ} (C : Code n) (w6 : ℕ)
    (hlo : count C 6 + 2 ≤ count C 3 + 2 * w6)
    (hhi : 2 * w6 + 2 ≤ count C 3 + count C 6) :
    count C 6 ≤ 2 * w6 + count C 3 ∧ 2 * w6 ≤ count C 3 + count C 6 := by
  constructor <;> omega

/-- Step 5 of `W5 ⊆ W3'`: assemble the seven `W3'` conditions to prove
`W5 ⊆ W3'` (the paper writes this as `W5 ⊂ W3'`). -/
lemma class1_W5_subset_W3prime {n : ℕ} (C : Code n) (d w3 w6 : ℕ)
    (hle : count C 3 ≤ count C 6) (hW5 : W5mem C d w3 w6) :
    W3primeMem C d w3 w6 := by
  rcases hW5 with ⟨hsum, hdiff, hth, hw3le, hw6le⟩
  have hwin := class1_W3prime_w6_window C w3 w6 hsum hdiff hw3le
  have hw3box := class1_W3prime_w3_box C w3 hle hw3le
  have hw6box := class1_W3prime_w6_box C w6 hwin.1 hwin.2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · omega
  · exact hdiff
  · exact hth
  · exact hw3box.1
  · exact hw3box.2
  · exact hw6box.1
  · exact hw6box.2

/-! ## Cumulative-to-threshold reindexing for α⁵ (`eq:alpha5i` → `eq:115`) -/

/-- The `dRow3` value of a weight triple, with `dRow3 < d` standing for the
cumulative condition `dCode y < d` in the α⁵ reindexing. -/
abbrev dRow3Less {n : ℕ} (C : Code n) (w3 w5 w6 d : ℕ) : Prop :=
  (count C 3 - w3) + (count C 5 - w5) + w6 < d

/-- `dRow2` value of a weight triple with `≤ d` standing for the cumulative
`dCode ≤ d` condition in the α³ B-part reindexing. -/
abbrev dRow2Le {n : ℕ} (C : Code n) (w3 w5 w6 d : ℕ) : Prop :=
  1 + (count C 3 - w3) + w5 + (count C 6 - w6) ≤ d

/-- Summing `[X = i]` over `i < d` gives `[X < d]` (the indicator identity
behind replacing the distance-equals-`i` filter by a distance-below-`d`
filter).  Here `d ≥ 1`, so `Icc 0 (d-1)` is exactly `range d`. -/
lemma sum_ite_eq_lt {d B X : ℕ} (hd : 1 ≤ d) :
    (∑ i ∈ Finset.Icc 0 (d - 1), if X = i then B else 0) = if X < d then B else 0 := by
  by_cases hX : X < d
  · rw [if_pos hX]
    have hmem : X ∈ Finset.Icc 0 (d - 1) := by
      simp [Finset.mem_Icc]
      omega
    calc
      (∑ i ∈ Finset.Icc 0 (d - 1), if X = i then B else 0) = if X = X then B else 0 :=
        Finset.sum_eq_single X (by intro i hi hne; rw [if_neg (by intro h; exact hne h.symm)])
          (by intro hne; exact False.elim (hne hmem))
      _ = B := by simp
  · rw [if_neg hX]
    apply Finset.sum_eq_zero
    intro i hi
    have hi' : i < d := by
      have hle : i ≤ d - 1 := (Finset.mem_Icc.mp hi).2
      omega
    have hne : X ≠ i := by
      intro heq
      have : X < d := by simpa [heq] using hi'
      exact hX this
    rw [if_neg hne]

/-- The same indicator identity with an additional hypothesis `P` that is
independent of the summed index. -/
lemma sum_ite_and_eq_lt {d B : ℕ} (P : Prop) [Decidable P] (X : ℕ) (hd : 1 ≤ d) :
    (∑ i ∈ Finset.Icc 0 (d - 1), if P ∧ X = i then B else 0) =
      if P ∧ X < d then B else 0 := by
  by_cases hP : P
  · calc
      (∑ i ∈ Finset.Icc 0 (d - 1), if P ∧ X = i then B else 0)
          = ∑ i ∈ Finset.Icc 0 (d - 1), if X = i then B else 0 := by
              apply Finset.sum_congr rfl
              intro i hi
              simp [hP]
      _ = if X < d then B else 0 := sum_ite_eq_lt (d := d) (B := B) (X := X) hd
      _ = if P ∧ X < d then B else 0 := by simp [hP]
  · simp [hP]

/-- Summing `[X = i]` over `1 ≤ i ≤ d` gives `[X ≤ d]` (for `X ≥ 1`). -/
lemma sum_ite_eq_le {d B X : ℕ} (hX : 1 ≤ X) :
    (∑ i ∈ Finset.Icc 1 d, if X = i then B else 0) = if X ≤ d then B else 0 := by
  by_cases hXd : X ≤ d
  · rw [if_pos hXd]
    have hmem : X ∈ Finset.Icc 1 d := by
      simp [Finset.mem_Icc, hX, hXd]
    calc
      (∑ i ∈ Finset.Icc 1 d, if X = i then B else 0) = if X = X then B else 0 :=
        Finset.sum_eq_single X (by intro i hi hne; rw [if_neg (by intro h; exact hne h.symm)])
          (by intro hne; exact False.elim (hne hmem))
      _ = B := by simp
  · rw [if_neg hXd]
    apply Finset.sum_eq_zero
    intro i hi
    have hle : i ≤ d := (Finset.mem_Icc.mp hi).2
    have hne : X ≠ i := by
      intro heq
      rw [heq] at hXd
      exact hXd hle
    rw [if_neg hne]

/-- The same indicator identity with an index-independent hypothesis `P`. -/
lemma sum_ite_and_eq_le {d B : ℕ} (P : Prop) [Decidable P] (X : ℕ) (hX : 1 ≤ X) :
    (∑ i ∈ Finset.Icc 1 d, if P ∧ X = i then B else 0) = if P ∧ X ≤ d then B else 0 := by
  by_cases hP : P
  · calc
      (∑ i ∈ Finset.Icc 1 d, if P ∧ X = i then B else 0)
          = ∑ i ∈ Finset.Icc 1 d, if X = i then B else 0 := by
              apply Finset.sum_congr rfl
              intro i hi
              simp [hP]
      _ = if X ≤ d then B else 0 := sum_ite_eq_le (B := B) (X := X) hX
      _ = if P ∧ X ≤ d then B else 0 := by simp [hP]
  · simp [hP]

/-- Commute the three inner sums of a triple sum. -/
lemma sum3_comm {s t u : Finset ℕ} (f : ℕ → ℕ → ℕ → ℕ) :
    (∑ a ∈ s, ∑ b ∈ t, ∑ c ∈ u, f a b c) = ∑ b ∈ t, ∑ c ∈ u, ∑ a ∈ s, f a b c := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Finset.sum_comm]

/-- Collapse `∑_{i < d} α⁵(i)` into a single triple sum over `(w3,w5,w6)`
with the cumulative condition `dRow3 < d` (the first step of the paper's
reduction from `eq:alpha5i` to `eq:115`). -/
lemma alpha5_cumulative_eq_threshold {n : ℕ} (C : Code n) (t : Fin n) (d : ℕ) (hd : 1 ≤ d)
    (htypes : ∀ u : Fin n, colVal (C u) = 1 ∨ colVal (C u) = 3 ∨
      colVal (C u) = 5 ∨ colVal (C u) = 6)
    (h1 : count C 1 = 1) (hcol : C t = col1) :
    (∑ i ∈ Finset.Icc 0 (d - 1), alpha5 C t i) =
      ∑ w3 ∈ Finset.Icc 0 (count C 3),
        ∑ w5 ∈ Finset.Icc 0 (count C 5),
          ∑ w6 ∈ Finset.Icc 0 (count C 6),
            if Y5WeightCond C w3 w5 w6 ∧ dRow3Less C w3 w5 w6 d then
              Nat.choose (count C 3) w3 * Nat.choose (count C 5) w5 *
                Nat.choose (count C 6) w6
            else 0 := by
  let F : ℕ → ℕ → ℕ → ℕ → ℕ := fun i w3 w5 w6 =>
    if Y5WeightCond C w3 w5 w6 ∧ dRow3WeightEq C w3 w5 w6 i then
      Nat.choose (count C 3) w3 * Nat.choose (count C 5) w5 *
        Nat.choose (count C 6) w6
    else 0
  calc
    (∑ i ∈ Finset.Icc 0 (d - 1), alpha5 C t i)
        = ∑ i ∈ Finset.Icc 0 (d - 1),
            ∑ w3 ∈ Finset.Icc 0 (count C 3),
              ∑ w5 ∈ Finset.Icc 0 (count C 5),
                ∑ w6 ∈ Finset.Icc 0 (count C 6), F i w3 w5 w6 := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [alpha5_closed_count1 C t i htypes h1 hcol]
    _ = ∑ w3 ∈ Finset.Icc 0 (count C 3),
          ∑ w5 ∈ Finset.Icc 0 (count C 5),
            ∑ w6 ∈ Finset.Icc 0 (count C 6),
              ∑ i ∈ Finset.Icc 0 (d - 1), F i w3 w5 w6 := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro w3 hw3
          rw [sum3_comm]
    _ = ∑ w3 ∈ Finset.Icc 0 (count C 3),
          ∑ w5 ∈ Finset.Icc 0 (count C 5),
            ∑ w6 ∈ Finset.Icc 0 (count C 6),
              if Y5WeightCond C w3 w5 w6 ∧ dRow3Less C w3 w5 w6 d then
                Nat.choose (count C 3) w3 * Nat.choose (count C 5) w5 *
                  Nat.choose (count C 6) w6
              else 0 := by
          apply Finset.sum_congr rfl; intro w3 hw3
          apply Finset.sum_congr rfl; intro w5 hw5
          apply Finset.sum_congr rfl; intro w6 hw6
          let B : ℕ := Nat.choose (count C 3) w3 * Nat.choose (count C 5) w5 *
            Nat.choose (count C 6) w6
          let X : ℕ := (count C 3 - w3) + (count C 5 - w5) + w6
          have h := sum_ite_and_eq_lt (d := d) (B := B) (P := Y5WeightCond C w3 w5 w6) (X := X) hd
          simpa [F, B, X, dRow3Less, dRow3WeightEq] using h

/-- The unique `w5` forced by the Y5 weight equation `eq:5yc2` (with |1| = 1),
written without signed subtraction. -/
def w5Arg {n : ℕ} (C : Code n) (w6 : ℕ) : ℕ :=
  if count C 5 ≤ count C 6 then w6 - (count C 6 - count C 5) / 2
  else (count C 5 - count C 6) / 2 + w6

/-- The 2D W5 sum of the paper's `eq:115`: the |5| factor is eliminated by
`w5Arg`, so the sum runs only over `(w3,w6)`. -/
def W5Sum {n : ℕ} (C : Code n) (d : ℕ) : ℕ :=
  ∑ w3 ∈ Finset.Icc 0 (count C 3),
    ∑ w6 ∈ Finset.Icc 0 (count C 6),
      if W5mem C d w3 w6 then
        Nat.choose (count C 3) w3 * Nat.choose (count C 5) (w5Arg C w6) *
          Nat.choose (count C 6) w6
      else 0

/-- The Y5 weight equation determines `w5` as `w5Arg C w6`, using the parity of
`|5|` and `|6|` to make the half-difference exact. -/
lemma w5_eq_w5Arg_of_Y5WeightCond {n : ℕ} (C : Code n) (w3 w5 w6 : ℕ)
    (hpar35 : Even (count C 5) ↔ Even (count C 6)) (h : Y5WeightCond C w3 w5 w6) :
    w5 = w5Arg C w6 := by
  have heq : count C 6 + 2 * w5 = count C 5 + 2 * w6 := h.1
  unfold w5Arg
  by_cases h56 : count C 5 ≤ count C 6
  · have hsub_even : Even (count C 6 - count C 5) := by
      exact (Nat.even_sub h56).2 hpar35.symm
    rcases hsub_even with ⟨k, hk⟩
    have hk2 : count C 6 - count C 5 = 2 * k := by omega
    have hdiv : (count C 6 - count C 5) / 2 = k := by
      rw [hk2, Nat.mul_div_right k (by decide : 0 < 2)]
    rw [if_pos h56, hdiv]
    have hw : 2 * w5 = 2 * (w6 - k) := by omega
    have hk_le : k ≤ w6 := by omega
    omega
  · have hsub_even : Even (count C 5 - count C 6) := by
      exact (Nat.even_sub (le_of_lt (lt_of_not_ge h56))).2 hpar35
    rcases hsub_even with ⟨k, hk⟩
    have hk2 : count C 5 - count C 6 = 2 * k := by omega
    have hdiv : (count C 5 - count C 6) / 2 = k := by
      rw [hk2, Nat.mul_div_right k (by decide : 0 < 2)]
    rw [if_neg h56, hdiv]
    have hw : 2 * w5 = 2 * (k + w6) := by omega
    omega

/-- Substituting `w5 = w5Arg C w6` into `count C 5 - w5` gives the weight-free
half-sum expression `(count C 5 + count C 6)/2 - w6` (paper `eq:5yc2` with
|1| = 1). -/
lemma count5_sub_w5Arg_of_eq {n : ℕ} (C : Code n) (w6 : ℕ)
    (hpar35 : Even (count C 5) ↔ Even (count C 6))
    (heq : count C 6 + 2 * w5Arg C w6 = count C 5 + 2 * w6) :
    count C 5 - w5Arg C w6 = (count C 5 + count C 6) / 2 - w6 := by
  unfold w5Arg at heq ⊢
  by_cases h56 : count C 5 ≤ count C 6
  · have hsub_even : Even (count C 6 - count C 5) := (Nat.even_sub h56).2 hpar35.symm
    rcases hsub_even with ⟨k, hk⟩
    have hk2 : count C 6 - count C 5 = 2 * k := by omega
    have hdiv : (count C 6 - count C 5) / 2 = k := by
      rw [hk2, Nat.mul_div_right k (by decide : 0 < 2)]
    rw [if_pos h56, hdiv]
    rw [if_pos h56, hdiv] at heq
    have h6 : count C 6 = count C 5 + 2 * k := by omega
    have hsum2 : (count C 5 + count C 6) / 2 = count C 5 + k := by
      rw [h6]
      rw [show count C 5 + (count C 5 + 2 * k) = 2 * (count C 5 + k) by omega]
      rw [Nat.mul_div_right (count C 5 + k) (by decide : 0 < 2)]
    rw [hsum2]
    omega
  · have hsub_even : Even (count C 5 - count C 6) :=
      (Nat.even_sub (le_of_lt (lt_of_not_ge h56))).2 hpar35
    rcases hsub_even with ⟨k, hk⟩
    have hk2 : count C 5 - count C 6 = 2 * k := by omega
    have hdiv : (count C 5 - count C 6) / 2 = k := by
      rw [hk2, Nat.mul_div_right k (by decide : 0 < 2)]
    rw [if_neg h56, hdiv]
    have h5 : count C 5 = count C 6 + 2 * k := by omega
    have hsum2 : (count C 5 + count C 6) / 2 = count C 6 + k := by
      rw [h5]
      rw [show count C 6 + 2 * k + count C 6 = 2 * (count C 6 + k) by omega]
      rw [Nat.mul_div_right (count C 6 + k) (by decide : 0 < 2)]
    rw [hsum2]
    omega

/-- `w5Arg` is the solution of the Y5 weight equation `eq:5yc2` (with |1| = 1),
under the no-underflow bound on `w6`. -/
lemma w5Arg_eq {n : ℕ} (C : Code n) (w6 : ℕ)
    (hpar35 : Even (count C 5) ↔ Even (count C 6))
    (hw6lo : (count C 6 - count C 5) / 2 ≤ w6) :
    count C 6 + 2 * w5Arg C w6 = count C 5 + 2 * w6 := by
  unfold w5Arg
  by_cases h56 : count C 5 ≤ count C 6
  · have hsub_even : Even (count C 6 - count C 5) := (Nat.even_sub h56).2 hpar35.symm
    rcases hsub_even with ⟨k, hk⟩
    have hk2 : count C 6 - count C 5 = 2 * k := by omega
    have hdiv : (count C 6 - count C 5) / 2 = k := by
      rw [hk2, Nat.mul_div_right k (by decide : 0 < 2)]
    rw [if_pos h56, hdiv]
    have h6 : count C 6 = count C 5 + 2 * k := by omega
    rw [h6]
    omega
  · have hsub_even : Even (count C 5 - count C 6) :=
      (Nat.even_sub (le_of_lt (lt_of_not_ge h56))).2 hpar35
    rcases hsub_even with ⟨k, hk⟩
    have hk2 : count C 5 - count C 6 = 2 * k := by omega
    have hdiv : (count C 5 - count C 6) / 2 = k := by
      rw [hk2, Nat.mul_div_right k (by decide : 0 < 2)]
    rw [if_neg h56, hdiv]
    have h5 : count C 5 = count C 6 + 2 * k := by omega
    rw [h5]
    omega

/-- Under `W5mem` and `|3| ≤ |5|`, the eliminated `w5Arg` is a valid weight
(so it lies in `Icc 0 |5|`). -/
lemma w5Arg_mem_Icc_of_W5mem {n : ℕ} (C : Code n) (d w3 w6 : ℕ)
    (hpar35 : Even (count C 5) ↔ Even (count C 6)) (h35 : count C 3 ≤ count C 5)
    (hw3 : w3 ≤ count C 3) (hW5 : W5mem C d w3 w6) :
    w5Arg C w6 ∈ Finset.Icc 0 (count C 5) := by
  rcases hW5 with ⟨hsum36, hdiff36, _hth, _hw3', _hw6'⟩
  unfold w5Arg
  by_cases h56 : count C 5 ≤ count C 6
  · have hsub_even : Even (count C 6 - count C 5) := (Nat.even_sub h56).2 hpar35.symm
    rcases hsub_even with ⟨k, hk⟩
    have hk2 : count C 6 - count C 5 = 2 * k := by omega
    have h6 : count C 6 = count C 5 + 2 * k := by omega
    have hdiv : (count C 6 - count C 5) / 2 = k := by
      rw [hk2, Nat.mul_div_right k (by decide : 0 < 2)]
    rw [if_pos h56, hdiv]
    simp [Finset.mem_Icc]
    omega
  · have hsub_even : Even (count C 5 - count C 6) :=
      (Nat.even_sub (le_of_lt (lt_of_not_ge h56))).2 hpar35
    rcases hsub_even with ⟨k, hk⟩
    have hk2 : count C 5 - count C 6 = 2 * k := by omega
    have h5 : count C 5 = count C 6 + 2 * k := by omega
    have hdiv : (count C 5 - count C 6) / 2 = k := by
      rw [hk2, Nat.mul_div_right k (by decide : 0 < 2)]
    rw [if_neg h56, hdiv]
    simp [Finset.mem_Icc]
    omega

/-- The unique `w5` forced by the Y3 B-case equation `eq:3yd4` (with |1| = 1),
valid because `|3| ≤ |5|`. -/
def w5ArgY3 {n : ℕ} (C : Code n) (w3 : ℕ) : ℕ :=
  (count C 5 - count C 3) / 2 + w3

/-- The Y3 B-case weight equation determines `w5` as `w5ArgY3 C w3`. -/
lemma w5_eq_w5ArgY3_of_Y3WeightCondB {n : ℕ} (C : Code n) (w3 w5 w6 : ℕ)
    (hpar53 : Even (count C 5) ↔ Even (count C 3)) (h35 : count C 3 ≤ count C 5)
    (h : Y3WeightCondB C w3 w5 w6) :
    w5 = w5ArgY3 C w3 := by
  have heq : count C 3 + 2 * w5 = count C 5 + 2 * w3 := h.2.1
  unfold w5ArgY3
  have hsub_even : Even (count C 5 - count C 3) := (Nat.even_sub h35).2 hpar53
  rcases hsub_even with ⟨k, hk⟩
  have hk2 : count C 5 - count C 3 = 2 * k := by omega
  have hdiv : (count C 5 - count C 3) / 2 = k := by
    rw [hk2, Nat.mul_div_right k (by decide : 0 < 2)]
  rw [hdiv]
  omega

/-- `w5ArgY3 C w3` satisfies the Y3 B-case weight equation `eq:3yd4`. -/
lemma w5ArgY3_eq {n : ℕ} (C : Code n) (w3 : ℕ)
    (hpar53 : Even (count C 5) ↔ Even (count C 3)) (h35 : count C 3 ≤ count C 5) :
    count C 3 + 2 * w5ArgY3 C w3 = count C 5 + 2 * w3 := by
  unfold w5ArgY3
  have hsub_even : Even (count C 5 - count C 3) := (Nat.even_sub h35).2 hpar53
  rcases hsub_even with ⟨k, hk⟩
  have hk2 : count C 5 - count C 3 = 2 * k := by omega
  have hdiv : (count C 5 - count C 3) / 2 = k := by
    rw [hk2, Nat.mul_div_right k (by decide : 0 < 2)]
  rw [hdiv]
  omega

/-- `w5ArgY3 C w3` is a valid weight under `|3| ≤ |5|` and `w3 ≤ |3|`. -/
lemma w5ArgY3_mem_Icc {n : ℕ} (C : Code n) (w3 : ℕ)
    (hpar53 : Even (count C 5) ↔ Even (count C 3)) (h35 : count C 3 ≤ count C 5)
    (hw3 : w3 ≤ count C 3) :
    w5ArgY3 C w3 ∈ Finset.Icc 0 (count C 5) := by
  unfold w5ArgY3
  have hsub_even : Even (count C 5 - count C 3) := (Nat.even_sub h35).2 hpar53
  rcases hsub_even with ⟨k, hk⟩
  have hk2 : count C 5 - count C 3 = 2 * k := by omega
  have hdiv : (count C 5 - count C 3) / 2 = k := by
    rw [hk2, Nat.mul_div_right k (by decide : 0 < 2)]
  rw [hdiv]
  simp [Finset.mem_Icc]
  omega

/-- The |5| factors agree under the reflection `w6 ↦ w3 + (|6|-|3|)/2`. -/
lemma w5Arg_reflect {n : ℕ} (C : Code n) (w3 : ℕ)
    (hpar35 : Even (count C 5) ↔ Even (count C 6))
    (hpar53 : Even (count C 5) ↔ Even (count C 3))
    (h35 : count C 3 ≤ count C 5) (h36 : count C 3 ≤ count C 6) :
    w5Arg C (w3 + (count C 6 - count C 3) / 2) = w5ArgY3 C w3 := by
  unfold w5Arg w5ArgY3
  have hsub53 : Even (count C 5 - count C 3) := (Nat.even_sub h35).2 hpar53
  have hsub63 : Even (count C 6 - count C 3) := (Nat.even_sub h36).2 (hpar35.symm.trans hpar53)
  rcases hsub53 with ⟨k53, hk53⟩
  rcases hsub63 with ⟨k63, hk63⟩
  have hk53' : count C 5 - count C 3 = 2 * k53 := by omega
  have hk63' : count C 6 - count C 3 = 2 * k63 := by omega
  have hdiv53 : (count C 5 - count C 3) / 2 = k53 := by
    rw [hk53', Nat.mul_div_right k53 (by decide : 0 < 2)]
  have hdiv63 : (count C 6 - count C 3) / 2 = k63 := by
    rw [hk63', Nat.mul_div_right k63 (by decide : 0 < 2)]
  rw [hdiv53, hdiv63]
  by_cases h56 : count C 5 ≤ count C 6
  · have hsub65 : Even (count C 6 - count C 5) := (Nat.even_sub h56).2 hpar35.symm
    rcases hsub65 with ⟨k65, hk65⟩
    have hk65' : count C 6 - count C 5 = 2 * k65 := by omega
    have hdiv65 : (count C 6 - count C 5) / 2 = k65 := by
      rw [hk65', Nat.mul_div_right k65 (by decide : 0 < 2)]
    rw [if_pos h56, hdiv65]
    omega
  · have hsub56 : Even (count C 5 - count C 6) :=
      (Nat.even_sub (le_of_lt (lt_of_not_ge h56))).2 hpar35
    rcases hsub56 with ⟨k56, hk56⟩
    have hk56' : count C 5 - count C 6 = 2 * k56 := by omega
    have hdiv56 : (count C 5 - count C 6) / 2 = k56 := by
      rw [hk56', Nat.mul_div_right k56 (by decide : 0 < 2)]
    rw [if_neg h56, hdiv56]
    omega

/-- Same-parity `a` and `b` have even sum. -/
lemma Even_add_of_iff {a b : ℕ} (h : Even a ↔ Even b) : Even (a + b) := by
  by_cases ha : Even a
  · exact Even.add ha (h.mp ha)
  · have hoa : Odd a := Nat.not_even_iff_odd.mp ha
    have hob : Odd b := Nat.not_even_iff_odd.mp (fun hb => ha (h.mpr hb))
    exact Odd.add_odd hoa hob

/-- The `Y5WeightCond ∧ dRow3 < d` condition at a fixed `(w3,w6)` is equivalent
to `w5 = w5Arg` together with the 2D `W5mem` condition (paper `eq:5yc1`–
`eq:5yc5` and `eq:115`, with the threshold from the Class-I blocklength
identity). -/
lemma Y5WeightCond_dRow3Less_iff {n : ℕ} (C : Code n) (d w3 w5 w6 : ℕ)
    (hd : 1 ≤ d) (hpar35 : Even (count C 5) ↔ Even (count C 6))
    (hpar36 : Even (count C 3) ↔ Even (count C 6))
    (htotal : totalCounts C {1, 3, 5, 6} = n) (h1 : count C 1 = 1)
    (h35 : count C 3 ≤ count C 5) (hw3 : w3 ≤ count C 3) (hw5 : w5 ≤ count C 5)
    (hw6 : w6 ≤ count C 6) :
    (Y5WeightCond C w3 w5 w6 ∧ dRow3Less C w3 w5 w6 d) ↔
      (w5 = w5Arg C w6 ∧ W5mem C d w3 w6) := by
  constructor
  · intro h
    rcases h with ⟨hY, hless⟩
    have hw5eq : w5 = w5Arg C w6 := w5_eq_w5Arg_of_Y5WeightCond C w3 w5 w6 hpar35 hY
    refine ⟨hw5eq, ?_⟩
    rcases hY with ⟨heq, hsum3, hdiff3⟩
    have hpar36_sum : Even (count C 3 + count C 6) := Even_add_of_iff hpar36
    rcases hpar36_sum with ⟨k36, hk36⟩
    have hsum36 : count C 3 + count C 6 + 2 ≤ 2 * (w3 + w6) := by omega
    have hdiff36 : 2 * w6 + count C 3 + 2 ≤ 2 * w3 + count C 6 := by omega
    have hth : n + count C 3 + 1 ≤ 2 * w3 + 2 * d := by
      have htot : count C 1 + count C 3 + count C 5 + count C 6 = n := by
        simp [totalCounts] at htotal
        omega
      have hpar56 : Even (count C 5 + count C 6) := Even_add_of_iff hpar35
      rcases hpar56 with ⟨k56, hk56⟩
      have hc5 : count C 5 - w5Arg C w6 = (count C 5 + count C 6) / 2 - w6 := by
        apply count5_sub_w5Arg_of_eq C w6 hpar35
        simpa [hw5eq] using heq
      have hsum56_div : (count C 5 + count C 6) / 2 = k56 := by
        rw [hk56, ← two_mul k56, Nat.mul_div_right k56 (by decide : 0 < 2)]
      have hless' : count C 3 - w3 + k56 < d := by
        have hh : (count C 3 - w3) + (count C 5 - w5) + w6 < d := hless
        rw [hw5eq] at hh
        rw [hc5] at hh
        rw [hsum56_div] at hh
        omega
      have hrel : count C 3 + 2 * k56 = n - 1 := by omega
      have hpar_n : Even (n + count C 3 - 1) := by
        refine ⟨count C 3 + k56, ?_⟩
        omega
      rcases hpar_n with ⟨kn, hkn⟩
      omega
    unfold W5mem
    exact ⟨hsum36, hdiff36, hth, hw3, hw6⟩
  · intro h
    rcases h with ⟨hw5eq, hW5⟩
    rcases hW5 with ⟨hsum36, hdiff36, hth, hw3', hw6'⟩
    refine ⟨?_, ?_⟩
    · unfold Y5WeightCond
      have hwin := class1_W3prime_w6_window C w3 w6 hsum36 hdiff36 hw3
      have hw6lo : (count C 6 - count C 5) / 2 ≤ w6 := by
        by_cases h56 : count C 5 ≤ count C 6
        · have hsub_even : Even (count C 6 - count C 5) := (Nat.even_sub h56).2 hpar35.symm
          rcases hsub_even with ⟨k, hk⟩
          rw [hk, ← two_mul k, Nat.mul_div_right k (by decide : 0 < 2)]
          have hwin1 : count C 6 + 2 ≤ count C 3 + 2 * w6 := hwin.1
          omega
        · rw [Nat.sub_eq_zero_of_le (le_of_lt (lt_of_not_ge h56))]
          simp
      have heq : count C 6 + 2 * w5 = count C 5 + 2 * w6 := by
        rw [hw5eq]
        exact w5Arg_eq C w6 hpar35 hw6lo
      have hsum3 : count C 3 + count C 5 + 1 ≤ 2 * (w3 + w5) := by omega
      have hdiff3 : count C 3 + 2 * w6 + 1 ≤ 2 * w3 + count C 6 := by omega
      exact ⟨heq, hsum3, hdiff3⟩
    · unfold dRow3Less
      have htot : count C 1 + count C 3 + count C 5 + count C 6 = n := by
        simp [totalCounts] at htotal
        omega
      have hpar56 : Even (count C 5 + count C 6) := Even_add_of_iff hpar35
      rcases hpar56 with ⟨k56, hk56⟩
      have hwin := class1_W3prime_w6_window C w3 w6 hsum36 hdiff36 hw3
      have hw6lo : (count C 6 - count C 5) / 2 ≤ w6 := by
        by_cases h56 : count C 5 ≤ count C 6
        · have hsub_even : Even (count C 6 - count C 5) := (Nat.even_sub h56).2 hpar35.symm
          rcases hsub_even with ⟨k, hk⟩
          rw [hk, ← two_mul k, Nat.mul_div_right k (by decide : 0 < 2)]
          have hwin1 : count C 6 + 2 ≤ count C 3 + 2 * w6 := hwin.1
          omega
        · rw [Nat.sub_eq_zero_of_le (le_of_lt (lt_of_not_ge h56))]
          simp
      have heq' : count C 6 + 2 * w5Arg C w6 = count C 5 + 2 * w6 :=
        w5Arg_eq C w6 hpar35 hw6lo
      have hc5 : count C 5 - w5Arg C w6 = (count C 5 + count C 6) / 2 - w6 :=
        count5_sub_w5Arg_of_eq C w6 hpar35 heq'
      have hsum56_div : (count C 5 + count C 6) / 2 = k56 := by
        rw [hk56, ← two_mul k56, Nat.mul_div_right k56 (by decide : 0 < 2)]
      have hrel : count C 3 + 2 * k56 = n - 1 := by omega
      have hpar_n : Even (n + count C 3 - 1) := by
        refine ⟨count C 3 + k56, ?_⟩
        omega
      rcases hpar_n with ⟨kn, hkn⟩
      have hlt : count C 3 - w3 + k56 < d := by omega
      rw [hw5eq, hc5, hsum56_div]
      omega

/-- Collapse the `w5` sum in the α⁵ threshold form to the 2D `W5Sum` (paper
`eq:115`): `w5` is uniquely `w5Arg`, and the remaining conditions are exactly
`W5mem`. -/
lemma alpha5_threshold_eq_W5Sum {n : ℕ} (C : Code n) (d : ℕ) (hd : 1 ≤ d)
    (hpar35 : Even (count C 5) ↔ Even (count C 6))
    (hpar36 : Even (count C 3) ↔ Even (count C 6))
    (htotal : totalCounts C {1, 3, 5, 6} = n) (h1 : count C 1 = 1)
    (h35 : count C 3 ≤ count C 5) :
    (∑ w3 ∈ Finset.Icc 0 (count C 3),
       ∑ w5 ∈ Finset.Icc 0 (count C 5),
         ∑ w6 ∈ Finset.Icc 0 (count C 6),
           if Y5WeightCond C w3 w5 w6 ∧ dRow3Less C w3 w5 w6 d then
             Nat.choose (count C 3) w3 * Nat.choose (count C 5) w5 *
               Nat.choose (count C 6) w6
           else 0)
    = W5Sum C d := by
  unfold W5Sum
  apply Finset.sum_congr rfl; intro w3 hw3
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro w6 hw6
  have hw3le : w3 ≤ count C 3 := (Finset.mem_Icc.mp hw3).2
  have hw6le : w6 ≤ count C 6 := (Finset.mem_Icc.mp hw6).2
  by_cases hW : W5mem C d w3 w6
  · rw [if_pos hW]
    refine (Finset.sum_eq_single (w5Arg C w6) ?_ ?_).trans ?_
    · intro w5 hw5mem hne
      by_cases hcond : Y5WeightCond C w3 w5 w6 ∧ dRow3Less C w3 w5 w6 d
      · have hw5eq : w5 = w5Arg C w6 :=
          w5_eq_w5Arg_of_Y5WeightCond C w3 w5 w6 hpar35 hcond.1
        exact False.elim (hne hw5eq)
      · rw [if_neg hcond]
    · intro hnot
      have hmem : w5Arg C w6 ∈ Finset.Icc 0 (count C 5) :=
        w5Arg_mem_Icc_of_W5mem C d w3 w6 hpar35 h35 hw3le hW
      exact False.elim (hnot hmem)
    · have hcond : Y5WeightCond C w3 (w5Arg C w6) w6 ∧
          dRow3Less C w3 (w5Arg C w6) w6 d := by
        have hmem : w5Arg C w6 ∈ Finset.Icc 0 (count C 5) :=
          w5Arg_mem_Icc_of_W5mem C d w3 w6 hpar35 h35 hw3le hW
        have hw5le : w5Arg C w6 ≤ count C 5 := (Finset.mem_Icc.mp hmem).2
        exact (Y5WeightCond_dRow3Less_iff C d w3 (w5Arg C w6) w6 hd hpar35 hpar36
          htotal h1 h35 hw3le hw5le hw6le).2 ⟨rfl, hW⟩
      rw [if_pos hcond]
  · rw [if_neg hW]
    apply Finset.sum_eq_zero
    intro w5 hw5mem
    by_cases hcond : Y5WeightCond C w3 w5 w6 ∧ dRow3Less C w3 w5 w6 d
    · have hw5le : w5 ≤ count C 5 := (Finset.mem_Icc.mp hw5mem).2
      have hiff := Y5WeightCond_dRow3Less_iff C d w3 w5 w6 hd hpar35 hpar36 htotal h1
        h35 hw3le hw5le hw6le
      have hW' : W5mem C d w3 w6 := (hiff.1 hcond).2
      exact False.elim (hW hW')
    · rw [if_neg hcond]

/-- Cumulative α³ dominates its Y3 B-part, reindexed to a single triple sum
with the cumulative condition `dRow2 ≤ d` (paper `eq:110`, B case of
`eq:y3b`). -/
lemma alpha3_cumulative_ge_threshold_B {n : ℕ} (C : Code n) (t : Fin n) (d : ℕ)
    (htypes : ∀ u : Fin n, colVal (C u) = 1 ∨ colVal (C u) = 3 ∨
      colVal (C u) = 5 ∨ colVal (C u) = 6)
    (h1 : count C 1 = 1) (hcol : C t = col1) :
    (∑ i ∈ Finset.Icc 1 d, alpha3 C t i) ≥
      ∑ w3 ∈ Finset.Icc 0 (count C 3),
        ∑ w5 ∈ Finset.Icc 0 (count C 5),
          ∑ w6 ∈ Finset.Icc 0 (count C 6),
            if Y3WeightCondB C w3 w5 w6 ∧ dRow2Le C w3 w5 w6 d then
              Nat.choose (count C 3) w3 * Nat.choose (count C 5) w5 *
                Nat.choose (count C 6) w6
            else 0 := by
  let B : ℕ → ℕ → ℕ → ℕ := fun w3 w5 w6 =>
    Nat.choose (count C 3) w3 * Nat.choose (count C 5) w5 * Nat.choose (count C 6) w6
  have hpoint : ∀ i : ℕ,
      alpha3 C t i ≥
        ∑ w3 ∈ Finset.Icc 0 (count C 3),
          ∑ w5 ∈ Finset.Icc 0 (count C 5),
            ∑ w6 ∈ Finset.Icc 0 (count C 6),
              if Y3WeightCondB C w3 w5 w6 ∧ dRow2WeightEq C w3 w5 w6 i then B w3 w5 w6
              else 0 := by
    intro i
    rw [alpha3_closed_count1 C t i htypes h1 hcol]
    apply Finset.sum_le_sum; intro w3 hw3
    apply Finset.sum_le_sum; intro w5 hw5
    apply Finset.sum_le_sum; intro w6 hw6
    by_cases hB : Y3WeightCondB C w3 w5 w6 ∧ dRow2WeightEq C w3 w5 w6 i
    · rw [if_pos hB]
      rw [if_pos (show (Y3WeightCondA C w3 w5 w6 ∨ Y3WeightCondB C w3 w5 w6) ∧
          dRow2WeightEq C w3 w5 w6 i from ⟨Or.inr hB.1, hB.2⟩)]
    · rw [if_neg hB]
      exact Nat.zero_le _
  calc
    (∑ i ∈ Finset.Icc 1 d, alpha3 C t i) ≥
        ∑ i ∈ Finset.Icc 1 d,
          ∑ w3 ∈ Finset.Icc 0 (count C 3),
            ∑ w5 ∈ Finset.Icc 0 (count C 5),
              ∑ w6 ∈ Finset.Icc 0 (count C 6),
                if Y3WeightCondB C w3 w5 w6 ∧ dRow2WeightEq C w3 w5 w6 i then B w3 w5 w6
                else 0 := by
      apply Finset.sum_le_sum
      intro i hi
      exact hpoint i
    _ = ∑ w3 ∈ Finset.Icc 0 (count C 3),
          ∑ w5 ∈ Finset.Icc 0 (count C 5),
            ∑ w6 ∈ Finset.Icc 0 (count C 6),
              ∑ i ∈ Finset.Icc 1 d,
                if Y3WeightCondB C w3 w5 w6 ∧ dRow2WeightEq C w3 w5 w6 i then B w3 w5 w6
                else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro w3 hw3
      rw [sum3_comm]
    _ = ∑ w3 ∈ Finset.Icc 0 (count C 3),
          ∑ w5 ∈ Finset.Icc 0 (count C 5),
            ∑ w6 ∈ Finset.Icc 0 (count C 6),
              if Y3WeightCondB C w3 w5 w6 ∧ dRow2Le C w3 w5 w6 d then B w3 w5 w6
              else 0 := by
      apply Finset.sum_congr rfl; intro w3 hw3
      apply Finset.sum_congr rfl; intro w5 hw5
      apply Finset.sum_congr rfl; intro w6 hw6
      let X : ℕ := 1 + (count C 3 - w3) + w5 + (count C 6 - w6)
      have hX : 1 ≤ X := by omega
      have h := sum_ite_and_eq_le (d := d) (B := B w3 w5 w6)
        (P := Y3WeightCondB C w3 w5 w6) (X := X) hX
      simpa [X, dRow2Le, dRow2WeightEq, B] using h

/-- The cumulative α³ sum is exactly the weight-sum over both Y3 branches
(`Y3WeightCondA ∨ Y3WeightCondB` with `dRow2 ≤ d`). -/
lemma alpha3_cumulative_eq_threshold_AB {n : ℕ} (C : Code n) (t : Fin n) (d : ℕ)
    (htypes : ∀ u : Fin n, colVal (C u) = 1 ∨ colVal (C u) = 3 ∨
      colVal (C u) = 5 ∨ colVal (C u) = 6)
    (h1 : count C 1 = 1) (hcol : C t = col1) :
    (∑ i ∈ Finset.Icc 1 d, alpha3 C t i) =
      ∑ w3 ∈ Finset.Icc 0 (count C 3),
        ∑ w5 ∈ Finset.Icc 0 (count C 5),
          ∑ w6 ∈ Finset.Icc 0 (count C 6),
            if (Y3WeightCondA C w3 w5 w6 ∨ Y3WeightCondB C w3 w5 w6) ∧
                dRow2Le C w3 w5 w6 d then
              Nat.choose (count C 3) w3 * Nat.choose (count C 5) w5 *
                Nat.choose (count C 6) w6
            else 0 := by
  let B : ℕ → ℕ → ℕ → ℕ := fun w3 w5 w6 =>
    Nat.choose (count C 3) w3 * Nat.choose (count C 5) w5 * Nat.choose (count C 6) w6
  have hpoint : ∀ i : ℕ,
      alpha3 C t i =
        ∑ w3 ∈ Finset.Icc 0 (count C 3),
          ∑ w5 ∈ Finset.Icc 0 (count C 5),
            ∑ w6 ∈ Finset.Icc 0 (count C 6),
              if (Y3WeightCondA C w3 w5 w6 ∨ Y3WeightCondB C w3 w5 w6) ∧
                  dRow2WeightEq C w3 w5 w6 i then B w3 w5 w6
              else 0 := by
    intro i
    rw [alpha3_closed_count1 C t i htypes h1 hcol]
  calc
    (∑ i ∈ Finset.Icc 1 d, alpha3 C t i) =
        ∑ i ∈ Finset.Icc 1 d,
          ∑ w3 ∈ Finset.Icc 0 (count C 3),
            ∑ w5 ∈ Finset.Icc 0 (count C 5),
              ∑ w6 ∈ Finset.Icc 0 (count C 6),
                if (Y3WeightCondA C w3 w5 w6 ∨ Y3WeightCondB C w3 w5 w6) ∧
                    dRow2WeightEq C w3 w5 w6 i then B w3 w5 w6
                else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hpoint i
    _ = ∑ w3 ∈ Finset.Icc 0 (count C 3),
          ∑ w5 ∈ Finset.Icc 0 (count C 5),
            ∑ w6 ∈ Finset.Icc 0 (count C 6),
              ∑ i ∈ Finset.Icc 1 d,
                if (Y3WeightCondA C w3 w5 w6 ∨ Y3WeightCondB C w3 w5 w6) ∧
                    dRow2WeightEq C w3 w5 w6 i then B w3 w5 w6
                else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro w3 hw3
      rw [sum3_comm]
    _ = ∑ w3 ∈ Finset.Icc 0 (count C 3),
          ∑ w5 ∈ Finset.Icc 0 (count C 5),
            ∑ w6 ∈ Finset.Icc 0 (count C 6),
              if (Y3WeightCondA C w3 w5 w6 ∨ Y3WeightCondB C w3 w5 w6) ∧
                  dRow2Le C w3 w5 w6 d then B w3 w5 w6
              else 0 := by
      apply Finset.sum_congr rfl; intro w3 hw3
      apply Finset.sum_congr rfl; intro w5 hw5
      apply Finset.sum_congr rfl; intro w6 hw6
      let X : ℕ := 1 + (count C 3 - w3) + w5 + (count C 6 - w6)
      have hX : 1 ≤ X := by omega
      have h := sum_ite_and_eq_le (d := d) (B := B w3 w5 w6)
        (P := Y3WeightCondA C w3 w5 w6 ∨ Y3WeightCondB C w3 w5 w6) (X := X) hX
      simpa [X, dRow2Le, dRow2WeightEq, B] using h

/-- Pre-reflection 2D W3 conditions of the Y3 B-case (paper `eq:3yd5`,
`eq:3yd6` and the `w6` threshold). -/
abbrev W3mem {n : ℕ} (C : Code n) (d w3 w6 : ℕ) : Prop :=
  count C 3 + count C 6 + 1 ≤ 2 * (w3 + w6) ∧
  2 * w3 + count C 6 + 1 ≤ 2 * w6 + count C 3 ∧
  n + count C 6 + 1 ≤ 2 * w6 + 2 * d ∧
  w3 ≤ count C 3 ∧ w6 ≤ count C 6

/-- The 2D W3 sum before reflection: `w5` is eliminated as `w5ArgY3`. -/
def W3Sum {n : ℕ} (C : Code n) (d : ℕ) : ℕ :=
  ∑ w3 ∈ Finset.Icc 0 (count C 3),
    ∑ w6 ∈ Finset.Icc 0 (count C 6),
      if W3mem C d w3 w6 then
        Nat.choose (count C 3) w3 * Nat.choose (count C 5) (w5ArgY3 C w3) *
          Nat.choose (count C 6) w6
      else 0

/-- The paper's reflection `φ(w3,w6) = (w6-r, w3+r)` with `r = (|6|-|3|)/2`
maps `W3mem` bijectively onto `W3primeMem`. -/
lemma W3mem_reflect_iff {n : ℕ} (C : Code n) (d w3 w6 : ℕ)
    (hpar36 : Even (count C 3) ↔ Even (count C 6)) (h36 : count C 3 ≤ count C 6) :
    W3mem C d w3 w6 ↔
      W3primeMem C d (w6 - (count C 6 - count C 3) / 2) (w3 + (count C 6 - count C 3) / 2) := by
  unfold W3mem W3primeMem
  have hsub_even : Even (count C 6 - count C 3) := (Nat.even_sub h36).2 hpar36.symm
  rcases hsub_even with ⟨r, hr⟩
  have hr2 : count C 6 - count C 3 = 2 * r := by omega
  have hdiv : (count C 6 - count C 3) / 2 = r := by
    rw [hr2, Nat.mul_div_right r (by decide : 0 < 2)]
  rw [hdiv]
  have hpar_sum : Even (count C 3 + count C 6) := Even_add_of_iff hpar36
  rcases hpar_sum with ⟨k, hk⟩
  constructor
  · intro h
    rcases h with ⟨hsum, hdiff, hth, hw3, hw6⟩
    have hrle : r ≤ w6 := by omega
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
  · intro h
    rcases h with ⟨hsum, hdiff, hth, _hw3', _hw6'⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · omega
    · omega
    · omega
    · omega
    · omega

/-- The `Y3WeightCondB ∧ dRow2 ≤ d` condition is equivalent to
`w5 = w5ArgY3` together with the pre-reflection 2D `W3mem`. -/
lemma Y3WeightCondB_dRow2Le_iff {n : ℕ} (C : Code n) (d w3 w5 w6 : ℕ)
    (hpar53 : Even (count C 5) ↔ Even (count C 3)) (h35 : count C 3 ≤ count C 5)
    (htotal : totalCounts C {1, 3, 5, 6} = n) (h1 : count C 1 = 1)
    (hw3 : w3 ≤ count C 3) (hw6 : w6 ≤ count C 6) :
    (Y3WeightCondB C w3 w5 w6 ∧ dRow2Le C w3 w5 w6 d) ↔
      (w5 = w5ArgY3 C w3 ∧ W3mem C d w3 w6) := by
  constructor
  · intro h
    rcases h with ⟨hY, hless⟩
    have hw5eq : w5 = w5ArgY3 C w3 := w5_eq_w5ArgY3_of_Y3WeightCondB C w3 w5 w6 hpar53 h35 hY
    refine ⟨hw5eq, ?_⟩
    rcases hY with ⟨hsum3, heq3, hdiff3⟩
    have hsum : count C 3 + count C 6 + 1 ≤ 2 * (w3 + w6) := by omega
    have hdiff : 2 * w3 + count C 6 + 1 ≤ 2 * w6 + count C 3 := by omega
    have hth : n + count C 6 + 1 ≤ 2 * w6 + 2 * d := by
      have htot : count C 1 + count C 3 + count C 5 + count C 6 = n := by
        simp [totalCounts] at htotal
        omega
      have hsub_even : Even (count C 5 - count C 3) := (Nat.even_sub h35).2 hpar53
      rcases hsub_even with ⟨k, hk⟩
      have hk2 : count C 5 - count C 3 = 2 * k := by omega
      have hdiv : (count C 5 - count C 3) / 2 = k := by
        rw [hk2, Nat.mul_div_right k (by decide : 0 < 2)]
      have hless' : 1 + count C 3 + k + count C 6 - w6 ≤ d := by
        have hh : 1 + (count C 3 - w3) + w5 + (count C 6 - w6) ≤ d := hless
        rw [hw5eq] at hh
        unfold w5ArgY3 at hh
        rw [hdiv] at hh
        omega
      have hn : n = 1 + 2 * count C 3 + 2 * k + count C 6 := by omega
      omega
    unfold W3mem
    exact ⟨hsum, hdiff, hth, hw3, hw6⟩
  · intro h
    rcases h with ⟨hw5eq, hW3⟩
    rcases hW3 with ⟨hsum, hdiff, hth, _hw3, _hw6⟩
    refine ⟨?_, ?_⟩
    · unfold Y3WeightCondB
      have heq3 : count C 3 + 2 * w5 = count C 5 + 2 * w3 := by
        rw [hw5eq]
        exact w5ArgY3_eq C w3 hpar53 h35
      have hsum3 : 2 * (w5 + w6) ≥ count C 5 + count C 6 + 1 := by omega
      have hdiff3 : count C 3 + 2 * w6 ≥ count C 6 + 2 * w3 + 1 := by omega
      exact ⟨hsum3, heq3, hdiff3⟩
    · unfold dRow2Le
      have htot : count C 1 + count C 3 + count C 5 + count C 6 = n := by
        simp [totalCounts] at htotal
        omega
      have hsub_even : Even (count C 5 - count C 3) := (Nat.even_sub h35).2 hpar53
      rcases hsub_even with ⟨k, hk⟩
      have hk2 : count C 5 - count C 3 = 2 * k := by omega
      have hdiv : (count C 5 - count C 3) / 2 = k := by
        rw [hk2, Nat.mul_div_right k (by decide : 0 < 2)]
      have hn : n = 1 + 2 * count C 3 + 2 * k + count C 6 := by omega
      have hle : 1 + count C 3 + k + count C 6 - w6 ≤ d := by omega
      have hh : 1 + (count C 3 - w3) + (w5ArgY3 C w3) + (count C 6 - w6) ≤ d := by
        unfold w5ArgY3
        rw [hdiv]
        omega
      simpa [hw5eq] using hh

/-- Collapse the `w5` sum in the α³ B-part threshold form to the pre-reflection
2D `W3Sum`: `w5` is uniquely `w5ArgY3`. -/
lemma alpha3_threshold_eq_W3Sum {n : ℕ} (C : Code n) (d : ℕ)
    (hpar53 : Even (count C 5) ↔ Even (count C 3)) (h35 : count C 3 ≤ count C 5)
    (htotal : totalCounts C {1, 3, 5, 6} = n) (h1 : count C 1 = 1) :
    (∑ w3 ∈ Finset.Icc 0 (count C 3),
       ∑ w5 ∈ Finset.Icc 0 (count C 5),
         ∑ w6 ∈ Finset.Icc 0 (count C 6),
           if Y3WeightCondB C w3 w5 w6 ∧ dRow2Le C w3 w5 w6 d then
             Nat.choose (count C 3) w3 * Nat.choose (count C 5) w5 *
               Nat.choose (count C 6) w6
           else 0)
    = W3Sum C d := by
  unfold W3Sum
  apply Finset.sum_congr rfl; intro w3 hw3
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro w6 hw6
  have hw3le : w3 ≤ count C 3 := (Finset.mem_Icc.mp hw3).2
  have hw6le : w6 ≤ count C 6 := (Finset.mem_Icc.mp hw6).2
  by_cases hW : W3mem C d w3 w6
  · rw [if_pos hW]
    refine (Finset.sum_eq_single (w5ArgY3 C w3) ?_ ?_).trans ?_
    · intro w5 hw5mem hne
      by_cases hcond : Y3WeightCondB C w3 w5 w6 ∧ dRow2Le C w3 w5 w6 d
      · have hw5eq : w5 = w5ArgY3 C w3 :=
          w5_eq_w5ArgY3_of_Y3WeightCondB C w3 w5 w6 hpar53 h35 hcond.1
        exact False.elim (hne hw5eq)
      · rw [if_neg hcond]
    · intro hnot
      have hmem : w5ArgY3 C w3 ∈ Finset.Icc 0 (count C 5) :=
        w5ArgY3_mem_Icc C w3 hpar53 h35 hw3le
      exact False.elim (hnot hmem)
    · have hcond : Y3WeightCondB C w3 (w5ArgY3 C w3) w6 ∧
          dRow2Le C w3 (w5ArgY3 C w3) w6 d := by
        have hmem : w5ArgY3 C w3 ∈ Finset.Icc 0 (count C 5) :=
          w5ArgY3_mem_Icc C w3 hpar53 h35 hw3le
        have hw5le : w5ArgY3 C w3 ≤ count C 5 := (Finset.mem_Icc.mp hmem).2
        exact (Y3WeightCondB_dRow2Le_iff C d w3 (w5ArgY3 C w3) w6 hpar53 h35
          htotal h1 hw3le hw6le).2 ⟨rfl, hW⟩
      rw [if_pos hcond]
  · rw [if_neg hW]
    apply Finset.sum_eq_zero
    intro w5 hw5mem
    by_cases hcond : Y3WeightCondB C w3 w5 w6 ∧ dRow2Le C w3 w5 w6 d
    · have hiff := Y3WeightCondB_dRow2Le_iff C d w3 w5 w6 hpar53 h35 htotal h1 hw3le hw6le
      have hW' : W3mem C d w3 w6 := (hiff.1 hcond).2
      exact False.elim (hW hW')
    · rw [if_neg hcond]

/-- Reflection/`lemma:cli1` (Lemma 28) comparison for the paper's `thm:11` (Theorem 16) `n > 4`
branch: for `(w3,w6) ∈ W5`, the W5 binomial pair is no larger than the
reflected W3' pair (equality when `|3| = |6|`, strict when `|3| < |6|`). -/
lemma class1_reflection_binomial_le {n : ℕ} (C : Code n) (w3 w6 : ℕ)
    (hpar : Even (count C 3) ↔ Even (count C 6))
    (hle : count C 3 ≤ count C 6) (hpos : 0 < count C 3)
    (hsum : count C 3 + count C 6 + 2 ≤ 2 * (w3 + w6))
    (hdiff : 2 * w6 + count C 3 + 2 ≤ 2 * w3 + count C 6)
    (hw3le : w3 ≤ count C 3) :
    Nat.choose (count C 3) w3 * Nat.choose (count C 6) w6 ≤
      Nat.choose (count C 3) (w6 - (count C 6 - count C 3) / 2) *
        Nat.choose (count C 6) ((count C 6 - count C 3) / 2 + w3) := by
  by_cases hlt : count C 3 < count C 6
  · have hwin := class1_W3prime_w6_window C w3 w6 hsum hdiff hw3le
    have hsub_even : Even (count C 6 - count C 3) := by
      exact (Nat.even_sub hle).2 hpar.symm
    rcases hsub_even with ⟨k, hk⟩
    have hceq : count C 6 = count C 3 + 2 * k := by omega
    have hw6lo : (count C 6 - count C 3) / 2 ≤ w6 := by
      rw [hk, ← two_mul k, Nat.mul_div_right k (by decide : 0 < 2)]
      have hwin1' : count C 6 + 2 ≤ count C 3 + 2 * w6 := hwin.1
      rw [hceq] at hwin1'
      omega
    have hsubcast : (((count C 6 - count C 3) / 2 : ℕ) : ℚ) =
        ((count C 6 : ℚ) - count C 3) / 2 := by
      exact cast_half_sub (count C 6) (count C 3) hle hpar.symm
    let v1 : ℚ := (w3 : ℚ) - (count C 3 : ℚ) / 2
    let v2 : ℚ := (w6 : ℚ) - (count C 6 : ℚ) / 2
    have hbound : (count C 3 : ℚ) / 2 ≥ |v1| := by
      apply abs_le.mpr
      constructor
      · dsimp [v1]
        have hw3q : (0 : ℚ) ≤ w3 := by exact_mod_cast (Nat.zero_le w3)
        nlinarith
      · dsimp [v1]
        have hw3leq : (w3 : ℚ) ≤ count C 3 := by exact_mod_cast hw3le
        nlinarith
    have hv1_ge_v2 : v2 + 1 ≤ v1 := by
      dsimp [v1, v2]
      have hdiffq : (2 : ℚ) * w6 + count C 3 + 2 ≤ (2 : ℚ) * w3 + count C 6 := by
        exact_mod_cast hdiff
      nlinarith
    have hv1_ge_negv2 : -v2 + 1 ≤ v1 := by
      dsimp [v1, v2]
      have hsumq : (count C 3 : ℚ) + count C 6 + 2 ≤ 2 * (w3 : ℚ) + 2 * (w6 : ℚ) := by
        simpa [Nat.cast_add, mul_add] using (by exact_mod_cast hsum :
          (count C 3 : ℚ) + count C 6 + 2 ≤ 2 * ((w3 + w6 : ℕ) : ℚ))
      nlinarith
    have hord : |v1| > |v2| := by
      have hlt2 : |v2| < v1 := by
        rw [abs_lt]
        constructor
        · nlinarith [hv1_ge_negv2]
        · nlinarith [hv1_ge_v2]
      have hv1_nonneg : 0 ≤ v1 := by
        exact le_of_lt (lt_of_le_of_lt (abs_nonneg v2) hlt2)
      rw [abs_of_nonneg hv1_nonneg]
      exact hlt2
    have ha : (count C 6 : ℚ) / 2 + v1 = ((count C 6 - count C 3) / 2 + w3 : ℕ) := by
      dsimp [v1]
      rw [Nat.cast_add, hsubcast]
      ring
    have hb : (count C 3 : ℚ) / 2 + v2 = (w6 - (count C 6 - count C 3) / 2 : ℕ) := by
      dsimp [v2]
      rw [Nat.cast_sub hw6lo, hsubcast]
      ring
    have hc : (count C 6 : ℚ) / 2 + v2 = (w6 : ℕ) := by
      dsimp [v2]
      ring
    have hd : (count C 3 : ℚ) / 2 + v1 = (w3 : ℕ) := by
      dsimp [v1]
      ring
    have hterm := choose_product_inequality (n1 := count C 6) (n2 := count C 3)
        (v1 := v1) (v2 := v2)
        (a := (count C 6 - count C 3) / 2 + w3)
        (b := w6 - (count C 6 - count C 3) / 2)
        (c := w6) (d := w3)
        hlt hpos hpar.symm hbound hord ha hb hc hd
    exact (by simpa [Nat.mul_comm] using le_of_lt hterm)
  · have heq : count C 3 = count C 6 := by omega
    rw [heq]
    rw [Nat.sub_self, Nat.zero_div, Nat.sub_zero, Nat.zero_add]
    exact le_of_eq (Nat.mul_comm _ _)

/-- The 2D W3' sum of the paper's `eq:113` (reflected |3|/|6| coordinates, |5|
factor shared with `W5Sum`). -/
def W3primeSum {n : ℕ} (C : Code n) (d : ℕ) : ℕ :=
  ∑ w3 ∈ Finset.Icc 0 (count C 3),
    ∑ w6 ∈ Finset.Icc 0 (count C 6),
      if W3primeMem C d w3 w6 then
        Nat.choose (count C 3) (w6 - (count C 6 - count C 3) / 2) *
        Nat.choose (count C 5) (w5Arg C w6) *
        Nat.choose (count C 6) ((count C 6 - count C 3) / 2 + w3)
      else 0

/-- The wide-range W3' sum: `w3', w6'` range up to `(|3|+|6|)/2` after the
paper's reflection. -/
def W3primeSumWide {n : ℕ} (C : Code n) (d : ℕ) : ℕ :=
  ∑ w3 ∈ Finset.Icc 0 ((count C 3 + count C 6) / 2),
    ∑ w6 ∈ Finset.Icc 0 ((count C 3 + count C 6) / 2),
      if W3primeMem C d w3 w6 then
        Nat.choose (count C 3) (w6 - (count C 6 - count C 3) / 2) *
        Nat.choose (count C 5) (w5Arg C w6) *
        Nat.choose (count C 6) ((count C 6 - count C 3) / 2 + w3)
      else 0

/-- The paper's reflection change of variables `φ(w3,w6) = (w6-r, w3+r)`
(with `r = (|6|-|3|)/2`) identifies `W3Sum` and `W3primeSum`.  The
pre-reflection `W3mem` and post-reflection `W3primeMem` are matched by
`W3mem_reflect_iff`, and the binomials match via `w5Arg_reflect`; `φ` is an
involution, so it is a bijection. -/
lemma W3Sum_eq_W3primeSum {n : ℕ} (C : Code n) (d : ℕ)
    (hpar36 : Even (count C 3) ↔ Even (count C 6))
    (hpar35 : Even (count C 5) ↔ Even (count C 6))
    (hpar53 : Even (count C 5) ↔ Even (count C 3))
    (h36 : count C 3 ≤ count C 6) (h35 : count C 3 ≤ count C 5) :
    W3Sum C d = W3primeSumWide C d := by
  have hsub_even : Even (count C 6 - count C 3) := (Nat.even_sub h36).2 hpar36.symm
  rcases hsub_even with ⟨rr, hrr⟩
  have hrr2 : count C 6 - count C 3 = 2 * rr := by omega
  have hdiv : (count C 6 - count C 3) / 2 = rr := by
    rw [hrr2, Nat.mul_div_right rr (by decide : 0 < 2)]
  have havg : (count C 3 + count C 6) / 2 = count C 3 + rr := by
    have hpar_sum : Even (count C 3 + count C 6) := Even_add_of_iff hpar36
    rcases hpar_sum with ⟨kk, hkk⟩
    have hkk2 : count C 3 + count C 6 = 2 * kk := by omega
    have hrel : kk = count C 3 + rr := by omega
    rw [hkk2, Nat.mul_div_right kk (by decide : 0 < 2), hrel]
  let P : Finset (ℕ × ℕ) := (Finset.Icc 0 (count C 3)) ×ˢ (Finset.Icc 0 (count C 6))
  let Q : Finset (ℕ × ℕ) := (Finset.Icc 0 ((count C 3 + count C 6) / 2)) ×ˢ
    (Finset.Icc 0 ((count C 3 + count C 6) / 2))
  let s : Finset (ℕ × ℕ) := P.filter (fun p => W3mem C d p.1 p.2)
  let t : Finset (ℕ × ℕ) := Q.filter (fun p => W3primeMem C d p.1 p.2)
  let B : ℕ × ℕ → ℕ := fun p => Nat.choose (count C 3) p.1 *
    Nat.choose (count C 5) (w5ArgY3 C p.1) * Nat.choose (count C 6) p.2
  let B' : ℕ × ℕ → ℕ := fun p => Nat.choose (count C 3) (p.2 - rr) *
    Nat.choose (count C 5) (w5Arg C p.2) * Nat.choose (count C 6) (rr + p.1)
  let φ : ℕ × ℕ → ℕ × ℕ := fun p => (p.2 - rr, p.1 + rr)
  have hW3Sum : W3Sum C d = ∑ p ∈ s, B p := by
    unfold W3Sum s P B
    simp [Finset.sum_product, Finset.sum_filter]
  have hW3primeSum : W3primeSumWide C d = ∑ p ∈ t, B' p := by
    unfold W3primeSumWide t Q B'
    simp [Finset.sum_product, Finset.sum_filter, hdiv]
  have hbij : (∑ p ∈ s, B p) = ∑ p ∈ t, B' p := by
    refine Finset.sum_bij (fun p _ => φ p) ?hi ?inj ?surj ?h
    · intro p hp
      have hpW : W3mem C d p.1 p.2 := (Finset.mem_filter.mp hp).2
      have hmemP : p ∈ P := (Finset.mem_filter.mp hp).1
      have hw3le : p.1 ≤ count C 3 := (Finset.mem_Icc.mp (Finset.mem_product.mp hmemP).1).2
      have hw6le : p.2 ≤ count C 6 := (Finset.mem_Icc.mp (Finset.mem_product.mp hmemP).2).2
      have href := (W3mem_reflect_iff C d p.1 p.2 hpar36 h36).1 hpW
      dsimp [φ, t, Q]
      refine Finset.mem_filter.mpr ⟨?_, ?_⟩
      · rw [havg]
        refine Finset.mem_product.mpr ⟨?_, ?_⟩
        · simp [Finset.mem_Icc]
          omega
        · simp [Finset.mem_Icc]
          omega
      · simpa [hdiv] using href
    · intro p₁ hp₁ p₂ hp₂ h
      dsimp [φ] at h
      have hcomp := Prod.ext_iff.mp h
      have hmemP₁ : p₁ ∈ P := (Finset.mem_filter.mp hp₁).1
      have hmemP₂ : p₂ ∈ P := (Finset.mem_filter.mp hp₂).1
      have hw6₁ : p₁.2 ≤ count C 6 := (Finset.mem_Icc.mp (Finset.mem_product.mp hmemP₁).2).2
      have hw6₂ : p₂.2 ≤ count C 6 := (Finset.mem_Icc.mp (Finset.mem_product.mp hmemP₂).2).2
      have hrr₁ : rr ≤ p₁.2 := by
        have hpW₁ : W3mem C d p₁.1 p₁.2 := (Finset.mem_filter.mp hp₁).2
        omega
      have hrr₂ : rr ≤ p₂.2 := by
        have hpW₂ : W3mem C d p₂.1 p₂.2 := (Finset.mem_filter.mp hp₂).2
        omega
      have h1 : p₁.2 = p₂.2 := by omega
      have h2 : p₁.1 = p₂.1 := by omega
      exact Prod.ext h2 h1
    · intro q hq
      have hqW : W3primeMem C d q.1 q.2 := (Finset.mem_filter.mp hq).2
      have hmemQ : q ∈ Q := (Finset.mem_filter.mp hq).1
      have hq1le : q.1 ≤ count C 3 + rr := by
        have h := (Finset.mem_product.mp hmemQ).1
        have h' : q.1 ≤ (count C 3 + count C 6) / 2 := (Finset.mem_Icc.mp h).2
        rw [havg] at h'
        exact h'
      have hq2le : q.2 ≤ count C 3 + rr := by
        have h := (Finset.mem_product.mp hmemQ).2
        have h' : q.2 ≤ (count C 3 + count C 6) / 2 := (Finset.mem_Icc.mp h).2
        rw [havg] at h'
        exact h'
      have hq2ge : rr ≤ q.2 := by
        have hbox : count C 6 ≤ 2 * q.2 + count C 3 := hqW.2.2.2.2.2.1
        omega
      have h6eq : count C 6 = count C 3 + 2 * rr := by omega
      let p : ℕ × ℕ := φ q
      refine ⟨p, ?_, ?_⟩
      · dsimp [p, s, P]
        refine Finset.mem_filter.mpr ⟨?_, ?_⟩
        · refine Finset.mem_product.mpr ⟨?_, ?_⟩
          · dsimp [φ]
            simp [Finset.mem_Icc]
            omega
          · dsimp [φ]
            simp [Finset.mem_Icc]
            omega
        · apply (W3mem_reflect_iff C d (q.2 - rr) (q.1 + rr) hpar36 h36).2
          rw [hdiv]
          have h1 : (q.1 + rr) - rr = q.1 := by omega
          have h2 : (q.2 - rr) + rr = q.2 := by omega
          rw [h1, h2]
          exact hqW
      · dsimp [p, φ]
        ext <;> omega
    · intro p hp
      have hpW : W3mem C d p.1 p.2 := (Finset.mem_filter.mp hp).2
      have hmemP : p ∈ P := (Finset.mem_filter.mp hp).1
      have hw3le : p.1 ≤ count C 3 := (Finset.mem_Icc.mp (Finset.mem_product.mp hmemP).1).2
      have hw6le : p.2 ≤ count C 6 := (Finset.mem_Icc.mp (Finset.mem_product.mp hmemP).2).2
      rcases hpW with ⟨hsum, hdiff, _hth, _hw3, _hw6⟩
      have hrle : rr ≤ p.2 := by omega
      dsimp [B, B', φ]
      have h5 := w5Arg_reflect C p.1 hpar35 hpar53 h35 h36
      dsimp [w5ArgY3] at h5
      rw [hdiv] at h5
      rw [h5]
      congr 1
      · congr 2
        omega
      · congr 2
        omega
  rw [hW3Sum, hW3primeSum]
  exact hbij

/-- The 2D domination `W5Sum ≤ W3primeSum`: `W5 ⊆ W3'` and the per-term
reflection comparison `lemma:cli1` (Lemma 28) (`class1_reflection_binomial_le`). -/
lemma W5Sum_le_W3primeSum {n : ℕ} (C : Code n) (d : ℕ)
    (hpar36 : Even (count C 3) ↔ Even (count C 6))
    (hle : count C 3 ≤ count C 6) (hpos : 0 < count C 3) :
    W5Sum C d ≤ W3primeSum C d := by
  unfold W5Sum W3primeSum
  apply Finset.sum_le_sum; intro w3 hw3
  apply Finset.sum_le_sum; intro w6 hw6
  by_cases hW : W5mem C d w3 w6
  · rw [if_pos hW]
    have hW3 : W3primeMem C d w3 w6 := class1_W5_subset_W3prime C d w3 w6 hle hW
    rw [if_pos hW3]
    rcases hW with ⟨hsum, hdiff, _hth, hw3le, _hw6le⟩
    have hcoeff : Nat.choose (count C 3) w3 * Nat.choose (count C 6) w6 ≤
        Nat.choose (count C 3) (w6 - (count C 6 - count C 3) / 2) *
          Nat.choose (count C 6) ((count C 6 - count C 3) / 2 + w3) :=
      class1_reflection_binomial_le C w3 w6 hpar36 hle hpos hsum hdiff hw3le
    have h := Nat.mul_le_mul_right (Nat.choose (count C 5) (w5Arg C w6)) hcoeff
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h
  · rw [if_neg hW]
    exact Nat.zero_le _

/-- The narrow-range W3' sum is no larger than the wide-range one (the extra
terms in the narrow range have zero |3| factor, and the wide range adds only
nonnegative terms). -/
lemma W3primeSum_le_W3primeSumWide {n : ℕ} (C : Code n) (d : ℕ)
    (hpar36 : Even (count C 3) ↔ Even (count C 6)) (h36 : count C 3 ≤ count C 6) :
    W3primeSum C d ≤ W3primeSumWide C d := by
  have hsub_even : Even (count C 6 - count C 3) := (Nat.even_sub h36).2 hpar36.symm
  rcases hsub_even with ⟨rr, hrr⟩
  have hrr2 : count C 6 - count C 3 = 2 * rr := by omega
  have hdiv : (count C 6 - count C 3) / 2 = rr := by
    rw [hrr2, Nat.mul_div_right rr (by decide : 0 < 2)]
  have havg : (count C 3 + count C 6) / 2 = count C 3 + rr := by
    have hpar_sum : Even (count C 3 + count C 6) := Even_add_of_iff hpar36
    rcases hpar_sum with ⟨kk, hkk⟩
    have hkk2 : count C 3 + count C 6 = 2 * kk := by omega
    have hrel : kk = count C 3 + rr := by omega
    rw [hkk2, Nat.mul_div_right kk (by decide : 0 < 2), hrel]
  let S := Finset.Icc 0 ((count C 3 + count C 6) / 2)
  let B' : ℕ → ℕ → ℕ := fun w3 w6 =>
    if W3primeMem C d w3 w6 then
      Nat.choose (count C 3) (w6 - rr) * Nat.choose (count C 5) (w5Arg C w6) *
        Nat.choose (count C 6) (rr + w3)
    else 0
  have h6sub : S ⊆ Finset.Icc 0 (count C 6) := by
    intro x hx
    have hxle : x ≤ (count C 3 + count C 6) / 2 := (Finset.mem_Icc.mp hx).2
    have hxle' : x ≤ count C 3 + rr := by
      rw [havg] at hxle
      exact hxle
    have h6eq : count C 6 = count C 3 + 2 * rr := by omega
    clear hdiv havg hxle hx hrr hrr2 h36
    have hmid : count C 3 + rr ≤ count C 6 := by
      rw [h6eq]
      omega
    simpa [Finset.mem_Icc] using le_trans hxle' hmid
  have h3sub : Finset.Icc 0 (count C 3) ⊆ S := by
    intro x hx
    have hxle : x ≤ count C 3 := (Finset.mem_Icc.mp hx).2
    have h : x ≤ count C 3 + rr := by omega
    simpa [S, Finset.mem_Icc, havg] using h
  have hshrink : W3primeSum C d = ∑ w3 ∈ Finset.Icc 0 (count C 3), ∑ w6 ∈ S, B' w3 w6 := by
    unfold W3primeSum
    apply Finset.sum_congr rfl; intro w3 hw3
    rw [hdiv]
    exact (Finset.sum_subset h6sub (by
      intro w6 hw6Icc hw6not
      have hw6gt : (count C 3 + count C 6) / 2 < w6 := by
        have hle : w6 ≤ count C 6 := (Finset.mem_Icc.mp hw6Icc).2
        have hnot : w6 ∉ S := hw6not
        have hnotle : ¬ w6 ≤ (count C 3 + count C 6) / 2 := by
          intro h
          exact hnot (by dsimp [S]; simp [Finset.mem_Icc, h])
        omega
      have hlt : count C 3 < w6 - rr := by
        rw [havg] at hw6gt
        omega
      have hchoose : Nat.choose (count C 3) (w6 - rr) = 0 := Nat.choose_eq_zero_of_lt hlt
      by_cases hW : W3primeMem C d w3 w6
      · rw [if_pos hW, hchoose]
        simp
      · rw [if_neg hW])).symm
  have hext : (∑ w3 ∈ Finset.Icc 0 (count C 3), ∑ w6 ∈ S, B' w3 w6) ≤
      ∑ w3 ∈ S, ∑ w6 ∈ S, B' w3 w6 := by
    refine Finset.sum_le_sum_of_subset_of_nonneg h3sub ?_
    intro w3 hw3S hw3not
    exact Finset.sum_nonneg (by intro w6 hw6; dsimp [B']; exact Nat.zero_le _)
  have hwide : W3primeSumWide C d = ∑ w3 ∈ S, ∑ w6 ∈ S, B' w3 w6 := by
    unfold W3primeSumWide
    dsimp [S, B']
    rw [hdiv]
  calc
    W3primeSum C d = ∑ w3 ∈ Finset.Icc 0 (count C 3), ∑ w6 ∈ S, B' w3 w6 := hshrink
    _ ≤ ∑ w3 ∈ S, ∑ w6 ∈ S, B' w3 w6 := hext
    _ = W3primeSumWide C d := hwide.symm

/-- Unpack `ClassI C` into the type/parity/blocklength hypotheses needed by the
α³/α⁵ machinery. -/
lemma classI_hyps {n : ℕ} (C : Code n) (h : ClassI C) :
    (∀ u : Fin n, colVal (C u) = 1 ∨ colVal (C u) = 3 ∨
      colVal (C u) = 5 ∨ colVal (C u) = 6) ∧
    (Even (count C 5) ↔ Even (count C 6)) ∧
    (Even (count C 3) ↔ Even (count C 6)) ∧
    (Even (count C 5) ↔ Even (count C 3)) ∧
    totalCounts C {1, 3, 5, 6} = n := by
  rcases h with ⟨_hodd1, hpar, htotal⟩
  have htypes : ∀ u : Fin n, colVal (C u) = 1 ∨ colVal (C u) = 3 ∨
      colVal (C u) = 5 ∨ colVal (C u) = 6 := by
    intro u
    exact types_1356_of_totalCounts C htotal u
  have hpar35 : Even (count C 5) ↔ Even (count C 6) := by
    rcases hpar with hEven | hOdd
    · exact ⟨fun _ => hEven.2.2, fun _ => hEven.2.1⟩
    · constructor
      · intro h5; exact False.elim ((Nat.not_even_iff_odd.mpr hOdd.2.1) h5)
      · intro h6; exact False.elim ((Nat.not_even_iff_odd.mpr hOdd.2.2) h6)
  have hpar36 : Even (count C 3) ↔ Even (count C 6) := by
    rcases hpar with hEven | hOdd
    · exact ⟨fun _ => hEven.2.2, fun _ => hEven.1⟩
    · constructor
      · intro h3; exact False.elim ((Nat.not_even_iff_odd.mpr hOdd.1) h3)
      · intro h6; exact False.elim ((Nat.not_even_iff_odd.mpr hOdd.2.2) h6)
  have hpar53 : Even (count C 5) ↔ Even (count C 3) := by
    rcases hpar with hEven | hOdd
    · exact ⟨fun _ => hEven.1, fun _ => hEven.2.1⟩
    · constructor
      · intro h5; exact False.elim ((Nat.not_even_iff_odd.mpr hOdd.2.1) h5)
      · intro h3; exact False.elim ((Nat.not_even_iff_odd.mpr hOdd.1) h3)
  exact ⟨htypes, hpar35, hpar36, hpar53, htotal⟩

/-- For the Class-I `|1|=1`, `|3|=min>0` case, `Psi d ≥ 0` follows by chaining
`Σ α⁵ = W5Sum ≤ W3primeSum ≤ W3primeSumWide = W3Sum ≤ Σ α³`. -/
lemma class1_psi_nonneg {n : ℕ} (C : Code n) (t : Fin n) (d : ℕ)
    (hd : 1 ≤ d)
    (htypes : ∀ u : Fin n, colVal (C u) = 1 ∨ colVal (C u) = 3 ∨
      colVal (C u) = 5 ∨ colVal (C u) = 6)
    (h1 : count C 1 = 1) (hcol : C t = col1)
    (hpar35 : Even (count C 5) ↔ Even (count C 6))
    (hpar36 : Even (count C 3) ↔ Even (count C 6))
    (hpar53 : Even (count C 5) ↔ Even (count C 3))
    (h35 : count C 3 ≤ count C 5) (h36 : count C 3 ≤ count C 6)
    (htotal : totalCounts C {1, 3, 5, 6} = n) (hpos : 0 < count C 3) :
    Psi C t d ≥ 0 := by
  have h5 : (∑ i ∈ Finset.Icc 0 (d - 1), alpha5 C t i) = W5Sum C d := by
    rw [alpha5_cumulative_eq_threshold C t d hd htypes h1 hcol]
    exact alpha5_threshold_eq_W5Sum C d hd hpar35 hpar36 htotal h1 h35
  have hchain : (∑ i ∈ Finset.Icc 0 (d - 1), alpha5 C t i) ≤
      ∑ i ∈ Finset.Icc 1 d, alpha3 C t i := by
    rw [h5]
    calc
      W5Sum C d ≤ W3primeSum C d := W5Sum_le_W3primeSum C d hpar36 h36 hpos
      _ ≤ W3primeSumWide C d := W3primeSum_le_W3primeSumWide C d hpar36 h36
      _ = W3Sum C d := (W3Sum_eq_W3primeSum C d hpar36 hpar35 hpar53 h36 h35).symm
      _ = (∑ w3 ∈ Finset.Icc 0 (count C 3),
          ∑ w5 ∈ Finset.Icc 0 (count C 5),
            ∑ w6 ∈ Finset.Icc 0 (count C 6),
              if Y3WeightCondB C w3 w5 w6 ∧ dRow2Le C w3 w5 w6 d then
                Nat.choose (count C 3) w3 * Nat.choose (count C 5) w5 *
                  Nat.choose (count C 6) w6
              else 0) := (alpha3_threshold_eq_W3Sum C d hpar53 h35 htotal h1).symm
      _ ≤ ∑ i ∈ Finset.Icc 1 d, alpha3 C t i :=
        alpha3_cumulative_ge_threshold_B C t d htypes h1 hcol
  unfold Psi
  exact sub_nonneg.mpr (by exact_mod_cast hchain)

/-- The paper's `W3'` witness `(w3',w6') = ((|3|+|6|)/2, |6|/2)` lies in
`W3primeMem` when `|6| ≥ 2` and `d` is large enough (`eq:113` + threshold). -/
lemma W3primeMem_witness {n : ℕ} (C : Code n) (d : ℕ)
    (hpar36 : Even (count C 3) ↔ Even (count C 6))
    (h6 : 2 ≤ count C 6) (hd : n + 1 ≤ count C 6 + 2 * d) :
    W3primeMem C d ((count C 3 + count C 6) / 2) (count C 6 / 2) := by
  unfold W3primeMem
  have hsum_even : Even (count C 3 + count C 6) := Even_add_of_iff hpar36
  rcases hsum_even with ⟨k, hk⟩
  have hk2 : count C 3 + count C 6 = 2 * k := by omega
  have hdiv_sum : (count C 3 + count C 6) / 2 = k := by
    rw [hk2, Nat.mul_div_right k (by decide : 0 < 2)]
  by_cases h6e : Even (count C 6)
  · rcases h6e with ⟨m, hm⟩
    have hm2 : count C 6 = 2 * m := by omega
    have hdiv6 : count C 6 / 2 = m := by
      rw [hm2, Nat.mul_div_right m (by decide : 0 < 2)]
    rw [hdiv_sum, hdiv6]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega
  · have ho6 : Odd (count C 6) := Nat.not_even_iff_odd.mp h6e
    rcases ho6 with ⟨m, hm⟩
    have hm2 : count C 6 = 2 * m + 1 := by omega
    have hdiv6 : count C 6 / 2 = m := by omega
    rw [hdiv_sum, hdiv6]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

/-- The witness binomial is strictly positive: its |6| factor is
`C(|6|,|6|) = 1`, and its |3| and |5| factors are central binomials. -/
lemma witness_binomial_pos {n : ℕ} (C : Code n)
    (hpar36 : Even (count C 3) ↔ Even (count C 6))
    (hpar35 : Even (count C 5) ↔ Even (count C 6))
    (_hpar53 : Even (count C 5) ↔ Even (count C 3))
    (h36 : count C 3 ≤ count C 6) (_h35 : count C 3 ≤ count C 5)
    (_h6 : 2 ≤ count C 6) :
    0 < Nat.choose (count C 3) ((count C 6) / 2 - (count C 6 - count C 3) / 2) *
        Nat.choose (count C 5) (w5Arg C ((count C 6) / 2)) *
        Nat.choose (count C 6) ((count C 6 - count C 3) / 2 + (count C 3 + count C 6) / 2) := by
  have hsub_even : Even (count C 6 - count C 3) := (Nat.even_sub h36).2 hpar36.symm
  rcases hsub_even with ⟨r, hr⟩
  have hr2 : count C 6 - count C 3 = 2 * r := by omega
  have hdiv_sub : (count C 6 - count C 3) / 2 = r := by
    rw [hr2, Nat.mul_div_right r (by decide : 0 < 2)]
  have hsum_even : Even (count C 3 + count C 6) := Even_add_of_iff hpar36
  rcases hsum_even with ⟨s, hs⟩
  have hs2 : count C 3 + count C 6 = 2 * s := by omega
  have hdiv_sum : (count C 3 + count C 6) / 2 = s := by
    rw [hs2, Nat.mul_div_right s (by decide : 0 < 2)]
  rw [hdiv_sub, hdiv_sum]
  -- |6| factor: C(|6|, r+s) = C(|6|, |6|) = 1
  have h6eq : count C 6 = r + s := by omega
  have hchoose6 : Nat.choose (count C 6) (r + s) = 1 := by
    rw [h6eq]
    exact Nat.choose_self (r + s)
  rw [hchoose6]
  rw [Nat.mul_one]
  -- |3| factor: C(|3|, w6 - r) is a valid central binomial
  obtain ⟨m, hm⟩ | ⟨m, hm⟩ := Nat.even_or_odd (count C 6)
  · have hm2 : count C 6 = 2 * m := by omega
    have h3e : Even (count C 3) := hpar36.mpr ⟨m, hm⟩
    rcases h3e with ⟨j, hj⟩
    have hj2 : count C 3 = 2 * j := by omega
    have hdiv6 : count C 6 / 2 = m := by rw [hm2, Nat.mul_div_right m (by decide : 0 < 2)]
    rw [hdiv6]
    have hjr : m - r = j := by omega
    rw [hjr]
    -- C(2j, j) * C(|5|, w5Arg m) > 0
    have hc3 : 0 < Nat.choose (count C 3) j := by
      rw [hj2]
      exact Nat.choose_pos (by omega : j ≤ 2 * j)
    have hw5 : w5Arg C m ≤ count C 5 := by
      unfold w5Arg
      by_cases h56 : count C 5 ≤ count C 6
      · rw [if_pos h56]
        have hsub5 : Even (count C 6 - count C 5) := (Nat.even_sub h56).2 hpar35.symm
        rcases hsub5 with ⟨u, hu⟩
        have hu2 : count C 6 - count C 5 = 2 * u := by omega
        have hdivu : (count C 6 - count C 5) / 2 = u := by
          rw [hu2, Nat.mul_div_right u (by decide : 0 < 2)]
        rw [hdivu]
        omega
      · rw [if_neg h56]
        have hsub5 : Even (count C 5 - count C 6) :=
          (Nat.even_sub (le_of_lt (lt_of_not_ge h56))).2 hpar35
        rcases hsub5 with ⟨u, hu⟩
        have hu2 : count C 5 - count C 6 = 2 * u := by omega
        have hdivu : (count C 5 - count C 6) / 2 = u := by
          rw [hu2, Nat.mul_div_right u (by decide : 0 < 2)]
        rw [hdivu]
        omega
    have hc5 : 0 < Nat.choose (count C 5) (w5Arg C m) :=
      Nat.choose_pos hw5
    exact mul_pos hc3 hc5
  · have hm2 : count C 6 = 2 * m + 1 := by omega
    have h3o : Odd (count C 3) := by
      rcases Nat.even_or_odd (count C 3) with h3e | h3o
      · exfalso
        exact (Nat.not_even_iff_odd.mpr ⟨m, hm⟩) (hpar36.mp h3e)
      · exact h3o
    rcases h3o with ⟨j, hj⟩
    have hj2 : count C 3 = 2 * j + 1 := by omega
    have hdiv6 : count C 6 / 2 = m := by omega
    rw [hdiv6]
    have hjr : m - r = j := by omega
    rw [hjr]
    have hc3 : 0 < Nat.choose (count C 3) j := by
      rw [hj2]
      exact Nat.choose_pos (by omega : j ≤ 2 * j + 1)
    have hw5 : w5Arg C m ≤ count C 5 := by
      unfold w5Arg
      by_cases h56 : count C 5 ≤ count C 6
      · rw [if_pos h56]
        have hsub5 : Even (count C 6 - count C 5) := (Nat.even_sub h56).2 hpar35.symm
        rcases hsub5 with ⟨u, hu⟩
        have hu2 : count C 6 - count C 5 = 2 * u := by omega
        have hdivu : (count C 6 - count C 5) / 2 = u := by
          rw [hu2, Nat.mul_div_right u (by decide : 0 < 2)]
        rw [hdivu]
        omega
      · rw [if_neg h56]
        have hsub5 : Even (count C 5 - count C 6) :=
          (Nat.even_sub (le_of_lt (lt_of_not_ge h56))).2 hpar35
        rcases hsub5 with ⟨u, hu⟩
        have hu2 : count C 5 - count C 6 = 2 * u := by omega
        have hdivu : (count C 5 - count C 6) / 2 = u := by
          rw [hu2, Nat.mul_div_right u (by decide : 0 < 2)]
        rw [hdivu]
        omega
    have hc5 : 0 < Nat.choose (count C 5) (w5Arg C m) := Nat.choose_pos hw5
    exact mul_pos hc3 hc5

/-- The witness lies strictly outside the narrow `w3 ≤ |3|` range, so the wide
W3' sum is strictly larger than the narrow one. -/
lemma W3primeSumWide_strict {n : ℕ} (C : Code n) (d : ℕ)
    (hpar36 : Even (count C 3) ↔ Even (count C 6))
    (hpar35 : Even (count C 5) ↔ Even (count C 6))
    (hpar53 : Even (count C 5) ↔ Even (count C 3))
    (h36 : count C 3 ≤ count C 6) (h35 : count C 3 ≤ count C 5)
    (hlt : count C 3 < count C 6) (h6 : 2 ≤ count C 6)
    (hd : n + 1 ≤ count C 6 + 2 * d) :
    W3primeSum C d < W3primeSumWide C d := by
  have hsub_even : Even (count C 6 - count C 3) := (Nat.even_sub h36).2 hpar36.symm
  rcases hsub_even with ⟨rr, hrr⟩
  have hrr2 : count C 6 - count C 3 = 2 * rr := by omega
  have hdiv : (count C 6 - count C 3) / 2 = rr := by
    rw [hrr2, Nat.mul_div_right rr (by decide : 0 < 2)]
  have havg : (count C 3 + count C 6) / 2 = count C 3 + rr := by
    have hpar_sum : Even (count C 3 + count C 6) := Even_add_of_iff hpar36
    rcases hpar_sum with ⟨kk, hkk⟩
    have hkk2 : count C 3 + count C 6 = 2 * kk := by omega
    have hrel : kk = count C 3 + rr := by omega
    rw [hkk2, Nat.mul_div_right kk (by decide : 0 < 2), hrel]
  let S := Finset.Icc 0 ((count C 3 + count C 6) / 2)
  let B' : ℕ → ℕ → ℕ := fun w3 w6 =>
    if W3primeMem C d w3 w6 then
      Nat.choose (count C 3) (w6 - rr) * Nat.choose (count C 5) (w5Arg C w6) *
        Nat.choose (count C 6) (rr + w3)
    else 0
  let G : ℕ → ℕ := fun w3 => ∑ w6 ∈ S, B' w3 w6
  have h6sub : S ⊆ Finset.Icc 0 (count C 6) := by
    intro x hx
    have hxle : x ≤ (count C 3 + count C 6) / 2 := (Finset.mem_Icc.mp hx).2
    have hxle' : x ≤ count C 3 + rr := by
      rw [havg] at hxle
      exact hxle
    have h6eq : count C 6 = count C 3 + 2 * rr := by omega
    simpa [Finset.mem_Icc] using le_trans hxle' (by omega)
  have h3sub : Finset.Icc 0 (count C 3) ⊆ S := by
    intro x hx
    have hxle : x ≤ count C 3 := (Finset.mem_Icc.mp hx).2
    have h : x ≤ count C 3 + rr := by omega
    simpa [S, Finset.mem_Icc, havg] using h
  have hshrink : W3primeSum C d = ∑ w3 ∈ Finset.Icc 0 (count C 3), G w3 := by
    unfold W3primeSum G
    apply Finset.sum_congr rfl; intro w3 hw3
    rw [hdiv]
    exact (Finset.sum_subset h6sub (by
      intro w6 hw6Icc hw6not
      have hw6gt : (count C 3 + count C 6) / 2 < w6 := by
        have hle : w6 ≤ count C 6 := (Finset.mem_Icc.mp hw6Icc).2
        have hnot : w6 ∉ S := hw6not
        have hnotle : ¬ w6 ≤ (count C 3 + count C 6) / 2 := by
          intro h
          exact hnot (by dsimp [S]; simp [Finset.mem_Icc, h])
        omega
      have hlt : count C 3 < w6 - rr := by
        rw [havg] at hw6gt
        omega
      have hchoose : Nat.choose (count C 3) (w6 - rr) = 0 := Nat.choose_eq_zero_of_lt hlt
      by_cases hW : W3primeMem C d w3 w6
      · rw [if_pos hW, hchoose]; simp
      · rw [if_neg hW])).symm
  have hwide : W3primeSumWide C d = ∑ w3 ∈ S, G w3 := by
    unfold W3primeSumWide G
    dsimp [S, B']
    rw [hdiv]
  let avg := (count C 3 + count C 6) / 2
  have hwmem : W3primeMem C d avg (count C 6 / 2) := W3primeMem_witness C d hpar36 h6 hd
  have hbpos : 0 < Nat.choose (count C 3) ((count C 6) / 2 - (count C 6 - count C 3) / 2) *
      Nat.choose (count C 5) (w5Arg C ((count C 6) / 2)) *
      Nat.choose (count C 6) ((count C 6 - count C 3) / 2 + (count C 3 + count C 6) / 2) := by
    exact witness_binomial_pos C hpar36 hpar35 hpar53 h36 h35 h6
  have hBpos : 0 < B' avg (count C 6 / 2) := by
    change 0 < (if W3primeMem C d avg (count C 6 / 2) then
      Nat.choose (count C 3) ((count C 6) / 2 - rr) * Nat.choose (count C 5) (w5Arg C ((count C 6) / 2)) *
        Nat.choose (count C 6) (rr + avg) else 0)
    rw [if_pos hwmem]
    dsimp [avg]
    simpa [hdiv, havg] using hbpos
  have hGpos : 0 < G avg := by
    dsimp [G]
    have hmem6 : count C 6 / 2 ∈ S := by
      dsimp [S]
      simp [Finset.mem_Icc]
      exact Nat.div_le_div_right (by omega : count C 6 ≤ count C 3 + count C 6)
    exact lt_of_lt_of_le hBpos (Finset.single_le_sum (by intro w6 hw6; dsimp [B']; exact Nat.zero_le _) hmem6)
  have havg_not : avg ∉ Finset.Icc 0 (count C 3) := by
    dsimp [avg]
    rw [havg]
    simp [Finset.mem_Icc]
    omega
  have havgS : avg ∈ S := by
    dsimp [S, avg]
    simp [Finset.mem_Icc]
  have h3sub_erase : Finset.Icc 0 (count C 3) ⊆ S.erase avg := by
    intro x hx
    refine Finset.mem_erase.mpr ⟨?_, h3sub hx⟩
    intro hxeq
    have h : avg ∈ Finset.Icc 0 (count C 3) := by
      rw [← hxeq]
      exact hx
    exact havg_not h
  have hle : (∑ w3 ∈ Finset.Icc 0 (count C 3), G w3) ≤ ∑ w3 ∈ S.erase avg, G w3 := by
    exact Finset.sum_le_sum_of_subset_of_nonneg h3sub_erase (by intro w3 hw3 hnot; exact Nat.zero_le _)
  have hS : (∑ w3 ∈ S, G w3) = G avg + ∑ w3 ∈ S.erase avg, G w3 := by
    exact (Finset.add_sum_erase S G havgS).symm
  have hstrict : (∑ w3 ∈ Finset.Icc 0 (count C 3), G w3) < ∑ w3 ∈ S, G w3 := by
    rw [hS]
    omega
  rw [hshrink, hwide]
  exact hstrict

/-- For the Class-I `|1|=1`, `|3|=min>0`, `|3|<|6|` case, `Psi n > 0` at the
top distance `d = n`, by strict domination plus the witness. -/
lemma class1_psi_pos {n : ℕ} (C : Code n) (t : Fin n)
    (hn : 1 ≤ n)
    (htypes : ∀ u : Fin n, colVal (C u) = 1 ∨ colVal (C u) = 3 ∨
      colVal (C u) = 5 ∨ colVal (C u) = 6)
    (h1 : count C 1 = 1) (hcol : C t = col1)
    (hpar35 : Even (count C 5) ↔ Even (count C 6))
    (hpar36 : Even (count C 3) ↔ Even (count C 6))
    (hpar53 : Even (count C 5) ↔ Even (count C 3))
    (h35 : count C 3 ≤ count C 5) (h36 : count C 3 ≤ count C 6)
    (htotal : totalCounts C {1, 3, 5, 6} = n)
    (hpos : 0 < count C 3) (hlt : count C 3 < count C 6)
    (h6 : 2 ≤ count C 6) :
    Psi C t n > 0 := by
  have h5 : (∑ i ∈ Finset.Icc 0 (n - 1), alpha5 C t i) = W5Sum C n := by
    rw [alpha5_cumulative_eq_threshold C t n hn htypes h1 hcol]
    exact alpha5_threshold_eq_W5Sum C n hn hpar35 hpar36 htotal h1 h35
  have hdom : W5Sum C n ≤ W3primeSum C n := W5Sum_le_W3primeSum C n hpar36 h36 hpos
  have hstrict : W3primeSum C n < W3primeSumWide C n := by
    apply W3primeSumWide_strict C n hpar36 hpar35 hpar53 h36 h35 hlt h6
    omega
  have hα3 : W3primeSumWide C n ≤ ∑ i ∈ Finset.Icc 1 n, alpha3 C t i := by
    calc
      W3primeSumWide C n = W3Sum C n := (W3Sum_eq_W3primeSum C n hpar36 hpar35 hpar53 h36 h35).symm
      _ = (∑ w3 ∈ Finset.Icc 0 (count C 3),
          ∑ w5 ∈ Finset.Icc 0 (count C 5),
            ∑ w6 ∈ Finset.Icc 0 (count C 6),
              if Y3WeightCondB C w3 w5 w6 ∧ dRow2Le C w3 w5 w6 n then
                Nat.choose (count C 3) w3 * Nat.choose (count C 5) w5 *
                  Nat.choose (count C 6) w6
              else 0) := (alpha3_threshold_eq_W3Sum C n hpar53 h35 htotal h1).symm
      _ ≤ ∑ i ∈ Finset.Icc 1 n, alpha3 C t i := alpha3_cumulative_ge_threshold_B C t n htypes h1 hcol
  have hchain : (∑ i ∈ Finset.Icc 0 (n - 1), alpha5 C t i) < ∑ i ∈ Finset.Icc 1 n, alpha3 C t i := by
    rw [h5]
    exact lt_of_le_of_lt hdom (lt_of_lt_of_le hstrict hα3)
  unfold Psi
  exact sub_pos.mpr (by exact_mod_cast hchain)

/-- `thm:11` (Theorem 16) |3| = |6| strictness: the branch-A word (zeros on type 3/5, ones
on type 6) lies in Y3 at distance |3|+1 and is not counted by the B-part, so
`Psi d > 0` for d ≥ |3|+1. -/
lemma class1_psi_pos_eq {n : ℕ} (C : Code n) (t : Fin n)
    (htypes : ∀ u : Fin n, colVal (C u) = 1 ∨ colVal (C u) = 3 ∨
      colVal (C u) = 5 ∨ colVal (C u) = 6)
    (h1 : count C 1 = 1) (hcol : C t = col1)
    (hpar35 : Even (count C 5) ↔ Even (count C 6))
    (hpar36 : Even (count C 3) ↔ Even (count C 6))
    (hpar53 : Even (count C 5) ↔ Even (count C 3))
    (h35 : count C 3 ≤ count C 5) (h36 : count C 3 ≤ count C 6)
    (htotal : totalCounts C {1, 3, 5, 6} = n)
    (hpos : 0 < count C 3) (heq : count C 3 = count C 6)
    (hd : count C 3 + 1 ≤ d) :
    Psi C t d > 0 := by
  let T : ℕ → ℕ → ℕ → ℕ := fun w3 w5 w6 =>
    Nat.choose (count C 3) w3 * Nat.choose (count C 5) w5 * Nat.choose (count C 6) w6
  let Bsum : ℕ :=
    ∑ w3 ∈ Finset.Icc 0 (count C 3),
      ∑ w5 ∈ Finset.Icc 0 (count C 5),
        ∑ w6 ∈ Finset.Icc 0 (count C 6),
          if Y3WeightCondB C w3 w5 w6 ∧ dRow2Le C w3 w5 w6 d then T w3 w5 w6 else 0
  have hAword_cond : Y3WeightCondA C 0 0 (count C 6) := by
    unfold Y3WeightCondA
    clear hpar35 hpar36 hpar53 htotal
    constructor <;> omega
  have hAword_notB : ¬ Y3WeightCondB C 0 0 (count C 6) := by
    unfold Y3WeightCondB
    clear hpar35 hpar36 hpar53 htotal
    intro h
    rcases h with ⟨h1', _, _⟩
    omega
  have hAword_d : dRow2Le C 0 0 (count C 6) d := by
    unfold dRow2Le
    clear hpar35 hpar36 hpar53 htotal
    omega
  have hcond : (Y3WeightCondA C 0 0 (count C 6) ∧ ¬ Y3WeightCondB C 0 0 (count C 6)) ∧
      dRow2Le C 0 0 (count C 6) d := ⟨⟨hAword_cond, hAword_notB⟩, hAword_d⟩
  have hT1 : T 0 0 (count C 6) = 1 := by
    simp [T, heq]
  have hpoint : ∀ w3 w5 w6,
      (if (Y3WeightCondA C w3 w5 w6 ∨ Y3WeightCondB C w3 w5 w6) ∧
          dRow2Le C w3 w5 w6 d then T w3 w5 w6 else 0) =
        (if Y3WeightCondB C w3 w5 w6 ∧ dRow2Le C w3 w5 w6 d then T w3 w5 w6 else 0) +
          (if (Y3WeightCondA C w3 w5 w6 ∧ ¬ Y3WeightCondB C w3 w5 w6) ∧
              dRow2Le C w3 w5 w6 d then T w3 w5 w6 else 0) := by
    intro w3 w5 w6
    by_cases hAB : (Y3WeightCondA C w3 w5 w6 ∨ Y3WeightCondB C w3 w5 w6) ∧
        dRow2Le C w3 w5 w6 d
    · rcases hAB with ⟨hAB', hd'⟩
      rcases hAB' with hA' | hB'
      · -- A holds
        by_cases hB' : Y3WeightCondB C w3 w5 w6
        · have hABc : (Y3WeightCondA C w3 w5 w6 ∨ Y3WeightCondB C w3 w5 w6) ∧
              dRow2Le C w3 w5 w6 d := ⟨Or.inl hA', hd'⟩
          have hBc : Y3WeightCondB C w3 w5 w6 ∧ dRow2Le C w3 w5 w6 d := ⟨hB', hd'⟩
          have hAc : ¬ ((Y3WeightCondA C w3 w5 w6 ∧ ¬ Y3WeightCondB C w3 w5 w6) ∧
              dRow2Le C w3 w5 w6 d) := by
            rintro ⟨hA, hd'⟩
            rcases hA with ⟨hA', hnb⟩
            exact hnb hB'
          rw [if_pos hABc, if_pos hBc, if_neg hAc]
          simp
        · have hABc : (Y3WeightCondA C w3 w5 w6 ∨ Y3WeightCondB C w3 w5 w6) ∧
              dRow2Le C w3 w5 w6 d := ⟨Or.inl hA', hd'⟩
          have hAc : (Y3WeightCondA C w3 w5 w6 ∧ ¬ Y3WeightCondB C w3 w5 w6) ∧
              dRow2Le C w3 w5 w6 d := ⟨⟨hA', hB'⟩, hd'⟩
          have hBf : ¬ (Y3WeightCondB C w3 w5 w6 ∧ dRow2Le C w3 w5 w6 d) := by
            rintro ⟨hb, _⟩
            exact hB' hb
          rw [if_pos hABc, if_neg hBf, if_pos hAc]
          simp
      · -- B holds
        have hABc : (Y3WeightCondA C w3 w5 w6 ∨ Y3WeightCondB C w3 w5 w6) ∧
            dRow2Le C w3 w5 w6 d := ⟨Or.inr hB', hd'⟩
        have hBc : Y3WeightCondB C w3 w5 w6 ∧ dRow2Le C w3 w5 w6 d := ⟨hB', hd'⟩
        have hAc : ¬ ((Y3WeightCondA C w3 w5 w6 ∧ ¬ Y3WeightCondB C w3 w5 w6) ∧
            dRow2Le C w3 w5 w6 d) := by
          rintro ⟨hA, hd'⟩
          rcases hA with ⟨hA', hnb⟩
          exact hnb hB'
        rw [if_pos hABc, if_pos hBc, if_neg hAc]
        simp
    · -- neither (A∨B)∧D
      have hBf : ¬ (Y3WeightCondB C w3 w5 w6 ∧ dRow2Le C w3 w5 w6 d) := by
        rintro ⟨hb, hd'⟩
        exact hAB ⟨Or.inr hb, hd'⟩
      have hAf : ¬ ((Y3WeightCondA C w3 w5 w6 ∧ ¬ Y3WeightCondB C w3 w5 w6) ∧
          dRow2Le C w3 w5 w6 d) := by
        rintro ⟨hA, hd'⟩
        exact hAB ⟨Or.inl hA.1, hd'⟩
      rw [if_neg hAB, if_neg hBf, if_neg hAf]
  have hsplit : (∑ w3 ∈ Finset.Icc 0 (count C 3),
        ∑ w5 ∈ Finset.Icc 0 (count C 5),
          ∑ w6 ∈ Finset.Icc 0 (count C 6),
            if (Y3WeightCondA C w3 w5 w6 ∨ Y3WeightCondB C w3 w5 w6) ∧
                dRow2Le C w3 w5 w6 d then T w3 w5 w6 else 0) =
      Bsum + (∑ w3 ∈ Finset.Icc 0 (count C 3),
        ∑ w5 ∈ Finset.Icc 0 (count C 5),
          ∑ w6 ∈ Finset.Icc 0 (count C 6),
            if (Y3WeightCondA C w3 w5 w6 ∧ ¬ Y3WeightCondB C w3 w5 w6) ∧
       dRow2Le C w3 w5 w6 d then T w3 w5 w6 else 0) := by
    unfold Bsum
    simp_rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro w3 hw3
    apply Finset.sum_congr rfl; intro w5 hw5
    apply Finset.sum_congr rfl; intro w6 hw6
    exact hpoint w3 w5 w6
  have hApos : 1 ≤ (∑ w3 ∈ Finset.Icc 0 (count C 3),
        ∑ w5 ∈ Finset.Icc 0 (count C 5),
          ∑ w6 ∈ Finset.Icc 0 (count C 6),
            if (Y3WeightCondA C w3 w5 w6 ∧ ¬ Y3WeightCondB C w3 w5 w6) ∧
                dRow2Le C w3 w5 w6 d then T w3 w5 w6 else 0) := by
    let f : ℕ → ℕ → ℕ → ℕ := fun w3 w5 w6 =>
      if (Y3WeightCondA C w3 w5 w6 ∧ ¬ Y3WeightCondB C w3 w5 w6) ∧
          dRow2Le C w3 w5 w6 d then T w3 w5 w6 else 0
    have hmem3 : (0 : ℕ) ∈ Finset.Icc 0 (count C 3) := by simp
    have hmem5 : (0 : ℕ) ∈ Finset.Icc 0 (count C 5) := by simp
    have hmem6 : (count C 6) ∈ Finset.Icc 0 (count C 6) := by simp
    have hval : f 0 0 (count C 6) = 1 := by
      dsimp [f]
      rw [if_pos hcond, hT1]
    have h6 : (∑ w6 ∈ Finset.Icc 0 (count C 6), f 0 0 w6) ≥ 1 := by
      calc
        (∑ w6 ∈ Finset.Icc 0 (count C 6), f 0 0 w6) ≥ f 0 0 (count C 6) :=
          Finset.single_le_sum (s := Finset.Icc 0 (count C 6))
            (f := fun w6 => f 0 0 w6)
            (by intro w6 _; exact Nat.zero_le _) hmem6
        _ = 1 := hval
    have h5 : (∑ w5 ∈ Finset.Icc 0 (count C 5), ∑ w6 ∈ Finset.Icc 0 (count C 6), f 0 w5 w6) ≥ 1 := by
      calc
        (∑ w5 ∈ Finset.Icc 0 (count C 5), ∑ w6 ∈ Finset.Icc 0 (count C 6), f 0 w5 w6)
            ≥ ∑ w6 ∈ Finset.Icc 0 (count C 6), f 0 0 w6 :=
          Finset.single_le_sum (s := Finset.Icc 0 (count C 5))
            (f := fun w5 => ∑ w6 ∈ Finset.Icc 0 (count C 6), f 0 w5 w6)
            (by intro w5 _; exact Nat.zero_le _) hmem5
        _ ≥ 1 := h6
    calc
      (∑ w3 ∈ Finset.Icc 0 (count C 3),
          ∑ w5 ∈ Finset.Icc 0 (count C 5),
            ∑ w6 ∈ Finset.Icc 0 (count C 6), f w3 w5 w6)
          ≥ ∑ w5 ∈ Finset.Icc 0 (count C 5), ∑ w6 ∈ Finset.Icc 0 (count C 6), f 0 w5 w6 :=
        Finset.single_le_sum (s := Finset.Icc 0 (count C 3))
          (f := fun w3 => ∑ w5 ∈ Finset.Icc 0 (count C 5), ∑ w6 ∈ Finset.Icc 0 (count C 6), f w3 w5 w6)
          (by intro w3 _; exact Nat.zero_le _) hmem3
      _ ≥ 1 := h5
  have hAB := alpha3_cumulative_eq_threshold_AB C t d htypes h1 hcol
  have hge : (∑ i ∈ Finset.Icc 1 d, alpha3 C t i) ≥ Bsum + 1 := by
    rw [hAB, hsplit]
    omega
  have hB : Bsum = W3Sum C d := by
    unfold Bsum
    exact (alpha3_threshold_eq_W3Sum C d hpar53 h35 htotal h1)
  have h5 : (∑ i ∈ Finset.Icc 0 (d - 1), alpha5 C t i) = W5Sum C d := by
    rw [alpha5_cumulative_eq_threshold C t d (by omega : 1 ≤ d) htypes h1 hcol]
    exact alpha5_threshold_eq_W5Sum C d (by omega : 1 ≤ d) hpar35 hpar36 htotal h1 h35
  have hW5le : W5Sum C d ≤ Bsum := by
    calc
      W5Sum C d ≤ W3primeSum C d := W5Sum_le_W3primeSum C d hpar36 h36 hpos
      _ ≤ W3primeSumWide C d := W3primeSum_le_W3primeSumWide C d hpar36 h36
      _ = W3Sum C d := (W3Sum_eq_W3primeSum C d hpar36 hpar35 hpar53 h36 h35).symm
      _ = Bsum := hB.symm
  have hchain : (∑ i ∈ Finset.Icc 0 (d - 1), alpha5 C t i) + 1 ≤
      ∑ i ∈ Finset.Icc 1 d, alpha3 C t i := by
    rw [h5]
    exact le_trans (Nat.add_le_add_right hW5le 1) hge
  unfold Psi
  exact sub_pos.mpr (by exact_mod_cast hchain)

/-- With |3| = 0 the W5 set is empty, so the cumulative α⁵ sum is zero. -/
lemma class1_alpha5_sum_zero {n : ℕ} (C : Code n) (t : Fin n) (d : ℕ) (hd : 1 ≤ d)
    (htypes : ∀ u : Fin n, colVal (C u) = 1 ∨ colVal (C u) = 3 ∨
      colVal (C u) = 5 ∨ colVal (C u) = 6)
    (h1 : count C 1 = 1) (hcol : C t = col1)
    (hpar35 : Even (count C 5) ↔ Even (count C 6))
    (hpar36 : Even (count C 3) ↔ Even (count C 6))
    (_hpar53 : Even (count C 5) ↔ Even (count C 3))
    (h35 : count C 3 ≤ count C 5) (_h36 : count C 3 ≤ count C 6)
    (htotal : totalCounts C {1, 3, 5, 6} = n) (h0 : count C 3 = 0) :
    (∑ i ∈ Finset.Icc 0 (d - 1), alpha5 C t i) = 0 := by
  have hW5 : W5Sum C d = 0 := by
    unfold W5Sum
    apply Finset.sum_eq_zero
    intro w3 hw3
    have hw3 : w3 = 0 := by
      have hw3le : w3 ≤ count C 3 := (Finset.mem_Icc.mp hw3).2
      omega
    apply Finset.sum_eq_zero
    intro w6 hw6
    by_cases hW : W5mem C d w3 w6
    · exfalso
      rcases hW with ⟨hsum, hdiff, _, _, _⟩
      rw [hw3] at hsum hdiff
      omega
    · rw [if_neg hW]
  rw [alpha5_cumulative_eq_threshold C t d hd htypes h1 hcol]
  rw [alpha5_threshold_eq_W5Sum C d hd hpar35 hpar36 htotal h1 h35]
  exact hW5

/-- `thm:11` (Theorem 16) |3| = 0 case: `Psi d ≥ 0` for all d (with |3| = 0, `Σα⁵ = 0`). -/
lemma class1_psi_nonneg_zero {n : ℕ} (C : Code n) (t : Fin n) (d : ℕ) (hd : 1 ≤ d)
    (htypes : ∀ u : Fin n, colVal (C u) = 1 ∨ colVal (C u) = 3 ∨
      colVal (C u) = 5 ∨ colVal (C u) = 6)
    (h1 : count C 1 = 1) (hcol : C t = col1)
    (hpar35 : Even (count C 5) ↔ Even (count C 6))
    (hpar36 : Even (count C 3) ↔ Even (count C 6))
    (hpar53 : Even (count C 5) ↔ Even (count C 3))
    (h35 : count C 3 ≤ count C 5) (h36 : count C 3 ≤ count C 6)
    (htotal : totalCounts C {1, 3, 5, 6} = n) (h0 : count C 3 = 0) :
    Psi C t d ≥ 0 := by
  have h5 : (∑ i ∈ Finset.Icc 0 (d - 1), alpha5 C t i) = 0 :=
    class1_alpha5_sum_zero C t d hd htypes h1 hcol hpar35 hpar36 hpar53 h35 h36 htotal h0
  unfold Psi
  have h5z : (∑ i ∈ Finset.Icc 0 (d - 1), (alpha5 C t i : ℤ)) = 0 := by
    exact_mod_cast h5
  rw [h5z]
  simp
  exact_mod_cast (Nat.zero_le (∑ i ∈ Finset.Icc 1 d, alpha3 C t i))

/-- `thm:11` (Theorem 16) |3| = 0 strictness: with |3| = 0 the W5 set is empty, so
`Σα⁵ = 0`, while the Y3 weight-sum is positive at `d = n` (a branch-A or
branch-B word exists); hence `Psi n > 0`. -/
lemma class1_psi_pos_zero {n : ℕ} (C : Code n) (t : Fin n)
    (htypes : ∀ u : Fin n, colVal (C u) = 1 ∨ colVal (C u) = 3 ∨
      colVal (C u) = 5 ∨ colVal (C u) = 6)
    (h1 : count C 1 = 1) (hcol : C t = col1)
    (hpar35 : Even (count C 5) ↔ Even (count C 6))
    (hpar36 : Even (count C 3) ↔ Even (count C 6))
    (hpar53 : Even (count C 5) ↔ Even (count C 3))
    (h35 : count C 3 ≤ count C 5) (h36 : count C 3 ≤ count C 6)
    (htotal : totalCounts C {1, 3, 5, 6} = n)
    (h0 : count C 3 = 0) (hpos56 : 2 ≤ count C 5 + count C 6) :
    Psi C t n > 0 := by
  have hn : 1 ≤ n := by
    have h1' : 1 ≤ count C 1 := by rw [h1]
    have hle : count C 1 ≤ n := by
      calc
        count C 1 ≤ ∑ i ∈ ({1, 3, 5, 6} : Finset ℕ), count C i := by
          exact Finset.single_le_sum (by intro i _; exact Nat.zero_le _) (by simp)
        _ = n := htotal
    omega
  have h5 : (∑ i ∈ Finset.Icc 0 (n - 1), alpha5 C t i) = 0 := by
    exact class1_alpha5_sum_zero C t n hn htypes h1 hcol hpar35 hpar36 hpar53 h35 h36 htotal h0
  have hAB := alpha3_cumulative_eq_threshold_AB C t n htypes h1 hcol
  have hα3pos : 1 ≤ ∑ i ∈ Finset.Icc 1 n, alpha3 C t i := by
    let T : ℕ → ℕ → ℕ → ℕ := fun w3 w5 w6 =>
      Nat.choose (count C 3) w3 * Nat.choose (count C 5) w5 * Nat.choose (count C 6) w6
    by_cases hb : 2 ≤ count C 6
    · -- branch B word at (0, |5|/2, |6|/2+1)
      have hc5e : Even (count C 5) := (hpar53).2 (by rw [h0]; exact ⟨0, rfl⟩)
      have hc6e : Even (count C 6) := (hpar36).1 (by rw [h0]; exact ⟨0, rfl⟩)
      rcases hc5e with ⟨k5, hk5⟩
      rcases hc6e with ⟨k6, hk6⟩
      have hdiv5 : count C 5 / 2 = k5 := by
        have hk5' : count C 5 = 2 * k5 := by omega
        rw [hk5', Nat.mul_div_right k5 (by decide : 0 < 2)]
      have hdiv6 : count C 6 / 2 = k6 := by
        have hk6' : count C 6 = 2 * k6 := by omega
        rw [hk6', Nat.mul_div_right k6 (by decide : 0 < 2)]
      have hnsum : n = 1 + count C 5 + count C 6 := by
        calc
          n = ∑ i ∈ ({1, 3, 5, 6} : Finset ℕ), count C i := htotal.symm
          _ = 1 + count C 5 + count C 6 := by
            simp [h1, h0]
            omega
      have hcond : (Y3WeightCondA C 0 (count C 5 / 2) (count C 6 / 2 + 1) ∨
            Y3WeightCondB C 0 (count C 5 / 2) (count C 6 / 2 + 1)) ∧
          dRow2Le C 0 (count C 5 / 2) (count C 6 / 2 + 1) n := by
        constructor
        · right
          unfold Y3WeightCondB
          constructor <;> omega
        · unfold dRow2Le
          omega
      have hpos : 0 < Nat.choose (count C 3) 0 * Nat.choose (count C 5) (count C 5 / 2) *
          Nat.choose (count C 6) (count C 6 / 2 + 1) := by
        have hc5 : 0 < Nat.choose (count C 5) (count C 5 / 2) :=
          Nat.choose_pos (by omega : count C 5 / 2 ≤ count C 5)
        have hc6 : 0 < Nat.choose (count C 6) (count C 6 / 2 + 1) :=
          Nat.choose_pos (by
            have hk6' : count C 6 = 2 * k6 := by omega
            omega)
        exact Nat.mul_pos (Nat.mul_pos (by rw [h0]; norm_num) hc5) hc6
      let f : ℕ → ℕ → ℕ → ℕ := fun w3 w5 w6 =>
        if (Y3WeightCondA C w3 w5 w6 ∨ Y3WeightCondB C w3 w5 w6) ∧
            dRow2Le C w3 w5 w6 n then T w3 w5 w6 else 0
      have hval : f 0 (count C 5 / 2) (count C 6 / 2 + 1) ≥ 1 := by
        dsimp [f]
        rw [if_pos hcond]
        exact hpos
      have hmem3 : (0 : ℕ) ∈ Finset.Icc 0 (count C 3) := by simp
      have hmem5 : count C 5 / 2 ∈ Finset.Icc 0 (count C 5) := by
        exact Finset.mem_Icc.mpr ⟨Nat.zero_le _, Nat.div_le_self _ _⟩
      have hmem6 : count C 6 / 2 + 1 ∈ Finset.Icc 0 (count C 6) := by
        have hk6' : count C 6 = 2 * k6 := by omega
        apply Finset.mem_Icc.mpr
        constructor
        · exact Nat.zero_le _
        · rw [hk6']
          omega
      have h6 : (∑ w6 ∈ Finset.Icc 0 (count C 6), f 0 (count C 5 / 2) w6) ≥ 1 := by
        calc
          (∑ w6 ∈ Finset.Icc 0 (count C 6), f 0 (count C 5 / 2) w6)
              ≥ f 0 (count C 5 / 2) (count C 6 / 2 + 1) :=
            Finset.single_le_sum (s := Finset.Icc 0 (count C 6))
              (f := fun w6 => f 0 (count C 5 / 2) w6)
              (by intro w6 _; exact Nat.zero_le _) hmem6
          _ ≥ 1 := hval
      have h5' : (∑ w5 ∈ Finset.Icc 0 (count C 5),
          ∑ w6 ∈ Finset.Icc 0 (count C 6), f 0 w5 w6) ≥ 1 := by
        calc
          (∑ w5 ∈ Finset.Icc 0 (count C 5), ∑ w6 ∈ Finset.Icc 0 (count C 6), f 0 w5 w6)
              ≥ ∑ w6 ∈ Finset.Icc 0 (count C 6), f 0 (count C 5 / 2) w6 :=
            Finset.single_le_sum (s := Finset.Icc 0 (count C 5))
              (f := fun w5 => ∑ w6 ∈ Finset.Icc 0 (count C 6), f 0 w5 w6)
              (by intro w5 _; exact Nat.zero_le _) hmem5
          _ ≥ 1 := h6
      have hge' : (∑ w3 ∈ Finset.Icc 0 (count C 3),
          ∑ w5 ∈ Finset.Icc 0 (count C 5),
            ∑ w6 ∈ Finset.Icc 0 (count C 6), f w3 w5 w6) ≥ 1 := by
        calc
          (∑ w3 ∈ Finset.Icc 0 (count C 3),
              ∑ w5 ∈ Finset.Icc 0 (count C 5),
                ∑ w6 ∈ Finset.Icc 0 (count C 6), f w3 w5 w6)
              ≥ ∑ w5 ∈ Finset.Icc 0 (count C 5), ∑ w6 ∈ Finset.Icc 0 (count C 6), f 0 w5 w6 :=
            Finset.single_le_sum (s := Finset.Icc 0 (count C 3))
              (f := fun w3 => ∑ w5 ∈ Finset.Icc 0 (count C 5), ∑ w6 ∈ Finset.Icc 0 (count C 6), f w3 w5 w6)
              (by intro w3 _; exact Nat.zero_le _) hmem3
          _ ≥ 1 := h5'
      rw [hAB]
      exact hge'
    · -- branch A word at (0, 0, 0)
      have hb0 : count C 6 = 0 := by
        have h6e : Even (count C 6) := (hpar36).1 (by rw [h0]; exact ⟨0, rfl⟩)
        rcases h6e with ⟨k, hk⟩
        have : count C 6 ≤ 1 := by omega
        omega
      have hcond : (Y3WeightCondA C 0 0 0 ∨ Y3WeightCondB C 0 0 0) ∧
          dRow2Le C 0 0 0 n := by
        constructor
        · left
          unfold Y3WeightCondA
          constructor <;> omega
        · unfold dRow2Le
          omega
      have hpos : 0 < Nat.choose (count C 3) 0 * Nat.choose (count C 5) 0 *
          Nat.choose (count C 6) 0 := by
        norm_num
      let f : ℕ → ℕ → ℕ → ℕ := fun w3 w5 w6 =>
        if (Y3WeightCondA C w3 w5 w6 ∨ Y3WeightCondB C w3 w5 w6) ∧
            dRow2Le C w3 w5 w6 n then T w3 w5 w6 else 0
      have hval : f 0 0 0 ≥ 1 := by
        dsimp [f]
        rw [if_pos hcond]
        exact hpos
      have hmem3 : (0 : ℕ) ∈ Finset.Icc 0 (count C 3) := by simp
      have hmem5 : (0 : ℕ) ∈ Finset.Icc 0 (count C 5) := by simp
      have hmem6 : (0 : ℕ) ∈ Finset.Icc 0 (count C 6) := by simp
      have h6 : (∑ w6 ∈ Finset.Icc 0 (count C 6), f 0 0 w6) ≥ 1 := by
        calc
          (∑ w6 ∈ Finset.Icc 0 (count C 6), f 0 0 w6) ≥ f 0 0 0 :=
            Finset.single_le_sum (s := Finset.Icc 0 (count C 6))
              (f := fun w6 => f 0 0 w6)
              (by intro w6 _; exact Nat.zero_le _) hmem6
          _ ≥ 1 := hval
      have h5' : (∑ w5 ∈ Finset.Icc 0 (count C 5), ∑ w6 ∈ Finset.Icc 0 (count C 6), f 0 w5 w6) ≥ 1 := by
        calc
          (∑ w5 ∈ Finset.Icc 0 (count C 5), ∑ w6 ∈ Finset.Icc 0 (count C 6), f 0 w5 w6)
              ≥ ∑ w6 ∈ Finset.Icc 0 (count C 6), f 0 0 w6 :=
            Finset.single_le_sum (s := Finset.Icc 0 (count C 5))
              (f := fun w5 => ∑ w6 ∈ Finset.Icc 0 (count C 6), f 0 w5 w6)
              (by intro w5 _; exact Nat.zero_le _) hmem5
          _ ≥ 1 := h6
      have hge' : (∑ w3 ∈ Finset.Icc 0 (count C 3),
          ∑ w5 ∈ Finset.Icc 0 (count C 5),
            ∑ w6 ∈ Finset.Icc 0 (count C 6), f w3 w5 w6) ≥ 1 := by
        calc
          (∑ w3 ∈ Finset.Icc 0 (count C 3),
              ∑ w5 ∈ Finset.Icc 0 (count C 5),
                ∑ w6 ∈ Finset.Icc 0 (count C 6), f w3 w5 w6)
              ≥ ∑ w5 ∈ Finset.Icc 0 (count C 5), ∑ w6 ∈ Finset.Icc 0 (count C 6), f 0 w5 w6 :=
            Finset.single_le_sum (s := Finset.Icc 0 (count C 3))
              (f := fun w3 => ∑ w5 ∈ Finset.Icc 0 (count C 5), ∑ w6 ∈ Finset.Icc 0 (count C 6), f w3 w5 w6)
              (by intro w3 _; exact Nat.zero_le _) hmem3
          _ ≥ 1 := h5'
      rw [hAB]
      exact hge'
  have hchain : (∑ i ∈ Finset.Icc 0 (n - 1), alpha5 C t i) <
      ∑ i ∈ Finset.Icc 1 n, alpha3 C t i := by
    rw [h5]
    exact lt_of_lt_of_le (by norm_num : 0 < 1) hα3pos
  unfold Psi
  exact sub_pos.mpr (by exact_mod_cast hchain)

/-- `thm:11` (Theorem 16) canonical strict case: |1| = 1 and |3| = min > 0 with |3| < |6|
(so n > 3); replacing the type-1 column by `col3` is strictly better. -/
lemma class1_one_col3_strict {n : ℕ} (C : Code n) (t : Fin n)
    (htypes : ∀ u : Fin n, colVal (C u) = 1 ∨ colVal (C u) = 3 ∨
      colVal (C u) = 5 ∨ colVal (C u) = 6)
    (h1 : count C 1 = 1) (hcol : C t = col1)
    (hpar35 : Even (count C 5) ↔ Even (count C 6))
    (hpar36 : Even (count C 3) ↔ Even (count C 6))
    (hpar53 : Even (count C 5) ↔ Even (count C 3))
    (h35 : count C 3 ≤ count C 5) (h36 : count C 3 ≤ count C 6)
    (htotal : totalCounts C {1, 3, 5, 6} = n)
    (hpos : 0 < count C 3) (hlt : count C 3 < count C 6) :
    UniversalStrictBetter (replaceColumn C t col3) C := by
  let C' : Code n := replaceColumn C t col3
  have hcol' : C' t = col3 := by simp [C', replaceColumn]
  have hsame : ∀ u : Fin n, u ≠ t → C' u = C u := by
    intro u hu
    simp [C', replaceColumn, hu]
  have hn : 1 ≤ n := by
    have h1' : 1 ≤ count C 1 := by rw [h1]
    have hle : count C 1 ≤ n := by
      calc
        count C 1 ≤ ∑ i ∈ ({1, 3, 5, 6} : Finset ℕ), count C i := by
          exact Finset.single_le_sum (by intro i _; exact Nat.zero_le _) (by simp)
        _ = n := htotal
    omega
  have h6 : 2 ≤ count C 6 := by omega
  have hge : ∀ d ∈ Finset.Icc 1 n, Psi C t d ≥ 0 := by
    intro d hd
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
    exact class1_psi_nonneg C t d hd1 htypes h1 hcol hpar35 hpar36 hpar53 h35 h36 htotal hpos
  have hgt : ∃ d ∈ Finset.Icc 1 n, Psi C t d > 0 := by
    refine ⟨n, by simp [Finset.mem_Icc, hn], ?_⟩
    exact class1_psi_pos C t hn htypes h1 hcol hpar35 hpar36 hpar53 h35 h36 htotal hpos hlt h6
  exact cumulative_strict C C' t hcol hcol' hsame hge hgt

/-- `thm:11` (Theorem 16) canonical equality case: |1| = 1, |3| = min > 0 and |3| = |6|
(covering in particular n = 4 with |3| = |5| = |6| = 1); replacing the type-1
column by `col3` is strictly better. -/
lemma class1_one_col3_strict_eq {n : ℕ} (C : Code n) (t : Fin n)
    (htypes : ∀ u : Fin n, colVal (C u) = 1 ∨ colVal (C u) = 3 ∨
      colVal (C u) = 5 ∨ colVal (C u) = 6)
    (h1 : count C 1 = 1) (hcol : C t = col1)
    (hpar35 : Even (count C 5) ↔ Even (count C 6))
    (hpar36 : Even (count C 3) ↔ Even (count C 6))
    (hpar53 : Even (count C 5) ↔ Even (count C 3))
    (h35 : count C 3 ≤ count C 5) (h36 : count C 3 ≤ count C 6)
    (htotal : totalCounts C {1, 3, 5, 6} = n)
    (hpos : 0 < count C 3) (heq : count C 3 = count C 6) :
    UniversalStrictBetter (replaceColumn C t col3) C := by
  let C' : Code n := replaceColumn C t col3
  have hcol' : C' t = col3 := by simp [C', replaceColumn]
  have hsame : ∀ u : Fin n, u ≠ t → C' u = C u := by
    intro u hu
    simp [C', replaceColumn, hu]
  have hn : 1 ≤ n := by
    have h1' : 1 ≤ count C 1 := by rw [h1]
    have hle : count C 1 ≤ n := by
      calc
        count C 1 ≤ ∑ i ∈ ({1, 3, 5, 6} : Finset ℕ), count C i := by
          exact Finset.single_le_sum (by intro i _; exact Nat.zero_le _) (by simp)
        _ = n := htotal
    omega
  have hd : count C 3 + 1 ≤ n := by
    have hle' : count C 3 + count C 6 + count C 1 ≤ n := by
      calc
        count C 3 + count C 6 + count C 1 ≤
            ∑ i ∈ ({1, 3, 5, 6} : Finset ℕ), count C i := by
          simp [Finset.sum_insert]
          omega
        _ = n := htotal
    omega
  have hge : ∀ d ∈ Finset.Icc 1 n, Psi C t d ≥ 0 := by
    intro d hd
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
    exact class1_psi_nonneg C t d hd1 htypes h1 hcol hpar35 hpar36 hpar53 h35 h36 htotal hpos
  have hgt : ∃ d ∈ Finset.Icc 1 n, Psi C t d > 0 := by
    refine ⟨n, by simp [Finset.mem_Icc, hn], ?_⟩
    exact class1_psi_pos_eq C t htypes h1 hcol hpar35 hpar36 hpar53 h35 h36 htotal hpos heq hd
  exact cumulative_strict C C' t hcol hcol' hsame hge hgt

/-- `thm:11` (Theorem 16) |3| = 0 case: |1| = 1, |3| = 0 (the minimizer) and
|5| + |6| ≥ 2 (true for a genuine code with n ≠ 3); replacing the type-1
column by `col3` is strictly better. -/
lemma class1_one_col3_strict_zero {n : ℕ} (C : Code n) (t : Fin n)
    (htypes : ∀ u : Fin n, colVal (C u) = 1 ∨ colVal (C u) = 3 ∨
      colVal (C u) = 5 ∨ colVal (C u) = 6)
    (h1 : count C 1 = 1) (hcol : C t = col1)
    (hpar35 : Even (count C 5) ↔ Even (count C 6))
    (hpar36 : Even (count C 3) ↔ Even (count C 6))
    (hpar53 : Even (count C 5) ↔ Even (count C 3))
    (h35 : count C 3 ≤ count C 5) (h36 : count C 3 ≤ count C 6)
    (htotal : totalCounts C {1, 3, 5, 6} = n)
    (h0 : count C 3 = 0) (hpos56 : 2 ≤ count C 5 + count C 6) :
    UniversalStrictBetter (replaceColumn C t col3) C := by
  let C' : Code n := replaceColumn C t col3
  have hcol' : C' t = col3 := by simp [C', replaceColumn]
  have hsame : ∀ u : Fin n, u ≠ t → C' u = C u := by
    intro u hu
    simp [C', replaceColumn, hu]
  have hn : 1 ≤ n := by
    have h1' : 1 ≤ count C 1 := by rw [h1]
    have hle : count C 1 ≤ n := by
      calc
        count C 1 ≤ ∑ i ∈ ({1, 3, 5, 6} : Finset ℕ), count C i := by
          exact Finset.single_le_sum (by intro i _; exact Nat.zero_le _) (by simp)
        _ = n := htotal
    omega
  have hge : ∀ d ∈ Finset.Icc 1 n, Psi C t d ≥ 0 := by
    intro d hd
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
    exact class1_psi_nonneg_zero C t d hd1 htypes h1 hcol hpar35 hpar36 hpar53 h35 h36 htotal h0
  have hgt : ∃ d ∈ Finset.Icc 1 n, Psi C t d > 0 := by
    refine ⟨n, by simp [Finset.mem_Icc, hn], ?_⟩
    exact class1_psi_pos_zero C t htypes h1 hcol hpar35 hpar36 hpar53 h35 h36 htotal h0 hpos56
  exact cumulative_strict C C' t hcol hcol' hsame hge hgt

/-- `thm:11` (Theorem 16) argmin = col5 reduction: when |5| is the strict minimizer, the
`swap12` equivalence (types 3↔5) reduces the comparison to the |3| = min
case. -/
lemma class1_one_col5_strict {n : ℕ} (C : Code n) (t : Fin n)
    (htypes : ∀ u : Fin n, colVal (C u) = 1 ∨ colVal (C u) = 3 ∨
      colVal (C u) = 5 ∨ colVal (C u) = 6)
    (h1 : count C 1 = 1) (hcol : C t = col1)
    (hpar35 : Even (count C 5) ↔ Even (count C 6))
    (_hpar36 : Even (count C 3) ↔ Even (count C 6))
    (hpar53 : Even (count C 5) ↔ Even (count C 3))
    (htotal : totalCounts C {1, 3, 5, 6} = n)
    (h5min : ¬ (count C 3 ≤ count C 5 ∧ count C 3 ≤ count C 6))
    (h56 : count C 5 ≤ count C 6) (hpos56 : 2 ≤ count C 5 + count C 6) :
    UniversalStrictBetter (replaceColumn C t col5) C := by
  let Cs : Code n := swap12Code C
  have hEq : Equivalent C Cs := Equivalent_swap12Code C
  have htypes' : ∀ u : Fin n, colVal (Cs u) = 1 ∨ colVal (Cs u) = 3 ∨
      colVal (Cs u) = 5 ∨ colVal (Cs u) = 6 := by
    intro u
    rcases htypes u with h1' | h3' | h5' | h6'
    · have hc : C u = col1 := (colVal_eq_one_iff_col1 (C u)).1 h1'
      exact Or.inl (by simp [Cs, swap12Code, hc, rowPermute_swap12_col1, colVal_col1])
    · have hc : C u = col3 := (colVal_eq_three_iff_col3 (C u)).1 h3'
      exact Or.inr (Or.inr (Or.inl (by simp [Cs, swap12Code, hc, rowPermute_swap12_col3, colVal_col5])))
    · have hc : C u = col5 := (colVal_eq_five_iff_col5 (C u)).1 h5'
      exact Or.inr (Or.inl (by simp [Cs, swap12Code, hc, rowPermute_swap12_col5, colVal_col3]))
    · have hc : C u = col6 := (colVal_eq_six_iff_col6 (C u)).1 h6'
      exact Or.inr (Or.inr (Or.inr (by simp [Cs, swap12Code, hc, rowPermute_swap12_col6, colVal_col6])))
  have hc1' : count Cs 1 = 1 := by
    rw [count_swap12Code_one C htypes, h1]
  have hcol' : Cs t = col1 := by
    simp [Cs, swap12Code, hcol, rowPermute_swap12_col1]
  have hc3' : count Cs 3 = count C 5 := count_swap12Code C htypes
  have hc5' : count Cs 5 = count C 3 := count_swap12Code_five C htypes
  have hc6' : count Cs 6 = count C 6 := count_swap12Code_six C htypes
  have hpar35' : Even (count Cs 5) ↔ Even (count Cs 6) := by
    rw [hc5', hc6']
    exact hpar53.symm.trans hpar35
  have hpar36' : Even (count Cs 3) ↔ Even (count Cs 6) := by
    rw [hc3', hc6']
    exact hpar35
  have hpar53' : Even (count Cs 5) ↔ Even (count Cs 3) := by
    rw [hc5', hc3']
    exact hpar53.symm
  have hnot35 : ¬ count C 3 ≤ count C 5 := by
    intro h35c
    by_cases h36c : count C 3 ≤ count C 6
    · exact h5min ⟨h35c, h36c⟩
    · have h63 : count C 6 < count C 3 := Nat.lt_of_not_ge h36c
      have h53 : count C 5 < count C 3 := lt_of_le_of_lt h56 h63
      omega
  have h35' : count Cs 3 ≤ count Cs 5 := by
    rw [hc3', hc5']
    omega
  have h36' : count Cs 3 ≤ count Cs 6 := by
    rw [hc3', hc6']
    exact h56
  have htotal' : totalCounts Cs {1, 3, 5, 6} = n := by
    unfold totalCounts
    calc
      (∑ i ∈ ({1, 3, 5, 6} : Finset ℕ), count Cs i)
          = 1 + count C 5 + count C 3 + count C 6 := by
        simp [hc1', hc3', hc5', hc6', Finset.sum_insert]
        omega
      _ = n := by
        have hsum : count C 1 + count C 3 + count C 5 + count C 6 = n := by
          calc
            count C 1 + count C 3 + count C 5 + count C 6
                = ∑ i ∈ ({1, 3, 5, 6} : Finset ℕ), count C i := by
                  simp [Finset.sum_insert]
                  omega
            _ = n := htotal
        omega
  have hEq' : ∀ s' : Column,
      Equivalent (replaceColumn C t s') (replaceColumn Cs t (rowPermute swap12 s')) := by
    intro s'
    refine ⟨swap12, Equiv.refl (Fin n), (fun _ => false), ?_⟩
    intro u
    by_cases hu : u = t
    · subst u
      simp [replaceColumn, Cs]
    · simp [replaceColumn, hu, Cs, swap12Code]
  have hEq5 : Equivalent (replaceColumn C t col5) (replaceColumn Cs t col3) := by
    simpa [rowPermute_swap12_col5] using (hEq' col5)
  by_cases hz : count Cs 3 = 0
  · -- |3|̃ = 0
    have hpos56' : 2 ≤ count Cs 5 + count Cs 6 := by
      rw [hc5', hc6']
      omega
    have hdom : UniversalStrictBetter (replaceColumn Cs t col3) Cs :=
      class1_one_col3_strict_zero Cs t htypes' hc1' hcol' hpar35' hpar36' hpar53' h35' h36' htotal' hz hpos56'
    exact universalStrictBetter_of_equivalent
      (replaceColumn C t col5) (replaceColumn Cs t col3) C Cs
      hEq5 hEq hdom
  · -- |3|̃ > 0
    have hpos' : 0 < count Cs 3 := by omega
    by_cases heq : count Cs 3 = count Cs 6
    · have hdom : UniversalStrictBetter (replaceColumn Cs t col3) Cs :=
        class1_one_col3_strict_eq Cs t htypes' hc1' hcol' hpar35' hpar36' hpar53' h35' h36' htotal' hpos' heq
      exact universalStrictBetter_of_equivalent
        (replaceColumn C t col5) (replaceColumn Cs t col3) C Cs
        hEq5 hEq hdom
    · have hlt : count Cs 3 < count Cs 6 := by omega
      have hdom : UniversalStrictBetter (replaceColumn Cs t col3) Cs :=
        class1_one_col3_strict Cs t htypes' hc1' hcol' hpar35' hpar36' hpar53' h35' h36' htotal' hpos' hlt
      exact universalStrictBetter_of_equivalent
        (replaceColumn C t col5) (replaceColumn Cs t col3) C Cs
        hEq5 hEq hdom

/-- For n = 3 there is no genuine Class-I code with |1| = 1: the parity
constraint forces the two linear-type columns to be equal, so two codewords
coincide. -/
-- native_decide: Contentful · n=3 · checked 2026-08-26
lemma no_classI_count1_distinct_n3 :
    ∀ C : Code 3, DistinctRows C → ClassI C → count C 1 = 1 → False := by
  intro C hdist h h1
  have hmain : ∀ C : Code 3,
      (∀ i j : Fin 4, i ≠ j → row C i ≠ row C j) →
      (Odd (count C 1) ∧ ((Even (count C 3) ∧ Even (count C 5) ∧ Even (count C 6)) ∨
        (Odd (count C 3) ∧ Odd (count C 5) ∧ Odd (count C 6))) ∧
        totalCounts C {1, 3, 5, 6} = 3) →
      count C 1 = 1 → False := by
    native_decide
  simpa [DistinctRows, ClassI] using (hmain C hdist h h1)

/-! ## λ-role-symmetry under the 3↔6 column swap (col6 case of `thm:11` (Theorem 16))

For a Class-I code whose minimizer is type 6 there is no code equivalence
(row permutation, column flip, or word-bit permutation) that swaps the roles
of types 3 and 6 while fixing type 1 (`CompanionNote.tex` item 9).  We
therefore prove a weaker but sufficient symmetry at the level of λ: the
column-wise swap `swap36Code` (types 3↔6, fixing 1 and 5) preserves λ via the
word bijection `flipOn (S36 C)` (flip the bits on the 3/6 positions), which
preserves `dCode`. -/

/-- Flip the bits of a word at every position in `S`. -/
def flipOn {n : ℕ} (S : Finset (Fin n)) (y : Word n) : Word n :=
  fun u => if u ∈ S then !(y u) else y u

/-- `flipOn` is an involution. -/
lemma flipOn_involutive {n : ℕ} (S : Finset (Fin n)) (y : Word n) :
    flipOn S (flipOn S y) = y := by
  funext u
  by_cases hu : u ∈ S <;> simp [flipOn, hu]

/-- Flipping the same positions of both words preserves their Hamming distance. -/
lemma hammingDist_flipOn_flipOn {n : ℕ} (S : Finset (Fin n)) (x y : Word n) :
    hammingDist (flipOn S x) (flipOn S y) = hammingDist x y := by
  unfold hammingDist
  congr 1
  funext u
  by_cases hu : u ∈ S <;> simp [bitXor, flipOn, hu]

/-- `flipOn S` as a word bijection (its own inverse). -/
def flipOnEquiv {n : ℕ} (S : Finset (Fin n)) : Word n ≃ Word n where
  toFun := flipOn S
  invFun := flipOn S
  left_inv := flipOn_involutive S
  right_inv := flipOn_involutive S

/-- The positions where `C` has a type-3 or type-6 column. -/
def S36 {n : ℕ} (C : Code n) : Finset (Fin n) :=
  Finset.univ.filter fun u => colVal (C u) = 3 ∨ colVal (C u) = 6

/-- Swap the roles of types 3 and 6 (fixing types 1 and 5) at every column. -/
def swap36Code {n : ℕ} (C : Code n) : Code n := fun u =>
  if colVal (C u) = 3 then col6 else if colVal (C u) = 6 then col3 else C u

/-- `colVal` of the 3↔6-swapped column. -/
lemma colVal_swap36Code {n : ℕ} (C : Code n)
    (htypes : ∀ u : Fin n, colVal (C u) = 1 ∨ colVal (C u) = 3 ∨
      colVal (C u) = 5 ∨ colVal (C u) = 6) (u : Fin n) :
    colVal (swap36Code C u) = if colVal (C u) = 3 then 6 else if colVal (C u) = 6 then 3 else colVal (C u) := by
  rcases htypes u with h1 | h3 | h5 | h6
  · simp [swap36Code, h1]
  · simp [swap36Code, h3, colVal_col6]
  · simp [swap36Code, h5]
  · simp [swap36Code, h6, colVal_col3]

/-- The 3↔6 swap preserves the type set {1,3,5,6}. -/
lemma types_swap36Code {n : ℕ} (C : Code n)
    (htypes : ∀ u : Fin n, colVal (C u) = 1 ∨ colVal (C u) = 3 ∨
      colVal (C u) = 5 ∨ colVal (C u) = 6) (u : Fin n) :
    colVal (swap36Code C u) = 1 ∨ colVal (swap36Code C u) = 3 ∨
      colVal (swap36Code C u) = 5 ∨ colVal (swap36Code C u) = 6 := by
  rcases htypes u with h1 | h3 | h5 | h6
  · simp [swap36Code, h1]
  · simp [swap36Code, h3, colVal_col6]
  · simp [swap36Code, h5]
  · simp [swap36Code, h6, colVal_col3]

/-- The 3↔6 swap fixes type-1 columns. -/
lemma count_swap36Code_one {n : ℕ} (C : Code n)
    (htypes : ∀ u : Fin n, colVal (C u) = 1 ∨ colVal (C u) = 3 ∨
      colVal (C u) = 5 ∨ colVal (C u) = 6) :
    count (swap36Code C) 1 = count C 1 := by
  unfold count swap36Code
  apply Finset.sum_congr rfl
  intro u _
  rcases htypes u with h1 | h3 | h5 | h6
  · simp [h1]
  · simp [h3, colVal_col6]
  · simp [h5]
  · simp [h6, colVal_col3]

/-- The 3↔6 swap sends type-3 columns to type-6 ones, so |3|̃ = |6|. -/
lemma count_swap36Code_three {n : ℕ} (C : Code n)
    (htypes : ∀ u : Fin n, colVal (C u) = 1 ∨ colVal (C u) = 3 ∨
      colVal (C u) = 5 ∨ colVal (C u) = 6) :
    count (swap36Code C) 3 = count C 6 := by
  unfold count swap36Code
  apply Finset.sum_congr rfl
  intro u _
  rcases htypes u with h1 | h3 | h5 | h6
  · simp [h1]
  · simp [h3, colVal_col6]
  · simp [h5]
  · simp [h6, colVal_col3]

/-- The 3↔6 swap fixes type-5 columns. -/
lemma count_swap36Code_five {n : ℕ} (C : Code n)
    (htypes : ∀ u : Fin n, colVal (C u) = 1 ∨ colVal (C u) = 3 ∨
      colVal (C u) = 5 ∨ colVal (C u) = 6) :
    count (swap36Code C) 5 = count C 5 := by
  unfold count swap36Code
  apply Finset.sum_congr rfl
  intro u _
  rcases htypes u with h1 | h3 | h5 | h6
  · simp [h1]
  · simp [h3, colVal_col6]
  · simp [h5]
  · simp [h6, colVal_col3]

/-- The 3↔6 swap sends type-6 columns to type-3 ones, so |6|̃ = |3|. -/
lemma count_swap36Code_six {n : ℕ} (C : Code n)
    (htypes : ∀ u : Fin n, colVal (C u) = 1 ∨ colVal (C u) = 3 ∨
      colVal (C u) = 5 ∨ colVal (C u) = 6) :
    count (swap36Code C) 6 = count C 3 := by
  unfold count swap36Code
  apply Finset.sum_congr rfl
  intro u _
  rcases htypes u with h1 | h3 | h5 | h6
  · simp [h1]
  · simp [h3, colVal_col6]
  · simp [h5]
  · simp [h6, colVal_col3]

/-- Row 0 is all-zero and unchanged by the 3↔6 swap. -/
lemma row0_swap36Code {n : ℕ} (C : Code n)
    (htypes : ∀ u : Fin n, colVal (C u) = 1 ∨ colVal (C u) = 3 ∨
      colVal (C u) = 5 ∨ colVal (C u) = 6) :
    row0 (swap36Code C) = row0 C := by
  funext u
  rcases htypes u with h1 | h3 | h5 | h6
  · have hc : C u = col1 := (colVal_eq_one_iff_col1 (C u)).1 h1
    simp [swap36Code, hc, colVal_col1, row0, row, colBit]
  · have hc : C u = col3 := (colVal_eq_three_iff_col3 (C u)).1 h3
    simp [swap36Code, hc, colVal_col3, col6, col3, row0, row, colBit]
  · have hc : C u = col5 := (colVal_eq_five_iff_col5 (C u)).1 h5
    simp [swap36Code, hc, colVal_col5, row0, row, colBit]
  · have hc : C u = col6 := (colVal_eq_six_iff_col6 (C u)).1 h6
    simp [swap36Code, hc, colVal_col6, col3, col6, row0, row, colBit]

/-- Row 2 is the indicator of the 3/6 positions and is unchanged by the swap. -/
lemma row2_swap36Code {n : ℕ} (C : Code n)
    (htypes : ∀ u : Fin n, colVal (C u) = 1 ∨ colVal (C u) = 3 ∨
      colVal (C u) = 5 ∨ colVal (C u) = 6) :
    row2 (swap36Code C) = row2 C := by
  funext u
  rcases htypes u with h1 | h3 | h5 | h6
  · have hc : C u = col1 := (colVal_eq_one_iff_col1 (C u)).1 h1
    simp [swap36Code, hc, colVal_col1, row2, row, colBit]
  · have hc : C u = col3 := (colVal_eq_three_iff_col3 (C u)).1 h3
    simp [swap36Code, hc, colVal_col3, col6, col3, row2, row, colBit]
  · have hc : C u = col5 := (colVal_eq_five_iff_col5 (C u)).1 h5
    simp [swap36Code, hc, colVal_col5, row2, row, colBit]
  · have hc : C u = col6 := (colVal_eq_six_iff_col6 (C u)).1 h6
    simp [swap36Code, hc, colVal_col6, col3, col6, row2, row, colBit]

/-- Row 1 of the swapped code is row 1 of `C` with the bits on the 3/6
positions flipped. -/
lemma row1_swap36Code {n : ℕ} (C : Code n)
    (htypes : ∀ u : Fin n, colVal (C u) = 1 ∨ colVal (C u) = 3 ∨
      colVal (C u) = 5 ∨ colVal (C u) = 6) :
    row1 (swap36Code C) = flipOn (S36 C) (row1 C) := by
  funext u
  rcases htypes u with h1 | h3 | h5 | h6
  · have hc : C u = col1 := (colVal_eq_one_iff_col1 (C u)).1 h1
    simp [swap36Code, hc, colVal_col1, col1, row1, row, colBit, S36, flipOn]
  · have hc : C u = col3 := (colVal_eq_three_iff_col3 (C u)).1 h3
    simp [swap36Code, hc, colVal_col3, col6, col3, row1, row, colBit, S36, flipOn]
  · have hc : C u = col5 := (colVal_eq_five_iff_col5 (C u)).1 h5
    simp [swap36Code, hc, colVal_col5, col5, row1, row, colBit, S36, flipOn]
  · have hc : C u = col6 := (colVal_eq_six_iff_col6 (C u)).1 h6
    simp [swap36Code, hc, colVal_col6, col3, col6, row1, row, colBit, S36, flipOn]

/-- Row 3 of the swapped code is row 3 of `C` with the bits on the 3/6
positions flipped. -/
lemma row3_swap36Code {n : ℕ} (C : Code n)
    (htypes : ∀ u : Fin n, colVal (C u) = 1 ∨ colVal (C u) = 3 ∨
      colVal (C u) = 5 ∨ colVal (C u) = 6) :
    row3 (swap36Code C) = flipOn (S36 C) (row3 C) := by
  funext u
  rcases htypes u with h1 | h3 | h5 | h6
  · have hc : C u = col1 := (colVal_eq_one_iff_col1 (C u)).1 h1
    simp [swap36Code, hc, colVal_col1, col1, row3, row, colBit, S36, flipOn]
  · have hc : C u = col3 := (colVal_eq_three_iff_col3 (C u)).1 h3
    simp [swap36Code, hc, colVal_col3, col6, col3, row3, row, colBit, S36, flipOn]
  · have hc : C u = col5 := (colVal_eq_five_iff_col5 (C u)).1 h5
    simp [swap36Code, hc, colVal_col5, col5, row3, row, colBit, S36, flipOn]
  · have hc : C u = col6 := (colVal_eq_six_iff_col6 (C u)).1 h6
    simp [swap36Code, hc, colVal_col6, col3, col6, row3, row, colBit, S36, flipOn]

/-- Row 2 of `C` is the flip of the (all-zero) row 0 on the 3/6 positions. -/
lemma row2_eq_flipOn_row0 {n : ℕ} (C : Code n)
    (htypes : ∀ u : Fin n, colVal (C u) = 1 ∨ colVal (C u) = 3 ∨
      colVal (C u) = 5 ∨ colVal (C u) = 6) :
    row2 C = flipOn (S36 C) (row0 C) := by
  funext u
  rcases htypes u with h1 | h3 | h5 | h6
  · have hc : C u = col1 := (colVal_eq_one_iff_col1 (C u)).1 h1
    simp [hc, colVal_col1, col1, row2, row0, row, colBit, S36, flipOn]
  · have hc : C u = col3 := (colVal_eq_three_iff_col3 (C u)).1 h3
    simp [hc, colVal_col3, col3, row2, row0, row, colBit, S36, flipOn]
  · have hc : C u = col5 := (colVal_eq_five_iff_col5 (C u)).1 h5
    simp [hc, colVal_col5, col5, row2, row0, row, colBit, S36, flipOn]
  · have hc : C u = col6 := (colVal_eq_six_iff_col6 (C u)).1 h6
    simp [hc, colVal_col6, col6, row2, row0, row, colBit, S36, flipOn]

/-- The 3↔6 column swap preserves the code distance under the word bijection
`flipOn (S36 C)`. -/
lemma dCode_swap36Code {n : ℕ} (C : Code n)
    (htypes : ∀ u : Fin n, colVal (C u) = 1 ∨ colVal (C u) = 3 ∨
      colVal (C u) = 5 ∨ colVal (C u) = 6) (y : Word n) :
    dCode (swap36Code C) (flipOn (S36 C) y) = dCode C y := by
  have hrow0 : row0 (swap36Code C) = row0 C := row0_swap36Code C htypes
  have hrow2 : row2 (swap36Code C) = row2 C := row2_swap36Code C htypes
  have hrow1 : row1 (swap36Code C) = flipOn (S36 C) (row1 C) := row1_swap36Code C htypes
  have hrow3 : row3 (swap36Code C) = flipOn (S36 C) (row3 C) := row3_swap36Code C htypes
  have hrow0φ : row0 C = flipOn (S36 C) (row2 C) := by
    rw [row2_eq_flipOn_row0 C htypes, flipOn_involutive]
  have hd0 : hammingDist (row0 (swap36Code C)) (flipOn (S36 C) y) =
      hammingDist (row2 C) y := by
    rw [hrow0, hrow0φ, hammingDist_flipOn_flipOn]
  have hd1 : hammingDist (row1 (swap36Code C)) (flipOn (S36 C) y) =
      hammingDist (row1 C) y := by
    rw [hrow1, hammingDist_flipOn_flipOn]
  have hd2 : hammingDist (row2 (swap36Code C)) (flipOn (S36 C) y) =
      hammingDist (row0 C) y := by
    rw [hrow2, row2_eq_flipOn_row0 C htypes, hammingDist_flipOn_flipOn]
  have hd3 : hammingDist (row3 (swap36Code C)) (flipOn (S36 C) y) =
      hammingDist (row3 C) y := by
    rw [hrow3, hammingDist_flipOn_flipOn]
  unfold dCode
  rw [hd0, hd1, hd2, hd3]
  simp [Nat.min_left_comm]

/-- The 3↔6 column swap preserves λ for every ε. -/
lemma lambda_swap36 {n : ℕ} (C : Code n)
    (htypes : ∀ u : Fin n, colVal (C u) = 1 ∨ colVal (C u) = 3 ∨
      colVal (C u) = 5 ∨ colVal (C u) = 6) (ε : ℝ) :
    lambda (swap36Code C) ε = lambda C ε := by
  unfold lambda
  congr 1
  let g : Word n ≃ Word n := flipOnEquiv (S36 C)
  have hdcode : ∀ y : Word n, dCode (swap36Code C) (g y) = dCode C y := by
    intro y
    exact dCode_swap36Code C htypes y
  calc
    (∑ y : Word n, weight n ε (dCode (swap36Code C) y))
        = ∑ y : Word n, weight n ε (dCode (swap36Code C) (g y)) := by
          apply Finset.sum_bij (fun y _ => g.symm y)
          · intro y _; simp
          · intro a _ b _ hab
            exact g.symm.injective hab
          · intro b _
            refine ⟨g b, by simp, by simp⟩
          · intro y _; simp
    _ = ∑ y : Word n, weight n ε (dCode C y) := by
          simp [hdcode]

/-- `thm:11` (Theorem 16) col6: swapping the roles of types 3 and 6 preserves λ for
type-{1,3,5,6} codes (not a code equivalence; see `CompanionNote.tex` item 9). -/
lemma class1_lambda_swap36 {n : ℕ} (C : Code n)
    (htypes : ∀ u : Fin n, colVal (C u) = 1 ∨ colVal (C u) = 3 ∨
      colVal (C u) = 5 ∨ colVal (C u) = 6) :
    UniversalEqual (swap36Code C) C := by
  intro ε _ _
  exact lambda_swap36 C htypes ε

/-- Lift a strict comparison of the 3↔6-swapped code to one of the original
code, using the λ-role-symmetry on both sides. -/
lemma class1_col6_from_dom {n : ℕ} (C : Code n) (t : Fin n)
    (htypes : ∀ u : Fin n, colVal (C u) = 1 ∨ colVal (C u) = 3 ∨
      colVal (C u) = 5 ∨ colVal (C u) = 6)
    (hdom : UniversalStrictBetter (replaceColumn (swap36Code C) t col3) (swap36Code C)) :
    UniversalStrictBetter (replaceColumn C t col6) C := by
  let C' : Code n := replaceColumn C t col6
  let C36 : Code n := swap36Code C
  let C36' : Code n := replaceColumn C36 t col3
  have htypes' : ∀ u : Fin n, colVal (C' u) = 1 ∨ colVal (C' u) = 3 ∨
      colVal (C' u) = 5 ∨ colVal (C' u) = 6 := by
    intro u
    by_cases hu : u = t
    · subst u
      simp [C', replaceColumn, colVal_col6]
    · simp [C', replaceColumn, hu, htypes u]
  have hswap : swap36Code C' = C36' := by
    funext u
    by_cases hu : u = t
    · subst u
      simp [C', C36', replaceColumn, swap36Code, colVal_col6]
    · simp [C', C36', C36, replaceColumn, swap36Code, hu]
  have hsymC : UniversalEqual C36 C := class1_lambda_swap36 C htypes
  have hsymC' : UniversalEqual C36' C' := by
    rw [← hswap]
    exact class1_lambda_swap36 C' htypes'
  intro ε hε0 hε1
  have heq1 : lambda C' ε = lambda C36' ε := (hsymC' ε hε0 hε1).symm
  have hgt : lambda C36' ε > lambda C36 ε := hdom ε hε0 hε1
  have heq2 : lambda C36 ε = lambda C ε := hsymC ε hε0 hε1
  linarith

/-- `thm:11` (Theorem 16) argmin = col6 reduction: when |6| is the minimizer, the 3↔6
λ-role-symmetry (`class1_lambda_swap36`) reduces the comparison to the
|3| = min case on the swapped code. -/
lemma class1_one_col6_strict {n : ℕ} (C : Code n) (t : Fin n)
    (htypes : ∀ u : Fin n, colVal (C u) = 1 ∨ colVal (C u) = 3 ∨
      colVal (C u) = 5 ∨ colVal (C u) = 6)
    (h1 : count C 1 = 1) (hcol : C t = col1)
    (hpar35 : Even (count C 5) ↔ Even (count C 6))
    (hpar36 : Even (count C 3) ↔ Even (count C 6))
    (hpar53 : Even (count C 5) ↔ Even (count C 3))
    (h36 : count C 6 ≤ count C 3) (h56 : count C 6 ≤ count C 5)
    (htotal : totalCounts C {1, 3, 5, 6} = n)
    (hpos35 : 2 ≤ count C 3 + count C 5) :
    UniversalStrictBetter (replaceColumn C t col6) C := by
  let C36 : Code n := swap36Code C
  have htypes36 : ∀ u : Fin n, colVal (C36 u) = 1 ∨ colVal (C36 u) = 3 ∨
      colVal (C36 u) = 5 ∨ colVal (C36 u) = 6 := by
    intro u
    exact types_swap36Code C htypes u
  have h136 : count C36 1 = 1 := by
    rw [count_swap36Code_one C htypes, h1]
  have hcol36 : C36 t = col1 := by
    dsimp [C36]
    simp [swap36Code, hcol, colVal_col1]
  have hc336 : count C36 3 = count C 6 := count_swap36Code_three C htypes
  have hc536 : count C36 5 = count C 5 := count_swap36Code_five C htypes
  have hc636 : count C36 6 = count C 3 := count_swap36Code_six C htypes
  have hpar3536 : Even (count C36 5) ↔ Even (count C36 6) := by
    rw [hc536, hc636]
    exact hpar53
  have hpar3636 : Even (count C36 3) ↔ Even (count C36 6) := by
    rw [hc336, hc636]
    exact hpar36.symm
  have hpar5336 : Even (count C36 5) ↔ Even (count C36 3) := by
    rw [hc536, hc336]
    exact hpar35
  have h3536 : count C36 3 ≤ count C36 5 := by
    rw [hc336, hc536]
    exact h56
  have h3636 : count C36 3 ≤ count C36 6 := by
    rw [hc336, hc636]
    exact h36
  have htotal36 : totalCounts C36 {1, 3, 5, 6} = n := by
    unfold totalCounts
    calc
      (∑ i ∈ ({1, 3, 5, 6} : Finset ℕ), count C36 i)
          = count C 1 + count C 6 + count C 5 + count C 3 := by
            simp [hc336, hc536, hc636, Finset.sum_insert]
            omega
      _ = n := by
        have hsum : count C 1 + count C 3 + count C 5 + count C 6 = n := by
          calc
            count C 1 + count C 3 + count C 5 + count C 6
                = ∑ i ∈ ({1, 3, 5, 6} : Finset ℕ), count C i := by
                  simp [Finset.sum_insert]
                  omega
            _ = n := htotal
        omega
  by_cases hz : count C 6 = 0
  · -- |3|' = 0
    have hz36 : count C36 3 = 0 := by rw [hc336, hz]
    have hpos5636 : 2 ≤ count C36 5 + count C36 6 := by
      rw [hc536, hc636]
      omega
    have hdom : UniversalStrictBetter (replaceColumn C36 t col3) C36 :=
      class1_one_col3_strict_zero C36 t htypes36 h136 hcol36 hpar3536 hpar3636 hpar5336 h3536 h3636 htotal36 hz36 hpos5636
    exact class1_col6_from_dom C t htypes hdom
  · -- |3|' > 0
    have hpos36 : 0 < count C36 3 := by rw [hc336]; omega
    by_cases heq : count C36 3 = count C36 6
    · have hdom : UniversalStrictBetter (replaceColumn C36 t col3) C36 :=
        class1_one_col3_strict_eq C36 t htypes36 h136 hcol36 hpar3536 hpar3636 hpar5336 h3536 h3636 htotal36 hpos36 heq
      exact class1_col6_from_dom C t htypes hdom
    · have hlt : count C36 3 < count C36 6 := by omega
      have hdom : UniversalStrictBetter (replaceColumn C36 t col3) C36 :=
        class1_one_col3_strict C36 t htypes36 h136 hcol36 hpar3536 hpar3636 hpar5336 h3536 h3636 htotal36 hpos36 hlt
      exact class1_col6_from_dom C t htypes hdom

/-! ## Bounds from distinct rows (for the `class1_one` case split) -/

/-- With no type-5 or type-6 columns, rows 0 and 1 coincide (types 1 and 3
have no bit-1); `DistinctRows` rules this out. -/
lemma row0_eq_row1_of_no_five_six {n : ℕ} (C : Code n)
    (htypes : ∀ u : Fin n, colVal (C u) = 1 ∨ colVal (C u) = 3 ∨
      colVal (C u) = 5 ∨ colVal (C u) = 6)
    (h5 : count C 5 = 0) (h6 : count C 6 = 0) :
    row0 C = row1 C := by
  funext u
  rcases htypes u with h1' | h3' | h5' | h6'
  · have hc : C u = col1 := (colVal_eq_one_iff_col1 (C u)).1 h1'
    simp [hc, col1, row0, row1, row, colBit]
  · have hc : C u = col3 := (colVal_eq_three_iff_col3 (C u)).1 h3'
    simp [hc, col3, row0, row1, row, colBit]
  · have hpos : 1 ≤ count C 5 := count_pos_of_colVal C u h5'
    omega
  · have hpos : 1 ≤ count C 6 := count_pos_of_colVal C u h6'
    omega

/-- In a genuine code with |5| ≤ |6|, |5| + |6| ≥ 2: parity makes the pair
(0,1) impossible, and `DistinctRows` excludes |5| = |6| = 0 (rows 0 and 1
would coincide). -/
lemma class1_hpos56_of_count1 {n : ℕ} (C : Code n)
    (htypes : ∀ u : Fin n, colVal (C u) = 1 ∨ colVal (C u) = 3 ∨
      colVal (C u) = 5 ∨ colVal (C u) = 6)
    (hpar35 : Even (count C 5) ↔ Even (count C 6))
    (h56 : count C 5 ≤ count C 6) (hdist : DistinctRows C) :
    2 ≤ count C 5 + count C 6 := by
  by_contra hlt
  have hsumle : count C 5 + count C 6 ≤ 1 := by omega
  have hc5z : count C 5 = 0 := by omega
  have hc6e : Even (count C 6) := (hpar35.1) (by rw [hc5z]; exact ⟨0, rfl⟩)
  have hc6z : count C 6 = 0 := by
    rcases hc6e with ⟨k, hk⟩
    omega
  have hrow : row0 C = row1 C := row0_eq_row1_of_no_five_six C htypes hc5z hc6z
  have hne : row0 C ≠ row1 C := by
    exact hdist ⟨0, by decide⟩ ⟨1, by decide⟩ (by decide)
  exact hne hrow

/-- With |3| = 0, |5| + |6| ≥ 2: parity forces both even, so
|5| = |6| = 0 would make rows 0 and 1 coincide. -/
lemma class1_hpos56_of_c3zero {n : ℕ} (C : Code n)
    (htypes : ∀ u : Fin n, colVal (C u) = 1 ∨ colVal (C u) = 3 ∨
      colVal (C u) = 5 ∨ colVal (C u) = 6)
    (hpar53 : Even (count C 5) ↔ Even (count C 3))
    (hpar36 : Even (count C 3) ↔ Even (count C 6))
    (h0 : count C 3 = 0) (hdist : DistinctRows C) :
    2 ≤ count C 5 + count C 6 := by
  by_contra hlt
  have hsumle : count C 5 + count C 6 ≤ 1 := by omega
  have hc3e : Even (count C 3) := by rw [h0]; exact ⟨0, rfl⟩
  have hc5e : Even (count C 5) := hpar53.2 hc3e
  have hc6e : Even (count C 6) := hpar36.1 hc3e
  have hc5z : count C 5 = 0 := by
    rcases hc5e with ⟨k, hk⟩
    omega
  have hc6z : count C 6 = 0 := by
    rcases hc6e with ⟨k, hk⟩
    omega
  have hrow : row0 C = row1 C := row0_eq_row1_of_no_five_six C htypes hc5z hc6z
  have hne : row0 C ≠ row1 C := by
    exact hdist ⟨0, by decide⟩ ⟨1, by decide⟩ (by decide)
  exact hne hrow

/-- With |5| > |6|, |3| + |5| ≥ 2: |3| = 0 and |5| = 1 (forced by
|6| < |5| ≤ 1) would have opposite parities. -/
lemma class1_hpos35_of_count1 {n : ℕ} (C : Code n)
    (hpar53 : Even (count C 5) ↔ Even (count C 3))
    (h65 : count C 6 < count C 5) :
    2 ≤ count C 3 + count C 5 := by
  by_contra hlt
  have hsumle : count C 3 + count C 5 ≤ 1 := by omega
  have hc3z : count C 3 = 0 := by omega
  have hc5ge : 1 ≤ count C 5 := by omega
  have hc5e : Even (count C 5) := (hpar53.2) (by rw [hc3z]; exact ⟨0, rfl⟩)
  rcases hc5e with ⟨k, hk⟩
  omega

/-! ## `thm:301` (Theorem 17) (`class1_min`): |3| = min ∈ {0,1} with general odd |1|

The paper (§6.3) reduces `thm:301` (Theorem 17) to the case |3| = min ∈ {0,1}: Class-I-a
(|3| = 0: n odd, |5|,|6| even) and Class-I-b (|3| = 1: n even, |5|,|6| odd).
The |3| = 0 case is reduced here to a single binomial bound
(`class1_alpha3_cum_ge_alpha5_threshold`, paper eq. sa_2 vs eq. a3xs); the
|3| = 1 case is pending. -/

/-- With |3| = 0 every Y5 word lies at distance (n−1)/2 (paper eq. 5yc1):
the Y5 equations force d₂ = d₃+1, so d_C = d₃ = (|1|+|5|+|6|−1)/2. -/
lemma class1_alpha5_dist_eq_threshold {n : ℕ} (C : Code n) (t : Fin n)
    (htypes : ∀ u : Fin n, colVal (C u) = 1 ∨ colVal (C u) = 3 ∨
      colVal (C u) = 5 ∨ colVal (C u) = 6)
    (hcol : C t = col1) (h3 : count C 3 = 0)
    (htotal : totalCounts C {1, 3, 5, 6} = n) (y : Word n) (hy : Y5 C t y) :
    dCode C y = (n - 1) / 2 := by
  rcases (Y5_iff_col1 C t y hcol).1 hy with ⟨_hyt, hmin, hd2⟩
  have hd3d0 : dRow C 3 y ≤ dRow C 0 y := by
    have hle0 : dRow C 3 y + 2 ≤ dRow C 0 y := le_trans hmin (Nat.min_le_left _ _)
    omega
  have hd3d1 : dRow C 3 y ≤ dRow C 1 y := by
    have hle1 : dRow C 3 y + 2 ≤ dRow C 1 y := le_trans hmin (Nat.min_le_right _ _)
    omega
  have hd3d2 : dRow C 3 y < dRow C 2 y := by
    rw [hd2]
    omega
  have hdCode : dCode C y = dRow C 3 y := by
    unfold dCode
    rw [show hammingDist (row0 C) y = dRow C 0 y by rfl]
    rw [show hammingDist (row1 C) y = dRow C 1 y by rfl]
    rw [show hammingDist (row2 C) y = dRow C 2 y by rfl]
    rw [show hammingDist (row3 C) y = dRow C 3 y by rfl]
    rw [Nat.min_eq_right (le_of_lt hd3d2), Nat.min_eq_right hd3d1, Nat.min_eq_right hd3d0]
  have hw3 : w_i C 3 y = 0 := w_i_eq_zero_of_count_zero C 3 y h3
  have hw1le : w_i C 1 y ≤ count C 1 := w_i_le_count C 1 y
  have hw5le : w_i C 5 y ≤ count C 5 := w_i_le_count C 5 y
  have hw6le : w_i C 6 y ≤ count C 6 := w_i_le_count C 6 y
  have hd2' : dRow C 2 y = w_i C 1 y + (count C 3 - w_i C 3 y) + w_i C 5 y +
      (count C 6 - w_i C 6 y) := dRow2_of_type1356 C htypes y
  have hd3' : dRow C 3 y = (count C 1 - w_i C 1 y) + (count C 3 - w_i C 3 y) +
      (count C 5 - w_i C 5 y) + w_i C 6 y := dRow3_of_type1356 C htypes y
  have hmain : 2 * w_i C 6 y =
      2 * w_i C 1 y + 2 * w_i C 5 y + count C 6 - count C 1 - count C 5 - 1 := by
    have hd2d3 : dRow C 2 y = dRow C 3 y + 1 := hd2
    rw [hd2', hd3', hw3, h3] at hd2d3
    omega
  have h2d3 : 2 * dRow C 3 y = n - 1 := by
    have hsum : count C 1 + count C 3 + count C 5 + count C 6 = n := by
      calc
        count C 1 + count C 3 + count C 5 + count C 6
            = ∑ i ∈ ({1, 3, 5, 6} : Finset ℕ), count C i := by
              simp [Finset.sum_insert]
              omega
        _ = n := htotal
    rw [hd3', hw3, h3]
    rw [h3] at hsum
    omega
  have hdiv : dRow C 3 y = (n - 1) / 2 := by
    rw [← h2d3]
    rw [Nat.mul_div_right _ (by decide : 0 < 2)]
  rw [hdCode, hdiv]

/-- With |3| = 0, α⁵(d) = 0 unless d = (n−1)/2 (paper eq. 5yc1). -/
lemma class1_alpha5_eq_zero_of_ne_threshold {n : ℕ} (C : Code n) (t : Fin n) (d : ℕ)
    (htypes : ∀ u : Fin n, colVal (C u) = 1 ∨ colVal (C u) = 3 ∨
      colVal (C u) = 5 ∨ colVal (C u) = 6)
    (hcol : C t = col1) (h3 : count C 3 = 0)
    (htotal : totalCounts C {1, 3, 5, 6} = n) (hd : d ≠ (n - 1) / 2) :
    alpha5 C t d = 0 := by
  unfold alpha5
  by_contra h
  have hpos : 0 < (Finset.univ.filter fun y : Word n => Y5 C t y ∧ dCode C y = d).card := by
    exact Nat.pos_of_ne_zero h
  rcases Finset.card_pos.mp hpos with ⟨y, hmem⟩
  have hy5 : Y5 C t y := (Finset.mem_filter.mp hmem).2.1
  have hdc : dCode C y = (n - 1) / 2 :=
    class1_alpha5_dist_eq_threshold C t htypes hcol h3 htotal y hy5
  have hd' : dCode C y = d := (Finset.mem_filter.mp hmem).2.2
  exact hd (by omega)

/-! ### Class-I-a building blocks: Y5 weights and word counting -/

/-- `Y5` for a `{1,3,5,6}` code with |3| = 0 and general |1|, in the
division-free form of the paper's eq:5yc1–eq:5yc4: eq:5yc2, together with
the two inequalities eq:5yc3/eq:5yc4 (after substituting eq:5yc2). -/
lemma Y5_iff_weights_c3zero {n : ℕ} (C : Code n) (t : Fin n) (y : Word n)
    (htypes : ∀ u : Fin n, colVal (C u) = 1 ∨ colVal (C u) = 3 ∨
      colVal (C u) = 5 ∨ colVal (C u) = 6)
    (hcol : C t = col1) (h3 : count C 3 = 0) :
    Y5 C t y ↔ y t = true ∧
      w_i C 1 y + w_i C 5 y + (count C 6 - w_i C 6 y) =
        (count C 1 - w_i C 1 y) + (count C 5 - w_i C 5 y) + w_i C 6 y + 1 ∧
      count C 6 + 1 ≤ 2 * w_i C 6 y ∧
      2 * w_i C 5 y + 1 ≤ count C 5 := by
  have hw3 : w_i C 3 y = 0 := w_i_eq_zero_of_count_zero C 3 y h3
  have hw1le : w_i C 1 y ≤ count C 1 := w_i_le_count C 1 y
  have hw5le : w_i C 5 y ≤ count C 5 := w_i_le_count C 5 y
  have hw6le : w_i C 6 y ≤ count C 6 := w_i_le_count C 6 y
  have hd0 : dRow C 0 y = w_i C 1 y + w_i C 5 y + w_i C 6 y := by
    rw [dRow0_of_type1356 C htypes y, hw3]
    simp
  have hd1 : dRow C 1 y = w_i C 1 y + (count C 5 - w_i C 5 y) + (count C 6 - w_i C 6 y) := by
    rw [dRow1_of_type1356 C htypes y, hw3]
    simp
  have hd2' : dRow C 2 y = w_i C 1 y + w_i C 5 y + (count C 6 - w_i C 6 y) := by
    rw [dRow2_of_type1356 C htypes y, hw3, h3]
    simp
  have hd3 : dRow C 3 y = (count C 1 - w_i C 1 y) + (count C 5 - w_i C 5 y) + w_i C 6 y := by
    rw [dRow3_of_type1356 C htypes y, hw3, h3]
    simp
  rw [Y5_iff_col1 C t y hcol]
  constructor
  · intro h
    rcases h with ⟨hyt, hmin, hd2⟩
    have hd0ge : dRow C 3 y + 2 ≤ dRow C 0 y := (le_min_iff.mp hmin).1
    have hd1ge : dRow C 3 y + 2 ≤ dRow C 1 y := (le_min_iff.mp hmin).2
    have hcond1 : w_i C 1 y + w_i C 5 y + (count C 6 - w_i C 6 y) =
        (count C 1 - w_i C 1 y) + (count C 5 - w_i C 5 y) + w_i C 6 y + 1 := by
      rw [hd2', hd3] at hd2
      exact hd2
    have hcond2 : count C 6 + 1 ≤ 2 * w_i C 6 y := by
      have hd0ge' : w_i C 1 y + w_i C 5 y + w_i C 6 y ≥
          (count C 1 - w_i C 1 y) + (count C 5 - w_i C 5 y) + w_i C 6 y + 2 := by
        have h := hd0ge
        rw [hd3, hd0] at h
        exact h
      have hz1 : (w_i C 1 y : ℤ) + (w_i C 5 y : ℤ) + ((count C 6 - w_i C 6 y) : ℤ) =
          ((count C 1 - w_i C 1 y) : ℤ) + ((count C 5 - w_i C 5 y) : ℤ) + (w_i C 6 y : ℤ) + 1 := by
        exact_mod_cast hcond1
      have hd0geZ : (w_i C 1 y : ℤ) + (w_i C 5 y : ℤ) + (w_i C 6 y : ℤ) ≥
          ((count C 1 : ℤ) - w_i C 1 y) + ((count C 5 : ℤ) - w_i C 5 y) + (w_i C 6 y : ℤ) + 2 := by
        exact_mod_cast hd0ge'
      have hcond2' : (count C 6 : ℤ) + 1 ≤ 2 * (w_i C 6 y : ℤ) := by omega
      exact_mod_cast hcond2'
    have hcond3 : 2 * w_i C 5 y + 1 ≤ count C 5 := by
      have hd1ge' : w_i C 1 y + (count C 5 - w_i C 5 y) + (count C 6 - w_i C 6 y) ≥
          (count C 1 - w_i C 1 y) + (count C 5 - w_i C 5 y) + w_i C 6 y + 2 := by
        have h := hd1ge
        rw [hd3, hd1] at h
        exact h
      have hz1 : (w_i C 1 y : ℤ) + (w_i C 5 y : ℤ) + ((count C 6 - w_i C 6 y) : ℤ) =
          ((count C 1 - w_i C 1 y) : ℤ) + ((count C 5 - w_i C 5 y) : ℤ) + (w_i C 6 y : ℤ) + 1 := by
        exact_mod_cast hcond1
      have hd1geZ : (w_i C 1 y : ℤ) + ((count C 5 : ℤ) - w_i C 5 y) + ((count C 6 : ℤ) - w_i C 6 y) ≥
          ((count C 1 : ℤ) - w_i C 1 y) + ((count C 5 : ℤ) - w_i C 5 y) + (w_i C 6 y : ℤ) + 2 := by
        exact_mod_cast hd1ge'
      have hcond3' : 2 * (w_i C 5 y : ℤ) + 1 ≤ (count C 5 : ℤ) := by omega
      exact_mod_cast hcond3'
    exact ⟨hyt, hcond1, hcond2, hcond3⟩
  · intro h
    rcases h with ⟨hyt, hcond1, hcond2, hcond3⟩
    refine ⟨hyt, ?_, ?_⟩
    · have hge0 : dRow C 3 y + 2 ≤ dRow C 0 y := by
        rw [hd3, hd0]
        have hz1 : (w_i C 1 y : ℤ) + (w_i C 5 y : ℤ) + ((count C 6 : ℤ) - w_i C 6 y) =
            ((count C 1 : ℤ) - w_i C 1 y) + ((count C 5 : ℤ) - w_i C 5 y) + (w_i C 6 y : ℤ) + 1 := by
          exact_mod_cast hcond1
        have hc2 : (count C 6 : ℤ) + 1 ≤ 2 * (w_i C 6 y : ℤ) := by
          exact_mod_cast hcond2
        have hgeZ : (w_i C 1 y : ℤ) + (w_i C 5 y : ℤ) + (w_i C 6 y : ℤ) ≥
            ((count C 1 : ℤ) - w_i C 1 y) + ((count C 5 : ℤ) - w_i C 5 y) + (w_i C 6 y : ℤ) + 2 := by omega
        exact_mod_cast hgeZ
      have hge1 : dRow C 3 y + 2 ≤ dRow C 1 y := by
        rw [hd3, hd1]
        have hz1 : (w_i C 1 y : ℤ) + (w_i C 5 y : ℤ) + ((count C 6 : ℤ) - w_i C 6 y) =
            ((count C 1 : ℤ) - w_i C 1 y) + ((count C 5 : ℤ) - w_i C 5 y) + (w_i C 6 y : ℤ) + 1 := by
          exact_mod_cast hcond1
        have hc3 : 2 * (w_i C 5 y : ℤ) + 1 ≤ (count C 5 : ℤ) := by
          exact_mod_cast hcond3
        have hgeZ : (w_i C 1 y : ℤ) + ((count C 5 : ℤ) - w_i C 5 y) + ((count C 6 : ℤ) - w_i C 6 y) ≥
            ((count C 1 : ℤ) - w_i C 1 y) + ((count C 5 : ℤ) - w_i C 5 y) + (w_i C 6 y : ℤ) + 2 := by omega
        exact_mod_cast hgeZ
      exact le_min hge0 hge1
    · rw [hd2', hd3]
      omega

/-- The type fibers of a `{1,3,5,6}` code are pairwise disjoint. -/
lemma fiber_disjoint_1356 {n : ℕ} (C : Code n) {i j : ℕ}
    (hij : i ≠ j) : Disjoint (fiber C i) (fiber C j) := by
  rw [Finset.disjoint_left]
  intro u hu huj
  have hi : colVal (C u) = i := (Finset.mem_filter.mp hu).2
  have hj : colVal (C u) = j := (Finset.mem_filter.mp huj).2
  exact hij (hi.symm.trans hj)

/-- Two words agree iff they agree on the set of positions where each is 1. -/
lemma word_eq_iff_ones {n : ℕ} (x y : Word n) :
    x = y ↔ ∀ u : Fin n, x u = true ↔ y u = true := by
  constructor
  · intro h
    subst h
    intro u
    rfl
  · intro h
    funext u
    by_cases hxu : x u = true <;> by_cases hyu : y u = true
    · rw [hxu, hyu]
    · have h' := (h u).1 hxu
      exact False.elim (hyu h')
    · have h' := (h u).2 hyu
      exact False.elim (hxu h')
    · have hxf : x u = false := Bool.eq_false_of_not_eq_true hxu
      have hyf : y u = false := Bool.eq_false_of_not_eq_true hyu
      rw [hxf, hyf]

/-- Number of words with y_t = 1 and prescribed weights (w1, w5, w6) on the
types 1, 5, 6 of a |3| = 0 code: C(|1|−1,w1−1)·C(|5|,w5)·C(|6|,w6) (paper §3.1
counting, with the type-1 column t forced to be one). -/
lemma count_words_htrue_weights_1356 {n : ℕ} (C : Code n)
    (htypes : ∀ u : Fin n, colVal (C u) = 1 ∨ colVal (C u) = 3 ∨
      colVal (C u) = 5 ∨ colVal (C u) = 6)
    (h3 : count C 3 = 0) (t : Fin n) (hcol : C t = col1) (w1 w5 w6 : ℕ)
    (hw1pos : 1 ≤ w1) :
    ((Finset.univ : Finset (Word n)).filter
      fun y => y t = true ∧ w_i C 1 y = w1 ∧ w_i C 5 y = w5 ∧ w_i C 6 y = w6).card =
      Nat.choose (count C 1 - 1) (w1 - 1) * Nat.choose (count C 5) w5 *
        Nat.choose (count C 6) w6 := by
  let S : Finset (Word n) := (Finset.univ : Finset (Word n)).filter
    fun y => y t = true ∧ w_i C 1 y = w1 ∧ w_i C 5 y = w5 ∧ w_i C 6 y = w6
  let A : Finset (Fin n) := fiber C 1 \ {t}
  let T : Finset (Finset (Fin n) × Finset (Fin n) × Finset (Fin n)) :=
    (A.powersetCard (w1 - 1)) ×ˢ ((fiber C 5).powersetCard w5) ×ˢ
      ((fiber C 6).powersetCard w6)
  have ht : t ∈ fiber C 1 := by simp [fiber, hcol, colVal_col1]
  have hcardA : A.card = count C 1 - 1 := by
    dsimp [A]
    rw [← Finset.erase_eq, Finset.card_erase_of_mem ht, fiber_card_eq_count C 1]
  have hcardT : T.card = Nat.choose (count C 1 - 1) (w1 - 1) * Nat.choose (count C 5) w5 *
      Nat.choose (count C 6) w6 := by
    dsimp [T]
    rw [Finset.card_product, Finset.card_product, Finset.card_powersetCard, Finset.card_powersetCard,
        Finset.card_powersetCard, hcardA, fiber_card_eq_count C 5, fiber_card_eq_count C 6]
    ring
  have hdisj15 : Disjoint (fiber C 1) (fiber C 5) := fiber_disjoint_1356 C (by decide : (1 : ℕ) ≠ 5)
  have hdisj16 : Disjoint (fiber C 1) (fiber C 6) := fiber_disjoint_1356 C (by decide : (1 : ℕ) ≠ 6)
  have hdisj56 : Disjoint (fiber C 5) (fiber C 6) := fiber_disjoint_1356 C (by decide : (5 : ℕ) ≠ 6)
  have hones_split (y : Word n) (hyt : y t = true) :
      onesOn (fiber C 1) y = insert t (onesOn A y) := by
    ext u
    constructor
    · intro hu
      have huf : u ∈ fiber C 1 := (Finset.mem_filter.mp hu).1
      have hut : y u = true := (Finset.mem_filter.mp hu).2
      by_cases hut' : u = t
      · simp [hut']
      · have huA : u ∈ A := by
          simp [A]
          exact ⟨huf, hut'⟩
        have huones : u ∈ onesOn A y := Finset.mem_filter.mpr ⟨huA, hut⟩
        simp [huones]
    · intro hu
      rcases Finset.mem_insert.mp hu with hut' | huA
      · subst u
        exact Finset.mem_filter.mpr ⟨ht, hyt⟩
      · have huA' : u ∈ A := (Finset.mem_filter.mp huA).1
        have huf : u ∈ fiber C 1 := (Finset.mem_sdiff.mp huA').1
        have hut'' : y u = true := (Finset.mem_filter.mp huA).2
        exact Finset.mem_filter.mpr ⟨huf, hut''⟩
  have hnot_t (y : Word n) (hyt : y t = true) : t ∉ onesOn A y := by
    intro htA
    have hmem : t ∈ A := (Finset.mem_filter.mp htA).1
    exact (Finset.mem_sdiff.mp hmem).2 (by simp)
  have hcard : S.card = T.card := by
    dsimp [S, T]
    refine Finset.card_bij (fun y _ => (onesOn A y, ⟨onesOn (fiber C 5) y, onesOn (fiber C 6) y⟩)) ?_ ?_ ?_
    · intro y hy
      rcases (Finset.mem_filter.mp hy).2 with ⟨hyt, hw1, hw5, hw6⟩
      have hcardA1 : (onesOn A y).card = w1 - 1 := by
        have hcard1 : (onesOn (fiber C 1) y).card = w1 := by
          rw [← w_i_eq_card_onesOn, hw1]
        rw [hones_split y hyt, Finset.card_insert_of_notMem (hnot_t y hyt)] at hcard1
        omega
      have hcard5 : (onesOn (fiber C 5) y).card = w5 := by
        rw [← w_i_eq_card_onesOn, hw5]
      have hcard6 : (onesOn (fiber C 6) y).card = w6 := by
        rw [← w_i_eq_card_onesOn, hw6]
      exact Finset.mem_product.mpr
        ⟨Finset.mem_powersetCard.mpr ⟨by exact Finset.filter_subset _ _, hcardA1⟩,
          Finset.mem_product.mpr
            ⟨Finset.mem_powersetCard.mpr ⟨by exact Finset.filter_subset _ _, hcard5⟩,
              Finset.mem_powersetCard.mpr ⟨by exact Finset.filter_subset _ _, hcard6⟩⟩⟩
    · intro y hy y' hy' h
      apply (word_eq_iff_ones y y').2
      intro u
      have hyt : y t = true := (Finset.mem_filter.mp hy).2.1
      have hyt' : y' t = true := (Finset.mem_filter.mp hy').2.1
      have hA : onesOn A y = onesOn A y' := congrArg Prod.fst h
      have h5 : onesOn (fiber C 5) y = onesOn (fiber C 5) y' := congrArg (fun g => g.2.1) h
      have h6 : onesOn (fiber C 6) y = onesOn (fiber C 6) y' := congrArg (fun g => g.2.2) h
      rcases htypes u with h1' | h3' | h5' | h6'
      · by_cases hut : u = t
        · subst u
          exact ⟨fun _ => hyt', fun _ => hyt⟩
        · have huf : u ∈ fiber C 1 := by simp [fiber, h1']
          constructor
          · intro hyu
            have huA : u ∈ onesOn A y := Finset.mem_filter.mpr ⟨by simp [A]; exact ⟨huf, hut⟩, hyu⟩
            have huA' : u ∈ onesOn A y' := by simpa [hA] using huA
            exact (Finset.mem_filter.mp huA').2
          · intro hy'u
            have huA' : u ∈ onesOn A y' := Finset.mem_filter.mpr ⟨by simp [A]; exact ⟨huf, hut⟩, hy'u⟩
            have huA : u ∈ onesOn A y := by simpa [← hA] using huA'
            exact (Finset.mem_filter.mp huA).2
      · have hpos : 1 ≤ count C 3 := count_pos_of_colVal C u h3'
        omega
      · have huf : u ∈ fiber C 5 := by simp [fiber, h5']
        constructor
        · intro hyu
          have hu5 : u ∈ onesOn (fiber C 5) y := Finset.mem_filter.mpr ⟨huf, hyu⟩
          have hu5' : u ∈ onesOn (fiber C 5) y' := by simpa [h5] using hu5
          exact (Finset.mem_filter.mp hu5').2
        · intro hy'u
          have hu5' : u ∈ onesOn (fiber C 5) y' := Finset.mem_filter.mpr ⟨huf, hy'u⟩
          have hu5 : u ∈ onesOn (fiber C 5) y := by simpa [← h5] using hu5'
          exact (Finset.mem_filter.mp hu5).2
      · have huf : u ∈ fiber C 6 := by simp [fiber, h6']
        constructor
        · intro hyu
          have hu6 : u ∈ onesOn (fiber C 6) y := Finset.mem_filter.mpr ⟨huf, hyu⟩
          have hu6' : u ∈ onesOn (fiber C 6) y' := by simpa [h6] using hu6
          exact (Finset.mem_filter.mp hu6').2
        · intro hy'u
          have hu6' : u ∈ onesOn (fiber C 6) y' := Finset.mem_filter.mpr ⟨huf, hy'u⟩
          have hu6 : u ∈ onesOn (fiber C 6) y := by simpa [← h6] using hu6'
          exact (Finset.mem_filter.mp hu6).2
    · intro g hg
      let y : Word n := fun u => u = t ∨ u ∈ g.1 ∨ u ∈ g.2.1 ∨ u ∈ g.2.2
      have hg1 : g.1 ∈ A.powersetCard (w1 - 1) := (Finset.mem_product.mp hg).1
      have hg56 : g.2 ∈ (fiber C 5).powersetCard w5 ×ˢ (fiber C 6).powersetCard w6 :=
        (Finset.mem_product.mp hg).2
      have hg5 : g.2.1 ∈ (fiber C 5).powersetCard w5 := (Finset.mem_product.mp hg56).1
      have hg6 : g.2.2 ∈ (fiber C 6).powersetCard w6 := (Finset.mem_product.mp hg56).2
      have hg1sub : g.1 ⊆ A := (Finset.mem_powersetCard.mp hg1).1
      have hg1card : g.1.card = w1 - 1 := (Finset.mem_powersetCard.mp hg1).2
      have hg5sub : g.2.1 ⊆ fiber C 5 := (Finset.mem_powersetCard.mp hg5).1
      have hg5card : g.2.1.card = w5 := (Finset.mem_powersetCard.mp hg5).2
      have hg6sub : g.2.2 ⊆ fiber C 6 := (Finset.mem_powersetCard.mp hg6).1
      have hg6card : g.2.2.card = w6 := (Finset.mem_powersetCard.mp hg6).2
      have hg1sub1 : g.1 ⊆ fiber C 1 := by
        intro u hu
        exact (Finset.mem_sdiff.mp (hg1sub hu)).1
      have hones1 : onesOn (fiber C 1) y = insert t g.1 := by
        ext u
        constructor
        · intro hu
          have huf : u ∈ fiber C 1 := (Finset.mem_filter.mp hu).1
          have hut : y u = true := (Finset.mem_filter.mp hu).2
          have hnot5 : u ∉ fiber C 5 := fun h => (Finset.disjoint_left.mp hdisj15) huf h
          have hnot6 : u ∉ fiber C 6 := fun h => (Finset.disjoint_left.mp hdisj16) huf h
          simp [y] at hut
          rcases hut with hut | hg1' | hg5' | hg6'
          · simp [hut]
          · simp [hg1']
          · exact False.elim (hnot5 (hg5sub hg5'))
          · exact False.elim (hnot6 (hg6sub hg6'))
        · intro hu
          rcases Finset.mem_insert.mp hu with hut | hg1'
          · subst u
            exact Finset.mem_filter.mpr ⟨ht, by simp [y]⟩
          · have huf : u ∈ fiber C 1 := hg1sub1 hg1'
            exact Finset.mem_filter.mpr ⟨huf, by simp [y, hg1']⟩
      have hones5 : onesOn (fiber C 5) y = g.2.1 := by
        ext u
        constructor
        · intro hu
          have huf : u ∈ fiber C 5 := (Finset.mem_filter.mp hu).1
          have hut : y u = true := (Finset.mem_filter.mp hu).2
          have hnot1 : u ∉ fiber C 1 := fun h => (Finset.disjoint_left.mp hdisj15) h huf
          have hnot6 : u ∉ fiber C 6 := fun h => (Finset.disjoint_left.mp hdisj56) huf h
          simp [y] at hut
          rcases hut with hut | hg1' | hg5' | hg6'
          · have huf1 : t ∈ fiber C 1 := ht
            subst u
            exact False.elim ((Finset.disjoint_left.mp hdisj15) huf1 huf)
          · exact False.elim (hnot1 (hg1sub1 hg1'))
          · exact hg5'
          · exact False.elim (hnot6 (hg6sub hg6'))
        · intro hg5'
          have huf : u ∈ fiber C 5 := hg5sub hg5'
          exact Finset.mem_filter.mpr ⟨huf, by simp [y, hg5']⟩
      have hones6 : onesOn (fiber C 6) y = g.2.2 := by
        ext u
        constructor
        · intro hu
          have huf : u ∈ fiber C 6 := (Finset.mem_filter.mp hu).1
          have hut : y u = true := (Finset.mem_filter.mp hu).2
          have hnot1 : u ∉ fiber C 1 := fun h => (Finset.disjoint_left.mp hdisj16) h huf
          have hnot5 : u ∉ fiber C 5 := fun h => (Finset.disjoint_left.mp hdisj56) h huf
          simp [y] at hut
          rcases hut with hut | hg1' | hg5' | hg6'
          · have huf1 : t ∈ fiber C 1 := ht
            subst u
            exact False.elim ((Finset.disjoint_left.mp hdisj16) huf1 huf)
          · exact False.elim (hnot1 (hg1sub1 hg1'))
          · exact False.elim (hnot5 (hg5sub hg5'))
          · exact hg6'
        · intro hg6'
          have huf : u ∈ fiber C 6 := hg6sub hg6'
          exact Finset.mem_filter.mpr ⟨huf, by simp [y, hg6']⟩
      have hw1' : w_i C 1 y = w1 := by
        have hnotg : t ∉ g.1 := by
          intro htA
          have hmem : t ∈ g.1 := htA
          have hmemA : t ∈ A := hg1sub hmem
          exact (Finset.mem_sdiff.mp hmemA).2 (by simp)
        rw [w_i_eq_card_onesOn, hones1, Finset.card_insert_of_notMem hnotg, hg1card]
        omega
      have hw5' : w_i C 5 y = w5 := by
        rw [w_i_eq_card_onesOn, hones5, hg5card]
      have hw6' : w_i C 6 y = w6 := by
        rw [w_i_eq_card_onesOn, hones6, hg6card]
      refine ⟨y, ?_, ?_⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ y, ⟨by simp [y], hw1', hw5', hw6'⟩⟩
      · have hA' : onesOn A y = g.1 := by
          -- onesOn A y = onesOn (fiber C 1 \ {t}) y = (onesOn (fiber C 1) y) \ {t}
          have hsplit : onesOn A y = onesOn (fiber C 1) y \ {t} := by
            ext u
            constructor
            · intro hu
              have huA : u ∈ A := (Finset.mem_filter.mp hu).1
              have hut : y u = true := (Finset.mem_filter.mp hu).2
              exact Finset.mem_sdiff.mpr
                ⟨Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp huA).1, hut⟩, (Finset.mem_sdiff.mp huA).2⟩
            · intro hu
              have hu12 := Finset.mem_sdiff.mp hu
              have hu1 : u ∈ fiber C 1 := (Finset.mem_filter.mp hu12.1).1
              have hut : y u = true := (Finset.mem_filter.mp hu12.1).2
              have hut' : u ≠ t := by
                intro hut
                exact hu12.2 (by simp [hut])
              exact Finset.mem_filter.mpr
                ⟨Finset.mem_sdiff.mpr ⟨hu1, by intro h; exact hut' (Finset.mem_singleton.mp h)⟩, hut⟩
          rw [hsplit, hones1]
          ext u
          simp
          constructor
          · intro hu
            rcases hu with ⟨hut', hne⟩
            rcases hut' with hmem | hmem
            · subst u
              exact False.elim (hne (by simp))
            · exact hmem
          · intro hmem
            refine ⟨Or.inr hmem, ?_⟩
            intro hut
            subst u
            have hmemA : t ∈ A := hg1sub hmem
            exact (Finset.mem_sdiff.mp hmemA).2 (by simp)
        have h5' : onesOn (fiber C 5) y = g.2.1 := hones5
        have h6' : onesOn (fiber C 6) y = g.2.2 := hones6
        rw [hA', h5', h6']
  rw [← hcardT, ← hcard]

/-- The high-distance Y5 weight conditions for |3| = 1 (w3 = 1: eq. 5yc2,
2w6 ≥ |6|+1, 2w5+1 ≤ |5|). -/
abbrev Y5HighCondC3one {n : ℕ} (C : Code n) (w1 w5 w6 : ℕ) : Prop :=
  w1 + w5 + (count C 6 - w6) = (count C 1 - w1) + (count C 5 - w5) + w6 + 1 ∧
    count C 6 + 1 ≤ 2 * w6 ∧ 2 * w5 + 1 ≤ count C 5

/-- The low-distance Y5 weight conditions for |3| = 1 (w3 = 0: eq. 5yc2,
2w6 ≥ |6|+3, 2w5+3 ≤ |5|). -/
abbrev Y5LowCondC3one {n : ℕ} (C : Code n) (w1 w5 w6 : ℕ) : Prop :=
  w1 + w5 + (count C 6 - w6) = (count C 1 - w1) + (count C 5 - w5) + w6 + 1 ∧
    count C 6 + 3 ≤ 2 * w6 ∧ 2 * w5 + 3 ≤ count C 5

/-- The Y5 weight conditions for a |3| = 0 code (division-free, eq. 5yc2–5yc4). -/
abbrev Y5WeightCondC3zero {n : ℕ} (C : Code n) (w1 w5 w6 : ℕ) : Prop :=
  w1 + w5 + (count C 6 - w6) = (count C 1 - w1) + (count C 5 - w5) + w6 + 1 ∧
    count C 6 + 1 ≤ 2 * w6 ∧ 2 * w5 + 1 ≤ count C 5

/-- α⁵((n−1)/2) for |3| = 0 as the binomial sum over the Y5 weight region
(paper eq. alpha5i / eq. sa_2 first line, with the type-1 column t forced). -/
lemma alpha5_c3zero_eq_sum {n : ℕ} (C : Code n) (t : Fin n)
    (htypes : ∀ u : Fin n, colVal (C u) = 1 ∨ colVal (C u) = 3 ∨
      colVal (C u) = 5 ∨ colVal (C u) = 6)
    (hcol : C t = col1) (h3 : count C 3 = 0)
    (htotal : totalCounts C {1, 3, 5, 6} = n) :
    alpha5 C t ((n - 1) / 2) =
      ∑ w1 ∈ Finset.Icc 1 (count C 1),
        ∑ w5 ∈ Finset.Icc 0 (count C 5),
          ∑ w6 ∈ Finset.Icc 0 (count C 6),
            if Y5WeightCondC3zero C w1 w5 w6 then
              Nat.choose (count C 1 - 1) (w1 - 1) * Nat.choose (count C 5) w5 *
                Nat.choose (count C 6) w6
            else 0 := by
  unfold alpha5
  let F : ℕ × ℕ × ℕ → Finset (Word n) := fun w =>
    (Finset.univ : Finset (Word n)).filter
      fun y => y t = true ∧ w_i C 1 y = w.1 ∧ w_i C 5 y = w.2.1 ∧ w_i C 6 y = w.2.2
  let S : Finset (ℕ × ℕ × ℕ) :=
    (Finset.Icc 1 (count C 1)) ×ˢ ((Finset.Icc 0 (count C 5)) ×ˢ (Finset.Icc 0 (count C 6)))
  let W : Finset (ℕ × ℕ × ℕ) := S.filter fun w => Y5WeightCondC3zero C w.1 w.2.1 w.2.2
  have hdist : ∀ y : Word n, Y5 C t y → dCode C y = (n - 1) / 2 :=
    fun y hy => class1_alpha5_dist_eq_threshold C t htypes hcol h3 htotal y hy
  have hA : (Finset.univ.filter fun y : Word n => Y5 C t y ∧ dCode C y = (n - 1) / 2) =
      Finset.univ.filter fun y : Word n => Y5 C t y := by
    ext y
    constructor
    · intro hy
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ y, (Finset.mem_filter.mp hy).2.1⟩
    · intro hy
      have hy5 : Y5 C t y := (Finset.mem_filter.mp hy).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ y, ⟨hy5, hdist y hy5⟩⟩
  have hB : (Finset.univ.filter fun y : Word n => Y5 C t y) = W.biUnion F := by
    ext y
    constructor
    · intro hy
      have hy5 : Y5 C t y := (Finset.mem_filter.mp hy).2
      have hc := (Y5_iff_weights_c3zero C t y htypes hcol h3).1 hy5
      have hcond : Y5WeightCondC3zero C (w_i C 1 y) (w_i C 5 y) (w_i C 6 y) := hc.2
      have hw1le : w_i C 1 y ≤ count C 1 := w_i_le_count C 1 y
      have hw5le : w_i C 5 y ≤ count C 5 := w_i_le_count C 5 y
      have hw6le : w_i C 6 y ≤ count C 6 := w_i_le_count C 6 y
      have hmem1 : t ∈ onesOn (fiber C 1) y :=
        Finset.mem_filter.mpr ⟨by simp [fiber, hcol, colVal_col1], hc.1⟩
      have hc1 : 1 ≤ (onesOn (fiber C 1) y).card := Finset.card_pos.mpr ⟨t, hmem1⟩
      have hw1pos : 1 ≤ w_i C 1 y := by
        rw [← w_i_eq_card_onesOn] at hc1
        exact hc1
      refine Finset.mem_biUnion.mpr ⟨(w_i C 1 y, (w_i C 5 y, w_i C 6 y)), ?_, ?_⟩
      · refine Finset.mem_filter.mpr ⟨?_, hcond⟩
        refine Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hw1pos, hw1le⟩, ?_⟩
        refine Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.zero_le _, hw5le⟩,
          Finset.mem_Icc.mpr ⟨Nat.zero_le _, hw6le⟩⟩
      · refine Finset.mem_filter.mpr ⟨Finset.mem_univ y, ?_⟩
        exact ⟨hc.1, rfl, rfl, rfl⟩
    · intro hy
      rcases Finset.mem_biUnion.mp hy with ⟨w, hw, hyw⟩
      have hwS : w ∈ S := (Finset.mem_filter.mp hw).1
      have hcond : Y5WeightCondC3zero C w.1 w.2.1 w.2.2 := (Finset.mem_filter.mp hw).2
      have hywf := (Finset.mem_filter.mp hyw).2
      have hyt : y t = true := hywf.1
      have hw1 : w_i C 1 y = w.1 := hywf.2.1
      have hw5 : w_i C 5 y = w.2.1 := hywf.2.2.1
      have hw6 : w_i C 6 y = w.2.2 := hywf.2.2.2
      have hcond' : Y5WeightCondC3zero C (w_i C 1 y) (w_i C 5 y) (w_i C 6 y) := by
        simpa [← hw1, ← hw5, ← hw6] using hcond
      have hy5 : Y5 C t y :=
        (Y5_iff_weights_c3zero C t y htypes hcol h3).2 ⟨hyt, hcond'⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ y, hy5⟩
  rw [hA, hB]
  have hdisj : ((W : Set (ℕ × ℕ × ℕ))).PairwiseDisjoint F := by
    intro a ha b hb hab
    change Disjoint (F a) (F b)
    rw [Finset.disjoint_left]
    intro y hya hyb
    have ha' := (Finset.mem_filter.mp hya).2
    have hb' := (Finset.mem_filter.mp hyb).2
    have h1 : a.1 = b.1 := ha'.2.1.symm.trans hb'.2.1
    have h5 : a.2.1 = b.2.1 := ha'.2.2.1.symm.trans hb'.2.2.1
    have h6 : a.2.2 = b.2.2 := ha'.2.2.2.symm.trans hb'.2.2.2
    exact hab (Prod.ext h1 (Prod.ext h5 h6))
  rw [Finset.card_biUnion hdisj]
  simp [W, S, F, Finset.sum_filter, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro w1 hw1
  apply Finset.sum_congr rfl
  intro w5 hw5
  apply Finset.sum_congr rfl
  intro w6 hw6
  by_cases hcond : Y5WeightCondC3zero C w1 w5 w6
  · rw [if_pos hcond, if_pos hcond]
    have hw1pos : 1 ≤ w1 := (Finset.mem_Icc.mp hw1).1
    exact count_words_htrue_weights_1356 C htypes h3 t hcol w1 w5 w6 hw1pos
  · rw [if_neg hcond, if_neg hcond]

/-- The Y5 conditions (|3| = 0) force the eq:5 region on (w1′, w6) with
w1′ = |1| − w1 + 1 (paper eq. 7 → eq. 5; the weaker `≤ |1|+|6|` bound
suffices, absorbing the parity slack). -/
lemma Y5WeightCond_c3zero_imp_region {n : ℕ} (C : Code n) (w1 w5 w6 : ℕ)
    (hpar36 : Even (count C 3) ↔ Even (count C 6)) (h3 : count C 3 = 0)
    (_hw1pos : 1 ≤ w1) (hw1le : w1 ≤ count C 1) (hw6le : w6 ≤ count C 6)
    (hcond : Y5WeightCondC3zero C w1 w5 w6) :
    count C 6 + 2 ≤ 2 * w6 ∧
      2 * (count C 1 - w1 + 1) + 2 * w6 ≤ count C 1 + count C 6 := by
  rcases hcond with ⟨heq, hw6ge, hw5le⟩
  have hc6e : Even (count C 6) := hpar36.1 (by rw [h3]; exact ⟨0, rfl⟩)
  have hw6ge' : count C 6 + 2 ≤ 2 * w6 := by
    rcases hc6e with ⟨k, hk⟩
    omega
  have hw5le' : w5 ≤ count C 5 := by omega
  have hZ1 : (w1 : ℤ) + (w5 : ℤ) + ((count C 6 : ℤ) - w6) =
      ((count C 1 : ℤ) - w1) + ((count C 5 : ℤ) - w5) + (w6 : ℤ) + 1 := by
    exact_mod_cast heq
  have hZ2 : 2 * (w6 : ℤ) ≤ 2 * (w1 : ℤ) + (count C 6 : ℤ) - count C 1 - 2 := by
    have hw5leZ : 2 * (w5 : ℤ) + 1 ≤ (count C 5 : ℤ) := by exact_mod_cast hw5le
    omega
  have hc1w1 : (((count C 1 - w1 + 1) : ℕ) : ℤ) = (count C 1 : ℤ) - (w1 : ℤ) + 1 := by
    rw [Nat.cast_add, Nat.cast_sub hw1le]
    norm_num
  have hZ3 : (2 : ℤ) * (((count C 1 - w1 + 1) : ℕ) : ℤ) + 2 * (w6 : ℤ) ≤
      (count C 1 : ℤ) + (count C 6 : ℤ) := by
    rw [hc1w1]
    omega
  exact ⟨hw6ge', by exact_mod_cast hZ3⟩

/-- The Y5 equation (|3| = 0) determines w5 from (w1, w6). -/
lemma Y5WeightCond_c3zero_w5_unique {n : ℕ} (C : Code n) {w1 w5 w5' w6 : ℕ}
    (h1 : Y5WeightCondC3zero C w1 w5 w6) (h2 : Y5WeightCondC3zero C w1 w5' w6) :
    w5 = w5' := by
  rcases h1 with ⟨heq1, _, hw5le⟩
  rcases h2 with ⟨heq2, _, hw5le'⟩
  have hw5le1 : w5 ≤ count C 5 := by omega
  have hw5le2 : w5' ≤ count C 5 := by omega
  omega

/-- For fixed (w1, w6), the Y5 w5-sum is bounded by the eq:5-region indicator
times C(|5|, |5|/2): the equation determines at most one w5, and each binomial
is at most the middle one (`Nat.choose_le_middle`). -/
lemma Y5WeightCond_c3zero_inner_le {n : ℕ} (C : Code n) (w1 w6 : ℕ)
    (hpar36 : Even (count C 3) ↔ Even (count C 6)) (h3 : count C 3 = 0)
    (hw1pos : 1 ≤ w1) (hw1le : w1 ≤ count C 1) (hw6le : w6 ≤ count C 6) :
    (∑ w5 ∈ Finset.Icc 0 (count C 5),
        if Y5WeightCondC3zero C w1 w5 w6 then Nat.choose (count C 5) w5 else 0) ≤
      if count C 6 + 2 ≤ 2 * w6 ∧ 2 * (count C 1 - w1 + 1) + 2 * w6 ≤ count C 1 + count C 6 then
        Nat.choose (count C 5) (count C 5 / 2)
      else 0 := by
  by_cases hregion : count C 6 + 2 ≤ 2 * w6 ∧ 2 * (count C 1 - w1 + 1) + 2 * w6 ≤ count C 1 + count C 6
  · rw [if_pos hregion]
    let s : Finset ℕ := Finset.Icc 0 (count C 5)
    let f : ℕ → ℕ := fun w5 => if Y5WeightCondC3zero C w1 w5 w6 then Nat.choose (count C 5) w5 else 0
    have hle_pointwise : ∀ w5 ∈ s.filter (fun w5 => Y5WeightCondC3zero C w1 w5 w6),
        f w5 ≤ Nat.choose (count C 5) (count C 5 / 2) := by
      intro w5 hw5
      have hc : Y5WeightCondC3zero C w1 w5 w6 := (Finset.mem_filter.mp hw5).2
      have : f w5 = Nat.choose (count C 5) w5 := by simp [f, hc]
      rw [this]
      exact Nat.choose_le_middle w5 (count C 5)
    have hcard : (s.filter (fun w5 => Y5WeightCondC3zero C w1 w5 w6) |>.card) ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      have ha' := (Finset.mem_filter.mp ha).2
      have hb' := (Finset.mem_filter.mp hb).2
      exact (Y5WeightCond_c3zero_w5_unique C hb' ha').symm
    calc
      (∑ w5 ∈ s, f w5) =
          ∑ w5 ∈ s.filter (fun w5 => Y5WeightCondC3zero C w1 w5 w6), f w5 := by
        rw [← Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro w5 hw5
        have hc : Y5WeightCondC3zero C w1 w5 w6 := (Finset.mem_filter.mp hw5).2
        simp [f, hc]
      _ ≤ (s.filter (fun w5 => Y5WeightCondC3zero C w1 w5 w6) |>.card) *
            Nat.choose (count C 5) (count C 5 / 2) := by
        simpa [nsmul_eq_mul] using
          Finset.sum_le_card_nsmul (s.filter (fun w5 => Y5WeightCondC3zero C w1 w5 w6)) f
            (Nat.choose (count C 5) (count C 5 / 2)) hle_pointwise
      _ ≤ 1 * Nat.choose (count C 5) (count C 5 / 2) := by
        exact Nat.mul_le_mul_right _ hcard
      _ = Nat.choose (count C 5) (count C 5 / 2) := by simp
  · rw [if_neg hregion]
    have hsum0 : (∑ w5 ∈ Finset.Icc 0 (count C 5),
        if Y5WeightCondC3zero C w1 w5 w6 then Nat.choose (count C 5) w5 else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro w5 hw5
      by_cases hc : Y5WeightCondC3zero C w1 w5 w6
      · rw [if_pos hc]
        have hreg := Y5WeightCond_c3zero_imp_region C w1 w5 w6 hpar36 h3 hw1pos hw1le hw6le hc
        exact False.elim (hregion ⟨hreg.1, hreg.2⟩)
      · rw [if_neg hc]
    exact le_of_eq hsum0

/-- α⁵((n−1)/2) ≤ the eq:5 binomial sum (with w1′ = |1|−w1+1 reindexed to
w1): the Y5 equation collapses the w5-sum (uniqueness), `choose_le_middle`
bounds each binomial, and the substitution makes the region an upper bound. -/
lemma alpha5_c3zero_le_eq5 {n : ℕ} (C : Code n) (t : Fin n)
    (htypes : ∀ u : Fin n, colVal (C u) = 1 ∨ colVal (C u) = 3 ∨
      colVal (C u) = 5 ∨ colVal (C u) = 6)
    (hcol : C t = col1) (h3 : count C 3 = 0)
    (_hpar35 : Even (count C 5) ↔ Even (count C 6))
    (hpar36 : Even (count C 3) ↔ Even (count C 6))
    (_hpar53 : Even (count C 5) ↔ Even (count C 3))
    (htotal : totalCounts C {1, 3, 5, 6} = n) (_hodd1 : Odd (count C 1)) :
    alpha5 C t ((n - 1) / 2) ≤
      ∑ w1 ∈ Finset.Icc 1 (count C 1),
        ∑ w6 ∈ Finset.Icc 0 (count C 6),
          if count C 6 + 2 ≤ 2 * w6 ∧ 2 * w1 + 2 * w6 ≤ count C 1 + count C 6 then
            Nat.choose (count C 1 - 1) (w1 - 1) * Nat.choose (count C 5) (count C 5 / 2) *
              Nat.choose (count C 6) w6
          else 0 := by
  rw [alpha5_c3zero_eq_sum C t htypes hcol h3 htotal]
  let s1 : Finset ℕ := Finset.Icc 1 (count C 1)
  let s5 : Finset ℕ := Finset.Icc 0 (count C 5)
  let s6 : Finset ℕ := Finset.Icc 0 (count C 6)
  calc
    (∑ w1 ∈ s1, ∑ w5 ∈ s5, ∑ w6 ∈ s6,
        if Y5WeightCondC3zero C w1 w5 w6 then
          Nat.choose (count C 1 - 1) (w1 - 1) * Nat.choose (count C 5) w5 *
            Nat.choose (count C 6) w6
        else 0)
        ≤ ∑ w1 ∈ s1, ∑ w6 ∈ s6,
            if count C 6 + 2 ≤ 2 * w6 ∧ 2 * (count C 1 - w1 + 1) + 2 * w6 ≤ count C 1 + count C 6 then
              Nat.choose (count C 1 - 1) (w1 - 1) * Nat.choose (count C 5) (count C 5 / 2) *
                Nat.choose (count C 6) w6
            else 0 := by
      apply Finset.sum_le_sum
      intro w1 hw1
      rw [Finset.sum_comm]
      apply Finset.sum_le_sum
      intro w6 hw6
      have hw1pos : 1 ≤ w1 := (Finset.mem_Icc.mp hw1).1
      have hw1le : w1 ≤ count C 1 := (Finset.mem_Icc.mp hw1).2
      have hw6le : w6 ≤ count C 6 := (Finset.mem_Icc.mp hw6).2
      have hin := Y5WeightCond_c3zero_inner_le C w1 w6 hpar36 h3 hw1pos hw1le hw6le
      have hfac : (∑ w5 ∈ s5, if Y5WeightCondC3zero C w1 w5 w6 then
            Nat.choose (count C 1 - 1) (w1 - 1) * Nat.choose (count C 5) w5 *
              Nat.choose (count C 6) w6
            else 0) =
          Nat.choose (count C 1 - 1) (w1 - 1) * Nat.choose (count C 6) w6 *
            (∑ w5 ∈ s5, if Y5WeightCondC3zero C w1 w5 w6 then Nat.choose (count C 5) w5 else 0) := by
        calc
          (∑ w5 ∈ s5, if Y5WeightCondC3zero C w1 w5 w6 then
              Nat.choose (count C 1 - 1) (w1 - 1) * Nat.choose (count C 5) w5 *
                Nat.choose (count C 6) w6
              else 0)
              = ∑ w5 ∈ s5, (Nat.choose (count C 1 - 1) (w1 - 1) * Nat.choose (count C 6) w6) *
                  (if Y5WeightCondC3zero C w1 w5 w6 then Nat.choose (count C 5) w5 else 0) := by
                apply Finset.sum_congr rfl
                intro w5 hw5
                by_cases hc : Y5WeightCondC3zero C w1 w5 w6
                · rw [if_pos hc, if_pos hc]
                  ring
                · rw [if_neg hc, if_neg hc]
                  simp
          _ = Nat.choose (count C 1 - 1) (w1 - 1) * Nat.choose (count C 6) w6 *
                (∑ w5 ∈ s5, if Y5WeightCondC3zero C w1 w5 w6 then Nat.choose (count C 5) w5 else 0) := by
                rw [Finset.mul_sum]
      calc
        (∑ w5 ∈ s5, if Y5WeightCondC3zero C w1 w5 w6 then
            Nat.choose (count C 1 - 1) (w1 - 1) * Nat.choose (count C 5) w5 *
              Nat.choose (count C 6) w6
            else 0)
            = Nat.choose (count C 1 - 1) (w1 - 1) * Nat.choose (count C 6) w6 *
                (∑ w5 ∈ s5, if Y5WeightCondC3zero C w1 w5 w6 then Nat.choose (count C 5) w5 else 0) := hfac
        _ ≤ Nat.choose (count C 1 - 1) (w1 - 1) * Nat.choose (count C 6) w6 *
              (if count C 6 + 2 ≤ 2 * w6 ∧ 2 * (count C 1 - w1 + 1) + 2 * w6 ≤ count C 1 + count C 6 then
                Nat.choose (count C 5) (count C 5 / 2)
               else 0) := by
              exact Nat.mul_le_mul_left (Nat.choose (count C 1 - 1) (w1 - 1) * Nat.choose (count C 6) w6) hin
        _ = if count C 6 + 2 ≤ 2 * w6 ∧ 2 * (count C 1 - w1 + 1) + 2 * w6 ≤ count C 1 + count C 6 then
                Nat.choose (count C 1 - 1) (w1 - 1) * Nat.choose (count C 5) (count C 5 / 2) *
                  Nat.choose (count C 6) w6
              else 0 := by
              by_cases hc : count C 6 + 2 ≤ 2 * w6 ∧ 2 * (count C 1 - w1 + 1) + 2 * w6 ≤ count C 1 + count C 6
              · rw [if_pos hc, if_pos hc]
                ring
              · rw [if_neg hc, if_neg hc]
                simp
    _ = ∑ w1 ∈ s1, ∑ w6 ∈ s6,
            if count C 6 + 2 ≤ 2 * w6 ∧ 2 * w1 + 2 * w6 ≤ count C 1 + count C 6 then
              Nat.choose (count C 1 - 1) (w1 - 1) * Nat.choose (count C 5) (count C 5 / 2) *
                Nat.choose (count C 6) w6
            else 0 := by
      -- reindex w1 ↦ |1| − w1 + 1 (an involution on Icc 1 |1|)
      apply Finset.sum_bij (fun w1 _ => count C 1 - w1 + 1)
      · intro w1 hw1
        have hw1pos : 1 ≤ w1 := (Finset.mem_Icc.mp hw1).1
        have hw1le : w1 ≤ count C 1 := (Finset.mem_Icc.mp hw1).2
        exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      · intro a ha b hb h
        have ha2 : a ≤ count C 1 := (Finset.mem_Icc.mp ha).2
        have hb2 : b ≤ count C 1 := (Finset.mem_Icc.mp hb).2
        omega
      · intro b hb
        refine ⟨count C 1 - b + 1, ?_, ?_⟩
        · have hb2 : b ≤ count C 1 := (Finset.mem_Icc.mp hb).2
          have hb1 : 1 ≤ b := (Finset.mem_Icc.mp hb).1
          exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
        · have hb1 : 1 ≤ b := (Finset.mem_Icc.mp hb).1
          have hb2 : b ≤ count C 1 := (Finset.mem_Icc.mp hb).2
          omega
      · intro w1 hw1
        apply Finset.sum_congr rfl
        intro w6 hw6
        have hw1pos : 1 ≤ w1 := (Finset.mem_Icc.mp hw1).1
        have hw1le : w1 ≤ count C 1 := (Finset.mem_Icc.mp hw1).2
        have hchoose : Nat.choose (count C 1 - 1) (count C 1 - w1) =
            Nat.choose (count C 1 - 1) (w1 - 1) := by
          have hk : w1 - 1 ≤ count C 1 - 1 := by omega
          have hsym := Nat.choose_symm hk
          have harg : (count C 1 - 1) - (w1 - 1) = count C 1 - w1 := by omega
          simpa [harg] using hsym
        by_cases hc : count C 6 + 2 ≤ 2 * w6 ∧ 2 * (count C 1 - w1 + 1) + 2 * w6 ≤ count C 1 + count C 6
        · rw [if_pos hc, if_pos hc]
          have harg' : (count C 1 - w1 + 1) - 1 = count C 1 - w1 := by omega
          rw [harg', hchoose]
        · rw [if_neg hc, if_neg hc]

/-- A word with y_t = 1, 2w5 = |5|, 2w6 ≥ |6| and 2w1+|6| ≤ 2w6+|1| is a
Y3 word of the (weak) B-branch with dCode ≤ (n+1)/2 (paper eq. 3yd1–3yd4,
eq. a3xs; the dCode condition is automatic). -/
lemma Y3B_word_c3zero {n : ℕ} (C : Code n) (t : Fin n) (y : Word n)
    (htypes : ∀ u : Fin n, colVal (C u) = 1 ∨ colVal (C u) = 3 ∨
      colVal (C u) = 5 ∨ colVal (C u) = 6)
    (hcol : C t = col1) (h3 : count C 3 = 0)
    (hpar53 : Even (count C 5) ↔ Even (count C 3))
    (htotal : totalCounts C {1, 3, 5, 6} = n)
    (hyt : y t = true)
    (hw1pos : 1 ≤ w_i C 1 y)
    (hw5 : 2 * w_i C 5 y = count C 5)
    (hw6ge : count C 6 ≤ 2 * w_i C 6 y)
    (hw16 : 2 * w_i C 1 y + count C 6 ≤ 2 * w_i C 6 y + count C 1) :
    Y3 C t y ∧ 1 ≤ dCode C y ∧ dCode C y ≤ (n + 1) / 2 := by
  have hw3 : w_i C 3 y = 0 := w_i_eq_zero_of_count_zero C 3 y h3
  have hw1le : w_i C 1 y ≤ count C 1 := w_i_le_count C 1 y
  have hw5le : w_i C 5 y ≤ count C 5 := w_i_le_count C 5 y
  have hw6le : w_i C 6 y ≤ count C 6 := w_i_le_count C 6 y
  have hd0 : dRow C 0 y = w_i C 1 y + w_i C 5 y + w_i C 6 y := by
    rw [dRow0_of_type1356 C htypes y, hw3]
    simp
  have hd1 : dRow C 1 y = w_i C 1 y + (count C 5 - w_i C 5 y) + (count C 6 - w_i C 6 y) := by
    rw [dRow1_of_type1356 C htypes y, hw3]
    simp
  have hd2' : dRow C 2 y = w_i C 1 y + w_i C 5 y + (count C 6 - w_i C 6 y) := by
    rw [dRow2_of_type1356 C htypes y, hw3, h3]
    simp
  have hd3 : dRow C 3 y = (count C 1 - w_i C 1 y) + (count C 5 - w_i C 5 y) + w_i C 6 y := by
    rw [dRow3_of_type1356 C htypes y, hw3, h3]
    simp
  have hd1le0 : dRow C 1 y ≤ dRow C 0 y := by
    rw [hd0, hd1]
    omega
  have hd2eq1 : dRow C 2 y = dRow C 1 y := by
    rw [hd2', hd1]
    omega
  have hd3ge1 : dRow C 1 y ≤ dRow C 3 y := by
    rw [hd1, hd3]
    omega
  have hy3 : Y3 C t y := (Y3_iff_col1 C t y hcol).2 ⟨hyt, by
      rw [Nat.min_eq_right hd1le0]
      exact hd3ge1, by
      rw [Nat.min_eq_right hd1le0]
      exact hd2eq1⟩
  have hdCode2 : dCode C y = dRow C 2 y := by
    unfold dCode
    rw [show hammingDist (row0 C) y = dRow C 0 y by rfl]
    rw [show hammingDist (row1 C) y = dRow C 1 y by rfl]
    rw [show hammingDist (row2 C) y = dRow C 2 y by rfl]
    rw [show hammingDist (row3 C) y = dRow C 3 y by rfl]
    have hd2le3 : dRow C 2 y ≤ dRow C 3 y := by rw [hd2eq1]; exact hd3ge1
    have hd2le1 : dRow C 2 y ≤ dRow C 1 y := le_of_eq hd2eq1
    have hd2le0 : dRow C 2 y ≤ dRow C 0 y := le_trans hd2le1 hd1le0
    rw [Nat.min_eq_left hd2le3, Nat.min_eq_right hd2le1, Nat.min_eq_right hd2le0]
  have hd2le : dRow C 2 y ≤ (n + 1) / 2 := by
    have hc5e : Even (count C 5) := hpar53.2 (by rw [h3]; exact ⟨0, rfl⟩)
    have hw5' : w_i C 5 y = count C 5 / 2 := by
      rw [← hw5]
      rw [Nat.mul_div_right _ (by decide : 0 < 2)]
    have hsum : count C 1 + count C 5 + count C 6 = n := by
      have h4 : count C 1 + count C 3 + count C 5 + count C 6 = n := by
        calc
          count C 1 + count C 3 + count C 5 + count C 6
              = ∑ i ∈ ({1, 3, 5, 6} : Finset ℕ), count C i := by
                simp [Finset.sum_insert]
                omega
          _ = n := htotal
      rw [h3] at h4
      omega
    have h2d2 : 2 * dRow C 2 y ≤ n := by
      have hw5e : 2 * (count C 5 / 2) = count C 5 := by
        rcases hc5e with ⟨k, hk⟩
        have hk' : count C 5 = 2 * k := by omega
        rw [hk']
        rw [Nat.mul_div_right k (by decide : 0 < 2)]
      have hZ : (2 : ℤ) * (dRow C 2 y : ℤ) ≤ (n : ℤ) := by
        rw [hd2']
        push_cast
        have hZ16 : 2 * (w_i C 1 y : ℤ) + (count C 6 : ℤ) ≤
            2 * (w_i C 6 y : ℤ) + (count C 1 : ℤ) := by exact_mod_cast hw16
        have hZ5 : 2 * ((count C 5 / 2 : ℕ) : ℤ) = (count C 5 : ℤ) := by
          exact_mod_cast hw5e
        have hZ6 : ((count C 6 - w_i C 6 y : ℕ) : ℤ) =
            (count C 6 : ℤ) - (w_i C 6 y : ℤ) := by
          rw [Nat.cast_sub hw6le]
        have hsumZ : (count C 1 : ℤ) + (count C 5 : ℤ) + (count C 6 : ℤ) = (n : ℤ) := by
          exact_mod_cast hsum
        rw [hw5', hZ6]
        omega
      exact_mod_cast hZ
    have hd2le' : dRow C 2 y ≤ n / 2 := by
      exact (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mpr (by simpa [mul_comm] using h2d2)
    exact le_trans hd2le' (Nat.div_le_div_right (by omega : n ≤ n + 1))
  have hdge1 : 1 ≤ dRow C 2 y := by
    rw [hd2']
    omega
  exact ⟨hy3, by rw [hdCode2]; exact hdge1, by rw [hdCode2]; exact hd2le⟩

/-- The cumulative Σ_{i=1..d} α³(i) counts the Y3 words with dCode in
[1, d]. -/
lemma alpha3_cumulative_card {n : ℕ} (C : Code n) (t : Fin n) (d : ℕ) :
    (∑ i ∈ Finset.Icc 1 d, alpha3 C t i) =
      (Finset.univ.filter fun y : Word n => Y3 C t y ∧ 1 ≤ dCode C y ∧ dCode C y ≤ d).card := by
  let V : ℕ → Finset (Word n) := fun i =>
    (Finset.univ : Finset (Word n)).filter fun y => Y3 C t y ∧ dCode C y = i
  have hU : (Finset.univ.filter fun y : Word n => Y3 C t y ∧ 1 ≤ dCode C y ∧ dCode C y ≤ d) =
      (Finset.Icc 1 d).biUnion V := by
    ext y
    constructor
    · intro hy
      have hc := (Finset.mem_filter.mp hy).2
      refine Finset.mem_biUnion.mpr ⟨dCode C y, ?_, ?_⟩
      · exact Finset.mem_Icc.mpr ⟨hc.2.1, hc.2.2⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ y, ⟨hc.1, rfl⟩⟩
    · intro hy
      rcases Finset.mem_biUnion.mp hy with ⟨i, hi, hyv⟩
      have hc := (Finset.mem_filter.mp hyv).2
      have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
      have hid : i ≤ d := (Finset.mem_Icc.mp hi).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ y, ⟨hc.1, by
        rw [hc.2]
        exact ⟨hi1, hid⟩⟩⟩
  have hdisj : ((Finset.Icc 1 d : Set ℕ)).PairwiseDisjoint V := by
    intro a ha b hb hab
    change Disjoint (V a) (V b)
    rw [Finset.disjoint_left]
    intro y hya hyb
    have ha' := (Finset.mem_filter.mp hya).2
    have hb' := (Finset.mem_filter.mp hyb).2
    exact hab (ha'.2.symm.trans hb'.2)
  rw [hU, Finset.card_biUnion hdisj]
  apply Finset.sum_congr rfl
  intro i hi
  rfl

/-- Σ_{i=1..d} α³(i) ≥ the eq:a3xs binomial sum: the Y3-B region words
(w5 = |5|/2, 2w6 ≥ |6|, 2w1+|6| ≤ 2w6+|1|) all have dCode ≤ (n+1)/2 ≤ d,
so their count is a lower bound. -/
lemma class1_alpha3_cum_ge_a3xs {n : ℕ} (C : Code n) (t : Fin n) (d : ℕ)
    (htypes : ∀ u : Fin n, colVal (C u) = 1 ∨ colVal (C u) = 3 ∨
      colVal (C u) = 5 ∨ colVal (C u) = 6)
    (hcol : C t = col1) (h3 : count C 3 = 0)
    (_hpar35 : Even (count C 5) ↔ Even (count C 6))
    (_hpar36 : Even (count C 3) ↔ Even (count C 6))
    (hpar53 : Even (count C 5) ↔ Even (count C 3))
    (htotal : totalCounts C {1, 3, 5, 6} = n) (_hodd1 : Odd (count C 1))
    (hd : (n + 1) / 2 ≤ d) :
    (∑ i ∈ Finset.Icc 1 d, alpha3 C t i) ≥
      ∑ w1 ∈ Finset.Icc 1 (count C 1),
        ∑ w6 ∈ Finset.Icc 0 (count C 6),
          if count C 6 ≤ 2 * w6 ∧ 2 * w1 + count C 6 ≤ 2 * w6 + count C 1 then
            Nat.choose (count C 1 - 1) (w1 - 1) * Nat.choose (count C 5) (count C 5 / 2) *
              Nat.choose (count C 6) w6
          else 0 := by
  rw [alpha3_cumulative_card C t d]
  let F : ℕ × ℕ → Finset (Word n) := fun w =>
    (Finset.univ : Finset (Word n)).filter
      fun y => y t = true ∧ w_i C 1 y = w.1 ∧ w_i C 5 y = count C 5 / 2 ∧ w_i C 6 y = w.2
  let S : Finset (ℕ × ℕ) :=
    (Finset.Icc 1 (count C 1)) ×ˢ (Finset.Icc 0 (count C 6))
  let W : Finset (ℕ × ℕ) := S.filter fun w =>
    count C 6 ≤ 2 * w.2 ∧ 2 * w.1 + count C 6 ≤ 2 * w.2 + count C 1
  have hsub : W.biUnion F ⊆
      Finset.univ.filter (fun y : Word n => Y3 C t y ∧ 1 ≤ dCode C y ∧ dCode C y ≤ d) := by
    intro y hy
    rcases Finset.mem_biUnion.mp hy with ⟨w, hw, hyw⟩
    have hcond := (Finset.mem_filter.mp hw).2
    have hywf := (Finset.mem_filter.mp hyw).2
    have hyt : y t = true := hywf.1
    have hw1 : w_i C 1 y = w.1 := hywf.2.1
    have hw5 : w_i C 5 y = count C 5 / 2 := hywf.2.2.1
    have hw6 : w_i C 6 y = w.2 := hywf.2.2.2
    have hw1pos : 1 ≤ w_i C 1 y := by
      have hw1mem : w.1 ∈ Finset.Icc 1 (count C 1) := (Finset.mem_product.mp (Finset.mem_filter.mp hw).1).1
      have hw1ge : 1 ≤ w.1 := (Finset.mem_Icc.mp hw1mem).1
      omega
    have hw5d : 2 * w_i C 5 y = count C 5 := by
      rcases hpar53.2 (by rw [h3]; exact ⟨0, rfl⟩) with ⟨k, hk⟩
      have hk' : count C 5 = 2 * k := by omega
      rw [hw5, hk']
      rw [Nat.mul_div_right k (by decide : 0 < 2)]
    have hcond' : count C 6 ≤ 2 * w_i C 6 y ∧ 2 * w_i C 1 y + count C 6 ≤ 2 * w_i C 6 y + count C 1 := by
      simpa [← hw1, ← hw6] using hcond
    have hb := Y3B_word_c3zero C t y htypes hcol h3 hpar53 htotal hyt hw1pos hw5d hcond'.1 hcond'.2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ y, ⟨hb.1, hb.2.1, le_trans hb.2.2 (by omega : (n + 1) / 2 ≤ d)⟩⟩
  have hdisj : ((W : Set (ℕ × ℕ))).PairwiseDisjoint F := by
    intro a ha b hb hab
    change Disjoint (F a) (F b)
    rw [Finset.disjoint_left]
    intro y hya hyb
    have ha' := (Finset.mem_filter.mp hya).2
    have hb' := (Finset.mem_filter.mp hyb).2
    have h1 : a.1 = b.1 := ha'.2.1.symm.trans hb'.2.1
    have h6 : a.2 = b.2 := ha'.2.2.2.symm.trans hb'.2.2.2
    exact hab (Prod.ext h1 h6)
  calc
    (∑ w1 ∈ Finset.Icc 1 (count C 1), ∑ w6 ∈ Finset.Icc 0 (count C 6),
        if count C 6 ≤ 2 * w6 ∧ 2 * w1 + count C 6 ≤ 2 * w6 + count C 1 then
          Nat.choose (count C 1 - 1) (w1 - 1) * Nat.choose (count C 5) (count C 5 / 2) *
            Nat.choose (count C 6) w6
        else 0)
        = (W.biUnion F).card := by
          rw [Finset.card_biUnion hdisj]
          simp [W, S, F, Finset.sum_filter, Finset.sum_product]
          apply Finset.sum_congr rfl
          intro w1 hw1
          apply Finset.sum_congr rfl
          intro w6 hw6
          by_cases hc : count C 6 ≤ 2 * w6 ∧ 2 * w1 + count C 6 ≤ 2 * w6 + count C 1
          · rw [if_pos hc, if_pos hc]
            have hw1pos : 1 ≤ w1 := (Finset.mem_Icc.mp hw1).1
            exact (count_words_htrue_weights_1356 C htypes h3 t hcol w1 (count C 5 / 2) w6 hw1pos).symm
          · rw [if_neg hc, if_neg hc]
      _ ≤ (Finset.univ.filter fun y : Word n => Y3 C t y ∧ 1 ≤ dCode C y ∧ dCode C y ≤ d).card := by
            exact Finset.card_le_card hsub

/-- The eq:5 region is contained in the eq:a3xs region, so the binomial sum
is no larger (the paper's final comparison; `2w6 ≥ |6|+2` absorbs the slack). -/
lemma class1_eq5_le_a3xs {n : ℕ} (C : Code n) :
    (∑ w1 ∈ Finset.Icc 1 (count C 1), ∑ w6 ∈ Finset.Icc 0 (count C 6),
        if count C 6 + 2 ≤ 2 * w6 ∧ 2 * w1 + 2 * w6 ≤ count C 1 + count C 6 then
          Nat.choose (count C 1 - 1) (w1 - 1) * Nat.choose (count C 5) (count C 5 / 2) *
            Nat.choose (count C 6) w6
        else 0) ≤
      (∑ w1 ∈ Finset.Icc 1 (count C 1), ∑ w6 ∈ Finset.Icc 0 (count C 6),
        if count C 6 ≤ 2 * w6 ∧ 2 * w1 + count C 6 ≤ 2 * w6 + count C 1 then
          Nat.choose (count C 1 - 1) (w1 - 1) * Nat.choose (count C 5) (count C 5 / 2) *
            Nat.choose (count C 6) w6
        else 0) := by
  apply Finset.sum_le_sum
  intro w1 hw1
  apply Finset.sum_le_sum
  intro w6 hw6
  by_cases h5 : count C 6 + 2 ≤ 2 * w6 ∧ 2 * w1 + 2 * w6 ≤ count C 1 + count C 6
  · rw [if_pos h5]
    have h6ge : count C 6 ≤ 2 * w6 := by omega
    have h16 : 2 * w1 + count C 6 ≤ 2 * w6 + count C 1 := by
      have hZ1 : (2 : ℤ) * w1 + 2 * (w6 : ℤ) ≤ (count C 1 : ℤ) + count C 6 := by
        exact_mod_cast h5.2
      have hZ2 : (count C 6 : ℤ) + 2 ≤ 2 * (w6 : ℤ) := by exact_mod_cast h5.1
      have hZ : (2 : ℤ) * (w1 : ℤ) + (count C 6 : ℤ) ≤ 2 * (w6 : ℤ) + (count C 1 : ℤ) := by omega
      exact_mod_cast hZ
    rw [if_pos ⟨h6ge, h16⟩]
  · rw [if_neg h5]
    exact Nat.zero_le _

/-- Class-I-a binomial core of `thm:301` (Theorem 17): with |3| = 0 and d ≥ (n+1)/2,
Σ_{i≤d} α³(i) ≥ α⁵((n−1)/2).  The eq. sa_2/eq. 5 upper bound for α⁵, the
eq. a3xs lower bound for Σα³, and the region containment are all proved. -/
lemma class1_alpha3_cum_ge_alpha5_threshold {n : ℕ} (C : Code n) (t : Fin n) (d : ℕ)
    (htypes : ∀ u : Fin n, colVal (C u) = 1 ∨ colVal (C u) = 3 ∨
      colVal (C u) = 5 ∨ colVal (C u) = 6)
    (hcol : C t = col1) (h3 : count C 3 = 0)
    (hpar35 : Even (count C 5) ↔ Even (count C 6))
    (hpar36 : Even (count C 3) ↔ Even (count C 6))
    (hpar53 : Even (count C 5) ↔ Even (count C 3))
    (htotal : totalCounts C {1, 3, 5, 6} = n) (hodd1 : Odd (count C 1))
    (hd : (n + 1) / 2 ≤ d) :
    (∑ i ∈ Finset.Icc 1 d, alpha3 C t i) ≥ alpha5 C t ((n - 1) / 2) := by
  calc
    alpha5 C t ((n - 1) / 2) ≤
        ∑ w1 ∈ Finset.Icc 1 (count C 1), ∑ w6 ∈ Finset.Icc 0 (count C 6),
          if count C 6 + 2 ≤ 2 * w6 ∧ 2 * w1 + 2 * w6 ≤ count C 1 + count C 6 then
            Nat.choose (count C 1 - 1) (w1 - 1) * Nat.choose (count C 5) (count C 5 / 2) *
              Nat.choose (count C 6) w6
          else 0 :=
          alpha5_c3zero_le_eq5 C t htypes hcol h3 hpar35 hpar36 hpar53 htotal hodd1
    _ ≤ ∑ w1 ∈ Finset.Icc 1 (count C 1), ∑ w6 ∈ Finset.Icc 0 (count C 6),
          if count C 6 ≤ 2 * w6 ∧ 2 * w1 + count C 6 ≤ 2 * w6 + count C 1 then
            Nat.choose (count C 1 - 1) (w1 - 1) * Nat.choose (count C 5) (count C 5 / 2) *
              Nat.choose (count C 6) w6
          else 0 :=
          class1_eq5_le_a3xs C
    _ ≤ ∑ i ∈ Finset.Icc 1 d, alpha3 C t i :=
          class1_alpha3_cum_ge_a3xs C t d htypes hcol h3 hpar35 hpar36 hpar53 htotal hodd1 hd

/-! ## Class-I-b (|3| = 1): Y5 weight characterization and distance split -/

/-- The Y5 weight conditions for a |3| = 1 code (division-free, eq. 5yc2–5yc4
with w3 ∈ {0,1}). -/
abbrev Y5WeightCondC3one {n : ℕ} (C : Code n) (w3 w1 w5 w6 : ℕ) : Prop :=
  w3 ≤ 1 ∧
    w1 + w5 + (count C 6 - w6) = (count C 1 - w1) + (count C 5 - w5) + w6 + 1 ∧
    count C 6 + 3 ≤ 2 * (w3 + w6) ∧
    2 * w5 + 3 ≤ 2 * w3 + count C 5

/-- `Y5` for a `{1,3,5,6}` code with |3| = 1 and general odd |1|, in the
division-free form of eq. 5yc2–5yc4 (the paper's eq:12/eq:11 follow by
eliminating w5). -/
lemma Y5_iff_weights_c3one {n : ℕ} (C : Code n) (t : Fin n) (y : Word n)
    (htypes : ∀ u : Fin n, colVal (C u) = 1 ∨ colVal (C u) = 3 ∨
      colVal (C u) = 5 ∨ colVal (C u) = 6)
    (hcol : C t = col1) (h3 : count C 3 = 1)
    (hpar36 : Even (count C 3) ↔ Even (count C 6))
    (hpar53 : Even (count C 5) ↔ Even (count C 3)) :
    Y5 C t y ↔ y t = true ∧
      Y5WeightCondC3one C (w_i C 3 y) (w_i C 1 y) (w_i C 5 y) (w_i C 6 y) := by
  have hw3le : w_i C 3 y ≤ 1 := by
    exact le_trans (w_i_le_count C 3 y) (by rw [h3])
  have hw1le : w_i C 1 y ≤ count C 1 := w_i_le_count C 1 y
  have hw5le : w_i C 5 y ≤ count C 5 := w_i_le_count C 5 y
  have hw6le : w_i C 6 y ≤ count C 6 := w_i_le_count C 6 y
  have hd0 : dRow C 0 y = w_i C 1 y + w_i C 3 y + w_i C 5 y + w_i C 6 y :=
    dRow0_of_type1356 C htypes y
  have hd1 : dRow C 1 y = w_i C 1 y + w_i C 3 y + (count C 5 - w_i C 5 y) +
      (count C 6 - w_i C 6 y) := dRow1_of_type1356 C htypes y
  have hd2' : dRow C 2 y = w_i C 1 y + (1 - w_i C 3 y) + w_i C 5 y +
      (count C 6 - w_i C 6 y) := by
    rw [dRow2_of_type1356 C htypes y, h3]
  have hd3 : dRow C 3 y = (count C 1 - w_i C 1 y) + (1 - w_i C 3 y) +
      (count C 5 - w_i C 5 y) + w_i C 6 y := by
    rw [dRow3_of_type1356 C htypes y, h3]
  rw [Y5_iff_col1 C t y hcol]
  constructor
  · intro h
    rcases h with ⟨hyt, hmin, hd2⟩
    have hd0ge : dRow C 3 y + 2 ≤ dRow C 0 y := (le_min_iff.mp hmin).1
    have hd1ge : dRow C 3 y + 2 ≤ dRow C 1 y := (le_min_iff.mp hmin).2
    have hcond1 : w_i C 1 y + w_i C 5 y + (count C 6 - w_i C 6 y) =
        (count C 1 - w_i C 1 y) + (count C 5 - w_i C 5 y) + w_i C 6 y + 1 := by
      have hd2d3 : dRow C 2 y = dRow C 3 y + 1 := hd2
      rw [hd2', hd3] at hd2d3
      omega
    have hcond2 : count C 6 + 3 ≤ 2 * (w_i C 3 y + w_i C 6 y) := by
      have hd0ge' : w_i C 1 y + w_i C 3 y + w_i C 5 y + w_i C 6 y ≥
          (count C 1 - w_i C 1 y) + (1 - w_i C 3 y) + (count C 5 - w_i C 5 y) +
            w_i C 6 y + 2 := by
        have h := hd0ge
        rw [hd3, hd0] at h
        exact h
      have hdirect : count C 6 + 2 ≤ 2 * (w_i C 3 y + w_i C 6 y) := by
        have hZ1 : (w_i C 1 y : ℤ) + (w_i C 5 y : ℤ) + ((count C 6 : ℤ) - w_i C 6 y) =
            ((count C 1 : ℤ) - w_i C 1 y) + ((count C 5 : ℤ) - w_i C 5 y) +
              (w_i C 6 y : ℤ) + 1 := by exact_mod_cast hcond1
        have hZ2 : (w_i C 1 y : ℤ) + (w_i C 3 y : ℤ) + (w_i C 5 y : ℤ) + (w_i C 6 y : ℤ) ≥
            ((count C 1 : ℤ) - w_i C 1 y) + (1 - w_i C 3 y) + ((count C 5 : ℤ) - w_i C 5 y) +
              (w_i C 6 y : ℤ) + 2 := by exact_mod_cast hd0ge'
        have hZ : (count C 6 : ℤ) + 2 ≤ 2 * ((w_i C 3 y : ℤ) + w_i C 6 y) := by omega
        exact_mod_cast hZ
      have hodd3 : Odd (count C 3) := by rw [h3]; exact ⟨0, rfl⟩
      have hodd6 : Odd (count C 6) := by
        rw [← Nat.not_even_iff_odd]
        intro he6
        have hodd3' : ¬ Even (count C 3) := (Nat.not_even_iff_odd.mpr hodd3)
        exact hodd3' (hpar36.mpr he6)
      rcases hodd6 with ⟨k, hk⟩
      have hk' : count C 6 = 2 * k + 1 := by omega
      have hE : Even (2 * (w_i C 3 y + w_i C 6 y)) := ⟨w_i C 3 y + w_i C 6 y, by omega⟩
      rcases hE with ⟨a, ha⟩
      have h2a : 2 * k + 3 ≤ 2 * a := by
        rw [hk', ha] at hdirect
        omega
      have hage : k + 2 ≤ a := by omega
      rw [hk', ha]
      omega
    have hcond3 : 2 * w_i C 5 y + 3 ≤ 2 * w_i C 3 y + count C 5 := by
      have hd1ge' : w_i C 1 y + w_i C 3 y + (count C 5 - w_i C 5 y) + (count C 6 - w_i C 6 y) ≥
          (count C 1 - w_i C 1 y) + (1 - w_i C 3 y) + (count C 5 - w_i C 5 y) +
            w_i C 6 y + 2 := by
        have h := hd1ge
        rw [hd3, hd1] at h
        exact h
      have hZ1 : (w_i C 1 y : ℤ) + (w_i C 5 y : ℤ) + ((count C 6 : ℤ) - w_i C 6 y) =
          ((count C 1 : ℤ) - w_i C 1 y) + ((count C 5 : ℤ) - w_i C 5 y) +
            (w_i C 6 y : ℤ) + 1 := by exact_mod_cast hcond1
      have hZ2 : (w_i C 1 y : ℤ) + (w_i C 3 y : ℤ) + ((count C 5 : ℤ) - w_i C 5 y) +
            ((count C 6 : ℤ) - w_i C 6 y) ≥
          ((count C 1 : ℤ) - w_i C 1 y) + (1 - w_i C 3 y) + ((count C 5 : ℤ) - w_i C 5 y) +
            (w_i C 6 y : ℤ) + 2 := by
        have hz : (w_i C 1 y : ℤ) + (w_i C 3 y : ℤ) +
              ((count C 5 - w_i C 5 y : ℕ) : ℤ) + ((count C 6 - w_i C 6 y : ℕ) : ℤ) ≥
            ((count C 1 - w_i C 1 y : ℕ) : ℤ) + ((1 - w_i C 3 y : ℕ) : ℤ) +
              ((count C 5 - w_i C 5 y : ℕ) : ℤ) + (w_i C 6 y : ℤ) + 2 := by
          exact_mod_cast hd1ge'
        rw [Nat.cast_sub hw5le, Nat.cast_sub hw6le, Nat.cast_sub hw1le, Nat.cast_sub hw3le] at hz
        exact hz
      have hZ : 2 * (w_i C 5 y : ℤ) + 2 ≤ 2 * (w_i C 3 y : ℤ) + (count C 5 : ℤ) := by omega
      have hodd3' : Odd (count C 3) := by rw [h3]; exact ⟨0, rfl⟩
      have hodd5 : Odd (count C 5) := by
        rw [← Nat.not_even_iff_odd]
        intro he5
        have hodd3'' : ¬ Even (count C 3) := (Nat.not_even_iff_odd.mpr hodd3')
        exact hodd3'' (hpar53.mp he5)
      rcases hodd5 with ⟨k, hk⟩
      have hk' : count C 5 = 2 * k + 1 := by omega
      have hZ' : 2 * (w_i C 5 y : ℤ) + 3 ≤ 2 * (w_i C 3 y : ℤ) + (count C 5 : ℤ) := by
        rw [hk'] at hZ
        omega
      exact_mod_cast hZ'
    exact ⟨hyt, hw3le, hcond1, hcond2, hcond3⟩
  · intro h
    rcases h with ⟨hyt, hcond⟩
    rcases hcond with ⟨hw3le, hcond1, hcond2, hcond3⟩
    refine ⟨hyt, ?_, ?_⟩
    · have hge0 : dRow C 3 y + 2 ≤ dRow C 0 y := by
        rw [hd3, hd0]
        have hZ1 : (w_i C 1 y : ℤ) + (w_i C 5 y : ℤ) + ((count C 6 : ℤ) - w_i C 6 y) =
            ((count C 1 : ℤ) - w_i C 1 y) + ((count C 5 : ℤ) - w_i C 5 y) +
              (w_i C 6 y : ℤ) + 1 := by exact_mod_cast hcond1
        have hZ2 : (count C 6 : ℤ) + 3 ≤ 2 * ((w_i C 3 y : ℤ) + w_i C 6 y) := by
          exact_mod_cast hcond2
        have hZ : (w_i C 1 y : ℤ) + (w_i C 3 y : ℤ) + (w_i C 5 y : ℤ) + (w_i C 6 y : ℤ) ≥
            ((count C 1 : ℤ) - w_i C 1 y) + (1 - w_i C 3 y) + ((count C 5 : ℤ) - w_i C 5 y) +
              (w_i C 6 y : ℤ) + 2 := by omega
        exact_mod_cast hZ
      have hge1 : dRow C 3 y + 2 ≤ dRow C 1 y := by
        rw [hd3, hd1]
        have hZ1 : (w_i C 1 y : ℤ) + (w_i C 5 y : ℤ) + ((count C 6 : ℤ) - w_i C 6 y) =
            ((count C 1 : ℤ) - w_i C 1 y) + ((count C 5 : ℤ) - w_i C 5 y) +
              (w_i C 6 y : ℤ) + 1 := by exact_mod_cast hcond1
        have hZ2 : 2 * (w_i C 5 y : ℤ) + 3 ≤ 2 * (w_i C 3 y : ℤ) + (count C 5 : ℤ) := by
          exact_mod_cast hcond3
        have hZ : (w_i C 1 y : ℤ) + (w_i C 3 y : ℤ) + ((count C 5 : ℤ) - w_i C 5 y) +
              ((count C 6 : ℤ) - w_i C 6 y) ≥
            ((count C 1 : ℤ) - w_i C 1 y) + (1 - w_i C 3 y) + ((count C 5 : ℤ) - w_i C 5 y) +
              (w_i C 6 y : ℤ) + 2 := by omega
        exact_mod_cast hZ
      exact le_min hge0 hge1
    · rw [hd2', hd3]
      have hZ1 : (w_i C 1 y : ℤ) + (w_i C 5 y : ℤ) + ((count C 6 : ℤ) - w_i C 6 y) =
          ((count C 1 : ℤ) - w_i C 1 y) + ((count C 5 : ℤ) - w_i C 5 y) +
            (w_i C 6 y : ℤ) + 1 := by exact_mod_cast hcond1
      have hZ : (w_i C 1 y : ℤ) + (1 - w_i C 3 y) + (w_i C 5 y : ℤ) +
            ((count C 6 : ℤ) - w_i C 6 y) =
          ((count C 1 : ℤ) - w_i C 1 y) + (1 - w_i C 3 y) + ((count C 5 : ℤ) - w_i C 5 y) +
            (w_i C 6 y : ℤ) + 1 := by omega
      exact_mod_cast hZ

/-- For a |3| = 1 code every Y5 word satisfies dCode + w₃ = n/2, hence
dCode ∈ {n/2−1, n/2} with w₃ = 1 ⟺ dCode = n/2−1 (paper eq. 5yc1). -/
lemma Y5_dist_c3one {n : ℕ} (C : Code n) (t : Fin n) (y : Word n)
    (htypes : ∀ u : Fin n, colVal (C u) = 1 ∨ colVal (C u) = 3 ∨
      colVal (C u) = 5 ∨ colVal (C u) = 6)
    (hcol : C t = col1) (h3 : count C 3 = 1)
    (hpar36 : Even (count C 3) ↔ Even (count C 6))
    (hpar53 : Even (count C 5) ↔ Even (count C 3))
    (htotal : totalCounts C {1, 3, 5, 6} = n) (hy : Y5 C t y) :
    dCode C y + w_i C 3 y = n / 2 ∧
      (dCode C y = n / 2 - 1 ∨ dCode C y = n / 2) := by
  have hw3le : w_i C 3 y ≤ 1 := by
    exact le_trans (w_i_le_count C 3 y) (by rw [h3])
  have hw1le : w_i C 1 y ≤ count C 1 := w_i_le_count C 1 y
  have hw5le : w_i C 5 y ≤ count C 5 := w_i_le_count C 5 y
  have hw6le : w_i C 6 y ≤ count C 6 := w_i_le_count C 6 y
  rcases (Y5_iff_col1 C t y hcol).1 hy with ⟨_hyt, hmin, hd2⟩
  have hd3d0 : dRow C 3 y ≤ dRow C 0 y := by
    have hle0 : dRow C 3 y + 2 ≤ dRow C 0 y := le_trans hmin (Nat.min_le_left _ _)
    omega
  have hd3d1 : dRow C 3 y ≤ dRow C 1 y := by
    have hle1 : dRow C 3 y + 2 ≤ dRow C 1 y := le_trans hmin (Nat.min_le_right _ _)
    omega
  have hd3d2 : dRow C 3 y < dRow C 2 y := by
    rw [hd2]
    omega
  have hdCode : dCode C y = dRow C 3 y := by
    unfold dCode
    rw [show hammingDist (row0 C) y = dRow C 0 y by rfl]
    rw [show hammingDist (row1 C) y = dRow C 1 y by rfl]
    rw [show hammingDist (row2 C) y = dRow C 2 y by rfl]
    rw [show hammingDist (row3 C) y = dRow C 3 y by rfl]
    rw [Nat.min_eq_right (le_of_lt hd3d2), Nat.min_eq_right hd3d1, Nat.min_eq_right hd3d0]
  have hd2' : dRow C 2 y = w_i C 1 y + (1 - w_i C 3 y) + w_i C 5 y +
      (count C 6 - w_i C 6 y) := by
    rw [dRow2_of_type1356 C htypes y, h3]
  have hd3' : dRow C 3 y = (count C 1 - w_i C 1 y) + (1 - w_i C 3 y) +
      (count C 5 - w_i C 5 y) + w_i C 6 y := by
    rw [dRow3_of_type1356 C htypes y, h3]
  have hc := (Y5_iff_weights_c3one C t y htypes hcol h3 hpar36 hpar53).1 hy
  have hcond1 : w_i C 1 y + w_i C 5 y + (count C 6 - w_i C 6 y) =
      (count C 1 - w_i C 1 y) + (count C 5 - w_i C 5 y) + w_i C 6 y + 1 := hc.2.2.1
  have hsum : count C 1 + count C 5 + count C 6 = n - 1 := by
    have h4 : count C 1 + count C 3 + count C 5 + count C 6 = n := by
      calc
        count C 1 + count C 3 + count C 5 + count C 6
            = ∑ i ∈ ({1, 3, 5, 6} : Finset ℕ), count C i := by
              simp [Finset.sum_insert]
              omega
        _ = n := htotal
    rw [h3] at h4
    omega
  have h2d3 : 2 * dRow C 3 y = n - 2 * w_i C 3 y := by
    have hsum' : count C 1 + count C 5 + count C 6 + 1 = n := by omega
    rw [hd3']
    omega
  have hmain : 2 * dCode C y = n - 2 * w_i C 3 y := by
    rw [hdCode]
    exact h2d3
  have hmain' : dCode C y + w_i C 3 y = n / 2 := by
    have h2 : n = 2 * (dCode C y + w_i C 3 y) := by omega
    calc
      dCode C y + w_i C 3 y = (2 * (dCode C y + w_i C 3 y)) / 2 := by
        rw [Nat.mul_div_right _ (by decide : 0 < 2)]
      _ = n / 2 := by rw [← h2]
  have hmem : dCode C y = n / 2 - 1 ∨ dCode C y = n / 2 := by
    have hw3 : w_i C 3 y = 0 ∨ w_i C 3 y = 1 := by omega
    rcases hw3 with hw30 | hw31
    · right
      omega
    · left
      omega
  exact ⟨hmain', hmem⟩

/-- With |3| = 1, α⁵(d) = 0 unless d ∈ {n/2−1, n/2} (paper eq. 5yc1). -/
lemma class1_alpha5_eq_zero_c3one {n : ℕ} (C : Code n) (t : Fin n) (d : ℕ)
    (htypes : ∀ u : Fin n, colVal (C u) = 1 ∨ colVal (C u) = 3 ∨
      colVal (C u) = 5 ∨ colVal (C u) = 6)
    (hcol : C t = col1) (h3 : count C 3 = 1)
    (hpar36 : Even (count C 3) ↔ Even (count C 6))
    (hpar53 : Even (count C 5) ↔ Even (count C 3))
    (htotal : totalCounts C {1, 3, 5, 6} = n)
    (hd : d ≠ n / 2 - 1 ∧ d ≠ n / 2) :
    alpha5 C t d = 0 := by
  unfold alpha5
  by_contra h
  have hpos : 0 < (Finset.univ.filter fun y : Word n => Y5 C t y ∧ dCode C y = d).card := by
    exact Nat.pos_of_ne_zero h
  rcases Finset.card_pos.mp hpos with ⟨y, hmem⟩
  have hy5 : Y5 C t y := (Finset.mem_filter.mp hmem).2.1
  have hdc : dCode C y = d := (Finset.mem_filter.mp hmem).2.2
  have hd' := (Y5_dist_c3one C t y htypes hcol h3 hpar36 hpar53 htotal hy5).2
  rcases hd' with hleft | hright
  · exact hd.1 (by omega)
  · exact hd.2 (by omega)


/-- With |3| = 0, Ψ_d ≥ 0 for all d (thm:301 Class-I-a): below (n−1)/2 the
α⁵ sum vanishes (eq. 5yc1), and above it the binomial core applies. -/
lemma class1_psi_nonneg_c3zero {n : ℕ} (C : Code n) (t : Fin n) (d : ℕ) (hd : 1 ≤ d)
    (htypes : ∀ u : Fin n, colVal (C u) = 1 ∨ colVal (C u) = 3 ∨
      colVal (C u) = 5 ∨ colVal (C u) = 6)
    (hcol : C t = col1) (h3 : count C 3 = 0)
    (hpar35 : Even (count C 5) ↔ Even (count C 6))
    (hpar36 : Even (count C 3) ↔ Even (count C 6))
    (hpar53 : Even (count C 5) ↔ Even (count C 3))
    (htotal : totalCounts C {1, 3, 5, 6} = n) (hodd1 : Odd (count C 1)) :
    Psi C t d ≥ 0 := by
  by_cases hlow : d ≤ (n - 1) / 2
  · unfold Psi
    have hsum5 : (∑ i ∈ Finset.Icc 0 (d - 1), alpha5 C t i) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hile : i ≤ d - 1 := (Finset.mem_Icc.mp hi).2
      have hne : i ≠ (n - 1) / 2 := by omega
      exact class1_alpha5_eq_zero_of_ne_threshold C t i htypes hcol h3 htotal hne
    have h5z : (∑ i ∈ Finset.Icc 0 (d - 1), (alpha5 C t i : ℤ)) = 0 := by
      exact_mod_cast hsum5
    rw [h5z]
    simp
    exact_mod_cast (Nat.zero_le (∑ i ∈ Finset.Icc 1 d, alpha3 C t i))
  · have hnodd : Odd n := by
      rcases hodd1 with ⟨a, ha⟩
      have hc3e : Even (count C 3) := by rw [h3]; exact ⟨0, rfl⟩
      have hc5e : Even (count C 5) := hpar53.2 hc3e
      have hc6e : Even (count C 6) := hpar36.1 hc3e
      rcases hc5e with ⟨b, hb⟩
      rcases hc6e with ⟨c, hc⟩
      refine ⟨a + b + c, ?_⟩
      have hsum : count C 1 + count C 3 + count C 5 + count C 6 = n := by
        calc
          count C 1 + count C 3 + count C 5 + count C 6
              = ∑ i ∈ ({1, 3, 5, 6} : Finset ℕ), count C i := by
                simp [Finset.sum_insert]
                omega
          _ = n := htotal
      rw [ha, h3, hb, hc] at hsum
      omega
    rcases hnodd with ⟨k, hk⟩
    have hdiv : (n + 1) / 2 = (n - 1) / 2 + 1 := by
      have hnp1 : n + 1 = 2 * (k + 1) := by omega
      have hnm1 : n - 1 = 2 * k := by omega
      rw [hnp1, Nat.mul_div_right (k + 1) (by decide : 0 < 2)]
      rw [hnm1, Nat.mul_div_right k (by decide : 0 < 2)]
    have hdhigh : (n + 1) / 2 ≤ d := by
      have hgt : (n - 1) / 2 < d := Nat.lt_of_not_ge hlow
      omega
    unfold Psi
    have hsum5 : (∑ i ∈ Finset.Icc 0 (d - 1), alpha5 C t i) =
        alpha5 C t ((n - 1) / 2) := by
      refine Finset.sum_eq_single (a := (n - 1) / 2) ?_ ?_
      · intro i hi hne
        exact class1_alpha5_eq_zero_of_ne_threshold C t i htypes hcol h3 htotal hne
      · intro hnotmem
        have hmem : (n - 1) / 2 ∈ Finset.Icc 0 (d - 1) := by
          rw [Finset.mem_Icc]
          omega
        exact (hnotmem hmem).elim
    have h5z : (∑ i ∈ Finset.Icc 0 (d - 1), (alpha5 C t i : ℤ)) =
        (alpha5 C t ((n - 1) / 2) : ℤ) := by
      exact_mod_cast hsum5
    rw [h5z]
    have hge : (∑ i ∈ Finset.Icc 1 d, alpha3 C t i) ≥ alpha5 C t ((n - 1) / 2) :=
      class1_alpha3_cum_ge_alpha5_threshold C t d htypes hcol h3 hpar35 hpar36 hpar53 htotal hodd1 hdhigh
    exact sub_nonneg.mpr (by exact_mod_cast hge)

/-- Number of words with y_t = 1 and prescribed weights (w1, w3, w5, w6) on
the types 1, 3, 5, 6: C(|1|−1,w1−1)·C(|3|,w3)·C(|5|,w5)·C(|6|,w6). -/
lemma count_words_htrue_weights_1356_w3 {n : ℕ} (C : Code n)
    (htypes : ∀ u : Fin n, colVal (C u) = 1 ∨ colVal (C u) = 3 ∨
      colVal (C u) = 5 ∨ colVal (C u) = 6)
    (t : Fin n) (hcol : C t = col1) (w1 w3 w5 w6 : ℕ) (hw1pos : 1 ≤ w1) :
    ((Finset.univ : Finset (Word n)).filter
      fun y => y t = true ∧ w_i C 1 y = w1 ∧ w_i C 3 y = w3 ∧
        w_i C 5 y = w5 ∧ w_i C 6 y = w6).card =
      Nat.choose (count C 1 - 1) (w1 - 1) * Nat.choose (count C 3) w3 *
        Nat.choose (count C 5) w5 * Nat.choose (count C 6) w6 := by
  let S : Finset (Word n) := (Finset.univ : Finset (Word n)).filter
    fun y => y t = true ∧ w_i C 1 y = w1 ∧ w_i C 3 y = w3 ∧
      w_i C 5 y = w5 ∧ w_i C 6 y = w6
  let A : Finset (Fin n) := fiber C 1 \ {t}
  let T : Finset (Finset (Fin n) × Finset (Fin n) × Finset (Fin n) × Finset (Fin n)) :=
    (A.powersetCard (w1 - 1)) ×ˢ ((fiber C 3).powersetCard w3) ×ˢ
      ((fiber C 5).powersetCard w5) ×ˢ ((fiber C 6).powersetCard w6)
  have ht : t ∈ fiber C 1 := by simp [fiber, hcol, colVal_col1]
  have hcardA : A.card = count C 1 - 1 := by
    dsimp [A]
    rw [← Finset.erase_eq, Finset.card_erase_of_mem ht, fiber_card_eq_count C 1]
  have hcardT : T.card = Nat.choose (count C 1 - 1) (w1 - 1) * Nat.choose (count C 3) w3 *
      Nat.choose (count C 5) w5 * Nat.choose (count C 6) w6 := by
    dsimp [T]
    rw [Finset.card_product, Finset.card_product, Finset.card_product, Finset.card_powersetCard,
        Finset.card_powersetCard, Finset.card_powersetCard, Finset.card_powersetCard,
        hcardA, fiber_card_eq_count C 3, fiber_card_eq_count C 5, fiber_card_eq_count C 6]
    ring
  have hdisj13 : Disjoint (fiber C 1) (fiber C 3) := fiber_disjoint_1356 C (by decide : (1 : ℕ) ≠ 3)
  have hdisj15 : Disjoint (fiber C 1) (fiber C 5) := fiber_disjoint_1356 C (by decide : (1 : ℕ) ≠ 5)
  have hdisj16 : Disjoint (fiber C 1) (fiber C 6) := fiber_disjoint_1356 C (by decide : (1 : ℕ) ≠ 6)
  have hdisj35 : Disjoint (fiber C 3) (fiber C 5) := fiber_disjoint_1356 C (by decide : (3 : ℕ) ≠ 5)
  have hdisj36 : Disjoint (fiber C 3) (fiber C 6) := fiber_disjoint_1356 C (by decide : (3 : ℕ) ≠ 6)
  have hdisj56 : Disjoint (fiber C 5) (fiber C 6) := fiber_disjoint_1356 C (by decide : (5 : ℕ) ≠ 6)
  have hones_split (y : Word n) (hyt : y t = true) :
      onesOn (fiber C 1) y = insert t (onesOn A y) := by
    ext u
    constructor
    · intro hu
      have huf : u ∈ fiber C 1 := (Finset.mem_filter.mp hu).1
      have hut : y u = true := (Finset.mem_filter.mp hu).2
      by_cases hut' : u = t
      · simp [hut']
      · have huA : u ∈ A := by
          simp [A]
          exact ⟨huf, hut'⟩
        have huones : u ∈ onesOn A y := Finset.mem_filter.mpr ⟨huA, hut⟩
        simp [huones]
    · intro hu
      rcases Finset.mem_insert.mp hu with hut' | huA
      · subst u
        exact Finset.mem_filter.mpr ⟨ht, hyt⟩
      · have huA' : u ∈ A := (Finset.mem_filter.mp huA).1
        have huf : u ∈ fiber C 1 := (Finset.mem_sdiff.mp huA').1
        have hut'' : y u = true := (Finset.mem_filter.mp huA).2
        exact Finset.mem_filter.mpr ⟨huf, hut''⟩
  have hnot_t (y : Word n) (hyt : y t = true) : t ∉ onesOn A y := by
    intro htA
    have hmem : t ∈ A := (Finset.mem_filter.mp htA).1
    exact (Finset.mem_sdiff.mp hmem).2 (by simp)
  have hcard : S.card = T.card := by
    dsimp [S, T]
    refine Finset.card_bij
      (fun y _ => (onesOn A y, ⟨onesOn (fiber C 3) y, ⟨onesOn (fiber C 5) y, onesOn (fiber C 6) y⟩⟩)) ?_ ?_ ?_
    · intro y hy
      rcases (Finset.mem_filter.mp hy).2 with ⟨hyt, hw1, hw3, hw5, hw6⟩
      have hcardA1 : (onesOn A y).card = w1 - 1 := by
        have hcard1 : (onesOn (fiber C 1) y).card = w1 := by
          rw [← w_i_eq_card_onesOn, hw1]
        rw [hones_split y hyt, Finset.card_insert_of_notMem (hnot_t y hyt)] at hcard1
        omega
      have hcard3 : (onesOn (fiber C 3) y).card = w3 := by
        rw [← w_i_eq_card_onesOn, hw3]
      have hcard5 : (onesOn (fiber C 5) y).card = w5 := by
        rw [← w_i_eq_card_onesOn, hw5]
      have hcard6 : (onesOn (fiber C 6) y).card = w6 := by
        rw [← w_i_eq_card_onesOn, hw6]
      exact Finset.mem_product.mpr
        ⟨Finset.mem_powersetCard.mpr ⟨by exact Finset.filter_subset _ _, hcardA1⟩,
          Finset.mem_product.mpr
            ⟨Finset.mem_powersetCard.mpr ⟨by exact Finset.filter_subset _ _, hcard3⟩,
              Finset.mem_product.mpr
                ⟨Finset.mem_powersetCard.mpr ⟨by exact Finset.filter_subset _ _, hcard5⟩,
                  Finset.mem_powersetCard.mpr ⟨by exact Finset.filter_subset _ _, hcard6⟩⟩⟩⟩
    · intro y hy y' hy' h
      apply (word_eq_iff_ones y y').2
      intro u
      have hyt : y t = true := (Finset.mem_filter.mp hy).2.1
      have hyt' : y' t = true := (Finset.mem_filter.mp hy').2.1
      have hA : onesOn A y = onesOn A y' := congrArg Prod.fst h
      have h3 : onesOn (fiber C 3) y = onesOn (fiber C 3) y' := congrArg (fun g => g.2.1) h
      have h5 : onesOn (fiber C 5) y = onesOn (fiber C 5) y' := congrArg (fun g => g.2.2.1) h
      have h6 : onesOn (fiber C 6) y = onesOn (fiber C 6) y' := congrArg (fun g => g.2.2.2) h
      rcases htypes u with h1' | h3' | h5' | h6'
      · by_cases hut : u = t
        · subst u
          exact ⟨fun _ => hyt', fun _ => hyt⟩
        · have huf : u ∈ fiber C 1 := by simp [fiber, h1']
          constructor
          · intro hyu
            have huA : u ∈ onesOn A y := Finset.mem_filter.mpr ⟨by simp [A]; exact ⟨huf, hut⟩, hyu⟩
            have huA' : u ∈ onesOn A y' := by simpa [hA] using huA
            exact (Finset.mem_filter.mp huA').2
          · intro hy'u
            have huA' : u ∈ onesOn A y' := Finset.mem_filter.mpr ⟨by simp [A]; exact ⟨huf, hut⟩, hy'u⟩
            have huA : u ∈ onesOn A y := by simpa [← hA] using huA'
            exact (Finset.mem_filter.mp huA).2
      · have huf : u ∈ fiber C 3 := by simp [fiber, h3']
        constructor
        · intro hyu
          have hu3 : u ∈ onesOn (fiber C 3) y := Finset.mem_filter.mpr ⟨huf, hyu⟩
          have hu3' : u ∈ onesOn (fiber C 3) y' := by simpa [h3] using hu3
          exact (Finset.mem_filter.mp hu3').2
        · intro hy'u
          have hu3' : u ∈ onesOn (fiber C 3) y' := Finset.mem_filter.mpr ⟨huf, hy'u⟩
          have hu3 : u ∈ onesOn (fiber C 3) y := by simpa [← h3] using hu3'
          exact (Finset.mem_filter.mp hu3).2
      · have huf : u ∈ fiber C 5 := by simp [fiber, h5']
        constructor
        · intro hyu
          have hu5 : u ∈ onesOn (fiber C 5) y := Finset.mem_filter.mpr ⟨huf, hyu⟩
          have hu5' : u ∈ onesOn (fiber C 5) y' := by simpa [h5] using hu5
          exact (Finset.mem_filter.mp hu5').2
        · intro hy'u
          have hu5' : u ∈ onesOn (fiber C 5) y' := Finset.mem_filter.mpr ⟨huf, hy'u⟩
          have hu5 : u ∈ onesOn (fiber C 5) y := by simpa [← h5] using hu5'
          exact (Finset.mem_filter.mp hu5).2
      · have huf : u ∈ fiber C 6 := by simp [fiber, h6']
        constructor
        · intro hyu
          have hu6 : u ∈ onesOn (fiber C 6) y := Finset.mem_filter.mpr ⟨huf, hyu⟩
          have hu6' : u ∈ onesOn (fiber C 6) y' := by simpa [h6] using hu6
          exact (Finset.mem_filter.mp hu6').2
        · intro hy'u
          have hu6' : u ∈ onesOn (fiber C 6) y' := Finset.mem_filter.mpr ⟨huf, hy'u⟩
          have hu6 : u ∈ onesOn (fiber C 6) y := by simpa [← h6] using hu6'
          exact (Finset.mem_filter.mp hu6).2
    · intro g hg
      let y : Word n := fun u => u = t ∨ u ∈ g.1 ∨ u ∈ g.2.1 ∨ u ∈ g.2.2.1 ∨ u ∈ g.2.2.2
      have hg1 : g.1 ∈ A.powersetCard (w1 - 1) := (Finset.mem_product.mp hg).1
      have hg3 : g.2.1 ∈ (fiber C 3).powersetCard w3 :=
        (Finset.mem_product.mp (Finset.mem_product.mp hg).2).1
      have hg5 : g.2.2.1 ∈ (fiber C 5).powersetCard w5 :=
        (Finset.mem_product.mp (Finset.mem_product.mp (Finset.mem_product.mp hg).2).2).1
      have hg6 : g.2.2.2 ∈ (fiber C 6).powersetCard w6 :=
        (Finset.mem_product.mp (Finset.mem_product.mp (Finset.mem_product.mp hg).2).2).2
      have hg1sub : g.1 ⊆ A := (Finset.mem_powersetCard.mp hg1).1
      have hg1card : g.1.card = w1 - 1 := (Finset.mem_powersetCard.mp hg1).2
      have hg3sub : g.2.1 ⊆ fiber C 3 := (Finset.mem_powersetCard.mp hg3).1
      have hg3card : g.2.1.card = w3 := (Finset.mem_powersetCard.mp hg3).2
      have hg5sub : g.2.2.1 ⊆ fiber C 5 := (Finset.mem_powersetCard.mp hg5).1
      have hg5card : g.2.2.1.card = w5 := (Finset.mem_powersetCard.mp hg5).2
      have hg6sub : g.2.2.2 ⊆ fiber C 6 := (Finset.mem_powersetCard.mp hg6).1
      have hg6card : g.2.2.2.card = w6 := (Finset.mem_powersetCard.mp hg6).2
      have hg1sub1 : g.1 ⊆ fiber C 1 := by
        intro u hu
        exact (Finset.mem_sdiff.mp (hg1sub hu)).1
      have hones1 : onesOn (fiber C 1) y = insert t g.1 := by
        ext u
        constructor
        · intro hu
          have huf : u ∈ fiber C 1 := (Finset.mem_filter.mp hu).1
          have hut : y u = true := (Finset.mem_filter.mp hu).2
          have hnot3 : u ∉ fiber C 3 := fun h => (Finset.disjoint_left.mp hdisj13) huf h
          have hnot5 : u ∉ fiber C 5 := fun h => (Finset.disjoint_left.mp hdisj15) huf h
          have hnot6 : u ∉ fiber C 6 := fun h => (Finset.disjoint_left.mp hdisj16) huf h
          simp [y] at hut
          rcases hut with hut | hg1' | hg3' | hg5' | hg6'
          · simp [hut]
          · simp [hg1']
          · exact False.elim (hnot3 (hg3sub hg3'))
          · exact False.elim (hnot5 (hg5sub hg5'))
          · exact False.elim (hnot6 (hg6sub hg6'))
        · intro hu
          rcases Finset.mem_insert.mp hu with hut | hg1'
          · subst u
            exact Finset.mem_filter.mpr ⟨ht, by simp [y]⟩
          · have huf : u ∈ fiber C 1 := hg1sub1 hg1'
            exact Finset.mem_filter.mpr ⟨huf, by simp [y, hg1']⟩
      have hones3 : onesOn (fiber C 3) y = g.2.1 := by
        ext u
        constructor
        · intro hu
          have huf : u ∈ fiber C 3 := (Finset.mem_filter.mp hu).1
          have hut : y u = true := (Finset.mem_filter.mp hu).2
          have hnot1 : u ∉ fiber C 1 := fun h => (Finset.disjoint_left.mp hdisj13) h huf
          have hnot5 : u ∉ fiber C 5 := fun h => (Finset.disjoint_left.mp hdisj35) huf h
          have hnot6 : u ∉ fiber C 6 := fun h => (Finset.disjoint_left.mp hdisj36) huf h
          simp [y] at hut
          rcases hut with hut | hg1' | hg3' | hg5' | hg6'
          · have huf1 : t ∈ fiber C 1 := ht
            subst u
            exact False.elim ((Finset.disjoint_left.mp hdisj13) huf1 huf)
          · exact False.elim (hnot1 (hg1sub1 hg1'))
          · exact hg3'
          · exact False.elim (hnot5 (hg5sub hg5'))
          · exact False.elim (hnot6 (hg6sub hg6'))
        · intro hg3'
          have huf : u ∈ fiber C 3 := hg3sub hg3'
          exact Finset.mem_filter.mpr ⟨huf, by simp [y, hg3']⟩
      have hones5 : onesOn (fiber C 5) y = g.2.2.1 := by
        ext u
        constructor
        · intro hu
          have huf : u ∈ fiber C 5 := (Finset.mem_filter.mp hu).1
          have hut : y u = true := (Finset.mem_filter.mp hu).2
          have hnot1 : u ∉ fiber C 1 := fun h => (Finset.disjoint_left.mp hdisj15) h huf
          have hnot3 : u ∉ fiber C 3 := fun h => (Finset.disjoint_left.mp hdisj35) h huf
          have hnot6 : u ∉ fiber C 6 := fun h => (Finset.disjoint_left.mp hdisj56) huf h
          simp [y] at hut
          rcases hut with hut | hg1' | hg3' | hg5' | hg6'
          · have huf1 : t ∈ fiber C 1 := ht
            subst u
            exact False.elim ((Finset.disjoint_left.mp hdisj15) huf1 huf)
          · exact False.elim (hnot1 (hg1sub1 hg1'))
          · exact False.elim (hnot3 (hg3sub hg3'))
          · exact hg5'
          · exact False.elim (hnot6 (hg6sub hg6'))
        · intro hg5'
          have huf : u ∈ fiber C 5 := hg5sub hg5'
          exact Finset.mem_filter.mpr ⟨huf, by simp [y, hg5']⟩
      have hones6 : onesOn (fiber C 6) y = g.2.2.2 := by
        ext u
        constructor
        · intro hu
          have huf : u ∈ fiber C 6 := (Finset.mem_filter.mp hu).1
          have hut : y u = true := (Finset.mem_filter.mp hu).2
          have hnot1 : u ∉ fiber C 1 := fun h => (Finset.disjoint_left.mp hdisj16) h huf
          have hnot3 : u ∉ fiber C 3 := fun h => (Finset.disjoint_left.mp hdisj36) h huf
          have hnot5 : u ∉ fiber C 5 := fun h => (Finset.disjoint_left.mp hdisj56) h huf
          simp [y] at hut
          rcases hut with hut | hg1' | hg3' | hg5' | hg6'
          · have huf1 : t ∈ fiber C 1 := ht
            subst u
            exact False.elim ((Finset.disjoint_left.mp hdisj16) huf1 huf)
          · exact False.elim (hnot1 (hg1sub1 hg1'))
          · exact False.elim (hnot3 (hg3sub hg3'))
          · exact False.elim (hnot5 (hg5sub hg5'))
          · exact hg6'
        · intro hg6'
          have huf : u ∈ fiber C 6 := hg6sub hg6'
          exact Finset.mem_filter.mpr ⟨huf, by simp [y, hg6']⟩
      have hw1' : w_i C 1 y = w1 := by
        have hnotg : t ∉ g.1 := by
          intro htA
          have hmemA : t ∈ A := hg1sub htA
          exact (Finset.mem_sdiff.mp hmemA).2 (by simp)
        rw [w_i_eq_card_onesOn, hones1, Finset.card_insert_of_notMem hnotg, hg1card]
        omega
      have hw3' : w_i C 3 y = w3 := by
        rw [w_i_eq_card_onesOn, hones3, hg3card]
      have hw5' : w_i C 5 y = w5 := by
        rw [w_i_eq_card_onesOn, hones5, hg5card]
      have hw6' : w_i C 6 y = w6 := by
        rw [w_i_eq_card_onesOn, hones6, hg6card]
      refine ⟨y, ?_, ?_⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ y, ⟨by simp [y], hw1', hw3', hw5', hw6'⟩⟩
      · have hA' : onesOn A y = g.1 := by
          have hsplit : onesOn A y = onesOn (fiber C 1) y \ {t} := by
            ext u
            constructor
            · intro hu
              have huA : u ∈ A := (Finset.mem_filter.mp hu).1
              have hut : y u = true := (Finset.mem_filter.mp hu).2
              exact Finset.mem_sdiff.mpr
                ⟨Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp huA).1, hut⟩, (Finset.mem_sdiff.mp huA).2⟩
            · intro hu
              have hu12 := Finset.mem_sdiff.mp hu
              have hu1 : u ∈ fiber C 1 := (Finset.mem_filter.mp hu12.1).1
              have hut : y u = true := (Finset.mem_filter.mp hu12.1).2
              have hut' : u ≠ t := by
                intro h
                exact hu12.2 (by simp [h])
              exact Finset.mem_filter.mpr
                ⟨Finset.mem_sdiff.mpr ⟨hu1, by intro h; exact hut' (Finset.mem_singleton.mp h)⟩, hut⟩
          rw [hsplit, hones1]
          ext u
          simp
          constructor
          · intro hu
            rcases hu with ⟨hut', hne⟩
            rcases hut' with hmem | hmem
            · subst u
              exact False.elim (hne (by simp))
            · exact hmem
          · intro hmem
            refine ⟨Or.inr hmem, ?_⟩
            intro hut
            subst u
            have hmemA : t ∈ A := hg1sub hmem
            exact (Finset.mem_sdiff.mp hmemA).2 (by simp)
        have h3' : onesOn (fiber C 3) y = g.2.1 := hones3
        have h5' : onesOn (fiber C 5) y = g.2.2.1 := hones5
        have h6' : onesOn (fiber C 6) y = g.2.2.2 := hones6
        rw [hA', h3', h5', h6']
  rw [← hcardT, ← hcard]
/-- α⁵(i) for |3| = 1 as the binomial sum over the w3 = w3v Y5 region
(paper eq. of1/eq. of3 first lines). -/
lemma alpha5_c3one_eq_sum_aux {n : ℕ} (C : Code n) (t : Fin n) (i w3v : ℕ)
    (htypes : ∀ u : Fin n, colVal (C u) = 1 ∨ colVal (C u) = 3 ∨
      colVal (C u) = 5 ∨ colVal (C u) = 6)
    (hcol : C t = col1) (h3 : count C 3 = 1)
    (hpar36 : Even (count C 3) ↔ Even (count C 6))
    (hpar53 : Even (count C 5) ↔ Even (count C 3))
    (_htotal : totalCounts C {1, 3, 5, 6} = n)
    (hdist : ∀ y : Word n, Y5 C t y → (dCode C y = i ↔ w_i C 3 y = w3v))
    (hcond : ∀ y : Word n, Y5 C t y → w_i C 3 y = w3v →
      Y5WeightCondC3one C w3v (w_i C 1 y) (w_i C 5 y) (w_i C 6 y))
    (hcond' : ∀ y : Word n, y t = true → w_i C 3 y = w3v →
      Y5WeightCondC3one C w3v (w_i C 1 y) (w_i C 5 y) (w_i C 6 y) → Y5 C t y) :
    alpha5 C t i =
      ∑ w1 ∈ Finset.Icc 1 (count C 1),
        ∑ w5 ∈ Finset.Icc 0 (count C 5),
          ∑ w6 ∈ Finset.Icc 0 (count C 6),
            if Y5WeightCondC3one C w3v w1 w5 w6 then
              Nat.choose (count C 1 - 1) (w1 - 1) * Nat.choose (count C 5) w5 *
                Nat.choose (count C 6) w6
            else 0 := by
  unfold alpha5
  let F : ℕ × ℕ × ℕ → Finset (Word n) := fun w =>
    (Finset.univ : Finset (Word n)).filter
      fun y => y t = true ∧ w_i C 3 y = w3v ∧ w_i C 1 y = w.1 ∧
        w_i C 5 y = w.2.1 ∧ w_i C 6 y = w.2.2
  let S : Finset (ℕ × ℕ × ℕ) :=
    (Finset.Icc 1 (count C 1)) ×ˢ ((Finset.Icc 0 (count C 5)) ×ˢ (Finset.Icc 0 (count C 6)))
  let W : Finset (ℕ × ℕ × ℕ) := S.filter fun w => Y5WeightCondC3one C w3v w.1 w.2.1 w.2.2
  have hA : (Finset.univ.filter fun y : Word n => Y5 C t y ∧ dCode C y = i) =
      Finset.univ.filter fun y : Word n => Y5 C t y ∧ w_i C 3 y = w3v := by
    ext y
    constructor
    · intro hy
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ y, ⟨(Finset.mem_filter.mp hy).2.1,
        (hdist y (Finset.mem_filter.mp hy).2.1).1 (Finset.mem_filter.mp hy).2.2⟩⟩
    · intro hy
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ y, ⟨(Finset.mem_filter.mp hy).2.1,
        (hdist y (Finset.mem_filter.mp hy).2.1).2 (Finset.mem_filter.mp hy).2.2⟩⟩
  have hB : (Finset.univ.filter fun y : Word n => Y5 C t y ∧ w_i C 3 y = w3v) = W.biUnion F := by
    ext y
    constructor
    · intro hy
      have hy5 : Y5 C t y := (Finset.mem_filter.mp hy).2.1
      have hw3 : w_i C 3 y = w3v := (Finset.mem_filter.mp hy).2.2
      have hc := (Y5_iff_weights_c3one C t y htypes hcol h3 hpar36 hpar53).1 hy5
      have hcondw : Y5WeightCondC3one C w3v (w_i C 1 y) (w_i C 5 y) (w_i C 6 y) := hcond y hy5 hw3
      have hw1le : w_i C 1 y ≤ count C 1 := w_i_le_count C 1 y
      have hw5le : w_i C 5 y ≤ count C 5 := w_i_le_count C 5 y
      have hw6le : w_i C 6 y ≤ count C 6 := w_i_le_count C 6 y
      have hmem1 : t ∈ onesOn (fiber C 1) y :=
        Finset.mem_filter.mpr ⟨by simp [fiber, hcol, colVal_col1], hc.1⟩
      have hc1 : 1 ≤ (onesOn (fiber C 1) y).card := Finset.card_pos.mpr ⟨t, hmem1⟩
      have hw1pos : 1 ≤ w_i C 1 y := by
        rw [← w_i_eq_card_onesOn] at hc1
        exact hc1
      refine Finset.mem_biUnion.mpr ⟨(w_i C 1 y, (w_i C 5 y, w_i C 6 y)), ?_, ?_⟩
      · refine Finset.mem_filter.mpr ⟨?_, hcondw⟩
        refine Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hw1pos, hw1le⟩, ?_⟩
        refine Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.zero_le _, hw5le⟩,
          Finset.mem_Icc.mpr ⟨Nat.zero_le _, hw6le⟩⟩
      · refine Finset.mem_filter.mpr ⟨Finset.mem_univ y, ?_⟩
        exact ⟨hc.1, hw3, rfl, rfl, rfl⟩
    · intro hy
      rcases Finset.mem_biUnion.mp hy with ⟨w, hw, hyw⟩
      have hcondw : Y5WeightCondC3one C w3v w.1 w.2.1 w.2.2 := (Finset.mem_filter.mp hw).2
      have hywf := (Finset.mem_filter.mp hyw).2
      have hyt : y t = true := hywf.1
      have hw3 : w_i C 3 y = w3v := hywf.2.1
      have hw1 : w_i C 1 y = w.1 := hywf.2.2.1
      have hw5 : w_i C 5 y = w.2.1 := hywf.2.2.2.1
      have hw6 : w_i C 6 y = w.2.2 := hywf.2.2.2.2
      have hcondw' : Y5WeightCondC3one C w3v (w_i C 1 y) (w_i C 5 y) (w_i C 6 y) := by
        simpa [← hw1, ← hw5, ← hw6] using hcondw
      have hy5 : Y5 C t y := hcond' y hyt hw3 hcondw'
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ y, ⟨hy5, hw3⟩⟩
  rw [hA, hB]
  have hdisj : ((W : Set (ℕ × ℕ × ℕ))).PairwiseDisjoint F := by
    intro a ha b hb hab
    change Disjoint (F a) (F b)
    rw [Finset.disjoint_left]
    intro y hya hyb
    have ha' := (Finset.mem_filter.mp hya).2
    have hb' := (Finset.mem_filter.mp hyb).2
    have h1 : a.1 = b.1 := ha'.2.2.1.symm.trans hb'.2.2.1
    have h5 : a.2.1 = b.2.1 := ha'.2.2.2.1.symm.trans hb'.2.2.2.1
    have h6 : a.2.2 = b.2.2 := ha'.2.2.2.2.symm.trans hb'.2.2.2.2
    exact hab (Prod.ext h1 (Prod.ext h5 h6))
  rw [Finset.card_biUnion hdisj]
  simp [W, S, F, Finset.sum_filter, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro w1 hw1
  apply Finset.sum_congr rfl
  intro w5 hw5
  apply Finset.sum_congr rfl
  intro w6 hw6
  by_cases hcondw : Y5WeightCondC3one C w3v w1 w5 w6
  · rw [if_pos hcondw, if_pos hcondw]
    have hw1pos : 1 ≤ w1 := (Finset.mem_Icc.mp hw1).1
    have hc3w : Nat.choose (count C 3) w3v = 1 := by
      have hw3le : w3v ≤ 1 := hcondw.1
      rw [h3]
      by_cases hz : w3v = 0
      · rw [hz]
        rfl
      · have hz' : w3v = 1 := by omega
        rw [hz']
        rfl
    have hcnt := count_words_htrue_weights_1356_w3 C htypes t hcol w1 w3v w5 w6 hw1pos
    -- hcnt : (F (w1, (w5, w6))).card = C(c1−1,w1−1)·C(c3,w3v)·C(c5,w5)·C(c6,w6)
    rw [show Nat.choose (count C 1 - 1) (w1 - 1) * Nat.choose (count C 5) w5 *
        Nat.choose (count C 6) w6 = Nat.choose (count C 1 - 1) (w1 - 1) * Nat.choose (count C 3) w3v *
          Nat.choose (count C 5) w5 * Nat.choose (count C 6) w6 by
        rw [hc3w]
        ring]
    simpa [F, and_comm, and_left_comm, and_assoc] using hcnt
  · rw [if_neg hcondw, if_neg hcondw]

/-- The w3 = 1 Y5 conditions equal the high-distance form (eq. of1). -/
lemma Y5WeightCond_c3one_high_iff {n : ℕ} (C : Code n) (w1 w5 w6 : ℕ) :
    Y5WeightCondC3one C 1 w1 w5 w6 ↔ Y5HighCondC3one C w1 w5 w6 := by
  constructor
  · intro h
    rcases h with ⟨_, h1, h2, h3⟩
    exact ⟨h1, by omega, by omega⟩
  · intro h
    rcases h with ⟨h1, h2, h3⟩
    exact ⟨by decide, h1, by omega, by omega⟩

/-- The w3 = 0 Y5 conditions equal the low-distance form (eq. of3). -/
lemma Y5WeightCond_c3one_low_iff {n : ℕ} (C : Code n) (w1 w5 w6 : ℕ) :
    Y5WeightCondC3one C 0 w1 w5 w6 ↔ Y5LowCondC3one C w1 w5 w6 := by
  constructor
  · intro h
    rcases h with ⟨_, h1, h2, h3⟩
    exact ⟨h1, by omega, by omega⟩
  · intro h
    rcases h with ⟨h1, h2, h3⟩
    exact ⟨by decide, h1, by omega, by omega⟩

/-- α⁵(n/2−1) for |3| = 1 as the binomial sum over the w3 = 1 Y5 region
(paper eq. of1). -/
lemma alpha5_c3one_eq_sum_high {n : ℕ} (C : Code n) (t : Fin n)
    (htypes : ∀ u : Fin n, colVal (C u) = 1 ∨ colVal (C u) = 3 ∨
      colVal (C u) = 5 ∨ colVal (C u) = 6)
    (hcol : C t = col1) (h3 : count C 3 = 1)
    (hpar36 : Even (count C 3) ↔ Even (count C 6))
    (hpar53 : Even (count C 5) ↔ Even (count C 3))
    (htotal : totalCounts C {1, 3, 5, 6} = n) (hodd1 : Odd (count C 1)) :
    alpha5 C t (n / 2 - 1) =
      ∑ w1 ∈ Finset.Icc 1 (count C 1),
        ∑ w5 ∈ Finset.Icc 0 (count C 5),
          ∑ w6 ∈ Finset.Icc 0 (count C 6),
            if Y5HighCondC3one C w1 w5 w6 then
              Nat.choose (count C 1 - 1) (w1 - 1) * Nat.choose (count C 5) w5 *
                Nat.choose (count C 6) w6
            else 0 := by
  have hdist : ∀ y : Word n, Y5 C t y → (dCode C y = n / 2 - 1 ↔ w_i C 3 y = 1) := by
    intro y hy
    have hd := (Y5_dist_c3one C t y htypes hcol h3 hpar36 hpar53 htotal hy).1
    have hn2 : 2 ≤ n := by
      rcases hodd1 with ⟨k1, hk1⟩
      have hodd3 : Odd (count C 3) := by rw [h3]; exact ⟨0, rfl⟩
      have hodd5 : Odd (count C 5) := by
        rw [← Nat.not_even_iff_odd]
        intro he5
        have hodd3' : ¬ Even (count C 3) := (Nat.not_even_iff_odd.mpr hodd3)
        exact hodd3' (hpar53.mp he5)
      have hodd6 : Odd (count C 6) := by
        rw [← Nat.not_even_iff_odd]
        intro he6
        have hodd3' : ¬ Even (count C 3) := (Nat.not_even_iff_odd.mpr hodd3)
        exact hodd3' (hpar36.mpr he6)
      rcases hodd5 with ⟨k5, hk5⟩
      rcases hodd6 with ⟨k6, hk6⟩
      have h4 : count C 1 + count C 3 + count C 5 + count C 6 = n := by
        calc
          count C 1 + count C 3 + count C 5 + count C 6
              = ∑ i ∈ ({1, 3, 5, 6} : Finset ℕ), count C i := by
                simp [Finset.sum_insert]
                omega
          _ = n := htotal
      rw [h3, hk1, hk5, hk6] at h4
      omega
    have hn2div : 1 ≤ n / 2 := by omega
    constructor
    · intro h
      omega
    · intro h
      omega
  have hcond : ∀ y : Word n, Y5 C t y → w_i C 3 y = 1 →
      Y5WeightCondC3one C 1 (w_i C 1 y) (w_i C 5 y) (w_i C 6 y) := by
    intro y hy hw3
    have hc := (Y5_iff_weights_c3one C t y htypes hcol h3 hpar36 hpar53).1 hy
    simpa [hw3] using hc.2
  have hcond' : ∀ y : Word n, y t = true → w_i C 3 y = 1 →
      Y5WeightCondC3one C 1 (w_i C 1 y) (w_i C 5 y) (w_i C 6 y) → Y5 C t y := by
    intro y hyt hw3 hc
    exact (Y5_iff_weights_c3one C t y htypes hcol h3 hpar36 hpar53).2 ⟨hyt, by simpa [hw3] using hc⟩
  rw [alpha5_c3one_eq_sum_aux C t (n / 2 - 1) 1 htypes hcol h3 hpar36 hpar53 htotal hdist hcond hcond']
  apply Finset.sum_congr rfl
  intro w1 hw1
  apply Finset.sum_congr rfl
  intro w5 hw5
  apply Finset.sum_congr rfl
  intro w6 hw6
  by_cases hc : Y5HighCondC3one C w1 w5 w6
  · rw [if_pos hc, if_pos ((Y5WeightCond_c3one_high_iff C w1 w5 w6).2 hc)]
  · rw [if_neg hc, if_neg]
    intro h
    exact hc ((Y5WeightCond_c3one_high_iff C w1 w5 w6).1 h)

/-- α⁵(n/2) for |3| = 1 as the binomial sum over the w3 = 0 Y5 region
(paper eq. of3). -/
lemma alpha5_c3one_eq_sum_low {n : ℕ} (C : Code n) (t : Fin n)
    (htypes : ∀ u : Fin n, colVal (C u) = 1 ∨ colVal (C u) = 3 ∨
      colVal (C u) = 5 ∨ colVal (C u) = 6)
    (hcol : C t = col1) (h3 : count C 3 = 1)
    (hpar36 : Even (count C 3) ↔ Even (count C 6))
    (hpar53 : Even (count C 5) ↔ Even (count C 3))
    (htotal : totalCounts C {1, 3, 5, 6} = n) :
    alpha5 C t (n / 2) =
      ∑ w1 ∈ Finset.Icc 1 (count C 1),
        ∑ w5 ∈ Finset.Icc 0 (count C 5),
          ∑ w6 ∈ Finset.Icc 0 (count C 6),
            if Y5LowCondC3one C w1 w5 w6 then
              Nat.choose (count C 1 - 1) (w1 - 1) * Nat.choose (count C 5) w5 *
                Nat.choose (count C 6) w6
            else 0 := by
  have hdist : ∀ y : Word n, Y5 C t y → (dCode C y = n / 2 ↔ w_i C 3 y = 0) := by
    intro y hy
    have hd := (Y5_dist_c3one C t y htypes hcol h3 hpar36 hpar53 htotal hy).1
    constructor
    · intro h
      omega
    · intro h
      omega
  have hcond : ∀ y : Word n, Y5 C t y → w_i C 3 y = 0 →
      Y5WeightCondC3one C 0 (w_i C 1 y) (w_i C 5 y) (w_i C 6 y) := by
    intro y hy hw3
    have hc := (Y5_iff_weights_c3one C t y htypes hcol h3 hpar36 hpar53).1 hy
    simpa [hw3] using hc.2
  have hcond' : ∀ y : Word n, y t = true → w_i C 3 y = 0 →
      Y5WeightCondC3one C 0 (w_i C 1 y) (w_i C 5 y) (w_i C 6 y) → Y5 C t y := by
    intro y hyt hw3 hc
    exact (Y5_iff_weights_c3one C t y htypes hcol h3 hpar36 hpar53).2 ⟨hyt, by simpa [hw3] using hc⟩
  rw [alpha5_c3one_eq_sum_aux C t (n / 2) 0 htypes hcol h3 hpar36 hpar53 htotal hdist hcond hcond']
  apply Finset.sum_congr rfl
  intro w1 hw1
  apply Finset.sum_congr rfl
  intro w5 hw5
  apply Finset.sum_congr rfl
  intro w6 hw6
  by_cases hc : Y5LowCondC3one C w1 w5 w6
  · rw [if_pos hc, if_pos ((Y5WeightCond_c3one_low_iff C w1 w5 w6).2 hc)]
  · rw [if_neg hc, if_neg]
    intro h
    exact hc ((Y5WeightCond_c3one_low_iff C w1 w5 w6).1 h)

/-- For odd |5|, C(|5|,r) ≤ C(|5|,(|5|+1)/2) (the middle binomial). -/
lemma odd_choose_le_middle_high {c5 r : ℕ} (hodd : Odd c5) :
    Nat.choose c5 r ≤ Nat.choose c5 ((c5 + 1) / 2) := by
  have hle := Nat.choose_le_middle r c5
  rcases hodd with ⟨k, hk⟩
  have hk' : c5 = 2 * k + 1 := by omega
  have h1 : (c5 + 1) / 2 = k + 1 := by rw [hk']; omega
  have h2 : c5 / 2 = k := by rw [hk']; omega
  have hsym := Nat.choose_symm_half k
  calc
    Nat.choose c5 r ≤ Nat.choose c5 (c5 / 2) := hle
    _ = Nat.choose c5 ((c5 + 1) / 2) := by
      rw [h1, h2, hk']
      exact hsym.symm

/-- For odd |5|, C(|5|,r) ≤ C(|5|,(|5|−1)/2) (the middle binomial). -/
lemma odd_choose_le_middle_low {c5 r : ℕ} (hodd : Odd c5) :
    Nat.choose c5 r ≤ Nat.choose c5 ((c5 - 1) / 2) := by
  have hle := Nat.choose_le_middle r c5
  rcases hodd with ⟨k, hk⟩
  have hk' : c5 = 2 * k + 1 := by omega
  have hdiv : c5 / 2 = (c5 - 1) / 2 := by rw [hk']; omega
  simpa [hdiv] using hle

/-- The high Y5 conditions force the eq:of2 region on (w1′, w6) with
w1′ = |1| − w1 + 1 (paper eq. 12 → eq. of2; direct algebra, no parity). -/
lemma Y5HighCond_c3one_imp_region {n : ℕ} (C : Code n) (w1 w5 w6 : ℕ)
    (hw1le : w1 ≤ count C 1) (hw6le : w6 ≤ count C 6)
    (hcond : Y5HighCondC3one C w1 w5 w6) :
    count C 6 + 1 ≤ 2 * w6 ∧
      2 * (count C 1 - w1 + 1) + 2 * w6 ≤ count C 1 + count C 6 := by
  rcases hcond with ⟨heq, hw6ge, hw5le⟩
  have hw5le' : w5 ≤ count C 5 := by omega
  have hZ1 : (w1 : ℤ) + (w5 : ℤ) + ((count C 6 : ℤ) - w6) =
      ((count C 1 : ℤ) - w1) + ((count C 5 : ℤ) - w5) + (w6 : ℤ) + 1 := by
    exact_mod_cast heq
  have hZ2 : 2 * (w6 : ℤ) ≤ 2 * (w1 : ℤ) + (count C 6 : ℤ) - count C 1 - 2 := by
    have hw5leZ : 2 * (w5 : ℤ) + 1 ≤ (count C 5 : ℤ) := by exact_mod_cast hw5le
    omega
  have hc1w1 : (((count C 1 - w1 + 1) : ℕ) : ℤ) = (count C 1 : ℤ) - (w1 : ℤ) + 1 := by
    rw [Nat.cast_add, Nat.cast_sub hw1le]
    norm_num
  have hZ3 : (2 : ℤ) * (((count C 1 - w1 + 1) : ℕ) : ℤ) + 2 * (w6 : ℤ) ≤
      (count C 1 : ℤ) + (count C 6 : ℤ) := by
    rw [hc1w1]
    omega
  exact ⟨hw6ge, by exact_mod_cast hZ3⟩

/-- The low Y5 conditions force the eq:of4 region on (w1′, w6) (paper
eq. 11 → eq. of4; direct algebra, no parity). -/
lemma Y5LowCond_c3one_imp_region {n : ℕ} (C : Code n) (w1 w5 w6 : ℕ)
    (hw1le : w1 ≤ count C 1) (hw6le : w6 ≤ count C 6)
    (hcond : Y5LowCondC3one C w1 w5 w6) :
    count C 6 + 3 ≤ 2 * w6 ∧
      2 * (count C 1 - w1 + 1) + 2 * w6 + 2 ≤ count C 1 + count C 6 := by
  rcases hcond with ⟨heq, hw6ge, hw5le⟩
  have hw5le' : w5 ≤ count C 5 := by omega
  have hZ1 : (w1 : ℤ) + (w5 : ℤ) + ((count C 6 : ℤ) - w6) =
      ((count C 1 : ℤ) - w1) + ((count C 5 : ℤ) - w5) + (w6 : ℤ) + 1 := by
    exact_mod_cast heq
  have hZ2 : 2 * (w6 : ℤ) ≤ 2 * (w1 : ℤ) + (count C 6 : ℤ) - count C 1 - 4 := by
    have hw5leZ : 2 * (w5 : ℤ) + 3 ≤ (count C 5 : ℤ) := by exact_mod_cast hw5le
    omega
  have hc1w1 : (((count C 1 - w1 + 1) : ℕ) : ℤ) = (count C 1 : ℤ) - (w1 : ℤ) + 1 := by
    rw [Nat.cast_add, Nat.cast_sub hw1le]
    norm_num
  have hZ3 : (2 : ℤ) * (((count C 1 - w1 + 1) : ℕ) : ℤ) + 2 * (w6 : ℤ) + 2 ≤
      (count C 1 : ℤ) + (count C 6 : ℤ) := by
    rw [hc1w1]
    omega
  exact ⟨hw6ge, by exact_mod_cast hZ3⟩

/-- The high Y5 equation determines w5 from (w1, w6). -/
lemma Y5HighCond_c3one_w5_unique {n : ℕ} (C : Code n) {w1 w5 w5' w6 : ℕ}
    (h1 : Y5HighCondC3one C w1 w5 w6) (h2 : Y5HighCondC3one C w1 w5' w6) :
    w5 = w5' := by
  rcases h1 with ⟨heq1, _, hw5le⟩
  rcases h2 with ⟨heq2, _, hw5le'⟩
  have hw5le1 : w5 ≤ count C 5 := by omega
  have hw5le2 : w5' ≤ count C 5 := by omega
  omega

/-- The low Y5 equation determines w5 from (w1, w6). -/
lemma Y5LowCond_c3one_w5_unique {n : ℕ} (C : Code n) {w1 w5 w5' w6 : ℕ}
    (h1 : Y5LowCondC3one C w1 w5 w6) (h2 : Y5LowCondC3one C w1 w5' w6) :
    w5 = w5' := by
  rcases h1 with ⟨heq1, _, hw5le⟩
  rcases h2 with ⟨heq2, _, hw5le'⟩
  have hw5le1 : w5 ≤ count C 5 := by omega
  have hw5le2 : w5' ≤ count C 5 := by omega
  omega

/-- For fixed (w1, w6), the high Y5 w5-sum is bounded by the eq:of2-region
indicator times C(|5|,(|5|+1)/2). -/
lemma Y5HighCond_c3one_inner_le {n : ℕ} (C : Code n) (w1 w6 : ℕ)
    (hw1le : w1 ≤ count C 1) (hw6le : w6 ≤ count C 6)
    (hodd5 : Odd (count C 5)) :
    (∑ w5 ∈ Finset.Icc 0 (count C 5),
        if Y5HighCondC3one C w1 w5 w6 then Nat.choose (count C 5) w5 else 0) ≤
      if count C 6 + 1 ≤ 2 * w6 ∧ 2 * (count C 1 - w1 + 1) + 2 * w6 ≤ count C 1 + count C 6 then
        Nat.choose (count C 5) ((count C 5 + 1) / 2)
      else 0 := by
  by_cases hregion : count C 6 + 1 ≤ 2 * w6 ∧ 2 * (count C 1 - w1 + 1) + 2 * w6 ≤ count C 1 + count C 6
  · rw [if_pos hregion]
    let s : Finset ℕ := Finset.Icc 0 (count C 5)
    let f : ℕ → ℕ := fun w5 => if Y5HighCondC3one C w1 w5 w6 then Nat.choose (count C 5) w5 else 0
    have hle_pointwise : ∀ w5 ∈ s.filter (fun w5 => Y5HighCondC3one C w1 w5 w6),
        f w5 ≤ Nat.choose (count C 5) ((count C 5 + 1) / 2) := by
      intro w5 hw5
      have hc : Y5HighCondC3one C w1 w5 w6 := (Finset.mem_filter.mp hw5).2
      have : f w5 = Nat.choose (count C 5) w5 := by simp [f, hc]
      rw [this]
      exact odd_choose_le_middle_high hodd5
    have hcard : (s.filter (fun w5 => Y5HighCondC3one C w1 w5 w6) |>.card) ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      have ha' := (Finset.mem_filter.mp ha).2
      have hb' := (Finset.mem_filter.mp hb).2
      exact (Y5HighCond_c3one_w5_unique C hb' ha').symm
    calc
      (∑ w5 ∈ s, f w5) =
          ∑ w5 ∈ s.filter (fun w5 => Y5HighCondC3one C w1 w5 w6), f w5 := by
        rw [← Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro w5 hw5
        have hc : Y5HighCondC3one C w1 w5 w6 := (Finset.mem_filter.mp hw5).2
        simp [f, hc]
      _ ≤ (s.filter (fun w5 => Y5HighCondC3one C w1 w5 w6) |>.card) *
            Nat.choose (count C 5) ((count C 5 + 1) / 2) := by
        simpa [nsmul_eq_mul] using
          Finset.sum_le_card_nsmul (s.filter (fun w5 => Y5HighCondC3one C w1 w5 w6)) f
            (Nat.choose (count C 5) ((count C 5 + 1) / 2)) hle_pointwise
      _ ≤ 1 * Nat.choose (count C 5) ((count C 5 + 1) / 2) := by
        exact Nat.mul_le_mul_right _ hcard
      _ = Nat.choose (count C 5) ((count C 5 + 1) / 2) := by simp
  · rw [if_neg hregion]
    have hsum0 : (∑ w5 ∈ Finset.Icc 0 (count C 5),
        if Y5HighCondC3one C w1 w5 w6 then Nat.choose (count C 5) w5 else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro w5 hw5
      by_cases hc : Y5HighCondC3one C w1 w5 w6
      · rw [if_pos hc]
        have hreg := Y5HighCond_c3one_imp_region C w1 w5 w6 hw1le hw6le hc
        exact False.elim (hregion ⟨hreg.1, hreg.2⟩)
      · rw [if_neg hc]
    exact le_of_eq hsum0

/-- For fixed (w1, w6), the low Y5 w5-sum is bounded by the eq:of4-region
indicator times C(|5|,(|5|−1)/2). -/
lemma Y5LowCond_c3one_inner_le {n : ℕ} (C : Code n) (w1 w6 : ℕ)
    (hw1le : w1 ≤ count C 1) (hw6le : w6 ≤ count C 6)
    (hodd5 : Odd (count C 5)) :
    (∑ w5 ∈ Finset.Icc 0 (count C 5),
        if Y5LowCondC3one C w1 w5 w6 then Nat.choose (count C 5) w5 else 0) ≤
      if count C 6 + 3 ≤ 2 * w6 ∧ 2 * (count C 1 - w1 + 1) + 2 * w6 + 2 ≤ count C 1 + count C 6 then
        Nat.choose (count C 5) ((count C 5 - 1) / 2)
      else 0 := by
  by_cases hregion : count C 6 + 3 ≤ 2 * w6 ∧ 2 * (count C 1 - w1 + 1) + 2 * w6 + 2 ≤ count C 1 + count C 6
  · rw [if_pos hregion]
    let s : Finset ℕ := Finset.Icc 0 (count C 5)
    let f : ℕ → ℕ := fun w5 => if Y5LowCondC3one C w1 w5 w6 then Nat.choose (count C 5) w5 else 0
    have hle_pointwise : ∀ w5 ∈ s.filter (fun w5 => Y5LowCondC3one C w1 w5 w6),
        f w5 ≤ Nat.choose (count C 5) ((count C 5 - 1) / 2) := by
      intro w5 hw5
      have hc : Y5LowCondC3one C w1 w5 w6 := (Finset.mem_filter.mp hw5).2
      have : f w5 = Nat.choose (count C 5) w5 := by simp [f, hc]
      rw [this]
      exact odd_choose_le_middle_low hodd5
    have hcard : (s.filter (fun w5 => Y5LowCondC3one C w1 w5 w6) |>.card) ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      have ha' := (Finset.mem_filter.mp ha).2
      have hb' := (Finset.mem_filter.mp hb).2
      exact (Y5LowCond_c3one_w5_unique C hb' ha').symm
    calc
      (∑ w5 ∈ s, f w5) =
          ∑ w5 ∈ s.filter (fun w5 => Y5LowCondC3one C w1 w5 w6), f w5 := by
        rw [← Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro w5 hw5
        have hc : Y5LowCondC3one C w1 w5 w6 := (Finset.mem_filter.mp hw5).2
        simp [f, hc]
      _ ≤ (s.filter (fun w5 => Y5LowCondC3one C w1 w5 w6) |>.card) *
            Nat.choose (count C 5) ((count C 5 - 1) / 2) := by
        simpa [nsmul_eq_mul] using
          Finset.sum_le_card_nsmul (s.filter (fun w5 => Y5LowCondC3one C w1 w5 w6)) f
            (Nat.choose (count C 5) ((count C 5 - 1) / 2)) hle_pointwise
      _ ≤ 1 * Nat.choose (count C 5) ((count C 5 - 1) / 2) := by
        exact Nat.mul_le_mul_right _ hcard
      _ = Nat.choose (count C 5) ((count C 5 - 1) / 2) := by simp
  · rw [if_neg hregion]
    have hsum0 : (∑ w5 ∈ Finset.Icc 0 (count C 5),
        if Y5LowCondC3one C w1 w5 w6 then Nat.choose (count C 5) w5 else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro w5 hw5
      by_cases hc : Y5LowCondC3one C w1 w5 w6
      · rw [if_pos hc]
        have hreg := Y5LowCond_c3one_imp_region C w1 w5 w6 hw1le hw6le hc
        exact False.elim (hregion ⟨hreg.1, hreg.2⟩)
      · rw [if_neg hc]
    exact le_of_eq hsum0

/-- α⁵(n/2−1) ≤ the eq:of2 binomial sum (w1′ = |1|−w1+1 reindexed to w1):
the Y5 equation collapses the w5-sum and `odd_choose_le_middle_high` bounds
each binomial. -/
lemma alpha5_c3one_le_of2 {n : ℕ} (C : Code n) (t : Fin n)
    (htypes : ∀ u : Fin n, colVal (C u) = 1 ∨ colVal (C u) = 3 ∨
      colVal (C u) = 5 ∨ colVal (C u) = 6)
    (hcol : C t = col1) (h3 : count C 3 = 1)
    (hpar36 : Even (count C 3) ↔ Even (count C 6))
    (hpar53 : Even (count C 5) ↔ Even (count C 3))
    (htotal : totalCounts C {1, 3, 5, 6} = n) (hodd1 : Odd (count C 1))
    (hodd5 : Odd (count C 5)) :
    alpha5 C t (n / 2 - 1) ≤
      ∑ w1 ∈ Finset.Icc 1 (count C 1),
        ∑ w6 ∈ Finset.Icc 0 (count C 6),
          if count C 6 + 1 ≤ 2 * w6 ∧ 2 * w1 + 2 * w6 ≤ count C 1 + count C 6 then
            Nat.choose (count C 1 - 1) (w1 - 1) * Nat.choose (count C 5) ((count C 5 + 1) / 2) *
              Nat.choose (count C 6) w6
          else 0 := by
  rw [alpha5_c3one_eq_sum_high C t htypes hcol h3 hpar36 hpar53 htotal hodd1]
  let s1 : Finset ℕ := Finset.Icc 1 (count C 1)
  let s5 : Finset ℕ := Finset.Icc 0 (count C 5)
  let s6 : Finset ℕ := Finset.Icc 0 (count C 6)
  calc
    (∑ w1 ∈ s1, ∑ w5 ∈ s5, ∑ w6 ∈ s6,
        if Y5HighCondC3one C w1 w5 w6 then
          Nat.choose (count C 1 - 1) (w1 - 1) * Nat.choose (count C 5) w5 *
            Nat.choose (count C 6) w6
        else 0)
        ≤ ∑ w1 ∈ s1, ∑ w6 ∈ s6,
            if count C 6 + 1 ≤ 2 * w6 ∧ 2 * (count C 1 - w1 + 1) + 2 * w6 ≤ count C 1 + count C 6 then
              Nat.choose (count C 1 - 1) (w1 - 1) * Nat.choose (count C 5) ((count C 5 + 1) / 2) *
                Nat.choose (count C 6) w6
            else 0 := by
      apply Finset.sum_le_sum
      intro w1 hw1
      rw [Finset.sum_comm]
      apply Finset.sum_le_sum
      intro w6 hw6
      have hw1pos : 1 ≤ w1 := (Finset.mem_Icc.mp hw1).1
      have hw1le : w1 ≤ count C 1 := (Finset.mem_Icc.mp hw1).2
      have hw6le : w6 ≤ count C 6 := (Finset.mem_Icc.mp hw6).2
      have hin := Y5HighCond_c3one_inner_le C w1 w6 hw1le hw6le hodd5
      have hfac : (∑ w5 ∈ s5, if Y5HighCondC3one C w1 w5 w6 then
            Nat.choose (count C 1 - 1) (w1 - 1) * Nat.choose (count C 5) w5 *
              Nat.choose (count C 6) w6
            else 0) =
          Nat.choose (count C 1 - 1) (w1 - 1) * Nat.choose (count C 6) w6 *
            (∑ w5 ∈ s5, if Y5HighCondC3one C w1 w5 w6 then Nat.choose (count C 5) w5 else 0) := by
        calc
          (∑ w5 ∈ s5, if Y5HighCondC3one C w1 w5 w6 then
              Nat.choose (count C 1 - 1) (w1 - 1) * Nat.choose (count C 5) w5 *
                Nat.choose (count C 6) w6
              else 0)
              = ∑ w5 ∈ s5, (Nat.choose (count C 1 - 1) (w1 - 1) * Nat.choose (count C 6) w6) *
                  (if Y5HighCondC3one C w1 w5 w6 then Nat.choose (count C 5) w5 else 0) := by
                apply Finset.sum_congr rfl
                intro w5 hw5
                by_cases hc : Y5HighCondC3one C w1 w5 w6
                · rw [if_pos hc, if_pos hc]
                  ring
                · rw [if_neg hc, if_neg hc]
                  simp
          _ = Nat.choose (count C 1 - 1) (w1 - 1) * Nat.choose (count C 6) w6 *
                (∑ w5 ∈ s5, if Y5HighCondC3one C w1 w5 w6 then Nat.choose (count C 5) w5 else 0) := by
                rw [Finset.mul_sum]
      calc
        (∑ w5 ∈ s5, if Y5HighCondC3one C w1 w5 w6 then
            Nat.choose (count C 1 - 1) (w1 - 1) * Nat.choose (count C 5) w5 *
              Nat.choose (count C 6) w6
            else 0)
            = Nat.choose (count C 1 - 1) (w1 - 1) * Nat.choose (count C 6) w6 *
                (∑ w5 ∈ s5, if Y5HighCondC3one C w1 w5 w6 then Nat.choose (count C 5) w5 else 0) := hfac
        _ ≤ Nat.choose (count C 1 - 1) (w1 - 1) * Nat.choose (count C 6) w6 *
              (if count C 6 + 1 ≤ 2 * w6 ∧ 2 * (count C 1 - w1 + 1) + 2 * w6 ≤ count C 1 + count C 6 then
                Nat.choose (count C 5) ((count C 5 + 1) / 2)
               else 0) := by
              exact Nat.mul_le_mul_left (Nat.choose (count C 1 - 1) (w1 - 1) * Nat.choose (count C 6) w6) hin
        _ = if count C 6 + 1 ≤ 2 * w6 ∧ 2 * (count C 1 - w1 + 1) + 2 * w6 ≤ count C 1 + count C 6 then
                Nat.choose (count C 1 - 1) (w1 - 1) * Nat.choose (count C 5) ((count C 5 + 1) / 2) *
                  Nat.choose (count C 6) w6
              else 0 := by
              by_cases hc : count C 6 + 1 ≤ 2 * w6 ∧ 2 * (count C 1 - w1 + 1) + 2 * w6 ≤ count C 1 + count C 6
              · rw [if_pos hc, if_pos hc]
                ring
              · rw [if_neg hc, if_neg hc]
                simp
    _ = ∑ w1 ∈ s1, ∑ w6 ∈ s6,
            if count C 6 + 1 ≤ 2 * w6 ∧ 2 * w1 + 2 * w6 ≤ count C 1 + count C 6 then
              Nat.choose (count C 1 - 1) (w1 - 1) * Nat.choose (count C 5) ((count C 5 + 1) / 2) *
                Nat.choose (count C 6) w6
            else 0 := by
      apply Finset.sum_bij (fun w1 _ => count C 1 - w1 + 1)
      · intro w1 hw1
        have hw1pos : 1 ≤ w1 := (Finset.mem_Icc.mp hw1).1
        have hw1le : w1 ≤ count C 1 := (Finset.mem_Icc.mp hw1).2
        exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      · intro a ha b hb h
        have ha2 : a ≤ count C 1 := (Finset.mem_Icc.mp ha).2
        have hb2 : b ≤ count C 1 := (Finset.mem_Icc.mp hb).2
        omega
      · intro b hb
        refine ⟨count C 1 - b + 1, ?_, ?_⟩
        · have hb2 : b ≤ count C 1 := (Finset.mem_Icc.mp hb).2
          have hb1 : 1 ≤ b := (Finset.mem_Icc.mp hb).1
          exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
        · have hb1 : 1 ≤ b := (Finset.mem_Icc.mp hb).1
          have hb2 : b ≤ count C 1 := (Finset.mem_Icc.mp hb).2
          omega
      · intro w1 hw1
        apply Finset.sum_congr rfl
        intro w6 hw6
        have hw1pos : 1 ≤ w1 := (Finset.mem_Icc.mp hw1).1
        have hw1le : w1 ≤ count C 1 := (Finset.mem_Icc.mp hw1).2
        have hchoose : Nat.choose (count C 1 - 1) (count C 1 - w1) =
            Nat.choose (count C 1 - 1) (w1 - 1) := by
          have hk : w1 - 1 ≤ count C 1 - 1 := by omega
          have hsym := Nat.choose_symm hk
          have harg : (count C 1 - 1) - (w1 - 1) = count C 1 - w1 := by omega
          simpa [harg] using hsym
        by_cases hc : count C 6 + 1 ≤ 2 * w6 ∧ 2 * (count C 1 - w1 + 1) + 2 * w6 ≤ count C 1 + count C 6
        · rw [if_pos hc, if_pos hc]
          have harg' : (count C 1 - w1 + 1) - 1 = count C 1 - w1 := by omega
          rw [harg', hchoose]
        · rw [if_neg hc, if_neg hc]

/-- α⁵(n/2) ≤ the eq:of4 binomial sum (w1′ = |1|−w1+1 reindexed to w1). -/
lemma alpha5_c3one_le_of4 {n : ℕ} (C : Code n) (t : Fin n)
    (htypes : ∀ u : Fin n, colVal (C u) = 1 ∨ colVal (C u) = 3 ∨
      colVal (C u) = 5 ∨ colVal (C u) = 6)
    (hcol : C t = col1) (h3 : count C 3 = 1)
    (hpar36 : Even (count C 3) ↔ Even (count C 6))
    (hpar53 : Even (count C 5) ↔ Even (count C 3))
    (htotal : totalCounts C {1, 3, 5, 6} = n)
    (hodd5 : Odd (count C 5)) :
    alpha5 C t (n / 2) ≤
      ∑ w1 ∈ Finset.Icc 1 (count C 1),
        ∑ w6 ∈ Finset.Icc 0 (count C 6),
          if count C 6 + 3 ≤ 2 * w6 ∧ 2 * w1 + 2 * w6 + 2 ≤ count C 1 + count C 6 then
            Nat.choose (count C 1 - 1) (w1 - 1) * Nat.choose (count C 5) ((count C 5 - 1) / 2) *
              Nat.choose (count C 6) w6
          else 0 := by
  rw [alpha5_c3one_eq_sum_low C t htypes hcol h3 hpar36 hpar53 htotal]
  let s1 : Finset ℕ := Finset.Icc 1 (count C 1)
  let s5 : Finset ℕ := Finset.Icc 0 (count C 5)
  let s6 : Finset ℕ := Finset.Icc 0 (count C 6)
  calc
    (∑ w1 ∈ s1, ∑ w5 ∈ s5, ∑ w6 ∈ s6,
        if Y5LowCondC3one C w1 w5 w6 then
          Nat.choose (count C 1 - 1) (w1 - 1) * Nat.choose (count C 5) w5 *
            Nat.choose (count C 6) w6
        else 0)
        ≤ ∑ w1 ∈ s1, ∑ w6 ∈ s6,
            if count C 6 + 3 ≤ 2 * w6 ∧ 2 * (count C 1 - w1 + 1) + 2 * w6 + 2 ≤ count C 1 + count C 6 then
              Nat.choose (count C 1 - 1) (w1 - 1) * Nat.choose (count C 5) ((count C 5 - 1) / 2) *
                Nat.choose (count C 6) w6
            else 0 := by
      apply Finset.sum_le_sum
      intro w1 hw1
      rw [Finset.sum_comm]
      apply Finset.sum_le_sum
      intro w6 hw6
      have hw1pos : 1 ≤ w1 := (Finset.mem_Icc.mp hw1).1
      have hw1le : w1 ≤ count C 1 := (Finset.mem_Icc.mp hw1).2
      have hw6le : w6 ≤ count C 6 := (Finset.mem_Icc.mp hw6).2
      have hin := Y5LowCond_c3one_inner_le C w1 w6 hw1le hw6le hodd5
      have hfac : (∑ w5 ∈ s5, if Y5LowCondC3one C w1 w5 w6 then
            Nat.choose (count C 1 - 1) (w1 - 1) * Nat.choose (count C 5) w5 *
              Nat.choose (count C 6) w6
            else 0) =
          Nat.choose (count C 1 - 1) (w1 - 1) * Nat.choose (count C 6) w6 *
            (∑ w5 ∈ s5, if Y5LowCondC3one C w1 w5 w6 then Nat.choose (count C 5) w5 else 0) := by
        calc
          (∑ w5 ∈ s5, if Y5LowCondC3one C w1 w5 w6 then
              Nat.choose (count C 1 - 1) (w1 - 1) * Nat.choose (count C 5) w5 *
                Nat.choose (count C 6) w6
              else 0)
              = ∑ w5 ∈ s5, (Nat.choose (count C 1 - 1) (w1 - 1) * Nat.choose (count C 6) w6) *
                  (if Y5LowCondC3one C w1 w5 w6 then Nat.choose (count C 5) w5 else 0) := by
                apply Finset.sum_congr rfl
                intro w5 hw5
                by_cases hc : Y5LowCondC3one C w1 w5 w6
                · rw [if_pos hc, if_pos hc]
                  ring
                · rw [if_neg hc, if_neg hc]
                  simp
          _ = Nat.choose (count C 1 - 1) (w1 - 1) * Nat.choose (count C 6) w6 *
                (∑ w5 ∈ s5, if Y5LowCondC3one C w1 w5 w6 then Nat.choose (count C 5) w5 else 0) := by
                rw [Finset.mul_sum]
      calc
        (∑ w5 ∈ s5, if Y5LowCondC3one C w1 w5 w6 then
            Nat.choose (count C 1 - 1) (w1 - 1) * Nat.choose (count C 5) w5 *
              Nat.choose (count C 6) w6
            else 0)
            = Nat.choose (count C 1 - 1) (w1 - 1) * Nat.choose (count C 6) w6 *
                (∑ w5 ∈ s5, if Y5LowCondC3one C w1 w5 w6 then Nat.choose (count C 5) w5 else 0) := hfac
        _ ≤ Nat.choose (count C 1 - 1) (w1 - 1) * Nat.choose (count C 6) w6 *
              (if count C 6 + 3 ≤ 2 * w6 ∧ 2 * (count C 1 - w1 + 1) + 2 * w6 + 2 ≤ count C 1 + count C 6 then
                Nat.choose (count C 5) ((count C 5 - 1) / 2)
               else 0) := by
              exact Nat.mul_le_mul_left (Nat.choose (count C 1 - 1) (w1 - 1) * Nat.choose (count C 6) w6) hin
        _ = if count C 6 + 3 ≤ 2 * w6 ∧ 2 * (count C 1 - w1 + 1) + 2 * w6 + 2 ≤ count C 1 + count C 6 then
                Nat.choose (count C 1 - 1) (w1 - 1) * Nat.choose (count C 5) ((count C 5 - 1) / 2) *
                  Nat.choose (count C 6) w6
              else 0 := by
              by_cases hc : count C 6 + 3 ≤ 2 * w6 ∧ 2 * (count C 1 - w1 + 1) + 2 * w6 + 2 ≤ count C 1 + count C 6
              · rw [if_pos hc, if_pos hc]
                ring
              · rw [if_neg hc, if_neg hc]
                simp
    _ = ∑ w1 ∈ s1, ∑ w6 ∈ s6,
            if count C 6 + 3 ≤ 2 * w6 ∧ 2 * w1 + 2 * w6 + 2 ≤ count C 1 + count C 6 then
              Nat.choose (count C 1 - 1) (w1 - 1) * Nat.choose (count C 5) ((count C 5 - 1) / 2) *
                Nat.choose (count C 6) w6
            else 0 := by
      apply Finset.sum_bij (fun w1 _ => count C 1 - w1 + 1)
      · intro w1 hw1
        have hw1pos : 1 ≤ w1 := (Finset.mem_Icc.mp hw1).1
        have hw1le : w1 ≤ count C 1 := (Finset.mem_Icc.mp hw1).2
        exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      · intro a ha b hb h
        have ha2 : a ≤ count C 1 := (Finset.mem_Icc.mp ha).2
        have hb2 : b ≤ count C 1 := (Finset.mem_Icc.mp hb).2
        omega
      · intro b hb
        refine ⟨count C 1 - b + 1, ?_, ?_⟩
        · have hb2 : b ≤ count C 1 := (Finset.mem_Icc.mp hb).2
          have hb1 : 1 ≤ b := (Finset.mem_Icc.mp hb).1
          exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
        · have hb1 : 1 ≤ b := (Finset.mem_Icc.mp hb).1
          have hb2 : b ≤ count C 1 := (Finset.mem_Icc.mp hb).2
          omega
      · intro w1 hw1
        apply Finset.sum_congr rfl
        intro w6 hw6
        have hw1pos : 1 ≤ w1 := (Finset.mem_Icc.mp hw1).1
        have hw1le : w1 ≤ count C 1 := (Finset.mem_Icc.mp hw1).2
        have hchoose : Nat.choose (count C 1 - 1) (count C 1 - w1) =
            Nat.choose (count C 1 - 1) (w1 - 1) := by
          have hk : w1 - 1 ≤ count C 1 - 1 := by omega
          have hsym := Nat.choose_symm hk
          have harg : (count C 1 - 1) - (w1 - 1) = count C 1 - w1 := by omega
          simpa [harg] using hsym
        by_cases hc : count C 6 + 3 ≤ 2 * w6 ∧ 2 * (count C 1 - w1 + 1) + 2 * w6 + 2 ≤ count C 1 + count C 6
        · rw [if_pos hc, if_pos hc]
          have harg' : (count C 1 - w1 + 1) - 1 = count C 1 - w1 := by omega
          rw [harg', hchoose]
        · rw [if_neg hc, if_neg hc]


/-- A word with y_t = 1, w3 = 1, 2w5 = |5|+1, 2w6 ≥ |6|−1 and
2w1+|6|+1 ≤ 2w6+|1| is a Y3 word of the B-branch with dCode ≤ n/2
(paper eq. 3yd1–3yd4; eq. sa_5). -/
lemma Y3B_word_c3one_high {n : ℕ} (C : Code n) (t : Fin n) (y : Word n)
    (htypes : ∀ u : Fin n, colVal (C u) = 1 ∨ colVal (C u) = 3 ∨
      colVal (C u) = 5 ∨ colVal (C u) = 6)
    (hcol : C t = col1) (h3 : count C 3 = 1)
    (htotal : totalCounts C {1, 3, 5, 6} = n)
    (hyt : y t = true)
    (hw3 : w_i C 3 y = 1)
    (hw1pos : 1 ≤ w_i C 1 y)
    (hw5 : 2 * w_i C 5 y = count C 5 + 1)
    (hw6ge : count C 6 ≤ 2 * w_i C 6 y + 1)
    (hw16 : 2 * w_i C 1 y + count C 6 + 1 ≤ 2 * w_i C 6 y + count C 1) :
    Y3 C t y ∧ 1 ≤ dCode C y ∧ dCode C y ≤ n / 2 := by
  have hw1le : w_i C 1 y ≤ count C 1 := w_i_le_count C 1 y
  have hw5le : w_i C 5 y ≤ count C 5 := w_i_le_count C 5 y
  have hw6le : w_i C 6 y ≤ count C 6 := w_i_le_count C 6 y
  have hd0 : dRow C 0 y = w_i C 1 y + w_i C 3 y + w_i C 5 y + w_i C 6 y :=
    dRow0_of_type1356 C htypes y
  have hd1 : dRow C 1 y = w_i C 1 y + w_i C 3 y + (count C 5 - w_i C 5 y) +
      (count C 6 - w_i C 6 y) := dRow1_of_type1356 C htypes y
  have hd2' : dRow C 2 y = w_i C 1 y + (1 - w_i C 3 y) + w_i C 5 y +
      (count C 6 - w_i C 6 y) := by
    rw [dRow2_of_type1356 C htypes y, h3]
  have hd3 : dRow C 3 y = (count C 1 - w_i C 1 y) + (1 - w_i C 3 y) +
      (count C 5 - w_i C 5 y) + w_i C 6 y := by
    rw [dRow3_of_type1356 C htypes y, h3]
  have hd1le0 : dRow C 1 y ≤ dRow C 0 y := by
    rw [hd0, hd1]
    omega
  have hd2eq1 : dRow C 2 y = dRow C 1 y := by
    rw [hd2', hd1]
    omega
  have hd3ge1 : dRow C 1 y ≤ dRow C 3 y := by
    rw [hd1, hd3]
    omega
  have hy3 : Y3 C t y := (Y3_iff_col1 C t y hcol).2 ⟨hyt, by
      rw [Nat.min_eq_right hd1le0]
      exact hd3ge1, by
      rw [Nat.min_eq_right hd1le0]
      exact hd2eq1⟩
  have hdCode : dCode C y = dRow C 2 y := by
    unfold dCode
    rw [show hammingDist (row0 C) y = dRow C 0 y by rfl]
    rw [show hammingDist (row1 C) y = dRow C 1 y by rfl]
    rw [show hammingDist (row2 C) y = dRow C 2 y by rfl]
    rw [show hammingDist (row3 C) y = dRow C 3 y by rfl]
    have hd2le3 : dRow C 2 y ≤ dRow C 3 y := by rw [hd2eq1]; exact hd3ge1
    have hd2le1 : dRow C 2 y ≤ dRow C 1 y := le_of_eq hd2eq1
    have hd2le0 : dRow C 2 y ≤ dRow C 0 y := le_trans hd2le1 hd1le0
    rw [Nat.min_eq_left hd2le3, Nat.min_eq_right hd2le1, Nat.min_eq_right hd2le0]
  have hd2le : dRow C 2 y ≤ n / 2 := by
    have hsum : count C 1 + count C 5 + count C 6 = n - 1 := by
      have h4 : count C 1 + count C 3 + count C 5 + count C 6 = n := by
        calc
          count C 1 + count C 3 + count C 5 + count C 6
              = ∑ i ∈ ({1, 3, 5, 6} : Finset ℕ), count C i := by
                simp [Finset.sum_insert]
                omega
          _ = n := htotal
      rw [h3] at h4
      omega
    have h2d2 : 2 * dRow C 2 y ≤ n - 1 := by
      rw [hd2', hw3]
      omega
    have hd2le' : dRow C 2 y ≤ (n - 1) / 2 := by
      exact (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mpr (by simpa [mul_comm] using h2d2)
    exact le_trans hd2le' (Nat.div_le_div_right (by omega : n - 1 ≤ n))
  have hd2ge1 : 1 ≤ dRow C 2 y := by
    rw [hd2', hw3]
    omega
  exact ⟨hy3, by rw [hdCode]; exact hd2ge1, by rw [hdCode]; exact hd2le⟩

/-- A word with y_t = 1, w3 = 0, 2w5+1 = |5|, 2w6 ≥ |6|+1 and
2w1+|6| ≤ 2w6+|1|+1 is a Y3 word of the B-branch with dCode ≤ n/2+1
(paper eq. 3yd1–3yd4; eq. sa_6). -/
lemma Y3B_word_c3one_low {n : ℕ} (C : Code n) (t : Fin n) (y : Word n)
    (htypes : ∀ u : Fin n, colVal (C u) = 1 ∨ colVal (C u) = 3 ∨
      colVal (C u) = 5 ∨ colVal (C u) = 6)
    (hcol : C t = col1) (h3 : count C 3 = 1)
    (htotal : totalCounts C {1, 3, 5, 6} = n)
    (hyt : y t = true)
    (hw3 : w_i C 3 y = 0)
    (hw1pos : 1 ≤ w_i C 1 y)
    (hw5 : 2 * w_i C 5 y + 1 = count C 5)
    (hw6ge : count C 6 + 1 ≤ 2 * w_i C 6 y)
    (hw16 : 2 * w_i C 1 y + count C 6 ≤ 2 * w_i C 6 y + count C 1 + 1) :
    Y3 C t y ∧ 1 ≤ dCode C y ∧ dCode C y ≤ n / 2 + 1 := by
  have hw1le : w_i C 1 y ≤ count C 1 := w_i_le_count C 1 y
  have hw5le : w_i C 5 y ≤ count C 5 := w_i_le_count C 5 y
  have hw6le : w_i C 6 y ≤ count C 6 := w_i_le_count C 6 y
  have hd0 : dRow C 0 y = w_i C 1 y + w_i C 3 y + w_i C 5 y + w_i C 6 y :=
    dRow0_of_type1356 C htypes y
  have hd1 : dRow C 1 y = w_i C 1 y + w_i C 3 y + (count C 5 - w_i C 5 y) +
      (count C 6 - w_i C 6 y) := dRow1_of_type1356 C htypes y
  have hd2' : dRow C 2 y = w_i C 1 y + (1 - w_i C 3 y) + w_i C 5 y +
      (count C 6 - w_i C 6 y) := by
    rw [dRow2_of_type1356 C htypes y, h3]
  have hd3 : dRow C 3 y = (count C 1 - w_i C 1 y) + (1 - w_i C 3 y) +
      (count C 5 - w_i C 5 y) + w_i C 6 y := by
    rw [dRow3_of_type1356 C htypes y, h3]
  have hd1le0 : dRow C 1 y ≤ dRow C 0 y := by
    rw [hd0, hd1]
    omega
  have hd2eq1 : dRow C 2 y = dRow C 1 y := by
    rw [hd2', hd1]
    omega
  have hd3ge1 : dRow C 1 y ≤ dRow C 3 y := by
    rw [hd1, hd3]
    omega
  have hy3 : Y3 C t y := (Y3_iff_col1 C t y hcol).2 ⟨hyt, by
      rw [Nat.min_eq_right hd1le0]
      exact hd3ge1, by
      rw [Nat.min_eq_right hd1le0]
      exact hd2eq1⟩
  have hdCode : dCode C y = dRow C 2 y := by
    unfold dCode
    rw [show hammingDist (row0 C) y = dRow C 0 y by rfl]
    rw [show hammingDist (row1 C) y = dRow C 1 y by rfl]
    rw [show hammingDist (row2 C) y = dRow C 2 y by rfl]
    rw [show hammingDist (row3 C) y = dRow C 3 y by rfl]
    have hd2le3 : dRow C 2 y ≤ dRow C 3 y := by rw [hd2eq1]; exact hd3ge1
    have hd2le1 : dRow C 2 y ≤ dRow C 1 y := le_of_eq hd2eq1
    have hd2le0 : dRow C 2 y ≤ dRow C 0 y := le_trans hd2le1 hd1le0
    rw [Nat.min_eq_left hd2le3, Nat.min_eq_right hd2le1, Nat.min_eq_right hd2le0]
  have hd2le : dRow C 2 y ≤ n / 2 + 1 := by
    have hsum : count C 1 + count C 5 + count C 6 = n - 1 := by
      have h4 : count C 1 + count C 3 + count C 5 + count C 6 = n := by
        calc
          count C 1 + count C 3 + count C 5 + count C 6
              = ∑ i ∈ ({1, 3, 5, 6} : Finset ℕ), count C i := by
                simp [Finset.sum_insert]
                omega
          _ = n := htotal
      rw [h3] at h4
      omega
    have h2d2 : 2 * dRow C 2 y ≤ n + 1 := by
      rw [hd2', hw3]
      omega
    have hd2le' : dRow C 2 y ≤ (n + 1) / 2 := by
      exact (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mpr (by simpa [mul_comm] using h2d2)
    have hle : (n + 1) / 2 ≤ n / 2 + 1 := by omega
    exact le_trans hd2le' hle
  have hd2ge1 : 1 ≤ dRow C 2 y := by
    rw [hd2', hw3]
    omega
  exact ⟨hy3, by rw [hdCode]; exact hd2ge1, by rw [hdCode]; exact hd2le⟩

/-- Σ_{i=1..d} α³(i) ≥ the eq:sa_5 binomial sum (the w3 = 1 Y3-B region
words all have dCode ≤ n/2 ≤ d). -/
lemma class1_alpha3_cum_ge_sa5 {n : ℕ} (C : Code n) (t : Fin n) (d : ℕ)
    (htypes : ∀ u : Fin n, colVal (C u) = 1 ∨ colVal (C u) = 3 ∨
      colVal (C u) = 5 ∨ colVal (C u) = 6)
    (hcol : C t = col1) (h3 : count C 3 = 1)
    (_hpar35 : Even (count C 5) ↔ Even (count C 6))
    (_hpar36 : Even (count C 3) ↔ Even (count C 6))
    (_hpar53 : Even (count C 5) ↔ Even (count C 3))
    (htotal : totalCounts C {1, 3, 5, 6} = n) (hodd5 : Odd (count C 5))
    (hd : n / 2 ≤ d) :
    (∑ i ∈ Finset.Icc 1 d, alpha3 C t i) ≥
      ∑ w1 ∈ Finset.Icc 1 (count C 1),
        ∑ w6 ∈ Finset.Icc 0 (count C 6),
          if count C 6 ≤ 2 * w6 + 1 ∧ 2 * w1 + count C 6 + 1 ≤ 2 * w6 + count C 1 then
            Nat.choose (count C 1 - 1) (w1 - 1) * Nat.choose (count C 5) ((count C 5 + 1) / 2) *
              Nat.choose (count C 6) w6
          else 0 := by
  rw [alpha3_cumulative_card C t d]
  let F : ℕ × ℕ → Finset (Word n) := fun w =>
    (Finset.univ : Finset (Word n)).filter
      fun y => y t = true ∧ w_i C 3 y = 1 ∧ w_i C 1 y = w.1 ∧
        w_i C 5 y = (count C 5 + 1) / 2 ∧ w_i C 6 y = w.2
  let S : Finset (ℕ × ℕ) :=
    (Finset.Icc 1 (count C 1)) ×ˢ (Finset.Icc 0 (count C 6))
  let W : Finset (ℕ × ℕ) := S.filter fun w =>
    count C 6 ≤ 2 * w.2 + 1 ∧ 2 * w.1 + count C 6 + 1 ≤ 2 * w.2 + count C 1
  have hsub : W.biUnion F ⊆
      Finset.univ.filter (fun y : Word n => Y3 C t y ∧ 1 ≤ dCode C y ∧ dCode C y ≤ d) := by
    intro y hy
    rcases Finset.mem_biUnion.mp hy with ⟨w, hw, hyw⟩
    have hcond := (Finset.mem_filter.mp hw).2
    have hywf := (Finset.mem_filter.mp hyw).2
    have hyt : y t = true := hywf.1
    have hw3 : w_i C 3 y = 1 := hywf.2.1
    have hw1 : w_i C 1 y = w.1 := hywf.2.2.1
    have hw5 : w_i C 5 y = (count C 5 + 1) / 2 := hywf.2.2.2.1
    have hw6 : w_i C 6 y = w.2 := hywf.2.2.2.2
    have hw1pos : 1 ≤ w_i C 1 y := by
      have hw1mem : w.1 ∈ Finset.Icc 1 (count C 1) := (Finset.mem_product.mp (Finset.mem_filter.mp hw).1).1
      have hw1ge : 1 ≤ w.1 := (Finset.mem_Icc.mp hw1mem).1
      omega
    have hw5d : 2 * w_i C 5 y = count C 5 + 1 := by
      rcases hodd5 with ⟨k, hk⟩
      have hk' : count C 5 = 2 * k + 1 := by omega
      have hdiv : (count C 5 + 1) / 2 = k + 1 := by rw [hk']; omega
      rw [hw5, hdiv, hk']
      omega
    have hcond' : count C 6 ≤ 2 * w_i C 6 y + 1 ∧
        2 * w_i C 1 y + count C 6 + 1 ≤ 2 * w_i C 6 y + count C 1 := by
      simpa [← hw1, ← hw6] using hcond
    have hb := Y3B_word_c3one_high C t y htypes hcol h3 htotal hyt hw3 hw1pos hw5d hcond'.1 hcond'.2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ y, ⟨hb.1, hb.2.1, le_trans hb.2.2 (by omega : n / 2 ≤ d)⟩⟩
  have hdisj : ((W : Set (ℕ × ℕ))).PairwiseDisjoint F := by
    intro a ha b hb hab
    change Disjoint (F a) (F b)
    rw [Finset.disjoint_left]
    intro y hya hyb
    have ha' := (Finset.mem_filter.mp hya).2
    have hb' := (Finset.mem_filter.mp hyb).2
    have h1 : a.1 = b.1 := ha'.2.2.1.symm.trans hb'.2.2.1
    have h6 : a.2 = b.2 := ha'.2.2.2.2.symm.trans hb'.2.2.2.2
    exact hab (Prod.ext h1 h6)
  calc
    (∑ w1 ∈ Finset.Icc 1 (count C 1), ∑ w6 ∈ Finset.Icc 0 (count C 6),
        if count C 6 ≤ 2 * w6 + 1 ∧ 2 * w1 + count C 6 + 1 ≤ 2 * w6 + count C 1 then
          Nat.choose (count C 1 - 1) (w1 - 1) * Nat.choose (count C 5) ((count C 5 + 1) / 2) *
            Nat.choose (count C 6) w6
        else 0)
        = (W.biUnion F).card := by
          rw [Finset.card_biUnion hdisj]
          simp [W, S, F, Finset.sum_filter, Finset.sum_product]
          apply Finset.sum_congr rfl
          intro w1 hw1
          apply Finset.sum_congr rfl
          intro w6 hw6
          by_cases hc : count C 6 ≤ 2 * w6 + 1 ∧ 2 * w1 + count C 6 < 2 * w6 + count C 1
          · have hw1pos : 1 ≤ w1 := (Finset.mem_Icc.mp hw1).1
            have hc3w : Nat.choose (count C 3) 1 = 1 := by rw [h3]; rfl
            have hcnt := count_words_htrue_weights_1356_w3 C htypes t hcol w1 1 ((count C 5 + 1) / 2) w6 hw1pos
            have hcnt' : (F (w1, w6)).card =
                Nat.choose (count C 1 - 1) (w1 - 1) * Nat.choose (count C 3) 1 *
                  Nat.choose (count C 5) ((count C 5 + 1) / 2) * Nat.choose (count C 6) w6 := by
              simpa [F, and_comm, and_left_comm, and_assoc] using hcnt
            have hgoal : Nat.choose (count C 1 - 1) (w1 - 1) * Nat.choose (count C 5) ((count C 5 + 1) / 2) *
                  Nat.choose (count C 6) w6 = (F (w1, w6)).card := by
              rw [hc3w] at hcnt'
              simpa using hcnt'.symm
            simpa [hc] using hgoal
          · simp [hc]
      _ ≤ (Finset.univ.filter fun y : Word n => Y3 C t y ∧ 1 ≤ dCode C y ∧ dCode C y ≤ d).card := by
            exact Finset.card_le_card hsub

/-- Σ_{i=1..d} α³(i) ≥ the eq:sa_6 binomial sum (the w3 = 0 Y3-B region
words all have dCode ≤ n/2+1 ≤ d). -/
lemma class1_alpha3_cum_ge_sa6 {n : ℕ} (C : Code n) (t : Fin n) (d : ℕ)
    (htypes : ∀ u : Fin n, colVal (C u) = 1 ∨ colVal (C u) = 3 ∨
      colVal (C u) = 5 ∨ colVal (C u) = 6)
    (hcol : C t = col1) (h3 : count C 3 = 1)
    (_hpar35 : Even (count C 5) ↔ Even (count C 6))
    (_hpar36 : Even (count C 3) ↔ Even (count C 6))
    (_hpar53 : Even (count C 5) ↔ Even (count C 3))
    (htotal : totalCounts C {1, 3, 5, 6} = n) (hodd5 : Odd (count C 5))
    (hd : n / 2 + 1 ≤ d) :
    (∑ i ∈ Finset.Icc 1 d, alpha3 C t i) ≥
      ∑ w1 ∈ Finset.Icc 1 (count C 1),
        ∑ w6 ∈ Finset.Icc 0 (count C 6),
          if count C 6 + 1 ≤ 2 * w6 ∧ 2 * w1 + count C 6 ≤ 2 * w6 + count C 1 + 1 then
            Nat.choose (count C 1 - 1) (w1 - 1) * Nat.choose (count C 5) ((count C 5 - 1) / 2) *
              Nat.choose (count C 6) w6
          else 0 := by
  rw [alpha3_cumulative_card C t d]
  let F : ℕ × ℕ → Finset (Word n) := fun w =>
    (Finset.univ : Finset (Word n)).filter
      fun y => y t = true ∧ w_i C 3 y = 0 ∧ w_i C 1 y = w.1 ∧
        w_i C 5 y = (count C 5 - 1) / 2 ∧ w_i C 6 y = w.2
  let S : Finset (ℕ × ℕ) :=
    (Finset.Icc 1 (count C 1)) ×ˢ (Finset.Icc 0 (count C 6))
  let W : Finset (ℕ × ℕ) := S.filter fun w =>
    count C 6 + 1 ≤ 2 * w.2 ∧ 2 * w.1 + count C 6 ≤ 2 * w.2 + count C 1 + 1
  have hsub : W.biUnion F ⊆
      Finset.univ.filter (fun y : Word n => Y3 C t y ∧ 1 ≤ dCode C y ∧ dCode C y ≤ d) := by
    intro y hy
    rcases Finset.mem_biUnion.mp hy with ⟨w, hw, hyw⟩
    have hcond := (Finset.mem_filter.mp hw).2
    have hywf := (Finset.mem_filter.mp hyw).2
    have hyt : y t = true := hywf.1
    have hw3 : w_i C 3 y = 0 := hywf.2.1
    have hw1 : w_i C 1 y = w.1 := hywf.2.2.1
    have hw5 : w_i C 5 y = (count C 5 - 1) / 2 := hywf.2.2.2.1
    have hw6 : w_i C 6 y = w.2 := hywf.2.2.2.2
    have hw1pos : 1 ≤ w_i C 1 y := by
      have hw1mem : w.1 ∈ Finset.Icc 1 (count C 1) := (Finset.mem_product.mp (Finset.mem_filter.mp hw).1).1
      have hw1ge : 1 ≤ w.1 := (Finset.mem_Icc.mp hw1mem).1
      omega
    have hw5d : 2 * w_i C 5 y + 1 = count C 5 := by
      rcases hodd5 with ⟨k, hk⟩
      have hk' : count C 5 = 2 * k + 1 := by omega
      have hdiv : (count C 5 - 1) / 2 = k := by rw [hk']; omega
      rw [hw5, hdiv, hk']
    have hcond' : count C 6 + 1 ≤ 2 * w_i C 6 y ∧
        2 * w_i C 1 y + count C 6 ≤ 2 * w_i C 6 y + count C 1 + 1 := by
      simpa [← hw1, ← hw6] using hcond
    have hb := Y3B_word_c3one_low C t y htypes hcol h3 htotal hyt hw3 hw1pos hw5d hcond'.1 hcond'.2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ y, ⟨hb.1, hb.2.1, le_trans hb.2.2 (by omega : n / 2 + 1 ≤ d)⟩⟩
  have hdisj : ((W : Set (ℕ × ℕ))).PairwiseDisjoint F := by
    intro a ha b hb hab
    change Disjoint (F a) (F b)
    rw [Finset.disjoint_left]
    intro y hya hyb
    have ha' := (Finset.mem_filter.mp hya).2
    have hb' := (Finset.mem_filter.mp hyb).2
    have h1 : a.1 = b.1 := ha'.2.2.1.symm.trans hb'.2.2.1
    have h6 : a.2 = b.2 := ha'.2.2.2.2.symm.trans hb'.2.2.2.2
    exact hab (Prod.ext h1 h6)
  calc
    (∑ w1 ∈ Finset.Icc 1 (count C 1), ∑ w6 ∈ Finset.Icc 0 (count C 6),
        if count C 6 + 1 ≤ 2 * w6 ∧ 2 * w1 + count C 6 ≤ 2 * w6 + count C 1 + 1 then
          Nat.choose (count C 1 - 1) (w1 - 1) * Nat.choose (count C 5) ((count C 5 - 1) / 2) *
            Nat.choose (count C 6) w6
        else 0)
        = (W.biUnion F).card := by
          rw [Finset.card_biUnion hdisj]
          simp [W, S, F, Finset.sum_filter, Finset.sum_product]
          apply Finset.sum_congr rfl
          intro w1 hw1
          apply Finset.sum_congr rfl
          intro w6 hw6
          by_cases hc : count C 6 < 2 * w6 ∧ 2 * w1 + count C 6 ≤ 2 * w6 + count C 1 + 1
          · have hw1pos : 1 ≤ w1 := (Finset.mem_Icc.mp hw1).1
            have hc3w : Nat.choose (count C 3) 0 = 1 := by rw [h3]; rfl
            have hcnt := count_words_htrue_weights_1356_w3 C htypes t hcol w1 0 ((count C 5 - 1) / 2) w6 hw1pos
            have hcnt' : (F (w1, w6)).card =
                Nat.choose (count C 1 - 1) (w1 - 1) * Nat.choose (count C 3) 0 *
                  Nat.choose (count C 5) ((count C 5 - 1) / 2) * Nat.choose (count C 6) w6 := by
              simpa [F, and_comm, and_left_comm, and_assoc] using hcnt
            have hgoal : Nat.choose (count C 1 - 1) (w1 - 1) * Nat.choose (count C 5) ((count C 5 - 1) / 2) *
                  Nat.choose (count C 6) w6 = (F (w1, w6)).card := by
              rw [hc3w] at hcnt'
              simpa using hcnt'.symm
            simpa [hc] using hgoal
          · simp [hc]
      _ ≤ (Finset.univ.filter fun y : Word n => Y3 C t y ∧ 1 ≤ dCode C y ∧ dCode C y ≤ d).card := by
            exact Finset.card_le_card hsub

/-- The eq:of2 region is contained in the eq:sa_5 region (`2w6 ≥ |6|+1` and
`2w1+2w6 ≤ |1|+|6|` imply `2w1+|6|+1 ≤ 2w6+|1|`; this is the comparison
behind eq. of5), so the binomial sum is no larger. -/
lemma class1_of2_le_sa5 {n : ℕ} (C : Code n) :
    (∑ w1 ∈ Finset.Icc 1 (count C 1), ∑ w6 ∈ Finset.Icc 0 (count C 6),
        if count C 6 + 1 ≤ 2 * w6 ∧ 2 * w1 + 2 * w6 ≤ count C 1 + count C 6 then
          Nat.choose (count C 1 - 1) (w1 - 1) * Nat.choose (count C 5) ((count C 5 + 1) / 2) *
            Nat.choose (count C 6) w6
        else 0) ≤
      (∑ w1 ∈ Finset.Icc 1 (count C 1), ∑ w6 ∈ Finset.Icc 0 (count C 6),
        if count C 6 ≤ 2 * w6 + 1 ∧ 2 * w1 + count C 6 + 1 ≤ 2 * w6 + count C 1 then
          Nat.choose (count C 1 - 1) (w1 - 1) * Nat.choose (count C 5) ((count C 5 + 1) / 2) *
            Nat.choose (count C 6) w6
        else 0) := by
  apply Finset.sum_le_sum
  intro w1 hw1
  apply Finset.sum_le_sum
  intro w6 hw6
  by_cases h : count C 6 + 1 ≤ 2 * w6 ∧ 2 * w1 + 2 * w6 ≤ count C 1 + count C 6
  · rw [if_pos h]
    have h1 : count C 6 ≤ 2 * w6 + 1 := by omega
    have h2 : 2 * w1 + count C 6 + 1 ≤ 2 * w6 + count C 1 := by
      have hZ : (2 : ℤ) * (w1 : ℤ) + (count C 6 : ℤ) + 1 ≤
          2 * (w6 : ℤ) + (count C 1 : ℤ) := by
        have h1Z : (count C 6 : ℤ) + 1 ≤ 2 * (w6 : ℤ) := by exact_mod_cast h.1
        have h2Z : (2 : ℤ) * (w1 : ℤ) + 2 * (w6 : ℤ) ≤
            (count C 1 : ℤ) + count C 6 := by exact_mod_cast h.2
        omega
      exact_mod_cast hZ
    rw [if_pos ⟨h1, h2⟩]
  · rw [if_neg h]
    exact Nat.zero_le _

/-- The eq:of4 region is contained in the eq:sa_6 region (`2w6 ≥ |6|+3` and
`2w1+2w6+2 ≤ |1|+|6|` imply `2w1+|6| ≤ 2w6+|1|+1`; this is the comparison
behind eq. of6), so the binomial sum is no larger. -/
lemma class1_of4_le_sa6 {n : ℕ} (C : Code n) :
    (∑ w1 ∈ Finset.Icc 1 (count C 1), ∑ w6 ∈ Finset.Icc 0 (count C 6),
        if count C 6 + 3 ≤ 2 * w6 ∧ 2 * w1 + 2 * w6 + 2 ≤ count C 1 + count C 6 then
          Nat.choose (count C 1 - 1) (w1 - 1) * Nat.choose (count C 5) ((count C 5 - 1) / 2) *
            Nat.choose (count C 6) w6
        else 0) ≤
      (∑ w1 ∈ Finset.Icc 1 (count C 1), ∑ w6 ∈ Finset.Icc 0 (count C 6),
        if count C 6 + 1 ≤ 2 * w6 ∧ 2 * w1 + count C 6 ≤ 2 * w6 + count C 1 + 1 then
          Nat.choose (count C 1 - 1) (w1 - 1) * Nat.choose (count C 5) ((count C 5 - 1) / 2) *
            Nat.choose (count C 6) w6
        else 0) := by
  apply Finset.sum_le_sum
  intro w1 hw1
  apply Finset.sum_le_sum
  intro w6 hw6
  by_cases h : count C 6 + 3 ≤ 2 * w6 ∧ 2 * w1 + 2 * w6 + 2 ≤ count C 1 + count C 6
  · rw [if_pos h]
    have h1 : count C 6 + 1 ≤ 2 * w6 := by omega
    have h2 : 2 * w1 + count C 6 ≤ 2 * w6 + count C 1 + 1 := by
      have hZ : (2 : ℤ) * (w1 : ℤ) + (count C 6 : ℤ) ≤
          2 * (w6 : ℤ) + (count C 1 : ℤ) + 1 := by
        have h1Z : (count C 6 : ℤ) + 3 ≤ 2 * (w6 : ℤ) := by exact_mod_cast h.1
        have h2Z : (2 : ℤ) * (w1 : ℤ) + 2 * (w6 : ℤ) + 2 ≤
            (count C 1 : ℤ) + count C 6 := by exact_mod_cast h.2
        omega
      exact_mod_cast hZ
    rw [if_pos ⟨h1, h2⟩]
  · rw [if_neg h]
    exact Nat.zero_le _

/-- Σ_{i=1..d} α³(i) ≥ the sum of the eq:sa_5 and eq:sa_6 binomial sums:
the w₃ = 1 and w₃ = 0 region words are disjoint subsets of the Y3 words with
dCode ≤ d, so their counts add and stay below the cumulative count. -/
lemma class1_alpha3_cum_ge_sa5_add_sa6 {n : ℕ} (C : Code n) (t : Fin n) (d : ℕ)
    (htypes : ∀ u : Fin n, colVal (C u) = 1 ∨ colVal (C u) = 3 ∨
      colVal (C u) = 5 ∨ colVal (C u) = 6)
    (hcol : C t = col1) (h3 : count C 3 = 1)
    (_hpar35 : Even (count C 5) ↔ Even (count C 6))
    (_hpar36 : Even (count C 3) ↔ Even (count C 6))
    (_hpar53 : Even (count C 5) ↔ Even (count C 3))
    (htotal : totalCounts C {1, 3, 5, 6} = n) (hodd5 : Odd (count C 5))
    (hd : n / 2 + 1 ≤ d) :
    (∑ w1 ∈ Finset.Icc 1 (count C 1), ∑ w6 ∈ Finset.Icc 0 (count C 6),
        if count C 6 ≤ 2 * w6 + 1 ∧ 2 * w1 + count C 6 + 1 ≤ 2 * w6 + count C 1 then
          Nat.choose (count C 1 - 1) (w1 - 1) * Nat.choose (count C 5) ((count C 5 + 1) / 2) *
            Nat.choose (count C 6) w6
        else 0) +
      (∑ w1 ∈ Finset.Icc 1 (count C 1), ∑ w6 ∈ Finset.Icc 0 (count C 6),
        if count C 6 + 1 ≤ 2 * w6 ∧ 2 * w1 + count C 6 ≤ 2 * w6 + count C 1 + 1 then
          Nat.choose (count C 1 - 1) (w1 - 1) * Nat.choose (count C 5) ((count C 5 - 1) / 2) *
            Nat.choose (count C 6) w6
        else 0) ≤
      (∑ i ∈ Finset.Icc 1 d, alpha3 C t i) := by
  rw [alpha3_cumulative_card C t d]
  let F5 : ℕ × ℕ → Finset (Word n) := fun w =>
    (Finset.univ : Finset (Word n)).filter
      fun y => y t = true ∧ w_i C 3 y = 1 ∧ w_i C 1 y = w.1 ∧
        w_i C 5 y = (count C 5 + 1) / 2 ∧ w_i C 6 y = w.2
  let F6 : ℕ × ℕ → Finset (Word n) := fun w =>
    (Finset.univ : Finset (Word n)).filter
      fun y => y t = true ∧ w_i C 3 y = 0 ∧ w_i C 1 y = w.1 ∧
        w_i C 5 y = (count C 5 - 1) / 2 ∧ w_i C 6 y = w.2
  let S : Finset (ℕ × ℕ) :=
    (Finset.Icc 1 (count C 1)) ×ˢ (Finset.Icc 0 (count C 6))
  let W5 : Finset (ℕ × ℕ) := S.filter fun w =>
    count C 6 ≤ 2 * w.2 + 1 ∧ 2 * w.1 + count C 6 + 1 ≤ 2 * w.2 + count C 1
  let W6 : Finset (ℕ × ℕ) := S.filter fun w =>
    count C 6 + 1 ≤ 2 * w.2 ∧ 2 * w.1 + count C 6 ≤ 2 * w.2 + count C 1 + 1
  let T : Finset (Word n) := Finset.univ.filter
    fun y : Word n => Y3 C t y ∧ 1 ≤ dCode C y ∧ dCode C y ≤ d
  have hsub5 : W5.biUnion F5 ⊆ T := by
    intro y hy
    rcases Finset.mem_biUnion.mp hy with ⟨w, hw, hyw⟩
    have hcond := (Finset.mem_filter.mp hw).2
    have hywf := (Finset.mem_filter.mp hyw).2
    have hyt : y t = true := hywf.1
    have hw3 : w_i C 3 y = 1 := hywf.2.1
    have hw1 : w_i C 1 y = w.1 := hywf.2.2.1
    have hw5 : w_i C 5 y = (count C 5 + 1) / 2 := hywf.2.2.2.1
    have hw6 : w_i C 6 y = w.2 := hywf.2.2.2.2
    have hw1pos : 1 ≤ w_i C 1 y := by
      have hw1mem : w.1 ∈ Finset.Icc 1 (count C 1) := (Finset.mem_product.mp (Finset.mem_filter.mp hw).1).1
      have hw1ge : 1 ≤ w.1 := (Finset.mem_Icc.mp hw1mem).1
      omega
    have hw5d : 2 * w_i C 5 y = count C 5 + 1 := by
      rcases hodd5 with ⟨k, hk⟩
      have hk' : count C 5 = 2 * k + 1 := by omega
      have hdiv : (count C 5 + 1) / 2 = k + 1 := by rw [hk']; omega
      rw [hw5, hdiv, hk']
      omega
    have hcond' : count C 6 ≤ 2 * w_i C 6 y + 1 ∧
        2 * w_i C 1 y + count C 6 + 1 ≤ 2 * w_i C 6 y + count C 1 := by
      simpa [← hw1, ← hw6] using hcond
    have hb := Y3B_word_c3one_high C t y htypes hcol h3 htotal hyt hw3 hw1pos hw5d hcond'.1 hcond'.2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ y, ⟨hb.1, hb.2.1, le_trans hb.2.2 (by omega : n / 2 ≤ d)⟩⟩
  have hsub6 : W6.biUnion F6 ⊆ T := by
    intro y hy
    rcases Finset.mem_biUnion.mp hy with ⟨w, hw, hyw⟩
    have hcond := (Finset.mem_filter.mp hw).2
    have hywf := (Finset.mem_filter.mp hyw).2
    have hyt : y t = true := hywf.1
    have hw3 : w_i C 3 y = 0 := hywf.2.1
    have hw1 : w_i C 1 y = w.1 := hywf.2.2.1
    have hw5 : w_i C 5 y = (count C 5 - 1) / 2 := hywf.2.2.2.1
    have hw6 : w_i C 6 y = w.2 := hywf.2.2.2.2
    have hw1pos : 1 ≤ w_i C 1 y := by
      have hw1mem : w.1 ∈ Finset.Icc 1 (count C 1) := (Finset.mem_product.mp (Finset.mem_filter.mp hw).1).1
      have hw1ge : 1 ≤ w.1 := (Finset.mem_Icc.mp hw1mem).1
      omega
    have hw5d : 2 * w_i C 5 y + 1 = count C 5 := by
      rcases hodd5 with ⟨k, hk⟩
      have hk' : count C 5 = 2 * k + 1 := by omega
      have hdiv : (count C 5 - 1) / 2 = k := by rw [hk']; omega
      rw [hw5, hdiv, hk']
    have hcond' : count C 6 + 1 ≤ 2 * w_i C 6 y ∧
        2 * w_i C 1 y + count C 6 ≤ 2 * w_i C 6 y + count C 1 + 1 := by
      simpa [← hw1, ← hw6] using hcond
    have hb := Y3B_word_c3one_low C t y htypes hcol h3 htotal hyt hw3 hw1pos hw5d hcond'.1 hcond'.2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ y, ⟨hb.1, hb.2.1, le_trans hb.2.2 (by omega : n / 2 + 1 ≤ d)⟩⟩
  have hdisj5 : ((W5 : Set (ℕ × ℕ))).PairwiseDisjoint F5 := by
    intro a ha b hb hab
    change Disjoint (F5 a) (F5 b)
    rw [Finset.disjoint_left]
    intro y hya hyb
    have ha' := (Finset.mem_filter.mp hya).2
    have hb' := (Finset.mem_filter.mp hyb).2
    have h1 : a.1 = b.1 := ha'.2.2.1.symm.trans hb'.2.2.1
    have h6 : a.2 = b.2 := ha'.2.2.2.2.symm.trans hb'.2.2.2.2
    exact hab (Prod.ext h1 h6)
  have hdisj6 : ((W6 : Set (ℕ × ℕ))).PairwiseDisjoint F6 := by
    intro a ha b hb hab
    change Disjoint (F6 a) (F6 b)
    rw [Finset.disjoint_left]
    intro y hya hyb
    have ha' := (Finset.mem_filter.mp hya).2
    have hb' := (Finset.mem_filter.mp hyb).2
    have h1 : a.1 = b.1 := ha'.2.2.1.symm.trans hb'.2.2.1
    have h6 : a.2 = b.2 := ha'.2.2.2.2.symm.trans hb'.2.2.2.2
    exact hab (Prod.ext h1 h6)
  have hdisj56 : Disjoint (W5.biUnion F5) (W6.biUnion F6) := by
    rw [Finset.disjoint_left]
    intro y hy5 hy6
    rcases Finset.mem_biUnion.mp hy5 with ⟨a, ha, hya⟩
    rcases Finset.mem_biUnion.mp hy6 with ⟨b, hb, hyb⟩
    have ha' := (Finset.mem_filter.mp hya).2
    have hb' := (Finset.mem_filter.mp hyb).2
    have hw3a : w_i C 3 y = 1 := ha'.2.1
    have hw3b : w_i C 3 y = 0 := hb'.2.1
    omega
  have hcard5 : (∑ w1 ∈ Finset.Icc 1 (count C 1), ∑ w6 ∈ Finset.Icc 0 (count C 6),
        if count C 6 ≤ 2 * w6 + 1 ∧ 2 * w1 + count C 6 + 1 ≤ 2 * w6 + count C 1 then
          Nat.choose (count C 1 - 1) (w1 - 1) * Nat.choose (count C 5) ((count C 5 + 1) / 2) *
            Nat.choose (count C 6) w6
        else 0) = (W5.biUnion F5).card := by
    rw [Finset.card_biUnion hdisj5]
    simp [W5, S, F5, Finset.sum_filter, Finset.sum_product]
    apply Finset.sum_congr rfl
    intro w1 hw1
    apply Finset.sum_congr rfl
    intro w6 hw6
    by_cases hc : count C 6 ≤ 2 * w6 + 1 ∧ 2 * w1 + count C 6 < 2 * w6 + count C 1
    · have hw1pos : 1 ≤ w1 := (Finset.mem_Icc.mp hw1).1
      have hc3w : Nat.choose (count C 3) 1 = 1 := by rw [h3]; rfl
      have hcnt := count_words_htrue_weights_1356_w3 C htypes t hcol w1 1 ((count C 5 + 1) / 2) w6 hw1pos
      have hcnt' : (F5 (w1, w6)).card =
          Nat.choose (count C 1 - 1) (w1 - 1) * Nat.choose (count C 3) 1 *
            Nat.choose (count C 5) ((count C 5 + 1) / 2) * Nat.choose (count C 6) w6 := by
        simpa [F5, and_comm, and_left_comm, and_assoc] using hcnt
      have hgoal : Nat.choose (count C 1 - 1) (w1 - 1) * Nat.choose (count C 5) ((count C 5 + 1) / 2) *
            Nat.choose (count C 6) w6 = (F5 (w1, w6)).card := by
        rw [hc3w] at hcnt'
        simpa using hcnt'.symm
      simpa [hc] using hgoal
    · simp [hc]
  have hcard6 : (∑ w1 ∈ Finset.Icc 1 (count C 1), ∑ w6 ∈ Finset.Icc 0 (count C 6),
        if count C 6 + 1 ≤ 2 * w6 ∧ 2 * w1 + count C 6 ≤ 2 * w6 + count C 1 + 1 then
          Nat.choose (count C 1 - 1) (w1 - 1) * Nat.choose (count C 5) ((count C 5 - 1) / 2) *
            Nat.choose (count C 6) w6
        else 0) = (W6.biUnion F6).card := by
    rw [Finset.card_biUnion hdisj6]
    simp [W6, S, F6, Finset.sum_filter, Finset.sum_product]
    apply Finset.sum_congr rfl
    intro w1 hw1
    apply Finset.sum_congr rfl
    intro w6 hw6
    by_cases hc : count C 6 < 2 * w6 ∧ 2 * w1 + count C 6 ≤ 2 * w6 + count C 1 + 1
    · have hw1pos : 1 ≤ w1 := (Finset.mem_Icc.mp hw1).1
      have hc3w : Nat.choose (count C 3) 0 = 1 := by rw [h3]; rfl
      have hcnt := count_words_htrue_weights_1356_w3 C htypes t hcol w1 0 ((count C 5 - 1) / 2) w6 hw1pos
      have hcnt' : (F6 (w1, w6)).card =
          Nat.choose (count C 1 - 1) (w1 - 1) * Nat.choose (count C 3) 0 *
            Nat.choose (count C 5) ((count C 5 - 1) / 2) * Nat.choose (count C 6) w6 := by
        simpa [F6, and_comm, and_left_comm, and_assoc] using hcnt
      have hgoal : Nat.choose (count C 1 - 1) (w1 - 1) * Nat.choose (count C 5) ((count C 5 - 1) / 2) *
            Nat.choose (count C 6) w6 = (F6 (w1, w6)).card := by
        rw [hc3w] at hcnt'
        simpa using hcnt'.symm
      simpa [hc] using hgoal
    · simp [hc]
  calc
    (∑ w1 ∈ Finset.Icc 1 (count C 1), ∑ w6 ∈ Finset.Icc 0 (count C 6),
        if count C 6 ≤ 2 * w6 + 1 ∧ 2 * w1 + count C 6 + 1 ≤ 2 * w6 + count C 1 then
          Nat.choose (count C 1 - 1) (w1 - 1) * Nat.choose (count C 5) ((count C 5 + 1) / 2) *
            Nat.choose (count C 6) w6
        else 0) +
      (∑ w1 ∈ Finset.Icc 1 (count C 1), ∑ w6 ∈ Finset.Icc 0 (count C 6),
        if count C 6 + 1 ≤ 2 * w6 ∧ 2 * w1 + count C 6 ≤ 2 * w6 + count C 1 + 1 then
          Nat.choose (count C 1 - 1) (w1 - 1) * Nat.choose (count C 5) ((count C 5 - 1) / 2) *
            Nat.choose (count C 6) w6
        else 0)
        = (W5.biUnion F5).card + (W6.biUnion F6).card := by rw [hcard5, hcard6]
    _ = ((W5.biUnion F5) ∪ (W6.biUnion F6)).card := by
          rw [Finset.card_union_of_disjoint hdisj56]
    _ ≤ T.card := by
          exact Finset.card_le_card (Finset.union_subset hsub5 hsub6)

/-- With |3| = 1, Ψ_d ≥ 0 for all d (thm:301 Class-I-b): below n/2−1 the
α⁵ sum vanishes (eq. 5yc1), at d = n/2 the eq. of5 comparison applies, and
above it the eq. of5 + eq. of6 comparisons apply. -/
lemma class1_psi_nonneg_c3one {n : ℕ} (C : Code n) (t : Fin n) (d : ℕ) (hd : 1 ≤ d)
    (htypes : ∀ u : Fin n, colVal (C u) = 1 ∨ colVal (C u) = 3 ∨
      colVal (C u) = 5 ∨ colVal (C u) = 6)
    (hcol : C t = col1) (h3 : count C 3 = 1)
    (hpar35 : Even (count C 5) ↔ Even (count C 6))
    (hpar36 : Even (count C 3) ↔ Even (count C 6))
    (hpar53 : Even (count C 5) ↔ Even (count C 3))
    (htotal : totalCounts C {1, 3, 5, 6} = n) (hodd1 : Odd (count C 1))
    (hodd5 : Odd (count C 5)) :
    Psi C t d ≥ 0 := by
  have hodd3 : Odd (count C 3) := by rw [h3]; exact ⟨0, rfl⟩
  have hodd6 : Odd (count C 6) := by
    rw [← Nat.not_even_iff_odd]
    intro he6
    have hodd3' : ¬ Even (count C 3) := (Nat.not_even_iff_odd.mpr hodd3)
    exact hodd3' (hpar36.mpr he6)
  have hn4 : 4 ≤ n := by
    have hc1ge : 1 ≤ count C 1 := by rcases hodd1 with ⟨k, hk⟩; omega
    have hc3ge : 1 ≤ count C 3 := by rw [h3]
    have hc5ge : 1 ≤ count C 5 := by rcases hodd5 with ⟨k, hk⟩; omega
    have hc6ge : 1 ≤ count C 6 := by rcases hodd6 with ⟨k, hk⟩; omega
    have hsum : count C 1 + count C 3 + count C 5 + count C 6 = n := by
      calc
        count C 1 + count C 3 + count C 5 + count C 6
            = ∑ i ∈ ({1, 3, 5, 6} : Finset ℕ), count C i := by
              simp [Finset.sum_insert]
              omega
        _ = n := htotal
    omega
  by_cases hlow : d ≤ n / 2 - 1
  · unfold Psi
    have hsum5 : (∑ i ∈ Finset.Icc 0 (d - 1), alpha5 C t i) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hile : i ≤ d - 1 := (Finset.mem_Icc.mp hi).2
      have hne1 : i ≠ n / 2 - 1 := by omega
      have hne2 : i ≠ n / 2 := by omega
      exact class1_alpha5_eq_zero_c3one C t i htypes hcol h3 hpar36 hpar53 htotal ⟨hne1, hne2⟩
    have h5z : (∑ i ∈ Finset.Icc 0 (d - 1), (alpha5 C t i : ℤ)) = 0 := by
      exact_mod_cast hsum5
    rw [h5z]
    simp
    exact_mod_cast (Nat.zero_le (∑ i ∈ Finset.Icc 1 d, alpha3 C t i))
  · have hdge : n / 2 ≤ d := by omega
    by_cases hmid : d = n / 2
    · have hsum5 : (∑ i ∈ Finset.Icc 0 (d - 1), alpha5 C t i) =
          alpha5 C t (n / 2 - 1) := by
        rw [hmid]
        refine Finset.sum_eq_single (a := n / 2 - 1) ?_ ?_
        · intro i hi hne
          have hile : i ≤ n / 2 - 1 := (Finset.mem_Icc.mp hi).2
          have hne2 : i ≠ n / 2 := by omega
          exact class1_alpha5_eq_zero_c3one C t i htypes hcol h3 hpar36 hpar53 htotal ⟨hne, hne2⟩
        · intro hnotmem
          have hmem : n / 2 - 1 ∈ Finset.Icc 0 (n / 2 - 1) := by
            rw [Finset.mem_Icc]
            omega
          exact (hnotmem hmem).elim
      have h5z : (∑ i ∈ Finset.Icc 0 (d - 1), (alpha5 C t i : ℤ)) =
          (alpha5 C t (n / 2 - 1) : ℤ) := by exact_mod_cast hsum5
      unfold Psi
      rw [h5z]
      have hge : (∑ i ∈ Finset.Icc 1 d, alpha3 C t i) ≥ alpha5 C t (n / 2 - 1) :=
        le_trans (le_trans (alpha5_c3one_le_of2 C t htypes hcol h3 hpar36 hpar53 htotal hodd1 hodd5)
          (class1_of2_le_sa5 C))
          (class1_alpha3_cum_ge_sa5 C t d htypes hcol h3 hpar35 hpar36 hpar53 htotal hodd5 hdge)
      exact sub_nonneg.mpr (by exact_mod_cast hge)
    · have hdge6 : n / 2 + 1 ≤ d := by omega
      have hsum5 : (∑ i ∈ Finset.Icc 0 (d - 1), alpha5 C t i) =
          alpha5 C t (n / 2 - 1) + alpha5 C t (n / 2) := by
        have hsub : ({n / 2 - 1, n / 2} : Finset ℕ) ⊆ Finset.Icc 0 (d - 1) := by
          intro i hi
          simp at hi
          rcases hi with hi | hi
          · subst i
            rw [Finset.mem_Icc]
            omega
          · subst i
            rw [Finset.mem_Icc]
            omega
        have hvan : ∀ i ∈ Finset.Icc 0 (d - 1), i ∉ ({n / 2 - 1, n / 2} : Finset ℕ) →
            alpha5 C t i = 0 := by
          intro i hi hnot
          have hne1 : i ≠ n / 2 - 1 := by
            intro h
            exact hnot (by simp [h])
          have hne2 : i ≠ n / 2 := by
            intro h
            exact hnot (by simp [h])
          exact class1_alpha5_eq_zero_c3one C t i htypes hcol h3 hpar36 hpar53 htotal ⟨hne1, hne2⟩
        calc
          (∑ i ∈ Finset.Icc 0 (d - 1), alpha5 C t i)
              = ∑ i ∈ ({n / 2 - 1, n / 2} : Finset ℕ), alpha5 C t i :=
                (Finset.sum_subset hsub hvan).symm
          _ = alpha5 C t (n / 2 - 1) + alpha5 C t (n / 2) := by
                have hne : n / 2 - 1 ≠ n / 2 := by omega
                simp [Finset.sum_insert, hne]
      have h5z : (∑ i ∈ Finset.Icc 0 (d - 1), (alpha5 C t i : ℤ)) =
          (alpha5 C t (n / 2 - 1) : ℤ) + (alpha5 C t (n / 2) : ℤ) := by exact_mod_cast hsum5
      unfold Psi
      rw [h5z]
      have hle1 : alpha5 C t (n / 2 - 1) ≤
          (∑ w1 ∈ Finset.Icc 1 (count C 1), ∑ w6 ∈ Finset.Icc 0 (count C 6),
            if count C 6 ≤ 2 * w6 + 1 ∧ 2 * w1 + count C 6 + 1 ≤ 2 * w6 + count C 1 then
              Nat.choose (count C 1 - 1) (w1 - 1) * Nat.choose (count C 5) ((count C 5 + 1) / 2) *
                Nat.choose (count C 6) w6
            else 0) :=
        le_trans (alpha5_c3one_le_of2 C t htypes hcol h3 hpar36 hpar53 htotal hodd1 hodd5)
          (class1_of2_le_sa5 C)
      have hle2 : alpha5 C t (n / 2) ≤
          (∑ w1 ∈ Finset.Icc 1 (count C 1), ∑ w6 ∈ Finset.Icc 0 (count C 6),
            if count C 6 + 1 ≤ 2 * w6 ∧ 2 * w1 + count C 6 ≤ 2 * w6 + count C 1 + 1 then
              Nat.choose (count C 1 - 1) (w1 - 1) * Nat.choose (count C 5) ((count C 5 - 1) / 2) *
                Nat.choose (count C 6) w6
            else 0) :=
        le_trans (alpha5_c3one_le_of4 C t htypes hcol h3 hpar36 hpar53 htotal hodd5)
          (class1_of4_le_sa6 C)
      have hle : (∑ w1 ∈ Finset.Icc 1 (count C 1), ∑ w6 ∈ Finset.Icc 0 (count C 6),
            if count C 6 ≤ 2 * w6 + 1 ∧ 2 * w1 + count C 6 + 1 ≤ 2 * w6 + count C 1 then
              Nat.choose (count C 1 - 1) (w1 - 1) * Nat.choose (count C 5) ((count C 5 + 1) / 2) *
                Nat.choose (count C 6) w6
            else 0) +
          (∑ w1 ∈ Finset.Icc 1 (count C 1), ∑ w6 ∈ Finset.Icc 0 (count C 6),
            if count C 6 + 1 ≤ 2 * w6 ∧ 2 * w1 + count C 6 ≤ 2 * w6 + count C 1 + 1 then
              Nat.choose (count C 1 - 1) (w1 - 1) * Nat.choose (count C 5) ((count C 5 - 1) / 2) *
                Nat.choose (count C 6) w6
            else 0) ≤
          (∑ i ∈ Finset.Icc 1 d, alpha3 C t i) :=
        class1_alpha3_cum_ge_sa5_add_sa6 C t d htypes hcol h3 hpar35 hpar36 hpar53 htotal hodd5 hdge6
      have hgeZ : (∑ i ∈ Finset.Icc 1 d, (alpha3 C t i : ℤ)) ≥
          (alpha5 C t (n / 2 - 1) : ℤ) + (alpha5 C t (n / 2) : ℤ) := by
        have hsumZ : (alpha5 C t (n / 2 - 1) : ℤ) + (alpha5 C t (n / 2) : ℤ) ≤
            (∑ w1 ∈ Finset.Icc 1 (count C 1), ∑ w6 ∈ Finset.Icc 0 (count C 6),
              if count C 6 ≤ 2 * w6 + 1 ∧ 2 * w1 + count C 6 + 1 ≤ 2 * w6 + count C 1 then
                Nat.choose (count C 1 - 1) (w1 - 1) * Nat.choose (count C 5) ((count C 5 + 1) / 2) *
                  Nat.choose (count C 6) w6
              else 0) +
            (∑ w1 ∈ Finset.Icc 1 (count C 1), ∑ w6 ∈ Finset.Icc 0 (count C 6),
              if count C 6 + 1 ≤ 2 * w6 ∧ 2 * w1 + count C 6 ≤ 2 * w6 + count C 1 + 1 then
                Nat.choose (count C 1 - 1) (w1 - 1) * Nat.choose (count C 5) ((count C 5 - 1) / 2) *
                  Nat.choose (count C 6) w6
              else 0) := by
          exact_mod_cast (Nat.add_le_add hle1 hle2)
        have hleZ : (∑ w1 ∈ Finset.Icc 1 (count C 1), ∑ w6 ∈ Finset.Icc 0 (count C 6),
              if count C 6 ≤ 2 * w6 + 1 ∧ 2 * w1 + count C 6 + 1 ≤ 2 * w6 + count C 1 then
                Nat.choose (count C 1 - 1) (w1 - 1) * Nat.choose (count C 5) ((count C 5 + 1) / 2) *
                  Nat.choose (count C 6) w6
              else 0) +
            (∑ w1 ∈ Finset.Icc 1 (count C 1), ∑ w6 ∈ Finset.Icc 0 (count C 6),
              if count C 6 + 1 ≤ 2 * w6 ∧ 2 * w1 + count C 6 ≤ 2 * w6 + count C 1 + 1 then
                Nat.choose (count C 1 - 1) (w1 - 1) * Nat.choose (count C 5) ((count C 5 - 1) / 2) *
                  Nat.choose (count C 6) w6
              else 0) ≤
            (∑ i ∈ Finset.Icc 1 d, (alpha3 C t i : ℤ)) := by
          exact_mod_cast hle
        omega
      exact sub_nonneg.mpr hgeZ

/-- `thm:301` (Theorem 17) canonical case: |3| = min ∈ {0,1} with |1| odd (general);
replacing the type-1 column by `col3` is never worse.  Class-I-a (|3| = 0)
uses the ψ ≥ 0 machinery (`class1_psi_nonneg_c3zero`); Class-I-b (|3| = 1)
uses `class1_psi_nonneg_c3one` (eq. of2/of4 upper bounds, eq. sa_5/sa_6
lower bounds, and the two containments). -/
lemma class1_min_col3 {n : ℕ} (C : Code n) (t : Fin n)
    (htypes : ∀ u : Fin n, colVal (C u) = 1 ∨ colVal (C u) = 3 ∨
      colVal (C u) = 5 ∨ colVal (C u) = 6)
    (hcol : C t = col1)
    (hpar35 : Even (count C 5) ↔ Even (count C 6))
    (hpar36 : Even (count C 3) ↔ Even (count C 6))
    (hpar53 : Even (count C 5) ↔ Even (count C 3))
    (_h35 : count C 3 ≤ count C 5) (_h36 : count C 3 ≤ count C 6)
    (htotal : totalCounts C {1, 3, 5, 6} = n) (hodd1 : Odd (count C 1))
    (h3le1 : count C 3 ≤ 1) :
    UniversalBetter (replaceColumn C t col3) C := by
  let C' : Code n := replaceColumn C t col3
  have hcol' : C' t = col3 := by simp [C', replaceColumn]
  have hsame : ∀ u : Fin n, u ≠ t → C' u = C u := by
    intro u hu
    simp [C', replaceColumn, hu]
  by_cases hz : count C 3 = 0
  · -- Class-I-a: |3| = 0
    have hge : ∀ d ∈ Finset.Icc 1 n, Psi C t d ≥ 0 := by
      intro d hd
      exact class1_psi_nonneg_c3zero C t d (Finset.mem_Icc.mp hd).1 htypes hcol hz hpar35 hpar36 hpar53 htotal hodd1
    exact cumulative_nonneg C C' t hcol hcol' hsame hge
  · -- Class-I-b: |3| = 1 (paper eq. of2/eq. sa_5, eq. of4/eq. sa_6)
    have h3 : count C 3 = 1 := by omega
    have hodd3 : Odd (count C 3) := by rw [h3]; exact ⟨0, rfl⟩
    have hodd5 : Odd (count C 5) := by
      rw [← Nat.not_even_iff_odd]
      intro he5
      have hodd3' : ¬ Even (count C 3) := (Nat.not_even_iff_odd.mpr hodd3)
      exact hodd3' (hpar53.mp he5)
    have hge : ∀ d ∈ Finset.Icc 1 n, Psi C t d ≥ 0 := by
      intro d hd
      exact class1_psi_nonneg_c3one C t d (Finset.mem_Icc.mp hd).1 htypes hcol h3 hpar35 hpar36 hpar53 htotal hodd1 hodd5
    exact cumulative_nonneg C C' t hcol hcol' hsame hge

/-- Lift a non-strict comparison of the 3↔6-swapped code to one of the
original code, using the λ-role-symmetry on both sides. -/
lemma class1_min_col6_from_dom {n : ℕ} (C : Code n) (t : Fin n)
    (htypes : ∀ u : Fin n, colVal (C u) = 1 ∨ colVal (C u) = 3 ∨
      colVal (C u) = 5 ∨ colVal (C u) = 6)
    (hdom : UniversalBetter (replaceColumn (swap36Code C) t col3) (swap36Code C)) :
    UniversalBetter (replaceColumn C t col6) C := by
  let C' : Code n := replaceColumn C t col6
  let C36 : Code n := swap36Code C
  let C36' : Code n := replaceColumn C36 t col3
  have htypes' : ∀ u : Fin n, colVal (C' u) = 1 ∨ colVal (C' u) = 3 ∨
      colVal (C' u) = 5 ∨ colVal (C' u) = 6 := by
    intro u
    by_cases hu : u = t
    · subst u
      simp [C', replaceColumn, colVal_col6]
    · simp [C', replaceColumn, hu, htypes u]
  have hswap : swap36Code C' = C36' := by
    funext u
    by_cases hu : u = t
    · subst u
      simp [C', C36', replaceColumn, swap36Code, colVal_col6]
    · simp [C', C36', C36, replaceColumn, swap36Code, hu]
  have hsymC : UniversalEqual C36 C := class1_lambda_swap36 C htypes
  have hsymC' : UniversalEqual C36' C' := by
    rw [← hswap]
    exact class1_lambda_swap36 C' htypes'
  intro ε hε0 hε1
  have heq1 : lambda C' ε = lambda C36' ε := (hsymC' ε hε0 hε1).symm
  have hge : lambda C36' ε ≥ lambda C36 ε := hdom ε hε0 hε1
  have heq2 : lambda C36 ε = lambda C ε := hsymC ε hε0 hε1
  linarith

/-! ## Theorem statements (`thm:11` (Theorem 16), `thm:301` (Theorem 17)) -/

/-- Theorem `thm:11` (Theorem 16): Class-I code with |1| = 1; replacing the type-1 column by
the argmin type is strictly better unless n = 3, where it is equal.  The
α³/α⁵ binomial closed forms, the cumulative-sum domination (`class1_psi_*`),
and the argmin case split (col3 via `class1_one_col3_strict*`, col5 via the
`swap12` equivalence `class1_one_col5_strict`, col6 via the λ-role-symmetry
`class1_one_col6_strict`) are all proved.  The `DistinctRows` hypothesis rules
out duplicate-codeword codes, for which the paper's n = 3 equality is not
literally true; see `CompanionNote.tex` §Discrepancies. -/
theorem class1_one {n : ℕ} (C : Code n) (t : Fin n) (hdist : DistinctRows C) (h : ClassI C)
    (h1 : count C 1 = 1) (h0 : C t = col1) :
    let C' := replaceColumn C t (argminType C)
    (n ≠ 3 → UniversalStrictBetter C' C) ∧ (n = 3 → UniversalEqual C' C) := by
  rcases classI_hyps C h with ⟨htypes, hpar35, hpar36, hpar53, htotal⟩
  constructor
  · intro _hn3
    by_cases h3min : count C 3 ≤ count C 5 ∧ count C 3 ≤ count C 6
    · -- argmin = col3
      have harg : argminType C = col3 := argminType_eq_col3 C h3min
      by_cases hz : count C 3 = 0
      · have hpos56 : 2 ≤ count C 5 + count C 6 :=
          class1_hpos56_of_c3zero C htypes hpar53 hpar36 hz hdist
        have hdom : UniversalStrictBetter (replaceColumn C t col3) C :=
          class1_one_col3_strict_zero C t htypes h1 h0 hpar35 hpar36 hpar53
            h3min.1 h3min.2 htotal hz hpos56
        simpa [harg] using hdom
      · have hpos : 0 < count C 3 := by omega
        by_cases heq : count C 3 = count C 6
        · have hdom : UniversalStrictBetter (replaceColumn C t col3) C :=
            class1_one_col3_strict_eq C t htypes h1 h0 hpar35 hpar36 hpar53
              h3min.1 h3min.2 htotal hpos heq
          simpa [harg] using hdom
        · have hlt : count C 3 < count C 6 := by omega
          have hdom : UniversalStrictBetter (replaceColumn C t col3) C :=
            class1_one_col3_strict C t htypes h1 h0 hpar35 hpar36 hpar53
              h3min.1 h3min.2 htotal hpos hlt
          simpa [harg] using hdom
    · -- argmin ≠ 3
      by_cases h56 : count C 5 ≤ count C 6
      · -- argmin = col5
        have harg : argminType C = col5 := argminType_eq_col5 C h3min h56
        have hpos56 : 2 ≤ count C 5 + count C 6 :=
          class1_hpos56_of_count1 C htypes hpar35 h56 hdist
        have hdom : UniversalStrictBetter (replaceColumn C t col5) C :=
          class1_one_col5_strict C t htypes h1 h0 hpar35 hpar36 hpar53 htotal h3min h56 hpos56
        simpa [harg] using hdom
      · -- argmin = col6
        have harg : argminType C = col6 := argminType_eq_col6 C h3min h56
        have h65 : count C 6 < count C 5 := Nat.lt_of_not_ge h56
        have h56c : count C 6 ≤ count C 5 := le_of_lt h65
        have h36c : count C 6 ≤ count C 3 := by
          by_contra hnot
          have h36gt : count C 3 < count C 6 := Nat.lt_of_not_ge hnot
          have h35lt : count C 3 < count C 5 := lt_trans h36gt h65
          exact h3min ⟨le_of_lt h35lt, le_of_lt h36gt⟩
        have hpos35 : 2 ≤ count C 3 + count C 5 :=
          class1_hpos35_of_count1 C hpar53 h65
        have hdom : UniversalStrictBetter (replaceColumn C t col6) C :=
          class1_one_col6_strict C t htypes h1 h0 hpar35 hpar36 hpar53 h36c h56c htotal hpos35
        simpa [harg] using hdom
  · intro hn3
    subst n
    exact (no_classI_count1_distinct_n3 C hdist h h1).elim

/-- Theorem `thm:301` (Theorem 17): Class-I code with min{|3|,|5|,|6|} ∈ {0,1}; replacing a
type-1 column by the argmin type is never worse.  The min = 5 and min = 6
cases reduce to |3| = min via the `swap12` equivalence and the λ-role-symmetry
(`class1_min_col6_from_dom`); the canonical |3| = min ∈ {0,1} case is
`class1_min_col3` (Class-I-a done, Class-I-b pending). -/
theorem class1_min {n : ℕ} (C : Code n) (t : Fin n) (h : ClassI C) (h0 : C t = col1)
    (hm : min (count C 3) (min (count C 5) (count C 6)) ≤ 1) :
    UniversalBetter (replaceColumn C t (argminType C)) C := by
  rcases h with ⟨hodd1, hpar, htotal⟩
  have htypes : ∀ u : Fin n, colVal (C u) = 1 ∨ colVal (C u) = 3 ∨
      colVal (C u) = 5 ∨ colVal (C u) = 6 := by
    intro u
    exact types_1356_of_totalCounts C htotal u
  have hpar35 : Even (count C 5) ↔ Even (count C 6) := by
    rcases hpar with hEven | hOdd
    · exact ⟨fun _ => hEven.2.2, fun _ => hEven.2.1⟩
    · constructor
      · intro h5; exact False.elim ((Nat.not_even_iff_odd.mpr hOdd.2.1) h5)
      · intro h6; exact False.elim ((Nat.not_even_iff_odd.mpr hOdd.2.2) h6)
  have hpar36 : Even (count C 3) ↔ Even (count C 6) := by
    rcases hpar with hEven | hOdd
    · exact ⟨fun _ => hEven.2.2, fun _ => hEven.1⟩
    · constructor
      · intro h3; exact False.elim ((Nat.not_even_iff_odd.mpr hOdd.1) h3)
      · intro h6; exact False.elim ((Nat.not_even_iff_odd.mpr hOdd.2.2) h6)
  have hpar53 : Even (count C 5) ↔ Even (count C 3) := by
    rcases hpar with hEven | hOdd
    · exact ⟨fun _ => hEven.1, fun _ => hEven.2.1⟩
    · constructor
      · intro h5; exact False.elim ((Nat.not_even_iff_odd.mpr hOdd.2.1) h5)
      · intro h3; exact False.elim ((Nat.not_even_iff_odd.mpr hOdd.1) h3)
  by_cases h3min : count C 3 ≤ count C 5 ∧ count C 3 ≤ count C 6
  · -- argmin = col3
    have harg : argminType C = col3 := argminType_eq_col3 C h3min
    have h3le1 : count C 3 ≤ 1 := by
      have hmin : min (count C 3) (min (count C 5) (count C 6)) = count C 3 := by
        rw [Nat.min_eq_left (le_min h3min.1 h3min.2)]
      rw [hmin] at hm
      exact hm
    have hdom : UniversalBetter (replaceColumn C t col3) C :=
      class1_min_col3 C t htypes h0 hpar35 hpar36 hpar53 h3min.1 h3min.2 htotal hodd1 h3le1
    simpa [harg] using hdom
  · -- argmin ≠ 3
    by_cases h56 : count C 5 ≤ count C 6
    · -- argmin = col5 (swap12 reduction to |3| = min)
      have harg : argminType C = col5 := argminType_eq_col5 C h3min h56
      let Cs : Code n := swap12Code C
      have hEq : Equivalent C Cs := Equivalent_swap12Code C
      have htypes' : ∀ u : Fin n, colVal (Cs u) = 1 ∨ colVal (Cs u) = 3 ∨
          colVal (Cs u) = 5 ∨ colVal (Cs u) = 6 := by
        intro u
        rcases htypes u with h1' | h3' | h5' | h6'
        · have hc : C u = col1 := (colVal_eq_one_iff_col1 (C u)).1 h1'
          exact Or.inl (by simp [Cs, swap12Code, hc, rowPermute_swap12_col1, colVal_col1])
        · have hc : C u = col3 := (colVal_eq_three_iff_col3 (C u)).1 h3'
          exact Or.inr (Or.inr (Or.inl (by simp [Cs, swap12Code, hc, rowPermute_swap12_col3, colVal_col5])))
        · have hc : C u = col5 := (colVal_eq_five_iff_col5 (C u)).1 h5'
          exact Or.inr (Or.inl (by simp [Cs, swap12Code, hc, rowPermute_swap12_col5, colVal_col3]))
        · have hc : C u = col6 := (colVal_eq_six_iff_col6 (C u)).1 h6'
          exact Or.inr (Or.inr (Or.inr (by simp [Cs, swap12Code, hc, rowPermute_swap12_col6, colVal_col6])))
      have hcol' : Cs t = col1 := by
        simp [Cs, swap12Code, h0, rowPermute_swap12_col1]
      have hc1' : count Cs 1 = count C 1 := count_swap12Code_one C htypes
      have hc3' : count Cs 3 = count C 5 := count_swap12Code C htypes
      have hc5' : count Cs 5 = count C 3 := count_swap12Code_five C htypes
      have hc6' : count Cs 6 = count C 6 := count_swap12Code_six C htypes
      have hodd1' : Odd (count Cs 1) := by rw [hc1']; exact hodd1
      have hpar35' : Even (count Cs 5) ↔ Even (count Cs 6) := by
        rw [hc5', hc6']
        exact hpar53.symm.trans hpar35
      have hpar36' : Even (count Cs 3) ↔ Even (count Cs 6) := by
        rw [hc3', hc6']
        exact hpar35
      have hpar53' : Even (count Cs 5) ↔ Even (count Cs 3) := by
        rw [hc5', hc3']
        exact hpar53.symm
      have hnot35 : ¬ count C 3 ≤ count C 5 := by
        intro h35c
        by_cases h36c : count C 3 ≤ count C 6
        · exact h3min ⟨h35c, h36c⟩
        · have h63 : count C 6 < count C 3 := Nat.lt_of_not_ge h36c
          have h53 : count C 5 < count C 3 := lt_of_le_of_lt h56 h63
          omega
      have h35' : count Cs 3 ≤ count Cs 5 := by
        rw [hc3', hc5']
        omega
      have h36' : count Cs 3 ≤ count Cs 6 := by
        rw [hc3', hc6']
        exact h56
      have h5le1 : count C 5 ≤ 1 := by
        have h53' : count C 5 < count C 3 := Nat.lt_of_not_ge hnot35
        have hle : count C 5 ≤ min (count C 3) (min (count C 5) (count C 6)) := by
          rw [Nat.min_eq_left h56]
          rw [Nat.min_eq_right (le_of_lt h53')]
        omega
      have h3le1' : count Cs 3 ≤ 1 := by
        rw [hc3']
        exact h5le1
      have htotal' : totalCounts Cs {1, 3, 5, 6} = n := by
        unfold totalCounts
        calc
          (∑ i ∈ ({1, 3, 5, 6} : Finset ℕ), count Cs i)
              = count C 1 + count C 5 + count C 3 + count C 6 := by
                simp [hc1', hc3', hc5', hc6', Finset.sum_insert]
                omega
          _ = n := by
            have hsum : count C 1 + count C 3 + count C 5 + count C 6 = n := by
              calc
                count C 1 + count C 3 + count C 5 + count C 6
                    = ∑ i ∈ ({1, 3, 5, 6} : Finset ℕ), count C i := by
                      simp [Finset.sum_insert]
                      omega
                _ = n := htotal
            omega
      have hdom' : UniversalBetter (replaceColumn Cs t col3) Cs :=
        class1_min_col3 Cs t htypes' hcol' hpar35' hpar36' hpar53' h35' h36' htotal' hodd1' h3le1'
      have hEq' : ∀ s' : Column,
          Equivalent (replaceColumn C t s') (replaceColumn Cs t (rowPermute swap12 s')) := by
        intro s'
        refine ⟨swap12, Equiv.refl (Fin n), (fun _ => false), ?_⟩
        intro u
        by_cases hu : u = t
        · subst u
          simp [replaceColumn, Cs]
        · simp [replaceColumn, hu, Cs, swap12Code]
      have hEq5 : Equivalent (replaceColumn C t col5) (replaceColumn Cs t col3) := by
        simpa [rowPermute_swap12_col5] using (hEq' col5)
      have hdom : UniversalBetter (replaceColumn C t col5) C :=
        universalBetter_of_equivalent (replaceColumn C t col5) (replaceColumn Cs t col3) C Cs
          hEq5 hEq hdom'
      simpa [harg] using hdom
    · -- argmin = col6 (λ-role-symmetry reduction to |3| = min)
      have harg : argminType C = col6 := argminType_eq_col6 C h3min h56
      let C36 : Code n := swap36Code C
      have htypes36 : ∀ u : Fin n, colVal (C36 u) = 1 ∨ colVal (C36 u) = 3 ∨
          colVal (C36 u) = 5 ∨ colVal (C36 u) = 6 := by
        intro u
        exact types_swap36Code C htypes u
      have hcol36 : C36 t = col1 := by
        dsimp [C36]
        simp [swap36Code, h0, colVal_col1]
      have hc136 : count C36 1 = count C 1 := count_swap36Code_one C htypes
      have hc336 : count C36 3 = count C 6 := count_swap36Code_three C htypes
      have hc536 : count C36 5 = count C 5 := count_swap36Code_five C htypes
      have hc636 : count C36 6 = count C 3 := count_swap36Code_six C htypes
      have hodd136 : Odd (count C36 1) := by rw [hc136]; exact hodd1
      have hpar3536 : Even (count C36 5) ↔ Even (count C36 6) := by
        rw [hc536, hc636]
        exact hpar53
      have hpar3636 : Even (count C36 3) ↔ Even (count C36 6) := by
        rw [hc336, hc636]
        exact hpar36.symm
      have hpar5336 : Even (count C36 5) ↔ Even (count C36 3) := by
        rw [hc536, hc336]
        exact hpar35
      have h65 : count C 6 < count C 5 := Nat.lt_of_not_ge h56
      have h56c : count C 6 ≤ count C 5 := le_of_lt h65
      have h36c : count C 6 ≤ count C 3 := by
        by_contra hnot
        have h36gt : count C 3 < count C 6 := Nat.lt_of_not_ge hnot
        have h35lt : count C 3 < count C 5 := lt_trans h36gt h65
        exact h3min ⟨le_of_lt h35lt, le_of_lt h36gt⟩
      have h3536 : count C36 3 ≤ count C36 5 := by
        rw [hc336, hc536]
        exact h56c
      have h3636 : count C36 3 ≤ count C36 6 := by
        rw [hc336, hc636]
        exact h36c
      have h6le1 : count C 6 ≤ 1 := by
        have hle : count C 6 ≤ min (count C 3) (min (count C 5) (count C 6)) := by
          rw [Nat.min_eq_right h56c]
          rw [Nat.min_eq_right h36c]
        omega
      have h3le136 : count C36 3 ≤ 1 := by
        rw [hc336]
        exact h6le1
      have htotal36 : totalCounts C36 {1, 3, 5, 6} = n := by
        unfold totalCounts
        calc
          (∑ i ∈ ({1, 3, 5, 6} : Finset ℕ), count C36 i)
              = count C 1 + count C 6 + count C 5 + count C 3 := by
                simp [hc136, hc336, hc536, hc636, Finset.sum_insert]
                omega
          _ = n := by
            have hsum : count C 1 + count C 3 + count C 5 + count C 6 = n := by
              calc
                count C 1 + count C 3 + count C 5 + count C 6
                    = ∑ i ∈ ({1, 3, 5, 6} : Finset ℕ), count C i := by
                      simp [Finset.sum_insert]
                      omega
                _ = n := htotal
            omega
      have hdom36 : UniversalBetter (replaceColumn C36 t col3) C36 :=
        class1_min_col3 C36 t htypes36 hcol36 hpar3536 hpar3636 hpar5336 h3536 h3636 htotal36 hodd136 h3le136
      have hdom : UniversalBetter (replaceColumn C t col6) C :=
        class1_min_col6_from_dom C t htypes hdom36
      simpa [harg] using hdom

end N4Code
