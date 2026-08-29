import N4Code.ClassI

/-!
# The n > 3 covering and the sufficient condition (`thm:nbig3` (Theorem 3),
`thm:condition_optimalcode` (Theorem 4), paper §3.4)

`lm_all` (Reduction.lean) covers optimal codes with columns in 1..14 with
linear/Class-I/II/III codes; `thm:nbig3` (Theorem 3) excludes 0/15 columns and shows
Class-III codes are not optimal for n > 3 (via `class3_to_linear` and the
`thm:linearopt` (Theorem 2) residues), leaving linear/Class-I/II.  `thm:condition_optimalcode` (Theorem 4)
then refines to linear codes under the argmin-type hypothesis, using
`thm:nbig3` (Theorem 3), `class2_to_class1`, and `class1_one` (`thm:11` (Theorem 16)).

This module sits after ClassI so it sees both the Reduction machinery and the
Linear `thm:linearopt` (Theorem 2) residues.
-/

namespace N4Code

/-- `hammingDist` between two rows is invariant under the cast bijection on
positions (used to move from `linearCode` to the cast form `linCode`). -/
lemma hammingDist_row_cast {m n : ℕ} (h : m = n) (C : Code m) (i j : Fin 4) :
    hammingDist (row (cast (congrArg Code h) C) i) (row (cast (congrArg Code h) C) j) =
      hammingDist (row C i) (row C j) := by
  rw [← dRow_eq_hammingDist, ← dRow_eq_hammingDist]
  rw [dRow_eq_indicator_sum, dRow_eq_indicator_sum]
  apply Finset.sum_bij (fun t _ => Fin.cast h.symm t)
  · intro t _; simp
  · intro a _ b _ hab
    have hfin : Fin.cast h (Fin.cast h.symm a) = Fin.cast h (Fin.cast h.symm b) := by rw [hab]
    simpa using hfin
  · intro k _
    refine ⟨Fin.cast h k, by simp, ?_⟩
    rfl
  · intro t _
    have hc : (cast (congrArg Code h) C) t = C (Fin.cast h.symm t) := cast_code_apply h C t
    simp [row, colBit, hc]
    by_cases hb : C (Fin.cast h.symm t) i = C (Fin.cast h.symm t) j <;> simp [hb]

-- native_decide: Mechanical · n=any · checked 2026-08-27
/-- Pairwise row distances of `linearCode a b c`: rows 1,2 (d01 = b+c). -/
lemma linearCode_hDist_01 (a b c : ℕ) :
    hammingDist (row (linearCode a b c) ⟨0, by decide⟩) (row (linearCode a b c) ⟨1, by decide⟩) = b + c := by
  have hS : ∀ t : Fin (a + b + c), colVal (linearCode a b c t) ∈ ({3, 5, 6} : Finset ℕ) := by
    intro t
    rcases linear_col_type (n3 := a) (n5 := b) (n6 := c) t with h3 | h5 | h6
    · simp [h3]
    · simp [h5]
    · simp [h6]
  have hsum := sum_indicator_of_types (linearCode a b c) ({3, 5, 6} : Finset ℕ)
    (fun k => k.testBit 3 ≠ k.testBit 2) hS
  rw [hammingDist_row_eq_indicator]
  change (∑ t : Fin (a + b + c),
    if (colVal (linearCode a b c t)).testBit 3 ≠ (colVal (linearCode a b c t)).testBit 2 then 1 else 0) = b + c
  rw [hsum]
  have h3a : (3 : ℕ).testBit 3 = false := by native_decide
  have h3b : (3 : ℕ).testBit 2 = false := by native_decide
  have h5a : (5 : ℕ).testBit 3 = false := by native_decide
  have h5b : (5 : ℕ).testBit 2 = true := by native_decide
  have h6a : (6 : ℕ).testBit 3 = false := by native_decide
  have h6b : (6 : ℕ).testBit 2 = true := by native_decide
  simp [Finset.sum_insert, h3a, h3b, h5a, h5b, h6a, h6b,
    linear_count_5, linear_count_6]

-- native_decide: Mechanical · n=any · checked 2026-08-27
/-- Pairwise row distances of `linearCode a b c`: rows 1,3 (d02 = a+c). -/
lemma linearCode_hDist_02 (a b c : ℕ) :
    hammingDist (row (linearCode a b c) ⟨0, by decide⟩) (row (linearCode a b c) ⟨2, by decide⟩) = a + c := by
  have hS : ∀ t : Fin (a + b + c), colVal (linearCode a b c t) ∈ ({3, 5, 6} : Finset ℕ) := by
    intro t
    rcases linear_col_type (n3 := a) (n5 := b) (n6 := c) t with h3 | h5 | h6
    · simp [h3]
    · simp [h5]
    · simp [h6]
  have hsum := sum_indicator_of_types (linearCode a b c) ({3, 5, 6} : Finset ℕ)
    (fun k => k.testBit 3 ≠ k.testBit 1) hS
  rw [hammingDist_row_eq_indicator]
  change (∑ t : Fin (a + b + c),
    if (colVal (linearCode a b c t)).testBit 3 ≠ (colVal (linearCode a b c t)).testBit 1 then 1 else 0) = a + c
  rw [hsum]
  have h3a : (3 : ℕ).testBit 3 = false := by native_decide
  have h3b : (3 : ℕ).testBit 1 = true := by native_decide
  have h5a : (5 : ℕ).testBit 3 = false := by native_decide
  have h5b : (5 : ℕ).testBit 1 = false := by native_decide
  have h6a : (6 : ℕ).testBit 3 = false := by native_decide
  have h6b : (6 : ℕ).testBit 1 = true := by native_decide
  simp [Finset.sum_insert, h3a, h3b, h5a, h5b, h6a, h6b,
    linear_count_3, linear_count_6]

-- native_decide: Mechanical · n=any · checked 2026-08-27
/-- Pairwise row distances of `linearCode a b c`: rows 1,4 (d03 = a+b). -/
lemma linearCode_hDist_03 (a b c : ℕ) :
    hammingDist (row (linearCode a b c) ⟨0, by decide⟩) (row (linearCode a b c) ⟨3, by decide⟩) = a + b := by
  have hS : ∀ t : Fin (a + b + c), colVal (linearCode a b c t) ∈ ({3, 5, 6} : Finset ℕ) := by
    intro t
    rcases linear_col_type (n3 := a) (n5 := b) (n6 := c) t with h3 | h5 | h6
    · simp [h3]
    · simp [h5]
    · simp [h6]
  have hsum := sum_indicator_of_types (linearCode a b c) ({3, 5, 6} : Finset ℕ)
    (fun k => k.testBit 3 ≠ k.testBit 0) hS
  rw [hammingDist_row_eq_indicator]
  change (∑ t : Fin (a + b + c),
    if (colVal (linearCode a b c t)).testBit 3 ≠ (colVal (linearCode a b c t)).testBit 0 then 1 else 0) = a + b
  rw [hsum]
  have h3a : (3 : ℕ).testBit 3 = false := by native_decide
  have h3b : (3 : ℕ).testBit 0 = true := by native_decide
  have h5a : (5 : ℕ).testBit 3 = false := by native_decide
  have h5b : (5 : ℕ).testBit 0 = true := by native_decide
  have h6a : (6 : ℕ).testBit 3 = false := by native_decide
  have h6b : (6 : ℕ).testBit 0 = false := by native_decide
  simp [Finset.sum_insert, h3a, h5a, h6a,
    linear_count_3, linear_count_5]

-- native_decide: Mechanical · n=any · checked 2026-08-27
/-- Pairwise row distances of `linearCode a b c`: rows 2,3 (d12 = a+b). -/
lemma linearCode_hDist_12 (a b c : ℕ) :
    hammingDist (row (linearCode a b c) ⟨1, by decide⟩) (row (linearCode a b c) ⟨2, by decide⟩) = a + b := by
  have hS : ∀ t : Fin (a + b + c), colVal (linearCode a b c t) ∈ ({3, 5, 6} : Finset ℕ) := by
    intro t
    rcases linear_col_type (n3 := a) (n5 := b) (n6 := c) t with h3 | h5 | h6
    · simp [h3]
    · simp [h5]
    · simp [h6]
  have hsum := sum_indicator_of_types (linearCode a b c) ({3, 5, 6} : Finset ℕ)
    (fun k => k.testBit 2 ≠ k.testBit 1) hS
  rw [hammingDist_row_eq_indicator]
  change (∑ t : Fin (a + b + c),
    if (colVal (linearCode a b c t)).testBit 2 ≠ (colVal (linearCode a b c t)).testBit 1 then 1 else 0) = a + b
  rw [hsum]
  have h3a : (3 : ℕ).testBit 2 = false := by native_decide
  have h3b : (3 : ℕ).testBit 1 = true := by native_decide
  have h5a : (5 : ℕ).testBit 2 = true := by native_decide
  have h5b : (5 : ℕ).testBit 1 = false := by native_decide
  have h6a : (6 : ℕ).testBit 2 = true := by native_decide
  have h6b : (6 : ℕ).testBit 1 = true := by native_decide
  simp [Finset.sum_insert, h3a, h3b, h5a, h5b, h6a, h6b,
    linear_count_3, linear_count_5]

-- native_decide: Mechanical · n=any · checked 2026-08-27
/-- Pairwise row distances of `linearCode a b c`: rows 2,4 (d13 = a+c). -/
lemma linearCode_hDist_13 (a b c : ℕ) :
    hammingDist (row (linearCode a b c) ⟨1, by decide⟩) (row (linearCode a b c) ⟨3, by decide⟩) = a + c := by
  have hS : ∀ t : Fin (a + b + c), colVal (linearCode a b c t) ∈ ({3, 5, 6} : Finset ℕ) := by
    intro t
    rcases linear_col_type (n3 := a) (n5 := b) (n6 := c) t with h3 | h5 | h6
    · simp [h3]
    · simp [h5]
    · simp [h6]
  have hsum := sum_indicator_of_types (linearCode a b c) ({3, 5, 6} : Finset ℕ)
    (fun k => k.testBit 2 ≠ k.testBit 0) hS
  rw [hammingDist_row_eq_indicator]
  change (∑ t : Fin (a + b + c),
    if (colVal (linearCode a b c t)).testBit 2 ≠ (colVal (linearCode a b c t)).testBit 0 then 1 else 0) = a + c
  rw [hsum]
  have h3a : (3 : ℕ).testBit 2 = false := by native_decide
  have h3b : (3 : ℕ).testBit 0 = true := by native_decide
  have h5a : (5 : ℕ).testBit 2 = true := by native_decide
  have h5b : (5 : ℕ).testBit 0 = true := by native_decide
  have h6a : (6 : ℕ).testBit 2 = true := by native_decide
  have h6b : (6 : ℕ).testBit 0 = false := by native_decide
  simp [Finset.sum_insert, h3a, h5a, h6a,
    linear_count_3, linear_count_6]

-- native_decide: Mechanical · n=any · checked 2026-08-27
/-- Pairwise row distances of `linearCode a b c`: rows 3,4 (d23 = b+c). -/
lemma linearCode_hDist_23 (a b c : ℕ) :
    hammingDist (row (linearCode a b c) ⟨2, by decide⟩) (row (linearCode a b c) ⟨3, by decide⟩) = b + c := by
  have hS : ∀ t : Fin (a + b + c), colVal (linearCode a b c t) ∈ ({3, 5, 6} : Finset ℕ) := by
    intro t
    rcases linear_col_type (n3 := a) (n5 := b) (n6 := c) t with h3 | h5 | h6
    · simp [h3]
    · simp [h5]
    · simp [h6]
  have hsum := sum_indicator_of_types (linearCode a b c) ({3, 5, 6} : Finset ℕ)
    (fun k => k.testBit 1 ≠ k.testBit 0) hS
  rw [hammingDist_row_eq_indicator]
  change (∑ t : Fin (a + b + c),
    if (colVal (linearCode a b c t)).testBit 1 ≠ (colVal (linearCode a b c t)).testBit 0 then 1 else 0) = b + c
  rw [hsum]
  have h3a : (3 : ℕ).testBit 1 = true := by native_decide
  have h3b : (3 : ℕ).testBit 0 = true := by native_decide
  have h5a : (5 : ℕ).testBit 1 = false := by native_decide
  have h5b : (5 : ℕ).testBit 0 = true := by native_decide
  have h6a : (6 : ℕ).testBit 1 = true := by native_decide
  have h6b : (6 : ℕ).testBit 0 = false := by native_decide
  simp [Finset.sum_insert, h3a, h5a, h6a,
    linear_count_5, linear_count_6]

/-- Pairwise row distances of `linCode a b c hsum`: rows 1,2 (d01 = b+c). -/
lemma linCode_hDist_01 {n : ℕ} {a b c : ℕ} (hsum : a + b + c = n) :
    hammingDist (row (linCode a b c hsum) ⟨0, by decide⟩) (row (linCode a b c hsum) ⟨1, by decide⟩) = b + c := by
  change hammingDist (row (cast (congrArg Code hsum) (linearCode a b c)) ⟨0, by decide⟩)
      (row (cast (congrArg Code hsum) (linearCode a b c)) ⟨1, by decide⟩) = b + c
  rw [hammingDist_row_cast hsum]
  exact linearCode_hDist_01 a b c

/-- Pairwise row distances of `linCode a b c hsum`: rows 1,3 (d02 = a+c). -/
lemma linCode_hDist_02 {n : ℕ} {a b c : ℕ} (hsum : a + b + c = n) :
    hammingDist (row (linCode a b c hsum) ⟨0, by decide⟩) (row (linCode a b c hsum) ⟨2, by decide⟩) = a + c := by
  change hammingDist (row (cast (congrArg Code hsum) (linearCode a b c)) ⟨0, by decide⟩)
      (row (cast (congrArg Code hsum) (linearCode a b c)) ⟨2, by decide⟩) = a + c
  rw [hammingDist_row_cast hsum]
  exact linearCode_hDist_02 a b c

/-- Pairwise row distances of `linCode a b c hsum`: rows 1,4 (d03 = a+b). -/
lemma linCode_hDist_03 {n : ℕ} {a b c : ℕ} (hsum : a + b + c = n) :
    hammingDist (row (linCode a b c hsum) ⟨0, by decide⟩) (row (linCode a b c hsum) ⟨3, by decide⟩) = a + b := by
  change hammingDist (row (cast (congrArg Code hsum) (linearCode a b c)) ⟨0, by decide⟩)
      (row (cast (congrArg Code hsum) (linearCode a b c)) ⟨3, by decide⟩) = a + b
  rw [hammingDist_row_cast hsum]
  exact linearCode_hDist_03 a b c

/-- Pairwise row distances of `linCode a b c hsum`: rows 2,3 (d12 = a+b). -/
lemma linCode_hDist_12 {n : ℕ} {a b c : ℕ} (hsum : a + b + c = n) :
    hammingDist (row (linCode a b c hsum) ⟨1, by decide⟩) (row (linCode a b c hsum) ⟨2, by decide⟩) = a + b := by
  change hammingDist (row (cast (congrArg Code hsum) (linearCode a b c)) ⟨1, by decide⟩)
      (row (cast (congrArg Code hsum) (linearCode a b c)) ⟨2, by decide⟩) = a + b
  rw [hammingDist_row_cast hsum]
  exact linearCode_hDist_12 a b c

/-- Pairwise row distances of `linCode a b c hsum`: rows 2,4 (d13 = a+c). -/
lemma linCode_hDist_13 {n : ℕ} {a b c : ℕ} (hsum : a + b + c = n) :
    hammingDist (row (linCode a b c hsum) ⟨1, by decide⟩) (row (linCode a b c hsum) ⟨3, by decide⟩) = a + c := by
  change hammingDist (row (cast (congrArg Code hsum) (linearCode a b c)) ⟨1, by decide⟩)
      (row (cast (congrArg Code hsum) (linearCode a b c)) ⟨3, by decide⟩) = a + c
  rw [hammingDist_row_cast hsum]
  exact linearCode_hDist_13 a b c

/-- Pairwise row distances of `linCode a b c hsum`: rows 3,4 (d23 = b+c). -/
lemma linCode_hDist_23 {n : ℕ} {a b c : ℕ} (hsum : a + b + c = n) :
    hammingDist (row (linCode a b c hsum) ⟨2, by decide⟩) (row (linCode a b c hsum) ⟨3, by decide⟩) = b + c := by
  change hammingDist (row (cast (congrArg Code hsum) (linearCode a b c)) ⟨2, by decide⟩)
      (row (cast (congrArg Code hsum) (linearCode a b c)) ⟨3, by decide⟩) = b + c
  rw [hammingDist_row_cast hsum]
  exact linearCode_hDist_23 a b c

/-- The pairwise row distances are preserved by equivalence: the row
permutation `ρ` relabels the rows and the column flips cancel. -/
lemma hammingDist_row_equiv {n : ℕ} {C C' : Code n} (h : Equivalent C C') :
    ∃ ρ : Equiv (Fin 4) (Fin 4), ∀ i j : Fin 4,
      hammingDist (row C' i) (row C' j) = hammingDist (row C (ρ i)) (row C (ρ j)) := by
  rcases h with ⟨ρ, p, f, hh⟩
  refine ⟨ρ, ?_⟩
  intro i j
  rw [← dRow_eq_hammingDist, ← dRow_eq_hammingDist]
  rw [dRow_eq_indicator_sum, dRow_eq_indicator_sum]
  apply Finset.sum_bij (fun t _ => p.symm t)
  · intro t _; simp
  · intro a _ b _ hab
    have hp : p (p.symm a) = p (p.symm b) := by rw [hab]
    simpa using hp
  · intro k _
    refine ⟨p k, by simp, ?_⟩
    exact p.symm_apply_apply k
  · intro t _
    have hh' : C' t = rowPermute ρ (if f (p.symm t) then flipCol (C (p.symm t)) else C (p.symm t)) := by
      simpa [p.apply_symm_apply] using hh (p.symm t)
    simp [row, colBit, hh', rowPermute]
    by_cases hf : f (p.symm t) <;> by_cases hb : C (p.symm t) (ρ i) = C (p.symm t) (ρ j) <;>
      simp [hf, hb, flipCol]

/-- The minimum pairwise row distance. -/
def pairwiseMin {n : ℕ} (C : Code n) : ℕ :=
  min (hammingDist (row C ⟨0, by decide⟩) (row C ⟨1, by decide⟩))
    (min (hammingDist (row C ⟨0, by decide⟩) (row C ⟨2, by decide⟩))
      (min (hammingDist (row C ⟨0, by decide⟩) (row C ⟨3, by decide⟩))
        (min (hammingDist (row C ⟨1, by decide⟩) (row C ⟨2, by decide⟩))
          (min (hammingDist (row C ⟨1, by decide⟩) (row C ⟨3, by decide⟩))
            (hammingDist (row C ⟨2, by decide⟩) (row C ⟨3, by decide⟩))))))

/-- `pairwiseMin` is at most every distance between two distinct rows. -/
lemma pairwiseMin_le_all {n : ℕ} (C : Code n) {i j : Fin 4} (hij : i ≠ j) :
    pairwiseMin C ≤ hammingDist (row C i) (row C j) := by
  fin_cases i <;> fin_cases j <;> simp [pairwiseMin, hammingDist_symm] at hij ⊢

/-- `pairwiseMin` is attained at some row pair. -/
lemma pairwiseMin_mem {n : ℕ} (C : Code n) :
    ∃ i j : Fin 4, i ≠ j ∧ pairwiseMin C = hammingDist (row C i) (row C j) := by
  have hcases : pairwiseMin C = hammingDist (row C ⟨0, by decide⟩) (row C ⟨1, by decide⟩) ∨
      pairwiseMin C = hammingDist (row C ⟨0, by decide⟩) (row C ⟨2, by decide⟩) ∨
      pairwiseMin C = hammingDist (row C ⟨0, by decide⟩) (row C ⟨3, by decide⟩) ∨
      pairwiseMin C = hammingDist (row C ⟨1, by decide⟩) (row C ⟨2, by decide⟩) ∨
      pairwiseMin C = hammingDist (row C ⟨1, by decide⟩) (row C ⟨3, by decide⟩) ∨
      pairwiseMin C = hammingDist (row C ⟨2, by decide⟩) (row C ⟨3, by decide⟩) := by
    unfold pairwiseMin
    omega
  rcases hcases with h1 | h2 | h3 | h4 | h5 | h6
  · exact ⟨⟨0, by decide⟩, ⟨1, by decide⟩, by decide, h1⟩
  · exact ⟨⟨0, by decide⟩, ⟨2, by decide⟩, by decide, h2⟩
  · exact ⟨⟨0, by decide⟩, ⟨3, by decide⟩, by decide, h3⟩
  · exact ⟨⟨1, by decide⟩, ⟨2, by decide⟩, by decide, h4⟩
  · exact ⟨⟨1, by decide⟩, ⟨3, by decide⟩, by decide, h5⟩
  · exact ⟨⟨2, by decide⟩, ⟨3, by decide⟩, by decide, h6⟩

/-- `pairwiseMin` is invariant under equivalence. -/
lemma pairwiseMin_equiv {n : ℕ} {C C' : Code n} (h : Equivalent C C') :
    pairwiseMin C = pairwiseMin C' := by
  apply le_antisymm
  · have hle : ∀ i j : Fin 4, i ≠ j → pairwiseMin C ≤ hammingDist (row C' i) (row C' j) := by
      intro i j hij
      rcases hammingDist_row_equiv h with ⟨ρ, hd⟩
      rw [hd i j]
      exact pairwiseMin_le_all (C := C) (i := ρ i) (j := ρ j) (by
        intro h
        exact hij (ρ.injective h))
    rcases pairwiseMin_mem C' with ⟨i, j, hij, hmem⟩
    rw [hmem]
    exact hle i j hij
  · have hle : ∀ i j : Fin 4, i ≠ j → pairwiseMin C' ≤ hammingDist (row C i) (row C j) := by
      intro i j hij
      rcases hammingDist_row_equiv (equivalent_symm h) with ⟨ρ, hd⟩
      rw [hd i j]
      exact pairwiseMin_le_all (C := C') (i := ρ i) (j := ρ j) (by
        intro h
        exact hij (ρ.injective h))
    rcases pairwiseMin_mem C with ⟨i, j, hij, hmem⟩
    rw [hmem]
    exact hle i j hij

/-- The maximum pairwise row distance. -/
def pairwiseMax {n : ℕ} (C : Code n) : ℕ :=
  max (hammingDist (row C ⟨0, by decide⟩) (row C ⟨1, by decide⟩))
    (max (hammingDist (row C ⟨0, by decide⟩) (row C ⟨2, by decide⟩))
      (max (hammingDist (row C ⟨0, by decide⟩) (row C ⟨3, by decide⟩))
        (max (hammingDist (row C ⟨1, by decide⟩) (row C ⟨2, by decide⟩))
          (max (hammingDist (row C ⟨1, by decide⟩) (row C ⟨3, by decide⟩))
            (hammingDist (row C ⟨2, by decide⟩) (row C ⟨3, by decide⟩))))))

/-- `pairwiseMax` is at least every distance between two distinct rows. -/
lemma pairwiseMax_ge_all {n : ℕ} (C : Code n) {i j : Fin 4} (hij : i ≠ j) :
    hammingDist (row C i) (row C j) ≤ pairwiseMax C := by
  fin_cases i <;> fin_cases j <;> simp [pairwiseMax, hammingDist_symm] at hij ⊢

/-- `pairwiseMax` is attained at some pair of distinct rows. -/
lemma pairwiseMax_mem {n : ℕ} (C : Code n) :
    ∃ i j : Fin 4, i ≠ j ∧ pairwiseMax C = hammingDist (row C i) (row C j) := by
  have hcases : pairwiseMax C = hammingDist (row C ⟨0, by decide⟩) (row C ⟨1, by decide⟩) ∨
      pairwiseMax C = hammingDist (row C ⟨0, by decide⟩) (row C ⟨2, by decide⟩) ∨
      pairwiseMax C = hammingDist (row C ⟨0, by decide⟩) (row C ⟨3, by decide⟩) ∨
      pairwiseMax C = hammingDist (row C ⟨1, by decide⟩) (row C ⟨2, by decide⟩) ∨
      pairwiseMax C = hammingDist (row C ⟨1, by decide⟩) (row C ⟨3, by decide⟩) ∨
      pairwiseMax C = hammingDist (row C ⟨2, by decide⟩) (row C ⟨3, by decide⟩) := by
    unfold pairwiseMax
    omega
  rcases hcases with h1 | h2 | h3 | h4 | h5 | h6
  · exact ⟨⟨0, by decide⟩, ⟨1, by decide⟩, by decide, h1⟩
  · exact ⟨⟨0, by decide⟩, ⟨2, by decide⟩, by decide, h2⟩
  · exact ⟨⟨0, by decide⟩, ⟨3, by decide⟩, by decide, h3⟩
  · exact ⟨⟨1, by decide⟩, ⟨2, by decide⟩, by decide, h4⟩
  · exact ⟨⟨1, by decide⟩, ⟨3, by decide⟩, by decide, h5⟩
  · exact ⟨⟨2, by decide⟩, ⟨3, by decide⟩, by decide, h6⟩

/-- `pairwiseMax` is invariant under equivalence. -/
lemma pairwiseMax_equiv {n : ℕ} {C C' : Code n} (h : Equivalent C C') :
    pairwiseMax C = pairwiseMax C' := by
  apply le_antisymm
  · rcases pairwiseMax_mem C with ⟨i, j, hij, hmem⟩
    rw [hmem]
    rcases hammingDist_row_equiv h with ⟨ρ, hd⟩
    have hd' : hammingDist (row C i) (row C j) = hammingDist (row C' (ρ.symm i)) (row C' (ρ.symm j)) := by
      rw [hd (ρ.symm i) (ρ.symm j)]
      simp [ρ.apply_symm_apply]
    rw [hd']
    exact pairwiseMax_ge_all (C := C') (i := ρ.symm i) (j := ρ.symm j) (by
      intro h
      exact hij (ρ.symm.injective h))
  · rcases pairwiseMax_mem C' with ⟨i, j, hij, hmem⟩
    rw [hmem]
    rcases hammingDist_row_equiv h with ⟨ρ, hd⟩
    rw [hd i j]
    exact pairwiseMax_ge_all (C := C) (i := ρ i) (j := ρ j) (by
      intro h
      exact hij (ρ.injective h))

/-- Any distinct-row distance of `linCode a b c hsum` is one of a+b, a+c, b+c. -/
lemma linCode_rowDist_mem {n a b c : ℕ} (hsum : a + b + c = n) {i j : Fin 4} (hij : i ≠ j) :
    hammingDist (row (linCode a b c hsum) i) (row (linCode a b c hsum) j) = a + b ∨
    hammingDist (row (linCode a b c hsum) i) (row (linCode a b c hsum) j) = a + c ∨
    hammingDist (row (linCode a b c hsum) i) (row (linCode a b c hsum) j) = b + c := by
  fin_cases i <;> fin_cases j
  · exfalso; exact hij rfl
  · right; right; exact linCode_hDist_01 hsum
  · right; left; exact linCode_hDist_02 hsum
  · left; exact linCode_hDist_03 hsum
  · right; right; rw [hammingDist_symm]; exact linCode_hDist_01 hsum
  · exfalso; exact hij rfl
  · left; exact linCode_hDist_12 hsum
  · right; left; exact linCode_hDist_13 hsum
  · right; left; rw [hammingDist_symm]; exact linCode_hDist_02 hsum
  · left; rw [hammingDist_symm]; exact linCode_hDist_12 hsum
  · exfalso; exact hij rfl
  · right; right; exact linCode_hDist_23 hsum
  · left; rw [hammingDist_symm]; exact linCode_hDist_03 hsum
  · right; left; rw [hammingDist_symm]; exact linCode_hDist_13 hsum
  · right; right; rw [hammingDist_symm]; exact linCode_hDist_23 hsum
  · exfalso; exact hij rfl

/-- `pairwiseMin` of `linCode a b c hsum` is n − max(a,b,c). -/
lemma linCode_pairwiseMin {n a b c : ℕ} (hsum : a + b + c = n) :
    pairwiseMin (linCode a b c hsum) = n - max a (max b c) := by
  apply le_antisymm
  · have h1 : pairwiseMin (linCode a b c hsum) ≤ a + b := by
      rw [← linCode_hDist_03 hsum]
      exact pairwiseMin_le_all (C := linCode a b c hsum) (i := ⟨0, by decide⟩) (j := ⟨3, by decide⟩) (by decide)
    have h2 : pairwiseMin (linCode a b c hsum) ≤ a + c := by
      rw [← linCode_hDist_13 hsum]
      exact pairwiseMin_le_all (C := linCode a b c hsum) (i := ⟨1, by decide⟩) (j := ⟨3, by decide⟩) (by decide)
    have h3 : pairwiseMin (linCode a b c hsum) ≤ b + c := by
      rw [← linCode_hDist_23 hsum]
      exact pairwiseMin_le_all (C := linCode a b c hsum) (i := ⟨2, by decide⟩) (j := ⟨3, by decide⟩) (by decide)
    omega
  · rcases pairwiseMin_mem (linCode a b c hsum) with ⟨i, j, hij, hmem⟩
    rw [hmem]
    rcases linCode_rowDist_mem hsum hij with hmem' | hmem' | hmem'
    · rw [hmem']; omega
    · rw [hmem']; omega
    · rw [hmem']; omega

/-- `pairwiseMax` of `linCode a b c hsum` is n − min(a,b,c). -/
lemma linCode_pairwiseMax {n a b c : ℕ} (hsum : a + b + c = n) :
    pairwiseMax (linCode a b c hsum) = n - min a (min b c) := by
  apply le_antisymm
  · rcases pairwiseMax_mem (linCode a b c hsum) with ⟨i, j, hij, hmem⟩
    rw [hmem]
    rcases linCode_rowDist_mem hsum hij with hmem' | hmem' | hmem'
    · rw [hmem']; omega
    · rw [hmem']; omega
    · rw [hmem']; omega
  · have h1 : a + b ≤ pairwiseMax (linCode a b c hsum) := by
      rw [← linCode_hDist_03 hsum]
      exact pairwiseMax_ge_all (C := linCode a b c hsum) (i := ⟨0, by decide⟩) (j := ⟨3, by decide⟩) (by decide)
    have h2 : a + c ≤ pairwiseMax (linCode a b c hsum) := by
      rw [← linCode_hDist_13 hsum]
      exact pairwiseMax_ge_all (C := linCode a b c hsum) (i := ⟨1, by decide⟩) (j := ⟨3, by decide⟩) (by decide)
    have h3 : b + c ≤ pairwiseMax (linCode a b c hsum) := by
      rw [← linCode_hDist_23 hsum]
      exact pairwiseMax_ge_all (C := linCode a b c hsum) (i := ⟨2, by decide⟩) (j := ⟨3, by decide⟩) (by decide)
    omega

/-- Equivalent `linCode`s have the same maximum and minimum counts. -/
lemma linCode_equiv_sorted {n a b c A B C : ℕ} (hsum1 : a + b + c = n) (hsum2 : A + B + C = n)
    (h : Equivalent (linCode a b c hsum1) (linCode A B C hsum2)) :
    max a (max b c) = max A (max B C) ∧ min a (min b c) = min A (min B C) ∧
      (a + b + c - max a (max b c) - min a (min b c)) =
        (A + B + C - max A (max B C) - min A (min B C)) := by
  have hminpm : pairwiseMin (linCode a b c hsum1) = pairwiseMin (linCode A B C hsum2) :=
    pairwiseMin_equiv h
  rw [linCode_pairwiseMin hsum1, linCode_pairwiseMin hsum2] at hminpm
  have hmaxpm : pairwiseMax (linCode a b c hsum1) = pairwiseMax (linCode A B C hsum2) :=
    pairwiseMax_equiv h
  rw [linCode_pairwiseMax hsum1, linCode_pairwiseMax hsum2] at hmaxpm
  have hmaxle : max a (max b c) ≤ n := by omega
  have hmaxle' : max A (max B C) ≤ n := by omega
  have hmax : max a (max b c) = max A (max B C) := by omega
  have hminle : min a (min b c) ≤ n := by omega
  have hminle' : min A (min B C) ≤ n := by omega
  have hmin : min a (min b c) = min A (min B C) := by omega
  have hmid : (a + b + c - max a (max b c) - min a (min b c)) =
      (A + B + C - max A (max B C) - min A (min B C)) := by omega
  exact ⟨hmax, hmin, hmid⟩

/-- A `linCode` with a zero count is not equivalent to one with all counts
positive (the canonical optimal linear codes for n > 3 have all three counts
positive). -/
lemma linCode_ne_equiv_of_count_zero {n a b c A B C : ℕ}
    (hsum1 : a + b + c = n) (hsum2 : A + B + C = n)
    (hzero : b = 0 ∨ c = 0) (hpos : 0 < A ∧ 0 < B ∧ 0 < C) :
    ¬ Equivalent (linCode a b c hsum1) (linCode A B C hsum2) := by
  intro h
  have hs := linCode_equiv_sorted hsum1 hsum2 h
  have hmin1 : min a (min b c) = 0 := by
    rcases hzero with hb | hc
    · rw [hb]; simp
    · rw [hc]; simp
  have hmin2 : 1 ≤ min A (min B C) := by omega
  rw [hs.2.1] at hmin1
  omega

/-- The C0-form linear code (1, b, c) with b,c odd is not equivalent to the
canonical optimal code C(k,k,k−1) for n = 3k−1 (k ≥ 2). -/
lemma linCode_ne_equiv_c0form_r2 {n b c k : ℕ} (hsum : 1 + b + c = n) (hsumk : k + k + (k - 1) = n)
    (hb : Odd b) (hc : Odd c) (hk : 2 ≤ k) :
    ¬ Equivalent (linCode 1 b c hsum) (linCode k k (k - 1) hsumk) := by
  intro h
  have hs := linCode_equiv_sorted hsum hsumk h
  have hb1 : 1 ≤ b := by rcases hb with ⟨m, hm⟩; omega
  have hc1 : 1 ≤ c := by rcases hc with ⟨m, hm⟩; omega
  have hmin1 : min 1 (min b c) = 1 := by omega
  have hmineq : k - 1 = 1 := by
    have hm := hs.2.1
    have hkmin : min k (min k (k - 1)) = k - 1 := by omega
    rw [hmin1, hkmin] at hm
    exact hm.symm
  have hk2 : k = 2 := by omega
  have hmaxeq : max b c = 2 := by
    have hm := hs.1
    have hmaxk : max k (max k (k - 1)) = k := by omega
    rw [hmaxk, hk2] at hm
    -- hm : max 1 (max b c) = 2; max 1 (max b c) = max b c
    have hmax1 : max 1 (max b c) = max b c := by omega
    rw [hmax1] at hm
    exact hm
  have hbc : b + c = 4 := by omega
  rcases hb with ⟨m, hm⟩
  rcases hc with ⟨m', hm'⟩
  omega

/-- The C0-form linear code (1, b, c) with b,c odd is not equivalent to the
canonical optimal code C(k+1,k,k) for n = 3k+1 (k ≥ 2). -/
lemma linCode_ne_equiv_c0form_r1a {n b c k : ℕ} (hsum : 1 + b + c = n) (hsumk : k + 1 + k + k = n)
    (hb : Odd b) (hc : Odd c) (hk : 2 ≤ k) :
    ¬ Equivalent (linCode 1 b c hsum) (linCode (k + 1) k k hsumk) := by
  intro h
  have hs := linCode_equiv_sorted hsum hsumk h
  have hb1 : 1 ≤ b := by rcases hb with ⟨m, hm⟩; omega
  have hc1 : 1 ≤ c := by rcases hc with ⟨m, hm⟩; omega
  have hmin1 : min 1 (min b c) = 1 := by omega
  have hm := hs.2.1
  have hkmin : min (k + 1) (min k k) = k := by omega
  rw [hmin1, hkmin] at hm
  omega

/-- The C0-form linear code (1, b, c) with b,c odd is not equivalent to the
canonical optimal code C(k+2,k,k−1) for n = 3k+1 (k ≥ 2). -/
lemma linCode_ne_equiv_c0form_r1b {n b c k : ℕ} (hsum : 1 + b + c = n) (hsumk : k + 2 + k + (k - 1) = n)
    (hb : Odd b) (hc : Odd c) (hk : 2 ≤ k) :
    ¬ Equivalent (linCode 1 b c hsum) (linCode (k + 2) k (k - 1) hsumk) := by
  intro h
  have hs := linCode_equiv_sorted hsum hsumk h
  have hb1 : 1 ≤ b := by rcases hb with ⟨m, hm⟩; omega
  have hc1 : 1 ≤ c := by rcases hc with ⟨m, hm⟩; omega
  -- min: 1 vs k−1; max: max b c vs k+2; middle: n−max−1 vs k
  have hmin1 : min 1 (min b c) = 1 := by omega
  have hmax1 : max 1 (max b c) = max b c := by omega
  have hmineq : k - 1 = 1 := by
    have hm := hs.2.1
    have hkmin : min (k + 2) (min k (k - 1)) = k - 1 := by omega
    rw [hmin1, hkmin] at hm
    exact hm.symm
  have hk2 : k = 2 := by omega
  have hmaxeq : max b c = k + 2 := by
    have hm := hs.1
    have hmaxk : max (k + 2) (max k (k - 1)) = k + 2 := by omega
    rw [hmax1, hmaxk] at hm
    exact hm
  have hbc : b + c = 6 := by omega
  rcases hb with ⟨m, hm⟩
  rcases hc with ⟨m', hm'⟩
  omega

/-- The C0-form linear code (1, b, c) with b,c odd is not equivalent to the
canonical optimal code C(k+1,k+1,k−2) for n = 3k (k ≥ 3). -/
lemma linCode_ne_equiv_c0form_r0a {n b c k : ℕ} (hsum : 1 + b + c = n) (hsumk : (k + 1) + (k + 1) + (k - 2) = n)
    (hb : Odd b) (hc : Odd c) (hk : 3 ≤ k) :
    ¬ Equivalent (linCode 1 b c hsum) (linCode (k + 1) (k + 1) (k - 2) hsumk) := by
  intro h
  have hs := linCode_equiv_sorted hsum hsumk h
  have hb1 : 1 ≤ b := by rcases hb with ⟨m, hm⟩; omega
  have hc1 : 1 ≤ c := by rcases hc with ⟨m, hm⟩; omega
  have hmin1 : min 1 (min b c) = 1 := by omega
  have hmax1 : max 1 (max b c) = max b c := by omega
  by_cases hk4 : 4 ≤ k
  · -- min differs: 1 vs k−2 ≥ 2
    have hm := hs.2.1
    have hkmin : min (k + 1) (min (k + 1) (k - 2)) = k - 2 := by omega
    rw [hmin1, hkmin] at hm
    omega
  · -- k = 3: max differs
    have hk3 : k = 3 := by omega
    have hm := hs.1
    have hmaxk : max (k + 1) (max (k + 1) (k - 2)) = k + 1 := by omega
    rw [hmax1, hmaxk, hk3] at hm
    have hmaxeq : max b c = 4 := by omega
    have hbc : b + c = 8 := by omega
    rcases hb with ⟨m, hm⟩
    rcases hc with ⟨m', hm'⟩
    omega

/-- The C0-form linear code (1, b, c) with b,c odd is not equivalent to the
canonical optimal code C(k+1,k,k−1) for n = 3k (k ≥ 3). -/
lemma linCode_ne_equiv_c0form_r0b {n b c k : ℕ} (hsum : 1 + b + c = n) (hsumk : k + 1 + k + (k - 1) = n)
    (hb : Odd b) (hc : Odd c) (hk : 3 ≤ k) :
    ¬ Equivalent (linCode 1 b c hsum) (linCode (k + 1) k (k - 1) hsumk) := by
  intro h
  have hs := linCode_equiv_sorted hsum hsumk h
  have hb1 : 1 ≤ b := by rcases hb with ⟨m, hm⟩; omega
  have hc1 : 1 ≤ c := by rcases hc with ⟨m, hm⟩; omega
  have hmin1 : min 1 (min b c) = 1 := by omega
  have hm := hs.2.1
  have hkmin : min (k + 1) (min k (k - 1)) = k - 1 := by omega
  rw [hmin1, hkmin] at hm
  omega

/-- The number of columns of weight 0 or 4 (zero or all-ones columns). -/
def weight04Count {n : ℕ} (C : Code n) : ℕ :=
  (Finset.univ.filter fun t : Fin n => colWeight (C t) = 0 ∨ colWeight (C t) = 4).card

/-- The weight-0/4 count is invariant under equivalence. -/
lemma weight04Count_equiv {n : ℕ} {C C' : Code n} (h : Equivalent C C') :
    weight04Count C = weight04Count C' := by
  rcases h with ⟨ρ, p, f, hh⟩
  unfold weight04Count
  have hiff : ∀ t : Fin n, (colWeight (C' (p t)) = 0 ∨ colWeight (C' (p t)) = 4) ↔
      (colWeight (C t) = 0 ∨ colWeight (C t) = 4) := by
    intro t
    have hrel : colWeight (C' (p t)) = colWeight (C t) ∨
        colWeight (C' (p t)) = 4 - colWeight (C t) := by
      rw [hh t]
      cases hf : f t <;> simp [colWeight_rowPermute, colWeight_flip]
    have hle : colWeight (C t) ≤ 4 := colWeight_le_4 (C t)
    constructor
    · intro hw
      rcases hw with hw0 | hw4
      · rcases hrel with h | h
        · left; omega
        · right; omega
      · rcases hrel with h | h
        · right; omega
        · left; omega
    · intro hw
      rcases hw with hw0 | hw4
      · rcases hrel with h | h
        · left; omega
        · right; omega
      · rcases hrel with h | h
        · right; omega
        · left; omega
  apply Finset.card_bij (fun t _ => p t)
  · intro t ht
    exact Finset.mem_filter.mpr ⟨by simp, (hiff t).mpr (Finset.mem_filter.mp ht).2⟩
  · intro a _ b _ hab
    exact p.injective hab
  · intro b hb
    refine ⟨p.symm b, ?_, by simp⟩
    have hb' : (colWeight (C' (p (p.symm b))) = 0 ∨ colWeight (C' (p (p.symm b))) = 4) := by
      simpa using (Finset.mem_filter.mp hb).2
    exact Finset.mem_filter.mpr ⟨by simp, (hiff (p.symm b)).mp hb'⟩

-- native_decide: Mechanical · n=any · checked 2026-08-27
/-- A C0-form code's weight-0/4 columns are exactly its type-0 columns. -/
lemma weight04Count_c0form {n : ℕ} (C : Code n) (h : C0form C) :
    weight04Count C = count C 0 := by
  unfold weight04Count
  rw [count_eq_card]
  congr 1
  ext t
  constructor
  · intro hw
    have hw' := (Finset.mem_filter.mp hw).2
    rcases C0form_types C h t with h0 | h5 | h6
    · exact Finset.mem_filter.mpr ⟨by simp, h0⟩
    · exfalso
      have hc5 : C t = colOfNat 5 := by rw [← colOfNat_colVal (C t), h5]
      have hw5 : colWeight (C t) = 2 := by rw [hc5]; native_decide
      rcases hw' with h0' | h4' <;> omega
    · exfalso
      have hc6 : C t = colOfNat 6 := by rw [← colOfNat_colVal (C t), h6]
      have hw6 : colWeight (C t) = 2 := by rw [hc6]; native_decide
      rcases hw' with h0' | h4' <;> omega
  · intro hv
    have hv' := (Finset.mem_filter.mp hv).2
    have hc : C t = col0 := (colVal_eq_zero_iff_col0 (C t)).mp hv'
    exact Finset.mem_filter.mpr ⟨by simp, by rw [hc]; native_decide⟩

-- native_decide: Mechanical · n=any · checked 2026-08-27
/-- Replacing a type-0 column by type 3 lowers the weight-0/4 count by one. -/
lemma weight04Count_replaced {n : ℕ} (C : Code n) (t : Fin n) (ht : C t = col0) :
    weight04Count (replaceColumn C t col3) = weight04Count C - 1 := by
  unfold weight04Count
  have hw0 : colWeight col0 = 0 := by native_decide
  have hmem : t ∈ (Finset.univ.filter fun u : Fin n => colWeight (C u) = 0 ∨ colWeight (C u) = 4) := by
    exact Finset.mem_filter.mpr ⟨by simp, Or.inl (by rw [ht]; exact hw0)⟩
  have hfilter : (Finset.univ.filter fun u : Fin n =>
      colWeight (replaceColumn C t col3 u) = 0 ∨ colWeight (replaceColumn C t col3 u) = 4)
      = (Finset.univ.filter fun u : Fin n => colWeight (C u) = 0 ∨ colWeight (C u) = 4).erase t := by
    ext u
    constructor
    · intro hu
      by_cases hut : u = t
      · subst u
        have hc : replaceColumn C t col3 t = col3 := by simp [replaceColumn]
        have hu' := (Finset.mem_filter.mp hu).2
        rw [hc] at hu'
        have hw3 : colWeight col3 = 2 := by native_decide
        rcases hu' with h0' | h4' <;> omega
      · have hsame : replaceColumn C t col3 u = C u := by simp [replaceColumn, hut]
        exact Finset.mem_erase.mpr ⟨hut, Finset.mem_filter.mpr ⟨by simp, by simpa [hsame] using hu⟩⟩
    · intro hu
      rcases Finset.mem_erase.mp hu with ⟨hut, hu0⟩
      have hsame : replaceColumn C t col3 u = C u := by simp [replaceColumn, hut]
      exact Finset.mem_filter.mpr ⟨by simp, by simpa [hsame] using (Finset.mem_filter.mp hu0).2⟩
  rw [hfilter, Finset.card_erase_of_mem hmem]

/-- Replacing a 0-column of a C0-form code with |0| ≥ 2 breaks
C0-form-equivalence: the result is not equivalent to any C0-form code. -/
lemma c0form_replaced_not_equiv_c0form {n : ℕ} (C : Code n) (h : C0form C) (t : Fin n)
    (ht : C t = col0) (h2 : 2 ≤ count C 0) :
    ¬ ∃ C0 : Code n, Equivalent (replaceColumn C t col3) C0 ∧ C0form C0 := by
  rintro ⟨C0, hEq, hC0⟩
  have hw := weight04Count_equiv hEq
  have hw1' := weight04Count_replaced C t ht
  rw [weight04Count_c0form C h] at hw1'
  have hw1 : weight04Count (replaceColumn C t col3) = count C 0 - 1 := hw1'
  have hw2 : weight04Count C0 = count C0 0 := weight04Count_c0form C0 hC0
  have hcnt : count C 0 + count C 5 + count C 6 = n := h.1
  have hcnt0 : count C0 0 + count C0 5 + count C0 6 = n := hC0.1
  have hparC : Even (count C 5 + count C 6) := by
    rcases h.2.1 with ⟨m, hm⟩
    rcases h.2.2 with ⟨m', hm'⟩
    refine ⟨m + m' + 1, by omega⟩
  have hparC0 : Even (count C0 5 + count C0 6) := by
    rcases hC0.2.1 with ⟨m, hm⟩
    rcases hC0.2.2 with ⟨m', hm'⟩
    refine ⟨m + m' + 1, by omega⟩
  have hsum : count C0 5 + count C0 6 = count C 5 + count C 6 + 1 := by omega
  rw [hsum] at hparC0
  rcases hparC0 with ⟨k, hk⟩
  rcases hparC with ⟨l, hl⟩
  omega

/-- n = 3k−1 when n ≡ 2 mod 3. -/
lemma n_eq_3k_sub1 {n : ℕ} (h : n % 3 = 2) :
    n = ((n + 1) / 3) + ((n + 1) / 3) + (((n + 1) / 3) - 1) := by
  have hn : n = 3 * (n / 3) + 2 := by
    rw [← Nat.mod_add_div n 3]
    omega
  have hk : (n + 1) / 3 = n / 3 + 1 := by
    have h1 : n + 1 = 3 * (n / 3 + 1) := by omega
    rw [h1, Nat.mul_comm, Nat.mul_div_left (n / 3 + 1) (by decide : 0 < 3)]
  omega

/-- n = 3k when n ≡ 0 mod 3. -/
lemma n_eq_3k {n : ℕ} (h : n % 3 = 0) (hn1 : 1 ≤ n) :
    n = n / 3 + 1 + n / 3 + (n / 3 - 1) := by
  have hn : n = 3 * (n / 3) := by
    rw [← Nat.mod_add_div n 3]
    omega
  omega

/-- n = 3k+1 when n ≡ 1 mod 3. -/
lemma n_eq_3k_add1 {n : ℕ} (h : n % 3 = 1) (_hn1 : 1 ≤ n) :
    n = (n - 1) / 3 + 1 + (n - 1) / 3 + (n - 1) / 3 := by
  have hn : n = 3 * (n / 3) + 1 := by
    rw [← Nat.mod_add_div n 3]
    omega
  have hk : (n - 1) / 3 = n / 3 := by
    have h1 : n - 1 = 3 * (n / 3) := by omega
    rw [h1, Nat.mul_comm, Nat.mul_div_left (n / 3) (by decide : 0 < 3)]
  omega

/-- (n+1)/3 = n/3 + 1 when n ≡ 2 mod 3. -/
lemma n_plus1_div3_of_mod2 {n : ℕ} (h : n % 3 = 2) : (n + 1) / 3 = n / 3 + 1 := by
  have hn : n = 3 * (n / 3) + 2 := by rw [← Nat.mod_add_div n 3]; omega
  have h1 : n + 1 = 3 * (n / 3 + 1) := by omega
  rw [h1, Nat.mul_comm, Nat.mul_div_left (n / 3 + 1) (by decide : 0 < 3)]

/-- (n−1)/3 = n/3 when n ≡ 1 mod 3. -/
lemma n_minus1_div3_of_mod1 {n : ℕ} (h : n % 3 = 1) (_hn1 : 1 ≤ n) : (n - 1) / 3 = n / 3 := by
  have hn : n = 3 * (n / 3) + 1 := by rw [← Nat.mod_add_div n 3]; omega
  have h1 : n - 1 = 3 * (n / 3) := by omega
  rw [h1, Nat.mul_comm, Nat.mul_div_left (n / 3) (by decide : 0 < 3)]

/-- Casting a `linCode` along the blocklength equality agrees with the
proof-cast version. -/
lemma cast_linCode {m n a b c : ℕ} (h1 : m = n) (hsum1 : a + b + c = m) (hsum2 : a + b + c = n) :
    cast (congrArg Code h1) (linCode a b c hsum1) = linCode a b c hsum2 := by
  unfold linCode
  rw [cast_cast]

/-- `linCode a b c hsum` is linear when at least two of the counts are
positive. -/
lemma isLinear_linCode_of_two_pos {n a b c : ℕ} (hsum : a + b + c = n)
    (hpos : (0 < a ∧ 0 < b) ∨ (0 < a ∧ 0 < c) ∨ (0 < b ∧ 0 < c)) :
    IsLinear (linCode a b c hsum) := by
  constructor
  · intro t
    have hmem := linear_col_type (n3 := a) (n5 := b) (n6 := c)
      (Fin.cast hsum.symm t)
    -- linCode a b c hsum t = linearCode a b c (cast t)
    have hc : linCode a b c hsum t = linearCode a b c (Fin.cast hsum.symm t) := by
      unfold linCode
      rw [cast_code_apply hsum]
    rcases hmem with h3 | h5 | h6
    · right; left; rw [hc, h3]
    · right; right; left; rw [hc, h5]
    · right; right; right; rw [hc, h6]
  · rcases hpos with ⟨ha, hb⟩ | ⟨ha, hc⟩ | ⟨hb, hc⟩
    · left; constructor
      · simpa [count_linCode_3 hsum] using ha
      · simpa [count_linCode_5 hsum] using hb
    · right; left; constructor
      · simpa [count_linCode_3 hsum] using ha
      · simpa [count_linCode_6 hsum] using hc
    · right; right; constructor
      · simpa [count_linCode_5 hsum] using hb
      · simpa [count_linCode_6 hsum] using hc

/-- A linear code with counts (a,b,c), n odd > 3 and b = 0 or c = 0 is
strictly dominated by the canonical optimal linear code. -/
lemma linear_zero_count_not_optimal {n : ℕ} (hn : 3 < n) (hodd : Odd n) {a b c : ℕ}
    (hsum : a + b + c = n) (hpos : (0 < a ∧ 0 < b) ∨ (0 < a ∧ 0 < c) ∨ (0 < b ∧ 0 < c))
    (hzero : b = 0 ∨ c = 0) :
    ∃ O : Code n, IsLinear O ∧ UniversalStrictBetter O (linCode a b c hsum) := by
  have hlin : IsLinear (linCode a b c hsum) := isLinear_linCode_of_two_pos hsum hpos
  by_cases h2 : n % 3 = 2
  · have hsumk : (n + 1) / 3 + (n + 1) / 3 + ((n + 1) / 3 - 1) = n := (n_eq_3k_sub1 h2).symm
    have hsum' : a + b + c = (n + 1) / 3 + (n + 1) / 3 + ((n + 1) / 3 - 1) := by omega
    have hk1 : 1 ≤ (n + 1) / 3 := by
      rw [n_plus1_div3_of_mod2 h2]
      have hn3 : 3 * (n / 3) + 2 = n := by rw [← Nat.mod_add_div n 3]; omega
      have hq : 1 ≤ n / 3 := by omega
      omega
    have hlin' : IsLinear (linCode a b c hsum') := isLinear_linCode_of_two_pos hsum' hpos
    have hne : ¬ Equivalent (linCode ((n + 1) / 3) ((n + 1) / 3) (((n + 1) / 3) - 1) rfl)
        (linCode a b c hsum') := by
      intro h
      exact (linCode_ne_equiv_of_count_zero hsum' rfl hzero ⟨by omega, by omega, by omega⟩)
        (equivalent_symm h)
    have hdom' : UniversalStrictBetter (linCode ((n + 1) / 3) ((n + 1) / 3) (((n + 1) / 3) - 1) rfl)
        (linCode a b c hsum') :=
      linear_opt_residue2 (hk := hk1) (D := linCode a b c hsum') hlin' hne
    have hdom : UniversalStrictBetter
        (cast (congrArg Code hsumk) (linCode ((n + 1) / 3) ((n + 1) / 3) (((n + 1) / 3) - 1) rfl))
        (cast (congrArg Code hsumk) (linCode a b c hsum')) :=
      universalStrictBetter_of_cast hsumk hdom'
    exact ⟨linCode ((n + 1) / 3) ((n + 1) / 3) (((n + 1) / 3) - 1) hsumk,
      isLinear_linCode (a := (n + 1) / 3) (b := (n + 1) / 3) (c := ((n + 1) / 3) - 1)
        (by omega) (by omega) hsumk,
      by simpa [linCode] using hdom⟩
  · by_cases h0 : n % 3 = 0
    · have hk2 : 2 ≤ n / 3 := by
        have hn3 : 3 * (n / 3) = n := by rw [← Nat.mod_add_div n 3]; omega
        have hnd : 3 * (n / 3) > 3 := by omega
        omega
      have hk3 : 3 ≤ n / 3 := by
        rcases hodd with ⟨m, hm⟩
        by_contra hnot
        have hn3 : 3 * (n / 3) = n := by rw [← Nat.mod_add_div n 3]; omega
        omega
      have hsumk : n / 3 + 1 + n / 3 + (n / 3 - 1) = n := (n_eq_3k h0 (by omega)).symm
      have hsum' : a + b + c = n / 3 + 1 + n / 3 + (n / 3 - 1) := by omega
      have hlin' : IsLinear (linCode a b c hsum') := isLinear_linCode_of_two_pos hsum' hpos
      have hsumI1 : (n / 3 + 1) + (n / 3 + 1) + (n / 3 - 2) = n / 3 + 1 + n / 3 + (n / 3 - 1) := by omega
      have hsumI2 : (n / 3 + 1) + n / 3 + (n / 3 - 1) = n / 3 + 1 + n / 3 + (n / 3 - 1) := rfl
      have hne1 : ¬ Equivalent (linCode (n / 3 + 1) (n / 3 + 1) (n / 3 - 2) hsumI1)
          (linCode a b c hsum') := by
        intro h
        exact (linCode_ne_equiv_of_count_zero hsum' hsumI1 hzero ⟨by omega, by omega, by omega⟩)
          (equivalent_symm h)
      have hne2 : ¬ Equivalent (linCode (n / 3 + 1) (n / 3) (n / 3 - 1) hsumI2)
          (linCode a b c hsum') := by
        intro h
        exact (linCode_ne_equiv_of_count_zero hsum' hsumI2 hzero ⟨by omega, by omega, by omega⟩)
          (equivalent_symm h)
      have hres0' := (linear_opt_residue0 (hk := hk2)).1
      have hres0 := hres0' (D := linCode a b c hsum') hlin' hne1 hne2
      have hdom : UniversalStrictBetter (linCode (n / 3 + 1) (n / 3 + 1) (n / 3 - 2) hsumI1)
          (linCode a b c hsum') :=
        hres0
      have hdomn : UniversalStrictBetter
          (cast (congrArg Code hsumk) (linCode (n / 3 + 1) (n / 3 + 1) (n / 3 - 2) hsumI1))
          (cast (congrArg Code hsumk) (linCode a b c hsum')) :=
        universalStrictBetter_of_cast hsumk hdom
      exact ⟨linCode (n / 3 + 1) (n / 3 + 1) (n / 3 - 2) (by omega : (n / 3 + 1) + (n / 3 + 1) + (n / 3 - 2) = n),
        isLinear_linCode (a := n / 3 + 1) (b := n / 3 + 1) (c := n / 3 - 2)
          (by omega) (by omega) (by omega : (n / 3 + 1) + (n / 3 + 1) + (n / 3 - 2) = n), by
          rw [cast_linCode hsumk hsumI1 (by omega : (n / 3 + 1) + (n / 3 + 1) + (n / 3 - 2) = n),
            cast_linCode hsumk hsum' hsum] at hdomn
          exact hdomn⟩
    · have hk2 : 2 ≤ (n - 1) / 3 := by
        rw [n_minus1_div3_of_mod1 (by omega : n % 3 = 1) (by omega : 1 ≤ n)]
        have hn3 : 3 * (n / 3) + 1 = n := by rw [← Nat.mod_add_div n 3]; omega
        rcases hodd with ⟨m, hm⟩
        by_contra hnot
        omega
      have hsumk : (n - 1) / 3 + 1 + (n - 1) / 3 + (n - 1) / 3 = n := (n_eq_3k_add1 (by omega : n % 3 = 1) (by omega : 1 ≤ n)).symm
      have hsum' : a + b + c = (n - 1) / 3 + 1 + (n - 1) / 3 + (n - 1) / 3 := by omega
      have hlin' : IsLinear (linCode a b c hsum') := isLinear_linCode_of_two_pos hsum' hpos
      have hsumI1 : ((n - 1) / 3 + 1) + (n - 1) / 3 + (n - 1) / 3 = (n - 1) / 3 + 1 + (n - 1) / 3 + (n - 1) / 3 := rfl
      have hsumI2 : ((n - 1) / 3 + 2) + (n - 1) / 3 + ((n - 1) / 3 - 1) = (n - 1) / 3 + 1 + (n - 1) / 3 + (n - 1) / 3 := by omega
      have hne1 : ¬ Equivalent (linCode ((n - 1) / 3 + 1) ((n - 1) / 3) ((n - 1) / 3) hsumI1)
          (linCode a b c hsum') := by
        intro h
        exact (linCode_ne_equiv_of_count_zero hsum' hsumI1 hzero ⟨by omega, by omega, by omega⟩)
          (equivalent_symm h)
      have hne2 : ¬ Equivalent (linCode ((n - 1) / 3 + 2) ((n - 1) / 3) ((n - 1) / 3 - 1) hsumI2)
          (linCode a b c hsum') := by
        intro h
        exact (linCode_ne_equiv_of_count_zero hsum' hsumI2 hzero ⟨by omega, by omega, by omega⟩)
          (equivalent_symm h)
      have hres1' := (linear_opt_residue1 (hk := (by omega : 1 ≤ (n - 1) / 3))).1
      have hres1 := hres1' (D := linCode a b c hsum') hlin' hne1 hne2
      have hdom : UniversalStrictBetter (linCode ((n - 1) / 3 + 1) ((n - 1) / 3) ((n - 1) / 3) hsumI1)
          (linCode a b c hsum') :=
        hres1
      have hdomn : UniversalStrictBetter
          (cast (congrArg Code hsumk) (linCode ((n - 1) / 3 + 1) ((n - 1) / 3) ((n - 1) / 3) hsumI1))
          (cast (congrArg Code hsumk) (linCode a b c hsum')) :=
        universalStrictBetter_of_cast hsumk hdom
      exact ⟨linCode ((n - 1) / 3 + 1) ((n - 1) / 3) ((n - 1) / 3) (by omega : ((n - 1) / 3 + 1) + (n - 1) / 3 + (n - 1) / 3 = n),
        isLinear_linCode (a := (n - 1) / 3 + 1) (b := (n - 1) / 3) (c := (n - 1) / 3)
          (by omega) (by omega) (by omega : ((n - 1) / 3 + 1) + (n - 1) / 3 + (n - 1) / 3 = n), by
          rw [cast_linCode hsumk hsumI1 (by omega : ((n - 1) / 3 + 1) + (n - 1) / 3 + (n - 1) / 3 = n),
            cast_linCode hsumk hsum' hsum] at hdomn
          exact hdomn⟩

/-- The C0-form linear code (1, b, c) with b,c odd and n odd > 3 is strictly
dominated by the canonical optimal linear code. -/
lemma linear_c0form_not_optimal {n : ℕ} (hn : 3 < n) (hodd : Odd n) {b c : ℕ}
    (hsum : 1 + b + c = n) (hb : Odd b) (hc : Odd c) :
    ∃ O : Code n, IsLinear O ∧ UniversalStrictBetter O (linCode 1 b c hsum) := by
  have hpos : (0 < 1 ∧ 0 < b) ∨ (0 < 1 ∧ 0 < c) ∨ (0 < b ∧ 0 < c) :=
    Or.inl ⟨by norm_num, by rcases hb with ⟨m, hm⟩; omega⟩
  have hlin : IsLinear (linCode 1 b c hsum) := isLinear_linCode_of_two_pos hsum hpos
  by_cases h2 : n % 3 = 2
  · have hsumk : (n + 1) / 3 + (n + 1) / 3 + ((n + 1) / 3 - 1) = n := (n_eq_3k_sub1 h2).symm
    have hsum' : 1 + b + c = (n + 1) / 3 + (n + 1) / 3 + ((n + 1) / 3 - 1) := by omega
    have hlin' : IsLinear (linCode 1 b c hsum') := isLinear_linCode_of_two_pos hsum' hpos
    have hk1 : 1 ≤ (n + 1) / 3 := by
      rw [n_plus1_div3_of_mod2 h2]
      have hn3 : 3 * (n / 3) + 2 = n := by rw [← Nat.mod_add_div n 3]; omega
      have hq : 1 ≤ n / 3 := by omega
      omega
    have hk2 : 2 ≤ (n + 1) / 3 := by
      rw [n_plus1_div3_of_mod2 h2]
      have hn3 : 3 * (n / 3) + 2 = n := by rw [← Nat.mod_add_div n 3]; omega
      have hq : 1 ≤ n / 3 := by omega
      omega
    have hne : ¬ Equivalent (linCode ((n + 1) / 3) ((n + 1) / 3) (((n + 1) / 3) - 1) rfl)
        (linCode 1 b c hsum') := by
      intro h
      exact (linCode_ne_equiv_c0form_r2 hsum' rfl hb hc hk2) (equivalent_symm h)
    have hdom' : UniversalStrictBetter (linCode ((n + 1) / 3) ((n + 1) / 3) (((n + 1) / 3) - 1) rfl)
        (linCode 1 b c hsum') :=
      linear_opt_residue2 (hk := hk1) (D := linCode 1 b c hsum') hlin' hne
    have hdom : UniversalStrictBetter
        (cast (congrArg Code hsumk) (linCode ((n + 1) / 3) ((n + 1) / 3) (((n + 1) / 3) - 1) rfl))
        (cast (congrArg Code hsumk) (linCode 1 b c hsum')) :=
      universalStrictBetter_of_cast hsumk hdom'
    exact ⟨linCode ((n + 1) / 3) ((n + 1) / 3) (((n + 1) / 3) - 1) hsumk,
      isLinear_linCode (a := (n + 1) / 3) (b := (n + 1) / 3) (c := ((n + 1) / 3) - 1)
        (by omega) (by omega) hsumk,
      by simpa [linCode] using hdom⟩
  · by_cases h0 : n % 3 = 0
    · have hk3 : 3 ≤ n / 3 := by
        rcases hodd with ⟨m, hm⟩
        by_contra hnot
        have hn3 : 3 * (n / 3) = n := by rw [← Nat.mod_add_div n 3]; omega
        omega
      have hsumk : n / 3 + 1 + n / 3 + (n / 3 - 1) = n := (n_eq_3k h0 (by omega)).symm
      have hsum' : 1 + b + c = n / 3 + 1 + n / 3 + (n / 3 - 1) := by omega
      have hlin' : IsLinear (linCode 1 b c hsum') := isLinear_linCode_of_two_pos hsum' hpos
      have hsumI1 : (n / 3 + 1) + (n / 3 + 1) + (n / 3 - 2) = n / 3 + 1 + n / 3 + (n / 3 - 1) := by omega
      have hsumI2 : (n / 3 + 1) + n / 3 + (n / 3 - 1) = n / 3 + 1 + n / 3 + (n / 3 - 1) := rfl
      have hne1 : ¬ Equivalent (linCode (n / 3 + 1) (n / 3 + 1) (n / 3 - 2) hsumI1)
          (linCode 1 b c hsum') := by
        intro h
        exact (linCode_ne_equiv_c0form_r0a hsum' hsumI1 hb hc hk3) (equivalent_symm h)
      have hne2 : ¬ Equivalent (linCode (n / 3 + 1) (n / 3) (n / 3 - 1) hsumI2)
          (linCode 1 b c hsum') := by
        intro h
        exact (linCode_ne_equiv_c0form_r0b hsum' hsumI2 hb hc hk3) (equivalent_symm h)
      have hres0' := (linear_opt_residue0 (hk := (by omega : 2 ≤ n / 3))).1
      have hres0 := hres0' (D := linCode 1 b c hsum') hlin' hne1 hne2
      have hdom : UniversalStrictBetter (linCode (n / 3 + 1) (n / 3 + 1) (n / 3 - 2) hsumI1)
          (linCode 1 b c hsum') := hres0
      have hdomn : UniversalStrictBetter
          (cast (congrArg Code hsumk) (linCode (n / 3 + 1) (n / 3 + 1) (n / 3 - 2) hsumI1))
          (cast (congrArg Code hsumk) (linCode 1 b c hsum')) :=
        universalStrictBetter_of_cast hsumk hdom
      exact ⟨linCode (n / 3 + 1) (n / 3 + 1) (n / 3 - 2) (by omega : (n / 3 + 1) + (n / 3 + 1) + (n / 3 - 2) = n),
        isLinear_linCode (a := n / 3 + 1) (b := n / 3 + 1) (c := n / 3 - 2)
          (by omega) (by omega) (by omega : (n / 3 + 1) + (n / 3 + 1) + (n / 3 - 2) = n), by
          rw [cast_linCode hsumk hsumI1 (by omega : (n / 3 + 1) + (n / 3 + 1) + (n / 3 - 2) = n),
            cast_linCode hsumk hsum' hsum] at hdomn
          exact hdomn⟩
    · have hk2 : 2 ≤ (n - 1) / 3 := by
        rw [n_minus1_div3_of_mod1 (by omega : n % 3 = 1) (by omega : 1 ≤ n)]
        have hn3 : 3 * (n / 3) + 1 = n := by rw [← Nat.mod_add_div n 3]; omega
        rcases hodd with ⟨m, hm⟩
        by_contra hnot
        omega
      have hsumk : (n - 1) / 3 + 1 + (n - 1) / 3 + (n - 1) / 3 = n := (n_eq_3k_add1 (by omega : n % 3 = 1) (by omega : 1 ≤ n)).symm
      have hsum' : 1 + b + c = (n - 1) / 3 + 1 + (n - 1) / 3 + (n - 1) / 3 := by omega
      have hlin' : IsLinear (linCode 1 b c hsum') := isLinear_linCode_of_two_pos hsum' hpos
      have hsumI1 : ((n - 1) / 3 + 1) + (n - 1) / 3 + (n - 1) / 3 = (n - 1) / 3 + 1 + (n - 1) / 3 + (n - 1) / 3 := rfl
      have hsumI2 : ((n - 1) / 3 + 2) + (n - 1) / 3 + ((n - 1) / 3 - 1) = (n - 1) / 3 + 1 + (n - 1) / 3 + (n - 1) / 3 := by omega
      have hne1 : ¬ Equivalent (linCode ((n - 1) / 3 + 1) ((n - 1) / 3) ((n - 1) / 3) hsumI1)
          (linCode 1 b c hsum') := by
        intro h
        exact (linCode_ne_equiv_c0form_r1a hsum' hsumI1 hb hc hk2) (equivalent_symm h)
      have hne2 : ¬ Equivalent (linCode ((n - 1) / 3 + 2) ((n - 1) / 3) ((n - 1) / 3 - 1) hsumI2)
          (linCode 1 b c hsum') := by
        intro h
        exact (linCode_ne_equiv_c0form_r1b hsum' hsumI2 hb hc hk2) (equivalent_symm h)
      have hres1' := (linear_opt_residue1 (hk := (by omega : 1 ≤ (n - 1) / 3))).1
      have hres1 := hres1' (D := linCode 1 b c hsum') hlin' hne1 hne2
      have hdom : UniversalStrictBetter (linCode ((n - 1) / 3 + 1) ((n - 1) / 3) ((n - 1) / 3) hsumI1)
          (linCode 1 b c hsum') := hres1
      have hdomn : UniversalStrictBetter
          (cast (congrArg Code hsumk) (linCode ((n - 1) / 3 + 1) ((n - 1) / 3) ((n - 1) / 3) hsumI1))
          (cast (congrArg Code hsumk) (linCode 1 b c hsum')) :=
        universalStrictBetter_of_cast hsumk hdom
      exact ⟨linCode ((n - 1) / 3 + 1) ((n - 1) / 3) ((n - 1) / 3) (by omega : ((n - 1) / 3 + 1) + (n - 1) / 3 + (n - 1) / 3 = n),
        isLinear_linCode (a := (n - 1) / 3 + 1) (b := (n - 1) / 3) (c := (n - 1) / 3)
          (by omega) (by omega) (by omega : ((n - 1) / 3 + 1) + (n - 1) / 3 + (n - 1) / 3 = n), by
          rw [cast_linCode hsumk hsumI1 (by omega : ((n - 1) / 3 + 1) + (n - 1) / 3 + (n - 1) / 3 = n),
            cast_linCode hsumk hsum' hsum] at hdomn
          exact hdomn⟩
/-- "No strictly better code" transports through λ-equality. -/
lemma noStrict_of_equal {n : ℕ} {D C : Code n} (hEq : UniversalEqual D C)
    (hno : ∀ E : Code n, UniversalStrictBetter E C → False) :
    ∀ E : Code n, UniversalStrictBetter E D → False := by
  intro E hE
  apply hno E
  intro ε h0 h1
  have hl : lambda D ε = lambda C ε := hEq ε h0 h1
  rw [← hl]
  exact hE ε h0 h1

/-- A code with a type-0 column is not optimal for n > 3 (proof of
`thm:nbig3` (Theorem 3), using `thm:0column` (Theorem 6) and `cor:0col`
(Corollary 7); the C0-form case reduces to a strictly dominated linear
code). -/
-- native_decide: Mechanical · n=any · checked 2026-08-27
lemma zero_column_not_optimal {n : ℕ} (hn : 3 < n) {C : Code n}
    (hnoStrict : ∀ D : Code n, UniversalStrictBetter D C → False)
    (t : Fin n) (ht : C t = col0) : False := by
  have h0pos : 1 ≤ count C 0 := count_pos_of_colVal C t (by rw [ht]; native_decide)
  by_cases hC0 : ∃ C0, Equivalent C C0 ∧ C0form C0
  · rcases hC0 with ⟨C0, hEq, hC0f⟩
    have hnoStrictC0 : ∀ D : Code n, UniversalStrictBetter D C0 → False :=
      noStrict_of_equiv hnoStrict hEq
    have h0posC0 : 1 ≤ count C0 0 := by
      have hwC : 1 ≤ weight04Count C := by
        unfold weight04Count
        have hmem : t ∈ (Finset.univ.filter fun u : Fin n => colWeight (C u) = 0 ∨ colWeight (C u) = 4) := by
          exact Finset.mem_filter.mpr ⟨by simp, Or.inl (by rw [ht]; native_decide)⟩
        exact Nat.succ_le_of_lt (Finset.card_pos.mpr ⟨t, hmem⟩)
      have hw0 : count C0 0 = weight04Count C :=
        ((weight04Count_equiv hEq).trans (weight04Count_c0form C0 hC0f)).symm
      rw [hw0]
      exact hwC
    rcases exists_col_of_colVal C0 0 h0posC0 with ⟨t0, ht0⟩
    have ht0' : C0 t0 = col0 := (colVal_eq_zero_iff_col0 (C0 t0)).mp ht0
    let L1 : Code n := replaceColumn C0 t0 col3
    have hEqL1 : UniversalEqual L1 C0 :=
      (zero_column C0 t0 ht0' ⟨C0, equivalent_refl C0, hC0f⟩ col3)
    have hnoStrictL1 : ∀ D : Code n, UniversalStrictBetter D L1 → False :=
      noStrict_of_equal hEqL1 hnoStrictC0
    by_cases h1 : count C0 0 = 1
    · have hc0L1 : count L1 0 = 0 := by
        have hc := count_replace_dec C0 t0 col3 0 (by rw [ht0']; native_decide) (by native_decide)
        rw [hc, h1]
      have hc3 : count L1 3 = 1 := by
        have hc := count_replace_inc C0 t0 col3 3 (by rw [ht0']; native_decide) (by native_decide)
        rw [hc]
        have h3z : count C0 3 = 0 := by
          rw [count_eq_card, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
          intro u hu
          have hcv : colVal (C0 u) = 3 := (Finset.mem_filter.mp hu).2
          rcases C0form_types C0 hC0f u with h0 | h5 | h6
          · rw [h0] at hcv; norm_num at hcv
          · rw [h5] at hcv; norm_num at hcv
          · rw [h6] at hcv; norm_num at hcv
        omega
      have hc5 : count L1 5 = count C0 5 :=
        count_replace_eq C0 t0 col3 5 (by rw [ht0']; native_decide) (by native_decide)
      have hc6 : count L1 6 = count C0 6 :=
        count_replace_eq C0 t0 col3 6 (by rw [ht0']; native_decide) (by native_decide)
      have hlinL1 : IsLinear L1 := by
        constructor
        · intro u
          by_cases hu : u = t0
          · subst u
            have hcu : L1 t0 = col3 := by simp [L1, replaceColumn]
            rw [hcu]
            right; left; native_decide
          · have hcu : L1 u = C0 u := by simp [L1, replaceColumn, hu]
            rcases C0form_types C0 hC0f u with h0 | h5 | h6
            · left; rw [hcu, h0]
            · right; right; left; rw [hcu, h5]
            · right; right; right; rw [hcu, h6]
        · left; constructor
          · rw [hc3]; norm_num
          · have h5 : 1 ≤ count C0 5 := by rcases hC0f.2.1 with ⟨m, hm⟩; omega
            rw [hc5]
            omega
      have hodd : Odd n := by
        have hcnt : count C0 0 + count C0 5 + count C0 6 = n := hC0f.1
        rcases hC0f.2.1 with ⟨a, ha⟩
        rcases hC0f.2.2 with ⟨b, hb⟩
        refine ⟨a + b + 1, ?_⟩
        omega
      have hsum : 1 + count C0 5 + count C0 6 = n := by
        have hcnt : count C0 0 + count C0 5 + count C0 6 = n := hC0f.1
        omega
      have hsumL : 1 + count L1 5 + count L1 6 = n := by
        rw [← hc3, linear_count_sum_eq L1 hlinL1 hc0L1]
      rcases linear_c0form_not_optimal hn hodd hsumL
        (by simpa [hc5] using hC0f.2.1) (by simpa [hc6] using hC0f.2.2) with ⟨O, hlinO, hdom⟩
      have hEqLin := linear_equiv_linearCode L1 hlinL1 hc0L1
      have hEqCodes : linCode (count L1 3) (count L1 5) (count L1 6) (linear_count_sum_eq L1 hlinL1 hc0L1) =
          linCode 1 (count L1 5) (count L1 6) hsumL :=
        linCode_eq_of_counts hc3 rfl rfl (linear_count_sum_eq L1 hlinL1 hc0L1) hsumL
      have hdom' : UniversalStrictBetter O
          (linCode (count L1 3) (count L1 5) (count L1 6) (linear_count_sum_eq L1 hlinL1 hc0L1)) := by
        rw [hEqCodes]
        exact hdom
      have hdomL : UniversalStrictBetter O L1 := by
        have hU : UniversalEqual
            (linCode (count L1 3) (count L1 5) (count L1 6) (linear_count_sum_eq L1 hlinL1 hc0L1)) L1 :=
          universalEqual_of_equivalent L1
            (linCode (count L1 3) (count L1 5) (count L1 6) (linear_count_sum_eq L1 hlinL1 hc0L1)) hEqLin
        exact universalStrictBetter_of_eq_left hdom' hU
      exact hnoStrictL1 O hdomL
    · have h2 : 2 ≤ count C0 0 := by omega
      have hnotC0L1 : ¬ ∃ C0', Equivalent L1 C0' ∧ C0form C0' :=
        c0form_replaced_not_equiv_c0form C0 hC0f t0 ht0' h2
      have h0posL1 : 1 ≤ count L1 0 := by
        have hc := count_replace_dec C0 t0 col3 0 (by rw [ht0']; native_decide) (by native_decide)
        rw [hc]
        omega
      rcases zero_column_strict L1 h0posL1 hnotC0L1 with ⟨t', ht', s', hs', hstrict⟩
      exact hnoStrictL1 (replaceColumn L1 t' s') hstrict
  · rcases zero_column_strict C h0pos hC0 with ⟨t', ht', s', hs', hstrict⟩
    exact hnoStrict (replaceColumn C t' s') hstrict

/-- A {1,3,5,6,7}-code has no type-0 columns. -/
lemma count_zero_of_13567 {n : ℕ} (C : Code n) (h : totalCounts C {1, 3, 5, 6, 7} = n) :
    count C 0 = 0 := by
  rw [count_eq_card, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro t ht
  have hcv : colVal (C t) = 0 := (Finset.mem_filter.mp ht).2
  have hm := colVal_mem_of_totalCounts C ({1, 3, 5, 6, 7} : Finset ℕ) h t
  simp [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with h1 | h3 | h5 | h6 | h7
  · rw [h1] at hcv; norm_num at hcv
  · rw [h3] at hcv; norm_num at hcv
  · rw [h5] at hcv; norm_num at hcv
  · rw [h6] at hcv; norm_num at hcv
  · rw [h7] at hcv; norm_num at hcv

/-- A Class-III code with n > 3 is not optimal: its equivalent-λ linear image
has one of |5|,|6| zero and the other two counts positive, and is strictly
dominated by the canonical optimal linear code. -/
-- native_decide: Mechanical · n=any · checked 2026-08-27
lemma classIII_not_optimal {n : ℕ} (hn : 3 < n) {C : Code n} (h : ClassIII C)
    (hnoStrict : ∀ D : Code n, UniversalStrictBetter D C → False) : False := by
  rcases h with ⟨htot, hpar⟩
  have hodd : Odd n := by
    rcases hpar with hA | hB
    · rcases hA with ⟨h1, _h7, _h6, h3e, h5o⟩
      rcases h3e with ⟨a, ha⟩
      rcases h5o with ⟨b, hb⟩
      have hcnt : count C 1 + count C 3 + count C 5 + count C 6 + count C 7 = n := by
        unfold totalCounts at htot
        simp [Finset.sum_insert] at htot
        omega
      refine ⟨a + b + 1, ?_⟩
      omega
    · rcases hB with ⟨h1, _h5, _h7, h3o, h6o⟩
      rcases h3o with ⟨a, ha⟩
      rcases h6o with ⟨b, hb⟩
      have hcnt : count C 1 + count C 3 + count C 5 + count C 6 + count C 7 = n := by
        unfold totalCounts at htot
        simp [Finset.sum_insert] at htot
        omega
      refine ⟨a + b + 1, ?_⟩
      omega
  have h07 : Columns07 C := Columns07_of_types_13567 C htot
  have h24 : count C 2 = 0 ∧ count C 4 = 0 := count_two_four_zero_of_13567 C htot
  rcases hpar with hA | hB
  · -- Class-III-a: |1|=|7|=1, |6|=0, |3| even, |5| odd
    rcases hA with ⟨h1eq, h7eq, h6eq, _h3e, h5o⟩
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
    let L : Code n := replaceColumn C1 t2 col5
    have h3' : L t1 = col3 := by simp [L, C1, replaceColumn, htne]
    have h5' : L t2 = col5 := by simp [L, C1, replaceColumn]
    have hsame : ∀ u : Fin n, u ≠ t1 → u ≠ t2 → L u = C u := by
      intro u hu1 hu2
      simp [L, C1, replaceColumn, hu1, hu2]
    have hflip := two_bit_flip C L t1 t2 htne ht1 ht7 h3' h5' hsame h07
    have heq : UniversalEqual L C :=
      (hflip.2.1).mpr ⟨h1eq, h7eq, h24.1, h24.2, h6eq, Or.inr h5o⟩
    have hnoStrictL : ∀ D : Code n, UniversalStrictBetter D L → False :=
      noStrict_of_equal heq hnoStrict
    have hz0 : count L 0 = 0 := by
      have hc0C : count C 0 = 0 := count_zero_of_13567 C htot
      have hc1 : count C1 0 = count C 0 :=
        count_replace_eq C t1 col3 0 (by rw [ht1]; native_decide) (by native_decide)
      have hc2 : count L 0 = count C1 0 :=
        count_replace_eq C1 t2 col5 0 (by
          have hcv : colVal (C1 t2) = 7 := by
            change colVal (if t2 = t1 then col3 else C t2) = 7
            rw [if_neg (Ne.symm htne)]
            rw [ht7]
            native_decide
          omega) (by native_decide)
      rw [hc2, hc1, hc0C]
    have hc3L : count L 3 = count C 3 + 1 := by
      have hc1' : count C1 3 = count C 3 + 1 :=
        count_replace_inc C t1 col3 3 (by rw [ht1]; native_decide) (by native_decide)
      have hc2' : count L 3 = count C1 3 :=
        count_replace_eq C1 t2 col5 3 (by
          have hcv : colVal (C1 t2) = 7 := by
            change colVal (if t2 = t1 then col3 else C t2) = 7
            rw [if_neg (Ne.symm htne)]
            rw [ht7]
            native_decide
          omega) (by native_decide)
      rw [hc2', hc1']
    have hc5L : count L 5 = count C 5 + 1 := by
      have hc1' : count C1 5 = count C 5 :=
        count_replace_eq C t1 col3 5 (by rw [ht1]; native_decide) (by native_decide)
      have hc2' : count L 5 = count C1 5 + 1 :=
        count_replace_inc C1 t2 col5 5 (by
          have hcv : colVal (C1 t2) = 7 := by
            change colVal (if t2 = t1 then col3 else C t2) = 7
            rw [if_neg (Ne.symm htne)]
            rw [ht7]
            native_decide
          omega) (by native_decide)
      rw [hc2', hc1']
    have hc6L : count L 6 = 0 := by
      have hc1' : count C1 6 = count C 6 :=
        count_replace_eq C t1 col3 6 (by rw [ht1]; native_decide) (by native_decide)
      have hc2' : count L 6 = count C1 6 :=
        count_replace_eq C1 t2 col5 6 (by
          have hcv : colVal (C1 t2) = 7 := by
            change colVal (if t2 = t1 then col3 else C t2) = 7
            rw [if_neg (Ne.symm htne)]
            rw [ht7]
            native_decide
          omega) (by native_decide)
      rw [hc2', hc1', h6eq]
    have hlinL : IsLinear L := by
      constructor
      · intro t
        by_cases ht1' : t = t1
        · subst t
          have hcu : L t1 = col3 := by simp [L, C1, replaceColumn, htne]
          rw [hcu]
          right; left; native_decide
        · by_cases ht2' : t = t2
          · subst t
            have hcu : L t2 = col5 := by simp [L, C1, replaceColumn]
            rw [hcu]
            right; right; left; native_decide
          · have hcu : L t = C t := by simp [L, C1, replaceColumn, ht1', ht2']
            have hm := colVal_mem_of_totalCounts C ({1, 3, 5, 6, 7} : Finset ℕ) htot t
            simp [Finset.mem_insert, Finset.mem_singleton] at hm
            rcases hm with h1 | h3 | h5 | h6 | h7
            · exfalso
              have hge2 : 2 ≤ count C 1 := count_ge_two_of_two C 1 t1 t (Ne.symm ht1') (by rw [ht1]; native_decide) h1
              omega
            · right; left; rw [hcu, h3]
            · right; right; left; rw [hcu, h5]
            · right; right; right; rw [hcu, h6]
            · exfalso
              have hge2 : 2 ≤ count C 7 := count_ge_two_of_two C 7 t2 t (Ne.symm ht2') (by rw [ht7]; native_decide) h7
              omega
      · left; constructor
        · rw [hc3L]; omega
        · have h5 : 1 ≤ count C 5 := by rcases h5o with ⟨m, hm⟩; omega
          rw [hc5L]; omega
    have hsumLin : count L 3 + count L 5 + count L 6 = n :=
      linear_count_sum_eq L hlinL hz0
    have hpos : (0 < count L 3 ∧ 0 < count L 5) ∨ (0 < count L 3 ∧ 0 < count L 6) ∨
        (0 < count L 5 ∧ 0 < count L 6) := by
      left; constructor
      · rw [hc3L]; omega
      · rw [hc5L]; omega
    rcases linear_zero_count_not_optimal hn hodd hsumLin hpos (Or.inr hc6L) with ⟨O, _hlinO, hdom⟩
    have hEqLin := linear_equiv_linearCode L hlinL hz0
    have hdomL : UniversalStrictBetter O L := by
      have hU : UniversalEqual (linCode (count L 3) (count L 5) (count L 6) hsumLin) L :=
        universalEqual_of_equivalent L (linCode (count L 3) (count L 5) (count L 6) hsumLin) hEqLin
      exact universalStrictBetter_of_eq_left hdom hU
    exact hnoStrictL O hdomL

  · -- Class-III-b: |1|=1, |5|=|7|=0, |3|,|6| odd
    rcases hB with ⟨h1eq, h5eq, h7eq, h3o, h6o⟩
    have h1ge : 1 ≤ count C 1 := by rw [h1eq]
    rcases exists_col1_of_count_pos C h1ge with ⟨t1, ht1⟩
    let L : Code n := replaceColumn C t1 col3
    have hcol : L t1 = col3 := by simp [L, replaceColumn]
    have hsame : ∀ u : Fin n, u ≠ t1 → L u = C u := by
      intro u hu
      simp [L, replaceColumn, hu]
    have heven : Even (hammingDist (row2 C) (row3 C)) := by
      rw [hammingDist_row2_row3_eq C h07]
      rcases h6o with ⟨b, hb⟩
      refine ⟨b + 1, ?_⟩
      omega
    have hflip := one_bit_flip C L t1 ht1 hcol hsame heven h07
    have heq : UniversalEqual L C :=
      (hflip.2).mpr (Or.inr (Or.inl ⟨h1eq, h24.1, h24.2, h5eq, h7eq, h3o, h6o⟩))
    have hnoStrictL : ∀ D : Code n, UniversalStrictBetter D L → False :=
      noStrict_of_equal heq hnoStrict
    have hz0 : count L 0 = 0 := by
      have hc0C : count C 0 = 0 := count_zero_of_13567 C htot
      have hc1 : count L 0 = count C 0 :=
        count_replace_eq C t1 col3 0 (by rw [ht1]; native_decide) (by native_decide)
      rw [hc1, hc0C]
    have hc3L : count L 3 = count C 3 + 1 :=
      count_replace_inc C t1 col3 3 (by rw [ht1]; native_decide) (by native_decide)
    have hc5L : count L 5 = 0 := by
      have hc := count_replace_eq C t1 col3 5 (by rw [ht1]; native_decide) (by native_decide)
      rw [hc, h5eq]
    have hc6L : count L 6 = count C 6 :=
      count_replace_eq C t1 col3 6 (by rw [ht1]; native_decide) (by native_decide)
    have hlinL : IsLinear L := by
      constructor
      · intro t
        by_cases ht1' : t = t1
        · subst t
          have hcu : L t1 = col3 := by simp [L, replaceColumn]
          rw [hcu]
          right; left; native_decide
        · have hcu : L t = C t := by simp [L, replaceColumn, ht1']
          have hm := colVal_mem_of_totalCounts C ({1, 3, 5, 6, 7} : Finset ℕ) htot t
          simp [Finset.mem_insert, Finset.mem_singleton] at hm
          rcases hm with h1 | h3 | h5 | h6 | h7
          · exfalso
            have hge2 : 2 ≤ count C 1 := count_ge_two_of_two C 1 t1 t (Ne.symm ht1') (by rw [ht1]; native_decide) h1
            omega
          · right; left; rw [hcu, h3]
          · exfalso
            have hp : 1 ≤ count C 5 := count_pos_of_colVal C t h5
            omega
          · right; right; right; rw [hcu, h6]
          · exfalso
            have hp7 : 1 ≤ count C 7 := count_pos_of_colVal C t h7
            omega
      · right; left; constructor
        · rw [hc3L]; omega
        · rw [hc6L]
          have h6 : 1 ≤ count C 6 := by rcases h6o with ⟨m, hm⟩; omega
          omega
    have hsumLin : count L 3 + count L 5 + count L 6 = n :=
      linear_count_sum_eq L hlinL hz0
    have hpos : (0 < count L 3 ∧ 0 < count L 5) ∨ (0 < count L 3 ∧ 0 < count L 6) ∨
        (0 < count L 5 ∧ 0 < count L 6) := by
      right; left; constructor
      · rw [hc3L]; omega
      · rw [hc6L]
        have h6 : 1 ≤ count C 6 := by rcases h6o with ⟨m, hm⟩; omega
        omega
    rcases linear_zero_count_not_optimal hn hodd hsumLin hpos (Or.inl hc5L) with ⟨O, _hlinO, hdom⟩
    have hEqLin := linear_equiv_linearCode L hlinL hz0
    have hdomL : UniversalStrictBetter O L := by
      have hU : UniversalEqual (linCode (count L 3) (count L 5) (count L 6) hsumLin) L :=
        universalEqual_of_equivalent L (linCode (count L 3) (count L 5) (count L 6) hsumLin) hEqLin
      exact universalStrictBetter_of_eq_left hdom hU
    exact hnoStrictL O hdomL
/-! ## Class-I |1| = 1 degenerate codes (thm:11 duplicate-row cases)

`class1_one` (`thm:11` (Theorem 16)) covers Class-I codes with |1| = 1 and distinct rows.
The remaining Class-I |1| = 1 codes (n > 3) have exactly one of
(|5|,|6|), (|3|,|6|), (|3|,|5|) both zero; replacing the single type-1
column by the argmin type then adds a missing row, so the replacement is
strictly better by `universalStrictBetter_of_rows_subset`.  This keeps
`condition_optimalcode` independent of the `DistinctRows` caveat of
`thm:11` (Theorem 16) (CompanionNote §Discrepancies).
-/

/-- Row `j` of a code that is `colA` at `t` and `colB` at every other
position. -/
lemma row_of_two_columns {n : ℕ} {C : Code n} {t : Fin n} (colA colB : Column)
    (ht : C t = colA) (hall : ∀ u : Fin n, u ≠ t → C u = colB) (j : Fin 4) :
    row C j = fun u => if u = t then colBit j colA else colBit j colB := by
  funext u
  by_cases hu : u = t
  · subst u
    simp [row, ht]
  · simp [row, hall u hu, hu]

/-- Class-I rows 0 and 1 coincide only if |5| = |6| = 0 (types 5 and 6 are
the only types whose bits 3 and 2 differ). -/
-- native_decide: Mechanical · n=any · checked 2026-08-27
lemma count56_zero_of_row01_eq {n : ℕ} (C : Code n)
    (_htypes : ∀ u : Fin n, colVal (C u) = 1 ∨ colVal (C u) = 3 ∨
      colVal (C u) = 5 ∨ colVal (C u) = 6)
    (h : row0 C = row1 C) : count C 5 = 0 ∧ count C 6 = 0 := by
  constructor
  · by_contra h5
    have hp : 1 ≤ count C 5 := Nat.succ_le_of_lt (Nat.pos_of_ne_zero h5)
    rcases exists_col_of_colVal C 5 hp with ⟨u, hu⟩
    have htu : row0 C u = row1 C u := congrFun h u
    have hb0 : row0 C u = false := by
      change colBit ⟨0, by decide⟩ (C u) = false
      rw [colBit_eq_testBit, hu]
      native_decide
    have hb1 : row1 C u = true := by
      change colBit ⟨1, by decide⟩ (C u) = true
      rw [colBit_eq_testBit, hu]
      native_decide
    rw [hb0, hb1] at htu
    exact Bool.noConfusion htu
  · by_contra h6
    have hp : 1 ≤ count C 6 := Nat.succ_le_of_lt (Nat.pos_of_ne_zero h6)
    rcases exists_col_of_colVal C 6 hp with ⟨u, hu⟩
    have htu : row0 C u = row1 C u := congrFun h u
    have hb0 : row0 C u = false := by
      change colBit ⟨0, by decide⟩ (C u) = false
      rw [colBit_eq_testBit, hu]
      native_decide
    have hb1 : row1 C u = true := by
      change colBit ⟨1, by decide⟩ (C u) = true
      rw [colBit_eq_testBit, hu]
      native_decide
    rw [hb0, hb1] at htu
    exact Bool.noConfusion htu

/-- Class-I rows 0 and 2 coincide only if |3| = |6| = 0 (types 3 and 6 are
the only types whose bits 3 and 1 differ). -/
-- native_decide: Mechanical · n=any · checked 2026-08-27
lemma count36_zero_of_row02_eq {n : ℕ} (C : Code n)
    (_htypes : ∀ u : Fin n, colVal (C u) = 1 ∨ colVal (C u) = 3 ∨
      colVal (C u) = 5 ∨ colVal (C u) = 6)
    (h : row0 C = row2 C) : count C 3 = 0 ∧ count C 6 = 0 := by
  constructor
  · by_contra h3
    have hp : 1 ≤ count C 3 := Nat.succ_le_of_lt (Nat.pos_of_ne_zero h3)
    rcases exists_col_of_colVal C 3 hp with ⟨u, hu⟩
    have htu : row0 C u = row2 C u := congrFun h u
    have hb0 : row0 C u = false := by
      change colBit ⟨0, by decide⟩ (C u) = false
      rw [colBit_eq_testBit, hu]
      native_decide
    have hb2 : row2 C u = true := by
      change colBit ⟨2, by decide⟩ (C u) = true
      rw [colBit_eq_testBit, hu]
      native_decide
    rw [hb0, hb2] at htu
    exact Bool.noConfusion htu
  · by_contra h6
    have hp : 1 ≤ count C 6 := Nat.succ_le_of_lt (Nat.pos_of_ne_zero h6)
    rcases exists_col_of_colVal C 6 hp with ⟨u, hu⟩
    have htu : row0 C u = row2 C u := congrFun h u
    have hb0 : row0 C u = false := by
      change colBit ⟨0, by decide⟩ (C u) = false
      rw [colBit_eq_testBit, hu]
      native_decide
    have hb2 : row2 C u = true := by
      change colBit ⟨2, by decide⟩ (C u) = true
      rw [colBit_eq_testBit, hu]
      native_decide
    rw [hb0, hb2] at htu
    exact Bool.noConfusion htu

/-- Class-I rows 1 and 2 coincide only if |3| = |5| = 0 (types 3 and 5 are
the only types whose bits 2 and 1 differ). -/
-- native_decide: Mechanical · n=any · checked 2026-08-27
lemma count35_zero_of_row12_eq {n : ℕ} (C : Code n)
    (_htypes : ∀ u : Fin n, colVal (C u) = 1 ∨ colVal (C u) = 3 ∨
      colVal (C u) = 5 ∨ colVal (C u) = 6)
    (h : row1 C = row2 C) : count C 3 = 0 ∧ count C 5 = 0 := by
  constructor
  · by_contra h3
    have hp : 1 ≤ count C 3 := Nat.succ_le_of_lt (Nat.pos_of_ne_zero h3)
    rcases exists_col_of_colVal C 3 hp with ⟨u, hu⟩
    have htu : row1 C u = row2 C u := congrFun h u
    have hb1 : row1 C u = false := by
      change colBit ⟨1, by decide⟩ (C u) = false
      rw [colBit_eq_testBit, hu]
      native_decide
    have hb2 : row2 C u = true := by
      change colBit ⟨2, by decide⟩ (C u) = true
      rw [colBit_eq_testBit, hu]
      native_decide
    rw [hb1, hb2] at htu
    exact Bool.noConfusion htu
  · by_contra h5
    have hp : 1 ≤ count C 5 := Nat.succ_le_of_lt (Nat.pos_of_ne_zero h5)
    rcases exists_col_of_colVal C 5 hp with ⟨u, hu⟩
    have htu : row1 C u = row2 C u := congrFun h u
    have hb1 : row1 C u = true := by
      change colBit ⟨1, by decide⟩ (C u) = true
      rw [colBit_eq_testBit, hu]
      native_decide
    have hb2 : row2 C u = false := by
      change colBit ⟨2, by decide⟩ (C u) = false
      rw [colBit_eq_testBit, hu]
      native_decide
    rw [hb1, hb2] at htu
    exact Bool.noConfusion htu

-- native_decide: Mechanical · n=any · checked 2026-08-27
/-- Rows 0 and 3 of a {1,3,5,6}-code with a type-1 column are distinct. -/
lemma row03_ne_of_types1356 {n : ℕ} (C : Code n)
    (_htypes : ∀ u : Fin n, colVal (C u) = 1 ∨ colVal (C u) = 3 ∨
      colVal (C u) = 5 ∨ colVal (C u) = 6) (h1 : 1 ≤ count C 1) :
    row0 C ≠ row3 C := by
  rcases exists_col1_of_count_pos C h1 with ⟨t, ht⟩
  intro h
  have htu : row0 C t = row3 C t := congrFun h t
  have hb0 : row0 C t = false := by
    change colBit ⟨0, by decide⟩ (C t) = false
    rw [colBit_eq_testBit, ht]
    native_decide
  have hb3 : row3 C t = true := by
    change colBit ⟨3, by decide⟩ (C t) = true
    rw [colBit_eq_testBit, ht]
    native_decide
  rw [hb0, hb3] at htu
  exact Bool.noConfusion htu

-- native_decide: Mechanical · n=any · checked 2026-08-27
/-- Rows 1 and 3 of a {1,3,5,6}-code with a type-1 column are distinct. -/
lemma row13_ne_of_types1356 {n : ℕ} (C : Code n)
    (_htypes : ∀ u : Fin n, colVal (C u) = 1 ∨ colVal (C u) = 3 ∨
      colVal (C u) = 5 ∨ colVal (C u) = 6) (h1 : 1 ≤ count C 1) :
    row1 C ≠ row3 C := by
  rcases exists_col1_of_count_pos C h1 with ⟨t, ht⟩
  intro h
  have htu : row1 C t = row3 C t := congrFun h t
  have hb1 : row1 C t = false := by
    change colBit ⟨1, by decide⟩ (C t) = false
    rw [colBit_eq_testBit, ht]
    native_decide
  have hb3 : row3 C t = true := by
    change colBit ⟨3, by decide⟩ (C t) = true
    rw [colBit_eq_testBit, ht]
    native_decide
  rw [hb1, hb3] at htu
  exact Bool.noConfusion htu

-- native_decide: Mechanical · n=any · checked 2026-08-27
/-- Rows 2 and 3 of a {1,3,5,6}-code with a type-1 column are distinct. -/
lemma row23_ne_of_types1356 {n : ℕ} (C : Code n)
    (_htypes : ∀ u : Fin n, colVal (C u) = 1 ∨ colVal (C u) = 3 ∨
      colVal (C u) = 5 ∨ colVal (C u) = 6) (h1 : 1 ≤ count C 1) :
    row2 C ≠ row3 C := by
  rcases exists_col1_of_count_pos C h1 with ⟨t, ht⟩
  intro h
  have htu : row2 C t = row3 C t := congrFun h t
  have hb2 : row2 C t = false := by
    change colBit ⟨2, by decide⟩ (C t) = false
    rw [colBit_eq_testBit, ht]
    native_decide
  have hb3 : row3 C t = true := by
    change colBit ⟨3, by decide⟩ (C t) = true
    rw [colBit_eq_testBit, ht]
    native_decide
  rw [hb2, hb3] at htu
  exact Bool.noConfusion htu

/-- A Class-I code with |1| = 1 whose rows are not distinct has one of the
three count profiles (|5|=|6|=0), (|3|=|6|=0), (|3|=|5|=0). -/
lemma classI_count1_duplicate_cases {n : ℕ} {C : Code n} (h : ClassI C) (h1 : count C 1 = 1)
    (hnd : ¬ DistinctRows C) :
    (count C 5 = 0 ∧ count C 6 = 0) ∨ (count C 3 = 0 ∧ count C 6 = 0) ∨
      (count C 3 = 0 ∧ count C 5 = 0) := by
  rcases classI_hyps C h with ⟨htypes, _hpar35, _hpar36, _hpar53, _htotal⟩
  have h1ge : 1 ≤ count C 1 := by rw [h1]
  have hnd' : ∃ i j : Fin 4, i ≠ j ∧ row C i = row C j := by
    by_contra hnot
    apply hnd
    intro i j hij
    by_contra hne
    exact hnot ⟨i, j, hij, hne⟩
  rcases hnd' with ⟨i, j, hij, hrow⟩
  have hfin0 : row C (0 : Fin 4) = row0 C := by
    rw [show (0 : Fin 4) = (⟨0, by decide⟩ : Fin 4) from by exact Fin.ext rfl]
    rfl
  have hfin1 : row C (1 : Fin 4) = row1 C := by
    rw [show (1 : Fin 4) = (⟨1, by decide⟩ : Fin 4) from by exact Fin.ext rfl]
    rfl
  have hfin2 : row C (2 : Fin 4) = row2 C := by
    rw [show (2 : Fin 4) = (⟨2, by decide⟩ : Fin 4) from by exact Fin.ext rfl]
    rfl
  have hfin3 : row C (3 : Fin 4) = row3 C := by
    rw [show (3 : Fin 4) = (⟨3, by decide⟩ : Fin 4) from by exact Fin.ext rfl]
    rfl
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · simp at hrow
    rw [hfin0, hfin1] at hrow
    exact Or.inl (count56_zero_of_row01_eq C htypes hrow)
  · simp at hrow
    rw [hfin0, hfin2] at hrow
    exact Or.inr (Or.inl (count36_zero_of_row02_eq C htypes hrow))
  · simp at hrow
    rw [hfin0, hfin3] at hrow
    exact (row03_ne_of_types1356 C htypes h1ge hrow).elim
  · simp at hrow
    rw [hfin1, hfin0] at hrow
    exact Or.inl (count56_zero_of_row01_eq C htypes hrow.symm)
  · exact (hij rfl).elim
  · simp at hrow
    rw [hfin1, hfin2] at hrow
    exact Or.inr (Or.inr (count35_zero_of_row12_eq C htypes hrow))
  · simp at hrow
    rw [hfin1, hfin3] at hrow
    exact (row13_ne_of_types1356 C htypes h1ge hrow).elim
  · simp at hrow
    rw [hfin2, hfin0] at hrow
    exact Or.inr (Or.inl (count36_zero_of_row02_eq C htypes hrow.symm))
  · simp at hrow
    rw [hfin2, hfin1] at hrow
    exact Or.inr (Or.inr (count35_zero_of_row12_eq C htypes hrow.symm))
  · exact (hij rfl).elim
  · simp at hrow
    rw [hfin2, hfin3] at hrow
    exact (row23_ne_of_types1356 C htypes h1ge hrow).elim
  · simp at hrow
    rw [hfin3, hfin0] at hrow
    exact (row03_ne_of_types1356 C htypes h1ge hrow.symm).elim
  · simp at hrow
    rw [hfin3, hfin1] at hrow
    exact (row13_ne_of_types1356 C htypes h1ge hrow.symm).elim
  · simp at hrow
    rw [hfin3, hfin2] at hrow
    exact (row23_ne_of_types1356 C htypes h1ge hrow.symm).elim
  · exact (hij rfl).elim

/-- (1, 3^{n-1}) with the type-1 column replaced by col5: the row set gains
the missing word with a single 1 at the replaced position.
Instantiates `thm:11` (Theorem 16) on the |5| = |6| = 0 duplicate-row
profile (s = argmin is 5); used in `classI_count1_not_optimal`, proof of
`thm:nbig3` (Theorem 3). -/
-- native_decide: Mechanical · n=any · checked 2026-08-27
lemma strict_better_col1_col3_to_col5 {n : ℕ} (hn2 : 2 ≤ n) (C : Code n) (t : Fin n)
    (ht : C t = col1) (hall : ∀ u : Fin n, u ≠ t → C u = col3) :
    ∃ D : Code n, UniversalStrictBetter D C := by
  let D : Code n := replaceColumn C t col5
  have hDt : D t = col5 := by simp [D, replaceColumn]
  have hDall : ∀ u : Fin n, u ≠ t → D u = col3 := by
    intro u hu
    simp [D, replaceColumn, hu, hall u hu]
  have hsup : ∀ j : Fin 4, ∃ j' : Fin 4, row C j = row D j' := by
    intro j
    fin_cases j
    · refine ⟨0, ?_⟩
      funext u
      by_cases hu : u = t
      · subst u; simp [row, ht, hDt]; native_decide
      · simp [row, hall u hu, hDall u hu]
    · refine ⟨0, ?_⟩
      funext u
      by_cases hu : u = t
      · subst u; simp [row, ht, hDt]; native_decide
      · simp [row, hall u hu, hDall u hu]; native_decide
    · refine ⟨2, ?_⟩
      funext u
      by_cases hu : u = t
      · subst u; simp [row, ht, hDt]; native_decide
      · simp [row, hall u hu, hDall u hu]
    · refine ⟨3, ?_⟩
      funext u
      by_cases hu : u = t
      · subst u; simp [row, ht, hDt]; native_decide
      · simp [row, hall u hu, hDall u hu]
  have hnew : ∃ j' : Fin 4, ∀ j : Fin 4, row C j ≠ row D j' := by
    refine ⟨1, ?_⟩
    intro j
    fin_cases j
    · intro h
      have htu := congrFun h t
      simp [row, ht, hDt] at htu
      exact Bool.noConfusion htu
    · intro h
      have htu := congrFun h t
      simp [row, ht, hDt] at htu
      exact Bool.noConfusion htu
    · intro h
      have htu := congrFun h t
      simp [row, ht, hDt] at htu
      exact Bool.noConfusion htu
    · rcases exists_ne_fin hn2 t with ⟨s, hs⟩
      intro h
      have hsu := congrFun h s
      simp [row, hall s hs, hDall s hs] at hsu
      exact Bool.noConfusion hsu
  exact ⟨D, universalStrictBetter_of_rows_subset C D hsup hnew⟩

/-- (1, 5^{n-1}) with the type-1 column replaced by col3: the row set gains
the missing word with a single 1 at the replaced position.
Instantiates `thm:11` (Theorem 16) on the |3| = |6| = 0 duplicate-row
profile (s = argmin is 3); used in `classI_count1_not_optimal`, proof of
`thm:nbig3` (Theorem 3). -/
-- native_decide: Mechanical · n=any · checked 2026-08-27
lemma strict_better_col1_col5_to_col3 {n : ℕ} (hn2 : 2 ≤ n) (C : Code n) (t : Fin n)
    (ht : C t = col1) (hall : ∀ u : Fin n, u ≠ t → C u = col5) :
    ∃ D : Code n, UniversalStrictBetter D C := by
  let D : Code n := replaceColumn C t col3
  have hDt : D t = col3 := by simp [D, replaceColumn]
  have hDall : ∀ u : Fin n, u ≠ t → D u = col5 := by
    intro u hu
    simp [D, replaceColumn, hu, hall u hu]
  have hsup : ∀ j : Fin 4, ∃ j' : Fin 4, row C j = row D j' := by
    intro j
    fin_cases j
    · refine ⟨0, ?_⟩
      funext u
      by_cases hu : u = t
      · subst u; simp [row, ht, hDt]; native_decide
      · simp [row, hall u hu, hDall u hu]
    · refine ⟨1, ?_⟩
      funext u
      by_cases hu : u = t
      · subst u; simp [row, ht, hDt]; native_decide
      · simp [row, hall u hu, hDall u hu]
    · refine ⟨0, ?_⟩
      funext u
      by_cases hu : u = t
      · subst u; simp [row, ht, hDt]; native_decide
      · simp [row, hall u hu, hDall u hu]; native_decide
    · refine ⟨3, ?_⟩
      funext u
      by_cases hu : u = t
      · subst u; simp [row, ht, hDt]; native_decide
      · simp [row, hall u hu, hDall u hu]
  have hnew : ∃ j' : Fin 4, ∀ j : Fin 4, row C j ≠ row D j' := by
    refine ⟨2, ?_⟩
    intro j
    fin_cases j
    · intro h
      have htu := congrFun h t
      simp [row, ht, hDt] at htu
      exact Bool.noConfusion htu
    · intro h
      have htu := congrFun h t
      simp [row, ht, hDt] at htu
      exact Bool.noConfusion htu
    · intro h
      have htu := congrFun h t
      simp [row, ht, hDt] at htu
      exact Bool.noConfusion htu
    · rcases exists_ne_fin hn2 t with ⟨s, hs⟩
      intro h
      have hsu := congrFun h s
      simp [row, hall s hs, hDall s hs] at hsu
      exact Bool.noConfusion hsu
  exact ⟨D, universalStrictBetter_of_rows_subset C D hsup hnew⟩

/-- (1, 6^{n-1}) with the type-1 column replaced by col3: the row set gains
the all-ones word.
Instantiates `thm:11` (Theorem 16) on the |3| = |5| = 0 duplicate-row
profile (s = argmin is 3); used in `classI_count1_not_optimal`, proof of
`thm:nbig3` (Theorem 3). -/
-- native_decide: Mechanical · n=any · checked 2026-08-27
lemma strict_better_col1_col6_to_col3 {n : ℕ} (hn2 : 2 ≤ n) (C : Code n) (t : Fin n)
    (ht : C t = col1) (hall : ∀ u : Fin n, u ≠ t → C u = col6) :
    ∃ D : Code n, UniversalStrictBetter D C := by
  let D : Code n := replaceColumn C t col3
  have hDt : D t = col3 := by simp [D, replaceColumn]
  have hDall : ∀ u : Fin n, u ≠ t → D u = col6 := by
    intro u hu
    simp [D, replaceColumn, hu, hall u hu]
  have hsup : ∀ j : Fin 4, ∃ j' : Fin 4, row C j = row D j' := by
    intro j
    fin_cases j
    · refine ⟨0, ?_⟩
      funext u
      by_cases hu : u = t
      · subst u; simp [row, ht, hDt]; native_decide
      · simp [row, hall u hu, hDall u hu]
    · refine ⟨1, ?_⟩
      funext u
      by_cases hu : u = t
      · subst u; simp [row, ht, hDt]; native_decide
      · simp [row, hall u hu, hDall u hu]
    · refine ⟨1, ?_⟩
      funext u
      by_cases hu : u = t
      · subst u; simp [row, ht, hDt]; native_decide
      · simp [row, hall u hu, hDall u hu]; native_decide
    · refine ⟨3, ?_⟩
      funext u
      by_cases hu : u = t
      · subst u; simp [row, ht, hDt]; native_decide
      · simp [row, hall u hu, hDall u hu]
  have hnew : ∃ j' : Fin 4, ∀ j : Fin 4, row C j ≠ row D j' := by
    refine ⟨2, ?_⟩
    intro j
    fin_cases j
    · intro h
      have htu := congrFun h t
      simp [row, ht, hDt] at htu
      exact Bool.noConfusion htu
    · intro h
      have htu := congrFun h t
      simp [row, ht, hDt] at htu
      exact Bool.noConfusion htu
    · intro h
      have htu := congrFun h t
      simp [row, ht, hDt] at htu
      exact Bool.noConfusion htu
    · rcases exists_ne_fin hn2 t with ⟨s, hs⟩
      intro h
      have hsu := congrFun h s
      simp [row, hall s hs, hDall s hs] at hsu
      exact Bool.noConfusion hsu
  exact ⟨D, universalStrictBetter_of_rows_subset C D hsup hnew⟩

/-- A Class-I code with |1| = 1 and n > 3 is strictly dominated: either
`thm:11` (Theorem 16) applies (distinct rows) or one of the three duplicate-row profiles
above has a strictly better replacement. -/
-- native_decide: Mechanical · n=any · checked 2026-08-27
lemma classI_count1_not_optimal {n : ℕ} (hn : n > 3) {C : Code n}
    (h : ClassI C) (h1 : count C 1 = 1) :
    ∃ D : Code n, UniversalStrictBetter D C := by
  rcases classI_hyps C h with ⟨htypes, _hpar35, _hpar36, _hpar53, htotal⟩
  rcases exists_col1_of_count_pos C (by rw [h1]) with ⟨t, ht⟩
  by_cases hdist : DistinctRows C
  · exact ⟨replaceColumn C t (argminType C),
      (class1_one C t hdist h h1 ht).1 (by omega : n ≠ 3)⟩
  · rcases classI_count1_duplicate_cases h h1 hdist with h56 | h36 | h35
    · rcases h56 with ⟨h5z, h6z⟩
      have hall : ∀ u : Fin n, u ≠ t → C u = col3 := by
        intro u hu
        rcases htypes u with h1' | h3' | h5' | h6'
        · have hge2 : 2 ≤ count C 1 :=
            count_ge_two_of_two C 1 t u (Ne.symm hu) (by rw [ht]; native_decide) h1'
          omega
        · exact (colVal_eq_three_iff_col3 (C u)).1 h3'
        · have hp : 1 ≤ count C 5 := count_pos_of_colVal C u h5'
          omega
        · have hp : 1 ≤ count C 6 := count_pos_of_colVal C u h6'
          omega
      exact strict_better_col1_col3_to_col5 (by omega : 2 ≤ n) C t ht hall
    · rcases h36 with ⟨h3z, h6z⟩
      have hall : ∀ u : Fin n, u ≠ t → C u = col5 := by
        intro u hu
        rcases htypes u with h1' | h3' | h5' | h6'
        · have hge2 : 2 ≤ count C 1 :=
            count_ge_two_of_two C 1 t u (Ne.symm hu) (by rw [ht]; native_decide) h1'
          omega
        · have hp : 1 ≤ count C 3 := count_pos_of_colVal C u h3'
          omega
        · exact (colVal_eq_five_iff_col5 (C u)).1 h5'
        · have hp : 1 ≤ count C 6 := count_pos_of_colVal C u h6'
          omega
      exact strict_better_col1_col5_to_col3 (by omega : 2 ≤ n) C t ht hall
    · rcases h35 with ⟨h3z, h5z⟩
      have hall : ∀ u : Fin n, u ≠ t → C u = col6 := by
        intro u hu
        rcases htypes u with h1' | h3' | h5' | h6'
        · have hge2 : 2 ≤ count C 1 :=
            count_ge_two_of_two C 1 t u (Ne.symm hu) (by rw [ht]; native_decide) h1'
          omega
        · have hp : 1 ≤ count C 3 := count_pos_of_colVal C u h3'
          omega
        · have hp : 1 ≤ count C 5 := count_pos_of_colVal C u h5'
          omega
        · exact (colVal_eq_six_iff_col6 (C u)).1 h6'
      exact strict_better_col1_col6_to_col3 (by omega : 2 ≤ n) C t ht hall

-- native_decide: Mechanical · n=any · checked 2026-08-27
/-- Replacing a type-1 column by the argmin type lowers |1| by one. -/
lemma count_replace_argmin_1 {n : ℕ} (C : Code n) (t : Fin n) (ht : C t = col1) :
    count (replaceColumn C t (argminType C)) 1 = count C 1 - 1 :=
  count_replace_dec C t (argminType C) 1
    (by rw [ht]; native_decide)
    (by
      rcases argminType_is_type C with h3 | h5 | h6
      · rw [h3]; native_decide
      · rw [h5]; native_decide
      · rw [h6]; native_decide)

/-- Replacing a type-1 column by `col3` in a Class-I code with |1| ≥ 3 gives
a Class-II code: |1| becomes even and |3| flips parity, which is exactly
Class-II-b when |3|,|5|,|6| were even and Class-II-a when they were odd. -/
-- native_decide: Mechanical · n=any · checked 2026-08-27
lemma classI_replace_col3_is_classII {n : ℕ} (C : Code n) (t : Fin n) (h : ClassI C)
    (hge3 : 3 ≤ count C 1) (ht : C t = col1) :
    ClassII (replaceColumn C t col3) := by
  rcases h with ⟨hodd1, hpar, htotal⟩
  let C1 : Code n := replaceColumn C t col3
  have hc1_1 : count C1 1 = count C 1 - 1 := by
    simpa [C1] using count_replace_dec C t col3 1 (by rw [ht]; native_decide) (by native_decide)
  have hc1_3 : count C1 3 = count C 3 + 1 := by
    simpa [C1] using count_replace_inc C t col3 3 (by rw [ht]; native_decide) (by native_decide)
  have hc1_5 : count C1 5 = count C 5 := by
    simpa [C1] using count_replace_eq C t col3 5 (by rw [ht]; native_decide) (by native_decide)
  have hc1_6 : count C1 6 = count C 6 := by
    simpa [C1] using count_replace_eq C t col3 6 (by rw [ht]; native_decide) (by native_decide)
  have hpos1 : 0 < count C1 1 := by
    rcases hodd1 with ⟨k, hk⟩
    have hk1 : 1 ≤ k := by
      rw [hk] at hge3
      omega
    rw [hc1_1, hk]
    omega
  have htotC1 : totalCounts C1 {1, 3, 5, 6} = n := by
    rw [totalCounts]
    simp [Finset.sum_insert]
    rw [hc1_1, hc1_3, hc1_5, hc1_6]
    rw [totalCounts] at htotal
    simp [Finset.sum_insert] at htotal
    omega
  constructor
  · exact hpos1
  · constructor
    · exact htotC1
    · rcases hpar with hEven | hOdd
      · right
        constructor
        · rcases hodd1 with ⟨k, hk⟩
          rw [hc1_1, hk]
          exact ⟨k, by omega⟩
        · constructor
          · rcases hEven.1 with ⟨a, ha⟩
            rw [hc1_3, ha]
            exact ⟨a, by omega⟩
          · constructor
            · rw [hc1_5]; exact hEven.2.1
            · rw [hc1_6]; exact hEven.2.2
      · left
        constructor
        · rcases hodd1 with ⟨k, hk⟩
          rw [hc1_1, hk]
          exact ⟨k, by omega⟩
        · constructor
          · rcases hOdd.1 with ⟨a, ha⟩
            rw [hc1_3, ha]
            exact ⟨a + 1, by omega⟩
          · constructor
            · rw [hc1_5]; exact hOdd.2.1
            · rw [hc1_6]; exact hOdd.2.2

/-- One descent step: a Class-I code with |1| ≥ 3 is dominated (via the
`thm:condition_optimalcode` (Theorem 4) hypothesis) by a Class-I code with |1| reduced
by 2, obtained by the argmin replacement followed by `thm:class2` (Lemma 14). -/
-- native_decide: Mechanical · n=any · checked 2026-08-27
lemma classI_descend_one {n : ℕ} (_hn : n > 3)
    (hcond : ∀ C : Code n, ClassI C → count C 1 ≥ 3 → ∀ t : Fin n, C t = col1 →
      UniversalBetter (replaceColumn C t (argminType C)) C)
    {C : Code n} (h : ClassI C) (hge3 : 3 ≤ count C 1) :
    ∃ C2 : Code n, ClassI C2 ∧ count C2 1 = count C 1 - 2 ∧ UniversalBetter C2 C := by
  rcases classI_hyps C h with ⟨htypes, _hpar35, _hpar36, _hpar53, htotal⟩
  rcases exists_col1_of_count_pos C (by omega : 1 ≤ count C 1) with ⟨t, ht⟩
  let C1 : Code n := replaceColumn C t (argminType C)
  have htypesC1 : ∀ u : Fin n, colVal (C1 u) = 1 ∨ colVal (C1 u) = 3 ∨
      colVal (C1 u) = 5 ∨ colVal (C1 u) = 6 := by
    intro u
    by_cases hu : u = t
    · subst u
      rcases argminType_is_type C with h3 | h5 | h6
      · simp [C1, replaceColumn, h3]
      · simp [C1, replaceColumn, h5]
      · simp [C1, replaceColumn, h6]
    · simpa [C1, replaceColumn, hu] using htypes u
  rcases argminType_is_type C with harg3 | harg5 | harg6
  · -- argmin = col3: the replacement itself is Class-II
    have harg : argminType C = col3 := (colVal_eq_three_iff_col3 (argminType C)).mp harg3
    have hC1 : ClassII C1 := by
      simpa [C1, harg] using classI_replace_col3_is_classII C t h hge3 ht
    rcases class2_to_class1 C1 hC1 with ⟨C2, hC2, hEq21, hc2⟩
    have hb1 : UniversalBetter C1 C := by simpa [C1, harg] using hcond C h hge3 t ht
    have hb2 : UniversalBetter C2 C := universalBetter_of_equal_left C2 C1 C hEq21 hb1
    refine ⟨C2, hC2, ?_, hb2⟩
    have hc1' : count C1 1 = count C 1 - 1 := by
      simpa [C1, harg] using count_replace_argmin_1 C t ht
    rw [hc2, hc1']
    omega
  · -- argmin = col5: the 3↔5 role swap of the replacement is Class-II
    have harg : argminType C = col5 := (colVal_eq_five_iff_col5 (argminType C)).mp harg5
    let D : Code n := swap12Code C1
    have hc1_1 : count C1 1 = count C 1 - 1 := by
      simpa [C1, harg] using count_replace_argmin_1 C t ht
    have hc1_3 : count C1 3 = count C 3 := by
      simpa [C1, harg] using count_replace_eq C t col5 3 (by rw [ht]; native_decide) (by native_decide)
    have hc1_5 : count C1 5 = count C 5 + 1 := by
      simpa [C1, harg] using count_replace_inc C t col5 5 (by rw [ht]; native_decide) (by native_decide)
    have hc1_6 : count C1 6 = count C 6 := by
      simpa [C1, harg] using count_replace_eq C t col5 6 (by rw [ht]; native_decide) (by native_decide)
    have hD_1 : count D 1 = count C 1 - 1 := by
      simpa [D] using (count_swap12Code_one C1 htypesC1).trans hc1_1
    have hD_3 : count D 3 = count C 5 + 1 := by
      simpa [D] using (count_swap12Code C1 htypesC1).trans hc1_5
    have hD_5 : count D 5 = count C 3 := by
      simpa [D] using (count_swap12Code_five C1 htypesC1).trans hc1_3
    have hD_6 : count D 6 = count C 6 := by
      simpa [D] using (count_swap12Code_six C1 htypesC1).trans hc1_6
    have hD : ClassII D := by
      rcases h with ⟨hodd1, hpar, htotal'⟩
      constructor
      · rw [hD_1]
        rcases hodd1 with ⟨k, hk⟩
        rw [hk]
        omega
      · constructor
        · rw [totalCounts]
          simp [Finset.sum_insert]
          rw [hD_1, hD_3, hD_5, hD_6]
          rw [totalCounts] at htotal'
          simp [Finset.sum_insert] at htotal'
          omega
        · rcases hpar with hEven | hOdd
          · right
            constructor
            · rcases hodd1 with ⟨k, hk⟩
              rw [hD_1, hk]
              exact ⟨k, by omega⟩
            · constructor
              · rcases hEven.2.1 with ⟨a, ha⟩
                rw [hD_3, ha]
                exact ⟨a, by omega⟩
              · constructor
                · rw [hD_5]; exact hEven.1
                · rw [hD_6]; exact hEven.2.2
          · left
            constructor
            · rcases hodd1 with ⟨k, hk⟩
              rw [hD_1, hk]
              exact ⟨k, by omega⟩
            · constructor
              · rcases hOdd.2.1 with ⟨a, ha⟩
                rw [hD_3, ha]
                exact ⟨a + 1, by omega⟩
              · constructor
                · rw [hD_5]; exact hOdd.1
                · rw [hD_6]; exact hOdd.2.2
    rcases class2_to_class1 D hD with ⟨C2, hC2, hEq21, hc2⟩
    have hb1 : UniversalBetter C1 C := by simpa [C1, harg] using hcond C h hge3 t ht
    have hEqD : UniversalEqual D C1 := universalEqual_of_equivalent C1 D (Equivalent_swap12Code C1)
    have hEq2 : UniversalEqual C2 C1 := universalEqual_trans hEq21 hEqD
    have hb2 : UniversalBetter C2 C := universalBetter_of_equal_left C2 C1 C hEq2 hb1
    refine ⟨C2, hC2, ?_, hb2⟩
    rw [hc2, hD_1]
    omega
  · -- argmin = col6: the 3↔6 role swap of the replacement is Class-II
    have harg : argminType C = col6 := (colVal_eq_six_iff_col6 (argminType C)).mp harg6
    let D : Code n := swap36Code C1
    have hc1_1 : count C1 1 = count C 1 - 1 := by
      simpa [C1, harg] using count_replace_argmin_1 C t ht
    have hc1_3 : count C1 3 = count C 3 := by
      simpa [C1, harg] using count_replace_eq C t col6 3 (by rw [ht]; native_decide) (by native_decide)
    have hc1_5 : count C1 5 = count C 5 := by
      simpa [C1, harg] using count_replace_eq C t col6 5 (by rw [ht]; native_decide) (by native_decide)
    have hc1_6 : count C1 6 = count C 6 + 1 := by
      simpa [C1, harg] using count_replace_inc C t col6 6 (by rw [ht]; native_decide) (by native_decide)
    have hD_1 : count D 1 = count C 1 - 1 := by
      simpa [D] using (count_swap36Code_one C1 htypesC1).trans hc1_1
    have hD_3 : count D 3 = count C 6 + 1 := by
      simpa [D] using (count_swap36Code_three C1 htypesC1).trans hc1_6
    have hD_5 : count D 5 = count C 5 := by
      simpa [D] using (count_swap36Code_five C1 htypesC1).trans hc1_5
    have hD_6 : count D 6 = count C 3 := by
      simpa [D] using (count_swap36Code_six C1 htypesC1).trans hc1_3
    have hD : ClassII D := by
      rcases h with ⟨hodd1, hpar, htotal'⟩
      constructor
      · rw [hD_1]
        rcases hodd1 with ⟨k, hk⟩
        rw [hk]
        omega
      · constructor
        · rw [totalCounts]
          simp [Finset.sum_insert]
          rw [hD_1, hD_3, hD_5, hD_6]
          rw [totalCounts] at htotal'
          simp [Finset.sum_insert] at htotal'
          omega
        · rcases hpar with hEven | hOdd
          · right
            constructor
            · rcases hodd1 with ⟨k, hk⟩
              rw [hD_1, hk]
              exact ⟨k, by omega⟩
            · constructor
              · rcases hEven.2.2 with ⟨a, ha⟩
                rw [hD_3, ha]
                exact ⟨a, by omega⟩
              · constructor
                · rw [hD_5]; exact hEven.2.1
                · rw [hD_6]; exact hEven.1
          · left
            constructor
            · rcases hodd1 with ⟨k, hk⟩
              rw [hD_1, hk]
              exact ⟨k, by omega⟩
            · constructor
              · rcases hOdd.2.2 with ⟨a, ha⟩
                rw [hD_3, ha]
                exact ⟨a + 1, by omega⟩
              · constructor
                · rw [hD_5]; exact hOdd.2.1
                · rw [hD_6]; exact hOdd.1
    rcases class2_to_class1 D hD with ⟨C2, hC2, hEq21, hc2⟩
    have hb1 : UniversalBetter C1 C := by simpa [C1, harg] using hcond C h hge3 t ht
    have hEqD : UniversalEqual D C1 := class1_lambda_swap36 C1 htypesC1
    have hEq2 : UniversalEqual C2 C1 := universalEqual_trans hEq21 hEqD
    have hb2 : UniversalBetter C2 C := universalBetter_of_equal_left C2 C1 C hEq2 hb1
    refine ⟨C2, hC2, ?_, hb2⟩
    rw [hc2, hD_1]
    omega

/-- Iterating the descent reaches a Class-I code with |1| = 1 that is no
worse than the original (`thm:condition_optimalcode` (Theorem 4) proof step). -/
lemma classI_descend_to_count1 {n : ℕ} (hn : n > 3)
    (hcond : ∀ C : Code n, ClassI C → count C 1 ≥ 3 → ∀ t : Fin n, C t = col1 →
      UniversalBetter (replaceColumn C t (argminType C)) C)
    {C : Code n} (h : ClassI C) :
    ∃ Ck : Code n, ClassI Ck ∧ count Ck 1 = 1 ∧ UniversalBetter Ck C := by
  have hind : ∀ m : ℕ, ∀ C : Code n, ClassI C → count C 1 = m →
      ∃ Ck : Code n, ClassI Ck ∧ count Ck 1 = 1 ∧ UniversalBetter Ck C := by
    intro m
    refine Nat.strong_induction_on m ?_
    intro m ih C hC hm
    by_cases h1 : count C 1 = 1
    · exact ⟨C, hC, h1, universalBetter_refl C⟩
    · have hge3 : 3 ≤ count C 1 := by
        rcases hC.1 with ⟨k, hk⟩
        by_cases hk0 : k = 0
        · have : count C 1 = 1 := by rw [hk, hk0]; norm_num
          omega
        · have hk1 : 1 ≤ k := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hk0)
          omega
      rcases classI_descend_one hn hcond hC hge3 with ⟨C2, hC2, hc2, hb2⟩
      have hlt : count C2 1 < m := by
        rw [hc2]
        omega
      rcases ih (count C2 1) hlt C2 hC2 rfl with ⟨Ck, hCk, h1k, hbk⟩
      exact ⟨Ck, hCk, h1k, universalBetter_trans hbk hb2⟩
  exact hind (count C 1) C h rfl

/-- Under the `thm:condition_optimalcode` (Theorem 4) hypothesis, no Class-I code with
n > 3 is optimal (the descent to |1| = 1 followed by `thm:11` (Theorem 16) / the
duplicate-row strict improvements yields a strictly better code). -/
lemma classI_not_optimal_under_cond {n : ℕ} (hn : n > 3)
    (hcond : ∀ C : Code n, ClassI C → count C 1 ≥ 3 → ∀ t : Fin n, C t = col1 →
      UniversalBetter (replaceColumn C t (argminType C)) C)
    {C : Code n} (h : ClassI C)
    (hnoStrict : ∀ D : Code n, UniversalStrictBetter D C → False) : False := by
  rcases classI_descend_to_count1 hn hcond h with ⟨Ck, hCk, h1k, hbk⟩
  rcases classI_count1_not_optimal hn hCk h1k with ⟨D, hdom⟩
  apply hnoStrict D
  intro ε h0 h1
  have hDk : lambda D ε > lambda Ck ε := hdom ε h0 h1
  have hkC : lambda Ck ε ≥ lambda C ε := hbk ε h0 h1
  linarith

/-- Theorem `thm:nbig3` (Theorem 3): for n > 3, every optimal code is equivalent to a
linear, Class-I, or Class-II code.  (Depends on `thm:linearopt` (Theorem 2), Phase F.) -/
-- native_decide: Mechanical · n=any · checked 2026-08-27
theorem optimal_equivalent_linear_class1_class2 (n : ℕ) (hn : n > 3) :
    ∀ ε : ℝ, 0 < ε → ε < 1 / 2 → ∀ C : Code n,
      OptimalAt C ε →
        ∃ C' : Code n, Equivalent C C' ∧
          (IsLinear C' ∨ ClassI C' ∨ ClassII C') := by
  intro ε hε0 hε1 C hOpt
  have hnoStrict : ∀ D : Code n, UniversalStrictBetter D C → False := by
    intro D hD
    have hgt : lambda D ε > lambda C ε := hD ε hε0 hε1
    have hge : lambda C ε ≥ lambda D ε := hOpt D
    linarith
  have hcols : ∀ t : Fin n, 1 ≤ colVal (C t) ∧ colVal (C t) ≤ 14 := by
    intro t
    constructor
    · by_contra hnot
      have hv0 : colVal (C t) = 0 := by
        have hle15 := colVal_le_15 (C t)
        omega
      exact zero_column_not_optimal hn hnoStrict t ((colVal_eq_zero_iff_col0 (C t)).mp hv0)
    · by_contra hnot
      have hv15 : colVal (C t) = 15 := by
        have hle15 := colVal_le_15 (C t)
        omega
      -- a type-15 column flips to type-0, and `flipHighColumns` is equivalent
      have hflip0 : colVal (flipCol (C t)) = 0 := by
        rw [colVal_flipCol, hv15]
      have hfc0 : flipCol (C t) = col0 := (colVal_eq_zero_iff_col0 (flipCol (C t))).mp hflip0
      have hc0 : flipHighColumns C t = col0 := by
        unfold flipHighColumns
        have hgt7 : 7 < colVal (C t) := by rw [hv15]; native_decide
        rw [if_pos (decide_eq_true hgt7)]
        exact hfc0
      have hEq1 : Equivalent C (flipHighColumns C) := flipHighColumns_equiv C
      have hnoStrict1 : ∀ D : Code n, UniversalStrictBetter D (flipHighColumns C) → False :=
        noStrict_of_equiv hnoStrict hEq1
      exact zero_column_not_optimal hn hnoStrict1 t hc0
  rcases lm_all n (by omega : 2 ≤ n) C hcols hnoStrict with ⟨C', hEq, hcl⟩
  rcases hcl with hlin | hci | hcii | hciii
  · exact ⟨C', hEq, Or.inl hlin⟩
  · exact ⟨C', hEq, Or.inr (Or.inl hci)⟩
  · exact ⟨C', hEq, Or.inr (Or.inr hcii)⟩
  · exfalso
    have hnoStrictC' : ∀ D : Code n, UniversalStrictBetter D C' → False :=
      noStrict_of_equiv hnoStrict hEq
    exact classIII_not_optimal hn hciii hnoStrictC'

/-- Theorem `thm:condition_optimalcode` (Theorem 4): if every Class-I code with |1| ≥ 3 is
not better than the code obtained by replacing a type-1 column by the argmin
type, then all optimal codes are equivalent to linear codes. -/
theorem condition_optimalcode (n : ℕ) (hn : n > 3)
    (hcond : ∀ C : Code n, ClassI C → count C 1 ≥ 3 →
      ∀ t : Fin n, C t = col1 →
        UniversalBetter (replaceColumn C t (argminType C)) C) :
    ∀ ε : ℝ, 0 < ε → ε < 1 / 2 → ∀ C : Code n,
      OptimalAt C ε → ∃ C' : Code n, Equivalent C C' ∧ IsLinear C' := by
  intro ε hε0 hε1 C hOpt
  have hnoStrict : ∀ D : Code n, UniversalStrictBetter D C → False := by
    intro D hD
    have hgt : lambda D ε > lambda C ε := hD ε hε0 hε1
    have hge : lambda C ε ≥ lambda D ε := hOpt D
    linarith
  rcases optimal_equivalent_linear_class1_class2 n hn ε hε0 hε1 C hOpt with ⟨C', hEq, hcl⟩
  rcases hcl with hlin | hci | hcii
  · exact ⟨C', hEq, hlin⟩
  · exfalso
    have hnoStrictC' : ∀ D : Code n, UniversalStrictBetter D C' → False :=
      noStrict_of_equiv hnoStrict hEq
    exact classI_not_optimal_under_cond hn hcond hci hnoStrictC'
  · exfalso
    have hnoStrictC' : ∀ D : Code n, UniversalStrictBetter D C' → False :=
      noStrict_of_equiv hnoStrict hEq
    rcases class2_to_class1 C' hcii with ⟨C'', hCI, hEq'', _hc1''⟩
    have hnoStrictC'' : ∀ D : Code n, UniversalStrictBetter D C'' → False :=
      noStrict_of_equal hEq'' hnoStrictC'
    exact classI_not_optimal_under_cond hn hcond hCI hnoStrictC''

end N4Code
