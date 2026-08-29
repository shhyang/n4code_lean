import N4Code.Definitions
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FinCases

/-!
# Phase A: foundational lemmas

Hamming weight/distance basics, XOR identities, column-count identities
(`Σ_i |i|_C = n`), row/distance facts, α-basic facts, and the binomial
counting lemma that underpins every α-formula in the paper.
-/

open scoped BigOperators

set_option maxHeartbeats 4000000

namespace N4Code

/-! ## XOR identities -/

/-- XOR is commutative. -/
lemma bitXor_comm {n : ℕ} (x y : Word n) : bitXor x y = bitXor y x := by
  funext i
  by_cases hx : x i = true <;> by_cases hy : y i = true <;> simp [bitXor, hx, hy]

/-- XOR is associative. -/
lemma bitXor_assoc {n : ℕ} (x y z : Word n) : bitXor (bitXor x y) z = bitXor x (bitXor y z) := by
  funext i
  by_cases hx : x i = true <;> by_cases hy : y i = true <;> by_cases hz : z i = true <;>
    simp [bitXor, hx, hy, hz]

/-- XOR with itself is the zero word. -/
lemma bitXor_self {n : ℕ} (x : Word n) : bitXor x x = fun _ => false := by
  funext i
  by_cases hx : x i = true <;> simp [bitXor, hx]

/-- XOR with the zero word is the identity. -/
lemma bitXor_false {n : ℕ} (y : Word n) : bitXor (fun _ => false) y = y := by
  funext i
  by_cases hy : y i = true <;> simp [bitXor, hy]

/-- XOR is zero exactly when the words agree. -/
lemma bitXor_eq_false_iff {n : ℕ} (x y : Word n) : (bitXor x y = fun _ => false) ↔ x = y := by
  constructor
  · intro h
    funext i
    have h' := congrFun h i
    cases hx : x i <;> cases hy : y i <;> simp [bitXor] at h'
    all_goals simp_all
  · intro h
    rw [← h]
    exact bitXor_self x

/-! ## Hamming weight and distance -/

/-- A word has weight zero iff it is the zero word. -/
lemma hammingWeight_eq_zero_iff {n : ℕ} (w : Word n) :
    hammingWeight w = 0 ↔ ∀ i : Fin n, w i = false := by
  unfold hammingWeight
  rw [Finset.sum_eq_zero_iff]
  constructor
  · intro h i
    have hi := h i (Finset.mem_univ i)
    cases hx : w i <;> simp [hx] at hi ⊢
  · intro h i _
    have hx : w i = false := h i
    simp [hx]

/-- Hamming distance is reflexive. -/
lemma hammingDist_self {n : ℕ} (x : Word n) : hammingDist x x = 0 := by
  rw [hammingDist, bitXor_self]
  simp [hammingWeight]

/-- Hamming distance is symmetric. -/
lemma hammingDist_symm {n : ℕ} (x y : Word n) : hammingDist x y = hammingDist y x := by
  rw [hammingDist, hammingDist, bitXor_comm]

/-- Hamming distance is zero iff the words are equal. -/
lemma hammingDist_eq_zero_iff {n : ℕ} (x y : Word n) : hammingDist x y = 0 ↔ x = y := by
  rw [hammingDist, hammingWeight_eq_zero_iff]
  rw [show (∀ i : Fin n, bitXor x y i = false) ↔ bitXor x y = fun _ => false by
    constructor
    · intro h
      funext i
      exact h i
    · intro h i
      simpa using (congrFun h i)]
  exact bitXor_eq_false_iff x y

/-- Hamming distance between two n-bit words is at most n. -/
lemma hammingDist_le {n : ℕ} (x y : Word n) : hammingDist x y ≤ n := by
  unfold hammingDist hammingWeight
  calc
    (∑ i ∈ (Finset.univ : Finset (Fin n)), if bitXor x y i = true then 1 else 0) ≤
        ∑ i ∈ (Finset.univ : Finset (Fin n)), 1 := by
      apply Finset.sum_le_sum
      intro i _
      by_cases h : bitXor x y i = true <;> simp [h]
    _ = n := by simp

/-! ## Column-type counts -/

-- native_decide: Mechanical · n=any · checked 2026-08-24
/-- The type number of a column is at most 15. -/
lemma colVal_le_15 (c : Column) : colVal c ≤ 15 := by
  unfold colVal
  have hstep : (∑ j : Fin 4, if c j then 2 ^ (3 - j.val) else 0) ≤
      ∑ j : Fin 4, 2 ^ (3 - j.val) := by
    apply Finset.sum_le_sum
    intro j _
    by_cases h : c j = true <;> simp [h]
  have hval : (∑ j : Fin 4, 2 ^ (3 - j.val)) = 15 := by native_decide
  rw [← hval]
  exact hstep

/-- |i|_C as the number of type-i columns (cardinality form). -/
lemma count_eq_card {n : ℕ} (C : Code n) (i : ℕ) :
    count C i = (Finset.univ.filter fun t : Fin n => colVal (C t) = i).card := by
  simp [count]

/-- Types 16 and above never occur as column types. -/
lemma count_eq_zero_of_16_le {n : ℕ} (C : Code n) {i : ℕ} (hi : 16 ≤ i) : count C i = 0 := by
  unfold count
  apply Finset.sum_eq_zero
  intro t _
  have hle := colVal_le_15 (C t)
  have : colVal (C t) ≠ i := by omega
  simp [this]

/-- The counts of all 16 column types sum to n (paper §2.1). -/
lemma sum_counts_eq_n {n : ℕ} (C : Code n) : (∑ i ∈ Finset.Icc 0 15, count C i) = n := by
  rw [show (∑ i ∈ Finset.Icc 0 15, count C i) =
        ∑ i ∈ Finset.Icc 0 15, ∑ t ∈ (Finset.univ : Finset (Fin n)),
          if colVal (C t) = i then 1 else 0 by
        apply Finset.sum_congr rfl
        intro i _
        rfl]
  rw [Finset.sum_comm]
  simp [Finset.sum_ite_eq, colVal_le_15]

/-! ## Rows and code distance -/

/-- d_j(y) is the Hamming distance from y to the j-th codeword (paper eq. (d)). -/
lemma dRow_eq_hammingDist {n : ℕ} (C : Code n) (j : Fin 4) (y : Word n) :
    dRow C j y = hammingDist (row C j) y := rfl

/-- d_C(y) is the minimum of the row distances. -/
lemma dCode_le_dRow {n : ℕ} (C : Code n) (j : Fin 4) (y : Word n) :
    dCode C y ≤ dRow C j y := by
  unfold dCode dRow
  fin_cases j
  · exact Nat.min_le_left _ _
  · exact (Nat.min_le_right _ _).trans (Nat.min_le_left _ _)
  · exact (Nat.min_le_right _ _).trans ((Nat.min_le_right _ _).trans (Nat.min_le_left _ _))
  · exact (Nat.min_le_right _ _).trans ((Nat.min_le_right _ _).trans (Nat.min_le_right _ _))

/-- A row distance is the sum of the per-column test-bit mismatches. -/
lemma hammingDist_row_eq_indicator {n : ℕ} (C : Code n) (i j : Fin 4) :
    hammingDist (row C i) (row C j) =
      ∑ t : Fin n, if (colVal (C t)).testBit (3 - i.val) ≠ (colVal (C t)).testBit (3 - j.val) then 1 else 0 := by
  unfold hammingDist hammingWeight bitXor
  apply Finset.sum_congr rfl
  intro t _
  simp [row, colBit_eq_testBit]

/-- The code distance of any word is at most n. -/
lemma dCode_le {n : ℕ} (C : Code n) (y : Word n) : dCode C y ≤ n := by
  exact (dCode_le_dRow C ⟨0, by decide⟩ y).trans (hammingDist_le _ _)

/-! ## α-basic facts -/

/-- α_C(d) as the number of words at distance d (cardinality form). -/
lemma alpha_eq_card {n : ℕ} (C : Code n) (d : ℕ) :
    alpha C d = (Finset.univ.filter fun y : Word n => dCode C y = d).card := by
  simp [alpha]

/-- No word is at distance greater than n. -/
lemma alpha_eq_zero_of_lt {n : ℕ} (C : Code n) {d : ℕ} (hd : n < d) : alpha C d = 0 := by
  unfold alpha
  apply Finset.sum_eq_zero
  intro y _
  have hle := dCode_le C y
  have : dCode C y ≠ d := by omega
  simp [this]

/-- The distance distribution partitions the 2^n words. -/
lemma sum_alpha_eq_two_pow {n : ℕ} (C : Code n) : (∑ d ∈ Finset.Icc 0 n, alpha C d) = 2 ^ n := by
  rw [show (∑ d ∈ Finset.Icc 0 n, alpha C d) =
        ∑ d ∈ Finset.Icc 0 n, ∑ y ∈ (Finset.univ : Finset (Word n)),
          if dCode C y = d then 1 else 0 by
        apply Finset.sum_congr rfl
        intro d _
        rfl]
  rw [Finset.sum_comm]
  have hbool : Fintype.card Bool = 2 := by decide
  simp [Finset.sum_ite_eq, dCode_le, Fintype.card_pi, hbool]

/-! ## d_j(y) in terms of the w_i (paper eq. d1–d4) -/

/-- Expand a sum over `Fin 4` into its four terms. -/
lemma sum_fin_four (f : Fin 4 → ℕ) :
    (∑ k : Fin 4, f k) = f ⟨0, by decide⟩ + f ⟨1, by decide⟩ + f ⟨2, by decide⟩ + f ⟨3, by decide⟩ := by
  have huniv : (Finset.univ : Finset (Fin 4)) =
      ({⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩} : Finset (Fin 4)) := by
    ext k
    fin_cases k <;> simp
  rw [huniv]
  simp [add_assoc]

lemma bool_xor_eq_true (a b : Bool) : Bool.xor a b = true ↔ a ≠ b := by
  cases a <;> cases b <;> simp [Bool.xor]

/-! ## Counting-lemma helpers -/

/-- The positions of `s` where y is 1. -/
def onesOn {n : ℕ} (s : Finset (Fin n)) (y : Word n) : Finset (Fin n) :=
  s.filter fun t => y t = true

/-- The columns of C of type i. -/
def fiber {n : ℕ} (C : Code n) (i : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun t : Fin n => colVal (C t) = i

lemma w_i_eq_card_onesOn {n : ℕ} (C : Code n) (i : ℕ) (y : Word n) :
    w_i C i y = (onesOn (fiber C i) y).card := rfl

lemma fiber_card_eq_count {n : ℕ} (C : Code n) (i : ℕ) :
    (fiber C i).card = count C i := by
  rw [count_eq_card]
  rfl

/-- The columns of type i contribute `w_i` (bit j = 0) or `|i| − w_i`
(bit j = 1) to d_j(y) — paper eq. (d1)–(d4), §3.1. -/
lemma class_contribution {n : ℕ} (C : Code n) (j : Fin 4) (y : Word n) (i : ℕ) :
    (∑ t ∈ (Finset.univ.filter fun t : Fin n => colVal (C t) = i),
        if C t j ≠ y t then 1 else 0) =
      if i.testBit (3 - j.val) then count C i - w_i C i y else w_i C i y := by
  cases hbit : i.testBit (3 - j.val)
  · -- bit j of type i is 0: contribution is w_i
    have hb : ∀ t : Fin n, colVal (C t) = i → C t j = false := by
      intro t ht
      change colBit j (C t) = false
      rw [colBit_eq_testBit (C t) j, ht, hbit]
    have hsum : (∑ t ∈ (Finset.univ.filter fun t : Fin n => colVal (C t) = i),
        if C t j ≠ y t then 1 else 0) =
        ∑ t ∈ (Finset.univ.filter fun t : Fin n => colVal (C t) = i),
          if y t = true then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro t ht
      have hcol : colVal (C t) = i := (Finset.mem_filter.mp ht).2
      have hb' := hb t hcol
      cases hy : y t <;> simp [hb']
    have hw : (∑ t ∈ (Finset.univ.filter fun t : Fin n => colVal (C t) = i),
        if y t = true then 1 else 0) = w_i C i y := by
      rw [w_i_eq_card_onesOn]
      simp [onesOn, fiber]
    rw [hsum, hw]
    simp
  · -- bit j of type i is 1: contribution is count − w_i
    have hb : ∀ t : Fin n, colVal (C t) = i → C t j = true := by
      intro t ht
      change colBit j (C t) = true
      rw [colBit_eq_testBit (C t) j, ht, hbit]
    have hcard : (∑ t ∈ (Finset.univ.filter fun t : Fin n => colVal (C t) = i), 1) = count C i := by
      rw [count_eq_card]
      simp
    have hw : (∑ t ∈ (Finset.univ.filter fun t : Fin n => colVal (C t) = i),
        if y t = true then 1 else 0) = w_i C i y := by
      rw [w_i_eq_card_onesOn]
      simp [onesOn, fiber]
    have hsum : (∑ t ∈ (Finset.univ.filter fun t : Fin n => colVal (C t) = i),
        if y t = false then 1 else 0) = count C i - w_i C i y := by
      have hadd : (∑ t ∈ (Finset.univ.filter fun t : Fin n => colVal (C t) = i),
          if y t = false then 1 else 0) + w_i C i y = count C i := by
        rw [← hcard, ← hw, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro t _
        cases hy : y t <;> simp
      omega
    have hsum' : (∑ t ∈ (Finset.univ.filter fun t : Fin n => colVal (C t) = i),
        if C t j ≠ y t then 1 else 0) = count C i - w_i C i y := by
      rw [show (∑ t ∈ (Finset.univ.filter fun t : Fin n => colVal (C t) = i),
            if C t j ≠ y t then 1 else 0) =
          ∑ t ∈ (Finset.univ.filter fun t : Fin n => colVal (C t) = i),
            if y t = false then 1 else 0 by
        apply Finset.sum_congr rfl
        intro t ht
        have hcol : colVal (C t) = i := (Finset.mem_filter.mp ht).2
        have hb' := hb t hcol
        cases hy : y t <;> simp [hb']]
      exact hsum
    rw [hsum']
    simp

/-- d_j(y) expressed through the per-type weights w_i (paper eq. d1–d4). -/
lemma dRow_eq_sum {n : ℕ} (C : Code n) (j : Fin 4) (y : Word n) :
    dRow C j y = ∑ i ∈ Finset.Icc 0 15,
      if i.testBit (3 - j.val) then count C i - w_i C i y else w_i C i y := by
  rw [dRow_eq_hammingDist]
  unfold hammingDist hammingWeight
  have hstep : (∑ t ∈ (Finset.univ : Finset (Fin n)),
        if bitXor (row C j) y t = true then 1 else 0) =
      ∑ t ∈ (Finset.univ : Finset (Fin n)),
        ∑ i ∈ Finset.Icc 0 15,
          if colVal (C t) = i then (if C t j ≠ y t then 1 else 0) else 0 := by
    apply Finset.sum_congr rfl
    intro t _
    have hsummand : (if bitXor (row C j) y t = true then 1 else 0) =
        if C t j ≠ y t then 1 else 0 := by
      by_cases h : bitXor (row C j) y t = true <;> by_cases hne : C t j ≠ y t <;>
        simp [hne, bitXor, row, colBit]
    rw [hsummand]
    rw [Finset.sum_ite_eq]
    simp [colVal_le_15]
  rw [hstep, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_filter (s := (Finset.univ : Finset (Fin n)))
    (p := fun t : Fin n => colVal (C t) = i)
    (f := fun t : Fin n => if C t j ≠ y t then 1 else 0)]
  exact class_contribution C j y i

/-! ## The binomial counting lemma -/

/-- Words whose per-type weights are the prescribed ones. -/
def GoodWords {n : ℕ} (C : Code n) (k : ℕ → ℕ) : Finset (Word n) :=
  (Finset.univ : Finset (Word n)).filter
    fun y : Word n => (∑ i ∈ Finset.Icc 0 15, if w_i C i y = k i then 0 else 1) = 0

/-- A word is good iff all its per-type weights match. -/
lemma goodWord_iff {n : ℕ} (C : Code n) (k : ℕ → ℕ) (y : Word n) :
    y ∈ GoodWords C k ↔ ∀ i ∈ Finset.Icc 0 15, w_i C i y = k i := by
  unfold GoodWords
  simp

/-- The value of a `Fin 16` element lies in `0..15`. -/
lemma fin16_val_mem_Icc (a : Fin 16) : a.val ∈ Finset.Icc 0 15 := by
  rw [Finset.mem_Icc]
  omega

/-- The tuple of the per-type ones-subsets of a word. -/
def wordTuple {n : ℕ} (C : Code n) (y : Word n) : Fin 16 → Finset (Fin n) :=
  fun a => onesOn (fiber C a.val) y

/-- A tuple is good if each entry is a k_i-subset of the type-i columns. -/
def GoodTuplePred {n : ℕ} (C : Code n) (k : ℕ → ℕ) (g : Fin 16 → Finset (Fin n)) : Prop :=
  ∀ a : Fin 16, g a ∈ (fiber C a.val).powersetCard (k a.val)

instance goodTuplePredDecidable {n : ℕ} (C : Code n) (k : ℕ → ℕ) (g : Fin 16 → Finset (Fin n)) :
    Decidable (GoodTuplePred C k g) := by
  unfold GoodTuplePred
  infer_instance

/-- The finset of good tuples. -/
def GoodTuples {n : ℕ} (C : Code n) (k : ℕ → ℕ) : Finset (Fin 16 → Finset (Fin n)) :=
  (Finset.univ : Finset (Fin 16 → Finset (Fin n))).filter fun g => GoodTuplePred C k g

/-- The word whose ones-set intersects the type-i columns in the tuple's set. -/
def tupleWord {n : ℕ} (C : Code n) (g : Fin 16 → Finset (Fin n)) : Word n :=
  fun t => if t ∈ g ⟨colVal (C t), Nat.lt_succ_of_le (colVal_le_15 (C t))⟩ then true else false

/-- The ones of `tupleWord C g` on the type-i columns equal the tuple's set. -/
lemma onesOn_tupleWord {n : ℕ} (C : Code n) (k : ℕ → ℕ) (g : Fin 16 → Finset (Fin n))
    (hg : GoodTuplePred C k g) {i : ℕ} (hi : i ∈ Finset.Icc 0 15) :
    onesOn (fiber C i) (tupleWord C g) = g ⟨i, by
      have hi' : i ≤ 15 := (Finset.mem_Icc.mp hi).2
      omega⟩ := by
  ext t
  simp [onesOn, fiber, tupleWord]
  constructor
  · intro ht
    simpa [ht.1] using ht.2
  · intro ht
    have hi' : i < 16 := by
      have hi'' : i ≤ 15 := (Finset.mem_Icc.mp hi).2
      omega
    have hg' : g ⟨i, hi'⟩ ∈ (fiber C i).powersetCard (k i) := hg ⟨i, hi'⟩
    have hsub : g ⟨i, hi'⟩ ⊆ fiber C i := (Finset.mem_powersetCard.mp hg').1
    have ht' : t ∈ fiber C i := hsub ht
    have hcol : colVal (C t) = i := (Finset.mem_filter.mp ht').2
    constructor
    · exact hcol
    · simpa [hcol] using ht

/-- A good word maps to a good tuple. -/
lemma wordTuple_mem {n : ℕ} (C : Code n) (k : ℕ → ℕ) {y : Word n} (hy : y ∈ GoodWords C k) :
    GoodTuplePred C k (wordTuple C y) := by
  intro a
  rw [Finset.mem_powersetCard]
  constructor
  · exact Finset.filter_subset _ _
  · change (onesOn (fiber C a.val) y).card = k a.val
    rw [← w_i_eq_card_onesOn]
    exact (goodWord_iff C k y).1 hy a.val (fin16_val_mem_Icc a)

/-- A good tuple maps to a good word. -/
lemma tupleWord_mem {n : ℕ} (C : Code n) (k : ℕ → ℕ) {g : Fin 16 → Finset (Fin n)}
    (hg : GoodTuplePred C k g) : tupleWord C g ∈ GoodWords C k := by
  apply (goodWord_iff C k (tupleWord C g)).2
  intro i hi
  have hi' : i < 16 := by
    have hi'' : i ≤ 15 := (Finset.mem_Icc.mp hi).2
    omega
  rw [w_i_eq_card_onesOn, onesOn_tupleWord C k g hg hi]
  exact (Finset.mem_powersetCard.mp (hg ⟨i, hi'⟩)).2

/-- Rebuilding a word from its tuple recovers the word. -/
lemma tupleWord_wordTuple {n : ℕ} (C : Code n) (y : Word n) :
    tupleWord C (wordTuple C y) = y := by
  ext t
  simp [tupleWord, wordTuple, onesOn, fiber]

/-- Building a tuple from a tuple-built word recovers the tuple. -/
lemma wordTuple_tupleWord {n : ℕ} (C : Code n) (k : ℕ → ℕ)
    {g : Fin 16 → Finset (Fin n)} (hg : GoodTuplePred C k g) :
    wordTuple C (tupleWord C g) = g := by
  funext a
  change onesOn (fiber C a.val) (tupleWord C g) = g a
  rw [onesOn_tupleWord C k g hg (fin16_val_mem_Icc a)]

/-- Good words and good tuples are equinumerous. -/
lemma goodWords_card {n : ℕ} (C : Code n) (k : ℕ → ℕ) :
    (GoodWords C k).card = (GoodTuples C k).card := by
  let A := {y : Word n // y ∈ GoodWords C k}
  let B := {g : Fin 16 → Finset (Fin n) // g ∈ GoodTuples C k}
  have hA : Fintype.card A = (GoodWords C k).card := by
    change (Finset.univ : Finset A).card = (GoodWords C k).card
    rw [show (Finset.univ : Finset A) = (GoodWords C k).attach by
      ext a
      exact iff_of_true (by simp) (Finset.mem_attach (GoodWords C k) a)]
    exact Finset.card_attach
  have hB : Fintype.card B = (GoodTuples C k).card := by
    change (Finset.univ : Finset B).card = (GoodTuples C k).card
    rw [show (Finset.univ : Finset B) = (GoodTuples C k).attach by
      ext g
      exact iff_of_true (by simp) (Finset.mem_attach (GoodTuples C k) g)]
    exact Finset.card_attach
  have hEq : A ≃ B :=
    { toFun := fun y => ⟨wordTuple C y.1,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, wordTuple_mem C k y.2⟩⟩
      invFun := fun g => ⟨tupleWord C g.1, tupleWord_mem C k (Finset.mem_filter.mp g.2).2⟩
      left_inv := fun y => by
        apply Subtype.ext
        exact tupleWord_wordTuple C y.1
      right_inv := fun g => by
        apply Subtype.ext
        exact wordTuple_tupleWord C k (Finset.mem_filter.mp g.2).2 }
  rw [← hA, ← hB]
  exact Fintype.card_congr hEq

/-- The number of good tuples is the product of binomials. -/
lemma goodTuples_card {n : ℕ} (C : Code n) (k : ℕ → ℕ) :
    (GoodTuples C k).card = ∏ i ∈ Finset.Icc 0 15, Nat.choose (count C i) (k i) := by
  let B := {g : Fin 16 → Finset (Fin n) // g ∈ GoodTuples C k}
  have hB : Fintype.card B = (GoodTuples C k).card := by
    change (Finset.univ : Finset B).card = (GoodTuples C k).card
    rw [show (Finset.univ : Finset B) = (GoodTuples C k).attach by
      ext g
      exact iff_of_true (by simp) (Finset.mem_attach (GoodTuples C k) g)]
    exact Finset.card_attach
  have hsub : ∀ a : Fin 16,
      Fintype.card {S : Finset (Fin n) // S ∈ (fiber C a.val).powersetCard (k a.val)} =
        Nat.choose (count C a.val) (k a.val) := by
    intro a
    change (Finset.univ : Finset {S : Finset (Fin n) // S ∈ (fiber C a.val).powersetCard (k a.val)}).card =
      Nat.choose (count C a.val) (k a.val)
    rw [show (Finset.univ : Finset {S : Finset (Fin n) // S ∈ (fiber C a.val).powersetCard (k a.val)}) =
        ((fiber C a.val).powersetCard (k a.val)).attach by
      ext S
      exact iff_of_true (by simp)
        (Finset.mem_attach ((fiber C a.val).powersetCard (k a.val)) S)]
    rw [Finset.card_attach, Finset.card_powersetCard, fiber_card_eq_count]
  have hEq : B ≃ ((a : Fin 16) →
      {S : Finset (Fin n) // S ∈ (fiber C a.val).powersetCard (k a.val)}) :=
    { toFun := fun g a => ⟨g.1 a, (Finset.mem_filter.mp g.2).2 a⟩
      invFun := fun t => ⟨fun a => (t a).1,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun a => (t a).2⟩⟩
      left_inv := fun g => by
        apply Subtype.ext
        ext a
        rfl
      right_inv := fun t => by
        funext a
        apply Subtype.ext
        rfl }
  rw [← hB]
  rw [Fintype.card_congr hEq, Fintype.card_pi]
  calc
    (∏ a ∈ (Finset.univ : Finset (Fin 16)),
        Fintype.card {S : Finset (Fin n) // S ∈ (fiber C a.val).powersetCard (k a.val)}) =
        ∏ a ∈ (Finset.univ : Finset (Fin 16)), Nat.choose (count C a.val) (k a.val) := by
      apply Finset.prod_congr rfl
      intro a _
      exact hsub a
    _ = ∏ i ∈ Finset.Icc 0 15, Nat.choose (count C i) (k i) := by
      exact Finset.prod_bij
        (fun (a : Fin 16) _ => (a.val : ℕ))
        (by intro a _; exact Finset.mem_Icc.mpr ⟨Nat.zero_le a.val, Nat.le_of_lt_succ a.isLt⟩)
        (by intro a _ b _ h; apply Fin.ext; exact h)
        (by
          intro b hb
          refine ⟨⟨b, ?_⟩, ?_, ?_⟩
          · exact Nat.lt_succ_of_le (Finset.mem_Icc.mp hb).2
          · simp
          · rfl)
        (by intro a _; rfl)

/-- The number of words with prescribed per-type weights is the product of
binomials: Π_i C(|i|, k_i) (paper §3.1 counting fact). -/
lemma count_words_with_prescribed_weights {n : ℕ} (C : Code n) (k : ℕ → ℕ) :
    ((Finset.univ : Finset (Word n)).filter
        fun y : Word n => (∑ i ∈ Finset.Icc 0 15, if w_i C i y = k i then 0 else 1) = 0).card =
      ∏ i ∈ Finset.Icc 0 15, Nat.choose (count C i) (k i) := by
  rw [show ((Finset.univ : Finset (Word n)).filter
        fun y : Word n => (∑ i ∈ Finset.Icc 0 15, if w_i C i y = k i then 0 else 1) = 0) =
      GoodWords C k by
    rfl]
  rw [goodWords_card, goodTuples_card]

/-! ## Worked-example regression checks (paper §2.1) -/

-- native_decide: Contentful · n=any · checked 2026-08-24
-- Values computed by `#eval` (not stated in the paper); they lock the
-- definitions against each other: the 128 = 2^7 words split as
-- 4 + 28 + 52 + 36 + 8 across distances 0..4.
example : alpha example74 0 = 4 := by native_decide
example : alpha example74 1 = 28 := by native_decide
example : alpha example74 2 = 52 := by native_decide
example : alpha example74 3 = 36 := by native_decide
example : alpha example74 4 = 8 := by native_decide
example : alpha example74 5 = 0 := by native_decide
example : alpha example74 6 = 0 := by native_decide
example : alpha example74 7 = 0 := by native_decide
example : (∑ d ∈ Finset.Icc 0 7, alpha example74 d) = 128 := by native_decide

-- Codeword rows read off the paper's matrix: c1 = 0000000, c2 = 0001111,
-- c3 = 0110011, c4 = 1010101; all pairwise distances are 4.
example : hammingWeight (row example74 ⟨0, by decide⟩) = 0 := by native_decide
example : hammingDist (row example74 ⟨0, by decide⟩) (row example74 ⟨1, by decide⟩) = 4 := by
  native_decide
example : hammingDist (row example74 ⟨2, by decide⟩) (row example74 ⟨3, by decide⟩) = 4 := by
  native_decide
example : hammingDist (row example74 ⟨0, by decide⟩) (row example74 ⟨3, by decide⟩) = 4 := by
  native_decide

end N4Code
