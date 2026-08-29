import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Interval
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.Ring.Parity
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Core definitions

Model for "On Optimal Finite-Length Block Codes of Size Four for Binary
Symmetric Channels" (Dong--Yang, IEEE Trans. Inf. Theory 71(1):138–166, 2025).

Representation: an `(n,4)` code is a list of `n` columns, each a 4-bit vector
(`Column := Fin 4 → Bool`).  The paper's type number `colVal c` reproduces the
paper's `bspan{i}` numbering: `colVal (0,0,0,1) = 1`, `(0,0,1,1) = 3`,
`(0,1,0,1) = 5`, `(0,1,1,0) = 6`, `(0,1,1,1) = 7`.

Column-change statements are parameterized by the position `t : Fin n` of the
changed column (the paper's "WLOG the first column"); this avoids requiring
`n ≥ 1` for `0 : Fin n` literals.
-/

open scoped BigOperators

noncomputable section

namespace N4Code

/-! ## Binary words and Hamming distance -/

abbrev Word (n : ℕ) := Fin n → Bool

/-- Bitwise XOR of two words. -/
def bitXor {n : ℕ} (x y : Word n) : Word n := fun i => Bool.xor (x i) (y i)

/-- Hamming weight of a word. -/
def hammingWeight {n : ℕ} (x : Word n) : ℕ :=
  ∑ i ∈ (Finset.univ : Finset (Fin n)), if x i = true then 1 else 0

/-- Hamming distance between two words. -/
def hammingDist {n : ℕ} (x y : Word n) : ℕ := hammingWeight (bitXor x y)

/-! ## Columns and codes -/

/-- A column of an (n,4) code: the four entries (row 1 at index 0). -/
abbrev Column := Fin 4 → Bool

/-- The j-th bit of a column. -/
def colBit (j : Fin 4) (c : Column) : Bool := c j

/-- Type number of a column, matching the paper's `bspan{i}`.
Row 1 (index 0) is the most significant bit: `(b₁ b₂ b₃ b₄) ↦ 8b₁+4b₂+2b₃+b₄`. -/
def colVal (c : Column) : ℕ := ∑ j : Fin 4, if c j then 2 ^ (3 - j.val) else 0

/-- Flipping all bits of a column. -/
def flipCol (c : Column) : Column := fun j => !(c j)

/-- Row permutation acting on a column: new row j carries old row `ρ j`. -/
def rowPermute (ρ : Equiv (Fin 4) (Fin 4)) (c : Column) : Column := fun j => c (ρ j)

/-- An (n,4) code as its columns. -/
abbrev Code (n : ℕ) := Fin n → Column

/-- The j-th codeword (row) of a code. -/
def row {n : ℕ} (C : Code n) (j : Fin 4) : Word n := fun t => colBit j (C t)

def row0 {n : ℕ} (C : Code n) : Word n := row C ⟨0, by decide⟩
def row1 {n : ℕ} (C : Code n) : Word n := row C ⟨1, by decide⟩
def row2 {n : ℕ} (C : Code n) : Word n := row C ⟨2, by decide⟩
def row3 {n : ℕ} (C : Code n) : Word n := row C ⟨3, by decide⟩

/-- The four codewords of a code are pairwise distinct (a genuine `(n,4)`
code). -/
def DistinctRows {n : ℕ} (C : Code n) : Prop :=
  ∀ i j : Fin 4, i ≠ j → row C i ≠ row C j

/-- |i|_C: number of columns of type i. -/
def count {n : ℕ} (C : Code n) (i : ℕ) : ℕ :=
  ∑ t : Fin n, if colVal (C t) = i then 1 else 0

/-- Sum of |i|_C over a set of types. -/
def totalCounts {n : ℕ} (C : Code n) (types : Finset ℕ) : ℕ :=
  ∑ i ∈ types, count C i

/-- Number of positions in `s` where y is 1. -/
def weightOn {n : ℕ} (y : Word n) (s : Finset (Fin n)) : ℕ :=
  (s.filter fun t => y t = true).card

/-- w_i(y): number of ones of y in the positions where C has type-i columns. -/
def w_i {n : ℕ} (C : Code n) (i : ℕ) (y : Word n) : ℕ :=
  weightOn y (Finset.univ.filter fun t => colVal (C t) = i)

/-- d_j(y): Hamming distance from y to the j-th codeword. -/
def dRow {n : ℕ} (C : Code n) (j : Fin 4) (y : Word n) : ℕ := hammingDist (row C j) y

/-- d_C(y): minimum distance from y to the code (M = 4). -/
def dCode {n : ℕ} (C : Code n) (y : Word n) : ℕ :=
  min (hammingDist (row0 C) y)
    (min (hammingDist (row1 C) y) (min (hammingDist (row2 C) y) (hammingDist (row3 C) y)))

/-- α_C(d): number of y with d_C(y) = d. -/
def alpha {n : ℕ} (C : Code n) (d : ℕ) : ℕ :=
  ∑ y : Word n, if dCode C y = d then 1 else 0

/-- λ_C(ε): average correct-decoding probability under ML decoding. -/
def lambda {n : ℕ} (C : Code n) (ε : ℝ) : ℝ :=
  (1 / 4 : ℝ) * ∑ y : Word n, (1 - ε) ^ (n - dCode C y) * ε ^ (dCode C y)

/-! ## Universal comparison -/

/-- λ_{C₁} ≥ λ_{C₂} for all 0 < ε < 1/2. -/
def UniversalBetter {n : ℕ} (C₁ C₂ : Code n) : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 1 / 2 → lambda C₁ ε ≥ lambda C₂ ε

/-- λ_{C₁} > λ_{C₂} for all 0 < ε < 1/2. -/
def UniversalStrictBetter {n : ℕ} (C₁ C₂ : Code n) : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 1 / 2 → lambda C₁ ε > lambda C₂ ε

/-- λ_{C₁} = λ_{C₂} for all 0 < ε < 1/2. -/
def UniversalEqual {n : ℕ} (C₁ C₂ : Code n) : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 1 / 2 → lambda C₁ ε = lambda C₂ ε

/-- Optimality at a fixed crossover probability ε. -/
def OptimalAt {n : ℕ} (C : Code n) (ε : ℝ) : Prop :=
  ∀ D : Code n, lambda C ε ≥ lambda D ε

/-! ## Equivalence (row/column permutations, column flips) -/

/-- C' is equivalent to C (paper Def. in §2.1). -/
def Equivalent {n : ℕ} (C C' : Code n) : Prop :=
  ∃ ρ : Equiv (Fin 4) (Fin 4), ∃ p : Equiv (Fin n) (Fin n), ∃ f : Fin n → Bool,
    ∀ t : Fin n, C' (p t) = rowPermute ρ (if f t then flipCol (C t) else C t)

/-! ## The special column types -/

def col0 : Column := fun _ => false
def col1 : Column := fun j => j.val = 3
def col3 : Column := fun j => j.val = 2 ∨ j.val = 3
def col5 : Column := fun j => j.val = 1 ∨ j.val = 3
def col6 : Column := fun j => j.val = 1 ∨ j.val = 2
def col7 : Column := fun j => j.val = 1 ∨ j.val = 2 ∨ j.val = 3

-- native_decide: Mechanical · n=any · checked 2026-08-24
/-- Sanity checks: the `colVal` numbering matches the paper's `bspan{i}`. -/
example : colVal col0 = 0 := by native_decide
example : colVal col1 = 1 := by native_decide
example : colVal col3 = 3 := by native_decide
example : colVal col5 = 5 := by native_decide
example : colVal col6 = 6 := by native_decide
example : colVal col7 = 7 := by native_decide

/-- Columns restricted to the paper's types 0..7 (row-1 bit is 0). -/
def Columns07 {n : ℕ} (C : Code n) : Prop := ∀ t : Fin n, C t 0 = false

/-! ## Code classes (paper §2.3, §3.4) -/

/-- Linear (n,4) code: only types 3,5,6, at least two of them positive. -/
def IsLinear {n : ℕ} (C : Code n) : Prop :=
  (∀ t : Fin n, colVal (C t) = 0 ∨ colVal (C t) = 3 ∨ colVal (C t) = 5 ∨ colVal (C t) = 6) ∧
    ((count C 3 > 0 ∧ count C 5 > 0) ∨ (count C 3 > 0 ∧ count C 6 > 0) ∨
      (count C 5 > 0 ∧ count C 6 > 0))

/-- Class-I: |1| odd, |3|,|5|,|6| of the same parity, and |1|+|3|+|5|+|6| = n. -/
def ClassI {n : ℕ} (C : Code n) : Prop :=
  Odd (count C 1) ∧
    ((Even (count C 3) ∧ Even (count C 5) ∧ Even (count C 6)) ∨
      (Odd (count C 3) ∧ Odd (count C 5) ∧ Odd (count C 6))) ∧
    totalCounts C {1, 3, 5, 6} = n

/-- Class-II: |1| > 0, |1|+|3|+|5|+|6| = n, and parity condition (a) or (b). -/
def ClassII {n : ℕ} (C : Code n) : Prop :=
  count C 1 > 0 ∧ totalCounts C {1, 3, 5, 6} = n ∧
    ((Even (count C 1) ∧ Even (count C 3) ∧ Odd (count C 5) ∧ Odd (count C 6)) ∨
      (Even (count C 1) ∧ Odd (count C 3) ∧ Even (count C 5) ∧ Even (count C 6)))

/-- Class-III: |1|+|3|+|5|+|6|+|7| = n and condition (a) or (b). -/
def ClassIII {n : ℕ} (C : Code n) : Prop :=
  totalCounts C {1, 3, 5, 6, 7} = n ∧
    ((count C 1 = 1 ∧ count C 7 = 1 ∧ count C 6 = 0 ∧ Even (count C 3) ∧
        Odd (count C 5)) ∨
      (count C 1 = 1 ∧ count C 5 = 0 ∧ count C 7 = 0 ∧ Odd (count C 3) ∧
        Odd (count C 6)))

/-- Same parity for three numbers. -/
def SameParity (a b c : ℕ) : Prop :=
  (Even a ↔ Even b) ∧ (Even b ↔ Even c)

/-! ## Linear representative C(n3,n5,n6) -/

/-- The code with n₃ columns of type 3, then n₅ of type 5, then n₆ of type 6. -/
def linearCode (n3 n5 n6 : ℕ) : Code (n3 + n5 + n6) :=
  fun t =>
    if t.val < n3 then col3
    else if t.val < n3 + n5 then col5
    else col6

/-! ## Column change helpers -/

/-- Flip the bit of y at position t. -/
def flipBit {n : ℕ} (t : Fin n) (y : Word n) : Word n :=
  fun u => if u = t then !(y u) else y u

/-- Flip the bits of y at positions t₁ and t₂. -/
def flipTwoBits {n : ℕ} (t₁ t₂ : Fin n) (y : Word n) : Word n :=
  fun u => if u = t₁ ∨ u = t₂ then !(y u) else y u

/-- Replace the column at position t by s'. -/
def replaceColumn {n : ℕ} (C : Code n) (t : Fin n) (s' : Column) : Code n :=
  fun u => if u = t then s' else C u

/-! ## One-column change (paper §3.2) -/

/-- d_O = min of rows {1,2,4} (rows 0,1,3). -/
def dO {n : ℕ} (C : Code n) (y : Word n) : ℕ :=
  min (hammingDist (row0 C) y) (min (hammingDist (row1 C) y) (hammingDist (row3 C) y))

/-- d_P with P = {3} (row 2). -/
def dP {n : ℕ} (C : Code n) (y : Word n) : ℕ := hammingDist (row2 C) y

/-- d_O(F_t y): the primed O-distance, paper eq. (69) (manuscript eq:dprim). -/
def dOp {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) : ℕ := dO C (flipBit t y)

/-- d_P(F_t y): the primed P-distance, paper eq. (69) (manuscript eq:dprim). -/
def dPp {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) : ℕ := dP C (flipBit t y)

/-- d_O(F_{t₁,t₂} y): the primed O-distance for two flips. -/
def dOp2 {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (y : Word n) : ℕ := dO C (flipTwoBits t₁ t₂ y)

/-- d_P(F_{t₁,t₂} y): the primed P-distance for two flips. -/
def dPp2 {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (y : Word n) : ℕ := dP C (flipTwoBits t₁ t₂ y)

/-- The five sets Y1..Y5 of eq.(y1)-(y5); t is the changed column. -/
def Y1 {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) : Prop :=
  (dO C y ≤ dP C y ∧ dP C y < dPp C t y) ∨
    (dO C y ≤ dPp C t y ∧ dPp C t y ≤ dP C y ∧ dOp C t y ≤ dPp C t y)

def Y2 {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) : Prop :=
  (dP C y ≤ dPp C t y ∧ dP C y < dO C y) ∨
    (dPp C t y < dP C y ∧ dP C y ≤ dO C y ∧ dP C y ≤ dOp C t y)

def Y3 {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) : Prop :=
  dPp C t y = dOp C t y ∧ dPp C t y < dP C y ∧ dP C y = dO C y

def Y4 {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) : Prop :=
  dP C y = dPp C t y ∧ dPp C t y = dO C y ∧ dO C y < dOp C t y

def Y5 {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) : Prop :=
  dPp C t y = dO C y ∧ dOp C t y = dP C y ∧ dO C y < dOp C t y

instance decY1 {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) : Decidable (Y1 C t y) := by
  unfold Y1; infer_instance
instance decY2 {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) : Decidable (Y2 C t y) := by
  unfold Y2; infer_instance
instance decY3 {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) : Decidable (Y3 C t y) := by
  unfold Y3; infer_instance
instance decY4 {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) : Decidable (Y4 C t y) := by
  unfold Y4; infer_instance
instance decY5 {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) : Decidable (Y5 C t y) := by
  unfold Y5; infer_instance

/-- Y_i as a Fin 5-indexed predicate. -/
def YSet {n : ℕ} (C : Code n) (t : Fin n) (i : Fin 5) (y : Word n) : Prop :=
  if i.val = 0 then Y1 C t y
  else if i.val = 1 then Y2 C t y
  else if i.val = 2 then Y3 C t y
  else if i.val = 3 then Y4 C t y
  else Y5 C t y

/-- The mapping g1 of §3.2; t is the changed column. -/
def g1 {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) : Word n :=
  if Y1 C t y ∨ Y3 C t y then y else flipBit t y

/-- α_C³(d): y in Y3 with d_C(y) = d. -/
def alpha3 {n : ℕ} (C : Code n) (t : Fin n) (d : ℕ) : ℕ :=
  (Finset.univ.filter fun y : Word n => Y3 C t y ∧ dCode C y = d).card

/-- α_C⁵(d): y in Y5 with d_C(y) = d. -/
def alpha5 {n : ℕ} (C : Code n) (t : Fin n) (d : ℕ) : ℕ :=
  (Finset.univ.filter fun y : Word n => Y5 C t y ∧ dCode C y = d).card

/-- Ψ_d := Σ_{i≤d} α³(i) − Σ_{i<d} α⁵(i) (integer, to allow sign). -/
def Psi {n : ℕ} (C : Code n) (t : Fin n) (d : ℕ) : ℤ :=
  (∑ i ∈ Finset.Icc 1 d, (alpha3 C t i : ℤ)) -
    ∑ i ∈ Finset.Icc 0 (d - 1), (alpha5 C t i : ℤ)

/-! ## Two-column change (paper §4) -/

/-- The five sets Z1..Z5 of eq.(y21)-(y25); t₁,t₂ are the changed columns.

The paper's eq. (y25) prints `Z₅` with the same conditions as `Z₄` (making the
partition claim false).  Following the paper's own proof (`eq:y45`, `eq:ineq2`,
`eq:ineq3`, and the set `A₁`), the intended split of the region
`B := y₁≠y₂ ∧ d_O > d_P ∧ d_P' ∧ d_P > d_O ∧ d_O'` is:
`Z₄ = B ∩ {d_P' < d_O ∧ d_O'}`, `Z₅ = B ∩ {d_O ∧ d_O' ≤ d_P'}`.  See
`Notation.md` §4 item 7. -/
def Z1 {n : ℕ} (_C : Code n) (t₁ t₂ : Fin n) (y : Word n) : Prop := y t₁ = y t₂

def Z2 {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (y : Word n) : Prop :=
  y t₁ ≠ y t₂ ∧ dO C y ≤ min (dP C y) (dPp2 C t₁ t₂ y)

def Z3 {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (y : Word n) : Prop :=
  y t₁ ≠ y t₂ ∧ dO C y > min (dP C y) (dPp2 C t₁ t₂ y) ∧
    dP C y ≤ min (dO C y) (dOp2 C t₁ t₂ y)

def Z4 {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (y : Word n) : Prop :=
  y t₁ ≠ y t₂ ∧ dO C y > min (dP C y) (dPp2 C t₁ t₂ y) ∧
    dP C y > min (dO C y) (dOp2 C t₁ t₂ y) ∧
    dPp2 C t₁ t₂ y < min (dO C y) (dOp2 C t₁ t₂ y)

def Z5 {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (y : Word n) : Prop :=
  y t₁ ≠ y t₂ ∧ dO C y > min (dP C y) (dPp2 C t₁ t₂ y) ∧
    dP C y > min (dO C y) (dOp2 C t₁ t₂ y) ∧
    min (dO C y) (dOp2 C t₁ t₂ y) ≤ dPp2 C t₁ t₂ y

/-- Z4¹ := Z4 with the extra condition min(d_O, d_P) > d_O'. -/
def Z41 {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (y : Word n) : Prop :=
  Z4 C t₁ t₂ y ∧ min (dO C y) (dP C y) > dOp2 C t₁ t₂ y

instance decZ1 {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (y : Word n) :
    Decidable (Z1 C t₁ t₂ y) := by
  unfold Z1; infer_instance
instance decZ2 {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (y : Word n) :
    Decidable (Z2 C t₁ t₂ y) := by
  unfold Z2; infer_instance
instance decZ3 {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (y : Word n) :
    Decidable (Z3 C t₁ t₂ y) := by
  unfold Z3; infer_instance
instance decZ4 {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (y : Word n) :
    Decidable (Z4 C t₁ t₂ y) := by
  unfold Z4; infer_instance
instance decZ5 {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (y : Word n) :
    Decidable (Z5 C t₁ t₂ y) := by
  unfold Z5; infer_instance

instance decZ41 {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (y : Word n) :
    Decidable (Z41 C t₁ t₂ y) := by
  unfold Z41; infer_instance

/-- Z_i as a Fin 5-indexed predicate. -/
def ZSet {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (i : Fin 5) (y : Word n) : Prop :=
  if i.val = 0 then Z1 C t₁ t₂ y
  else if i.val = 1 then Z2 C t₁ t₂ y
  else if i.val = 2 then Z3 C t₁ t₂ y
  else if i.val = 3 then Z4 C t₁ t₂ y
  else Z5 C t₁ t₂ y

/-- The mapping g2 of §4; t₁,t₂ are the changed columns. -/
def g2 {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (y : Word n) : Word n :=
  if Z1 C t₁ t₂ y ∨ Z2 C t₁ t₂ y ∨ Z5 C t₁ t₂ y then y
  else flipTwoBits t₁ t₂ y

/-! ## Helper for the Class-I theorems -/

/-- s = argmin over {3,5,6} of |i|_C (ties broken in the order 3, 5, 6). -/
def argminType {n : ℕ} (C : Code n) : Column :=
  if count C 3 ≤ count C 5 ∧ count C 3 ≤ count C 6 then col3
  else if count C 5 ≤ count C 6 then col5
  else col6

/-! ## Explicit codes used in the n = 3 classification (thm:n8) -/

/-- C_A of eq.(eq:0columnlinear): columns (3, 5, 0). -/
def CA : Code 3 := fun t =>
  if t.val = 0 then col3 else if t.val = 1 then col5 else col0

/-- The code with columns (1, 5, 7) (first matrix in eq.(eq:2)). -/
def code135 : Code 3 := fun t =>
  if t.val = 0 then col1 else if t.val = 1 then col5 else col7

/-- The code with columns (1, 3, 6) (second matrix in eq.(eq:2)). -/
def code136 : Code 3 := fun t =>
  if t.val = 0 then col1 else if t.val = 1 then col3 else col6

/-- The five-code set of thm:n8 for n = 3. -/
def InOptimal3 (C : Code 3) : Prop :=
  C = code135 ∨ C = code136 ∨ C = CA ∨ C = linearCode 1 1 1 ∨ C = linearCode 1 2 0

/-! ## Paper worked example (§2.1): the (7,4) code with columns bspan{1}..bspan{7} -/

/-- The column with type number i (bits read MSB-first, matching `colVal`). -/
def colOfNat (i : ℕ) : Column := fun j => i.testBit (3 - j.val)

-- native_decide: Mechanical · n=any · checked 2026-08-24
/-- Bit j of a column equals bit `3 - j.val` of its type number (row 1 = MSB). -/
lemma colBit_eq_testBit (c : Column) (j : Fin 4) :
    colBit j c = (colVal c).testBit (3 - j.val) := by
  have h : ∀ (c : Column) (j : Fin 4),
      colBit j c = (colVal c).testBit (3 - j.val) := by
    native_decide
  exact h c j

/-- Rebuilding a column from its type number recovers the column. -/
lemma colOfNat_colVal (c : Column) : colOfNat (colVal c) = c := by
  funext r
  simpa [colBit, colOfNat] using (colBit_eq_testBit c r).symm

-- native_decide: Mechanical · n=any · checked 2026-08-24
/-- A column has value 1 exactly when it is `col1`. -/
lemma colVal_eq_one_iff_col1 (c : Column) : colVal c = 1 ↔ c = col1 := by
  constructor
  · intro h
    funext j
    fin_cases j
    · change colBit ⟨0, by decide⟩ c = false
      rw [colBit_eq_testBit, h]
      native_decide
    · change colBit ⟨1, by decide⟩ c = false
      rw [colBit_eq_testBit, h]
      native_decide
    · change colBit ⟨2, by decide⟩ c = false
      rw [colBit_eq_testBit, h]
      native_decide
    · change colBit ⟨3, by decide⟩ c = true
      rw [colBit_eq_testBit, h]
      native_decide
  · intro h
    rw [h]
    native_decide

-- native_decide: Mechanical · n=any · checked 2026-08-24
/-- A column has value 3 exactly when it is `col3`. -/
lemma colVal_eq_three_iff_col3 (c : Column) : colVal c = 3 ↔ c = col3 := by
  constructor
  · intro h; rw [← colOfNat_colVal c, h]; native_decide
  · intro h; rw [h]; native_decide

-- native_decide: Mechanical · n=any · checked 2026-08-24
/-- A column has value 5 exactly when it is `col5`. -/
lemma colVal_eq_five_iff_col5 (c : Column) : colVal c = 5 ↔ c = col5 := by
  constructor
  · intro h; rw [← colOfNat_colVal c, h]; native_decide
  · intro h; rw [h]; native_decide

-- native_decide: Mechanical · n=any · checked 2026-08-24
/-- A column has value 6 exactly when it is `col6`. -/
lemma colVal_eq_six_iff_col6 (c : Column) : colVal c = 6 ↔ c = col6 := by
  constructor
  · intro h; rw [← colOfNat_colVal c, h]; native_decide
  · intro h; rw [h]; native_decide

/-- The paper's (7,4) example code: column t has type t.val + 1. -/
def example74 : Code 7 := fun t => colOfNat (t.val + 1)

-- native_decide: Mechanical · n=any · checked 2026-08-24
/-- Consistency: |i| = 1 for every type i = 1..7 in the worked example. -/
example : count example74 1 = 1 := by native_decide
example : count example74 2 = 1 := by native_decide
example : count example74 3 = 1 := by native_decide
example : count example74 4 = 1 := by native_decide
example : count example74 5 = 1 := by native_decide
example : count example74 6 = 1 := by native_decide
example : count example74 7 = 1 := by native_decide
example : (∑ i ∈ Finset.Icc 1 7, count example74 i) = 7 := by native_decide

end N4Code
