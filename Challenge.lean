import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Ring.Parity
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Advertised statement

The paper results submitted here are Theorems 1--5 of Dong--Yang, *On
Optimal Finite-Length Block Codes of Size Four for Binary Symmetric
Channels*.  The Lean statements use the equivalent strict-improvement
contrapositive forms: a code that is not equivalent to the relevant optimal
family is universally strictly dominated.

The definitions below are the small, auditable statement surface.  They are
deliberately self-contained; the proof in `Solution.lean` imports the full
`N4Code` development and proves this same declaration.
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

/-- A column of an `(n,4)` code: the four entries, row 1 at index 0. -/
abbrev Column := Fin 4 → Bool

/-- The `j`-th bit of a column. -/
def colBit (j : Fin 4) (c : Column) : Bool := c j

/-- Type number of a column, matching the paper's `bspan{i}` numbering:
row 1 (index 0) is the most significant bit. -/
def colVal (c : Column) : ℕ := ∑ j : Fin 4, if c j then 2 ^ (3 - j.val) else 0

/-- Flipping all bits of a column. -/
def flipCol (c : Column) : Column := fun j => !(c j)

/-- Row permutation acting on a column. -/
def rowPermute (ρ : Equiv (Fin 4) (Fin 4)) (c : Column) : Column := fun j => c (ρ j)

/-- An `(n,4)` code as its columns. -/
abbrev Code (n : ℕ) := Fin n → Column

/-- The `j`-th codeword (row) of a code. -/
def row {n : ℕ} (C : Code n) (j : Fin 4) : Word n := fun t => colBit j (C t)

def row0 {n : ℕ} (C : Code n) : Word n := row C ⟨0, by decide⟩
def row1 {n : ℕ} (C : Code n) : Word n := row C ⟨1, by decide⟩
def row2 {n : ℕ} (C : Code n) : Word n := row C ⟨2, by decide⟩
def row3 {n : ℕ} (C : Code n) : Word n := row C ⟨3, by decide⟩

/-- `d_C(y)`: minimum distance from `y` to the code (`M = 4`). -/
def dCode {n : ℕ} (C : Code n) (y : Word n) : ℕ :=
  min (hammingDist (row0 C) y)
    (min (hammingDist (row1 C) y) (min (hammingDist (row2 C) y) (hammingDist (row3 C) y)))

/-- `λ_C(ε)`: average correct-decoding probability under ML decoding. -/
def lambda {n : ℕ} (C : Code n) (ε : ℝ) : ℝ :=
  (1 / 4 : ℝ) * ∑ y : Word n, (1 - ε) ^ (n - dCode C y) * ε ^ (dCode C y)

/-- `λ_{C₁} ≥ λ_{C₂}` for all `0 < ε < 1/2`. -/
def UniversalBetter {n : ℕ} (C₁ C₂ : Code n) : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 1 / 2 → lambda C₁ ε ≥ lambda C₂ ε

/-- `λ_{C₁} > λ_{C₂}` for all `0 < ε < 1/2`. -/
def UniversalStrictBetter {n : ℕ} (C₁ C₂ : Code n) : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 1 / 2 → lambda C₁ ε > lambda C₂ ε

/-- Optimality at a fixed crossover probability `ε`. -/
def OptimalAt {n : ℕ} (C : Code n) (ε : ℝ) : Prop :=
  ∀ D : Code n, lambda C ε ≥ lambda D ε

/-! ## Column-type counts and code classes -/

/-- `|i|_C`: number of columns of type `i`. -/
def count {n : ℕ} (C : Code n) (i : ℕ) : ℕ :=
  ∑ t : Fin n, if colVal (C t) = i then 1 else 0

/-- Sum of `|i|_C` over a set of types. -/
def totalCounts {n : ℕ} (C : Code n) (types : Finset ℕ) : ℕ :=
  ∑ i ∈ types, count C i

/-- The special column types. -/
def col0 : Column := fun _ => false
def col1 : Column := fun j => j.val = 3
def col3 : Column := fun j => j.val = 2 ∨ j.val = 3
def col5 : Column := fun j => j.val = 1 ∨ j.val = 3
def col6 : Column := fun j => j.val = 1 ∨ j.val = 2
def col7 : Column := fun j => j.val = 1 ∨ j.val = 2 ∨ j.val = 3

/-- Linear `(n,4)` code: only types 3,5,6, with at least two of them positive. -/
def IsLinear {n : ℕ} (C : Code n) : Prop :=
  (∀ t : Fin n, colVal (C t) = 0 ∨ colVal (C t) = 3 ∨ colVal (C t) = 5 ∨ colVal (C t) = 6) ∧
    ((count C 3 > 0 ∧ count C 5 > 0) ∨ (count C 3 > 0 ∧ count C 6 > 0) ∨
      (count C 5 > 0 ∧ count C 6 > 0))

/-- Class-I: `|1|` odd, `|3|,|5|,|6|` of the same parity, and
`|1|+|3|+|5|+|6| = n`. -/
def ClassI {n : ℕ} (C : Code n) : Prop :=
  Odd (count C 1) ∧
    ((Even (count C 3) ∧ Even (count C 5) ∧ Even (count C 6)) ∨
      (Odd (count C 3) ∧ Odd (count C 5) ∧ Odd (count C 6))) ∧
    totalCounts C {1, 3, 5, 6} = n

/-- Class-II: `|1| > 0`, `|1|+|3|+|5|+|6| = n`, and one of the two parity
conditions from the paper. -/
def ClassII {n : ℕ} (C : Code n) : Prop :=
  count C 1 > 0 ∧ totalCounts C {1, 3, 5, 6} = n ∧
    ((Even (count C 1) ∧ Even (count C 3) ∧ Odd (count C 5) ∧ Odd (count C 6)) ∨
      (Even (count C 1) ∧ Odd (count C 3) ∧ Even (count C 5) ∧ Even (count C 6)))

/-- Equivalence of codes by row/column permutations and column flips. -/
def Equivalent {n : ℕ} (C C' : Code n) : Prop :=
  ∃ ρ : Equiv (Fin 4) (Fin 4), ∃ p : Equiv (Fin n) (Fin n), ∃ f : Fin n → Bool,
    ∀ t : Fin n, C' (p t) = rowPermute ρ (if f t then flipCol (C t) else C t)

/-- Replace the column at position `t` by `s'`. -/
def replaceColumn {n : ℕ} (C : Code n) (t : Fin n) (s' : Column) : Code n :=
  fun u => if u = t then s' else C u

/-- `s = argmin` over `{3,5,6}` of `|i|_C`, with ties broken as `3,5,6`. -/
def argminType {n : ℕ} (C : Code n) : Column :=
  if count C 3 ≤ count C 5 ∧ count C 3 ≤ count C 6 then col3
  else if count C 5 ≤ count C 6 then col5
  else col6

/-! ## Linear representative and the explicit `n = 3` codes -/

/-- The code with `n3` columns of type 3, then `n5` of type 5, then `n6` of type 6. -/
def linearCode (n3 n5 n6 : ℕ) : Code (n3 + n5 + n6) :=
  fun t =>
    if t.val < n3 then col3
    else if t.val < n3 + n5 then col5
    else col6

/-- The canonical code for counts `(a,b,c)` as a code of length `n`. -/
def linCode {n : ℕ} (a b c : ℕ) (h : a + b + c = n) : Code n :=
  cast (congrArg Code h) (linearCode a b c)

/-- `C_A` of eq.(eq:0columnlinear): columns `(3, 5, 0)`. -/
def CA : Code 3 := fun t =>
  if t.val = 0 then col3 else if t.val = 1 then col5 else col0

/-- The code with columns `(1, 5, 7)`. -/
def code135 : Code 3 := fun t =>
  if t.val = 0 then col1 else if t.val = 1 then col5 else col7

/-- The code with columns `(1, 3, 6)`. -/
def code136 : Code 3 := fun t =>
  if t.val = 0 then col1 else if t.val = 1 then col3 else col6

/-- The five-code set of Theorem 5 for `n = 3`. -/
def InOptimal3 (C : Code 3) : Prop :=
  C = code135 ∨ C = code136 ∨ C = CA ∨ C = linearCode 1 1 1 ∨ C = linearCode 1 2 0

/-! ## Theorems 1--5 of the paper -/

/-- Theorem `thm:two` (Theorem 1): for every crossover probability there is an
optimal `(n,4)` code that is linear or Class-I. -/
theorem palomar_thm1 (n : ℕ) (hn : 2 ≤ n) :
    ∀ ε : ℝ, 0 < ε → ε < 1 / 2 →
      ∃ C : Code n, (IsLinear C ∨ ClassI C) ∧ OptimalAt C ε := by
  sorry

/-- Theorem `thm:linearopt` (Theorem 2), residue `n = 3k - 1`. -/
theorem palomar_thm2_residue2 {k : ℕ} (hk : k ≥ 1) :
    ∀ D : Code (k + k + (k - 1)), IsLinear D →
      ¬ Equivalent (linearCode k k (k - 1)) D →
        UniversalStrictBetter (linearCode k k (k - 1)) D := by
  sorry

/-- Theorem `thm:linearopt` (Theorem 2), `n = 3`. -/
theorem palomar_thm2_n3 :
    ∀ D : Code 3, IsLinear D →
      ¬ Equivalent CA D → ¬ Equivalent (linearCode 1 1 1) D → ¬ Equivalent (linearCode 1 2 0) D →
        UniversalStrictBetter CA D ∧
          UniversalStrictBetter (linearCode 1 1 1) D ∧
            UniversalStrictBetter (linearCode 1 2 0) D := by
  sorry

/-- Theorem `thm:linearopt` (Theorem 2), residue `n = 3k` with `k ≥ 2`. -/
theorem palomar_thm2_residue0 {k : ℕ} (hk : k ≥ 2) :
    (∀ D : Code (k + 1 + k + (k - 1)), IsLinear D →
        ¬ Equivalent (linCode (k + 1) (k + 1) (k - 2) (by omega)) D →
        ¬ Equivalent (linCode (k + 1) k (k - 1) (by omega)) D →
          UniversalStrictBetter (linCode (k + 1) (k + 1) (k - 2) (by omega)) D) ∧
      (∀ D : Code (k + 1 + k + (k - 1)), IsLinear D →
        ¬ Equivalent (linCode (k + 1) (k + 1) (k - 2) (by omega)) D →
        ¬ Equivalent (linCode (k + 1) k (k - 1) (by omega)) D →
          UniversalStrictBetter (linCode (k + 1) k (k - 1) (by omega)) D) := by
  sorry

/-- Theorem `thm:linearopt` (Theorem 2), residue `n = 3k + 1`. -/
theorem palomar_thm2_residue1 {k : ℕ} (hk : k ≥ 1) :
    (∀ D : Code (k + 1 + k + k), IsLinear D →
        ¬ Equivalent (linCode (k + 1) k k (by omega)) D →
        ¬ Equivalent (linCode (k + 2) k (k - 1) (by omega)) D →
          UniversalStrictBetter (linCode (k + 1) k k (by omega)) D) ∧
      (∀ D : Code (k + 1 + k + k), IsLinear D →
        ¬ Equivalent (linCode (k + 1) k k (by omega)) D →
        ¬ Equivalent (linCode (k + 2) k (k - 1) (by omega)) D →
          UniversalStrictBetter (linCode (k + 2) k (k - 1) (by omega)) D) := by
  sorry

/-- Theorem `thm:nbig3` (Theorem 3): if `C` is not equivalent to a linear,
Class-I, or Class-II code, then some code is universally strictly better. -/
theorem palomar_thm3 (n : ℕ) (hn : n > 3) (C : Code n)
    (hnot : ∀ C' : Code n, Equivalent C C' →
      ¬ (IsLinear C' ∨ ClassI C' ∨ ClassII C')) :
    ∃ D : Code n, UniversalStrictBetter D C := by
  sorry

/-- Theorem `thm:condition_optimalcode` (Theorem 4): under the stated Class-I
condition, any code not equivalent to a linear code is universally strictly
dominated. -/
theorem palomar_thm4 (n : ℕ) (hn : n > 3)
    (hcond : ∀ C : Code n, ClassI C → count C 1 ≥ 3 →
      ∀ t : Fin n, C t = col1 →
        UniversalBetter (replaceColumn C t (argminType C)) C) :
    ∀ C : Code n,
      (∀ C' : Code n, Equivalent C C' → ¬ IsLinear C') →
        ∃ D : Code n, UniversalStrictBetter D C := by
  sorry

/-- Theorem `thm:n8` (Theorem 5): for `2 ≤ n ≤ 8`, every optimal code is
equivalent to a linear code, with the explicit five-code classification for
`n = 3`. -/
theorem palomar_thm5 (n : ℕ) (hn2 : 2 ≤ n) (hn8 : n ≤ 8) :
    (n ≠ 3 → ∀ C : Code n,
      (∀ C' : Code n, Equivalent C C' → ¬ IsLinear C') →
        ∃ D : Code n, UniversalStrictBetter D C) ∧
      (n = 3 → ∀ C : Code 3,
        (∀ C' : Code 3, Equivalent C C' → ¬ InOptimal3 C') →
          ∃ D : Code 3, UniversalStrictBetter D C) := by
  sorry

end N4Code
