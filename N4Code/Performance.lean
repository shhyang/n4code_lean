import N4Code.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Positivity

/-!
# Phase B: performance facts

The strict monotonicity of the decoding-probability weight in the distance
(used by `thm:com` (Lemma 18)), and the invariance of α and λ under code equivalence
(row/column permutations and column flips).
-/

open scoped BigOperators

namespace N4Code

/-! ## The decoding-probability weight is strictly decreasing in distance -/

/-- The contribution of a word at distance x to λ_C(ε). -/
def weight (n : ℕ) (ε : ℝ) (x : ℕ) : ℝ := (1 - ε) ^ (n - x) * ε ^ x

/-- Moving one step further from the code strictly decreases the weight. -/
lemma weight_step {n : ℕ} {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1 / 2) (x : ℕ) :
    weight n ε (x + 1) < weight n ε x := by
  by_cases hx : x < n
  · have hn : n - (x + 1) = n - x - 1 := by omega
    have hn' : n - x = (n - x - 1) + 1 := by omega
    have hεlt : ε < 1 - ε := by linarith
    have hpos1 : 0 < 1 - ε := by nlinarith [hε1]
    have hposE : 0 < ε ^ x := by positivity
    calc
      (1 - ε) ^ (n - (x + 1)) * ε ^ (x + 1)
          = (1 - ε) ^ (n - x - 1) * (ε ^ x * ε) := by rw [hn, pow_succ]
      _ = ((1 - ε) ^ (n - x - 1) * ε ^ x) * ε := by ring
      _ < ((1 - ε) ^ (n - x - 1) * ε ^ x) * (1 - ε) := by
            exact mul_lt_mul_of_pos_left hεlt (by positivity : 0 < (1 - ε) ^ (n - x - 1) * ε ^ x)
      _ = (1 - ε) ^ (n - x) * ε ^ x := by
            have hmul : ((1 - ε) ^ (n - x - 1) * ε ^ x) * (1 - ε) =
                ((1 - ε) ^ (n - x - 1) * (1 - ε)) * ε ^ x := by ring
            rw [hmul]
            rw [← pow_succ]
            rw [show (n - x - 1) + 1 = n - x by omega]
  · have hn1 : n - (x + 1) = 0 := by omega
    have hn2 : n - x = 0 := by omega
    have hεlt1 : ε < 1 := by nlinarith [hε1]
    calc
      (1 - ε) ^ (n - (x + 1)) * ε ^ (x + 1)
          = ε ^ (x + 1) := by rw [hn1, pow_zero, one_mul]
      _ < ε ^ x := by
            rw [pow_succ]
            calc
              ε ^ x * ε < ε ^ x * 1 := by
                    exact mul_lt_mul_of_pos_left hεlt1 (by positivity : 0 < ε ^ x)
              _ = ε ^ x := by rw [mul_one]
      _ = (1 - ε) ^ (n - x) * ε ^ x := by rw [hn2, pow_zero, one_mul]

/-- The weight is strictly decreasing in the distance (paper proof of `thm:com` (Lemma 18)). -/
lemma weight_strictAnti {n : ℕ} {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1 / 2) :
    ∀ {a b : ℕ}, a < b → weight n ε b < weight n ε a := by
  intro a b hab
  have hk : b = a + (b - a - 1) + 1 := by omega
  rw [hk]
  have hiter : ∀ k : ℕ, weight n ε (a + k + 1) < weight n ε a := by
    intro k
    induction k with
    | zero =>
        simpa using weight_step hε0 hε1 a
    | succ k ih =>
        have hstep : weight n ε (a + (k + 1) + 1) < weight n ε (a + k + 1) := by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using weight_step hε0 hε1 (a + k + 1)
        exact lt_trans hstep ih
  exact hiter (b - a - 1)

/-- Distance-comparison form used by `thm:com` (Lemma 18): closer words contribute more. -/
lemma weight_lt_of_dist_lt {n : ℕ} {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1 / 2)
    {a b : ℕ} (h : a < b) :
    (1 - ε) ^ (n - b) * ε ^ b < (1 - ε) ^ (n - a) * ε ^ a :=
  weight_strictAnti hε0 hε1 h

/-! ## Minimum over four rows is permutation-invariant -/

/-- The nested four-fold minimum equals the minimum over the image set. -/
lemma min4_eq_image (a : Fin 4 → ℕ) :
    min (a 0) (min (a 1) (min (a 2) (a 3))) = (Finset.univ.image a).min' (by simp) := by
  apply le_antisymm
  · apply Finset.le_min' (Finset.univ.image a) (by simp) (min (a 0) (min (a 1) (min (a 2) (a 3))))
    intro y hy
    rcases (Finset.mem_image.mp hy) with ⟨j, _hj, hjy⟩
    rw [← hjy]
    fin_cases j
    · exact Nat.min_le_left _ _
    · exact (Nat.min_le_right _ _).trans (Nat.min_le_left _ _)
    · exact (Nat.min_le_right _ _).trans ((Nat.min_le_right _ _).trans (Nat.min_le_left _ _))
    · exact (Nat.min_le_right _ _).trans ((Nat.min_le_right _ _).trans (Nat.min_le_right _ _))
  · exact le_min (Finset.min'_le (Finset.univ.image a) (a 0) (by simp))
      (le_min (Finset.min'_le (Finset.univ.image a) (a 1) (by simp))
        (le_min (Finset.min'_le (Finset.univ.image a) (a 2) (by simp))
          (Finset.min'_le (Finset.univ.image a) (a 3) (by simp))))

/-- Permuting the four rows does not change the minimum distance. -/
lemma min4_perm (a : Fin 4 → ℕ) (ρ : Equiv (Fin 4) (Fin 4)) :
    min (a (ρ 0)) (min (a (ρ 1)) (min (a (ρ 2)) (a (ρ 3)))) =
      min (a 0) (min (a 1) (min (a 2) (a 3))) := by
  calc
    min (a (ρ 0)) (min (a (ρ 1)) (min (a (ρ 2)) (a (ρ 3))))
        = (Finset.univ.image (fun j : Fin 4 => a (ρ j))).min' (by simp) :=
          min4_eq_image (fun j : Fin 4 => a (ρ j))
    _ = (Finset.univ.image a).min' (by simp) := by
          congr 1
          ext x
          constructor
          · intro hx
            rcases (Finset.mem_image.mp hx) with ⟨j, _hj, hjy⟩
            apply Finset.mem_image.mpr
            refine ⟨ρ j, ?_, hjy⟩
            simp
          · intro hy
            rcases (Finset.mem_image.mp hy) with ⟨k, _hk, hky⟩
            apply Finset.mem_image.mpr
            refine ⟨ρ.symm k, ?_, ?_⟩
            · simp
            · simpa using hky
    _ = min (a 0) (min (a 1) (min (a 2) (a 3))) := (min4_eq_image a).symm

/-! ## Equivalence invariance -/

/-- The word transform induced by a column permutation p and column flips f. -/
def wordTransform {n : ℕ} (p : Equiv (Fin n) (Fin n)) (f : Fin n → Bool) (y : Word n) : Word n :=
  fun t => if f t then !(y (p t)) else y (p t)

/-- The inverse word transform. -/
def wordTransformInv {n : ℕ} (p : Equiv (Fin n) (Fin n)) (f : Fin n → Bool) (y : Word n) : Word n :=
  fun t => if f (p.symm t) then !(y (p.symm t)) else y (p.symm t)

lemma wordTransform_inv_left {n : ℕ} (p : Equiv (Fin n) (Fin n)) (f : Fin n → Bool) (y : Word n) :
    wordTransform p f (wordTransformInv p f y) = y := by
  funext t
  cases hf : f t <;> simp [wordTransform, wordTransformInv, hf]

lemma wordTransform_inv_right {n : ℕ} (p : Equiv (Fin n) (Fin n)) (f : Fin n → Bool) (y : Word n) :
    wordTransformInv p f (wordTransform p f y) = y := by
  funext t
  cases hf : f (p.symm t) <;> simp [wordTransform, wordTransformInv, hf]

/-- The word transform is bijective. -/
lemma wordTransform_bijective {n : ℕ} (p : Equiv (Fin n) (Fin n)) (f : Fin n → Bool) :
    Function.Bijective (wordTransform p f) :=
  ⟨fun a b hab => by
    have h := congrArg (wordTransformInv p f) hab
    simpa [wordTransform_inv_right, wordTransform_inv_left] using h,
   fun y => ⟨wordTransformInv p f y, wordTransform_inv_left p f y⟩⟩

/-- d_j(y) as a sum of mismatch indicators. -/
lemma dRow_eq_indicator_sum {n : ℕ} (C : Code n) (j : Fin 4) (y : Word n) :
    dRow C j y = ∑ t : Fin n, if colBit j (C t) ≠ y t then 1 else 0 := by
  rw [dRow_eq_hammingDist]
  unfold hammingDist hammingWeight
  apply Finset.sum_congr rfl
  intro t _
  cases hb : C t j <;> cases hy : y t <;>
    simp [hy, bitXor, row, colBit]

/-- Row distances transform along the equivalence. -/
lemma dRow_equiv {n : ℕ} (C C' : Code n) {ρ : Equiv (Fin 4) (Fin 4)}
    {p : Equiv (Fin n) (Fin n)} {f : Fin n → Bool}
    (h : ∀ t : Fin n, C' (p t) = rowPermute ρ (if f t then flipCol (C t) else C t))
    (j : Fin 4) (y : Word n) :
    dRow C' j y = dRow C (ρ j) (wordTransform p f y) := by
  rw [dRow_eq_indicator_sum, dRow_eq_indicator_sum]
  calc
    (∑ t : Fin n, if colBit j (C' t) ≠ y t then 1 else 0)
        = ∑ t : Fin n, if colBit j (C' (p t)) ≠ y (p t) then 1 else 0 := by
          symm
          apply Finset.sum_bij (fun t _ => p t)
          · intro t _; simp
          · intro a _ b _ hab
            exact p.injective hab
          · intro b _
            exact ⟨p.symm b, by simp, by simp⟩
          · intro t _; rfl
    _ = ∑ t : Fin n, if colBit (ρ j) (C t) ≠ wordTransform p f y t then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro t _
          have hcol : colBit j (C' (p t)) =
              if f t then !(colBit (ρ j) (C t)) else colBit (ρ j) (C t) := by
            rw [h t]
            by_cases hf : f t = true <;> simp [rowPermute, flipCol, colBit, hf]
          by_cases hf : f t <;> simp [wordTransform, hf, hcol]

/-- The code distance transforms along the equivalence. -/
lemma dCode_equiv {n : ℕ} (C C' : Code n) {ρ : Equiv (Fin 4) (Fin 4)}
    {p : Equiv (Fin n) (Fin n)} {f : Fin n → Bool}
    (h : ∀ t : Fin n, C' (p t) = rowPermute ρ (if f t then flipCol (C t) else C t))
    (y : Word n) :
    dCode C' y = dCode C (wordTransform p f y) := by
  unfold dCode
  calc
    min (dRow C' 0 y) (min (dRow C' 1 y) (min (dRow C' 2 y) (dRow C' 3 y)))
        = min (dRow C (ρ 0) (wordTransform p f y))
            (min (dRow C (ρ 1) (wordTransform p f y))
              (min (dRow C (ρ 2) (wordTransform p f y)) (dRow C (ρ 3) (wordTransform p f y)))) := by
          simp [dRow_equiv C C' h]
    _ = min (dRow C 0 (wordTransform p f y))
          (min (dRow C 1 (wordTransform p f y))
            (min (dRow C 2 (wordTransform p f y)) (dRow C 3 (wordTransform p f y)))) :=
          min4_perm (fun k => dRow C k (wordTransform p f y)) ρ

/-- α is invariant under equivalence. -/
lemma alpha_equiv {n : ℕ} (C C' : Code n) (h : Equivalent C C') (d : ℕ) :
    alpha C' d = alpha C d := by
  rcases h with ⟨ρ, p, f, h⟩
  have hd : ∀ y : Word n, dCode C' y = dCode C (wordTransform p f y) := dCode_equiv C C' h
  unfold alpha
  calc
    (∑ y : Word n, if dCode C' y = d then 1 else 0)
        = ∑ y : Word n, if dCode C (wordTransform p f y) = d then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro y _
          rw [hd y]
    _ = ∑ y : Word n, if dCode C y = d then 1 else 0 := by
          apply Finset.sum_bij (fun y _ => wordTransform p f y)
          · intro y _; simp
          · intro a _ b _ hab
            exact (wordTransform_bijective p f).1 hab
          · intro b _
            exact ⟨wordTransformInv p f b, by simp, wordTransform_inv_left p f b⟩
          · intro y _; rfl

/-- λ is invariant under equivalence. -/
lemma lambda_equiv {n : ℕ} (C C' : Code n) (h : Equivalent C C') (ε : ℝ) :
    lambda C' ε = lambda C ε := by
  rcases h with ⟨ρ, p, f, h⟩
  have hd : ∀ y : Word n, dCode C' y = dCode C (wordTransform p f y) := dCode_equiv C C' h
  unfold lambda
  congr 1
  calc
    (∑ y : Word n, (1 - ε) ^ (n - dCode C' y) * ε ^ (dCode C' y))
        = ∑ y : Word n, (1 - ε) ^ (n - dCode C (wordTransform p f y)) * ε ^ (dCode C (wordTransform p f y)) := by
          apply Finset.sum_congr rfl
          intro y _
          rw [hd y]
    _ = ∑ y : Word n, (1 - ε) ^ (n - dCode C y) * ε ^ (dCode C y) := by
          apply Finset.sum_bij (fun y _ => wordTransform p f y)
          · intro y _; simp
          · intro a _ b _ hab
            exact (wordTransform_bijective p f).1 hab
          · intro b _
            exact ⟨wordTransformInv p f b, by simp, wordTransform_inv_left p f b⟩
          · intro y _; rfl

/-- Equivalent codes have identical performance. -/
lemma universalEqual_of_equivalent {n : ℕ} (C C' : Code n) (h : Equivalent C C') :
    UniversalEqual C' C := by
  intro ε h0 h1
  exact lambda_equiv C C' h ε

/-- Equivalent codes inherit strict universal domination. -/
lemma universalStrictBetter_of_equivalent {n : ℕ} (C₁ C₁' C₂ C₂' : Code n)
    (h1 : Equivalent C₁ C₁') (h2 : Equivalent C₂ C₂') (h : UniversalStrictBetter C₁' C₂') :
    UniversalStrictBetter C₁ C₂ := by
  intro ε hε0 hε1
  have hlt := h ε hε0 hε1
  have heq1 := lambda_equiv C₁ C₁' h1 ε
  have heq2 := lambda_equiv C₂ C₂' h2 ε
  linarith

/-! ## Column-weight parity invariants and no-cross-class -/

/-- The Hamming weight of a column (number of 1-bits). -/
def colWeight (c : Column) : ℕ := (Finset.univ.filter fun r : Fin 4 => c r = true).card

/-- Row permutations preserve column weight. -/
lemma colWeight_rowPermute (ρ : Equiv (Fin 4) (Fin 4)) (c : Column) :
    colWeight (rowPermute ρ c) = colWeight c := by
  unfold colWeight rowPermute
  apply Finset.card_bij (fun r _ => ρ r)
  · intro r hr
    simpa using hr
  · intro a _ b _ hab
    exact ρ.injective hab
  · intro b hb
    refine ⟨ρ.symm b, ?_, ?_⟩
    · simpa using hb
    · simp

-- native_decide: Mechanical · n=any · checked 2026-08-24
/-- Column flips change weight w to 4 − w. -/
lemma colWeight_flip : ∀ c : Column, colWeight (flipCol c) = 4 - colWeight c := by
  native_decide

-- native_decide: Mechanical · n=any · checked 2026-08-24
/-- Column weights are at most 4. -/
lemma colWeight_le_4 : ∀ c : Column, colWeight c ≤ 4 := by
  native_decide

/-- `UniversalBetter` is reflexive. -/
lemma universalBetter_refl {n : ℕ} (C : Code n) : UniversalBetter C C := by
  intro ε h0 h1
  exact le_rfl

/-- `UniversalBetter` is transitive. -/
lemma universalBetter_trans {n : ℕ} {A B C : Code n} (hAB : UniversalBetter A B)
    (hBC : UniversalBetter B C) : UniversalBetter A C := by
  intro ε h0 h1
  exact le_trans (hBC ε h0 h1) (hAB ε h0 h1)

/-- All columns of a code have even weight. -/
def allEvenWeights {n : ℕ} (C : Code n) : Prop := ∀ t : Fin n, Even (colWeight (C t))

/-- A weight differing by the flip relation preserves parity. -/
lemma even_weight_iff {a b : ℕ} (h : b = a ∨ b = 4 - a) (ha4 : a ≤ 4) (hb4 : b ≤ 4) :
    Even b ↔ Even a := by
  constructor
  · intro hb
    rcases h with h | h
    · simpa [h] using hb
    · rcases hb with ⟨k, hk⟩
      refine ⟨2 - k, ?_⟩
      omega
  · intro ha
    rcases h with h | h
    · simpa [h] using ha
    · rcases ha with ⟨k, hk⟩
      refine ⟨2 - k, ?_⟩
      omega

/-- The even-weight property is invariant under equivalence. -/
lemma allEvenWeights_equiv {n : ℕ} (C C' : Code n) (h : Equivalent C C') :
    allEvenWeights C ↔ allEvenWeights C' := by
  rcases h with ⟨ρ, p, f, h⟩
  have hrel : ∀ t : Fin n, colWeight (C' (p t)) = colWeight (C t) ∨
      colWeight (C' (p t)) = 4 - colWeight (C t) := by
    intro t
    rw [h t]
    cases hf : f t <;> simp [colWeight_rowPermute, colWeight_flip]
  constructor
  · intro hc t
    have ht' : C' t = C' (p (p.symm t)) := by simp
    rw [ht']
    exact (even_weight_iff (hrel (p.symm t)) (colWeight_le_4 _) (colWeight_le_4 _)).mpr
      (hc (p.symm t))
  · intro hc t
    exact (even_weight_iff (hrel t) (colWeight_le_4 _) (colWeight_le_4 _)).mp (hc (p t))

-- native_decide: Mechanical · n=any · checked 2026-08-24
/-- Linear codes have only even-weight columns. -/
lemma IsLinear_all_even {n : ℕ} (C : Code n) (h : IsLinear C) : allEvenWeights C := by
  intro t
  rcases h.1 t with h0 | h3 | h5 | h6
  · have : colWeight (C t) = 0 := by
      rw [← colOfNat_colVal (C t), h0]
      native_decide
    rw [this]
    exact ⟨0, by omega⟩
  · have : colWeight (C t) = 2 := by
      rw [← colOfNat_colVal (C t), h3]
      native_decide
    rw [this]
    exact ⟨1, by omega⟩
  · have : colWeight (C t) = 2 := by
      rw [← colOfNat_colVal (C t), h5]
      native_decide
    rw [this]
    exact ⟨1, by omega⟩
  · have : colWeight (C t) = 2 := by
      rw [← colOfNat_colVal (C t), h6]
      native_decide
    rw [this]
    exact ⟨1, by omega⟩

/-- A positive count of type-i columns means some column has that type. -/
lemma count_pos_iff_exists {n : ℕ} (C : Code n) (i : ℕ) :
    count C i > 0 ↔ ∃ t : Fin n, colVal (C t) = i := by
  constructor
  · intro h
    by_contra hn
    have hz : count C i = 0 := by
      unfold count
      apply Finset.sum_eq_zero
      intro t _
      have : colVal (C t) ≠ i := by
        intro hti
        exact hn ⟨t, hti⟩
      simp [this]
    omega
  · rintro ⟨t, ht⟩
    by_contra hn
    have hz : count C i = 0 := by omega
    have hz' : ∀ t' : Fin n, colVal (C t') ≠ i := by
      simpa [count] using hz
    exact hz' t ht

-- native_decide: Mechanical · n=any · checked 2026-08-24
/-- A code with a positive |1| has a weight-1 column. -/
lemma exists_weight1_of_count1_pos {n : ℕ} (C : Code n) (hpos : count C 1 > 0) :
    ∃ t : Fin n, colWeight (C t) = 1 := by
  rcases (count_pos_iff_exists C 1).1 hpos with ⟨t, ht⟩
  refine ⟨t, ?_⟩
  rw [← colOfNat_colVal (C t), ht]
  native_decide

/-- A weight-1 column is odd, so the code is not all-even. -/
lemma not_all_even_of_weight1 {n : ℕ} (C : Code n) (h : ∃ t : Fin n, colWeight (C t) = 1) :
    ¬ allEvenWeights C := by
  rintro hE
  rcases h with ⟨t, ht⟩
  have : Even (colWeight (C t)) := hE t
  rw [ht] at this
  rcases this with ⟨k, hk⟩
  omega

/-- No linear code is equivalent to a code with a type-1 column
(Class-I, Class-II, or Class-III all have |1| > 0). -/
lemma linear_not_equiv_weight1 {n : ℕ} (C C' : Code n) (hC : IsLinear C) (hpos : count C' 1 > 0) :
    ¬ Equivalent C C' := by
  intro heq
  exact (not_all_even_of_weight1 C' (exists_weight1_of_count1_pos C' hpos))
    ((allEvenWeights_equiv C C' heq).mp (IsLinear_all_even C hC))

lemma classI_count1_pos {n : ℕ} (C : Code n) (h : ClassI C) : count C 1 > 0 := by
  rcases h.1 with ⟨k, hk⟩
  omega

lemma classII_count1_pos {n : ℕ} (C : Code n) (h : ClassII C) : count C 1 > 0 := h.1

lemma classIII_count1_pos {n : ℕ} (C : Code n) (h : ClassIII C) : count C 1 > 0 := by
  rcases h.2 with h | h
  · omega
  · omega

/-- No linear code is equivalent to a Class-I code. -/
lemma no_cross_class_linear_class1 {n : ℕ} (C C' : Code n) (hC : IsLinear C) (hC' : ClassI C') :
    ¬ Equivalent C C' :=
  linear_not_equiv_weight1 C C' hC (classI_count1_pos C' hC')

/-- No linear code is equivalent to a Class-II code. -/
lemma no_cross_class_linear_class2 {n : ℕ} (C C' : Code n) (hC : IsLinear C) (hC' : ClassII C') :
    ¬ Equivalent C C' :=
  linear_not_equiv_weight1 C C' hC (classII_count1_pos C' hC')

/-- No linear code is equivalent to a Class-III code. -/
lemma no_cross_class_linear_class3 {n : ℕ} (C C' : Code n) (hC : IsLinear C) (hC' : ClassIII C') :
    ¬ Equivalent C C' :=
  linear_not_equiv_weight1 C C' hC (classIII_count1_pos C' hC')

end N4Code
