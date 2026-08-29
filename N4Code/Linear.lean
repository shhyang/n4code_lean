import N4Code.Compare
import N4Code.ZeroColumn
import Mathlib.Tactic.IntervalCases

/-!
# Phase F: linear codes (paper §3.4, `thm:linearcompare` (Theorem 12), `thm:linearopt` (Theorem 2))

Comparison of linear codes `C(n3,n5,n6)` with a single column changed:
the Y3/Y5 characterizations and closed forms for α³(d), α⁵(d)
(eq. cli4–cli9), `thm:linearcompare` (Theorem 12) (3 cases), `cor:linear1` (Corollary 13), and
`thm:linearopt` (Theorem 2) (mod-3 classification n = 3k−1, 3k, 3k+1, plus n = 3, with
the strict universal domination claim proved by improvement chains).

See `AGENTS.md` for build/consistency rules and `PLAN.md` Phase F for the
work plan.  The paper statements are the placeholder stubs in
`N4Code/Statements.lean` (§3.4); prove them here and replace each stub with
a comment pointing back (as done for `thm:0column` (Theorem 6) in `ZeroColumn.lean`).
-/

namespace N4Code

/-! ## Linear-code facts

The representative `C(n3,n5,n6) = linearCode n3 n5 n6` has columns of types
3, 5, 6 only.  We record its counts, per-type weights, and the four row
distances (paper eq. d in §5), which drive every α-formula in this module.
-/

-- native_decide: Mechanical · n=any · checked 2026-08-24
/-- `colVal col3 = 3`. -/
lemma colVal_col3 : colVal col3 = 3 := by native_decide

-- native_decide: Mechanical · n=any · checked 2026-08-24
/-- `colVal col5 = 5`. -/
lemma colVal_col5 : colVal col5 = 5 := by native_decide

-- native_decide: Mechanical · n=any · checked 2026-08-24
/-- `colVal col6 = 6`. -/
lemma colVal_col6 : colVal col6 = 6 := by native_decide

/-- Every column of `linearCode n3 n5 n6` has type 3, 5, or 6. -/
lemma linear_col_type {n3 n5 n6 : ℕ} (t : Fin (n3 + n5 + n6)) :
    colVal (linearCode n3 n5 n6 t) = 3 ∨ colVal (linearCode n3 n5 n6 t) = 5 ∨
      colVal (linearCode n3 n5 n6 t) = 6 := by
  by_cases h1 : t.val < n3
  · left
    simp [linearCode, h1, colVal_col3]
  · by_cases h2 : t.val < n3 + n5
    · right; left
      simp [linearCode, h1, h2, colVal_col5]
    · right; right
      simp [linearCode, h1, h2, colVal_col6]

/-- The type-3 columns of `linearCode n3 n5 n6` are exactly the first `n3`. -/
lemma linear_fiber_3 {n3 n5 n6 : ℕ} :
    fiber (linearCode n3 n5 n6) 3 =
      (Finset.univ : Finset (Fin (n3 + n5 + n6))).filter (fun t => t.val < n3) := by
  ext t
  have hiff : colVal (linearCode n3 n5 n6 t) = 3 ↔ t.val < n3 := by
    by_cases h1 : t.val < n3
    · constructor <;> intro h
      · exact h1
      · simp [linearCode, h1, colVal_col3]
    · by_cases h5 : t.val < n3 + n5
      · constructor <;> intro h
        · have hc : colVal (linearCode n3 n5 n6 t) = 5 := by
            simp [linearCode, h1, h5, colVal_col5]
          rw [hc] at h
          norm_num at h
        · exact False.elim (h1 h)
      · constructor <;> intro h
        · have hc : colVal (linearCode n3 n5 n6 t) = 6 := by
            simp [linearCode, h1, h5, colVal_col6]
          rw [hc] at h
          norm_num at h
        · exact False.elim (h1 h)
  simpa [fiber]

/-- The type-5 columns of `linearCode n3 n5 n6` are exactly positions
`n3 ≤ t < n3 + n5`. -/
lemma linear_fiber_5 {n3 n5 n6 : ℕ} :
    fiber (linearCode n3 n5 n6) 5 =
      (Finset.univ : Finset (Fin (n3 + n5 + n6))).filter
        (fun t => n3 ≤ t.val ∧ t.val < n3 + n5) := by
  ext t
  have hiff : colVal (linearCode n3 n5 n6 t) = 5 ↔ n3 ≤ t.val ∧ t.val < n3 + n5 := by
    by_cases h1 : t.val < n3
    · constructor <;> intro h
      · have hc : colVal (linearCode n3 n5 n6 t) = 3 := by
          simp [linearCode, h1, colVal_col3]
        rw [hc] at h
        norm_num at h
      · omega
    · by_cases h5 : t.val < n3 + n5
      · constructor <;> intro h
        · exact ⟨le_of_not_gt h1, h5⟩
        · simp [linearCode, h1, h5, colVal_col5]
      · constructor <;> intro h
        · have hc : colVal (linearCode n3 n5 n6 t) = 6 := by
            simp [linearCode, h1, h5, colVal_col6]
          rw [hc] at h
          norm_num at h
        · omega
  simpa [fiber]

/-- The type-6 columns of `linearCode n3 n5 n6` are exactly the last `n6`. -/
lemma linear_fiber_6 {n3 n5 n6 : ℕ} :
    fiber (linearCode n3 n5 n6) 6 =
      (Finset.univ : Finset (Fin (n3 + n5 + n6))).filter
        (fun t => n3 + n5 ≤ t.val) := by
  ext t
  have hiff : colVal (linearCode n3 n5 n6 t) = 6 ↔ n3 + n5 ≤ t.val := by
    by_cases h1 : t.val < n3
    · constructor <;> intro h
      · have hc : colVal (linearCode n3 n5 n6 t) = 3 := by
          simp [linearCode, h1, colVal_col3]
        rw [hc] at h
        norm_num at h
      · omega
    · by_cases h5 : t.val < n3 + n5
      · constructor <;> intro h
        · have hc : colVal (linearCode n3 n5 n6 t) = 5 := by
            simp [linearCode, h1, h5, colVal_col5]
          rw [hc] at h
          norm_num at h
        · omega
      · constructor <;> intro h
        · by_contra hn
          have hn' : t.val < n3 + n5 := by omega
          have hc : colVal (linearCode n3 n5 n6 t) = 5 := by
            simp [linearCode, h1, hn', colVal_col5]
          rw [hc] at h
          norm_num at h
        · simp [linearCode, h1, h5, colVal_col6]
  simpa [fiber]

/-- The card of `{t : Fin n | t.val < m}` is `m` when `m ≤ n`. -/
lemma card_fin_lt {m n : ℕ} (h : m ≤ n) :
    (Finset.univ.filter (fun t : Fin n => t.val < m)).card = m := by
  let f : Fin m → Fin n := fun i => ⟨i.val, by omega⟩
  have hbij : (Finset.univ.filter (fun t : Fin n => t.val < m)) =
      (Finset.univ : Finset (Fin m)).map ⟨f, by
        intro a b hab
        apply Fin.ext
        have hv := congrArg Fin.val hab
        simpa [f] using hv⟩ := by
    ext t
    constructor
    · intro ht
      have ht' : t.val < m := by simpa using ht
      have hmem : ⟨t.val, ht'⟩ ∈ (Finset.univ : Finset (Fin m)) := by simp
      refine Finset.mem_map.mpr ⟨⟨t.val, ht'⟩, hmem, ?_⟩
      apply Fin.ext
      change (f ⟨t.val, ht'⟩).val = t.val
      simp [f]
    · intro hm
      rw [Finset.mem_map] at hm
      rcases hm with ⟨i, hi, hti⟩
      have hv : i.val = t.val := by
        change (f i).val = t.val
        exact congrArg Fin.val hti
      have hlt : t.val < m := by
        rw [← hv]
        exact i.isLt
      simp [hlt]
  rw [hbij, Finset.card_map]
  simp

/-- `|3|` of `C(n3,n5,n6)` is `n3`. -/
lemma linear_count_3 {n3 n5 n6 : ℕ} : count (linearCode n3 n5 n6) 3 = n3 := by
  rw [count_eq_card]
  change (fiber (linearCode n3 n5 n6) 3).card = n3
  rw [linear_fiber_3]
  exact card_fin_lt (m := n3) (n := n3 + n5 + n6) (by omega)

/-- `|5|` of `C(n3,n5,n6)` is `n5`. -/
lemma linear_count_5 {n3 n5 n6 : ℕ} : count (linearCode n3 n5 n6) 5 = n5 := by
  rw [count_eq_card]
  change (fiber (linearCode n3 n5 n6) 5).card = n5
  rw [linear_fiber_5]
  let f : Fin n5 → Fin (n3 + n5 + n6) := fun i => ⟨n3 + i.val, by omega⟩
  have hbij : (Finset.univ.filter (fun t : Fin (n3 + n5 + n6) =>
      n3 ≤ t.val ∧ t.val < n3 + n5)) =
      (Finset.univ : Finset (Fin n5)).map ⟨f, by
        intro a b hab
        apply Fin.ext
        have hv := congrArg Fin.val hab
        simpa [f] using hv⟩ := by
    ext t
    constructor
    · intro ht
      have ht' : n3 ≤ t.val ∧ t.val < n3 + n5 := by simpa using ht
      have hmem : ⟨t.val - n3, by omega⟩ ∈ (Finset.univ : Finset (Fin n5)) := by simp
      refine Finset.mem_map.mpr ⟨⟨t.val - n3, by omega⟩, hmem, ?_⟩
      apply Fin.ext
      change (f ⟨t.val - n3, by omega⟩).val = t.val
      simp [f]
      omega
    · intro hm
      rw [Finset.mem_map] at hm
      rcases hm with ⟨i, hi, hti⟩
      have hv : n3 + i.val = t.val := by
        change (f i).val = t.val
        exact congrArg Fin.val hti
      have hge : n3 ≤ t.val := by omega
      have hlt : t.val < n3 + n5 := by omega
      simp [hge, hlt]
  rw [hbij, Finset.card_map]
  simp

/-- `|6|` of `C(n3,n5,n6)` is `n6`. -/
lemma linear_count_6 {n3 n5 n6 : ℕ} : count (linearCode n3 n5 n6) 6 = n6 := by
  rw [count_eq_card]
  change (fiber (linearCode n3 n5 n6) 6).card = n6
  rw [linear_fiber_6]
  let f : Fin n6 → Fin (n3 + n5 + n6) := fun i => ⟨n3 + n5 + i.val, by omega⟩
  have hbij : (Finset.univ.filter (fun t : Fin (n3 + n5 + n6) =>
      n3 + n5 ≤ t.val)) =
      (Finset.univ : Finset (Fin n6)).map ⟨f, by
        intro a b hab
        apply Fin.ext
        have hv := congrArg Fin.val hab
        simpa [f] using hv⟩ := by
    ext t
    constructor
    · intro ht
      have ht' : n3 + n5 ≤ t.val := by simpa using ht
      have hmem : ⟨t.val - (n3 + n5), by omega⟩ ∈ (Finset.univ : Finset (Fin n6)) := by simp
      refine Finset.mem_map.mpr ⟨⟨t.val - (n3 + n5), by omega⟩, hmem, ?_⟩
      apply Fin.ext
      change (f ⟨t.val - (n3 + n5), by omega⟩).val = t.val
      simp [f]
      omega
    · intro hm
      rw [Finset.mem_map] at hm
      rcases hm with ⟨i, hi, hti⟩
      have hv : n3 + n5 + i.val = t.val := by
        change (f i).val = t.val
        exact congrArg Fin.val hti
      have hlt : n3 + n5 ≤ t.val := by omega
      simp [hlt]
  rw [hbij, Finset.card_map]
  simp

/-- Types other than 3, 5, 6 have weight zero in a linear code. -/
lemma linear_w_i_eq_zero {n3 n5 n6 : ℕ} {i : ℕ} (y : Word (n3 + n5 + n6))
    (hi3 : i ≠ 3) (hi5 : i ≠ 5) (hi6 : i ≠ 6) :
    w_i (linearCode n3 n5 n6) i y = 0 := by
  unfold w_i weightOn
  rw [Finset.card_eq_zero]
  rw [Finset.filter_eq_empty_iff]
  intro t ht
  simp at ht
  rcases linear_col_type (n3 := n3) (n5 := n5) (n6 := n6) t with h3 | h5 | h6
  · exact False.elim (hi3 (ht.symm.trans h3))
  · exact False.elim (hi5 (ht.symm.trans h5))
  · exact False.elim (hi6 (ht.symm.trans h6))

/-- The first row of a linear code is the zero row. -/
lemma linear_row0_zero {n3 n5 n6 : ℕ} :
    row (linearCode n3 n5 n6) ⟨0, by decide⟩ = fun _ : Fin (n3 + n5 + n6) => false := by
  funext t
  by_cases h1 : t.val < n3
  · simp [row, colBit, linearCode, h1, col3]
  · by_cases h2 : t.val < n3 + n5
    · simp [row, colBit, linearCode, h1, h2, col5]
    · simp [row, colBit, linearCode, h1, h2, col6]

/-- The four row distances of a linear code, in terms of `w3,w5,w6`
(paper eq. d, §5). -/
lemma linear_dRow_eq {n3 n5 n6 : ℕ} (j : Fin 4) (y : Word (n3 + n5 + n6)) :
    dRow (linearCode n3 n5 n6) j y =
      (if (3).testBit (3 - j.val) then n3 - w_i (linearCode n3 n5 n6) 3 y
        else w_i (linearCode n3 n5 n6) 3 y) +
      (if (5).testBit (3 - j.val) then n5 - w_i (linearCode n3 n5 n6) 5 y
        else w_i (linearCode n3 n5 n6) 5 y) +
      (if (6).testBit (3 - j.val) then n6 - w_i (linearCode n3 n5 n6) 6 y
        else w_i (linearCode n3 n5 n6) 6 y) := by
  rw [dRow_eq_sum]
  let C := linearCode n3 n5 n6
  let F : ℕ → ℕ := fun i => if i.testBit (3 - j.val) then count C i - w_i C i y
    else w_i C i y
  have hzero : ∀ i ∈ Finset.Icc 0 15, i ≠ 3 → i ≠ 5 → i ≠ 6 → F i = 0 := by
    intro i hi hi3 hi5 hi6
    unfold F
    have hw : w_i C i y = 0 :=
      linear_w_i_eq_zero (n3 := n3) (n5 := n5) (n6 := n6) (y := y) hi3 hi5 hi6
    have hc : count C i = 0 := by
      rw [count_eq_card]
      rw [Finset.card_eq_zero]
      rw [Finset.filter_eq_empty_iff]
      intro t _
      rcases linear_col_type (n3 := n3) (n5 := n5) (n6 := n6) t with h3 | h5 | h6
      · intro hc
        exact hi3 (hc.symm.trans h3)
      · intro hc
        exact hi5 (hc.symm.trans h5)
      · intro hc
        exact hi6 (hc.symm.trans h6)
    simp [hw, hc]
  have hmain : (∑ i ∈ Finset.Icc 0 15, F i) = F 3 + (F 5 + F 6) := by
    rw [← Finset.sum_erase_add (s := Finset.Icc 0 15) (a := 3) (f := F) (by simp)]
    rw [← Finset.sum_erase_add (s := (Finset.Icc 0 15).erase 3) (a := 5) (f := F)
      (by simp)]
    rw [← Finset.sum_erase_add (s := ((Finset.Icc 0 15).erase 3).erase 5) (a := 6)
      (f := F) (by simp)]
    have hrest : (∑ i ∈ (((Finset.Icc 0 15).erase 3).erase 5).erase 6, F i) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hi6' : i ≠ 6 := (Finset.mem_erase.mp hi).1
      have hi5' : i ≠ 5 := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
      have hi3' : i ≠ 3 :=
        (Finset.mem_erase.mp (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).2).1
      have hiIcc : i ∈ Finset.Icc 0 15 :=
        (Finset.mem_erase.mp (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).2).2
      exact hzero i hiIcc hi3' hi5' hi6'
    rw [hrest]
    simp
    ac_rfl
  change (∑ i ∈ Finset.Icc 0 15, F i) =
      ((if (3).testBit (3 - j.val) then n3 - w_i C 3 y else w_i C 3 y) +
        (if (5).testBit (3 - j.val) then n5 - w_i C 5 y else w_i C 5 y)) +
          (if (6).testBit (3 - j.val) then n6 - w_i C 6 y else w_i C 6 y)
  rw [hmain]
  simp [F, C]
  rw [linear_count_3, linear_count_5, linear_count_6]
  ac_rfl

-- native_decide: Mechanical · n=any · checked 2026-08-24
/-- `d_{row 1}` of a linear code: `w3 + w5 + w6`. -/
lemma linear_dRow0 {n3 n5 n6 : ℕ} (y : Word (n3 + n5 + n6)) :
    dRow (linearCode n3 n5 n6) ⟨0, by decide⟩ y =
      w_i (linearCode n3 n5 n6) 3 y + w_i (linearCode n3 n5 n6) 5 y +
        w_i (linearCode n3 n5 n6) 6 y := by
  rw [linear_dRow_eq]
  have ht3 : (3).testBit 3 = false := by native_decide
  have ht5 : (5).testBit 3 = false := by native_decide
  have ht6 : (6).testBit 3 = false := by native_decide
  simp [ht3, ht5, ht6, add_assoc]

-- native_decide: Mechanical · n=any · checked 2026-08-24
/-- `d_{row 2}` of a linear code: `w3 + (n5 − w5) + (n6 − w6)`. -/
lemma linear_dRow1 {n3 n5 n6 : ℕ} (y : Word (n3 + n5 + n6)) :
    dRow (linearCode n3 n5 n6) ⟨1, by decide⟩ y =
      w_i (linearCode n3 n5 n6) 3 y +
        (n5 - w_i (linearCode n3 n5 n6) 5 y) +
          (n6 - w_i (linearCode n3 n5 n6) 6 y) := by
  rw [linear_dRow_eq]
  have ht3 : (3).testBit 2 = false := by native_decide
  have ht5 : (5).testBit 2 = true := by native_decide
  have ht6 : (6).testBit 2 = true := by native_decide
  simp [ht3, ht5, ht6, add_assoc]

-- native_decide: Mechanical · n=any · checked 2026-08-24
/-- `d_{row 3}` of a linear code: `(n3 − w3) + w5 + (n6 − w6)`. -/
lemma linear_dRow2 {n3 n5 n6 : ℕ} (y : Word (n3 + n5 + n6)) :
    dRow (linearCode n3 n5 n6) ⟨2, by decide⟩ y =
      (n3 - w_i (linearCode n3 n5 n6) 3 y) +
        w_i (linearCode n3 n5 n6) 5 y +
          (n6 - w_i (linearCode n3 n5 n6) 6 y) := by
  rw [linear_dRow_eq]
  have ht3 : (3).testBit 1 = true := by native_decide
  have ht5 : (5).testBit 1 = false := by native_decide
  have ht6 : (6).testBit 1 = true := by native_decide
  simp [ht3, ht5, ht6, add_assoc]

-- native_decide: Mechanical · n=any · checked 2026-08-24
/-- `d_{row 4}` of a linear code: `(n3 − w3) + (n5 − w5) + w6`. -/
lemma linear_dRow3 {n3 n5 n6 : ℕ} (y : Word (n3 + n5 + n6)) :
    dRow (linearCode n3 n5 n6) ⟨3, by decide⟩ y =
      (n3 - w_i (linearCode n3 n5 n6) 3 y) +
        (n5 - w_i (linearCode n3 n5 n6) 5 y) +
          w_i (linearCode n3 n5 n6) 6 y := by
  rw [linear_dRow_eq]
  have ht3 : (3).testBit 0 = true := by native_decide
  have ht5 : (5).testBit 0 = true := by native_decide
  have ht6 : (6).testBit 0 = false := by native_decide
  simp [ht3, ht5, ht6, add_assoc]

/-- `w3 + w5 + w6 = hammingWeight y` for a linear code. -/
lemma linear_wsum_eq_hammingWeight {n3 n5 n6 : ℕ} (y : Word (n3 + n5 + n6)) :
    w_i (linearCode n3 n5 n6) 3 y + w_i (linearCode n3 n5 n6) 5 y +
        w_i (linearCode n3 n5 n6) 6 y = hammingWeight y := by
  rw [← linear_dRow0 y, dRow_eq_hammingDist, linear_row0_zero]
  unfold hammingDist
  rw [bitXor_false]

/-- Flipping the changed (type-3) column with `y t = true` decreases `w3` by one. -/
lemma w3_flip_true {n : ℕ} (C : Code n) (t : Fin n) (y : Word n)
    (hcol : C t = col3) (ht : y t = true) :
    w_i C 3 (flipBit t y) + 1 = w_i C 3 y := by
  rw [w_i_eq_card_onesOn, w_i_eq_card_onesOn]
  unfold onesOn
  have hset : (fiber C 3).filter (fun u : Fin n => flipBit t y u = true) =
      ((fiber C 3).filter (fun u : Fin n => y u = true)).erase t := by
    ext u
    by_cases hut : u = t
    · subst u
      simp [fiber, hcol, colVal_col3, ht, flipBit]
    · simp [hut, flipBit]
  have hmem : t ∈ (fiber C 3).filter (fun u : Fin n => y u = true) := by
    simp [fiber, hcol, colVal_col3, ht]
  rw [hset, Finset.card_erase_of_mem hmem]
  have hpos : 0 < ((fiber C 3).filter (fun u : Fin n => y u = true)).card :=
    Finset.card_pos.mpr ⟨t, hmem⟩
  omega

/-- Flipping the changed (type-3) column with `y t = false` increases `w3` by one. -/
lemma w3_flip_false {n : ℕ} (C : Code n) (t : Fin n) (y : Word n)
    (hcol : C t = col3) (ht : y t = false) :
    w_i C 3 (flipBit t y) = w_i C 3 y + 1 := by
  rw [w_i_eq_card_onesOn, w_i_eq_card_onesOn]
  unfold onesOn
  have hset : (fiber C 3).filter (fun u : Fin n => flipBit t y u = true) =
      insert t ((fiber C 3).filter (fun u : Fin n => y u = true)) := by
    ext u
    by_cases hut : u = t
    · subst u
      simp [fiber, hcol, colVal_col3, ht, flipBit]
    · simp [hut, flipBit]
  have hnot : t ∉ (fiber C 3).filter (fun u : Fin n => y u = true) := by
    simp [ht]
  rw [hset, Finset.card_insert_of_notMem hnot]

/-- Flipping the changed column does not change `w5`. -/
lemma w5_flip {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) (hcol : C t = col3) :
    w_i C 5 (flipBit t y) = w_i C 5 y := by
  rw [w_i_eq_card_onesOn, w_i_eq_card_onesOn]
  unfold onesOn
  apply congrArg Finset.card
  ext u
  by_cases hut : u = t
  · subst u
    simp [fiber, hcol, colVal_col3, flipBit]
  · simp [hut, flipBit]

/-- Flipping the changed column does not change `w6`. -/
lemma w6_flip {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) (hcol : C t = col3) :
    w_i C 6 (flipBit t y) = w_i C 6 y := by
  rw [w_i_eq_card_onesOn, w_i_eq_card_onesOn]
  unfold onesOn
  apply congrArg Finset.card
  ext u
  by_cases hut : u = t
  · subst u
    simp [fiber, hcol, colVal_col3, flipBit]
  · simp [hut, flipBit]

/-! ## Generic one-column zones over an O/P split

For an arbitrary partition of the four rows into O and P (encoded by the two
minimum-distance functions `dO` and `dP`), the five zones Y1..Y5 of eq.
(y1)–(y5) and the pairing map `g1` satisfy the same combinatorial facts
(`lemma:1` (Lemma 19)): exhaustiveness, disjointness, and bijectivity.  The proofs below
only need that flipping one bit changes each row distance by at most one.
We instantiate them for the linear 3 → 5 change afterwards (rows
O = {1,4} = indices 0,3 and P = {2,3} = indices 1,2, paper §5).
-/

def gY1 {n : ℕ} (dO dP : Word n → ℕ) (t : Fin n) (y : Word n) : Prop :=
  (dO y ≤ dP y ∧ dP y < dP (flipBit t y)) ∨
    (dO y ≤ dP (flipBit t y) ∧ dP (flipBit t y) ≤ dP y ∧
      dO (flipBit t y) ≤ dP (flipBit t y))

def gY2 {n : ℕ} (dO dP : Word n → ℕ) (t : Fin n) (y : Word n) : Prop :=
  (dP y ≤ dP (flipBit t y) ∧ dP y < dO y) ∨
    (dP (flipBit t y) < dP y ∧ dP y ≤ dO y ∧ dP y ≤ dO (flipBit t y))

def gY3 {n : ℕ} (dO dP : Word n → ℕ) (t : Fin n) (y : Word n) : Prop :=
  dP (flipBit t y) = dO (flipBit t y) ∧ dP (flipBit t y) < dP y ∧ dP y = dO y

def gY4 {n : ℕ} (dO dP : Word n → ℕ) (t : Fin n) (y : Word n) : Prop :=
  dP y = dP (flipBit t y) ∧ dP (flipBit t y) = dO y ∧ dO y < dO (flipBit t y)

def gY5 {n : ℕ} (dO dP : Word n → ℕ) (t : Fin n) (y : Word n) : Prop :=
  dP (flipBit t y) = dO y ∧ dO (flipBit t y) = dP y ∧ dO y < dO (flipBit t y)

/-- The pairing map `g1` of eq. (g1): identity on Y1 ∪ Y3, flip otherwise. -/
noncomputable def gG1 {n : ℕ} (dO dP : Word n → ℕ) (t : Fin n) (y : Word n) : Word n := by
  classical
  exact if gY1 dO dP t y ∨ gY3 dO dP t y then y else flipBit t y

/-- Y1 ∪ Y4 ∪ Y5 = {y : d_O ≤ min(d_P, d_P')} (paper lemma5a). -/
lemma gY1_or_gY4_or_gY5_iff {n : ℕ} (dO dP : Word n → ℕ) (t : Fin n) (y : Word n)
    (h1 : dO (flipBit t y) ≤ dO y + 1) (h2 : dO y ≤ dO (flipBit t y) + 1)
    (h3 : dP (flipBit t y) ≤ dP y + 1) (h4 : dP y ≤ dP (flipBit t y) + 1) :
    (gY1 dO dP t y ∨ gY4 dO dP t y ∨ gY5 dO dP t y) ↔
      dO y ≤ min (dP y) (dP (flipBit t y)) := by
  constructor
  · intro hy
    rcases hy with hy | hy | hy
    · rcases hy with hy | hy
      · rcases hy with ⟨ha, hb⟩
        exact le_min ha (le_trans ha (le_of_lt hb))
      · rcases hy with ⟨ha, hb, hc⟩
        exact le_min (le_trans ha hb) ha
    · rcases hy with ⟨ha, hb, hc⟩
      exact le_min (le_of_eq (hb.symm.trans ha.symm)) (le_of_eq hb.symm)
    · rcases hy with ⟨ha, hb, hc⟩
      exact le_min (le_of_lt (lt_of_lt_of_eq hc hb)) (le_of_eq ha.symm)
  · intro h
    have hdP : dO y ≤ dP y := (le_min_iff.mp h).1
    have hdPp : dO y ≤ dP (flipBit t y) := (le_min_iff.mp h).2
    by_cases hcmp : dP y < dP (flipBit t y)
    · exact Or.inl (Or.inl ⟨hdP, hcmp⟩)
    · have hdPp_le : dP (flipBit t y) ≤ dP y := le_of_not_gt hcmp
      by_cases hop : dO (flipBit t y) ≤ dP (flipBit t y)
      · exact Or.inl (Or.inr ⟨hdPp, hdPp_le, hop⟩)
      · have hop' : dP (flipBit t y) < dO (flipBit t y) := lt_of_not_ge hop
        by_cases heq : dP (flipBit t y) = dP y
        · have hdO_eq : dP (flipBit t y) = dO y := by omega
          exact Or.inr (Or.inl ⟨heq.symm, hdO_eq, by omega⟩)
        · have hdPp_lt : dP (flipBit t y) < dP y := lt_of_le_of_ne hdPp_le heq
          have hdO_eq : dP (flipBit t y) = dO y := by omega
          have hdOp_eq : dO (flipBit t y) = dP y := by omega
          exact Or.inr (Or.inr ⟨hdO_eq, hdOp_eq, by omega⟩)

/-- Y2 ∪ Y3 = {y : d_O > min(d_P, d_P')}. -/
lemma gY2_or_gY3_iff {n : ℕ} (dO dP : Word n → ℕ) (t : Fin n) (y : Word n)
    (h1 : dO (flipBit t y) ≤ dO y + 1) (h2 : dO y ≤ dO (flipBit t y) + 1)
    (h3 : dP (flipBit t y) ≤ dP y + 1) (h4 : dP y ≤ dP (flipBit t y) + 1) :
    (gY2 dO dP t y ∨ gY3 dO dP t y) ↔ dO y > min (dP y) (dP (flipBit t y)) := by
  constructor
  · intro hy
    rcases hy with hy | hy
    · rcases hy with hy | hy
      · rcases hy with ⟨ha, hb⟩
        rw [min_eq_left ha]
        exact hb
      · rcases hy with ⟨ha, hb, hc⟩
        rw [min_eq_right (le_of_lt ha)]
        omega
    · rcases hy with ⟨ha, hb, hc⟩
      rw [min_eq_right (le_of_lt hb)]
      exact lt_of_lt_of_eq hb hc
  · intro h
    have hgt : min (dP y) (dP (flipBit t y)) < dO y := h
    by_cases hcmp : dP y < dP (flipBit t y)
    · have hdP : dP y < dO y := by
        rw [min_eq_left (le_of_lt hcmp)] at hgt
        exact hgt
      exact Or.inl (Or.inl ⟨le_of_lt hcmp, hdP⟩)
    · have hdPp_le : dP (flipBit t y) ≤ dP y := le_of_not_gt hcmp
      by_cases heq : dP (flipBit t y) = dP y
      · have hdP : dP y < dO y := by
          rw [heq] at hgt
          simpa using hgt
        exact Or.inl (Or.inl ⟨le_of_eq heq.symm, hdP⟩)
      · have hdPp_lt : dP (flipBit t y) < dP y := lt_of_le_of_ne hdPp_le heq
        have hdPp_lt_dO : dP (flipBit t y) < dO y := by
          rw [min_eq_right (le_of_lt hdPp_lt)] at hgt
          exact hgt
        by_cases hop : dO (flipBit t y) ≤ dP (flipBit t y)
        · have hdOp_eq : dO (flipBit t y) = dP (flipBit t y) := by omega
          have hdP_eq : dP y = dO y := by omega
          exact Or.inr ⟨hdOp_eq.symm, hdPp_lt, hdP_eq⟩
        · have hdP_le_dO : dP y ≤ dO y := by omega
          have hdP_le_dOp : dP y ≤ dO (flipBit t y) := by omega
          exact Or.inl (Or.inr ⟨hdPp_lt, hdP_le_dO, hdP_le_dOp⟩)

lemma gY1_gY2_disjoint {n : ℕ} (dO dP : Word n → ℕ) (t : Fin n) (y : Word n) :
    ¬ (gY1 dO dP t y ∧ gY2 dO dP t y) := by
  rintro ⟨hy1, hy2⟩
  rcases hy2 with hy2 | hy2
  · rcases hy2 with ⟨h2a, h2b⟩
    rcases hy1 with hy1 | hy1
    · rcases hy1 with ⟨h1a, h1b⟩
      omega
    · rcases hy1 with ⟨h1a, h1b, h1c⟩
      omega
  · rcases hy2 with ⟨h2a, h2b, h2c⟩
    rcases hy1 with hy1 | hy1
    · rcases hy1 with ⟨h1a, h1b⟩
      omega
    · rcases hy1 with ⟨h1a, h1b, h1c⟩
      omega

lemma gY1_gY3_disjoint {n : ℕ} (dO dP : Word n → ℕ) (t : Fin n) (y : Word n) :
    ¬ (gY1 dO dP t y ∧ gY3 dO dP t y) := by
  rintro ⟨hy1, hy3⟩
  rcases hy3 with ⟨h3a, h3b, h3c⟩
  rcases hy1 with hy1 | hy1
  · rcases hy1 with ⟨h1a, h1b⟩
    omega
  · rcases hy1 with ⟨h1a, h1b, h1c⟩
    omega

lemma gY1_gY4_disjoint {n : ℕ} (dO dP : Word n → ℕ) (t : Fin n) (y : Word n) :
    ¬ (gY1 dO dP t y ∧ gY4 dO dP t y) := by
  rintro ⟨hy1, hy4⟩
  rcases hy4 with ⟨h4a, h4b, h4c⟩
  rcases hy1 with hy1 | hy1
  · rcases hy1 with ⟨h1a, h1b⟩
    omega
  · rcases hy1 with ⟨h1a, h1b, h1c⟩
    omega

lemma gY1_gY5_disjoint {n : ℕ} (dO dP : Word n → ℕ) (t : Fin n) (y : Word n) :
    ¬ (gY1 dO dP t y ∧ gY5 dO dP t y) := by
  rintro ⟨hy1, hy5⟩
  rcases hy5 with ⟨h5a, h5b, h5c⟩
  rcases hy1 with hy1 | hy1
  · rcases hy1 with ⟨h1a, h1b⟩
    omega
  · rcases hy1 with ⟨h1a, h1b, h1c⟩
    omega

lemma gY2_gY3_disjoint {n : ℕ} (dO dP : Word n → ℕ) (t : Fin n) (y : Word n) :
    ¬ (gY2 dO dP t y ∧ gY3 dO dP t y) := by
  rintro ⟨hy2, hy3⟩
  rcases hy3 with ⟨h3a, h3b, h3c⟩
  rcases hy2 with hy2 | hy2
  · rcases hy2 with ⟨h2a, h2b⟩
    omega
  · rcases hy2 with ⟨h2a, h2b, h2c⟩
    omega

lemma gY3_gY4_disjoint {n : ℕ} (dO dP : Word n → ℕ) (t : Fin n) (y : Word n) :
    ¬ (gY3 dO dP t y ∧ gY4 dO dP t y) := by
  rintro ⟨hy3, hy4⟩
  rcases hy4 with ⟨h4a, h4b, h4c⟩
  rcases hy3 with ⟨h3a, h3b, h3c⟩
  omega

lemma gY3_gY5_disjoint {n : ℕ} (dO dP : Word n → ℕ) (t : Fin n) (y : Word n) :
    ¬ (gY3 dO dP t y ∧ gY5 dO dP t y) := by
  rintro ⟨hy3, hy5⟩
  rcases hy5 with ⟨h5a, h5b, h5c⟩
  rcases hy3 with ⟨h3a, h3b, h3c⟩
  omega

/-- Exhaustiveness: every word lies in one of the five zones. -/
lemma gY_mem {n : ℕ} (dO dP : Word n → ℕ) (t : Fin n) (y : Word n)
    (h1 : dO (flipBit t y) ≤ dO y + 1) (h2 : dO y ≤ dO (flipBit t y) + 1)
    (h3 : dP (flipBit t y) ≤ dP y + 1) (h4 : dP y ≤ dP (flipBit t y) + 1) :
    gY1 dO dP t y ∨ gY2 dO dP t y ∨ gY3 dO dP t y ∨ gY4 dO dP t y ∨
      gY5 dO dP t y := by
  by_cases h : dO y ≤ min (dP y) (dP (flipBit t y))
  · have hA := (gY1_or_gY4_or_gY5_iff dO dP t y h1 h2 h3 h4).mpr h
    rcases hA with hy | hy | hy
    · exact Or.inl hy
    · exact Or.inr (Or.inr (Or.inr (Or.inl hy)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr hy)))
  · have hB := (gY2_or_gY3_iff dO dP t y h1 h2 h3 h4).mpr (lt_of_not_ge h)
    rcases hB with hy | hy
    · exact Or.inr (Or.inl hy)
    · exact Or.inr (Or.inr (Or.inl hy))

/-- Flipping the bit at t maps Y1 ∪ Y3 back to itself. -/
lemma gY13_closed {n : ℕ} (dO dP : Word n → ℕ) (t : Fin n) (y : Word n)
    (h1 : dO (flipBit t y) ≤ dO y + 1) (h2 : dO y ≤ dO (flipBit t y) + 1)
    (h3 : dP (flipBit t y) ≤ dP y + 1) (h4 : dP y ≤ dP (flipBit t y) + 1) :
    (gY1 dO dP t (flipBit t y) ∨ gY3 dO dP t (flipBit t y)) →
      (gY1 dO dP t y ∨ gY3 dO dP t y) := by
  intro hy
  rcases hy with hy | hy
  · rcases hy with hy | hy
    · have hOp_le_Pp : dO (flipBit t y) ≤ dP (flipBit t y) := hy.1
      have hPp_lt_P : dP (flipBit t y) < dP y := by
        simpa [flipBit_involutive] using hy.2
      by_cases h1 : dO y ≤ dP (flipBit t y)
      · exact Or.inl (Or.inr ⟨h1, le_of_lt hPp_lt_P, hOp_le_Pp⟩)
      · have hOp_eq_Pp : dO (flipBit t y) = dP (flipBit t y) := by omega
        have hP_eq_dO : dP y = dO y := by omega
        exact Or.inr ⟨hOp_eq_Pp.symm, hPp_lt_P, hP_eq_dO⟩
    · have hOp_le_P : dO (flipBit t y) ≤ dP y := by
        simpa [flipBit_involutive] using hy.1
      have hP_le_Pp : dP y ≤ dP (flipBit t y) := by
        simpa [flipBit_involutive] using hy.2.1
      have hO_le_P : dO y ≤ dP y := by
        simpa [flipBit_involutive] using hy.2.2
      by_cases h2 : dP y < dP (flipBit t y)
      · exact Or.inl (Or.inl ⟨hO_le_P, h2⟩)
      · have hP_eq_Pp : dP y = dP (flipBit t y) := le_antisymm hP_le_Pp (le_of_not_gt h2)
        exact Or.inl (Or.inr ⟨by rw [← hP_eq_Pp]; exact hO_le_P, by rw [hP_eq_Pp],
          by rw [← hP_eq_Pp]; exact hOp_le_P⟩)
  · rcases hy with ⟨h1, h2, h3⟩
    have hP_eq_O : dP y = dO y := by
      simpa [flipBit_involutive] using h1
    have hP_lt_Pp : dP y < dP (flipBit t y) := by
      simpa [flipBit_involutive] using h2
    have hPp_eq_Op : dP (flipBit t y) = dO (flipBit t y) := by
      simpa [flipBit_involutive] using h3
    exact Or.inl (Or.inl ⟨by rw [hP_eq_O], hP_lt_Pp⟩)

/-- Flipping the bit at t maps the complement of Y1 ∪ Y3 into itself. -/
lemma gY13_complement_closed {n : ℕ} (dO dP : Word n → ℕ) (t : Fin n) (y : Word n)
    (h1 : dO (flipBit t y) ≤ dO y + 1) (h2 : dO y ≤ dO (flipBit t y) + 1)
    (h3 : dP (flipBit t y) ≤ dP y + 1) (h4 : dP y ≤ dP (flipBit t y) + 1) :
    ¬ (gY1 dO dP t y ∨ gY3 dO dP t y) →
      ¬ (gY1 dO dP t (flipBit t y) ∨ gY3 dO dP t (flipBit t y)) := by
  intro hnot h
  exact hnot (gY13_closed dO dP t y h1 h2 h3 h4 h)

/-- `g1` is a bijection. -/
theorem gG1_bijective {n : ℕ} (dO dP : Word n → ℕ) (t : Fin n)
    (h1 : ∀ y : Word n, dO (flipBit t y) ≤ dO y + 1)
    (h2 : ∀ y : Word n, dO y ≤ dO (flipBit t y) + 1)
    (h3 : ∀ y : Word n, dP (flipBit t y) ≤ dP y + 1)
    (h4 : ∀ y : Word n, dP y ≤ dP (flipBit t y) + 1) :
    Function.Bijective (gG1 dO dP t) := by
  classical
  let h : Word n → Word n := fun z =>
    if gY1 dO dP t z ∨ gY3 dO dP t z then z else flipBit t z
  have hleft : ∀ y : Word n, h (gG1 dO dP t y) = y := by
    intro y
    by_cases hy : gY1 dO dP t y ∨ gY3 dO dP t y
    · simp [gG1, h, hy]
    · have hcl := gY13_complement_closed dO dP t y (h1 y) (h2 y) (h3 y) (h4 y) hy
      simp [gG1, h, hy, hcl, flipBit_involutive t y]
  have hright : ∀ z : Word n, gG1 dO dP t (h z) = z := by
    intro z
    by_cases hz : gY1 dO dP t z ∨ gY3 dO dP t z
    · simp [gG1, h, hz]
    · have hcl := gY13_complement_closed dO dP t z (h1 z) (h2 z) (h3 z) (h4 z) hz
      simp [gG1, h, hz, hcl, flipBit_involutive t z]
  refine ⟨?inj, ?surj⟩
  · intro a b hab
    rw [← hleft a, ← hleft b, hab]
  · intro z
    exact ⟨h z, hleft z⟩

/-! ## The linear 3 → 5 change: local O/P split

Replacing a type-3 column by type 5 keeps rows 1 and 4 (indices 0, 3) and
changes rows 2 and 3 (indices 1, 2), so the paper's §5 split is
O = {1,4}, P = {2,3} in row labels (eq. op, §5).
-/

/-- d_O = min(d_1, d_4) (rows 0 and 3). -/
def linO {n : ℕ} (C : Code n) (y : Word n) : ℕ :=
  min (dRow C ⟨0, by decide⟩ y) (dRow C ⟨3, by decide⟩ y)

/-- d_P = min(d_2, d_3) (rows 1 and 2). -/
def linP {n : ℕ} (C : Code n) (y : Word n) : ℕ :=
  min (dRow C ⟨1, by decide⟩ y) (dRow C ⟨2, by decide⟩ y)

/-- d_O(F_t y). -/
def linOp {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) : ℕ := linO C (flipBit t y)

/-- d_P(F_t y). -/
def linPp {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) : ℕ := linP C (flipBit t y)

abbrev linY1 {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) : Prop :=
  gY1 (linO C) (linP C) t y

abbrev linY2 {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) : Prop :=
  gY2 (linO C) (linP C) t y

abbrev linY3 {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) : Prop :=
  gY3 (linO C) (linP C) t y

abbrev linY4 {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) : Prop :=
  gY4 (linO C) (linP C) t y

abbrev linY5 {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) : Prop :=
  gY5 (linO C) (linP C) t y

noncomputable abbrev linG1 {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) : Word n :=
  gG1 (linO C) (linP C) t y

instance decLinY1 {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) :
    Decidable (linY1 C t y) := by
  unfold linY1 gY1
  infer_instance

instance decLinY2 {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) :
    Decidable (linY2 C t y) := by
  unfold linY2 gY2
  infer_instance

instance decLinY3 {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) :
    Decidable (linY3 C t y) := by
  unfold linY3 gY3
  infer_instance

instance decLinY4 {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) :
    Decidable (linY4 C t y) := by
  unfold linY4 gY4
  infer_instance

instance decLinY5 {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) :
    Decidable (linY5 C t y) := by
  unfold linY5 gY5
  infer_instance

lemma min2_le_add_one {a b a' b' : ℕ} (h1 : a' ≤ a + 1) (h2 : b' ≤ b + 1) :
    min a' b' ≤ min a b + 1 := by
  calc
    min a' b' ≤ min (a + 1) (b + 1) := by
      apply le_min
      · exact le_trans (Nat.min_le_left _ _) h1
      · exact le_trans (Nat.min_le_right _ _) h2
    _ = min a b + 1 := by omega

/-- Flipping one bit changes d_O by at most one. -/
lemma linO_flip_bounds {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) :
    linO C (flipBit t y) ≤ linO C y + 1 ∧ linO C y ≤ linO C (flipBit t y) + 1 := by
  unfold linO
  constructor
  · apply min2_le_add_one
    · exact (dRow_flip_le_add_one C ⟨0, by decide⟩ t y).1
    · exact (dRow_flip_le_add_one C ⟨3, by decide⟩ t y).1
  · apply min2_le_add_one
    · exact (dRow_flip_le_add_one C ⟨0, by decide⟩ t y).2
    · exact (dRow_flip_le_add_one C ⟨3, by decide⟩ t y).2

/-- Flipping one bit changes d_P by at most one. -/
lemma linP_flip_bounds {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) :
    linP C (flipBit t y) ≤ linP C y + 1 ∧ linP C y ≤ linP C (flipBit t y) + 1 := by
  unfold linP
  constructor
  · apply min2_le_add_one
    · exact (dRow_flip_le_add_one C ⟨1, by decide⟩ t y).1
    · exact (dRow_flip_le_add_one C ⟨2, by decide⟩ t y).1
  · apply min2_le_add_one
    · exact (dRow_flip_le_add_one C ⟨1, by decide⟩ t y).2
    · exact (dRow_flip_le_add_one C ⟨2, by decide⟩ t y).2

/-- Exhaustiveness of the linear-case zones. -/
lemma lin_y_mem {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) :
    linY1 C t y ∨ linY2 C t y ∨ linY3 C t y ∨ linY4 C t y ∨ linY5 C t y :=
  gY_mem (linO C) (linP C) t y
    (linO_flip_bounds C t y).1 (linO_flip_bounds C t y).2
    (linP_flip_bounds C t y).1 (linP_flip_bounds C t y).2

/-- `g1` is a bijection in the linear case. -/
theorem linG1_bijective {n : ℕ} (C : Code n) (t : Fin n) :
    Function.Bijective (linG1 C t) :=
  gG1_bijective (linO C) (linP C) t
    (fun y => (linO_flip_bounds C t y).1) (fun y => (linO_flip_bounds C t y).2)
    (fun y => (linP_flip_bounds C t y).1) (fun y => (linP_flip_bounds C t y).2)

noncomputable def linG1Equiv {n : ℕ} (C : Code n) (t : Fin n) : Word n ≃ Word n :=
  Equiv.ofBijective (linG1 C t) (linG1_bijective C t)

/-- d_C(y) = min(d_O(y), d_P(y)) for the linear split. -/
lemma lin_dCode_eq_min {n : ℕ} (C : Code n) (y : Word n) :
    dCode C y = min (linO C y) (linP C y) := by
  unfold dCode linO linP
  ac_rfl

/-- Replacing a type-3 column by type 5 leaves rows 1 and 4 unchanged. -/
lemma lin_dRow_replace_eq {n : ℕ} (C : Code n) (t : Fin n) (y : Word n)
    (hcol : C t = col3) (j : Fin 4) (hj : j ≠ 1) (hj2 : j ≠ 2) :
    dRow (replaceColumn C t col5) j y = dRow C j y := by
  rw [dRow_eq_indicator_sum, dRow_eq_indicator_sum]
  apply Finset.sum_congr rfl
  intro u _
  by_cases h : u = t <;> simp [replaceColumn, h]
  · have hb : colBit j col5 = colBit j col3 := by
      fin_cases j <;> simp [colBit, col3, col5] at hj hj2 ⊢
    rw [hcol, hb]

/-- Replacing a type-3 column by type 5 flips rows 2 and 3. -/
lemma lin_dRow_replace_flip {n : ℕ} (C : Code n) (t : Fin n) (y : Word n)
    (hcol : C t = col3) (j : Fin 4) (hj : j = 1 ∨ j = 2) :
    dRow (replaceColumn C t col5) j y = dRow C j (flipBit t y) := by
  rcases hj with rfl | rfl
  · rw [dRow_eq_indicator_sum, dRow_eq_indicator_sum]
    apply Finset.sum_congr rfl
    intro u _
    by_cases h : u = t <;> by_cases hy : y t = true <;>
      simp [replaceColumn, flipBit, colBit, col3, col5, h, hcol, hy]
  · rw [dRow_eq_indicator_sum, dRow_eq_indicator_sum]
    apply Finset.sum_congr rfl
    intro u _
    by_cases h : u = t <;> by_cases hy : y t = true <;>
      simp [replaceColumn, flipBit, colBit, col3, col5, h, hcol, hy]

/-- d_{C'}(y) = min(d_O(y), d_P'(y)) for the 3 → 5 change (paper eq. dcp). -/
lemma lin_dCode_replace {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) (hcol : C t = col3) :
    dCode (replaceColumn C t col5) y = min (linO C y) (linPp C t y) := by
  unfold dCode linO linPp linP
  change min (dRow (replaceColumn C t col5) ⟨0, by decide⟩ y)
      (min (dRow (replaceColumn C t col5) ⟨1, by decide⟩ y)
        (min (dRow (replaceColumn C t col5) ⟨2, by decide⟩ y)
          (dRow (replaceColumn C t col5) ⟨3, by decide⟩ y))) =
    min (min (dRow C ⟨0, by decide⟩ y) (dRow C ⟨3, by decide⟩ y))
      (min (dRow C ⟨1, by decide⟩ (flipBit t y)) (dRow C ⟨2, by decide⟩ (flipBit t y)))
  rw [lin_dRow_replace_eq C t y hcol ⟨0, by decide⟩ (by decide) (by decide),
    lin_dRow_replace_flip C t y hcol ⟨1, by decide⟩ (by decide),
    lin_dRow_replace_flip C t y hcol ⟨2, by decide⟩ (by decide),
    lin_dRow_replace_eq C t y hcol ⟨3, by decide⟩ (by decide) (by decide)]
  omega

/-- d_{C'}(F_t y) = min(d_O'(y), d_P(y)) for the 3 → 5 change (paper eq. dcpf). -/
lemma lin_dCode_replace_flip {n : ℕ} (C : Code n) (t : Fin n) (y : Word n)
    (hcol : C t = col3) :
    dCode (replaceColumn C t col5) (flipBit t y) = min (linOp C t y) (linP C y) := by
  rw [lin_dCode_replace C t (flipBit t y) hcol]
  unfold linOp linPp
  rw [flipBit_involutive]

/-- C' is exactly the replacement of column t by type 5. -/
lemma replace_3_5_eq {n : ℕ} (C C' : Code n) (t : Fin n) (hcol' : C' t = col5)
    (hsame : ∀ u : Fin n, u ≠ t → C' u = C u) :
    C' = replaceColumn C t col5 := by
  funext u
  by_cases hu : u = t <;> simp [replaceColumn, hu, hcol', hsame]

lemma linY1_Y2_disjoint {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) :
    ¬ (linY1 C t y ∧ linY2 C t y) :=
  gY1_gY2_disjoint (linO C) (linP C) t y

lemma linY2_Y3_disjoint {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) :
    ¬ (linY2 C t y ∧ linY3 C t y) :=
  gY2_gY3_disjoint (linO C) (linP C) t y

lemma linY1_Y4_disjoint {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) :
    ¬ (linY1 C t y ∧ linY4 C t y) :=
  gY1_gY4_disjoint (linO C) (linP C) t y

lemma linY3_Y4_disjoint {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) :
    ¬ (linY3 C t y ∧ linY4 C t y) :=
  gY3_gY4_disjoint (linO C) (linP C) t y

lemma linY1_Y5_disjoint {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) :
    ¬ (linY1 C t y ∧ linY5 C t y) :=
  gY1_gY5_disjoint (linO C) (linP C) t y

lemma linY3_Y5_disjoint {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) :
    ¬ (linY3 C t y ∧ linY5 C t y) :=
  gY3_gY5_disjoint (linO C) (linP C) t y

/-! ## Lemma `lemma:1` (Lemma 19) for the 3 → 5 change -/

/-- y ∈ Y1 → d_C(y) = d_{C'}(y) = d_O. -/
theorem lin_y_rel_1 {n : ℕ} (C C' : Code n) (t : Fin n) (hcol : C t = col3)
    (hcol' : C' t = col5) (hsame : ∀ u : Fin n, u ≠ t → C' u = C u)
    {y : Word n} (hy : linY1 C t y) :
    dCode C y = dCode C' y ∧ dCode C y = linO C y := by
  have hrep : C' = replaceColumn C t col5 := replace_3_5_eq C C' t hcol' hsame
  have hdC : dCode C y = min (linO C y) (linP C y) := lin_dCode_eq_min C y
  have hdC' : dCode C' y = min (linO C y) (linPp C t y) := by
    rw [hrep, lin_dCode_replace C t y hcol]
  rcases hy with hy | hy
  · rcases hy with ⟨h1, h2⟩
    have hdOp : linO C y ≤ linPp C t y := by
      simpa [linPp] using (le_trans h1 (le_of_lt h2))
    constructor
    · rw [hdC, hdC']
      simp [linPp]
      rw [min_eq_left h1, min_eq_left (le_trans h1 (le_of_lt h2))]
    · rw [hdC, min_eq_left h1]
  · rcases hy with ⟨h1, h2, h3⟩
    have hdP : linO C y ≤ linP C y := le_trans h1 h2
    constructor
    · rw [hdC, hdC']
      simp [linPp]
      rw [min_eq_left hdP, min_eq_left h1]
    · rw [hdC, min_eq_left hdP]

/-- y ∈ Y2 → d_C(y) = d_{C'}(F_t y) = d_P. -/
theorem lin_y_rel_2 {n : ℕ} (C C' : Code n) (t : Fin n) (hcol : C t = col3)
    (hcol' : C' t = col5) (hsame : ∀ u : Fin n, u ≠ t → C' u = C u)
    {y : Word n} (hy : linY2 C t y) :
    dCode C y = dCode C' (flipBit t y) ∧ dCode C y = linP C y := by
  have hrep : C' = replaceColumn C t col5 := replace_3_5_eq C C' t hcol' hsame
  have hdC : dCode C y = min (linO C y) (linP C y) := lin_dCode_eq_min C y
  have hdC'f : dCode C' (flipBit t y) = min (linOp C t y) (linP C y) := by
    rw [hrep, lin_dCode_replace_flip C t y hcol]
  rcases hy with hy | hy
  · rcases hy with ⟨h1, h2⟩
    have hdP : linP C y ≤ linO C y := le_of_lt h2
    have hdPo : linP C y ≤ linOp C t y := by
      change linP C y ≤ linO C (flipBit t y)
      have h := linO_flip_bounds C t y
      omega
    constructor
    · rw [hdC, hdC'f]
      simp [linOp]
      rw [min_eq_right hdP, min_eq_right (by simpa [linOp] using hdPo)]
    · rw [hdC, min_eq_right hdP]
  · rcases hy with ⟨h1, h2, h3⟩
    have h3' : linP C y ≤ linOp C t y := by
      simpa [linOp] using h3
    constructor
    · rw [hdC, hdC'f]
      rw [min_eq_right h2, min_eq_right h3']
    · rw [hdC, min_eq_right h2]

/-- y ∈ Y3 → d_C(y) = d_P = d_{C'}(y) + 1. -/
theorem lin_y_rel_3 {n : ℕ} (C C' : Code n) (t : Fin n) (hcol : C t = col3)
    (hcol' : C' t = col5) (hsame : ∀ u : Fin n, u ≠ t → C' u = C u)
    {y : Word n} (hy : linY3 C t y) :
    dCode C y = linP C y ∧ dCode C y = dCode C' y + 1 := by
  have hrep : C' = replaceColumn C t col5 := replace_3_5_eq C C' t hcol' hsame
  have hdC : dCode C y = min (linO C y) (linP C y) := lin_dCode_eq_min C y
  have hdC' : dCode C' y = min (linO C y) (linPp C t y) := by
    rw [hrep, lin_dCode_replace C t y hcol]
  rcases hy with ⟨h1, h2, h3⟩
  have hdP : dCode C y = linP C y := by
    rw [hdC]
    rw [← h3]
    simp
  have hdC'p : dCode C' y = linPp C t y := by
    have hle : linPp C t y ≤ linO C y := by
      simpa [linPp] using (le_of_lt (lt_of_lt_of_eq h2 h3))
    rw [hdC', min_eq_right hle]
  constructor
  · exact hdP
  · rw [hdP, hdC'p]
    change linP C y = linP C (flipBit t y) + 1
    have h := linP_flip_bounds C t y
    omega

/-- y ∈ Y4 → d_C(y) = d_O = d_{C'}(F_t y) = d_P. -/
theorem lin_y_rel_4 {n : ℕ} (C C' : Code n) (t : Fin n) (hcol : C t = col3)
    (hcol' : C' t = col5) (hsame : ∀ u : Fin n, u ≠ t → C' u = C u)
    {y : Word n} (hy : linY4 C t y) :
    dCode C y = linO C y ∧ dCode C y = dCode C' (flipBit t y) ∧
      dCode C' (flipBit t y) = linP C y := by
  have hrep : C' = replaceColumn C t col5 := replace_3_5_eq C C' t hcol' hsame
  have hdC : dCode C y = min (linO C y) (linP C y) := lin_dCode_eq_min C y
  have hdC'f : dCode C' (flipBit t y) = min (linOp C t y) (linP C y) := by
    rw [hrep, lin_dCode_replace_flip C t y hcol]
  rcases hy with ⟨h1, h2, h3⟩
  have hdO : dCode C y = linO C y := by
    rw [hdC]
    rw [h1, h2]
    simp
  have hdP' : dCode C' (flipBit t y) = linP C y := by
    rw [hdC'f]
    have hle : linP C y ≤ linOp C t y := by
      have hd : linP C y = linO C y := h1.trans h2
      rw [hd]
      exact le_of_lt h3
    rw [min_eq_right hle]
  constructor
  · exact hdO
  · constructor
    · rw [hdO, hdP']
      exact (h1.trans h2).symm
    · exact hdP'

/-- y ∈ Y5 → d_C(y) + 1 = d_{C'}(F_t y) = d_P. -/
theorem lin_y_rel_5 {n : ℕ} (C C' : Code n) (t : Fin n) (hcol : C t = col3)
    (hcol' : C' t = col5) (hsame : ∀ u : Fin n, u ≠ t → C' u = C u)
    {y : Word n} (hy : linY5 C t y) :
    dCode C y + 1 = dCode C' (flipBit t y) ∧ dCode C' (flipBit t y) = linP C y := by
  have hrep : C' = replaceColumn C t col5 := replace_3_5_eq C C' t hcol' hsame
  have hdC : dCode C y = min (linO C y) (linP C y) := lin_dCode_eq_min C y
  have hdC'f : dCode C' (flipBit t y) = min (linOp C t y) (linP C y) := by
    rw [hrep, lin_dCode_replace_flip C t y hcol]
  rcases hy with ⟨h1, h2, h3⟩
  have hdO : dCode C y = linO C y := by
    rw [hdC]
    have hle : linO C y ≤ linP C y := le_of_lt (lt_of_lt_of_eq h3 h2)
    rw [min_eq_left hle]
  have hdP' : dCode C' (flipBit t y) = linP C y := by
    have h2' : linOp C t y = linP C y := by simpa [linOp] using h2
    rw [hdC'f, h2']
    simp
  constructor
  · rw [hdO, hdP']
    have h := linO_flip_bounds C t y
    omega
  · exact hdP'

/-- Corollary `cor:1` (Corollary 21) (3) for the 3 → 5 change: if Y5 = ∅ then λ_{C'} ≥ λ_C,
with equality iff Y3 = ∅. -/
theorem lin_cumulative_no_y5 {n : ℕ} (C C' : Code n) (t : Fin n)
    (hcol : C t = col3) (hcol' : C' t = col5)
    (hsame : ∀ u : Fin n, u ≠ t → C' u = C u)
    (h5 : ∀ y : Word n, ¬ linY5 C t y) :
    UniversalBetter C' C ∧
      (UniversalEqual C' C ↔ ∀ y : Word n, ¬ linY3 C t y) := by
  let S : Finset (Word n) := Finset.univ.filter (linY3 C t)
  have hgt : ∀ y : Word n, y ∈ S → dCode C y > dCode C' (linG1 C t y) := by
    intro y hy
    have h3 : linY3 C t y := (Finset.mem_filter.mp hy).2
    have h := (lin_y_rel_3 C C' t hcol hcol' hsame h3).2
    have h3' : gY3 (linO C) (linP C) t y := h3
    simp [linG1, gG1, h3']
    omega
  have heq : ∀ y : Word n, y ∉ S → dCode C y = dCode C' (linG1 C t y) := by
    intro y hy
    have h3 : ¬ linY3 C t y := by
      intro h3
      exact hy (Finset.mem_filter.mpr ⟨by simp, h3⟩)
    have hy14 : linY1 C t y ∨ linY2 C t y ∨ linY4 C t y := by
      rcases lin_y_mem C t y with hy' | hy' | hy' | hy' | hy'
      · exact Or.inl hy'
      · exact Or.inr (Or.inl hy')
      · exfalso; exact h3 hy'
      · exact Or.inr (Or.inr hy')
      · exfalso; exact h5 y hy'
    rcases hy14 with hy1 | hy2 | hy4
    · have h := lin_y_rel_1 C C' t hcol hcol' hsame hy1
      have hy1' : gY1 (linO C) (linP C) t y := hy1
      simp [linG1, gG1, hy1', h.1]
    · have h1 : ¬ linY1 C t y := fun hy1 => linY1_Y2_disjoint C t y ⟨hy1, hy2⟩
      have h3' : ¬ linY3 C t y := fun hy3 => linY2_Y3_disjoint C t y ⟨hy2, hy3⟩
      have h1' : ¬ gY1 (linO C) (linP C) t y := h1
      have h3'' : ¬ gY3 (linO C) (linP C) t y := h3'
      have hg1 : linG1 C t y = flipBit t y := by
        simp [linG1, gG1, h1', h3'']
      rw [hg1]
      exact (lin_y_rel_2 C C' t hcol hcol' hsame hy2).1
    · have h1 : ¬ linY1 C t y := fun hy1 => linY1_Y4_disjoint C t y ⟨hy1, hy4⟩
      have h3' : ¬ linY3 C t y := fun hy3 => linY3_Y4_disjoint C t y ⟨hy3, hy4⟩
      have h1' : ¬ gY1 (linO C) (linP C) t y := h1
      have h3'' : ¬ gY3 (linO C) (linP C) t y := h3'
      have hg1 : linG1 C t y = flipBit t y := by
        simp [linG1, gG1, h1', h3'']
      rw [hg1]
      exact (lin_y_rel_4 C C' t hcol hcol' hsame hy4).2.1
  constructor
  · exact compare_bij C C' S (linG1Equiv C t) hgt heq
  · constructor
    · intro heq2 y h3
      have hne : ∃ y : Word n, y ∈ S := ⟨y, Finset.mem_filter.mpr ⟨by simp, h3⟩⟩
      have hstrict := compare_bij_strict C C' S (linG1Equiv C t) hgt heq hne
      have hgt' : lambda C' (1 / 4 : ℝ) > lambda C (1 / 4) :=
        hstrict (1 / 4) (by norm_num) (by norm_num)
      have heq' : lambda C' (1 / 4 : ℝ) = lambda C (1 / 4) :=
        heq2 (1 / 4) (by norm_num) (by norm_num)
      exact (lt_irrefl _ (hgt'.trans_eq heq')).elim
    · intro hy3
      have heqall : ∀ y : Word n, dCode C y = dCode C' (linG1 C t y) := by
        intro y
        by_cases hy : y ∈ S
        · exact False.elim (hy3 y (Finset.mem_filter.mp hy).2)
        · exact heq y hy
      exact compare_bij_eq C C' (linG1Equiv C t) heqall

/-! ## Weight characterizations of the zones for `C(n3,n5,n6)`

With `C = linearCode n3 n5 n6` and a type-3 column at `t`, the four row
distances are (paper eq. d, §5):
`d1 = w3+w5+w6`, `d2 = w3+(n5−w5)+(n6−w6)`, `d3 = (n3−w3)+w5+(n6−w6)`,
`d4 = (n3−w3)+(n5−w5)+w6` (rows 0..3).  Flipping `t` changes only `w3`, so
the primed distances shift by ±1; we record those shifts and then the zone
characterizations that drive the parity analysis (eq. cli4–cli9).
-/

/-- Flipping a type-3 column with `y t = true` decreases row-1 distance. -/
lemma lin_dRow0_flip_true {n3 n5 n6 : ℕ} (y : Word (n3 + n5 + n6))
    (t : Fin (n3 + n5 + n6)) (hcol : linearCode n3 n5 n6 t = col3) (ht : y t = true) :
    dRow (linearCode n3 n5 n6) ⟨0, by decide⟩ (flipBit t y) + 1 =
      dRow (linearCode n3 n5 n6) ⟨0, by decide⟩ y := by
  rw [linear_dRow0 (flipBit t y), linear_dRow0 y]
  have hw3 := w3_flip_true (C := linearCode n3 n5 n6) t y hcol ht
  have hw5 := w5_flip (C := linearCode n3 n5 n6) t y hcol
  have hw6 := w6_flip (C := linearCode n3 n5 n6) t y hcol
  rw [hw5, hw6]
  omega

/-- Flipping a type-3 column with `y t = true` decreases row-2 distance. -/
lemma lin_dRow1_flip_true {n3 n5 n6 : ℕ} (y : Word (n3 + n5 + n6))
    (t : Fin (n3 + n5 + n6)) (hcol : linearCode n3 n5 n6 t = col3) (ht : y t = true) :
    dRow (linearCode n3 n5 n6) ⟨1, by decide⟩ (flipBit t y) + 1 =
      dRow (linearCode n3 n5 n6) ⟨1, by decide⟩ y := by
  rw [linear_dRow1 (flipBit t y), linear_dRow1 y]
  have hw3 := w3_flip_true (C := linearCode n3 n5 n6) t y hcol ht
  have hw5 := w5_flip (C := linearCode n3 n5 n6) t y hcol
  have hw6 := w6_flip (C := linearCode n3 n5 n6) t y hcol
  rw [hw5, hw6]
  omega

/-- Flipping a type-3 column with `y t = true` increases row-3 distance. -/
lemma lin_dRow2_flip_true {n3 n5 n6 : ℕ} (y : Word (n3 + n5 + n6))
    (t : Fin (n3 + n5 + n6)) (hcol : linearCode n3 n5 n6 t = col3) (ht : y t = true) :
    dRow (linearCode n3 n5 n6) ⟨2, by decide⟩ (flipBit t y) =
      dRow (linearCode n3 n5 n6) ⟨2, by decide⟩ y + 1 := by
  rw [linear_dRow2 (flipBit t y), linear_dRow2 y]
  have hw3 := w3_flip_true (C := linearCode n3 n5 n6) t y hcol ht
  have hw5 := w5_flip (C := linearCode n3 n5 n6) t y hcol
  have hw6 := w6_flip (C := linearCode n3 n5 n6) t y hcol
  have hw3le : w_i (linearCode n3 n5 n6) 3 y ≤ n3 :=
    le_trans (w_i_le_count (linearCode n3 n5 n6) 3 y) (le_of_eq linear_count_3)
  have hw5le : w_i (linearCode n3 n5 n6) 5 y ≤ n5 :=
    le_trans (w_i_le_count (linearCode n3 n5 n6) 5 y) (le_of_eq linear_count_5)
  have hw6le : w_i (linearCode n3 n5 n6) 6 y ≤ n6 :=
    le_trans (w_i_le_count (linearCode n3 n5 n6) 6 y) (le_of_eq linear_count_6)
  rw [hw5, hw6]
  omega

/-- Flipping a type-3 column with `y t = true` increases row-4 distance. -/
lemma lin_dRow3_flip_true {n3 n5 n6 : ℕ} (y : Word (n3 + n5 + n6))
    (t : Fin (n3 + n5 + n6)) (hcol : linearCode n3 n5 n6 t = col3) (ht : y t = true) :
    dRow (linearCode n3 n5 n6) ⟨3, by decide⟩ (flipBit t y) =
      dRow (linearCode n3 n5 n6) ⟨3, by decide⟩ y + 1 := by
  rw [linear_dRow3 (flipBit t y), linear_dRow3 y]
  have hw3 := w3_flip_true (C := linearCode n3 n5 n6) t y hcol ht
  have hw5 := w5_flip (C := linearCode n3 n5 n6) t y hcol
  have hw6 := w6_flip (C := linearCode n3 n5 n6) t y hcol
  have hw3le : w_i (linearCode n3 n5 n6) 3 y ≤ n3 :=
    le_trans (w_i_le_count (linearCode n3 n5 n6) 3 y) (le_of_eq linear_count_3)
  have hw5le : w_i (linearCode n3 n5 n6) 5 y ≤ n5 :=
    le_trans (w_i_le_count (linearCode n3 n5 n6) 5 y) (le_of_eq linear_count_5)
  have hw6le : w_i (linearCode n3 n5 n6) 6 y ≤ n6 :=
    le_trans (w_i_le_count (linearCode n3 n5 n6) 6 y) (le_of_eq linear_count_6)
  rw [hw5, hw6]
  omega

/-- Flipping a type-3 column with `y t = false` increases row-1 distance. -/
lemma lin_dRow0_flip_false {n3 n5 n6 : ℕ} (y : Word (n3 + n5 + n6))
    (t : Fin (n3 + n5 + n6)) (hcol : linearCode n3 n5 n6 t = col3) (ht : y t = false) :
    dRow (linearCode n3 n5 n6) ⟨0, by decide⟩ (flipBit t y) =
      dRow (linearCode n3 n5 n6) ⟨0, by decide⟩ y + 1 := by
  rw [linear_dRow0 (flipBit t y), linear_dRow0 y]
  have hw3 := w3_flip_false (C := linearCode n3 n5 n6) t y hcol ht
  have hw5 := w5_flip (C := linearCode n3 n5 n6) t y hcol
  have hw6 := w6_flip (C := linearCode n3 n5 n6) t y hcol
  have hw3le : w_i (linearCode n3 n5 n6) 3 y ≤ n3 :=
    le_trans (w_i_le_count (linearCode n3 n5 n6) 3 y) (le_of_eq linear_count_3)
  have hw5le : w_i (linearCode n3 n5 n6) 5 y ≤ n5 :=
    le_trans (w_i_le_count (linearCode n3 n5 n6) 5 y) (le_of_eq linear_count_5)
  have hw6le : w_i (linearCode n3 n5 n6) 6 y ≤ n6 :=
    le_trans (w_i_le_count (linearCode n3 n5 n6) 6 y) (le_of_eq linear_count_6)
  rw [hw5, hw6]
  omega

/-- Flipping a type-3 column with `y t = false` increases row-2 distance. -/
lemma lin_dRow1_flip_false {n3 n5 n6 : ℕ} (y : Word (n3 + n5 + n6))
    (t : Fin (n3 + n5 + n6)) (hcol : linearCode n3 n5 n6 t = col3) (ht : y t = false) :
    dRow (linearCode n3 n5 n6) ⟨1, by decide⟩ (flipBit t y) =
      dRow (linearCode n3 n5 n6) ⟨1, by decide⟩ y + 1 := by
  rw [linear_dRow1 (flipBit t y), linear_dRow1 y]
  have hw3 := w3_flip_false (C := linearCode n3 n5 n6) t y hcol ht
  have hw5 := w5_flip (C := linearCode n3 n5 n6) t y hcol
  have hw6 := w6_flip (C := linearCode n3 n5 n6) t y hcol
  have hw3le : w_i (linearCode n3 n5 n6) 3 y ≤ n3 :=
    le_trans (w_i_le_count (linearCode n3 n5 n6) 3 y) (le_of_eq linear_count_3)
  have hw5le : w_i (linearCode n3 n5 n6) 5 y ≤ n5 :=
    le_trans (w_i_le_count (linearCode n3 n5 n6) 5 y) (le_of_eq linear_count_5)
  have hw6le : w_i (linearCode n3 n5 n6) 6 y ≤ n6 :=
    le_trans (w_i_le_count (linearCode n3 n5 n6) 6 y) (le_of_eq linear_count_6)
  rw [hw5, hw6]
  omega

/-- `w3 ≥ 1` when `y t = true` at a type-3 column. -/
lemma linear_w3_pos_of_true {n3 n5 n6 : ℕ} (y : Word (n3 + n5 + n6))
    (t : Fin (n3 + n5 + n6)) (hcol : linearCode n3 n5 n6 t = col3) (ht : y t = true) :
    1 ≤ w_i (linearCode n3 n5 n6) 3 y := by
  rw [w_i_eq_card_onesOn]
  unfold onesOn
  have hmem : t ∈ (fiber (linearCode n3 n5 n6) 3).filter (fun u => y u = true) := by
    simp [fiber, hcol, colVal_col3, ht]
  have hpos : 0 < ((fiber (linearCode n3 n5 n6) 3).filter (fun u => y u = true)).card :=
    Finset.card_pos.mpr ⟨t, hmem⟩
  omega

/-- `w3 < n3` when `y t = false` at a type-3 column. -/
lemma linear_w3_lt_n3_of_false {n3 n5 n6 : ℕ} (y : Word (n3 + n5 + n6))
    (t : Fin (n3 + n5 + n6)) (hcol : linearCode n3 n5 n6 t = col3) (ht : y t = false) :
    w_i (linearCode n3 n5 n6) 3 y < n3 := by
  have hsub : (fiber (linearCode n3 n5 n6) 3).filter (fun u => y u = true) ⊆
      (fiber (linearCode n3 n5 n6) 3).erase t := by
    intro u hu
    have hu1 : u ∈ fiber (linearCode n3 n5 n6) 3 := (Finset.mem_filter.mp hu).1
    have hu2 : y u = true := (Finset.mem_filter.mp hu).2
    have hut : u ≠ t := by
      intro hut
      subst u
      simp [ht] at hu2
    exact Finset.mem_erase.mpr ⟨hut, hu1⟩
  have hcard : w_i (linearCode n3 n5 n6) 3 y ≤
      ((fiber (linearCode n3 n5 n6) 3).erase t).card := by
    rw [w_i_eq_card_onesOn]
    unfold onesOn
    exact Finset.card_le_card hsub
  have hmem : t ∈ fiber (linearCode n3 n5 n6) 3 := by
    simp [fiber, hcol, colVal_col3]
  have hn3pos : 0 < n3 := by
    have hpos : 0 < (fiber (linearCode n3 n5 n6) 3).card :=
      Finset.card_pos.mpr ⟨t, hmem⟩
    rw [fiber_card_eq_count, linear_count_3] at hpos
    exact hpos
  have hcard' : ((fiber (linearCode n3 n5 n6) 3).erase t).card < n3 := by
    rw [Finset.card_erase_of_mem hmem, fiber_card_eq_count, linear_count_3]
    omega
  omega

/-- Flipping a type-3 column with `y t = false` decreases row-3 distance. -/
lemma lin_dRow2_flip_false {n3 n5 n6 : ℕ} (y : Word (n3 + n5 + n6))
    (t : Fin (n3 + n5 + n6)) (hcol : linearCode n3 n5 n6 t = col3) (ht : y t = false) :
    dRow (linearCode n3 n5 n6) ⟨2, by decide⟩ (flipBit t y) + 1 =
      dRow (linearCode n3 n5 n6) ⟨2, by decide⟩ y := by
  rw [linear_dRow2 (flipBit t y), linear_dRow2 y]
  have hw3 := w3_flip_false (C := linearCode n3 n5 n6) t y hcol ht
  have hw5 := w5_flip (C := linearCode n3 n5 n6) t y hcol
  have hw6 := w6_flip (C := linearCode n3 n5 n6) t y hcol
  have hw3lt : w_i (linearCode n3 n5 n6) 3 y < n3 :=
    linear_w3_lt_n3_of_false y t hcol ht
  have hw5le : w_i (linearCode n3 n5 n6) 5 y ≤ n5 :=
    le_trans (w_i_le_count (linearCode n3 n5 n6) 5 y) (le_of_eq linear_count_5)
  have hw6le : w_i (linearCode n3 n5 n6) 6 y ≤ n6 :=
    le_trans (w_i_le_count (linearCode n3 n5 n6) 6 y) (le_of_eq linear_count_6)
  rw [hw5, hw6]
  omega

/-- Flipping a type-3 column with `y t = false` decreases row-4 distance. -/
lemma lin_dRow3_flip_false {n3 n5 n6 : ℕ} (y : Word (n3 + n5 + n6))
    (t : Fin (n3 + n5 + n6)) (hcol : linearCode n3 n5 n6 t = col3) (ht : y t = false) :
    dRow (linearCode n3 n5 n6) ⟨3, by decide⟩ (flipBit t y) + 1 =
      dRow (linearCode n3 n5 n6) ⟨3, by decide⟩ y := by
  rw [linear_dRow3 (flipBit t y), linear_dRow3 y]
  have hw3 := w3_flip_false (C := linearCode n3 n5 n6) t y hcol ht
  have hw5 := w5_flip (C := linearCode n3 n5 n6) t y hcol
  have hw6 := w6_flip (C := linearCode n3 n5 n6) t y hcol
  have hw3lt : w_i (linearCode n3 n5 n6) 3 y < n3 :=
    linear_w3_lt_n3_of_false y t hcol ht
  have hw5le : w_i (linearCode n3 n5 n6) 5 y ≤ n5 :=
    le_trans (w_i_le_count (linearCode n3 n5 n6) 5 y) (le_of_eq linear_count_5)
  have hw6le : w_i (linearCode n3 n5 n6) 6 y ≤ n6 :=
    le_trans (w_i_le_count (linearCode n3 n5 n6) 6 y) (le_of_eq linear_count_6)
  rw [hw5, hw6]
  omega

/-- Y3 for `y t = true`: `d1 = d2 = dCode` and `d3, d4 ≥ d1` (paper eq. cli4). -/
lemma linY3_weights_true {n3 n5 n6 : ℕ} (y : Word (n3 + n5 + n6))
    (t : Fin (n3 + n5 + n6)) (hcol : linearCode n3 n5 n6 t = col3) (ht : y t = true)
    (he0 : dRow (linearCode n3 n5 n6) ⟨0, by decide⟩ y =
      dRow (linearCode n3 n5 n6) ⟨1, by decide⟩ y)
    (he2 : dRow (linearCode n3 n5 n6) ⟨0, by decide⟩ y ≤
      dRow (linearCode n3 n5 n6) ⟨2, by decide⟩ y)
    (he3 : dRow (linearCode n3 n5 n6) ⟨0, by decide⟩ y ≤
      dRow (linearCode n3 n5 n6) ⟨3, by decide⟩ y) :
    linY3 (linearCode n3 n5 n6) t y := by
  unfold linY3 gY3
  have h0 := lin_dRow0_flip_true y t hcol ht
  have h1 := lin_dRow1_flip_true y t hcol ht
  have h2 := lin_dRow2_flip_true y t hcol ht
  have h3 := lin_dRow3_flip_true y t hcol ht
  have h0' : dRow (linearCode n3 n5 n6) ⟨0, by decide⟩ (flipBit t y) =
      dRow (linearCode n3 n5 n6) ⟨0, by decide⟩ y - 1 := by omega
  have h1' : dRow (linearCode n3 n5 n6) ⟨1, by decide⟩ (flipBit t y) =
      dRow (linearCode n3 n5 n6) ⟨1, by decide⟩ y - 1 := by omega
  have h2' : dRow (linearCode n3 n5 n6) ⟨2, by decide⟩ (flipBit t y) =
      dRow (linearCode n3 n5 n6) ⟨2, by decide⟩ y + 1 := h2
  have h3' : dRow (linearCode n3 n5 n6) ⟨3, by decide⟩ (flipBit t y) =
      dRow (linearCode n3 n5 n6) ⟨3, by decide⟩ y + 1 := h3
  have hw3pos : 1 ≤ w_i (linearCode n3 n5 n6) 3 y :=
    linear_w3_pos_of_true y t hcol ht
  have he0pos : 1 ≤ dRow (linearCode n3 n5 n6) ⟨0, by decide⟩ y := by
    rw [linear_dRow0]
    omega
  unfold linP linO
  rw [h1', h2', h0', h3']
  constructor
  · rw [← he0]
    have hle1 : dRow (linearCode n3 n5 n6) ⟨0, by omega⟩ y - 1 ≤
        dRow (linearCode n3 n5 n6) ⟨2, by omega⟩ y + 1 := by omega
    have hle2 : dRow (linearCode n3 n5 n6) ⟨0, by omega⟩ y - 1 ≤
        dRow (linearCode n3 n5 n6) ⟨3, by omega⟩ y + 1 := by omega
    rw [min_eq_left hle1, min_eq_left hle2]
  · constructor
    · rw [← he0]
      have hle1 : dRow (linearCode n3 n5 n6) ⟨0, by omega⟩ y - 1 ≤
        dRow (linearCode n3 n5 n6) ⟨2, by omega⟩ y + 1 := by omega
      have hle2 : dRow (linearCode n3 n5 n6) ⟨0, by omega⟩ y ≤
        dRow (linearCode n3 n5 n6) ⟨2, by omega⟩ y := by omega
      rw [min_eq_left hle1]
      rw [min_eq_left hle2]
      omega
    · rw [← he0]
      have hle1 : dRow (linearCode n3 n5 n6) ⟨0, by omega⟩ y ≤
        dRow (linearCode n3 n5 n6) ⟨2, by omega⟩ y := by omega
      have hle2 : dRow (linearCode n3 n5 n6) ⟨0, by omega⟩ y ≤
        dRow (linearCode n3 n5 n6) ⟨3, by omega⟩ y := by omega
      rw [min_eq_left hle1, min_eq_left hle2]

/-- Y3 for `y t = false`: `d3 = d4 = dCode` and `d1, d2 ≥ d3` (paper eq. cli5). -/
lemma linY3_weights_false {n3 n5 n6 : ℕ} (y : Word (n3 + n5 + n6))
    (t : Fin (n3 + n5 + n6)) (hcol : linearCode n3 n5 n6 t = col3) (ht : y t = false)
    (he2 : dRow (linearCode n3 n5 n6) ⟨2, by decide⟩ y =
      dRow (linearCode n3 n5 n6) ⟨3, by decide⟩ y)
    (he0 : dRow (linearCode n3 n5 n6) ⟨2, by decide⟩ y ≤
      dRow (linearCode n3 n5 n6) ⟨0, by decide⟩ y)
    (he1 : dRow (linearCode n3 n5 n6) ⟨2, by decide⟩ y ≤
      dRow (linearCode n3 n5 n6) ⟨1, by decide⟩ y) :
    linY3 (linearCode n3 n5 n6) t y := by
  unfold linY3 gY3
  have h0 := lin_dRow0_flip_false y t hcol ht
  have h1 := lin_dRow1_flip_false y t hcol ht
  have h2 := lin_dRow2_flip_false y t hcol ht
  have h3 := lin_dRow3_flip_false y t hcol ht
  have h0' : dRow (linearCode n3 n5 n6) ⟨0, by decide⟩ (flipBit t y) =
      dRow (linearCode n3 n5 n6) ⟨0, by decide⟩ y + 1 := h0
  have h1' : dRow (linearCode n3 n5 n6) ⟨1, by decide⟩ (flipBit t y) =
      dRow (linearCode n3 n5 n6) ⟨1, by decide⟩ y + 1 := h1
  have h2' : dRow (linearCode n3 n5 n6) ⟨2, by decide⟩ (flipBit t y) =
      dRow (linearCode n3 n5 n6) ⟨2, by decide⟩ y - 1 := by omega
  have h3' : dRow (linearCode n3 n5 n6) ⟨3, by decide⟩ (flipBit t y) =
      dRow (linearCode n3 n5 n6) ⟨3, by decide⟩ y - 1 := by omega
  have hw3lt : w_i (linearCode n3 n5 n6) 3 y < n3 :=
    linear_w3_lt_n3_of_false y t hcol ht
  have he2pos : 1 ≤ dRow (linearCode n3 n5 n6) ⟨2, by decide⟩ y := by
    rw [linear_dRow2]
    omega
  unfold linP linO
  rw [h1', h2', h0', h3']
  constructor
  · rw [← he2]
    have hle1 : dRow (linearCode n3 n5 n6) ⟨2, by omega⟩ y - 1 ≤
        dRow (linearCode n3 n5 n6) ⟨0, by omega⟩ y + 1 := by omega
    have hle2 : dRow (linearCode n3 n5 n6) ⟨2, by omega⟩ y - 1 ≤
        dRow (linearCode n3 n5 n6) ⟨1, by omega⟩ y + 1 := by omega
    rw [min_eq_right hle1, min_eq_right hle2]
  · constructor
    · have hle1 : dRow (linearCode n3 n5 n6) ⟨2, by omega⟩ y - 1 ≤
        dRow (linearCode n3 n5 n6) ⟨1, by omega⟩ y + 1 := by omega
      have hle2 : dRow (linearCode n3 n5 n6) ⟨2, by omega⟩ y ≤
        dRow (linearCode n3 n5 n6) ⟨1, by omega⟩ y := by omega
      rw [min_eq_right hle1]
      rw [min_eq_right hle2]
      omega
    · rw [← he2]
      have hle1 : dRow (linearCode n3 n5 n6) ⟨2, by omega⟩ y ≤
        dRow (linearCode n3 n5 n6) ⟨0, by omega⟩ y := by omega
      have hle2 : dRow (linearCode n3 n5 n6) ⟨2, by omega⟩ y ≤
        dRow (linearCode n3 n5 n6) ⟨1, by omega⟩ y := by omega
      rw [min_eq_right hle1, min_eq_right hle2]

/-! ## Parity consequences of the zones -/

/-- Y3 with `y t = true`: d1 = d2 and d3, d4 ≥ d1. -/
lemma linY3_true_implies {n3 n5 n6 : ℕ} (y : Word (n3 + n5 + n6))
    (t : Fin (n3 + n5 + n6)) (hcol : linearCode n3 n5 n6 t = col3) (ht : y t = true)
    (hy : linY3 (linearCode n3 n5 n6) t y) :
    dRow (linearCode n3 n5 n6) ⟨0, by decide⟩ y =
        dRow (linearCode n3 n5 n6) ⟨1, by decide⟩ y ∧
      dRow (linearCode n3 n5 n6) ⟨0, by decide⟩ y ≤
        dRow (linearCode n3 n5 n6) ⟨2, by decide⟩ y ∧
      dRow (linearCode n3 n5 n6) ⟨0, by decide⟩ y ≤
        dRow (linearCode n3 n5 n6) ⟨3, by decide⟩ y := by
  let L := linearCode n3 n5 n6
  unfold linY3 gY3 at hy
  rcases hy with ⟨h1, h2, h3⟩
  change linP L (flipBit t y) = linO L (flipBit t y) at h1
  change linP L (flipBit t y) < linP L y at h2
  change linP L y = linO L y at h3
  have h0 := lin_dRow0_flip_true y t hcol ht
  have h1f := lin_dRow1_flip_true y t hcol ht
  have h2f := lin_dRow2_flip_true y t hcol ht
  have h3f := lin_dRow3_flip_true y t hcol ht
  have hw3pos : 1 ≤ w_i (linearCode n3 n5 n6) 3 y :=
    linear_w3_pos_of_true y t hcol ht
  have he1pos : 1 ≤ dRow L ⟨1, by decide⟩ y := by
    rw [linear_dRow1]
    omega
  have hw3pos : 1 ≤ w_i (linearCode n3 n5 n6) 3 y :=
    linear_w3_pos_of_true y t hcol ht
  have he1pos : 1 ≤ dRow L ⟨1, by decide⟩ y := by
    rw [linear_dRow1]
    omega
  have h0' : dRow L ⟨0, by decide⟩ (flipBit t y) = dRow L ⟨0, by decide⟩ y - 1 := by
    change dRow (linearCode n3 n5 n6) ⟨0, by decide⟩ (flipBit t y) =
      dRow (linearCode n3 n5 n6) ⟨0, by decide⟩ y - 1
    omega
  have h1' : dRow L ⟨1, by decide⟩ (flipBit t y) = dRow L ⟨1, by decide⟩ y - 1 := by
    change dRow (linearCode n3 n5 n6) ⟨1, by decide⟩ (flipBit t y) =
      dRow (linearCode n3 n5 n6) ⟨1, by decide⟩ y - 1
    omega
  have h2' : dRow L ⟨2, by decide⟩ (flipBit t y) = dRow L ⟨2, by decide⟩ y + 1 := h2f
  have h3' : dRow L ⟨3, by decide⟩ (flipBit t y) = dRow L ⟨3, by decide⟩ y + 1 := h3f
  have hPp : linP L (flipBit t y) =
      min (dRow L ⟨1, by decide⟩ y - 1) (dRow L ⟨2, by decide⟩ y + 1) := by
    unfold linP
    rw [h1', h2']
  have hOp : linO L (flipBit t y) =
      min (dRow L ⟨0, by decide⟩ y - 1) (dRow L ⟨3, by decide⟩ y + 1) := by
    unfold linO
    rw [h0', h3']
  have hP : linP L y = min (dRow L ⟨1, by decide⟩ y) (dRow L ⟨2, by decide⟩ y) := rfl
  have hO : linO L y = min (dRow L ⟨0, by decide⟩ y) (dRow L ⟨3, by decide⟩ y) := rfl
  have h12 : dRow L ⟨1, by decide⟩ y ≤ dRow L ⟨2, by decide⟩ y := by
    by_contra hn
    have h21 : dRow L ⟨2, by decide⟩ y < dRow L ⟨1, by decide⟩ y := by omega
    have hmin : min (dRow L ⟨1, by decide⟩ y - 1) (dRow L ⟨2, by decide⟩ y + 1) ≥
        dRow L ⟨2, by decide⟩ y := by
      apply le_min
      · omega
      · omega
    have hmin2 : min (dRow L ⟨1, by decide⟩ y) (dRow L ⟨2, by decide⟩ y) =
        dRow L ⟨2, by decide⟩ y := min_eq_right (le_of_lt h21)
    have h2' : min (dRow L ⟨1, by decide⟩ y - 1) (dRow L ⟨2, by decide⟩ y + 1) <
        dRow L ⟨2, by decide⟩ y := by
      rw [hPp, hP] at h2
      rwa [hmin2] at h2
    omega
  have h3' : dRow L ⟨1, by decide⟩ y =
      min (dRow L ⟨0, by decide⟩ y) (dRow L ⟨3, by decide⟩ y) := by
    have hh : min (dRow L ⟨1, by decide⟩ y) (dRow L ⟨2, by decide⟩ y) =
        min (dRow L ⟨0, by decide⟩ y) (dRow L ⟨3, by decide⟩ y) := by
      rw [← hP, ← hO]
      exact h3
    rw [min_eq_left h12] at hh
    exact hh
  have he0ge : dRow L ⟨1, by decide⟩ y ≤ dRow L ⟨0, by decide⟩ y :=
    (le_min_iff.mp (le_of_eq h3')).1
  have he3ge : dRow L ⟨1, by decide⟩ y ≤ dRow L ⟨3, by decide⟩ y :=
    (le_min_iff.mp (le_of_eq h3')).2
  have h1' : dRow L ⟨1, by decide⟩ y - 1 =
      min (dRow L ⟨0, by decide⟩ y - 1) (dRow L ⟨3, by decide⟩ y + 1) := by
    rw [hPp, hOp] at h1
    have hle1 : dRow L ⟨1, by omega⟩ y - 1 ≤
        dRow L ⟨2, by omega⟩ y + 1 := by omega
    rw [min_eq_left hle1] at h1
    exact h1
  have hcase : dRow L ⟨0, by decide⟩ y - 1 = dRow L ⟨1, by decide⟩ y - 1 ∨
      dRow L ⟨3, by decide⟩ y + 1 = dRow L ⟨1, by decide⟩ y - 1 := by
    by_cases hle : dRow L ⟨0, by decide⟩ y - 1 ≤ dRow L ⟨3, by decide⟩ y + 1
    · left
      rw [min_eq_left hle] at h1'
      omega
    · right
      rw [min_eq_right (le_of_not_ge hle)] at h1'
      omega
  have he0e1 : dRow L ⟨0, by decide⟩ y = dRow L ⟨1, by decide⟩ y := by
    rcases hcase with hc | hc
    · omega
    · omega
  constructor
  · exact he0e1
  · constructor
    · rw [he0e1]
      exact h12
    · rw [he0e1]
      exact he3ge

/-- Y3 with `y t = false`: d3 = d4 and d1, d2 ≥ d3. -/
lemma linY3_false_implies {n3 n5 n6 : ℕ} (y : Word (n3 + n5 + n6))
    (t : Fin (n3 + n5 + n6)) (hcol : linearCode n3 n5 n6 t = col3) (ht : y t = false)
    (hy : linY3 (linearCode n3 n5 n6) t y) :
    dRow (linearCode n3 n5 n6) ⟨2, by decide⟩ y =
        dRow (linearCode n3 n5 n6) ⟨3, by decide⟩ y ∧
      dRow (linearCode n3 n5 n6) ⟨2, by decide⟩ y ≤
        dRow (linearCode n3 n5 n6) ⟨0, by decide⟩ y ∧
      dRow (linearCode n3 n5 n6) ⟨2, by decide⟩ y ≤
        dRow (linearCode n3 n5 n6) ⟨1, by decide⟩ y := by
  let L := linearCode n3 n5 n6
  unfold linY3 gY3 at hy
  rcases hy with ⟨h1, h2, h3⟩
  change linP L (flipBit t y) = linO L (flipBit t y) at h1
  change linP L (flipBit t y) < linP L y at h2
  change linP L y = linO L y at h3
  have h0 := lin_dRow0_flip_false y t hcol ht
  have h1f := lin_dRow1_flip_false y t hcol ht
  have h2f := lin_dRow2_flip_false y t hcol ht
  have h3f := lin_dRow3_flip_false y t hcol ht
  have hw3lt : w_i (linearCode n3 n5 n6) 3 y < n3 :=
    linear_w3_lt_n3_of_false y t hcol ht
  have he2pos : 1 ≤ dRow L ⟨2, by decide⟩ y := by
    rw [linear_dRow2]
    omega
  have h0' : dRow L ⟨0, by decide⟩ (flipBit t y) = dRow L ⟨0, by decide⟩ y + 1 := h0
  have h1' : dRow L ⟨1, by decide⟩ (flipBit t y) = dRow L ⟨1, by decide⟩ y + 1 := h1f
  have h2' : dRow L ⟨2, by decide⟩ (flipBit t y) = dRow L ⟨2, by decide⟩ y - 1 := by
    change dRow (linearCode n3 n5 n6) ⟨2, by decide⟩ (flipBit t y) =
      dRow (linearCode n3 n5 n6) ⟨2, by decide⟩ y - 1
    omega
  have h3' : dRow L ⟨3, by decide⟩ (flipBit t y) = dRow L ⟨3, by decide⟩ y - 1 := by
    change dRow (linearCode n3 n5 n6) ⟨3, by decide⟩ (flipBit t y) =
      dRow (linearCode n3 n5 n6) ⟨3, by decide⟩ y - 1
    omega
  have hPp : linP L (flipBit t y) =
      min (dRow L ⟨1, by decide⟩ y + 1) (dRow L ⟨2, by decide⟩ y - 1) := by
    unfold linP
    rw [h1', h2']
  have hOp : linO L (flipBit t y) =
      min (dRow L ⟨0, by decide⟩ y + 1) (dRow L ⟨3, by decide⟩ y - 1) := by
    unfold linO
    rw [h0', h3']
  have hP : linP L y = min (dRow L ⟨1, by decide⟩ y) (dRow L ⟨2, by decide⟩ y) := rfl
  have hO : linO L y = min (dRow L ⟨0, by decide⟩ y) (dRow L ⟨3, by decide⟩ y) := rfl
  have h21 : dRow L ⟨2, by decide⟩ y ≤ dRow L ⟨1, by decide⟩ y := by
    by_contra hn
    have h12 : dRow L ⟨1, by decide⟩ y < dRow L ⟨2, by decide⟩ y := by omega
    have hmin : min (dRow L ⟨1, by decide⟩ y + 1) (dRow L ⟨2, by decide⟩ y - 1) ≥
        dRow L ⟨1, by decide⟩ y := by
      apply le_min
      · omega
      · omega
    have hmin2 : min (dRow L ⟨1, by decide⟩ y) (dRow L ⟨2, by decide⟩ y) =
        dRow L ⟨1, by decide⟩ y := min_eq_left (le_of_lt h12)
    have h2' : min (dRow L ⟨1, by decide⟩ y + 1) (dRow L ⟨2, by decide⟩ y - 1) <
        dRow L ⟨1, by decide⟩ y := by
      rw [hPp, hP] at h2
      rwa [hmin2] at h2
    omega
  have h3' : dRow L ⟨2, by decide⟩ y =
      min (dRow L ⟨0, by decide⟩ y) (dRow L ⟨3, by decide⟩ y) := by
    have hh : min (dRow L ⟨1, by decide⟩ y) (dRow L ⟨2, by decide⟩ y) =
        min (dRow L ⟨0, by decide⟩ y) (dRow L ⟨3, by decide⟩ y) := by
      rw [← hP, ← hO]
      exact h3
    rw [min_eq_right h21] at hh
    exact hh
  have he0ge : dRow L ⟨2, by decide⟩ y ≤ dRow L ⟨0, by decide⟩ y :=
    (le_min_iff.mp (le_of_eq h3')).1
  have he3ge : dRow L ⟨2, by decide⟩ y ≤ dRow L ⟨3, by decide⟩ y :=
    (le_min_iff.mp (le_of_eq h3')).2
  have h1' : dRow L ⟨2, by decide⟩ y - 1 =
      min (dRow L ⟨0, by decide⟩ y + 1) (dRow L ⟨3, by decide⟩ y - 1) := by
    rw [hPp, hOp] at h1
    have hle1 : dRow L ⟨2, by omega⟩ y - 1 ≤
        dRow L ⟨1, by omega⟩ y + 1 := by omega
    rw [min_eq_right hle1] at h1
    exact h1
  have hcase : dRow L ⟨0, by decide⟩ y + 1 = dRow L ⟨2, by decide⟩ y - 1 ∨
      dRow L ⟨3, by decide⟩ y - 1 = dRow L ⟨2, by decide⟩ y - 1 := by
    by_cases hle : dRow L ⟨0, by decide⟩ y + 1 ≤ dRow L ⟨3, by decide⟩ y - 1
    · left
      rw [min_eq_left hle] at h1'
      omega
    · right
      rw [min_eq_right (le_of_not_ge hle)] at h1'
      omega
  have he2e3 : dRow L ⟨2, by decide⟩ y = dRow L ⟨3, by decide⟩ y := by
    rcases hcase with hc | hc
    · omega
    · omega
  constructor
  · exact he2e3
  · constructor
    · exact he0ge
    · exact h21

/-- The weight form of Y3 for `y t = true` (paper eq. cli7, integer form). -/
lemma linY3_true_weights {n3 n5 n6 : ℕ} (y : Word (n3 + n5 + n6))
    (t : Fin (n3 + n5 + n6)) (hcol : linearCode n3 n5 n6 t = col3) (ht : y t = true)
    (_hpar : Even (n5 + n6))
    (hy : linY3 (linearCode n3 n5 n6) t y)
    (hd : dCode (linearCode n3 n5 n6) y = d) :
    w_i (linearCode n3 n5 n6) 3 y = d - (n5 + n6) / 2 ∧
      w_i (linearCode n3 n5 n6) 6 y = (n5 + n6) / 2 - w_i (linearCode n3 n5 n6) 5 y ∧
        2 * w_i (linearCode n3 n5 n6) 5 y ≥ 2 * d - n3 - n6 ∧
        2 * w_i (linearCode n3 n5 n6) 5 y ≤ n3 + 2 * n5 + n6 - 2 * d := by
  let w3 := w_i (linearCode n3 n5 n6) 3 y
  let w5 := w_i (linearCode n3 n5 n6) 5 y
  let w6 := w_i (linearCode n3 n5 n6) 6 y
  have hY := linY3_true_implies y t hcol ht hy
  have hw5le : w5 ≤ n5 := by
    simpa [w5, linear_count_5] using (w_i_le_count (linearCode n3 n5 n6) 5 y)
  have hw6le : w6 ≤ n6 := by
    simpa [w6, linear_count_6] using (w_i_le_count (linearCode n3 n5 n6) 6 y)
  have hw3le : w3 ≤ n3 := by
    simpa [w3, linear_count_3] using (w_i_le_count (linearCode n3 n5 n6) 3 y)
  have hdRow0 : dRow (linearCode n3 n5 n6) ⟨0, by decide⟩ y = w3 + w5 + w6 := by
    simpa [w3, w5, w6] using linear_dRow0 y
  have hdRow1 : dRow (linearCode n3 n5 n6) ⟨1, by decide⟩ y = w3 + (n5 - w5) + (n6 - w6) := by
    simpa [w3, w5, w6] using linear_dRow1 y
  have hdRow2 : dRow (linearCode n3 n5 n6) ⟨2, by decide⟩ y = (n3 - w3) + w5 + (n6 - w6) := by
    simpa [w3, w5, w6] using linear_dRow2 y
  have hdRow3 : dRow (linearCode n3 n5 n6) ⟨3, by decide⟩ y = (n3 - w3) + (n5 - w5) + w6 := by
    simpa [w3, w5, w6] using linear_dRow3 y
  have hdCode : dRow (linearCode n3 n5 n6) ⟨0, by decide⟩ y = d := by
    have hle : dRow (linearCode n3 n5 n6) ⟨0, by decide⟩ y ≤
        min (dRow (linearCode n3 n5 n6) ⟨1, by decide⟩ y)
          (min (dRow (linearCode n3 n5 n6) ⟨2, by decide⟩ y) (dRow (linearCode n3 n5 n6) ⟨3, by decide⟩ y)) := by
      apply le_min
      · exact le_of_eq hY.1
      · apply le_min
        · exact hY.2.1
        · exact hY.2.2
    have hmin : min (dRow (linearCode n3 n5 n6) ⟨0, by decide⟩ y)
        (min (dRow (linearCode n3 n5 n6) ⟨1, by decide⟩ y)
          (min (dRow (linearCode n3 n5 n6) ⟨2, by decide⟩ y) (dRow (linearCode n3 n5 n6) ⟨3, by decide⟩ y))) =
        dRow (linearCode n3 n5 n6) ⟨0, by decide⟩ y := by
      rw [min_eq_left hle]
    have hdC : dCode (linearCode n3 n5 n6) y = dRow (linearCode n3 n5 n6) ⟨0, by decide⟩ y := by
      change min (dRow (linearCode n3 n5 n6) ⟨0, by decide⟩ y)
          (min (dRow (linearCode n3 n5 n6) ⟨1, by decide⟩ y)
            (min (dRow (linearCode n3 n5 n6) ⟨2, by decide⟩ y) (dRow (linearCode n3 n5 n6) ⟨3, by decide⟩ y))) =
          dRow (linearCode n3 n5 n6) ⟨0, by decide⟩ y
      exact hmin
    rwa [hdC] at hd
  have hsum : w5 + w6 = (n5 + n6) / 2 := by
    have hw : w3 + w5 + w6 = w3 + (n5 - w5) + (n6 - w6) := by
      calc
        w3 + w5 + w6 = dRow (linearCode n3 n5 n6) ⟨0, by decide⟩ y := hdRow0.symm
        _ = dRow (linearCode n3 n5 n6) ⟨1, by decide⟩ y := hY.1
        _ = w3 + (n5 - w5) + (n6 - w6) := hdRow1
    have h2 : 2 * (w5 + w6) = n5 + n6 := by omega
    have h2' : (n5 + n6) / 2 = w5 + w6 := by
      rw [← h2, Nat.mul_div_right (w5 + w6) (by decide : 0 < 2)]
    exact h2'.symm
  have hw3 : w3 = d - (n5 + n6) / 2 := by
    have : w3 + (w5 + w6) = d := by
      calc
        w3 + (w5 + w6) = w3 + w5 + w6 := by omega
        _ = dRow (linearCode n3 n5 n6) ⟨0, by decide⟩ y := hdRow0.symm
        _ = d := hdCode
    omega
  have hw6 : w6 = (n5 + n6) / 2 - w5 := by
    have : w5 + w6 = (n5 + n6) / 2 := hsum
    omega
  have hge2' : 2 * w5 ≥ 2 * d - n3 - n6 := by
    have h3ge : (n3 - w3) + w5 + (n6 - w6) ≥ d := by
      calc
        (n3 - w3) + w5 + (n6 - w6) = dRow (linearCode n3 n5 n6) ⟨2, by decide⟩ y := hdRow2.symm
        _ ≥ dRow (linearCode n3 n5 n6) ⟨0, by decide⟩ y := hY.2.1
        _ = d := hdCode
    omega
  have hge3' : 2 * w5 ≤ n3 + 2 * n5 + n6 - 2 * d := by
    have h4ge : (n3 - w3) + (n5 - w5) + w6 ≥ d := by
      calc
        (n3 - w3) + (n5 - w5) + w6 = dRow (linearCode n3 n5 n6) ⟨3, by decide⟩ y := hdRow3.symm
        _ ≥ dRow (linearCode n3 n5 n6) ⟨0, by decide⟩ y := hY.2.2
        _ = d := hdCode
    omega
  constructor
  · exact hw3
  · constructor
    · exact hw6
    · constructor
      · simpa [w3, w5, w6] using hge2'
      · simpa [w3, w5, w6] using hge3'

/-- Y5 with `y t = true`: d2 = d4 + 1. -/
lemma linY5_true_implies {n3 n5 n6 : ℕ} (y : Word (n3 + n5 + n6))
    (t : Fin (n3 + n5 + n6)) (hcol : linearCode n3 n5 n6 t = col3) (ht : y t = true)
    (hy : linY5 (linearCode n3 n5 n6) t y) :
    dRow (linearCode n3 n5 n6) ⟨1, by decide⟩ y =
      dRow (linearCode n3 n5 n6) ⟨3, by decide⟩ y + 1 := by
  let L := linearCode n3 n5 n6
  unfold linY5 gY5 at hy
  rcases hy with ⟨h1, h2, h3⟩
  change linP L (flipBit t y) = linO L y at h1
  change linO L (flipBit t y) = linP L y at h2
  change linO L y < linO L (flipBit t y) at h3
  have h0 := lin_dRow0_flip_true y t hcol ht
  have h1f := lin_dRow1_flip_true y t hcol ht
  have h2f := lin_dRow2_flip_true y t hcol ht
  have h3f := lin_dRow3_flip_true y t hcol ht
  have h0' : dRow L ⟨0, by decide⟩ (flipBit t y) = dRow L ⟨0, by decide⟩ y - 1 := by
    change dRow (linearCode n3 n5 n6) ⟨0, by decide⟩ (flipBit t y) =
      dRow (linearCode n3 n5 n6) ⟨0, by decide⟩ y - 1
    omega
  have h1' : dRow L ⟨1, by decide⟩ (flipBit t y) = dRow L ⟨1, by decide⟩ y - 1 := by
    change dRow (linearCode n3 n5 n6) ⟨1, by decide⟩ (flipBit t y) =
      dRow (linearCode n3 n5 n6) ⟨1, by decide⟩ y - 1
    omega
  have h2' : dRow L ⟨2, by decide⟩ (flipBit t y) = dRow L ⟨2, by decide⟩ y + 1 := h2f
  have h3' : dRow L ⟨3, by decide⟩ (flipBit t y) = dRow L ⟨3, by decide⟩ y + 1 := h3f
  have hPp : linP L (flipBit t y) =
      min (dRow L ⟨1, by decide⟩ y - 1) (dRow L ⟨2, by decide⟩ y + 1) := by
    unfold linP
    rw [h1', h2']
  have hOp : linO L (flipBit t y) =
      min (dRow L ⟨0, by decide⟩ y - 1) (dRow L ⟨3, by decide⟩ y + 1) := by
    unfold linO
    rw [h0', h3']
  have hP : linP L y = min (dRow L ⟨1, by decide⟩ y) (dRow L ⟨2, by decide⟩ y) := rfl
  have hO : linO L y = min (dRow L ⟨0, by decide⟩ y) (dRow L ⟨3, by decide⟩ y) := rfl
  have he0gt : dRow L ⟨3, by decide⟩ y < dRow L ⟨0, by decide⟩ y := by
    by_contra hn
    have hle : dRow L ⟨0, by decide⟩ y ≤ dRow L ⟨3, by decide⟩ y := by omega
    have hm1 : min (dRow L ⟨0, by decide⟩ y) (dRow L ⟨3, by decide⟩ y) =
        dRow L ⟨0, by decide⟩ y := min_eq_left hle
    have hm2 : min (dRow L ⟨0, by decide⟩ y - 1) (dRow L ⟨3, by decide⟩ y + 1) ≤
        dRow L ⟨0, by decide⟩ y - 1 := Nat.min_le_left _ _
    rw [hO, hOp] at h3
    rw [hm1] at h3
    omega
  have hmin3 : min (dRow L ⟨0, by decide⟩ y - 1) (dRow L ⟨3, by decide⟩ y + 1) =
      dRow L ⟨3, by decide⟩ y + 1 := by
    have hle1 : dRow L ⟨3, by omega⟩ y + 1 ≤
        dRow L ⟨0, by omega⟩ y - 1 := by omega
    rw [min_eq_right hle1]
  have h2' : dRow L ⟨3, by decide⟩ y + 1 =
      min (dRow L ⟨1, by decide⟩ y) (dRow L ⟨2, by decide⟩ y) := by
    rw [hOp, hP] at h2
    rwa [hmin3] at h2
  have he1ge : dRow L ⟨3, by decide⟩ y + 1 ≤ dRow L ⟨1, by decide⟩ y :=
    (le_min_iff.mp (le_of_eq h2')).1
  have he2ge : dRow L ⟨3, by decide⟩ y + 1 ≤ dRow L ⟨2, by decide⟩ y :=
    (le_min_iff.mp (le_of_eq h2')).2
  have hminO : min (dRow L ⟨0, by decide⟩ y) (dRow L ⟨3, by decide⟩ y) =
      dRow L ⟨3, by decide⟩ y := min_eq_right (le_of_lt he0gt)
  have h1' : min (dRow L ⟨1, by decide⟩ y - 1) (dRow L ⟨2, by decide⟩ y + 1) =
      dRow L ⟨3, by decide⟩ y := by
    rw [hPp, hO] at h1
    rwa [hminO] at h1
  have hcase : dRow L ⟨1, by decide⟩ y - 1 = dRow L ⟨3, by decide⟩ y ∨
      dRow L ⟨2, by decide⟩ y + 1 = dRow L ⟨3, by decide⟩ y := by
    by_cases hle : dRow L ⟨1, by decide⟩ y - 1 ≤ dRow L ⟨2, by decide⟩ y + 1
    · left
      rw [min_eq_left hle] at h1'
      omega
    · right
      rw [min_eq_right (le_of_not_ge hle)] at h1'
      omega
  change dRow L ⟨1, by decide⟩ y = dRow L ⟨3, by decide⟩ y + 1
  rcases hcase with hc | hc
  · omega
  · omega

/-- Y5 with `y t = false`: d1 + 1 = d3 (i.e. d_O + 1 = d_P-row). -/
lemma linY5_false_implies {n3 n5 n6 : ℕ} (y : Word (n3 + n5 + n6))
    (t : Fin (n3 + n5 + n6)) (hcol : linearCode n3 n5 n6 t = col3) (ht : y t = false)
    (hy : linY5 (linearCode n3 n5 n6) t y) :
    dRow (linearCode n3 n5 n6) ⟨0, by decide⟩ y + 1 =
        dRow (linearCode n3 n5 n6) ⟨2, by decide⟩ y := by
  let L := linearCode n3 n5 n6
  unfold linY5 gY5 at hy
  rcases hy with ⟨h1, h2, h3⟩
  change linP L (flipBit t y) = linO L y at h1
  change linO L (flipBit t y) = linP L y at h2
  change linO L y < linO L (flipBit t y) at h3
  have h0 := lin_dRow0_flip_false y t hcol ht
  have h1f := lin_dRow1_flip_false y t hcol ht
  have h2f := lin_dRow2_flip_false y t hcol ht
  have h3f := lin_dRow3_flip_false y t hcol ht
  have h0' : dRow L ⟨0, by decide⟩ (flipBit t y) = dRow L ⟨0, by decide⟩ y + 1 := h0
  have h1' : dRow L ⟨1, by decide⟩ (flipBit t y) = dRow L ⟨1, by decide⟩ y + 1 := h1f
  have h2' : dRow L ⟨2, by decide⟩ (flipBit t y) = dRow L ⟨2, by decide⟩ y - 1 := by
    change dRow (linearCode n3 n5 n6) ⟨2, by decide⟩ (flipBit t y) =
      dRow (linearCode n3 n5 n6) ⟨2, by decide⟩ y - 1
    omega
  have h3' : dRow L ⟨3, by decide⟩ (flipBit t y) = dRow L ⟨3, by decide⟩ y - 1 := by
    change dRow (linearCode n3 n5 n6) ⟨3, by decide⟩ (flipBit t y) =
      dRow (linearCode n3 n5 n6) ⟨3, by decide⟩ y - 1
    omega
  have hPp : linP L (flipBit t y) =
      min (dRow L ⟨1, by decide⟩ y + 1) (dRow L ⟨2, by decide⟩ y - 1) := by
    unfold linP
    rw [h1', h2']
  have hOp : linO L (flipBit t y) =
      min (dRow L ⟨0, by decide⟩ y + 1) (dRow L ⟨3, by decide⟩ y - 1) := by
    unfold linO
    rw [h0', h3']
  have hP : linP L y = min (dRow L ⟨1, by decide⟩ y) (dRow L ⟨2, by decide⟩ y) := rfl
  have hO : linO L y = min (dRow L ⟨0, by decide⟩ y) (dRow L ⟨3, by decide⟩ y) := rfl
  have he0le : dRow L ⟨0, by decide⟩ y ≤ dRow L ⟨3, by decide⟩ y := by
    by_contra hn
    have h30 : dRow L ⟨3, by decide⟩ y < dRow L ⟨0, by decide⟩ y := by omega
    have hm1 : min (dRow L ⟨0, by decide⟩ y) (dRow L ⟨3, by decide⟩ y) =
        dRow L ⟨3, by decide⟩ y := min_eq_right (le_of_lt h30)
    have hm2 : dRow L ⟨0, by decide⟩ y ≤
        min (dRow L ⟨0, by decide⟩ y + 1) (dRow L ⟨3, by decide⟩ y - 1) := by
      apply le_min
      · omega
      · omega
    rw [hO, hOp] at h3
    rw [hm1] at h3
    omega
  have hmin3 : min (dRow L ⟨0, by decide⟩ y + 1) (dRow L ⟨3, by decide⟩ y - 1) =
      dRow L ⟨0, by decide⟩ y + 1 := by
    have hle1 : dRow L ⟨0, by omega⟩ y + 1 ≤
        dRow L ⟨3, by omega⟩ y - 1 := by omega
    rw [min_eq_left hle1]
  have h2' : dRow L ⟨0, by decide⟩ y + 1 =
      min (dRow L ⟨1, by decide⟩ y) (dRow L ⟨2, by decide⟩ y) := by
    rw [hOp, hP] at h2
    rwa [hmin3] at h2
  have he1ge : dRow L ⟨0, by decide⟩ y + 1 ≤ dRow L ⟨1, by decide⟩ y :=
    (le_min_iff.mp (le_of_eq h2')).1
  have he2ge : dRow L ⟨0, by decide⟩ y + 1 ≤ dRow L ⟨2, by decide⟩ y :=
    (le_min_iff.mp (le_of_eq h2')).2
  have hminO : min (dRow L ⟨0, by decide⟩ y) (dRow L ⟨3, by decide⟩ y) =
      dRow L ⟨0, by decide⟩ y := min_eq_left he0le
  have h1' : min (dRow L ⟨1, by decide⟩ y + 1) (dRow L ⟨2, by decide⟩ y - 1) =
      dRow L ⟨0, by decide⟩ y := by
    rw [hPp, hO] at h1
    rwa [hminO] at h1
  have hcase : dRow L ⟨1, by decide⟩ y + 1 = dRow L ⟨0, by decide⟩ y ∨
      dRow L ⟨2, by decide⟩ y - 1 = dRow L ⟨0, by decide⟩ y := by
    by_cases hle : dRow L ⟨1, by decide⟩ y + 1 ≤ dRow L ⟨2, by decide⟩ y - 1
    · left
      rw [min_eq_left hle] at h1'
      omega
    · right
      rw [min_eq_right (le_of_not_ge hle)] at h1'
      omega
  change dRow L ⟨0, by decide⟩ y + 1 = dRow L ⟨2, by decide⟩ y
  rcases hcase with hc | hc
  · omega
  · omega

/-- The full distance relations for Y5 with `y t = false` (eq. cli6):
`d1 + 1 = d3` and `d1 + 1 ≤ d2`, `d1 + 2 ≤ d4` (row labels 0..3). -/
lemma linY5_false_relations {n3 n5 n6 : ℕ} (y : Word (n3 + n5 + n6))
    (t : Fin (n3 + n5 + n6)) (hcol : linearCode n3 n5 n6 t = col3) (ht : y t = false)
    (hy : linY5 (linearCode n3 n5 n6) t y) :
    dRow (linearCode n3 n5 n6) ⟨0, by decide⟩ y + 1 =
        dRow (linearCode n3 n5 n6) ⟨2, by decide⟩ y ∧
      dRow (linearCode n3 n5 n6) ⟨0, by decide⟩ y + 1 ≤
        dRow (linearCode n3 n5 n6) ⟨1, by decide⟩ y ∧
      dRow (linearCode n3 n5 n6) ⟨0, by decide⟩ y + 2 ≤
        dRow (linearCode n3 n5 n6) ⟨3, by decide⟩ y := by
  let L := linearCode n3 n5 n6
  unfold linY5 gY5 at hy
  rcases hy with ⟨h1, h2, h3⟩
  change linP L (flipBit t y) = linO L y at h1
  change linO L (flipBit t y) = linP L y at h2
  change linO L y < linO L (flipBit t y) at h3
  have h0 := lin_dRow0_flip_false y t hcol ht
  have h1f := lin_dRow1_flip_false y t hcol ht
  have h2f := lin_dRow2_flip_false y t hcol ht
  have h3f := lin_dRow3_flip_false y t hcol ht
  have h0' : dRow L ⟨0, by decide⟩ (flipBit t y) = dRow L ⟨0, by decide⟩ y + 1 := h0
  have h1' : dRow L ⟨1, by decide⟩ (flipBit t y) = dRow L ⟨1, by decide⟩ y + 1 := h1f
  have h2' : dRow L ⟨2, by decide⟩ (flipBit t y) = dRow L ⟨2, by decide⟩ y - 1 := by
    change dRow (linearCode n3 n5 n6) ⟨2, by decide⟩ (flipBit t y) =
      dRow (linearCode n3 n5 n6) ⟨2, by decide⟩ y - 1
    omega
  have h3' : dRow L ⟨3, by decide⟩ (flipBit t y) = dRow L ⟨3, by decide⟩ y - 1 := by
    change dRow (linearCode n3 n5 n6) ⟨3, by decide⟩ (flipBit t y) =
      dRow (linearCode n3 n5 n6) ⟨3, by decide⟩ y - 1
    omega
  have hPp : linP L (flipBit t y) =
      min (dRow L ⟨1, by decide⟩ y + 1) (dRow L ⟨2, by decide⟩ y - 1) := by
    unfold linP
    rw [h1', h2']
  have hOp : linO L (flipBit t y) =
      min (dRow L ⟨0, by decide⟩ y + 1) (dRow L ⟨3, by decide⟩ y - 1) := by
    unfold linO
    rw [h0', h3']
  have hP : linP L y = min (dRow L ⟨1, by decide⟩ y) (dRow L ⟨2, by decide⟩ y) := rfl
  have hO : linO L y = min (dRow L ⟨0, by decide⟩ y) (dRow L ⟨3, by decide⟩ y) := rfl
  have he0le : dRow L ⟨0, by decide⟩ y ≤ dRow L ⟨3, by decide⟩ y := by
    by_contra hn
    have h30 : dRow L ⟨3, by decide⟩ y < dRow L ⟨0, by decide⟩ y := by omega
    have hm1 : min (dRow L ⟨0, by decide⟩ y) (dRow L ⟨3, by decide⟩ y) =
        dRow L ⟨3, by decide⟩ y := min_eq_right (le_of_lt h30)
    have hm2 : dRow L ⟨0, by decide⟩ y ≤
        min (dRow L ⟨0, by decide⟩ y + 1) (dRow L ⟨3, by decide⟩ y - 1) := by
      apply le_min
      · omega
      · omega
    rw [hO, hOp] at h3
    rw [hm1] at h3
    omega
  have h3lt : dRow L ⟨0, by decide⟩ y < dRow L ⟨3, by decide⟩ y - 1 := by
    have h3v : linO L y < linO L (flipBit t y) := h3
    rw [hO, hOp] at h3v
    have hle3 : min (dRow L ⟨0, by decide⟩ y + 1) (dRow L ⟨3, by decide⟩ y - 1) ≤
        dRow L ⟨3, by decide⟩ y - 1 := Nat.min_le_right _ _
    have hminO' : min (dRow L ⟨0, by decide⟩ y) (dRow L ⟨3, by decide⟩ y) =
        dRow L ⟨0, by decide⟩ y := min_eq_left he0le
    rw [hminO'] at h3v
    exact lt_of_lt_of_le h3v hle3
  have h3lt' : dRow L ⟨0, by decide⟩ y + 1 < dRow L ⟨3, by decide⟩ y := by
    have hle : dRow L ⟨0, by decide⟩ y + 1 ≤ dRow L ⟨3, by decide⟩ y - 1 :=
      Nat.succ_le_of_lt h3lt
    have hbpos3 : 0 < dRow L ⟨3, by decide⟩ y := by
      by_contra hb
      have hb0 : dRow L ⟨3, by decide⟩ y = 0 := by omega
      have hle0 : dRow L ⟨0, by decide⟩ y + 1 ≤ (0 : ℕ) := by
        rw [hb0] at hle
        omega
      omega
    exact lt_of_le_of_lt hle (Nat.sub_lt hbpos3 (by decide : 0 < 1))
  have he3ge : dRow L ⟨0, by decide⟩ y + 1 ≤ dRow L ⟨3, by decide⟩ y - 1 :=
    Nat.succ_le_of_lt h3lt
  have hmin3 : min (dRow L ⟨0, by decide⟩ y + 1) (dRow L ⟨3, by decide⟩ y - 1) =
      dRow L ⟨0, by decide⟩ y + 1 := by
    rw [min_eq_left he3ge]
  have h2' : dRow L ⟨0, by decide⟩ y + 1 =
      min (dRow L ⟨1, by decide⟩ y) (dRow L ⟨2, by decide⟩ y) := by
    rw [hOp, hP] at h2
    rwa [hmin3] at h2
  have he1ge : dRow L ⟨0, by decide⟩ y + 1 ≤ dRow L ⟨1, by decide⟩ y :=
    (le_min_iff.mp (le_of_eq h2')).1
  have he2ge : dRow L ⟨0, by decide⟩ y + 1 ≤ dRow L ⟨2, by decide⟩ y :=
    (le_min_iff.mp (le_of_eq h2')).2
  have hminO : min (dRow L ⟨0, by decide⟩ y) (dRow L ⟨3, by decide⟩ y) =
      dRow L ⟨0, by decide⟩ y := min_eq_left he0le
  have h1' : min (dRow L ⟨1, by decide⟩ y + 1) (dRow L ⟨2, by decide⟩ y - 1) =
      dRow L ⟨0, by decide⟩ y := by
    rw [hPp, hO] at h1
    rwa [hminO] at h1
  have hcase : dRow L ⟨1, by decide⟩ y + 1 = dRow L ⟨0, by decide⟩ y ∨
      dRow L ⟨2, by decide⟩ y - 1 = dRow L ⟨0, by decide⟩ y := by
    by_cases hle : dRow L ⟨1, by decide⟩ y + 1 ≤ dRow L ⟨2, by decide⟩ y - 1
    · left
      rw [min_eq_left hle] at h1'
      omega
    · right
      rw [min_eq_right (le_of_not_ge hle)] at h1'
      omega
  constructor
  · change dRow L ⟨0, by decide⟩ y + 1 = dRow L ⟨2, by decide⟩ y
    rcases hcase with hc | hc
    · omega
    · omega
  · constructor
    · exact he1ge
    · exact Nat.succ_le_of_lt h3lt'

/-- Y5 for `y t = false`: `d1 + 1 = d3` and `d1 + 1 ≤ d2`, `d1 + 2 ≤ d4`
(row labels 0..3) force `linY5` (the reverse of `linY5_false_relations`). -/
lemma linY5_weights_false {n3 n5 n6 : ℕ} (y : Word (n3 + n5 + n6))
    (t : Fin (n3 + n5 + n6)) (hcol : linearCode n3 n5 n6 t = col3) (ht : y t = false)
    (he0 : dRow (linearCode n3 n5 n6) ⟨0, by decide⟩ y + 1 =
      dRow (linearCode n3 n5 n6) ⟨2, by decide⟩ y)
    (he1 : dRow (linearCode n3 n5 n6) ⟨0, by decide⟩ y + 1 ≤
      dRow (linearCode n3 n5 n6) ⟨1, by decide⟩ y)
    (he3 : dRow (linearCode n3 n5 n6) ⟨0, by decide⟩ y + 2 ≤
      dRow (linearCode n3 n5 n6) ⟨3, by decide⟩ y) :
    linY5 (linearCode n3 n5 n6) t y := by
  unfold linY5 gY5
  have h0 := lin_dRow0_flip_false y t hcol ht
  have h1 := lin_dRow1_flip_false y t hcol ht
  have h2 := lin_dRow2_flip_false y t hcol ht
  have h3 := lin_dRow3_flip_false y t hcol ht
  have h0' : dRow (linearCode n3 n5 n6) ⟨0, by decide⟩ (flipBit t y) =
      dRow (linearCode n3 n5 n6) ⟨0, by decide⟩ y + 1 := h0
  have h1' : dRow (linearCode n3 n5 n6) ⟨1, by decide⟩ (flipBit t y) =
      dRow (linearCode n3 n5 n6) ⟨1, by decide⟩ y + 1 := h1
  have h2' : dRow (linearCode n3 n5 n6) ⟨2, by decide⟩ (flipBit t y) =
      dRow (linearCode n3 n5 n6) ⟨2, by decide⟩ y - 1 := by omega
  have h3' : dRow (linearCode n3 n5 n6) ⟨3, by decide⟩ (flipBit t y) =
      dRow (linearCode n3 n5 n6) ⟨3, by decide⟩ y - 1 := by omega
  unfold linP linO
  rw [h1', h2', h0', h3']
  constructor
  · have hminP : min (dRow (linearCode n3 n5 n6) ⟨1, by decide⟩ y + 1)
        (dRow (linearCode n3 n5 n6) ⟨2, by decide⟩ y - 1) =
        dRow (linearCode n3 n5 n6) ⟨0, by decide⟩ y := by
      have hsub : dRow (linearCode n3 n5 n6) ⟨2, by decide⟩ y - 1 =
          dRow (linearCode n3 n5 n6) ⟨0, by decide⟩ y := by omega
      have hge : dRow (linearCode n3 n5 n6) ⟨0, by decide⟩ y ≤
          dRow (linearCode n3 n5 n6) ⟨1, by decide⟩ y + 1 := by omega
      rw [hsub, min_eq_right hge]
    have hminO : min (dRow (linearCode n3 n5 n6) ⟨0, by decide⟩ y)
        (dRow (linearCode n3 n5 n6) ⟨3, by decide⟩ y) =
        dRow (linearCode n3 n5 n6) ⟨0, by decide⟩ y := by
      have hle1 : dRow (linearCode n3 n5 n6) ⟨0, by omega⟩ y ≤
        dRow (linearCode n3 n5 n6) ⟨3, by omega⟩ y := by omega
      rw [min_eq_left hle1]
    rw [hminP, hminO]
  · constructor
    · have hminO' : min (dRow (linearCode n3 n5 n6) ⟨0, by decide⟩ y + 1)
          (dRow (linearCode n3 n5 n6) ⟨3, by decide⟩ y - 1) =
          dRow (linearCode n3 n5 n6) ⟨0, by decide⟩ y + 1 := by
        have hle : dRow (linearCode n3 n5 n6) ⟨0, by decide⟩ y + 1 ≤
            dRow (linearCode n3 n5 n6) ⟨3, by decide⟩ y - 1 := by omega
        rw [min_eq_left hle]
      have hminP : min (dRow (linearCode n3 n5 n6) ⟨1, by decide⟩ y)
          (dRow (linearCode n3 n5 n6) ⟨2, by decide⟩ y) =
          dRow (linearCode n3 n5 n6) ⟨0, by decide⟩ y + 1 := by
        have hle2 : dRow (linearCode n3 n5 n6) ⟨2, by decide⟩ y =
            dRow (linearCode n3 n5 n6) ⟨0, by decide⟩ y + 1 := he0.symm
        rw [hle2, min_eq_right he1]
      rw [hminO', hminP]
    · have hminO : min (dRow (linearCode n3 n5 n6) ⟨0, by decide⟩ y)
          (dRow (linearCode n3 n5 n6) ⟨3, by decide⟩ y) =
          dRow (linearCode n3 n5 n6) ⟨0, by decide⟩ y := by
        have hle1 : dRow (linearCode n3 n5 n6) ⟨0, by omega⟩ y ≤
          dRow (linearCode n3 n5 n6) ⟨3, by omega⟩ y := by omega
        rw [min_eq_left hle1]
      have hminO' : min (dRow (linearCode n3 n5 n6) ⟨0, by decide⟩ y + 1)
          (dRow (linearCode n3 n5 n6) ⟨3, by decide⟩ y - 1) =
          dRow (linearCode n3 n5 n6) ⟨0, by decide⟩ y + 1 := by
        have hle : dRow (linearCode n3 n5 n6) ⟨0, by decide⟩ y + 1 ≤
            dRow (linearCode n3 n5 n6) ⟨3, by decide⟩ y - 1 := by omega
        rw [min_eq_left hle]
      rw [hminO, hminO']
      omega

/-- If `a` and `b` are even and `a + b ≥ 2q + 1`, then `a + b ≥ 2q + 2`. -/
lemma even_add_ge_odd_add_two {a b q : ℕ} (hparA : Even a) (hparB : Even b)
    (hge : a + b ≥ 2 * q + 1) :
    a + b ≥ 2 * q + 2 := by
  by_cases h : a + b = 2 * q + 1
  · have hodd : Odd (a + b) := by rw [h]; exact ⟨q, by omega⟩
    have heven : Even (a + b) := by
      rcases hparA with ⟨r, hr⟩
      rcases hparB with ⟨s, hs⟩
      refine ⟨r + s, ?_⟩
      rw [hr, hs]
      omega
    exact False.elim ((Nat.not_even_iff_odd.mpr hodd) heven)
  · omega

/-- The weight form of Y5 with `y t = false` (eq. cli6, only-if direction):
`w5 = d − m`, `w6 = m − w3`, and the two range bounds on `w3`, where
`m = (n3+n6−1)/2` (here `hm : n3 + n6 = 2*m + 1`). -/
lemma linY5_false_weights {n3 n5 n6 d m : ℕ} (y : Word (n3 + n5 + n6))
    (t : Fin (n3 + n5 + n6)) (hcol : linearCode n3 n5 n6 t = col3) (ht : y t = false)
    (hpar : Even (n5 + n6)) (hm : n3 + n6 = 2 * m + 1)
    (hy : linY5 (linearCode n3 n5 n6) t y)
    (hd : dCode (linearCode n3 n5 n6) y = d) :
    w_i (linearCode n3 n5 n6) 5 y = d - m ∧
      w_i (linearCode n3 n5 n6) 6 y = m - w_i (linearCode n3 n5 n6) 3 y ∧
        2 * w_i (linearCode n3 n5 n6) 3 y + (n5 + n6) ≥ 2 * d + 2 ∧
        2 * w_i (linearCode n3 n5 n6) 3 y + 2 * d ≤ n3 + n5 + 2 * m - 2 := by
  let w3 := w_i (linearCode n3 n5 n6) 3 y
  let w5 := w_i (linearCode n3 n5 n6) 5 y
  let w6 := w_i (linearCode n3 n5 n6) 6 y
  have hrel := linY5_false_relations y t hcol ht hy
  rcases hrel with ⟨hdRow2, hdRow1, hdRow3⟩
  have hw5le : w5 ≤ n5 := by
    simpa [w5, linear_count_5] using (w_i_le_count (linearCode n3 n5 n6) 5 y)
  have hw6le : w6 ≤ n6 := by
    simpa [w6, linear_count_6] using (w_i_le_count (linearCode n3 n5 n6) 6 y)
  have hw3le : w3 ≤ n3 := by
    simpa [w3, linear_count_3] using (w_i_le_count (linearCode n3 n5 n6) 3 y)
  have hdRow0 : dRow (linearCode n3 n5 n6) ⟨0, by decide⟩ y = w3 + w5 + w6 := by
    simpa [w3, w5, w6] using linear_dRow0 y
  have hdRow1' : dRow (linearCode n3 n5 n6) ⟨1, by decide⟩ y = w3 + (n5 - w5) + (n6 - w6) := by
    simpa [w3, w5, w6] using linear_dRow1 y
  have hdRow2' : dRow (linearCode n3 n5 n6) ⟨2, by decide⟩ y = (n3 - w3) + w5 + (n6 - w6) := by
    simpa [w3, w5, w6] using linear_dRow2 y
  have hdRow3' : dRow (linearCode n3 n5 n6) ⟨3, by decide⟩ y = (n3 - w3) + (n5 - w5) + w6 := by
    simpa [w3, w5, w6] using linear_dRow3 y
  have hdRow0d : dRow (linearCode n3 n5 n6) ⟨0, by decide⟩ y = d := by
    have hleO : dRow (linearCode n3 n5 n6) ⟨0, by decide⟩ y ≤
        dRow (linearCode n3 n5 n6) ⟨3, by decide⟩ y := by omega
    have hleP : dRow (linearCode n3 n5 n6) ⟨0, by decide⟩ y + 1 ≤
        dRow (linearCode n3 n5 n6) ⟨1, by decide⟩ y := hdRow1
    have hminO : linO (linearCode n3 n5 n6) y =
        dRow (linearCode n3 n5 n6) ⟨0, by decide⟩ y := by
      unfold linO
      rw [min_eq_left hleO]
    have hminP : linP (linearCode n3 n5 n6) y ≥
        dRow (linearCode n3 n5 n6) ⟨0, by decide⟩ y + 1 := by
      unfold linP
      have h1 : dRow (linearCode n3 n5 n6) ⟨0, by decide⟩ y + 1 ≤
          min (dRow (linearCode n3 n5 n6) ⟨1, by decide⟩ y)
            (dRow (linearCode n3 n5 n6) ⟨2, by decide⟩ y) := by
        apply le_min
        · exact hdRow1
        · omega
      exact h1
    have hdC : dCode (linearCode n3 n5 n6) y =
        dRow (linearCode n3 n5 n6) ⟨0, by decide⟩ y := by
      change min (dRow (linearCode n3 n5 n6) ⟨0, by decide⟩ y)
          (min (dRow (linearCode n3 n5 n6) ⟨1, by decide⟩ y)
            (min (dRow (linearCode n3 n5 n6) ⟨2, by decide⟩ y) (dRow (linearCode n3 n5 n6) ⟨3, by decide⟩ y))) =
          dRow (linearCode n3 n5 n6) ⟨0, by decide⟩ y
      have hle : dRow (linearCode n3 n5 n6) ⟨0, by decide⟩ y ≤
          min (dRow (linearCode n3 n5 n6) ⟨1, by decide⟩ y)
            (min (dRow (linearCode n3 n5 n6) ⟨2, by decide⟩ y) (dRow (linearCode n3 n5 n6) ⟨3, by decide⟩ y)) := by
        apply le_min
        · omega
        · apply le_min
          · omega
          · omega
      rw [min_eq_left hle]
    rwa [hdC] at hd
  have hsumW : w3 + w6 = m := by
    have h1 : w3 + w5 + w6 + 1 = (n3 - w3) + w5 + (n6 - w6) := by
      calc
        w3 + w5 + w6 + 1 = dRow (linearCode n3 n5 n6) ⟨0, by decide⟩ y + 1 := by
          rw [hdRow0]
        _ = dRow (linearCode n3 n5 n6) ⟨2, by decide⟩ y := hdRow2
        _ = (n3 - w3) + w5 + (n6 - w6) := hdRow2'
    have h2 : 2 * (w3 + w6) + 1 = n3 + n6 := by omega
    have h3 : 2 * (w3 + w6) = 2 * m := by omega
    omega
  have hw3leM : w3 ≤ m := by omega
  have hsum5m : w5 + m = d := by
    calc
      w5 + m = w5 + (w3 + w6) := by rw [hsumW]
      _ = w3 + w5 + w6 := by omega
      _ = dRow (linearCode n3 n5 n6) ⟨0, by decide⟩ y := hdRow0.symm
      _ = d := hdRow0d
  have hw5 : w5 = d - m := by omega
  have hw6 : w6 = m - w3 := by omega
  have hdge : m ≤ d := by omega
  constructor
  · simpa [w5] using hw5
  · constructor
    · simpa [w6] using hw6
    · constructor
      · have hge1 : d + 1 ≤ dRow (linearCode n3 n5 n6) ⟨1, by decide⟩ y := by omega
        have hge2 : 2 * w3 + (n5 + n6) ≥ 2 * d + 2 := by
          rw [hdRow1'] at hge1
          have hge' : 2 * w3 + (n5 + n6) ≥ 2 * d + 1 := by omega
          exact even_add_ge_odd_add_two ⟨w3, by ring⟩ hpar hge'
        simpa [w3] using hge2
      · have hge3 : d + 2 ≤ dRow (linearCode n3 n5 n6) ⟨3, by decide⟩ y := by omega
        have hle3 : 2 * w3 + 2 * d ≤ n3 + n5 + 2 * m - 2 := by
          rw [hdRow3'] at hge3
          omega
        simpa [w3] using hle3

/-- Y5 at the first column with `y t = false`: the weight form (eq. cli6),
with `hm : n3 + n6 = 2m + 1` and `d ≥ m`.  The bounds are written without
subtractions (`2w3 + (n5+n6) ≥ 2d+2` and `2w3 + 2d ≤ n3+n5+2m−2`) so that
`omega` can use them directly. -/
lemma linY5_false_iff' {n3 n5 n6 d m : ℕ} (y : Word (n3 + n5 + n6))
    (hn3 : 0 < n3) (hpar : Even (n5 + n6)) (hm : n3 + n6 = 2 * m + 1)
    (ht : y ⟨0, by omega⟩ = false) (hd : dCode (linearCode n3 n5 n6) y = d)
    (hge : m ≤ d) (hn56 : n5 ≤ n6) :
    linY5 (linearCode n3 n5 n6) ⟨0, by omega⟩ y ↔
      w_i (linearCode n3 n5 n6) 5 y = d - m ∧
      w_i (linearCode n3 n5 n6) 6 y = m - w_i (linearCode n3 n5 n6) 3 y ∧
        2 * w_i (linearCode n3 n5 n6) 3 y + (n5 + n6) ≥ 2 * d + 2 ∧
        2 * w_i (linearCode n3 n5 n6) 3 y + 2 * d ≤ n3 + n5 + 2 * m - 2 := by
  let t0 : Fin (n3 + n5 + n6) := ⟨0, by omega⟩
  have hcol : linearCode n3 n5 n6 t0 = col3 := by
    simp [t0, linearCode, hn3]
  constructor
  · intro hy
    exact linY5_false_weights y t0 hcol ht hpar hm hy hd
  · intro hw
    let w3 := w_i (linearCode n3 n5 n6) 3 y
    let w5 := w_i (linearCode n3 n5 n6) 5 y
    let w6 := w_i (linearCode n3 n5 n6) 6 y
    have hw5m : w5 = d - m := by simpa [w5] using hw.1
    have hw6m : w6 = m - w3 := by simpa [w3, w6] using hw.2.1
    have hw5le : w5 ≤ n5 := by
      simpa [w5, linear_count_5] using (w_i_le_count (linearCode n3 n5 n6) 5 y)
    have hw6le : w6 ≤ n6 := by
      simpa [w6, linear_count_6] using (w_i_le_count (linearCode n3 n5 n6) 6 y)
    have hw3le : w3 ≤ n3 := by
      simpa [w3, linear_count_3] using (w_i_le_count (linearCode n3 n5 n6) 3 y)
    have hw3leM : w3 ≤ m := by
      have h1 : 2 * w3 ≤ n3 + n5 - 2 := by omega
      have h2 : n3 + n5 - 2 ≤ 2 * m := by omega
      omega
    have hsumW : w3 + w6 = m := by omega
    have hdRow0 : dRow (linearCode n3 n5 n6) ⟨0, by decide⟩ y = w3 + w5 + w6 := by
      simpa [w3, w5, w6] using linear_dRow0 y
    have hdRow1 : dRow (linearCode n3 n5 n6) ⟨1, by decide⟩ y = w3 + (n5 - w5) + (n6 - w6) := by
      simpa [w3, w5, w6] using linear_dRow1 y
    have hdRow2 : dRow (linearCode n3 n5 n6) ⟨2, by decide⟩ y = (n3 - w3) + w5 + (n6 - w6) := by
      simpa [w3, w5, w6] using linear_dRow2 y
    have hdRow3 : dRow (linearCode n3 n5 n6) ⟨3, by decide⟩ y = (n3 - w3) + (n5 - w5) + w6 := by
      simpa [w3, w5, w6] using linear_dRow3 y
    have hd0 : dRow (linearCode n3 n5 n6) ⟨0, by decide⟩ y = d := by
      rw [hdRow0]
      omega
    have hd2 : dRow (linearCode n3 n5 n6) ⟨0, by decide⟩ y + 1 =
        dRow (linearCode n3 n5 n6) ⟨2, by decide⟩ y := by
      rw [hdRow0, hdRow2]
      omega
    have hd1 : dRow (linearCode n3 n5 n6) ⟨0, by decide⟩ y + 1 ≤
        dRow (linearCode n3 n5 n6) ⟨1, by decide⟩ y := by
      rw [hdRow0, hdRow1]
      omega
    have hd3 : dRow (linearCode n3 n5 n6) ⟨0, by decide⟩ y + 2 ≤
        dRow (linearCode n3 n5 n6) ⟨3, by decide⟩ y := by
      rw [hdRow0, hdRow3]
      omega
    exact linY5_weights_false y t0 hcol ht hd2 hd1 hd3

/-- The type fibers of a linear code are pairwise disjoint. -/
lemma linear_fiber_disjoint {n3 n5 n6 : ℕ} {i j : ℕ} (hij : i ≠ j) :
    Disjoint (fiber (linearCode n3 n5 n6) i) (fiber (linearCode n3 n5 n6) j) := by
  rw [Finset.disjoint_left]
  intro t ht ht'
  have hci : colVal (linearCode n3 n5 n6 t) = i := (Finset.mem_filter.mp ht).2
  have hcj : colVal (linearCode n3 n5 n6 t) = j := (Finset.mem_filter.mp ht').2
  exact hij (hci.symm.trans hcj)

/-- Every position of a linear code is a type-3, type-5, or type-6 column. -/
lemma linear_univ_cover {n3 n5 n6 : ℕ} :
    (Finset.univ : Finset (Fin (n3 + n5 + n6))) =
      fiber (linearCode n3 n5 n6) 3 ∪ fiber (linearCode n3 n5 n6) 5 ∪
        fiber (linearCode n3 n5 n6) 6 := by
  ext t
  constructor
  · intro _
    rcases linear_col_type (n3 := n3) (n5 := n5) (n6 := n6) t with h | h | h
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (by simp [fiber, h]))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (by simp [fiber, h]))
    · exact Finset.mem_union_right _ (by simp [fiber, h])
  · intro ht
    simp

/-- The first column of a linear code with n3 > 0 is a type-3 column. -/
lemma linear_first_col3 {n3 n5 n6 : ℕ} (hn3 : 0 < n3) :
    (⟨0, by omega⟩ : Fin (n3 + n5 + n6)) ∈ fiber (linearCode n3 n5 n6) 3 := by
  simp [fiber]
  change colVal (linearCode n3 n5 n6 ⟨0, by omega⟩) = 3
  simp [linearCode, hn3, colVal_col3]

/-- Number of words with `y t₀ = true` and prescribed per-type weights. -/
lemma linear_count_words (n3 n5 n6 k3 k5 k6 : ℕ) (hn3 : 0 < n3) (hk3 : 1 ≤ k3) :
    (Finset.univ.filter fun y : Word (n3 + n5 + n6) =>
      y ⟨0, by omega⟩ = true ∧
      w_i (linearCode n3 n5 n6) 3 y = k3 ∧
      w_i (linearCode n3 n5 n6) 5 y = k5 ∧
      w_i (linearCode n3 n5 n6) 6 y = k6).card =
    Nat.choose (n3 - 1) (k3 - 1) * Nat.choose n5 k5 * Nat.choose n6 k6 := by
  let t0 : Fin (n3 + n5 + n6) := ⟨0, by omega⟩
  let F3 := fiber (linearCode n3 n5 n6) 3
  let F5 := fiber (linearCode n3 n5 n6) 5
  let F6 := fiber (linearCode n3 n5 n6) 6
  let S : Finset (Word (n3 + n5 + n6)) :=
    Finset.univ.filter fun y => y t0 = true ∧
      w_i (linearCode n3 n5 n6) 3 y = k3 ∧
      w_i (linearCode n3 n5 n6) 5 y = k5 ∧
      w_i (linearCode n3 n5 n6) 6 y = k6
  let T : Finset (Finset (Fin (n3 + n5 + n6)) × (Finset (Fin (n3 + n5 + n6)) × Finset (Fin (n3 + n5 + n6)))) :=
    (Finset.powersetCard (k3 - 1) (F3.erase t0)) ×ˢ
      ((Finset.powersetCard k5 F5) ×ˢ (Finset.powersetCard k6 F6))
  have ht0F3 : t0 ∈ F3 := by simpa [F3] using (linear_first_col3 (n3 := n3) (n5 := n5) (n6 := n6) hn3)
  have hdis35 : Disjoint F3 F5 := by
    simp [F3, F5, linear_fiber_disjoint (n3 := n3) (n5 := n5) (n6 := n6) (by norm_num : (3 : ℕ) ≠ 5)]
  have hdis36 : Disjoint F3 F6 := by
    simp [F3, F6, linear_fiber_disjoint (n3 := n3) (n5 := n5) (n6 := n6) (by norm_num : (3 : ℕ) ≠ 6)]
  have hdis56 : Disjoint F5 F6 := by
    simp [F5, F6, linear_fiber_disjoint (n3 := n3) (n5 := n5) (n6 := n6) (by norm_num : (5 : ℕ) ≠ 6)]
  have honesF3 (y : Word (n3 + n5 + n6)) (hy : y t0 = true) :
      onesOn F3 y = insert t0 (onesOn (F3.erase t0) y) := by
    ext u
    constructor
    · intro hu
      have hu3 : u ∈ F3 := (Finset.mem_filter.mp hu).1
      by_cases hut : u = t0
      · simp [hut]
      · exact Finset.mem_insert.mpr (Or.inr
          (Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hut, hu3⟩, (Finset.mem_filter.mp hu).2⟩))
    · intro hu
      rcases (Finset.mem_insert.mp hu) with rfl | hu
      · exact Finset.mem_filter.mpr ⟨ht0F3, hy⟩
      · exact Finset.mem_filter.mpr ⟨(Finset.mem_erase.mp (Finset.mem_filter.mp hu).1).2, (Finset.mem_filter.mp hu).2⟩
  have hcardF3 : (F3.erase t0).card = n3 - 1 := by
    have hc : F3.card = n3 := by
      simpa [F3] using (fiber_card_eq_count (linearCode n3 n5 n6) 3).trans (linear_count_3 (n3 := n3) (n5 := n5) (n6 := n6))
    have hmem : t0 ∈ F3 := ht0F3
    rw [Finset.card_erase_of_mem hmem, hc]
  have hcardF5 : F5.card = n5 := by
    simpa [F5] using (fiber_card_eq_count (linearCode n3 n5 n6) 5).trans (linear_count_5 (n3 := n3) (n5 := n5) (n6 := n6))
  have hcardF6 : F6.card = n6 := by
    simpa [F6] using (fiber_card_eq_count (linearCode n3 n5 n6) 6).trans (linear_count_6 (n3 := n3) (n5 := n5) (n6 := n6))
  have hbij : S.card = T.card := by
    apply Finset.card_bij (fun y hy => (onesOn (F3.erase t0) y, (onesOn F5 y, onesOn F6 y)))
    · intro y hy
      rcases (Finset.mem_filter.mp hy).2 with ⟨hyt, hw3, hw5, hw6⟩
      have hA : onesOn (F3.erase t0) y ∈ Finset.powersetCard (k3 - 1) (F3.erase t0) := by
        rw [Finset.mem_powersetCard]
        constructor
        · exact Finset.filter_subset _ _
        · have hfull : (onesOn F3 y).card = k3 := by simpa [w_i_eq_card_onesOn] using hw3
          have hsplit : onesOn F3 y = insert t0 (onesOn (F3.erase t0) y) := honesF3 y hyt
          have ht0not : t0 ∉ onesOn (F3.erase t0) y := by
            intro ht
            have : t0 ∈ F3.erase t0 := (Finset.mem_filter.mp ht).1
            exact (Finset.mem_erase.mp this).1 rfl
          have hcard : (insert t0 (onesOn (F3.erase t0) y)).card = (onesOn (F3.erase t0) y).card + 1 :=
            Finset.card_insert_of_notMem ht0not
          rw [hsplit, hcard] at hfull
          omega
      have hB : onesOn F5 y ∈ Finset.powersetCard k5 F5 := by
        rw [Finset.mem_powersetCard]
        constructor
        · exact Finset.filter_subset _ _
        · simpa [w_i_eq_card_onesOn] using hw5
      have hC : onesOn F6 y ∈ Finset.powersetCard k6 F6 := by
        rw [Finset.mem_powersetCard]
        constructor
        · exact Finset.filter_subset _ _
        · simpa [w_i_eq_card_onesOn] using hw6
      simp [T, hA, hB, hC]
    · intro a ha b hb hab
      ext u
      have haS := (Finset.mem_filter.mp ha).2
      have hbS := (Finset.mem_filter.mp hb).2
      have hpair : (onesOn (F3.erase t0) a, (onesOn F5 a, onesOn F6 a)) =
          (onesOn (F3.erase t0) b, (onesOn F5 b, onesOn F6 b)) := by
        simpa using hab
      have hAeq : onesOn (F3.erase t0) a = onesOn (F3.erase t0) b := congrArg Prod.fst hpair
      have hBeq : onesOn F5 a = onesOn F5 b := congrArg (fun p => p.2.1) hpair
      have hCeq : onesOn F6 a = onesOn F6 b := congrArg (fun p => p.2.2) hpair
      have hcover : u = t0 ∨ u ∈ F3.erase t0 ∨ u ∈ F5 ∨ u ∈ F6 := by
        have huniv := linear_univ_cover (n3 := n3) (n5 := n5) (n6 := n6)
        have hu : u ∈ F3 ∪ F5 ∪ F6 := by
          rw [← huniv]
          simp
        rcases (Finset.mem_union.mp hu) with hu35 | hu6
        · rcases (Finset.mem_union.mp hu35) with hu3 | hu5
          · by_cases hut : u = t0
            · exact Or.inl hut
            · exact Or.inr (Or.inl (Finset.mem_erase.mpr ⟨hut, hu3⟩))
          · exact Or.inr (Or.inr (Or.inl hu5))
        · exact Or.inr (Or.inr (Or.inr hu6))
      rcases hcover with rfl | hu3 | hu5 | hu6
      · simp [haS.1, hbS.1]
      · have ha' : a u = true ↔ u ∈ onesOn (F3.erase t0) a := by
          constructor
          · intro h; exact Finset.mem_filter.mpr ⟨hu3, h⟩
          · intro h; exact (Finset.mem_filter.mp h).2
        have hb' : b u = true ↔ u ∈ onesOn (F3.erase t0) b := by
          constructor
          · intro h; exact Finset.mem_filter.mpr ⟨hu3, h⟩
          · intro h; exact (Finset.mem_filter.mp h).2
        by_cases hat : a u = true
        · have : b u = true := by
            have huA : u ∈ onesOn (F3.erase t0) a := ha'.mp hat
            have huB : u ∈ onesOn (F3.erase t0) b := by rwa [← hAeq]
            exact (hb'.mpr huB)
          simp [hat, this]
        · have : b u = false := by
            by_contra hbfalse
            have hbt : b u = true := by
              cases hb2 : b u
              · exfalso; exact hbfalse hb2
              · rfl
            have huB : u ∈ onesOn (F3.erase t0) b := hb'.mp hbt
            have huA : u ∈ onesOn (F3.erase t0) a := by rwa [hAeq]
            exact hat (ha'.mpr huA)
          simp [hat, this]
      · have ha' : a u = true ↔ u ∈ onesOn F5 a := by
          constructor
          · intro h; exact Finset.mem_filter.mpr ⟨hu5, h⟩
          · intro h; exact (Finset.mem_filter.mp h).2
        have hb' : b u = true ↔ u ∈ onesOn F5 b := by
          constructor
          · intro h; exact Finset.mem_filter.mpr ⟨hu5, h⟩
          · intro h; exact (Finset.mem_filter.mp h).2
        by_cases hat : a u = true
        · have : b u = true := by
            have huA : u ∈ onesOn F5 a := ha'.mp hat
            have huB : u ∈ onesOn F5 b := by rwa [← hBeq]
            exact (hb'.mpr huB)
          simp [hat, this]
        · have : b u = false := by
            by_contra hbfalse
            have hbt : b u = true := by
              cases hb2 : b u
              · exfalso; exact hbfalse hb2
              · rfl
            have huB : u ∈ onesOn F5 b := hb'.mp hbt
            have huA : u ∈ onesOn F5 a := by rwa [hBeq]
            exact hat (ha'.mpr huA)
          simp [hat, this]
      · have ha' : a u = true ↔ u ∈ onesOn F6 a := by
          constructor
          · intro h; exact Finset.mem_filter.mpr ⟨hu6, h⟩
          · intro h; exact (Finset.mem_filter.mp h).2
        have hb' : b u = true ↔ u ∈ onesOn F6 b := by
          constructor
          · intro h; exact Finset.mem_filter.mpr ⟨hu6, h⟩
          · intro h; exact (Finset.mem_filter.mp h).2
        by_cases hat : a u = true
        · have : b u = true := by
            have huA : u ∈ onesOn F6 a := ha'.mp hat
            have huB : u ∈ onesOn F6 b := by rwa [← hCeq]
            exact (hb'.mpr huB)
          simp [hat, this]
        · have : b u = false := by
            by_contra hbfalse
            have hbt : b u = true := by
              cases hb2 : b u
              · exfalso; exact hbfalse hb2
              · rfl
            have huB : u ∈ onesOn F6 b := hb'.mp hbt
            have huA : u ∈ onesOn F6 a := by rwa [hCeq]
            exact hat (ha'.mpr huA)
          simp [hat, this]
    · intro z hz
      -- surjectivity: build y from the triple
      rcases z with ⟨A, B, C⟩
      -- hz : (A, (B, C)) ∈ T
      have hA : A ∈ Finset.powersetCard (k3 - 1) (F3.erase t0) := (Finset.mem_product.mp hz).1
      have hBC : (B, C) ∈ (Finset.powersetCard k5 F5) ×ˢ Finset.powersetCard k6 F6 := (Finset.mem_product.mp hz).2
      have hB : B ∈ Finset.powersetCard k5 F5 := (Finset.mem_product.mp hBC).1
      have hC : C ∈ Finset.powersetCard k6 F6 := (Finset.mem_product.mp hBC).2
      let y : Word (n3 + n5 + n6) := fun u => decide (u ∈ A ∨ u ∈ B ∨ u ∈ C ∨ u = t0)
      have hA3 : onesOn F3 y = insert t0 A := by
        ext u
        constructor
        · intro hu
          have huF : u ∈ F3 := (Finset.mem_filter.mp hu).1
          have huy : y u := (Finset.mem_filter.mp hu).2
          have hsubA : A ⊆ F3.erase t0 := (Finset.mem_powersetCard.mp hA).1
          by_cases hut : u = t0
          · simp [hut]
          · have hmem : u ∈ A ∨ u ∈ B ∨ u ∈ C := by
              have hy' : u ∈ A ∨ u ∈ B ∨ u ∈ C ∨ u = t0 := by simpa [y] using huy
              rcases hy' with huA | huB | huC | hut'
              · exact Or.inl huA
              · have huB' : u ∈ F5 := (Finset.mem_powersetCard.mp hB).1 huB
                exact False.elim ((Finset.disjoint_left.mp hdis35) huF huB')
              · have huC' : u ∈ F6 := (Finset.mem_powersetCard.mp hC).1 huC
                exact False.elim ((Finset.disjoint_left.mp hdis36) huF huC')
              · exact False.elim (hut hut')
            rcases hmem with huA | huB | huC
            · simp [huA]
            · exact False.elim ((Finset.disjoint_left.mp hdis35) huF ((Finset.mem_powersetCard.mp hB).1 huB))
            · exact False.elim ((Finset.disjoint_left.mp hdis36) huF ((Finset.mem_powersetCard.mp hC).1 huC))
        · intro hu
          rcases (Finset.mem_insert.mp hu) with rfl | huA
          · exact Finset.mem_filter.mpr ⟨ht0F3, by simp [y]⟩
          · have hsubA : A ⊆ F3.erase t0 := (Finset.mem_powersetCard.mp hA).1
            have huF3 : u ∈ F3 := (Finset.mem_erase.mp (hsubA huA)).2
            exact Finset.mem_filter.mpr ⟨huF3, by simp [y, huA]⟩
      have hB5 : onesOn F5 y = B := by
        ext u
        constructor
        · intro hu
          have huF : u ∈ F5 := (Finset.mem_filter.mp hu).1
          have hy' : u ∈ A ∨ u ∈ B ∨ u ∈ C ∨ u = t0 := by
            simpa [y] using (Finset.mem_filter.mp hu).2
          rcases hy' with huA | huB | huC | hut
          · have huA' : u ∈ F3 := (Finset.mem_erase.mp ((Finset.mem_powersetCard.mp hA).1 huA)).2
            exact False.elim ((Finset.disjoint_left.mp hdis35) huA' huF)
          · exact huB
          · have huC' : u ∈ F6 := (Finset.mem_powersetCard.mp hC).1 huC
            exact False.elim ((Finset.disjoint_left.mp hdis56) huF huC')
          · have hut' : u = t0 := hut
            have hu3 : t0 ∈ F3 := ht0F3
            exact False.elim ((Finset.disjoint_left.mp hdis35) hu3 (by simpa [hut'] using huF))
        · intro hu
          have huF : u ∈ F5 := (Finset.mem_powersetCard.mp hB).1 hu
          exact Finset.mem_filter.mpr ⟨huF, by simp [y, hu]⟩
      have hC6 : onesOn F6 y = C := by
        ext u
        constructor
        · intro hu
          have huF : u ∈ F6 := (Finset.mem_filter.mp hu).1
          have hy' : u ∈ A ∨ u ∈ B ∨ u ∈ C ∨ u = t0 := by
            simpa [y] using (Finset.mem_filter.mp hu).2
          rcases hy' with huA | huB | huC | hut
          · have huA' : u ∈ F3 := (Finset.mem_erase.mp ((Finset.mem_powersetCard.mp hA).1 huA)).2
            exact False.elim ((Finset.disjoint_left.mp hdis36) huA' huF)
          · have huB' : u ∈ F5 := (Finset.mem_powersetCard.mp hB).1 huB
            exact False.elim ((Finset.disjoint_left.mp hdis56) huB' huF)
          · exact huC
          · have hut' : u = t0 := hut
            have hu3 : t0 ∈ F3 := ht0F3
            exact False.elim ((Finset.disjoint_left.mp hdis36) hu3 (by simpa [hut'] using huF))
        · intro hu
          have huF : u ∈ F6 := (Finset.mem_powersetCard.mp hC).1 hu
          exact Finset.mem_filter.mpr ⟨huF, by simp [y, hu]⟩
      have hA3' : onesOn (F3.erase t0) y = A := by
        ext u
        constructor
        · intro hu
          have huE : u ∈ F3.erase t0 := (Finset.mem_filter.mp hu).1
          have hy' : u ∈ A ∨ u ∈ B ∨ u ∈ C ∨ u = t0 := by
            simpa [y] using (Finset.mem_filter.mp hu).2
          rcases hy' with huA | huB | huC | hut
          · exact huA
          · have huB' : u ∈ F5 := (Finset.mem_powersetCard.mp hB).1 huB
            have huF : u ∈ F3 := (Finset.mem_erase.mp huE).2
            exact False.elim ((Finset.disjoint_left.mp hdis35) huF huB')
          · have huC' : u ∈ F6 := (Finset.mem_powersetCard.mp hC).1 huC
            have huF : u ∈ F3 := (Finset.mem_erase.mp huE).2
            exact False.elim ((Finset.disjoint_left.mp hdis36) huF huC')
          · exact False.elim ((Finset.mem_erase.mp huE).1 hut)
        · intro huA
          have hsub : A ⊆ F3.erase t0 := (Finset.mem_powersetCard.mp hA).1
          have huE : u ∈ F3.erase t0 := hsub huA
          exact Finset.mem_filter.mpr ⟨huE, by simp [y, huA]⟩
      have hyS : y ∈ S := by
        simp [S]
        constructor
        · simp [y]
        · constructor
          · rw [w_i_eq_card_onesOn, hA3]
            have hAcard : A.card = k3 - 1 := (Finset.mem_powersetCard.mp hA).2
            have ht0notA : t0 ∉ A := by
              intro ht
              have : t0 ∈ F3.erase t0 := (Finset.mem_powersetCard.mp hA).1 ht
              exact (Finset.mem_erase.mp this).1 rfl
            have hcard : (insert t0 A).card = A.card + 1 := Finset.card_insert_of_notMem ht0notA
            rw [hcard, hAcard]
            omega
          · constructor
            · rw [w_i_eq_card_onesOn, hB5]
              exact (Finset.mem_powersetCard.mp hB).2
            · rw [w_i_eq_card_onesOn, hC6]
              exact (Finset.mem_powersetCard.mp hC).2
      refine ⟨y, hyS, ?_⟩
      simp [hA3', hB5, hC6]
  calc
    S.card = T.card := hbij
    _ = (Finset.powersetCard (k3 - 1) (F3.erase t0)).card *
        ((Finset.powersetCard k5 F5).card * (Finset.powersetCard k6 F6).card) := by
          rw [Finset.card_product]
          rw [Finset.card_product]
    _ = Nat.choose (n3 - 1) (k3 - 1) * (Nat.choose n5 k5 * Nat.choose n6 k6) := by
          rw [Finset.card_powersetCard, hcardF3]
          rw [Finset.card_powersetCard, hcardF5]
          rw [Finset.card_powersetCard, hcardF6]
    _ = Nat.choose (n3 - 1) (k3 - 1) * Nat.choose n5 k5 * Nat.choose n6 k6 := by ring

/-- Counting words with `y t0 = false` and prescribed weights (eq. cli6):
since the first type-3 column contributes bit 0, the type-3 choices are among
the remaining `n3 - 1` columns. -/
lemma linear_count_words_false (n3 n5 n6 k3 k5 k6 : ℕ) (hn3 : 0 < n3) :
    (Finset.univ.filter fun y : Word (n3 + n5 + n6) =>
      y ⟨0, by omega⟩ = false ∧
      w_i (linearCode n3 n5 n6) 3 y = k3 ∧
      w_i (linearCode n3 n5 n6) 5 y = k5 ∧
      w_i (linearCode n3 n5 n6) 6 y = k6).card =
    Nat.choose (n3 - 1) k3 * Nat.choose n5 k5 * Nat.choose n6 k6 := by
  let t0 : Fin (n3 + n5 + n6) := ⟨0, by omega⟩
  let F3 := fiber (linearCode n3 n5 n6) 3
  let F5 := fiber (linearCode n3 n5 n6) 5
  let F6 := fiber (linearCode n3 n5 n6) 6
  let S : Finset (Word (n3 + n5 + n6)) :=
    Finset.univ.filter fun y => y t0 = false ∧
      w_i (linearCode n3 n5 n6) 3 y = k3 ∧
      w_i (linearCode n3 n5 n6) 5 y = k5 ∧
      w_i (linearCode n3 n5 n6) 6 y = k6
  let T : Finset (Finset (Fin (n3 + n5 + n6)) × (Finset (Fin (n3 + n5 + n6)) × Finset (Fin (n3 + n5 + n6)))) :=
    (Finset.powersetCard k3 (F3.erase t0)) ×ˢ
      ((Finset.powersetCard k5 F5) ×ˢ (Finset.powersetCard k6 F6))
  have ht0F3 : t0 ∈ F3 := by simpa [F3] using (linear_first_col3 (n3 := n3) (n5 := n5) (n6 := n6) hn3)
  have hdis35 : Disjoint F3 F5 := by
    simp [F3, F5, linear_fiber_disjoint (n3 := n3) (n5 := n5) (n6 := n6) (by norm_num : (3 : ℕ) ≠ 5)]
  have hdis36 : Disjoint F3 F6 := by
    simp [F3, F6, linear_fiber_disjoint (n3 := n3) (n5 := n5) (n6 := n6) (by norm_num : (3 : ℕ) ≠ 6)]
  have hdis56 : Disjoint F5 F6 := by
    simp [F5, F6, linear_fiber_disjoint (n3 := n3) (n5 := n5) (n6 := n6) (by norm_num : (5 : ℕ) ≠ 6)]
  have hcardF3 : (F3.erase t0).card = n3 - 1 := by
    have hc : F3.card = n3 := by
      simpa [F3] using (fiber_card_eq_count (linearCode n3 n5 n6) 3).trans (linear_count_3 (n3 := n3) (n5 := n5) (n6 := n6))
    have hmem : t0 ∈ F3 := ht0F3
    rw [Finset.card_erase_of_mem hmem, hc]
  have hcardF5 : F5.card = n5 := by
    simpa [F5] using (fiber_card_eq_count (linearCode n3 n5 n6) 5).trans (linear_count_5 (n3 := n3) (n5 := n5) (n6 := n6))
  have hcardF6 : F6.card = n6 := by
    simpa [F6] using (fiber_card_eq_count (linearCode n3 n5 n6) 6).trans (linear_count_6 (n3 := n3) (n5 := n5) (n6 := n6))
  have hbij : S.card = T.card := by
    apply Finset.card_bij (fun y hy => (onesOn (F3.erase t0) y, (onesOn F5 y, onesOn F6 y)))
    · intro y hy
      rcases (Finset.mem_filter.mp hy).2 with ⟨hyt, hw3, hw5, hw6⟩
      have hones3 : onesOn F3 y = onesOn (F3.erase t0) y := by
        ext u
        constructor
        · intro hu
          have huF : u ∈ F3 := (Finset.mem_filter.mp hu).1
          have huy : y u = true := (Finset.mem_filter.mp hu).2
          by_cases hut : u = t0
          · subst u
            simp [hyt] at huy
          · exact Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hut, huF⟩, huy⟩
        · intro hu
          have huF : u ∈ F3 := (Finset.mem_erase.mp (Finset.mem_filter.mp hu).1).2
          exact Finset.mem_filter.mpr ⟨huF, (Finset.mem_filter.mp hu).2⟩
      have hA : onesOn (F3.erase t0) y ∈ Finset.powersetCard k3 (F3.erase t0) := by
        rw [Finset.mem_powersetCard]
        constructor
        · exact Finset.filter_subset _ _
        · have hw3' : (onesOn (F3.erase t0) y).card = k3 := by
            rw [← hones3]
            simpa [w_i_eq_card_onesOn] using hw3
          exact hw3'
      have hB : onesOn F5 y ∈ Finset.powersetCard k5 F5 := by
        rw [Finset.mem_powersetCard]
        constructor
        · exact Finset.filter_subset _ _
        · simpa [w_i_eq_card_onesOn] using hw5
      have hC : onesOn F6 y ∈ Finset.powersetCard k6 F6 := by
        rw [Finset.mem_powersetCard]
        constructor
        · exact Finset.filter_subset _ _
        · simpa [w_i_eq_card_onesOn] using hw6
      simp [T, hA, hB, hC]
    · intro a ha b hb hab
      ext u
      have haS := (Finset.mem_filter.mp ha).2
      have hbS := (Finset.mem_filter.mp hb).2
      have hpair : (onesOn (F3.erase t0) a, (onesOn F5 a, onesOn F6 a)) =
          (onesOn (F3.erase t0) b, (onesOn F5 b, onesOn F6 b)) := by
        simpa using hab
      have hAeq : onesOn (F3.erase t0) a = onesOn (F3.erase t0) b := congrArg Prod.fst hpair
      have hBeq : onesOn F5 a = onesOn F5 b := congrArg (fun p => p.2.1) hpair
      have hCeq : onesOn F6 a = onesOn F6 b := congrArg (fun p => p.2.2) hpair
      have hcover : u = t0 ∨ u ∈ F3.erase t0 ∨ u ∈ F5 ∨ u ∈ F6 := by
        have huniv := linear_univ_cover (n3 := n3) (n5 := n5) (n6 := n6)
        have hu : u ∈ F3 ∪ F5 ∪ F6 := by
          rw [← huniv]
          simp
        rcases (Finset.mem_union.mp hu) with hu35 | hu6
        · rcases (Finset.mem_union.mp hu35) with hu3 | hu5
          · by_cases hut : u = t0
            · exact Or.inl hut
            · exact Or.inr (Or.inl (Finset.mem_erase.mpr ⟨hut, hu3⟩))
          · exact Or.inr (Or.inr (Or.inl hu5))
        · exact Or.inr (Or.inr (Or.inr hu6))
      rcases hcover with rfl | hu3 | hu5 | hu6
      · simp [haS.1, hbS.1]
      · have ha' : a u = true ↔ u ∈ onesOn (F3.erase t0) a := by
          constructor
          · intro h; exact Finset.mem_filter.mpr ⟨hu3, h⟩
          · intro h; exact (Finset.mem_filter.mp h).2
        have hb' : b u = true ↔ u ∈ onesOn (F3.erase t0) b := by
          constructor
          · intro h; exact Finset.mem_filter.mpr ⟨hu3, h⟩
          · intro h; exact (Finset.mem_filter.mp h).2
        by_cases hat : a u = true
        · have : b u = true := by
            have huA : u ∈ onesOn (F3.erase t0) a := ha'.mp hat
            have huB : u ∈ onesOn (F3.erase t0) b := by rwa [← hAeq]
            exact (hb'.mpr huB)
          simp [hat, this]
        · have : b u = false := by
            by_contra hbfalse
            have hbt : b u = true := by
              cases hb2 : b u
              · exfalso; exact hbfalse hb2
              · rfl
            have huB : u ∈ onesOn (F3.erase t0) b := hb'.mp hbt
            have huA : u ∈ onesOn (F3.erase t0) a := by rwa [hAeq]
            exact hat (ha'.mpr huA)
          simp [hat, this]
      · have ha' : a u = true ↔ u ∈ onesOn F5 a := by
          constructor
          · intro h; exact Finset.mem_filter.mpr ⟨hu5, h⟩
          · intro h; exact (Finset.mem_filter.mp h).2
        have hb' : b u = true ↔ u ∈ onesOn F5 b := by
          constructor
          · intro h; exact Finset.mem_filter.mpr ⟨hu5, h⟩
          · intro h; exact (Finset.mem_filter.mp h).2
        by_cases hat : a u = true
        · have : b u = true := by
            have huA : u ∈ onesOn F5 a := ha'.mp hat
            have huB : u ∈ onesOn F5 b := by rwa [← hBeq]
            exact (hb'.mpr huB)
          simp [hat, this]
        · have : b u = false := by
            by_contra hbfalse
            have hbt : b u = true := by
              cases hb2 : b u
              · exfalso; exact hbfalse hb2
              · rfl
            have huB : u ∈ onesOn F5 b := hb'.mp hbt
            have huA : u ∈ onesOn F5 a := by rwa [hBeq]
            exact hat (ha'.mpr huA)
          simp [hat, this]
      · have ha' : a u = true ↔ u ∈ onesOn F6 a := by
          constructor
          · intro h; exact Finset.mem_filter.mpr ⟨hu6, h⟩
          · intro h; exact (Finset.mem_filter.mp h).2
        have hb' : b u = true ↔ u ∈ onesOn F6 b := by
          constructor
          · intro h; exact Finset.mem_filter.mpr ⟨hu6, h⟩
          · intro h; exact (Finset.mem_filter.mp h).2
        by_cases hat : a u = true
        · have : b u = true := by
            have huA : u ∈ onesOn F6 a := ha'.mp hat
            have huB : u ∈ onesOn F6 b := by rwa [← hCeq]
            exact (hb'.mpr huB)
          simp [hat, this]
        · have : b u = false := by
            by_contra hbfalse
            have hbt : b u = true := by
              cases hb2 : b u
              · exfalso; exact hbfalse hb2
              · rfl
            have huB : u ∈ onesOn F6 b := hb'.mp hbt
            have huA : u ∈ onesOn F6 a := by rwa [hCeq]
            exact hat (ha'.mpr huA)
          simp [hat, this]
    · intro z hz
      rcases z with ⟨A, B, C⟩
      have hA : A ∈ Finset.powersetCard k3 (F3.erase t0) := (Finset.mem_product.mp hz).1
      have hBC : (B, C) ∈ (Finset.powersetCard k5 F5) ×ˢ Finset.powersetCard k6 F6 := (Finset.mem_product.mp hz).2
      have hB : B ∈ Finset.powersetCard k5 F5 := (Finset.mem_product.mp hBC).1
      have hC : C ∈ Finset.powersetCard k6 F6 := (Finset.mem_product.mp hBC).2
      let y : Word (n3 + n5 + n6) := fun u => decide (u ∈ A ∨ u ∈ B ∨ u ∈ C)
      have ht0notA : t0 ∉ A := by
        intro ht
        have hmem : t0 ∈ F3.erase t0 := (Finset.mem_powersetCard.mp hA).1 ht
        exact (Finset.mem_erase.mp hmem).1 rfl
      have ht0notB : t0 ∉ B := by
        intro ht
        have htF5 : t0 ∈ F5 := (Finset.mem_powersetCard.mp hB).1 ht
        exact (Finset.disjoint_left.mp hdis35) ht0F3 htF5
      have ht0notC : t0 ∉ C := by
        intro ht
        have htF6 : t0 ∈ F6 := (Finset.mem_powersetCard.mp hC).1 ht
        exact (Finset.disjoint_left.mp hdis36) ht0F3 htF6
      have hA3' : onesOn (F3.erase t0) y = A := by
        ext u
        constructor
        · intro hu
          have huE : u ∈ F3.erase t0 := (Finset.mem_filter.mp hu).1
          have hy' : u ∈ A ∨ u ∈ B ∨ u ∈ C := by
            simpa [y] using (Finset.mem_filter.mp hu).2
          rcases hy' with huA | huB | huC
          · exact huA
          · have huB' : u ∈ F5 := (Finset.mem_powersetCard.mp hB).1 huB
            have huF : u ∈ F3 := (Finset.mem_erase.mp huE).2
            exact False.elim ((Finset.disjoint_left.mp hdis35) huF huB')
          · have huC' : u ∈ F6 := (Finset.mem_powersetCard.mp hC).1 huC
            have huF : u ∈ F3 := (Finset.mem_erase.mp huE).2
            exact False.elim ((Finset.disjoint_left.mp hdis36) huF huC')
        · intro huA
          have hsub : A ⊆ F3.erase t0 := (Finset.mem_powersetCard.mp hA).1
          have huE : u ∈ F3.erase t0 := hsub huA
          exact Finset.mem_filter.mpr ⟨huE, by simp [y, huA]⟩
      have hA3 : onesOn F3 y = A := by
        ext u
        constructor
        · intro hu
          have huF : u ∈ F3 := (Finset.mem_filter.mp hu).1
          have hy' : u ∈ A ∨ u ∈ B ∨ u ∈ C := by
            simpa [y] using (Finset.mem_filter.mp hu).2
          rcases hy' with huA | huB | huC
          · exact huA
          · have huB' : u ∈ F5 := (Finset.mem_powersetCard.mp hB).1 huB
            exact False.elim ((Finset.disjoint_left.mp hdis35) huF huB')
          · have huC' : u ∈ F6 := (Finset.mem_powersetCard.mp hC).1 huC
            exact False.elim ((Finset.disjoint_left.mp hdis36) huF huC')
        · intro huA
          have hsub : A ⊆ F3.erase t0 := (Finset.mem_powersetCard.mp hA).1
          have huF : u ∈ F3 := (Finset.mem_erase.mp (hsub huA)).2
          exact Finset.mem_filter.mpr ⟨huF, by simp [y, huA]⟩
      have hB5 : onesOn F5 y = B := by
        ext u
        constructor
        · intro hu
          have huF : u ∈ F5 := (Finset.mem_filter.mp hu).1
          have hy' : u ∈ A ∨ u ∈ B ∨ u ∈ C := by
            simpa [y] using (Finset.mem_filter.mp hu).2
          rcases hy' with huA | huB | huC
          · have huA' : u ∈ F3 := (Finset.mem_erase.mp ((Finset.mem_powersetCard.mp hA).1 huA)).2
            exact False.elim ((Finset.disjoint_left.mp hdis35) huA' huF)
          · exact huB
          · have huC' : u ∈ F6 := (Finset.mem_powersetCard.mp hC).1 huC
            exact False.elim ((Finset.disjoint_left.mp hdis56) huF huC')
        · intro hu
          have huF : u ∈ F5 := (Finset.mem_powersetCard.mp hB).1 hu
          exact Finset.mem_filter.mpr ⟨huF, by simp [y, hu]⟩
      have hC6 : onesOn F6 y = C := by
        ext u
        constructor
        · intro hu
          have huF : u ∈ F6 := (Finset.mem_filter.mp hu).1
          have hy' : u ∈ A ∨ u ∈ B ∨ u ∈ C := by
            simpa [y] using (Finset.mem_filter.mp hu).2
          rcases hy' with huA | huB | huC
          · have huA' : u ∈ F3 := (Finset.mem_erase.mp ((Finset.mem_powersetCard.mp hA).1 huA)).2
            exact False.elim ((Finset.disjoint_left.mp hdis36) huA' huF)
          · have huB' : u ∈ F5 := (Finset.mem_powersetCard.mp hB).1 huB
            exact False.elim ((Finset.disjoint_left.mp hdis56) huB' huF)
          · exact huC
        · intro hu
          have huF : u ∈ F6 := (Finset.mem_powersetCard.mp hC).1 hu
          exact Finset.mem_filter.mpr ⟨huF, by simp [y, hu]⟩
      have hyS : y ∈ S := by
        simp [S]
        constructor
        · simp [y, ht0notA, ht0notB, ht0notC]
        · constructor
          · rw [w_i_eq_card_onesOn, hA3]
            exact (Finset.mem_powersetCard.mp hA).2
          · constructor
            · rw [w_i_eq_card_onesOn, hB5]
              exact (Finset.mem_powersetCard.mp hB).2
            · rw [w_i_eq_card_onesOn, hC6]
              exact (Finset.mem_powersetCard.mp hC).2
      refine ⟨y, hyS, ?_⟩
      simp [hA3', hB5, hC6]
  calc
    S.card = T.card := hbij
    _ = (Finset.powersetCard k3 (F3.erase t0)).card *
        ((Finset.powersetCard k5 F5).card * (Finset.powersetCard k6 F6).card) := by
          rw [Finset.card_product]
          rw [Finset.card_product]
    _ = Nat.choose (n3 - 1) k3 * (Nat.choose n5 k5 * Nat.choose n6 k6) := by
          rw [Finset.card_powersetCard, hcardF3]
          rw [Finset.card_powersetCard, hcardF5]
          rw [Finset.card_powersetCard, hcardF6]
    _ = Nat.choose (n3 - 1) k3 * Nat.choose n5 k5 * Nat.choose n6 k6 := by ring

/-- Y3 at the first column with `y t = true`: the weight form (eq. cli7),
with the range condition `2d ≥ n3+n5` that makes the sums consistent. -/
lemma linY3_true_iff' {n3 n5 n6 : ℕ} (y : Word (n3 + n5 + n6))
    (hn3 : 0 < n3) (hpar : Even (n5 + n6)) (ht : y ⟨0, by omega⟩ = true)
    (hd : dCode (linearCode n3 n5 n6) y = d) (_hge : 2 * d ≥ n3 + n5) (hn56 : n5 ≤ n6) :
    linY3 (linearCode n3 n5 n6) ⟨0, by omega⟩ y ↔
      w_i (linearCode n3 n5 n6) 3 y = d - (n5 + n6) / 2 ∧
      w_i (linearCode n3 n5 n6) 6 y = (n5 + n6) / 2 - w_i (linearCode n3 n5 n6) 5 y ∧
        2 * w_i (linearCode n3 n5 n6) 5 y ≥ 2 * d - n3 - n6 ∧
        2 * w_i (linearCode n3 n5 n6) 5 y ≤ n3 + 2 * n5 + n6 - 2 * d := by
  let t0 : Fin (n3 + n5 + n6) := ⟨0, by omega⟩
  have hcol : linearCode n3 n5 n6 t0 = col3 := by
    simp [t0, linearCode, hn3]
  constructor
  · intro hy
    exact linY3_true_weights y t0 hcol ht hpar hy hd
  · intro hw
    rcases hpar with ⟨k, hk⟩
    have hkdiv : (2 * k) / 2 = k := Nat.mul_div_right k (by decide : 0 < 2)
    have hS : (n5 + n6) / 2 = k := by
      rw [hk, ← two_mul k, hkdiv]
    let w3 := w_i (linearCode n3 n5 n6) 3 y
    let w5 := w_i (linearCode n3 n5 n6) 5 y
    let w6 := w_i (linearCode n3 n5 n6) 6 y
    have hw3k : w3 = d - k := by
      have : w3 = d - (n5 + n6) / 2 := by simpa [w3] using hw.1
      rw [hS] at this
      exact this
    have hw6k : w6 = k - w5 := by
      have : w6 = (n5 + n6) / 2 - w5 := by simpa [w3, w5, w6] using hw.2.1
      rw [hS] at this
      exact this
    have hw5le : w5 ≤ n5 := by
      simpa [w5, linear_count_5] using (w_i_le_count (linearCode n3 n5 n6) 5 y)
    have hw6le : w6 ≤ n6 := by
      simpa [w6, linear_count_6] using (w_i_le_count (linearCode n3 n5 n6) 6 y)
    have hw3pos : 1 ≤ w3 := by
      simpa [w3] using (linear_w3_pos_of_true y t0 hcol ht)
    have hkd : k < d := by
      have : 1 ≤ d - k := by simpa [hw3k] using hw3pos
      exact Nat.lt_of_sub_pos (lt_of_lt_of_le (by norm_num : 0 < 1) this)
    -- w5 ≤ k via the dRow1 < d contradiction
    have hw5leK : w5 ≤ k := by
      by_contra h
      have hw5gt : k < w5 := by omega
      have hw6zero : w6 = 0 := by
        rw [hw6k, Nat.sub_eq_zero_of_le (le_of_lt hw5gt)]
      have hd2lt : dRow (linearCode n3 n5 n6) ⟨1, by decide⟩ y < d := by
        have hsum56 : (n5 - w5) + n6 = (n5 + n6) - w5 :=
          (Nat.sub_add_comm (n := n5) (m := n6) (k := w5) hw5le).symm
        have hsum2k : (n5 + n6) - w5 = 2 * k - w5 := by
          rw [hk, two_mul]
        have h2kw : 2 * k - w5 < k := by omega
        rw [linear_dRow1 y]
        change w3 + (n5 - w5) + (n6 - w6) < d
        rw [hw3k, hw6zero]
        simp
        rw [add_assoc, hsum56, hsum2k]
        omega
      have hle1 : dCode (linearCode n3 n5 n6) y ≤ dRow (linearCode n3 n5 n6) ⟨1, by decide⟩ y := by
        unfold dCode
        exact le_trans (min_le_right _ _) (min_le_left _ _)
      have : d < d := by omega
      exact False.elim (lt_irrefl d this)
    have hsum : w5 + w6 = k := by
      rw [hw6k, Nat.add_sub_cancel' hw5leK]
    have hd0 : w3 + w5 + w6 = d := by
      rw [hw3k, add_assoc, hsum]
      omega
    have hdRow0 : dRow (linearCode n3 n5 n6) ⟨0, by decide⟩ y = w3 + w5 + w6 := by
      simpa [w3, w5, w6] using linear_dRow0 y
    have hdRow0d : dRow (linearCode n3 n5 n6) ⟨0, by decide⟩ y = d := by
      rw [hdRow0]
      exact hd0
    have he0 : dRow (linearCode n3 n5 n6) ⟨0, by decide⟩ y =
        dRow (linearCode n3 n5 n6) ⟨1, by decide⟩ y := by
      have hdRow1 : dRow (linearCode n3 n5 n6) ⟨1, by decide⟩ y = w3 + (n5 - w5) + (n6 - w6) := by
        simpa [w3, w5, w6] using linear_dRow1 y
      have hsum56 : (n5 - w5) + (n6 - w6) = k := by
        have h1 : (n5 - w5) + (n6 - w6) = (n5 + n6) - (w5 + w6) := by omega
        rw [h1, hsum, hk]
        omega
      calc
        dRow (linearCode n3 n5 n6) ⟨0, by decide⟩ y = w3 + w5 + w6 := hdRow0
        _ = w3 + k := by
          rw [add_assoc, hsum]
        _ = w3 + (n5 - w5) + (n6 - w6) := by rw [add_assoc, hsum56]
        _ = dRow (linearCode n3 n5 n6) ⟨1, by decide⟩ y := hdRow1.symm
    have he2 : dRow (linearCode n3 n5 n6) ⟨0, by decide⟩ y ≤
        dRow (linearCode n3 n5 n6) ⟨2, by decide⟩ y := by
      have h2 : d ≤ dRow (linearCode n3 n5 n6) ⟨2, by decide⟩ y := by
        have hdCode_le : dCode (linearCode n3 n5 n6) y ≤ dRow (linearCode n3 n5 n6) ⟨2, by decide⟩ y := by
          unfold dCode
          exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
        rwa [hd] at hdCode_le
      rw [hdRow0d]
      exact h2
    have he3 : dRow (linearCode n3 n5 n6) ⟨0, by decide⟩ y ≤
        dRow (linearCode n3 n5 n6) ⟨3, by decide⟩ y := by
      have h2 : d ≤ dRow (linearCode n3 n5 n6) ⟨3, by decide⟩ y := by
        have hdCode_le : dCode (linearCode n3 n5 n6) y ≤ dRow (linearCode n3 n5 n6) ⟨3, by decide⟩ y := by
          unfold dCode
          exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
        rwa [hd] at hdCode_le
      rw [hdRow0d]
      exact h2
    exact linY3_weights_true y t0 hcol ht he0 he2 he3

/-! ## Parity consequences (paper cases 1)–2) of `thm:linearcompare` (Theorem 12)) -/

/-- d1 = d2 forces n5 + n6 even. -/
lemma linear_e0e1_implies_even_sum {n3 n5 n6 : ℕ} (y : Word (n3 + n5 + n6))
    (h : dRow (linearCode n3 n5 n6) ⟨0, by decide⟩ y =
      dRow (linearCode n3 n5 n6) ⟨1, by decide⟩ y) :
    Even (n5 + n6) := by
  rw [linear_dRow0, linear_dRow1] at h
  have hw5le : w_i (linearCode n3 n5 n6) 5 y ≤ n5 :=
    le_trans (w_i_le_count (linearCode n3 n5 n6) 5 y) (le_of_eq linear_count_5)
  have hw6le : w_i (linearCode n3 n5 n6) 6 y ≤ n6 :=
    le_trans (w_i_le_count (linearCode n3 n5 n6) 6 y) (le_of_eq linear_count_6)
  refine ⟨w_i (linearCode n3 n5 n6) 5 y + w_i (linearCode n3 n5 n6) 6 y, ?_⟩
  omega

/-- d3 = d4 forces n5 + n6 even. -/
lemma linear_e2e3_implies_even_sum {n3 n5 n6 : ℕ} (y : Word (n3 + n5 + n6))
    (h : dRow (linearCode n3 n5 n6) ⟨2, by decide⟩ y =
      dRow (linearCode n3 n5 n6) ⟨3, by decide⟩ y) :
    Even (n5 + n6) := by
  rw [linear_dRow2, linear_dRow3] at h
  have hw5le : w_i (linearCode n3 n5 n6) 5 y ≤ n5 :=
    le_trans (w_i_le_count (linearCode n3 n5 n6) 5 y) (le_of_eq linear_count_5)
  have hw6le : w_i (linearCode n3 n5 n6) 6 y ≤ n6 :=
    le_trans (w_i_le_count (linearCode n3 n5 n6) 6 y) (le_of_eq linear_count_6)
  refine ⟨w_i (linearCode n3 n5 n6) 5 y + n6 - w_i (linearCode n3 n5 n6) 6 y, ?_⟩
  omega

/-- Y3 forces n5 and n6 to have the same parity. -/
lemma linY3_implies_same_parity_5_6 {n3 n5 n6 : ℕ} (y : Word (n3 + n5 + n6))
    (t : Fin (n3 + n5 + n6)) (hcol : linearCode n3 n5 n6 t = col3)
    (hy : linY3 (linearCode n3 n5 n6) t y) :
    (Even n5 ↔ Even n6) := by
  by_cases ht : y t = true
  · have h := linY3_true_implies y t hcol ht hy
    exact Nat.even_add.mp (linear_e0e1_implies_even_sum y h.1)
  · have ht' : y t = false := by simp [ht]
    have h := linY3_false_implies y t hcol ht' hy
    exact Nat.even_add.mp (linear_e2e3_implies_even_sum y h.1)

/-- Y3 with `y t = true` forces 2·w3 ≤ n3. -/
lemma linY3_true_implies_2w3_le_n3 {n3 n5 n6 : ℕ} (y : Word (n3 + n5 + n6))
    (t : Fin (n3 + n5 + n6)) (hcol : linearCode n3 n5 n6 t = col3) (ht : y t = true)
    (hy : linY3 (linearCode n3 n5 n6) t y) :
    2 * w_i (linearCode n3 n5 n6) 3 y ≤ n3 := by
  have h := linY3_true_implies y t hcol ht hy
  rcases h with ⟨he0, he2, he3⟩
  rw [linear_dRow0, linear_dRow1] at he0
  rw [linear_dRow0, linear_dRow2] at he2
  rw [linear_dRow0, linear_dRow3] at he3
  have hw3le : w_i (linearCode n3 n5 n6) 3 y ≤ n3 :=
    le_trans (w_i_le_count (linearCode n3 n5 n6) 3 y) (le_of_eq linear_count_3)
  omega

/-- d2 = d4 + 1 forces n3 and n6 to have different parity. -/
lemma linear_e1e3_implies_not_same_parity_3_6 {n3 n5 n6 : ℕ}
    (y : Word (n3 + n5 + n6))
    (h : dRow (linearCode n3 n5 n6) ⟨1, by decide⟩ y =
      dRow (linearCode n3 n5 n6) ⟨3, by decide⟩ y + 1) :
    ¬ (Even n3 ↔ Even n6) := by
  rw [linear_dRow1, linear_dRow3] at h
  have hw3le : w_i (linearCode n3 n5 n6) 3 y ≤ n3 :=
    le_trans (w_i_le_count (linearCode n3 n5 n6) 3 y) (le_of_eq linear_count_3)
  have hw5le : w_i (linearCode n3 n5 n6) 5 y ≤ n5 :=
    le_trans (w_i_le_count (linearCode n3 n5 n6) 5 y) (le_of_eq linear_count_5)
  have hw6le : w_i (linearCode n3 n5 n6) 6 y ≤ n6 :=
    le_trans (w_i_le_count (linearCode n3 n5 n6) 6 y) (le_of_eq linear_count_6)
  intro hiff
  by_cases hn3 : Even n3
  · rcases hn3 with ⟨k3, hk3⟩
    have hn6 : Even n6 := hiff.mp (by exact ⟨k3, hk3⟩)
    rcases hn6 with ⟨k6, hk6⟩
    omega
  · have hn3' : Odd n3 := Nat.not_even_iff_odd.mp hn3
    have hn6' : ¬ Even n6 := mt hiff.mpr hn3
    have hn6'' : Odd n6 := Nat.not_even_iff_odd.mp hn6'
    rcases hn3' with ⟨k3, hk3⟩
    rcases hn6'' with ⟨k6, hk6⟩
    omega

/-- d1 + 1 = d3 forces n3 and n6 to have different parity. -/
lemma linear_e2e0_implies_not_same_parity_3_6 {n3 n5 n6 : ℕ}
    (y : Word (n3 + n5 + n6))
    (h : dRow (linearCode n3 n5 n6) ⟨0, by decide⟩ y + 1 =
      dRow (linearCode n3 n5 n6) ⟨2, by decide⟩ y) :
    ¬ (Even n3 ↔ Even n6) := by
  rw [linear_dRow0, linear_dRow2] at h
  have hw3le : w_i (linearCode n3 n5 n6) 3 y ≤ n3 :=
    le_trans (w_i_le_count (linearCode n3 n5 n6) 3 y) (le_of_eq linear_count_3)
  have hw5le : w_i (linearCode n3 n5 n6) 5 y ≤ n5 :=
    le_trans (w_i_le_count (linearCode n3 n5 n6) 5 y) (le_of_eq linear_count_5)
  have hw6le : w_i (linearCode n3 n5 n6) 6 y ≤ n6 :=
    le_trans (w_i_le_count (linearCode n3 n5 n6) 6 y) (le_of_eq linear_count_6)
  intro hiff
  by_cases hn3 : Even n3
  · rcases hn3 with ⟨k3, hk3⟩
    have hn6 : Even n6 := hiff.mp (by exact ⟨k3, hk3⟩)
    rcases hn6 with ⟨k6, hk6⟩
    omega
  · have hn3' : Odd n3 := Nat.not_even_iff_odd.mp hn3
    have hn6' : ¬ Even n6 := mt hiff.mpr hn3
    have hn6'' : Odd n6 := Nat.not_even_iff_odd.mp hn6'
    rcases hn3' with ⟨k3, hk3⟩
    rcases hn6'' with ⟨k6, hk6⟩
    omega

/-- Y5 forces n3 and n6 to have different parity. -/
lemma linY5_implies_not_same_parity_3_6 {n3 n5 n6 : ℕ} (y : Word (n3 + n5 + n6))
    (t : Fin (n3 + n5 + n6)) (hcol : linearCode n3 n5 n6 t = col3)
    (hy : linY5 (linearCode n3 n5 n6) t y) :
    ¬ (Even n3 ↔ Even n6) := by
  by_cases ht : y t = true
  · exact linear_e1e3_implies_not_same_parity_3_6 y (linY5_true_implies y t hcol ht hy)
  · have ht' : y t = false := by simp [ht]
    exact linear_e2e0_implies_not_same_parity_3_6 y (linY5_false_implies y t hcol ht' hy)

/-- Y3 is empty when n3 = 1 (a type-3 column cannot witness the flip). -/
lemma linY3_empty_n3_1 {n3 n5 n6 : ℕ} (hn3 : n3 = 1)
    (y : Word (n3 + n5 + n6)) (t : Fin (n3 + n5 + n6))
    (hcol : linearCode n3 n5 n6 t = col3) :
    ¬ linY3 (linearCode n3 n5 n6) t y := by
  intro hy
  by_cases ht : y t = true
  · have hw := linY3_true_implies_2w3_le_n3 y t hcol ht hy
    have hwpos : 1 ≤ w_i (linearCode n3 n5 n6) 3 y :=
      linear_w3_pos_of_true y t hcol ht
    omega
  · have ht' : y t = false := by simp [ht]
    have h := linY3_false_implies y t hcol ht' hy
    rcases h with ⟨he2, he0, he1⟩
    rw [linear_dRow2, linear_dRow3] at he2
    rw [linear_dRow2, linear_dRow0] at he0
    rw [linear_dRow2, linear_dRow1] at he1
    have hw3 : w_i (linearCode n3 n5 n6) 3 y = 0 := by
      have hlt : w_i (linearCode n3 n5 n6) 3 y < n3 :=
        linear_w3_lt_n3_of_false y t hcol ht'
      omega
    have hw3le : w_i (linearCode n3 n5 n6) 3 y ≤ n3 :=
      le_trans (w_i_le_count (linearCode n3 n5 n6) 3 y) (le_of_eq linear_count_3)
    have hw5le : w_i (linearCode n3 n5 n6) 5 y ≤ n5 :=
      le_trans (w_i_le_count (linearCode n3 n5 n6) 5 y) (le_of_eq linear_count_5)
    have hw6le : w_i (linearCode n3 n5 n6) 6 y ≤ n6 :=
      le_trans (w_i_le_count (linearCode n3 n5 n6) 6 y) (le_of_eq linear_count_6)
    omega

/-! ## Explicit witnesses for Y3 (paper case 2) of `thm:linearcompare` (Theorem 12)) -/

/-- The word with ones on the first `a` type-3, `b` type-5, and `c` type-6
columns. -/
def linearWitness {n3 n5 n6 : ℕ} (a b c : ℕ) : Word (n3 + n5 + n6) :=
  fun u => u.val < a ∨ (n3 ≤ u.val ∧ u.val < n3 + b) ∨
    (n3 + n5 ≤ u.val ∧ u.val < n3 + n5 + c)

/-- The witness has exactly `a` ones on the type-3 columns. -/
lemma linearWitness_w3 {n3 n5 n6 : ℕ} {a b c : ℕ} (ha : a ≤ n3) :
    w_i (linearCode n3 n5 n6) 3 (linearWitness (n3 := n3) (n5 := n5) (n6 := n6) a b c) = a := by
  rw [w_i_eq_card_onesOn]
  unfold onesOn
  rw [linear_fiber_3]
  have hbij : ((Finset.univ : Finset (Fin (n3 + n5 + n6))).filter
      (fun u => u.val < n3)).filter
        (fun u => linearWitness (n3 := n3) (n5 := n5) (n6 := n6) a b c u = true) =
      (Finset.univ : Finset (Fin (n3 + n5 + n6))).filter (fun u => u.val < a) := by
    ext u
    simp [linearWitness]
    constructor
    · intro h
      rcases h with ⟨h1, h2⟩
      rcases h2 with h2 | h2 | h2
      · exact h2
      · omega
      · omega
    · intro h
      exact ⟨by omega, Or.inl h⟩
  rw [hbij]
  exact card_fin_lt (m := a) (n := n3 + n5 + n6) (by omega)

/-- The witness has exactly `b` ones on the type-5 columns. -/
lemma linearWitness_w5 {n3 n5 n6 : ℕ} {a b c : ℕ} (ha : a ≤ n3) (hb : b ≤ n5) :
    w_i (linearCode n3 n5 n6) 5 (linearWitness (n3 := n3) (n5 := n5) (n6 := n6) a b c) = b := by
  rw [w_i_eq_card_onesOn]
  unfold onesOn
  rw [linear_fiber_5]
  have hbij : ((Finset.univ : Finset (Fin (n3 + n5 + n6))).filter
      (fun u => n3 ≤ u.val ∧ u.val < n3 + n5)).filter
        (fun u => linearWitness (n3 := n3) (n5 := n5) (n6 := n6) a b c u = true) =
      (Finset.univ : Finset (Fin (n3 + n5 + n6))).filter
        (fun u => n3 ≤ u.val ∧ u.val < n3 + b) := by
    ext u
    simp [linearWitness]
    constructor
    · intro h
      rcases h with ⟨h1, h2⟩
      rcases h1 with ⟨h1a, h1b⟩
      rcases h2 with h2 | h2 | h2
      · omega
      · exact ⟨h2.1, h2.2⟩
      · omega
    · intro h
      exact ⟨⟨h.1, by omega⟩, Or.inr (Or.inl h)⟩
  rw [hbij]
  -- card of {u : n3 ≤ u.val < n3 + b} is b
  let f : Fin b → Fin (n3 + n5 + n6) := fun i => ⟨n3 + i.val, by omega⟩
  have hb2 : (Finset.univ.filter (fun u : Fin (n3 + n5 + n6) =>
      n3 ≤ u.val ∧ u.val < n3 + b)) =
      (Finset.univ : Finset (Fin b)).map ⟨f, by
        intro x y hxy
        apply Fin.ext
        have hv := congrArg Fin.val hxy
        simpa [f] using hv⟩ := by
    ext u
    constructor
    · intro hu
      have hu' : n3 ≤ u.val ∧ u.val < n3 + b := by simpa using hu
      have hmem : ⟨u.val - n3, by omega⟩ ∈ (Finset.univ : Finset (Fin b)) := by simp
      refine Finset.mem_map.mpr ⟨⟨u.val - n3, by omega⟩, hmem, ?_⟩
      apply Fin.ext
      change (f ⟨u.val - n3, by omega⟩).val = u.val
      simp [f]
      omega
    · intro hm
      rw [Finset.mem_map] at hm
      rcases hm with ⟨i, hi, hiu⟩
      have hv : (f i).val = u.val := congrArg Fin.val hiu
      have hval : n3 + i.val = u.val := by simpa [f] using hv
      have hge : n3 ≤ u.val := by omega
      have hlt : u.val < n3 + b := by omega
      simp [hge, hlt]
  rw [hb2, Finset.card_map]
  simp

/-- The witness has exactly `c` ones on the type-6 columns. -/
lemma linearWitness_w6 {n3 n5 n6 : ℕ} {a b c : ℕ} (ha : a ≤ n3) (hb : b ≤ n5)
    (hc : c ≤ n6) :
    w_i (linearCode n3 n5 n6) 6 (linearWitness (n3 := n3) (n5 := n5) (n6 := n6) a b c) = c := by
  rw [w_i_eq_card_onesOn]
  unfold onesOn
  rw [linear_fiber_6]
  have hbij : ((Finset.univ : Finset (Fin (n3 + n5 + n6))).filter
      (fun u => n3 + n5 ≤ u.val)).filter
        (fun u => linearWitness (n3 := n3) (n5 := n5) (n6 := n6) a b c u = true) =
      (Finset.univ : Finset (Fin (n3 + n5 + n6))).filter
        (fun u => n3 + n5 ≤ u.val ∧ u.val < n3 + n5 + c) := by
    ext u
    simp [linearWitness]
    intro hA
    constructor
    · intro h
      rcases h with h | h | h
      · omega
      · omega
      · exact h.2
    · intro h
      exact Or.inr (Or.inr ⟨hA, h⟩)
  rw [hbij]
  let f : Fin c → Fin (n3 + n5 + n6) := fun i => ⟨n3 + n5 + i.val, by omega⟩
  have hb2 : (Finset.univ.filter (fun u : Fin (n3 + n5 + n6) =>
      n3 + n5 ≤ u.val ∧ u.val < n3 + n5 + c)) =
      (Finset.univ : Finset (Fin c)).map ⟨f, by
        intro x y hxy
        apply Fin.ext
        have hv := congrArg Fin.val hxy
        simpa [f] using hv⟩ := by
    ext u
    constructor
    · intro hu
      have hu' : n3 + n5 ≤ u.val ∧ u.val < n3 + n5 + c := by simpa using hu
      have hmem : ⟨u.val - (n3 + n5), by omega⟩ ∈ (Finset.univ : Finset (Fin c)) := by simp
      refine Finset.mem_map.mpr ⟨⟨u.val - (n3 + n5), by omega⟩, hmem, ?_⟩
      apply Fin.ext
      change (f ⟨u.val - (n3 + n5), by omega⟩).val = u.val
      simp [f]
      omega
    · intro hm
      rw [Finset.mem_map] at hm
      rcases hm with ⟨i, hi, hiu⟩
      have hv : (f i).val = u.val := congrArg Fin.val hiu
      have hval : n3 + n5 + i.val = u.val := by simpa [f] using hv
      have hge : n3 + n5 ≤ u.val := by omega
      have hlt : u.val < n3 + n5 + c := by omega
      simp [hge, hlt]
  rw [hb2, Finset.card_map]
  simp

/-- The witness has bit 1 at the first (type-3) column when a ≥ 1. -/
lemma linearWitness_t {n3 n5 n6 : ℕ} {a b c : ℕ} (ha : 1 ≤ a) (ha' : a ≤ n3) :
    linearWitness (n3 := n3) (n5 := n5) (n6 := n6) a b c ⟨0, by omega⟩ = true := by
  simp [linearWitness]
  left
  omega

/-- All-odd case-2 witness: `w3 = (n3−1)/2, w5 = (n5−1)/2, w6 = (n6+1)/2`. -/
lemma linY3_witness_odd {n3 n5 n6 : ℕ} (hn3odd : Odd n3) (hn5odd : Odd n5)
    (hn6odd : Odd n6) (hn3 : 3 ≤ n3) :
    ∃ y : Word (n3 + n5 + n6), linY3 (linearCode n3 n5 n6) ⟨0, by omega⟩ y := by
  rcases hn3odd with ⟨k3, hk3⟩
  rcases hn5odd with ⟨k5, hk5⟩
  rcases hn6odd with ⟨k6, hk6⟩
  let a := k3
  let b := k5
  let c := k6 + 1
  let y := linearWitness (n3 := n3) (n5 := n5) (n6 := n6) a b c
  refine ⟨y, ?_⟩
  have ha1 : 1 ≤ a := by
    have : 2 * k3 + 1 ≥ 3 := by omega
    omega
  have ha : a ≤ n3 := by omega
  have hb : b ≤ n5 := by omega
  have hc : c ≤ n6 := by omega
  have hcol : (linearCode n3 n5 n6) ⟨0, by omega⟩ = col3 := by
    simp [linearCode]
    omega
  have ht : y ⟨0, by omega⟩ = true := by
    unfold y
    exact linearWitness_t (n3 := n3) (n5 := n5) (n6 := n6) (a := a) (b := b) (c := c) ha1 ha
  have hw3 : w_i (linearCode n3 n5 n6) 3 y = a :=
    linearWitness_w3 (n3 := n3) (n5 := n5) (n6 := n6) (a := a) (b := b) (c := c) ha
  have hw5 : w_i (linearCode n3 n5 n6) 5 y = b :=
    linearWitness_w5 (n3 := n3) (n5 := n5) (n6 := n6) (a := a) (b := b) (c := c) ha hb
  have hw6 : w_i (linearCode n3 n5 n6) 6 y = c :=
    linearWitness_w6 (n3 := n3) (n5 := n5) (n6 := n6) (a := a) (b := b) (c := c) ha hb hc
  have he0 : dRow (linearCode n3 n5 n6) ⟨0, by decide⟩ y =
      dRow (linearCode n3 n5 n6) ⟨1, by decide⟩ y := by
    rw [linear_dRow0, linear_dRow1, hw3, hw5, hw6]
    change k3 + k5 + (k6 + 1) = k3 + (n5 - k5) + (n6 - (k6 + 1))
    omega
  have he2 : dRow (linearCode n3 n5 n6) ⟨0, by decide⟩ y ≤
      dRow (linearCode n3 n5 n6) ⟨2, by decide⟩ y := by
    rw [linear_dRow0, linear_dRow2, hw3, hw5, hw6]
    change k3 + k5 + (k6 + 1) ≤ (n3 - k3) + k5 + (n6 - (k6 + 1))
    omega
  have he3 : dRow (linearCode n3 n5 n6) ⟨0, by decide⟩ y ≤
      dRow (linearCode n3 n5 n6) ⟨3, by decide⟩ y := by
    rw [linear_dRow0, linear_dRow3, hw3, hw5, hw6]
    change k3 + k5 + (k6 + 1) ≤ (n3 - k3) + (n5 - k5) + (k6 + 1)
    omega
  exact linY3_weights_true y ⟨0, by omega⟩ hcol ht he0 he2 he3

/-- All-even case-2 witness: `w3 = n3/2, w5 = n5/2, w6 = n6/2`. -/
lemma linY3_witness_even {n3 n5 n6 : ℕ} (hn3e : Even n3) (hn5e : Even n5)
    (hn6e : Even n6) (hn3 : 2 ≤ n3) :
    ∃ y : Word (n3 + n5 + n6), linY3 (linearCode n3 n5 n6) ⟨0, by omega⟩ y := by
  rcases hn3e with ⟨k3, hk3⟩
  rcases hn5e with ⟨k5, hk5⟩
  rcases hn6e with ⟨k6, hk6⟩
  let a := k3
  let b := k5
  let c := k6
  let y := linearWitness (n3 := n3) (n5 := n5) (n6 := n6) a b c
  refine ⟨y, ?_⟩
  have ha1 : 1 ≤ a := by
    have : k3 + k3 ≥ 2 := by omega
    omega
  have ha : a ≤ n3 := by omega
  have hb : b ≤ n5 := by omega
  have hc : c ≤ n6 := by omega
  have hcol : (linearCode n3 n5 n6) ⟨0, by omega⟩ = col3 := by
    simp [linearCode]
    omega
  have ht : y ⟨0, by omega⟩ = true := by
    unfold y
    exact linearWitness_t (n3 := n3) (n5 := n5) (n6 := n6) (a := a) (b := b) (c := c) ha1 ha
  have hw3 : w_i (linearCode n3 n5 n6) 3 y = a :=
    linearWitness_w3 (n3 := n3) (n5 := n5) (n6 := n6) (a := a) (b := b) (c := c) ha
  have hw5 : w_i (linearCode n3 n5 n6) 5 y = b :=
    linearWitness_w5 (n3 := n3) (n5 := n5) (n6 := n6) (a := a) (b := b) (c := c) ha hb
  have hw6 : w_i (linearCode n3 n5 n6) 6 y = c :=
    linearWitness_w6 (n3 := n3) (n5 := n5) (n6 := n6) (a := a) (b := b) (c := c) ha hb hc
  have he0 : dRow (linearCode n3 n5 n6) ⟨0, by decide⟩ y =
      dRow (linearCode n3 n5 n6) ⟨1, by decide⟩ y := by
    rw [linear_dRow0, linear_dRow1, hw3, hw5, hw6]
    change k3 + k5 + k6 = k3 + (n5 - k5) + (n6 - k6)
    omega
  have he2 : dRow (linearCode n3 n5 n6) ⟨0, by decide⟩ y ≤
      dRow (linearCode n3 n5 n6) ⟨2, by decide⟩ y := by
    rw [linear_dRow0, linear_dRow2, hw3, hw5, hw6]
    change k3 + k5 + k6 ≤ (n3 - k3) + k5 + (n6 - k6)
    omega
  have he3 : dRow (linearCode n3 n5 n6) ⟨0, by decide⟩ y ≤
      dRow (linearCode n3 n5 n6) ⟨3, by decide⟩ y := by
    rw [linear_dRow0, linear_dRow3, hw3, hw5, hw6]
    change k3 + k5 + k6 ≤ (n3 - k3) + (n5 - k5) + k6
    omega
  exact linY3_weights_true y ⟨0, by omega⟩ hcol ht he0 he2 he3

/-- Case 2 (same parity, n3 ≥ 2): there is a Y3 witness. -/
lemma linY3_nonempty_case2 {n3 n5 n6 : ℕ} (hn3 : n3 ≥ 2) (hpar : SameParity n3 n5 n6) :
    ∃ y : Word (n3 + n5 + n6), linY3 (linearCode n3 n5 n6) ⟨0, by omega⟩ y := by
  by_cases hn3e : Even n3
  · have hn5e : Even n5 := hpar.1.mp hn3e
    have hn6e : Even n6 := hpar.2.mp hn5e
    exact linY3_witness_even hn3e hn5e hn6e (by omega)
  · have hn3o : Odd n3 := Nat.not_even_iff_odd.mp hn3e
    have hn5o : Odd n5 := Nat.not_even_iff_odd.mp (mt hpar.1.mpr hn3e)
    have hn6o : Odd n6 := Nat.not_even_iff_odd.mp (mt hpar.2.mpr (mt hpar.1.mpr hn3e))
    have hn3ge : 3 ≤ n3 := by
      rcases hn3o with ⟨k, hk⟩
      omega
    exact linY3_witness_odd hn3o hn5o hn6o hn3ge

/-- Odd n5 + n6 makes Y3 empty. -/
lemma linY3_empty_of_odd_5_6 {n3 n5 n6 : ℕ} (h : Odd (n5 + n6))
    (y : Word (n3 + n5 + n6)) (t : Fin (n3 + n5 + n6))
    (hcol : linearCode n3 n5 n6 t = col3) :
    ¬ linY3 (linearCode n3 n5 n6) t y := by
  intro hy
  have hpar := linY3_implies_same_parity_5_6 y t hcol hy
  have hpar' : Even (n5 + n6) := Nat.even_add.mpr hpar
  rcases hpar' with ⟨r, hr⟩
  rcases h with ⟨k, hk⟩
  omega

/-- Same-parity n3,n6 makes Y5 empty. -/
lemma linY5_empty_of_same_parity_3_6 {n3 n5 n6 : ℕ} (h : Even n3 ↔ Even n6)
    (y : Word (n3 + n5 + n6)) (t : Fin (n3 + n5 + n6))
    (hcol : linearCode n3 n5 n6 t = col3) :
    ¬ linY5 (linearCode n3 n5 n6) t y := by
  intro hy
  exact (linY5_implies_not_same_parity_3_6 y t hcol hy) h

/-- `SameParity n3 (n5+1) n6` forces n3 ~ n6 and n5 !~ n6. -/
lemma same_parity_3_5p_6_implies {n3 n5 n6 : ℕ} (h : SameParity n3 (n5 + 1) n6) :
    (Even n3 ↔ Even n6) ∧ Odd (n5 + n6) := by
  rcases h with ⟨h1, h2⟩
  have h36 : Even n3 ↔ Even n6 := h1.trans h2
  have hodd56 : Odd n5 ↔ Even n6 := by
    simpa [Nat.even_add_one] using h2
  have hn56 : ¬ (Even n5 ↔ Even n6) := by
    intro he56
    by_cases hn5 : Even n5
    · have ho5 : Odd n5 := hodd56.mpr (he56.mp hn5)
      exact (Nat.not_even_iff_odd.mpr ho5) hn5
    · have ho5 : Odd n5 := Nat.not_even_iff_odd.mp hn5
      have he6 : Even n6 := hodd56.mp ho5
      exact hn5 (he56.mpr he6)
  have hodd : Odd (n5 + n6) := by
    rw [← Nat.not_even_iff_odd]
    intro he
    exact hn56 (Nat.even_add.mp he)
  exact ⟨h36, hodd⟩

/-- Case 1 of `thm:linearcompare` (Theorem 12): n3, n5+1, n6 same parity ⇒ equal. -/
lemma linear_compare_case1 {n3 n5 n6 : ℕ} (hn3 : n3 > 0)
    (h : SameParity n3 (n5 + 1) n6) :
    UniversalEqual (replaceColumn (linearCode n3 n5 n6) ⟨0, by omega⟩ col5)
      (linearCode n3 n5 n6) := by
  have hcol : (linearCode n3 n5 n6) ⟨0, by omega⟩ = col3 := by
    simp [linearCode]
    omega
  have hpar := same_parity_3_5p_6_implies h
  have h5empty : ∀ y : Word (n3 + n5 + n6),
      ¬ linY5 (linearCode n3 n5 n6) ⟨0, by omega⟩ y :=
    fun y => linY5_empty_of_same_parity_3_6 (n3 := n3) (n5 := n5) hpar.1 y
      ⟨0, by omega⟩ hcol
  have h3empty : ∀ y : Word (n3 + n5 + n6),
      ¬ linY3 (linearCode n3 n5 n6) ⟨0, by omega⟩ y :=
    fun y => linY3_empty_of_odd_5_6 (n3 := n3) (n5 := n5) hpar.2 y
      ⟨0, by omega⟩ hcol
  have hcom := lin_cumulative_no_y5 (C := linearCode n3 n5 n6)
    (C' := replaceColumn (linearCode n3 n5 n6) ⟨0, by omega⟩ col5)
    ⟨0, by omega⟩ hcol rfl
    (by intro u hu; simp [replaceColumn, hu]) h5empty
  exact hcom.2.mpr h3empty

/-- The strict version of `lin_cumulative_no_y5`: Y3 nonempty gives strictness. -/
theorem lin_strict_no_y5 {n : ℕ} (C C' : Code n) (t : Fin n)
    (hcol : C t = col3) (hcol' : C' t = col5)
    (hsame : ∀ u : Fin n, u ≠ t → C' u = C u)
    (h5 : ∀ y : Word n, ¬ linY5 C t y)
    (h3 : ∃ y : Word n, linY3 C t y) :
    UniversalStrictBetter C' C := by
  let S : Finset (Word n) := Finset.univ.filter (linY3 C t)
  have hgt : ∀ y : Word n, y ∈ S → dCode C y > dCode C' (linG1 C t y) := by
    intro y hy
    have h3' : linY3 C t y := (Finset.mem_filter.mp hy).2
    have h := (lin_y_rel_3 C C' t hcol hcol' hsame h3').2
    have h3g : gY3 (linO C) (linP C) t y := h3'
    simp [linG1, gG1, h3g]
    omega
  have heq : ∀ y : Word n, y ∉ S → dCode C y = dCode C' (linG1 C t y) := by
    intro y hy
    have h3' : ¬ linY3 C t y := by
      intro h3'
      exact hy (Finset.mem_filter.mpr ⟨by simp, h3'⟩)
    have hy14 : linY1 C t y ∨ linY2 C t y ∨ linY4 C t y := by
      rcases lin_y_mem C t y with hy' | hy' | hy' | hy' | hy'
      · exact Or.inl hy'
      · exact Or.inr (Or.inl hy')
      · exfalso; exact h3' hy'
      · exact Or.inr (Or.inr hy')
      · exfalso; exact h5 y hy'
    rcases hy14 with hy1 | hy2 | hy4
    · have h := lin_y_rel_1 C C' t hcol hcol' hsame hy1
      have hy1g : gY1 (linO C) (linP C) t y := hy1
      simp [linG1, gG1, hy1g, h.1]
    · have h1 : ¬ linY1 C t y := fun hy1 => linY1_Y2_disjoint C t y ⟨hy1, hy2⟩
      have h3'' : ¬ linY3 C t y := fun hy3 => linY2_Y3_disjoint C t y ⟨hy2, hy3⟩
      have h1g : ¬ gY1 (linO C) (linP C) t y := h1
      have h3g : ¬ gY3 (linO C) (linP C) t y := h3''
      have hg1 : linG1 C t y = flipBit t y := by
        simp [linG1, gG1, h1g, h3g]
      rw [hg1]
      exact (lin_y_rel_2 C C' t hcol hcol' hsame hy2).1
    · have h1 : ¬ linY1 C t y := fun hy1 => linY1_Y4_disjoint C t y ⟨hy1, hy4⟩
      have h3'' : ¬ linY3 C t y := fun hy3 => linY3_Y4_disjoint C t y ⟨hy3, hy4⟩
      have h1g : ¬ gY1 (linO C) (linP C) t y := h1
      have h3g : ¬ gY3 (linO C) (linP C) t y := h3''
      have hg1 : linG1 C t y = flipBit t y := by
        simp [linG1, gG1, h1g, h3g]
      rw [hg1]
      exact (lin_y_rel_4 C C' t hcol hcol' hsame hy4).2.1
  rcases h3 with ⟨y, hy⟩
  exact compare_bij_strict C C' S (linG1Equiv C t) hgt heq
    ⟨y, Finset.mem_filter.mpr ⟨by simp, hy⟩⟩

/-- Case 2 of `thm:linearcompare` (Theorem 12): n3, n5, n6 same parity ⇒ n3=1 equal,
n3 ≥ 2 strict. -/
lemma linear_compare_case2 {n3 n5 n6 : ℕ} (hn3 : n3 > 0) (h : SameParity n3 n5 n6) :
    (n3 = 1 → UniversalEqual (replaceColumn (linearCode n3 n5 n6) ⟨0, by omega⟩ col5)
      (linearCode n3 n5 n6)) ∧
    (n3 ≥ 2 → UniversalStrictBetter (replaceColumn (linearCode n3 n5 n6) ⟨0, by omega⟩ col5)
      (linearCode n3 n5 n6)) := by
  have hcol : (linearCode n3 n5 n6) ⟨0, by omega⟩ = col3 := by
    simp [linearCode]
    omega
  have h36 : Even n3 ↔ Even n6 := h.1.trans h.2
  have h5empty : ∀ y : Word (n3 + n5 + n6),
      ¬ linY5 (linearCode n3 n5 n6) ⟨0, by omega⟩ y :=
    fun y => linY5_empty_of_same_parity_3_6 (n3 := n3) (n5 := n5) h36 y
      ⟨0, by omega⟩ hcol
  have hcom := lin_cumulative_no_y5 (C := linearCode n3 n5 n6)
    (C' := replaceColumn (linearCode n3 n5 n6) ⟨0, by omega⟩ col5)
    ⟨0, by omega⟩ hcol rfl
    (by intro u hu; simp [replaceColumn, hu]) h5empty
  constructor
  · intro hn31
    apply hcom.2.mpr
    intro y hy
    exact linY3_empty_n3_1 hn31 y ⟨0, by omega⟩ hcol hy
  · intro hn3ge
    have hne : ∃ y : Word (n3 + n5 + n6), linY3 (linearCode n3 n5 n6) ⟨0, by omega⟩ y :=
      linY3_nonempty_case2 hn3ge h
    exact lin_strict_no_y5 (C := linearCode n3 n5 n6)
      (C' := replaceColumn (linearCode n3 n5 n6) ⟨0, by omega⟩ col5)
      ⟨0, by omega⟩ hcol rfl
      (by intro u hu; simp [replaceColumn, hu]) h5empty hne

/-! ## The exact λ-difference for the 3 → 5 change (paper `the:1` (Theorem 20)-type) -/

/-- α³(d) for the linear 3 → 5 change: words in Y3 at distance d. -/
def linAlpha3 {n : ℕ} (C : Code n) (t : Fin n) (d : ℕ) : ℕ :=
  (Finset.univ.filter fun y : Word n => linY3 C t y ∧ dCode C y = d).card

/-- α⁵(d) for the linear 3 → 5 change: words in Y5 at distance d. -/
def linAlpha5 {n : ℕ} (C : Code n) (t : Fin n) (d : ℕ) : ℕ :=
  (Finset.univ.filter fun y : Word n => linY5 C t y ∧ dCode C y = d).card

/-- Ψ_d := Σ_{i≤d} α³(i) − Σ_{i<d} α⁵(i) for the linear change. -/
def linPsi {n : ℕ} (C : Code n) (t : Fin n) (d : ℕ) : ℤ :=
  (∑ i ∈ Finset.Icc 1 d, (linAlpha3 C t i : ℤ)) -
    ∑ i ∈ Finset.Icc 0 (d - 1), (linAlpha5 C t i : ℤ)

/-- Flipping the bits at the type-3 and type-5 positions (paper eq. cli8). -/
def flip35 {n3 n5 n6 : ℕ} (y : Word (n3 + n5 + n6)) : Word (n3 + n5 + n6) :=
  fun t => if t.val < n3 + n5 then !(y t) else y t

lemma flip35_involutive {n3 n5 n6 : ℕ} (y : Word (n3 + n5 + n6)) :
    flip35 (flip35 y) = y := by
  funext t
  by_cases ht : t.val < n3 + n5 <;> simp [flip35, ht]

/-- Flipping the 3/5 bits complements the type-3 weight. -/
lemma w3_flip35 {n3 n5 n6 : ℕ} (y : Word (n3 + n5 + n6)) :
    w_i (linearCode n3 n5 n6) 3 (flip35 y) = n3 - w_i (linearCode n3 n5 n6) 3 y := by
  let C := linearCode n3 n5 n6
  have hfib : fiber C 3 = (Finset.univ : Finset (Fin (n3 + n5 + n6))).filter (fun t => t.val < n3) := by
    simpa [C] using linear_fiber_3 (n3 := n3) (n5 := n5) (n6 := n6)
  have hsubset : (Finset.univ.filter fun t : Fin (n3 + n5 + n6) => t.val < n3) ⊆
      Finset.univ.filter fun t : Fin (n3 + n5 + n6) => t.val < n3 + n5 := by
    intro t ht
    simp at ht ⊢
    omega
  have hones : onesOn (fiber C 3) (flip35 y) = (fiber C 3) \ onesOn (fiber C 3) y := by
    ext t
    rw [Finset.mem_sdiff]
    constructor
    · intro ht
      have htC : t ∈ fiber C 3 := (Finset.mem_filter.mp ht).1
      have hflip : flip35 y t = true := (Finset.mem_filter.mp ht).2
      have ht3 : t.val < n3 := by
        have hmem : t ∈ (Finset.univ.filter fun t : Fin (n3 + n5 + n6) => t.val < n3) := by
          simpa [hfib] using htC
        exact (Finset.mem_filter.mp hmem).2
      have htflip : t.val < n3 + n5 := by omega
      constructor
      · exact htC
      · intro hty
        have hy : y t = true := (Finset.mem_filter.mp hty).2
        have : flip35 y t = !(y t) := by simp [flip35, htflip]
        simp [this, hy] at hflip
    · intro ht
      have htC : t ∈ fiber C 3 := ht.1
      have htny : t ∉ onesOn (fiber C 3) y := ht.2
      have ht3 : t.val < n3 := by
        have hmem : t ∈ (Finset.univ.filter fun t : Fin (n3 + n5 + n6) => t.val < n3) := by
          simpa [hfib] using htC
        exact (Finset.mem_filter.mp hmem).2
      have htflip : t.val < n3 + n5 := by omega
      have hy : y t = false := by
        by_contra h
        have hyt : y t = true := by
          cases hb : y t
          · exfalso; exact h hb
          · rfl
        exact htny (Finset.mem_filter.mpr ⟨htC, hyt⟩)
      exact Finset.mem_filter.mpr ⟨htC, by simp [flip35, htflip, hy]⟩
  have hcard := congrArg Finset.card hones
  rw [← w_i_eq_card_onesOn] at hcard
  -- hcard : |onesOn C3 (flip35 y)| = |C3 \ onesOn C3 y|
  have hcard' : ((fiber C 3) \ onesOn (fiber C 3) y).card =
      (fiber C 3).card - (onesOn (fiber C 3) y).card := by
    rw [Finset.card_sdiff]
    have hsub2 : onesOn (fiber C 3) y ⊆ fiber C 3 := by
      intro t ht
      exact (Finset.mem_filter.mp ht).1
    have heq : onesOn (fiber C 3) y ∩ fiber C 3 = onesOn (fiber C 3) y :=
      Finset.inter_eq_left.mpr hsub2
    rw [heq]
  rw [hcard'] at hcard
  have hcount : (fiber C 3).card = n3 := by
    simpa [C] using (fiber_card_eq_count (linearCode n3 n5 n6) 3).trans
      (linear_count_3 (n3 := n3) (n5 := n5) (n6 := n6))
  rw [w_i_eq_card_onesOn, hcount] at hcard
  exact hcard

/-- Flipping the 3/5 bits complements the type-5 weight. -/
lemma w5_flip35 {n3 n5 n6 : ℕ} (y : Word (n3 + n5 + n6)) :
    w_i (linearCode n3 n5 n6) 5 (flip35 y) = n5 - w_i (linearCode n3 n5 n6) 5 y := by
  let C := linearCode n3 n5 n6
  have hfib : fiber C 5 = (Finset.univ : Finset (Fin (n3 + n5 + n6))).filter
      (fun t => n3 ≤ t.val ∧ t.val < n3 + n5) := by
    simpa [C] using linear_fiber_5 (n3 := n3) (n5 := n5) (n6 := n6)
  have hsubset : (Finset.univ.filter fun t : Fin (n3 + n5 + n6) => n3 ≤ t.val ∧ t.val < n3 + n5) ⊆
      Finset.univ.filter fun t : Fin (n3 + n5 + n6) => t.val < n3 + n5 := by
    intro t ht
    simp at ht ⊢
    omega
  have hones : onesOn (fiber C 5) (flip35 y) = (fiber C 5) \ onesOn (fiber C 5) y := by
    ext t
    rw [Finset.mem_sdiff]
    constructor
    · intro ht
      have htC : t ∈ fiber C 5 := (Finset.mem_filter.mp ht).1
      have hflip : flip35 y t = true := (Finset.mem_filter.mp ht).2
      have ht5 : n3 ≤ t.val ∧ t.val < n3 + n5 := by
        have hmem : t ∈ (Finset.univ.filter fun t : Fin (n3 + n5 + n6) => n3 ≤ t.val ∧ t.val < n3 + n5) := by
          simpa [hfib] using htC
        exact (Finset.mem_filter.mp hmem).2
      have htflip : t.val < n3 + n5 := ht5.2
      constructor
      · exact htC
      · intro hty
        have hy : y t = true := (Finset.mem_filter.mp hty).2
        have : flip35 y t = !(y t) := by simp [flip35, htflip]
        simp [this, hy] at hflip
    · intro ht
      have htC : t ∈ fiber C 5 := ht.1
      have htny : t ∉ onesOn (fiber C 5) y := ht.2
      have ht5 : n3 ≤ t.val ∧ t.val < n3 + n5 := by
        have hmem : t ∈ (Finset.univ.filter fun t : Fin (n3 + n5 + n6) => n3 ≤ t.val ∧ t.val < n3 + n5) := by
          simpa [hfib] using htC
        exact (Finset.mem_filter.mp hmem).2
      have htflip : t.val < n3 + n5 := ht5.2
      have hy : y t = false := by
        by_contra h
        have hyt : y t = true := by
          cases hb : y t
          · exfalso; exact h hb
          · rfl
        exact htny (Finset.mem_filter.mpr ⟨htC, hyt⟩)
      exact Finset.mem_filter.mpr ⟨htC, by simp [flip35, htflip, hy]⟩
  have hcard := congrArg Finset.card hones
  rw [← w_i_eq_card_onesOn] at hcard
  have hcard' : ((fiber C 5) \ onesOn (fiber C 5) y).card =
      (fiber C 5).card - (onesOn (fiber C 5) y).card := by
    rw [Finset.card_sdiff]
    have hsub2 : onesOn (fiber C 5) y ⊆ fiber C 5 := by
      intro t ht
      exact (Finset.mem_filter.mp ht).1
    have heq : onesOn (fiber C 5) y ∩ fiber C 5 = onesOn (fiber C 5) y :=
      Finset.inter_eq_left.mpr hsub2
    rw [heq]
  rw [hcard'] at hcard
  have hcount : (fiber C 5).card = n5 := by
    simpa [C] using (fiber_card_eq_count (linearCode n3 n5 n6) 5).trans
      (linear_count_5 (n3 := n3) (n5 := n5) (n6 := n6))
  rw [w_i_eq_card_onesOn, hcount] at hcard
  exact hcard

/-- Flipping the 3/5 bits leaves the type-6 weight unchanged. -/
lemma w6_flip35 {n3 n5 n6 : ℕ} (y : Word (n3 + n5 + n6)) :
    w_i (linearCode n3 n5 n6) 6 (flip35 y) = w_i (linearCode n3 n5 n6) 6 y := by
  let C := linearCode n3 n5 n6
  have hones : onesOn (fiber C 6) (flip35 y) = onesOn (fiber C 6) y := by
    ext t
    constructor
    · intro ht
      have htC : t ∈ fiber C 6 := (Finset.mem_filter.mp ht).1
      have ht6 : n3 + n5 ≤ t.val := by
        have hmem : t ∈ (Finset.univ.filter fun t : Fin (n3 + n5 + n6) => n3 + n5 ≤ t.val) := by
          simpa [C, linear_fiber_6] using htC
        exact (Finset.mem_filter.mp hmem).2
      have hnot : ¬ t.val < n3 + n5 := by omega
      have hy : y t = true := by
        have hflip : flip35 y t = true := (Finset.mem_filter.mp ht).2
        simp [flip35, hnot] at hflip
        exact hflip
      exact Finset.mem_filter.mpr ⟨htC, hy⟩
    · intro ht
      have htC : t ∈ fiber C 6 := (Finset.mem_filter.mp ht).1
      have ht6 : n3 + n5 ≤ t.val := by
        have hmem : t ∈ (Finset.univ.filter fun t : Fin (n3 + n5 + n6) => n3 + n5 ≤ t.val) := by
          simpa [C, linear_fiber_6] using htC
        exact (Finset.mem_filter.mp hmem).2
      have hnot : ¬ t.val < n3 + n5 := by omega
      have hy : y t = true := (Finset.mem_filter.mp ht).2
      exact Finset.mem_filter.mpr ⟨htC, by simp [flip35, hnot, hy]⟩
  rw [w_i_eq_card_onesOn, w_i_eq_card_onesOn, hones]

/-- flip35 swaps rows 0 and 3 of the linear code. -/
lemma dRow_flip35_03 {n3 n5 n6 : ℕ} (y : Word (n3 + n5 + n6)) :
    dRow (linearCode n3 n5 n6) ⟨0, by decide⟩ (flip35 y) =
      dRow (linearCode n3 n5 n6) ⟨3, by decide⟩ y := by
  have hw3le : w_i (linearCode n3 n5 n6) 3 y ≤ n3 := by
    simpa [linear_count_3] using (w_i_le_count (linearCode n3 n5 n6) 3 y)
  have hw5le : w_i (linearCode n3 n5 n6) 5 y ≤ n5 := by
    simpa [linear_count_5] using (w_i_le_count (linearCode n3 n5 n6) 5 y)
  have hw6le : w_i (linearCode n3 n5 n6) 6 y ≤ n6 := by
    simpa [linear_count_6] using (w_i_le_count (linearCode n3 n5 n6) 6 y)
  rw [linear_dRow0 (flip35 y), linear_dRow3 y, w3_flip35, w5_flip35, w6_flip35]

/-- flip35 swaps rows 1 and 2 of the linear code. -/
lemma dRow_flip35_12 {n3 n5 n6 : ℕ} (y : Word (n3 + n5 + n6)) :
    dRow (linearCode n3 n5 n6) ⟨1, by decide⟩ (flip35 y) =
      dRow (linearCode n3 n5 n6) ⟨2, by decide⟩ y := by
  have hw3le : w_i (linearCode n3 n5 n6) 3 y ≤ n3 := by
    simpa [linear_count_3] using (w_i_le_count (linearCode n3 n5 n6) 3 y)
  have hw5le : w_i (linearCode n3 n5 n6) 5 y ≤ n5 := by
    simpa [linear_count_5] using (w_i_le_count (linearCode n3 n5 n6) 5 y)
  have hw6le : w_i (linearCode n3 n5 n6) 6 y ≤ n6 := by
    simpa [linear_count_6] using (w_i_le_count (linearCode n3 n5 n6) 6 y)
  rw [linear_dRow1 (flip35 y), linear_dRow2 y, w3_flip35, w5_flip35, w6_flip35]
  omega

/-- flip35 preserves the O-minimum. -/
lemma linO_flip35 {n3 n5 n6 : ℕ} (y : Word (n3 + n5 + n6)) :
    linO (linearCode n3 n5 n6) (flip35 y) = linO (linearCode n3 n5 n6) y := by
  unfold linO
  change min (dRow (linearCode n3 n5 n6) ⟨0, by decide⟩ (flip35 y))
      (dRow (linearCode n3 n5 n6) ⟨3, by decide⟩ (flip35 y)) =
    min (dRow (linearCode n3 n5 n6) ⟨0, by decide⟩ y)
      (dRow (linearCode n3 n5 n6) ⟨3, by decide⟩ y)
  rw [linear_dRow0 (flip35 y), linear_dRow3 (flip35 y), linear_dRow0 y, linear_dRow3 y,
    w3_flip35, w5_flip35, w6_flip35]
  have hw3le : w_i (linearCode n3 n5 n6) 3 y ≤ n3 := by
    simpa [linear_count_3] using (w_i_le_count (linearCode n3 n5 n6) 3 y)
  have hw5le : w_i (linearCode n3 n5 n6) 5 y ≤ n5 := by
    simpa [linear_count_5] using (w_i_le_count (linearCode n3 n5 n6) 5 y)
  rw [Nat.sub_sub_self hw3le]
  rw [Nat.sub_sub_self hw5le]
  rw [min_comm]

lemma linP_flip35 {n3 n5 n6 : ℕ} (y : Word (n3 + n5 + n6)) :
    linP (linearCode n3 n5 n6) (flip35 y) = linP (linearCode n3 n5 n6) y := by
  unfold linP
  change min (dRow (linearCode n3 n5 n6) ⟨1, by decide⟩ (flip35 y))
      (dRow (linearCode n3 n5 n6) ⟨2, by decide⟩ (flip35 y)) =
    min (dRow (linearCode n3 n5 n6) ⟨1, by decide⟩ y)
      (dRow (linearCode n3 n5 n6) ⟨2, by decide⟩ y)
  rw [linear_dRow1 (flip35 y), linear_dRow2 (flip35 y), linear_dRow1 y, linear_dRow2 y,
    w3_flip35, w5_flip35, w6_flip35]
  have hw3le : w_i (linearCode n3 n5 n6) 3 y ≤ n3 := by
    simpa [linear_count_3] using (w_i_le_count (linearCode n3 n5 n6) 3 y)
  have hw5le : w_i (linearCode n3 n5 n6) 5 y ≤ n5 := by
    simpa [linear_count_5] using (w_i_le_count (linearCode n3 n5 n6) 5 y)
  rw [Nat.sub_sub_self hw5le]
  rw [Nat.sub_sub_self hw3le]
  rw [min_comm]

lemma dCode_flip35 {n3 n5 n6 : ℕ} (y : Word (n3 + n5 + n6)) :
    dCode (linearCode n3 n5 n6) (flip35 y) = dCode (linearCode n3 n5 n6) y := by
  rw [lin_dCode_eq_min, linO_flip35, linP_flip35]
  rw [← lin_dCode_eq_min]

/-- flip35 commutes with flipping the first column. -/
lemma flipBit_comm_flip35 {n3 n5 n6 : ℕ} (t : Fin (n3 + n5 + n6))
    (ht : t.val < n3 + n5) (y : Word (n3 + n5 + n6)) :
    flipBit t (flip35 y) = flip35 (flipBit t y) := by
  funext u
  by_cases hu : u = t
  · subst u
    simp [flipBit, flip35, ht]
  · by_cases hu35 : u.val < n3 + n5
    · simp [flipBit, flip35, hu, hu35]
    · simp [flipBit, flip35, hu, hu35]

/-- flip35 preserves membership in Y3. -/
lemma linY3_flip35 {n3 n5 n6 : ℕ} (y : Word (n3 + n5 + n6))
    (t : Fin (n3 + n5 + n6)) (ht : t.val < n3 + n5) :
    linY3 (linearCode n3 n5 n6) t (flip35 y) ↔ linY3 (linearCode n3 n5 n6) t y := by
  unfold linY3 gY3
  simp [flipBit_comm_flip35 t ht y, linO_flip35, linP_flip35]

/-- flip35 preserves membership in Y5. -/
lemma linY5_flip35 {n3 n5 n6 : ℕ} (y : Word (n3 + n5 + n6))
    (t : Fin (n3 + n5 + n6)) (ht : t.val < n3 + n5) :
    linY5 (linearCode n3 n5 n6) t (flip35 y) ↔ linY5 (linearCode n3 n5 n6) t y := by
  unfold linY5 gY5
  simp [flipBit_comm_flip35 t ht y, linO_flip35, linP_flip35]

/-- α³(d) is twice the number of Y3 witnesses with `y t = true` (eq. cli8). -/
lemma linAlpha3_eq_two_mul {n3 n5 n6 : ℕ} (d : ℕ) (hn3 : 0 < n3) :
    linAlpha3 (linearCode n3 n5 n6) ⟨0, by omega⟩ d =
      2 * (Finset.univ.filter fun y : Word (n3 + n5 + n6) =>
        linY3 (linearCode n3 n5 n6) ⟨0, by omega⟩ y ∧
        dCode (linearCode n3 n5 n6) y = d ∧ y ⟨0, by omega⟩ = true).card := by
  let C := linearCode n3 n5 n6
  let t0 : Fin (n3 + n5 + n6) := ⟨0, by omega⟩
  have hA : Finset.univ.filter (fun y : Word (n3 + n5 + n6) => linY3 C t0 y ∧ dCode C y = d) =
      (Finset.univ.filter fun y => linY3 C t0 y ∧ dCode C y = d ∧ y t0 = true) ∪
      (Finset.univ.filter fun y => linY3 C t0 y ∧ dCode C y = d ∧ y t0 = false) := by
    ext y
    constructor
    · intro hy
      have hY := (Finset.mem_filter.mp hy).2.1
      have hd := (Finset.mem_filter.mp hy).2.2
      by_cases hyt : y t0
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨by simp, ⟨hY, hd, hyt⟩⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨by simp, ⟨hY, hd, by simpa using hyt⟩⟩)
    · intro hy
      rcases (Finset.mem_union.mp hy) with hy' | hy'
      · exact Finset.mem_filter.mpr ⟨by simp, (Finset.mem_filter.mp hy').2.1, (Finset.mem_filter.mp hy').2.2.1⟩
      · exact Finset.mem_filter.mpr ⟨by simp, (Finset.mem_filter.mp hy').2.1, (Finset.mem_filter.mp hy').2.2.1⟩
  have hdisj : Disjoint
      (Finset.univ.filter fun y : Word (n3 + n5 + n6) => linY3 C t0 y ∧ dCode C y = d ∧ y t0 = true)
      (Finset.univ.filter fun y : Word (n3 + n5 + n6) => linY3 C t0 y ∧ dCode C y = d ∧ y t0 = false) := by
    rw [Finset.disjoint_filter]
    intro y _ h1 h2
    have hbad : (true : Bool) = false := h1.2.2.symm.trans h2.2.2
    exact Bool.noConfusion hbad
  unfold linAlpha3
  have hA' : (Finset.univ.filter fun y : Word (n3 + n5 + n6) => linY3 C t0 y ∧ dCode C y = d) =
      (Finset.univ.filter fun y => linY3 C t0 y ∧ dCode C y = d ∧ y t0 = true) ∪
      (Finset.univ.filter fun y => linY3 C t0 y ∧ dCode C y = d ∧ y t0 = false) := hA
  have hcardA : (Finset.univ.filter fun y : Word (n3 + n5 + n6) => linY3 C t0 y ∧ dCode C y = d).card =
      (Finset.univ.filter fun y => linY3 C t0 y ∧ dCode C y = d ∧ y t0 = true).card +
        (Finset.univ.filter fun y => linY3 C t0 y ∧ dCode C y = d ∧ y t0 = false).card := by
    rw [hA', Finset.card_union_of_disjoint hdisj]
  have hbij : (Finset.univ.filter fun y : Word (n3 + n5 + n6) => linY3 C t0 y ∧ dCode C y = d ∧ y t0 = false).card =
      (Finset.univ.filter fun y : Word (n3 + n5 + n6) => linY3 C t0 y ∧ dCode C y = d ∧ y t0 = true).card := by
    apply Finset.card_bij (fun y hy => flip35 y)
    · intro y hy
      rcases (Finset.mem_filter.mp hy).2 with ⟨hY, hd, hytf⟩
      have ht03 : t0.val < n3 + n5 := by
        simp [t0]
        omega
      have hY' : linY3 C t0 (flip35 y) := by
        simpa [C] using (linY3_flip35 (n3 := n3) (n5 := n5) (n6 := n6) y t0 ht03).2 hY
      have hd' : dCode C (flip35 y) = d := by
        simpa [C] using (dCode_flip35 (n3 := n3) (n5 := n5) (n6 := n6) y).trans hd
      have hyt' : flip35 y t0 = true := by
        simp [flip35, ht03, t0, hytf]
      exact Finset.mem_filter.mpr ⟨by simp, ⟨hY', hd', hyt'⟩⟩
    · intro a ha b hb hab
      have hfi : flip35 (flip35 a) = a := flip35_involutive a
      have hfj : flip35 (flip35 b) = b := flip35_involutive b
      calc
        a = flip35 (flip35 a) := hfi.symm
        _ = flip35 (flip35 b) := by rw [hab]
        _ = b := hfj
    · intro z hz
      refine ⟨flip35 z, ?_, ?_⟩
      · rcases (Finset.mem_filter.mp hz).2 with ⟨hY, hd, hyt⟩
        have ht03 : t0.val < n3 + n5 := by
          simp [t0]
          omega
        have hY' : linY3 C t0 (flip35 z) := by
          simpa [C] using (linY3_flip35 (n3 := n3) (n5 := n5) (n6 := n6) z t0 ht03).2 hY
        have hd' : dCode C (flip35 z) = d := by
          simpa [C] using (dCode_flip35 (n3 := n3) (n5 := n5) (n6 := n6) z).trans hd
        have hyt' : flip35 z t0 = false := by
          simp [flip35, ht03, t0, hyt]
        exact Finset.mem_filter.mpr ⟨by simp, ⟨hY', hd', hyt'⟩⟩
      · exact flip35_involutive z
  rw [hcardA, hbij]
  ring

/-- α⁵(d) is twice the number of Y5 witnesses with `y t = false` (eq. cli9). -/
lemma linAlpha5_eq_two_mul {n3 n5 n6 : ℕ} (d : ℕ) (hn3 : 0 < n3) :
    linAlpha5 (linearCode n3 n5 n6) ⟨0, by omega⟩ d =
      2 * (Finset.univ.filter fun y : Word (n3 + n5 + n6) =>
        linY5 (linearCode n3 n5 n6) ⟨0, by omega⟩ y ∧
        dCode (linearCode n3 n5 n6) y = d ∧ y ⟨0, by omega⟩ = false).card := by
  let C := linearCode n3 n5 n6
  let t0 : Fin (n3 + n5 + n6) := ⟨0, by omega⟩
  have hA : Finset.univ.filter (fun y : Word (n3 + n5 + n6) => linY5 C t0 y ∧ dCode C y = d) =
      (Finset.univ.filter fun y => linY5 C t0 y ∧ dCode C y = d ∧ y t0 = false) ∪
      (Finset.univ.filter fun y => linY5 C t0 y ∧ dCode C y = d ∧ y t0 = true) := by
    ext y
    constructor
    · intro hy
      have hY := (Finset.mem_filter.mp hy).2.1
      have hd := (Finset.mem_filter.mp hy).2.2
      by_cases hyt : y t0
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨by simp, ⟨hY, hd, hyt⟩⟩)
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨by simp, ⟨hY, hd, by simpa using hyt⟩⟩)
    · intro hy
      rcases (Finset.mem_union.mp hy) with hy' | hy'
      · exact Finset.mem_filter.mpr ⟨by simp, (Finset.mem_filter.mp hy').2.1, (Finset.mem_filter.mp hy').2.2.1⟩
      · exact Finset.mem_filter.mpr ⟨by simp, (Finset.mem_filter.mp hy').2.1, (Finset.mem_filter.mp hy').2.2.1⟩
  have hdisj : Disjoint
      (Finset.univ.filter fun y : Word (n3 + n5 + n6) => linY5 C t0 y ∧ dCode C y = d ∧ y t0 = false)
      (Finset.univ.filter fun y : Word (n3 + n5 + n6) => linY5 C t0 y ∧ dCode C y = d ∧ y t0 = true) := by
    rw [Finset.disjoint_filter]
    intro y _ h1 h2
    have hbad : (false : Bool) = true := h1.2.2.symm.trans h2.2.2
    exact Bool.noConfusion hbad
  unfold linAlpha5
  have hA' : (Finset.univ.filter fun y : Word (n3 + n5 + n6) => linY5 C t0 y ∧ dCode C y = d) =
      (Finset.univ.filter fun y => linY5 C t0 y ∧ dCode C y = d ∧ y t0 = false) ∪
      (Finset.univ.filter fun y => linY5 C t0 y ∧ dCode C y = d ∧ y t0 = true) := hA
  have hcardA : (Finset.univ.filter fun y : Word (n3 + n5 + n6) => linY5 C t0 y ∧ dCode C y = d).card =
      (Finset.univ.filter fun y => linY5 C t0 y ∧ dCode C y = d ∧ y t0 = false).card +
        (Finset.univ.filter fun y => linY5 C t0 y ∧ dCode C y = d ∧ y t0 = true).card := by
    rw [hA', Finset.card_union_of_disjoint hdisj]
  have hbij : (Finset.univ.filter fun y : Word (n3 + n5 + n6) => linY5 C t0 y ∧ dCode C y = d ∧ y t0 = true).card =
      (Finset.univ.filter fun y : Word (n3 + n5 + n6) => linY5 C t0 y ∧ dCode C y = d ∧ y t0 = false).card := by
    apply Finset.card_bij (fun y hy => flip35 y)
    · intro y hy
      rcases (Finset.mem_filter.mp hy).2 with ⟨hY, hd, hyt⟩
      have ht03 : t0.val < n3 + n5 := by
        simp [t0]
        omega
      have hY' : linY5 C t0 (flip35 y) := by
        simpa [C] using (linY5_flip35 (n3 := n3) (n5 := n5) (n6 := n6) y t0 ht03).2 hY
      have hd' : dCode C (flip35 y) = d := by
        simpa [C] using (dCode_flip35 (n3 := n3) (n5 := n5) (n6 := n6) y).trans hd
      have hyt' : flip35 y t0 = false := by
        simp [flip35, ht03, t0, hyt]
      exact Finset.mem_filter.mpr ⟨by simp, ⟨hY', hd', hyt'⟩⟩
    · intro a ha b hb hab
      have hfi : flip35 (flip35 a) = a := flip35_involutive a
      have hfj : flip35 (flip35 b) = b := flip35_involutive b
      calc
        a = flip35 (flip35 a) := hfi.symm
        _ = flip35 (flip35 b) := by rw [hab]
        _ = b := hfj
    · intro z hz
      refine ⟨flip35 z, ?_, ?_⟩
      · rcases (Finset.mem_filter.mp hz).2 with ⟨hY, hd, hytf⟩
        have ht03 : t0.val < n3 + n5 := by
          simp [t0]
          omega
        have hY' : linY5 C t0 (flip35 z) := by
          simpa [C] using (linY5_flip35 (n3 := n3) (n5 := n5) (n6 := n6) z t0 ht03).2 hY
        have hd' : dCode C (flip35 z) = d := by
          simpa [C] using (dCode_flip35 (n3 := n3) (n5 := n5) (n6 := n6) z).trans hd
        have hyt' : flip35 z t0 = true := by
          simp [flip35, ht03, t0, hytf]
        exact Finset.mem_filter.mpr ⟨by simp, ⟨hY', hd', hyt'⟩⟩
      · exact flip35_involutive z
  rw [hcardA, hbij]
  ring

/-- Closed form of α³(d+1) for the linear 3 → 5 change (paper eq. cli3).
With the case-3 parity `n5+n6 = 2k`, `n3+n6 = 2m+1` and
`n5 ≤ min n3 n6`, the exact summation range from eq. cli7 is
`d+1−m ≤ w5 ≤ n5+m−d−1` (the paper writes `d−(n3+n6−3)/2 … n5−d+(n3+n6−3)/2`,
which differs by one — see CompanionNote).  The hypothesis `hkd : k ≤ d` is
the paper's case split: α³(d) = 0 when d < (n5+n6)/2, so eq. cli3 is only
applied for d ≥ (n5+n6)/2 (where the binomial `(n3−1).choose (d−k)` has a
non-vanishing w3 index). -/
lemma linAlpha3_closed {n3 n5 n6 d k m : ℕ} (hn3 : 0 < n3)
    (hpar : Even (n5 + n6)) (hk : n5 + n6 = 2 * k) (hm : n3 + n6 = 2 * m + 1)
    (hge : 2 * (d + 1) ≥ n3 + n5) (hn56 : n5 ≤ n6) (hn53 : n5 ≤ n3)
    (hmd : m ≤ d + 1) (hln : d + 1 ≤ n5 + m) (hkd : k ≤ d) :
    linAlpha3 (linearCode n3 n5 n6) ⟨0, by omega⟩ (d + 1) =
      2 * (∑ w5 ∈ Finset.Icc (d + 1 - m) (n5 + m - (d + 1)),
        Nat.choose (n3 - 1) (d - k) *
          (Nat.choose n5 w5 * Nat.choose n6 (k - w5))) := by
  have hkdiv : (n5 + n6) / 2 = k := by
    rw [hk, Nat.mul_div_right k (by decide : 0 < 2)]
  rw [linAlpha3_eq_two_mul (d + 1) hn3]
  -- decompose the Y3-with-`y 0 = true` filter over the w5 range
  have hrange (y : Word (n3 + n5 + n6))
      (hw : 2 * w_i (linearCode n3 n5 n6) 5 y ≥ 2 * (d + 1) - n3 - n6 ∧
        2 * w_i (linearCode n3 n5 n6) 5 y ≤ n3 + 2 * n5 + n6 - 2 * (d + 1)) :
      d + 1 - m ≤ w_i (linearCode n3 n5 n6) 5 y ∧
        w_i (linearCode n3 n5 n6) 5 y ≤ n5 + m - (d + 1) := by
    constructor <;> omega
  have hfilter :
      (Finset.univ.filter fun y : Word (n3 + n5 + n6) =>
        linY3 (linearCode n3 n5 n6) ⟨0, by omega⟩ y ∧
        dCode (linearCode n3 n5 n6) y = d + 1 ∧ y ⟨0, by omega⟩ = true) =
      Finset.biUnion (Finset.Icc (d + 1 - m) (n5 + m - (d + 1))) fun w5 =>
        Finset.univ.filter fun y : Word (n3 + n5 + n6) =>
          w_i (linearCode n3 n5 n6) 3 y = d + 1 - k ∧
            w_i (linearCode n3 n5 n6) 5 y = w5 ∧
            w_i (linearCode n3 n5 n6) 6 y = k - w5 ∧
            y ⟨0, by omega⟩ = true := by
    ext y
    constructor
    · intro hy
      rcases (Finset.mem_filter.mp hy).2 with ⟨hY, hd, hyt⟩
      have hw := (linY3_true_iff' y hn3 hpar hyt hd hge hn56).1 hY
      have hr := hrange y ⟨hw.2.2.1, hw.2.2.2⟩
      refine Finset.mem_biUnion.mpr ⟨w_i (linearCode n3 n5 n6) 5 y, ?_, ?_⟩
      · exact Finset.mem_Icc.mpr hr
      · have hw3 : w_i (linearCode n3 n5 n6) 3 y = d + 1 - k := by
          simpa [hkdiv] using hw.1
        have hw6 : w_i (linearCode n3 n5 n6) 6 y = k - w_i (linearCode n3 n5 n6) 5 y := by
          simpa [hkdiv] using hw.2.1
        exact Finset.mem_filter.mpr ⟨by simp, ⟨hw3, rfl, hw6, hyt⟩⟩
    · intro hy
      rcases Finset.mem_biUnion.mp hy with ⟨w5, hw5, hyw⟩
      rcases (Finset.mem_filter.mp hyw).2 with ⟨hw3, hw5eq, hw6, hyt⟩
      have hd : dCode (linearCode n3 n5 n6) y = d + 1 := by
        have hw3C : w_i (linearCode n3 n5 n6) 3 y = d + 1 - k := hw3
        have hw5C : w_i (linearCode n3 n5 n6) 5 y = w5 := hw5eq
        have hw6C : w_i (linearCode n3 n5 n6) 6 y = k - w5 := hw6
        have hw5k : w5 ≤ k := by
          have hw5u : w5 ≤ n5 + m - (d + 1) := (Finset.mem_Icc.mp hw5).2
          have huk : n5 + m - (d + 1) ≤ k := by
            have h1 : n5 + 2 * m - 2 * (d + 1) ≤ n6 := by omega
            have h1' : 2 * (n5 + m) - 2 * (d + 1) ≤ n5 + n6 := by omega
            have h1'' : n5 + m - (d + 1) ≤ k := by
              rw [hk] at h1'
              omega
            exact h1''
          omega
        have hw5le5 : w5 ≤ n5 := by
          have hw5u : w5 ≤ n5 + m - (d + 1) := (Finset.mem_Icc.mp hw5).2
          have hmd' : m ≤ d + 1 := hmd
          omega
        have hk6le : k - w5 ≤ n6 := by
          have hkn6 : k ≤ n6 := by omega
          omega
        have hd0 : dRow (linearCode n3 n5 n6) ⟨0, by decide⟩ y = d + 1 := by
          change dRow (linearCode n3 n5 n6) ⟨0, by omega⟩ y = d + 1
          have hdr : dRow (linearCode n3 n5 n6) ⟨0, by omega⟩ y =
              w_i (linearCode n3 n5 n6) 3 y + w_i (linearCode n3 n5 n6) 5 y +
                w_i (linearCode n3 n5 n6) 6 y := by
            simpa using (linear_dRow0 (n3 := n3) (n5 := n5) (n6 := n6) y)
          rw [hdr, hw3C, hw5C, hw6C]
          omega
        have hd1 : dRow (linearCode n3 n5 n6) ⟨1, by decide⟩ y = d + 1 := by
          change dRow (linearCode n3 n5 n6) ⟨1, by omega⟩ y = d + 1
          have hdr : dRow (linearCode n3 n5 n6) ⟨1, by omega⟩ y =
              w_i (linearCode n3 n5 n6) 3 y + (n5 - w_i (linearCode n3 n5 n6) 5 y) +
                (n6 - w_i (linearCode n3 n5 n6) 6 y) := by
            simpa using (linear_dRow1 (n3 := n3) (n5 := n5) (n6 := n6) y)
          rw [hdr, hw3C, hw5C, hw6C]
          omega
        have hd2 : d + 1 ≤ dRow (linearCode n3 n5 n6) ⟨2, by decide⟩ y := by
          have hw5g : d + 1 - m ≤ w5 := (Finset.mem_Icc.mp hw5).1
          have hd2' : dRow (linearCode n3 n5 n6) ⟨2, by omega⟩ y =
              (n3 - w_i (linearCode n3 n5 n6) 3 y) +
                w_i (linearCode n3 n5 n6) 5 y +
                  (n6 - w_i (linearCode n3 n5 n6) 6 y) := by
            simpa using (linear_dRow2 (n3 := n3) (n5 := n5) (n6 := n6) y)
          rw [hd2', hw3C, hw5C, hw6C]
          omega
        have hd3 : d + 1 ≤ dRow (linearCode n3 n5 n6) ⟨3, by decide⟩ y := by
          have hw5u : w5 ≤ n5 + m - (d + 1) := (Finset.mem_Icc.mp hw5).2
          have hd3' : dRow (linearCode n3 n5 n6) ⟨3, by omega⟩ y =
              (n3 - w_i (linearCode n3 n5 n6) 3 y) +
                (n5 - w_i (linearCode n3 n5 n6) 5 y) +
                  w_i (linearCode n3 n5 n6) 6 y := by
            simpa using (linear_dRow3 (n3 := n3) (n5 := n5) (n6 := n6) y)
          rw [hd3', hw3C, hw5C, hw6C]
          omega
        have hO : linO (linearCode n3 n5 n6) y = d + 1 := by
          have hmin : min (dRow (linearCode n3 n5 n6) ⟨0, by decide⟩ y)
              (dRow (linearCode n3 n5 n6) ⟨3, by decide⟩ y) = d + 1 := by
            rw [hd0, min_eq_left hd3]
          change min (dRow (linearCode n3 n5 n6) ⟨0, by decide⟩ y)
              (dRow (linearCode n3 n5 n6) ⟨3, by decide⟩ y) = d + 1
          exact hmin
        have hP : linP (linearCode n3 n5 n6) y = d + 1 := by
          have hmin : min (dRow (linearCode n3 n5 n6) ⟨1, by decide⟩ y)
              (dRow (linearCode n3 n5 n6) ⟨2, by decide⟩ y) = d + 1 := by
            rw [hd1, min_eq_left hd2]
          change min (dRow (linearCode n3 n5 n6) ⟨1, by decide⟩ y)
              (dRow (linearCode n3 n5 n6) ⟨2, by decide⟩ y) = d + 1
          exact hmin
        rw [lin_dCode_eq_min (linearCode n3 n5 n6) y, hO, hP]
        omega
      have hY : linY3 (linearCode n3 n5 n6) ⟨0, by omega⟩ y := by
        apply (linY3_true_iff' y hn3 hpar hyt hd hge hn56).2
        constructor
        · simpa [hkdiv] using hw3
        · constructor
          · simpa [hkdiv, hw5eq] using hw6
          · constructor
            · have hw5ge : d + 1 - m ≤ w5 := (Finset.mem_Icc.mp hw5).1
              have hw5ge' : 2 * w_i (linearCode n3 n5 n6) 5 y ≥ 2 * (d + 1) - n3 - n6 := by
                have hmm : 2 * (d + 1) - n3 - n6 = 2 * (d + 1) - (2 * m + 1) := by omega
                rw [hmm]
                omega
              exact hw5ge'
            · have hw5le : w5 ≤ n5 + m - (d + 1) := (Finset.mem_Icc.mp hw5).2
              have hw5le' : 2 * w_i (linearCode n3 n5 n6) 5 y ≤
                  n3 + 2 * n5 + n6 - 2 * (d + 1) := by
                have hmm : n3 + 2 * n5 + n6 - 2 * (d + 1) =
                    (2 * m + 1) + 2 * n5 - 2 * (d + 1) := by omega
                rw [hmm]
                omega
              exact hw5le'
      exact Finset.mem_filter.mpr ⟨by simp, ⟨hY, hd, hyt⟩⟩
  have hdisj : ((Finset.Icc (d + 1 - m) (n5 + m - (d + 1)) : Set ℕ).PairwiseDisjoint fun w5 =>
      Finset.univ.filter fun y : Word (n3 + n5 + n6) =>
        w_i (linearCode n3 n5 n6) 3 y = d + 1 - k ∧
        w_i (linearCode n3 n5 n6) 5 y = w5 ∧
        w_i (linearCode n3 n5 n6) 6 y = k - w5 ∧
        y ⟨0, by omega⟩ = true) := by
    intro a ha b hb hab
    change Disjoint
      (Finset.univ.filter fun y : Word (n3 + n5 + n6) =>
        w_i (linearCode n3 n5 n6) 3 y = d + 1 - k ∧
          w_i (linearCode n3 n5 n6) 5 y = a ∧
          w_i (linearCode n3 n5 n6) 6 y = k - a ∧ y ⟨0, by omega⟩ = true)
      (Finset.univ.filter fun y : Word (n3 + n5 + n6) =>
        w_i (linearCode n3 n5 n6) 3 y = d + 1 - k ∧
          w_i (linearCode n3 n5 n6) 5 y = b ∧
          w_i (linearCode n3 n5 n6) 6 y = k - b ∧ y ⟨0, by omega⟩ = true)
    rw [Finset.disjoint_left]
    intro y hya hyb
    have hwa : w_i (linearCode n3 n5 n6) 5 y = a :=
      (Finset.mem_filter.mp hya).2.2.1
    have hwb : w_i (linearCode n3 n5 n6) 5 y = b :=
      (Finset.mem_filter.mp hyb).2.2.1
    exact hab (hwa.symm.trans hwb)
  rw [hfilter, Finset.card_biUnion hdisj]
  -- each subfilter has the binomial count
  apply congrArg (fun x : ℕ => 2 * x)
  apply Finset.sum_congr rfl
  intro w5 hw5
  have hw5le5 : w5 ≤ n5 := by
    have hw5u : w5 ≤ n5 + m - (d + 1) := (Finset.mem_Icc.mp hw5).2
    omega
  have hk3 : 1 ≤ d + 1 - k := by omega
  have hk6 : k - w5 ≤ n6 := by omega
  have hfilter' : (Finset.univ.filter (fun y : Word (n3 + n5 + n6) =>
      y ⟨0, by omega⟩ = true ∧ w_i (linearCode n3 n5 n6) 3 y = d + 1 - k ∧
        w_i (linearCode n3 n5 n6) 5 y = w5 ∧
        w_i (linearCode n3 n5 n6) 6 y = k - w5)) =
      (Finset.univ.filter (fun y : Word (n3 + n5 + n6) =>
        w_i (linearCode n3 n5 n6) 3 y = d + 1 - k ∧
          w_i (linearCode n3 n5 n6) 5 y = w5 ∧
          w_i (linearCode n3 n5 n6) 6 y = k - w5 ∧ y ⟨0, by omega⟩ = true)) := by
    ext y
    simp
    tauto
  rw [← congrArg Finset.card hfilter']
  rw [linear_count_words n3 n5 n6 (d + 1 - k) w5 (k - w5) hn3 hk3]
  have : d + 1 - k - 1 = d - k := by omega
  rw [this]
  ac_rfl

/-- If `b` is odd and `2a ≤ b`, then `2a < b` (the gap is the missing even). -/
lemma two_mul_lt_of_odd {a b : ℕ} (hodd : Odd b) (hle : 2 * a ≤ b) : 2 * a < b := by
  rcases hodd with ⟨q, hq⟩
  have hle' : 2 * a ≤ 2 * q + 1 := by omega
  have hle2 : 2 * a ≤ 2 * q := by
    by_cases h : 2 * a = 2 * q + 1
    · have hodd' : Odd (2 * a) := by rw [h]; exact ⟨q, by omega⟩
      have heven : Even (2 * a) := ⟨a, by ring⟩
      exact False.elim ((Nat.not_even_iff_odd.mpr hodd') heven)
    · omega
  have hlt : 2 * a < 2 * q + 1 := Nat.lt_succ_of_le hle2
  rw [← hq] at hlt
  exact hlt

/-- Closed form of α⁵(d) for the linear 3 → 5 change (paper eq. cli2).
With the case-3 parity `n5+n6 = 2k`, `n3+n6 = 2m+1`, `n5 ≤ min n3 n6` and
`m ≤ d ≤ n5+m−1`, the summation range for `w̃₃ = w3 + k − m` is
`d+1−m ≤ w̃₃ ≤ n5+m−d−1`; the `C(n3−1, w̃₃+m−k)` index is the paper's
`w̃₃ − (n5−n3+1)/2`. -/
lemma linAlpha5_closed {n3 n5 n6 d k m : ℕ} (hn3 : 0 < n3)
    (hpar : Even (n5 + n6)) (hk : n5 + n6 = 2 * k) (hm : n3 + n6 = 2 * m + 1)
    (hge : m ≤ d) (hn56 : n5 ≤ n6) (hn53 : n5 ≤ n3)
    (hln : d ≤ n5 + m - 1) :
    linAlpha5 (linearCode n3 n5 n6) ⟨0, by omega⟩ d =
      2 * (∑ w3t ∈ Finset.Icc (d + 1 - m) (n5 + m - (d + 1)),
        Nat.choose (n3 - 1) (w3t + m - k) *
          (Nat.choose n5 (d - m) * Nat.choose n6 (k - w3t))) := by
  have hkdiv : (n5 + n6) / 2 = k := by
    rw [hk, Nat.mul_div_right k (by decide : 0 < 2)]
  rw [linAlpha5_eq_two_mul d hn3]
  have hkm : k ≤ m := by
    have h1 : 2 * k ≤ 2 * m + 1 := by omega
    by_contra h
    have hgt : m < k := by omega
    omega
  -- decompose the Y5-with-`y 0 = false` filter over the w̃₃ range
  have hrange (y : Word (n3 + n5 + n6))
      (hw : 2 * w_i (linearCode n3 n5 n6) 3 y + (n5 + n6) ≥ 2 * d + 2 ∧
        2 * w_i (linearCode n3 n5 n6) 3 y + 2 * d ≤ n3 + n5 + 2 * m - 2) :
      d + 1 - m ≤ w_i (linearCode n3 n5 n6) 3 y + k - m ∧
        w_i (linearCode n3 n5 n6) 3 y + k - m ≤ n5 + m - (d + 1) := by
    constructor
    · have h1 : 2 * w_i (linearCode n3 n5 n6) 3 y ≥ 2 * (d + 1 - k) := by omega
      have hw3ge : w_i (linearCode n3 n5 n6) 3 y ≥ d + 1 - k := by omega
      omega
    · have hle : 2 * w_i (linearCode n3 n5 n6) 3 y ≤ n3 + n5 + 2 * m - 2 * d - 2 := by omega
      have hle2 : 2 * (w_i (linearCode n3 n5 n6) 3 y + k - m) ≤
          2 * (n5 + m - (d + 1)) + 1 := by omega
      have hlt2 : 2 * (w_i (linearCode n3 n5 n6) 3 y + k - m) <
          2 * (n5 + m - (d + 1)) + 1 :=
        two_mul_lt_of_odd ⟨n5 + m - (d + 1), by omega⟩ hle2
      omega
  have hfilter :
      (Finset.univ.filter fun y : Word (n3 + n5 + n6) =>
        linY5 (linearCode n3 n5 n6) ⟨0, by omega⟩ y ∧
        dCode (linearCode n3 n5 n6) y = d ∧ y ⟨0, by omega⟩ = false) =
      Finset.biUnion (Finset.Icc (d + 1 - m) (n5 + m - (d + 1))) fun w3t =>
        Finset.univ.filter fun y : Word (n3 + n5 + n6) =>
          w_i (linearCode n3 n5 n6) 3 y = w3t + m - k ∧
            w_i (linearCode n3 n5 n6) 5 y = d - m ∧
            w_i (linearCode n3 n5 n6) 6 y = k - w3t ∧
            y ⟨0, by omega⟩ = false := by
    ext y
    constructor
    · intro hy
      rcases (Finset.mem_filter.mp hy).2 with ⟨hY, hd, hyt⟩
      have hw := (linY5_false_iff' y hn3 hpar hm hyt hd hge hn56).1 hY
      have hr := hrange y ⟨hw.2.2.1, hw.2.2.2⟩
      refine Finset.mem_biUnion.mpr ⟨w_i (linearCode n3 n5 n6) 3 y + k - m, ?_, ?_⟩
      · exact Finset.mem_Icc.mpr hr
      · have hw3 : w_i (linearCode n3 n5 n6) 3 y =
            (w_i (linearCode n3 n5 n6) 3 y + k - m) + m - k := by omega
        have hw6 : w_i (linearCode n3 n5 n6) 6 y =
            k - (w_i (linearCode n3 n5 n6) 3 y + k - m) := by omega
        exact Finset.mem_filter.mpr ⟨by simp, ⟨hw3, hw.1, hw6, hyt⟩⟩
    · intro hy
      rcases Finset.mem_biUnion.mp hy with ⟨w3t, hw3t, hyw⟩
      rcases (Finset.mem_filter.mp hyw).2 with ⟨hw3, hw5, hw6, hyt⟩
      have hw3tge : d + 1 - m ≤ w3t := (Finset.mem_Icc.mp hw3t).1
      have hw3tle : w3t ≤ n5 + m - (d + 1) := (Finset.mem_Icc.mp hw3t).2
      have hw3leM : w_i (linearCode n3 n5 n6) 3 y ≤ m := by omega
      have hw3tlek : w3t ≤ k := by omega
      have hw3tgek : k ≤ w3t + m := by omega
      have hd0 : dRow (linearCode n3 n5 n6) ⟨0, by decide⟩ y = d := by
        have hdr : dRow (linearCode n3 n5 n6) ⟨0, by omega⟩ y =
            w_i (linearCode n3 n5 n6) 3 y + w_i (linearCode n3 n5 n6) 5 y +
              w_i (linearCode n3 n5 n6) 6 y := by
          simpa using (linear_dRow0 (n3 := n3) (n5 := n5) (n6 := n6) y)
        rw [hdr, hw3, hw5, hw6]
        omega
      have hd1 : d + 2 ≤ dRow (linearCode n3 n5 n6) ⟨1, by decide⟩ y := by
        have hdr : dRow (linearCode n3 n5 n6) ⟨1, by omega⟩ y =
            w_i (linearCode n3 n5 n6) 3 y + (n5 - w_i (linearCode n3 n5 n6) 5 y) +
              (n6 - w_i (linearCode n3 n5 n6) 6 y) := by
          simpa using (linear_dRow1 (n3 := n3) (n5 := n5) (n6 := n6) y)
        rw [hdr, hw3, hw5, hw6]
        omega
      have hd2 : dRow (linearCode n3 n5 n6) ⟨0, by decide⟩ y + 1 =
          dRow (linearCode n3 n5 n6) ⟨2, by decide⟩ y := by
        have hdr : dRow (linearCode n3 n5 n6) ⟨2, by omega⟩ y =
            (n3 - w_i (linearCode n3 n5 n6) 3 y) +
              w_i (linearCode n3 n5 n6) 5 y +
                (n6 - w_i (linearCode n3 n5 n6) 6 y) := by
          simpa using (linear_dRow2 (n3 := n3) (n5 := n5) (n6 := n6) y)
        rw [hdr, hw3, hw5, hw6]
        omega
      have hd3 : d + 2 ≤ dRow (linearCode n3 n5 n6) ⟨3, by decide⟩ y := by
        have hdr : dRow (linearCode n3 n5 n6) ⟨3, by omega⟩ y =
            (n3 - w_i (linearCode n3 n5 n6) 3 y) +
              (n5 - w_i (linearCode n3 n5 n6) 5 y) +
                w_i (linearCode n3 n5 n6) 6 y := by
          simpa using (linear_dRow3 (n3 := n3) (n5 := n5) (n6 := n6) y)
        rw [hdr, hw3, hw5, hw6]
        omega
      have hdC : dCode (linearCode n3 n5 n6) y = d := by
        change min (dRow (linearCode n3 n5 n6) ⟨0, by decide⟩ y)
            (min (dRow (linearCode n3 n5 n6) ⟨1, by decide⟩ y)
              (min (dRow (linearCode n3 n5 n6) ⟨2, by decide⟩ y) (dRow (linearCode n3 n5 n6) ⟨3, by decide⟩ y))) =
            d
        have hle1 : d ≤
            min (dRow (linearCode n3 n5 n6) ⟨1, by omega⟩ y)
              (min (dRow (linearCode n3 n5 n6) ⟨2, by omega⟩ y) (dRow (linearCode n3 n5 n6) ⟨3, by omega⟩ y)) := by omega
        rw [hd0, min_eq_left hle1]
      have hY : linY5 (linearCode n3 n5 n6) ⟨0, by omega⟩ y := by
        apply (linY5_false_iff' y hn3 hpar hm hyt hdC hge hn56).2
        constructor
        · exact hw5
        · constructor
          · have hmw3 : m - w_i (linearCode n3 n5 n6) 3 y =
                k - w3t := by omega
            simpa [hmw3] using hw6
          · constructor
            · have hge' : 2 * w_i (linearCode n3 n5 n6) 3 y + (n5 + n6) ≥ 2 * d + 2 := by omega
              exact hge'
            · have hle' : 2 * w_i (linearCode n3 n5 n6) 3 y + 2 * d ≤ n3 + n5 + 2 * m - 2 := by omega
              exact hle'
      exact Finset.mem_filter.mpr ⟨by simp, ⟨hY, hdC, hyt⟩⟩
  have hdisj : ((Finset.Icc (d + 1 - m) (n5 + m - (d + 1)) : Set ℕ).PairwiseDisjoint fun w3t =>
      Finset.univ.filter fun y : Word (n3 + n5 + n6) =>
        w_i (linearCode n3 n5 n6) 3 y = w3t + m - k ∧
          w_i (linearCode n3 n5 n6) 5 y = d - m ∧
          w_i (linearCode n3 n5 n6) 6 y = k - w3t ∧
          y ⟨0, by omega⟩ = false) := by
    intro a ha b hb hab
    change Disjoint
      (Finset.univ.filter fun y : Word (n3 + n5 + n6) =>
        w_i (linearCode n3 n5 n6) 3 y = a + m - k ∧
          w_i (linearCode n3 n5 n6) 5 y = d - m ∧
          w_i (linearCode n3 n5 n6) 6 y = k - a ∧ y ⟨0, by omega⟩ = false)
      (Finset.univ.filter fun y : Word (n3 + n5 + n6) =>
        w_i (linearCode n3 n5 n6) 3 y = b + m - k ∧
          w_i (linearCode n3 n5 n6) 5 y = d - m ∧
          w_i (linearCode n3 n5 n6) 6 y = k - b ∧ y ⟨0, by omega⟩ = false)
    rw [Finset.disjoint_left]
    intro y hya hyb
    have hwa : w_i (linearCode n3 n5 n6) 3 y = a + m - k :=
      (Finset.mem_filter.mp hya).2.1
    have hwb : w_i (linearCode n3 n5 n6) 3 y = b + m - k :=
      (Finset.mem_filter.mp hyb).2.1
    have hma : a + m - k = b + m - k := hwa.symm.trans hwb
    omega
  rw [hfilter, Finset.card_biUnion hdisj]
  -- each subfilter has the binomial count
  apply congrArg (fun x : ℕ => 2 * x)
  apply Finset.sum_congr rfl
  intro w3t hw3t
  have hw3tlek : w3t ≤ k := by
    have hw3tu : w3t ≤ n5 + m - (d + 1) := (Finset.mem_Icc.mp hw3t).2
    omega
  have hw3tgek : k ≤ w3t + m := by omega
  have hdm : d - m ≤ n5 := by
    have hd : d ≤ n5 + m := by omega
    omega
  have hw3idx : w3t + m - k ≤ n3 - 1 := by
    have hw3tu : w3t ≤ n5 + m - (d + 1) := (Finset.mem_Icc.mp hw3t).2
    have hdge : m ≤ d := hge
    omega
  have hfilter' : (Finset.univ.filter (fun y : Word (n3 + n5 + n6) =>
      y ⟨0, by omega⟩ = false ∧ w_i (linearCode n3 n5 n6) 3 y = w3t + m - k ∧
        w_i (linearCode n3 n5 n6) 5 y = d - m ∧
        w_i (linearCode n3 n5 n6) 6 y = k - w3t)) =
      (Finset.univ.filter (fun y : Word (n3 + n5 + n6) =>
        w_i (linearCode n3 n5 n6) 3 y = w3t + m - k ∧
          w_i (linearCode n3 n5 n6) 5 y = d - m ∧
          w_i (linearCode n3 n5 n6) 6 y = k - w3t ∧ y ⟨0, by omega⟩ = false)) := by
    ext y
    simp
    tauto
  rw [← congrArg Finset.card hfilter']
  rw [linear_count_words_false n3 n5 n6 (w3t + m - k) (d - m) (k - w3t) hn3]
  ac_rfl

/-- For Y5 with `y t = false` at distance `d`, the parameter `m = (n3+n6−1)/2`
satisfies `m ≤ d` (the paper's α⁵(d) = 0 for d < m). -/
lemma linY5_false_implies_m_le_d {n3 n5 n6 d m : ℕ} (y : Word (n3 + n5 + n6))
    (t : Fin (n3 + n5 + n6)) (hcol : linearCode n3 n5 n6 t = col3) (ht : y t = false)
    (hm : n3 + n6 = 2 * m + 1) (hy : linY5 (linearCode n3 n5 n6) t y)
    (hd : dCode (linearCode n3 n5 n6) y = d) : m ≤ d := by
  let w3 := w_i (linearCode n3 n5 n6) 3 y
  let w5 := w_i (linearCode n3 n5 n6) 5 y
  let w6 := w_i (linearCode n3 n5 n6) 6 y
  have hrel := linY5_false_relations y t hcol ht hy
  rcases hrel with ⟨hdRow2, hdRow1, hdRow3⟩
  have hw5le : w5 ≤ n5 := by
    simpa [w5, linear_count_5] using (w_i_le_count (linearCode n3 n5 n6) 5 y)
  have hw6le : w6 ≤ n6 := by
    simpa [w6, linear_count_6] using (w_i_le_count (linearCode n3 n5 n6) 6 y)
  have hw3le : w3 ≤ n3 := by
    simpa [w3, linear_count_3] using (w_i_le_count (linearCode n3 n5 n6) 3 y)
  have hdRow0 : dRow (linearCode n3 n5 n6) ⟨0, by decide⟩ y = w3 + w5 + w6 := by
    simpa [w3, w5, w6] using linear_dRow0 y
  have hdRow2' : dRow (linearCode n3 n5 n6) ⟨2, by decide⟩ y = (n3 - w3) + w5 + (n6 - w6) := by
    simpa [w3, w5, w6] using linear_dRow2 y
  have hdRow0d : dRow (linearCode n3 n5 n6) ⟨0, by decide⟩ y = d := by
    have hleO : dRow (linearCode n3 n5 n6) ⟨0, by decide⟩ y ≤
        dRow (linearCode n3 n5 n6) ⟨3, by decide⟩ y := by omega
    have hdC : dCode (linearCode n3 n5 n6) y =
        dRow (linearCode n3 n5 n6) ⟨0, by decide⟩ y := by
      change min (dRow (linearCode n3 n5 n6) ⟨0, by decide⟩ y)
          (min (dRow (linearCode n3 n5 n6) ⟨1, by decide⟩ y)
            (min (dRow (linearCode n3 n5 n6) ⟨2, by decide⟩ y) (dRow (linearCode n3 n5 n6) ⟨3, by decide⟩ y))) =
          dRow (linearCode n3 n5 n6) ⟨0, by decide⟩ y
      have hle : dRow (linearCode n3 n5 n6) ⟨0, by decide⟩ y ≤
          min (dRow (linearCode n3 n5 n6) ⟨1, by decide⟩ y)
            (min (dRow (linearCode n3 n5 n6) ⟨2, by decide⟩ y) (dRow (linearCode n3 n5 n6) ⟨3, by decide⟩ y)) := by
        apply le_min
        · omega
        · apply le_min
          · omega
          · omega
      rw [min_eq_left hle]
    rwa [hdC] at hd
  have hsum : w3 + w6 = m := by
    have h1 : w3 + w5 + w6 + 1 = (n3 - w3) + w5 + (n6 - w6) := by
      calc
        w3 + w5 + w6 + 1 = dRow (linearCode n3 n5 n6) ⟨0, by decide⟩ y + 1 := by
          rw [hdRow0]
        _ = dRow (linearCode n3 n5 n6) ⟨2, by decide⟩ y := hdRow2
        _ = (n3 - w3) + w5 + (n6 - w6) := hdRow2'
    have h2 : 2 * (w3 + w6) + 1 = n3 + n6 := by omega
    have h3 : 2 * (w3 + w6) = 2 * m := by omega
    omega
  have hd0 : d = w3 + w6 + w5 := by
    rw [← hdRow0d, hdRow0]
    omega
  omega

/-- α⁵(d) = 0 for d < m (eq. cli6: the weight `w5 = d−m` cannot be realized). -/
lemma linAlpha5_zero_of_lt_m {n3 n5 n6 d m : ℕ} (hn3 : 0 < n3)
    (hm : n3 + n6 = 2 * m + 1) (hd : d < m) :
    linAlpha5 (linearCode n3 n5 n6) ⟨0, by omega⟩ d = 0 := by
  rw [linAlpha5_eq_two_mul d hn3]
  have hcol : linearCode n3 n5 n6 ⟨0, by omega⟩ = col3 := by
    simp [linearCode, hn3]
  have hempty : (Finset.univ.filter fun y : Word (n3 + n5 + n6) =>
      linY5 (linearCode n3 n5 n6) ⟨0, by omega⟩ y ∧ dCode (linearCode n3 n5 n6) y = d ∧
        y ⟨0, by omega⟩ = false) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro y hy
    rcases (Finset.mem_filter.mp hy).2 with ⟨hY, hdC, hyt⟩
    have hmle : m ≤ d := linY5_false_implies_m_le_d y ⟨0, by omega⟩ hcol hyt hm hY hdC
    omega
  simp [hempty]

/-- α⁵(d) = 0 for `d ≥ n5 + m` (eq. cli6: the `w̃₃` range is empty). -/
lemma linAlpha5_zero_of_ge_n5m {n3 n5 n6 d k m : ℕ} (hn3 : 0 < n3)
    (hpar : Even (n5 + n6)) (hk : n5 + n6 = 2 * k) (hm : n3 + n6 = 2 * m + 1)
    (hn56 : n5 ≤ n6) (_hn53 : n5 ≤ n3) (hd : n5 + m ≤ d) :
    linAlpha5 (linearCode n3 n5 n6) ⟨0, by omega⟩ d = 0 := by
  rw [linAlpha5_eq_two_mul d hn3]
  have hcol : linearCode n3 n5 n6 ⟨0, by omega⟩ = col3 := by
    simp [linearCode, hn3]
  have hge : m ≤ d := by omega
  have hempty : (Finset.univ.filter fun y : Word (n3 + n5 + n6) =>
      linY5 (linearCode n3 n5 n6) ⟨0, by omega⟩ y ∧ dCode (linearCode n3 n5 n6) y = d ∧
        y ⟨0, by omega⟩ = false) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro y hy
    rcases (Finset.mem_filter.mp hy).2 with ⟨hY, hdC, hyt⟩
    have hw := (linY5_false_iff' y hn3 hpar hm hyt hdC hge hn56).1 hY
    have hw5le : w_i (linearCode n3 n5 n6) 5 y ≤ n5 := by
      simpa [linear_count_5] using (w_i_le_count (linearCode n3 n5 n6) 5 y)
    have hd5 : d - m ≤ n5 := by omega
    have hdeq : d = n5 + m := by omega
    have hw3ge : w_i (linearCode n3 n5 n6) 3 y ≥ n5 + m + 1 - k := by omega
    have hw3le : 2 * w_i (linearCode n3 n5 n6) 3 y ≤ n3 + n5 - 2 := by omega
    omega
  simp [hempty]

/-- Case 3, equality sub-case: when `n3 = n5+1` (so `k = m` and
`n3−1 = n5`), the closed forms of eq. cli3 and eq. cli2 agree termwise on the
shared range, giving `α³(d+1) = α⁵(d)` for `m ≤ d ≤ n5+m−1`. -/
lemma lin_alpha3_succ_eq_alpha5 {n3 n5 n6 d k m : ℕ} (hn3 : 0 < n3)
    (hpar : Even (n5 + n6)) (hk : n5 + n6 = 2 * k) (hm : n3 + n6 = 2 * m + 1)
    (hge : m ≤ d) (hn56 : n5 ≤ n6) (hn53 : n5 ≤ n3)
    (hln : d ≤ n5 + m - 1) (hn5 : 0 < n5) (heq : n3 = n5 + 1) :
    linAlpha3 (linearCode n3 n5 n6) ⟨0, by omega⟩ (d + 1) =
      linAlpha5 (linearCode n3 n5 n6) ⟨0, by omega⟩ d := by
  have hkm : k = m := by
    have h1 : n5 + n6 = 2 * m := by omega
    have h2 : 2 * k = 2 * m := by omega
    omega
  have hkd : k ≤ d := by omega
  have hge3 : 2 * (d + 1) ≥ n3 + n5 := by
    have h1 : 2 * m + 2 ≤ 2 * (d + 1) := by omega
    have h2 : n3 + n5 + 1 ≤ 2 * m + 2 := by omega
    omega
  have hmd : m ≤ d + 1 := by omega
  have hln3 : d + 1 ≤ n5 + m := by
    omega
  rw [linAlpha3_closed (n3 := n3) (n5 := n5) (n6 := n6) (d := d) (k := k) (m := m)
    hn3 hpar hk hm hge3 hn56 hn53 hmd hln3 hkd]
  rw [linAlpha5_closed (n3 := n3) (n5 := n5) (n6 := n6) (d := d) (k := k) (m := m)
    hn3 hpar hk hm hge hn56 hn53 hln]
  apply congrArg (fun x : ℕ => 2 * x)
  apply Finset.sum_congr rfl
  intro w hw
  have hn3m1 : n3 - 1 = n5 := by omega
  have hwmm : w + m - m = w := by omega
  rw [hn3m1, hkm]
  rw [hwmm]
  ring

/-- α³(d+1) = 0 for `d+1 ≤ m` when `k = m` (equality case of case 3): the
`y t = true` half has `w3 = d+1−m ≤ 0`. -/
lemma linAlpha3_zero_of_lt_m_eq {n3 n5 n6 d k m : ℕ} (hn3 : 0 < n3)
    (hpar : Even (n5 + n6)) (hk : n5 + n6 = 2 * k) (hm : n3 + n6 = 2 * m + 1)
    (hd : d + 1 ≤ m) (hkm : k = m) :
    linAlpha3 (linearCode n3 n5 n6) ⟨0, by omega⟩ (d + 1) = 0 := by
  rw [linAlpha3_eq_two_mul (d + 1) hn3]
  have hcol : linearCode n3 n5 n6 ⟨0, by omega⟩ = col3 := by
    simp [linearCode, hn3]
  have hkdiv : (n5 + n6) / 2 = k := by
    rw [hk, Nat.mul_div_right k (by decide : 0 < 2)]
  have hempty : (Finset.univ.filter fun y : Word (n3 + n5 + n6) =>
      linY3 (linearCode n3 n5 n6) ⟨0, by omega⟩ y ∧ dCode (linearCode n3 n5 n6) y = d + 1 ∧
        y ⟨0, by omega⟩ = true) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro y hy
    rcases (Finset.mem_filter.mp hy).2 with ⟨hY, hdC, hyt⟩
    have hw := linY3_true_weights y ⟨0, by omega⟩ hcol hyt hpar hY hdC
    have hw3 : w_i (linearCode n3 n5 n6) 3 y = d + 1 - k := by
      simpa [hkdiv] using hw.1
    have hw3pos : 1 ≤ w_i (linearCode n3 n5 n6) 3 y :=
      linear_w3_pos_of_true y ⟨0, by omega⟩ hcol hyt
    rw [hkm] at hw3
    omega
  simp [hempty]

/-- α³(d+1) = 0 for `d ≥ n5 + m`: the `y t = true` half has
`2·w5 ≥ 2(d+1) − n3 − n6 > 2·n5`. -/
lemma linAlpha3_zero_of_ge_n5m {n3 n5 n6 d k m : ℕ} (hn3 : 0 < n3)
    (hpar : Even (n5 + n6)) (hk : n5 + n6 = 2 * k) (hm : n3 + n6 = 2 * m + 1)
    (hd : n5 + m ≤ d) :
    linAlpha3 (linearCode n3 n5 n6) ⟨0, by omega⟩ (d + 1) = 0 := by
  rw [linAlpha3_eq_two_mul (d + 1) hn3]
  have hcol : linearCode n3 n5 n6 ⟨0, by omega⟩ = col3 := by
    simp [linearCode, hn3]
  have hempty : (Finset.univ.filter fun y : Word (n3 + n5 + n6) =>
      linY3 (linearCode n3 n5 n6) ⟨0, by omega⟩ y ∧ dCode (linearCode n3 n5 n6) y = d + 1 ∧
        y ⟨0, by omega⟩ = true) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro y hy
    rcases (Finset.mem_filter.mp hy).2 with ⟨hY, hdC, hyt⟩
    have hw := linY3_true_weights y ⟨0, by omega⟩ hcol hyt hpar hY hdC
    have hw5le : w_i (linearCode n3 n5 n6) 5 y ≤ n5 := by
      simpa [linear_count_5] using (w_i_le_count (linearCode n3 n5 n6) 5 y)
    have hw5ge : w_i (linearCode n3 n5 n6) 5 y ≥ n5 + 1 := by
      have h1 : 2 * w_i (linearCode n3 n5 n6) 5 y ≥ 2 * (d + 1) - n3 - n6 := hw.2.2.1
      omega
    omega
  simp [hempty]

/-- Flipping at t maps Y1 ∪ Y3 back to itself. -/
lemma linY13_closed {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) :
    (linY1 C t (flipBit t y) ∨ linY3 C t (flipBit t y)) →
      (linY1 C t y ∨ linY3 C t y) := by
  intro h
  exact gY13_closed (linO C) (linP C) t y
    (linO_flip_bounds C t y).1 (linO_flip_bounds C t y).2
    (linP_flip_bounds C t y).1 (linP_flip_bounds C t y).2 h

/-- Flipping at t maps the complement of Y1 ∪ Y3 into itself. -/
lemma linY13_complement_closed {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) :
    ¬ (linY1 C t y ∨ linY3 C t y) →
      ¬ (linY1 C t (flipBit t y) ∨ linY3 C t (flipBit t y)) := by
  intro hnot h
  exact hnot (linY13_closed C t y h)

/-- `g1` is an involution. -/
lemma linG1_involutive {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) :
    linG1 C t (linG1 C t y) = y := by
  by_cases hy : linY1 C t y ∨ linY3 C t y
  · have hy' : gY1 (linO C) (linP C) t y ∨ gY3 (linO C) (linP C) t y := hy
    simp [linG1, gG1, hy']
  · have hy' : ¬ (gY1 (linO C) (linP C) t y ∨ gY3 (linO C) (linP C) t y) := by
      simpa [linY1, linY3] using hy
    have hcl := linY13_complement_closed C t y hy
    have hcl' : ¬ (gY1 (linO C) (linP C) t (flipBit t y) ∨
        gY3 (linO C) (linP C) t (flipBit t y)) := by
      simpa [linY1, linY3] using hcl
    simp [linG1, gG1, hy', hcl', flipBit_involutive t y]

/-- α³(0) = 0 for the linear change. -/
lemma linAlpha3_zero {n : ℕ} (C C' : Code n) (t : Fin n) (hcol : C t = col3)
    (hcol' : C' t = col5) (hsame : ∀ u : Fin n, u ≠ t → C' u = C u) :
    linAlpha3 C t 0 = 0 := by
  rw [linAlpha3, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro y hy
  have h3 : linY3 C t y := (Finset.mem_filter.mp hy).2.1
  have hd0 : dCode C y = 0 := (Finset.mem_filter.mp hy).2.2
  have h := (lin_y_rel_3 C C' t hcol hcol' hsame h3).2
  omega

/-- α⁵(n) = 0 for the linear change. -/
lemma linAlpha5_n_zero {n : ℕ} (C C' : Code n) (t : Fin n) (hcol : C t = col3)
    (hcol' : C' t = col5) (hsame : ∀ u : Fin n, u ≠ t → C' u = C u) :
    linAlpha5 C t n = 0 := by
  rw [linAlpha5, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro y hy
  have h5 : linY5 C t y := (Finset.mem_filter.mp hy).2.1
  have hdn : dCode C y = n := (Finset.mem_filter.mp hy).2.2
  have h := (lin_y_rel_5 C C' t hcol hcol' hsame h5).1
  have hle := dCode_le C' (flipBit t y)
  omega

/-- Σ over Y3 words of r^(d−1), grouped by distance. -/
lemma lin_sum_Y3_pow {n : ℕ} (C C' : Code n) (t : Fin n) (hcol : C t = col3)
    (hcol' : C' t = col5) (hsame : ∀ u : Fin n, u ≠ t → C' u = C u) (r : ℝ) :
    (∑ y ∈ Finset.univ.filter (linY3 C t), r ^ (dCode C y - 1)) =
      ∑ d ∈ Finset.Icc 1 n, (linAlpha3 C t d : ℝ) * r ^ (d - 1) := by
  have h0 : (linAlpha3 C t 0 : ℝ) = 0 := by
    simp [linAlpha3_zero C C' t hcol hcol' hsame]
  calc
    (∑ y ∈ Finset.univ.filter (linY3 C t), r ^ (dCode C y - 1))
        = ∑ d ∈ Finset.Icc 0 n, (linAlpha3 C t d : ℝ) * r ^ (d - 1) := by
          rw [sum_by_dist C (linY3 C t) (fun d => r ^ (d - 1))]
          simp [linAlpha3]
    _ = ∑ d ∈ Finset.Icc 1 n, (linAlpha3 C t d : ℝ) * r ^ (d - 1) := by
          exact sum_Icc0_eq_Icc1 (fun d => (linAlpha3 C t d : ℝ) * r ^ (d - 1))
            (by simp [h0])

/-- Σ over Y5 words of r^d, grouped by distance. -/
lemma lin_sum_Y5_pow {n : ℕ} (C C' : Code n) (t : Fin n) (hcol : C t = col3)
    (hcol' : C' t = col5) (hsame : ∀ u : Fin n, u ≠ t → C' u = C u) (r : ℝ) :
    (∑ y ∈ Finset.univ.filter (linY5 C t), r ^ (dCode C y)) =
      ∑ d ∈ Finset.Icc 1 n, (linAlpha5 C t (d - 1) : ℝ) * r ^ (d - 1) := by
  have h0 : (linAlpha5 C t n : ℝ) = 0 := by
    simp [linAlpha5_n_zero C C' t hcol hcol' hsame]
  calc
    (∑ y ∈ Finset.univ.filter (linY5 C t), r ^ (dCode C y))
        = ∑ d ∈ Finset.Icc 0 n, (linAlpha5 C t d : ℝ) * r ^ d := by
          rw [sum_by_dist C (linY5 C t) (fun d => r ^ d)]
          simp [linAlpha5]
    _ = ∑ e ∈ Finset.Icc 1 (n + 1), (linAlpha5 C t (e - 1) : ℝ) * r ^ (e - 1) := by
          refine Finset.sum_bij (fun d _ => d + 1) ?_ ?_ ?_ ?_
          · intro d hd
            simp [Finset.mem_Icc] at hd ⊢
            omega
          · intro a ha b hb hab
            omega
          · intro e he
            refine ⟨e - 1, ?_, ?_⟩
            · simp [Finset.mem_Icc] at he ⊢
              omega
            · have he1 : 1 ≤ e := (Finset.mem_Icc.mp he).1
              omega
          · intro d hd
            have hsub : (d + 1) - 1 = d := by omega
            rw [hsub]
    _ = ∑ e ∈ Finset.Icc 1 n, (linAlpha5 C t (e - 1) : ℝ) * r ^ (e - 1) := by
          have htop : ∑ e ∈ Finset.Icc (n + 1) (n + 1),
              (linAlpha5 C t (e - 1) : ℝ) * r ^ (e - 1) = 0 := by
            simp [h0]
          have hsplit : Finset.Icc 1 (n + 1) = Finset.Icc 1 n ∪ Finset.Icc (n + 1) (n + 1) := by
            ext e
            simp [Finset.mem_Icc]
            omega
          rw [hsplit, Finset.sum_union]
          · rw [htop]
            simp
          · simp [Finset.disjoint_left]
            omega

/-- The Y3 part of the λ-difference, factored (paper `the:1` (Theorem 20)). -/
lemma lin_sum_Y3_weight_diff {n : ℕ} (C C' : Code n) (t : Fin n) (hcol : C t = col3)
    (hcol' : C' t = col5) (hsame : ∀ u : Fin n, u ≠ t → C' u = C u)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1 / 2) :
    (∑ y ∈ Finset.univ.filter (linY3 C t),
        (weight n ε (dCode C y - 1) - weight n ε (dCode C y))) =
      (1 - ε) ^ n * (1 - ε / (1 - ε)) *
        ∑ y ∈ Finset.univ.filter (linY3 C t), (ε / (1 - ε)) ^ (dCode C y - 1) := by
  calc
    (∑ y ∈ Finset.univ.filter (linY3 C t),
        (weight n ε (dCode C y - 1) - weight n ε (dCode C y)))
        = ∑ y ∈ Finset.univ.filter (linY3 C t),
            (1 - ε) ^ n * (1 - ε / (1 - ε)) * (ε / (1 - ε)) ^ (dCode C y - 1) := by
          apply Finset.sum_congr rfl
          intro y hy
          have h3 : linY3 C t y := (Finset.mem_filter.mp hy).2
          have hd1 : 1 ≤ dCode C y := by
            have h := (lin_y_rel_3 C C' t hcol hcol' hsame h3).2
            omega
          have hdn : dCode C y ≤ n := dCode_le C y
          exact weight_pred_diff (n := n) (ε := ε) hε0 hε1 (d := dCode C y) hd1 hdn
    _ = (1 - ε) ^ n * (1 - ε / (1 - ε)) *
          ∑ y ∈ Finset.univ.filter (linY3 C t), (ε / (1 - ε)) ^ (dCode C y - 1) := by
          rw [Finset.mul_sum]

/-- The Y5 part of the λ-difference, factored (paper `the:1` (Theorem 20)). -/
lemma lin_sum_Y5_weight_diff {n : ℕ} (C C' : Code n) (t : Fin n) (hcol : C t = col3)
    (hcol' : C' t = col5) (hsame : ∀ u : Fin n, u ≠ t → C' u = C u)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1 / 2) :
    (∑ y ∈ Finset.univ.filter (linY5 C t),
        (weight n ε (dCode C y + 1) - weight n ε (dCode C y))) =
      -((1 - ε) ^ n * (1 - ε / (1 - ε)) *
          ∑ y ∈ Finset.univ.filter (linY5 C t), (ε / (1 - ε)) ^ (dCode C y)) := by
  calc
    (∑ y ∈ Finset.univ.filter (linY5 C t),
        (weight n ε (dCode C y + 1) - weight n ε (dCode C y)))
        = ∑ y ∈ Finset.univ.filter (linY5 C t),
            -((1 - ε) ^ n * (1 - ε / (1 - ε)) * (ε / (1 - ε)) ^ (dCode C y)) := by
          apply Finset.sum_congr rfl
          intro y hy
          have h5 : linY5 C t y := (Finset.mem_filter.mp hy).2
          have hdn : dCode C y < n := by
            have h := (lin_y_rel_5 C C' t hcol hcol' hsame h5).1
            have hle := dCode_le C' (flipBit t y)
            omega
          exact weight_succ_diff (n := n) (ε := ε) hε0 hε1 (d := dCode C y) hdn
    _ = -((1 - ε) ^ n * (1 - ε / (1 - ε)) *
          ∑ y ∈ Finset.univ.filter (linY5 C t), (ε / (1 - ε)) ^ (dCode C y)) := by
          rw [Finset.sum_neg_distrib]
          rw [Finset.mul_sum]

/-- λ_{C'} − λ_C equals a weighted sum over Y3 (closer) and Y5 (farther). -/
lemma lin_lambda_diff_y3y5 {n : ℕ} (C C' : Code n) (t : Fin n) (hcol : C t = col3)
    (hcol' : C' t = col5) (hsame : ∀ u : Fin n, u ≠ t → C' u = C u) (ε : ℝ) :
    lambda C' ε - lambda C ε =
      (1 / 4 : ℝ) *
        ((∑ y ∈ Finset.univ.filter (linY3 C t),
            (weight n ε (dCode C y - 1) - weight n ε (dCode C y))) +
         (∑ y ∈ Finset.univ.filter (linY5 C t),
            (weight n ε (dCode C y + 1) - weight n ε (dCode C y)))) := by
  unfold lambda
  rw [← mul_sub]
  congr 1
  have hg : (∑ y : Word n, weight n ε (dCode C' y)) =
      ∑ y : Word n, weight n ε (dCode C' (linG1 C t y)) := by
    refine Finset.sum_bij (fun y _ => linG1Equiv C t y) ?_ ?_ ?_ ?_
    · intro y _; exact Finset.mem_univ _
    · intro a _ b _ hab
      exact (linG1Equiv C t).injective hab
    · intro b _
      refine ⟨linG1Equiv C t b, Finset.mem_univ _, ?_⟩
      change linG1 C t (linG1 C t b) = b
      exact linG1_involutive C t b
    · intro y _
      have hg1 : linG1 C t (linG1Equiv C t y) = y := by
        change linG1 C t (linG1 C t y) = y
        exact linG1_involutive C t y
      rw [hg1]
  change (∑ y : Word n, weight n ε (dCode C' y)) - ∑ y : Word n, weight n ε (dCode C y) =
      (∑ y ∈ Finset.univ.filter (linY3 C t),
          (weight n ε (dCode C y - 1) - weight n ε (dCode C y))) +
      (∑ y ∈ Finset.univ.filter (linY5 C t),
          (weight n ε (dCode C y + 1) - weight n ε (dCode C y)))
  rw [hg, ← Finset.sum_sub_distrib]
  have hf : ∀ y : Word n,
      weight n ε (dCode C' (linG1 C t y)) - weight n ε (dCode C y) =
        (if linY3 C t y then weight n ε (dCode C y - 1) - weight n ε (dCode C y) else 0) +
        (if linY5 C t y then weight n ε (dCode C y + 1) - weight n ε (dCode C y) else 0) := by
    intro y
    by_cases h3 : linY3 C t y
    · have h5 : ¬ linY5 C t y := fun hy => linY3_Y5_disjoint C t y ⟨h3, hy⟩
      have hd : dCode C' (linG1 C t y) = dCode C y - 1 := by
        have h := (lin_y_rel_3 C C' t hcol hcol' hsame h3).2
        have h3g : gY3 (linO C) (linP C) t y := h3
        simp [linG1, gG1, h3g]
        omega
      simp [h3, h5, hd]
    · by_cases h5 : linY5 C t y
      · have h1 : ¬ linY1 C t y := fun hy => linY1_Y5_disjoint C t y ⟨hy, h5⟩
        have h1g : ¬ gY1 (linO C) (linP C) t y := h1
        have h3g : ¬ gY3 (linO C) (linP C) t y := h3
        have hg1 : linG1 C t y = flipBit t y := by
          simp [linG1, gG1, h1g, h3g]
        have hd : dCode C' (linG1 C t y) = dCode C y + 1 := by
          rw [hg1]
          exact (lin_y_rel_5 C C' t hcol hcol' hsame h5).1.symm
        simp [h3, h5, hd]
      · have h0 : weight n ε (dCode C' (linG1 C t y)) - weight n ε (dCode C y) = 0 := by
          have hy : linY1 C t y ∨ linY2 C t y ∨ linY4 C t y := by
            rcases lin_y_mem C t y with hy | hy | hy | hy | hy
            · exact Or.inl hy
            · exact Or.inr (Or.inl hy)
            · exfalso; exact h3 hy
            · exact Or.inr (Or.inr hy)
            · exfalso; exact h5 hy
          rcases hy with hy | hy | hy
          · have h := lin_y_rel_1 C C' t hcol hcol' hsame hy
            have hd : dCode C' (linG1 C t y) = dCode C y := by
              have hyg : gY1 (linO C) (linP C) t y := hy
              simp [linG1, gG1, hyg, h.1]
            rw [hd]
            ring
          · have h1 : ¬ linY1 C t y := fun hy1 => linY1_Y2_disjoint C t y ⟨hy1, hy⟩
            have h3' : ¬ linY3 C t y := fun hy3 => linY2_Y3_disjoint C t y ⟨hy, hy3⟩
            have h1g : ¬ gY1 (linO C) (linP C) t y := h1
            have h3g : ¬ gY3 (linO C) (linP C) t y := h3'
            have hg1 : linG1 C t y = flipBit t y := by
              simp [linG1, gG1, h1g, h3g]
            have hd : dCode C' (linG1 C t y) = dCode C y := by
              rw [hg1]
              exact (lin_y_rel_2 C C' t hcol hcol' hsame hy).1.symm
            rw [hd]
            ring
          · have h1 : ¬ linY1 C t y := fun hy1 => linY1_Y4_disjoint C t y ⟨hy1, hy⟩
            have h3' : ¬ linY3 C t y := fun hy3 => linY3_Y4_disjoint C t y ⟨hy3, hy⟩
            have h1g : ¬ gY1 (linO C) (linP C) t y := h1
            have h3g : ¬ gY3 (linO C) (linP C) t y := h3'
            have hg1 : linG1 C t y = flipBit t y := by
              simp [linG1, gG1, h1g, h3g]
            have hd : dCode C' (linG1 C t y) = dCode C y := by
              rw [hg1]
              exact (lin_y_rel_4 C C' t hcol hcol' hsame hy).2.1.symm
            rw [hd]
            ring
        simp [h3, h5, h0]
  have hsum : (∑ y : Word n,
      (weight n ε (dCode C' (linG1 C t y)) - weight n ε (dCode C y))) =
      ∑ y : Word n,
        ((if linY3 C t y then weight n ε (dCode C y - 1) - weight n ε (dCode C y) else 0) +
         (if linY5 C t y then weight n ε (dCode C y + 1) - weight n ε (dCode C y) else 0)) := by
    congr 1
    funext y
    exact hf y
  rw [hsum]
  rw [Finset.sum_add_distrib]
  rw [Finset.sum_filter]
  rw [Finset.sum_filter]

/-- Theorem `the:1` (Theorem 20) for the 3 → 5 change: exact λ-difference. -/
theorem lin_lambda_diff_one_column {n : ℕ} (C C' : Code n) (t : Fin n)
    (hcol : C t = col3) (hcol' : C' t = col5)
    (hsame : ∀ u : Fin n, u ≠ t → C' u = C u) :
    ∀ ε : ℝ, 0 < ε → ε < 1 / 2 →
      lambda C' ε - lambda C ε =
        ((1 - ε) ^ n / 4) * (1 - ε / (1 - ε)) *
          ∑ d ∈ Finset.Icc 1 n,
            ((linAlpha3 C t d : ℝ) - (linAlpha5 C t (d - 1) : ℝ)) *
              (ε / (1 - ε)) ^ (d - 1) := by
  intro ε hε0 hε1
  rw [lin_lambda_diff_y3y5 C C' t hcol hcol' hsame ε]
  rw [lin_sum_Y3_weight_diff C C' t hcol hcol' hsame ε hε0 hε1,
      lin_sum_Y5_weight_diff C C' t hcol hcol' hsame ε hε0 hε1]
  rw [lin_sum_Y3_pow C C' t hcol hcol' hsame (ε / (1 - ε)),
      lin_sum_Y5_pow C C' t hcol hcol' hsame (ε / (1 - ε))]
  have hsum :
      (∑ d ∈ Finset.Icc 1 n, (linAlpha3 C t d : ℝ) * (ε / (1 - ε)) ^ (d - 1)) -
        ∑ d ∈ Finset.Icc 1 n, (linAlpha5 C t (d - 1) : ℝ) * (ε / (1 - ε)) ^ (d - 1) =
      ∑ d ∈ Finset.Icc 1 n,
        ((linAlpha3 C t d : ℝ) - (linAlpha5 C t (d - 1) : ℝ)) * (ε / (1 - ε)) ^ (d - 1) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    ring
  rw [← hsum]
  ring

/-- The real prefix sums of α³(i) − α⁵(i−1) equal the integer Ψ_d. -/
lemma lin_Psi_real {n : ℕ} (C : Code n) (t : Fin n) (d : ℕ) (hd : 1 ≤ d) :
    (∑ i ∈ Finset.Icc 1 d, ((linAlpha3 C t i : ℝ) - (linAlpha5 C t (i - 1) : ℝ))) =
      linPsi C t d := by
  have hre : (∑ i ∈ Finset.Icc 1 d, (linAlpha5 C t (i - 1) : ℝ)) =
      ∑ j ∈ Finset.Icc 0 (d - 1), (linAlpha5 C t j : ℝ) := by
    refine Finset.sum_bij (fun i _ => i - 1) ?_ ?_ ?_ ?_
    · intro i hi
      simp [Finset.mem_Icc] at hi ⊢
      omega
    · intro a ha b hb hab
      have ha1 : 1 ≤ a := (Finset.mem_Icc.mp ha).1
      have hb1 : 1 ≤ b := (Finset.mem_Icc.mp hb).1
      omega
    · intro j hj
      refine ⟨j + 1, ?_, ?_⟩
      · have hj1 : j ≤ d - 1 := (Finset.mem_Icc.mp hj).2
        have hdsub : d - 1 + 1 = d := Nat.sub_add_cancel hd
        have hle' : j + 1 ≤ d - 1 + 1 := Nat.succ_le_succ hj1
        have hle : j + 1 ≤ d := by rwa [hdsub] at hle'
        simp [Finset.mem_Icc, hle]
      · have hsub : (j + 1) - 1 = j := by omega
        rw [hsub]
    · intro i hi
      rfl
  unfold linPsi
  rw [Int.cast_sub, Int.cast_sum, Int.cast_sum]
  rw [Finset.sum_sub_distrib, hre]
  norm_num

/-- Corollary `cor:1` (Corollary 21) (1) for the 3 → 5 change: all Ψ_d = 0 ⇒ equal. -/
theorem lin_cumulative_criterion {n : ℕ} (C C' : Code n) (t : Fin n)
    (hcol : C t = col3) (hcol' : C' t = col5)
    (hsame : ∀ u : Fin n, u ≠ t → C' u = C u)
    (hΨ : ∀ d ∈ Finset.Icc 1 n, linPsi C t d = 0) : UniversalEqual C' C := by
  intro ε hε0 hε1
  apply sub_eq_zero.mp
  rw [lin_lambda_diff_one_column C C' t hcol hcol' hsame ε hε0 hε1]
  have hSum : (∑ d ∈ Finset.Icc 1 n,
      ((linAlpha3 C t d : ℝ) - (linAlpha5 C t (d - 1) : ℝ)) * (ε / (1 - ε)) ^ (d - 1)) = 0 := by
    rw [abel_sum (fun i => (linAlpha3 C t i : ℝ) - (linAlpha5 C t (i - 1) : ℝ)) (ε / (1 - ε))]
    by_cases hn : n = 0
    · subst n
      simp
    · have hn1 : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn)
      have hterm1 : (∑ i ∈ Finset.Icc 1 n,
          ((linAlpha3 C t i : ℝ) - (linAlpha5 C t (i - 1) : ℝ))) * (ε / (1 - ε)) ^ (n - 1) = 0 := by
        rw [lin_Psi_real C t n hn1, hΨ n (by simp [Finset.mem_Icc, hn1])]
        norm_num
      have hterm2 : (∑ d ∈ Finset.Icc 1 (n - 1),
          (∑ i ∈ Finset.Icc 1 d, ((linAlpha3 C t i : ℝ) - (linAlpha5 C t (i - 1) : ℝ))) *
            ((ε / (1 - ε)) ^ (d - 1) - (ε / (1 - ε)) ^ d)) = 0 := by
        apply Finset.sum_eq_zero
        intro d hd
        have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
        have hd2 : d ≤ n - 1 := (Finset.mem_Icc.mp hd).2
        have hdn : d ≤ n := by omega
        rw [lin_Psi_real C t d hd1, hΨ d (by simp [Finset.mem_Icc, hd1, hdn])]
        norm_num
      rw [hterm1, hterm2]
      ring
  rw [hSum]
  ring

/-- Corollary `cor:1` (Corollary 21) (2) for the 3 → 5 change: Ψ_d ≥ 0 and some Ψ_d > 0 ⇒ strict. -/
theorem lin_cumulative_strict {n : ℕ} (C C' : Code n) (t : Fin n)
    (hcol : C t = col3) (hcol' : C' t = col5)
    (hsame : ∀ u : Fin n, u ≠ t → C' u = C u)
    (hge : ∀ d ∈ Finset.Icc 1 n, linPsi C t d ≥ 0)
    (hgt : ∃ d ∈ Finset.Icc 1 n, linPsi C t d > 0) :
    UniversalStrictBetter C' C := by
  intro ε hε0 hε1
  apply sub_pos.mp
  rw [lin_lambda_diff_one_column C C' t hcol hcol' hsame ε hε0 hε1]
  have hSum : (0 : ℝ) < ∑ d ∈ Finset.Icc 1 n,
      ((linAlpha3 C t d : ℝ) - (linAlpha5 C t (d - 1) : ℝ)) * (ε / (1 - ε)) ^ (d - 1) := by
    rw [abel_sum (fun i => (linAlpha3 C t i : ℝ) - (linAlpha5 C t (i - 1) : ℝ)) (ε / (1 - ε))]
    by_cases hn : n = 0
    · subst n
      exfalso
      rcases hgt with ⟨d, hd, _⟩
      simp at hd
    · have hn1 : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn)
      have hC_nonneg : ∀ d ∈ Finset.Icc 1 (n - 1),
          0 ≤ (∑ i ∈ Finset.Icc 1 d, ((linAlpha3 C t i : ℝ) - (linAlpha5 C t (i - 1) : ℝ))) *
            ((ε / (1 - ε)) ^ (d - 1) - (ε / (1 - ε)) ^ d) := by
        intro d hd
        have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
        have hd2 : d ≤ n - 1 := (Finset.mem_Icc.mp hd).2
        have hdn : d ≤ n := by omega
        rw [lin_Psi_real C t d hd1]
        have hPd : 0 ≤ (linPsi C t d : ℝ) := by
          exact_mod_cast hge d (by simp [Finset.mem_Icc, hd1, hdn])
        exact mul_nonneg hPd (le_of_lt (r_pow_sub_pos hε0 hε1 hd1))
      have hterm1 : 0 ≤ (∑ i ∈ Finset.Icc 1 n,
          ((linAlpha3 C t i : ℝ) - (linAlpha5 C t (i - 1) : ℝ))) * (ε / (1 - ε)) ^ (n - 1) := by
        rw [lin_Psi_real C t n hn1]
        have hPn : 0 ≤ (linPsi C t n : ℝ) := by
          exact_mod_cast hge n (by simp [Finset.mem_Icc, hn1])
        exact mul_nonneg hPn (pow_nonneg (le_of_lt (r_pos hε0 hε1)) (n - 1))
      have hterm2 : 0 ≤ ∑ d ∈ Finset.Icc 1 (n - 1),
          (∑ i ∈ Finset.Icc 1 d, ((linAlpha3 C t i : ℝ) - (linAlpha5 C t (i - 1) : ℝ))) *
            ((ε / (1 - ε)) ^ (d - 1) - (ε / (1 - ε)) ^ d) := by
        exact Finset.sum_nonneg hC_nonneg
      rcases hgt with ⟨d0, hd0mem, hd0gt⟩
      have hd01 : 1 ≤ d0 := (Finset.mem_Icc.mp hd0mem).1
      have hd0n : d0 ≤ n := (Finset.mem_Icc.mp hd0mem).2
      by_cases hd0eq : d0 = n
      · have hterm1' : 0 < (∑ i ∈ Finset.Icc 1 n,
            ((linAlpha3 C t i : ℝ) - (linAlpha5 C t (i - 1) : ℝ))) * (ε / (1 - ε)) ^ (n - 1) := by
          rw [lin_Psi_real C t n hn1]
          have hPn : 0 < (linPsi C t n : ℝ) := by
            have hgtn : linPsi C t n > 0 := by
              simpa [hd0eq] using hd0gt
            exact_mod_cast hgtn
          exact mul_pos hPn (pow_pos (r_pos hε0 hε1) (n - 1))
        have hsum0 : 0 < (∑ i ∈ Finset.Icc 1 n,
            ((linAlpha3 C t i : ℝ) - (linAlpha5 C t (i - 1) : ℝ))) * (ε / (1 - ε)) ^ (n - 1) +
            ∑ d ∈ Finset.Icc 1 (n - 1),
              (∑ i ∈ Finset.Icc 1 d, ((linAlpha3 C t i : ℝ) - (linAlpha5 C t (i - 1) : ℝ))) *
                ((ε / (1 - ε)) ^ (d - 1) - (ε / (1 - ε)) ^ d) := by
          linarith
        exact hsum0
      · have hd0lt : d0 ≤ n - 1 := by omega
        have hterm2' : 0 < ∑ d ∈ Finset.Icc 1 (n - 1),
            (∑ i ∈ Finset.Icc 1 d, ((linAlpha3 C t i : ℝ) - (linAlpha5 C t (i - 1) : ℝ))) *
              ((ε / (1 - ε)) ^ (d - 1) - (ε / (1 - ε)) ^ d) := by
          apply Finset.sum_pos'
          · intro d hd
            have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
            have hd2 : d ≤ n - 1 := (Finset.mem_Icc.mp hd).2
            have hdn : d ≤ n := by omega
            rw [lin_Psi_real C t d hd1]
            have hPd : 0 ≤ (linPsi C t d : ℝ) := by
              exact_mod_cast hge d (by simp [Finset.mem_Icc, hd1, hdn])
            exact mul_nonneg hPd (le_of_lt (r_pow_sub_pos hε0 hε1 hd1))
          · refine ⟨d0, ?_, ?_⟩
            · exact Finset.mem_Icc.mpr ⟨hd01, hd0lt⟩
            · rw [lin_Psi_real C t d0 hd01]
              have hPd : 0 < (linPsi C t d0 : ℝ) := by
                exact_mod_cast hd0gt
              exact mul_pos hPd (r_pow_sub_pos hε0 hε1 hd01)
        have hsum0 : 0 < (∑ i ∈ Finset.Icc 1 n,
            ((linAlpha3 C t i : ℝ) - (linAlpha5 C t (i - 1) : ℝ))) * (ε / (1 - ε)) ^ (n - 1) +
            ∑ d ∈ Finset.Icc 1 (n - 1),
              (∑ i ∈ Finset.Icc 1 d, ((linAlpha3 C t i : ℝ) - (linAlpha5 C t (i - 1) : ℝ))) *
                ((ε / (1 - ε)) ^ (d - 1) - (ε / (1 - ε)) ^ d) := by
          linarith
        exact hsum0
  have hpos : 0 < ((1 - ε) ^ n / 4) * (1 - ε / (1 - ε)) := by
    have hden : 0 < 1 - ε := by linarith
    have h1 : 0 < (1 - ε) ^ n := pow_pos hden n
    have h2 : 0 < (1 : ℝ) - ε / (1 - ε) := by
      have hε0' : 0 < ε / (1 - ε) := div_pos hε0 hden
      have hε1' : ε / (1 - ε) < 1 := by
        rw [div_lt_one hden]
        linarith
      linarith
    positivity
  exact mul_pos hpos hSum

-- Phase F statements (moved from `Statements.lean` so this module can be
-- developed in parallel without touching shared files).  Each placeholder
-- proof hole corresponds to the paper label in its docstring; replace it
-- with a real proof and keep the docstring.

set_option maxHeartbeats 800000

/-- `lemma:cli1` (Lemma 28): support lemmas for the refined binomial inequality. -/
lemma choose_ratio_step (n m : ℕ) (hm : m < n) :
    ((Nat.choose n (m + 1) : ℚ) / Nat.choose n m) = ((n : ℚ) - m) / (m + 1) := by
  have hc : 0 < Nat.choose n m := Nat.choose_pos (by omega)
  have h1 := congrArg (fun x : ℕ => (x : ℚ)) (Nat.choose_succ_right_eq n m)
  have h : (Nat.choose n (m + 1) : ℚ) * (m + 1) =
      (Nat.choose n m : ℚ) * ((n : ℚ) - m) := by
    simpa [Nat.cast_mul, Nat.cast_sub (by omega : m ≤ n)] using h1
  field_simp [hc.ne']
  exact h

lemma choose_ratio_telescope (n m Δ : ℕ) (h : m + Δ ≤ n) :
    (∏ j ∈ Finset.range Δ, ((Nat.choose n (m + j + 1) : ℚ) / Nat.choose n (m + j))) =
      (Nat.choose n (m + Δ) : ℚ) / Nat.choose n m := by
  induction Δ with
  | zero =>
      simp
      have hc : (Nat.choose n m : ℚ) ≠ 0 := by
        exact_mod_cast (Nat.choose_pos (by omega : m ≤ n)).ne'
      rw [div_self hc]
  | succ Δ ih =>
      have hmΔ : m + Δ ≤ n := by omega
      calc
        (∏ j ∈ Finset.range (Δ + 1), ((Nat.choose n (m + j + 1) : ℚ) / Nat.choose n (m + j)))
            = (∏ j ∈ Finset.range Δ, ((Nat.choose n (m + j + 1) : ℚ) / Nat.choose n (m + j))) *
                ((Nat.choose n (m + Δ + 1) : ℚ) / Nat.choose n (m + Δ)) := by
              rw [Finset.prod_range_succ]
        _ = (Nat.choose n (m + Δ) : ℚ) / Nat.choose n m *
              ((Nat.choose n (m + Δ + 1) : ℚ) / Nat.choose n (m + Δ)) := by
              rw [ih hmΔ]
        _ = (Nat.choose n (m + Δ + 1) : ℚ) / Nat.choose n m := by
              have ha : (Nat.choose n (m + Δ) : ℚ) ≠ 0 := by
                exact_mod_cast (Nat.choose_pos (by omega)).ne'
              have hb : (Nat.choose n m : ℚ) ≠ 0 := by
                exact_mod_cast (Nat.choose_pos (by omega : m ≤ n)).ne'
              field_simp [ha, hb]

lemma prod_pos_of_pos (n : ℕ) (r : ℕ → ℚ) (h : ∀ j, j < n → 0 < r j) :
    0 < ∏ j ∈ Finset.range n, r j := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.prod_range_succ]
      exact mul_pos (ih (fun j hj => h j (by omega))) (h n (by omega))

lemma prod_gt_prod_pos (n : ℕ) (r1 r2 : ℕ → ℚ) (hn : 0 < n)
    (h : ∀ j, j < n → 0 < r2 j ∧ r2 j < r1 j) :
    (∏ j ∈ Finset.range n, r1 j) > (∏ j ∈ Finset.range n, r2 j) := by
  induction n with
  | zero => exfalso; omega
  | succ n ih =>
      by_cases hn0 : n = 0
      · subst n
        simp
        exact (h 0 (by omega)).2
      · have hprev : 0 < n := Nat.pos_of_ne_zero hn0
        have hlt1 : (∏ j ∈ Finset.range n, r1 j) > (∏ j ∈ Finset.range n, r2 j) :=
          ih hprev (fun j hj => h j (by omega))
        have hrn1 : 0 < r1 n := lt_trans (h n (by omega)).1 (h n (by omega)).2
        have hrn2 : 0 < r2 n := (h n (by omega)).1
        have hgtn : r2 n < r1 n := (h n (by omega)).2
        have hprod2 : 0 < ∏ j ∈ Finset.range n, r2 j :=
          prod_pos_of_pos n r2 (fun j hj => (h j (by omega)).1)
        have h1 : (∏ j ∈ Finset.range n, r2 j) * r1 n <
            (∏ j ∈ Finset.range n, r1 j) * r1 n :=
          mul_lt_mul_of_pos_right hlt1 hrn1
        have h2 : (∏ j ∈ Finset.range n, r2 j) * r2 n <
            (∏ j ∈ Finset.range n, r2 j) * r1 n :=
          mul_lt_mul_of_pos_left hgtn hprod2
        rw [Finset.prod_range_succ, Finset.prod_range_succ]
        exact lt_trans h2 h1

/-- The even-difference cast: (n1 - n2)/2 in ℚ is ((n1 : ℚ) - n2)/2. -/
lemma cast_half_sub (n1 n2 : ℕ) (hge : n2 ≤ n1) (hpar : Even n1 ↔ Even n2) :
    (((n1 - n2) / 2 : ℕ) : ℚ) = ((n1 : ℚ) - n2) / 2 := by
  by_cases h1 : Even n1
  · have h2 : Even n2 := hpar.mp h1
    rcases h1 with ⟨a, ha⟩
    rcases h2 with ⟨b, hb⟩
    have hab : b ≤ a := by omega
    have hsub : n1 - n2 = 2 * (a - b) := by
      rw [ha, hb]
      omega
    rw [hsub, ha, hb]
    norm_num [Nat.cast_mul, Nat.cast_sub hab]
    ring
  · have ho1 : Odd n1 := Nat.not_even_iff_odd.mp h1
    have ho2 : Odd n2 := Nat.not_even_iff_odd.mp (fun h => h1 (hpar.mpr h))
    rcases ho1 with ⟨a, ha⟩
    rcases ho2 with ⟨b, hb⟩
    have hab : b ≤ a := by omega
    have hsub : n1 - n2 = 2 * (a - b) := by
      rw [ha, hb]
      omega
    rw [hsub, ha, hb]
    norm_num [Nat.cast_mul, Nat.cast_sub hab]
    ring

/-- Core comparison: the binomial product with the larger defect on the larger
`n` is strictly larger (paper `lemma:cli1` (Lemma 28), canonical case: v1 > v2 ≥ 0). -/
lemma choose_product_inequality_core (n1 n2 a b c d : ℕ)
    (hpar : Even n1 ↔ Even n2) (hlt : n1 > n2) (hac : a > c)
    (hbd : d = b + (a - c)) (hcb : c = b + (n1 - n2) / 2)
    (ha1 : a ≤ n1) (hc1 : c ≤ n1) (hb2 : b ≤ n2) (hd2 : d ≤ n2)
    (hbq : (n2 : ℚ) / 2 ≤ b) :
    Nat.choose n1 a * Nat.choose n2 b > Nat.choose n1 c * Nat.choose n2 d := by
  let Δ : ℕ := a - c
  have hΔpos : 0 < Δ := Nat.sub_pos_of_lt hac
  have hΔ : a = c + Δ := by
    simpa [Δ] using (Nat.add_sub_cancel' (le_of_lt hac)).symm
  have hd : d = b + Δ := by
    simpa [Δ] using hbd
  let r1 : ℕ → ℚ := fun j => ((n1 : ℚ) - (c + j : ℚ)) / ((c + j : ℚ) + 1)
  let r2 : ℕ → ℚ := fun j => ((n2 : ℚ) - (b + j : ℚ)) / ((b + j : ℚ) + 1)
  have hc1Δ : c + Δ ≤ n1 := by simpa [hΔ] using ha1
  have hb2Δ : b + Δ ≤ n2 := by simpa [hd] using hd2
  have ht1 : (∏ j ∈ Finset.range Δ, ((Nat.choose n1 (c + j + 1) : ℚ) / Nat.choose n1 (c + j))) =
      (Nat.choose n1 (c + Δ) : ℚ) / Nat.choose n1 c := choose_ratio_telescope n1 c Δ hc1Δ
  have ht2 : (∏ j ∈ Finset.range Δ, ((Nat.choose n2 (b + j + 1) : ℚ) / Nat.choose n2 (b + j))) =
      (Nat.choose n2 (b + Δ) : ℚ) / Nat.choose n2 b := choose_ratio_telescope n2 b Δ hb2Δ
  have hprod1 : (∏ j ∈ Finset.range Δ, ((Nat.choose n1 (c + j + 1) : ℚ) / Nat.choose n1 (c + j))) =
      ∏ j ∈ Finset.range Δ, r1 j := by
    apply Finset.prod_congr rfl
    intro j hj
    have hcj : c + j < n1 := lt_of_lt_of_le (Nat.add_lt_add_left (Finset.mem_range.mp hj) c) hc1Δ
    rw [choose_ratio_step n1 (c + j) hcj]
    simp [r1]
  have hprod2 : (∏ j ∈ Finset.range Δ, ((Nat.choose n2 (b + j + 1) : ℚ) / Nat.choose n2 (b + j))) =
      ∏ j ∈ Finset.range Δ, r2 j := by
    apply Finset.prod_congr rfl
    intro j hj
    have hbj : b + j < n2 := lt_of_lt_of_le (Nat.add_lt_add_left (Finset.mem_range.mp hj) b) hb2Δ
    rw [choose_ratio_step n2 (b + j) hbj]
    simp [r2]
  have hδ : (((n1 - n2) / 2 : ℕ) : ℚ) = ((n1 : ℚ) - n2) / 2 := cast_half_sub n1 n2 (le_of_lt hlt) hpar
  have hδq : 0 < (((n1 - n2) / 2 : ℕ) : ℚ) := by
    have hpos : 0 < n1 - n2 := Nat.sub_pos_of_lt hlt
    have hdiv : 0 < (n1 - n2) / 2 := by
      have hev : Even (n1 - n2) := by
        by_cases h1 : Even n1
        · have h2 : Even n2 := hpar.mp h1
          rcases h1 with ⟨a', ha'⟩
          rcases h2 with ⟨b', hb'⟩
          refine ⟨a' - b', ?_⟩
          rw [ha', hb']
          omega
        · have ho2 : Odd n2 := Nat.not_even_iff_odd.mp (fun h => h1 (hpar.mpr h))
          rcases (Nat.not_even_iff_odd.mp h1) with ⟨a', ha'⟩
          rcases ho2 with ⟨b', hb'⟩
          refine ⟨a' - b', ?_⟩
          rw [ha', hb']
          omega
      rcases hev with ⟨k, hk⟩
      have hkpos : 0 < k := by omega
      rw [hk, ← two_mul k, Nat.mul_div_right k (by decide : 0 < 2)]
      exact hkpos
    exact_mod_cast hdiv
  have hcbq : (c : ℚ) = (b : ℚ) + (((n1 - n2) / 2 : ℕ) : ℚ) := by
    rw [hcb]
    norm_num
  have hcmp : ∀ j, j < Δ → 0 < r2 j ∧ r2 j < r1 j := by
    intro j hj
    let A2 : ℚ := (n2 : ℚ) - (b + j : ℚ)
    let D2 : ℚ := (b + j : ℚ) + 1
    let δ : ℚ := (((n1 - n2) / 2 : ℕ) : ℚ)
    have hD2gtA2 : A2 < D2 := by
      dsimp [A2, D2]
      have h2b : (n2 : ℚ) ≤ 2 * (b : ℚ) := by nlinarith [hbq]
      have hj0 : 0 ≤ (j : ℚ) := by positivity
      nlinarith
    have hstep' : j + 1 ≤ Δ := Nat.succ_le_of_lt hj
    have hle : b + j + 1 ≤ b + Δ := by
      rw [Nat.add_assoc]
      exact Nat.add_le_add_left hstep' b
    have hbjq : (b + j : ℚ) + 1 ≤ (n2 : ℚ) := by
      exact_mod_cast (le_trans hle hb2Δ)
    have hA2pos : 0 < A2 := by
      dsimp [A2]
      nlinarith [hbjq]
    have hD2p : 0 < D2 := by nlinarith [hA2pos, hD2gtA2]
    have hD2dp : 0 < D2 + δ := by positivity
    have hcross : A2 * (D2 + δ) < (A2 + δ) * D2 := by
      have hmul : δ * A2 < δ * D2 := mul_lt_mul_of_pos_left hD2gtA2 hδq
      nlinarith
    have hstep : A2 / D2 < (A2 + δ) / (D2 + δ) := by
      field_simp [hD2p.ne', hD2dp.ne']
      nlinarith [hcross]
    have hA1 : (n1 : ℚ) - (c + j : ℚ) = A2 + δ := by
      rw [hcbq]
      nlinarith [hδ]
    have hD1 : (c + j : ℚ) + 1 = D2 + δ := by
      rw [hcbq]
      nlinarith [hδ]
    constructor
    · rw [show r2 j = A2 / D2 by simp [r2, A2, D2]]
      exact div_pos hA2pos hD2p
    · rw [show r2 j = A2 / D2 by simp [r2, A2, D2]]
      rw [show r1 j = (A2 + δ) / (D2 + δ) by
        change ((n1 : ℚ) - (c + j : ℚ)) / ((c + j : ℚ) + 1) = (A2 + δ) / (D2 + δ)
        rw [hA1, hD1]]
      exact hstep
  have hprod := prod_gt_prod_pos Δ r1 r2 hΔpos hcmp
  have hratio : (Nat.choose n1 a : ℚ) / Nat.choose n1 c >
      (Nat.choose n2 d : ℚ) / Nat.choose n2 b := by
    calc
      (Nat.choose n1 a : ℚ) / Nat.choose n1 c
          = (Nat.choose n1 (c + Δ) : ℚ) / Nat.choose n1 c := by rw [hΔ]
      _ = ∏ j ∈ Finset.range Δ, r1 j := by
            rw [← ht1, hprod1]
      _ > ∏ j ∈ Finset.range Δ, r2 j := hprod
      _ = (Nat.choose n2 (b + Δ) : ℚ) / Nat.choose n2 b := by
            rw [← ht2, hprod2]
      _ = (Nat.choose n2 d : ℚ) / Nat.choose n2 b := by rw [hd]
  have hC1 : 0 < Nat.choose n1 c := Nat.choose_pos hc1
  have hC2 : 0 < Nat.choose n2 b := Nat.choose_pos hb2
  have hQ : (Nat.choose n1 a : ℚ) * (Nat.choose n2 b : ℚ) >
      (Nat.choose n1 c : ℚ) * (Nat.choose n2 d : ℚ) := by
    have hC1q : (Nat.choose n1 c : ℚ) ≠ 0 := by exact_mod_cast hC1.ne'
    have hC2q : (Nat.choose n2 b : ℚ) ≠ 0 := by exact_mod_cast hC2.ne'
    have h1 := hratio
    field_simp [hC1q, hC2q] at h1
    nlinarith
  exact_mod_cast hQ

/-- `lemma:cli1` (Lemma 28) for nonnegative defects v1 ≥ v2 ≥ 0. -/
lemma choose_product_inequality_nonneg (n1 n2 : ℕ) (v1 v2 : ℚ) (a b c d : ℕ)
    (hlt : n1 > n2) (_hpos : 0 < n2) (hpar : Even n1 ↔ Even n2)
    (hbound : (n2 : ℚ) / 2 ≥ |v1|) (hord : |v1| > |v2|)
    (hv1 : 0 ≤ v1) (hv2 : 0 ≤ v2)
    (ha : (n1 : ℚ) / 2 + v1 = a) (hb : (n2 : ℚ) / 2 + v2 = b)
    (hc : (n1 : ℚ) / 2 + v2 = c) (hd : (n2 : ℚ) / 2 + v1 = d) :
    Nat.choose n1 a * Nat.choose n2 b > Nat.choose n1 c * Nat.choose n2 d := by
  have hv1' : v1 = |v1| := (abs_of_nonneg hv1).symm
  have hv2' : v2 = |v2| := (abs_of_nonneg hv2).symm
  have hac : a > c := by
    have hpos' : 0 < (a : ℚ) - c := by
      rw [show (a : ℚ) - c = v1 - v2 by nlinarith [ha, hc]]
      nlinarith [hord, hv1', hv2']
    have hltq : (c : ℚ) < a := by nlinarith [hpos']
    exact_mod_cast hltq
  have hbd : d = b + (a - c) := by
    have hdiff : (d : ℚ) - b = (a : ℚ) - c := by
      rw [show (d : ℚ) - b = v1 - v2 by nlinarith [hb, hd]]
      rw [show (a : ℚ) - c = v1 - v2 by nlinarith [ha, hc]]
    have hge : b ≤ d := by
      have : (b : ℚ) ≤ d := by nlinarith [hdiff, hac]
      exact_mod_cast this
    have hdiff' : ((d - b : ℕ) : ℚ) = ((a - c : ℕ) : ℚ) := by
      rw [Nat.cast_sub hge, Nat.cast_sub (le_of_lt hac)]
      exact hdiff
    have hsub : d - b = a - c := by exact_mod_cast hdiff'
    omega
  have hcb : c = b + (n1 - n2) / 2 := by
    have hc1 : (c : ℚ) - b = ((n1 : ℚ) - n2) / 2 := by nlinarith [hb, hc]
    have hc2 : (c : ℚ) - b = (((n1 - n2) / 2 : ℕ) : ℚ) := by
      rw [cast_half_sub n1 n2 (le_of_lt hlt) hpar]
      exact hc1
    have hge : b ≤ c := by
      have : (b : ℚ) ≤ c := by nlinarith [hc1, hlt]
      exact_mod_cast this
    have hc3 : ((c - b : ℕ) : ℚ) = (((n1 - n2) / 2 : ℕ) : ℚ) := by
      rw [Nat.cast_sub hge]
      exact hc2
    have hsub : c - b = (n1 - n2) / 2 := by exact_mod_cast hc3
    omega
  have hv1le : v1 ≤ (n2 : ℚ) / 2 := by
    have h1 := abs_le.mp hbound
    exact h1.2  -- hmm: h1.2 : v1 ≤ n2/2? abs_le.mp : |v1| ≤ b → -b ≤ v1 ∧ v1 ≤ b
  have hv2le : v2 ≤ (n2 : ℚ) / 2 := by
    have h1 := abs_le.mp hbound
    have h1' : |v1| ≤ (n2 : ℚ) / 2 := by
      rw [← hv1']
      exact h1.2
    have h2 : |v2| ≤ (n2 : ℚ) / 2 := le_trans (le_of_lt hord) h1'
    have h3 := abs_le.mp h2
    exact h3.2
  have ha1 : a ≤ n1 := by
    have hle : (a : ℚ) ≤ n1 := by
      have hn : (n2 : ℚ) < n1 := by exact_mod_cast hlt
      have hmid : (n1 : ℚ) / 2 + (n2 : ℚ) / 2 < n1 := by nlinarith
      nlinarith [ha, hv1le, hmid]
    exact_mod_cast hle
  have hc1 : c ≤ n1 := by
    have hle : (c : ℚ) ≤ n1 := by
      have hn : (n2 : ℚ) < n1 := by exact_mod_cast hlt
      have hmid : (n1 : ℚ) / 2 + (n2 : ℚ) / 2 < n1 := by nlinarith
      nlinarith [hc, hv2le, hmid]
    exact_mod_cast hle
  have hb2 : b ≤ n2 := by
    have hle : (b : ℚ) ≤ n2 := by
      have : (n2 : ℚ) / 2 + (n2 : ℚ) / 2 = n2 := by ring
      nlinarith [hb, hv2le, this]
    exact_mod_cast hle
  have hd2 : d ≤ n2 := by
    have hle : (d : ℚ) ≤ n2 := by
      have : (n2 : ℚ) / 2 + (n2 : ℚ) / 2 = n2 := by ring
      nlinarith [hd, hv1le, this]
    exact_mod_cast hle
  have hbq : (n2 : ℚ) / 2 ≤ b := by
    have : 0 ≤ v2 := hv2
    nlinarith [hb]
  exact choose_product_inequality_core n1 n2 a b c d hpar hlt hac hbd hcb ha1 hc1 hb2 hd2 hbq

/-- Lemma `lemma:cli1` (Lemma 28) (Appendix): refined binomial inequality. -/
theorem choose_product_inequality (n1 n2 : ℕ) (v1 v2 : ℚ) (a b c d : ℕ)
    (hlt : n1 > n2) (hpos : 0 < n2)
    (hpar : (Even n1 ↔ Even n2))
    (hbound : (n2 : ℚ) / 2 ≥ |v1|) (hord : |v1| > |v2|)
    (ha : (n1 : ℚ) / 2 + v1 = a) (hb : (n2 : ℚ) / 2 + v2 = b)
    (hc : (n1 : ℚ) / 2 + v2 = c) (hd : (n2 : ℚ) / 2 + v1 = d) :
    Nat.choose n1 a * Nat.choose n2 b > Nat.choose n1 c * Nat.choose n2 d := by
  have hn : (n2 : ℚ) < n1 := by exact_mod_cast hlt
  have hmid : (n1 : ℚ) / 2 + (n2 : ℚ) / 2 < n1 := by nlinarith
  by_cases hv1 : 0 ≤ v1
  · have hva : |v1| = v1 := abs_of_nonneg hv1
    have hv1le : v1 ≤ (n2 : ℚ) / 2 := (abs_le.mp hbound).2
    by_cases hv2 : 0 ≤ v2
    · exact choose_product_inequality_nonneg n1 n2 v1 v2 a b c d hlt hpos hpar hbound hord hv1 hv2 ha hb hc hd
    · have hv2' : 0 ≤ -v2 := by linarith
      have hord' : |v1| > |-v2| := by simpa [abs_neg] using hord
      have hb2 : b ≤ n2 := by
        have hle : (b : ℚ) ≤ n2 := by
          have h1' : |v1| ≤ (n2 : ℚ) / 2 := by
            rw [hva]
            exact hv1le
          have h2 : |v2| ≤ (n2 : ℚ) / 2 := le_trans (le_of_lt hord) h1'
          have hv2le : v2 ≤ (n2 : ℚ) / 2 := (abs_le.mp h2).2
          have : (n2 : ℚ) / 2 + (n2 : ℚ) / 2 = n2 := by ring
          nlinarith [hb, hv2le, this]
        exact_mod_cast hle
      have hc1 : c ≤ n1 := by
        have hle : (c : ℚ) ≤ n1 := by
          have h1' : |v1| ≤ (n2 : ℚ) / 2 := by
            rw [hva]
            exact hv1le
          have h2 : |v2| ≤ (n2 : ℚ) / 2 := le_trans (le_of_lt hord) h1'
          have hv2le : v2 ≤ (n2 : ℚ) / 2 := (abs_le.mp h2).2
          nlinarith [hc, hv2le, hmid]
        exact_mod_cast hle
      have hb' : (n2 : ℚ) / 2 + (-v2) = (n2 - b : ℕ) := by
        rw [Nat.cast_sub hb2]
        nlinarith [hb]
      have hc' : (n1 : ℚ) / 2 + (-v2) = (n1 - c : ℕ) := by
        rw [Nat.cast_sub hc1]
        nlinarith [hc]
      have hres := choose_product_inequality_nonneg n1 n2 v1 (-v2) a (n2 - b) (n1 - c) d
        hlt hpos hpar hbound hord' hv1 hv2' ha hb' hc' hd
      rw [Nat.choose_symm hb2, Nat.choose_symm hc1] at hres
      exact hres
  · have hv1' : 0 ≤ -v1 := by linarith
    have hord' : |-v1| > |v2| := by simpa [abs_neg] using hord
    have hbound' : (n2 : ℚ) / 2 ≥ |-v1| := by simpa [abs_neg] using hbound
    have ha' : (n1 : ℚ) / 2 + (-v1) = (n1 - a : ℕ) := by
      have hale : a ≤ n1 := by
        have hle : (a : ℚ) ≤ n1 := by nlinarith [ha, hv1, hmid]
        exact_mod_cast hle
      rw [Nat.cast_sub hale]
      nlinarith [ha]
    have hd' : (n2 : ℚ) / 2 + (-v1) = (n2 - d : ℕ) := by
      have hdle : d ≤ n2 := by
        have hle : (d : ℚ) ≤ n2 := by nlinarith [hd, hv1]
        exact_mod_cast hle
      rw [Nat.cast_sub hdle]
      nlinarith [hd]
    have hnv1 : |v1| = -v1 := by simpa [abs_neg] using (abs_of_nonneg hv1')
    have ha1 : a ≤ n1 := by
      have hle : (a : ℚ) ≤ n1 := by
        have hv1le : v1 ≤ (n2 : ℚ) / 2 := (abs_le.mp hbound).2
        nlinarith [ha, hv1le, hmid]
      exact_mod_cast hle
    have hd2 : d ≤ n2 := by
      have hle : (d : ℚ) ≤ n2 := by
        have hv1le : v1 ≤ (n2 : ℚ) / 2 := (abs_le.mp hbound).2
        have : (n2 : ℚ) / 2 + (n2 : ℚ) / 2 = n2 := by ring
        nlinarith [hd, hv1le, this]
      exact_mod_cast hle
    by_cases hv2 : 0 ≤ v2
    · have hres := choose_product_inequality_nonneg n1 n2 (-v1) v2 (n1 - a) b c (n2 - d)
        hlt hpos hpar hbound' hord' hv1' hv2 ha' hb hc hd'
      rw [Nat.choose_symm ha1, Nat.choose_symm hd2] at hres
      exact hres
    · have hv2' : 0 ≤ -v2 := by linarith
      have hord'' : |-v1| > |-v2| := by simpa [abs_neg] using hord
      have hb2 : b ≤ n2 := by
        have hle : (b : ℚ) ≤ n2 := by
          have h1 : |v1| ≤ (n2 : ℚ) / 2 := by
            have h2 := abs_le.mp hbound
            rw [hnv1]
            linarith [h2.1]
          have h2 : |v2| ≤ (n2 : ℚ) / 2 := le_trans (le_of_lt hord) h1
          have hv2le : v2 ≤ (n2 : ℚ) / 2 := (abs_le.mp h2).2
          have : (n2 : ℚ) / 2 + (n2 : ℚ) / 2 = n2 := by ring
          nlinarith [hb, hv2le, this]
        exact_mod_cast hle
      have hc1 : c ≤ n1 := by
        have hle : (c : ℚ) ≤ n1 := by
          have h1 : |v1| ≤ (n2 : ℚ) / 2 := by
            have h2 := abs_le.mp hbound
            rw [hnv1]
            linarith [h2.1]
          have h2 : |v2| ≤ (n2 : ℚ) / 2 := le_trans (le_of_lt hord) h1
          have hv2le : v2 ≤ (n2 : ℚ) / 2 := (abs_le.mp h2).2
          nlinarith [hc, hv2le, hmid]
        exact_mod_cast hle
      have hb' : (n2 : ℚ) / 2 + (-v2) = (n2 - b : ℕ) := by
        rw [Nat.cast_sub hb2]
        nlinarith [hb]
      have hc' : (n1 : ℚ) / 2 + (-v2) = (n1 - c : ℕ) := by
        rw [Nat.cast_sub hc1]
        nlinarith [hc]
      have hres := choose_product_inequality_nonneg n1 n2 (-v1) (-v2) (n1 - a) (n2 - b) (n1 - c) (n2 - d)
        hlt hpos hpar hbound' hord'' hv1' hv2' ha' hb' hc' hd'
      rw [Nat.choose_symm ha1, Nat.choose_symm hb2, Nat.choose_symm hc1, Nat.choose_symm hd2] at hres
      exact hres

set_option maxHeartbeats 800000
/-- Case 3, strict sub-case, in range `m ≤ d ≤ n5+m−1`: the closed forms of
eq. cli3 and eq. cli2 are compared termwise with `lemma:cli1` (Lemma 28)
(`choose_product_inequality`), giving `α³(d+1) ≥ α⁵(d)`. -/
lemma lin_alpha3_succ_ge_alpha5 {n3 n5 n6 d k m : ℕ} (hn3 : 0 < n3)
    (hpar : Even (n5 + n6)) (hk : n5 + n6 = 2 * k) (hm : n3 + n6 = 2 * m + 1)
    (hge : m ≤ d) (hn56 : n5 ≤ n6) (hn53 : n5 ≤ n3)
    (hln : d ≤ n5 + m - 1) (hn5 : 0 < n5) (hgt : n5 + 1 < n3)
    (hpar35 : Even (n3 - 1) ↔ Even n5) :
    linAlpha3 (linearCode n3 n5 n6) ⟨0, by omega⟩ (d + 1) ≥
      linAlpha5 (linearCode n3 n5 n6) ⟨0, by omega⟩ d := by
  have hkmlt : k < m := by
    have h1 : 2 * (m - k) ≥ 1 := by omega
    omega
  have hkd : k ≤ d := by omega
  have hge3 : 2 * (d + 1) ≥ n3 + n5 := by
    have h1 : 2 * m + 2 ≤ 2 * (d + 1) := by omega
    have h2 : n3 + n5 + 1 ≤ 2 * m + 2 := by omega
    omega
  have hmd : m ≤ d + 1 := by omega
  have hln3 : d + 1 ≤ n5 + m := by omega
  rw [linAlpha3_closed (n3 := n3) (n5 := n5) (n6 := n6) (d := d) (k := k) (m := m)
    hn3 hpar hk hm hge3 hn56 hn53 hmd hln3 hkd]
  rw [linAlpha5_closed (n3 := n3) (n5 := n5) (n6 := n6) (d := d) (k := k) (m := m)
    hn3 hpar hk hm hge hn56 hn53 hln]
  have hmq : (n3 : ℚ) + n6 = 2 * m + 1 := by exact_mod_cast hm
  have hkq : (n5 : ℚ) + n6 = 2 * k := by exact_mod_cast hk
  have hS : (∑ w ∈ Finset.Icc (d + 1 - m) (n5 + m - (d + 1)),
        Nat.choose (n3 - 1) (d - k) * (Nat.choose n5 w * Nat.choose n6 (k - w))) ≥
      (∑ w ∈ Finset.Icc (d + 1 - m) (n5 + m - (d + 1)),
        Nat.choose (n3 - 1) (w + m - k) * (Nat.choose n5 (d - m) * Nat.choose n6 (k - w))) := by
    by_cases hne : d + 1 - m ≤ n5 + m - (d + 1)
    · apply Finset.sum_le_sum
      intro w hw
      have hwrange : d + 1 - m ≤ w ∧ w ≤ n5 + m - (d + 1) := (Finset.mem_Icc.mp hw)
      let v1 : ℚ := (d : ℚ) - m - (n5 : ℚ) / 2
      let v2 : ℚ := (w : ℚ) - (n5 : ℚ) / 2
      have hde : (d : ℚ) ≤ (m : ℚ) + (n5 : ℚ) / 2 - 1 := by
        have h2d : 2 * (d : ℚ) + 2 ≤ (n5 : ℚ) + 2 * m := by
          have h2dn : 2 * d + 2 ≤ n5 + 2 * m := by omega
          exact_mod_cast h2dn
        linarith
      have hv1neg : v1 < 0 := by
        dsimp [v1]
        linarith [hde]
      have hv1abs : |v1| = (m : ℚ) + (n5 : ℚ) / 2 - d := by
        rw [abs_of_neg hv1neg]
        dsimp [v1]
        ring
      have hb1 : -((n5 : ℚ) / 2) ≤ v1 := by
        dsimp [v1]
        have hgeq : (m : ℚ) ≤ d := by exact_mod_cast hge
        linarith
      have hb2 : v1 ≤ (n5 : ℚ) / 2 := by
        dsimp [v1]
        have hdn : d ≤ n5 + m := by omega
        have hdnq : (d : ℚ) ≤ (n5 : ℚ) + m := by exact_mod_cast hdn
        linarith
      have hbound : (n5 : ℚ) / 2 ≥ |v1| := abs_le.mpr ⟨hb1, hb2⟩
      have hwU : (w : ℚ) ≤ (n5 : ℚ) + m - d - 1 := by
        have hwUn : w ≤ n5 + m - (d + 1) := hwrange.2
        have hle : d + 1 ≤ n5 + m := by omega
        have hcast : ((n5 + m - (d + 1) : ℕ) : ℚ) = (n5 : ℚ) + m - d - 1 := by
          rw [Nat.cast_sub hle]
          push_cast
          ring
        have hwUn' : (w : ℚ) ≤ ((n5 + m - (d + 1) : ℕ) : ℚ) := by exact_mod_cast hwUn
        rwa [hcast] at hwUn'
      have hwLq : (d : ℚ) + 1 - m ≤ w := by
        have hwL : (d + 1 - m : ℕ) ≤ w := hwrange.1
        have hleL : m ≤ d + 1 := hmd
        have hcastL : ((d + 1 - m : ℕ) : ℚ) = (d : ℚ) + 1 - m := by
          rw [Nat.cast_sub hleL]
          push_cast
          ring
        have h' : ((d + 1 - m : ℕ) : ℚ) ≤ w := by exact_mod_cast hwL
        rwa [hcastL] at h'
      have hw1 : w - (n5 : ℚ) / 2 < (m : ℚ) + (n5 : ℚ) / 2 - d := by
        linarith [hwU]
      have hw2' : -((m : ℚ) + (n5 : ℚ) / 2 - d) < w - (n5 : ℚ) / 2 := by
        linarith [hwLq]
      have hord : |v1| > |v2| := by
        rw [hv1abs]
        dsimp [v2]
        exact abs_lt.mpr ⟨hw2', hw1⟩
      have ha : ((n3 - 1 : ℕ) : ℚ) / 2 + v1 = (d - k : ℕ) := by
        dsimp [v1]
        rw [Nat.cast_sub hkd]
        rw [Nat.cast_sub (by omega : 1 ≤ n3)]
        have hmq : (n3 : ℚ) = 2 * m + 1 - n6 := by
          have h : (n3 : ℚ) + n6 = 2 * m + 1 := by exact_mod_cast hm
          linarith
        have hkq : (n5 : ℚ) = 2 * k - n6 := by
          have h : (n5 : ℚ) + n6 = 2 * k := by exact_mod_cast hk
          linarith
        rw [hmq, hkq]
        push_cast
        ring
      have hb : (n5 : ℚ) / 2 + v2 = (w : ℕ) := by
        dsimp [v2]
        ring_nf
      have hc : ((n3 - 1 : ℕ) : ℚ) / 2 + v2 = (w + m - k : ℕ) := by
        dsimp [v2]
        have hwmk : k ≤ w + m := by omega
        rw [Nat.cast_sub hwmk]
        rw [Nat.cast_sub (by omega : 1 ≤ n3)]
        have hmq : (n3 : ℚ) = 2 * m + 1 - n6 := by
          have h : (n3 : ℚ) + n6 = 2 * m + 1 := by exact_mod_cast hm
          linarith
        have hkq : (n5 : ℚ) = 2 * k - n6 := by
          have h : (n5 : ℚ) + n6 = 2 * k := by exact_mod_cast hk
          linarith
        rw [hmq, hkq]
        push_cast
        ring
      have hdd : (n5 : ℚ) / 2 + v1 = (d - m : ℕ) := by
        dsimp [v1]
        rw [Nat.cast_sub hge]
        ring
      have hterm := choose_product_inequality (n1 := n3 - 1) (n2 := n5) (v1 := v1) (v2 := v2)
        (a := d - k) (b := w) (c := w + m - k) (d := d - m)
        (by omega : n3 - 1 > n5) hn5 hpar35 hbound hord ha hb hc hdd
      exact (by simpa [mul_assoc] using
        Nat.mul_le_mul_right (Nat.choose n6 (k - w)) (le_of_lt hterm))
    · have hempty : Finset.Icc (d + 1 - m) (n5 + m - (d + 1)) = ∅ := by
        rw [Finset.Icc_eq_empty_iff]
        omega
      simp [hempty]
  have hSle : (∑ w ∈ Finset.Icc (d + 1 - m) (n5 + m - (d + 1)),
        Nat.choose (n3 - 1) (w + m - k) * (Nat.choose n5 (d - m) * Nat.choose n6 (k - w))) ≤
      (∑ w ∈ Finset.Icc (d + 1 - m) (n5 + m - (d + 1)),
        Nat.choose (n3 - 1) (d - k) * (Nat.choose n5 w * Nat.choose n6 (k - w))) := hS
  omega

/-- In the strict case `n3 > n5+1`, `α³(m) > 0` (the paper's
`Y3((n−1)/2, 1)` witness at `d = m−1`): the weight-fixed subfilter with
`w3 = m−k`, `w5 = 0`, `w6 = k` is nonempty. -/
lemma linAlpha3_pos_at_m {n3 n5 n6 k m : ℕ} (hn3 : 0 < n3)
    (_hpar : Even (n5 + n6)) (hk : n5 + n6 = 2 * k) (hm : n3 + n6 = 2 * m + 1)
    (hn56 : n5 ≤ n6) (_hn53 : n5 ≤ n3) (hgt : n5 + 1 < n3) :
    0 < linAlpha3 (linearCode n3 n5 n6) ⟨0, by omega⟩ m := by
  have hkmlt : k < m := by
    have h1 : 2 * (m - k) ≥ 1 := by omega
    omega
  have hw3pos : 1 ≤ m - k := by omega
  have hw3idx : m - k ≤ n3 - 1 := by omega
  have hk6 : k ≤ n6 := by omega
  have hcol : linearCode n3 n5 n6 ⟨0, by omega⟩ = col3 := by
    simp [linearCode, hn3]
  have hcount : 0 < (Finset.univ.filter fun y : Word (n3 + n5 + n6) =>
      y ⟨0, by omega⟩ = true ∧ w_i (linearCode n3 n5 n6) 3 y = m - k ∧
        w_i (linearCode n3 n5 n6) 5 y = 0 ∧ w_i (linearCode n3 n5 n6) 6 y = k).card := by
    rw [linear_count_words n3 n5 n6 (m - k) 0 k hn3 hw3pos]
    have h1 : 0 < Nat.choose (n3 - 1) (m - k - 1) := Nat.choose_pos (by omega)
    have h2 : 0 < Nat.choose n5 0 := by simp
    have h3 : 0 < Nat.choose n6 k := Nat.choose_pos hk6
    positivity
  have hsub : (Finset.univ.filter fun y : Word (n3 + n5 + n6) =>
      y ⟨0, by omega⟩ = true ∧ w_i (linearCode n3 n5 n6) 3 y = m - k ∧
        w_i (linearCode n3 n5 n6) 5 y = 0 ∧ w_i (linearCode n3 n5 n6) 6 y = k) ⊆
      (Finset.univ.filter fun y : Word (n3 + n5 + n6) =>
        linY3 (linearCode n3 n5 n6) ⟨0, by omega⟩ y ∧ dCode (linearCode n3 n5 n6) y = m ∧
          y ⟨0, by omega⟩ = true) := by
    intro y hy
    rcases (Finset.mem_filter.mp hy).2 with ⟨hyt, hw3, hw5, hw6⟩
    have hdRow0 : dRow (linearCode n3 n5 n6) ⟨0, by decide⟩ y =
        w_i (linearCode n3 n5 n6) 3 y + w_i (linearCode n3 n5 n6) 5 y +
          w_i (linearCode n3 n5 n6) 6 y := by
      simpa using (linear_dRow0 (n3 := n3) (n5 := n5) (n6 := n6) y)
    have hdRow1 : dRow (linearCode n3 n5 n6) ⟨1, by decide⟩ y =
        w_i (linearCode n3 n5 n6) 3 y + (n5 - w_i (linearCode n3 n5 n6) 5 y) +
          (n6 - w_i (linearCode n3 n5 n6) 6 y) := by
      simpa using (linear_dRow1 (n3 := n3) (n5 := n5) (n6 := n6) y)
    have hdRow2 : dRow (linearCode n3 n5 n6) ⟨2, by decide⟩ y =
        (n3 - w_i (linearCode n3 n5 n6) 3 y) + w_i (linearCode n3 n5 n6) 5 y +
          (n6 - w_i (linearCode n3 n5 n6) 6 y) := by
      simpa using (linear_dRow2 (n3 := n3) (n5 := n5) (n6 := n6) y)
    have hdRow3 : dRow (linearCode n3 n5 n6) ⟨3, by decide⟩ y =
        (n3 - w_i (linearCode n3 n5 n6) 3 y) + (n5 - w_i (linearCode n3 n5 n6) 5 y) +
          w_i (linearCode n3 n5 n6) 6 y := by
      simpa using (linear_dRow3 (n3 := n3) (n5 := n5) (n6 := n6) y)
    have hd0 : dRow (linearCode n3 n5 n6) ⟨0, by decide⟩ y = m := by
      rw [hdRow0, hw3, hw5, hw6]
      omega
    have hd1 : dRow (linearCode n3 n5 n6) ⟨1, by decide⟩ y = m := by
      rw [hdRow1, hw3, hw5, hw6]
      omega
    have hd2 : m ≤ dRow (linearCode n3 n5 n6) ⟨2, by decide⟩ y := by
      rw [hdRow2, hw3, hw5, hw6]
      omega
    have hd3 : m ≤ dRow (linearCode n3 n5 n6) ⟨3, by decide⟩ y := by
      rw [hdRow3, hw3, hw5, hw6]
      omega
    have hY : linY3 (linearCode n3 n5 n6) ⟨0, by omega⟩ y := by
      apply linY3_weights_true y ⟨0, by omega⟩ hcol hyt
      · rw [hd0, hd1]
      · rw [hd0]
        exact hd2
      · rw [hd0]
        exact hd3
    have hdC : dCode (linearCode n3 n5 n6) y = m := by
      change min (dRow (linearCode n3 n5 n6) ⟨0, by decide⟩ y)
          (min (dRow (linearCode n3 n5 n6) ⟨1, by decide⟩ y)
            (min (dRow (linearCode n3 n5 n6) ⟨2, by decide⟩ y) (dRow (linearCode n3 n5 n6) ⟨3, by decide⟩ y))) =
          m
      rw [hd0, hd1]
      rw [min_eq_left (le_min hd2 hd3)]
      simp
    exact Finset.mem_filter.mpr ⟨by simp, ⟨hY, hdC, hyt⟩⟩
  have hcard : 0 < (Finset.univ.filter fun y : Word (n3 + n5 + n6) =>
      linY3 (linearCode n3 n5 n6) ⟨0, by omega⟩ y ∧ dCode (linearCode n3 n5 n6) y = m ∧
        y ⟨0, by omega⟩ = true).card :=
    lt_of_lt_of_le hcount (Finset.card_le_card hsub)
  rw [linAlpha3_eq_two_mul m hn3]
  positivity

/-- Ψ_d telescopes to the pointwise differences α³(i+1) − α⁵(i). -/
lemma linPsi_eq_sum_diff {n : ℕ} (C : Code n) (t : Fin n) (d : ℕ) (hd : 1 ≤ d) :
    linPsi C t d =
      ∑ i ∈ Finset.Icc 0 (d - 1), ((linAlpha3 C t (i + 1) : ℤ) - (linAlpha5 C t i : ℤ)) := by
  unfold linPsi
  have hre : (∑ i ∈ Finset.Icc 1 d, (linAlpha3 C t i : ℤ)) =
      ∑ j ∈ Finset.Icc 0 (d - 1), (linAlpha3 C t (j + 1) : ℤ) := by
    refine Finset.sum_bij (fun i _ => i - 1) ?_ ?_ ?_ ?_
    · intro i hi
      simp [Finset.mem_Icc] at hi ⊢
      omega
    · intro a ha b hb hab
      have ha1 : 1 ≤ a := (Finset.mem_Icc.mp ha).1
      have hb1 : 1 ≤ b := (Finset.mem_Icc.mp hb).1
      omega
    · intro j hj
      refine ⟨j + 1, ?_, ?_⟩
      · have hj1 : j ≤ d - 1 := (Finset.mem_Icc.mp hj).2
        have hdsub : d - 1 + 1 = d := Nat.sub_add_cancel hd
        have hle' : j + 1 ≤ d - 1 + 1 := Nat.succ_le_succ hj1
        have hle : j + 1 ≤ d := by rwa [hdsub] at hle'
        simp [Finset.mem_Icc, hle]
      · have hsub : (j + 1) - 1 = j := by omega
        rw [hsub]
    · intro i hi
      have hsub : i - 1 + 1 = i := Nat.sub_add_cancel (Finset.mem_Icc.mp hi).1
      rw [hsub]
  rw [hre, ← Finset.sum_sub_distrib]

/-- If every pointwise difference is nonnegative, Ψ_d ≥ 0. -/
lemma linPsi_nonneg_of_succ_ge {n : ℕ} (C : Code n) (t : Fin n) (d : ℕ) (hd : 1 ≤ d)
    (h : ∀ i : ℕ, i < d → linAlpha3 C t (i + 1) ≥ linAlpha5 C t i) :
    0 ≤ linPsi C t d := by
  rw [linPsi_eq_sum_diff C t d hd]
  exact Finset.sum_nonneg (fun i hi => sub_nonneg.mpr (by
    have hsub : d - 1 + 1 = d := Nat.sub_add_cancel hd
    have hle' : i + 1 ≤ d - 1 + 1 := Nat.succ_le_succ (Finset.mem_Icc.mp hi).2
    have hid : i < d := by
      have hle : i + 1 ≤ d := by rwa [hsub] at hle'
      exact Nat.lt_of_succ_le hle
    exact_mod_cast h i hid))

/-- If some pointwise difference is positive and all are nonnegative, Ψ_d > 0. -/
lemma linPsi_pos_of_succ_gt {n : ℕ} (C : Code n) (t : Fin n) (d : ℕ) (hd : 1 ≤ d)
    (i0 : ℕ) (hi0 : i0 < d)
    (hgt : linAlpha3 C t (i0 + 1) > linAlpha5 C t i0)
    (h : ∀ i : ℕ, i < d → linAlpha3 C t (i + 1) ≥ linAlpha5 C t i) :
    0 < linPsi C t d := by
  rw [linPsi_eq_sum_diff C t d hd]
  have hnonneg : ∀ i ∈ Finset.Icc 0 (d - 1),
      0 ≤ (linAlpha3 C t (i + 1) : ℤ) - (linAlpha5 C t i : ℤ) := by
    intro i hi
    have hsub : d - 1 + 1 = d := Nat.sub_add_cancel hd
    have hle' : i + 1 ≤ d - 1 + 1 := Nat.succ_le_succ (Finset.mem_Icc.mp hi).2
    have hid : i < d := by
      have hle : i + 1 ≤ d := by rwa [hsub] at hle'
      exact Nat.lt_of_succ_le hle
    exact sub_nonneg.mpr (by exact_mod_cast h i hid)
  have hmem : i0 ∈ Finset.Icc 0 (d - 1) := by
    simp [Finset.mem_Icc]
    exact Nat.le_pred_of_lt hi0
  have hle := Finset.single_le_sum hnonneg hmem
  have hpos : 0 < (linAlpha3 C t (i0 + 1) : ℤ) - (linAlpha5 C t i0 : ℤ) :=
    sub_pos.mpr (by exact_mod_cast hgt)
  exact lt_of_lt_of_le hpos hle

/-- Pointwise equality α³(d+1) = α⁵(d) for all `d`, in the equality
sub-case `n3 = n5+1` of `thm:linearcompare` (Theorem 12) case 3. -/
lemma lin_alpha3_succ_eq_alpha5_pointwise {n3 n5 n6 d k m : ℕ} (hn3 : 0 < n3)
    (hpar : Even (n5 + n6)) (hk : n5 + n6 = 2 * k) (hm : n3 + n6 = 2 * m + 1)
    (hn56 : n5 ≤ n6) (hn53 : n5 ≤ n3) (heq : n3 = n5 + 1) :
    linAlpha3 (linearCode n3 n5 n6) ⟨0, by omega⟩ (d + 1) =
      linAlpha5 (linearCode n3 n5 n6) ⟨0, by omega⟩ d := by
  have hkm : k = m := by
    have h1 : n5 + n6 = 2 * m := by omega
    have h2 : 2 * k = 2 * m := by omega
    omega
  by_cases hlt : d < m
  · rw [linAlpha3_zero_of_lt_m_eq hn3 hpar hk hm (by omega : d + 1 ≤ m) hkm]
    rw [linAlpha5_zero_of_lt_m hn3 hm hlt]
  · have hge : m ≤ d := by omega
    by_cases hbig : n5 + m ≤ d
    · rw [linAlpha3_zero_of_ge_n5m hn3 hpar hk hm hbig]
      rw [linAlpha5_zero_of_ge_n5m hn3 hpar hk hm hn56 hn53 hbig]
    · have hln : d ≤ n5 + m - 1 := by omega
      by_cases hn5 : 0 < n5
      · exact lin_alpha3_succ_eq_alpha5 hn3 hpar hk hm hge hn56 hn53 hln hn5 heq
      · omega

/-- Pointwise comparison α³(d+1) ≥ α⁵(d) for all `d`, in the strict
sub-case `n3 > n5+1` of `thm:linearcompare` (Theorem 12) case 3. -/
lemma lin_alpha3_succ_ge_alpha5_pointwise {n3 n5 n6 d k m : ℕ} (hn3 : 0 < n3)
    (hpar : Even (n5 + n6)) (hk : n5 + n6 = 2 * k) (hm : n3 + n6 = 2 * m + 1)
    (hn56 : n5 ≤ n6) (hn53 : n5 ≤ n3) (hgt : n5 + 1 < n3)
    (hpar35 : Even (n3 - 1) ↔ Even n5) :
    linAlpha3 (linearCode n3 n5 n6) ⟨0, by omega⟩ (d + 1) ≥
      linAlpha5 (linearCode n3 n5 n6) ⟨0, by omega⟩ d := by
  by_cases hlt : d < m
  · rw [linAlpha5_zero_of_lt_m hn3 hm hlt]
    exact Nat.zero_le _
  · have hge : m ≤ d := by omega
    by_cases hbig : n5 + m ≤ d
    · rw [linAlpha5_zero_of_ge_n5m hn3 hpar hk hm hn56 hn53 hbig]
      exact Nat.zero_le _
    · have hln : d ≤ n5 + m - 1 := by omega
      by_cases hn5 : 0 < n5
      · exact lin_alpha3_succ_ge_alpha5 hn3 hpar hk hm hge hn56 hn53 hln hn5 hgt hpar35
      · omega

/-- In the strict case-3 sub-case, `m = (n3+n6−1)/2 ≥ 1`. -/
lemma lin_m_ge_one_of_case3 {n3 n5 n6 m : ℕ} (hgt : n5 + 1 < n3)
    (hm : n3 + n6 = 2 * m + 1) : 1 ≤ m := by
  have hn3ge : 2 ≤ n3 := by omega
  have h36 : 2 ≤ n3 + n6 := by omega
  omega

/-- In case 3, `m = (n3+n6−1)/2 ≤ n`. -/
lemma lin_m_le_n_of_case3 {n3 n5 n6 m : ℕ} (hm : n3 + n6 = 2 * m + 1) :
    m ≤ n3 + n5 + n6 := by
  have h1 : 2 * m + 1 ≤ n3 + n5 + n6 := by omega
  omega

/-- Case 3 of `thm:linearcompare` (Theorem 12): when `n5 ≤ min(n3,n6)` and
`n3−1, n5, n6` have the same parity, `n3 = n5+1` gives equality and
`n3 > n5+1` gives a strict improvement. -/
lemma linear_compare_case3 {n3 n5 n6 : ℕ} (hn3 : n3 > 0)
    (h53 : n5 ≤ n3) (h56 : n5 ≤ n6) (hpar : SameParity (n3 - 1) n5 n6) :
    (n3 = n5 + 1 → UniversalEqual (replaceColumn (linearCode n3 n5 n6) ⟨0, by omega⟩ col5)
      (linearCode n3 n5 n6)) ∧
    (n3 > n5 + 1 → UniversalStrictBetter (replaceColumn (linearCode n3 n5 n6) ⟨0, by omega⟩ col5)
      (linearCode n3 n5 n6)) := by
  rcases hpar with ⟨h35, h56'⟩
  have hpar56 : Even (n5 + n6) := Nat.even_add.mpr h56'
  rcases hpar56 with ⟨k, hk⟩
  have hpar56e : Even (n5 + n6) := ⟨k, hk⟩
  have hk2 : n5 + n6 = 2 * k := by
    rw [two_mul]
    exact hk
  have hodd36 : Odd (n3 + n6) := by
    rw [← Nat.not_even_iff_odd]
    intro heven
    have hiff : Even n3 ↔ Even n6 := Nat.even_add.mp heven
    have h31 : Even (n3 - 1) ↔ Even n6 := h35.trans h56'
    have hsame : Even (n3 - 1) ↔ Even n3 := h31.trans hiff.symm
    by_cases hn3e : Even n3
    · have hn31 : Even (n3 - 1) := hsame.mpr hn3e
      rcases hn3e with ⟨a, ha⟩
      rcases hn31 with ⟨b, hb⟩
      omega
    · have hn31 : Even (n3 - 1) := by
        have hn3o : Odd n3 := Nat.not_even_iff_odd.mp hn3e
        rcases hn3o with ⟨a, ha⟩
        refine ⟨a, ?_⟩
        omega
      exact hn3e (hsame.mp hn31)
  rcases hodd36 with ⟨m, hm⟩
  let n := n3 + n5 + n6
  let C : Code n := linearCode n3 n5 n6
  let C' : Code n := replaceColumn C ⟨0, by omega⟩ col5
  have hcol : C ⟨0, by omega⟩ = col3 := by
    simp [C, linearCode]
    omega
  have hcol' : C' ⟨0, by omega⟩ = col5 := by
    simp [C', C, replaceColumn]
  have hsameC : ∀ u : Fin n, u ≠ ⟨0, by omega⟩ → C' u = C u := by
    intro u hu
    simp [C', C, replaceColumn, hu]
  constructor
  · intro heq
    have hΨ : ∀ d ∈ Finset.Icc 1 n, linPsi C ⟨0, by omega⟩ d = 0 := by
      intro d hd
      rw [linPsi_eq_sum_diff C ⟨0, by omega⟩ d (Finset.mem_Icc.mp hd).1]
      apply Finset.sum_eq_zero
      intro i hi
      have hdiff : linAlpha3 C ⟨0, by omega⟩ (i + 1) = linAlpha5 C ⟨0, by omega⟩ i := by
        simpa [C] using (lin_alpha3_succ_eq_alpha5_pointwise (n3 := n3) (n5 := n5) (n6 := n6)
          (d := i) (k := k) (m := m) hn3 hpar56e hk2 hm h56 h53 heq)
      rw [hdiff]
      ring
    exact lin_cumulative_criterion C C' ⟨0, by omega⟩ hcol hcol' hsameC hΨ
  · intro hgt
    have hge : ∀ i : ℕ, i < n → linAlpha3 C ⟨0, by omega⟩ (i + 1) ≥ linAlpha5 C ⟨0, by omega⟩ i := by
      intro i hi
      simpa [C] using (lin_alpha3_succ_ge_alpha5_pointwise (n3 := n3) (n5 := n5) (n6 := n6)
        (d := i) (k := k) (m := m) hn3 hpar56e hk2 hm h56 h53 hgt h35)
    have hΨge : ∀ d ∈ Finset.Icc 1 n, 0 ≤ linPsi C ⟨0, by omega⟩ d := by
      intro d hd
      exact linPsi_nonneg_of_succ_ge C ⟨0, by omega⟩ d (Finset.mem_Icc.mp hd).1
        (fun i hi => hge i (Nat.lt_of_lt_of_le hi (Finset.mem_Icc.mp hd).2))
    have hmpos : 0 < linAlpha3 C ⟨0, by omega⟩ m := by
      simpa [C] using (linAlpha3_pos_at_m (n3 := n3) (n5 := n5) (n6 := n6) (k := k) (m := m)
        hn3 hpar56e hk2 hm h56 h53 hgt)
    have h5zero : linAlpha5 C ⟨0, by omega⟩ (m - 1) = 0 := by
      simpa [C] using (linAlpha5_zero_of_lt_m (n3 := n3) (n5 := n5) (n6 := n6) (d := m - 1) (m := m)
        hn3 hm (by omega : m - 1 < m))
    have hmgt : linAlpha3 C ⟨0, by omega⟩ m > linAlpha5 C ⟨0, by omega⟩ (m - 1) := by
      rw [h5zero]
      exact hmpos
    have hΨpos : ∃ d ∈ Finset.Icc 1 n, 0 < linPsi C ⟨0, by omega⟩ d := by
      refine ⟨m, ?_, ?_⟩
      · have h1 : 1 ≤ m := lin_m_ge_one_of_case3 hgt hm
        have h2 : m ≤ n := lin_m_le_n_of_case3 hm
        exact Finset.mem_Icc.mpr ⟨h1, h2⟩
      · have h1 : 1 ≤ m := lin_m_ge_one_of_case3 hgt hm
        have hmm : m - 1 + 1 = m := Nat.sub_add_cancel h1
        have hmm1 : m - 1 < m := Nat.sub_lt (by omega : 0 < m) (by decide : 0 < 1)
        have hmn : m ≤ n := by simpa [n] using (lin_m_le_n_of_case3 hm)
        exact linPsi_pos_of_succ_gt C ⟨0, by omega⟩ m (lin_m_ge_one_of_case3 hgt hm) (m - 1) hmm1
          (by simpa [hmm] using hmgt)
          (fun i hi => hge i (Nat.lt_of_lt_of_le hi hmn))
    exact lin_cumulative_strict C C' ⟨0, by omega⟩ hcol hcol' hsameC hΨge hΨpos

/-- Applying a cast of a `Code` to an index first transports the index. -/
lemma cast_code_apply {m n : ℕ} (h : m = n) (f : Code m) (x : Fin n) :
    (cast (congrArg Code h) f) x = f (Fin.cast h.symm x) := by
  subst h
  simp

/-- `replaceColumn (C(n3,n5,n6)) 0 col5` is equivalent to the canonical
`C(n3−1,n5+1,n6)` (swap the replaced first column with the first remaining
type-3 column). -/
lemma replace_linear_3_5_equiv (n3 n5 n6 : ℕ) (hn3 : 0 < n3) :
    let n := n3 + n5 + n6
    Equivalent (replaceColumn (linearCode n3 n5 n6) ⟨0, by omega⟩ col5)
      (cast (congrArg Code (by omega : (n3 - 1) + (n5 + 1) + n6 = n))
        (linearCode (n3 - 1) (n5 + 1) n6)) := by
  intro n
  let h : (n3 - 1) + (n5 + 1) + n6 = n := by omega
  let t0 : Fin n := ⟨0, by omega⟩
  let t1 : Fin n := ⟨n3 - 1, by omega⟩
  refine ⟨Equiv.refl (Fin 4), Equiv.swap t0 t1, fun _ => false, ?_⟩
  intro t
  have hcast : (cast (congrArg Code h) (linearCode (n3 - 1) (n5 + 1) n6)) (Equiv.swap t0 t1 t) =
      (linearCode (n3 - 1) (n5 + 1) n6) (Fin.cast h.symm (Equiv.swap t0 t1 t)) := by
    exact cast_code_apply h (linearCode (n3 - 1) (n5 + 1) n6) (Equiv.swap t0 t1 t)
  rw [hcast]
  have hval : ∀ x : Fin n, (Fin.cast h.symm x).val = x.val := by
    intro x
    rfl
  by_cases ht0 : t = t0
  · subst ht0
    have hswap : Equiv.swap t0 t1 t0 = t1 := Equiv.swap_apply_left t0 t1
    rw [hswap]
    have hL : (linearCode (n3 - 1) (n5 + 1) n6) (Fin.cast h.symm t1) = col5 := by
      have huval : (Fin.cast h.symm t1).val = n3 - 1 := by
        rw [hval]
      have hlt : n3 - 1 < (n3 - 1) + (n5 + 1) := by omega
      change (if (Fin.cast h.symm t1).val < n3 - 1 then col3
        else if (Fin.cast h.symm t1).val < (n3 - 1) + (n5 + 1) then col5 else col6) = col5
      rw [huval]
      simp [hlt]
    have hR : replaceColumn (linearCode n3 n5 n6) ⟨0, by omega⟩ col5 t0 = col5 := by
      simp [replaceColumn, t0]
    simpa [hL, hR, t0, rowPermute]
  · by_cases ht1 : t = t1
    · subst ht1
      have hswap : Equiv.swap t0 t1 t1 = t0 := Equiv.swap_apply_right t0 t1
      rw [hswap]
      have ht1ne0 : n3 - 1 ≠ 0 := by
        intro hz
        apply ht0
        apply Fin.ext
        simp [t0, t1, hz]
      have hn3ge2 : 2 ≤ n3 := by omega
      have hL : (linearCode (n3 - 1) (n5 + 1) n6) (Fin.cast h.symm t0) = col3 := by
        have huval : (Fin.cast h.symm t0).val = 0 := by
          rw [hval]
        have hlt : 0 < n3 - 1 := by omega
        change (if (Fin.cast h.symm t0).val < n3 - 1 then col3
          else if (Fin.cast h.symm t0).val < (n3 - 1) + (n5 + 1) then col5 else col6) = col3
        rw [huval]
        simp [hlt]
      have hR : replaceColumn (linearCode n3 n5 n6) ⟨0, by omega⟩ col5 t1 = col3 := by
        have ht0' : t1 ≠ ⟨0, by omega⟩ := by
          intro h
          apply ht0
          simpa [t0] using h
        have hcol3 : linearCode n3 n5 n6 t1 = col3 := by
          have hlt : n3 - 1 < n3 := by omega
          simp [linearCode, t1, hlt]
        simp [replaceColumn, ht0', hcol3]
      simpa [hL, hR, t0, rowPermute]
    · have hswap : Equiv.swap t0 t1 t = t := Equiv.swap_apply_of_ne_of_ne ht0 ht1
      rw [hswap]
      have huval : (Fin.cast h.symm t).val = t.val := by
        rw [hval]
      by_cases ht3 : t.val < n3 - 1
      · have hL : (linearCode (n3 - 1) (n5 + 1) n6) (Fin.cast h.symm t) = col3 := by
          simp [linearCode, ht3]
        have hR : linearCode n3 n5 n6 t = col3 := by
          have h3 : t.val < n3 := by omega
          simp [linearCode, h3]
        have ht0' : t ≠ ⟨0, by omega⟩ := by
          intro h
          apply ht0
          simpa [t0] using h
        have hRp : rowPermute (Equiv.refl (Fin 4))
            (replaceColumn (linearCode n3 n5 n6) ⟨0, by omega⟩ col5 t) = col3 := by
          have hrc : replaceColumn (linearCode n3 n5 n6) ⟨0, by omega⟩ col5 t =
              linearCode n3 n5 n6 t := by
            simp [replaceColumn, ht0']
          rw [hrc, hR]
          rfl
        exact (hL.trans hRp.symm)
      · have hge3 : n3 - 1 ≤ t.val := by omega
        have ht1' : t.val ≠ n3 - 1 := by
          intro h
          apply ht1
          apply Fin.ext
          simpa [t1] using h
        have hge3' : n3 ≤ t.val := by omega
        by_cases ht5 : t.val < (n3 - 1) + (n5 + 1)
        · have hL : (linearCode (n3 - 1) (n5 + 1) n6) (Fin.cast h.symm t) = col5 := by
            have hnot3 : ¬ t.val < n3 - 1 := not_lt_of_ge hge3
            simp [linearCode, hnot3, ht5]
          have hR : linearCode n3 n5 n6 t = col5 := by
            have hlt5 : t.val < n3 + n5 := by omega
            have hnot3' : ¬ t.val < n3 := not_lt_of_ge hge3'
            simp [linearCode, hnot3', hlt5]
          have ht0' : t ≠ ⟨0, by omega⟩ := by
            intro h
            apply ht0
            simpa [t0] using h
          have hRp : rowPermute (Equiv.refl (Fin 4))
              (replaceColumn (linearCode n3 n5 n6) ⟨0, by omega⟩ col5 t) = col5 := by
            have hrc : replaceColumn (linearCode n3 n5 n6) ⟨0, by omega⟩ col5 t =
                linearCode n3 n5 n6 t := by
              simp [replaceColumn, ht0']
            rw [hrc, hR]
            rfl
          exact (hL.trans hRp.symm)
        · have hge5 : (n3 - 1) + (n5 + 1) ≤ t.val := by omega
          have hge5' : n3 + n5 ≤ t.val := by omega
          have hL : (linearCode (n3 - 1) (n5 + 1) n6) (Fin.cast h.symm t) = col6 := by
            have hnot3 : ¬ t.val < n3 - 1 := not_lt_of_ge hge3
            have hnot5 : ¬ t.val < (n3 - 1) + (n5 + 1) := not_lt_of_ge hge5
            simp [linearCode, hnot3, hnot5]
          have hR : linearCode n3 n5 n6 t = col6 := by
            have hnot3' : ¬ t.val < n3 := not_lt_of_ge hge3'
            have hnot5' : ¬ t.val < n3 + n5 := not_lt_of_ge hge5'
            simp [linearCode, hnot3', hnot5']
          have ht0' : t ≠ ⟨0, by omega⟩ := by
            intro h
            apply ht0
            simpa [t0] using h
          have hRp : rowPermute (Equiv.refl (Fin 4))
              (replaceColumn (linearCode n3 n5 n6) ⟨0, by omega⟩ col5 t) = col6 := by
            have hrc : replaceColumn (linearCode n3 n5 n6) ⟨0, by omega⟩ col5 t =
                linearCode n3 n5 n6 t := by
              simp [replaceColumn, ht0']
            rw [hrc, hR]
            rfl
          exact (hL.trans hRp.symm)

/-- Equal universal performance transfers along an equivalence of the first
code. -/
lemma universalEqual_of_equiv_left {n : ℕ} {C D R : Code n} (hRD : Equivalent R D)
    (h : UniversalEqual R C) : UniversalEqual D C := by
  intro ε h0 h1
  have h1' := (universalEqual_of_equivalent R D hRD) ε h0 h1
  have h2' := h ε h0 h1
  linarith

/-- Strict universal domination transfers along an equivalence of the first
code. -/
lemma universalStrictBetter_of_equiv_left {n : ℕ} {C D R : Code n} (hRD : Equivalent R D)
    (h : UniversalStrictBetter R C) : UniversalStrictBetter D C := by
  intro ε h0 h1
  have hlt := h ε h0 h1
  have heq := lambda_equiv R D hRD ε
  linarith

/-- `UniversalEqual` is symmetric. -/
lemma universalEqual_symm {n : ℕ} {C D : Code n} (h : UniversalEqual C D) : UniversalEqual D C := by
  intro ε h0 h1
  exact (h ε h0 h1).symm

/-- `UniversalEqual` is transitive. -/
lemma universalEqual_trans {n : ℕ} {C₁ C₂ C₃ : Code n} (h12 : UniversalEqual C₁ C₂)
    (h23 : UniversalEqual C₂ C₃) : UniversalEqual C₁ C₃ := by
  intro ε h0 h1
  exact (h12 ε h0 h1).trans (h23 ε h0 h1)

/-- A strict comparison is preserved when the left code is replaced by an
equal one. -/
lemma universalStrictBetter_of_eq_right {n : ℕ} {C D E : Code n} (hCD : UniversalEqual C D)
    (hDE : UniversalStrictBetter D E) : UniversalStrictBetter C E := by
  intro ε h0 h1
  have h1' := hCD ε h0 h1
  have h2' := hDE ε h0 h1
  linarith

/-- A strict comparison is preserved when the right code is replaced by an
equal one. -/
lemma universalStrictBetter_of_eq_left {n : ℕ} {C D E : Code n} (hDE : UniversalStrictBetter D E)
    (hEC : UniversalEqual E C) : UniversalStrictBetter D C := by
  intro ε h0 h1
  have h1' := hDE ε h0 h1
  have h2' := hEC ε h0 h1
  linarith

/-- From `n3 ≡ n5+1 ≡ n6` derive `n3−2 ≡ n6 ≡ n5+1` (case 1, step 2). -/
lemma same_parity_3m2_6_5p_of {n3 n5 n6 : ℕ} (hn3 : 2 ≤ n3)
    (h : SameParity n3 (n5 + 1) n6) :
    SameParity (n3 - 2) n6 (n5 + 1) := by
  rcases h with ⟨h35p, h5p6⟩
  have h6p2 : Even (n6 + 2) ↔ Even n6 := by
    constructor
    · intro he
      rcases he with ⟨q, hq⟩
      have hq1 : 1 ≤ q := by omega
      refine ⟨q - 1, ?_⟩
      omega
    · intro he
      rcases he with ⟨q, hq⟩
      refine ⟨q + 1, ?_⟩
      omega
  have h3m2 : Even (n3 - 2) ↔ Even n3 := by
    constructor
    · intro he
      rcases he with ⟨q, hq⟩
      refine ⟨q + 1, ?_⟩
      omega
    · intro he
      rcases he with ⟨q, hq⟩
      have hq1 : 1 ≤ q := by omega
      refine ⟨q - 1, ?_⟩
      omega
  have h36 : Even n3 ↔ Even n6 := h35p.trans h5p6
  constructor
  · exact h3m2.trans h36
  · exact h36.symm.trans h35p

/-- From `n3 ≡ n5+1 ≡ n6` derive `n5+1 ≡ n6+2 ≡ n3−2` (case 1, step 3). -/
lemma same_parity_5p_6p2_3m2_of {n3 n5 n6 : ℕ} (hn3 : 2 ≤ n3)
    (h : SameParity n3 (n5 + 1) n6) :
    SameParity (n5 + 1) (n6 + 2) (n3 - 2) := by
  rcases h with ⟨h35p, h5p6⟩
  have h6p2 : Even (n6 + 2) ↔ Even n6 := by
    constructor
    · intro he
      rcases he with ⟨q, hq⟩
      have hq1 : 1 ≤ q := by omega
      refine ⟨q - 1, ?_⟩
      omega
    · intro he
      rcases he with ⟨q, hq⟩
      refine ⟨q + 1, ?_⟩
      omega
  have h3m2 : Even (n3 - 2) ↔ Even n3 := by
    constructor
    · intro he
      rcases he with ⟨q, hq⟩
      refine ⟨q + 1, ?_⟩
      omega
    · intro he
      rcases he with ⟨q, hq⟩
      have hq1 : 1 ≤ q := by omega
      refine ⟨q - 1, ?_⟩
      omega
  constructor
  · exact h5p6.trans h6p2.symm
  · exact h6p2.trans (h5p6.symm.trans (h35p.symm.trans h3m2.symm))

/-- `Even (n+2)` is the same parity as `Even n`. -/
lemma even_add_two_iff (n : ℕ) : Even (n + 2) ↔ Even n := by
  constructor
  · intro he
    rcases he with ⟨q, hq⟩
    have hq1 : 1 ≤ q := by omega
    refine ⟨q - 1, ?_⟩
    omega
  · intro he
    rcases he with ⟨q, hq⟩
    refine ⟨q + 1, ?_⟩
    omega

/-- `Even (n−2)` is the same parity as `Even n`, for `n ≥ 2`. -/
lemma even_sub_two_iff {n : ℕ} (hn : 2 ≤ n) : Even (n - 2) ↔ Even n := by
  constructor
  · intro he
    rcases he with ⟨q, hq⟩
    refine ⟨q + 1, ?_⟩
    omega
  · intro he
    rcases he with ⟨q, hq⟩
    have hq1 : 1 ≤ q := by omega
    refine ⟨q - 1, ?_⟩
    omega

/-- From `n3 ≡ n5 ≡ n6+1` derive `n3−2 ≡ n6+1 ≡ n5` (case 2). -/
lemma same_parity_3m2_6p_5_of {n3 n5 n6 : ℕ} (hn3 : 2 ≤ n3)
    (h : SameParity n3 n5 (n6 + 1)) :
    SameParity (n3 - 2) (n6 + 1) n5 := by
  rcases h with ⟨h35, h56p⟩
  constructor
  · exact (even_sub_two_iff hn3).trans (h35.trans h56p)
  · exact h56p.symm

/-- The row permutation swapping rows 2 and 3 (Fin indices 1 and 2) swaps
column types 5 and 6 and fixes type 3. -/
lemma rowSwap23_col5 :
    rowPermute (Equiv.swap ⟨2, by decide⟩ ⟨3, by decide⟩) col5 = col6 := by
  ext j
  fin_cases j <;> simp [rowPermute, col5, col6, Equiv.swap_apply_left, Equiv.swap_apply_right,
    Equiv.swap_apply_of_ne_of_ne]

lemma rowSwap23_col6 :
    rowPermute (Equiv.swap ⟨2, by decide⟩ ⟨3, by decide⟩) col6 = col5 := by
  ext j
  fin_cases j <;> simp [rowPermute, col5, col6, Equiv.swap_apply_left, Equiv.swap_apply_right,
    Equiv.swap_apply_of_ne_of_ne]

lemma rowSwap23_col3 :
    rowPermute (Equiv.swap ⟨2, by decide⟩ ⟨3, by decide⟩) col3 = col3 := by
  ext j
  fin_cases j <;> simp [rowPermute, col3, Equiv.swap_apply_left, Equiv.swap_apply_right,
    Equiv.swap_apply_of_ne_of_ne]

/-- The block permutation swapping the type-5 and type-6 regions of a
`linearCode`; with the row swap it makes `C(a,c,b)` equivalent to `C(a,b,c)`. -/
lemma linearCode_swap23_equiv (a b c : ℕ) :
    let n := a + b + c
    Equivalent (cast (congrArg Code (by omega : a + c + b = n)) (linearCode a c b))
      (cast (congrArg Code (by omega : a + b + c = n)) (linearCode a b c)) := by
  intro n
  let ρ : Equiv (Fin 4) (Fin 4) := Equiv.swap ⟨2, by decide⟩ ⟨3, by decide⟩
  let f := fun t : Fin n => if h1 : t.val < a then t
    else if h2 : t.val < a + b then ⟨t.val + c, by omega⟩
    else ⟨t.val - b, by omega⟩
  let g := fun t : Fin n => if h1 : t.val < a then t
    else if h2 : t.val < a + c then ⟨t.val + b, by omega⟩
    else ⟨t.val - c, by omega⟩
  let p : Equiv (Fin n) (Fin n) :=
    { toFun := g
      invFun := f
      left_inv := by
        intro t
        by_cases h1 : t.val < a
        · simp [f, g, h1]
        · have h1' : a ≤ t.val := by omega
          by_cases h2 : t.val < a + c
          · have hinv : g t = ⟨t.val + b, by omega⟩ := by
              simp [g, h1, h2]
            rw [hinv]
            have hn1 : ¬ t.val + b < a := by omega
            have hn2 : ¬ t.val + b < a + b := by omega
            have hto : f ⟨t.val + b, by omega⟩ = ⟨(t.val + b) - b, by omega⟩ := by
              simp [f, hn1, hn2]
            rw [hto]
            apply Fin.ext
            simp
          · have hinv : g t = ⟨t.val - c, by omega⟩ := by
              simp [g, h1, h2]
            rw [hinv]
            have hn1 : ¬ t.val - c < a := by omega
            have h2' : t.val - c < a + b := by omega
            have hto : f ⟨t.val - c, by omega⟩ = ⟨(t.val - c) + c, by omega⟩ := by
              simp [f, hn1, h2']
            rw [hto]
            apply Fin.ext
            change (t.val - c) + c = t.val
            have hge : c ≤ t.val := by omega
            rw [Nat.sub_add_cancel hge]
      right_inv := by
        intro t
        by_cases h1 : t.val < a
        · simp [f, g, h1]
        · have h1' : a ≤ t.val := by omega
          by_cases h2 : t.val < a + b
          · have hto : f t = ⟨t.val + c, by omega⟩ := by
              simp [f, h1, h2]
            rw [hto]
            have hn1 : ¬ t.val + c < a := by omega
            have hn2 : ¬ t.val + c < a + c := by omega
            have hinv : g ⟨t.val + c, by omega⟩ = ⟨(t.val + c) - c, by omega⟩ := by
              simp [g, hn1, hn2]
            rw [hinv]
            apply Fin.ext
            simp
          · have hto : f t = ⟨t.val - b, by omega⟩ := by
              simp [f, h1, h2]
            rw [hto]
            have hn1 : ¬ t.val - b < a := by omega
            have h2' : t.val - b < a + c := by omega
            have hinv : g ⟨t.val - b, by omega⟩ = ⟨(t.val - b) + b, by omega⟩ := by
              simp [g, hn1, h2']
            rw [hinv]
            apply Fin.ext
            change (t.val - b) + b = t.val
            have hge : b ≤ t.val := by omega
            rw [Nat.sub_add_cancel hge]
    }
  refine ⟨ρ, p, fun _ => false, ?_⟩
  intro t
  have hcast1 : (cast (congrArg Code (by omega : a + b + c = n)) (linearCode a b c)) (p t) =
      (linearCode a b c) (Fin.cast (by omega : a + b + c = n).symm (p t)) := by
    exact cast_code_apply (by omega : a + b + c = n) (linearCode a b c) (p t)
  have hcast2 : (cast (congrArg Code (by omega : a + c + b = n)) (linearCode a c b)) t =
      (linearCode a c b) (Fin.cast (by omega : a + c + b = n).symm t) := by
    exact cast_code_apply (by omega : a + c + b = n) (linearCode a c b) t
  rw [hcast1]
  rw [hcast2]
  by_cases ht1 : t.val < a
  · have hp : p t = t := by simp [p, g, ht1]
    rw [hp]
    have hval1 : (Fin.cast (by omega : a + b + c = n).symm t).val = t.val := rfl
    have hval2 : (Fin.cast (by omega : a + c + b = n).symm t).val = t.val := rfl
    have hL : (linearCode a b c) (Fin.cast (by omega : a + b + c = n).symm t) = col3 := by
      simp [linearCode, ht1]
    have hR : (linearCode a c b) (Fin.cast (by omega : a + c + b = n).symm t) = col3 := by
      simp [linearCode, ht1]
    rw [hL, hR]
    exact (rowSwap23_col3).symm
  · have ht1' : a ≤ t.val := by omega
    by_cases ht2 : t.val < a + c
    · have hp : p t = ⟨t.val + b, by omega⟩ := by
        apply Fin.ext
        simp [p, g, ht1, ht2]
      rw [hp]
      have hval1 : (Fin.cast (by omega : a + b + c = n).symm ⟨t.val + b, by omega⟩).val = t.val + b := rfl
      have hval2 : (Fin.cast (by omega : a + c + b = n).symm t).val = t.val := rfl
      have hL : (linearCode a b c) (Fin.cast (by omega : a + b + c = n).symm ⟨t.val + b, by omega⟩) = col6 := by
        have hn1 : ¬ t.val + b < a := by omega
        have hn2 : ¬ t.val + b < a + b := by omega
        simp [linearCode, hn1, hn2]
      have hR : (linearCode a c b) (Fin.cast (by omega : a + c + b = n).symm t) = col5 := by
        have hn1 : ¬ t.val < a := by omega
        simp [linearCode, ht2, hn1]
      rw [hL, hR]
      exact (rowSwap23_col5).symm
    · have ht2' : a + c ≤ t.val := by omega
      have hp : p t = ⟨t.val - c, by omega⟩ := by
        apply Fin.ext
        simp [p, g, ht1, ht2]
      rw [hp]
      have hval1 : (Fin.cast (by omega : a + b + c = n).symm ⟨t.val - c, by omega⟩).val = t.val - c := rfl
      have hval2 : (Fin.cast (by omega : a + c + b = n).symm t).val = t.val := rfl
      have hL : (linearCode a b c) (Fin.cast (by omega : a + b + c = n).symm ⟨t.val - c, by omega⟩) = col5 := by
        have hn1 : ¬ t.val - c < a := by omega
        have h2 : t.val - c < a + b := by omega
        simp [linearCode, hn1, h2]
      have hR : (linearCode a c b) (Fin.cast (by omega : a + c + b = n).symm t) = col6 := by
        have hn1 : ¬ t.val < a := by omega
        have hn2 : ¬ t.val < a + c := by omega
        simp [linearCode, hn1, hn2]
      rw [hL, hR]
      exact (rowSwap23_col6).symm

/-- The row permutation swapping rows 1 and 3 (Fin indices 0 and 2) swaps
column types 3 and 6 and fixes type 5. -/
lemma rowSwap13_col3 :
    rowPermute (Equiv.swap ⟨1, by decide⟩ ⟨3, by decide⟩) col3 = col6 := by
  ext j
  fin_cases j <;> simp [rowPermute, col3, col6, Equiv.swap_apply_left, Equiv.swap_apply_right,
    Equiv.swap_apply_of_ne_of_ne]

lemma rowSwap13_col6 :
    rowPermute (Equiv.swap ⟨1, by decide⟩ ⟨3, by decide⟩) col6 = col3 := by
  ext j
  fin_cases j <;> simp [rowPermute, col3, col6, Equiv.swap_apply_left, Equiv.swap_apply_right,
    Equiv.swap_apply_of_ne_of_ne]

lemma rowSwap13_col5 :
    rowPermute (Equiv.swap ⟨1, by decide⟩ ⟨3, by decide⟩) col5 = col5 := by
  ext j
  fin_cases j <;> simp [rowPermute, col5, Equiv.swap_apply_left, Equiv.swap_apply_right,
    Equiv.swap_apply_of_ne_of_ne]

/-- The block permutation swapping the type-3 and type-6 regions of a
`linearCode`; with the row swap it makes `C(c,b,a)` equivalent to `C(a,b,c)`. -/
lemma linearCode_swap13_equiv (a b c : ℕ) :
    let n := a + b + c
    Equivalent (cast (congrArg Code (by omega : c + b + a = n)) (linearCode c b a))
      (cast (congrArg Code (by omega : a + b + c = n)) (linearCode a b c)) := by
  intro n
  let ρ : Equiv (Fin 4) (Fin 4) := Equiv.swap ⟨1, by decide⟩ ⟨3, by decide⟩
  let f : Fin n → Fin n := fun t => if h1 : t.val < c then ⟨t.val + a + b, by omega⟩
    else if h2 : t.val < c + b then ⟨t.val - c + a, by omega⟩
    else ⟨t.val - c - b, by omega⟩
  let g : Fin n → Fin n := fun t => if h1 : t.val < a then ⟨t.val + b + c, by omega⟩
    else if h2 : t.val < a + b then ⟨t.val - a + c, by omega⟩
    else ⟨t.val - a - b, by omega⟩
  let p : Equiv (Fin n) (Fin n) :=
    { toFun := f
      invFun := g
      left_inv := by
        intro t
        by_cases h1 : t.val < c
        · apply Fin.ext
          have hto : f t = ⟨t.val + a + b, by omega⟩ := by
            simp [f, h1]
          rw [hto]
          have hn1 : ¬ t.val + a + b < a := by omega
          have hn2 : ¬ t.val + a + b < a + b := by omega
          have hinv : g ⟨t.val + a + b, by omega⟩ = ⟨(t.val + a + b) - a - b, by omega⟩ := by
            simp [g, hn1, hn2]
          rw [hinv]
          change (t.val + a + b) - a - b = t.val
          omega
        · have h1' : c ≤ t.val := by omega
          by_cases h2 : t.val < c + b
          · have hto : f t = ⟨t.val - c + a, by omega⟩ := by
              simp [f, h1, h2]
            rw [hto]
            have hn1 : ¬ t.val - c + a < a := by omega
            have hn2 : t.val - c + a < a + b := by omega
            have hinv : g ⟨t.val - c + a, by omega⟩ = ⟨(t.val - c + a) - a + c, by omega⟩ := by
              simp [g, hn1, hn2]
            rw [hinv]
            apply Fin.ext
            change (t.val - c + a) - a + c = t.val
            have hsub1 : (t.val - c + a) - a = t.val - c := by
              exact Nat.add_sub_cancel_right (t.val - c) a
            have hc : c ≤ t.val := by omega
            rw [hsub1, Nat.sub_add_cancel hc]
          · have hto : f t = ⟨t.val - c - b, by omega⟩ := by
              simp [f, h1, h2]
            rw [hto]
            have h1'' : t.val - c - b < a := by omega
            have hinv : g ⟨t.val - c - b, by omega⟩ = ⟨(t.val - c - b) + b + c, by omega⟩ := by
              simp [g, h1'']
            rw [hinv]
            apply Fin.ext
            change (t.val - c - b) + b + c = t.val
            have hcb : c + b ≤ t.val := by omega
            omega
      right_inv := by
        intro t
        by_cases h1 : t.val < a
        · apply Fin.ext
          have hinv : g t = ⟨t.val + b + c, by omega⟩ := by
            simp [g, h1]
          rw [hinv]
          have hn1 : ¬ t.val + b + c < c := by omega
          have hn2 : ¬ t.val + b + c < c + b := by omega
          have hto : f ⟨t.val + b + c, by omega⟩ = ⟨(t.val + b + c) - c - b, by omega⟩ := by
            simp [f, hn1, hn2]
          rw [hto]
          change (t.val + b + c) - c - b = t.val
          omega
        · have h1' : a ≤ t.val := by omega
          by_cases h2 : t.val < a + b
          · have hinv : g t = ⟨t.val - a + c, by omega⟩ := by
              simp [g, h1, h2]
            rw [hinv]
            have hn1 : ¬ t.val - a + c < c := by omega
            have hn2 : t.val - a + c < c + b := by omega
            have hto : f ⟨t.val - a + c, by omega⟩ = ⟨(t.val - a + c) - c + a, by omega⟩ := by
              simp [f, hn1, hn2]
            rw [hto]
            apply Fin.ext
            change (t.val - a + c) - c + a = t.val
            have hsub1 : (t.val - a + c) - c = t.val - a := by
              exact Nat.add_sub_cancel_right (t.val - a) c
            have ha : a ≤ t.val := by omega
            rw [hsub1, Nat.sub_add_cancel ha]
          · have hinv : g t = ⟨t.val - a - b, by omega⟩ := by
              simp [g, h1, h2]
            rw [hinv]
            have h1'' : t.val - a - b < c := by omega
            have hto : f ⟨t.val - a - b, by omega⟩ = ⟨(t.val - a - b) + a + b, by omega⟩ := by
              simp [f, h1'']
            rw [hto]
            apply Fin.ext
            change (t.val - a - b) + a + b = t.val
            have hab : a + b ≤ t.val := by omega
            omega
    }
  refine ⟨ρ, p, fun _ => false, ?_⟩
  intro t
  have hcast1 : (cast (congrArg Code (by omega : a + b + c = n)) (linearCode a b c)) (p t) =
      (linearCode a b c) (Fin.cast (by omega : a + b + c = n).symm (p t)) := by
    exact cast_code_apply (by omega : a + b + c = n) (linearCode a b c) (p t)
  have hcast2 : (cast (congrArg Code (by omega : c + b + a = n)) (linearCode c b a)) t =
      (linearCode c b a) (Fin.cast (by omega : c + b + a = n).symm t) := by
    exact cast_code_apply (by omega : c + b + a = n) (linearCode c b a) t
  rw [hcast1]
  rw [hcast2]
  by_cases ht1 : t.val < c
  · have hp : p t = ⟨t.val + a + b, by omega⟩ := by
      apply Fin.ext
      simp [p, f, ht1]
    rw [hp]
    have hval1 : (Fin.cast (by omega : a + b + c = n).symm ⟨t.val + a + b, by omega⟩).val = t.val + a + b := rfl
    have hval2 : (Fin.cast (by omega : c + b + a = n).symm t).val = t.val := rfl
    have hL : (linearCode a b c) (Fin.cast (by omega : a + b + c = n).symm ⟨t.val + a + b, by omega⟩) = col6 := by
      have hn1 : ¬ t.val + a + b < a := by omega
      have hn2 : ¬ t.val + a + b < a + b := by omega
      simp [linearCode, hn1, hn2]
    have hR : (linearCode c b a) (Fin.cast (by omega : c + b + a = n).symm t) = col3 := by
      simp [linearCode, ht1]
    rw [hL, hR]
    exact (rowSwap13_col3).symm
  · have ht1' : c ≤ t.val := by omega
    by_cases ht2 : t.val < c + b
    · have hp : p t = ⟨t.val - c + a, by omega⟩ := by
        apply Fin.ext
        simp [p, f, ht1, ht2]
      rw [hp]
      have hval1 : (Fin.cast (by omega : a + b + c = n).symm ⟨t.val - c + a, by omega⟩).val = t.val - c + a := rfl
      have hval2 : (Fin.cast (by omega : c + b + a = n).symm t).val = t.val := rfl
      have hL : (linearCode a b c) (Fin.cast (by omega : a + b + c = n).symm ⟨t.val - c + a, by omega⟩) = col5 := by
        have hn1 : ¬ t.val - c + a < a := by omega
        have h2 : t.val - c + a < a + b := by omega
        simp [linearCode, hn1, h2]
      have hR : (linearCode c b a) (Fin.cast (by omega : c + b + a = n).symm t) = col5 := by
        have hn1 : ¬ t.val < c := by omega
        simp [linearCode, ht2, hn1]
      rw [hL, hR]
      exact (rowSwap13_col5).symm
    · have ht2' : c + b ≤ t.val := by omega
      have hp : p t = ⟨t.val - c - b, by omega⟩ := by
        apply Fin.ext
        simp [p, f, ht1, ht2]
      rw [hp]
      have hval1 : (Fin.cast (by omega : a + b + c = n).symm ⟨t.val - c - b, by omega⟩).val = t.val - c - b := rfl
      have hval2 : (Fin.cast (by omega : c + b + a = n).symm t).val = t.val := rfl
      have hL : (linearCode a b c) (Fin.cast (by omega : a + b + c = n).symm ⟨t.val - c - b, by omega⟩) = col3 := by
        have h1 : t.val - c - b < a := by omega
        simp [linearCode, h1]
      have hR : (linearCode c b a) (Fin.cast (by omega : c + b + a = n).symm t) = col6 := by
        have hn1 : ¬ t.val < c := by omega
        have hn2 : ¬ t.val < c + b := by omega
        simp [linearCode, hn1, hn2]
      rw [hL, hR]
      exact (rowSwap13_col6).symm

/-- A casted code has the same λ as the original (the cast is a bijection on
the word space). -/
lemma lambda_cast {m n : ℕ} (h : m = n) (C : Code m) (ε : ℝ) :
    lambda (cast (congrArg Code h) C) ε = lambda C ε := by
  have hdRow : ∀ y : Word n, ∀ i : Fin 4,
      hammingDist (row (cast (congrArg Code h) C) i) y =
        hammingDist (row C i) (fun k : Fin m => y (Fin.cast h k)) := by
    intro y i
    change dRow (cast (congrArg Code h) C) i y = dRow C i (fun k : Fin m => y (Fin.cast h k))
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
      rw [hc]
      have hcast : Fin.cast h (Fin.cast h.symm t) = t := by
        apply Fin.ext
        simp
      rw [hcast]
  have hd : ∀ y : Word n, dCode (cast (congrArg Code h) C) y = dCode C (fun k => y (Fin.cast h k)) := by
    intro y
    simp [dCode, row0, row1, row2, row3, hdRow y 0, hdRow y 1, hdRow y 2, hdRow y 3]
  unfold lambda
  congr 1
  calc
    (∑ y : Word n, (1 - ε) ^ (n - dCode (cast (congrArg Code h) C) y) * ε ^ (dCode (cast (congrArg Code h) C) y))
        = ∑ y : Word n, (1 - ε) ^ (n - dCode C (fun k => y (Fin.cast h k))) * ε ^ (dCode C (fun k => y (Fin.cast h k))) := by
          apply Finset.sum_congr rfl
          intro y _
          rw [hd y]
    _ = ∑ z : Word m, (1 - ε) ^ (m - dCode C z) * ε ^ (dCode C z) := by
          apply Finset.sum_bij (fun y _ => fun k : Fin m => y (Fin.cast h k))
          · intro y _; simp
          · intro a _ b _ hab
            funext k
            have hk : Fin.cast h (Fin.cast h.symm k) = k := by
              apply Fin.ext
              simp
            have ha : a (Fin.cast h (Fin.cast h.symm k)) = b (Fin.cast h (Fin.cast h.symm k)) :=
              congrFun hab (Fin.cast h.symm k)
            rwa [hk] at ha
          · intro z _
            refine ⟨fun j : Fin n => z (Fin.cast h.symm j), by simp, ?_⟩
            funext k
            have hk : Fin.cast h.symm (Fin.cast h k) = k := by
              apply Fin.ext
              simp
            rw [show (fun j : Fin n => z (Fin.cast h.symm j)) (Fin.cast h k) =
              z (Fin.cast h.symm (Fin.cast h k)) by rfl]
            rw [hk]
          · intro y _
            rw [show n - dCode C (fun k => y (Fin.cast h k)) =
              m - dCode C (fun k => y (Fin.cast h k)) by omega]

/-- Transporting an equality comparison along an equal-length cast. -/
lemma universalEqual_of_cast {m n : ℕ} (h : m = n) {C D : Code m} (hCD : UniversalEqual C D) :
    UniversalEqual (cast (congrArg Code h) C) (cast (congrArg Code h) D) := by
  intro ε h0 h1
  rw [lambda_cast h C ε, lambda_cast h D ε]
  exact hCD ε h0 h1

/-- Transporting a strict comparison along an equal-length cast. -/
lemma universalStrictBetter_of_cast {m n : ℕ} (h : m = n) {C D : Code m}
    (hCD : UniversalStrictBetter C D) :
    UniversalStrictBetter (cast (congrArg Code h) C) (cast (congrArg Code h) D) := by
  intro ε h0 h1
  have hlt := hCD ε h0 h1
  rw [lambda_cast h C ε, lambda_cast h D ε]
  exact hlt

/-- Transporting an equivalence along an equal-length cast. -/
lemma equivalent_of_cast {m n : ℕ} (h : m = n) {C D : Code m} (hCD : Equivalent C D) :
    Equivalent (cast (congrArg Code h) C) (cast (congrArg Code h) D) := by
  rcases hCD with ⟨ρ, p, f, heq⟩
  refine ⟨ρ, Equiv.ofBijective (fun u : Fin n => Fin.cast h (p (Fin.cast h.symm u))) ?_,
    fun u => f (Fin.cast h.symm u), ?_⟩
  · constructor
    · intro a b hab
      apply Fin.ext
      have h1 : Fin.cast h.symm (Fin.cast h (p (Fin.cast h.symm a))) =
          Fin.cast h.symm (Fin.cast h (p (Fin.cast h.symm b))) := by
        simpa using (congrArg (fun x : Fin n => Fin.cast h.symm x) hab)
      have h2 : p (Fin.cast h.symm a) = p (Fin.cast h.symm b) := by simpa using h1
      have h3 : Fin.cast h.symm a = Fin.cast h.symm b := p.injective h2
      have h4 : Fin.cast h (Fin.cast h.symm a) = Fin.cast h (Fin.cast h.symm b) := by rw [h3]
      exact congrArg Fin.val h4
    · intro u
      refine ⟨Fin.cast h (p.symm (Fin.cast h.symm u)), ?_⟩
      apply Fin.ext
      simp
  · intro u
    change (cast (congrArg Code h) D) ((fun u : Fin n => Fin.cast h (p (Fin.cast h.symm u))) u) =
      rowPermute ρ (if (fun u => f (Fin.cast h.symm u)) u = true then flipCol ((cast (congrArg Code h) C) u)
        else (cast (congrArg Code h) C) u)
    have hc1 : (cast (congrArg Code h) D) (Fin.cast h (p (Fin.cast h.symm u))) =
        D (p (Fin.cast h.symm u)) := by
      rw [cast_code_apply h D (Fin.cast h (p (Fin.cast h.symm u)))]
      simp
    have hc2 : (cast (congrArg Code h) C) u = C (Fin.cast h.symm u) := by
      exact cast_code_apply h C u
    rw [hc1, hc2]
    exact heq (Fin.cast h.symm u)

/-- Theorem `thm:linearcompare` (Theorem 12): comparing C(n3,n5,n6) with
C(n3−1,n5+1,n6). -/
theorem linear_compare (n3 n5 n6 : ℕ) (hn3 : n3 > 0) :
    let n := n3 + n5 + n6
    let C : Code n := linearCode n3 n5 n6
    let C' : Code n :=
      cast (congrArg Code (by omega : (n3 - 1) + (n5 + 1) + n6 = n))
        (linearCode (n3 - 1) (n5 + 1) n6)
    (SameParity n3 (n5 + 1) n6 → UniversalEqual C' C) ∧
      (SameParity n3 n5 n6 →
        (n3 = 1 → UniversalEqual C' C) ∧ (n3 ≥ 2 → UniversalStrictBetter C' C)) ∧
      (n5 ≤ n3 → n5 ≤ n6 → SameParity (n3 - 1) n5 n6 →
        (n3 = n5 + 1 → UniversalEqual C' C) ∧
          (n3 > n5 + 1 → UniversalStrictBetter C' C)) := by
  intro n C C'
  let R : Code n := replaceColumn C ⟨0, by omega⟩ col5
  have hR : Equivalent R C' := by
    simpa [C, R] using (replace_linear_3_5_equiv n3 n5 n6 hn3)
  constructor
  · intro h1
    exact universalEqual_of_equiv_left hR (linear_compare_case1 hn3 h1)
  · constructor
    · intro h2
      rcases linear_compare_case2 hn3 h2 with ⟨heq2, hgt2⟩
      constructor
      · intro hn31
        exact universalEqual_of_equiv_left hR (heq2 hn31)
      · intro hn3ge
        exact universalStrictBetter_of_equiv_left hR (hgt2 hn3ge)
    · intro h53 h56 h3
      rcases linear_compare_case3 hn3 h53 h56 h3 with ⟨heq3, hgt3⟩
      constructor
      · intro heq'
        exact universalEqual_of_equiv_left hR (heq3 heq')
      · intro hgt'
        exact universalStrictBetter_of_equiv_left hR (hgt3 hgt')

/-- Corollary `cor:linear1` (Corollary 13): C(n3−2,n5,n6+2) strictly beats C(n3,n5,n6). -/
theorem linear_cor1 (n3 n5 n6 : ℕ) (hn3 : n3 ≥ 2) :
    let n := n3 + n5 + n6
    let C : Code n := linearCode n3 n5 n6
    let C' : Code n :=
      cast (congrArg Code (by omega : (n3 - 2) + n5 + (n6 + 2) = n))
        (linearCode (n3 - 2) n5 (n6 + 2))
    ((SameParity n3 (n5 + 1) n6 ∧ n3 ≥ n6 + 3 ∧ n5 ≥ n6 - 1) ∨
      (SameParity n3 n5 (n6 + 1) ∧ n3 ≥ n6 + 4 ∧ n5 ≥ n6 + 1)) →
      UniversalStrictBetter C' C := by
  intro n C C' h
  have hn3pos : n3 > 0 := by omega
  -- intermediate codes (cast to Fin n)
  let A : Code n :=
    cast (congrArg Code (by omega : (n3 - 1) + (n5 + 1) + n6 = n)) (linearCode (n3 - 1) (n5 + 1) n6)
  let B : Code n :=
    cast (congrArg Code (by omega : (n3 - 2) + (n5 + 1) + (n6 + 1) = n)) (linearCode (n3 - 2) (n5 + 1) (n6 + 1))
  let A2 : Code n :=
    cast (congrArg Code (by omega : (n3 - 1) + n5 + (n6 + 1) = n)) (linearCode (n3 - 1) n5 (n6 + 1))
  rcases h with h1 | h2
  · rcases h1 with ⟨hpar, hn36, hn56m⟩
    -- step 1: A = C
    have hA : UniversalEqual A C := by
      simpa [A, C] using (linear_compare n3 n5 n6 hn3pos).1 hpar
    -- step 2: B > A via the permuted 3→6 change
    have hstep2' : UniversalStrictBetter
        (cast (congrArg Code (by omega : (n3 - 2) + (n6 + 1) + (n5 + 1) = (n3 - 1) + n6 + (n5 + 1)))
          (linearCode (n3 - 2) (n6 + 1) (n5 + 1)))
        (linearCode (n3 - 1) n6 (n5 + 1)) := by
      have hpar3 : SameParity ((n3 - 1) - 1) n6 (n5 + 1) := by
        -- (n3−1)−1 = n3−2; same_parity_3m2_6_5p_of hpar
        simpa [Nat.sub_sub] using (same_parity_3m2_6_5p_of (by omega : 2 ≤ n3) hpar)
      have hcmp := (linear_compare (n3 - 1) n6 (n5 + 1) (by omega : n3 - 1 > 0)).2.2
        (by omega : n6 ≤ n3 - 1) (by omega : n6 ≤ n5 + 1) hpar3
      exact hcmp.2 (by omega : n3 - 1 > n6 + 1)
    have hstep2 : UniversalStrictBetter B A := by
      -- transport to Fin n
      have h2' : UniversalStrictBetter
          (cast (congrArg Code (by omega : (n3 - 2) + (n6 + 1) + (n5 + 1) = n))
            (linearCode (n3 - 2) (n6 + 1) (n5 + 1)))
          (cast (congrArg Code (by omega : (n3 - 1) + n6 + (n5 + 1) = n))
            (linearCode (n3 - 1) n6 (n5 + 1))) := by
        simpa using (universalStrictBetter_of_cast (by omega : (n3 - 1) + n6 + (n5 + 1) = n) hstep2')
      have eB : Equivalent
          (cast (congrArg Code (by omega : (n3 - 2) + (n6 + 1) + (n5 + 1) = n))
            (linearCode (n3 - 2) (n6 + 1) (n5 + 1))) B := by
        have e0 : Equivalent
            (cast (congrArg Code (by omega : (n3 - 2) + (n6 + 1) + (n5 + 1) = (n3 - 2) + (n5 + 1) + (n6 + 1)))
              (linearCode (n3 - 2) (n6 + 1) (n5 + 1)))
            (linearCode (n3 - 2) (n5 + 1) (n6 + 1)) :=
          linearCode_swap23_equiv (n3 - 2) (n5 + 1) (n6 + 1)
        have e1 := equivalent_of_cast (by omega : (n3 - 2) + (n5 + 1) + (n6 + 1) = n) e0
        simpa [B] using e1
      have eA : Equivalent
          (cast (congrArg Code (by omega : (n3 - 1) + n6 + (n5 + 1) = n))
            (linearCode (n3 - 1) n6 (n5 + 1))) A := by
        have e0 : Equivalent
            (cast (congrArg Code (by omega : (n3 - 1) + n6 + (n5 + 1) = (n3 - 1) + (n5 + 1) + n6))
              (linearCode (n3 - 1) n6 (n5 + 1)))
            (linearCode (n3 - 1) (n5 + 1) n6) :=
          linearCode_swap23_equiv (n3 - 1) (n5 + 1) n6
        have e1 := equivalent_of_cast (by omega : (n3 - 1) + (n5 + 1) + n6 = n) e0
        simpa [A] using e1
      exact universalStrictBetter_of_equivalent B
        (cast (congrArg Code (by omega : (n3 - 2) + (n6 + 1) + (n5 + 1) = n))
          (linearCode (n3 - 2) (n6 + 1) (n5 + 1)))
        A
        (cast (congrArg Code (by omega : (n3 - 1) + n6 + (n5 + 1) = n))
          (linearCode (n3 - 1) n6 (n5 + 1)))
        (equivalent_symm eB) (equivalent_symm eA) h2'
    -- step 3: C' = B via the permuted 5→6 change
    have hstep3' : UniversalEqual
        (cast (congrArg Code (by omega : n5 + (n6 + 2) + (n3 - 2) = (n5 + 1) + (n6 + 1) + (n3 - 2)))
          (linearCode n5 (n6 + 2) (n3 - 2)))
        (linearCode (n5 + 1) (n6 + 1) (n3 - 2)) := by
      have hpar3' : SameParity (n5 + 1) (n6 + 2) (n3 - 2) :=
        same_parity_5p_6p2_3m2_of (by omega : 2 ≤ n3) hpar
      exact (linear_compare (n5 + 1) (n6 + 1) (n3 - 2) (by omega)).1 hpar3'
    have hstep3 : UniversalEqual C' B := by
      have h3' : UniversalEqual
          (cast (congrArg Code (by omega : n5 + (n6 + 2) + (n3 - 2) = n))
            (linearCode n5 (n6 + 2) (n3 - 2)))
          (cast (congrArg Code (by omega : (n5 + 1) + (n6 + 1) + (n3 - 2) = n))
            (linearCode (n5 + 1) (n6 + 1) (n3 - 2))) := by
        simpa using (universalEqual_of_cast (by omega : (n5 + 1) + (n6 + 1) + (n3 - 2) = n) hstep3')
      -- 3-cycle equivalences: (5,6,3) ↔ (3,5,6) = swap13 then swap23
      have e13 : Equivalent
          (cast (congrArg Code (by omega : (n3 - 2) + (n6 + 1) + (n5 + 1) = n))
            (linearCode (n3 - 2) (n6 + 1) (n5 + 1)))
          (cast (congrArg Code (by omega : (n5 + 1) + (n6 + 1) + (n3 - 2) = n))
            (linearCode (n5 + 1) (n6 + 1) (n3 - 2))) := by
        have e0 : Equivalent
            (cast (congrArg Code (by omega : (n3 - 2) + (n6 + 1) + (n5 + 1) = (n5 + 1) + (n6 + 1) + (n3 - 2)))
              (linearCode (n3 - 2) (n6 + 1) (n5 + 1)))
            (linearCode (n5 + 1) (n6 + 1) (n3 - 2)) :=
          linearCode_swap13_equiv (n5 + 1) (n6 + 1) (n3 - 2)
        have e1 := equivalent_of_cast (by omega : (n5 + 1) + (n6 + 1) + (n3 - 2) = n) e0
        simpa using e1
      have e23 : Equivalent
          (cast (congrArg Code (by omega : (n3 - 2) + (n5 + 1) + (n6 + 1) = n))
            (linearCode (n3 - 2) (n5 + 1) (n6 + 1)))
          (cast (congrArg Code (by omega : (n3 - 2) + (n6 + 1) + (n5 + 1) = n))
            (linearCode (n3 - 2) (n6 + 1) (n5 + 1))) := by
        have e0 : Equivalent
            (cast (congrArg Code (by omega : (n3 - 2) + (n5 + 1) + (n6 + 1) = (n3 - 2) + (n6 + 1) + (n5 + 1)))
              (linearCode (n3 - 2) (n5 + 1) (n6 + 1)))
            (linearCode (n3 - 2) (n6 + 1) (n5 + 1)) :=
          linearCode_swap23_equiv (n3 - 2) (n6 + 1) (n5 + 1)
        have e1 := equivalent_of_cast (by omega : (n3 - 2) + (n6 + 1) + (n5 + 1) = n) e0
        simpa using e1
      have eBperm : Equivalent B
          (cast (congrArg Code (by omega : (n5 + 1) + (n6 + 1) + (n3 - 2) = n))
            (linearCode (n5 + 1) (n6 + 1) (n3 - 2))) := by
        simpa [B] using (equivalent_trans e23 e13)
      have e13' : Equivalent
          (cast (congrArg Code (by omega : (n3 - 2) + (n6 + 2) + n5 = n))
            (linearCode (n3 - 2) (n6 + 2) n5))
          (cast (congrArg Code (by omega : n5 + (n6 + 2) + (n3 - 2) = n))
            (linearCode n5 (n6 + 2) (n3 - 2))) := by
        have e0 : Equivalent
            (cast (congrArg Code (by omega : (n3 - 2) + (n6 + 2) + n5 = n5 + (n6 + 2) + (n3 - 2)))
              (linearCode (n3 - 2) (n6 + 2) n5))
            (linearCode n5 (n6 + 2) (n3 - 2)) :=
          linearCode_swap13_equiv n5 (n6 + 2) (n3 - 2)
        have e1 := equivalent_of_cast (by omega : n5 + (n6 + 2) + (n3 - 2) = n) e0
        simpa using e1
      have e23' : Equivalent
          (cast (congrArg Code (by omega : (n3 - 2) + (n6 + 2) + n5 = n))
            (linearCode (n3 - 2) (n6 + 2) n5))
          C' := by
        have e0 : Equivalent
            (cast (congrArg Code (by omega : (n3 - 2) + (n6 + 2) + n5 = (n3 - 2) + n5 + (n6 + 2)))
              (linearCode (n3 - 2) (n6 + 2) n5))
            (linearCode (n3 - 2) n5 (n6 + 2)) :=
          linearCode_swap23_equiv (n3 - 2) n5 (n6 + 2)
        have e1 := equivalent_of_cast (by omega : (n3 - 2) + n5 + (n6 + 2) = n) e0
        simpa [C'] using e1
      have eCperm : Equivalent C'
          (cast (congrArg Code (by omega : n5 + (n6 + 2) + (n3 - 2) = n))
            (linearCode n5 (n6 + 2) (n3 - 2))) := by
        exact equivalent_trans (equivalent_symm e23') e13'
      -- C' = X (h3' + eCperm), X = Bperm (eBperm) → C' = B
      have hX : UniversalEqual C'
          (cast (congrArg Code (by omega : (n5 + 1) + (n6 + 1) + (n3 - 2) = n))
            (linearCode (n5 + 1) (n6 + 1) (n3 - 2))) := by
        exact universalEqual_of_equiv_left (equivalent_symm eCperm) h3'
      have hXB : UniversalEqual
          (cast (congrArg Code (by omega : (n5 + 1) + (n6 + 1) + (n3 - 2) = n))
            (linearCode (n5 + 1) (n6 + 1) (n3 - 2))) B := by
        exact universalEqual_of_equivalent B (cast (congrArg Code (by omega : (n5 + 1) + (n6 + 1) + (n3 - 2) = n))
          (linearCode (n5 + 1) (n6 + 1) (n3 - 2))) eBperm
      exact universalEqual_trans hX hXB
    -- combine: λ_C' = λ_B > λ_A = λ_C
    exact universalStrictBetter_of_eq_left (universalStrictBetter_of_eq_right hstep3 hstep2) hA
  · rcases h2 with ⟨hpar, hn36, hn56m⟩
    -- step 1: A = C via the permuted 3→6 change (linearcompare-1, roles (3,6,5))
    have hpar1' : SameParity n3 (n6 + 1) n5 := ⟨hpar.1.trans hpar.2, hpar.2.symm⟩
    have hstep1' : UniversalEqual
        (cast (congrArg Code (by omega : (n3 - 1) + (n6 + 1) + n5 = n3 + n6 + n5))
          (linearCode (n3 - 1) (n6 + 1) n5))
        (linearCode n3 n6 n5) := by
      exact (linear_compare n3 n6 n5 hn3pos).1 hpar1'
    have hstep1 : UniversalEqual A2 C := by
      have h1' : UniversalEqual
          (cast (congrArg Code (by omega : (n3 - 1) + (n6 + 1) + n5 = n))
            (linearCode (n3 - 1) (n6 + 1) n5))
          (cast (congrArg Code (by omega : n3 + n6 + n5 = n))
            (linearCode n3 n6 n5)) := by
        simpa using (universalEqual_of_cast (by omega : n3 + n6 + n5 = n) hstep1')
      have eA2 : Equivalent
          (cast (congrArg Code (by omega : (n3 - 1) + (n6 + 1) + n5 = n))
            (linearCode (n3 - 1) (n6 + 1) n5)) A2 := by
        have e0 : Equivalent
            (cast (congrArg Code (by omega : (n3 - 1) + (n6 + 1) + n5 = (n3 - 1) + n5 + (n6 + 1)))
              (linearCode (n3 - 1) (n6 + 1) n5))
            (linearCode (n3 - 1) n5 (n6 + 1)) :=
          linearCode_swap23_equiv (n3 - 1) n5 (n6 + 1)
        have e1 := equivalent_of_cast (by omega : (n3 - 1) + n5 + (n6 + 1) = n) e0
        simpa [A2] using e1
      have eC2 : Equivalent
          (cast (congrArg Code (by omega : n3 + n6 + n5 = n))
            (linearCode n3 n6 n5)) C := by
        have e0 : Equivalent
            (cast (congrArg Code (by omega : n3 + n6 + n5 = n3 + n5 + n6))
              (linearCode n3 n6 n5))
            (linearCode n3 n5 n6) :=
          linearCode_swap23_equiv n3 n5 n6
        have e1 := equivalent_of_cast (by omega : n3 + n5 + n6 = n) e0
        simpa [C] using e1
      have h1'' : UniversalEqual A2
          (cast (congrArg Code (by omega : n3 + n6 + n5 = n)) (linearCode n3 n6 n5)) :=
        universalEqual_of_equiv_left eA2 h1'
      have hCeq : UniversalEqual
          (cast (congrArg Code (by omega : n3 + n6 + n5 = n)) (linearCode n3 n6 n5)) C :=
        universalEqual_symm (universalEqual_of_equivalent
          (cast (congrArg Code (by omega : n3 + n6 + n5 = n)) (linearCode n3 n6 n5)) C eC2)
      exact universalEqual_trans h1'' hCeq
    -- step 2: C' > A2 via the permuted 3→6 change (linearcompare-3, roles (3,6,5))
    have hpar3 : SameParity ((n3 - 1) - 1) (n6 + 1) n5 := by
      simpa [Nat.sub_sub] using (same_parity_3m2_6p_5_of (by omega : 2 ≤ n3) hpar)
    have hstep2' : UniversalStrictBetter
        (cast (congrArg Code (by omega : (n3 - 2) + (n6 + 2) + n5 = (n3 - 1) + (n6 + 1) + n5))
          (linearCode (n3 - 2) (n6 + 2) n5))
        (linearCode (n3 - 1) (n6 + 1) n5) := by
      have hcmp := (linear_compare (n3 - 1) (n6 + 1) n5 (by omega : n3 - 1 > 0)).2.2
        (by omega : n6 + 1 ≤ n3 - 1) (by omega : n6 + 1 ≤ n5) hpar3
      exact hcmp.2 (by omega : n3 - 1 > n6 + 2)
    have hstep2 : UniversalStrictBetter C' A2 := by
      have h2' : UniversalStrictBetter
          (cast (congrArg Code (by omega : (n3 - 2) + (n6 + 2) + n5 = n))
            (linearCode (n3 - 2) (n6 + 2) n5))
          (cast (congrArg Code (by omega : (n3 - 1) + (n6 + 1) + n5 = n))
            (linearCode (n3 - 1) (n6 + 1) n5)) := by
        simpa using (universalStrictBetter_of_cast (by omega : (n3 - 1) + (n6 + 1) + n5 = n) hstep2')
      have eC' : Equivalent
          (cast (congrArg Code (by omega : (n3 - 2) + (n6 + 2) + n5 = n))
            (linearCode (n3 - 2) (n6 + 2) n5)) C' := by
        have e0 : Equivalent
            (cast (congrArg Code (by omega : (n3 - 2) + (n6 + 2) + n5 = (n3 - 2) + n5 + (n6 + 2)))
              (linearCode (n3 - 2) (n6 + 2) n5))
            (linearCode (n3 - 2) n5 (n6 + 2)) :=
          linearCode_swap23_equiv (n3 - 2) n5 (n6 + 2)
        have e1 := equivalent_of_cast (by omega : (n3 - 2) + n5 + (n6 + 2) = n) e0
        simpa [C'] using e1
      have eA2 : Equivalent
          (cast (congrArg Code (by omega : (n3 - 1) + (n6 + 1) + n5 = n))
            (linearCode (n3 - 1) (n6 + 1) n5)) A2 := by
        have e0 : Equivalent
            (cast (congrArg Code (by omega : (n3 - 1) + (n6 + 1) + n5 = (n3 - 1) + n5 + (n6 + 1)))
              (linearCode (n3 - 1) (n6 + 1) n5))
            (linearCode (n3 - 1) n5 (n6 + 1)) :=
          linearCode_swap23_equiv (n3 - 1) n5 (n6 + 1)
        have e1 := equivalent_of_cast (by omega : (n3 - 1) + n5 + (n6 + 1) = n) e0
        simpa [A2] using e1
      exact universalStrictBetter_of_equivalent C'
        (cast (congrArg Code (by omega : (n3 - 2) + (n6 + 2) + n5 = n))
          (linearCode (n3 - 2) (n6 + 2) n5))
        A2
        (cast (congrArg Code (by omega : (n3 - 1) + (n6 + 1) + n5 = n))
          (linearCode (n3 - 1) (n6 + 1) n5))
        (equivalent_symm eC') (equivalent_symm eA2) h2'
    -- combine: λ_C' > λ_A = λ_C
    exact universalStrictBetter_of_eq_left hstep2 hstep1

/-- A column of value 3 is `col3`. -/
lemma fin4_univ : (Finset.univ : Finset (Fin 4)) =
    {⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩} := by
  ext j
  fin_cases j <;> simp


/-- For a linear code with no zero columns, the counts of types 3, 5, 6 add up
to the block length `n` (all other column types have count 0). -/
lemma linear_count_sum_eq {n : ℕ} (C : Code n) (hlin : IsLinear C) (hz : count C 0 = 0) :
    count C 3 + count C 5 + count C 6 = n := by
  have htypes : ∀ t : Fin n, colVal (C t) = 3 ∨ colVal (C t) = 5 ∨ colVal (C t) = 6 := by
    intro t
    rcases hlin.1 t with h0 | h3 | h5 | h6
    · exact False.elim (by
        have hmem : t ∈ fiber C 0 := by simp [fiber, h0]
        have hpos : 0 < (fiber C 0).card := Finset.card_pos.mpr ⟨t, hmem⟩
        have hc : 0 < count C 0 := by rwa [← fiber_card_eq_count]
        omega)
    · exact Or.inl h3
    · exact Or.inr (Or.inl h5)
    · exact Or.inr (Or.inr h6)
  have hsum := sum_counts_eq_n C
  have hzeros : ∀ i : ℕ, i ∉ ({3, 5, 6} : Finset ℕ) → count C i = 0 := by
    intro i hi
    by_contra hc
    have hpos : 0 < count C i := Nat.pos_of_ne_zero hc
    have hpos' : 0 < (fiber C i).card := by
      rw [← fiber_card_eq_count] at hpos
      exact hpos
    rcases Finset.card_pos.mp hpos' with ⟨t, ht⟩
    have hci : colVal (C t) = i := (Finset.mem_filter.mp ht).2
    rcases htypes t with h3 | h5 | h6
    · simp [Finset.mem_insert, Finset.mem_singleton] at hi
      omega
    · simp [Finset.mem_insert, Finset.mem_singleton] at hi
      omega
    · simp [Finset.mem_insert, Finset.mem_singleton] at hi
      omega
  -- the sum over Icc 0 15 collapses to counts of 3, 5, 6
  have hsum' : (∑ i ∈ Finset.Icc 0 15, count C i) = count C 3 + count C 5 + count C 6 := by
    -- split out 3, 5, 6 and zero the rest
    have hspl : Finset.Icc 0 15 = ({3, 5, 6} : Finset ℕ) ∪ Finset.Icc 0 15 \ ({3, 5, 6} : Finset ℕ) := by
      ext i
      simp
    rw [hspl, Finset.sum_union]
    · have hrest : (∑ i ∈ Finset.Icc 0 15 \ ({3, 5, 6} : Finset ℕ), count C i) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        exact hzeros i (Finset.mem_sdiff.mp hi).2
      rw [hrest, add_zero]
      simp
      omega
    · intro i hi hiB x hx
      -- disjoint
      have hxB : x ∈ Finset.Icc 0 15 \ ({3, 5, 6} : Finset ℕ) := hiB hx
      simpa using (Finset.mem_sdiff.mp hxB).2 (hi hx)
  omega

/-- A linear code with no zero columns is equivalent to the canonical
`linearCode` with its counts (group the type-3, type-5, type-6 columns by a
column permutation). -/
lemma linear_equiv_linearCode {n : ℕ} (C : Code n) (hlin : IsLinear C) (hz : count C 0 = 0) :
    let _m := count C 3 + count C 5 + count C 6
    Equivalent C (cast (congrArg Code (linear_count_sum_eq C hlin hz))
      (linearCode (count C 3) (count C 5) (count C 6))) := by
  intro m
  have hm : m = n := by
    dsimp [m]
    exact linear_count_sum_eq C hlin hz
  have htypes : ∀ t : Fin n, colVal (C t) = 3 ∨ colVal (C t) = 5 ∨ colVal (C t) = 6 := by
    intro t
    rcases hlin.1 t with h0 | h3 | h5 | h6
    · exact False.elim (by
        have hmem : t ∈ fiber C 0 := by simp [fiber, h0]
        have hpos : 0 < (fiber C 0).card := Finset.card_pos.mpr ⟨t, hmem⟩
        have hc : 0 < count C 0 := by rwa [← fiber_card_eq_count]
        omega)
    · exact Or.inl h3
    · exact Or.inr (Or.inl h5)
    · exact Or.inr (Or.inr h6)
  let k := fun t : Fin n => colVal (C t)
  let f := fun t : Fin n => (Finset.univ.filter fun u : Fin n =>
    k u < k t ∨ (k u = k t ∧ u.val < t.val)).card
  have hrank3 : ∀ t : Fin n, k t = 3 → f t < count C 3 := by
    intro t ht
    have hset : (Finset.univ.filter fun u : Fin n => k u < k t ∨ (k u = k t ∧ u.val < t.val)) =
        (Finset.univ.filter fun u : Fin n => k u = 3 ∧ u.val < t.val) := by
      ext u
      constructor
      · intro hu
        rcases (Finset.mem_filter.mp hu).2 with hlt | heq
        · have hu3 : k u = 3 ∨ k u = 5 ∨ k u = 6 := htypes u
          rcases hu3 with h3 | h5 | h6
          · simp [k] at h3 hlt ht ⊢
            exfalso
            omega
          · simp [k] at h5 hlt ht ⊢
            exfalso
            omega
          · simp [k] at h6 hlt ht ⊢
            exfalso
            omega
        · exact Finset.mem_filter.mpr ⟨by simp, by simpa [ht] using heq⟩
      · intro hu
        have hk3 : k u = 3 := (Finset.mem_filter.mp hu).2.1
        exact Finset.mem_filter.mpr ⟨by simp, Or.inr ⟨by omega, (Finset.mem_filter.mp hu).2.2⟩⟩
    dsimp [f]
    rw [hset]
    have hsub : (Finset.univ.filter fun u : Fin n => k u = 3 ∧ u.val < t.val) ⊂
        (Finset.univ.filter fun u : Fin n => k u = 3) := by
      rw [Finset.ssubset_iff]
      refine ⟨t, ?_, ?_⟩
      · simp
      · intro u hu
        rw [Finset.mem_insert] at hu
        rcases hu with rfl | hA
        · exact Finset.mem_filter.mpr ⟨by simp, by simp [ht]⟩
        · exact Finset.mem_filter.mpr ⟨by simp, (Finset.mem_filter.mp hA).2.1⟩
    have hlt := Finset.card_lt_card hsub
    simpa [k, count_eq_card] using hlt
  have hrank5 : ∀ t : Fin n, k t = 5 → count C 3 ≤ f t ∧ f t < count C 3 + count C 5 := by
    intro t ht
    have hset : (Finset.univ.filter fun u : Fin n => k u < k t ∨ (k u = k t ∧ u.val < t.val)) =
        (Finset.univ.filter fun u : Fin n => k u = 3 ∨ (k u = 5 ∧ u.val < t.val)) := by
      ext u
      constructor
      · intro hu
        rcases (Finset.mem_filter.mp hu).2 with hlt | heq
        · have hu3 : k u = 3 ∨ k u = 5 ∨ k u = 6 := htypes u
          rcases hu3 with h3 | h5 | h6
          · simp [k] at h3 hlt ht ⊢
            exact Or.inl h3
          · simp [k] at h5 hlt ht ⊢
            exfalso
            omega
          · simp [k] at h6 hlt ht ⊢
            exfalso
            omega
        · exact Finset.mem_filter.mpr ⟨by simp, Or.inr (by simpa [ht] using heq)⟩
      · intro hu
        rcases (Finset.mem_filter.mp hu).2 with h3 | h5
        · exact Finset.mem_filter.mpr ⟨by simp, Or.inl (by omega)⟩
        · exact Finset.mem_filter.mpr ⟨by simp, Or.inr ⟨by omega, h5.2⟩⟩
    dsimp [f]
    rw [hset]
    have hsplit : (Finset.univ.filter fun u : Fin n => k u = 3 ∨ (k u = 5 ∧ u.val < t.val)) =
        (Finset.univ.filter fun u : Fin n => k u = 3) ∪
          (Finset.univ.filter fun u : Fin n => k u = 5 ∧ u.val < t.val) := by
      ext u
      by_cases hu3 : k u = 3 <;> simp [Finset.mem_union, hu3]
    rw [hsplit, Finset.card_union_of_disjoint]
    · have hc3 : (Finset.univ.filter fun u : Fin n => k u = 3).card = count C 3 := by
        simp [k, count_eq_card]
      rw [hc3]
      have hsub : (Finset.univ.filter fun u : Fin n => k u = 5 ∧ u.val < t.val) ⊂
          (Finset.univ.filter fun u : Fin n => k u = 5) := by
        rw [Finset.ssubset_iff]
        refine ⟨t, ?_, ?_⟩
        · simp
        · intro u hu
          rw [Finset.mem_insert] at hu
          rcases hu with rfl | hA
          · exact Finset.mem_filter.mpr ⟨by simp, by simp [ht]⟩
          · exact Finset.mem_filter.mpr ⟨by simp, (Finset.mem_filter.mp hA).2.1⟩
      have hlt := Finset.card_lt_card hsub
      have hc5 : (Finset.univ.filter fun u : Fin n => k u = 5).card = count C 5 := by
        simp [k, count_eq_card]
      constructor
      · omega
      · rw [← hc5]
        omega
    · intro u hu huB x hx
      -- disjoint
      have hk3 : k x = 3 := (Finset.mem_filter.mp (hu hx)).2
      have hk5 : k x = 5 := (Finset.mem_filter.mp (huB hx)).2.1
      omega
  have hrank6 : ∀ t : Fin n, k t = 6 → count C 3 + count C 5 ≤ f t ∧ f t < n := by
    intro t ht
    have hset : (Finset.univ.filter fun u : Fin n => k u < k t ∨ (k u = k t ∧ u.val < t.val)) =
        (Finset.univ.filter fun u : Fin n => k u = 3 ∨ k u = 5 ∨ (k u = 6 ∧ u.val < t.val)) := by
      ext u
      constructor
      · intro hu
        rcases (Finset.mem_filter.mp hu).2 with hlt | heq
        · have hu3 : k u = 3 ∨ k u = 5 ∨ k u = 6 := htypes u
          rcases hu3 with h3 | h5 | h6
          · simp [k] at h3 hlt ht ⊢
            exact Or.inl h3
          · simp [k] at h5 hlt ht ⊢
            exact Or.inr (Or.inl h5)
          · simp [k] at h6 hlt ht ⊢
            exfalso
            omega
        · exact Finset.mem_filter.mpr ⟨by simp, Or.inr (Or.inr (by simpa [ht] using heq))⟩
      · intro hu
        rcases (Finset.mem_filter.mp hu).2 with h3 | h5 | h6
        · exact Finset.mem_filter.mpr ⟨by simp, Or.inl (by omega)⟩
        · exact Finset.mem_filter.mpr ⟨by simp, Or.inl (by omega)⟩
        · exact Finset.mem_filter.mpr ⟨by simp, Or.inr ⟨by omega, h6.2⟩⟩
    dsimp [f]
    rw [hset]
    have hsplit : (Finset.univ.filter fun u : Fin n => k u = 3 ∨ k u = 5 ∨ (k u = 6 ∧ u.val < t.val)) =
        (Finset.univ.filter fun u : Fin n => k u = 3 ∨ k u = 5) ∪
          (Finset.univ.filter fun u : Fin n => k u = 6 ∧ u.val < t.val) := by
      ext u
      by_cases hu6 : k u = 6 <;> simp [Finset.mem_union, hu6]
    rw [hsplit, Finset.card_union_of_disjoint]
    · have hc35 : (Finset.univ.filter fun u : Fin n => k u = 3 ∨ k u = 5).card =
        count C 3 + count C 5 := by
        have hs : (Finset.univ.filter fun u : Fin n => k u = 3 ∨ k u = 5) =
            (Finset.univ.filter fun u : Fin n => k u = 3) ∪
              (Finset.univ.filter fun u : Fin n => k u = 5) := by
          ext u
          by_cases hu3 : k u = 3 <;> simp [Finset.mem_union, hu3]
        rw [hs, Finset.card_union_of_disjoint]
        · have hc3 : (Finset.univ.filter fun u : Fin n => k u = 3).card = count C 3 := by
            simp [k, count_eq_card]
          have hc5 : (Finset.univ.filter fun u : Fin n => k u = 5).card = count C 5 := by
            simp [k, count_eq_card]
          rw [hc3, hc5]
        · intro u hu huB x hx
          have hk3 : k x = 3 := (Finset.mem_filter.mp (hu hx)).2
          have hk5 : k x = 5 := (Finset.mem_filter.mp (huB hx)).2
          omega
      rw [hc35]
      constructor
      · omega
      · -- f t < n: the filter is a proper subset of univ (t excluded)
        have hsub : (Finset.univ.filter fun u : Fin n =>
            k u = 3 ∨ k u = 5 ∨ (k u = 6 ∧ u.val < t.val)) ⊂ Finset.univ := by
          rw [Finset.ssubset_iff]
          refine ⟨t, ?_, ?_⟩
          · simp [ht]
          · intro u _
            simp
        have hlt := Finset.card_lt_card hsub
        have hcard : (Finset.univ.filter fun u : Fin n =>
            k u = 3 ∨ k u = 5 ∨ (k u = 6 ∧ u.val < t.val)).card =
            count C 3 + count C 5 +
              (Finset.univ.filter fun u : Fin n => k u = 6 ∧ u.val < t.val).card := by
          rw [hsplit, Finset.card_union_of_disjoint]
          · rw [hc35]
          · intro u hu huB x hx
            have hA : k x = 3 ∨ k x = 5 := (Finset.mem_filter.mp (hu hx)).2
            have hB : k x = 6 := (Finset.mem_filter.mp (huB hx)).2.1
            rcases hA with h3 | h5 <;> omega
        rw [hcard] at hlt
        simpa using hlt
    · intro u hu huB x hx
      have hA : k x = 3 ∨ k x = 5 := (Finset.mem_filter.mp (hu hx)).2
      have hB : k x = 6 := (Finset.mem_filter.mp (huB hx)).2.1
      rcases hA with h3 | h5 <;> omega
  have hfinj : Function.Injective f := by
    intro a b hab
    by_cases hk : k a = k b
    · -- same type: the within-type ranks agree, hence the positions agree
      have hle : a.val = b.val := by
        by_contra hne
        have hlt : a.val < b.val ∨ b.val < a.val := lt_or_gt_of_ne hne
        rcases hlt with habv | hbav
        · have h1 : (Finset.univ.filter fun u : Fin n =>
              k u < k a ∨ (k u = k a ∧ u.val < a.val)) ⊂
              (Finset.univ.filter fun u : Fin n =>
                k u < k b ∨ (k u = k b ∧ u.val < b.val)) := by
            rw [Finset.ssubset_iff]
            refine ⟨a, ?_, ?_⟩
            · simp
            · intro u hu
              rw [Finset.mem_insert] at hu
              rcases hu with rfl | hA
              · exact Finset.mem_filter.mpr ⟨by simp, Or.inr ⟨hk, habv⟩⟩
              · rcases (Finset.mem_filter.mp hA).2 with hltA | heqA
                · exact Finset.mem_filter.mpr ⟨by simp, Or.inl (by omega)⟩
                · exact Finset.mem_filter.mpr ⟨by simp, Or.inr ⟨by omega, by omega⟩⟩
          have hcard := Finset.card_lt_card h1
          have hab' : (Finset.univ.filter fun u : Fin n =>
              k u < k a ∨ (k u = k a ∧ u.val < a.val)).card =
              (Finset.univ.filter fun u : Fin n =>
                k u < k b ∨ (k u = k b ∧ u.val < b.val)).card := by
            simpa [f] using hab
          omega
        · have h1 : (Finset.univ.filter fun u : Fin n =>
              k u < k b ∨ (k u = k b ∧ u.val < b.val)) ⊂
              (Finset.univ.filter fun u : Fin n =>
                k u < k a ∨ (k u = k a ∧ u.val < a.val)) := by
            rw [Finset.ssubset_iff]
            refine ⟨b, ?_, ?_⟩
            · simp
            · intro u hu
              rw [Finset.mem_insert] at hu
              rcases hu with rfl | hB
              · exact Finset.mem_filter.mpr ⟨by simp, Or.inr ⟨by omega, hbav⟩⟩
              · rcases (Finset.mem_filter.mp hB).2 with hltB | heqB
                · exact Finset.mem_filter.mpr ⟨by simp, Or.inl (by omega)⟩
                · exact Finset.mem_filter.mpr ⟨by simp, Or.inr ⟨by omega, by omega⟩⟩
          have hcard := Finset.card_lt_card h1
          have hab' : (Finset.univ.filter fun u : Fin n =>
              k u < k b ∨ (k u = k b ∧ u.val < b.val)).card =
              (Finset.univ.filter fun u : Fin n =>
                k u < k a ∨ (k u = k a ∧ u.val < a.val)).card := by
            simpa [f] using hab.symm
          omega
      apply Fin.ext
      exact hle
    · -- different types: the earlier type has a strictly smaller rank
      have hka : k a = 3 ∨ k a = 5 ∨ k a = 6 := htypes a
      have hkb : k b = 3 ∨ k b = 5 ∨ k b = 6 := htypes b
      have hlt : k a < k b ∨ k b < k a := by omega
      rcases hlt with hab | hba
      · -- f a < f b
        have hfa : f a < f b := by
          rcases hka with h3 | h5 | h6
          · have hfa3 : f a < count C 3 := hrank3 a h3
            have hfb3 : count C 3 ≤ f b := by
              have : k b = 5 ∨ k b = 6 := by omega
              rcases this with h5 | h6
              · exact (hrank5 b h5).1
              · have hb6 : count C 3 + count C 5 ≤ f b := (hrank6 b h6).1
                omega
            omega
          · have hfa5 : f a < count C 3 + count C 5 := (hrank5 a h5).2
            have hfb5 : count C 3 + count C 5 ≤ f b := by
              have : k b = 6 := by omega
              exact (hrank6 b this).1
            omega
          · exfalso
            omega
        omega
      · -- f b < f a
        have hfb : f b < f a := by
          rcases hkb with h3 | h5 | h6
          · have hfb3 : f b < count C 3 := hrank3 b h3
            have hfa3 : count C 3 ≤ f a := by
              have : k a = 5 ∨ k a = 6 := by omega
              rcases this with h5 | h6
              · exact (hrank5 a h5).1
              · have ha6 : count C 3 + count C 5 ≤ f a := (hrank6 a h6).1
                omega
            omega
          · have hfb5 : f b < count C 3 + count C 5 := (hrank5 b h5).2
            have hfa5 : count C 3 + count C 5 ≤ f a := by
              have : k a = 6 := by omega
              exact (hrank6 a this).1
            omega
          · exfalso
            omega
        omega
  have hrange : ∀ t : Fin n, f t < n := by
    intro t
    have hsub : (Finset.univ.filter fun u : Fin n =>
        k u < k t ∨ (k u = k t ∧ u.val < t.val)) ⊂ Finset.univ := by
      rw [Finset.ssubset_iff]
      refine ⟨t, ?_, ?_⟩
      · simp
      · intro u _
        simp
    have hlt := Finset.card_lt_card hsub
    simpa [f] using hlt
  let g : Fin n → Fin n := fun t => ⟨f t, hrange t⟩
  have hginj : Function.Injective g := by
    intro a b hab
    apply Fin.ext
    exact congrArg Fin.val (hfinj (by simpa [g] using congrArg Fin.val hab))
  have hbijg : Function.Bijective g := by
    exact (Fintype.bijective_iff_injective_and_card g).mpr ⟨hginj, rfl⟩
  let p : Equiv (Fin n) (Fin n) := Equiv.ofBijective g hbijg
  refine ⟨Equiv.refl (Fin 4), p, fun _ => false, ?_⟩
  intro t
  have hkt : k t = 3 ∨ k t = 5 ∨ k t = 6 := htypes t
  have hcast : (cast (congrArg Code hm) (linearCode (count C 3) (count C 5) (count C 6))) (p t) =
      (linearCode (count C 3) (count C 5) (count C 6)) (Fin.cast hm.symm (p t)) := by
    exact cast_code_apply hm (linearCode (count C 3) (count C 5) (count C 6)) (p t)
  rw [hcast]
  have hpval : (p t).val = f t := by
    rfl
  rcases hkt with h3 | h5 | h6
  · -- type 3: rank < count 3 → col3
    have hlt : f t < count C 3 := hrank3 t h3
    have hL : (linearCode (count C 3) (count C 5) (count C 6)) (Fin.cast hm.symm (p t)) = col3 := by
      simp [linearCode, hpval, hlt]
    have hR : C t = col3 := by
      have hc : colVal (C t) = 3 := h3
      exact (colVal_eq_three_iff_col3 (C t)).mp hc
    rw [hL]
    exact hR.symm
  · -- type 5
    have hr := hrank5 t h5
    have hL : (linearCode (count C 3) (count C 5) (count C 6)) (Fin.cast hm.symm (p t)) = col5 := by
      have hge : count C 3 ≤ f t := hr.1
      have hlt : f t < count C 3 + count C 5 := hr.2
      simp [linearCode, hpval, hge, hlt]
    have hR : C t = col5 := by
      have hc : colVal (C t) = 5 := h5
      exact (colVal_eq_five_iff_col5 (C t)).mp hc
    rw [hL]
    exact hR.symm
  · -- type 6
    have hr := hrank6 t h6
    have hL : (linearCode (count C 3) (count C 5) (count C 6)) (Fin.cast hm.symm (p t)) = col6 := by
      have hge : count C 3 + count C 5 ≤ f t := hr.1
      simp [linearCode, hpval]
      by_cases h1 : f t < count C 3 <;> by_cases h2 : f t < count C 3 + count C 5 <;>
        simp [h1, h2] <;> omega
    have hR : C t = col6 := by
      have hc : colVal (C t) = 6 := h6
      exact (colVal_eq_six_iff_col6 (C t)).mp hc
    rw [hL]
    exact hR.symm

/-! ## `thm:linearopt` (Theorem 2): universal domination engine

The four `thm:linearopt` (Theorem 2) residues are proved by the paper's descent (each
strictly better code has a smaller spread `max a (max b c) − min a (min b c)`;
the descent terminates at the balanced ideal).  We first normalize an
arbitrary linear code without zero columns to `C(a,b,c)` (via
`linear_equiv_linearCode`), sort its counts (via row-block swaps), and run a
strong induction on the spread.  Codes with zero columns are reduced to
zero-column-free codes first (`linear_zero_to_nozero`).
-/

/-- The canonical code for counts (a,b,c) as a code of length n. -/
def linCode {n : ℕ} (a b c : ℕ) (h : a + b + c = n) : Code n :=
  cast (congrArg Code h) (linearCode a b c)

/-- Strict universal domination is transitive. -/
lemma universalStrictBetter_trans {n : ℕ} {A B C : Code n} (hAB : UniversalStrictBetter A B)
    (hBC : UniversalStrictBetter B C) : UniversalStrictBetter A C := by
  intro ε h0 h1
  exact lt_trans (hBC ε h0 h1) (hAB ε h0 h1)

/-- Strict then weak universal domination is strict. -/
lemma universalStrictBetter_of_better_right {n : ℕ} {A B C : Code n}
    (hAB : UniversalStrictBetter A B) (hBC : UniversalBetter B C) :
    UniversalStrictBetter A C := by
  intro ε h0 h1
  exact lt_of_le_of_lt (hBC ε h0 h1) (hAB ε h0 h1)


/-- Strict universal domination implies weak. -/
lemma universalBetter_of_strict {n : ℕ} {C D : Code n} (h : UniversalStrictBetter C D) :
    UniversalBetter C D := by
  intro ε h0 h1
  exact le_of_lt (h ε h0 h1)

/-- Equality of performance implies weak domination. -/
lemma universalBetter_of_equal {n : ℕ} {C D : Code n} (h : UniversalEqual C D) :
    UniversalBetter C D := by
  intro ε h0 h1
  exact le_of_eq (h ε h0 h1).symm

/-- swap23 (5↔6) equivalence for `linCode`. -/
lemma linCode_swap23_equiv {n : ℕ} {a b c : ℕ} (h1 : a + b + c = n) (h2 : a + c + b = n) :
    Equivalent (linCode a b c h1) (linCode a c b h2) := by
  have e0 : Equivalent
      (cast (congrArg Code (by omega : a + b + c = a + c + b)) (linearCode a b c))
      (linearCode a c b) := linearCode_swap23_equiv a c b
  have e1 := equivalent_of_cast (by omega : a + c + b = n) e0
  simpa [linCode, h1] using e1

/-- swap13 (3↔6) equivalence for `linCode`. -/
lemma linCode_swap13_equiv {n : ℕ} {a b c : ℕ} (h1 : a + b + c = n) (h2 : c + b + a = n) :
    Equivalent (linCode a b c h1) (linCode c b a h2) := by
  have e0 : Equivalent
      (cast (congrArg Code (by omega : a + b + c = c + b + a)) (linearCode a b c))
      (linearCode c b a) := linearCode_swap13_equiv c b a
  have e1 := equivalent_of_cast (by omega : c + b + a = n) e0
  simpa [linCode, h1] using e1

/-- Transport a role-swapped 3→5 comparison (roles (a,c,b)) to
`C(a−1,b,c+1) > C(a,b,c)`. -/
lemma linCode_m1_transport {n a b c : ℕ} (_ha : 1 ≤ a) (hsum : a + b + c = n)
    (hsum' : (a - 1) + b + (c + 1) = n)
    (h : UniversalStrictBetter
      (cast (congrArg Code (by omega : (a - 1) + (c + 1) + b = a + c + b))
        (linearCode (a - 1) (c + 1) b))
      (linearCode a c b)) :
    UniversalStrictBetter (linCode (a - 1) b (c + 1) hsum') (linCode a b c hsum) := by
  have h1' : UniversalStrictBetter
      (cast (congrArg Code (by omega : (a - 1) + (c + 1) + b = n))
        (linearCode (a - 1) (c + 1) b))
      (cast (congrArg Code (by omega : a + c + b = n)) (linearCode a c b)) := by
    simpa using (universalStrictBetter_of_cast (by omega : a + c + b = n) h)
  have e1 : Equivalent (linCode (a - 1) b (c + 1) hsum')
      (cast (congrArg Code (by omega : (a - 1) + (c + 1) + b = n))
        (linearCode (a - 1) (c + 1) b)) := by
    have e0 : Equivalent
        (cast (congrArg Code (by omega : (a - 1) + b + (c + 1) = (a - 1) + (c + 1) + b))
          (linearCode (a - 1) b (c + 1)))
        (linearCode (a - 1) (c + 1) b) :=
      linearCode_swap23_equiv (a - 1) (c + 1) b
    have e1' := equivalent_of_cast (by omega : (a - 1) + (c + 1) + b = n) e0
    simpa [linCode] using e1'
  have e2 : Equivalent (linCode a b c hsum)
      (cast (congrArg Code (by omega : a + c + b = n)) (linearCode a c b)) := by
    have e0 : Equivalent
        (cast (congrArg Code (by omega : a + b + c = a + c + b)) (linearCode a b c))
        (linearCode a c b) := linearCode_swap23_equiv a c b
    have e1' := equivalent_of_cast (by omega : a + c + b = n) e0
    simpa [linCode, hsum] using e1'
  exact universalStrictBetter_of_equivalent
    (linCode (a - 1) b (c + 1) hsum')
    (cast (congrArg Code (by omega : (a - 1) + (c + 1) + b = n)) (linearCode (a - 1) (c + 1) b))
    (linCode a b c hsum)
    (cast (congrArg Code (by omega : a + c + b = n)) (linearCode a c b))
    e1 e2 h1'

/-- The spread of the move `(a,b,c) ↦ (a−1,b,c+1)` decreases (n = 3k−1
descent, cases 1-1/1-2). -/
lemma spread_decrease_m1 {a b c : ℕ} (h1 : c ≤ b) (h2 : b ≤ a) (hsp : 2 ≤ a - c) :
    max (a - 1) (max b (c + 1)) - min (a - 1) (min b (c + 1)) < a - c := by
  by_cases hba : b < a
  · have hM : max (a - 1) (max b (c + 1)) ≤ a - 1 := by
      rw [Nat.max_le]; constructor
      · omega
      · rw [Nat.max_le]; constructor <;> omega
    have hm : c ≤ min (a - 1) (min b (c + 1)) := by
      rw [Nat.le_min]; constructor
      · omega
      · rw [Nat.le_min]; constructor <;> omega
    omega
  · have hab : a = b := by omega
    have hM : max (a - 1) (max b (c + 1)) ≤ a := by
      rw [Nat.max_le]; constructor
      · omega
      · rw [Nat.max_le]; constructor <;> omega
    have hm : c + 1 ≤ min (a - 1) (min b (c + 1)) := by
      rw [Nat.le_min]; constructor
      · omega
      · rw [Nat.le_min]; constructor <;> omega
    omega

/-- The spread of the move `(a,b,c) ↦ (a−2,b,c+2)` decreases (n = 3k−1
descent, cases 1-3/1-4). -/
lemma spread_decrease_m2 {a b c : ℕ} (h1 : c ≤ b) (h2 : b ≤ a) (hsp : 3 ≤ a - c) :
    max (a - 2) (max b (c + 2)) - min (a - 2) (min b (c + 2)) < a - c := by
  by_cases hba : b < a
  · have hM : max (a - 2) (max b (c + 2)) ≤ a - 1 := by
      rw [Nat.max_le]; constructor
      · omega
      · rw [Nat.max_le]; constructor <;> omega
    have hm : c ≤ min (a - 2) (min b (c + 2)) := by
      rw [Nat.le_min]; constructor
      · omega
      · rw [Nat.le_min]; constructor <;> omega
    omega
  · have hab : a = b := by omega
    have hM : max (a - 2) (max b (c + 2)) ≤ a := by
      rw [Nat.max_le]; constructor
      · omega
      · rw [Nat.max_le]; constructor <;> omega
    have hm : c + 1 ≤ min (a - 2) (min b (c + 2)) := by
      rw [Nat.le_min]; constructor
      · omega
      · rw [Nat.le_min]; constructor <;> omega
    omega

/-- `thm:linearopt` (Theorem 2) case 1-3 (n = 3k−1): `a ≥ c+3`. -/
lemma r2_case13_ha {a b c k : ℕ} (hk : 1 ≤ k) (hcb : c ≤ b) (hba : b ≤ a)
    (hsum : a + b + c = k + k + (k - 1)) (hpar3 : SameParity a (b + 1) c)
    (hsp : 2 ≤ a - c) : c + 3 ≤ a := by
  have ha2 : c + 2 ≤ a := by omega
  by_cases h2 : a = c + 2
  · exfalso
    have hb1c : Even (b + 1) ↔ Even c := hpar3.2
    have hparbc : ¬ (Even b ↔ Even c) := by
      have h' : ¬ Even b ↔ Even c := by
        rw [Nat.even_add_one] at hb1c
        exact hb1c
      tauto
    have hb : b = c + 1 := by
      have hcands : b = c ∨ b = c + 1 ∨ b = c + 2 := by omega
      rcases hcands with hb0 | hb1 | hb2
      · exfalso
        exact hparbc (by rw [hb0])
      · exact hb1
      · exfalso
        exact hparbc (by rw [hb2]; exact even_add_two_iff c)
    have : 3 * c + 3 = 3 * k - 1 := by
      rw [h2, hb] at hsum
      have hn' : k + k + (k - 1) = 3 * k - 1 := by omega
      omega
    omega
  · omega

/-- `thm:linearopt` (Theorem 2) case 1-4 (n = 3k−1): `a ≥ c+4`. -/
lemma r2_case14_ha {a b c k : ℕ} (hk : 1 ≤ k) (hcb : c ≤ b) (hba : b ≤ a)
    (hsum : a + b + c = k + k + (k - 1)) (hpar4 : SameParity a b (c + 1))
    (hsp : 2 ≤ a - c) : c + 4 ≤ a := by
  by_cases h2 : a = c + 2
  · exfalso
    have ha1c : Even a ↔ Even (c + 1) := hpar4.1.trans hpar4.2
    have hodd : ¬ (Even a ↔ Even c) := by
      have h' : Even a ↔ ¬ Even c := by
        rw [Nat.even_add_one] at ha1c
        exact ha1c
      tauto
    exact hodd (by rw [h2]; exact even_add_two_iff c)
  · by_cases h3 : a = c + 3
    · exfalso
      have hb1c : Even b ↔ Even (c + 1) := hpar4.2
      have hparbc : ¬ (Even b ↔ Even c) := by
        have h' : Even b ↔ ¬ Even c := by
          rw [Nat.even_add_one] at hb1c
          exact hb1c
        tauto
      have hcand : b = c + 1 ∨ b = c + 3 := by
        have hcands : b = c ∨ b = c + 1 ∨ b = c + 2 ∨ b = c + 3 := by omega
        rcases hcands with hb0 | hb1 | hb2 | hb3
        · exfalso
          exact hparbc (by rw [hb0])
        · exact Or.inl hb1
        · exfalso
          exact hparbc (by rw [hb2]; exact even_add_two_iff c)
        · exact Or.inr hb3
      rcases hcand with hb1 | hb3
      · have : 3 * c + 4 = 3 * k - 1 := by
          rw [h3, hb1] at hsum
          have hn' : k + k + (k - 1) = 3 * k - 1 := by omega
          omega
        omega
      · have : 3 * c + 6 = 3 * k - 1 := by
          rw [h3, hb3] at hsum
          have hn' : k + k + (k - 1) = 3 * k - 1 := by omega
          omega
        omega
    · omega

/-- `thm:linearopt` (Theorem 2) case 1-4 (n = 3k−1): `b ≥ c+1`. -/
lemma r2_case14_hb {a b c : ℕ} (hcb : c ≤ b) (hpar4 : SameParity a b (c + 1)) :
    c + 1 ≤ b := by
  have hb1c : Even b ↔ Even (c + 1) := hpar4.2
  have hparbc : ¬ (Even b ↔ Even c) := by
    have h' : Even b ↔ ¬ Even c := by
      rw [Nat.even_add_one] at hb1c
      exact hb1c
    tauto
  by_contra hb
  have : b = c := by omega
  exact hparbc (by rw [this])

/-- `thm:linearopt` (Theorem 2) case 1-4 (n = 3k−1): `SameParity a b (c+1)` follows when
the other three parity patterns fail. -/
lemma r2_case14_par {a b c : ℕ} (hpar1 : ¬ SameParity a b c) (hpar2 : ¬ SameParity (a + 1) b c)
    (hpar3 : ¬ SameParity a (b + 1) c) : SameParity a b (c + 1) := by
  by_cases hEa : Even a <;> by_cases hEb : Even b <;> by_cases hEc : Even c
  · exfalso; exact hpar1 (by simp [SameParity, hEa, hEb, hEc])
  · simp [SameParity, hEa, hEb, hEc, Nat.even_add_one]
  · exfalso; exact hpar3 (by simp [SameParity, hEa, hEb, hEc, Nat.even_add_one])
  · exfalso; exact hpar2 (by simp [SameParity, hEa, hEb, hEc, Nat.even_add_one])
  · exfalso; exact hpar2 (by simp [SameParity, hEa, hEb, hEc, Nat.even_add_one])
  · exfalso; exact hpar3 (by simp [SameParity, hEa, hEb, hEc, Nat.even_add_one])
  · simp [SameParity, hEa, hEb, hEc, Nat.even_add_one]
  · exfalso; exact hpar1 (by simp [SameParity, hEa, hEb, hEc])

/-- `thm:linearopt` (Theorem 2) descent, cases 1-1/1-2: if one of the first two parity
patterns holds, the m1 move `(a,b,c) ↦ (a−1,b,c+1)` is strictly better with
smaller spread. -/
lemma linear_descent_step_m1 {n a b c : ℕ}
    (hsorted : c ≤ b ∧ b ≤ a) (hsum : a + b + c = n) (hspread : 2 ≤ a - c)
    (hpar : SameParity a b c ∨ SameParity (a + 1) b c) :
    ∃ a' c' : ℕ, ∃ hsum' : a' + b + c' = n,
      max a' (max b c') - min a' (min b c') < a - c ∧
        UniversalStrictBetter (linCode a' b c' hsum') (linCode a b c hsum) := by
  have hcb : c ≤ b := hsorted.1
  have hba : b ≤ a := hsorted.2
  have ha1 : 1 ≤ a := by omega
  have hsum1 : (a - 1) + b + (c + 1) = n := by
    calc
      (a - 1) + b + (c + 1) = a + b + c := by omega
      _ = n := hsum
  rcases hpar with hpar1 | hpar2
  · -- case 1-1
    refine ⟨a - 1, c + 1, hsum1, ?_, ?_⟩
    · exact spread_decrease_m1 hcb hba hspread
    · have hpar' : SameParity a c b := ⟨hpar1.1.trans hpar1.2, hpar1.2.symm⟩
      have hcmp := (linear_compare a c b (by omega : 0 < a)).2.1 hpar'
      exact linCode_m1_transport ha1 hsum hsum1 (hcmp.2 (by omega : 2 ≤ a))
  · -- case 1-2
    refine ⟨a - 1, c + 1, hsum1, ?_, ?_⟩
    · exact spread_decrease_m1 hcb hba hspread
    · have hpar' : SameParity (a - 1) c b := by
        have h1 : Even (a - 1) ↔ Even (a + 1) := by
          have : a + 1 = (a - 1) + 2 := by omega
          rw [this]
          exact (even_add_two_iff (a - 1)).symm
        constructor
        · exact h1.trans (hpar2.1.trans hpar2.2)
        · exact hpar2.2.symm
      have hcmp := (linear_compare a c b (by omega : 0 < a)).2.2
        (by omega : c ≤ a) (by omega : c ≤ b) hpar'
      exact linCode_m1_transport ha1 hsum hsum1 (hcmp.2 (by omega : a > c + 1))

/-- `thm:linearopt` (Theorem 2) descent step for n = 3k−1: every sorted triple with
spread ≥ 2 has a strictly better code with smaller spread (paper cases
1-1 .. 1-4). -/
lemma linear_descent_step_r2 {k n a b c : ℕ} (hk : 1 ≤ k) (hn : n = k + k + (k - 1))
    (hsorted : c ≤ b ∧ b ≤ a) (hsum : a + b + c = n) (hspread : 2 ≤ a - c) :
    ∃ a' c' : ℕ, ∃ hsum' : a' + b + c' = n,
      max a' (max b c') - min a' (min b c') < a - c ∧
        UniversalStrictBetter (linCode a' b c' hsum') (linCode a b c hsum) := by
  have hcb : c ≤ b := hsorted.1
  have hba : b ≤ a := hsorted.2
  have hsum2 : (a - 2) + b + (c + 2) = n := by
    calc
      (a - 2) + b + (c + 2) = a + b + c := by omega
      _ = n := hsum
  by_cases hpar1 : SameParity a b c
  · exact linear_descent_step_m1 hsorted hsum hspread (Or.inl hpar1)
  · by_cases hpar2 : SameParity (a + 1) b c
    · exact linear_descent_step_m1 hsorted hsum hspread (Or.inr hpar2)
    · by_cases hpar3 : SameParity a (b + 1) c
      · -- case 1-3
        have ha : c + 3 ≤ a := r2_case13_ha hk hcb hba (by omega) hpar3 hspread
        have hb1 : c - 1 ≤ b := by omega
        refine ⟨a - 2, c + 2, hsum2, ?_, ?_⟩
        · have hsp2 : 3 ≤ a - c := by omega
          exact spread_decrease_m2 hcb hba hsp2
        · have hcor := linear_cor1 a b c (by omega : 2 ≤ a)
            (Or.inl ⟨hpar3, ha, hb1⟩)
          simpa [linCode] using (universalStrictBetter_of_cast (by omega : a + b + c = n) hcor)
      · -- case 1-4
        have hpar4 : SameParity a b (c + 1) := r2_case14_par hpar1 hpar2 hpar3
        have ha : c + 4 ≤ a := r2_case14_ha hk hcb hba (by omega) hpar4 hspread
        have hb1 : c + 1 ≤ b := r2_case14_hb hcb hpar4
        refine ⟨a - 2, c + 2, hsum2, ?_, ?_⟩
        · have hsp2 : 3 ≤ a - c := by omega
          exact spread_decrease_m2 hcb hba hsp2
        · have hcor := linear_cor1 a b c (by omega : 2 ≤ a)
            (Or.inr ⟨hpar4, ha, hb1⟩)
          simpa [linCode] using (universalStrictBetter_of_cast (by omega : a + b + c = n) hcor)

/-- `thm:linearopt` (Theorem 2) descent step for n = 3k and n = 3k+1: every sorted triple
with spread ≥ 4 has a strictly better code with smaller spread.  The four
parity cases are the same as the n = 3k−1 ones; the stronger spread hypothesis
supplies the `cor:linear1` (Corollary 13) bounds directly (no mod-3 argument needed). -/
lemma linear_descent_step_ge4 {n a b c : ℕ}
    (hsorted : c ≤ b ∧ b ≤ a) (hsum : a + b + c = n) (hspread : 4 ≤ a - c) :
    ∃ a' c' : ℕ, ∃ hsum' : a' + b + c' = n,
      max a' (max b c') - min a' (min b c') < a - c ∧
        UniversalStrictBetter (linCode a' b c' hsum') (linCode a b c hsum) := by
  have hcb : c ≤ b := hsorted.1
  have hba : b ≤ a := hsorted.2
  have hsum2 : (a - 2) + b + (c + 2) = n := by
    calc
      (a - 2) + b + (c + 2) = a + b + c := by omega
      _ = n := hsum
  by_cases hpar1 : SameParity a b c
  · exact linear_descent_step_m1 hsorted hsum (by omega) (Or.inl hpar1)
  · by_cases hpar2 : SameParity (a + 1) b c
    · exact linear_descent_step_m1 hsorted hsum (by omega) (Or.inr hpar2)
    · by_cases hpar3 : SameParity a (b + 1) c
      · -- case 2-3 / 3-3
        have ha : c + 3 ≤ a := by omega
        have hb1 : c - 1 ≤ b := by omega
        refine ⟨a - 2, c + 2, hsum2, ?_, ?_⟩
        · have hsp2 : 3 ≤ a - c := by omega
          exact spread_decrease_m2 hcb hba hsp2
        · have hcor := linear_cor1 a b c (by omega : 2 ≤ a)
            (Or.inl ⟨hpar3, ha, hb1⟩)
          simpa [linCode] using (universalStrictBetter_of_cast (by omega : a + b + c = n) hcor)
      · -- case 2-4 / 3-4
        have hpar4 : SameParity a b (c + 1) := r2_case14_par hpar1 hpar2 hpar3
        have ha : c + 4 ≤ a := by omega
        have hb1 : c + 1 ≤ b := r2_case14_hb hcb hpar4
        refine ⟨a - 2, c + 2, hsum2, ?_, ?_⟩
        · have hsp2 : 3 ≤ a - c := by omega
          exact spread_decrease_m2 hcb hba hsp2
        · have hcor := linear_cor1 a b c (by omega : 2 ≤ a)
            (Or.inr ⟨hpar4, ha, hb1⟩)
          simpa [linCode] using (universalStrictBetter_of_cast (by omega : a + b + c = n) hcor)

/-- The sorted triples with sum 3k (n = 3k residue) and spread ≤ 3: the two
ideals (k+1,k+1,k−2), (k+1,k,k−1), plus (k,k,k) and (k+2,k−1,k−1). -/
lemma r0_base_cases {A B C k : ℕ} (hk : 2 ≤ k) (hord : C ≤ B ∧ B ≤ A)
    (hsum : A + B + C = k + 1 + k + (k - 1)) (hsp : A - C ≤ 3) :
    (A = k ∧ B = k ∧ C = k) ∨ (A = k + 1 ∧ B = k ∧ C = k - 1) ∨
      (A = k + 1 ∧ B = k + 1 ∧ C = k - 2) ∨ (A = k + 2 ∧ B = k - 1 ∧ C = k - 1) := by
  have hA : A = C ∨ A = C + 1 ∨ A = C + 2 ∨ A = C + 3 := by omega
  rcases hA with hA0 | hA1 | hA2 | hA3
  · -- A = C: then B = C and 3C = 3k
    left
    omega
  · -- A = C + 1
    have hcand : B = C ∨ B = C + 1 := by omega
    rcases hcand with hB0 | hB1
    · exfalso
      omega
    · exfalso
      omega
  · -- A = C + 2
    have hcand : B = C ∨ B = C + 1 ∨ B = C + 2 := by omega
    rcases hcand with hB0 | hB1 | hB2
    · exfalso
      omega
    · right; left
      omega
    · exfalso
      omega
  · -- A = C + 3
    have hcand : B = C ∨ B = C + 1 ∨ B = C + 2 ∨ B = C + 3 := by omega
    rcases hcand with hB0 | hB1 | hB2 | hB3
    · right; right; right
      omega
    · exfalso
      omega
    · exfalso
      omega
    · right; right; left
      omega

/-- The sorted triples with sum 3k+1 (n = 3k+1 residue) and spread ≤ 3:
the two ideals (k+1,k,k), (k+2,k,k−1), plus (k+1,k+1,k−1). -/
lemma r1_base_cases {A B C k : ℕ} (hk : 1 ≤ k) (hord : C ≤ B ∧ B ≤ A)
    (hsum : A + B + C = k + 1 + k + k) (hsp : A - C ≤ 3) :
    (A = k + 1 ∧ B = k ∧ C = k) ∨ (A = k + 1 ∧ B = k + 1 ∧ C = k - 1) ∨
      (A = k + 2 ∧ B = k ∧ C = k - 1) := by
  have hA : A = C ∨ A = C + 1 ∨ A = C + 2 ∨ A = C + 3 := by omega
  rcases hA with hA0 | hA1 | hA2 | hA3
  · -- A = C
    exfalso
    omega
  · -- A = C + 1
    have hcand : B = C ∨ B = C + 1 := by omega
    rcases hcand with hB0 | hB1
    · left
      omega
    · exfalso
      omega
  · -- A = C + 2
    have hcand : B = C ∨ B = C + 1 ∨ B = C + 2 := by omega
    rcases hcand with hB0 | hB1 | hB2
    · exfalso
      omega
    · exfalso
      omega
    · right; left
      omega
  · -- A = C + 3
    have hcand : B = C ∨ B = C + 1 ∨ B = C + 2 ∨ B = C + 3 := by omega
    rcases hcand with hB0 | hB1 | hB2 | hB3
    · exfalso
      omega
    · right; right
      omega
    · exfalso
      omega
    · exfalso
      omega

/-- Transport a role-swapped 3→5 comparison (roles (a,c,b)) to the
`linCode` form with `UniversalEqual` (used for the λ-equality of the two
ideals in the n = 3k and n = 3k+1 residues). -/
lemma universalEqual_of_equiv_both {n : ℕ} (C₁ C₁' C₂ C₂' : Code n)
    (h1 : Equivalent C₁ C₁') (h2 : Equivalent C₂ C₂') (h : UniversalEqual C₁' C₂') :
    UniversalEqual C₁ C₂ := by
  intro ε h0 h1'
  have heq := h ε h0 h1'
  have heq1 := lambda_equiv C₁ C₁' h1 ε
  have heq2 := lambda_equiv C₂ C₂' h2 ε
  linarith

/-- Transport a role-swapped 3→5 comparison (roles (a,c,b)) to the
`linCode` form with `UniversalEqual` (used for the λ-equality of the two
ideals in the n = 3k and n = 3k+1 residues). -/
lemma linCode_m1_equal_transport {n a b c : ℕ} (_ha : 1 ≤ a) (hsum : a + b + c = n)
    (hsum' : (a - 1) + b + (c + 1) = n)
    (h : UniversalEqual
      (cast (congrArg Code (by omega : (a - 1) + (c + 1) + b = a + c + b))
        (linearCode (a - 1) (c + 1) b))
      (linearCode a c b)) :
    UniversalEqual (linCode (a - 1) b (c + 1) hsum') (linCode a b c hsum) := by
  have h1' : UniversalEqual
      (cast (congrArg Code (by omega : (a - 1) + (c + 1) + b = n))
        (linearCode (a - 1) (c + 1) b))
      (cast (congrArg Code (by omega : a + c + b = n)) (linearCode a c b)) := by
    simpa using (universalEqual_of_cast (by omega : a + c + b = n) h)
  have e1 : Equivalent (linCode (a - 1) b (c + 1) hsum')
      (cast (congrArg Code (by omega : (a - 1) + (c + 1) + b = n))
        (linearCode (a - 1) (c + 1) b)) := by
    have e0 : Equivalent
        (cast (congrArg Code (by omega : (a - 1) + b + (c + 1) = (a - 1) + (c + 1) + b))
          (linearCode (a - 1) b (c + 1)))
        (linearCode (a - 1) (c + 1) b) :=
      linearCode_swap23_equiv (a - 1) (c + 1) b
    have e1' := equivalent_of_cast (by omega : (a - 1) + (c + 1) + b = n) e0
    simpa [linCode] using e1'
  have e2 : Equivalent (linCode a b c hsum)
      (cast (congrArg Code (by omega : a + c + b = n)) (linearCode a c b)) := by
    have e0 : Equivalent
        (cast (congrArg Code (by omega : a + b + c = a + c + b)) (linearCode a b c))
        (linearCode a c b) := linearCode_swap23_equiv a c b
    have e1' := equivalent_of_cast (by omega : a + c + b = n) e0
    simpa [linCode, hsum] using e1'
  exact universalEqual_of_equiv_both
    (linCode (a - 1) b (c + 1) hsum')
    (cast (congrArg Code (by omega : (a - 1) + (c + 1) + b = n))
      (linearCode (a - 1) (c + 1) b))
    (linCode a b c hsum)
    (cast (congrArg Code (by omega : a + c + b = n)) (linearCode a c b))
    e1 e2 h1'

/-- Code equality gives universal equality of performance. -/
lemma universalEqual_of_eq {n : ℕ} {C D : Code n} (h : C = D) : UniversalEqual C D := by
  intro ε h0 h1
  rw [h]

/-- Universal equality is reflexive. -/
lemma universalEqual_refl {n : ℕ} (C : Code n) : UniversalEqual C C := by
  intro ε h0 h1
  rfl

/-- `linCode` with equal counts is the same code (the length proofs are
proof-irrelevant). -/
lemma linCode_eq_of_counts {n : ℕ} {a b c x y z : ℕ} (ha : a = x) (hb : b = y) (hc : c = z)
    (hsum : a + b + c = n) (hsum' : x + y + z = n) :
    linCode a b c hsum = linCode x y z hsum' := by
  subst x
  subst y
  subst z
  rfl

/-- Transport a direct 3→5 comparison to `linCode` form. -/
lemma linCode_m1_direct_transport {n a b c : ℕ} (_ha : 1 ≤ a) (hsum : a + b + c = n)
    (hsum' : (a - 1) + (b + 1) + c = n)
    (h : UniversalStrictBetter
      (cast (congrArg Code (by omega : (a - 1) + (b + 1) + c = a + b + c))
        (linearCode (a - 1) (b + 1) c))
      (linearCode a b c)) :
    UniversalStrictBetter (linCode (a - 1) (b + 1) c hsum') (linCode a b c hsum) := by
  have h1' : UniversalStrictBetter
      (cast (congrArg Code (by omega : (a - 1) + (b + 1) + c = n))
        (linearCode (a - 1) (b + 1) c))
      (cast (congrArg Code (by omega : a + b + c = n)) (linearCode a b c)) := by
    simpa using (universalStrictBetter_of_cast (by omega : a + b + c = n) h)
  have e1 : Equivalent (linCode (a - 1) (b + 1) c hsum')
      (cast (congrArg Code (by omega : (a - 1) + (b + 1) + c = n))
        (linearCode (a - 1) (b + 1) c)) := by
    have e0 : Equivalent
        (linearCode (a - 1) (b + 1) c)
        (linearCode (a - 1) (b + 1) c) := equivalent_refl _
    have e1' := equivalent_of_cast (by omega : (a - 1) + (b + 1) + c = n) e0
    simpa [linCode] using e1'
  have e2 : Equivalent (linCode a b c hsum)
      (cast (congrArg Code (by omega : a + b + c = n)) (linearCode a b c)) := by
    have e0 : Equivalent (linearCode a b c) (linearCode a b c) := equivalent_refl _
    have e1' := equivalent_of_cast (by omega : a + b + c = n) e0
    simpa [linCode, hsum] using e1'
  exact universalStrictBetter_of_eq_left
    (universalStrictBetter_of_equiv_left (equivalent_symm e1) h1')
    (universalEqual_of_equivalent
      (cast (congrArg Code (by omega : a + b + c = n)) (linearCode a b c))
      (linCode a b c hsum)
      (equivalent_symm e2))

/-- `thm:linearopt` (Theorem 2) n = 3k base: C(k+1,k,k−1) strictly dominates C(k,k,k). -/
lemma r0_kkk_dominated {k n : ℕ} (hk : 2 ≤ k) (hn : n = k + 1 + k + (k - 1))
    (hsum : k + k + k = n) :
    UniversalStrictBetter (linCode (k + 1) k (k - 1) (by omega)) (linCode k k k hsum) := by
  have hsum1 : (k - 1) + k + (k + 1) = n := by omega
  have hsum2 : (k + 1) + k + (k - 1) = n := by omega
  have hcmp := (linear_compare k k k (by omega : 0 < k)).2.1 (by simp [SameParity])
  have hdom : UniversalStrictBetter (linCode (k - 1) k (k + 1) hsum1) (linCode k k k hsum) :=
    linCode_m1_transport (by omega : 1 ≤ k) hsum hsum1 (hcmp.2 hk)
  have hEq : Equivalent (linCode (k - 1) k (k + 1) hsum1) (linCode (k + 1) k (k - 1) hsum2) :=
    linCode_swap13_equiv hsum1 hsum2
  exact universalStrictBetter_of_equiv_left hEq hdom

/-- `thm:linearopt` (Theorem 2) n = 3k base: C(k+1,k,k−1) strictly dominates
C(k+2,k−1,k−1). -/
lemma r0_kkkm1m1_dominated {k n : ℕ} (hk : 2 ≤ k) (hn : n = k + 1 + k + (k - 1))
    (hsum : (k + 2) + (k - 1) + (k - 1) = n) :
    UniversalStrictBetter (linCode (k + 1) k (k - 1) (by omega))
      (linCode (k + 2) (k - 1) (k - 1) hsum) := by
  have hsum1 : (k + 1) + (k - 1) + k = n := by omega
  have hsum2 : (k + 1) + k + (k - 1) = n := by omega
  have hpar2 : SameParity (k + 3) (k - 1) (k - 1) := by
    have h1 : Even (k + 3) ↔ Even (k + 1) := by
      have : k + 3 = (k + 1) + 2 := by omega
      rw [this]
      exact even_add_two_iff (k + 1)
    have h2 : Even (k + 1) ↔ Even (k - 1) := by
      have : k + 1 = (k - 1) + 2 := by omega
      rw [this]
      exact even_add_two_iff (k - 1)
    simp [SameParity, h1, h2]
  have hpar' : SameParity (k + 1) (k - 1) (k - 1) := by
    have h1 : Even (k + 1) ↔ Even (k + 3) := by
      have : k + 3 = (k + 1) + 2 := by omega
      rw [this]
      exact (even_add_two_iff (k + 1)).symm
    constructor
    · exact h1.trans (hpar2.1.trans hpar2.2)
    · exact hpar2.2.symm
  have hcmp := (linear_compare (k + 2) (k - 1) (k - 1) (by omega : 0 < k + 2)).2.2
    (by omega : k - 1 ≤ k + 2) (by omega : k - 1 ≤ k - 1) hpar'
  have hsum1' : (k + 2 - 1) + (k - 1) + (k - 1 + 1) = n := by omega
  have hdom : UniversalStrictBetter (linCode (k + 2 - 1) (k - 1) (k - 1 + 1) hsum1')
      (linCode (k + 2) (k - 1) (k - 1) hsum) :=
    linCode_m1_transport (by omega : 1 ≤ k + 2) hsum hsum1'
      (hcmp.2 (by omega : k + 2 > (k - 1) + 1))
  have hCast : linCode (k + 2 - 1) (k - 1) (k - 1 + 1) hsum1' = linCode (k + 1) (k - 1) k hsum1 := by
    apply linCode_eq_of_counts
    · omega
    · omega
    · omega
  have hEqC : Equivalent (linCode (k + 2 - 1) (k - 1) (k - 1 + 1) hsum1')
      (linCode (k + 1) (k - 1) k hsum1) := by
    rw [hCast]
    exact equivalent_refl _
  have hEq : Equivalent (linCode (k + 1) (k - 1) k hsum1)
      (linCode (k + 1) k (k - 1) hsum2) :=
    linCode_swap23_equiv hsum1 hsum2
  exact universalStrictBetter_of_equiv_left hEq (universalStrictBetter_of_equiv_left hEqC hdom)

/-- `thm:linearopt` (Theorem 2) n = 3k+1 base: C(k+2,k,k−1) strictly dominates
C(k+1,k+1,k−1). -/
lemma r1_mid_dominated {k n : ℕ} (hk : 1 ≤ k) (hn : n = k + 1 + k + k)
    (hsum : (k + 1) + (k + 1) + (k - 1) = n) :
    UniversalStrictBetter (linCode (k + 2) k (k - 1) (by omega))
      (linCode (k + 1) (k + 1) (k - 1) hsum) := by
  have hsum1 : k + (k + 2) + (k - 1) = n := by omega
  have hpar : SameParity (k + 1) (k + 1) (k - 1) := by
    have h1 : Even (k + 1) ↔ Even (k - 1) := by
      have : k + 1 = (k - 1) + 2 := by omega
      rw [this]
      exact even_add_two_iff (k - 1)
    simp [SameParity, h1]
  have hcmp := (linear_compare (k + 1) (k + 1) (k - 1) (by omega : 0 < k + 1)).2.1 hpar
  have hdom : UniversalStrictBetter (linCode k (k + 2) (k - 1) hsum1)
      (linCode (k + 1) (k + 1) (k - 1) hsum) :=
    linCode_m1_direct_transport (by omega : 1 ≤ k + 1) hsum hsum1 (hcmp.2 (by omega : 2 ≤ k + 1))
  have hsumA : (k - 1) + (k + 2) + k = n := by omega
  have hsumB : (k - 1) + k + (k + 2) = n := by omega
  have hsum2 : (k + 2) + k + (k - 1) = n := by omega
  have e0 : Equivalent (linCode k (k + 2) (k - 1) hsum1) (linCode (k - 1) (k + 2) k hsumA) :=
    linCode_swap13_equiv hsum1 hsumA
  have e1 : Equivalent (linCode (k - 1) (k + 2) k hsumA) (linCode (k - 1) k (k + 2) hsumB) :=
    linCode_swap23_equiv hsumA hsumB
  have e2 : Equivalent (linCode (k - 1) k (k + 2) hsumB) (linCode (k + 2) k (k - 1) hsum2) :=
    linCode_swap13_equiv hsumB hsum2
  have hEq : Equivalent (linCode k (k + 2) (k - 1) hsum1) (linCode (k + 2) k (k - 1) hsum2) :=
    equivalent_trans (equivalent_trans e0 e1) e2
  exact universalStrictBetter_of_equiv_left hEq hdom

/-- `thm:linearopt` (Theorem 2) n = 3k: the two optima have equal λ. -/
lemma r0_ideals_equal {k n : ℕ} (hk : 2 ≤ k) (hn : n = k + 1 + k + (k - 1))
    (hsumI1 : (k + 1) + (k + 1) + (k - 2) = n)
    (hsumI2 : (k + 1) + k + (k - 1) = n) :
    UniversalEqual (linCode (k + 1) (k + 1) (k - 2) hsumI1)
      (linCode (k + 1) k (k - 1) hsumI2) := by
  have hsumA : k + (k + 1) + (k - 1) = n := by omega
  have hpar : SameParity (k + 1) (k - 2 + 1) (k + 1) := by
    have h1 : Even (k + 1) ↔ Even (k - 2 + 1) := by
      have : k + 1 = (k - 2 + 1) + 2 := by omega
      rw [this]
      exact even_add_two_iff (k - 2 + 1)
    simp [SameParity, h1]
  have hcmp := (linear_compare (k + 1) (k - 2) (k + 1) (by omega : 0 < k + 1)).1 hpar
  have hT : UniversalEqual (linCode k (k + 1) (k - 1) hsumA)
      (linCode (k + 1) (k + 1) (k - 2) hsumI1) := by
    have hT0 := linCode_m1_equal_transport (a := k + 1) (b := k + 1) (c := k - 2)
      (by omega : 1 ≤ k + 1) hsumI1 (by omega : (k + 1 - 1) + (k + 1) + (k - 2 + 1) = n) hcmp
    have hCast : linCode k (k + 1) (k - 1) hsumA =
        linCode (k + 1 - 1) (k + 1) (k - 2 + 1) (by omega : (k + 1 - 1) + (k + 1) + (k - 2 + 1) = n) := by
      apply linCode_eq_of_counts
      · omega
      · omega
      · omega
    exact universalEqual_trans (universalEqual_of_eq hCast) hT0
  have hsumC : (k - 1) + (k + 1) + k = n := by omega
  have hsumD : (k - 1) + k + (k + 1) = n := by omega
  have e0 : Equivalent (linCode k (k + 1) (k - 1) hsumA) (linCode (k - 1) (k + 1) k hsumC) :=
    linCode_swap13_equiv hsumA hsumC
  have e1 : Equivalent (linCode (k - 1) (k + 1) k hsumC) (linCode (k - 1) k (k + 1) hsumD) :=
    linCode_swap23_equiv hsumC hsumD
  have e2 : Equivalent (linCode (k - 1) k (k + 1) hsumD) (linCode (k + 1) k (k - 1) hsumI2) :=
    linCode_swap13_equiv hsumD hsumI2
  have hEq : Equivalent (linCode k (k + 1) (k - 1) hsumA) (linCode (k + 1) k (k - 1) hsumI2) :=
    equivalent_trans (equivalent_trans e0 e1) e2
  have hUB : UniversalEqual (linCode (k + 1) k (k - 1) hsumI2) (linCode k (k + 1) (k - 1) hsumA) :=
    universalEqual_of_equiv_left hEq (universalEqual_refl (linCode k (k + 1) (k - 1) hsumA))
  exact universalEqual_trans (universalEqual_symm hT) (universalEqual_symm hUB)

/-- `thm:linearopt` (Theorem 2) n = 3k+1: the two optima have equal λ. -/
lemma r1_ideals_equal {k n : ℕ} (hk : 1 ≤ k) (hn : n = k + 1 + k + k)
    (hsumI1 : (k + 1) + k + k = n) (hsumI2 : (k + 2) + k + (k - 1) = n) :
    UniversalEqual (linCode (k + 1) k k hsumI1) (linCode (k + 2) k (k - 1) hsumI2) := by
  have hsumA : k + k + (k + 1) = n := by omega
  have hsumD : (k - 1) + k + (k + 2) = n := by omega
  have hpar : SameParity k (k + 2) k := by
    have h1 : Even (k + 2) ↔ Even k := by
      exact even_add_two_iff k
    simp [SameParity, h1]
  have hcmp := (linear_compare k (k + 1) k (by omega : 0 < k)).1 hpar
  have hT : UniversalEqual (linCode (k - 1) k (k + 2) (by omega : (k - 1) + k + (k + 2) = n))
      (linCode k k (k + 1) hsumA) := by
    have hT0 := linCode_m1_equal_transport (a := k) (b := k) (c := k + 1)
      (by omega : 1 ≤ k) hsumA (by omega : (k - 1) + k + (k + 2) = n) hcmp
    exact hT0
  have eL0 : Equivalent (linCode k k (k + 1) hsumA) (linCode (k + 1) k k hsumI1) :=
    linCode_swap13_equiv hsumA hsumI1
  have hL : UniversalEqual (linCode (k + 1) k k hsumI1) (linCode k k (k + 1) hsumA) :=
    universalEqual_of_equiv_left eL0 (universalEqual_refl (linCode k k (k + 1) hsumA))
  have hR : UniversalEqual (linCode (k - 1) k (k + 2) hsumD) (linCode (k + 2) k (k - 1) hsumI2) :=
    universalEqual_of_equiv_left (equivalent_symm (linCode_swap13_equiv hsumD hsumI2))
      (universalEqual_refl (linCode (k + 2) k (k - 1) hsumI2))
  exact universalEqual_trans (universalEqual_trans hL (universalEqual_symm hT)) hR

/-- Any triple is equivalent (via row-block swaps) to its sorted version; the
spread is unchanged. -/
lemma linCode_sorted_equiv {n : ℕ} {a b c : ℕ} (hsum : a + b + c = n) :
    ∃ A B C : ℕ, ∃ hsumABC : A + B + C = n,
      C ≤ B ∧ B ≤ A ∧
      Equivalent (linCode a b c hsum) (linCode A B C hsumABC) ∧
        max A (max B C) - min A (min B C) = max a (max b c) - min a (min b c) := by
  have hcases : (c ≤ b ∧ b ≤ a) ∨ (c ≤ a ∧ a ≤ b) ∨ (b ≤ c ∧ c ≤ a) ∨
      (b ≤ a ∧ a ≤ c) ∨ (a ≤ c ∧ c ≤ b) ∨ (a ≤ b ∧ b ≤ c) := by omega
  rcases hcases with h1 | h1 | h1 | h1 | h1 | h1
  · refine ⟨a, b, c, hsum, h1.1, h1.2, ?_, ?_⟩
    · exact equivalent_refl (linCode a b c hsum)
    · have hca : c ≤ a := by omega
      simp [h1.1, h1.2, hca]
  · -- (a,b,c) → sorted (b,a,c)
    have hsum_acb : a + c + b = n := by omega
    have hsum_bca : b + c + a = n := by omega
    have hsum_bac : b + a + c = n := by omega
    refine ⟨b, a, c, hsum_bac, h1.1, h1.2, ?_, ?_⟩
    · have e0 : Equivalent (linCode a b c hsum) (linCode a c b hsum_acb) :=
        linCode_swap23_equiv hsum hsum_acb
      have e1 : Equivalent (linCode a c b hsum_acb) (linCode b c a hsum_bca) :=
        linCode_swap13_equiv hsum_acb hsum_bca
      have e2 : Equivalent (linCode b c a hsum_bca) (linCode b a c hsum_bac) :=
        linCode_swap23_equiv hsum_bca hsum_bac
      exact equivalent_trans (equivalent_trans e0 e1) e2
    · have hbc : c ≤ b := by omega
      simp [h1.1, h1.2, hbc]
  · -- (a,b,c) → sorted (a,c,b)
    have hsum_acb : a + c + b = n := by omega
    refine ⟨a, c, b, hsum_acb, h1.1, h1.2, ?_, ?_⟩
    · exact linCode_swap23_equiv hsum hsum_acb
    · have hba : b ≤ a := by omega
      simp [h1.1, h1.2, hba]
  · -- (a,b,c) → sorted (c,a,b)
    have hsum_cba : c + b + a = n := by omega
    have hsum_cab : c + a + b = n := by omega
    refine ⟨c, a, b, hsum_cab, h1.1, h1.2, ?_, ?_⟩
    · have e0 : Equivalent (linCode a b c hsum) (linCode c b a hsum_cba) :=
        linCode_swap13_equiv hsum hsum_cba
      have e1 : Equivalent (linCode c b a hsum_cba) (linCode c a b hsum_cab) :=
        linCode_swap23_equiv hsum_cba hsum_cab
      exact equivalent_trans e0 e1
    · have hbc : b ≤ c := by omega
      simp [h1.1, h1.2, hbc]
  · -- (a,b,c) → sorted (b,c,a)
    have hsum_acb : a + c + b = n := by omega
    have hsum_bca : b + c + a = n := by omega
    refine ⟨b, c, a, hsum_bca, h1.1, h1.2, ?_, ?_⟩
    · have e0 : Equivalent (linCode a b c hsum) (linCode a c b hsum_acb) :=
        linCode_swap23_equiv hsum hsum_acb
      have e1 : Equivalent (linCode a c b hsum_acb) (linCode b c a hsum_bca) :=
        linCode_swap13_equiv hsum_acb hsum_bca
      exact equivalent_trans e0 e1
    · have hab : a ≤ b := by omega
      simp [h1.1, h1.2, hab]
  · -- (a,b,c) → sorted (c,b,a)
    have hsum_cba : c + b + a = n := by omega
    refine ⟨c, b, a, hsum_cba, h1.1, h1.2, ?_, ?_⟩
    · exact linCode_swap13_equiv hsum hsum_cba
    · have hac : a ≤ c := by omega
      simp [h1.1, h1.2, hac]

/-- A Finset of cardinality two containing two distinct elements is exactly
their pair. -/
lemma card_two_eq_pair {α : Type*} [DecidableEq α] {s : Finset α} {a b : α}
    (hcard : s.card = 2) (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b) : s = {a, b} := by
  have hsub : s ⊆ ({a, b} : Finset α) := by
    intro x hx
    by_contra hxab
    have hx1 : x ≠ a := by
      intro h
      exact hxab (by simp [h])
    have hx2 : x ≠ b := by
      intro h
      exact hxab (by simp [h])
    have hins : insert x ({a, b} : Finset α) ⊆ s := by
      intro y hy
      simp at hy
      rcases hy with rfl | rfl | rfl <;> simp [ha, hb, hx]
    have hcard3 : (insert x ({a, b} : Finset α)).card = 3 := by
      simp [hx1, hx2, hab]
    have hle : 3 ≤ s.card := by
      rw [← hcard3]
      exact Finset.card_le_card hins
    omega
  have hcard2 : ({a, b} : Finset α).card = 2 := by simp [hab]
  exact Finset.eq_of_subset_of_card_le hsub (by omega)

/-- If a type has count one, all positions of that type coincide. -/
lemma eq_of_count_one {n : ℕ} {C : Code n} {u v : Fin n} {i : ℕ}
    (hcnt : count C i = 1) (hu : colVal (C u) = i) (hv : colVal (C v) = i) : u = v := by
  have hcard : (Finset.univ.filter fun t : Fin n => colVal (C t) = i).card = 1 := by
    rw [count_eq_card C i] at hcnt
    exact hcnt
  have hmemu : u ∈ Finset.univ.filter fun t : Fin n => colVal (C t) = i := by simp [hu]
  have hmemv : v ∈ Finset.univ.filter fun t : Fin n => colVal (C t) = i := by simp [hv]
  rcases Finset.card_eq_one.mp hcard with ⟨x, hx⟩
  have hux : u = x := by
    have : u ∈ ({x} : Finset (Fin n)) := by simpa [hx] using hmemu
    simpa using this
  have hvx : v = x := by
    have : v ∈ ({x} : Finset (Fin n)) := by simpa [hx] using hmemv
    simpa using this
  exact hux.trans hvx.symm

/-- Three distinct positions covering `Fin 3` give the position permutation
`0 ↦ t1`, `1 ↦ t2`, `2 ↦ t0`. -/
lemma fin3_perm_of_cover {t0 t1 t2 : Fin 3}
    (hcover : ∀ u : Fin 3, u = t1 ∨ u = t2 ∨ u = t0)
    (h12 : t1 ≠ t2) (h01 : t1 ≠ t0) (h02 : t2 ≠ t0) :
    ∃ p : Equiv (Fin 3) (Fin 3), p 0 = t1 ∧ p 1 = t2 ∧ p 2 = t0 := by
  let f : Fin 3 → Fin 3 := fun u =>
    if u = t1 then (0 : Fin 3)
    else if u = t2 then (1 : Fin 3)
    else (2 : Fin 3)
  let g : Fin 3 → Fin 3 := fun u =>
    if u.val = 0 then t1
    else if u.val = 1 then t2
    else t0
  have hleft : Function.LeftInverse g f := by
    intro u
    by_cases h1 : u = t1
    · simp [f, g, h1]
    · by_cases h2 : u = t2
      · simp [f, g, h2, h12.symm]
      · have hu : u = t0 := by
          rcases hcover u with h | h | h
          · exact False.elim (h1 h)
          · exact False.elim (h2 h)
          · exact h
        simp [f, g, hu, h01.symm, h02.symm]
  have hright : Function.RightInverse g f := by
    intro u
    by_cases h0 : u.val = 0
    · have hu0 : u = (0 : Fin 3) := by
        apply Fin.ext
        exact h0
      simp [f, g, hu0]
    · by_cases h1 : u.val = 1
      · have hu1 : u = (1 : Fin 3) := by
          apply Fin.ext
          exact h1
        simp [f, g, hu1, h12.symm]
      · have hu2 : u.val = 2 := by omega
        have hu2' : u = (2 : Fin 3) := by
          apply Fin.ext
          exact hu2
        have hu0' : u ≠ (0 : Fin 3) := by
          intro h
          exact h0 (by simpa using congrArg Fin.val h)
        have hu1' : u ≠ (1 : Fin 3) := by
          intro h
          exact h1 (by simpa using congrArg Fin.val h)
        simp [f, g, hu2', h01.symm, h02.symm]
  let p : Fin 3 ≃ Fin 3 := ⟨g, f, hright, hleft⟩
  refine ⟨p, ?_, ?_, ?_⟩
  · change g 0 = t1
    simp [g]
  · change g 1 = t2
    simp [g]
  · change g 2 = t0
    simp [g]

-- native_decide: Mechanical · n=any · checked 2026-08-24
/-- Swapping rows 2 and 3 fixes `col3`. -/
lemma rowPermute_swap23_col3 :
    rowPermute (Equiv.swap (2 : Fin 4) (3 : Fin 4)) col3 = col3 := by
  native_decide

-- native_decide: Mechanical · n=any · checked 2026-08-24
/-- Swapping rows 2 and 3 maps `col5` to `col6`. -/
lemma rowPermute_swap23_col5 :
    rowPermute (Equiv.swap (2 : Fin 4) (3 : Fin 4)) col5 = col6 := by
  native_decide

-- native_decide: Mechanical · n=any · checked 2026-08-24
/-- The row 3-cycle (1 2 3) maps `col3` to `col5`. -/
lemma rowPermute_cycle_col3_col5 :
    rowPermute ((Equiv.swap (1 : Fin 4) (3 : Fin 4)).trans (Equiv.swap (1 : Fin 4) (2 : Fin 4))) col3 = col5 := by
  native_decide

-- native_decide: Mechanical · n=any · checked 2026-08-24
/-- The row 3-cycle (1 2 3) maps `col5` to `col6`. -/
lemma rowPermute_cycle_col5_col6 :
    rowPermute ((Equiv.swap (1 : Fin 4) (3 : Fin 4)).trans (Equiv.swap (1 : Fin 4) (2 : Fin 4))) col5 = col6 := by
  native_decide

/-- Sorted counts with spread ≤ 1 and sum 3k−1 are exactly (k,k,k−1). -/
lemma r2_base_counts {A B C k : ℕ} (hk : 1 ≤ k) (hord : C ≤ B ∧ B ≤ A)
    (hsum : A + B + C = k + k + (k - 1)) (hsp : A - C ≤ 1) :
    A = k ∧ B = k ∧ C = k - 1 := by
  have hABC : (A = C ∧ B = C) ∨ (A = C + 1 ∧ B = C) ∨ (A = C + 1 ∧ B = C + 1) := by
    have hA : A = C ∨ A = C + 1 := by omega
    rcases hA with hA0 | hA1
    · left
      constructor <;> omega
    · have hB : B = C ∨ B = C + 1 := by omega
      rcases hB with hB0 | hB1
      · exact Or.inr (Or.inl ⟨hA1, hB0⟩)
      · exact Or.inr (Or.inr ⟨hA1, hB1⟩)
  rcases hABC with hC | hC | hC
  · exfalso
    have : C + C + C = k + k + (k - 1) := by omega
    omega
  · exfalso
    have : C + C + C + 1 = k + k + (k - 1) := by omega
    omega
  · rcases hC with ⟨hA, hB⟩
    have hC' : C = k - 1 := by
      have : C + C + C + 2 = k + k + (k - 1) := by omega
      omega
    constructor
    · omega
    · constructor
      · omega
      · exact hC'

/-- `thm:linearopt` (Theorem 2) engine for n = 3k−1: the ideal C(k,k,k−1) strictly
dominates every non-equivalent linear code with only types 3, 5, 6 (strong
induction on the spread). -/
lemma linear_opt_r2_triple {k n : ℕ} (hk : 1 ≤ k) (hn : n = k + k + (k - 1)) :
    ∀ a b c : ℕ, ∀ hsum : a + b + c = n,
      ¬ Equivalent (linCode k k (k - 1) (by omega)) (linCode a b c hsum) →
        UniversalStrictBetter (linCode k k (k - 1) (by omega)) (linCode a b c hsum) := by
  let I : Code n := linCode k k (k - 1) (by omega)
  have hmain : ∀ s : ℕ, ∀ a b c : ℕ, ∀ hsum : a + b + c = n,
      max a (max b c) - min a (min b c) = s →
        ¬ Equivalent I (linCode a b c hsum) → UniversalStrictBetter I (linCode a b c hsum) := by
    intro s
    induction s using Nat.strong_induction_on with
    | h s ih =>
      intro a b c hsum hspread hne
      rcases linCode_sorted_equiv hsum with ⟨A, B, C, hsumABC, hord, hEqABC, hEq, hspEq⟩
      have hspABC : max A (max B C) - min A (min B C) = s := by
        rw [hspEq]
        exact hspread
      have hAC : A - C = s := by
        have hCA : C ≤ A := by omega
        have hred : max A (max B C) - min A (min B C) = A - C := by
          simp [hord, hEqABC, hCA]
        rw [← hred]
        exact hspABC
      by_cases hbase : A - C ≤ 1
      · -- base: (A,B,C) = (k,k,k−1), equivalent to the ideal
        exfalso
        have hcnts : A = k ∧ B = k ∧ C = k - 1 := r2_base_counts hk ⟨hord, hEqABC⟩ (by omega) hbase
        rcases hcnts with ⟨hA, hB, hC⟩
        subst A
        subst B
        subst C
        have hEqI : Equivalent (linCode k k (k - 1) hsumABC) I := by
          simpa [I] using (equivalent_refl (linCode k k (k - 1) hsumABC))
        have hEq : Equivalent I (linCode a b c hsum) :=
          equivalent_trans (equivalent_symm hEqI) (equivalent_symm hEq)
        exact hne hEq
      · -- descent: strictly better code with smaller spread
        have hsp2 : 2 ≤ A - C := by omega
        rcases linear_descent_step_r2 hk hn ⟨hord, hEqABC⟩ hsumABC hsp2 with ⟨a', c', hsum', hspdec, hbetter⟩
        have hsp' : max a' (max B c') - min a' (min B c') < s := by omega
        have hIH := ih (max a' (max B c') - min a' (min B c')) hsp' a' B c' hsum' rfl
        have hIgtDs : UniversalStrictBetter I (linCode A B C hsumABC) := by
          by_cases hEq' : Equivalent I (linCode a' B c' hsum')
          · exact universalStrictBetter_of_equiv_left (equivalent_symm hEq') hbetter
          · exact universalStrictBetter_trans (hIH hEq') hbetter
        exact universalStrictBetter_of_eq_left hIgtDs
          (universalEqual_of_equivalent (linCode a b c hsum) (linCode A B C hsumABC) hEq)
  intro a b c hsum hne
  have hm := hmain (max a (max b c) - min a (min b c)) a b c hsum rfl hne
  simpa [I] using hm

/-- The canonical code with counts (a,b,c) is linear when a,b > 0. -/
lemma isLinear_linearCode {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) :
    IsLinear (linearCode a b c) := by
  constructor
  · intro t
    by_cases h1 : t.val < a <;> by_cases h2 : t.val < a + b <;>
      simp [linearCode, h1, h2, colVal_col3, colVal_col5, colVal_col6]
  · left
    constructor
    · simpa [linear_count_3] using ha
    · simpa [linear_count_5] using hb

/-- `linCode` (the cast form) is linear when the first two counts are
positive. -/
lemma isLinear_linCode {n a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hsum : a + b + c = n) :
    IsLinear (linCode a b c hsum) := by
  cases hsum
  simpa [linCode] using (isLinear_linearCode ha hb)

/-- `linCode` count of type 3. -/
lemma count_linCode_3 {n a b c : ℕ} (hsum : a + b + c = n) :
    count (linCode a b c hsum) 3 = a := by
  cases hsum
  simpa [linCode] using (linear_count_3 (n3 := a) (n5 := b) (n6 := c))

/-- `linCode` count of type 5. -/
lemma count_linCode_5 {n a b c : ℕ} (hsum : a + b + c = n) :
    count (linCode a b c hsum) 5 = b := by
  cases hsum
  simpa [linCode] using (linear_count_5 (n3 := a) (n5 := b) (n6 := c))

/-- `linCode` count of type 6. -/
lemma count_linCode_6 {n a b c : ℕ} (hsum : a + b + c = n) :
    count (linCode a b c hsum) 6 = c := by
  cases hsum
  simpa [linCode] using (linear_count_6 (n3 := a) (n5 := b) (n6 := c))

/-- Replacing a zero column keeps counts of types other than 0 and
`colVal s'` unchanged. -/
-- native_decide: Mechanical · n=any · checked 2026-08-24
lemma count_replace_0_eq {n : ℕ} (C : Code n) (t : Fin n) (s' : Column) (h0 : C t = col0)
    {i : ℕ} (hi0 : i ≠ 0) (his : i ≠ colVal s') : count (replaceColumn C t s') i = count C i := by
  rw [count_eq_card (replaceColumn C t s') i, count_eq_card C i]
  have hset : (Finset.univ.filter fun u : Fin n => colVal ((replaceColumn C t s') u) = i) =
      (Finset.univ.filter fun u : Fin n => colVal (C u) = i) := by
    ext u
    by_cases hu : u = t
    · subst u
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hl : ¬ colVal s' = i := fun h => his h.symm
      have hr : ¬ colVal col0 = i := by
        intro h
        have hcv : colVal col0 = 0 := by native_decide
        exact hi0 (by omega)
      rw [show replaceColumn C t s' t = if t = t then s' else C t by rfl, if_pos rfl, h0]
      constructor
      · intro h
        exfalso
        exact hl h
      · intro h
        exfalso
        exact hr h
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [show replaceColumn C t s' u = if u = t then s' else C u by rfl, if_neg hu]
  rw [hset]

/-- Replacing a zero column by `s'` increases the count of type `colVal s'`
by one. -/
-- native_decide: Mechanical · n=any · checked 2026-08-24
lemma count_replace_0_self {n : ℕ} (C : Code n) (t : Fin n) (s' : Column) (h0 : C t = col0)
    (hs : colVal s' ≠ 0) : count (replaceColumn C t s') (colVal s') = count C (colVal s') + 1 := by
  rw [count_eq_card (replaceColumn C t s') (colVal s'), count_eq_card C (colVal s')]
  have hset : (Finset.univ.filter fun u : Fin n => colVal ((replaceColumn C t s') u) = colVal s') =
      insert t (Finset.univ.filter fun u : Fin n => colVal (C u) = colVal s') := by
    ext u
    by_cases hu : u = t
    · subst u
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [show replaceColumn C t s' t = if t = t then s' else C t by rfl, if_pos rfl]
      simp [Finset.mem_insert]
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [show replaceColumn C t s' u = if u = t then s' else C u by rfl, if_neg hu]
      simp [Finset.mem_insert, hu]
  rw [hset]
  rw [Finset.card_insert_of_notMem (by
    intro ht
    have hc : colVal (C t) = colVal s' := (Finset.mem_filter.mp ht).2
    have hcv : colVal (C t) = 0 := by
      rw [h0]
      native_decide
    omega)]

/-- Replacing a zero column does not decrease the count of any nonzero type. -/
lemma count_replace_0_ge {n : ℕ} (C : Code n) (t : Fin n) (h0 : C t = col0) (s' : Column)
    (i : ℕ) (hi : i ≠ 0) (hpos : 0 < count C i) : 0 < count (replaceColumn C t s') i := by
  by_cases his : i = colVal s'
  · have hc : count (replaceColumn C t s') (colVal s') = count C (colVal s') + 1 :=
      count_replace_0_self C t s' h0 (by
        intro h
        exact hi (by rw [his, h]))
    rw [his, hc]
    omega
  · have hc : count (replaceColumn C t s') i = count C i := count_replace_0_eq C t s' h0 hi his
    rw [hc]
    exact hpos

/-- Replacing a zero column of a linear code by a type-3/5/6 column keeps the
code linear. -/
lemma isLinear_replace_0 {n : ℕ} (C : Code n) (hlin : IsLinear C) (t : Fin n) (h0 : C t = col0)
    (s' : Column) (hs' : colVal s' = 3 ∨ colVal s' = 5 ∨ colVal s' = 6) :
    IsLinear (replaceColumn C t s') := by
  constructor
  · intro u
    by_cases hu : u = t
    · subst u
      simp [replaceColumn, hs']
    · simp [replaceColumn, hu]
      exact hlin.1 u
  · rcases hlin.2 with h35 | h36 | h56
    · left
      constructor
      · exact count_replace_0_ge C t h0 s' 3 (by omega) h35.1
      · exact count_replace_0_ge C t h0 s' 5 (by omega) h35.2
    · right; left
      constructor
      · exact count_replace_0_ge C t h0 s' 3 (by omega) h36.1
      · exact count_replace_0_ge C t h0 s' 6 (by omega) h36.2
    · right; right
      constructor
      · exact count_replace_0_ge C t h0 s' 5 (by omega) h56.1
      · exact count_replace_0_ge C t h0 s' 6 (by omega) h56.2

def col356 (i : ℕ) : Column := if i = 3 then col3 else if i = 5 then col5 else col6

-- native_decide: Mechanical · n=any · checked 2026-08-24
/-- `colVal (col356 i) = i` for i ∈ {3,5,6}. -/
lemma col356_val (i : ℕ) (hi : i = 3 ∨ i = 5 ∨ i = 6) : colVal (col356 i) = i := by
  rcases hi with h3 | h5 | h6
  · subst i; native_decide
  · subst i; native_decide
  · subst i; native_decide

/-- The image type of a type-`i` column under a row permutation and an
optional flip. -/
def actType (ρ : Equiv (Fin 4) (Fin 4)) (b : Bool) (i : ℕ) : ℕ :=
  colVal (rowPermute ρ (if b then flipCol (col356 i) else col356 i))

/-- `col356 i` is a two-bit column. -/
lemma col356_pair (i : ℕ) (hi : i = 3 ∨ i = 5 ∨ i = 6) :
    ∃ a b : Fin 4, a ≠ b ∧ (col356 i = fun j : Fin 4 => j = a ∨ j = b) := by
  rcases hi with h3 | h5 | h6
  · subst i; refine ⟨2, 3, by decide, ?_⟩
    funext j
    fin_cases j <;> simp [col356, col3]
  · subst i; refine ⟨1, 3, by decide, ?_⟩
    funext j
    fin_cases j <;> simp [col356, col5]
  · subst i; refine ⟨1, 2, by decide, ?_⟩
    funext j
    fin_cases j <;> simp [col356, col6]

/-- The flip of `col356 i` is a two-bit column. -/
lemma flip_col356_pair (i : ℕ) (hi : i = 3 ∨ i = 5 ∨ i = 6) :
    ∃ a b : Fin 4, a ≠ b ∧ (flipCol (col356 i) = fun j : Fin 4 => j = a ∨ j = b) := by
  rcases hi with h3 | h5 | h6
  · subst i; refine ⟨0, 1, by decide, ?_⟩
    funext j
    fin_cases j <;> simp [col356, col3, flipCol]
  · subst i; refine ⟨0, 2, by decide, ?_⟩
    funext j
    fin_cases j <;> simp [col356, col5, flipCol]
  · subst i; refine ⟨0, 3, by decide, ?_⟩
    funext j
    fin_cases j <;> simp [col356, col6, flipCol]

/-- A type-3/5/6 column has its row-1 bit (index 0) false. -/
lemma row0_false_of_colVal_356 {c : Column} (h : colVal c = 3 ∨ colVal c = 5 ∨ colVal c = 6) :
    c 0 = false := by
  rcases h with h3 | h5 | h6
  · simpa [col3] using congrFun ((colVal_eq_three_iff_col3 c).mp h3) 0
  · simpa [col5] using congrFun ((colVal_eq_five_iff_col5 c).mp h5) 0
  · simpa [col6] using congrFun ((colVal_eq_six_iff_col6 c).mp h6) 0

/-- The image of a two-bit column under a row permutation and a flip still
has exactly two ones, so it is never type 0. -/
lemma two_bit_image_not_zero (ρ : Equiv (Fin 4) (Fin 4)) (b : Bool) (i : ℕ)
    (hi : i = 3 ∨ i = 5 ∨ i = 6) : actType ρ b i ≠ 0 := by
  intro h
  have hsrc : ∃ p q : Fin 4, p ≠ q ∧
      ((if b then flipCol (col356 i) else col356 i) = fun j : Fin 4 => j = p ∨ j = q) := by
    by_cases hb : b = true
    · rcases (flip_col356_pair i hi) with ⟨p, q, hpq, hc⟩
      refine ⟨p, q, hpq, ?_⟩
      simpa [hb] using hc
    · rcases (col356_pair i hi) with ⟨p, q, hpq, hc⟩
      refine ⟨p, q, hpq, ?_⟩
      simpa [hb] using hc
  rcases hsrc with ⟨p, q, hpq, hc⟩
  have h2 : ∃ p' q' : Fin 4, p' ≠ q' ∧
      (rowPermute ρ (if b then flipCol (col356 i) else col356 i) = fun j : Fin 4 => j = p' ∨ j = q') := by
    refine ⟨ρ.symm p, ρ.symm q, ?_, ?_⟩
    · intro h'
      exact hpq (ρ.symm.injective h')
    · funext j
      have hv1 : ρ j = p ↔ j = ρ.symm p := (Equiv.eq_symm_apply ρ (x := p) (y := j)).symm
      have hv2 : ρ j = q ↔ j = ρ.symm q := (Equiv.eq_symm_apply ρ (x := q) (y := j)).symm
      simp [rowPermute, hc, hv1, hv2]
  have hcv := colVal_two_bit (rowPermute ρ (if b then flipCol (col356 i) else col356 i)) h2
  unfold actType at h
  rcases hcv with h3 | h5 | h6 | h9 | h10 | h12 <;> omega

/-- A flipped and an unflipped image of the same column cannot both be linear
types (their row-1 bits contradict). -/
lemma flip_unflip_contradiction {ρ : Equiv (Fin 4) (Fin 4)} {c : Column}
    (h1 : colVal (rowPermute ρ c) = 3 ∨ colVal (rowPermute ρ c) = 5 ∨
      colVal (rowPermute ρ c) = 6)
    (h2 : colVal (rowPermute ρ (flipCol c)) = 3 ∨ colVal (rowPermute ρ (flipCol c)) = 5 ∨
      colVal (rowPermute ρ (flipCol c)) = 6) : False := by
  have hb1 : (rowPermute ρ c) 0 = false := row0_false_of_colVal_356 h1
  have hb2 : (rowPermute ρ (flipCol c)) 0 = false := row0_false_of_colVal_356 h2
  have hc1 : c (ρ 0) = false := by simpa [rowPermute] using hb1
  have hc2 : c (ρ 0) = true := by
    have hnot : !(c (ρ 0)) = false := by simpa [rowPermute, flipCol] using hb2
    cases h : c (ρ 0) <;> simp [h] at hnot ⊢
  by_cases hc : c (ρ 0) = true
  · rw [hc] at hc1
    simp at hc1
  · have hcf : c (ρ 0) = false := by
      cases h : c (ρ 0) <;> simp [h] at hc ⊢
    rw [hcf] at hc2
    simp at hc2

/-- `flipCol` is injective. -/
lemma flipCol_injective : Function.Injective flipCol := by
  intro c c' h
  have h' := congrArg flipCol h
  simpa [flipCol_involutive] using h'

/-- A zero-value column is `col0`. -/
lemma col0_of_colVal_zero {c : Column} (h : colVal c = 0) : c = col0 :=
  (colVal_eq_zero_iff_col0 c).mp h

/-- A position with positive type count. -/
lemma exists_type_of_count_pos {n : ℕ} {C : Code n} {i : ℕ} (h : 0 < count C i) :
    ∃ t : Fin n, colVal (C t) = i := by
  rcases Finset.card_pos.mp (by rw [← count_eq_card C i]; exact h) with ⟨t, ht⟩
  exact ⟨t, (Finset.mem_filter.mp ht).2⟩

/-- The image of a type-3/5/6 column under the equivalence action is a
type-3/5/6 column. -/
lemma image_type_in_356 {n : ℕ} {C C' : Code n} (_hC : IsLinear C) (hC' : IsLinear C')
    {ρ : Equiv (Fin 4) (Fin 4)} {p : Equiv (Fin n) (Fin n)} {f : Fin n → Bool}
    (hh : ∀ t : Fin n, C' (p t) = rowPermute ρ (if f t then flipCol (C t) else C t))
    (t : Fin n) (hi : colVal (C t) = 3 ∨ colVal (C t) = 5 ∨ colVal (C t) = 6) :
    colVal (rowPermute ρ (if f t then flipCol (C t) else C t)) = 3 ∨
      colVal (rowPermute ρ (if f t then flipCol (C t) else C t)) = 5 ∨
      colVal (rowPermute ρ (if f t then flipCol (C t) else C t)) = 6 := by
  have hcv := hC'.1 (p t)
  have heq : colVal (C' (p t)) = colVal (rowPermute ρ (if f t then flipCol (C t) else C t)) := by
    rw [hh t]
  rcases hcv with h0 | h3 | h5 | h6
  · exfalso
    have hcv' : colVal (rowPermute ρ (if f t then flipCol (C t) else C t)) = 0 := by
      rwa [heq] at h0
    rcases hi with h3 | h5 | h6
    · have hc : C t = col356 3 := by
        simpa [col356] using (colVal_eq_three_iff_col3 (C t)).mp h3
      have hnb : actType ρ (f t) 3 ≠ 0 := two_bit_image_not_zero ρ (f t) 3 (Or.inl rfl)
      exact hnb (by simpa [actType, hc] using hcv')
    · have hc : C t = col356 5 := by
        simpa [col356] using (colVal_eq_five_iff_col5 (C t)).mp h5
      have hnb : actType ρ (f t) 5 ≠ 0 := two_bit_image_not_zero ρ (f t) 5 (Or.inr (Or.inl rfl))
      exact hnb (by simpa [actType, hc] using hcv')
    · have hc : C t = col356 6 := by
        simpa [col356] using (colVal_eq_six_iff_col6 (C t)).mp h6
      have hnb : actType ρ (f t) 6 ≠ 0 := two_bit_image_not_zero ρ (f t) 6 (Or.inr (Or.inr rfl))
      exact hnb (by simpa [actType, hc] using hcv')
  · exact Or.inl (by simpa [heq] using h3)
  · exact Or.inr (Or.inl (by simpa [heq] using h5))
  · exact Or.inr (Or.inr (by simpa [heq] using h6))

/-- The flip pattern is constant on each column type 3, 5, 6. -/
lemma flip_uniform {n : ℕ} {C C' : Code n} (hC : IsLinear C) (hC' : IsLinear C')
    {ρ : Equiv (Fin 4) (Fin 4)} {p : Equiv (Fin n) (Fin n)} {f : Fin n → Bool}
    (hh : ∀ t : Fin n, C' (p t) = rowPermute ρ (if f t then flipCol (C t) else C t))
    {i : ℕ} (hi : i = 3 ∨ i = 5 ∨ i = 6)
    {t₁ t₂ : Fin n} (ht1 : colVal (C t₁) = i) (ht2 : colVal (C t₂) = i) :
    f t₁ = f t₂ := by
  by_cases h1 : f t₁ = true
  · by_cases h2 : f t₂ = true
    · exact h1.trans h2.symm
    · exfalso
      have h2' : f t₂ = false := by
        by_cases hb : f t₂ = true
        · exfalso
          exact h2 hb
        · cases h : f t₂ <;> simp [h] at hb ⊢
      -- t₁ is flipped, t₂ is not; both images are linear types
      have himg1 : colVal (rowPermute ρ (flipCol (C t₁))) = 3 ∨
          colVal (rowPermute ρ (flipCol (C t₁))) = 5 ∨
          colVal (rowPermute ρ (flipCol (C t₁))) = 6 := by
        have h' : colVal (rowPermute ρ (if f t₁ then flipCol (C t₁) else C t₁)) = 3 ∨
            colVal (rowPermute ρ (if f t₁ then flipCol (C t₁) else C t₁)) = 5 ∨
            colVal (rowPermute ρ (if f t₁ then flipCol (C t₁) else C t₁)) = 6 :=
          image_type_in_356 hC hC' hh t₁ (by
            rcases hi with h3 | h5 | h6
            · exact Or.inl (by simpa [h3] using ht1)
            · exact Or.inr (Or.inl (by simpa [h5] using ht1))
            · exact Or.inr (Or.inr (by simpa [h6] using ht1)))
        simpa [h1] using h'
      have himg2 : colVal (rowPermute ρ (C t₂)) = 3 ∨
          colVal (rowPermute ρ (C t₂)) = 5 ∨
          colVal (rowPermute ρ (C t₂)) = 6 := by
        have h' : colVal (rowPermute ρ (if f t₂ then flipCol (C t₂) else C t₂)) = 3 ∨
            colVal (rowPermute ρ (if f t₂ then flipCol (C t₂) else C t₂)) = 5 ∨
            colVal (rowPermute ρ (if f t₂ then flipCol (C t₂) else C t₂)) = 6 :=
          image_type_in_356 hC hC' hh t₂ (by
            rcases hi with h3 | h5 | h6
            · exact Or.inl (by simpa [h3] using ht2)
            · exact Or.inr (Or.inl (by simpa [h5] using ht2))
            · exact Or.inr (Or.inr (by simpa [h6] using ht2)))
        simpa [h2'] using h'
      -- the two columns have the same type, hence are equal
      have hc : C t₁ = C t₂ := by
        rcases hi with h3 | h5 | h6
        · have h1' : C t₁ = col3 := (colVal_eq_three_iff_col3 (C t₁)).mp (by simpa [h3] using ht1)
          have h2' : C t₂ = col3 := (colVal_eq_three_iff_col3 (C t₂)).mp (by simpa [h3] using ht2)
          exact h1'.trans h2'.symm
        · have h1' : C t₁ = col5 := (colVal_eq_five_iff_col5 (C t₁)).mp (by simpa [h5] using ht1)
          have h2' : C t₂ = col5 := (colVal_eq_five_iff_col5 (C t₂)).mp (by simpa [h5] using ht2)
          exact h1'.trans h2'.symm
        · have h1' : C t₁ = col6 := (colVal_eq_six_iff_col6 (C t₁)).mp (by simpa [h6] using ht1)
          have h2' : C t₂ = col6 := (colVal_eq_six_iff_col6 (C t₂)).mp (by simpa [h6] using ht2)
          exact h1'.trans h2'.symm
      exact flip_unflip_contradiction (c := C t₂) (by simpa [hc] using himg2)
        (by simpa [hc] using himg1)
  · have h1' : f t₁ = false := by
      by_cases hb : f t₁ = true
      · exfalso
        exact h1 hb
      · cases h : f t₁ <;> simp [h] at hb ⊢
    by_cases h2 : f t₂ = true
    · exfalso
      -- t₂ flipped, t₁ not
      have himg1 : colVal (rowPermute ρ (C t₁)) = 3 ∨
          colVal (rowPermute ρ (C t₁)) = 5 ∨
          colVal (rowPermute ρ (C t₁)) = 6 := by
        have h' : colVal (rowPermute ρ (if f t₁ then flipCol (C t₁) else C t₁)) = 3 ∨
            colVal (rowPermute ρ (if f t₁ then flipCol (C t₁) else C t₁)) = 5 ∨
            colVal (rowPermute ρ (if f t₁ then flipCol (C t₁) else C t₁)) = 6 :=
          image_type_in_356 hC hC' hh t₁ (by
            rcases hi with h3 | h5 | h6
            · exact Or.inl (by simpa [h3] using ht1)
            · exact Or.inr (Or.inl (by simpa [h5] using ht1))
            · exact Or.inr (Or.inr (by simpa [h6] using ht1)))
        simpa [h1'] using h'
      have himg2 : colVal (rowPermute ρ (flipCol (C t₂))) = 3 ∨
          colVal (rowPermute ρ (flipCol (C t₂))) = 5 ∨
          colVal (rowPermute ρ (flipCol (C t₂))) = 6 := by
        have h' : colVal (rowPermute ρ (if f t₂ then flipCol (C t₂) else C t₂)) = 3 ∨
            colVal (rowPermute ρ (if f t₂ then flipCol (C t₂) else C t₂)) = 5 ∨
            colVal (rowPermute ρ (if f t₂ then flipCol (C t₂) else C t₂)) = 6 :=
          image_type_in_356 hC hC' hh t₂ (by
            rcases hi with h3 | h5 | h6
            · exact Or.inl (by simpa [h3] using ht2)
            · exact Or.inr (Or.inl (by simpa [h5] using ht2))
            · exact Or.inr (Or.inr (by simpa [h6] using ht2)))
        simpa [h2] using h'
      have hc : C t₁ = C t₂ := by
        rcases hi with h3 | h5 | h6
        · have h1' : C t₁ = col3 := (colVal_eq_three_iff_col3 (C t₁)).mp (by simpa [h3] using ht1)
          have h2' : C t₂ = col3 := (colVal_eq_three_iff_col3 (C t₂)).mp (by simpa [h3] using ht2)
          exact h1'.trans h2'.symm
        · have h1' : C t₁ = col5 := (colVal_eq_five_iff_col5 (C t₁)).mp (by simpa [h5] using ht1)
          have h2' : C t₂ = col5 := (colVal_eq_five_iff_col5 (C t₂)).mp (by simpa [h5] using ht2)
          exact h1'.trans h2'.symm
        · have h1' : C t₁ = col6 := (colVal_eq_six_iff_col6 (C t₁)).mp (by simpa [h6] using ht1)
          have h2' : C t₂ = col6 := (colVal_eq_six_iff_col6 (C t₂)).mp (by simpa [h6] using ht2)
          exact h1'.trans h2'.symm
      exact flip_unflip_contradiction (c := C t₁) (by simpa [hc] using himg1)
        (by simpa [hc] using himg2)
    · have h2' : f t₂ = false := by
        by_cases hb : f t₂ = true
        · exfalso
          exact h2 hb
        · cases h : f t₂ <;> simp [h] at hb ⊢
      exact h1'.trans h2'.symm

/-- The count of type `i` is at most the count of its image type. -/
lemma count_le_image {n : ℕ} {C C' : Code n} (hC : IsLinear C) (hC' : IsLinear C')
    {ρ : Equiv (Fin 4) (Fin 4)} {p : Equiv (Fin n) (Fin n)} {f : Fin n → Bool}
    (hh : ∀ t : Fin n, C' (p t) = rowPermute ρ (if f t then flipCol (C t) else C t))
    {i : ℕ} (hi : i = 3 ∨ i = 5 ∨ i = 6) (ti : Fin n) (hti : colVal (C ti) = i) :
    count C i ≤ count C' (actType ρ (f ti) i) := by
  rw [count_eq_card C i, count_eq_card C' (actType ρ (f ti) i)]
  have hsub : (Finset.univ.filter fun t : Fin n => colVal (C t) = i).image p ⊆
      Finset.univ.filter fun u : Fin n => colVal (C' u) = actType ρ (f ti) i := by
    intro u hu
    rcases Finset.mem_image.mp hu with ⟨t, ht, rfl⟩
    have hcv : colVal (C t) = i := (Finset.mem_filter.mp ht).2
    have hc : C t = col356 i := by
      rcases hi with h3 | h5 | h6
      · rw [h3]
        exact (colVal_eq_three_iff_col3 (C t)).mp (by simpa [h3] using hcv)
      · rw [h5]
        exact (colVal_eq_five_iff_col5 (C t)).mp (by simpa [h5] using hcv)
      · rw [h6]
        exact (colVal_eq_six_iff_col6 (C t)).mp (by simpa [h6] using hcv)
    have hf : f t = f ti := flip_uniform hC hC' hh hi hcv hti
    have heq : colVal (C' (p t)) = actType ρ (f ti) i := by
      rw [hh t]
      rw [actType, hf, hc]
    exact Finset.mem_filter.mpr ⟨by simp, heq⟩
  calc
    (Finset.univ.filter fun t : Fin n => colVal (C t) = i).card =
        ((Finset.univ.filter fun t : Fin n => colVal (C t) = i).image p).card := by
      exact (Finset.card_image_of_injective _ p.injective).symm
    _ ≤ (Finset.univ.filter fun u : Fin n => colVal (C' u) = actType ρ (f ti) i).card :=
      Finset.card_le_card hsub

/-- The image types of distinct positive types are distinct. -/
lemma sigma_inj_on_pos {n : ℕ} {C C' : Code n} (hC : IsLinear C) (hC' : IsLinear C')
    {ρ : Equiv (Fin 4) (Fin 4)} {p : Equiv (Fin n) (Fin n)} {f : Fin n → Bool}
    (hh : ∀ t : Fin n, C' (p t) = rowPermute ρ (if f t then flipCol (C t) else C t))
    {i j : ℕ} (hi : i = 3 ∨ i = 5 ∨ i = 6) (hj : j = 3 ∨ j = 5 ∨ j = 6)
    (ti tj : Fin n) (hti : colVal (C ti) = i) (htj : colVal (C tj) = j)
    (hne : i ≠ j) : actType ρ (f ti) i ≠ actType ρ (f tj) j := by
  intro h
  have hcti : C ti = col356 i := by
    rcases hi with h3 | h5 | h6
    · rw [h3]
      exact (colVal_eq_three_iff_col3 (C ti)).mp (by simpa [h3] using hti)
    · rw [h5]
      exact (colVal_eq_five_iff_col5 (C ti)).mp (by simpa [h5] using hti)
    · rw [h6]
      exact (colVal_eq_six_iff_col6 (C ti)).mp (by simpa [h6] using hti)
  have hctj : C tj = col356 j := by
    rcases hj with h3 | h5 | h6
    · rw [h3]
      exact (colVal_eq_three_iff_col3 (C tj)).mp (by simpa [h3] using htj)
    · rw [h5]
      exact (colVal_eq_five_iff_col5 (C tj)).mp (by simpa [h5] using htj)
    · rw [h6]
      exact (colVal_eq_six_iff_col6 (C tj)).mp (by simpa [h6] using htj)
  have hcv : colVal (rowPermute ρ (if f ti then flipCol (C ti) else C ti)) =
      colVal (rowPermute ρ (if f tj then flipCol (C tj) else C tj)) := by
    simpa [actType, hcti, hctj] using h
  have h3i : colVal (rowPermute ρ (if f ti then flipCol (C ti) else C ti)) = 3 ∨
      colVal (rowPermute ρ (if f ti then flipCol (C ti) else C ti)) = 5 ∨
      colVal (rowPermute ρ (if f ti then flipCol (C ti) else C ti)) = 6 :=
    image_type_in_356 hC hC' hh ti (by
      rcases hi with h3 | h5 | h6
      · exact Or.inl (by simpa [h3] using hti)
      · exact Or.inr (Or.inl (by simpa [h5] using hti))
      · exact Or.inr (Or.inr (by simpa [h6] using hti)))
  have h3j : colVal (rowPermute ρ (if f tj then flipCol (C tj) else C tj)) = 3 ∨
      colVal (rowPermute ρ (if f tj then flipCol (C tj) else C tj)) = 5 ∨
      colVal (rowPermute ρ (if f tj then flipCol (C tj) else C tj)) = 6 :=
    image_type_in_356 hC hC' hh tj (by
      rcases hj with h3 | h5 | h6
      · exact Or.inl (by simpa [h3] using htj)
      · exact Or.inr (Or.inl (by simpa [h5] using htj))
      · exact Or.inr (Or.inr (by simpa [h6] using htj)))
  have hcol : (if f ti then flipCol (C ti) else C ti) =
      (if f tj then flipCol (C tj) else C tj) := by
    have heq : rowPermute ρ (if f ti then flipCol (C ti) else C ti) =
        rowPermute ρ (if f tj then flipCol (C tj) else C tj) := by
      -- equal colVal of two linear-type columns → equal columns
      rcases h3i with h3i' | h5i' | h6i'
      · have h1 : rowPermute ρ (if f ti then flipCol (C ti) else C ti) = col3 :=
          (colVal_eq_three_iff_col3 _).mp h3i'
        have h2 : rowPermute ρ (if f tj then flipCol (C tj) else C tj) = col3 := by
          rcases h3j with h3j' | h5j' | h6j'
          · exact (colVal_eq_three_iff_col3 _).mp h3j'
          · exfalso; omega
          · exfalso; omega
        exact h1.trans h2.symm
      · have h1 : rowPermute ρ (if f ti then flipCol (C ti) else C ti) = col5 :=
          (colVal_eq_five_iff_col5 _).mp h5i'
        have h2 : rowPermute ρ (if f tj then flipCol (C tj) else C tj) = col5 := by
          rcases h3j with h3j' | h5j' | h6j'
          · exfalso; omega
          · exact (colVal_eq_five_iff_col5 _).mp h5j'
          · exfalso; omega
        exact h1.trans h2.symm
      · have h1 : rowPermute ρ (if f ti then flipCol (C ti) else C ti) = col6 :=
          (colVal_eq_six_iff_col6 _).mp h6i'
        have h2 : rowPermute ρ (if f tj then flipCol (C tj) else C tj) = col6 := by
          rcases h3j with h3j' | h5j' | h6j'
          · exfalso; omega
          · exfalso; omega
          · exact (colVal_eq_six_iff_col6 _).mp h6j'
        exact h1.trans h2.symm
    -- rowPermute is injective
    calc
      (if f ti then flipCol (C ti) else C ti)
          = rowPermute ρ.symm (rowPermute ρ (if f ti then flipCol (C ti) else C ti)) := by
            simpa using (rowPermute_symm ρ.symm _).symm
      _ = rowPermute ρ.symm (rowPermute ρ (if f tj then flipCol (C tj) else C tj)) := by
            rw [heq]
      _ = (if f tj then flipCol (C tj) else C tj) := by
            simpa using (rowPermute_symm ρ.symm _)
  -- the sources are equal; both C ti, C tj are two-bit columns of types i, j
  by_cases hf : f ti = f tj
  · -- same flip: C ti = C tj → colVal i = j
    have hc : C ti = C tj := by
      have h' : flipCol (C ti) = flipCol (C tj) ∨ C ti = C tj := by
        by_cases hb : f ti = true
        · have : f tj = true := by simpa [hf] using hb
          left
          simpa [hb, this] using hcol
        · have : f tj = false := by
            have hb' : f ti = false := by
              by_cases hb0 : f ti = true
              · exfalso
                exact hb hb0
              · cases h : f ti <;> simp [h] at hb0 ⊢
            simpa [hf, hb'] using hb'
          right
          simpa [hb, this] using hcol
      rcases h' with hflip | hid
      · -- flipCol (C ti) = flipCol (C tj) → C ti = C tj
        exact flipCol_injective hflip
      · exact hid
    have hcv' : colVal (C ti) = colVal (C tj) := congrArg colVal hc
    omega
  · -- different flips: one flipped, the other not — row-0 contradiction
    by_cases hb1 : f ti = true
    · have hb2' : f tj = false := by
        by_cases hb2 : f tj = true
        · exfalso
          exact hf (hb1.trans hb2.symm)
        · cases h : f tj <;> simp [h] at hb2 ⊢
      -- flipCol (C ti) = C tj (from hcol)
      have hc : flipCol (C ti) = C tj := by
        simpa [hb1, hb2'] using hcol
      have hbit : (flipCol (C ti)) 0 = true := by
        have hb : C ti 0 = false := row0_false_of_colVal_356 (by
          rcases hi with h3 | h5 | h6
          · exact Or.inl (by simpa [h3] using hti)
          · exact Or.inr (Or.inl (by simpa [h5] using hti))
          · exact Or.inr (Or.inr (by simpa [h6] using hti)))
        simp [flipCol, hb]
      have hb0 : C tj 0 = false := row0_false_of_colVal_356 (by
        rcases hj with h3 | h5 | h6
        · exact Or.inl (by simpa [h3] using htj)
        · exact Or.inr (Or.inl (by simpa [h5] using htj))
        · exact Or.inr (Or.inr (by simpa [h6] using htj)))
      rw [hc, hb0] at hbit
      simp at hbit
    · have hb1' : f ti = false := by
        by_cases hb0 : f ti = true
        · exfalso
          exact hb1 hb0
        · cases h : f ti <;> simp [h] at hb0 ⊢
      by_cases hb2 : f tj = true
      · -- C ti = flipCol (C tj) — row-0 contradiction
        have hc : C ti = flipCol (C tj) := by
          simpa [hb1', hb2] using hcol
        have hbit : (flipCol (C tj)) 0 = true := by
          have hb : C tj 0 = false := row0_false_of_colVal_356 (by
            rcases hj with h3 | h5 | h6
            · exact Or.inl (by simpa [h3] using htj)
            · exact Or.inr (Or.inl (by simpa [h5] using htj))
            · exact Or.inr (Or.inr (by simpa [h6] using htj)))
          simp [flipCol, hb]
        have hb0 : C ti 0 = false := row0_false_of_colVal_356 (by
          rcases hi with h3 | h5 | h6
          · exact Or.inl (by simpa [h3] using hti)
          · exact Or.inr (Or.inl (by simpa [h5] using hti))
          · exact Or.inr (Or.inr (by simpa [h6] using hti)))
        rw [← hc, hb0] at hbit
        simp at hbit
      · exfalso
        have hb2' : f tj = false := by
          by_cases hb3 : f tj = true
          · exfalso
            exact hb2 hb3
          · cases h : f tj <;> simp [h] at hb3 ⊢
        exact hf (hb1'.trans hb2'.symm)

/-- In a linear code, the counts of types 3, 5, 6 sum to `n − |0|`. -/
lemma linear_sum_counts {n : ℕ} {C : Code n} (hC : IsLinear C) :
    count C 3 + count C 5 + count C 6 = n - count C 0 := by
  have hzeros : ∀ i : ℕ, i ∉ ({0, 3, 5, 6} : Finset ℕ) → count C i = 0 := by
    intro i hi
    by_contra hc
    have hpos : 0 < count C i := Nat.pos_of_ne_zero hc
    rcases Finset.card_pos.mp (by rw [← count_eq_card C i]; exact hpos) with ⟨t, ht⟩
    have hci : colVal (C t) = i := (Finset.mem_filter.mp ht).2
    rcases hC.1 t with h0 | h3 | h5 | h6
    · simp [Finset.mem_insert, Finset.mem_singleton] at hi; omega
    · simp [Finset.mem_insert, Finset.mem_singleton] at hi; omega
    · simp [Finset.mem_insert, Finset.mem_singleton] at hi; omega
    · simp [Finset.mem_insert, Finset.mem_singleton] at hi; omega
  have hsumAll := sum_counts_eq_n C
  have hS : ({0, 3, 5, 6} : Finset ℕ) ⊆ Finset.Icc 0 15 := by
    intro x hx
    simp at hx ⊢
    omega
  have hcomp : (∑ i ∈ Finset.Icc 0 15 \ ({0, 3, 5, 6} : Finset ℕ), count C i) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    exact hzeros i (Finset.mem_sdiff.mp hi).2
  have hsplit : (∑ i ∈ Finset.Icc 0 15, count C i) =
      (∑ i ∈ ({0, 3, 5, 6} : Finset ℕ), count C i) +
        ∑ i ∈ Finset.Icc 0 15 \ ({0, 3, 5, 6} : Finset ℕ), count C i := by
    rw [← Finset.sum_sdiff hS]
    rw [add_comm]
  have hsum' : (∑ i ∈ ({0, 3, 5, 6} : Finset ℕ), count C i) =
      count C 0 + (count C 3 + (count C 5 + count C 6)) := by
    simp [Finset.sum_insert]
  omega

-- native_decide: Mechanical · n=any · checked 2026-08-24
/-- The number of zero columns does not decrease along an equivalence. -/
lemma count0_le {n : ℕ} {C C' : Code n} (_hC : IsLinear C) (hC' : IsLinear C')
    {ρ : Equiv (Fin 4) (Fin 4)} {p : Equiv (Fin n) (Fin n)} {f : Fin n → Bool}
    (hh : ∀ t : Fin n, C' (p t) = rowPermute ρ (if f t then flipCol (C t) else C t)) :
    count C 0 ≤ count C' 0 := by
  rw [count_eq_card C 0, count_eq_card C' 0]
  have hsub : (Finset.univ.filter fun t : Fin n => colVal (C t) = 0).image p ⊆
      Finset.univ.filter fun u : Fin n => colVal (C' u) = 0 := by
    intro u hu
    rcases Finset.mem_image.mp hu with ⟨t, ht, rfl⟩
    have hcv : colVal (C t) = 0 := (Finset.mem_filter.mp ht).2
    have hc0 : C t = col0 := col0_of_colVal_zero hcv
    have hf : f t = false := by
      by_cases hb : f t = true
      · exfalso
        have hcv' := hC'.1 (p t)
        have hc : C' (p t) = rowPermute ρ (flipCol col0) := by
          simp [hh t, hb, hc0]
        have hcv15 : colVal (rowPermute ρ (flipCol col0)) = 15 := by
          have hf0 : flipCol col0 = col15 := by funext k; simp [flipCol, col0, col15]
          rw [hf0]
          have hr : rowPermute ρ col15 = col15 := by funext k; simp [rowPermute, col15]
          rw [hr]
          native_decide
        rw [hc] at hcv'
        rcases hcv' with h0 | h3 | h5 | h6 <;> omega
      · by_cases hb0 : f t = true
        · exfalso
          exact hb hb0
        · cases h : f t <;> simp [h] at hb0 ⊢
    have heq : colVal (C' (p t)) = 0 := by
      simp [hh t, hf, hc0]
      have hf0 : rowPermute ρ col0 = col0 := rowPermute_col0 ρ
      rw [hf0]
      native_decide
    exact Finset.mem_filter.mpr ⟨by simp, heq⟩
  calc
    (Finset.univ.filter fun t : Fin n => colVal (C t) = 0).card =
        ((Finset.univ.filter fun t : Fin n => colVal (C t) = 0).image p).card := by
      exact (Finset.card_image_of_injective _ p.injective).symm
    _ ≤ (Finset.univ.filter fun u : Fin n => colVal (C' u) = 0).card :=
      Finset.card_le_card hsub

/-- Equivalence between linear codes preserves the number of zero columns. -/
lemma count0_equiv {n : ℕ} {C C' : Code n} (hC : IsLinear C) (hC' : IsLinear C')
    (h : Equivalent C C') : count C 0 = count C' 0 := by
  have hsym := equivalent_symm h
  rcases h with ⟨ρ, p, f, hh⟩
  have hle : count C 0 ≤ count C' 0 := count0_le hC hC' hh
  rcases hsym with ⟨ρ', p', f', hh'⟩
  have hle' : count C' 0 ≤ count C 0 := count0_le hC' hC hh'
  exact le_antisymm hle hle'

/-- Three distinct values in {3,5,6} are a permutation of (3,5,6). -/
lemma perm3_cases {s3 s5 s6 : ℕ} (h3 : s3 = 3 ∨ s3 = 5 ∨ s3 = 6)
    (h5 : s5 = 3 ∨ s5 = 5 ∨ s5 = 6) (h6 : s6 = 3 ∨ s6 = 5 ∨ s6 = 6)
    (h35 : s3 ≠ s5) (h36 : s3 ≠ s6) (h56 : s5 ≠ s6) :
    (s3 = 3 ∧ s5 = 5 ∧ s6 = 6) ∨ (s3 = 3 ∧ s5 = 6 ∧ s6 = 5) ∨
    (s3 = 5 ∧ s5 = 3 ∧ s6 = 6) ∨ (s3 = 5 ∧ s5 = 6 ∧ s6 = 3) ∨
    (s3 = 6 ∧ s5 = 3 ∧ s6 = 5) ∨ (s3 = 6 ∧ s5 = 5 ∧ s6 = 3) := by
  have h3lo : 3 ≤ s3 := by rcases h3 with h3 | h3 | h3 <;> omega
  have h3hi : s3 ≤ 6 := by rcases h3 with h3 | h3 | h3 <;> omega
  have h5lo : 3 ≤ s5 := by rcases h5 with h5 | h5 | h5 <;> omega
  have h5hi : s5 ≤ 6 := by rcases h5 with h5 | h5 | h5 <;> omega
  have h6lo : 3 ≤ s6 := by rcases h6 with h6 | h6 | h6 <;> omega
  have h6hi : s6 ≤ 6 := by rcases h6 with h6 | h6 | h6 <;> omega
  interval_cases s3 <;> interval_cases s5 <;> interval_cases s6 <;> omega

/-- Two distinct values in {3,5,6}. -/
lemma pair3_cases {s5 s6 : ℕ} (h5 : s5 = 3 ∨ s5 = 5 ∨ s5 = 6)
    (h6 : s6 = 3 ∨ s6 = 5 ∨ s6 = 6) (h56 : s5 ≠ s6) :
    (s5 = 3 ∧ s6 = 5) ∨ (s5 = 3 ∧ s6 = 6) ∨ (s5 = 5 ∧ s6 = 3) ∨
    (s5 = 5 ∧ s6 = 6) ∨ (s5 = 6 ∧ s6 = 3) ∨ (s5 = 6 ∧ s6 = 5) := by
  have h5lo : 3 ≤ s5 := by rcases h5 with h5 | h5 | h5 <;> omega
  have h5hi : s5 ≤ 6 := by rcases h5 with h5 | h5 | h5 <;> omega
  have h6lo : 3 ≤ s6 := by rcases h6 with h6 | h6 | h6 <;> omega
  have h6hi : s6 ≤ 6 := by rcases h6 with h6 | h6 | h6 <;> omega
  interval_cases s5 <;> interval_cases s6 <;> omega

/-- `thm:linearopt` (Theorem 2) C0-case engine: equivalence between linear codes preserves
the counts of types 3, 5, 6 up to a permutation of the three types.  (The
equivalence map is a row permutation `ρ` with per-column flips; linearity of
both codes forces the flip pattern to be constant on each type and the induced
action on the two-bit columns {3,5,6} is a permutation.) -/
lemma count_356_perm_equiv {n : ℕ} {C C' : Code n} (hC : IsLinear C) (hC' : IsLinear C')
    (h : Equivalent C C') :
    (count C 3, count C 5, count C 6) = (count C' 3, count C' 5, count C' 6) ∨
      (count C 3, count C 5, count C 6) = (count C' 5, count C' 3, count C' 6) ∨
      (count C 3, count C 5, count C 6) = (count C' 6, count C' 5, count C' 3) ∨
      (count C 3, count C 5, count C 6) = (count C' 5, count C' 6, count C' 3) ∨
      (count C 3, count C 5, count C 6) = (count C' 6, count C' 3, count C' 5) ∨
      (count C 3, count C 5, count C 6) = (count C' 3, count C' 6, count C' 5) := by
  have hcnt0 : count C 0 = count C' 0 := count0_equiv hC hC' h
  rcases h with ⟨ρ, p, f, hh⟩
  have hTot : count C 3 + count C 5 + count C 6 = count C' 3 + count C' 5 + count C' 6 := by
    rw [linear_sum_counts hC, linear_sum_counts hC', hcnt0]
  by_cases h3 : 0 < count C 3
  · by_cases h5 : 0 < count C 5
    · by_cases h6 : 0 < count C 6
      · -- all three types positive: σ is a permutation of {3,5,6}
        let t3 := Classical.choose (exists_type_of_count_pos h3)
        let t5 := Classical.choose (exists_type_of_count_pos h5)
        let t6 := Classical.choose (exists_type_of_count_pos h6)
        have ht3 : colVal (C t3) = 3 := Classical.choose_spec (exists_type_of_count_pos h3)
        have ht5 : colVal (C t5) = 5 := Classical.choose_spec (exists_type_of_count_pos h5)
        have ht6 : colVal (C t6) = 6 := Classical.choose_spec (exists_type_of_count_pos h6)
        let s3 := actType ρ (f t3) 3
        let s5 := actType ρ (f t5) 5
        let s6 := actType ρ (f t6) 6
        have hct3 : C t3 = col356 3 := (colVal_eq_three_iff_col3 (C t3)).mp ht3
        have hs3 : s3 = 3 ∨ s3 = 5 ∨ s3 = 6 := by
          have h' : colVal (rowPermute ρ (if f t3 then flipCol (C t3) else C t3)) = 3 ∨
              colVal (rowPermute ρ (if f t3 then flipCol (C t3) else C t3)) = 5 ∨
              colVal (rowPermute ρ (if f t3 then flipCol (C t3) else C t3)) = 6 :=
            image_type_in_356 hC hC' hh t3 (Or.inl ht3)
          simpa [s3, actType, hct3] using h'
        have hct5 : C t5 = col356 5 := (colVal_eq_five_iff_col5 (C t5)).mp ht5
        have hs5 : s5 = 3 ∨ s5 = 5 ∨ s5 = 6 := by
          have h' : colVal (rowPermute ρ (if f t5 then flipCol (C t5) else C t5)) = 3 ∨
              colVal (rowPermute ρ (if f t5 then flipCol (C t5) else C t5)) = 5 ∨
              colVal (rowPermute ρ (if f t5 then flipCol (C t5) else C t5)) = 6 :=
            image_type_in_356 hC hC' hh t5 (Or.inr (Or.inl ht5))
          simpa [s5, actType, hct5] using h'
        have hct6 : C t6 = col356 6 := (colVal_eq_six_iff_col6 (C t6)).mp ht6
        have hs6 : s6 = 3 ∨ s6 = 5 ∨ s6 = 6 := by
          have h' : colVal (rowPermute ρ (if f t6 then flipCol (C t6) else C t6)) = 3 ∨
              colVal (rowPermute ρ (if f t6 then flipCol (C t6) else C t6)) = 5 ∨
              colVal (rowPermute ρ (if f t6 then flipCol (C t6) else C t6)) = 6 :=
            image_type_in_356 hC hC' hh t6 (Or.inr (Or.inr ht6))
          simpa [s6, actType, hct6] using h'
        have hd35 : s3 ≠ s5 := sigma_inj_on_pos hC hC' hh (Or.inl rfl) (Or.inr (Or.inl rfl)) t3 t5 ht3 ht5 (by omega)
        have hd36 : s3 ≠ s6 := sigma_inj_on_pos hC hC' hh (Or.inl rfl) (Or.inr (Or.inr rfl)) t3 t6 ht3 ht6 (by omega)
        have hd56 : s5 ≠ s6 := sigma_inj_on_pos hC hC' hh (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl)) t5 t6 ht5 ht6 (by omega)
        have hle3 : count C 3 ≤ count C' s3 := by
          simpa [s3] using (count_le_image hC hC' hh (Or.inl rfl) t3 ht3)
        have hle5 : count C 5 ≤ count C' s5 := by
          simpa [s5] using (count_le_image hC hC' hh (Or.inr (Or.inl rfl)) t5 ht5)
        have hle6 : count C 6 ≤ count C' s6 := by
          simpa [s6] using (count_le_image hC hC' hh (Or.inr (Or.inr rfl)) t6 ht6)
        rcases perm3_cases hs3 hs5 hs6 hd35 hd36 hd56 with hperm | hperm | hperm | hperm | hperm | hperm
        · rcases hperm with ⟨hs3', hs5', hs6'⟩
          have hsumTot : count C' s3 + count C' s5 + count C' s6 = count C' 3 + count C' 5 + count C' 6 := by

            rw [hs3', hs5', hs6']

            try omega

          have hsumEq : count C 3 + count C 5 + count C 6 = count C' s3 + count C' s5 + count C' s6 := by
            omega
          have hEq3 : count C 3 = count C' s3 := by omega
          have hEq5 : count C 5 = count C' s5 := by omega
          have hEq6 : count C 6 = count C' s6 := by omega
          rw [hs3'] at hEq3
          rw [hs5'] at hEq5
          rw [hs6'] at hEq6
          left
          rw [hEq3, hEq5, hEq6]
        · rcases hperm with ⟨hs3', hs5', hs6'⟩
          have hsumTot : count C' s3 + count C' s5 + count C' s6 = count C' 3 + count C' 5 + count C' 6 := by

            rw [hs3', hs5', hs6']

            try omega

          have hsumEq : count C 3 + count C 5 + count C 6 = count C' s3 + count C' s5 + count C' s6 := by
            omega
          have hEq3 : count C 3 = count C' s3 := by omega
          have hEq5 : count C 5 = count C' s5 := by omega
          have hEq6 : count C 6 = count C' s6 := by omega
          rw [hs3'] at hEq3
          rw [hs5'] at hEq5
          rw [hs6'] at hEq6
          right; right; right; right; right
          rw [hEq3, hEq5, hEq6]
        · rcases hperm with ⟨hs3', hs5', hs6'⟩
          have hsumTot : count C' s3 + count C' s5 + count C' s6 = count C' 3 + count C' 5 + count C' 6 := by

            rw [hs3', hs5', hs6']

            try omega

          have hsumEq : count C 3 + count C 5 + count C 6 = count C' s3 + count C' s5 + count C' s6 := by
            omega
          have hEq3 : count C 3 = count C' s3 := by omega
          have hEq5 : count C 5 = count C' s5 := by omega
          have hEq6 : count C 6 = count C' s6 := by omega
          rw [hs3'] at hEq3
          rw [hs5'] at hEq5
          rw [hs6'] at hEq6
          right; left
          rw [hEq3, hEq5, hEq6]
        · rcases hperm with ⟨hs3', hs5', hs6'⟩
          have hsumTot : count C' s3 + count C' s5 + count C' s6 = count C' 3 + count C' 5 + count C' 6 := by

            rw [hs3', hs5', hs6']

            try omega

          have hsumEq : count C 3 + count C 5 + count C 6 = count C' s3 + count C' s5 + count C' s6 := by
            omega
          have hEq3 : count C 3 = count C' s3 := by omega
          have hEq5 : count C 5 = count C' s5 := by omega
          have hEq6 : count C 6 = count C' s6 := by omega
          rw [hs3'] at hEq3
          rw [hs5'] at hEq5
          rw [hs6'] at hEq6
          right; right; right; left
          rw [hEq3, hEq5, hEq6]
        · rcases hperm with ⟨hs3', hs5', hs6'⟩
          have hsumTot : count C' s3 + count C' s5 + count C' s6 = count C' 3 + count C' 5 + count C' 6 := by

            rw [hs3', hs5', hs6']

            try omega

          have hsumEq : count C 3 + count C 5 + count C 6 = count C' s3 + count C' s5 + count C' s6 := by
            omega
          have hEq3 : count C 3 = count C' s3 := by omega
          have hEq5 : count C 5 = count C' s5 := by omega
          have hEq6 : count C 6 = count C' s6 := by omega
          rw [hs3'] at hEq3
          rw [hs5'] at hEq5
          rw [hs6'] at hEq6
          right; right; right; right; left
          rw [hEq3, hEq5, hEq6]
        · rcases hperm with ⟨hs3', hs5', hs6'⟩
          have hsumTot : count C' s3 + count C' s5 + count C' s6 = count C' 3 + count C' 5 + count C' 6 := by

            rw [hs3', hs5', hs6']

            try omega

          have hsumEq : count C 3 + count C 5 + count C 6 = count C' s3 + count C' s5 + count C' s6 := by
            omega
          have hEq3 : count C 3 = count C' s3 := by omega
          have hEq5 : count C 5 = count C' s5 := by omega
          have hEq6 : count C 6 = count C' s6 := by omega
          rw [hs3'] at hEq3
          rw [hs5'] at hEq5
          rw [hs6'] at hEq6
          right; right; left
          rw [hEq3, hEq5, hEq6]
      · -- a, b > 0, c = 0
        let t3 := Classical.choose (exists_type_of_count_pos h3)
        let t5 := Classical.choose (exists_type_of_count_pos h5)
        have ht3 : colVal (C t3) = 3 := Classical.choose_spec (exists_type_of_count_pos h3)
        have ht5 : colVal (C t5) = 5 := Classical.choose_spec (exists_type_of_count_pos h5)
        let s3 := actType ρ (f t3) 3
        let s5 := actType ρ (f t5) 5
        have hct3 : C t3 = col356 3 := (colVal_eq_three_iff_col3 (C t3)).mp ht3
        have hs3 : s3 = 3 ∨ s3 = 5 ∨ s3 = 6 := by
          have h' : colVal (rowPermute ρ (if f t3 then flipCol (C t3) else C t3)) = 3 ∨
              colVal (rowPermute ρ (if f t3 then flipCol (C t3) else C t3)) = 5 ∨
              colVal (rowPermute ρ (if f t3 then flipCol (C t3) else C t3)) = 6 :=
            image_type_in_356 hC hC' hh t3 (Or.inl ht3)
          simpa [s3, actType, hct3] using h'
        have hct5 : C t5 = col356 5 := (colVal_eq_five_iff_col5 (C t5)).mp ht5
        have hs5 : s5 = 3 ∨ s5 = 5 ∨ s5 = 6 := by
          have h' : colVal (rowPermute ρ (if f t5 then flipCol (C t5) else C t5)) = 3 ∨
              colVal (rowPermute ρ (if f t5 then flipCol (C t5) else C t5)) = 5 ∨
              colVal (rowPermute ρ (if f t5 then flipCol (C t5) else C t5)) = 6 :=
            image_type_in_356 hC hC' hh t5 (Or.inr (Or.inl ht5))
          simpa [s5, actType, hct5] using h'
        have hd35 : s3 ≠ s5 := sigma_inj_on_pos hC hC' hh (Or.inl rfl) (Or.inr (Or.inl rfl)) t3 t5 ht3 ht5 (by omega)
        have hle3 : count C 3 ≤ count C' s3 := by
          simpa [s3] using (count_le_image hC hC' hh (Or.inl rfl) t3 ht3)
        have hle5 : count C 5 ≤ count C' s5 := by
          simpa [s5] using (count_le_image hC hC' hh (Or.inr (Or.inl rfl)) t5 ht5)
        have hc0 : count C 6 = 0 := by omega
        rcases pair3_cases hs3 hs5 hd35 with hp | hp | hp | hp | hp | hp
        · rcases hp with ⟨hs3', hs5'⟩
          have hle3' : count C 3 ≤ count C' 3 := by simpa [hs3'] using hle3
          have hle5' : count C 5 ≤ count C' 5 := by simpa [hs5'] using hle5
          have hsum : count C' 3 + count C' 5 + count C' 6 = count C 3 + count C 5 := by omega
          have he6 : count C' 6 = 0 := by omega
          have hEq3 : count C 3 = count C' 3 := by omega
          have hEq5 : count C 5 = count C' 5 := by omega
          left
          rw [hEq3, hEq5, he6, hc0]
        · rcases hp with ⟨hs3', hs5'⟩
          have hle3' : count C 3 ≤ count C' 3 := by simpa [hs3'] using hle3
          have hle5' : count C 5 ≤ count C' 6 := by simpa [hs5'] using hle5
          have hsum : count C' 3 + count C' 5 + count C' 6 = count C 3 + count C 5 := by omega
          have he5 : count C' 5 = 0 := by omega
          have hEq3 : count C 3 = count C' 3 := by omega
          have hEq5 : count C 5 = count C' 6 := by omega
          right; right; right; right; right
          rw [hEq3, hEq5, he5, hc0]
        · rcases hp with ⟨hs3', hs5'⟩
          have hle3' : count C 3 ≤ count C' 5 := by simpa [hs3'] using hle3
          have hle5' : count C 5 ≤ count C' 3 := by simpa [hs5'] using hle5
          have hsum : count C' 3 + count C' 5 + count C' 6 = count C 3 + count C 5 := by omega
          have he6 : count C' 6 = 0 := by omega
          have hEq3 : count C 3 = count C' 5 := by omega
          have hEq5 : count C 5 = count C' 3 := by omega
          right; left
          rw [hEq3, hEq5, he6, hc0]
        · rcases hp with ⟨hs3', hs5'⟩
          have hle3' : count C 3 ≤ count C' 5 := by simpa [hs3'] using hle3
          have hle5' : count C 5 ≤ count C' 6 := by simpa [hs5'] using hle5
          have hsum : count C' 3 + count C' 5 + count C' 6 = count C 3 + count C 5 := by omega
          have hd0 : count C' 3 = 0 := by omega
          have hEq3 : count C 3 = count C' 5 := by omega
          have hEq5 : count C 5 = count C' 6 := by omega
          right; right; right; left
          rw [hEq3, hEq5, hd0, hc0]
        · rcases hp with ⟨hs3', hs5'⟩
          have hle3' : count C 3 ≤ count C' 6 := by simpa [hs3'] using hle3
          have hle5' : count C 5 ≤ count C' 3 := by simpa [hs5'] using hle5
          have hsum : count C' 3 + count C' 5 + count C' 6 = count C 3 + count C 5 := by omega
          have he5 : count C' 5 = 0 := by omega
          have hEq3 : count C 3 = count C' 6 := by omega
          have hEq5 : count C 5 = count C' 3 := by omega
          right; right; right; right; left
          rw [hEq3, hEq5, he5, hc0]
        · rcases hp with ⟨hs3', hs5'⟩
          have hle3' : count C 3 ≤ count C' 6 := by simpa [hs3'] using hle3
          have hle5' : count C 5 ≤ count C' 5 := by simpa [hs5'] using hle5
          have hsum : count C' 3 + count C' 5 + count C' 6 = count C 3 + count C 5 := by omega
          have hd0 : count C' 3 = 0 := by omega
          have hEq3 : count C 3 = count C' 6 := by omega
          have hEq5 : count C 5 = count C' 5 := by omega
          right; right; left
          rw [hEq3, hEq5, hd0, hc0]
    · by_cases h6 : 0 < count C 6
      · -- a, c > 0, b = 0
        let t3 := Classical.choose (exists_type_of_count_pos h3)
        let t6 := Classical.choose (exists_type_of_count_pos h6)
        have ht3 : colVal (C t3) = 3 := Classical.choose_spec (exists_type_of_count_pos h3)
        have ht6 : colVal (C t6) = 6 := Classical.choose_spec (exists_type_of_count_pos h6)
        let s3 := actType ρ (f t3) 3
        let s6 := actType ρ (f t6) 6
        have hct3 : C t3 = col356 3 := (colVal_eq_three_iff_col3 (C t3)).mp ht3
        have hct6 : C t6 = col356 6 := (colVal_eq_six_iff_col6 (C t6)).mp ht6
        have hs3 : s3 = 3 ∨ s3 = 5 ∨ s3 = 6 := by
          have h' : colVal (rowPermute ρ (if f t3 then flipCol (C t3) else C t3)) = 3 ∨
              colVal (rowPermute ρ (if f t3 then flipCol (C t3) else C t3)) = 5 ∨
              colVal (rowPermute ρ (if f t3 then flipCol (C t3) else C t3)) = 6 :=
            image_type_in_356 hC hC' hh t3 (Or.inl ht3)
          simpa [s3, actType, hct3] using h'
        have hs6 : s6 = 3 ∨ s6 = 5 ∨ s6 = 6 := by
          have h' : colVal (rowPermute ρ (if f t6 then flipCol (C t6) else C t6)) = 3 ∨
              colVal (rowPermute ρ (if f t6 then flipCol (C t6) else C t6)) = 5 ∨
              colVal (rowPermute ρ (if f t6 then flipCol (C t6) else C t6)) = 6 :=
            image_type_in_356 hC hC' hh t6 (Or.inr (Or.inr ht6))
          simpa [s6, actType, hct6] using h'
        have hd36 : s3 ≠ s6 := sigma_inj_on_pos hC hC' hh (Or.inl rfl) (Or.inr (Or.inr rfl)) t3 t6 ht3 ht6 (by omega)
        have hle3 : count C 3 ≤ count C' s3 := by
          simpa [s3] using (count_le_image hC hC' hh (Or.inl rfl) t3 ht3)
        have hle6 : count C 6 ≤ count C' s6 := by
          simpa [s6] using (count_le_image hC hC' hh (Or.inr (Or.inr rfl)) t6 ht6)
        have hb0 : count C 5 = 0 := by omega
        rcases pair3_cases hs3 hs6 hd36 with hp | hp | hp | hp | hp | hp
        · rcases hp with ⟨hs3', hs6'⟩
          have hle3' : count C 3 ≤ count C' 3 := by simpa [hs3'] using hle3
          have hle6' : count C 6 ≤ count C' 5 := by simpa [hs6'] using hle6
          have hsum : count C' 3 + count C' 5 + count C' 6 = count C 3 + count C 6 := by omega
          have he6 : count C' 6 = 0 := by omega
          have hEq3 : count C 3 = count C' 3 := by omega
          have hEq6 : count C 6 = count C' 5 := by omega
          right; right; right; right; right
          rw [hEq3, hb0, hEq6, he6]
        · rcases hp with ⟨hs3', hs6'⟩
          have hle3' : count C 3 ≤ count C' 3 := by simpa [hs3'] using hle3
          have hle6' : count C 6 ≤ count C' 6 := by simpa [hs6'] using hle6
          have hsum : count C' 3 + count C' 5 + count C' 6 = count C 3 + count C 6 := by omega
          have he5 : count C' 5 = 0 := by omega
          have hEq3 : count C 3 = count C' 3 := by omega
          have hEq6 : count C 6 = count C' 6 := by omega
          left
          rw [hEq3, hb0, hEq6, he5]
        · rcases hp with ⟨hs3', hs6'⟩
          have hle3' : count C 3 ≤ count C' 5 := by simpa [hs3'] using hle3
          have hle6' : count C 6 ≤ count C' 3 := by simpa [hs6'] using hle6
          have hsum : count C' 3 + count C' 5 + count C' 6 = count C 3 + count C 6 := by omega
          have he6 : count C' 6 = 0 := by omega
          have hEq3 : count C 3 = count C' 5 := by omega
          have hEq6 : count C 6 = count C' 3 := by omega
          right; right; right; left
          rw [hEq3, hb0, hEq6, he6]
        · rcases hp with ⟨hs3', hs6'⟩
          have hle3' : count C 3 ≤ count C' 5 := by simpa [hs3'] using hle3
          have hle6' : count C 6 ≤ count C' 6 := by simpa [hs6'] using hle6
          have hsum : count C' 3 + count C' 5 + count C' 6 = count C 3 + count C 6 := by omega
          have hd0 : count C' 3 = 0 := by omega
          have hEq3 : count C 3 = count C' 5 := by omega
          have hEq6 : count C 6 = count C' 6 := by omega
          right; left
          rw [hEq3, hb0, hEq6, hd0]
        · rcases hp with ⟨hs3', hs6'⟩
          have hle3' : count C 3 ≤ count C' 6 := by simpa [hs3'] using hle3
          have hle6' : count C 6 ≤ count C' 3 := by simpa [hs6'] using hle6
          have hsum : count C' 3 + count C' 5 + count C' 6 = count C 3 + count C 6 := by omega
          have he5 : count C' 5 = 0 := by omega
          have hEq3 : count C 3 = count C' 6 := by omega
          have hEq6 : count C 6 = count C' 3 := by omega
          right; right; left
          rw [hEq3, hb0, hEq6, he5]
        · rcases hp with ⟨hs3', hs6'⟩
          have hle3' : count C 3 ≤ count C' 6 := by simpa [hs3'] using hle3
          have hle6' : count C 6 ≤ count C' 5 := by simpa [hs6'] using hle6
          have hsum : count C' 3 + count C' 5 + count C' 6 = count C 3 + count C 6 := by omega
          have hd0 : count C' 3 = 0 := by omega
          have hEq3 : count C 3 = count C' 6 := by omega
          have hEq6 : count C 6 = count C' 5 := by omega
          right; right; right; right; left
          rw [hEq3, hb0, hEq6, hd0]
      · -- a > 0 only
        let t3 := Classical.choose (exists_type_of_count_pos h3)
        have ht3 : colVal (C t3) = 3 := Classical.choose_spec (exists_type_of_count_pos h3)
        let s3 := actType ρ (f t3) 3
        have hct3 : C t3 = col356 3 := (colVal_eq_three_iff_col3 (C t3)).mp ht3
        have hs3 : s3 = 3 ∨ s3 = 5 ∨ s3 = 6 := by
          have h' : colVal (rowPermute ρ (if f t3 then flipCol (C t3) else C t3)) = 3 ∨
              colVal (rowPermute ρ (if f t3 then flipCol (C t3) else C t3)) = 5 ∨
              colVal (rowPermute ρ (if f t3 then flipCol (C t3) else C t3)) = 6 :=
            image_type_in_356 hC hC' hh t3 (Or.inl ht3)
          simpa [s3, actType, hct3] using h'
        have hle3 : count C 3 ≤ count C' s3 := by
          simpa [s3] using (count_le_image hC hC' hh (Or.inl rfl) t3 ht3)
        have hb0 : count C 5 = 0 := by omega
        have hc0 : count C 6 = 0 := by omega
        rcases hs3 with hs3' | hs3' | hs3'
        · have hle3' : count C 3 ≤ count C' 3 := by simpa [hs3'] using hle3
          have hsum : count C' 3 + count C' 5 + count C' 6 = count C 3 := by omega
          have he5 : count C' 5 = 0 := by omega
          have he6 : count C' 6 = 0 := by omega
          have hEq3 : count C 3 = count C' 3 := by omega
          left
          rw [hEq3, hb0, hc0, he5, he6]
        · have hle3' : count C 3 ≤ count C' 5 := by simpa [hs3'] using hle3
          have hsum : count C' 3 + count C' 5 + count C' 6 = count C 3 := by omega
          have hd0 : count C' 3 = 0 := by omega
          have hf0 : count C' 6 = 0 := by omega
          have hEq3 : count C 3 = count C' 5 := by omega
          right; left
          rw [hEq3, hb0, hc0, hd0, hf0]
        · have hle3' : count C 3 ≤ count C' 6 := by simpa [hs3'] using hle3
          have hsum : count C' 3 + count C' 5 + count C' 6 = count C 3 := by omega
          have hd0 : count C' 3 = 0 := by omega
          have he0 : count C' 5 = 0 := by omega
          have hEq3 : count C 3 = count C' 6 := by omega
          right; right; left
          rw [hEq3, hb0, hc0, hd0, he0]
  · by_cases h5 : 0 < count C 5
    · by_cases h6 : 0 < count C 6
      · -- b, c > 0, a = 0
        let t5 := Classical.choose (exists_type_of_count_pos h5)
        let t6 := Classical.choose (exists_type_of_count_pos h6)
        have ht5 : colVal (C t5) = 5 := Classical.choose_spec (exists_type_of_count_pos h5)
        have ht6 : colVal (C t6) = 6 := Classical.choose_spec (exists_type_of_count_pos h6)
        let s5 := actType ρ (f t5) 5
        let s6 := actType ρ (f t6) 6
        have hct5 : C t5 = col356 5 := (colVal_eq_five_iff_col5 (C t5)).mp ht5
        have hct6 : C t6 = col356 6 := (colVal_eq_six_iff_col6 (C t6)).mp ht6
        have hs5 : s5 = 3 ∨ s5 = 5 ∨ s5 = 6 := by
          have h' : colVal (rowPermute ρ (if f t5 then flipCol (C t5) else C t5)) = 3 ∨
              colVal (rowPermute ρ (if f t5 then flipCol (C t5) else C t5)) = 5 ∨
              colVal (rowPermute ρ (if f t5 then flipCol (C t5) else C t5)) = 6 :=
            image_type_in_356 hC hC' hh t5 (Or.inr (Or.inl ht5))
          simpa [s5, actType, hct5] using h'
        have hs6 : s6 = 3 ∨ s6 = 5 ∨ s6 = 6 := by
          have h' : colVal (rowPermute ρ (if f t6 then flipCol (C t6) else C t6)) = 3 ∨
              colVal (rowPermute ρ (if f t6 then flipCol (C t6) else C t6)) = 5 ∨
              colVal (rowPermute ρ (if f t6 then flipCol (C t6) else C t6)) = 6 :=
            image_type_in_356 hC hC' hh t6 (Or.inr (Or.inr ht6))
          simpa [s6, actType, hct6] using h'
        have hd56 : s5 ≠ s6 := sigma_inj_on_pos hC hC' hh (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl)) t5 t6 ht5 ht6 (by omega)
        have hle5 : count C 5 ≤ count C' s5 := by
          simpa [s5] using (count_le_image hC hC' hh (Or.inr (Or.inl rfl)) t5 ht5)
        have hle6 : count C 6 ≤ count C' s6 := by
          simpa [s6] using (count_le_image hC hC' hh (Or.inr (Or.inr rfl)) t6 ht6)
        have ha0 : count C 3 = 0 := by omega
        rcases pair3_cases hs5 hs6 hd56 with hp | hp | hp | hp | hp | hp
        · rcases hp with ⟨hs5', hs6'⟩
          have hle5' : count C 5 ≤ count C' 3 := by simpa [hs5'] using hle5
          have hle6' : count C 6 ≤ count C' 5 := by simpa [hs6'] using hle6
          have hsum : count C' 3 + count C' 5 + count C' 6 = count C 5 + count C 6 := by omega
          have he6 : count C' 6 = 0 := by omega
          have hEq5 : count C 5 = count C' 3 := by omega
          have hEq6 : count C 6 = count C' 5 := by omega
          right; right; right; right; left
          rw [ha0, hEq5, hEq6, he6]
        · rcases hp with ⟨hs5', hs6'⟩
          have hle5' : count C 5 ≤ count C' 3 := by simpa [hs5'] using hle5
          have hle6' : count C 6 ≤ count C' 6 := by simpa [hs6'] using hle6
          have hsum : count C' 3 + count C' 5 + count C' 6 = count C 5 + count C 6 := by omega
          have he5 : count C' 5 = 0 := by omega
          have hEq5 : count C 5 = count C' 3 := by omega
          have hEq6 : count C 6 = count C' 6 := by omega
          right; left
          rw [ha0, hEq5, hEq6, he5]
        · rcases hp with ⟨hs5', hs6'⟩
          have hle5' : count C 5 ≤ count C' 5 := by simpa [hs5'] using hle5
          have hle6' : count C 6 ≤ count C' 3 := by simpa [hs6'] using hle6
          have hsum : count C' 3 + count C' 5 + count C' 6 = count C 5 + count C 6 := by omega
          have he6 : count C' 6 = 0 := by omega
          have hEq5 : count C 5 = count C' 5 := by omega
          have hEq6 : count C 6 = count C' 3 := by omega
          right; right; left
          rw [ha0, hEq5, hEq6, he6]
        · rcases hp with ⟨hs5', hs6'⟩
          have hle5' : count C 5 ≤ count C' 5 := by simpa [hs5'] using hle5
          have hle6' : count C 6 ≤ count C' 6 := by simpa [hs6'] using hle6
          have hsum : count C' 3 + count C' 5 + count C' 6 = count C 5 + count C 6 := by omega
          have hd0 : count C' 3 = 0 := by omega
          have hEq5 : count C 5 = count C' 5 := by omega
          have hEq6 : count C 6 = count C' 6 := by omega
          left
          rw [ha0, hEq5, hEq6, hd0]
        · rcases hp with ⟨hs5', hs6'⟩
          have hle5' : count C 5 ≤ count C' 6 := by simpa [hs5'] using hle5
          have hle6' : count C 6 ≤ count C' 3 := by simpa [hs6'] using hle6
          have hsum : count C' 3 + count C' 5 + count C' 6 = count C 5 + count C 6 := by omega
          have he5 : count C' 5 = 0 := by omega
          have hEq5 : count C 5 = count C' 6 := by omega
          have hEq6 : count C 6 = count C' 3 := by omega
          right; right; right; left
          rw [ha0, hEq5, hEq6, he5]
        · rcases hp with ⟨hs5', hs6'⟩
          have hle5' : count C 5 ≤ count C' 6 := by simpa [hs5'] using hle5
          have hle6' : count C 6 ≤ count C' 5 := by simpa [hs6'] using hle6
          have hsum : count C' 3 + count C' 5 + count C' 6 = count C 5 + count C 6 := by omega
          have hd0 : count C' 3 = 0 := by omega
          have hEq5 : count C 5 = count C' 6 := by omega
          have hEq6 : count C 6 = count C' 5 := by omega
          right; right; right; right; right
          rw [ha0, hEq5, hEq6, hd0]
      · -- b > 0 only
        let t5 := Classical.choose (exists_type_of_count_pos h5)
        have ht5 : colVal (C t5) = 5 := Classical.choose_spec (exists_type_of_count_pos h5)
        let s5 := actType ρ (f t5) 5
        have hct5 : C t5 = col356 5 := (colVal_eq_five_iff_col5 (C t5)).mp ht5
        have hs5 : s5 = 3 ∨ s5 = 5 ∨ s5 = 6 := by
          have h' : colVal (rowPermute ρ (if f t5 then flipCol (C t5) else C t5)) = 3 ∨
              colVal (rowPermute ρ (if f t5 then flipCol (C t5) else C t5)) = 5 ∨
              colVal (rowPermute ρ (if f t5 then flipCol (C t5) else C t5)) = 6 :=
            image_type_in_356 hC hC' hh t5 (Or.inr (Or.inl ht5))
          simpa [s5, actType, hct5] using h'
        have hle5 : count C 5 ≤ count C' s5 := by
          simpa [s5] using (count_le_image hC hC' hh (Or.inr (Or.inl rfl)) t5 ht5)
        have ha0 : count C 3 = 0 := by omega
        have hc0 : count C 6 = 0 := by omega
        rcases hs5 with hs5' | hs5' | hs5'
        · have hle5' : count C 5 ≤ count C' 3 := by simpa [hs5'] using hle5
          have hsum : count C' 3 + count C' 5 + count C' 6 = count C 5 := by omega
          have he5 : count C' 5 = 0 := by omega
          have he6 : count C' 6 = 0 := by omega
          have hEq5 : count C 5 = count C' 3 := by omega
          right; left
          rw [ha0, hc0, hEq5, he5, he6]
        · have hle5' : count C 5 ≤ count C' 5 := by simpa [hs5'] using hle5
          have hsum : count C' 3 + count C' 5 + count C' 6 = count C 5 := by omega
          have he3 : count C' 3 = 0 := by omega
          have he6 : count C' 6 = 0 := by omega
          have hEq5 : count C 5 = count C' 5 := by omega
          left
          rw [ha0, hc0, hEq5, he3, he6]
        · have hle5' : count C 5 ≤ count C' 6 := by simpa [hs5'] using hle5
          have hsum : count C' 3 + count C' 5 + count C' 6 = count C 5 := by omega
          have he3 : count C' 3 = 0 := by omega
          have he5 : count C' 5 = 0 := by omega
          have hEq5 : count C 5 = count C' 6 := by omega
          right; right; right; left
          rw [ha0, hc0, hEq5, he3, he5]
    · by_cases h6 : 0 < count C 6
      · -- c > 0 only
        let t6 := Classical.choose (exists_type_of_count_pos h6)
        have ht6 : colVal (C t6) = 6 := Classical.choose_spec (exists_type_of_count_pos h6)
        let s6 := actType ρ (f t6) 6
        have hct6 : C t6 = col356 6 := (colVal_eq_six_iff_col6 (C t6)).mp ht6
        have hs6 : s6 = 3 ∨ s6 = 5 ∨ s6 = 6 := by
          have h' : colVal (rowPermute ρ (if f t6 then flipCol (C t6) else C t6)) = 3 ∨
              colVal (rowPermute ρ (if f t6 then flipCol (C t6) else C t6)) = 5 ∨
              colVal (rowPermute ρ (if f t6 then flipCol (C t6) else C t6)) = 6 :=
            image_type_in_356 hC hC' hh t6 (Or.inr (Or.inr ht6))
          simpa [s6, actType, hct6] using h'
        have hle6 : count C 6 ≤ count C' s6 := by
          simpa [s6] using (count_le_image hC hC' hh (Or.inr (Or.inr rfl)) t6 ht6)
        have ha0 : count C 3 = 0 := by omega
        have hb0 : count C 5 = 0 := by omega
        rcases hs6 with hs6' | hs6' | hs6'
        · have hle6' : count C 6 ≤ count C' 3 := by simpa [hs6'] using hle6
          have hsum : count C' 3 + count C' 5 + count C' 6 = count C 6 := by omega
          have he5 : count C' 5 = 0 := by omega
          have he6 : count C' 6 = 0 := by omega
          have hEq6 : count C 6 = count C' 3 := by omega
          right; right; left
          rw [ha0, hb0, hEq6, he5, he6]
        · have hle6' : count C 6 ≤ count C' 5 := by simpa [hs6'] using hle6
          have hsum : count C' 3 + count C' 5 + count C' 6 = count C 6 := by omega
          have he3 : count C' 3 = 0 := by omega
          have he6 : count C' 6 = 0 := by omega
          have hEq6 : count C 6 = count C' 5 := by omega
          right; right; right; right; right
          rw [ha0, hb0, hEq6, he3, he6]
        · have hle6' : count C 6 ≤ count C' 6 := by simpa [hs6'] using hle6
          have hsum : count C' 3 + count C' 5 + count C' 6 = count C 6 := by omega
          have he3 : count C' 3 = 0 := by omega
          have he5 : count C' 5 = 0 := by omega
          have hEq6 : count C 6 = count C' 6 := by omega
          left
          rw [ha0, hb0, hEq6, he3, he5]
      · -- none: all counts are zero
        have hb0 : count C 3 = 0 := by omega
        have hc0 : count C 5 = 0 := by omega
        have hd0 : count C 6 = 0 := by omega
        have hsum : count C' 3 + count C' 5 + count C' 6 = 0 := by omega
        have he0 : count C' 3 = 0 := by omega
        have hf0 : count C' 5 = 0 := by omega
        have hg0 : count C' 6 = 0 := by omega
        left
        rw [hb0, hc0, hd0, he0, hf0, hg0]

/-- `thm:linearopt` (Theorem 2) C0-case engine: equivalence between linear codes preserves
"all three counts |3|,|5|,|6| are odd". -/
lemma all_odd_counts_of_equivalent {n : ℕ} {C C' : Code n} (hC : IsLinear C) (hC' : IsLinear C')
    (h : Equivalent C C') :
    (Odd (count C 3) ∧ Odd (count C 5) ∧ Odd (count C 6)) →
      (Odd (count C' 3) ∧ Odd (count C' 5) ∧ Odd (count C' 6)) := by
  intro hall
  rcases count_356_perm_equiv hC hC' h with hp | hp | hp | hp | hp | hp
  · rcases hall with ⟨h3, h5, h6⟩
    have hc3 : count C 3 = count C' 3 := by simpa using congrArg Prod.fst hp
    have hc5 : count C 5 = count C' 5 := by simpa using congrArg (fun p : ℕ × ℕ × ℕ => p.2.1) hp
    have hc6 : count C 6 = count C' 6 := by simpa using congrArg (fun p : ℕ × ℕ × ℕ => p.2.2) hp
    constructor
    · rw [← hc3]; exact h3
    · constructor
      · rw [← hc5]; exact h5
      · rw [← hc6]; exact h6
  · rcases hall with ⟨h3, h5, h6⟩
    have hc5' : count C 3 = count C' 5 := by simpa using congrArg Prod.fst hp
    have hc3' : count C 5 = count C' 3 := by simpa using congrArg (fun p : ℕ × ℕ × ℕ => p.2.1) hp
    have hc6' : count C 6 = count C' 6 := by simpa using congrArg (fun p : ℕ × ℕ × ℕ => p.2.2) hp
    constructor
    · rw [← hc3']; exact h5
    · constructor
      · rw [← hc5']; exact h3
      · rw [← hc6']; exact h6
  · rcases hall with ⟨h3, h5, h6⟩
    have hc6' : count C 3 = count C' 6 := by simpa using congrArg Prod.fst hp
    have hc5' : count C 5 = count C' 5 := by simpa using congrArg (fun p : ℕ × ℕ × ℕ => p.2.1) hp
    have hc3' : count C 6 = count C' 3 := by simpa using congrArg (fun p : ℕ × ℕ × ℕ => p.2.2) hp
    constructor
    · rw [← hc3']; exact h6
    · constructor
      · rw [← hc5']; exact h5
      · rw [← hc6']; exact h3
  · rcases hall with ⟨h3, h5, h6⟩
    have hc5' : count C 3 = count C' 5 := by simpa using congrArg Prod.fst hp
    have hc6' : count C 5 = count C' 6 := by simpa using congrArg (fun p : ℕ × ℕ × ℕ => p.2.1) hp
    have hc3' : count C 6 = count C' 3 := by simpa using congrArg (fun p : ℕ × ℕ × ℕ => p.2.2) hp
    constructor
    · rw [← hc3']; exact h6
    · constructor
      · rw [← hc5']; exact h3
      · rw [← hc6']; exact h5
  · rcases hall with ⟨h3, h5, h6⟩
    have hc6' : count C 3 = count C' 6 := by simpa using congrArg Prod.fst hp
    have hc3' : count C 5 = count C' 3 := by simpa using congrArg (fun p : ℕ × ℕ × ℕ => p.2.1) hp
    have hc5' : count C 6 = count C' 5 := by simpa using congrArg (fun p : ℕ × ℕ × ℕ => p.2.2) hp
    constructor
    · rw [← hc3']; exact h5
    · constructor
      · rw [← hc5']; exact h6
      · rw [← hc6']; exact h3
  · rcases hall with ⟨h3, h5, h6⟩
    have hc3' : count C 3 = count C' 3 := by simpa using congrArg Prod.fst hp
    have hc6' : count C 5 = count C' 6 := by simpa using congrArg (fun p : ℕ × ℕ × ℕ => p.2.1) hp
    have hc5' : count C 6 = count C' 5 := by simpa using congrArg (fun p : ℕ × ℕ × ℕ => p.2.2) hp
    constructor
    · rw [← hc3']; exact h3
    · constructor
      · rw [← hc5']; exact h6
      · rw [← hc6']; exact h5

/-- The ideal C(k,k,k−1) never has all of |3|,|5|,|6| odd. -/
lemma not_all_odd_ideal_r2 {k : ℕ} (hk : 1 ≤ k) :
    ¬ (Odd k ∧ Odd k ∧ Odd (k - 1)) := by
  rintro ⟨h1, h2, h3⟩
  have hkne : ¬ Even k := (Nat.not_even_iff_odd).mpr h1
  rcases h3 with ⟨b, hb⟩
  have hke : Even k := by
    refine ⟨b + 1, ?_⟩
    omega
  exact hkne hke

/-- The ideal C(k+1,k+1,k−2) never has all of |3|,|5|,|6| odd. -/
lemma not_all_odd_ideal_r0a {k : ℕ} (hk : 2 ≤ k) :
    ¬ (Odd (k + 1) ∧ Odd (k + 1) ∧ Odd (k - 2)) := by
  rintro ⟨h1, h2, h3⟩
  rcases h1 with ⟨a, ha⟩
  rcases h3 with ⟨b, hb⟩
  omega

/-- The ideal C(k+1,k,k−1) never has all of |3|,|5|,|6| odd. -/
lemma not_all_odd_ideal_r0b {k : ℕ} (_hk : 2 ≤ k) :
    ¬ (Odd (k + 1) ∧ Odd k ∧ Odd (k - 1)) := by
  rintro ⟨h1, h2, h3⟩
  rcases h1 with ⟨a, ha⟩
  rcases h2 with ⟨b, hb⟩
  omega

/-- The ideal C(k+1,k,k) never has all of |3|,|5|,|6| odd. -/
lemma not_all_odd_ideal_r1a {k : ℕ} (_hk : 1 ≤ k) :
    ¬ (Odd (k + 1) ∧ Odd k ∧ Odd k) := by
  rintro ⟨h1, h2, h3⟩
  rcases h1 with ⟨a, ha⟩
  rcases h2 with ⟨b, hb⟩
  omega

/-- The ideal C(k+2,k,k−1) never has all of |3|,|5|,|6| odd. -/
lemma not_all_odd_ideal_r1b {k : ℕ} (hk : 1 ≤ k) :
    ¬ (Odd (k + 2) ∧ Odd k ∧ Odd (k - 1)) := by
  rintro ⟨h1, h2, h3⟩
  rcases h2 with ⟨a, ha⟩
  rcases h3 with ⟨b, hb⟩
  omega

/-- `thm:linearopt` (Theorem 2) C0 case: if `C'` has only types 0,5,6 with |3| = 0 and
|5|,|6| odd, then the counts of `C` (equivalent to `C'`) have exactly one
zero component and the other two are odd. -/
lemma c0_counts_perm {n : ℕ} {C C' : Code n} (hC : IsLinear C) (hC' : IsLinear C')
    (h : Equivalent C C') (h3 : count C' 3 = 0)
    (h5 : Odd (count C' 5)) (h6 : Odd (count C' 6)) :
    (count C 3 = 0 ∧ Odd (count C 5) ∧ Odd (count C 6)) ∨
    (count C 5 = 0 ∧ Odd (count C 3) ∧ Odd (count C 6)) ∨
    (count C 6 = 0 ∧ Odd (count C 3) ∧ Odd (count C 5)) := by
  rcases count_356_perm_equiv hC hC' h with hp | hp | hp | hp | hp | hp
  · -- (0, a, b)
    have hc3 : count C 3 = 0 := by simpa [h3] using congrArg Prod.fst hp
    have hc5 : count C 5 = count C' 5 := by simpa using congrArg (fun p : ℕ × ℕ × ℕ => p.2.1) hp
    have hc6 : count C 6 = count C' 6 := by simpa using congrArg (fun p : ℕ × ℕ × ℕ => p.2.2) hp
    left
    exact ⟨hc3, by rw [hc5]; exact h5, by rw [hc6]; exact h6⟩
  · -- (a, 0, b)
    have hc5 : count C 5 = 0 := by simpa [h3] using congrArg (fun p : ℕ × ℕ × ℕ => p.2.1) hp
    have hc3 : count C 3 = count C' 5 := by simpa using congrArg Prod.fst hp
    have hc6 : count C 6 = count C' 6 := by simpa using congrArg (fun p : ℕ × ℕ × ℕ => p.2.2) hp
    right; left
    exact ⟨hc5, by rw [hc3]; exact h5, by rw [hc6]; exact h6⟩
  · -- (b, a, 0)
    have hc6 : count C 6 = 0 := by simpa [h3] using congrArg (fun p : ℕ × ℕ × ℕ => p.2.2) hp
    have hc3 : count C 3 = count C' 6 := by simpa using congrArg Prod.fst hp
    have hc5 : count C 5 = count C' 5 := by simpa using congrArg (fun p : ℕ × ℕ × ℕ => p.2.1) hp
    right; right
    exact ⟨hc6, by rw [hc3]; exact h6, by rw [hc5]; exact h5⟩
  · -- (a, b, 0)
    have hc6 : count C 6 = 0 := by simpa [h3] using congrArg (fun p : ℕ × ℕ × ℕ => p.2.2) hp
    have hc3 : count C 3 = count C' 5 := by simpa using congrArg Prod.fst hp
    have hc5 : count C 5 = count C' 6 := by simpa using congrArg (fun p : ℕ × ℕ × ℕ => p.2.1) hp
    right; right
    exact ⟨hc6, by rw [hc3]; exact h5, by rw [hc5]; exact h6⟩
  · -- (b, 0, a)
    have hc5 : count C 5 = 0 := by simpa [h3] using congrArg (fun p : ℕ × ℕ × ℕ => p.2.1) hp
    have hc3 : count C 3 = count C' 6 := by simpa using congrArg Prod.fst hp
    have hc6 : count C 6 = count C' 5 := by simpa using congrArg (fun p : ℕ × ℕ × ℕ => p.2.2) hp
    right; left
    exact ⟨hc5, by rw [hc3]; exact h6, by rw [hc6]; exact h5⟩
  · -- (0, b, a)
    have hc3 : count C 3 = 0 := by simpa [h3] using congrArg Prod.fst hp
    have hc5 : count C 5 = count C' 6 := by simpa using congrArg (fun p : ℕ × ℕ × ℕ => p.2.1) hp
    have hc6 : count C 6 = count C' 5 := by simpa using congrArg (fun p : ℕ × ℕ × ℕ => p.2.2) hp
    left
    exact ⟨hc3, by rw [hc5]; exact h6, by rw [hc6]; exact h5⟩

/-- `thm:linearopt` (Theorem 2) C0 case: replacing the single zero column of a code
equivalent to a C0-form code by the type whose count is zero yields a linear
code with no zero columns, universally equal to the original, and with all of
|3|,|5|,|6| odd. -/
-- native_decide: Mechanical · n=any · checked 2026-08-24
lemma zero_column_all_odd {n : ℕ} {D : Code n} (hlin : IsLinear D) (h1 : count D 0 = 1)
    (t : Fin n) (ht : D t = col0)
    (hC0 : ∃ C0 : Code n, Equivalent D C0 ∧ count C0 0 + count C0 5 + count C0 6 = n ∧
      Odd (count C0 5) ∧ Odd (count C0 6)) :
    ∃ D' : Code n, IsLinear D' ∧ count D' 0 = 0 ∧ UniversalEqual D' D ∧
      (Odd (count D' 3) ∧ Odd (count D' 5) ∧ Odd (count D' 6)) := by
  rcases hC0 with ⟨C0, hEqC0, hcnt, h5odd, h6odd⟩
  have hlinC0 : IsLinear C0 := by
    -- C0 has only types 0,5,6: counts sum to n
    constructor
    · intro u
      have hmem : u ∈ (Finset.univ.filter fun t : Fin n => colVal (C0 t) = colVal (C0 u)) := by
        simp
      have hpos : 0 < count C0 (colVal (C0 u)) := by
        have hcard : 1 ≤ (Finset.univ.filter fun t : Fin n => colVal (C0 t) = colVal (C0 u)).card :=
          Nat.succ_le_of_lt (Finset.card_pos.mpr ⟨u, hmem⟩)
        rw [count_eq_card]
        exact hcard
      -- if colVal (C0 u) ∉ {0,5,6}, its count is 0 — contradiction
      by_cases hrest : colVal (C0 u) = 0 ∨ colVal (C0 u) = 5 ∨ colVal (C0 u) = 6
      · rcases hrest with h0 | h5 | h6
        · exact Or.inl h0
        · exact Or.inr (Or.inr (Or.inl h5))
        · exact Or.inr (Or.inr (Or.inr h6))
      · exfalso
        have hrest' : count C0 (colVal (C0 u)) = 0 := by
          -- sum over Icc 0 15 collapses to 0,5,6
          have hsumAll := sum_counts_eq_n C0
          have hS : ({0, 5, 6} : Finset ℕ) ⊆ Finset.Icc 0 15 := by
            intro x hx
            simp at hx ⊢
            omega
          have hsumS : (∑ i ∈ ({0, 5, 6} : Finset ℕ), count C0 i) = n := by
            simp [Finset.sum_insert]
            omega
          have hcomp : (∑ i ∈ Finset.Icc 0 15 \ ({0, 5, 6} : Finset ℕ), count C0 i) = 0 := by
            have hsplit : (∑ i ∈ Finset.Icc 0 15, count C0 i) =
                (∑ i ∈ ({0, 5, 6} : Finset ℕ), count C0 i) +
                  ∑ i ∈ Finset.Icc 0 15 \ ({0, 5, 6} : Finset ℕ), count C0 i := by
              rw [← Finset.sum_sdiff hS]
              rw [add_comm]
            omega
          have hle : count C0 (colVal (C0 u)) ≤
              ∑ i ∈ Finset.Icc 0 15 \ ({0, 5, 6} : Finset ℕ), count C0 i := by
            have hi : colVal (C0 u) ∈ Finset.Icc 0 15 \ ({0, 5, 6} : Finset ℕ) := by
              rw [Finset.mem_sdiff]
              constructor
              · simp [Finset.mem_Icc, colVal_le_15 (C0 u)]
              · intro hiS
                simp at hiS
                exact hrest hiS
            exact Finset.single_le_sum (by intro j _; exact Nat.zero_le _) hi
          omega
        omega
    · -- at least two positive: |5|,|6| are odd hence positive
      right; right
      constructor
      · rcases h5odd with ⟨a, ha⟩
        have : 0 < count C0 5 := by
          rw [ha]
          omega
        exact this
      · rcases h6odd with ⟨a, ha⟩
        have : 0 < count C0 6 := by
          rw [ha]
          omega
        exact this
  have h3zero : count C0 3 = 0 := by
    -- |3|_C0 = 0: from the C0-form sum
    have hsumC0 : (∑ i ∈ ({0, 5, 6} : Finset ℕ), count C0 i) = n := by
      simp [Finset.sum_insert]
      omega
    have hsumAll := sum_counts_eq_n C0
    have hz2 : (∑ i ∈ Finset.Icc 0 15 \ ({0, 5, 6} : Finset ℕ), count C0 i) = 0 := by
      have hsplit : (∑ i ∈ Finset.Icc 0 15, count C0 i) =
          (∑ i ∈ ({0, 5, 6} : Finset ℕ), count C0 i) +
            ∑ i ∈ Finset.Icc 0 15 \ ({0, 5, 6} : Finset ℕ), count C0 i := by
        have hS : ({0, 5, 6} : Finset ℕ) ⊆ Finset.Icc 0 15 := by
          intro x hx
          simp at hx ⊢
          omega
        rw [← Finset.sum_sdiff hS]
        omega
      omega
    have hle : count C0 3 ≤
        ∑ i ∈ Finset.Icc 0 15 \ ({0, 5, 6} : Finset ℕ), count C0 i := by
      have hi : 3 ∈ Finset.Icc 0 15 \ ({0, 5, 6} : Finset ℕ) := by
        rw [Finset.mem_sdiff]
        constructor
        · simp [Finset.mem_Icc]
        · simp
      exact Finset.single_le_sum (by intro j _; exact Nat.zero_le _) hi
    omega
  rcases c0_counts_perm hlin hlinC0 hEqC0 h3zero h5odd h6odd with hperm | hperm | hperm
  · -- count D 3 = 0: add a 3
    rcases hperm with ⟨h3z, h5o, h6o⟩
    let D' : Code n := replaceColumn D t col3
    have hlin' : IsLinear D' := isLinear_replace_0 D hlin t ht col3 (Or.inl (by native_decide : colVal col3 = 3))
    have hcnt' : count D' 0 = 0 := by
      rw [count_replace_0_nonzero D t col3 ht (by native_decide : col3 ≠ col0)]
      omega
    have hEq : UniversalEqual D' D :=
      zero_column D t ht ⟨C0, hEqC0, hcnt, h5odd, h6odd⟩ col3
    have hodd3 : Odd (count D' 3) := by
      have hself := count_replace_0_self D t col3 ht (by native_decide : colVal col3 ≠ 0)
      have hcv : colVal col3 = 3 := by native_decide
      rw [hcv] at hself
      have hc : count D' 3 = count D 3 + 1 := by simpa [D', hcv] using hself
      rw [hc, h3z]
      norm_num
    have hodd5 : Odd (count D' 5) := by
      have hc : count D' 5 = count D 5 := by
        have heq := count_replace_0_eq D t col3 ht (by omega : 5 ≠ 0) (by omega : 5 ≠ 3)
        simpa [D'] using heq
      rw [hc]
      exact h5o
    have hodd6 : Odd (count D' 6) := by
      have hc : count D' 6 = count D 6 := by
        have heq := count_replace_0_eq D t col3 ht (by omega : 6 ≠ 0) (by omega : 6 ≠ 3)
        simpa [D'] using heq
      rw [hc]
      exact h6o
    exact ⟨D', hlin', hcnt', hEq, ⟨hodd3, hodd5, hodd6⟩⟩
  · -- count D 5 = 0: add a 5
    rcases hperm with ⟨h5z, h3o, h6o⟩
    let D' : Code n := replaceColumn D t col5
    have hlin' : IsLinear D' := isLinear_replace_0 D hlin t ht col5 (Or.inr (Or.inl (by native_decide : colVal col5 = 5)))
    have hcnt' : count D' 0 = 0 := by
      rw [count_replace_0_nonzero D t col5 ht (by native_decide : col5 ≠ col0)]
      omega
    have hEq : UniversalEqual D' D :=
      zero_column D t ht ⟨C0, hEqC0, hcnt, h5odd, h6odd⟩ col5
    have hodd5 : Odd (count D' 5) := by
      have hself := count_replace_0_self D t col5 ht (by native_decide : colVal col5 ≠ 0)
      have hcv : colVal col5 = 5 := by native_decide
      rw [hcv] at hself
      have hc : count D' 5 = count D 5 + 1 := by simpa [D', hcv] using hself
      rw [hc, h5z]
      norm_num
    have hodd3 : Odd (count D' 3) := by
      have hc : count D' 3 = count D 3 := by
        have heq := count_replace_0_eq D t col5 ht (by omega : 3 ≠ 0) (by omega : 3 ≠ 5)
        simpa [D'] using heq
      rw [hc]
      exact h3o
    have hodd6 : Odd (count D' 6) := by
      have hc : count D' 6 = count D 6 := by
        have heq := count_replace_0_eq D t col5 ht (by omega : 6 ≠ 0) (by omega : 6 ≠ 5)
        simpa [D'] using heq
      rw [hc]
      exact h6o
    exact ⟨D', hlin', hcnt', hEq, ⟨hodd3, hodd5, hodd6⟩⟩
  · -- count D 6 = 0: add a 6
    rcases hperm with ⟨h6z, h3o, h5o⟩
    let D' : Code n := replaceColumn D t col6
    have hlin' : IsLinear D' := isLinear_replace_0 D hlin t ht col6 (Or.inr (Or.inr (by native_decide : colVal col6 = 6)))
    have hcnt' : count D' 0 = 0 := by
      rw [count_replace_0_nonzero D t col6 ht (by native_decide : col6 ≠ col0)]
      omega
    have hEq : UniversalEqual D' D :=
      zero_column D t ht ⟨C0, hEqC0, hcnt, h5odd, h6odd⟩ col6
    have hodd6 : Odd (count D' 6) := by
      have hself := count_replace_0_self D t col6 ht (by native_decide : colVal col6 ≠ 0)
      have hcv : colVal col6 = 6 := by native_decide
      rw [hcv] at hself
      have hc : count D' 6 = count D 6 + 1 := by simpa [D', hcv] using hself
      rw [hc, h6z]
      norm_num
    have hodd3 : Odd (count D' 3) := by
      have hc : count D' 3 = count D 3 := by
        have heq := count_replace_0_eq D t col6 ht (by omega : 3 ≠ 0) (by omega : 3 ≠ 6)
        simpa [D'] using heq
      rw [hc]
      exact h3o
    have hodd5 : Odd (count D' 5) := by
      have hc : count D' 5 = count D 5 := by
        have heq := count_replace_0_eq D t col6 ht (by omega : 5 ≠ 0) (by omega : 5 ≠ 6)
        simpa [D'] using heq
      rw [hc]
      exact h5o
    exact ⟨D', hlin', hcnt', hEq, ⟨hodd3, hodd5, hodd6⟩⟩

/-- `thm:linearopt` (Theorem 2) zero-column engine: any linear code with at least one
zero column is weakly dominated by a linear code with no zero columns; in the
C0 case the replacement has all-odd counts (3,5,6), otherwise the domination
is strict. -/
lemma linear_zero_to_nozero {n : ℕ} (D : Code n) (hlin : IsLinear D) (hz : count D 0 ≥ 1) :
    ∃ D' : Code n, IsLinear D' ∧ count D' 0 = 0 ∧ UniversalBetter D' D ∧
      (UniversalStrictBetter D' D ∨ (Odd (count D' 3) ∧ Odd (count D' 5) ∧ Odd (count D' 6))) := by
  have hmain : ∀ c : ℕ, ∀ D : Code n, IsLinear D → count D 0 = c → 1 ≤ count D 0 →
      ∃ D' : Code n, IsLinear D' ∧ count D' 0 = 0 ∧ UniversalBetter D' D ∧
        (UniversalStrictBetter D' D ∨ (Odd (count D' 3) ∧ Odd (count D' 5) ∧ Odd (count D' 6))) := by
    intro c
    induction c using Nat.strong_induction_on with
    | h c ih =>
      intro D hlin hcount hpos
      by_cases h0 : count D 0 = 0
      · exfalso
        omega
      · by_cases h1 : count D 0 = 1
        · -- exactly one zero column
          by_cases hC0 : ∃ C0 : Code n, Equivalent D C0 ∧
              count C0 0 + count C0 5 + count C0 6 = n ∧ Odd (count C0 5) ∧ Odd (count C0 6)
          · rcases exists_col0_of_count_pos D (by omega : 1 ≤ count D 0) with ⟨t, ht⟩
            rcases zero_column_all_odd hlin h1 t ht hC0 with ⟨D₁, hlin₁, hcount₁, heq, hallodd⟩
            exact ⟨D₁, hlin₁, hcount₁, universalBetter_of_equal heq, Or.inr hallodd⟩
          · rcases zero_column_strict D (by omega : count D 0 ≥ 1) hC0 with ⟨t, ht, s', hs', hstrict⟩
            let D₁ : Code n := replaceColumn D t s'
            have hlin₁ : IsLinear D₁ := isLinear_replace_0 D hlin t ht s' hs'
            have hcount₁ : count D₁ 0 = 0 := by
              rw [count_replace_0_nonzero D t s' ht (col0_ne_of_colVal_356 hs')]
              omega
            exact ⟨D₁, hlin₁, hcount₁, universalBetter_of_strict hstrict, Or.inl hstrict⟩
        · -- count D 0 ≥ 2
          rcases two_zero_columns D (by omega : 2 ≤ count D 0) with ⟨t₁, t₂, htne, ht1, ht2, s₁, s₂, hs1, hs2, hstrict⟩
          let D₁ : Code n := replaceColumn (replaceColumn D t₁ s₁) t₂ s₂
          have hlin₁ : IsLinear D₁ := by
            have hlin₁' : IsLinear (replaceColumn D t₁ s₁) :=
              isLinear_replace_0 D hlin t₁ ht1 s₁ hs1
            have ht2' : (replaceColumn D t₁ s₁) t₂ = col0 := by
              have hne : t₂ ≠ t₁ := htne.symm
              simp [replaceColumn, hne, ht2]
            exact isLinear_replace_0 (replaceColumn D t₁ s₁) hlin₁' t₂ ht2' s₂ hs2
          have hcount₁ : count D₁ 0 = count D 0 - 2 := by
            have hc2 : count (replaceColumn (replaceColumn D t₁ s₁) t₂ s₂) 0 =
                count (replaceColumn D t₁ s₁) 0 - 1 :=
              count_replace_0_nonzero (replaceColumn D t₁ s₁) t₂ s₂
                (by have hne : t₂ ≠ t₁ := htne.symm
                    simp [replaceColumn, hne, ht2])
                (col0_ne_of_colVal_356 hs2)
            have hc1 : count (replaceColumn D t₁ s₁) 0 = count D 0 - 1 :=
              count_replace_0_nonzero D t₁ s₁ ht1 (col0_ne_of_colVal_356 hs1)
            rw [hc2, hc1]
            omega
          by_cases h₁z : count D₁ 0 = 0
          · exact ⟨D₁, hlin₁, h₁z, universalBetter_of_strict hstrict, Or.inl hstrict⟩
          · have hlt : count D₁ 0 < count D 0 := by omega
            have h₁pos : 1 ≤ count D₁ 0 := by omega
            have hlt' : count D₁ 0 < c := by omega
            have hrec := ih (count D₁ 0) hlt' D₁ hlin₁ rfl h₁pos
            rcases hrec with ⟨D', hlin', hz', hbetter, hflag⟩
            have hflag' : UniversalStrictBetter D' D ∨
                (Odd (count D' 3) ∧ Odd (count D' 5) ∧ Odd (count D' 6)) := by
              rcases hflag with hflag1 | hflag2
              · exact Or.inl (universalStrictBetter_trans hflag1 hstrict)
              · exact Or.inr hflag2
            exact ⟨D', hlin', hz', universalBetter_trans hbetter (universalBetter_of_strict hstrict), hflag'⟩
  exact hmain (count D 0) D hlin rfl hz

/-- Theorem `thm:linearopt` (Theorem 2), n = 3k−1: C(k,k,k−1) strictly dominates every
non-equivalent linear code. -/
theorem linear_opt_residue2 {k : ℕ} (hk : k ≥ 1) :
    ∀ D : Code (k + k + (k - 1)), IsLinear D →
      ¬ Equivalent (linearCode k k (k - 1)) D →
        UniversalStrictBetter (linearCode k k (k - 1)) D := by
  intro D hlin hne
  let I : Code (k + k + (k - 1)) := linCode k k (k - 1) (by omega)
  by_cases hz : count D 0 = 0
  · -- no zero columns: normalize to the canonical counts
    have hEq : Equivalent D
        (linCode (count D 3) (count D 5) (count D 6) (linear_count_sum_eq D hlin hz)) := by
      simpa [linCode] using (linear_equiv_linearCode D hlin hz)
    have hneC : ¬ Equivalent I
        (linCode (count D 3) (count D 5) (count D 6) (linear_count_sum_eq D hlin hz)) := by
      intro hc
      have hc' : Equivalent (linearCode k k (k - 1))
          (linCode (count D 3) (count D 5) (count D 6) (linear_count_sum_eq D hlin hz)) := by
        simpa [I, linCode] using hc
      exact hne (equivalent_trans hc' (equivalent_symm hEq))
    have hDom := linear_opt_r2_triple hk rfl (count D 3) (count D 5) (count D 6)
      (linear_count_sum_eq D hlin hz) hneC
    have hDom' : UniversalStrictBetter I D :=
      universalStrictBetter_of_eq_left hDom
        (universalEqual_of_equivalent
          D (linCode (count D 3) (count D 5) (count D 6) (linear_count_sum_eq D hlin hz)) hEq)
    simpa [I, linCode] using hDom'
  · -- zero columns: reduce to a zero-column-free code first
    have hz1 : count D 0 ≥ 1 := by omega
    rcases linear_zero_to_nozero D hlin hz1 with ⟨D', hlin', hz0, hbetter, hflag⟩
    have hEq' : Equivalent D'
        (linCode (count D' 3) (count D' 5) (count D' 6) (linear_count_sum_eq D' hlin' hz0)) := by
      simpa [linCode] using (linear_equiv_linearCode D' hlin' hz0)
    have hIgtD : UniversalStrictBetter I D := by
      by_cases hEqI : Equivalent I D'
      · -- I ~ D': the strict chain or the all-odd contradiction gives I > D
        rcases hflag with hstrict | hallodd
        · have hID' : UniversalEqual I D' :=
            universalEqual_of_equivalent D' I (equivalent_symm hEqI)
          exact universalStrictBetter_of_eq_right hID' hstrict
        · exfalso
          -- D' has all-odd counts; I = (k,k,k−1) does not
          have hlinI : IsLinear I := by
            simpa [I, linCode] using (isLinear_linearCode (a := k) (b := k) (c := k - 1) hk (by omega))
          have hoddI : Odd (count I 3) ∧ Odd (count I 5) ∧ Odd (count I 6) :=
            all_odd_counts_of_equivalent (C := D') (C' := I) hlin' hlinI (equivalent_symm hEqI) hallodd
          have hnot : ¬ (Odd (count I 3) ∧ Odd (count I 5) ∧ Odd (count I 6)) := by
            have hcnt : count I 3 = k ∧ count I 5 = k ∧ count I 6 = k - 1 := by
              have h3 : count I 3 = k := by
                simpa [I, linCode] using (linear_count_3 (n3 := k) (n5 := k) (n6 := k - 1))
              have h5 : count I 5 = k := by
                simpa [I, linCode] using (linear_count_5 (n3 := k) (n5 := k) (n6 := k - 1))
              have h6 : count I 6 = k - 1 := by
                simpa [I, linCode] using (linear_count_6 (n3 := k) (n5 := k) (n6 := k - 1))
              exact ⟨h3, h5, h6⟩
            rcases hcnt with ⟨h3, h5, h6⟩
            rintro ⟨o3, o5, o6⟩
            have hk3 : Odd k := by simpa [h3] using o3
            have hk5 : Odd k := by simpa [h5] using o5
            have hk6 : Odd (k - 1) := by simpa [h6] using o6
            exact not_all_odd_ideal_r2 hk ⟨hk3, hk5, hk6⟩
          exact hnot hoddI
      · -- I > D' via the main descent, then I > D via the reduction chain
        have hneC' : ¬ Equivalent I
            (linCode (count D' 3) (count D' 5) (count D' 6) (linear_count_sum_eq D' hlin' hz0)) := by
          intro hc
          exact hEqI (equivalent_trans hc (equivalent_symm hEq'))
        have hDom' := linear_opt_r2_triple hk rfl (count D' 3) (count D' 5) (count D' 6)
          (linear_count_sum_eq D' hlin' hz0) hneC'
        have hIgtD' : UniversalStrictBetter I D' :=
          universalStrictBetter_of_eq_left hDom'
            (universalEqual_of_equivalent
              D' (linCode (count D' 3) (count D' 5) (count D' 6) (linear_count_sum_eq D' hlin' hz0)) hEq')
        exact universalStrictBetter_of_better_right hIgtD' hbetter
    simpa [I, linCode] using hIgtD

/- ### n = 3: linear codes are exactly the three equivalence classes

For n = 3 every linear code has counts (1,1,1), (2,1,0) (up to permutation)
or one zero column with counts (1,1,0) (up to permutation) — the last class
is equivalent to C_A, so the three optima cover all linear codes and the
theorem's "not equivalent to any of them" hypothesis is contradictory.
-/

/-- The linear (3,4) codes fall into the three classes [C_A], [C(1,1,1)],
[C(1,2,0)] (paper Table `table:optimal-linear`, n = 3). -/
-- native_decide: Contentful · n=3 · checked 2026-08-28
lemma linear3_classified (D : Code 3) (hlin : IsLinear D) :
    Equivalent CA D ∨ Equivalent (linearCode 1 1 1) D ∨ Equivalent (linearCode 1 2 0) D := by
  by_cases hz : count D 0 = 0
  · -- no zero columns: normalize to canonical counts
    have hEq : Equivalent D
        (linCode (count D 3) (count D 5) (count D 6) (linear_count_sum_eq D hlin hz)) := by
      simpa [linCode] using (linear_equiv_linearCode D hlin hz)
    have hsum : count D 3 + count D 5 + count D 6 = 3 := linear_count_sum_eq D hlin hz
    have hcnt : (count D 3 = 1 ∧ count D 5 = 1 ∧ count D 6 = 1) ∨
        (count D 3 = 2 ∧ count D 5 = 1 ∧ count D 6 = 0) ∨
        (count D 3 = 1 ∧ count D 5 = 2 ∧ count D 6 = 0) ∨
        (count D 3 = 1 ∧ count D 5 = 0 ∧ count D 6 = 2) ∨
        (count D 3 = 2 ∧ count D 5 = 0 ∧ count D 6 = 1) ∨
        (count D 3 = 0 ∧ count D 5 = 1 ∧ count D 6 = 2) ∨
        (count D 3 = 0 ∧ count D 5 = 2 ∧ count D 6 = 1) := by
      set a := count D 3 with ha
      set b := count D 5 with hb
      set c := count D 6 with hc
      have hsum' : a + b + c = 3 := by simpa [ha, hb, hc] using hsum
      have hpos' : (0 < a ∧ 0 < b) ∨ (0 < a ∧ 0 < c) ∨ (0 < b ∧ 0 < c) := by
        simpa [ha, hb, hc] using hlin.2
      have h3a : a ≤ 3 := by omega
      have h3b : b ≤ 3 := by omega
      have h3c : c ≤ 3 := by omega
      interval_cases a <;> interval_cases b <;> interval_cases c <;> omega
    rcases hcnt with h111 | h210 | h120 | h102 | h201 | h012 | h021
    · -- (1,1,1)
      have hEq' : Equivalent D (linCode 1 1 1 (by omega : 1 + 1 + 1 = 3)) := by
        have hid : linCode (count D 3) (count D 5) (count D 6) hsum =
            linCode 1 1 1 (by omega : 1 + 1 + 1 = 3) :=
          linCode_eq_of_counts h111.1 h111.2.1 h111.2.2 hsum (by omega)
        simpa [hid] using hEq
      have hid : linCode 1 1 1 (by omega : 1 + 1 + 1 = 3) = linearCode 1 1 1 := by simp [linCode]
      exact Or.inr (Or.inl (equivalent_symm (by simpa [hid] using hEq')))
    · -- (2,1,0): equivalent to C(1,2,0) via the swaps (2,1,0)~(2,0,1)~(1,0,2)~(1,2,0)
      have hsum1 : 2 + 0 + 1 = 3 := by omega
      have hsum2 : 1 + 0 + 2 = 3 := by omega
      have hsum3 : 1 + 2 + 0 = 3 := by omega
      have hEq' : Equivalent D (linCode 1 2 0 hsum3) := by
        have e0 : Equivalent D (linCode 2 1 0 (by omega : 2 + 1 + 0 = 3)) := by
          have hid : linCode (count D 3) (count D 5) (count D 6) hsum =
              linCode 2 1 0 (by omega : 2 + 1 + 0 = 3) :=
            linCode_eq_of_counts h210.1 h210.2.1 h210.2.2 hsum (by omega)
          simpa [hid] using hEq
        have e1 : Equivalent (linCode 2 1 0 (by omega : 2 + 1 + 0 = 3)) (linCode 2 0 1 hsum1) :=
          linCode_swap23_equiv (by omega : 2 + 1 + 0 = 3) hsum1
        have e2 : Equivalent (linCode 2 0 1 hsum1) (linCode 1 0 2 hsum2) :=
          linCode_swap13_equiv hsum1 hsum2
        have e3 : Equivalent (linCode 1 0 2 hsum2) (linCode 1 2 0 hsum3) :=
          linCode_swap23_equiv hsum2 hsum3
        exact equivalent_trans (equivalent_trans (equivalent_trans e0 e1) e2) e3
      have hid : linCode 1 2 0 hsum3 = linearCode 1 2 0 := by simp [linCode]
      exact Or.inr (Or.inr (equivalent_symm (by simpa [hid] using hEq')))
    · -- (1,2,0)
      have hEq' : Equivalent D (linCode 1 2 0 (by omega : 1 + 2 + 0 = 3)) := by
        have hid : linCode (count D 3) (count D 5) (count D 6) hsum =
            linCode 1 2 0 (by omega : 1 + 2 + 0 = 3) :=
          linCode_eq_of_counts h120.1 h120.2.1 h120.2.2 hsum (by omega)
        simpa [hid] using hEq
      have hid : linCode 1 2 0 (by omega : 1 + 2 + 0 = 3) = linearCode 1 2 0 := by simp [linCode]
      exact Or.inr (Or.inr (equivalent_symm (by simpa [hid] using hEq')))
    · -- (1,0,2): (1,0,2) ~ (1,2,0) via swap23
      have hsum' : 1 + 2 + 0 = 3 := by omega
      have hEq' : Equivalent D (linCode 1 2 0 hsum') := by
        have e0 : Equivalent D (linCode 1 0 2 (by omega : 1 + 0 + 2 = 3)) := by
          have hid : linCode (count D 3) (count D 5) (count D 6) hsum =
              linCode 1 0 2 (by omega : 1 + 0 + 2 = 3) :=
            linCode_eq_of_counts h102.1 h102.2.1 h102.2.2 hsum (by omega)
          simpa [hid] using hEq
        exact equivalent_trans e0 (linCode_swap23_equiv (by omega : 1 + 0 + 2 = 3) hsum')
      have hid : linCode 1 2 0 hsum' = linearCode 1 2 0 := by simp [linCode]
      exact Or.inr (Or.inr (equivalent_symm (by simpa [hid] using hEq')))
    · -- (2,0,1): (2,0,1) ~ (1,0,2) ~ (1,2,0)
      have hsum1 : 1 + 0 + 2 = 3 := by omega
      have hsum2 : 1 + 2 + 0 = 3 := by omega
      have hEq' : Equivalent D (linCode 1 2 0 hsum2) := by
        have e0 : Equivalent D (linCode 2 0 1 (by omega : 2 + 0 + 1 = 3)) := by
          have hid : linCode (count D 3) (count D 5) (count D 6) hsum =
              linCode 2 0 1 (by omega : 2 + 0 + 1 = 3) :=
            linCode_eq_of_counts h201.1 h201.2.1 h201.2.2 hsum (by omega)
          simpa [hid] using hEq
        have e1 : Equivalent (linCode 2 0 1 (by omega : 2 + 0 + 1 = 3)) (linCode 1 0 2 hsum1) :=
          linCode_swap13_equiv (by omega : 2 + 0 + 1 = 3) hsum1
        exact equivalent_trans (equivalent_trans e0 e1) (linCode_swap23_equiv hsum1 hsum2)
      have hid : linCode 1 2 0 hsum2 = linearCode 1 2 0 := by simp [linCode]
      exact Or.inr (Or.inr (equivalent_symm (by simpa [hid] using hEq')))
    · -- (0,1,2): (0,1,2) ~ (0,2,1) ~ (1,2,0)
      have hsum1 : 0 + 2 + 1 = 3 := by omega
      have hsum2 : 1 + 2 + 0 = 3 := by omega
      have hEq' : Equivalent D (linCode 1 2 0 hsum2) := by
        have e0 : Equivalent D (linCode 0 1 2 (by omega : 0 + 1 + 2 = 3)) := by
          have hid : linCode (count D 3) (count D 5) (count D 6) hsum =
              linCode 0 1 2 (by omega : 0 + 1 + 2 = 3) :=
            linCode_eq_of_counts h012.1 h012.2.1 h012.2.2 hsum (by omega)
          simpa [hid] using hEq
        have e1 : Equivalent (linCode 0 1 2 (by omega : 0 + 1 + 2 = 3)) (linCode 0 2 1 hsum1) :=
          linCode_swap23_equiv (by omega : 0 + 1 + 2 = 3) hsum1
        exact equivalent_trans (equivalent_trans e0 e1) (linCode_swap13_equiv hsum1 hsum2)
      have hid : linCode 1 2 0 hsum2 = linearCode 1 2 0 := by simp [linCode]
      exact Or.inr (Or.inr (equivalent_symm (by simpa [hid] using hEq')))
    · -- (0,2,1): (0,2,1) ~ (1,2,0) via swap13
      have hsum' : 1 + 2 + 0 = 3 := by omega
      have hEq' : Equivalent D (linCode 1 2 0 hsum') := by
        have e0 : Equivalent D (linCode 0 2 1 (by omega : 0 + 2 + 1 = 3)) := by
          have hid : linCode (count D 3) (count D 5) (count D 6) hsum =
              linCode 0 2 1 (by omega : 0 + 2 + 1 = 3) :=
            linCode_eq_of_counts h021.1 h021.2.1 h021.2.2 hsum (by omega)
          simpa [hid] using hEq
        exact equivalent_trans e0 (linCode_swap13_equiv (by omega : 0 + 2 + 1 = 3) hsum')
      have hid : linCode 1 2 0 hsum' = linearCode 1 2 0 := by simp [linCode]
      exact Or.inr (Or.inr (equivalent_symm (by simpa [hid] using hEq')))
  · -- zero columns: the two nonzero columns are of two distinct types 3,5,6,
    -- hence the code is equivalent to C_A = (col3, col5, col0)
    have hcnt0 : count D 0 = 1 := by
      by_contra h
      have h2 : 2 ≤ count D 0 := by omega
      have hle : count D 3 + count D 5 + count D 6 ≤ 1 := by
        have hsumAll := sum_counts_eq_n D
        have hzeros : ∀ i : ℕ, i ∉ ({0, 3, 5, 6} : Finset ℕ) → count D i = 0 := by
          intro i hi
          by_contra hc
          have hpos : 0 < count D i := Nat.pos_of_ne_zero hc
          rcases Finset.card_pos.mp (by rw [← count_eq_card D i]; exact hpos) with ⟨t, ht⟩
          have hci : colVal (D t) = i := (Finset.mem_filter.mp ht).2
          rcases hlin.1 t with h0 | h3 | h5 | h6
          · simp [Finset.mem_insert, Finset.mem_singleton] at hi; omega
          · simp [Finset.mem_insert, Finset.mem_singleton] at hi; omega
          · simp [Finset.mem_insert, Finset.mem_singleton] at hi; omega
          · simp [Finset.mem_insert, Finset.mem_singleton] at hi; omega
        have hsum' : (∑ i ∈ Finset.Icc 0 15, count D i) =
            count D 0 + (count D 3 + (count D 5 + count D 6)) := by
          have hS : ({0, 3, 5, 6} : Finset ℕ) ⊆ Finset.Icc 0 15 := by
            intro x hx
            simp at hx ⊢
            omega
          have hcomp : (∑ i ∈ Finset.Icc 0 15 \ ({0, 3, 5, 6} : Finset ℕ), count D i) = 0 := by
            apply Finset.sum_eq_zero
            intro i hi
            exact hzeros i (Finset.mem_sdiff.mp hi).2
          have hsplit : (∑ i ∈ Finset.Icc 0 15, count D i) =
              (∑ i ∈ ({0, 3, 5, 6} : Finset ℕ), count D i) +
                ∑ i ∈ Finset.Icc 0 15 \ ({0, 3, 5, 6} : Finset ℕ), count D i := by
            rw [← Finset.sum_sdiff hS]
            rw [add_comm]
          rw [hsplit, hcomp, add_zero]
          simp [Finset.sum_insert]
        omega
      rcases hlin.2 with h35 | h36 | h56
      · have : 2 ≤ count D 3 + count D 5 := by omega
        omega
      · have : 2 ≤ count D 3 + count D 6 := by omega
        omega
      · have : 2 ≤ count D 5 + count D 6 := by omega
        omega
    have hsum : count D 3 + count D 5 + count D 6 = 2 := by
      have hsumAll := sum_counts_eq_n D
      have hzeros : ∀ i : ℕ, i ∉ ({0, 3, 5, 6} : Finset ℕ) → count D i = 0 := by
        intro i hi
        by_contra hc
        have hpos : 0 < count D i := Nat.pos_of_ne_zero hc
        rcases Finset.card_pos.mp (by rw [← count_eq_card D i]; exact hpos) with ⟨t, ht⟩
        have hci : colVal (D t) = i := (Finset.mem_filter.mp ht).2
        rcases hlin.1 t with h0 | h3 | h5 | h6
        · simp [Finset.mem_insert, Finset.mem_singleton] at hi; omega
        · simp [Finset.mem_insert, Finset.mem_singleton] at hi; omega
        · simp [Finset.mem_insert, Finset.mem_singleton] at hi; omega
        · simp [Finset.mem_insert, Finset.mem_singleton] at hi; omega
      have hsum' : (∑ i ∈ Finset.Icc 0 15, count D i) =
          count D 0 + (count D 3 + (count D 5 + count D 6)) := by
        have hS : ({0, 3, 5, 6} : Finset ℕ) ⊆ Finset.Icc 0 15 := by
          intro x hx
          simp at hx ⊢
          omega
        have hcomp : (∑ i ∈ Finset.Icc 0 15 \ ({0, 3, 5, 6} : Finset ℕ), count D i) = 0 := by
          apply Finset.sum_eq_zero
          intro i hi
          exact hzeros i (Finset.mem_sdiff.mp hi).2
        have hsplit : (∑ i ∈ Finset.Icc 0 15, count D i) =
            (∑ i ∈ ({0, 3, 5, 6} : Finset ℕ), count D i) +
              ∑ i ∈ Finset.Icc 0 15 \ ({0, 3, 5, 6} : Finset ℕ), count D i := by
          rw [← Finset.sum_sdiff hS]
          rw [add_comm]
        rw [hsplit, hcomp, add_zero]
        simp [Finset.sum_insert]
      omega
    have hcnt : (count D 3 = 1 ∧ count D 5 = 1 ∧ count D 6 = 0) ∨
        (count D 3 = 1 ∧ count D 5 = 0 ∧ count D 6 = 1) ∨
        (count D 3 = 0 ∧ count D 5 = 1 ∧ count D 6 = 1) := by
      set a := count D 3 with ha
      set b := count D 5 with hb
      set c := count D 6 with hc
      have hsum' : a + b + c = 2 := by simpa [ha, hb, hc] using hsum
      have hpos' : (0 < a ∧ 0 < b) ∨ (0 < a ∧ 0 < c) ∨ (0 < b ∧ 0 < c) := by
        simpa [ha, hb, hc] using hlin.2
      have h3a : a ≤ 2 := by omega
      have h3b : b ≤ 2 := by omega
      have h3c : c ≤ 2 := by omega
      interval_cases a <;> interval_cases b <;> interval_cases c <;> omega
    rcases hcnt with h110 | h101 | h011
    · -- types (3,5): D ~ C_A directly (columns col0, col3, col5)
      rcases exists_col0_of_count_pos D (by omega : 1 ≤ count D 0) with ⟨t0, ht0⟩
      rcases Finset.card_pos.mp (by
        have : 0 < count D 3 := by rw [h110.1]; omega
        rw [← count_eq_card D 3]
        exact this) with ⟨t1, ht1⟩
      rcases Finset.card_pos.mp (by
        have : 0 < count D 5 := by rw [h110.2.1]; omega
        rw [← count_eq_card D 5]
        exact this) with ⟨t2, ht2⟩
      have ht1' : colVal (D t1) = 3 := (Finset.mem_filter.mp ht1).2
      have ht2' : colVal (D t2) = 5 := (Finset.mem_filter.mp ht2).2
      have ht1c : D t1 = col3 := (colVal_eq_three_iff_col3 (D t1)).mp ht1'
      have ht2c : D t2 = col5 := (colVal_eq_five_iff_col5 (D t2)).mp ht2'
      have ht0c : D t0 = col0 := ht0
      -- the three positions are distinct and cover Fin 3
      have hdist12 : t1 ≠ t2 := by
        intro h
        subst t2
        have hc : col3 = col5 := by
          rw [← ht1c, ← ht2c]
        have h3 : colVal col3 = 3 := by native_decide
        have h5 : colVal col5 = 5 := by native_decide
        omega
      have hdist01 : t1 ≠ t0 := by
        intro h
        subst t0
        have hc : col3 = col0 := by
          rw [← ht1c, ← ht0c]
        have hv : colVal col3 = 0 := by rw [hc]; native_decide
        have h3 : colVal col3 = 3 := by native_decide
        omega
      have hdist02 : t2 ≠ t0 := by
        intro h
        subst t0
        have hc : col5 = col0 := by
          rw [← ht2c, ← ht0c]
        have hv : colVal col5 = 0 := by rw [hc]; native_decide
        have h5 : colVal col5 = 5 := by native_decide
        omega
      have hcover : ∀ u : Fin 3, u = t1 ∨ u = t2 ∨ u = t0 := by
        intro u
        have hcu := hlin.1 u
        by_cases hz : colVal (D u) = 0
        · right; right
          exact eq_of_count_one hcnt0 hz (by rw [ht0c]; native_decide)
        · -- u has a nonzero type — u is t1 or t2 (the only nonzero positions)
          rcases hcu with h0 | h3 | h5 | h6
          · exfalso; exact hz h0
          · -- type 3: u = t1 (count 3 = 1)
            left
            have : u = t1 := eq_of_count_one h110.1 h3 ht1'
            exact this
          · -- type 5: u = t2
            right; left
            have : u = t2 := eq_of_count_one h110.2.1 h5 ht2'
            exact this
          · exfalso
            -- count 6 = 0 but u has type 6
            have hc6 : count D 6 = 0 := h110.2.2
            have hmem : u ∈ Finset.univ.filter fun t : Fin 3 => colVal (D t) = 6 := by simp [h6]
            have hpos : 0 < (Finset.univ.filter fun t : Fin 3 => colVal (D t) = 6).card :=
              Finset.card_pos.mpr ⟨u, hmem⟩
            rw [count_eq_card D 6] at hc6
            omega
      -- build the equivalence via the position permutation
      rcases fin3_perm_of_cover hcover hdist12 hdist01 hdist02 with ⟨p, hp0, hp1, hp2⟩
      refine Or.inl ⟨Equiv.refl (Fin 4), p, fun _ => false, ?_⟩
      intro u
      fin_cases u
      · simp [hp0, CA, ht1c, rowPermute_refl]
      · simp [hp1, CA, ht2c, rowPermute_refl]
      · simp [hp2, CA, ht0c, rowPermute_refl]
    · -- types (3,6): the row swap (2 3) maps col6 → col5 and fixes col3
      rcases exists_col0_of_count_pos D (by omega : 1 ≤ count D 0) with ⟨t0, ht0⟩
      rcases Finset.card_pos.mp (by
        have : 0 < count D 3 := by rw [h101.1]; omega
        rw [← count_eq_card D 3]
        exact this) with ⟨t1, ht1⟩
      rcases Finset.card_pos.mp (by
        have : 0 < count D 6 := by rw [h101.2.2]; omega
        rw [← count_eq_card D 6]
        exact this) with ⟨t2, ht2⟩
      have ht1' : colVal (D t1) = 3 := (Finset.mem_filter.mp ht1).2
      have ht2' : colVal (D t2) = 6 := (Finset.mem_filter.mp ht2).2
      have ht1c : D t1 = col3 := (colVal_eq_three_iff_col3 (D t1)).mp ht1'
      have ht2c : D t2 = col6 := (colVal_eq_six_iff_col6 (D t2)).mp ht2'
      have ht0c : D t0 = col0 := ht0
      have hdist12 : t1 ≠ t2 := by
        intro h
        subst t2
        have hc : col3 = col6 := by
          rw [← ht1c, ← ht2c]
        have h3 : colVal col3 = 3 := by native_decide
        have h6 : colVal col6 = 6 := by native_decide
        omega
      have hdist01 : t1 ≠ t0 := by
        intro h
        subst t0
        have hc : col3 = col0 := by
          rw [← ht1c, ← ht0c]
        have hv : colVal col3 = 0 := by rw [hc]; native_decide
        have h3 : colVal col3 = 3 := by native_decide
        omega
      have hdist02 : t2 ≠ t0 := by
        intro h
        subst t0
        have hc : col6 = col0 := by
          rw [← ht2c, ← ht0c]
        have hv : colVal col6 = 0 := by rw [hc]; native_decide
        have h6 : colVal col6 = 6 := by native_decide
        omega
      have hcover : ∀ u : Fin 3, u = t1 ∨ u = t2 ∨ u = t0 := by
        intro u
        have hcu := hlin.1 u
        by_cases hz : colVal (D u) = 0
        · right; right
          exact eq_of_count_one hcnt0 hz (by rw [ht0c]; native_decide)
        · rcases hcu with h0 | h3 | h5 | h6
          · exfalso; exact hz h0
          · left
            have : u = t1 := eq_of_count_one h101.1 h3 ht1'
            exact this
          · exfalso
            -- count 5 = 0 but u has type 5
            have hc5 : count D 5 = 0 := h101.2.1
            have hmem : u ∈ Finset.univ.filter fun t : Fin 3 => colVal (D t) = 5 := by simp [h5]
            have hpos : 0 < (Finset.univ.filter fun t : Fin 3 => colVal (D t) = 5).card :=
              Finset.card_pos.mpr ⟨u, hmem⟩
            rw [count_eq_card D 5] at hc5
            omega
          · right; left
            have : u = t2 := eq_of_count_one h101.2.2 h6 ht2'
            exact this
      rcases fin3_perm_of_cover hcover hdist12 hdist01 hdist02 with ⟨p, hp0, hp1, hp2⟩
      refine Or.inl ⟨Equiv.swap (2 : Fin 4) (3 : Fin 4), p, fun _ => false, ?_⟩
      intro u
      fin_cases u
      · simp [hp0, CA, ht1c, rowPermute_swap23_col3]
      · simp [hp1, CA, ht2c, rowPermute_swap23_col5]
      · simp [hp2, CA, ht0c, rowPermute_col0]
    · -- types (5,6): the row swap (1 3) maps col6 → col3 and fixes col5
      rcases exists_col0_of_count_pos D (by omega : 1 ≤ count D 0) with ⟨t0, ht0⟩
      rcases Finset.card_pos.mp (by
        have : 0 < count D 5 := by rw [h011.2.1]; omega
        rw [← count_eq_card D 5]
        exact this) with ⟨t1, ht1⟩
      rcases Finset.card_pos.mp (by
        have : 0 < count D 6 := by rw [h011.2.2]; omega
        rw [← count_eq_card D 6]
        exact this) with ⟨t2, ht2⟩
      have ht1' : colVal (D t1) = 5 := (Finset.mem_filter.mp ht1).2
      have ht2' : colVal (D t2) = 6 := (Finset.mem_filter.mp ht2).2
      have ht1c : D t1 = col5 := (colVal_eq_five_iff_col5 (D t1)).mp ht1'
      have ht2c : D t2 = col6 := (colVal_eq_six_iff_col6 (D t2)).mp ht2'
      have ht0c : D t0 = col0 := ht0
      have hdist12 : t1 ≠ t2 := by
        intro h
        subst t2
        have hc : col5 = col6 := by
          rw [← ht1c, ← ht2c]
        have h5 : colVal col5 = 5 := by native_decide
        have h6 : colVal col6 = 6 := by native_decide
        omega
      have hdist01 : t1 ≠ t0 := by
        intro h
        subst t0
        have hc : col5 = col0 := by
          rw [← ht1c, ← ht0c]
        have hv : colVal col5 = 0 := by rw [hc]; native_decide
        have h5 : colVal col5 = 5 := by native_decide
        omega
      have hdist02 : t2 ≠ t0 := by
        intro h
        subst t0
        have hc : col6 = col0 := by
          rw [← ht2c, ← ht0c]
        have hv : colVal col6 = 0 := by rw [hc]; native_decide
        have h6 : colVal col6 = 6 := by native_decide
        omega
      have hcover : ∀ u : Fin 3, u = t1 ∨ u = t2 ∨ u = t0 := by
        intro u
        have hcu := hlin.1 u
        by_cases hz : colVal (D u) = 0
        · right; right
          exact eq_of_count_one hcnt0 hz (by rw [ht0c]; native_decide)
        · rcases hcu with h0 | h3 | h5 | h6
          · exfalso; exact hz h0
          · exfalso
            -- count 3 = 0 but u has type 3
            have hc3 : count D 3 = 0 := h011.1
            have hmem : u ∈ Finset.univ.filter fun t : Fin 3 => colVal (D t) = 3 := by simp [h3]
            have hpos : 0 < (Finset.univ.filter fun t : Fin 3 => colVal (D t) = 3).card :=
              Finset.card_pos.mpr ⟨u, hmem⟩
            rw [count_eq_card D 3] at hc3
            omega
          · left
            have : u = t1 := eq_of_count_one h011.2.1 h5 ht1'
            exact this
          · right; left
            have : u = t2 := eq_of_count_one h011.2.2 h6 ht2'
            exact this
      rcases fin3_perm_of_cover hcover hdist12 hdist01 hdist02 with ⟨p, hp0, hp1, hp2⟩
      refine Or.inl ⟨(Equiv.swap (1 : Fin 4) (3 : Fin 4)).trans (Equiv.swap (1 : Fin 4) (2 : Fin 4)), p, fun _ => false, ?_⟩
      intro u
      fin_cases u
      · simp [hp0, CA, ht1c, rowPermute_cycle_col3_col5]
      · simp [hp1, CA, ht2c, rowPermute_cycle_col5_col6]
      · simp [hp2, CA, ht0c, rowPermute_col0]

/-- Theorem `thm:linearopt` (Theorem 2), n = 3: C_A, C(1,1,1), C(1,2,0) strictly dominate
every other non-equivalent linear code. -/
theorem linear_opt_n3 :
    ∀ D : Code 3, IsLinear D →
      ¬ Equivalent CA D → ¬ Equivalent (linearCode 1 1 1) D → ¬ Equivalent (linearCode 1 2 0) D →
        UniversalStrictBetter CA D ∧
          UniversalStrictBetter (linearCode 1 1 1) D ∧
            UniversalStrictBetter (linearCode 1 2 0) D := by
  intro D hlin hne1 hne2 hne3
  have hclass := linear3_classified D hlin
  rcases hclass with hc1 | hc2 | hc3
  · exact False.elim (hne1 hc1)
  · exact False.elim (hne2 hc2)
  · exact False.elim (hne3 hc3)
/-- `thm:linearopt` (Theorem 2) generic descent engine: given two λ-equal ideals `I1`, `I2`
and a verifier `rbase` for the terminal triples (spread ≤ 3), both ideals
strictly dominate every code with only types 3,5,6 that is not equivalent to
either (strong induction on the spread). -/
lemma linear_opt_engine {n : ℕ} (I1 I2 : Code n)
    (hEqI : UniversalEqual I1 I2)
    (rbase : ∀ A B C : ℕ, ∀ hsumABC : A + B + C = n, C ≤ B → B ≤ A → A - C ≤ 3 →
        ¬ Equivalent I1 (linCode A B C hsumABC) → ¬ Equivalent I2 (linCode A B C hsumABC) →
          UniversalStrictBetter I1 (linCode A B C hsumABC) ∧
          UniversalStrictBetter I2 (linCode A B C hsumABC)) :
    ∀ a b c : ℕ, ∀ hsum : a + b + c = n,
      ¬ Equivalent I1 (linCode a b c hsum) → ¬ Equivalent I2 (linCode a b c hsum) →
        UniversalStrictBetter I1 (linCode a b c hsum) ∧
        UniversalStrictBetter I2 (linCode a b c hsum) := by
  have hmain : ∀ s : ℕ, ∀ a b c : ℕ, ∀ hsum : a + b + c = n,
      max a (max b c) - min a (min b c) = s →
        ¬ Equivalent I1 (linCode a b c hsum) →
        ¬ Equivalent I2 (linCode a b c hsum) →
          UniversalStrictBetter I1 (linCode a b c hsum) ∧
          UniversalStrictBetter I2 (linCode a b c hsum) := by
    intro s
    induction s using Nat.strong_induction_on with
    | h s ih =>
      intro a b c hsum hspread hne1 hne2
      rcases linCode_sorted_equiv hsum with ⟨A, B, C, hsumABC, hord, hEqABC, hEq, hspEq⟩
      have hspABC : max A (max B C) - min A (min B C) = s := by
        rw [hspEq]
        exact hspread
      have hAC : A - C = s := by
        have hCA : C ≤ A := by omega
        have hred : max A (max B C) - min A (min B C) = A - C := by
          simp [hord, hEqABC, hCA]
        rw [← hred]
        exact hspABC
      have hne1S : ¬ Equivalent I1 (linCode A B C hsumABC) := by
        intro hc
        exact hne1 (equivalent_trans hc (equivalent_symm hEq))
      have hne2S : ¬ Equivalent I2 (linCode A B C hsumABC) := by
        intro hc
        exact hne2 (equivalent_trans hc (equivalent_symm hEq))
      by_cases hbase : A - C ≤ 3
      · -- base: the terminal triples
        have hb := rbase A B C hsumABC hord hEqABC hbase hne1S hne2S
        have htr : ∀ J : Code n, UniversalStrictBetter J (linCode A B C hsumABC) →
            UniversalStrictBetter J (linCode a b c hsum) := by
          intro J hJ
          exact universalStrictBetter_of_eq_left hJ
            (universalEqual_of_equivalent (linCode a b c hsum) (linCode A B C hsumABC) hEq)
        exact ⟨htr I1 hb.1, htr I2 hb.2⟩
      · -- descent: strictly better code with smaller spread
        have hsp4 : 4 ≤ A - C := by omega
        rcases linear_descent_step_ge4 ⟨hord, hEqABC⟩ hsumABC hsp4 with ⟨a', c', hsum', hspdec, hbetter⟩
        have hsp' : max a' (max B c') - min a' (min B c') < s := by omega
        have hIH := ih (max a' (max B c') - min a' (min B c')) hsp' a' B c' hsum' rfl
        have hIgtDs1 : UniversalStrictBetter I1 (linCode A B C hsumABC) := by
          by_cases hEq1' : Equivalent I1 (linCode a' B c' hsum')
          · exact universalStrictBetter_of_equiv_left (equivalent_symm hEq1') hbetter
          · by_cases hEq2' : Equivalent I2 (linCode a' B c' hsum')
            · have hI2gt : UniversalStrictBetter I2 (linCode A B C hsumABC) :=
                universalStrictBetter_of_equiv_left (equivalent_symm hEq2') hbetter
              exact universalStrictBetter_of_eq_right hEqI hI2gt
            · rcases hIH hEq1' hEq2' with ⟨h1, h2⟩
              exact universalStrictBetter_trans h1 hbetter
        have hIgtDs2 : UniversalStrictBetter I2 (linCode A B C hsumABC) := by
          by_cases hEq2' : Equivalent I2 (linCode a' B c' hsum')
          · exact universalStrictBetter_of_equiv_left (equivalent_symm hEq2') hbetter
          · by_cases hEq1' : Equivalent I1 (linCode a' B c' hsum')
            · have hI1gt : UniversalStrictBetter I1 (linCode A B C hsumABC) :=
                universalStrictBetter_of_equiv_left (equivalent_symm hEq1') hbetter
              exact universalStrictBetter_of_eq_right (universalEqual_symm hEqI) hI1gt
            · rcases hIH hEq1' hEq2' with ⟨h1, h2⟩
              exact universalStrictBetter_trans h2 hbetter
        have htr : ∀ J : Code n, UniversalStrictBetter J (linCode A B C hsumABC) →
            UniversalStrictBetter J (linCode a b c hsum) := by
          intro J hJ
          exact universalStrictBetter_of_eq_left hJ
            (universalEqual_of_equivalent (linCode a b c hsum) (linCode A B C hsumABC) hEq)
        exact ⟨htr I1 hIgtDs1, htr I2 hIgtDs2⟩
  intro a b c hsum hne1 hne2
  have hm := hmain (max a (max b c) - min a (min b c)) a b c hsum rfl hne1 hne2
  exact hm

/-- `thm:linearopt` (Theorem 2) engine for n = 3k: both ideals C(k+1,k+1,k−2) and
C(k+1,k,k−1) strictly dominate every linear code with only types 3,5,6 that
is not equivalent to either (strong induction on the spread). -/
lemma linear_opt_r0_triple {k n : ℕ} (hk : 2 ≤ k) (hn : n = k + 1 + k + (k - 1)) :
    ∀ a b c : ℕ, ∀ hsum : a + b + c = n,
      ¬ Equivalent (linCode (k + 1) (k + 1) (k - 2) (by omega)) (linCode a b c hsum) →
      ¬ Equivalent (linCode (k + 1) k (k - 1) (by omega)) (linCode a b c hsum) →
        UniversalStrictBetter (linCode (k + 1) (k + 1) (k - 2) (by omega)) (linCode a b c hsum) ∧
        UniversalStrictBetter (linCode (k + 1) k (k - 1) (by omega)) (linCode a b c hsum) := by
  let I1 : Code n := linCode (k + 1) (k + 1) (k - 2) (by omega)
  let I2 : Code n := linCode (k + 1) k (k - 1) (by omega)
  have hEqI : UniversalEqual I1 I2 := r0_ideals_equal hk hn (by omega) (by omega)
  have rbase : ∀ A B C : ℕ, ∀ hsumABC : A + B + C = n, C ≤ B → B ≤ A → A - C ≤ 3 →
      ¬ Equivalent I1 (linCode A B C hsumABC) → ¬ Equivalent I2 (linCode A B C hsumABC) →
        UniversalStrictBetter I1 (linCode A B C hsumABC) ∧
        UniversalStrictBetter I2 (linCode A B C hsumABC) := by
    intro A B C hsumABC hord1 hord2 hbase hne1 hne2
    rcases r0_base_cases hk ⟨hord1, hord2⟩ (by omega) hbase with hT | hT | hT | hT
    · rcases hT with ⟨hA, hB, hC⟩
      subst A
      subst B
      subst C
      have hdom2 : UniversalStrictBetter I2 (linCode k k k hsumABC) := by
        simpa [I2, linCode] using (r0_kkk_dominated hk hn hsumABC)
      exact ⟨universalStrictBetter_of_eq_right hEqI hdom2, hdom2⟩
    · rcases hT with ⟨hA, hB, hC⟩
      subst A
      subst B
      subst C
      have hEqI2 : Equivalent I2 (linCode (k + 1) k (k - 1) hsumABC) := by
        have hCastI2 : I2 = linCode (k + 1) k (k - 1) hsumABC := by
          dsimp [I2]
        rw [hCastI2]
        exact equivalent_refl _
      exact ⟨False.elim (hne2 hEqI2), False.elim (hne2 hEqI2)⟩
    · rcases hT with ⟨hA, hB, hC⟩
      subst A
      subst B
      subst C
      have hEqI1 : Equivalent I1 (linCode (k + 1) (k + 1) (k - 2) hsumABC) := by
        have hCastI1 : I1 = linCode (k + 1) (k + 1) (k - 2) hsumABC := by
          dsimp [I1]
        rw [hCastI1]
        exact equivalent_refl _
      exact ⟨False.elim (hne1 hEqI1), False.elim (hne1 hEqI1)⟩
    · rcases hT with ⟨hA, hB, hC⟩
      subst A
      subst B
      subst C
      have hdom2 : UniversalStrictBetter I2 (linCode (k + 2) (k - 1) (k - 1) hsumABC) := by
        simpa [I2, linCode] using (r0_kkkm1m1_dominated hk hn hsumABC)
      exact ⟨universalStrictBetter_of_eq_right hEqI hdom2, hdom2⟩
  intro a b c hsum hne1 hne2
  exact linear_opt_engine (I1 := I1) (I2 := I2) hEqI rbase a b c hsum hne1 hne2

/-- `thm:linearopt` (Theorem 2) engine for n = 3k+1: both ideals C(k+1,k,k) and
C(k+2,k,k−1) strictly dominate every linear code with only types 3,5,6 that
is not equivalent to either (strong induction on the spread). -/
lemma linear_opt_r1_triple {k n : ℕ} (hk : 1 ≤ k) (hn : n = k + 1 + k + k) :
    ∀ a b c : ℕ, ∀ hsum : a + b + c = n,
      ¬ Equivalent (linCode (k + 1) k k (by omega)) (linCode a b c hsum) →
      ¬ Equivalent (linCode (k + 2) k (k - 1) (by omega)) (linCode a b c hsum) →
        UniversalStrictBetter (linCode (k + 1) k k (by omega)) (linCode a b c hsum) ∧
        UniversalStrictBetter (linCode (k + 2) k (k - 1) (by omega)) (linCode a b c hsum) := by
  let I1 : Code n := linCode (k + 1) k k (by omega)
  let I2 : Code n := linCode (k + 2) k (k - 1) (by omega)
  have hEqI : UniversalEqual I1 I2 := r1_ideals_equal hk hn (by omega) (by omega)
  have rbase : ∀ A B C : ℕ, ∀ hsumABC : A + B + C = n, C ≤ B → B ≤ A → A - C ≤ 3 →
      ¬ Equivalent I1 (linCode A B C hsumABC) → ¬ Equivalent I2 (linCode A B C hsumABC) →
        UniversalStrictBetter I1 (linCode A B C hsumABC) ∧
        UniversalStrictBetter I2 (linCode A B C hsumABC) := by
    intro A B C hsumABC hord1 hord2 hbase hne1 hne2
    rcases r1_base_cases hk ⟨hord1, hord2⟩ (by omega) hbase with hT | hT | hT
    · rcases hT with ⟨hA, hB, hC⟩
      subst A
      subst B
      subst C
      have hEqI1 : Equivalent I1 (linCode (k + 1) k k hsumABC) := by
        have hCastI1 : I1 = linCode (k + 1) k k hsumABC := by
          dsimp [I1]
        rw [hCastI1]
        exact equivalent_refl _
      exact ⟨False.elim (hne1 hEqI1), False.elim (hne1 hEqI1)⟩
    · rcases hT with ⟨hA, hB, hC⟩
      subst A
      subst B
      subst C
      have hdom2 : UniversalStrictBetter I2 (linCode (k + 1) (k + 1) (k - 1) hsumABC) := by
        simpa [I2, linCode] using (r1_mid_dominated hk hn hsumABC)
      exact ⟨universalStrictBetter_of_eq_right hEqI hdom2, hdom2⟩
    · rcases hT with ⟨hA, hB, hC⟩
      subst A
      subst B
      subst C
      have hEqI2 : Equivalent I2 (linCode (k + 2) k (k - 1) hsumABC) := by
        have hCastI2 : I2 = linCode (k + 2) k (k - 1) hsumABC := by
          dsimp [I2]
        rw [hCastI2]
        exact equivalent_refl _
      exact ⟨False.elim (hne2 hEqI2), False.elim (hne2 hEqI2)⟩
  intro a b c hsum hne1 hne2
  exact linear_opt_engine (I1 := I1) (I2 := I2) hEqI rbase a b c hsum hne1 hne2

/-- `thm:linearopt` (Theorem 2) zero-column reduction: given two λ-equal linear ideals
with non-all-odd counts and an engine covering every non-equivalent
3/5/6-only code, any linear code with a zero column is strictly dominated by
both ideals (via `linear_zero_to_nozero`, the strict chain, and the all-odd
contradictions). -/
lemma residue_zero_column_dominated {n : ℕ} (I1 I2 : Code n)
    (hlinI1 : IsLinear I1) (hlinI2 : IsLinear I2)
    (hEqI : UniversalEqual I1 I2)
    (hnot1 : ¬ (Odd (count I1 3) ∧ Odd (count I1 5) ∧ Odd (count I1 6)))
    (hnot2 : ¬ (Odd (count I2 3) ∧ Odd (count I2 5) ∧ Odd (count I2 6)))
    (engine : ∀ a b c : ℕ, ∀ hsum : a + b + c = n,
        ¬ Equivalent I1 (linCode a b c hsum) → ¬ Equivalent I2 (linCode a b c hsum) →
          UniversalStrictBetter I1 (linCode a b c hsum) ∧
          UniversalStrictBetter I2 (linCode a b c hsum))
    {D : Code n} (hlin : IsLinear D) (hz : 1 ≤ count D 0)
    (_hne1 : ¬ Equivalent I1 D) (_hne2 : ¬ Equivalent I2 D) :
    UniversalStrictBetter I1 D ∧ UniversalStrictBetter I2 D := by
  rcases linear_zero_to_nozero D hlin hz with ⟨D', hlin', hz0, hbetter, hflag⟩
  have hEq' : Equivalent D'
      (linCode (count D' 3) (count D' 5) (count D' 6) (linear_count_sum_eq D' hlin' hz0)) := by
    simpa [linCode] using (linear_equiv_linearCode D' hlin' hz0)
  have hI1gtD : UniversalStrictBetter I1 D := by
    by_cases hEqI1 : Equivalent I1 D'
    · -- I1 ~ D': the strict chain or the all-odd contradiction gives I1 > D
      rcases hflag with hstrict | hallodd
      · have hID' : UniversalEqual I1 D' := universalEqual_of_equivalent D' I1 (equivalent_symm hEqI1)
        exact universalStrictBetter_of_eq_right hID' hstrict
      · exfalso
        have hoddI1 : Odd (count I1 3) ∧ Odd (count I1 5) ∧ Odd (count I1 6) :=
          all_odd_counts_of_equivalent (C := D') (C' := I1) hlin' hlinI1 (equivalent_symm hEqI1) hallodd
        exact hnot1 hoddI1
    · by_cases hEqI2 : Equivalent I2 D'
      · -- D' ~ I2: I2 > D (strict chain) or contradiction (all-odd)
        rcases hflag with hstrict | hallodd
        · have hI2gtD : UniversalStrictBetter I2 D := by
            have hID' : UniversalEqual I2 D' := universalEqual_of_equivalent D' I2 (equivalent_symm hEqI2)
            exact universalStrictBetter_of_eq_right hID' hstrict
          exact universalStrictBetter_of_eq_right hEqI hI2gtD
        · exfalso
          have hoddI2 : Odd (count I2 3) ∧ Odd (count I2 5) ∧ Odd (count I2 6) :=
            all_odd_counts_of_equivalent (C := D') (C' := I2) hlin' hlinI2 (equivalent_symm hEqI2) hallodd
          exact hnot2 hoddI2
      · -- neither ideal is equivalent to D': use the main descent on D'
        have hneC1' : ¬ Equivalent I1
            (linCode (count D' 3) (count D' 5) (count D' 6) (linear_count_sum_eq D' hlin' hz0)) := by
          intro hc
          exact hEqI1 (equivalent_trans hc (equivalent_symm hEq'))
        have hneC2' : ¬ Equivalent I2
            (linCode (count D' 3) (count D' 5) (count D' 6) (linear_count_sum_eq D' hlin' hz0)) := by
          intro hc
          exact hEqI2 (equivalent_trans hc (equivalent_symm hEq'))
        have hDom' := engine (count D' 3) (count D' 5) (count D' 6)
          (linear_count_sum_eq D' hlin' hz0) hneC1' hneC2'
        have hI1gtD' : UniversalStrictBetter I1 D' :=
          universalStrictBetter_of_eq_left hDom'.1
            (universalEqual_of_equivalent D' (linCode (count D' 3) (count D' 5) (count D' 6) (linear_count_sum_eq D' hlin' hz0)) hEq')
        exact universalStrictBetter_of_better_right hI1gtD' hbetter
  have hI2gtD : UniversalStrictBetter I2 D := by
    by_cases hEqI2 : Equivalent I2 D'
    · -- I2 ~ D': the strict chain or the all-odd contradiction gives I2 > D
      rcases hflag with hstrict | hallodd
      · have hID' : UniversalEqual I2 D' := universalEqual_of_equivalent D' I2 (equivalent_symm hEqI2)
        exact universalStrictBetter_of_eq_right hID' hstrict
      · exfalso
        have hoddI2 : Odd (count I2 3) ∧ Odd (count I2 5) ∧ Odd (count I2 6) :=
          all_odd_counts_of_equivalent (C := D') (C' := I2) hlin' hlinI2 (equivalent_symm hEqI2) hallodd
        exact hnot2 hoddI2
    · by_cases hEqI1 : Equivalent I1 D'
      · -- D' ~ I1: I1 > D (strict chain) or contradiction (all-odd)
        rcases hflag with hstrict | hallodd
        · have hI1gtD' : UniversalStrictBetter I1 D := by
            have hID' : UniversalEqual I1 D' := universalEqual_of_equivalent D' I1 (equivalent_symm hEqI1)
            exact universalStrictBetter_of_eq_right hID' hstrict
          exact universalStrictBetter_of_eq_right (universalEqual_symm hEqI) hI1gtD'
        · exfalso
          have hoddI1 : Odd (count I1 3) ∧ Odd (count I1 5) ∧ Odd (count I1 6) :=
            all_odd_counts_of_equivalent (C := D') (C' := I1) hlin' hlinI1 (equivalent_symm hEqI1) hallodd
          exact hnot1 hoddI1
      · -- neither ideal is equivalent to D': use the main descent on D'
        have hneC1' : ¬ Equivalent I1
            (linCode (count D' 3) (count D' 5) (count D' 6) (linear_count_sum_eq D' hlin' hz0)) := by
          intro hc
          exact hEqI1 (equivalent_trans hc (equivalent_symm hEq'))
        have hneC2' : ¬ Equivalent I2
            (linCode (count D' 3) (count D' 5) (count D' 6) (linear_count_sum_eq D' hlin' hz0)) := by
          intro hc
          exact hEqI2 (equivalent_trans hc (equivalent_symm hEq'))
        have hDom' := engine (count D' 3) (count D' 5) (count D' 6)
          (linear_count_sum_eq D' hlin' hz0) hneC1' hneC2'
        have hI2gtD' : UniversalStrictBetter I2 D' :=
          universalStrictBetter_of_eq_left hDom'.2
            (universalEqual_of_equivalent D' (linCode (count D' 3) (count D' 5) (count D' 6) (linear_count_sum_eq D' hlin' hz0)) hEq')
        exact universalStrictBetter_of_better_right hI2gtD' hbetter
  exact ⟨hI1gtD, hI2gtD⟩

/-- Theorem `thm:linearopt` (Theorem 2), n = 3k (k ≥ 2): C(k+1,k+1,k−2) and C(k+1,k,k−1)
strictly dominate every other non-equivalent linear code. -/
theorem linear_opt_residue0 {k : ℕ} (hk : k ≥ 2) :
    (∀ D : Code (k + 1 + k + (k - 1)), IsLinear D →
        ¬ Equivalent (linCode (k + 1) (k + 1) (k - 2) (by omega)) D →
        ¬ Equivalent (linCode (k + 1) k (k - 1) (by omega)) D →
          UniversalStrictBetter (linCode (k + 1) (k + 1) (k - 2) (by omega)) D) ∧
      (∀ D : Code (k + 1 + k + (k - 1)), IsLinear D →
        ¬ Equivalent (linCode (k + 1) (k + 1) (k - 2) (by omega)) D →
        ¬ Equivalent (linCode (k + 1) k (k - 1) (by omega)) D →
          UniversalStrictBetter (linCode (k + 1) k (k - 1) (by omega)) D) := by
  have hmain : ∀ D : Code (k + 1 + k + (k - 1)), IsLinear D →
      ¬ Equivalent (linCode (k + 1) (k + 1) (k - 2) (by omega)) D →
      ¬ Equivalent (linCode (k + 1) k (k - 1) (by omega)) D →
        UniversalStrictBetter (linCode (k + 1) (k + 1) (k - 2) (by omega)) D ∧
        UniversalStrictBetter (linCode (k + 1) k (k - 1) (by omega)) D := by
    intro D hlin hne1 hne2
    let I1 : Code (k + 1 + k + (k - 1)) := linCode (k + 1) (k + 1) (k - 2) (by omega)
    let I2 : Code (k + 1 + k + (k - 1)) := linCode (k + 1) k (k - 1) (by omega)
    have hEqI : UniversalEqual I1 I2 := r0_ideals_equal hk rfl (by omega) (by omega)
    have hlinI1 : IsLinear I1 := by
      exact isLinear_linCode (a := k + 1) (b := k + 1) (c := k - 2) (by omega) (by omega) (by omega)
    have hlinI2 : IsLinear I2 := by
      exact isLinear_linCode (a := k + 1) (b := k) (c := k - 1) (by omega) (by omega) (by omega)
    have hnot1 : ¬ (Odd (count I1 3) ∧ Odd (count I1 5) ∧ Odd (count I1 6)) := by
      have h3 : count I1 3 = k + 1 := by
        simpa [I1] using (count_linCode_3 (a := k + 1) (b := k + 1) (c := k - 2) (by omega))
      have h5 : count I1 5 = k + 1 := by
        simpa [I1] using (count_linCode_5 (a := k + 1) (b := k + 1) (c := k - 2) (by omega))
      have h6 : count I1 6 = k - 2 := by
        simpa [I1] using (count_linCode_6 (a := k + 1) (b := k + 1) (c := k - 2) (by omega))
      rintro ⟨o3, o5, o6⟩
      have hn3 : Odd (k + 1) := by simpa [h3] using o3
      have hn5 : Odd (k + 1) := by simpa [h5] using o5
      have hn6 : Odd (k - 2) := by simpa [h6] using o6
      exact not_all_odd_ideal_r0a hk ⟨hn3, hn5, hn6⟩
    have hnot2 : ¬ (Odd (count I2 3) ∧ Odd (count I2 5) ∧ Odd (count I2 6)) := by
      have h3 : count I2 3 = k + 1 := by
        simpa [I2] using (count_linCode_3 (a := k + 1) (b := k) (c := k - 1) (by omega))
      have h5 : count I2 5 = k := by
        simpa [I2] using (count_linCode_5 (a := k + 1) (b := k) (c := k - 1) (by omega))
      have h6 : count I2 6 = k - 1 := by
        simpa [I2] using (count_linCode_6 (a := k + 1) (b := k) (c := k - 1) (by omega))
      rintro ⟨o3, o5, o6⟩
      have hn3 : Odd (k + 1) := by simpa [h3] using o3
      have hn5 : Odd k := by simpa [h5] using o5
      have hn6 : Odd (k - 1) := by simpa [h6] using o6
      exact not_all_odd_ideal_r0b hk ⟨hn3, hn5, hn6⟩
    by_cases hz : count D 0 = 0
    · -- no zero columns: normalize to the canonical counts
      have hEq : Equivalent D
          (linCode (count D 3) (count D 5) (count D 6) (linear_count_sum_eq D hlin hz)) := by
        simpa [linCode] using (linear_equiv_linearCode D hlin hz)
      have hCastI1 : I1 = linCode (k + 1) (k + 1) (k - 2) (by omega) := by dsimp [I1]
      have hCastI2 : I2 = linCode (k + 1) k (k - 1) (by omega) := by dsimp [I2]
      have hneC1 : ¬ Equivalent I1
          (linCode (count D 3) (count D 5) (count D 6) (linear_count_sum_eq D hlin hz)) := by
        intro hc
        have hc' : Equivalent (linCode (k + 1) (k + 1) (k - 2) (by omega))
            (linCode (count D 3) (count D 5) (count D 6) (linear_count_sum_eq D hlin hz)) := by
          rw [← hCastI1]
          exact hc
        exact hne1 (equivalent_trans hc' (equivalent_symm hEq))
      have hneC2 : ¬ Equivalent I2
          (linCode (count D 3) (count D 5) (count D 6) (linear_count_sum_eq D hlin hz)) := by
        intro hc
        have hc' : Equivalent (linCode (k + 1) k (k - 1) (by omega))
            (linCode (count D 3) (count D 5) (count D 6) (linear_count_sum_eq D hlin hz)) := by
          rw [← hCastI2]
          exact hc
        exact hne2 (equivalent_trans hc' (equivalent_symm hEq))
      have hDom := linear_opt_r0_triple hk rfl (count D 3) (count D 5) (count D 6)
        (linear_count_sum_eq D hlin hz) hneC1 hneC2
      have hDom1 : UniversalStrictBetter I1 D :=
        universalStrictBetter_of_eq_left hDom.1
          (universalEqual_of_equivalent D (linCode (count D 3) (count D 5) (count D 6) (linear_count_sum_eq D hlin hz)) hEq)
      have hDom2 : UniversalStrictBetter I2 D :=
        universalStrictBetter_of_eq_left hDom.2
          (universalEqual_of_equivalent D (linCode (count D 3) (count D 5) (count D 6) (linear_count_sum_eq D hlin hz)) hEq)
      exact ⟨hDom1, hDom2⟩
    · -- zero columns: reduce to a zero-column-free code first
      have hz1 : count D 0 ≥ 1 := by omega
      exact residue_zero_column_dominated (I1 := I1) (I2 := I2) hlinI1 hlinI2 hEqI hnot1 hnot2
        (linear_opt_r0_triple hk rfl) hlin hz1 hne1 hne2
  constructor
  · intro D hlin hne1 hne2
    exact (hmain D hlin hne1 hne2).1
  · intro D hlin hne1 hne2
    exact (hmain D hlin hne1 hne2).2

/-- Theorem `thm:linearopt` (Theorem 2), n = 3k+1 (k ≥ 1): C(k+1,k,k) and C(k+2,k,k−1)
strictly dominate every other non-equivalent linear code. -/
theorem linear_opt_residue1 {k : ℕ} (hk : k ≥ 1) :
    (∀ D : Code (k + 1 + k + k), IsLinear D →
        ¬ Equivalent (linCode (k + 1) k k (by omega)) D →
        ¬ Equivalent (linCode (k + 2) k (k - 1) (by omega)) D →
          UniversalStrictBetter (linCode (k + 1) k k (by omega)) D) ∧
      (∀ D : Code (k + 1 + k + k), IsLinear D →
        ¬ Equivalent (linCode (k + 1) k k (by omega)) D →
        ¬ Equivalent (linCode (k + 2) k (k - 1) (by omega)) D →
          UniversalStrictBetter (linCode (k + 2) k (k - 1) (by omega)) D) := by
  have hmain : ∀ D : Code (k + 1 + k + k), IsLinear D →
      ¬ Equivalent (linCode (k + 1) k k (by omega)) D →
      ¬ Equivalent (linCode (k + 2) k (k - 1) (by omega)) D →
        UniversalStrictBetter (linCode (k + 1) k k (by omega)) D ∧
        UniversalStrictBetter (linCode (k + 2) k (k - 1) (by omega)) D := by
    intro D hlin hne1 hne2
    let I1 : Code (k + 1 + k + k) := linCode (k + 1) k k (by omega)
    let I2 : Code (k + 1 + k + k) := linCode (k + 2) k (k - 1) (by omega)
    have hEqI : UniversalEqual I1 I2 := r1_ideals_equal hk rfl (by omega) (by omega)
    have hlinI1 : IsLinear I1 := by
      exact isLinear_linCode (a := k + 1) (b := k) (c := k) (by omega) (by omega) (by omega)
    have hlinI2 : IsLinear I2 := by
      exact isLinear_linCode (a := k + 2) (b := k) (c := k - 1) (by omega) (by omega) (by omega)
    have hnot1 : ¬ (Odd (count I1 3) ∧ Odd (count I1 5) ∧ Odd (count I1 6)) := by
      have h3 : count I1 3 = k + 1 := by
        simpa [I1] using (count_linCode_3 (a := k + 1) (b := k) (c := k) (by omega))
      have h5 : count I1 5 = k := by
        simpa [I1] using (count_linCode_5 (a := k + 1) (b := k) (c := k) (by omega))
      have h6 : count I1 6 = k := by
        simpa [I1] using (count_linCode_6 (a := k + 1) (b := k) (c := k) (by omega))
      rintro ⟨o3, o5, o6⟩
      have hn3 : Odd (k + 1) := by simpa [h3] using o3
      have hn5 : Odd k := by simpa [h5] using o5
      have hn6 : Odd k := by simpa [h6] using o6
      exact not_all_odd_ideal_r1a hk ⟨hn3, hn5, hn6⟩
    have hnot2 : ¬ (Odd (count I2 3) ∧ Odd (count I2 5) ∧ Odd (count I2 6)) := by
      have h3 : count I2 3 = k + 2 := by
        simpa [I2] using (count_linCode_3 (a := k + 2) (b := k) (c := k - 1) (by omega))
      have h5 : count I2 5 = k := by
        simpa [I2] using (count_linCode_5 (a := k + 2) (b := k) (c := k - 1) (by omega))
      have h6 : count I2 6 = k - 1 := by
        simpa [I2] using (count_linCode_6 (a := k + 2) (b := k) (c := k - 1) (by omega))
      rintro ⟨o3, o5, o6⟩
      have hn3 : Odd (k + 2) := by simpa [h3] using o3
      have hn5 : Odd k := by simpa [h5] using o5
      have hn6 : Odd (k - 1) := by simpa [h6] using o6
      exact not_all_odd_ideal_r1b hk ⟨hn3, hn5, hn6⟩
    by_cases hz : count D 0 = 0
    · -- no zero columns: normalize to the canonical counts
      have hEq : Equivalent D
          (linCode (count D 3) (count D 5) (count D 6) (linear_count_sum_eq D hlin hz)) := by
        simpa [linCode] using (linear_equiv_linearCode D hlin hz)
      have hCastI1 : I1 = linCode (k + 1) k k (by omega) := by dsimp [I1]
      have hCastI2 : I2 = linCode (k + 2) k (k - 1) (by omega) := by dsimp [I2]
      have hneC1 : ¬ Equivalent I1
          (linCode (count D 3) (count D 5) (count D 6) (linear_count_sum_eq D hlin hz)) := by
        intro hc
        have hc' : Equivalent (linCode (k + 1) k k (by omega))
            (linCode (count D 3) (count D 5) (count D 6) (linear_count_sum_eq D hlin hz)) := by
          rw [← hCastI1]
          exact hc
        exact hne1 (equivalent_trans hc' (equivalent_symm hEq))
      have hneC2 : ¬ Equivalent I2
          (linCode (count D 3) (count D 5) (count D 6) (linear_count_sum_eq D hlin hz)) := by
        intro hc
        have hc' : Equivalent (linCode (k + 2) k (k - 1) (by omega))
            (linCode (count D 3) (count D 5) (count D 6) (linear_count_sum_eq D hlin hz)) := by
          rw [← hCastI2]
          exact hc
        exact hne2 (equivalent_trans hc' (equivalent_symm hEq))
      have hDom := linear_opt_r1_triple hk rfl (count D 3) (count D 5) (count D 6)
        (linear_count_sum_eq D hlin hz) hneC1 hneC2
      have hDom1 : UniversalStrictBetter I1 D :=
        universalStrictBetter_of_eq_left hDom.1
          (universalEqual_of_equivalent D (linCode (count D 3) (count D 5) (count D 6) (linear_count_sum_eq D hlin hz)) hEq)
      have hDom2 : UniversalStrictBetter I2 D :=
        universalStrictBetter_of_eq_left hDom.2
          (universalEqual_of_equivalent D (linCode (count D 3) (count D 5) (count D 6) (linear_count_sum_eq D hlin hz)) hEq)
      exact ⟨hDom1, hDom2⟩
    · -- zero columns: reduce to a zero-column-free code first
      have hz1 : count D 0 ≥ 1 := by omega
      exact residue_zero_column_dominated (I1 := I1) (I2 := I2) hlinI1 hlinI2 hEqI hnot1 hnot2
        (linear_opt_r1_triple hk rfl) hlin hz1 hne1 hne2
  constructor
  · intro D hlin hne1 hne2
    exact (hmain D hlin hne1 hne2).1
  · intro D hlin hne1 hne2
    exact (hmain D hlin hne1 hne2).2

end N4Code
