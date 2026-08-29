import N4Code.Comparison
import Mathlib.Tactic.FieldSimp

/-!
# Phase C: the paper's one-column comparison machinery

The generic comparison engine (`thm:com` (Lemma 18) and its strict/equality variants)
lives in `N4Code.Comparison`; this module derives the paper-specific
`lemma:1` (Lemma 19) Y/Z-region machinery, the exact one-column λ-difference
(`the:1` (Theorem 20)), and the cumulative criterion (`cor:1` (Corollary 21)) on top of it.
-/

namespace N4Code

/-! ## Lemma `lemma:1` (Lemma 19) distance machinery -/

/-- Flipping the same bit twice is the identity. -/
lemma flipBit_involutive {n : ℕ} (t : Fin n) (y : Word n) : flipBit t (flipBit t y) = y := by
  funext u
  by_cases h : u = t <;> simp [flipBit, h]

/-- Split a finite sum at one index. -/
lemma sum_split_at {n : ℕ} (f : Fin n → ℕ) (t : Fin n) :
    (∑ u : Fin n, f u) = (∑ u ∈ (Finset.univ.erase t), f u) + f t := by
  exact (Finset.sum_erase_add (Finset.univ : Finset (Fin n)) f (Finset.mem_univ t)).symm

/-- Flipping one bit changes each row distance by at most one. -/
lemma dRow_flip_le_add_one {n : ℕ} (C : Code n) (i : Fin 4) (t : Fin n) (y : Word n) :
    dRow C i (flipBit t y) ≤ dRow C i y + 1 ∧ dRow C i y ≤ dRow C i (flipBit t y) + 1 := by
  rw [dRow_eq_indicator_sum, dRow_eq_indicator_sum]
  have hsplit_new := sum_split_at
    (fun u : Fin n => if colBit i (C u) ≠ flipBit t y u then 1 else 0) t
  have hsplit_old := sum_split_at
    (fun u : Fin n => if colBit i (C u) ≠ y u then 1 else 0) t
  have hS : (∑ u ∈ (Finset.univ.erase t), if colBit i (C u) ≠ flipBit t y u then 1 else 0) =
      ∑ u ∈ (Finset.univ.erase t), if colBit i (C u) ≠ y u then 1 else 0 := by
    apply Finset.sum_congr rfl
    intro u hu
    have ht : u ≠ t := (Finset.mem_erase.mp hu).1
    simp [flipBit, ht]
  have hnewt : (if colBit i (C t) ≠ flipBit t y t then 1 else 0) ≤
      (if colBit i (C t) ≠ y t then 1 else 0) + 1 := by
    by_cases h : colBit i (C t) = y t <;> by_cases h2 : colBit i (C t) ≠ flipBit t y t <;>
      simp [flipBit, h]
  have holdt : (if colBit i (C t) ≠ y t then 1 else 0) ≤
      (if colBit i (C t) ≠ flipBit t y t then 1 else 0) + 1 := by
    by_cases h : colBit i (C t) = flipBit t y t <;> by_cases h2 : colBit i (C t) ≠ y t <;>
      simp [flipBit, h, h2]
  constructor
  · rw [hsplit_new, hsplit_old, hS]
    omega
  · rw [hsplit_old, hsplit_new, hS]
    omega

lemma min3_add_one (a b c : ℕ) : min (a + 1) (min (b + 1) (c + 1)) = min a (min b c) + 1 := by
  omega

lemma min3_le_add_one {a b c a' b' c' : ℕ} (h1 : a' ≤ a + 1) (h2 : b' ≤ b + 1)
    (h3 : c' ≤ c + 1) : min a' (min b' c') ≤ min a (min b c) + 1 := by
  calc
    min a' (min b' c') ≤ min (a + 1) (min (b + 1) (c + 1)) := by
      apply le_min
      · exact le_trans (Nat.min_le_left _ _) h1
      · apply le_min
        · exact le_trans (Nat.min_le_right _ _) (le_trans (Nat.min_le_left _ _) h2)
        · exact le_trans (Nat.min_le_right _ _) (le_trans (Nat.min_le_right _ _) h3)
    _ = min a (min b c) + 1 := min3_add_one a b c

lemma dOp_le_dO_add_one {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) :
    dOp C t y ≤ dO C y + 1 := by
  unfold dOp dO
  apply min3_le_add_one
  · exact (dRow_flip_le_add_one C ⟨0, by decide⟩ t y).1
  · exact (dRow_flip_le_add_one C ⟨1, by decide⟩ t y).1
  · exact (dRow_flip_le_add_one C ⟨3, by decide⟩ t y).1

lemma dO_le_dOp_add_one {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) :
    dO C y ≤ dOp C t y + 1 := by
  unfold dOp dO
  apply min3_le_add_one
  · exact (dRow_flip_le_add_one C ⟨0, by decide⟩ t y).2
  · exact (dRow_flip_le_add_one C ⟨1, by decide⟩ t y).2
  · exact (dRow_flip_le_add_one C ⟨3, by decide⟩ t y).2

lemma dPp_le_dP_add_one {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) :
    dPp C t y ≤ dP C y + 1 := by
  unfold dPp dP
  exact (dRow_flip_le_add_one C ⟨2, by decide⟩ t y).1

lemma dP_le_dPp_add_one {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) :
    dP C y ≤ dPp C t y + 1 := by
  unfold dPp dP
  exact (dRow_flip_le_add_one C ⟨2, by decide⟩ t y).2

/-- d_C(y) = min(d_O(y), d_P(y)) (paper eq. dc). -/
lemma dCode_eq_min_dO_dP {n : ℕ} (C : Code n) (y : Word n) :
    dCode C y = min (dO C y) (dP C y) := by
  unfold dCode dO dP
  omega

/-- Replacing a type-1 column by type 3 changes only the P row. -/
lemma dRow_replace_2 {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) (hcol : C t = col1) :
    dRow (replaceColumn C t col3) ⟨2, by decide⟩ y = dRow C ⟨2, by decide⟩ (flipBit t y) := by
  rw [dRow_eq_indicator_sum, dRow_eq_indicator_sum]
  apply Finset.sum_congr rfl
  intro u _
  by_cases h : u = t <;> by_cases hy : y t = true <;>
    simp [replaceColumn, flipBit, colBit, col1, col3, h, hcol, hy]

lemma dRow_replace_eq {n : ℕ} (C : Code n) (t : Fin n) (j : Fin 4) (y : Word n)
    (hcol : C t = col1) (hj : j ≠ 2) :
    dRow (replaceColumn C t col3) j y = dRow C j y := by
  rw [dRow_eq_indicator_sum, dRow_eq_indicator_sum]
  apply Finset.sum_congr rfl
  intro u _
  by_cases h : u = t <;> simp [replaceColumn, h]
  · have hb : colBit j col3 = colBit j col1 := by
      fin_cases j <;> simp [colBit, col1, col3] at hj ⊢
    rw [hcol, hb]

/-- d_{C'}(y) = min(d_O(y), d_P'(y)) for the one-column change (paper eq. dcp). -/
lemma dCode_replace_1_3 {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) (hcol : C t = col1) :
    dCode (replaceColumn C t col3) y = min (dO C y) (dPp C t y) := by
  unfold dCode dO dPp dP
  change min (dRow (replaceColumn C t col3) ⟨0, by decide⟩ y)
      (min (dRow (replaceColumn C t col3) ⟨1, by decide⟩ y)
        (min (dRow (replaceColumn C t col3) ⟨2, by decide⟩ y)
          (dRow (replaceColumn C t col3) ⟨3, by decide⟩ y))) =
    min (min (dRow C ⟨0, by decide⟩ y) (min (dRow C ⟨1, by decide⟩ y) (dRow C ⟨3, by decide⟩ y)))
      (dRow C ⟨2, by decide⟩ (flipBit t y))
  rw [dRow_replace_eq C t ⟨0, by decide⟩ y hcol (by decide),
    dRow_replace_eq C t ⟨1, by decide⟩ y hcol (by decide),
    dRow_replace_2 C t y hcol,
    dRow_replace_eq C t ⟨3, by decide⟩ y hcol (by decide)]
  omega

/-- d_{C'}(F_1 y) = min(d_O'(y), d_P(y)) (paper eq. dcpf). -/
lemma dCode_replace_flip {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) (hcol : C t = col1) :
    dCode (replaceColumn C t col3) (flipBit t y) = min (dOp C t y) (dP C y) := by
  rw [dCode_replace_1_3 C t (flipBit t y) hcol]
  unfold dOp dPp
  rw [flipBit_involutive]

/-- C' is exactly the replacement of column t by type 3. -/
lemma replace_1_3_eq {n : ℕ} (C C' : Code n) (t : Fin n) (hcol' : C' t = col3)
    (hsame : ∀ u : Fin n, u ≠ t → C' u = C u) :
    C' = replaceColumn C t col3 := by
  funext u
  by_cases hu : u = t <;> simp [replaceColumn, hu, hcol', hsame]

/-! ## Lemma `lemma:1` (Lemma 19), claims 1)–5) -/

/-- Lemma `lemma:1` (Lemma 19) (1): y ∈ Y1 → d_C(y) = d_C'(y) = d_O. -/
theorem y_rel_1 {n : ℕ} (C C' : Code n) (t : Fin n) (hcol : C t = col1)
    (hcol' : C' t = col3) (hsame : ∀ u : Fin n, u ≠ t → C' u = C u)
    {y : Word n} (hy : Y1 C t y) :
    dCode C y = dCode C' y ∧ dCode C y = dO C y := by
  have hrep : C' = replaceColumn C t col3 := replace_1_3_eq C C' t hcol' hsame
  have hdC : dCode C y = min (dO C y) (dP C y) := dCode_eq_min_dO_dP C y
  have hdC' : dCode C' y = min (dO C y) (dPp C t y) := by
    rw [hrep, dCode_replace_1_3 C t y hcol]
  rcases hy with hy | hy
  · rcases hy with ⟨h1, h2⟩
    have hdOp : dO C y ≤ dPp C t y := le_trans h1 (le_of_lt h2)
    constructor
    · rw [hdC, hdC', min_eq_left h1, min_eq_left hdOp]
    · rw [hdC, min_eq_left h1]
  · rcases hy with ⟨h1, h2, h3⟩
    have hdP : dO C y ≤ dP C y := le_trans h1 h2
    constructor
    · rw [hdC, hdC', min_eq_left hdP, min_eq_left h1]
    · rw [hdC, min_eq_left hdP]

/-- Lemma `lemma:1` (Lemma 19) (2): y ∈ Y2 → d_C(y) = d_C'(F1 y) = d_P. -/
theorem y_rel_2 {n : ℕ} (C C' : Code n) (t : Fin n) (hcol : C t = col1)
    (hcol' : C' t = col3) (hsame : ∀ u : Fin n, u ≠ t → C' u = C u)
    {y : Word n} (hy : Y2 C t y) :
    dCode C y = dCode C' (flipBit t y) ∧ dCode C y = dP C y := by
  have hrep : C' = replaceColumn C t col3 := replace_1_3_eq C C' t hcol' hsame
  have hdC : dCode C y = min (dO C y) (dP C y) := dCode_eq_min_dO_dP C y
  have hdC'f : dCode C' (flipBit t y) = min (dOp C t y) (dP C y) := by
    rw [hrep, dCode_replace_flip C t y hcol]
  rcases hy with hy | hy
  · rcases hy with ⟨h1, h2⟩
    have hdP : dP C y ≤ dO C y := le_of_lt h2
    have hdPo : dP C y ≤ dOp C t y := by
      have h := dO_le_dOp_add_one C t y
      omega
    constructor
    · rw [hdC, hdC'f, min_eq_right hdP, min_eq_right hdPo]
    · rw [hdC, min_eq_right hdP]
  · rcases hy with ⟨h1, h2, h3⟩
    constructor
    · rw [hdC, hdC'f, min_eq_right h2, min_eq_right h3]
    · rw [hdC, min_eq_right h2]

/-- Lemma `lemma:1` (Lemma 19) (3): y ∈ Y3 → d_C(y) = d_P = d_C'(y) + 1. -/
theorem y_rel_3 {n : ℕ} (C C' : Code n) (t : Fin n) (hcol : C t = col1)
    (hcol' : C' t = col3) (hsame : ∀ u : Fin n, u ≠ t → C' u = C u)
    {y : Word n} (hy : Y3 C t y) :
    dCode C y = dP C y ∧ dCode C y = dCode C' y + 1 := by
  have hrep : C' = replaceColumn C t col3 := replace_1_3_eq C C' t hcol' hsame
  have hdC : dCode C y = min (dO C y) (dP C y) := dCode_eq_min_dO_dP C y
  have hdC' : dCode C' y = min (dO C y) (dPp C t y) := by
    rw [hrep, dCode_replace_1_3 C t y hcol]
  rcases hy with ⟨h1, h2, h3⟩
  have hdP : dCode C y = dP C y := by
    rw [hdC]
    rw [← h3]
    simp
  have hdC'p : dCode C' y = dPp C t y := by
    rw [hdC', min_eq_right (le_of_lt (lt_of_lt_of_eq h2 h3))]
  constructor
  · exact hdP
  · rw [hdP, hdC'p]
    have h := dP_le_dPp_add_one C t y
    omega

/-- Lemma `lemma:1` (Lemma 19) (4): y ∈ Y4 → d_C(y) = d_O = d_C'(F1 y) = d_P. -/
theorem y_rel_4 {n : ℕ} (C C' : Code n) (t : Fin n) (hcol : C t = col1)
    (hcol' : C' t = col3) (hsame : ∀ u : Fin n, u ≠ t → C' u = C u)
    {y : Word n} (hy : Y4 C t y) :
    dCode C y = dO C y ∧ dCode C y = dCode C' (flipBit t y) ∧
      dCode C' (flipBit t y) = dP C y := by
  have hrep : C' = replaceColumn C t col3 := replace_1_3_eq C C' t hcol' hsame
  have hdC : dCode C y = min (dO C y) (dP C y) := dCode_eq_min_dO_dP C y
  have hdC'f : dCode C' (flipBit t y) = min (dOp C t y) (dP C y) := by
    rw [hrep, dCode_replace_flip C t y hcol]
  rcases hy with ⟨h1, h2, h3⟩
  have hdO : dCode C y = dO C y := by
    rw [hdC]
    rw [h1, h2]
    simp
  have hdP' : dCode C' (flipBit t y) = dP C y := by
    rw [hdC'f]
    have hle : dP C y ≤ dOp C t y := by
      have hd : dP C y = dO C y := h1.trans h2
      rw [hd]
      exact le_of_lt h3
    rw [min_eq_right hle]
  constructor
  · exact hdO
  · constructor
    · rw [hdO, hdP']
      exact (h1.trans h2).symm
    · exact hdP'

/-- Lemma `lemma:1` (Lemma 19) (5): y ∈ Y5 → d_C(y) + 1 = d_C'(F1 y) = d_P. -/
theorem y_rel_5 {n : ℕ} (C C' : Code n) (t : Fin n) (hcol : C t = col1)
    (hcol' : C' t = col3) (hsame : ∀ u : Fin n, u ≠ t → C' u = C u)
    {y : Word n} (hy : Y5 C t y) :
    dCode C y + 1 = dCode C' (flipBit t y) ∧ dCode C' (flipBit t y) = dP C y := by
  have hrep : C' = replaceColumn C t col3 := replace_1_3_eq C C' t hcol' hsame
  have hdC : dCode C y = min (dO C y) (dP C y) := dCode_eq_min_dO_dP C y
  have hdC'f : dCode C' (flipBit t y) = min (dOp C t y) (dP C y) := by
    rw [hrep, dCode_replace_flip C t y hcol]
  rcases hy with ⟨h1, h2, h3⟩
  have hdO : dCode C y = dO C y := by
    rw [hdC]
    have hle : dO C y ≤ dP C y := le_of_lt (lt_of_lt_of_eq h3 h2)
    rw [min_eq_left hle]
  have hdP' : dCode C' (flipBit t y) = dP C y := by
    rw [hdC'f, h2]
    simp
  constructor
  · rw [hdO, hdP']
    have h := dOp_le_dO_add_one C t y
    omega
  · exact hdP'

/-! ## Lemma `lemma:1` (Lemma 19): the partition -/

/-- Y1 ∪ Y4 ∪ Y5 = {y : d_O ≤ d_P ∧ d_P'} (paper eq. lemma5a). -/
lemma Y1_or_Y4_or_Y5_iff {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) :
    (Y1 C t y ∨ Y4 C t y ∨ Y5 C t y) ↔ dO C y ≤ min (dP C y) (dPp C t y) := by
  have h1 := dOp_le_dO_add_one C t y
  have h2 := dO_le_dOp_add_one C t y
  have h3 := dPp_le_dP_add_one C t y
  have h4 := dP_le_dPp_add_one C t y
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
    have hdP : dO C y ≤ dP C y := (le_min_iff.mp h).1
    have hdPp : dO C y ≤ dPp C t y := (le_min_iff.mp h).2
    by_cases hcmp : dP C y < dPp C t y
    · exact Or.inl (Or.inl ⟨hdP, hcmp⟩)
    · have hdPp_le : dPp C t y ≤ dP C y := le_of_not_gt hcmp
      by_cases hop : dOp C t y ≤ dPp C t y
      · exact Or.inl (Or.inr ⟨hdPp, hdPp_le, hop⟩)
      · have hop' : dPp C t y < dOp C t y := lt_of_not_ge hop
        by_cases heq : dPp C t y = dP C y
        · have hdO_eq : dPp C t y = dO C y := by omega
          exact Or.inr (Or.inl ⟨heq.symm, hdO_eq, by omega⟩)
        · have hdPp_lt : dPp C t y < dP C y := lt_of_le_of_ne hdPp_le heq
          have hdO_eq : dPp C t y = dO C y := by omega
          have hdOp_eq : dOp C t y = dP C y := by omega
          exact Or.inr (Or.inr ⟨hdO_eq, hdOp_eq, by omega⟩)

/-- Y2 ∪ Y3 = {y : d_O > d_P ∧ d_P'}. -/
lemma Y2_or_Y3_iff {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) :
    (Y2 C t y ∨ Y3 C t y) ↔ dO C y > min (dP C y) (dPp C t y) := by
  have h1 := dOp_le_dO_add_one C t y
  have h2 := dO_le_dOp_add_one C t y
  have h3 := dPp_le_dP_add_one C t y
  have h4 := dP_le_dPp_add_one C t y
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
    have hgt : min (dP C y) (dPp C t y) < dO C y := h
    by_cases hcmp : dP C y < dPp C t y
    · have hdP : dP C y < dO C y := by
        rw [min_eq_left (le_of_lt hcmp)] at hgt
        exact hgt
      exact Or.inl (Or.inl ⟨le_of_lt hcmp, hdP⟩)
    · have hdPp_le : dPp C t y ≤ dP C y := le_of_not_gt hcmp
      by_cases heq : dPp C t y = dP C y
      · have hdP : dP C y < dO C y := by
          rw [heq] at hgt
          simpa using hgt
        exact Or.inl (Or.inl ⟨le_of_eq heq.symm, hdP⟩)
      · have hdPp_lt : dPp C t y < dP C y := lt_of_le_of_ne hdPp_le heq
        have hdPp_lt_dO : dPp C t y < dO C y := by
          rw [min_eq_right (le_of_lt hdPp_lt)] at hgt
          exact hgt
        by_cases hop : dOp C t y ≤ dPp C t y
        · have hdOp_eq : dOp C t y = dPp C t y := by omega
          have hdP_eq : dP C y = dO C y := by omega
          exact Or.inr ⟨hdOp_eq.symm, hdPp_lt, hdP_eq⟩
        · have hdP_le_dO : dP C y ≤ dO C y := by omega
          have hdP_le_dOp : dP C y ≤ dOp C t y := by omega
          exact Or.inl (Or.inr ⟨hdPp_lt, hdP_le_dO, hdP_le_dOp⟩)

lemma Y1_Y4_disjoint {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) :
    ¬ (Y1 C t y ∧ Y4 C t y) := by
  rintro ⟨hy1, hy4⟩
  rcases hy4 with ⟨h4a, h4b, h4c⟩
  rcases hy1 with hy1 | hy1
  · rcases hy1 with ⟨h1a, h1b⟩
    omega
  · rcases hy1 with ⟨h1a, h1b, h1c⟩
    omega

lemma Y1_Y5_disjoint {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) :
    ¬ (Y1 C t y ∧ Y5 C t y) := by
  rintro ⟨hy1, hy5⟩
  rcases hy5 with ⟨h5a, h5b, h5c⟩
  rcases hy1 with hy1 | hy1
  · rcases hy1 with ⟨h1a, h1b⟩
    omega
  · rcases hy1 with ⟨h1a, h1b, h1c⟩
    omega

lemma Y4_Y5_disjoint {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) :
    ¬ (Y4 C t y ∧ Y5 C t y) := by
  have h1 := dOp_le_dO_add_one C t y
  rintro ⟨hy4, hy5⟩
  rcases hy4 with ⟨h4a, h4b, h4c⟩
  rcases hy5 with ⟨h5a, h5b, h5c⟩
  omega

lemma Y2_Y3_disjoint {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) :
    ¬ (Y2 C t y ∧ Y3 C t y) := by
  rintro ⟨hy2, hy3⟩
  rcases hy3 with ⟨h3a, h3b, h3c⟩
  rcases hy2 with hy2 | hy2
  · rcases hy2 with ⟨h2a, h2b⟩
    omega
  · rcases hy2 with ⟨h2a, h2b, h2c⟩
    omega

/-- Lemma `lemma:1` (Lemma 19): Y1..Y5 form a partition of the word space. -/
theorem y_partition {n : ℕ} (C _C' : Code n) (t : Fin n) :
    ∀ y : Word n, ∃! i : Fin 5, YSet C t i y := by
  intro y
  by_cases h : dO C y ≤ min (dP C y) (dPp C t y)
  · have hnot23 : ¬ (Y2 C t y ∨ Y3 C t y) := by
      intro h23
      have hgt : min (dP C y) (dPp C t y) < dO C y := (Y2_or_Y3_iff C t y).mp h23
      omega
    rcases (Y1_or_Y4_or_Y5_iff C t y).mpr h with hy | hy | hy
    · refine ⟨⟨0, by decide⟩, ?_, ?_⟩
      · simp [YSet, hy]
      · intro j hj
        fin_cases j
        · rfl
        · exfalso
          exact hnot23 (Or.inl (by simpa [YSet] using hj))
        · exfalso
          exact hnot23 (Or.inr (by simpa [YSet] using hj))
        · exfalso
          exact Y1_Y4_disjoint C t y ⟨hy, by simpa [YSet] using hj⟩
        · exfalso
          exact Y1_Y5_disjoint C t y ⟨hy, by simpa [YSet] using hj⟩
    · refine ⟨⟨3, by decide⟩, ?_, ?_⟩
      · simp [YSet, hy]
      · intro j hj
        fin_cases j
        · exfalso
          exact Y1_Y4_disjoint C t y ⟨by simpa [YSet] using hj, hy⟩
        · exfalso
          exact hnot23 (Or.inl (by simpa [YSet] using hj))
        · exfalso
          exact hnot23 (Or.inr (by simpa [YSet] using hj))
        · rfl
        · exfalso
          exact Y4_Y5_disjoint C t y ⟨hy, by simpa [YSet] using hj⟩
    · refine ⟨⟨4, by decide⟩, ?_, ?_⟩
      · simp [YSet, hy]
      · intro j hj
        fin_cases j
        · exfalso
          exact Y1_Y5_disjoint C t y ⟨by simpa [YSet] using hj, hy⟩
        · exfalso
          exact hnot23 (Or.inl (by simpa [YSet] using hj))
        · exfalso
          exact hnot23 (Or.inr (by simpa [YSet] using hj))
        · exfalso
          exact Y4_Y5_disjoint C t y ⟨by simpa [YSet] using hj, hy⟩
        · rfl
  · have hgt : min (dP C y) (dPp C t y) < dO C y := lt_of_not_ge h
    have hnotA : ¬ (Y1 C t y ∨ Y4 C t y ∨ Y5 C t y) := by
      intro hA'
      exact (lt_irrefl (dO C y))
        (lt_of_le_of_lt ((Y1_or_Y4_or_Y5_iff C t y).mp hA') hgt)
    rcases (Y2_or_Y3_iff C t y).mpr hgt with hy | hy
    · refine ⟨⟨1, by decide⟩, ?_, ?_⟩
      · simp [YSet, hy]
      · intro j hj
        fin_cases j
        · exfalso
          exact hnotA (Or.inl (by simpa [YSet] using hj))
        · rfl
        · exfalso
          exact Y2_Y3_disjoint C t y ⟨hy, by simpa [YSet] using hj⟩
        · exfalso
          exact hnotA (Or.inr (Or.inl (by simpa [YSet] using hj)))
        · exfalso
          exact hnotA (Or.inr (Or.inr (by simpa [YSet] using hj)))
    · refine ⟨⟨2, by decide⟩, ?_, ?_⟩
      · simp [YSet, hy]
      · intro j hj
        fin_cases j
        · exfalso
          exact hnotA (Or.inl (by simpa [YSet] using hj))
        · exfalso
          exact Y2_Y3_disjoint C t y ⟨by simpa [YSet] using hj, hy⟩
        · rfl
        · exfalso
          exact hnotA (Or.inr (Or.inl (by simpa [YSet] using hj)))
        · exfalso
          exact hnotA (Or.inr (Or.inr (by simpa [YSet] using hj)))

/-! ## Lemma `lemma:1` (Lemma 19): g1 is a bijection -/

/-- F1 preserves membership in Y1 ∪ Y3. -/
lemma Y13_closed {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) :
    (Y1 C t (flipBit t y) ∨ Y3 C t (flipBit t y)) → (Y1 C t y ∨ Y3 C t y) := by
  intro hy
  rcases hy with hy | hy
  · rcases hy with hy | hy
    · -- Y1 (F1 y), first disjunct: dOp y ≤ dPp y ∧ dPp y < dP y
      have hOp_le_Pp : dOp C t y ≤ dPp C t y := by
        simpa [dOp, dPp] using hy.1
      have hPp_lt_P : dPp C t y < dP C y := by
        simpa [dPp, flipBit_involutive] using hy.2
      have hdO_le : dO C y ≤ dOp C t y + 1 := dO_le_dOp_add_one C t y
      have hdP_le : dP C y ≤ dPp C t y + 1 := dP_le_dPp_add_one C t y
      by_cases h1 : dO C y ≤ dPp C t y
      · exact Or.inl (Or.inr ⟨h1, le_of_lt hPp_lt_P, hOp_le_Pp⟩)
      · have hOp_eq_Pp : dOp C t y = dPp C t y := by omega
        have hP_eq_dO : dP C y = dO C y := by omega
        exact Or.inr ⟨hOp_eq_Pp.symm, hPp_lt_P, hP_eq_dO⟩
    · -- Y1 (F1 y), second disjunct: dOp y ≤ dP y ∧ dP y ≤ dPp y ∧ dO y ≤ dP y
      have hOp_le_P : dOp C t y ≤ dP C y := by
        simpa [dOp, dPp, flipBit_involutive] using hy.1
      have hP_le_Pp : dP C y ≤ dPp C t y := by
        simpa [dPp, flipBit_involutive] using hy.2.1
      have hO_le_P : dO C y ≤ dP C y := by
        simpa [dOp, dPp, flipBit_involutive] using hy.2.2
      by_cases h2 : dP C y < dPp C t y
      · exact Or.inl (Or.inl ⟨hO_le_P, h2⟩)
      · have hP_eq_Pp : dP C y = dPp C t y := le_antisymm hP_le_Pp (le_of_not_gt h2)
        exact Or.inl (Or.inr ⟨by rw [← hP_eq_Pp]; exact hO_le_P, by rw [hP_eq_Pp],
          by rw [← hP_eq_Pp]; exact hOp_le_P⟩)
  · -- Y3 (F1 y): dP y = dO y ∧ dP y < dPp y ∧ dPp y = dOp y
    rcases hy with ⟨h1, h2, h3⟩
    have hP_eq_O : dP C y = dO C y := by
      simpa [dOp, dPp, flipBit_involutive] using h1
    have hP_lt_Pp : dP C y < dPp C t y := by
      simpa [dPp, flipBit_involutive] using h2
    have hPp_eq_Op : dPp C t y = dOp C t y := by
      simpa [dOp, dPp, flipBit_involutive] using h3
    exact Or.inl (Or.inl ⟨by rw [hP_eq_O], hP_lt_Pp⟩)

/-- F1 maps the complement of Y1 ∪ Y3 into itself. -/
lemma Y13_complement_closed {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) :
    ¬ (Y1 C t y ∨ Y3 C t y) → ¬ (Y1 C t (flipBit t y) ∨ Y3 C t (flipBit t y)) := by
  intro hnot h
  exact hnot (Y13_closed C t y h)

/-- g1 is an involution. -/
lemma g1_involutive {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) :
    g1 C t (g1 C t y) = y := by
  by_cases hy : Y1 C t y ∨ Y3 C t y
  · simp [g1, hy]
  · have hcl := Y13_complement_closed C t y hy
    simp [g1, hy, hcl, flipBit_involutive t y]

/-- Lemma `lemma:1` (Lemma 19): g1 is a bijection. -/
theorem g1_bijective {n : ℕ} (C _C' : Code n) (t : Fin n) :
    Function.Bijective (g1 C t) := by
  let h : Word n → Word n := fun z => if Y1 C t z ∨ Y3 C t z then z else flipBit t z
  have hleft : ∀ y : Word n, h (g1 C t y) = y := by
    intro y
    by_cases hy : Y1 C t y ∨ Y3 C t y
    · simp [g1, h, hy]
    · have hcl := Y13_complement_closed C t y hy
      simp [g1, h, hy, hcl, flipBit_involutive t y]
  have hright : ∀ z : Word n, g1 C t (h z) = z := by
    intro z
    by_cases hz : Y1 C t z ∨ Y3 C t z
    · simp [g1, h, hz]
    · have hcl := Y13_complement_closed C t z hz
      simp [g1, h, hz, hcl, flipBit_involutive t z]
  refine ⟨?inj, ?surj⟩
  · intro a b hab
    rw [← hleft a, ← hleft b, hab]
  · intro z
    exact ⟨h z, hleft z⟩

/-! ## Theorem `the:1` (Theorem 20): exact λ-difference for a one-column change -/

/-- The weight difference when the distance decreases by one (paper `the:1` (Theorem 20)). -/
lemma weight_pred_diff {n : ℕ} {ε : ℝ} (_hε0 : 0 < ε) (hε1 : ε < 1 / 2)
    {d : ℕ} (hd : 1 ≤ d) (hdn : d ≤ n) :
    weight n ε (d - 1) - weight n ε d =
      (1 - ε) ^ n * (1 - ε / (1 - ε)) * (ε / (1 - ε)) ^ (d - 1) := by
  have hden : 1 - ε ≠ 0 := by linarith
  have hnsub : n - (d - 1) = n - d + 1 := by omega
  have hsum : n - d + 1 + (d - 1) = n := by omega
  have hpow : (1 - ε) ^ (n - (d - 1)) = (1 - ε) ^ (n - d) * (1 - ε) := by
    rw [hnsub, pow_succ]
  have hepow : ε ^ d = ε ^ (d - 1) * ε := by
    calc
      ε ^ d = ε ^ ((d - 1) + 1) := by
        congr 1
        omega
      _ = ε ^ (d - 1) * ε := by rw [pow_succ]
  calc
    weight n ε (d - 1) - weight n ε d
        = (1 - ε) ^ (n - d) * (1 - ε) * ε ^ (d - 1) - (1 - ε) ^ (n - d) * (ε ^ (d - 1) * ε) := by
          unfold weight
          rw [hpow, hepow]
    _ = (1 - ε) ^ (n - d) * ε ^ (d - 1) * ((1 - ε) - ε) := by ring
    _ = (1 - ε) ^ n * (1 - ε / (1 - ε)) * (ε / (1 - ε)) ^ (d - 1) := by
          calc
            (1 - ε) ^ (n - d) * ε ^ (d - 1) * ((1 - ε) - ε)
                = (1 - ε) ^ (n - d) * (1 - ε) * ε ^ (d - 1) * (1 - 2 * ε) / (1 - ε) := by
                  field_simp [hden]
                  ring
            _ = (1 - ε) ^ (n - (d - 1)) * ε ^ (d - 1) * (1 - 2 * ε) / (1 - ε) := by
                  rw [← hpow]
            _ = (1 - ε) ^ (n - d + 1) * ε ^ (d - 1) * (1 - 2 * ε) / (1 - ε) := by
                  rw [hnsub]
            _ = (1 - ε) ^ (n - d + 1) * (1 - ε) ^ (d - 1)
                    * (1 - ε / (1 - ε)) * (ε / (1 - ε)) ^ (d - 1) := by
                  rw [div_pow]
                  field_simp [hden]
                  ring
            _ = (1 - ε) ^ n * (1 - ε / (1 - ε)) * (ε / (1 - ε)) ^ (d - 1) := by
                  rw [← pow_add, hsum]

/-- The weight difference when the distance increases by one (paper `the:1` (Theorem 20)). -/
lemma weight_succ_diff {n : ℕ} {ε : ℝ} (_hε0 : 0 < ε) (hε1 : ε < 1 / 2)
    {d : ℕ} (hdn : d < n) :
    weight n ε (d + 1) - weight n ε d =
      -((1 - ε) ^ n * (1 - ε / (1 - ε)) * (ε / (1 - ε)) ^ d) := by
  have h := weight_pred_diff (n := n) (ε := ε) _hε0 hε1 (d := d + 1) (by omega) (by omega)
  have hsub : d + 1 - 1 = d := by omega
  rw [hsub] at h
  linarith

lemma Y1_Y2_disjoint {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) :
    ¬ (Y1 C t y ∧ Y2 C t y) := by
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

lemma Y1_Y3_disjoint {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) :
    ¬ (Y1 C t y ∧ Y3 C t y) := by
  rintro ⟨hy1, hy3⟩
  rcases hy3 with ⟨h3a, h3b, h3c⟩
  rcases hy1 with hy1 | hy1
  · rcases hy1 with ⟨h1a, h1b⟩
    omega
  · rcases hy1 with ⟨h1a, h1b, h1c⟩
    omega

lemma Y2_Y4_disjoint {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) :
    ¬ (Y2 C t y ∧ Y4 C t y) := by
  rintro ⟨hy2, hy4⟩
  rcases hy4 with ⟨h4a, h4b, h4c⟩
  rcases hy2 with hy2 | hy2
  · rcases hy2 with ⟨h2a, h2b⟩
    omega
  · rcases hy2 with ⟨h2a, h2b, h2c⟩
    omega

lemma Y2_Y5_disjoint {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) :
    ¬ (Y2 C t y ∧ Y5 C t y) := by
  rintro ⟨hy2, hy5⟩
  rcases hy5 with ⟨h5a, h5b, h5c⟩
  rcases hy2 with hy2 | hy2
  · rcases hy2 with ⟨h2a, h2b⟩
    omega
  · rcases hy2 with ⟨h2a, h2b, h2c⟩
    omega

lemma Y3_Y4_disjoint {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) :
    ¬ (Y3 C t y ∧ Y4 C t y) := by
  rintro ⟨hy3, hy4⟩
  rcases hy4 with ⟨h4a, h4b, h4c⟩
  rcases hy3 with ⟨h3a, h3b, h3c⟩
  omega

lemma Y3_Y5_disjoint {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) :
    ¬ (Y3 C t y ∧ Y5 C t y) := by
  rintro ⟨hy3, hy5⟩
  rcases hy5 with ⟨h5a, h5b, h5c⟩
  rcases hy3 with ⟨h3a, h3b, h3c⟩
  omega

/-- Exhaustiveness of the Y-partition: every word lies in some Y_i. -/
lemma y_mem {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) :
    Y1 C t y ∨ Y2 C t y ∨ Y3 C t y ∨ Y4 C t y ∨ Y5 C t y := by
  by_cases h : dO C y ≤ min (dP C y) (dPp C t y)
  · have hA := (Y1_or_Y4_or_Y5_iff C t y).mpr h
    rcases hA with hy | hy | hy
    · exact Or.inl hy
    · exact Or.inr (Or.inr (Or.inr (Or.inl hy)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr hy)))
  · have hB := (Y2_or_Y3_iff C t y).mpr (lt_of_not_ge h)
    rcases hB with hy | hy
    · exact Or.inr (Or.inl hy)
    · exact Or.inr (Or.inr (Or.inl hy))

/-- α_C³(0) = 0: words in Y3 have distance at least one (paper `the:1` (Theorem 20)). -/
lemma alpha3_zero {n : ℕ} (C C' : Code n) (t : Fin n) (hcol : C t = col1)
    (hcol' : C' t = col3) (hsame : ∀ u : Fin n, u ≠ t → C' u = C u) :
    alpha3 C t 0 = 0 := by
  rw [alpha3, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro y hy
  have h3 : Y3 C t y := (Finset.mem_filter.mp hy).2.1
  have hd0 : dCode C y = 0 := (Finset.mem_filter.mp hy).2.2
  have h := (y_rel_3 C C' t hcol hcol' hsame h3).2
  omega

/-- α_C⁵(n) = 0: words in Y5 have distance at most n − 1 (paper `the:1` (Theorem 20)). -/
lemma alpha5_n_zero {n : ℕ} (C C' : Code n) (t : Fin n) (hcol : C t = col1)
    (hcol' : C' t = col3) (hsame : ∀ u : Fin n, u ≠ t → C' u = C u) :
    alpha5 C t n = 0 := by
  rw [alpha5, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro y hy
  have h5 : Y5 C t y := (Finset.mem_filter.mp hy).2.1
  have hdn : dCode C y = n := (Finset.mem_filter.mp hy).2.2
  have h := (y_rel_5 C C' t hcol hcol' hsame h5).1
  have hle := dCode_le C' (flipBit t y)
  omega

/-- g1 as an explicit equivalence of the word space. -/
noncomputable def g1Equiv {n : ℕ} (C : Code n) (t : Fin n) : Word n ≃ Word n :=
  Equiv.ofBijective (g1 C t) (g1_bijective C C t)

/-- Group a sum over filtered words by their distance to C. -/
lemma sum_by_dist {n : ℕ} (C : Code n) (P : Word n → Prop) [DecidablePred P]
    (f : ℕ → ℝ) :
    (∑ y ∈ (Finset.univ.filter P), f (dCode C y)) =
      ∑ d ∈ Finset.Icc 0 n,
        ((Finset.univ.filter fun y : Word n => P y ∧ dCode C y = d).card : ℝ) * f d := by
  let E : ℕ → Finset (Word n) := fun d =>
    Finset.univ.filter fun y : Word n => P y ∧ dCode C y = d
  calc
    (∑ y ∈ (Finset.univ.filter P), f (dCode C y))
        = ∑ x ∈ Finset.sigma (Finset.Icc 0 n) E, f x.1 := by
          refine Finset.sum_bij (fun y hy => ⟨dCode C y, y⟩) ?_ ?_ ?_ ?_
          · intro y hy
            have hle := dCode_le C y
            rw [Finset.mem_sigma]
            exact ⟨by simp [hle], by simpa [E] using hy⟩
          · intro a _ b _ hab
            exact congrArg (fun z : Sigma (fun _ : ℕ => Word n) => z.2) hab
          · intro x hx
            rcases x with ⟨d, y⟩
            have hyE : y ∈ E d := (Finset.mem_sigma.mp hx).2
            have hP : P y := (Finset.mem_filter.mp hyE).2.1
            refine ⟨y, ?_, ?_⟩
            · exact Finset.mem_filter.mpr ⟨by simp, hP⟩
            · have hdist : dCode C y = d := (Finset.mem_filter.mp hyE).2.2
              simp [hdist]
          · intro y hy
            rfl
    _ = ∑ d ∈ Finset.Icc 0 n, (E d).card * f d := by
          rw [Finset.sum_sigma]
          apply Finset.sum_congr rfl
          intro d hd
          simp [E]

/-- Dropping the d = 0 term of an interval sum when a(0) = 0. -/
lemma sum_Icc0_eq_Icc1 {n : ℕ} (a : ℕ → ℝ) (ha : a 0 = 0) :
    (∑ d ∈ Finset.Icc 0 n, a d) = ∑ d ∈ Finset.Icc 1 n, a d := by
  by_cases hn : n = 0
  · subst n
    simp [ha]
  · have h01 : (0 : ℕ) < n := Nat.pos_of_ne_zero hn
    have hsplit : Finset.Icc 0 n = insert 0 (Finset.Icc 1 n) := by
      ext d
      constructor
      · intro hd
        by_cases hd0 : d = 0
        · rw [Finset.mem_insert]
          exact Or.inl hd0
        · rw [Finset.mem_insert]
          right
          simp [Finset.mem_Icc] at hd ⊢
          omega
      · intro hd
        rw [Finset.mem_insert] at hd
        rcases hd with hd0 | hd1
        · simp [hd0]
        · simp [Finset.mem_Icc] at hd1 ⊢
          omega
    rw [hsplit, Finset.sum_insert]
    · simp [ha]
    · simp

/-- Σ over Y3 words of r^(d−1), grouped by distance (paper `the:1` (Theorem 20)). -/
lemma sum_Y3_pow {n : ℕ} (C C' : Code n) (t : Fin n) (hcol : C t = col1)
    (hcol' : C' t = col3) (hsame : ∀ u : Fin n, u ≠ t → C' u = C u) (r : ℝ) :
    (∑ y ∈ Finset.univ.filter (Y3 C t), r ^ (dCode C y - 1)) =
      ∑ d ∈ Finset.Icc 1 n, (alpha3 C t d : ℝ) * r ^ (d - 1) := by
  have h0 : (alpha3 C t 0 : ℝ) = 0 := by simp [alpha3_zero C C' t hcol hcol' hsame]
  calc
    (∑ y ∈ Finset.univ.filter (Y3 C t), r ^ (dCode C y - 1))
        = ∑ d ∈ Finset.Icc 0 n, (alpha3 C t d : ℝ) * r ^ (d - 1) := by
          rw [sum_by_dist C (Y3 C t) (fun d => r ^ (d - 1))]
          simp [alpha3]
    _ = ∑ d ∈ Finset.Icc 1 n, (alpha3 C t d : ℝ) * r ^ (d - 1) := by
          exact sum_Icc0_eq_Icc1 (fun d => (alpha3 C t d : ℝ) * r ^ (d - 1))
            (by simp [h0])

/-- Σ over Y5 words of r^d, grouped by distance (paper `the:1` (Theorem 20)). -/
lemma sum_Y5_pow {n : ℕ} (C C' : Code n) (t : Fin n) (hcol : C t = col1)
    (hcol' : C' t = col3) (hsame : ∀ u : Fin n, u ≠ t → C' u = C u) (r : ℝ) :
    (∑ y ∈ Finset.univ.filter (Y5 C t), r ^ (dCode C y)) =
      ∑ d ∈ Finset.Icc 1 n, (alpha5 C t (d - 1) : ℝ) * r ^ (d - 1) := by
  have h0 : (alpha5 C t n : ℝ) = 0 := by simp [alpha5_n_zero C C' t hcol hcol' hsame]
  calc
    (∑ y ∈ Finset.univ.filter (Y5 C t), r ^ (dCode C y))
        = ∑ d ∈ Finset.Icc 0 n, (alpha5 C t d : ℝ) * r ^ d := by
          rw [sum_by_dist C (Y5 C t) (fun d => r ^ d)]
          simp [alpha5]
    _ = ∑ e ∈ Finset.Icc 1 (n + 1), (alpha5 C t (e - 1) : ℝ) * r ^ (e - 1) := by
          refine Finset.sum_bij (fun d _ => d + 1) ?_ ?_ ?_ ?_
          · intro d hd
            simp [Finset.mem_Icc] at hd ⊢
            omega
          · intro a _ b _ hab
            omega
          · intro e he
            refine ⟨e - 1, ?_, ?_⟩
            · simp [Finset.mem_Icc] at he ⊢
              omega
            · have he' : 1 ≤ e := (Finset.mem_Icc.mp he).1
              have hsub : e - 1 + 1 = e := by omega
              rw [hsub]
          · intro d hd
            simp
    _ = ∑ d ∈ Finset.Icc 1 n, (alpha5 C t (d - 1) : ℝ) * r ^ (d - 1) := by
          have hsplit : Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
            ext e
            constructor
            · intro he
              by_cases he' : e = n + 1
              · rw [Finset.mem_insert]
                exact Or.inl he'
              · rw [Finset.mem_insert]
                right
                simp [Finset.mem_Icc] at he ⊢
                omega
            · intro he
              rw [Finset.mem_insert] at he
              rcases he with he' | he1
              · simp [he']
              · simp [Finset.mem_Icc] at he1 ⊢
                omega
          rw [hsplit, Finset.sum_insert]
          · simp [h0]
          · simp

/-- The Y3 part of the λ-difference, factored. -/
lemma sum_Y3_weight_diff {n : ℕ} (C C' : Code n) (t : Fin n) (hcol : C t = col1)
    (hcol' : C' t = col3) (hsame : ∀ u : Fin n, u ≠ t → C' u = C u)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1 / 2) :
    (∑ y ∈ Finset.univ.filter (Y3 C t),
        (weight n ε (dCode C y - 1) - weight n ε (dCode C y))) =
      (1 - ε) ^ n * (1 - ε / (1 - ε)) *
        ∑ y ∈ Finset.univ.filter (Y3 C t), (ε / (1 - ε)) ^ (dCode C y - 1) := by
  calc
    (∑ y ∈ Finset.univ.filter (Y3 C t),
        (weight n ε (dCode C y - 1) - weight n ε (dCode C y)))
        = ∑ y ∈ Finset.univ.filter (Y3 C t),
            (1 - ε) ^ n * (1 - ε / (1 - ε)) * (ε / (1 - ε)) ^ (dCode C y - 1) := by
          apply Finset.sum_congr rfl
          intro y hy
          have h3 : Y3 C t y := (Finset.mem_filter.mp hy).2
          have hd1 : 1 ≤ dCode C y := by
            have h := (y_rel_3 C C' t hcol hcol' hsame h3).2
            omega
          have hdn : dCode C y ≤ n := dCode_le C y
          exact weight_pred_diff (n := n) (ε := ε) hε0 hε1 (d := dCode C y) hd1 hdn
    _ = (1 - ε) ^ n * (1 - ε / (1 - ε)) *
          ∑ y ∈ Finset.univ.filter (Y3 C t), (ε / (1 - ε)) ^ (dCode C y - 1) := by
          rw [Finset.mul_sum]

/-- The Y5 part of the λ-difference, factored. -/
lemma sum_Y5_weight_diff {n : ℕ} (C C' : Code n) (t : Fin n) (hcol : C t = col1)
    (hcol' : C' t = col3) (hsame : ∀ u : Fin n, u ≠ t → C' u = C u)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1 / 2) :
    (∑ y ∈ Finset.univ.filter (Y5 C t),
        (weight n ε (dCode C y + 1) - weight n ε (dCode C y))) =
      -((1 - ε) ^ n * (1 - ε / (1 - ε)) *
          ∑ y ∈ Finset.univ.filter (Y5 C t), (ε / (1 - ε)) ^ (dCode C y)) := by
  calc
    (∑ y ∈ Finset.univ.filter (Y5 C t),
        (weight n ε (dCode C y + 1) - weight n ε (dCode C y)))
        = ∑ y ∈ Finset.univ.filter (Y5 C t),
            -((1 - ε) ^ n * (1 - ε / (1 - ε)) * (ε / (1 - ε)) ^ (dCode C y)) := by
          apply Finset.sum_congr rfl
          intro y hy
          have h5 : Y5 C t y := (Finset.mem_filter.mp hy).2
          have hdn : dCode C y < n := by
            have h := (y_rel_5 C C' t hcol hcol' hsame h5).1
            have hle := dCode_le C' (flipBit t y)
            omega
          exact weight_succ_diff (n := n) (ε := ε) hε0 hε1 (d := dCode C y) hdn
    _ = -((1 - ε) ^ n * (1 - ε / (1 - ε)) *
          ∑ y ∈ Finset.univ.filter (Y5 C t), (ε / (1 - ε)) ^ (dCode C y)) := by
          rw [Finset.sum_neg_distrib]
          rw [Finset.mul_sum]

/-- λ_{C'} − λ_C equals a weighted sum over Y3 (closer) and Y5 (farther) only. -/
lemma lambda_diff_y3y5 {n : ℕ} (C C' : Code n) (t : Fin n) (hcol : C t = col1)
    (hcol' : C' t = col3) (hsame : ∀ u : Fin n, u ≠ t → C' u = C u) (ε : ℝ) :
    lambda C' ε - lambda C ε =
      (1 / 4 : ℝ) *
        ((∑ y ∈ Finset.univ.filter (Y3 C t),
            (weight n ε (dCode C y - 1) - weight n ε (dCode C y))) +
         (∑ y ∈ Finset.univ.filter (Y5 C t),
            (weight n ε (dCode C y + 1) - weight n ε (dCode C y)))) := by
  unfold lambda
  rw [← mul_sub]
  congr 1
  have hg : (∑ y : Word n, weight n ε (dCode C' y)) =
      ∑ y : Word n, weight n ε (dCode C' (g1 C t y)) := by
    refine Finset.sum_bij (fun y _ => g1Equiv C t y) ?_ ?_ ?_ ?_
    · intro y _; exact Finset.mem_univ _
    · intro a _ b _ hab
      exact (g1Equiv C t).injective hab
    · intro b _
      refine ⟨g1Equiv C t b, Finset.mem_univ _, ?_⟩
      change g1 C t (g1 C t b) = b
      exact g1_involutive C t b
    · intro y _
      have hg1 : g1 C t (g1Equiv C t y) = y := by
        change g1 C t (g1 C t y) = y
        exact g1_involutive C t y
      rw [hg1]
  change (∑ y : Word n, weight n ε (dCode C' y)) - ∑ y : Word n, weight n ε (dCode C y) =
      (∑ y ∈ Finset.univ.filter (Y3 C t),
          (weight n ε (dCode C y - 1) - weight n ε (dCode C y))) +
      (∑ y ∈ Finset.univ.filter (Y5 C t),
          (weight n ε (dCode C y + 1) - weight n ε (dCode C y)))
  rw [hg, ← Finset.sum_sub_distrib]
  have hf : ∀ y : Word n,
      weight n ε (dCode C' (g1 C t y)) - weight n ε (dCode C y) =
        (if Y3 C t y then weight n ε (dCode C y - 1) - weight n ε (dCode C y) else 0) +
        (if Y5 C t y then weight n ε (dCode C y + 1) - weight n ε (dCode C y) else 0) := by
    intro y
    by_cases h3 : Y3 C t y
    · have h5 : ¬ Y5 C t y := fun hy => Y3_Y5_disjoint C t y ⟨h3, hy⟩
      have hd : dCode C' (g1 C t y) = dCode C y - 1 := by
        have h := (y_rel_3 C C' t hcol hcol' hsame h3).2
        simp [g1, h3]
        omega
      simp [h3, h5, hd]
    · by_cases h5 : Y5 C t y
      · have h1 : ¬ Y1 C t y := fun hy => Y1_Y5_disjoint C t y ⟨hy, h5⟩
        have hg1 : g1 C t y = flipBit t y := by
          simp [g1, h1, h3]
        have hd : dCode C' (g1 C t y) = dCode C y + 1 := by
          rw [hg1]
          exact (y_rel_5 C C' t hcol hcol' hsame h5).1.symm
        simp [h3, h5, hd]
      · have h0 : weight n ε (dCode C' (g1 C t y)) - weight n ε (dCode C y) = 0 := by
          have hy : Y1 C t y ∨ Y2 C t y ∨ Y4 C t y := by
            rcases y_mem C t y with hy | hy | hy | hy | hy
            · exact Or.inl hy
            · exact Or.inr (Or.inl hy)
            · exfalso; exact h3 hy
            · exact Or.inr (Or.inr hy)
            · exfalso; exact h5 hy
          rcases hy with hy | hy | hy
          · have h := y_rel_1 C C' t hcol hcol' hsame hy
            have hd : dCode C' (g1 C t y) = dCode C y := by
              simp [g1, hy, h.1]
            rw [hd]
            ring
          · have h1 : ¬ Y1 C t y := fun hy1 => Y1_Y2_disjoint C t y ⟨hy1, hy⟩
            have h3' : ¬ Y3 C t y := fun hy3 => Y2_Y3_disjoint C t y ⟨hy, hy3⟩
            have hg1 : g1 C t y = flipBit t y := by
              simp [g1, h1, h3']
            have hd : dCode C' (g1 C t y) = dCode C y := by
              rw [hg1]
              exact (y_rel_2 C C' t hcol hcol' hsame hy).1.symm
            rw [hd]
            ring
          · have h1 : ¬ Y1 C t y := fun hy1 => Y1_Y4_disjoint C t y ⟨hy1, hy⟩
            have h3' : ¬ Y3 C t y := fun hy3 => Y3_Y4_disjoint C t y ⟨hy3, hy⟩
            have hg1 : g1 C t y = flipBit t y := by
              simp [g1, h1, h3']
            have hd : dCode C' (g1 C t y) = dCode C y := by
              rw [hg1]
              exact (y_rel_4 C C' t hcol hcol' hsame hy).2.1.symm
            rw [hd]
            ring
        simp [h3, h5, h0]
  have hsum : (∑ y : Word n,
      (weight n ε (dCode C' (g1 C t y)) - weight n ε (dCode C y))) =
      ∑ y : Word n,
        ((if Y3 C t y then weight n ε (dCode C y - 1) - weight n ε (dCode C y) else 0) +
         (if Y5 C t y then weight n ε (dCode C y + 1) - weight n ε (dCode C y) else 0)) := by
    congr 1
    funext y
    exact hf y
  rw [hsum]
  rw [Finset.sum_add_distrib]
  rw [Finset.sum_filter]
  rw [Finset.sum_filter]

/-- Theorem `the:1` (Theorem 20): exact λ-difference for a one-column change. -/
theorem lambda_diff_one_column {n : ℕ} (C C' : Code n) (t : Fin n)
    (hcol : C t = col1) (hcol' : C' t = col3)
    (hsame : ∀ u : Fin n, u ≠ t → C' u = C u) :
    ∀ ε : ℝ, 0 < ε → ε < 1 / 2 →
      lambda C' ε - lambda C ε =
        ((1 - ε) ^ n / 4) * (1 - ε / (1 - ε)) *
          ∑ d ∈ Finset.Icc 1 n,
            ((alpha3 C t d : ℝ) - (alpha5 C t (d - 1) : ℝ)) *
              (ε / (1 - ε)) ^ (d - 1) := by
  intro ε hε0 hε1
  rw [lambda_diff_y3y5 C C' t hcol hcol' hsame ε]
  rw [sum_Y3_weight_diff C C' t hcol hcol' hsame ε hε0 hε1,
      sum_Y5_weight_diff C C' t hcol hcol' hsame ε hε0 hε1]
  rw [sum_Y3_pow C C' t hcol hcol' hsame (ε / (1 - ε)),
      sum_Y5_pow C C' t hcol hcol' hsame (ε / (1 - ε))]
  have hsum :
      (∑ d ∈ Finset.Icc 1 n, (alpha3 C t d : ℝ) * (ε / (1 - ε)) ^ (d - 1)) -
        ∑ d ∈ Finset.Icc 1 n, (alpha5 C t (d - 1) : ℝ) * (ε / (1 - ε)) ^ (d - 1) =
      ∑ d ∈ Finset.Icc 1 n,
        ((alpha3 C t d : ℝ) - (alpha5 C t (d - 1) : ℝ)) * (ε / (1 - ε)) ^ (d - 1) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    ring
  rw [← hsum]
  ring

/-- Corollary `cor:1` (Corollary 21) (3): Y5 = ∅ ⇒ λ_{C'} ≥ λ_C, equality iff Y3 = ∅. -/
theorem cumulative_no_y5 {n : ℕ} (C C' : Code n) (t : Fin n)
    (hcol : C t = col1) (hcol' : C' t = col3)
    (hsame : ∀ u : Fin n, u ≠ t → C' u = C u)
    (h5 : ∀ y : Word n, ¬ Y5 C t y) :
    UniversalBetter C' C ∧
      (UniversalEqual C' C ↔ ∀ y : Word n, ¬ Y3 C t y) := by
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
  constructor
  · exact compare_bij C C' S (g1Equiv C t) hgt heq
  · constructor
    · intro heq2 y h3
      have hne : ∃ y : Word n, y ∈ S := ⟨y, Finset.mem_filter.mpr ⟨by simp, h3⟩⟩
      have hstrict := compare_bij_strict C C' S (g1Equiv C t) hgt heq hne
      have hgt' : lambda C' (1 / 4 : ℝ) > lambda C (1 / 4) :=
        hstrict (1 / 4) (by norm_num) (by norm_num)
      have heq' : lambda C' (1 / 4 : ℝ) = lambda C (1 / 4) :=
        heq2 (1 / 4) (by norm_num) (by norm_num)
      exact (lt_irrefl _ (hgt'.trans_eq heq')).elim
    · intro hy3
      have heqall : ∀ y : Word n, dCode C y = dCode C' (g1 C t y) := by
        intro y
        by_cases hy : y ∈ S
        · exact False.elim (hy3 y (Finset.mem_filter.mp hy).2)
        · exact heq y hy
      exact compare_bij_eq C C' (g1Equiv C t) heqall

/-- Abel summation: Σ a_d r^(d−1) = Ψ_n r^(n−1) + Σ_{d<n} Ψ_d (r^(d−1) − r^d),
where Ψ_d = Σ_{i≤d} a_i (paper `cor:1` (Corollary 21)). -/
lemma abel_sum {n : ℕ} (a : ℕ → ℝ) (r : ℝ) :
    (∑ d ∈ Finset.Icc 1 n, a d * r ^ (d - 1)) =
      (∑ i ∈ Finset.Icc 1 n, a i) * r ^ (n - 1) +
        ∑ d ∈ Finset.Icc 1 (n - 1), (∑ i ∈ Finset.Icc 1 d, a i) * (r ^ (d - 1) - r ^ d) := by
  let P : ℕ → ℝ := fun d => ∑ i ∈ Finset.Icc 1 d, a i
  have hP0 : P 0 = 0 := by simp [P]
  have hsplit : ∀ d : ℕ, 1 ≤ d → Finset.Icc 1 d = insert d (Finset.Icc 1 (d - 1)) := by
    intro d hd
    ext i
    constructor
    · intro hi
      by_cases hid : i = d
      · rw [Finset.mem_insert]
        exact Or.inl hid
      · rw [Finset.mem_insert]
        right
        simp [Finset.mem_Icc] at hi ⊢
        omega
    · intro hi
      rw [Finset.mem_insert] at hi
      rcases hi with hid | hi1
      · rw [hid]
        simp [Finset.mem_Icc] at hd ⊢
        omega
      · simp [Finset.mem_Icc] at hi1 ⊢
        omega
  have hsplit0 : ∀ m : ℕ, Finset.Icc 0 m = insert 0 (Finset.Icc 1 m) := by
    intro m
    ext i
    constructor
    · intro hi
      by_cases hi0 : i = 0
      · rw [Finset.mem_insert]
        exact Or.inl hi0
      · rw [Finset.mem_insert]
        right
        simp [Finset.mem_Icc] at hi ⊢
        omega
    · intro hi
      rw [Finset.mem_insert] at hi
      rcases hi with hi0 | hi1
      · simp [hi0]
      · simp [Finset.mem_Icc] at hi1 ⊢
        omega
  have hP : ∀ d : ℕ, 1 ≤ d → P d = P (d - 1) + a d := by
    intro d hd
    unfold P
    have hdmem : d ∉ Finset.Icc 1 (d - 1) := by
      simp [Finset.mem_Icc]
      omega
    rw [hsplit d hd, Finset.sum_insert hdmem]
    rw [add_comm]
  calc
    (∑ d ∈ Finset.Icc 1 n, a d * r ^ (d - 1))
        = ∑ d ∈ Finset.Icc 1 n, (P d - P (d - 1)) * r ^ (d - 1) := by
          apply Finset.sum_congr rfl
          intro d hd
          have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
          rw [hP d hd1]
          ring
    _ = (∑ d ∈ Finset.Icc 1 n, P d * r ^ (d - 1)) -
        ∑ d ∈ Finset.Icc 1 n, P (d - 1) * r ^ (d - 1) := by
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro d hd
          ring
    _ = P n * r ^ (n - 1) + ∑ d ∈ Finset.Icc 1 (n - 1), P d * (r ^ (d - 1) - r ^ d) := by
          by_cases hn : n = 0
          · subst n
            simp [P]
          · have hn1 : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn)
            have hsn : Finset.Icc 1 n = insert n (Finset.Icc 1 (n - 1)) := hsplit n hn1
            have hre : (∑ d ∈ Finset.Icc 1 n, P (d - 1) * r ^ (d - 1)) =
                ∑ e ∈ Finset.Icc 0 (n - 1), P e * r ^ e := by
              refine Finset.sum_bij (fun d _ => d - 1) ?_ ?_ ?_ ?_
              · intro d hd
                simp [Finset.mem_Icc] at hd ⊢
                omega
              · intro a ha b hb hab
                have ha1 : 1 ≤ a := (Finset.mem_Icc.mp ha).1
                have hb1 : 1 ≤ b := (Finset.mem_Icc.mp hb).1
                omega
              · intro e he
                refine ⟨e + 1, ?_, ?_⟩
                · simp [Finset.mem_Icc] at he ⊢
                  omega
                · omega
              · intro d hd
                simp
            calc
              (∑ d ∈ Finset.Icc 1 n, P d * r ^ (d - 1)) -
                  ∑ d ∈ Finset.Icc 1 n, P (d - 1) * r ^ (d - 1)
                  = (P n * r ^ (n - 1) + ∑ d ∈ Finset.Icc 1 (n - 1), P d * r ^ (d - 1)) -
                      ∑ d ∈ Finset.Icc 1 n, P (d - 1) * r ^ (d - 1) := by
                    have hnmem : n ∉ Finset.Icc 1 (n - 1) := by
                      simp [Finset.mem_Icc]
                      omega
                    rw [hsn, Finset.sum_insert hnmem]
              _ = (P n * r ^ (n - 1) + ∑ d ∈ Finset.Icc 1 (n - 1), P d * r ^ (d - 1)) -
                  ∑ e ∈ Finset.Icc 0 (n - 1), P e * r ^ e := by
                    rw [hre]
              _ = (P n * r ^ (n - 1) + ∑ d ∈ Finset.Icc 1 (n - 1), P d * r ^ (d - 1)) -
                  (P 0 * r ^ 0 + ∑ d ∈ Finset.Icc 1 (n - 1), P d * r ^ d) := by
                    have h0mem : 0 ∉ Finset.Icc 1 (n - 1) := by
                      simp [Finset.mem_Icc]
                    rw [hsplit0 (n - 1), Finset.sum_insert h0mem]
              _ = P n * r ^ (n - 1) + ((∑ d ∈ Finset.Icc 1 (n - 1), P d * r ^ (d - 1)) -
                  ∑ d ∈ Finset.Icc 1 (n - 1), P d * r ^ d) := by
                    rw [hP0]
                    ring
              _ = P n * r ^ (n - 1) + ∑ d ∈ Finset.Icc 1 (n - 1), P d * (r ^ (d - 1) - r ^ d) := by
                    have hsub : (∑ d ∈ Finset.Icc 1 (n - 1), P d * r ^ (d - 1)) -
                        ∑ d ∈ Finset.Icc 1 (n - 1), P d * r ^ d =
                        ∑ d ∈ Finset.Icc 1 (n - 1), P d * (r ^ (d - 1) - r ^ d) := by
                      rw [← Finset.sum_sub_distrib]
                      apply Finset.sum_congr rfl
                      intro d hd
                      ring
                    rw [hsub]

/-- The real prefix sums of α³(i) − α⁵(i−1) equal the integer Ψ_d. -/
lemma Psi_real {n : ℕ} (C : Code n) (t : Fin n) (d : ℕ) (hd : 1 ≤ d) :
    (∑ i ∈ Finset.Icc 1 d, ((alpha3 C t i : ℝ) - (alpha5 C t (i - 1) : ℝ))) =
      Psi C t d := by
  have hre : (∑ i ∈ Finset.Icc 1 d, (alpha5 C t (i - 1) : ℝ)) =
      ∑ j ∈ Finset.Icc 0 (d - 1), (alpha5 C t j : ℝ) := by
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
      · simp [Finset.mem_Icc] at hj ⊢
        omega
      · omega
    · intro i hi
      rfl
  unfold Psi
  rw [Int.cast_sub, Int.cast_sum, Int.cast_sum]
  rw [Finset.sum_sub_distrib, hre]
  norm_num

/-- r = ε/(1−ε) is positive for 0 < ε < 1/2. -/
lemma r_pos {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1 / 2) : 0 < ε / (1 - ε) := by
  have h1 : 0 < 1 - ε := by linarith
  positivity

/-- r = ε/(1−ε) is less than one for ε < 1/2. -/
lemma r_lt_one {ε : ℝ} (hε1 : ε < 1 / 2) : ε / (1 - ε) < 1 := by
  have h1 : 0 < 1 - ε := by linarith
  exact (div_lt_one h1).mpr (by linarith)

/-- r^(d−1) − r^d > 0 for d ≥ 1 and 0 < ε < 1/2. -/
lemma r_pow_sub_pos {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1 / 2) {d : ℕ} (hd : 1 ≤ d) :
    0 < (ε / (1 - ε)) ^ (d - 1) - (ε / (1 - ε)) ^ d := by
  have hr : ε / (1 - ε) < 1 := r_lt_one hε1
  have hpos : 0 < (ε / (1 - ε)) ^ (d - 1) := pow_pos (r_pos hε0 hε1) (d - 1)
  have h1r : 0 < 1 - ε / (1 - ε) := by linarith
  have hpow' : (ε / (1 - ε)) ^ d = (ε / (1 - ε)) ^ (d - 1) * (ε / (1 - ε)) := by
    calc
      (ε / (1 - ε)) ^ d = (ε / (1 - ε)) ^ ((d - 1) + 1) := by
        congr 1
        omega
      _ = (ε / (1 - ε)) ^ (d - 1) * (ε / (1 - ε)) := by rw [pow_succ]
  calc
    (ε / (1 - ε)) ^ (d - 1) - (ε / (1 - ε)) ^ d
        = (ε / (1 - ε)) ^ (d - 1) * (1 - ε / (1 - ε)) := by
          rw [hpow']
          ring
    _ > 0 := mul_pos hpos h1r

/-- Corollary `cor:1` (Corollary 21) (1): all Ψ_d = 0 ⇒ λ_{C'} = λ_C. -/
theorem cumulative_criterion {n : ℕ} (C C' : Code n) (t : Fin n)
    (hcol : C t = col1) (hcol' : C' t = col3)
    (hsame : ∀ u : Fin n, u ≠ t → C' u = C u)
    (hΨ : ∀ d ∈ Finset.Icc 1 n, Psi C t d = 0) : UniversalEqual C' C := by
  intro ε hε0 hε1
  apply sub_eq_zero.mp
  rw [lambda_diff_one_column C C' t hcol hcol' hsame ε hε0 hε1]
  have hSum : (∑ d ∈ Finset.Icc 1 n,
      ((alpha3 C t d : ℝ) - (alpha5 C t (d - 1) : ℝ)) * (ε / (1 - ε)) ^ (d - 1)) = 0 := by
    rw [abel_sum (fun i => (alpha3 C t i : ℝ) - (alpha5 C t (i - 1) : ℝ)) (ε / (1 - ε))]
    by_cases hn : n = 0
    · subst n
      simp
    · have hn1 : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn)
      have hterm1 : (∑ i ∈ Finset.Icc 1 n,
          ((alpha3 C t i : ℝ) - (alpha5 C t (i - 1) : ℝ))) * (ε / (1 - ε)) ^ (n - 1) = 0 := by
        rw [Psi_real C t n hn1, hΨ n (by simp [Finset.mem_Icc, hn1])]
        norm_num
      have hterm2 : (∑ d ∈ Finset.Icc 1 (n - 1),
          (∑ i ∈ Finset.Icc 1 d, ((alpha3 C t i : ℝ) - (alpha5 C t (i - 1) : ℝ))) *
            ((ε / (1 - ε)) ^ (d - 1) - (ε / (1 - ε)) ^ d)) = 0 := by
        apply Finset.sum_eq_zero
        intro d hd
        have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
        have hd2 : d ≤ n - 1 := (Finset.mem_Icc.mp hd).2
        have hdn : d ≤ n := by omega
        rw [Psi_real C t d hd1, hΨ d (by simp [Finset.mem_Icc, hd1, hdn])]
        norm_num
      rw [hterm1, hterm2]
      ring
  rw [hSum]
  ring

/-- Corollary `cor:1` (Corollary 21) (2): all Ψ_d ≥ 0 and some Ψ_d > 0 ⇒ λ_{C'} > λ_C. -/
theorem cumulative_strict {n : ℕ} (C C' : Code n) (t : Fin n)
    (hcol : C t = col1) (hcol' : C' t = col3)
    (hsame : ∀ u : Fin n, u ≠ t → C' u = C u)
    (hge : ∀ d ∈ Finset.Icc 1 n, Psi C t d ≥ 0)
    (hgt : ∃ d ∈ Finset.Icc 1 n, Psi C t d > 0) :
    UniversalStrictBetter C' C := by
  intro ε hε0 hε1
  apply sub_pos.mp
  rw [lambda_diff_one_column C C' t hcol hcol' hsame ε hε0 hε1]
  have hSum : (0 : ℝ) < ∑ d ∈ Finset.Icc 1 n,
      ((alpha3 C t d : ℝ) - (alpha5 C t (d - 1) : ℝ)) * (ε / (1 - ε)) ^ (d - 1) := by
    rw [abel_sum (fun i => (alpha3 C t i : ℝ) - (alpha5 C t (i - 1) : ℝ)) (ε / (1 - ε))]
    by_cases hn : n = 0
    · subst n
      exfalso
      rcases hgt with ⟨d, hd, _⟩
      simp at hd
    · have hn1 : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn)
      have hC_nonneg : ∀ d ∈ Finset.Icc 1 (n - 1),
          0 ≤ (∑ i ∈ Finset.Icc 1 d, ((alpha3 C t i : ℝ) - (alpha5 C t (i - 1) : ℝ))) *
            ((ε / (1 - ε)) ^ (d - 1) - (ε / (1 - ε)) ^ d) := by
        intro d hd
        have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
        have hd2 : d ≤ n - 1 := (Finset.mem_Icc.mp hd).2
        have hdn : d ≤ n := by omega
        rw [Psi_real C t d hd1]
        have hPd : 0 ≤ (Psi C t d : ℝ) := by
          exact_mod_cast hge d (by simp [Finset.mem_Icc, hd1, hdn])
        exact mul_nonneg hPd (le_of_lt (r_pow_sub_pos hε0 hε1 hd1))
      have hterm1 : 0 ≤ (∑ i ∈ Finset.Icc 1 n,
          ((alpha3 C t i : ℝ) - (alpha5 C t (i - 1) : ℝ))) * (ε / (1 - ε)) ^ (n - 1) := by
        rw [Psi_real C t n hn1]
        have hPn : 0 ≤ (Psi C t n : ℝ) := by
          exact_mod_cast hge n (by simp [Finset.mem_Icc, hn1])
        exact mul_nonneg hPn (pow_nonneg (le_of_lt (r_pos hε0 hε1)) (n - 1))
      have hterm2 : 0 ≤ ∑ d ∈ Finset.Icc 1 (n - 1),
          (∑ i ∈ Finset.Icc 1 d, ((alpha3 C t i : ℝ) - (alpha5 C t (i - 1) : ℝ))) *
            ((ε / (1 - ε)) ^ (d - 1) - (ε / (1 - ε)) ^ d) := by
        exact Finset.sum_nonneg hC_nonneg
      rcases hgt with ⟨d0, hd0mem, hd0gt⟩
      have hd01 : 1 ≤ d0 := (Finset.mem_Icc.mp hd0mem).1
      have hd0n : d0 ≤ n := (Finset.mem_Icc.mp hd0mem).2
      by_cases hd0eq : d0 = n
      · have hterm1' : 0 < (∑ i ∈ Finset.Icc 1 n,
            ((alpha3 C t i : ℝ) - (alpha5 C t (i - 1) : ℝ))) * (ε / (1 - ε)) ^ (n - 1) := by
          rw [Psi_real C t n hn1]
          have hPn : 0 < (Psi C t n : ℝ) := by
            have hgtn : Psi C t n > 0 := by
              simpa [hd0eq] using hd0gt
            exact_mod_cast hgtn
          exact mul_pos hPn (pow_pos (r_pos hε0 hε1) (n - 1))
        have hsum0 : 0 < (∑ i ∈ Finset.Icc 1 n,
            ((alpha3 C t i : ℝ) - (alpha5 C t (i - 1) : ℝ))) * (ε / (1 - ε)) ^ (n - 1) +
            ∑ d ∈ Finset.Icc 1 (n - 1),
              (∑ i ∈ Finset.Icc 1 d, ((alpha3 C t i : ℝ) - (alpha5 C t (i - 1) : ℝ))) *
                ((ε / (1 - ε)) ^ (d - 1) - (ε / (1 - ε)) ^ d) := by
          linarith
        exact hsum0
      · have hd0lt : d0 ≤ n - 1 := by omega
        have hd0mem' : d0 ∈ Finset.Icc 1 (n - 1) := by
          simp [Finset.mem_Icc, hd01, hd0lt]
        have hC : 0 < (∑ i ∈ Finset.Icc 1 d0,
            ((alpha3 C t i : ℝ) - (alpha5 C t (i - 1) : ℝ))) *
              ((ε / (1 - ε)) ^ (d0 - 1) - (ε / (1 - ε)) ^ d0) := by
          rw [Psi_real C t d0 hd01]
          have hP : 0 < (Psi C t d0 : ℝ) := by
            exact_mod_cast hd0gt
          exact mul_pos hP (r_pow_sub_pos hε0 hε1 hd01)
        have hB : (∑ i ∈ Finset.Icc 1 d0,
            ((alpha3 C t i : ℝ) - (alpha5 C t (i - 1) : ℝ))) *
              ((ε / (1 - ε)) ^ (d0 - 1) - (ε / (1 - ε)) ^ d0) ≤
            ∑ d ∈ Finset.Icc 1 (n - 1),
              (∑ i ∈ Finset.Icc 1 d, ((alpha3 C t i : ℝ) - (alpha5 C t (i - 1) : ℝ))) *
                ((ε / (1 - ε)) ^ (d - 1) - (ε / (1 - ε)) ^ d) := by
          exact Finset.single_le_sum hC_nonneg hd0mem'
        have hsum0 : 0 < (∑ i ∈ Finset.Icc 1 n,
            ((alpha3 C t i : ℝ) - (alpha5 C t (i - 1) : ℝ))) * (ε / (1 - ε)) ^ (n - 1) +
            ∑ d ∈ Finset.Icc 1 (n - 1),
              (∑ i ∈ Finset.Icc 1 d, ((alpha3 C t i : ℝ) - (alpha5 C t (i - 1) : ℝ))) *
                ((ε / (1 - ε)) ^ (d - 1) - (ε / (1 - ε)) ^ d) := by
          linarith
        exact hsum0
  have hK : 0 < (1 - ε) ^ n / 4 * (1 - ε / (1 - ε)) := by
    have h1ε : 0 < 1 - ε := by linarith
    have hr1 : ε / (1 - ε) < 1 := r_lt_one hε1
    exact mul_pos (div_pos (pow_pos h1ε n) (by norm_num)) (by linarith)
  exact mul_pos hK hSum

/-- Corollary `cor:1` (Corollary 21) (non-strict): all Ψ_d ≥ 0 ⇒ λ_{C'} ≥ λ_C. -/
theorem cumulative_nonneg {n : ℕ} (C C' : Code n) (t : Fin n)
    (hcol : C t = col1) (hcol' : C' t = col3)
    (hsame : ∀ u : Fin n, u ≠ t → C' u = C u)
    (hge : ∀ d ∈ Finset.Icc 1 n, Psi C t d ≥ 0) : UniversalBetter C' C := by
  intro ε hε0 hε1
  apply sub_nonneg.mp
  rw [lambda_diff_one_column C C' t hcol hcol' hsame ε hε0 hε1]
  have hSum : (0 : ℝ) ≤ ∑ d ∈ Finset.Icc 1 n,
      ((alpha3 C t d : ℝ) - (alpha5 C t (d - 1) : ℝ)) * (ε / (1 - ε)) ^ (d - 1) := by
    rw [abel_sum (fun i => (alpha3 C t i : ℝ) - (alpha5 C t (i - 1) : ℝ)) (ε / (1 - ε))]
    by_cases hn : n = 0
    · subst n
      simp
    · have hn1 : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn)
      have hC_nonneg : ∀ d ∈ Finset.Icc 1 (n - 1),
          0 ≤ (∑ i ∈ Finset.Icc 1 d, ((alpha3 C t i : ℝ) - (alpha5 C t (i - 1) : ℝ))) *
            ((ε / (1 - ε)) ^ (d - 1) - (ε / (1 - ε)) ^ d) := by
        intro d hd
        have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
        have hd2 : d ≤ n - 1 := (Finset.mem_Icc.mp hd).2
        have hdn : d ≤ n := by omega
        rw [Psi_real C t d hd1]
        have hPd : 0 ≤ (Psi C t d : ℝ) := by
          exact_mod_cast hge d (by simp [Finset.mem_Icc, hd1, hdn])
        exact mul_nonneg hPd (le_of_lt (r_pow_sub_pos hε0 hε1 hd1))
      have hterm1 : 0 ≤ (∑ i ∈ Finset.Icc 1 n,
          ((alpha3 C t i : ℝ) - (alpha5 C t (i - 1) : ℝ))) * (ε / (1 - ε)) ^ (n - 1) := by
        rw [Psi_real C t n hn1]
        have hPn : 0 ≤ (Psi C t n : ℝ) := by
          exact_mod_cast hge n (by simp [Finset.mem_Icc, hn1])
        exact mul_nonneg hPn (pow_nonneg (le_of_lt (r_pos hε0 hε1)) (n - 1))
      have hterm2 : 0 ≤ ∑ d ∈ Finset.Icc 1 (n - 1),
          (∑ i ∈ Finset.Icc 1 d, ((alpha3 C t i : ℝ) - (alpha5 C t (i - 1) : ℝ))) *
            ((ε / (1 - ε)) ^ (d - 1) - (ε / (1 - ε)) ^ d) := by
        exact Finset.sum_nonneg hC_nonneg
      linarith
  have hK : 0 ≤ (1 - ε) ^ n / 4 * (1 - ε / (1 - ε)) := by
    have h1ε : 0 ≤ 1 - ε := by linarith
    have hr1 : ε / (1 - ε) < 1 := r_lt_one hε1
    exact mul_nonneg (div_nonneg (pow_nonneg h1ε n) (by norm_num)) (by linarith)
  exact mul_nonneg hK hSum

end N4Code
