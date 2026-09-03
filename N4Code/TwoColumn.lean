import N4Code.ZeroColumn

/-!
# Phase D: the two-column engine (paper §4, `lemma:2` (Lemma 22), `thm:odd` (Theorem 11))

For two codes `C` and `C'` differing only at positions `t₁` and `t₂`
(paper §4): the Z1..Z5 partition of the word space, the bijection `g2`,
the distance relations for each zone, the 16 parity cases
(`lemma:y4` (Lemma 24), `lemma:z5` (Lemma 24), `lm:2` (Lemma 25), `lm:3` (Lemma 26), `lm:16` (Lemma 27)), and `thm:odd` (Theorem 11)
(the (1,7)→(3,5) two-column flip with its equality characterization).

See `AGENTS.md` for build/consistency rules and `PLAN.md` Phase D for the
work plan.  The paper statements are the placeholder stubs in
`N4Code/Statements.lean` (§4); prove them here and replace each stub with a
comment pointing back (as done for `thm:0column` (Theorem 6) in `ZeroColumn.lean`).
-/

namespace N4Code

set_option maxRecDepth 1000000

open scoped BigOperators

/-! ## Two-flip distance machinery (paper §4, eq. thm2a/thm2b) -/

/-- F₂ is an involution. -/
lemma flipTwoBits_involutive {n : ℕ} (t₁ t₂ : Fin n) (y : Word n) :
    flipTwoBits t₁ t₂ (flipTwoBits t₁ t₂ y) = y := by
  funext u
  by_cases h : u = t₁ ∨ u = t₂ <;> simp [flipTwoBits, h]

/-- A Boolean inequality is one of the two orientations. -/
lemma bool_ne_cases {a b : Bool} (h : a ≠ b) :
    (a = true ∧ b = false) ∨ (a = false ∧ b = true) := by
  cases a <;> cases b
  · exfalso
    exact h rfl
  · exact Or.inr ⟨rfl, rfl⟩
  · exact Or.inl ⟨rfl, rfl⟩
  · exfalso
    exact h rfl

/-- If two functions agree off {t₁,t₂} and the first is one larger at both
positions, the first sum is two larger. -/
lemma sum_sub_two_pos {n : ℕ} (f g : Fin n → ℕ) (t₁ t₂ : Fin n) (htne : t₁ ≠ t₂)
    (h1 : f t₁ = g t₁ + 1) (h2 : f t₂ = g t₂ + 1)
    (hrest : ∀ u : Fin n, u ≠ t₁ → u ≠ t₂ → f u = g u) :
    (∑ u : Fin n, f u) = (∑ u : Fin n, g u) + 2 := by
  have he1 : (∑ u ∈ (Finset.univ.erase t₁).erase t₂, f u) =
      ∑ u ∈ (Finset.univ.erase t₁).erase t₂, g u := by
    apply Finset.sum_congr rfl
    intro u hu
    have hu2 : u ≠ t₂ := (Finset.mem_erase.mp hu).1
    have hu1 : u ≠ t₁ := (Finset.mem_erase.mp (Finset.mem_erase.mp hu).2).1
    exact hrest u hu1 hu2
  have hf1 : (∑ u : Fin n, f u) =
      (∑ u ∈ (Finset.univ.erase t₁).erase t₂, f u) + f t₂ + f t₁ := by
    rw [sum_split_at f t₁]
    have hb : (∑ u ∈ (Finset.univ.erase t₁), f u) =
        (∑ u ∈ (Finset.univ.erase t₁).erase t₂, f u) + f t₂ := by
      exact (Finset.sum_erase_add (Finset.univ.erase t₁) f
        (Finset.mem_erase.mpr ⟨htne.symm, Finset.mem_univ t₂⟩)).symm
    rw [hb]
  have hg1 : (∑ u : Fin n, g u) =
      (∑ u ∈ (Finset.univ.erase t₁).erase t₂, g u) + g t₂ + g t₁ := by
    rw [sum_split_at g t₁]
    have hb : (∑ u ∈ (Finset.univ.erase t₁), g u) =
        (∑ u ∈ (Finset.univ.erase t₁).erase t₂, g u) + g t₂ := by
      exact (Finset.sum_erase_add (Finset.univ.erase t₁) g
        (Finset.mem_erase.mpr ⟨htne.symm, Finset.mem_univ t₂⟩)).symm
    rw [hb]
  calc
    (∑ u : Fin n, f u) = (∑ u ∈ (Finset.univ.erase t₁).erase t₂, f u) + f t₂ + f t₁ := hf1
    _ = (∑ u ∈ (Finset.univ.erase t₁).erase t₂, g u) + (g t₂ + 1) + (g t₁ + 1) := by
          rw [he1, h1, h2]
    _ = (∑ u : Fin n, g u) + 2 := by
          rw [hg1]
          omega

/-- If two functions agree off {t₁,t₂} and the first is one smaller at both
positions, the first sum is two smaller. -/
lemma sum_sub_two_neg {n : ℕ} (f g : Fin n → ℕ) (t₁ t₂ : Fin n) (htne : t₁ ≠ t₂)
    (h1 : f t₁ + 1 = g t₁) (h2 : f t₂ + 1 = g t₂)
    (hrest : ∀ u : Fin n, u ≠ t₁ → u ≠ t₂ → f u = g u) :
    (∑ u : Fin n, f u) + 2 = (∑ u : Fin n, g u) := by
  have hpos : (∑ u : Fin n, g u) = (∑ u : Fin n, f u) + 2 := by
    apply sum_sub_two_pos g f t₁ t₂ htne
    · omega
    · omega
    · intro u hu1 hu2
      exact (hrest u hu1 hu2).symm
  omega

/-- If two functions agree off {t₁,t₂}, the first is one larger at t₁ and one
smaller at t₂, then the sums are equal. -/
lemma sum_sub_two_zero₁ {n : ℕ} (f g : Fin n → ℕ) (t₁ t₂ : Fin n) (htne : t₁ ≠ t₂)
    (h1 : f t₁ = g t₁ + 1) (h2 : f t₂ + 1 = g t₂)
    (hrest : ∀ u : Fin n, u ≠ t₁ → u ≠ t₂ → f u = g u) :
    (∑ u : Fin n, f u) = (∑ u : Fin n, g u) := by
  have he1 : (∑ u ∈ (Finset.univ.erase t₁).erase t₂, f u) =
      ∑ u ∈ (Finset.univ.erase t₁).erase t₂, g u := by
    apply Finset.sum_congr rfl
    intro u hu
    have hu2 : u ≠ t₂ := (Finset.mem_erase.mp hu).1
    have hu1 : u ≠ t₁ := (Finset.mem_erase.mp (Finset.mem_erase.mp hu).2).1
    exact hrest u hu1 hu2
  have hf1 : (∑ u : Fin n, f u) =
      (∑ u ∈ (Finset.univ.erase t₁).erase t₂, f u) + f t₂ + f t₁ := by
    rw [sum_split_at f t₁]
    have hb : (∑ u ∈ (Finset.univ.erase t₁), f u) =
        (∑ u ∈ (Finset.univ.erase t₁).erase t₂, f u) + f t₂ := by
      exact (Finset.sum_erase_add (Finset.univ.erase t₁) f
        (Finset.mem_erase.mpr ⟨htne.symm, Finset.mem_univ t₂⟩)).symm
    rw [hb]
  have hg1 : (∑ u : Fin n, g u) =
      (∑ u ∈ (Finset.univ.erase t₁).erase t₂, g u) + g t₂ + g t₁ := by
    rw [sum_split_at g t₁]
    have hb : (∑ u ∈ (Finset.univ.erase t₁), g u) =
        (∑ u ∈ (Finset.univ.erase t₁).erase t₂, g u) + g t₂ := by
      exact (Finset.sum_erase_add (Finset.univ.erase t₁) g
        (Finset.mem_erase.mpr ⟨htne.symm, Finset.mem_univ t₂⟩)).symm
    rw [hb]
  calc
    (∑ u : Fin n, f u) = (∑ u ∈ (Finset.univ.erase t₁).erase t₂, f u) + f t₂ + f t₁ := hf1
    _ = (∑ u ∈ (Finset.univ.erase t₁).erase t₂, g u) + (g t₂ - 1) + (g t₁ + 1) := by
          have hf₂ : f t₂ = g t₂ - 1 := by omega
          rw [he1, h1, hf₂]
    _ = (∑ u : Fin n, g u) := by
          rw [hg1]
          omega

/-- If two functions agree off {t₁,t₂}, the first is one smaller at t₁ and one
larger at t₂, then the sums are equal. -/
lemma sum_sub_two_zero₂ {n : ℕ} (f g : Fin n → ℕ) (t₁ t₂ : Fin n) (htne : t₁ ≠ t₂)
    (h1 : f t₁ + 1 = g t₁) (h2 : f t₂ = g t₂ + 1)
    (hrest : ∀ u : Fin n, u ≠ t₁ → u ≠ t₂ → f u = g u) :
    (∑ u : Fin n, f u) = (∑ u : Fin n, g u) := by
  exact (sum_sub_two_zero₁ g f t₁ t₂ htne
    (by omega) (by omega) (fun u hu1 hu2 => (hrest u hu1 hu2).symm)).symm

/-- Mismatch indicator: 1 at position u iff the code bit differs from w. -/
def mInd {n : ℕ} (C : Code n) (j : Fin 4) (w : Word n) (u : Fin n) : ℕ :=
  if colBit j (C u) ≠ w u then 1 else 0

/-- d_j(w) is the sum of the mismatch indicators. -/
lemma dRow_eq_mInd {n : ℕ} (C : Code n) (j : Fin 4) (w : Word n) :
    dRow C j w = ∑ u : Fin n, mInd C j w u := by
  rw [dRow_eq_indicator_sum]
  rfl

/-- Row distances of the changed rows (1 and 2) drop by two when
(y t₁ = true, y t₂ = false) — paper eq. (thm2a). -/
lemma dRow12_flip2_sub_two {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (htne : t₁ ≠ t₂)
    (h1 : C t₁ = col1) (h7 : C t₂ = col7) (y : Word n)
    (hy1 : y t₁ = true) (hy2 : y t₂ = false) :
    dRow C 1 (flipTwoBits t₁ t₂ y) + 2 = dRow C 1 y ∧
      dRow C 2 (flipTwoBits t₁ t₂ y) + 2 = dRow C 2 y := by
  constructor
  · rw [dRow_eq_mInd, dRow_eq_mInd]
    exact sum_sub_two_neg (mInd C 1 (flipTwoBits t₁ t₂ y)) (mInd C 1 y) t₁ t₂ htne
      (by simp [mInd, flipTwoBits, h1, colBit, col1, hy1])
      (by simp [mInd, flipTwoBits, h7, colBit, col7, hy2])
      (by intro u hu1 hu2; simp [mInd, flipTwoBits, hu1, hu2])
  · rw [dRow_eq_mInd, dRow_eq_mInd]
    exact sum_sub_two_neg (mInd C 2 (flipTwoBits t₁ t₂ y)) (mInd C 2 y) t₁ t₂ htne
      (by simp [mInd, flipTwoBits, h1, colBit, col1, hy1])
      (by simp [mInd, flipTwoBits, h7, colBit, col7, hy2])
      (by intro u hu1 hu2; simp [mInd, flipTwoBits, hu1, hu2])

/-- Row distances of the changed rows (1 and 2) rise by two when
(y t₁ = false, y t₂ = true) — paper eq. (thm2a). -/
lemma dRow12_flip2_add_two {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (htne : t₁ ≠ t₂)
    (h1 : C t₁ = col1) (h7 : C t₂ = col7) (y : Word n)
    (hy1 : y t₁ = false) (hy2 : y t₂ = true) :
    dRow C 1 (flipTwoBits t₁ t₂ y) = dRow C 1 y + 2 ∧
      dRow C 2 (flipTwoBits t₁ t₂ y) = dRow C 2 y + 2 := by
  constructor
  · rw [dRow_eq_mInd, dRow_eq_mInd]
    exact sum_sub_two_pos (mInd C 1 (flipTwoBits t₁ t₂ y)) (mInd C 1 y) t₁ t₂ htne
      (by simp [mInd, flipTwoBits, h1, colBit, col1, hy1])
      (by simp [mInd, flipTwoBits, h7, colBit, col7, hy2])
      (by intro u hu1 hu2; simp [mInd, flipTwoBits, hu1, hu2])
  · rw [dRow_eq_mInd, dRow_eq_mInd]
    exact sum_sub_two_pos (mInd C 2 (flipTwoBits t₁ t₂ y)) (mInd C 2 y) t₁ t₂ htne
      (by simp [mInd, flipTwoBits, h1, colBit, col1, hy1])
      (by simp [mInd, flipTwoBits, h7, colBit, col7, hy2])
      (by intro u hu1 hu2; simp [mInd, flipTwoBits, hu1, hu2])

/-- Rows 0 and 3 are unchanged under F₂ when y t₁ ≠ y t₂. -/
lemma dRow03_flip2_eq_ne {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (htne : t₁ ≠ t₂)
    (h1 : C t₁ = col1) (h7 : C t₂ = col7) (y : Word n) (hyne : y t₁ ≠ y t₂) :
    dRow C 0 (flipTwoBits t₁ t₂ y) = dRow C 0 y ∧
      dRow C 3 (flipTwoBits t₁ t₂ y) = dRow C 3 y := by
  rcases bool_ne_cases hyne with hy | hy
  · rcases hy with ⟨hy1, hy2⟩
    constructor
    · rw [dRow_eq_mInd, dRow_eq_mInd]
      exact sum_sub_two_zero₂ (mInd C 0 (flipTwoBits t₁ t₂ y)) (mInd C 0 y) t₁ t₂ htne
        (by simp [mInd, flipTwoBits, h1, colBit, col1, hy1])
        (by simp [mInd, flipTwoBits, h7, colBit, col7, hy2])
        (by intro u hu1 hu2; simp [mInd, flipTwoBits, hu1, hu2])
    · rw [dRow_eq_mInd, dRow_eq_mInd]
      exact sum_sub_two_zero₁ (mInd C 3 (flipTwoBits t₁ t₂ y)) (mInd C 3 y) t₁ t₂ htne
        (by simp [mInd, flipTwoBits, h1, colBit, col1, hy1])
        (by simp [mInd, flipTwoBits, h7, colBit, col7, hy2])
        (by intro u hu1 hu2; simp [mInd, flipTwoBits, hu1, hu2])
  · rcases hy with ⟨hy1, hy2⟩
    constructor
    · rw [dRow_eq_mInd, dRow_eq_mInd]
      exact sum_sub_two_zero₁ (mInd C 0 (flipTwoBits t₁ t₂ y)) (mInd C 0 y) t₁ t₂ htne
        (by simp [mInd, flipTwoBits, h1, colBit, col1, hy1])
        (by simp [mInd, flipTwoBits, h7, colBit, col7, hy2])
        (by intro u hu1 hu2; simp [mInd, flipTwoBits, hu1, hu2])
    · rw [dRow_eq_mInd, dRow_eq_mInd]
      exact sum_sub_two_zero₂ (mInd C 3 (flipTwoBits t₁ t₂ y)) (mInd C 3 y) t₁ t₂ htne
        (by simp [mInd, flipTwoBits, h1, colBit, col1, hy1])
        (by simp [mInd, flipTwoBits, h7, colBit, col7, hy2])
        (by intro u hu1 hu2; simp [mInd, flipTwoBits, hu1, hu2])

/-- Rows 1 and 2 are unchanged under F₂ when y t₁ = y t₂ (paper eq. thm2b). -/
lemma dRow12_flip2_eq_of_eq {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (htne : t₁ ≠ t₂)
    (h1 : C t₁ = col1) (h7 : C t₂ = col7) (y : Word n) (hyeq : y t₁ = y t₂) :
    dRow C 1 (flipTwoBits t₁ t₂ y) = dRow C 1 y ∧
      dRow C 2 (flipTwoBits t₁ t₂ y) = dRow C 2 y := by
  cases hy : y t₁
  · have hy1 : y t₁ = false := hy
    have hy2 : y t₂ = false := by simpa [hy1] using hyeq
    constructor
    · rw [dRow_eq_mInd, dRow_eq_mInd]
      exact sum_sub_two_zero₁ (mInd C 1 (flipTwoBits t₁ t₂ y)) (mInd C 1 y) t₁ t₂ htne
        (by simp [mInd, flipTwoBits, h1, colBit, col1, hy1])
        (by simp [mInd, flipTwoBits, h7, colBit, col7, hy2])
        (by intro u hu1 hu2; simp [mInd, flipTwoBits, hu1, hu2])
    · rw [dRow_eq_mInd, dRow_eq_mInd]
      exact sum_sub_two_zero₁ (mInd C 2 (flipTwoBits t₁ t₂ y)) (mInd C 2 y) t₁ t₂ htne
        (by simp [mInd, flipTwoBits, h1, colBit, col1, hy1])
        (by simp [mInd, flipTwoBits, h7, colBit, col7, hy2])
        (by intro u hu1 hu2; simp [mInd, flipTwoBits, hu1, hu2])
  · have hy1 : y t₁ = true := hy
    have hy2 : y t₂ = true := by simpa [hy1] using hyeq
    constructor
    · rw [dRow_eq_mInd, dRow_eq_mInd]
      exact sum_sub_two_zero₂ (mInd C 1 (flipTwoBits t₁ t₂ y)) (mInd C 1 y) t₁ t₂ htne
        (by simp [mInd, flipTwoBits, h1, colBit, col1, hy1])
        (by simp [mInd, flipTwoBits, h7, colBit, col7, hy2])
        (by intro u hu1 hu2; simp [mInd, flipTwoBits, hu1, hu2])
    · rw [dRow_eq_mInd, dRow_eq_mInd]
      exact sum_sub_two_zero₂ (mInd C 2 (flipTwoBits t₁ t₂ y)) (mInd C 2 y) t₁ t₂ htne
        (by simp [mInd, flipTwoBits, h1, colBit, col1, hy1])
        (by simp [mInd, flipTwoBits, h7, colBit, col7, hy2])
        (by intro u hu1 hu2; simp [mInd, flipTwoBits, hu1, hu2])

/-- d_P' = d_P when y t₁ = y t₂ (paper eq. thm2b). -/
lemma dPp2_eq_dP_of_eq {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (htne : t₁ ≠ t₂)
    (h1 : C t₁ = col1) (h7 : C t₂ = col7) (y : Word n) (hyeq : y t₁ = y t₂) :
    dPp2 C t₁ t₂ y = dP C y := by
  unfold dPp2 dP
  exact (dRow12_flip2_eq_of_eq C t₁ t₂ htne h1 h7 y hyeq).2

/-- d_O' ≤ d_O when (y t₁ = true, y t₂ = false). -/
lemma dOp2_le_dO_of_htrue_hfalse {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (htne : t₁ ≠ t₂)
    (h1 : C t₁ = col1) (h7 : C t₂ = col7) (y : Word n)
    (hy1 : y t₁ = true) (hy2 : y t₂ = false) :
    dOp2 C t₁ t₂ y ≤ dO C y := by
  have h03 := dRow03_flip2_eq_ne C t₁ t₂ htne h1 h7 y (by simp [hy1, hy2])
  have h12 := dRow12_flip2_sub_two C t₁ t₂ htne h1 h7 y hy1 hy2
  unfold dOp2 dO
  change min (dRow C 0 (flipTwoBits t₁ t₂ y))
      (min (dRow C 1 (flipTwoBits t₁ t₂ y)) (dRow C 3 (flipTwoBits t₁ t₂ y))) ≤
    min (dRow C 0 y) (min (dRow C 1 y) (dRow C 3 y))
  rw [h03.1, h03.2]
  have hle : dRow C 1 (flipTwoBits t₁ t₂ y) ≤ dRow C 1 y := by omega
  exact min_le_min le_rfl (min_le_min hle le_rfl)

/-- d_O ≤ d_O' when (y t₁ = false, y t₂ = true). -/
lemma dO_le_dOp2_of_hfalse_htrue {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (htne : t₁ ≠ t₂)
    (h1 : C t₁ = col1) (h7 : C t₂ = col7) (y : Word n)
    (hy1 : y t₁ = false) (hy2 : y t₂ = true) :
    dO C y ≤ dOp2 C t₁ t₂ y := by
  have h03 := dRow03_flip2_eq_ne C t₁ t₂ htne h1 h7 y (by simp [hy1, hy2])
  have h12 := dRow12_flip2_add_two C t₁ t₂ htne h1 h7 y hy1 hy2
  unfold dOp2 dO
  change min (dRow C 0 y) (min (dRow C 1 y) (dRow C 3 y)) ≤
    min (dRow C 0 (flipTwoBits t₁ t₂ y))
      (min (dRow C 1 (flipTwoBits t₁ t₂ y)) (dRow C 3 (flipTwoBits t₁ t₂ y)))
  rw [h03.1, h03.2]
  have hle : dRow C 1 y ≤ dRow C 1 (flipTwoBits t₁ t₂ y) := by omega
  exact min_le_min le_rfl (min_le_min hle le_rfl)

/-- d_P' + 2 = d_P when (y t₁ = true, y t₂ = false). -/
lemma dPp2_add_two_of_htrue_hfalse {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (htne : t₁ ≠ t₂)
    (h1 : C t₁ = col1) (h7 : C t₂ = col7) (y : Word n)
    (hy1 : y t₁ = true) (hy2 : y t₂ = false) :
    dPp2 C t₁ t₂ y + 2 = dP C y := by
  unfold dPp2 dP
  exact (dRow12_flip2_sub_two C t₁ t₂ htne h1 h7 y hy1 hy2).2

/-- d_P + 2 = d_P' when (y t₁ = false, y t₂ = true). -/
lemma dP_add_two_of_hfalse_htrue {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (htne : t₁ ≠ t₂)
    (h1 : C t₁ = col1) (h7 : C t₂ = col7) (y : Word n)
    (hy1 : y t₁ = false) (hy2 : y t₂ = true) :
    dP C y + 2 = dPp2 C t₁ t₂ y := by
  unfold dPp2 dP
  exact (dRow12_flip2_add_two C t₁ t₂ htne h1 h7 y hy1 hy2).2.symm

/-! ## Replacement structure: C' = (t₁ ↦ col3, t₂ ↦ col5) -/

/-- Replacing the two columns changes only row 2 (j ≠ 2 unchanged). -/
lemma dRow_replace_27_eq {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (htne : t₁ ≠ t₂)
    (j : Fin 4) (hj : j ≠ 2) (y : Word n) (h1 : C t₁ = col1) (h7 : C t₂ = col7) :
    dRow (replaceColumn (replaceColumn C t₁ col3) t₂ col5) j y = dRow C j y := by
  rw [dRow_eq_indicator_sum, dRow_eq_indicator_sum]
  apply Finset.sum_congr rfl
  intro u _
  by_cases hu1 : u = t₁
  · by_cases hu2 : u = t₂
    · exfalso
      exact htne (hu1.symm.trans hu2)
    · simp [replaceColumn, hu1, h1]
      have ht' : ¬ t₁ = t₂ := fun h => hu2 (hu1.trans h)
      simp [if_neg ht']
      have hb : colBit j col3 = colBit j col1 := by
        fin_cases j <;> simp [colBit, col1, col3] at hj ⊢
      rw [hb]
  · by_cases hu2 : u = t₂
    · simp [replaceColumn, hu2, h7]
      have hb : colBit j col5 = colBit j col7 := by
        fin_cases j <;> simp [colBit, col7, col5] at hj ⊢
      simp [hb]
    · simp [replaceColumn, hu1, hu2]

/-- Row 2 of the new code equals the old row-2 distance at the flipped word. -/
lemma dRow_replace_27_2 {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (htne : t₁ ≠ t₂)
    (y : Word n) (h1 : C t₁ = col1) (h7 : C t₂ = col7) :
    dRow (replaceColumn (replaceColumn C t₁ col3) t₂ col5) ⟨2, by decide⟩ y =
      dRow C ⟨2, by decide⟩ (flipTwoBits t₁ t₂ y) := by
  rw [dRow_eq_indicator_sum, dRow_eq_indicator_sum]
  apply Finset.sum_congr rfl
  intro u _
  by_cases hu1 : u = t₁
  · by_cases hu2 : u = t₂
    · exfalso
      exact htne (hu1.symm.trans hu2)
    · have ht' : ¬ t₁ = t₂ := fun h => hu2 (hu1.trans h)
      by_cases hyu : y u = true <;>
        simp [replaceColumn, flipTwoBits, hu1, h1, colBit, col1, col3, ht']
  · by_cases hu2 : u = t₂
    · have ht' : ¬ t₁ = t₂ := fun h => hu1 (hu2.trans h.symm)
      by_cases hyu : y u = true <;>
        simp [replaceColumn, flipTwoBits, hu2, h7, colBit, col7, col5]
    · by_cases hyu : y u = true <;>
        simp [replaceColumn, flipTwoBits, hu1, hu2, hyu]

/-- d_{C'}(y) = min(d_O(y), d_P'(y)) for the two-column change (paper eq. dcp). -/
lemma dCode_replace_27 {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (htne : t₁ ≠ t₂) (y : Word n)
    (h1 : C t₁ = col1) (h7 : C t₂ = col7) :
    dCode (replaceColumn (replaceColumn C t₁ col3) t₂ col5) y =
      min (dO C y) (dPp2 C t₁ t₂ y) := by
  unfold dCode dO dPp2 dP
  change min (dRow (replaceColumn (replaceColumn C t₁ col3) t₂ col5) ⟨0, by decide⟩ y)
      (min (dRow (replaceColumn (replaceColumn C t₁ col3) t₂ col5) ⟨1, by decide⟩ y)
        (min (dRow (replaceColumn (replaceColumn C t₁ col3) t₂ col5) ⟨2, by decide⟩ y)
          (dRow (replaceColumn (replaceColumn C t₁ col3) t₂ col5) ⟨3, by decide⟩ y))) =
    min (min (dRow C ⟨0, by decide⟩ y) (min (dRow C ⟨1, by decide⟩ y) (dRow C ⟨3, by decide⟩ y)))
      (dRow C ⟨2, by decide⟩ (flipTwoBits t₁ t₂ y))
  rw [dRow_replace_27_eq C t₁ t₂ htne ⟨0, by decide⟩ (by decide) y h1 h7,
    dRow_replace_27_eq C t₁ t₂ htne ⟨1, by decide⟩ (by decide) y h1 h7,
    dRow_replace_27_2 C t₁ t₂ htne y h1 h7,
    dRow_replace_27_eq C t₁ t₂ htne ⟨3, by decide⟩ (by decide) y h1 h7]
  omega

/-- d_{C'}(F₂ y) = min(d_O'(y), d_P(y)) for the two-column change (paper eq. dcpf). -/
lemma dCode_replace_flip_27 {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (htne : t₁ ≠ t₂) (y : Word n)
    (h1 : C t₁ = col1) (h7 : C t₂ = col7) :
    dCode (replaceColumn (replaceColumn C t₁ col3) t₂ col5) (flipTwoBits t₁ t₂ y) =
      min (dOp2 C t₁ t₂ y) (dP C y) := by
  rw [dCode_replace_27 C t₁ t₂ htne (flipTwoBits t₁ t₂ y) h1 h7]
  unfold dOp2 dPp2
  rw [flipTwoBits_involutive t₁ t₂ y]

/-- C' is exactly the two-column replacement. -/
lemma replace_27_eq {n : ℕ} (C C' : Code n) (t₁ t₂ : Fin n) (htne : t₁ ≠ t₂)
    (h3 : C' t₁ = col3) (h5 : C' t₂ = col5)
    (hsame : ∀ u : Fin n, u ≠ t₁ → u ≠ t₂ → C' u = C u) :
    C' = replaceColumn (replaceColumn C t₁ col3) t₂ col5 := by
  funext u
  by_cases hu1 : u = t₁
  · by_cases hu2 : u = t₂
    · exfalso
      exact htne (hu1.symm.trans hu2)
    · have ht' : ¬ t₁ = t₂ := fun h => hu2 (hu1.trans h)
      simp [replaceColumn, hu1, h3, if_neg ht']
  · by_cases hu2 : u = t₂
    · have ht' : ¬ t₁ = t₂ := fun h => hu1 (hu2.trans h.symm)
      simp [replaceColumn, hu2, h5]
    · simp [replaceColumn, hu1, hu2, hsame u hu1 hu2]

/-! ## Orientation of the Z sets -/

/-- y ∈ Z4 forces y t₁ = true, y t₂ = false. -/
lemma Z4_implies_htrue_hfalse {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (htne : t₁ ≠ t₂)
    (h1 : C t₁ = col1) (h7 : C t₂ = col7) {y : Word n} (hy : Z4 C t₁ t₂ y) :
    y t₁ = true ∧ y t₂ = false := by
  rcases bool_ne_cases hy.1 with hyo | hyo
  · exact hyo
  · exfalso
    rcases hyo with ⟨hy1, hy2⟩
    have hO := dO_le_dOp2_of_hfalse_htrue C t₁ t₂ htne h1 h7 y hy1 hy2
    have hP := dP_add_two_of_hfalse_htrue C t₁ t₂ htne h1 h7 y hy1 hy2
    have hgt1 : dO C y > min (dP C y) (dPp2 C t₁ t₂ y) := hy.2.1
    have hgt2 : dP C y > min (dO C y) (dOp2 C t₁ t₂ y) := hy.2.2.1
    have hmin1 : min (dP C y) (dPp2 C t₁ t₂ y) = dP C y := by
      rw [← hP, min_eq_left]
      omega
    have hmin2 : min (dO C y) (dOp2 C t₁ t₂ y) = dO C y := by
      exact min_eq_left hO
    omega

/-- y ∈ Z5 forces y t₁ = true, y t₂ = false. -/
lemma Z5_implies_htrue_hfalse {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (htne : t₁ ≠ t₂)
    (h1 : C t₁ = col1) (h7 : C t₂ = col7) {y : Word n} (hy : Z5 C t₁ t₂ y) :
    y t₁ = true ∧ y t₂ = false := by
  rcases bool_ne_cases hy.1 with hyo | hyo
  · exact hyo
  · exfalso
    rcases hyo with ⟨hy1, hy2⟩
    have hO := dO_le_dOp2_of_hfalse_htrue C t₁ t₂ htne h1 h7 y hy1 hy2
    have hP := dP_add_two_of_hfalse_htrue C t₁ t₂ htne h1 h7 y hy1 hy2
    have hgt1 : dO C y > min (dP C y) (dPp2 C t₁ t₂ y) := hy.2.1
    have hgt2 : dP C y > min (dO C y) (dOp2 C t₁ t₂ y) := hy.2.2.1
    have hmin1 : min (dP C y) (dPp2 C t₁ t₂ y) = dP C y := by
      rw [← hP, min_eq_left]
      omega
    have hmin2 : min (dO C y) (dOp2 C t₁ t₂ y) = dO C y := by
      exact min_eq_left hO
    omega

/-- Lemma `lemma:2` (Lemma 22): Z1..Z5 form a partition of the word space. -/
theorem z_partition {n : ℕ} (C _C' : Code n) (t₁ t₂ : Fin n) :
    ∀ y : Word n, ∃! i : Fin 5, ZSet C t₁ t₂ i y := by
  intro y
  by_cases heq : y t₁ = y t₂
  · refine ⟨⟨0, by decide⟩, ?_, ?_⟩
    · simp [ZSet, Z1, heq]
    · intro j hj
      have hz := by simpa [ZSet] using hj
      fin_cases j
      · rfl
      · exfalso
        exact hz.1 heq
      · exfalso
        exact hz.1 heq
      · exfalso
        exact hz.1 heq
      · exfalso
        exact hz.1 heq
  · have hne : y t₁ ≠ y t₂ := heq
    by_cases h2 : dO C y ≤ min (dP C y) (dPp2 C t₁ t₂ y)
    · refine ⟨⟨1, by decide⟩, ?_, ?_⟩
      · simp [ZSet, Z2, hne, h2]
      · intro j hj
        have hz := by simpa [ZSet] using hj
        fin_cases j
        · exfalso
          exact hne hz
        · rfl
        · exfalso
          exact (not_lt_of_ge h2) hz.2.1
        · exfalso
          exact (not_lt_of_ge h2) hz.2.1
        · exfalso
          exact (not_lt_of_ge h2) hz.2.1
    · have hgt : dO C y > min (dP C y) (dPp2 C t₁ t₂ y) := lt_of_not_ge h2
      by_cases h3 : dP C y ≤ min (dO C y) (dOp2 C t₁ t₂ y)
      · refine ⟨⟨2, by decide⟩, ?_, ?_⟩
        · simp [ZSet, Z3, hne, hgt, h3]
        · intro j hj
          have hz := by simpa [ZSet] using hj
          fin_cases j
          · exfalso
            exact hne hz
          · exfalso
            exact (not_lt_of_ge hz.2) hgt
          · rfl
          · exfalso
            exact (not_lt_of_ge h3) hz.2.2.1
          · exfalso
            exact (not_lt_of_ge h3) hz.2.2.1
      · have hgt2 : dP C y > min (dO C y) (dOp2 C t₁ t₂ y) := lt_of_not_ge h3
        by_cases h4 : min (dO C y) (dOp2 C t₁ t₂ y) ≤ dPp2 C t₁ t₂ y
        · refine ⟨⟨4, by decide⟩, ?_, ?_⟩
          · simp [ZSet, Z5, hne, hgt, hgt2, h4]
          · intro j hj
            have hz := by simpa [ZSet] using hj
            fin_cases j
            · exfalso
              exact hne hz
            · exfalso
              exact (not_lt_of_ge hz.2) hgt
            · exfalso
              exact h3 hz.2.2
            · exfalso
              exact (not_lt_of_ge h4) hz.2.2.2
            · rfl
        · refine ⟨⟨3, by decide⟩, ?_, ?_⟩
          · refine ⟨hne, hgt, hgt2, ?_⟩
            exact lt_of_not_ge h4
          · intro j hj
            have hz := by simpa [ZSet] using hj
            fin_cases j
            · exfalso
              exact hne hz
            · exfalso
              exact (not_lt_of_ge hz.2) hgt
            · exfalso
              exact h3 hz.2.2
            · rfl
            · exfalso
              exact h4 hz.2.2.2

/-- The complement of Z1 ∪ Z2 ∪ Z5 is Z3 ∪ Z4. -/
lemma z_not_A_implies_34 {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (y : Word n) :
    ¬ (Z1 C t₁ t₂ y ∨ Z2 C t₁ t₂ y ∨ Z5 C t₁ t₂ y) → (Z3 C t₁ t₂ y ∨ Z4 C t₁ t₂ y) := by
  intro hnot
  rcases z_partition C C t₁ t₂ y with ⟨i, hi, _⟩
  fin_cases i
  · exfalso
    exact hnot (Or.inl (by simpa [ZSet] using hi))
  · exfalso
    exact hnot (Or.inr (Or.inl (by simpa [ZSet] using hi)))
  · exact Or.inl (by simpa [ZSet] using hi)
  · exact Or.inr (by simpa [ZSet] using hi)
  · exfalso
    exact hnot (Or.inr (Or.inr (by simpa [ZSet] using hi)))

/-- Distance values at F₂ y in terms of their values at y, (t,f) orientation. -/
lemma distances_flip2_htrue_hfalse {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (htne : t₁ ≠ t₂)
    (h1 : C t₁ = col1) (h7 : C t₂ = col7) (y : Word n)
    (hy1 : y t₁ = true) (hy2 : y t₂ = false) :
    dO C (flipTwoBits t₁ t₂ y) = dOp2 C t₁ t₂ y ∧
      dP C (flipTwoBits t₁ t₂ y) + 2 = dP C y ∧
      dOp2 C t₁ t₂ (flipTwoBits t₁ t₂ y) = dO C y ∧
      dPp2 C t₁ t₂ (flipTwoBits t₁ t₂ y) = dP C y := by
  constructor
  · rfl
  · constructor
    · unfold dP
      exact (dRow12_flip2_sub_two C t₁ t₂ htne h1 h7 y hy1 hy2).2
    · constructor
      · unfold dOp2
        rw [flipTwoBits_involutive t₁ t₂ y]
      · unfold dPp2
        rw [flipTwoBits_involutive t₁ t₂ y]

/-- Distance values at F₂ y in terms of their values at y, (f,t) orientation. -/
lemma distances_flip2_hfalse_htrue {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (htne : t₁ ≠ t₂)
    (h1 : C t₁ = col1) (h7 : C t₂ = col7) (y : Word n)
    (hy1 : y t₁ = false) (hy2 : y t₂ = true) :
    dO C (flipTwoBits t₁ t₂ y) = dOp2 C t₁ t₂ y ∧
      dP C (flipTwoBits t₁ t₂ y) = dP C y + 2 ∧
      dOp2 C t₁ t₂ (flipTwoBits t₁ t₂ y) = dO C y ∧
      dPp2 C t₁ t₂ (flipTwoBits t₁ t₂ y) = dP C y := by
  constructor
  · rfl
  · constructor
    · unfold dP
      exact (dRow12_flip2_add_two C t₁ t₂ htne h1 h7 y hy1 hy2).2
    · constructor
      · unfold dOp2
        rw [flipTwoBits_involutive t₁ t₂ y]
      · unfold dPp2
        rw [flipTwoBits_involutive t₁ t₂ y]

/-- F₂ maps Z3 ∪ Z4 into itself (paper eq. y34p). -/
lemma Z34_flip2_closed {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (htne : t₁ ≠ t₂)
    (h1 : C t₁ = col1) (h7 : C t₂ = col7) (y : Word n) :
    (Z3 C t₁ t₂ y ∨ Z4 C t₁ t₂ y) →
      (Z3 C t₁ t₂ (flipTwoBits t₁ t₂ y) ∨ Z4 C t₁ t₂ (flipTwoBits t₁ t₂ y)) := by
  intro hz
  have hne : y t₁ ≠ y t₂ := by
    rcases hz with hz | hz
    · exact hz.1
    · exact hz.1
  rcases bool_ne_cases hne with hyo | hyo
  · rcases hyo with ⟨hy1, hy2⟩
    have hd := distances_flip2_htrue_hfalse C t₁ t₂ htne h1 h7 y hy1 hy2
    have hdO' : dO C (flipTwoBits t₁ t₂ y) = dOp2 C t₁ t₂ y := hd.1
    have hdP' : dP C (flipTwoBits t₁ t₂ y) = dP C y - 2 := by omega
    have hdOp2' : dOp2 C t₁ t₂ (flipTwoBits t₁ t₂ y) = dO C y := hd.2.2.1
    have hdPp2' : dPp2 C t₁ t₂ (flipTwoBits t₁ t₂ y) = dP C y := hd.2.2.2
    have hPp_lt_P : dPp2 C t₁ t₂ y < dP C y := by
      have hPp := dPp2_add_two_of_htrue_hfalse C t₁ t₂ htne h1 h7 y hy1 hy2
      omega
    have hmin0 : min (dP C y) (dPp2 C t₁ t₂ y) = dPp2 C t₁ t₂ y :=
      min_eq_right (le_of_lt hPp_lt_P)
    have hOp_le_O : dOp2 C t₁ t₂ y ≤ dO C y :=
      dOp2_le_dO_of_htrue_hfalse C t₁ t₂ htne h1 h7 y hy1 hy2
    rcases hz with hz | hz
    · rcases hz with ⟨_, hgt, hle⟩
      left
      unfold Z3
      refine ⟨?_, ?_, ?_⟩
      · simp [flipTwoBits, hy1, hy2]
      · rw [hdO', hdP', hdPp2']
        have hmin : min (dP C y - 2) (dP C y) = dP C y - 2 := by
          apply min_eq_left
          omega
        rw [hmin]
        have hOp_ge_P : dOp2 C t₁ t₂ y ≥ dP C y := le_trans hle (min_le_right _ _)
        omega
      · rw [hdP', hdOp2', hdO']
        have hP_le_Op : dP C y ≤ dOp2 C t₁ t₂ y := le_trans hle (min_le_right _ _)
        have hP_le_O : dP C y ≤ dO C y := le_trans hle (min_le_left _ _)
        have hgt' : dO C y > dPp2 C t₁ t₂ y := by
          rw [hmin0] at hgt
          exact hgt
        have hdO_ge : dP C y - 2 ≤ dO C y := by omega
        have hdOp_ge : dP C y - 2 ≤ dOp2 C t₁ t₂ y := by omega
        exact le_min hdOp_ge hdO_ge
    · rcases hz with ⟨_, _, hgt24, hlt⟩
      left
      unfold Z3
      refine ⟨?_, ?_, ?_⟩
      · simp [flipTwoBits, hy1, hy2]
      · rw [hdO', hdP', hdPp2']
        have hmin0' : min (dO C y) (dOp2 C t₁ t₂ y) = dOp2 C t₁ t₂ y :=
          min_eq_right hOp_le_O
        have hPp_lt_Op : dPp2 C t₁ t₂ y < dOp2 C t₁ t₂ y := by
          rw [hmin0'] at hlt
          exact hlt
        have hOp_lt_P : dOp2 C t₁ t₂ y < dP C y := by
          rw [hmin0'] at hgt24
          exact hgt24
        have hPp' : dPp2 C t₁ t₂ y + 2 = dP C y :=
          dPp2_add_two_of_htrue_hfalse C t₁ t₂ htne h1 h7 y hy1 hy2
        have hOp_eq : dOp2 C t₁ t₂ y = dP C y - 1 := by omega
        have hmin : min (dP C y - 2) (dP C y) = dP C y - 2 := by
          apply min_eq_left
          omega
        rw [hmin, hOp_eq]
        omega
      · rw [hdP', hdOp2', hdO']
        have hmin0' : min (dO C y) (dOp2 C t₁ t₂ y) = dOp2 C t₁ t₂ y :=
          min_eq_right hOp_le_O
        have hPp_lt_Op : dPp2 C t₁ t₂ y < dOp2 C t₁ t₂ y := by
          rw [hmin0'] at hlt
          exact hlt
        have hOp_lt_P : dOp2 C t₁ t₂ y < dP C y := by
          rw [hmin0'] at hgt24
          exact hgt24
        have hPp' : dPp2 C t₁ t₂ y + 2 = dP C y :=
          dPp2_add_two_of_htrue_hfalse C t₁ t₂ htne h1 h7 y hy1 hy2
        have hOp_eq : dOp2 C t₁ t₂ y = dP C y - 1 := by omega
        have hO_ge : dO C y ≥ dP C y - 1 := by omega
        have hdP_ge : dP C y - 2 ≤ dOp2 C t₁ t₂ y := by omega
        have hdO_ge : dP C y - 2 ≤ dO C y := by omega
        exact le_min hdP_ge hdO_ge
  · rcases hyo with ⟨hy1, hy2⟩
    have hd := distances_flip2_hfalse_htrue C t₁ t₂ htne h1 h7 y hy1 hy2
    have hdO' : dO C (flipTwoBits t₁ t₂ y) = dOp2 C t₁ t₂ y := hd.1
    have hdP' : dP C (flipTwoBits t₁ t₂ y) = dP C y + 2 := hd.2.1
    have hdOp2' : dOp2 C t₁ t₂ (flipTwoBits t₁ t₂ y) = dO C y := hd.2.2.1
    have hdPp2' : dPp2 C t₁ t₂ (flipTwoBits t₁ t₂ y) = dP C y := hd.2.2.2
    rcases hz with hz | hz
    · rcases hz with ⟨_, hgt, hle⟩
      have hOp_ge_O : dO C y ≤ dOp2 C t₁ t₂ y :=
        dO_le_dOp2_of_hfalse_htrue C t₁ t₂ htne h1 h7 y hy1 hy2
      have hP_lt_Pp : dP C y < dPp2 C t₁ t₂ y := by
        have hP := dP_add_two_of_hfalse_htrue C t₁ t₂ htne h1 h7 y hy1 hy2
        omega
      have hmin0 : min (dP C y) (dPp2 C t₁ t₂ y) = dP C y :=
        min_eq_left (le_of_lt hP_lt_Pp)
      have hO_gt_P : dO C y > dP C y := by
        rw [hmin0] at hgt
        exact hgt
      have hmin2 : min (dOp2 C t₁ t₂ y) (dO C y) = dO C y := min_eq_right hOp_ge_O
      by_cases hbig : dO C y ≥ dP C y + 2
      · left
        unfold Z3
        refine ⟨?_, ?_, ?_⟩
        · simp [flipTwoBits, hy1, hy2]
        · rw [hdO', hdP', hdPp2']
          have hmin : min (dP C y + 2) (dP C y) = dP C y := by
            apply min_eq_right
            omega
          rw [hmin]
          omega
        · rw [hdP', hdOp2', hdO']
          rw [hmin2]
          omega
      · right
        have hO_eq : dO C y = dP C y + 1 := by omega
        unfold Z4
        refine ⟨?_, ?_, ?_, ?_⟩
        · simp [flipTwoBits, hy1, hy2]
        · rw [hdO', hdP', hdPp2']
          have hmin : min (dP C y + 2) (dP C y) = dP C y := by
            apply min_eq_right
            omega
          rw [hmin]
          omega
        · rw [hdP', hdOp2', hdO']
          rw [hmin2, hO_eq]
          omega
        · rw [hdPp2', hdO', hdOp2']
          rw [hmin2, hO_eq]
          omega
    · exfalso
      rcases Z4_implies_htrue_hfalse C t₁ t₂ htne h1 h7 hz with ⟨ht₁, _⟩
      have hb : (true : Bool) = false := by simpa [hy1] using ht₁.symm
      simp at hb

/-- Z3 ∪ Z4 is disjoint from Z1 ∪ Z2 ∪ Z5. -/
lemma z_34_implies_not_A {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (y : Word n) :
    (Z3 C t₁ t₂ y ∨ Z4 C t₁ t₂ y) → ¬ (Z1 C t₁ t₂ y ∨ Z2 C t₁ t₂ y ∨ Z5 C t₁ t₂ y) := by
  rintro hz (h1 | h2 | h5)
  · rcases hz with hz | hz
    · exact hz.1 h1
    · exact hz.1 h1
  · rcases hz with hz | hz
    · exact (not_lt_of_ge h2.2) hz.2.1
    · exact (not_lt_of_ge h2.2) hz.2.1
  · rcases hz with hz | hz
    · exact (not_lt_of_ge hz.2.2) h5.2.2.1
    · exact (not_lt_of_ge h5.2.2.2) hz.2.2.2

/-- Lemma `lemma:2` (Lemma 22): g2 is a bijection. -/
theorem g2_bijective {n : ℕ} (C _C' : Code n) (t₁ t₂ : Fin n) (htne : t₁ ≠ t₂)
    (h1 : C t₁ = col1) (h7 : C t₂ = col7) :
    Function.Bijective (g2 C t₁ t₂) := by
  have hcl : ∀ y : Word n, (Z3 C t₁ t₂ y ∨ Z4 C t₁ t₂ y) →
      (Z3 C t₁ t₂ (flipTwoBits t₁ t₂ y) ∨ Z4 C t₁ t₂ (flipTwoBits t₁ t₂ y)) :=
    Z34_flip2_closed C t₁ t₂ htne h1 h7
  have hinv : ∀ y : Word n, g2 C t₁ t₂ (g2 C t₁ t₂ y) = y := by
    intro y
    by_cases hy : Z1 C t₁ t₂ y ∨ Z2 C t₁ t₂ y ∨ Z5 C t₁ t₂ y
    · simp [g2, hy]
    · have hz : Z3 C t₁ t₂ y ∨ Z4 C t₁ t₂ y := z_not_A_implies_34 C t₁ t₂ y hy
      have hcl' := hcl y hz
      have hnotA : ¬ (Z1 C t₁ t₂ (flipTwoBits t₁ t₂ y) ∨ Z2 C t₁ t₂ (flipTwoBits t₁ t₂ y) ∨
          Z5 C t₁ t₂ (flipTwoBits t₁ t₂ y)) :=
        z_34_implies_not_A C t₁ t₂ (flipTwoBits t₁ t₂ y) hcl'
      simp [g2, hy, hnotA, flipTwoBits_involutive t₁ t₂ y]
  refine ⟨?_, ?_⟩
  · intro a b hab
    rw [← hinv a, ← hinv b, hab]
  · intro z
    exact ⟨g2 C t₁ t₂ z, hinv z⟩

/-- Lemma `lemma:2` (Lemma 22) (1): y ∈ Z1 → d_C(y) = d_C'(y). -/
theorem z_rel_1 {n : ℕ} (C C' : Code n) (t₁ t₂ : Fin n) (htne : t₁ ≠ t₂)
    (h1 : C t₁ = col1) (h7 : C t₂ = col7)
    (h3 : C' t₁ = col3) (h5 : C' t₂ = col5)
    (hsame : ∀ u : Fin n, u ≠ t₁ → u ≠ t₂ → C' u = C u) {y : Word n}
    (hy : Z1 C t₁ t₂ y) : dCode C y = dCode C' y := by
  have hrep : C' = replaceColumn (replaceColumn C t₁ col3) t₂ col5 :=
    replace_27_eq C C' t₁ t₂ htne h3 h5 hsame
  have hdC : dCode C y = min (dO C y) (dP C y) := dCode_eq_min_dO_dP C y
  have hdC' : dCode C' y = min (dO C y) (dPp2 C t₁ t₂ y) := by
    rw [hrep, dCode_replace_27 C t₁ t₂ htne y h1 h7]
  have hP : dPp2 C t₁ t₂ y = dP C y := dPp2_eq_dP_of_eq C t₁ t₂ htne h1 h7 y hy
  rw [hdC, hdC', hP]

/-- Lemma `lemma:2` (Lemma 22) (2): y ∈ Z2 → d_C(y) = d_C'(y) = d_O. -/
theorem z_rel_2 {n : ℕ} (C C' : Code n) (t₁ t₂ : Fin n) (htne : t₁ ≠ t₂)
    (h1 : C t₁ = col1) (h7 : C t₂ = col7)
    (h3 : C' t₁ = col3) (h5 : C' t₂ = col5)
    (hsame : ∀ u : Fin n, u ≠ t₁ → u ≠ t₂ → C' u = C u) {y : Word n}
    (hy : Z2 C t₁ t₂ y) : dCode C y = dCode C' y ∧ dCode C y = dO C y := by
  have hrep : C' = replaceColumn (replaceColumn C t₁ col3) t₂ col5 :=
    replace_27_eq C C' t₁ t₂ htne h3 h5 hsame
  have hdC : dCode C y = min (dO C y) (dP C y) := dCode_eq_min_dO_dP C y
  have hdC' : dCode C' y = min (dO C y) (dPp2 C t₁ t₂ y) := by
    rw [hrep, dCode_replace_27 C t₁ t₂ htne y h1 h7]
  rcases hy with ⟨_hne, hle⟩
  have hOleP : dO C y ≤ dP C y := le_trans hle (min_le_left _ _)
  have hOlePp : dO C y ≤ dPp2 C t₁ t₂ y := le_trans hle (min_le_right _ _)
  constructor
  · rw [hdC, hdC', min_eq_left hOleP, min_eq_left hOlePp]
  · rw [hdC, min_eq_left hOleP]

/-- Lemma `lemma:2` (Lemma 22) (3): y ∈ Z3 → d_C(y) = d_C'(F2 y) = d_P. -/
theorem z_rel_3 {n : ℕ} (C C' : Code n) (t₁ t₂ : Fin n) (htne : t₁ ≠ t₂)
    (h1 : C t₁ = col1) (h7 : C t₂ = col7)
    (h3 : C' t₁ = col3) (h5 : C' t₂ = col5)
    (hsame : ∀ u : Fin n, u ≠ t₁ → u ≠ t₂ → C' u = C u) {y : Word n}
    (hy : Z3 C t₁ t₂ y) :
    dCode C y = dCode C' (flipTwoBits t₁ t₂ y) ∧ dCode C y = dP C y := by
  have hrep : C' = replaceColumn (replaceColumn C t₁ col3) t₂ col5 :=
    replace_27_eq C C' t₁ t₂ htne h3 h5 hsame
  have hdC : dCode C y = min (dO C y) (dP C y) := dCode_eq_min_dO_dP C y
  have hdC'f : dCode C' (flipTwoBits t₁ t₂ y) = min (dOp2 C t₁ t₂ y) (dP C y) := by
    rw [hrep, dCode_replace_flip_27 C t₁ t₂ htne y h1 h7]
  rcases hy with ⟨_hne, _hgt, hle⟩
  have hPleO : dP C y ≤ dO C y := le_trans hle (min_le_left _ _)
  have hPleOp : dP C y ≤ dOp2 C t₁ t₂ y := le_trans hle (min_le_right _ _)
  constructor
  · rw [hdC, hdC'f, min_eq_right hPleO, min_eq_right hPleOp]
  · rw [hdC, min_eq_right hPleO]

/-- Lemma `lemma:2` (Lemma 22) (4): y ∈ Z4 → d_C(y) = min(d_O,d_P) ∧ d_P ≥ d_C'(F2 y) = d_O'. -/
theorem z_rel_4 {n : ℕ} (C C' : Code n) (t₁ t₂ : Fin n) (htne : t₁ ≠ t₂)
    (h1 : C t₁ = col1) (h7 : C t₂ = col7)
    (h3 : C' t₁ = col3) (h5 : C' t₂ = col5)
    (hsame : ∀ u : Fin n, u ≠ t₁ → u ≠ t₂ → C' u = C u) {y : Word n}
    (hy : Z4 C t₁ t₂ y) :
    dCode C y = min (dO C y) (dP C y) ∧
      dCode C' (flipTwoBits t₁ t₂ y) = dOp2 C t₁ t₂ y ∧
        dP C y ≥ dCode C' (flipTwoBits t₁ t₂ y) := by
  have hrep : C' = replaceColumn (replaceColumn C t₁ col3) t₂ col5 :=
    replace_27_eq C C' t₁ t₂ htne h3 h5 hsame
  have hdC : dCode C y = min (dO C y) (dP C y) := dCode_eq_min_dO_dP C y
  have hdC'f : dCode C' (flipTwoBits t₁ t₂ y) = min (dOp2 C t₁ t₂ y) (dP C y) := by
    rw [hrep, dCode_replace_flip_27 C t₁ t₂ htne y h1 h7]
  have hor := Z4_implies_htrue_hfalse C t₁ t₂ htne h1 h7 hy
  rcases hor with ⟨hy1, hy2⟩
  have hOp_lt_P : dOp2 C t₁ t₂ y < dP C y := by
    have hle : dOp2 C t₁ t₂ y ≤ dO C y :=
      dOp2_le_dO_of_htrue_hfalse C t₁ t₂ htne h1 h7 y hy1 hy2
    have hgt : dP C y > min (dO C y) (dOp2 C t₁ t₂ y) := hy.2.2.1
    rw [min_eq_right hle] at hgt
    exact hgt
  constructor
  · exact hdC
  · constructor
    · rw [hdC'f, min_eq_left (le_of_lt hOp_lt_P)]
    · rw [hdC'f, min_eq_left (le_of_lt hOp_lt_P)]
      exact le_of_lt hOp_lt_P

/-- Lemma `lemma:2` (Lemma 22) (5): y ∈ Z5 → d_C(y) = min(d_O,d_P) ∧ d_P > d_C'(y) = d_P'. -/
theorem z_rel_5 {n : ℕ} (C C' : Code n) (t₁ t₂ : Fin n) (htne : t₁ ≠ t₂)
    (h1 : C t₁ = col1) (h7 : C t₂ = col7)
    (h3 : C' t₁ = col3) (h5 : C' t₂ = col5)
    (hsame : ∀ u : Fin n, u ≠ t₁ → u ≠ t₂ → C' u = C u) {y : Word n}
    (hy : Z5 C t₁ t₂ y) :
    dCode C y = min (dO C y) (dP C y) ∧ dP C y > dCode C' y ∧ dCode C' y = dP C' y := by
  have hrep : C' = replaceColumn (replaceColumn C t₁ col3) t₂ col5 :=
    replace_27_eq C C' t₁ t₂ htne h3 h5 hsame
  have hdC : dCode C y = min (dO C y) (dP C y) := dCode_eq_min_dO_dP C y
  have hdC' : dCode C' y = min (dO C y) (dPp2 C t₁ t₂ y) := by
    rw [hrep, dCode_replace_27 C t₁ t₂ htne y h1 h7]
  have hor := Z5_implies_htrue_hfalse C t₁ t₂ htne h1 h7 hy
  rcases hor with ⟨hy1, hy2⟩
  have hPp_lt_O : dPp2 C t₁ t₂ y < dO C y := by
    have hP : dPp2 C t₁ t₂ y + 2 = dP C y :=
      dPp2_add_two_of_htrue_hfalse C t₁ t₂ htne h1 h7 y hy1 hy2
    have hPp_le_P : dPp2 C t₁ t₂ y ≤ dP C y := by omega
    have hmin : min (dP C y) (dPp2 C t₁ t₂ y) = dPp2 C t₁ t₂ y :=
      min_eq_right hPp_le_P
    have hgt : dO C y > min (dP C y) (dPp2 C t₁ t₂ y) := hy.2.1
    rw [hmin] at hgt
    exact hgt
  constructor
  · exact hdC
  · constructor
    · rw [hdC', min_eq_right (le_of_lt hPp_lt_O)]
      have hP : dPp2 C t₁ t₂ y + 2 = dP C y :=
        dPp2_add_two_of_htrue_hfalse C t₁ t₂ htne h1 h7 y hy1 hy2
      omega
    · rw [hdC', min_eq_right (le_of_lt hPp_lt_O)]
      rw [hrep]
      change dRow C ⟨2, by decide⟩ (flipTwoBits t₁ t₂ y) =
        dRow (replaceColumn (replaceColumn C t₁ col3) t₂ col5) ⟨2, by decide⟩ y
      rw [dRow_replace_27_2 C t₁ t₂ htne y h1 h7]

-- decide: Mechanical · n=any · checked 2026-08-27
/-- w(c₂ ⊕ c₃) = |2|+|3|+|4|+|5| for a Columns07 code (paper eq. w4, published (28)). -/
lemma hammingDist_row1_row2_eq {n : ℕ} (C : Code n) (h07 : Columns07 C) :
    hammingDist (row1 C) (row2 C) = count C 2 + count C 3 + count C 4 + count C 5 := by
  have hS : ∀ t : Fin n, colVal (C t) ∈ Finset.Icc 0 7 := by
    intro t
    rw [Finset.mem_Icc]
    exact ⟨Nat.zero_le _, Columns07_le7 C h07 t⟩
  unfold row1 row2
  rw [hammingDist_rows_of_types C ⟨1, by decide⟩ ⟨2, by decide⟩ (Finset.Icc 0 7) hS, sum_Icc0_7]
  have h20 : (2 : ℕ).testBit 2 = false := by decide
  have h21 : (2 : ℕ).testBit 1 = true := by decide
  have h30 : (3 : ℕ).testBit 2 = false := by decide
  have h31 : (3 : ℕ).testBit 1 = true := by decide
  have h40 : (4 : ℕ).testBit 2 = true := by decide
  have h41 : (4 : ℕ).testBit 1 = false := by decide
  have h50 : (5 : ℕ).testBit 2 = true := by decide
  have h51 : (5 : ℕ).testBit 1 = false := by decide
  have h10 : (1 : ℕ).testBit 2 = false := by decide
  have h11 : (1 : ℕ).testBit 1 = false := by decide
  have h60 : (6 : ℕ).testBit 2 = true := by decide
  have h61 : (6 : ℕ).testBit 1 = true := by decide
  have h70 : (7 : ℕ).testBit 2 = true := by decide
  have h71 : (7 : ℕ).testBit 1 = true := by decide
  have h00 : (0 : ℕ).testBit 2 = false := by decide
  have h01 : (0 : ℕ).testBit 1 = false := by decide
  simp [h00, h01, h10, h11, h20, h21, h30, h31, h40, h41, h50, h51, h60, h61, h70, h71]

-- decide: Mechanical · n=any · checked 2026-08-27
/-- d₁ and d₂ in terms of the per-type weights for a Columns07 code. -/
lemma dRow12_columns07 {n : ℕ} (C : Code n) (y : Word n) (h07 : Columns07 C) :
    dRow C 1 y = w_i C 0 y + w_i C 1 y + w_i C 2 y + w_i C 3 y +
      (count C 4 - w_i C 4 y) + (count C 5 - w_i C 5 y) +
      (count C 6 - w_i C 6 y) + (count C 7 - w_i C 7 y) ∧
    dRow C 2 y = w_i C 0 y + w_i C 1 y + w_i C 4 y + w_i C 5 y +
      (count C 2 - w_i C 2 y) + (count C 3 - w_i C 3 y) +
      (count C 6 - w_i C 6 y) + (count C 7 - w_i C 7 y) := by
  have hS : ∀ t : Fin n, colVal (C t) ∈ Finset.Icc 0 7 := by
    intro t
    have hle := Columns07_le7 C h07 t
    simp [Finset.mem_Icc, hle]
  have hSle : (Finset.Icc 0 7 : Finset ℕ) ⊆ Finset.Icc 0 15 := by
    intro i hi
    simp [Finset.mem_Icc] at hi ⊢
    omega
  have hsum : ∀ j : Fin 4, dRow C j y = ∑ i ∈ Finset.Icc 0 7,
      if i.testBit (3 - j.val) then count C i - w_i C i y else w_i C i y := by
    intro j
    exact dRow_eq_sum_types C j y (Finset.Icc 0 7) hSle hS
  have h12 : (1 : ℕ).testBit 2 = false := by decide
  have h22 : (2 : ℕ).testBit 2 = false := by decide
  have h32 : (3 : ℕ).testBit 2 = false := by decide
  have h42 : (4 : ℕ).testBit 2 = true := by decide
  have h52 : (5 : ℕ).testBit 2 = true := by decide
  have h62 : (6 : ℕ).testBit 2 = true := by decide
  have h72 : (7 : ℕ).testBit 2 = true := by decide
  have h02 : (0 : ℕ).testBit 2 = false := by decide
  have h11 : (1 : ℕ).testBit 1 = false := by decide
  have h21 : (2 : ℕ).testBit 1 = true := by decide
  have h31 : (3 : ℕ).testBit 1 = true := by decide
  have h41 : (4 : ℕ).testBit 1 = false := by decide
  have h51 : (5 : ℕ).testBit 1 = false := by decide
  have h61 : (6 : ℕ).testBit 1 = true := by decide
  have h71 : (7 : ℕ).testBit 1 = true := by decide
  have h01 : (0 : ℕ).testBit 1 = false := by decide
  have hd1 : dRow C 1 y = w_i C 0 y + w_i C 1 y + w_i C 2 y + w_i C 3 y +
      (count C 4 - w_i C 4 y) + (count C 5 - w_i C 5 y) +
      (count C 6 - w_i C 6 y) + (count C 7 - w_i C 7 y) := by
    rw [hsum (1 : Fin 4), sum_Icc0_7]
    simp [h02, h12, h22, h32, h42, h52, h62, h72]
  have hd2 : dRow C 2 y = w_i C 0 y + w_i C 1 y + w_i C 4 y + w_i C 5 y +
      (count C 2 - w_i C 2 y) + (count C 3 - w_i C 3 y) +
      (count C 6 - w_i C 6 y) + (count C 7 - w_i C 7 y) := by
    rw [hsum (2 : Fin 4), sum_Icc0_7]
    simp [h01, h11, h21, h31, h41, h51, h61, h71]
    ac_rfl
  exact ⟨hd1, hd2⟩

/-- d₁ + d₂ = |2|+|3|+|4|+|5| + 2·K (parity of the sum of the two row
distances is the parity of |2|+|3|+|4|+|5|). -/
lemma dRow12_sum_decomp {n : ℕ} (C : Code n) (y : Word n) (h07 : Columns07 C) :
    dRow C 1 y + dRow C 2 y =
      count C 2 + count C 3 + count C 4 + count C 5 +
        2 * (w_i C 0 y + w_i C 1 y + (count C 6 - w_i C 6 y) + (count C 7 - w_i C 7 y)) := by
  rcases dRow12_columns07 C y h07 with ⟨hd1, hd2⟩
  rw [hd1, hd2]
  have hw2 : w_i C 2 y ≤ count C 2 := w_i_le_count C 2 y
  have hw3 : w_i C 3 y ≤ count C 3 := w_i_le_count C 3 y
  have hw4 : w_i C 4 y ≤ count C 4 := w_i_le_count C 4 y
  have hw5 : w_i C 5 y ≤ count C 5 := w_i_le_count C 5 y
  have hw6 : w_i C 6 y ≤ count C 6 := w_i_le_count C 6 y
  have hw7 : w_i C 7 y ≤ count C 7 := w_i_le_count C 7 y
  omega

/-- d_O' = min(d₁, d₂−2, d₄) in the (t,f) orientation. -/
lemma dOp2_eq_min_of_htrue_hfalse {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (htne : t₁ ≠ t₂)
    (h1 : C t₁ = col1) (h7 : C t₂ = col7) (y : Word n)
    (hy1 : y t₁ = true) (hy2 : y t₂ = false) :
    dOp2 C t₁ t₂ y = min (dRow C 0 y) (min (dRow C 1 y - 2) (dRow C 3 y)) := by
  have h03 := dRow03_flip2_eq_ne C t₁ t₂ htne h1 h7 y (by simp [hy1, hy2])
  have h12 := dRow12_flip2_sub_two C t₁ t₂ htne h1 h7 y hy1 hy2
  unfold dOp2 dO
  change min (dRow C 0 (flipTwoBits t₁ t₂ y))
      (min (dRow C 1 (flipTwoBits t₁ t₂ y)) (dRow C 3 (flipTwoBits t₁ t₂ y))) =
    min (dRow C 0 y) (min (dRow C 1 y - 2) (dRow C 3 y))
  rw [h03.1, h03.2]
  have hd1 : dRow C 1 (flipTwoBits t₁ t₂ y) = dRow C 1 y - 2 := by omega
  rw [hd1]

/-- d_P' = d_P − 2 in the (t,f) orientation. -/
lemma dPp2_eq_sub_two_of_htrue_hfalse {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (htne : t₁ ≠ t₂)
    (h1 : C t₁ = col1) (h7 : C t₂ = col7) (y : Word n)
    (hy1 : y t₁ = true) (hy2 : y t₂ = false) :
    dPp2 C t₁ t₂ y = dP C y - 2 := by
  have h12 := dRow12_flip2_sub_two C t₁ t₂ htne h1 h7 y hy1 hy2
  unfold dPp2 dP
  change dRow C 2 (flipTwoBits t₁ t₂ y) = dRow C 2 y - 2
  omega

/-- If min a (min b c) = d with a,c > d, then b = d. -/
lemma min3_eq_of_gt {a b c d : ℕ} (ha : d < a) (hc : d < c) (hm : min a (min b c) = d) :
    b = d := by
  have hle : d ≤ b := by
    rw [← hm]
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hle' : b ≤ d := by
    by_contra hnot
    have hgt : d < b := lt_of_not_ge hnot
    have hb1 : d + 1 ≤ b := Nat.succ_le_of_lt hgt
    have hb2 : d + 1 ≤ a := Nat.succ_le_of_lt ha
    have hb3 : d + 1 ≤ c := Nat.succ_le_of_lt hc
    have hmin_ge : d + 1 ≤ min a (min b c) := by
      apply le_min hb2
      apply le_min hb1 hb3
    rw [hm] at hmin_ge
    omega
  omega

/-- y ∈ Z4¹ forces the (t,f) orientation, d₂ = d₃+1, and d₃ ≤ min(d₁,d₄)
(paper eq. (y41) rewrite). -/
lemma Z41_implies_htrue_hfalse_d2_d3 {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (htne : t₁ ≠ t₂)
    (h1 : C t₁ = col1) (h7 : C t₂ = col7) {y : Word n} (hy : Z41 C t₁ t₂ y) :
    y t₁ = true ∧ y t₂ = false ∧ dRow C 1 y = dRow C 2 y + 1 ∧
      dRow C 2 y ≤ min (dRow C 0 y) (dRow C 3 y) := by
  rcases hy with ⟨hz4, hgt⟩
  rcases Z4_implies_htrue_hfalse C t₁ t₂ htne h1 h7 hz4 with ⟨hy1, hy2⟩
  have hOp := dOp2_eq_min_of_htrue_hfalse C t₁ t₂ htne h1 h7 y hy1 hy2
  have hPp_add : dPp2 C t₁ t₂ y + 2 = dP C y :=
    dPp2_add_two_of_htrue_hfalse C t₁ t₂ htne h1 h7 y hy1 hy2
  have hOp_le_O : dOp2 C t₁ t₂ y ≤ dO C y :=
    dOp2_le_dO_of_htrue_hfalse C t₁ t₂ htne h1 h7 y hy1 hy2
  have hOp_lt_P : dOp2 C t₁ t₂ y < dP C y := by
    have hgt2 : dP C y > min (dO C y) (dOp2 C t₁ t₂ y) := hz4.2.2.1
    rw [min_eq_right hOp_le_O] at hgt2
    exact hgt2
  have hPp_lt_Op : dPp2 C t₁ t₂ y < dOp2 C t₁ t₂ y := by
    have hlt : dPp2 C t₁ t₂ y < min (dO C y) (dOp2 C t₁ t₂ y) := hz4.2.2.2
    rw [min_eq_right hOp_le_O] at hlt
    exact hlt
  have hOp_eq : dOp2 C t₁ t₂ y = dP C y - 1 := by omega
  have hO_ge_P : dO C y ≥ dP C y := by
    have hmin_gt : min (dO C y) (dP C y) > dOp2 C t₁ t₂ y := hgt
    rw [hOp_eq] at hmin_gt
    have hmin_ge : dP C y ≤ min (dO C y) (dP C y) := by
      cases hdP : dP C y with
      | zero => omega
      | succ k =>
          have : k < min (dO C y) (dP C y) := by
            simpa [hdP] using hmin_gt
          exact Nat.succ_le_of_lt (by simpa [hdP] using this)
    rcases le_total (dO C y) (dP C y) with hle | hge
    · have : min (dO C y) (dP C y) = dO C y := min_eq_left hle
      rw [this] at hmin_ge
      omega
    · omega
  have hd0 : dRow C 2 y ≤ dRow C 0 y := by
    have h := le_trans hO_ge_P (min_le_left _ _)
    simpa [dO, dP, dRow, row0, row1, row2, row3] using h
  have hd1le : dRow C 2 y ≤ dRow C 1 y :=
    by
      have h := le_trans hO_ge_P (le_trans (min_le_right _ _) (min_le_left _ _))
      simpa [dO, dP, dRow, row0, row1, row2, row3] using h
  have hd3 : dRow C 2 y ≤ dRow C 3 y :=
    by
      have h := le_trans hO_ge_P (le_trans (min_le_right _ _) (min_le_right _ _))
      simpa [dO, dP, dRow, row0, row1, row2, row3] using h
  have hd2_le_min : dRow C 2 y ≤ min (dRow C 0 y) (dRow C 3 y) := le_min hd0 hd3
  have hRow2_ge_2 : 2 ≤ dRow C 2 y := by
    have hOp_ge_1 : 1 ≤ dOp2 C t₁ t₂ y := by
      exact Nat.succ_le_of_lt (lt_of_le_of_lt (Nat.zero_le _) hPp_lt_Op)
    rw [hOp_eq] at hOp_ge_1
    have : 1 ≤ dRow C 2 y - 1 := by
      simpa [dP, dRow, row2] using hOp_ge_1
    omega
  have hOp' : min (dRow C 0 y) (min (dRow C 1 y - 2) (dRow C 3 y)) = dRow C 2 y - 1 := by
    rw [← hOp]
    simpa [dP, dRow, row2] using hOp_eq
  have hd1' : dRow C 1 y - 2 = dRow C 2 y - 1 := by
    exact min3_eq_of_gt (a := dRow C 0 y) (c := dRow C 3 y)
      (by omega) (by omega) hOp'
  have hd1eq : dRow C 1 y = dRow C 2 y + 1 := by omega
  exact ⟨hy1, hy2, hd1eq, hd2_le_min⟩

/-- Lemma `lemma:y4` (Lemma 24): if w(c2 ⊕ c3) is even then Z4¹ is empty. -/
theorem z4_empty_of_even {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (htne : t₁ ≠ t₂)
    (h1 : C t₁ = col1) (h7 : C t₂ = col7) (h07 : Columns07 C)
    (h : Even (hammingDist (row1 C) (row2 C))) :
    ∀ y : Word n, ¬ Z41 C t₁ t₂ y := by
  intro y hy
  have hw : hammingDist (row1 C) (row2 C) =
      count C 2 + count C 3 + count C 4 + count C 5 :=
    hammingDist_row1_row2_eq C h07
  have hsum_even : Even (count C 2 + count C 3 + count C 4 + count C 5) := by
    simpa [hw] using h
  have hz := Z41_implies_htrue_hfalse_d2_d3 C t₁ t₂ htne h1 h7 hy
  rcases hz with ⟨_hy1, _hy2, hd2, _⟩
  have hdecomp := dRow12_sum_decomp C y h07
  have hsum_odd : Odd (dRow C 1 y + dRow C 2 y) := by
    rw [hd2]
    exact ⟨dRow C 2 y, by omega⟩
  rcases hsum_even with ⟨m, hm⟩
  have heven : Even (dRow C 1 y + dRow C 2 y) := by
    rw [hdecomp, hm]
    exact ⟨m + (w_i C 0 y + w_i C 1 y + (count C 6 - w_i C 6 y) + (count C 7 - w_i C 7 y)),
      by omega⟩
  rcases hsum_odd with ⟨k, hk⟩
  rcases heven with ⟨l, hl⟩
  omega

/-! ## Witness construction for the parity table -/

/-- Pick a k-subset of s (noncomputable choice). -/
noncomputable def pickSubset {n : ℕ} (s : Finset (Fin n)) (k : ℕ) (hk : k ≤ s.card) :
    Finset (Fin n) :=
  Classical.choose (Finset.powersetCard_nonempty_of_le hk)

/-- The picked subset is a k-subset. -/
lemma pickSubset_mem {n : ℕ} {s : Finset (Fin n)} {k : ℕ} (hk : k ≤ s.card) :
    pickSubset s k hk ∈ s.powersetCard k :=
  Classical.choose_spec (Finset.powersetCard_nonempty_of_le hk)

/-- The picked subset is contained in s. -/
lemma pickSubset_subset {n : ℕ} {s : Finset (Fin n)} {k : ℕ} (hk : k ≤ s.card) :
    pickSubset s k hk ⊆ s :=
  (Finset.mem_powersetCard.mp (pickSubset_mem hk)).1

/-- The picked subset has cardinality k. -/
lemma pickSubset_card {n : ℕ} {s : Finset (Fin n)} {k : ℕ} (hk : k ≤ s.card) :
    (pickSubset s k hk).card = k :=
  (Finset.mem_powersetCard.mp (pickSubset_mem hk)).2

/-- A word with prescribed per-type weights and the fixed bits y t₁ = true,
y t₂ = false, where t₁ is a type-1 and t₂ a type-7 column. -/
lemma exists_goodWord_fixed {n : ℕ} (C : Code n) (k : ℕ → ℕ) (t₁ t₂ : Fin n)
    (ht1 : colVal (C t₁) = 1) (ht2 : colVal (C t₂) = 7)
    (hk1 : 1 ≤ k 1) (hk7 : k 7 + 1 ≤ count C 7)
    (hk : ∀ i ∈ Finset.Icc 0 15, k i ≤ count C i) :
    ∃ y : Word n, y t₁ = true ∧ y t₂ = false ∧ ∀ i ∈ Finset.Icc 0 15, w_i C i y = k i := by
  have hf1 : t₁ ∈ fiber C 1 := by simp [fiber, ht1]
  have hf7 : t₂ ∈ fiber C 7 := by simp [fiber, ht2]
  have hk1le : k 1 - 1 ≤ ((fiber C 1).erase t₁).card := by
    have h1' : (fiber C 1).card = count C 1 := fiber_card_eq_count C 1
    have hcard : ((fiber C 1).erase t₁).card = count C 1 - 1 := by
      rw [Finset.card_erase_of_mem hf1, h1']
    have hk1' : k 1 ≤ count C 1 := hk 1 (by simp)
    omega
  have hk7le : k 7 ≤ ((fiber C 7).erase t₂).card := by
    have h7' : (fiber C 7).card = count C 7 := fiber_card_eq_count C 7
    have hcard : ((fiber C 7).erase t₂).card = count C 7 - 1 := by
      rw [Finset.card_erase_of_mem hf7, h7']
    omega
  let g : Fin 16 → Finset (Fin n) := fun a =>
    if h1a : a.val = 1 then
      insert t₁ (pickSubset ((fiber C 1).erase t₁) (k 1 - 1) hk1le)
    else if h7a : a.val = 7 then
      pickSubset ((fiber C 7).erase t₂) (k 7) hk7le
    else
      pickSubset (fiber C a.val) (k a.val) (by
        have hle := hk a.val (by
          have : a.val ≤ 15 := Nat.le_of_lt_succ a.isLt
          simp [Finset.mem_Icc, this])
        rw [fiber_card_eq_count]
        exact hle)
  let y : Word n := tupleWord C g
  have hg1 : g ⟨1, by decide⟩ =
      insert t₁ (pickSubset ((fiber C 1).erase t₁) (k 1 - 1) hk1le) := by
    simp [g]
  have hg7 : g ⟨7, by decide⟩ = pickSubset ((fiber C 7).erase t₂) (k 7) hk7le := by
    simp [g]
  have hg : GoodTuplePred C k g := by
    intro a
    by_cases ha1 : a.val = 1
    · have hg' : g a = insert t₁ (pickSubset ((fiber C 1).erase t₁) (k 1 - 1) hk1le) := by
        simp [g, ha1]
      rw [hg', ha1]
      rw [Finset.mem_powersetCard]
      refine ⟨?_, ?_⟩
      · intro u hu
        rw [Finset.mem_insert] at hu
        rcases hu with rfl | hu
        · exact hf1
        · have hsub := pickSubset_subset hk1le
          have : u ∈ (fiber C 1).erase t₁ := hsub hu
          exact (Finset.mem_erase.mp this).2
      · have hPcard : (pickSubset ((fiber C 1).erase t₁) (k 1 - 1) hk1le).card = k 1 - 1 :=
          pickSubset_card hk1le
        have ht1' : t₁ ∉ pickSubset ((fiber C 1).erase t₁) (k 1 - 1) hk1le := by
          intro h
          have hsub := pickSubset_subset hk1le
          have : t₁ ∈ (fiber C 1).erase t₁ := hsub h
          exact (Finset.mem_erase.mp this).1 rfl
        rw [Finset.card_insert_of_notMem ht1', hPcard]
        omega
    · by_cases ha7 : a.val = 7
      · have hg' : g a = pickSubset ((fiber C 7).erase t₂) (k 7) hk7le := by
          simp [g, ha7]
        rw [hg', ha7]
        have hsub : pickSubset ((fiber C 7).erase t₂) (k 7) hk7le ⊆ (fiber C 7).erase t₂ :=
          pickSubset_subset hk7le
        rw [Finset.mem_powersetCard]
        refine ⟨?_, ?_⟩
        · intro u hu
          exact (Finset.mem_erase.mp (hsub hu)).2
        · exact pickSubset_card hk7le
      · have hg' : g a = pickSubset (fiber C a.val) (k a.val)
          (by
            have hle := hk a.val (by
              have : a.val ≤ 15 := Nat.le_of_lt_succ a.isLt
              simp [Finset.mem_Icc, this])
            rw [fiber_card_eq_count]
            exact hle) := by
          simp [g, ha1, ha7]
        rw [hg']
        exact pickSubset_mem
          (by
            have hle := hk a.val (by
              have : a.val ≤ 15 := Nat.le_of_lt_succ a.isLt
              simp [Finset.mem_Icc, this])
            rw [fiber_card_eq_count]
            exact hle)
  have hy1 : y t₁ = true := by
    unfold y
    simp [tupleWord]
    have h : t₁ ∈ g ⟨colVal (C t₁), Nat.lt_succ_of_le (colVal_le_15 (C t₁))⟩ := by
      have hg1' : g ⟨colVal (C t₁), Nat.lt_succ_of_le (colVal_le_15 (C t₁))⟩ =
          insert t₁ (pickSubset ((fiber C 1).erase t₁) (k 1 - 1) hk1le) := by
        simpa [ht1] using hg1
      rw [hg1']
      exact Finset.mem_insert_self t₁ _
    exact h
  have hy2 : y t₂ = false := by
    unfold y
    simp [tupleWord]
    intro h
    have hg7' : g ⟨colVal (C t₂), Nat.lt_succ_of_le (colVal_le_15 (C t₂))⟩ =
        pickSubset ((fiber C 7).erase t₂) (k 7) hk7le := by
      simpa [ht2] using hg7
    rw [hg7'] at h
    have hsub := pickSubset_subset hk7le
    have : t₂ ∈ (fiber C 7).erase t₂ := hsub h
    exact (Finset.mem_erase.mp this).1 rfl
  have hw : ∀ i ∈ Finset.Icc 0 15, w_i C i y = k i := by
    intro i hi
    have hones := onesOn_tupleWord C k g hg hi
    rw [w_i_eq_card_onesOn]
    rw [hones]
    have hi' : i < 16 := by
      have : i ≤ 15 := (Finset.mem_Icc.mp hi).2
      omega
    by_cases hi1 : i = 1
    · subst i
      rw [hg1]
      have hPcard : (pickSubset ((fiber C 1).erase t₁) (k 1 - 1) hk1le).card = k 1 - 1 :=
        pickSubset_card hk1le
      have ht1' : t₁ ∉ pickSubset ((fiber C 1).erase t₁) (k 1 - 1) hk1le := by
        intro h
        have hsub := pickSubset_subset hk1le
        have : t₁ ∈ (fiber C 1).erase t₁ := hsub h
        exact (Finset.mem_erase.mp this).1 rfl
      rw [Finset.card_insert_of_notMem ht1', hPcard]
      omega
    · by_cases hi7 : i = 7
      · subst i
        rw [hg7]
        exact pickSubset_card hk7le
      · have hg' : g ⟨i, hi'⟩ = pickSubset (fiber C i) (k i)
            (by
              have hle := hk i hi
              rw [fiber_card_eq_count]
              exact hle) := by
          simp [g, hi1, hi7]
        rw [hg']
        exact pickSubset_card
          (by
            have hle := hk i hi
            rw [fiber_card_eq_count]
            exact hle)
  exact ⟨y, hy1, hy2, hw⟩

/-- If y differs from row j at one position, the row distance is at least 1. -/
lemma dRow_pos_of_mismatch {n : ℕ} (C : Code n) (j : Fin 4) (t : Fin n) (y : Word n)
    (h : y t ≠ row C j t) : 1 ≤ dRow C j y := by
  rw [dRow_eq_indicator_sum]
  rw [sum_split_at (fun u : Fin n => if colBit j (C u) ≠ y u then 1 else 0) t]
  have hterm : (if colBit j (C t) ≠ y t then 1 else 0) = 1 := by
    have : colBit j (C t) ≠ y t := by
      simpa [row, colBit] using h.symm
    simp [this]
  rw [hterm]
  omega

/-- If y differs from row j at two distinct positions, the row distance is
at least 2. -/
lemma dRow_ge_two_of_mismatch {n : ℕ} (C : Code n) (j : Fin 4) (t₁ t₂ : Fin n)
    (htne : t₁ ≠ t₂) (y : Word n)
    (h1 : y t₁ ≠ row C j t₁) (h2 : y t₂ ≠ row C j t₂) : 2 ≤ dRow C j y := by
  rw [dRow_eq_indicator_sum]
  have hterm1 : (if colBit j (C t₁) ≠ y t₁ then 1 else 0) = 1 := by
    have : colBit j (C t₁) ≠ y t₁ := by
      simpa [row, colBit] using h1.symm
    simp [this]
  have hterm2 : (if colBit j (C t₂) ≠ y t₂ then 1 else 0) = 1 := by
    have : colBit j (C t₂) ≠ y t₂ := by
      simpa [row, colBit] using h2.symm
    simp [this]
  have hs1 := sum_split_at (fun u : Fin n => if colBit j (C u) ≠ y u then 1 else 0) t₁
  rw [hs1]
  have hs2 : (∑ u ∈ (Finset.univ.erase t₁), if colBit j (C u) ≠ y u then 1 else 0) =
      (∑ u ∈ (Finset.univ.erase t₁).erase t₂, if colBit j (C u) ≠ y u then 1 else 0) +
        (if colBit j (C t₂) ≠ y t₂ then 1 else 0) := by
    exact (Finset.sum_erase_add (Finset.univ.erase t₁)
      (fun u : Fin n => if colBit j (C u) ≠ y u then 1 else 0)
      (Finset.mem_erase.mpr ⟨htne.symm, Finset.mem_univ t₂⟩)).symm
  rw [hs2, hterm1, hterm2]
  omega

/-- min a (min b c) = b when b ≤ a and b ≤ c. -/
lemma min3_eq_middle_of_le {a b c : ℕ} (ha : b ≤ a) (hc : b ≤ c) :
    min a (min b c) = b := by
  rw [min_eq_right (le_trans (min_le_left _ _) ha)]
  exact min_eq_left hc

/-- y with y₁=1, y₂=0, d₂ = d₃+1, d₃ ≤ min(d₁,d₄) lies in Z4¹
(the converse of `Z41_implies_htrue_hfalse_d2_d3`). -/
lemma Z41_of_htrue_hfalse_d2_d3 {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (htne : t₁ ≠ t₂)
    (h1 : C t₁ = col1) (h7 : C t₂ = col7) {y : Word n}
    (hy1 : y t₁ = true) (hy2 : y t₂ = false)
    (hd2 : dRow C 1 y = dRow C 2 y + 1)
    (hd3 : dRow C 2 y ≤ min (dRow C 0 y) (dRow C 3 y)) :
    Z41 C t₁ t₂ y := by
  have hOp := dOp2_eq_min_of_htrue_hfalse C t₁ t₂ htne h1 h7 y hy1 hy2
  have hPp : dPp2 C t₁ t₂ y = dP C y - 2 :=
    dPp2_eq_sub_two_of_htrue_hfalse C t₁ t₂ htne h1 h7 y hy1 hy2
  have hOp_le_O : dOp2 C t₁ t₂ y ≤ dO C y :=
    dOp2_le_dO_of_htrue_hfalse C t₁ t₂ htne h1 h7 y hy1 hy2
  have hd0 : dRow C 2 y ≤ dRow C 0 y := le_trans hd3 (min_le_left _ _)
  have hd4 : dRow C 2 y ≤ dRow C 3 y := le_trans hd3 (min_le_right _ _)
  have hd1 : dRow C 2 y ≤ dRow C 1 y := by
    rw [hd2]
    omega
  have hP_ge_2 : 2 ≤ dP C y := by
    have hne1 : y t₁ ≠ row C ⟨2, by decide⟩ t₁ := by
      simp [row, colBit, h1, col1, hy1]
    have hne2 : y t₂ ≠ row C ⟨2, by decide⟩ t₂ := by
      simp [row, colBit, h7, col7, hy2]
    change 2 ≤ dRow C ⟨2, by decide⟩ y
    exact dRow_ge_two_of_mismatch C ⟨2, by decide⟩ t₁ t₂ htne y hne1 hne2
  have hO_ge_P : dO C y ≥ dP C y := by
    have hO' : dRow C 2 y ≤ min (dRow C 0 y) (min (dRow C 1 y) (dRow C 3 y)) :=
      le_min hd0 (le_min hd1 hd4)
    simpa [dO, dP, dRow, row0, row1, row2, row3] using hO'
  have hOp_eq : dOp2 C t₁ t₂ y = dP C y - 1 := by
    have hd1m2 : dRow C 1 y - 2 = dRow C 2 y - 1 := by omega
    have hOp' : min (dRow C 0 y) (min (dRow C 1 y - 2) (dRow C 3 y)) = dRow C 2 y - 1 := by
      rw [hd1m2]
      apply min3_eq_middle_of_le
      · omega
      · omega
    rw [hOp]
    simpa [dP, dRow, row2] using hOp'
  have hgt1 : dO C y > min (dP C y) (dPp2 C t₁ t₂ y) := by
    have hmin : min (dP C y) (dP C y - 2) = dP C y - 2 := by
      apply min_eq_right
      omega
    rw [hPp, hmin]
    change dRow C 2 y - 2 < min (dRow C 0 y) (min (dRow C 1 y) (dRow C 3 y))
    have hmin_ge : dRow C 2 y ≤ min (dRow C 0 y) (min (dRow C 1 y) (dRow C 3 y)) :=
      le_min hd0 (le_min hd1 hd4)
    omega
  have hgt2 : dP C y > min (dO C y) (dOp2 C t₁ t₂ y) := by
    have hmin : min (dO C y) (dOp2 C t₁ t₂ y) = dOp2 C t₁ t₂ y := min_eq_right hOp_le_O
    rw [hmin, hOp_eq]
    omega
  have hgt3 : dPp2 C t₁ t₂ y < min (dO C y) (dOp2 C t₁ t₂ y) := by
    have hmin : min (dO C y) (dOp2 C t₁ t₂ y) = dOp2 C t₁ t₂ y := min_eq_right hOp_le_O
    rw [hmin, hOp_eq, hPp]
    omega
  have hgt4 : min (dO C y) (dP C y) > dOp2 C t₁ t₂ y := by
    have hmin : min (dO C y) (dP C y) = dP C y := by
      apply min_eq_right
      exact hO_ge_P
    rw [hmin, hOp_eq]
    omega
  unfold Z41
  refine ⟨⟨?_, hgt1, hgt2, hgt3⟩, hgt4⟩
  · simp [hy1, hy2]

-- decide: Mechanical · n=any · checked 2026-08-27
/-- d₀ and d₄ in terms of the per-type weights for a Columns07 code. -/
lemma dRow03_columns07 {n : ℕ} (C : Code n) (y : Word n) (h07 : Columns07 C) :
    dRow C 0 y = w_i C 0 y + w_i C 1 y + w_i C 2 y + w_i C 3 y + w_i C 4 y +
      w_i C 5 y + w_i C 6 y + w_i C 7 y ∧
    dRow C 3 y = w_i C 0 y + w_i C 2 y + w_i C 4 y + w_i C 6 y +
      (count C 1 - w_i C 1 y) + (count C 3 - w_i C 3 y) +
      (count C 5 - w_i C 5 y) + (count C 7 - w_i C 7 y) := by
  have hS : ∀ t : Fin n, colVal (C t) ∈ Finset.Icc 0 7 := by
    intro t
    have hle := Columns07_le7 C h07 t
    simp [Finset.mem_Icc, hle]
  have hSle : (Finset.Icc 0 7 : Finset ℕ) ⊆ Finset.Icc 0 15 := by
    intro i hi
    simp [Finset.mem_Icc] at hi ⊢
    omega
  have hsum : ∀ j : Fin 4, dRow C j y = ∑ i ∈ Finset.Icc 0 7,
      if i.testBit (3 - j.val) then count C i - w_i C i y else w_i C i y := by
    intro j
    exact dRow_eq_sum_types C j y (Finset.Icc 0 7) hSle hS
  have h03 : (0 : ℕ).testBit 3 = false := by decide
  have h13 : (1 : ℕ).testBit 3 = false := by decide
  have h23 : (2 : ℕ).testBit 3 = false := by decide
  have h33 : (3 : ℕ).testBit 3 = false := by decide
  have h43 : (4 : ℕ).testBit 3 = false := by decide
  have h53 : (5 : ℕ).testBit 3 = false := by decide
  have h63 : (6 : ℕ).testBit 3 = false := by decide
  have h73 : (7 : ℕ).testBit 3 = false := by decide
  have h00 : (0 : ℕ).testBit 0 = false := by decide
  have h10 : (1 : ℕ).testBit 0 = true := by decide
  have h20 : (2 : ℕ).testBit 0 = false := by decide
  have h30 : (3 : ℕ).testBit 0 = true := by decide
  have h40 : (4 : ℕ).testBit 0 = false := by decide
  have h50 : (5 : ℕ).testBit 0 = true := by decide
  have h60 : (6 : ℕ).testBit 0 = false := by decide
  have h70 : (7 : ℕ).testBit 0 = true := by decide
  have hd0 : dRow C 0 y = w_i C 0 y + w_i C 1 y + w_i C 2 y + w_i C 3 y + w_i C 4 y +
      w_i C 5 y + w_i C 6 y + w_i C 7 y := by
    rw [hsum (0 : Fin 4), sum_Icc0_7]
    simp [h03, h13, h23, h33, h43, h53, h63, h73]
  have hd4 : dRow C 3 y = w_i C 0 y + w_i C 2 y + w_i C 4 y + w_i C 6 y +
      (count C 1 - w_i C 1 y) + (count C 3 - w_i C 3 y) +
      (count C 5 - w_i C 5 y) + (count C 7 - w_i C 7 y) := by
    rw [hsum (3 : Fin 4), sum_Icc0_7]
    simp [h00, h10, h20, h30, h40, h50, h60, h70]
    ac_rfl
  exact ⟨hd0, hd4⟩

/-- The w-form of Z4¹ (paper eq. 2cw1-2cw3, published (204)-(206)): y₁=1, y₂=0 and the three
weight conditions imply y ∈ Z4¹. -/
lemma Z41_of_w {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (htne : t₁ ≠ t₂)
    (h1 : C t₁ = col1) (h7 : C t₂ = col7) (h07 : Columns07 C) (y : Word n)
    (hy1 : y t₁ = true) (hy2 : y t₂ = false)
    (h1eq : 2 * (w_i C 2 y + w_i C 3 y) + count C 4 + count C 5 =
        2 * (w_i C 4 y + w_i C 5 y) + count C 2 + count C 3 + 1)
    (h2ge : count C 2 + count C 3 + count C 6 + count C 7 ≤
        2 * (w_i C 2 y + w_i C 3 y + w_i C 6 y + w_i C 7 y))
    (h3ge : 2 * (w_i C 2 y + w_i C 6 y) + count C 1 + count C 5 ≥
        2 * (w_i C 1 y + w_i C 5 y) + count C 2 + count C 6) :
    Z41 C t₁ t₂ y := by
  apply Z41_of_htrue_hfalse_d2_d3 C t₁ t₂ htne h1 h7 hy1 hy2
  · have hd12 := dRow12_columns07 C y h07
    rcases hd12 with ⟨hd1, hd2⟩
    rw [hd1, hd2]
    have hw2 : w_i C 2 y ≤ count C 2 := w_i_le_count C 2 y
    have hw3 : w_i C 3 y ≤ count C 3 := w_i_le_count C 3 y
    have hw4 : w_i C 4 y ≤ count C 4 := w_i_le_count C 4 y
    have hw5 : w_i C 5 y ≤ count C 5 := w_i_le_count C 5 y
    omega
  · have hd12 := dRow12_columns07 C y h07
    have hd03 := dRow03_columns07 C y h07
    rcases hd12 with ⟨hd1, hd2⟩
    rcases hd03 with ⟨hd0, hd4⟩
    rw [hd2, hd0, hd4]
    have hw2 : w_i C 2 y ≤ count C 2 := w_i_le_count C 2 y
    have hw3 : w_i C 3 y ≤ count C 3 := w_i_le_count C 3 y
    have hw6 : w_i C 6 y ≤ count C 6 := w_i_le_count C 6 y
    have hw7 : w_i C 7 y ≤ count C 7 := w_i_le_count C 7 y
    have hw1 : w_i C 1 y ≤ count C 1 := w_i_le_count C 1 y
    have hw5 : w_i C 5 y ≤ count C 5 := w_i_le_count C 5 y
    exact le_min (by omega) (by omega)

/-- A type-i column exists at position t, so |i| ≥ 1. -/
lemma count_pos_of_colVal {n : ℕ} (C : Code n) {i : ℕ} (t : Fin n) (h : colVal (C t) = i) :
    1 ≤ count C i := by
  have ht : t ∈ fiber C i := by simp [fiber, h]
  rw [← fiber_card_eq_count]
  exact Nat.succ_le_of_lt (Finset.card_pos.mpr ⟨t, ht⟩)

/-- The witness table: weight values at types 1..7, zero elsewhere. -/
def tableZ (a1 a2 a3 a4 a5 a6 a7 : ℕ) (i : ℕ) : ℕ :=
  if i = 1 then a1 else if i = 2 then a2 else if i = 3 then a3
  else if i = 4 then a4 else if i = 5 then a5 else if i = 6 then a6
  else if i = 7 then a7 else 0

/-- Feasibility of a table assignment. -/
lemma tableZ_bounds {n : ℕ} (C : Code n) (a1 a2 a3 a4 a5 a6 a7 : ℕ)
    (h1 : a1 ≤ count C 1) (h2 : a2 ≤ count C 2) (h3 : a3 ≤ count C 3)
    (h4 : a4 ≤ count C 4) (h5 : a5 ≤ count C 5) (h6 : a6 ≤ count C 6)
    (h7 : a7 ≤ count C 7) :
    ∀ i ∈ Finset.Icc 0 15, tableZ a1 a2 a3 a4 a5 a6 a7 i ≤ count C i := by
  intro i hi
  by_cases hi1 : i = 1
  · subst i
    simp [tableZ, h1]
  · by_cases hi2 : i = 2
    · subst i
      simp [tableZ, h2]
    · by_cases hi3 : i = 3
      · subst i
        simp [tableZ, h3]
      · by_cases hi4 : i = 4
        · subst i
          simp [tableZ, h4]
        · by_cases hi5 : i = 5
          · subst i
            simp [tableZ, h5]
          · by_cases hi6 : i = 6
            · subst i
              simp [tableZ, h6]
            · by_cases hi7 : i = 7
              · subst i
                simp [tableZ, h7]
              · simp [tableZ, hi1, hi2, hi3, hi4, hi5, hi6, hi7]

/-- A Z4¹ witness from a feasible table assignment satisfying the three
weight conditions (paper eq. 2cw1-2cw3, published (204)-(206)). -/
-- decide: Mechanical · n=any · checked 2026-08-27
lemma z4_nonempty_of_table {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (htne : t₁ ≠ t₂)
    (h1 : C t₁ = col1) (h7 : C t₂ = col7) (h07 : Columns07 C)
    (a1 a2 a3 a4 a5 a6 a7 : ℕ)
    (ha1 : 1 ≤ a1) (ha7 : a7 + 1 ≤ count C 7)
    (hb1 : a1 ≤ count C 1) (hb2 : a2 ≤ count C 2) (hb3 : a3 ≤ count C 3)
    (hb4 : a4 ≤ count C 4) (hb5 : a5 ≤ count C 5) (hb6 : a6 ≤ count C 6)
    (hb7 : a7 ≤ count C 7)
    (h1eq : 2 * (a2 + a3) + count C 4 + count C 5 =
        2 * (a4 + a5) + count C 2 + count C 3 + 1)
    (h2ge : count C 2 + count C 3 + count C 6 + count C 7 ≤ 2 * (a2 + a3 + a6 + a7))
    (h3ge : 2 * (a2 + a6) + count C 1 + count C 5 ≥ 2 * (a1 + a5) + count C 2 + count C 6) :
    ∃ y : Word n, Z41 C t₁ t₂ y := by
  let k : ℕ → ℕ := tableZ a1 a2 a3 a4 a5 a6 a7
  have hk1' : 1 ≤ k 1 := by simp [k, tableZ, ha1]
  have hk7' : k 7 + 1 ≤ count C 7 := by simp [k, tableZ, ha7]
  have hkfeas : ∀ i ∈ Finset.Icc 0 15, k i ≤ count C i := by
    apply tableZ_bounds C a1 a2 a3 a4 a5 a6 a7 hb1 hb2 hb3 hb4 hb5 hb6 hb7
  have ht1 : colVal (C t₁) = 1 := by rw [h1]; decide
  have ht2 : colVal (C t₂) = 7 := by rw [h7]; decide
  rcases exists_goodWord_fixed C k t₁ t₂ ht1 ht2 hk1' hk7' hkfeas with ⟨y, hy1, hy2, hw⟩
  have hw1 : w_i C 1 y = a1 := by
    have := hw 1 (by simp)
    simpa [k, tableZ] using this
  have hw2 : w_i C 2 y = a2 := by
    have := hw 2 (by simp)
    simpa [k, tableZ] using this
  have hw3 : w_i C 3 y = a3 := by
    have := hw 3 (by simp)
    simpa [k, tableZ] using this
  have hw4 : w_i C 4 y = a4 := by
    have := hw 4 (by simp)
    simpa [k, tableZ] using this
  have hw5 : w_i C 5 y = a5 := by
    have := hw 5 (by simp)
    simpa [k, tableZ] using this
  have hw6 : w_i C 6 y = a6 := by
    have := hw 6 (by simp)
    simpa [k, tableZ] using this
  have hw7 : w_i C 7 y = a7 := by
    have := hw 7 (by simp)
    simpa [k, tableZ] using this
  refine ⟨y, ?_⟩
  apply Z41_of_w C t₁ t₂ htne h1 h7 h07 y hy1 hy2
  · rw [hw2, hw3, hw4, hw5]
    omega
  · rw [hw2, hw3, hw6, hw7]
    omega
  · rw [hw1, hw2, hw5, hw6]
    omega

/-- Lemma `lemma:y4` (Lemma 23): if w(c2 ⊕ c3) is odd and the parities of
(|2|,|3|,|4|,|5|) match cases 1, 4, 5, or 6, then Z4¹ is nonempty. Note that
the four cases imply that w(c2 ⊕ c3) is odd. -/
-- decide: Mechanical · n=any · checked 2026-08-27
theorem z4_nonempty_cases {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (htne : t₁ ≠ t₂)
    (h1 : C t₁ = col1) (h7 : C t₂ = col7) (h07 : Columns07 C)
    (_h : Odd (hammingDist (row1 C) (row2 C)))
    (hcase :
      (Odd (count C 2) ∧ Even (count C 3) ∧ Even (count C 4) ∧ Even (count C 5)) ∨
        (Odd (count C 2) ∧ Odd (count C 3) ∧ Odd (count C 4) ∧ Even (count C 5)) ∨
        (Odd (count C 2) ∧ Even (count C 3) ∧ Odd (count C 4) ∧ Odd (count C 5)) ∨
        (Even (count C 2) ∧ Odd (count C 3) ∧ Odd (count C 4) ∧ Odd (count C 5))) :
    ∃ y : Word n, Z41 C t₁ t₂ y := by
  have ht1 : colVal (C t₁) = 1 := by rw [h1]; decide
  have ht2 : colVal (C t₂) = 7 := by rw [h7]; decide
  have hc1 : 1 ≤ count C 1 := count_pos_of_colVal C t₁ ht1
  have hc7 : 1 ≤ count C 7 := count_pos_of_colVal C t₂ ht2
  rcases hcase with hcase | hcase | hcase | hcase
  · -- case 1: |2| odd, |3|,|4|,|5| even
    rcases hcase with ⟨h2o, h3e, h4e, h5e⟩
    rcases h2o with ⟨p2, hp2⟩
    rcases h3e with ⟨p3, hp3⟩
    rcases h4e with ⟨p4, hp4⟩
    rcases h5e with ⟨p5, hp5⟩
    refine z4_nonempty_of_table C t₁ t₂ htne h1 h7 h07 1 (p2 + 1) p3 p4 p5 (count C 6)
      (count C 7 - 1) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · rfl
    · omega
    · rw [hp2, hp3, hp4, hp5]
      omega
    · rw [hp2, hp3]
      omega
    · rw [hp2]
      omega
  · -- case 4: |2|,|3|,|4| odd, |5| even
    rcases hcase with ⟨h2o, h3o, h4o, h5e⟩
    rcases h2o with ⟨p2, hp2⟩
    rcases h3o with ⟨p3, hp3⟩
    rcases h4o with ⟨p4, hp4⟩
    rcases h5e with ⟨p5, hp5⟩
    refine z4_nonempty_of_table C t₁ t₂ htne h1 h7 h07 1 (p2 + 1) (p3 + 1) (p4 + 1) p5
      (count C 6) (count C 7 - 1) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · rfl
    · omega
    · rw [hp2, hp3, hp4, hp5]
      omega
    · rw [hp2, hp3]
      omega
    · rw [hp2]
      omega
  · -- case 5: |2|,|4|,|5| odd, |3| even
    rcases hcase with ⟨h2o, h3e, h4o, h5o⟩
    rcases h2o with ⟨p2, hp2⟩
    rcases h3e with ⟨p3, hp3⟩
    rcases h4o with ⟨p4, hp4⟩
    rcases h5o with ⟨p5, hp5⟩
    refine z4_nonempty_of_table C t₁ t₂ htne h1 h7 h07 1 (p2 + 1) p3 (p4 + 1) p5
      (count C 6) (count C 7 - 1) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · rfl
    · omega
    · rw [hp2, hp3, hp4, hp5]
      omega
    · rw [hp2, hp3]
      omega
    · rw [hp2, hp5]
      omega
  · -- case 6: |3|,|4|,|5| odd, |2| even
    rcases hcase with ⟨h2e, h3o, h4o, h5o⟩
    rcases h2e with ⟨p2, hp2⟩
    rcases h3o with ⟨p3, hp3⟩
    rcases h4o with ⟨p4, hp4⟩
    rcases h5o with ⟨p5, hp5⟩
    refine z4_nonempty_of_table C t₁ t₂ htne h1 h7 h07 1 p2 (p3 + 1) (p4 + 1) p5
      (count C 6) (count C 7 - 1) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · rfl
    · omega
    · rw [hp2, hp3, hp4, hp5]
      omega
    · rw [hp3]
      omega
    · rw [hp2, hp5]
      omega

/-- a + c = b implies a ≤ b. -/
lemma add_eq_le {a b c : ℕ} (h : a + c = b) : a ≤ b := by omega

/-- a + c = b with c ≤ 1 implies b − 1 ≤ a. -/
lemma sub_one_le_of_add_eq {a b c : ℕ} (h : a + c = b) (hc : c ≤ 1) : b - 1 ≤ a := by
  omega

/-- Subtraction is monotone. -/
lemma sub_two_mono {a b : ℕ} (h : a ≤ b) : a - 2 ≤ b - 2 := by omega

/-- a ≥ 2 gives a − 2 < a − 1. -/
lemma sub_two_lt_sub_one {a : ℕ} (h : 2 ≤ a) : a - 2 < a - 1 := by omega

/-- a − 1 ≤ b gives a ≤ b + 1. -/
lemma le_succ_of_sub_one_le {a b : ℕ} (h : a - 1 ≤ b) : a ≤ b + 1 := by omega

/-- The w-form of Z5 (paper eq. 3cw2/4cw2 and 3cw3/4cw3, published
(208)-(210) for the odd case, (211)-(213) for the even case): y₁=1, y₂=0,
d₁ + c = d₃ (c ∈ {0,1}), and the two weight inequalities imply y ∈ Z5. -/
lemma Z5_of_w {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (htne : t₁ ≠ t₂)
    (h1 : C t₁ = col1) (h7 : C t₂ = col7) (h07 : Columns07 C) (y : Word n)
    (hy1 : y t₁ = true) (hy2 : y t₂ = false)
    (c : ℕ) (hc : c ≤ 1) (hd12c : dRow C 1 y + c = dRow C 2 y)
    (h2ge : count C 2 + count C 3 + count C 6 + count C 7 - 1 ≤
        2 * (w_i C 2 y + w_i C 3 y + w_i C 6 y + w_i C 7 y))
    (h3le : 2 * (w_i C 1 y + w_i C 5 y) + count C 2 + count C 6 ≤
        2 * (w_i C 2 y + w_i C 6 y) + count C 1 + count C 5 + 1) :
    Z5 C t₁ t₂ y := by
  have hd12 := dRow12_columns07 C y h07
  have hd03 := dRow03_columns07 C y h07
  rcases hd12 with ⟨hd1, hd2⟩
  rcases hd03 with ⟨hd0, hd4⟩
  have hd23 : dRow C 1 y ≤ dRow C 2 y := add_eq_le hd12c
  have hd31 : dRow C 2 y - 1 ≤ dRow C 1 y := sub_one_le_of_add_eq hd12c hc
  have hP_ge_2 : 2 ≤ dP C y := by
    have hne1 : y t₁ ≠ row C ⟨2, by decide⟩ t₁ := by
      simp [row, colBit, h1, col1, hy1]
    have hne2 : y t₂ ≠ row C ⟨2, by decide⟩ t₂ := by
      simp [row, colBit, h7, col7, hy2]
    change 2 ≤ dRow C ⟨2, by decide⟩ y
    exact dRow_ge_two_of_mismatch C ⟨2, by decide⟩ t₁ t₂ htne y hne1 hne2
  have hd30 : dRow C 2 y - 1 ≤ dRow C 0 y := by
    rw [hd2, hd0]
    have hw2 : w_i C 2 y ≤ count C 2 := w_i_le_count C 2 y
    have hw3 : w_i C 3 y ≤ count C 3 := w_i_le_count C 3 y
    have hw6 : w_i C 6 y ≤ count C 6 := w_i_le_count C 6 y
    have hw7 : w_i C 7 y ≤ count C 7 := w_i_le_count C 7 y
    omega
  have hd34 : dRow C 2 y - 1 ≤ dRow C 3 y := by
    rw [hd2, hd4]
    have hw1 : w_i C 1 y ≤ count C 1 := w_i_le_count C 1 y
    have hw2 : w_i C 2 y ≤ count C 2 := w_i_le_count C 2 y
    have hw5 : w_i C 5 y ≤ count C 5 := w_i_le_count C 5 y
    have hw6 : w_i C 6 y ≤ count C 6 := w_i_le_count C 6 y
    omega
  have hd3_le_dO : dRow C 2 y ≤ dO C y + 1 := by
    have hmin : dRow C 2 y - 1 ≤ min (dRow C 0 y) (min (dRow C 1 y) (dRow C 3 y)) :=
      le_min hd30 (le_min hd31 hd34)
    have hO' : dRow C 2 y - 1 ≤ dO C y := by
      simpa [dO, dRow, row0, row1, row2, row3] using hmin
    exact le_succ_of_sub_one_le hO'
  have hOp := dOp2_eq_min_of_htrue_hfalse C t₁ t₂ htne h1 h7 y hy1 hy2
  have hPp : dPp2 C t₁ t₂ y = dP C y - 2 :=
    dPp2_eq_sub_two_of_htrue_hfalse C t₁ t₂ htne h1 h7 y hy1 hy2
  have hOp_le_d1m2 : dOp2 C t₁ t₂ y ≤ dRow C 1 y - 2 := by
    rw [hOp]
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hOp_le_Pp : dOp2 C t₁ t₂ y ≤ dPp2 C t₁ t₂ y := by
    rw [hPp]
    exact le_trans hOp_le_d1m2 (sub_two_mono hd23)
  have hOp_le_O : dOp2 C t₁ t₂ y ≤ dO C y :=
    dOp2_le_dO_of_htrue_hfalse C t₁ t₂ htne h1 h7 y hy1 hy2
  unfold Z5
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [hy1, hy2]
  · have hmin : min (dP C y) (dP C y - 2) = dP C y - 2 := by
      apply min_eq_right
      omega
    rw [hPp, hmin]
    change dRow C 2 y - 2 < min (dRow C 0 y) (min (dRow C 1 y) (dRow C 3 y))
    have hmin_ge : dRow C 2 y - 1 ≤ min (dRow C 0 y) (min (dRow C 1 y) (dRow C 3 y)) :=
      le_min hd30 (le_min hd31 hd34)
    have hRow2_ge_2 : 2 ≤ dRow C 2 y := by
      simpa [dP, dRow, row2] using hP_ge_2
    exact lt_of_lt_of_le (sub_two_lt_sub_one hRow2_ge_2) hmin_ge
  · have hmin : min (dO C y) (dOp2 C t₁ t₂ y) = dOp2 C t₁ t₂ y := min_eq_right hOp_le_O
    rw [hmin]
    have hOp_lt_P : dOp2 C t₁ t₂ y < dP C y := by
      have hle2 : dOp2 C t₁ t₂ y ≤ dP C y - 2 := by
        rw [← hPp]
        exact hOp_le_Pp
      omega
    exact hOp_lt_P
  · have hmin : min (dO C y) (dOp2 C t₁ t₂ y) = dOp2 C t₁ t₂ y := min_eq_right hOp_le_O
    rw [hmin]
    exact hOp_le_Pp

/-- A Z5 witness from a feasible table assignment (c = 1 in the odd case,
c = 0 in the even case; paper eq. 4cw1/3cw1, 4cw2/3cw2, 4cw3/3cw3,
published (208)-(210) for the odd case, (211)-(213) for the even case). -/
-- decide: Mechanical · n=any · checked 2026-08-27
lemma z5_nonempty_of_table {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (htne : t₁ ≠ t₂)
    (h1 : C t₁ = col1) (h7 : C t₂ = col7) (h07 : Columns07 C)
    (a1 a2 a3 a4 a5 a6 a7 : ℕ) (c : ℕ) (hc : c ≤ 1)
    (ha1 : 1 ≤ a1) (ha7 : a7 + 1 ≤ count C 7)
    (hb1 : a1 ≤ count C 1) (hb2 : a2 ≤ count C 2) (hb3 : a3 ≤ count C 3)
    (hb4 : a4 ≤ count C 4) (hb5 : a5 ≤ count C 5) (hb6 : a6 ≤ count C 6)
    (hb7 : a7 ≤ count C 7)
    (h1eq : 2 * (a2 + a3) + count C 4 + count C 5 + c =
        2 * (a4 + a5) + count C 2 + count C 3)
    (h2ge : count C 2 + count C 3 + count C 6 + count C 7 - 1 ≤ 2 * (a2 + a3 + a6 + a7))
    (h3le : 2 * (a1 + a5) + count C 2 + count C 6 ≤
        2 * (a2 + a6) + count C 1 + count C 5 + 1) :
    ∃ y : Word n, Z5 C t₁ t₂ y := by
  let k : ℕ → ℕ := tableZ a1 a2 a3 a4 a5 a6 a7
  have hk1' : 1 ≤ k 1 := by simp [k, tableZ, ha1]
  have hk7' : k 7 + 1 ≤ count C 7 := by simp [k, tableZ, ha7]
  have hkfeas : ∀ i ∈ Finset.Icc 0 15, k i ≤ count C i := by
    apply tableZ_bounds C a1 a2 a3 a4 a5 a6 a7 hb1 hb2 hb3 hb4 hb5 hb6 hb7
  have ht1 : colVal (C t₁) = 1 := by rw [h1]; decide
  have ht2 : colVal (C t₂) = 7 := by rw [h7]; decide
  rcases exists_goodWord_fixed C k t₁ t₂ ht1 ht2 hk1' hk7' hkfeas with ⟨y, hy1, hy2, hw⟩
  have hw1 : w_i C 1 y = a1 := by
    have := hw 1 (by simp)
    simpa [k, tableZ] using this
  have hw2 : w_i C 2 y = a2 := by
    have := hw 2 (by simp)
    simpa [k, tableZ] using this
  have hw3 : w_i C 3 y = a3 := by
    have := hw 3 (by simp)
    simpa [k, tableZ] using this
  have hw4 : w_i C 4 y = a4 := by
    have := hw 4 (by simp)
    simpa [k, tableZ] using this
  have hw5 : w_i C 5 y = a5 := by
    have := hw 5 (by simp)
    simpa [k, tableZ] using this
  have hw6 : w_i C 6 y = a6 := by
    have := hw 6 (by simp)
    simpa [k, tableZ] using this
  have hw7 : w_i C 7 y = a7 := by
    have := hw 7 (by simp)
    simpa [k, tableZ] using this
  have hd12c : dRow C 1 y + c = dRow C 2 y := by
    rcases dRow12_columns07 C y h07 with ⟨hd1, hd2⟩
    rw [hd1, hd2]
    have hw2' : w_i C 2 y ≤ count C 2 := w_i_le_count C 2 y
    have hw3' : w_i C 3 y ≤ count C 3 := w_i_le_count C 3 y
    have hw4' : w_i C 4 y ≤ count C 4 := w_i_le_count C 4 y
    have hw5' : w_i C 5 y ≤ count C 5 := w_i_le_count C 5 y
    rw [hw2, hw3, hw4, hw5]
    omega
  refine ⟨y, ?_⟩
  apply Z5_of_w C t₁ t₂ htne h1 h7 h07 y hy1 hy2 c hc hd12c ?_ ?_
  · rw [hw2, hw3, hw6, hw7]
    omega
  · rw [hw1, hw2, hw5, hw6]
    omega

-- decide: Mechanical · n=any · checked 2026-08-27
theorem z5_nonempty {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (htne : t₁ ≠ t₂)
    (h1 : C t₁ = col1) (h7 : C t₂ = col7) (h07 : Columns07 C)
    (hcase :
      (Odd (count C 2) ∧ Odd (count C 3) ∧ Odd (count C 5) ∧ Even (count C 4)) ∨
        (Even (count C 2) ∧ Even (count C 3) ∧ Even (count C 5) ∧ Odd (count C 4)) ∨
        (Even (hammingDist (row1 C) (row2 C)) ∧
          ¬ (Even (count C 2) ∧ Even (count C 4) ∧ Odd (count C 3) ∧ Odd (count C 5)))) :
    ∃ y : Word n, Z5 C t₁ t₂ y := by
  have hc1 : 1 ≤ count C 1 := count_pos_of_colVal C t₁ (by rw [h1]; decide)
  have hc7 : 1 ≤ count C 7 := count_pos_of_colVal C t₂ (by rw [h7]; decide)
  rcases hcase with hcase | hcase | hcase
  · -- case 7: |2|,|3|,|5| odd, |4| even
    rcases hcase with ⟨h2o, h3o, h5o, h4e⟩
    rcases h2o with ⟨p2, hp2⟩
    rcases h3o with ⟨p3, hp3⟩
    rcases h4e with ⟨p4, hp4⟩
    rcases h5o with ⟨p5, hp5⟩
    refine z5_nonempty_of_table C t₁ t₂ htne h1 h7 h07 1 (p2 + 1) p3 p4 (p5 + 1)
      (count C 6) (count C 7 - 1) 1 (by norm_num) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · rfl
    · omega
    · omega
    · omega
    · omega
  · -- case 8: |2|,|3|,|5| even, |4| odd
    rcases hcase with ⟨h2e, h3e, h5e, h4o⟩
    rcases h2e with ⟨p2, hp2⟩
    rcases h3e with ⟨p3, hp3⟩
    rcases h4o with ⟨p4, hp4⟩
    rcases h5e with ⟨p5, hp5⟩
    refine z5_nonempty_of_table C t₁ t₂ htne h1 h7 h07 1 p2 p3 (p4 + 1) p5
      (count C 6) (count C 7 - 1) 1 (by norm_num) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · rfl
    · omega
    · rw [hp2, hp3, hp4, hp5]
      omega
    · rw [hp2, hp3]
      omega
    · rw [hp2, hp5]
      omega
  · -- cases 9-15: w(c2⊕c3) even, not case 16
    rcases hcase with ⟨heven, hnot16⟩
    have heven' : Even (count C 2 + count C 3 + count C 4 + count C 5) := by
      rw [← hammingDist_row1_row2_eq C h07]
      exact heven
    by_cases h2e : Even (count C 2)
    · by_cases h3e : Even (count C 3)
      · by_cases h4e : Even (count C 4)
        · by_cases h5e : Even (count C 5)
          · -- case 9: all even
            rcases h2e with ⟨p2, hp2⟩
            rcases h3e with ⟨p3, hp3⟩
            rcases h4e with ⟨p4, hp4⟩
            rcases h5e with ⟨p5, hp5⟩
            refine z5_nonempty_of_table C t₁ t₂ htne h1 h7 h07 1 p2 p3 p4 p5
              (count C 6) (count C 7 - 1) 0 (by norm_num) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
            · omega
            · omega
            · omega
            · omega
            · omega
            · omega
            · omega
            · rfl
            · omega
            · omega
            · omega
            · omega
          · -- (E,E,E,O): odd sum, impossible
            exfalso
            rcases heven' with ⟨m, hm⟩
            rcases h2e with ⟨a, ha⟩
            rcases h3e with ⟨b, hb⟩
            rcases h4e with ⟨c, hc⟩
            have h5o : Odd (count C 5) := odd_of_not_even h5e
            rcases h5o with ⟨d, hd⟩
            omega
        · by_cases h5e : Even (count C 5)
          · -- (E,E,O,E): odd sum, impossible
            exfalso
            rcases heven' with ⟨m, hm⟩
            rcases h2e with ⟨a, ha⟩
            rcases h3e with ⟨b, hb⟩
            have h4o : Odd (count C 4) := odd_of_not_even h4e
            rcases h4o with ⟨c, hc⟩
            rcases h5e with ⟨d, hd⟩
            omega
          · -- case 14: (E,E,O,O), |4|,|5| odd
            rcases h2e with ⟨p2, hp2⟩
            rcases h3e with ⟨p3, hp3⟩
            have h4o : Odd (count C 4) := odd_of_not_even h4e
            rcases h4o with ⟨p4, hp4⟩
            have h5o : Odd (count C 5) := odd_of_not_even h5e
            rcases h5o with ⟨p5, hp5⟩
            refine z5_nonempty_of_table C t₁ t₂ htne h1 h7 h07 1 p2 p3 (p4 + 1) p5
              (count C 6) (count C 7 - 1) 0 (by norm_num) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
            · omega
            · omega
            · omega
            · omega
            · omega
            · omega
            · omega
            · rfl
            · omega
            · omega
            · omega
            · omega
      · by_cases h4e : Even (count C 4)
        · by_cases h5e : Even (count C 5)
          · -- (E,O,E,E): odd sum, impossible
            exfalso
            rcases heven' with ⟨m, hm⟩
            rcases h2e with ⟨a, ha⟩
            have h3o : Odd (count C 3) := odd_of_not_even h3e
            rcases h3o with ⟨b, hb⟩
            rcases h4e with ⟨c, hc⟩
            rcases h5e with ⟨d, hd⟩
            omega
          · -- case 16: (E,O,E,O), excluded
            exfalso
            exact hnot16 ⟨h2e, h4e, odd_of_not_even h3e, odd_of_not_even h5e⟩
        · by_cases h5e : Even (count C 5)
          · -- case 12: (E,O,O,E)
            rcases h2e with ⟨p2, hp2⟩
            have h3o : Odd (count C 3) := odd_of_not_even h3e
            rcases h3o with ⟨p3, hp3⟩
            have h4o : Odd (count C 4) := odd_of_not_even h4e
            rcases h4o with ⟨p4, hp4⟩
            rcases h5e with ⟨p5, hp5⟩
            refine z5_nonempty_of_table C t₁ t₂ htne h1 h7 h07 1 p2 (p3 + 1) (p4 + 1) p5
              (count C 6) (count C 7 - 1) 0 (by norm_num) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
            · omega
            · omega
            · omega
            · omega
            · omega
            · omega
            · omega
            · rfl
            · omega
            · omega
            · omega
            · omega
          · -- (E,O,O,O): odd sum, impossible
            exfalso
            rcases heven' with ⟨m, hm⟩
            rcases h2e with ⟨a, ha⟩
            have h3o : Odd (count C 3) := odd_of_not_even h3e
            rcases h3o with ⟨b, hb⟩
            have h4o : Odd (count C 4) := odd_of_not_even h4e
            rcases h4o with ⟨c, hc⟩
            have h5o : Odd (count C 5) := odd_of_not_even h5e
            rcases h5o with ⟨d, hd⟩
            omega
    · by_cases h3e : Even (count C 3)
      · by_cases h4e : Even (count C 4)
        · by_cases h5e : Even (count C 5)
          · -- (O,E,E,E): odd sum, impossible
            exfalso
            rcases heven' with ⟨m, hm⟩
            have h2o : Odd (count C 2) := odd_of_not_even h2e
            rcases h2o with ⟨a, ha⟩
            rcases h3e with ⟨b, hb⟩
            rcases h4e with ⟨c, hc⟩
            rcases h5e with ⟨d, hd⟩
            omega
          · -- case 11: (O,E,E,O)
            have h2o : Odd (count C 2) := odd_of_not_even h2e
            rcases h2o with ⟨p2, hp2⟩
            rcases h3e with ⟨p3, hp3⟩
            rcases h4e with ⟨p4, hp4⟩
            have h5o : Odd (count C 5) := odd_of_not_even h5e
            rcases h5o with ⟨p5, hp5⟩
            refine z5_nonempty_of_table C t₁ t₂ htne h1 h7 h07 1 (p2 + 1) p3 p4 (p5 + 1)
              (count C 6) (count C 7 - 1) 0 (by norm_num) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
            · omega
            · omega
            · omega
            · omega
            · omega
            · omega
            · omega
            · rfl
            · omega
            · omega
            · omega
            · omega
        · by_cases h5e : Even (count C 5)
          · -- case 13: (O,E,O,E)
            have h2o : Odd (count C 2) := odd_of_not_even h2e
            rcases h2o with ⟨p2, hp2⟩
            rcases h3e with ⟨p3, hp3⟩
            have h4o : Odd (count C 4) := odd_of_not_even h4e
            rcases h4o with ⟨p4, hp4⟩
            rcases h5e with ⟨p5, hp5⟩
            refine z5_nonempty_of_table C t₁ t₂ htne h1 h7 h07 1 (p2 + 1) p3 (p4 + 1) p5
              (count C 6) (count C 7 - 1) 0 (by norm_num) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
            · omega
            · omega
            · omega
            · omega
            · omega
            · omega
            · omega
            · rfl
            · omega
            · omega
            · omega
            · omega
          · -- (O,E,O,O): odd sum, impossible
            exfalso
            rcases heven' with ⟨m, hm⟩
            have h2o : Odd (count C 2) := odd_of_not_even h2e
            rcases h2o with ⟨a, ha⟩
            rcases h3e with ⟨b, hb⟩
            have h4o : Odd (count C 4) := odd_of_not_even h4e
            rcases h4o with ⟨c, hc⟩
            have h5o : Odd (count C 5) := odd_of_not_even h5e
            rcases h5o with ⟨d, hd⟩
            omega
      · by_cases h4e : Even (count C 4)
        · by_cases h5e : Even (count C 5)
          · -- case 10: (O,O,E,E)
            have h2o : Odd (count C 2) := odd_of_not_even h2e
            rcases h2o with ⟨p2, hp2⟩
            have h3o : Odd (count C 3) := odd_of_not_even h3e
            rcases h3o with ⟨p3, hp3⟩
            rcases h4e with ⟨p4, hp4⟩
            rcases h5e with ⟨p5, hp5⟩
            refine z5_nonempty_of_table C t₁ t₂ htne h1 h7 h07 1 (p2 + 1) p3 p4 p5
              (count C 6) (count C 7 - 1) 0 (by norm_num) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
            · omega
            · omega
            · omega
            · omega
            · omega
            · omega
            · omega
            · rfl
            · omega
            · omega
            · omega
            · omega
          · -- (O,O,E,O): odd sum, impossible
            exfalso
            rcases heven' with ⟨m, hm⟩
            have h2o : Odd (count C 2) := odd_of_not_even h2e
            rcases h2o with ⟨a, ha⟩
            have h3o : Odd (count C 3) := odd_of_not_even h3e
            rcases h3o with ⟨b, hb⟩
            rcases h4e with ⟨c, hc⟩
            have h5o : Odd (count C 5) := odd_of_not_even h5e
            rcases h5o with ⟨d, hd⟩
            omega
        · by_cases h5e : Even (count C 5)
          · -- (O,O,O,E): odd sum, impossible
            exfalso
            rcases heven' with ⟨m, hm⟩
            have h2o : Odd (count C 2) := odd_of_not_even h2e
            rcases h2o with ⟨a, ha⟩
            have h3o : Odd (count C 3) := odd_of_not_even h3e
            rcases h3o with ⟨b, hb⟩
            have h4o : Odd (count C 4) := odd_of_not_even h4e
            rcases h4o with ⟨c, hc⟩
            rcases h5e with ⟨d, hd⟩
            omega
          · -- case 15: all odd
            have h2o : Odd (count C 2) := odd_of_not_even h2e
            rcases h2o with ⟨p2, hp2⟩
            have h3o : Odd (count C 3) := odd_of_not_even h3e
            rcases h3o with ⟨p3, hp3⟩
            have h4o : Odd (count C 4) := odd_of_not_even h4e
            rcases h4o with ⟨p4, hp4⟩
            have h5o : Odd (count C 5) := odd_of_not_even h5e
            rcases h5o with ⟨p5, hp5⟩
            refine z5_nonempty_of_table C t₁ t₂ htne h1 h7 h07 1 (p2 + 1) p3 (p4 + 1) p5
              (count C 6) (count C 7 - 1) 0 (by norm_num) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
            · omega
            · omega
            · omega
            · omega
            · omega
            · omega
            · omega
            · rfl
            · omega
            · omega
            · omega
            · omega


/-! ## lm:2/lm:3/lm:16: the emptiness characterizations -/

/-- If |i| = 1 and the single type-i column has y = true, then w_i = 1. -/
lemma w_i_eq_of_single {n : ℕ} (C : Code n) (i : ℕ) (t : Fin n) (y : Word n)
    (hcount : count C i = 1) (ht : colVal (C t) = i) (hyt : y t = true) :
    w_i C i y = 1 := by
  have ht' : t ∈ fiber C i := by simp [fiber, ht]
  have hcard : (fiber C i).card = 1 := by
    rw [fiber_card_eq_count, hcount]
  have hfib : fiber C i = {t} := by
    rcases Finset.card_eq_one.mp hcard with ⟨a, ha⟩
    have hat : a = t := by
      have ht'a : t ∈ ({a} : Finset (Fin n)) := by
        rw [← ha]
        exact ht'
      exact (Finset.mem_singleton.mp ht'a).symm
    rw [ha, hat]
  rw [w_i_eq_card_onesOn]
  rw [hfib]
  have hone : onesOn {t} y = {t} := by
    ext u
    by_cases hu : u = t <;> simp [onesOn, hu, hyt]
  rw [hone]
  simp

/-- If |i| = 1 and the single type-i column has y = false, then w_i = 0. -/
lemma w_i_eq_zero_of_single_false {n : ℕ} (C : Code n) (i : ℕ) (t : Fin n) (y : Word n)
    (hcount : count C i = 1) (ht : colVal (C t) = i) (hyt : y t = false) :
    w_i C i y = 0 := by
  have ht' : t ∈ fiber C i := by simp [fiber, ht]
  have hcard : (fiber C i).card = 1 := by
    rw [fiber_card_eq_count, hcount]
  have hfib : fiber C i = {t} := by
    rcases Finset.card_eq_one.mp hcard with ⟨a, ha⟩
    have hat : a = t := by
      have ht'a : t ∈ ({a} : Finset (Fin n)) := by
        rw [← ha]
        exact ht'
      exact (Finset.mem_singleton.mp ht'a).symm
    rw [ha, hat]
  rw [w_i_eq_card_onesOn]
  rw [hfib]
  have hone : onesOn {t} y = ∅ := by
    ext u
    by_cases hu : u = t <;> simp [onesOn, hu, hyt]
  rw [hone]
  simp

/-- An even number at most an odd number is at most the even number one
smaller (2a ≤ 2b+1 sharpens to 2a+1 ≤ 2b+1). -/
lemma even_le_odd_succ {a b : ℕ} (h : 2 * a ≤ 2 * b + 1) : 2 * a + 1 ≤ 2 * b + 1 := by
  by_cases hab : a ≤ b
  · omega
  · exfalso
    have hgt : b < a := lt_of_not_ge hab
    omega

/-- An odd number at most an even number is at most the even number one
smaller (2a+1 ≤ 2b sharpens to 2a+2 ≤ 2b). -/
lemma odd_le_even_succ {a b : ℕ} (h : 2 * a + 1 ≤ 2 * b) : 2 * a + 2 ≤ 2 * b := by
  by_cases hab : a < b
  · omega
  · have hba : b ≤ a := le_of_not_gt hab
    omega

/-- An even number at most an odd number is at most the even number itself
(2a ≤ 2b+1 sharpens to 2a ≤ 2b). -/
lemma even_le_odd {a b : ℕ} (h : 2 * a ≤ 2 * b + 1) : 2 * a ≤ 2 * b := by
  by_cases hab : a ≤ b
  · omega
  · have hgt : b < a := lt_of_not_ge hab
    omega

/-- An odd number is not even. -/
lemma not_even_of_odd {a : ℕ} (h : Odd a) : ¬ Even a := by
  rintro ⟨k, hk⟩
  rcases h with ⟨l, hl⟩
  omega

/-- An even number is not odd. -/
lemma not_odd_of_even {a : ℕ} (h : Even a) : ¬ Odd a := by
  rintro ⟨l, hl⟩
  rcases h with ⟨k, hk⟩
  omega

/-- If min a (min b c) ≤ d with a,c > d, then b ≤ d. -/
lemma min3_le_of_gt {a b c d : ℕ} (ha : d < a) (hc : d < c) (hm : min a (min b c) ≤ d) :
    b ≤ d := by
  have hle : min b c ≤ d := by
    by_contra hnot
    have hgt : d < min b c := lt_of_not_ge hnot
    have hb1 : d + 1 ≤ min b c := Nat.succ_le_of_lt hgt
    have hb2 : d + 1 ≤ a := Nat.succ_le_of_lt ha
    have hmin_ge : d + 1 ≤ min a (min b c) := by
      apply le_min hb2 hb1
    omega
  rcases (min_le_iff.mp hle) with hb | hc'
  · exact hb
  · exfalso
    omega

/-- b−1 ≤ a ≤ b−2 with b ≥ 2 is impossible. -/
lemma sub_one_le_contra {a b : ℕ} (h1 : b - 1 ≤ a) (h2 : a ≤ b - 2) (hb : 2 ≤ b) : False := by
  omega

/-- a−2 ≤ b−2 with b ≥ 2 gives a ≤ b. -/
lemma sub_two_le_sub_two {a b : ℕ} (h : a - 2 ≤ b - 2) (hb : 2 ≤ b) : a ≤ b := by omega

/-- y ∈ Z5 forces the (t,f) orientation and the dRow conditions
d₁ ≤ d₃, d₃−1 ≤ d₀, d₃−1 ≤ d₄ (paper rewrite of eq. y25). -/
lemma Z5_implies_dRow {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (htne : t₁ ≠ t₂)
    (h1 : C t₁ = col1) (h7 : C t₂ = col7) {y : Word n} (hy : Z5 C t₁ t₂ y) :
    y t₁ = true ∧ y t₂ = false ∧ dRow C 1 y ≤ dRow C 2 y ∧
      dRow C 2 y - 1 ≤ dRow C 0 y ∧ dRow C 2 y - 1 ≤ dRow C 3 y ∧
        dRow C 2 y - 1 ≤ dO C y := by
  have hor := Z5_implies_htrue_hfalse C t₁ t₂ htne h1 h7 hy
  rcases hor with ⟨hy1, hy2⟩
  have hOp := dOp2_eq_min_of_htrue_hfalse C t₁ t₂ htne h1 h7 y hy1 hy2
  have hPp : dPp2 C t₁ t₂ y = dP C y - 2 :=
    dPp2_eq_sub_two_of_htrue_hfalse C t₁ t₂ htne h1 h7 y hy1 hy2
  have hOp_le_O : dOp2 C t₁ t₂ y ≤ dO C y :=
    dOp2_le_dO_of_htrue_hfalse C t₁ t₂ htne h1 h7 y hy1 hy2
  have hP_ge_2 : 2 ≤ dP C y := by
    have hne1 : y t₁ ≠ row C ⟨2, by decide⟩ t₁ := by
      simp [row, colBit, h1, col1, hy1]
    have hne2 : y t₂ ≠ row C ⟨2, by decide⟩ t₂ := by
      simp [row, colBit, h7, col7, hy2]
    change 2 ≤ dRow C ⟨2, by decide⟩ y
    exact dRow_ge_two_of_mismatch C ⟨2, by decide⟩ t₁ t₂ htne y hne1 hne2
  have hOp_le_Pp : dOp2 C t₁ t₂ y ≤ dPp2 C t₁ t₂ y := by
    have hmin : min (dO C y) (dOp2 C t₁ t₂ y) = dOp2 C t₁ t₂ y := min_eq_right hOp_le_O
    have hle : min (dO C y) (dOp2 C t₁ t₂ y) ≤ dPp2 C t₁ t₂ y := hy.2.2.2
    rw [hmin] at hle
    exact hle
  have hO_ge : dO C y ≥ dP C y - 1 := by
    have hminP : min (dP C y) (dP C y - 2) = dP C y - 2 := by
      apply min_eq_right
      omega
    have hgt : dO C y > min (dP C y) (dPp2 C t₁ t₂ y) := hy.2.1
    rw [hPp, hminP] at hgt
    change dP C y - 2 < dO C y at hgt
    omega
  have hRow2_ge_2 : 2 ≤ dRow C 2 y := by
    simpa [dP, dRow, row2] using hP_ge_2
  have hd0_ge : dRow C 2 y - 1 ≤ dRow C 0 y := by
    have hO' : dRow C 2 y - 1 ≤ dO C y := by
      simpa [dO, dP, dRow, row0, row1, row2, row3] using hO_ge
    exact le_trans hO' (min_le_left _ _)
  have hd4_ge : dRow C 2 y - 1 ≤ dRow C 3 y := by
    have hO' : dRow C 2 y - 1 ≤ dO C y := by
      simpa [dO, dP, dRow, row0, row1, row2, row3] using hO_ge
    exact le_trans hO' (le_trans (min_le_right _ _) (min_le_right _ _))
  have hdO_ge : dRow C 2 y - 1 ≤ dO C y := by
    simpa [dO, dP, dRow, row0, row1, row2, row3] using hO_ge
  have hd13 : dRow C 1 y ≤ dRow C 2 y := by
    have hOp_le_Pp' : dOp2 C t₁ t₂ y ≤ dP C y - 2 := by
      rw [← hPp]
      exact hOp_le_Pp
    rw [hOp] at hOp_le_Pp'
    rcases (min_le_iff.mp hOp_le_Pp') with h0 | hrest
    · exfalso
      exact sub_one_le_contra hd0_ge h0 hRow2_ge_2
    · rcases (min_le_iff.mp hrest) with h1 | h4
      · exact sub_two_le_sub_two h1 hRow2_ge_2
      · exfalso
        exact sub_one_le_contra hd4_ge h4 hRow2_ge_2
  exact ⟨hy1, hy2, hd13, hd0_ge, hd4_ge, hdO_ge⟩

/-- Lemma `lm:2` (Lemma 25) (case 2: |3| odd, |2|,|4|,|5| even): Z4¹ ∪ Z5 = ∅ iff
|1|=|7|=1, |2|=|4|=|6|=0, |3| odd, |5| even. -/
-- decide: Mechanical · n=any · checked 2026-08-27
theorem z45_empty_case2 {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (htne : t₁ ≠ t₂)
    (h1 : C t₁ = col1) (h7 : C t₂ = col7) (h07 : Columns07 C)
    (hcase : Odd (count C 3) ∧ Even (count C 2) ∧ Even (count C 4) ∧ Even (count C 5)) :
    ((∀ y : Word n, ¬ Z41 C t₁ t₂ y ∧ ¬ Z5 C t₁ t₂ y) ↔
      count C 1 = 1 ∧ count C 7 = 1 ∧ count C 2 = 0 ∧ count C 4 = 0 ∧
        count C 6 = 0 ∧ Odd (count C 3) ∧ Even (count C 5)) := by
  constructor
  · intro hE
    rcases hcase with ⟨h3o, h2e, h4e, h5e⟩
    rcases h3o with ⟨p3, hp3⟩
    rcases h2e with ⟨p2, hp2⟩
    rcases h4e with ⟨p4, hp4⟩
    rcases h5e with ⟨p5, hp5⟩
    have h1ge : 1 ≤ count C 1 := count_pos_of_colVal C t₁ (by rw [h1]; decide)
    have h7ge : 1 ≤ count C 7 := count_pos_of_colVal C t₂ (by rw [h7]; decide)
    constructor
    · by_contra h1ne
      have h1ge2 : 2 ≤ count C 1 := by omega
      have hwit : ∃ y : Word n, Z41 C t₁ t₂ y := by
        refine z4_nonempty_of_table C t₁ t₂ htne h1 h7 h07 1 p2 (p3 + 1) p4 p5
          (count C 6) (count C 7 - 1) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
        · omega
        · omega
        · omega
        · omega
        · omega
        · omega
        · omega
        · rfl
        · omega
        · omega
        · omega
        · omega
      rcases hwit with ⟨y, hy⟩
      exact (hE y).1 hy
    constructor
    · by_contra h7ne
      have h7ge2 : 2 ≤ count C 7 := by omega
      have hwit : ∃ y : Word n, Z5 C t₁ t₂ y := by
        refine z5_nonempty_of_table C t₁ t₂ htne h1 h7 h07 1 p2 p3 p4 p5
          (count C 6) (count C 7 - 1) 1 (by norm_num) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
        · omega
        · omega
        · omega
        · omega
        · omega
        · omega
        · omega
        · rfl
        · omega
        · omega
        · omega
        · omega
      rcases hwit with ⟨y, hy⟩
      exact (hE y).2 hy
    constructor
    · by_contra h2ne
      have h2pos : 1 ≤ count C 2 := by omega
      have hwit : ∃ y : Word n, Z41 C t₁ t₂ y := by
        refine z4_nonempty_of_table C t₁ t₂ htne h1 h7 h07 1 (p2 + 1) p3 p4 p5
          (count C 6) (count C 7 - 1) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
        · omega
        · omega
        · omega
        · omega
        · omega
        · omega
        · omega
        · rfl
        · omega
        · omega
        · omega
        · omega
      rcases hwit with ⟨y, hy⟩
      exact (hE y).1 hy
    constructor
    · by_contra h4ne
      have h4pos : 1 ≤ count C 4 := by omega
      have hwit : ∃ y : Word n, Z5 C t₁ t₂ y := by
        refine z5_nonempty_of_table C t₁ t₂ htne h1 h7 h07 1 p2 (p3 + 1) (p4 + 1) p5
          (count C 6) (count C 7 - 1) 1 (by norm_num) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
        · omega
        · omega
        · omega
        · omega
        · omega
        · omega
        · omega
        · rfl
        · omega
        · omega
        · omega
        · omega
      rcases hwit with ⟨y, hy⟩
      exact (hE y).2 hy
    · by_contra h6ne
      have h6ne' : count C 6 ≠ 0 := by
        intro h6
        exact h6ne ⟨h6, ⟨⟨p3, hp3⟩, ⟨p5, by omega⟩⟩⟩
      have h6pos : 1 ≤ count C 6 := Nat.succ_le_of_lt (Nat.pos_of_ne_zero h6ne')
      have hwit : ∃ y : Word n, Z5 C t₁ t₂ y := by
        refine z5_nonempty_of_table C t₁ t₂ htne h1 h7 h07 1 p2 p3 p4 p5
          (count C 6) (count C 7 - 1) 1 (by norm_num) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
        · omega
        · omega
        · omega
        · omega
        · omega
        · omega
        · omega
        · rfl
        · omega
        · omega
        · omega
        · omega
      rcases hwit with ⟨y, hy⟩
      exact (hE y).2 hy
  · rintro ⟨h1eq1, h7eq1, h2eq0, h4eq0, h6eq0, h3o, h5e⟩
    rcases h3o with ⟨p3, hp3⟩
    rcases h5e with ⟨p5, hp5⟩
    intro y
    constructor
    · intro hy
      have hz := Z41_implies_htrue_hfalse_d2_d3 C t₁ t₂ htne h1 h7 hy
      rcases hz with ⟨hy1, hy2, hd2, hd3⟩
      have hw1 : w_i C 1 y = 1 :=
        w_i_eq_of_single C 1 t₁ y h1eq1 (by rw [h1]; decide) hy1
      have hw7 : w_i C 7 y = 0 :=
        w_i_eq_zero_of_single_false C 7 t₂ y h7eq1 (by rw [h7]; decide) hy2
      have hw2 : w_i C 2 y = 0 := w_i_eq_zero_of_count_zero C 2 y h2eq0
      have hw4 : w_i C 4 y = 0 := w_i_eq_zero_of_count_zero C 4 y h4eq0
      have hw6 : w_i C 6 y = 0 := w_i_eq_zero_of_count_zero C 6 y h6eq0
      rcases dRow12_columns07 C y h07 with ⟨hd1, hd2'⟩
      rcases dRow03_columns07 C y h07 with ⟨hd0, hd4'⟩
      have ho1a : 2 * w_i C 3 y + count C 5 = 2 * w_i C 5 y + count C 3 + 1 := by
        rw [hd1, hd2'] at hd2
        rw [hw1, hw2, hw4, hw6, hw7, h7eq1, h2eq0, h4eq0, h6eq0] at hd2
        omega
      have ho1c : count C 3 + 1 ≤ 2 * w_i C 3 y := by
        have hd30 : dRow C 2 y ≤ dRow C 0 y := le_trans hd3 (min_le_left _ _)
        rw [hd2', hd0] at hd30
        rw [hw1, hw2, hw4, hw6, hw7, h7eq1, h2eq0, h6eq0] at hd30
        omega
      have ho1b : 2 * w_i C 5 y ≤ count C 5 - 1 := by
        have hd34 : dRow C 2 y ≤ dRow C 3 y := le_trans hd3 (min_le_right _ _)
        rw [hd2', hd4'] at hd34
        rw [hw1, hw2, hw4, hw6, hw7, h7eq1, h2eq0, h6eq0] at hd34
        omega
      omega
    · intro hy
      have hz := Z5_implies_dRow C t₁ t₂ htne h1 h7 hy
      rcases hz with ⟨hy1, hy2, hd13, hd30, hd34, _⟩
      have hw1 : w_i C 1 y = 1 :=
        w_i_eq_of_single C 1 t₁ y h1eq1 (by rw [h1]; decide) hy1
      have hw7 : w_i C 7 y = 0 :=
        w_i_eq_zero_of_single_false C 7 t₂ y h7eq1 (by rw [h7]; decide) hy2
      have hw2 : w_i C 2 y = 0 := w_i_eq_zero_of_count_zero C 2 y h2eq0
      have hw4 : w_i C 4 y = 0 := w_i_eq_zero_of_count_zero C 4 y h4eq0
      have hw6 : w_i C 6 y = 0 := w_i_eq_zero_of_count_zero C 6 y h6eq0
      rcases dRow12_columns07 C y h07 with ⟨hd1, hd2'⟩
      rcases dRow03_columns07 C y h07 with ⟨hd0, hd4'⟩
      have he1 : 2 * w_i C 3 y + count C 5 ≤ 2 * w_i C 5 y + count C 3 := by
        rw [hd1, hd2'] at hd13
        rw [hw1, hw2, hw4, hw6, hw7, h7eq1, h2eq0, h4eq0, h6eq0] at hd13
        omega
      have he2 : count C 3 ≤ 2 * w_i C 3 y := by
        rw [hd2', hd0] at hd30
        rw [hw1, hw2, hw4, hw6, hw7, h7eq1, h2eq0, h6eq0] at hd30
        omega
      have he3 : 2 * w_i C 5 y ≤ count C 5 := by
        rw [hd2', hd4'] at hd34
        rw [hw1, hw2, hw4, hw6, hw7, h7eq1, h2eq0, h6eq0] at hd34
        omega
      have he1' : 2 * w_i C 3 y + count C 5 + 1 ≤ 2 * w_i C 5 y + count C 3 := by
        rw [hp3, hp5] at he1
        have hsharp := even_le_odd_succ (a := w_i C 3 y + p5) (b := w_i C 5 y + p3) (by omega)
        rw [hp3, hp5]
        omega
      have hc1 : count C 5 + 1 ≤ 2 * w_i C 5 y := by omega
      omega


/-- Lemma `lm:3` (Lemma 26) (case 3: |5| odd, |2|,|3|,|4| even): Z4¹ ∪ Z5 = ∅ iff
|1|=|7|=1, |2|=|4|=|6|=0, |3| even, |5| odd. -/
-- decide: Mechanical · n=any · checked 2026-08-27
theorem z45_empty_case3 {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (htne : t₁ ≠ t₂)
    (h1 : C t₁ = col1) (h7 : C t₂ = col7) (h07 : Columns07 C)
    (hcase : Odd (count C 5) ∧ Even (count C 2) ∧ Even (count C 3) ∧ Even (count C 4)) :
    ((∀ y : Word n, ¬ Z41 C t₁ t₂ y ∧ ¬ Z5 C t₁ t₂ y) ↔
      count C 1 = 1 ∧ count C 7 = 1 ∧ count C 2 = 0 ∧ count C 4 = 0 ∧
        count C 6 = 0 ∧ Even (count C 3) ∧ Odd (count C 5)) := by
  constructor
  · intro hE
    rcases hcase with ⟨h5o, h2e, h3e, h4e⟩
    rcases h5o with ⟨p5, hp5⟩
    rcases h2e with ⟨p2, hp2⟩
    rcases h3e with ⟨p3, hp3⟩
    rcases h4e with ⟨p4, hp4⟩
    have h1ge : 1 ≤ count C 1 := count_pos_of_colVal C t₁ (by rw [h1]; decide)
    have h7ge : 1 ≤ count C 7 := count_pos_of_colVal C t₂ (by rw [h7]; decide)
    constructor
    · by_contra h1ne
      have h1ge2 : 2 ≤ count C 1 := by omega
      have hwit : ∃ y : Word n, Z5 C t₁ t₂ y := by
        refine z5_nonempty_of_table C t₁ t₂ htne h1 h7 h07 1 p2 p3 p4 (p5 + 1)
          (count C 6) (count C 7 - 1) 1 (by norm_num) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
        · omega
        · omega
        · omega
        · omega
        · omega
        · omega
        · omega
        · rfl
        · omega
        · omega
        · omega
        · omega
      rcases hwit with ⟨y, hy⟩
      exact (hE y).2 hy
    constructor
    · by_contra h7ne
      have h7ge2 : 2 ≤ count C 7 := by omega
      have hwit : ∃ y : Word n, Z41 C t₁ t₂ y := by
        refine z4_nonempty_of_table C t₁ t₂ htne h1 h7 h07 1 p2 p3 p4 p5
          (count C 6) (count C 7 - 1) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
        · omega
        · omega
        · omega
        · omega
        · omega
        · omega
        · omega
        · rfl
        · omega
        · omega
        · omega
        · omega
      rcases hwit with ⟨y, hy⟩
      exact (hE y).1 hy
    constructor
    · by_contra h2ne
      have h2pos : 1 ≤ count C 2 := by omega
      have hwit : ∃ y : Word n, Z41 C t₁ t₂ y := by
        refine z4_nonempty_of_table C t₁ t₂ htne h1 h7 h07 1 (p2 + 1) p3 p4 (p5 + 1)
          (count C 6) (count C 7 - 1) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
        · omega
        · omega
        · omega
        · omega
        · omega
        · omega
        · omega
        · rfl
        · omega
        · omega
        · omega
        · omega
      rcases hwit with ⟨y, hy⟩
      exact (hE y).1 hy
    constructor
    · by_contra h4ne
      have h4pos : 1 ≤ count C 4 := by omega
      have hwit : ∃ y : Word n, Z5 C t₁ t₂ y := by
        refine z5_nonempty_of_table C t₁ t₂ htne h1 h7 h07 1 p2 p3 (p4 + 1) p5
          (count C 6) (count C 7 - 1) 1 (by norm_num) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
        · omega
        · omega
        · omega
        · omega
        · omega
        · omega
        · omega
        · rfl
        · omega
        · omega
        · omega
        · omega
      rcases hwit with ⟨y, hy⟩
      exact (hE y).2 hy
    · by_contra h6ne
      have h6ne' : count C 6 ≠ 0 := by
        intro h6
        exact h6ne ⟨h6, ⟨⟨p3, by omega⟩, ⟨p5, hp5⟩⟩⟩
      have h6pos : 1 ≤ count C 6 := Nat.succ_le_of_lt (Nat.pos_of_ne_zero h6ne')
      have hwit : ∃ y : Word n, Z41 C t₁ t₂ y := by
        refine z4_nonempty_of_table C t₁ t₂ htne h1 h7 h07 1 p2 p3 p4 p5
          (count C 6) (count C 7 - 1) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
        · omega
        · omega
        · omega
        · omega
        · omega
        · omega
        · omega
        · rfl
        · omega
        · omega
        · omega
        · omega
      rcases hwit with ⟨y, hy⟩
      exact (hE y).1 hy
  · rintro ⟨h1eq1, h7eq1, h2eq0, h4eq0, h6eq0, h3e, h5o⟩
    rcases h3e with ⟨p3, hp3⟩
    rcases h5o with ⟨p5, hp5⟩
    intro y
    constructor
    · intro hy
      have hz := Z41_implies_htrue_hfalse_d2_d3 C t₁ t₂ htne h1 h7 hy
      rcases hz with ⟨hy1, hy2, hd2, hd3⟩
      have hw1 : w_i C 1 y = 1 :=
        w_i_eq_of_single C 1 t₁ y h1eq1 (by rw [h1]; decide) hy1
      have hw7 : w_i C 7 y = 0 :=
        w_i_eq_zero_of_single_false C 7 t₂ y h7eq1 (by rw [h7]; decide) hy2
      have hw2 : w_i C 2 y = 0 := w_i_eq_zero_of_count_zero C 2 y h2eq0
      have hw4 : w_i C 4 y = 0 := w_i_eq_zero_of_count_zero C 4 y h4eq0
      have hw6 : w_i C 6 y = 0 := w_i_eq_zero_of_count_zero C 6 y h6eq0
      rcases dRow12_columns07 C y h07 with ⟨hd1, hd2'⟩
      rcases dRow03_columns07 C y h07 with ⟨hd0, hd4'⟩
      have ho1a : 2 * w_i C 3 y + count C 5 = 2 * w_i C 5 y + count C 3 + 1 := by
        rw [hd1, hd2'] at hd2
        rw [hw1, hw2, hw4, hw6, hw7, h7eq1, h2eq0, h4eq0, h6eq0] at hd2
        omega
      have ho1c : count C 3 + 1 ≤ 2 * w_i C 3 y := by
        have hd30 : dRow C 2 y ≤ dRow C 0 y := le_trans hd3 (min_le_left _ _)
        rw [hd2', hd0] at hd30
        rw [hw1, hw2, hw4, hw6, hw7, h7eq1, h2eq0, h6eq0] at hd30
        omega
      have ho1b : 2 * w_i C 5 y ≤ count C 5 - 1 := by
        have hd34 : dRow C 2 y ≤ dRow C 3 y := le_trans hd3 (min_le_right _ _)
        rw [hd2', hd4'] at hd34
        rw [hw1, hw2, hw4, hw6, hw7, h7eq1, h2eq0, h6eq0] at hd34
        omega
      omega
    · intro hy
      have hz := Z5_implies_dRow C t₁ t₂ htne h1 h7 hy
      rcases hz with ⟨hy1, hy2, hd13, hd30, hd34, _⟩
      have hw1 : w_i C 1 y = 1 :=
        w_i_eq_of_single C 1 t₁ y h1eq1 (by rw [h1]; decide) hy1
      have hw7 : w_i C 7 y = 0 :=
        w_i_eq_zero_of_single_false C 7 t₂ y h7eq1 (by rw [h7]; decide) hy2
      have hw2 : w_i C 2 y = 0 := w_i_eq_zero_of_count_zero C 2 y h2eq0
      have hw4 : w_i C 4 y = 0 := w_i_eq_zero_of_count_zero C 4 y h4eq0
      have hw6 : w_i C 6 y = 0 := w_i_eq_zero_of_count_zero C 6 y h6eq0
      rcases dRow12_columns07 C y h07 with ⟨hd1, hd2'⟩
      rcases dRow03_columns07 C y h07 with ⟨hd0, hd4'⟩
      have he1 : 2 * w_i C 3 y + count C 5 ≤ 2 * w_i C 5 y + count C 3 := by
        rw [hd1, hd2'] at hd13
        rw [hw1, hw2, hw4, hw6, hw7, h7eq1, h2eq0, h4eq0, h6eq0] at hd13
        omega
      have he2 : count C 3 ≤ 2 * w_i C 3 y := by
        rw [hd2', hd0] at hd30
        rw [hw1, hw2, hw4, hw6, hw7, h7eq1, h2eq0, h6eq0] at hd30
        omega
      have he3 : 2 * w_i C 5 y ≤ count C 5 := by
        rw [hd2', hd4'] at hd34
        rw [hw1, hw2, hw4, hw6, hw7, h7eq1, h2eq0, h6eq0] at hd34
        omega
      have he1' : 2 * w_i C 3 y + count C 5 + 1 ≤ 2 * w_i C 5 y + count C 3 := by
        rw [hp3, hp5] at he1
        have hsharp := odd_le_even_succ (a := w_i C 3 y + p5) (b := w_i C 5 y + p3) (by omega)
        rw [hp3, hp5]
        omega
      have he3' : 2 * w_i C 5 y ≤ count C 5 - 1 := by
        rw [hp5] at he3
        have hsharp := even_le_odd (a := w_i C 5 y) (b := p5) (by omega)
        rw [hp5]
        omega
      have hc1 : count C 5 + 1 ≤ 2 * w_i C 5 y := by omega
      omega


/-- Lemma `lm:16` (Lemma 27) (case 16: |2|,|4| even, |3|,|5| odd): Z5 = ∅ iff
|1|=|7|=1, |2|=|4|=|6|=0, |3|,|5| odd. -/
-- decide: Mechanical · n=any · checked 2026-08-27
theorem z5_empty_case16 {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (htne : t₁ ≠ t₂)
    (h1 : C t₁ = col1) (h7 : C t₂ = col7) (h07 : Columns07 C)
    (hcase : Even (count C 2) ∧ Even (count C 4) ∧ Odd (count C 3) ∧ Odd (count C 5)) :
    ((∀ y : Word n, ¬ Z5 C t₁ t₂ y) ↔
      count C 1 = 1 ∧ count C 7 = 1 ∧ count C 2 = 0 ∧ count C 4 = 0 ∧
        count C 6 = 0 ∧ Odd (count C 3) ∧ Odd (count C 5)) := by
  constructor
  · intro hE
    rcases hcase with ⟨h2e, h4e, h3o, h5o⟩
    rcases h2e with ⟨p2, hp2⟩
    rcases h4e with ⟨p4, hp4⟩
    rcases h3o with ⟨p3, hp3⟩
    rcases h5o with ⟨p5, hp5⟩
    have h1ge : 1 ≤ count C 1 := count_pos_of_colVal C t₁ (by rw [h1]; decide)
    have h7ge : 1 ≤ count C 7 := count_pos_of_colVal C t₂ (by rw [h7]; decide)
    constructor
    · by_contra h1ne
      have h1ge2 : 2 ≤ count C 1 := by omega
      have hwit : ∃ y : Word n, Z5 C t₁ t₂ y := by
        refine z5_nonempty_of_table C t₁ t₂ htne h1 h7 h07 1 p2 (p3 + 1) p4 (p5 + 1)
          (count C 6) (count C 7 - 1) 0 (by norm_num) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
        · omega
        · omega
        · omega
        · omega
        · omega
        · omega
        · omega
        · rfl
        · omega
        · omega
        · omega
        · omega
      rcases hwit with ⟨y, hy⟩
      exact hE y hy
    constructor
    · by_contra h7ne
      have h7ge2 : 2 ≤ count C 7 := by omega
      have hwit : ∃ y : Word n, Z5 C t₁ t₂ y := by
        refine z5_nonempty_of_table C t₁ t₂ htne h1 h7 h07 1 p2 p3 p4 p5
          (count C 6) (count C 7 - 1) 0 (by norm_num) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
        · omega
        · omega
        · omega
        · omega
        · omega
        · omega
        · omega
        · rfl
        · omega
        · omega
        · omega
        · omega
      rcases hwit with ⟨y, hy⟩
      exact hE y hy
    constructor
    · by_contra h2ne
      have h2pos : 1 ≤ count C 2 := by omega
      have hwit : ∃ y : Word n, Z5 C t₁ t₂ y := by
        refine z5_nonempty_of_table C t₁ t₂ htne h1 h7 h07 1 (p2 + 1) p3 p4 (p5 + 1)
          (count C 6) (count C 7 - 1) 0 (by norm_num) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
        · omega
        · omega
        · omega
        · omega
        · omega
        · omega
        · omega
        · rfl
        · omega
        · omega
        · omega
        · omega
      rcases hwit with ⟨y, hy⟩
      exact hE y hy
    constructor
    · by_contra h4ne
      have h4pos : 1 ≤ count C 4 := by omega
      have hwit : ∃ y : Word n, Z5 C t₁ t₂ y := by
        refine z5_nonempty_of_table C t₁ t₂ htne h1 h7 h07 1 p2 (p3 + 1) (p4 + 1) p5
          (count C 6) (count C 7 - 1) 0 (by norm_num) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
        · omega
        · omega
        · omega
        · omega
        · omega
        · omega
        · omega
        · rfl
        · omega
        · omega
        · omega
        · omega
      rcases hwit with ⟨y, hy⟩
      exact hE y hy
    · by_contra h6ne
      have h6ne' : count C 6 ≠ 0 := by
        intro h6
        exact h6ne ⟨h6, ⟨⟨p3, hp3⟩, ⟨p5, hp5⟩⟩⟩
      have h6pos : 1 ≤ count C 6 := Nat.succ_le_of_lt (Nat.pos_of_ne_zero h6ne')
      have hwit : ∃ y : Word n, Z5 C t₁ t₂ y := by
        refine z5_nonempty_of_table C t₁ t₂ htne h1 h7 h07 1 p2 p3 p4 p5
          (count C 6) (count C 7 - 1) 0 (by norm_num) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
        · omega
        · omega
        · omega
        · omega
        · omega
        · omega
        · omega
        · rfl
        · omega
        · omega
        · omega
        · omega
      rcases hwit with ⟨y, hy⟩
      exact hE y hy
  · rintro ⟨h1eq1, h7eq1, h2eq0, h4eq0, h6eq0, h3o, h5o⟩
    rcases h3o with ⟨p3, hp3⟩
    rcases h5o with ⟨p5, hp5⟩
    intro y hy
    have hz := Z5_implies_dRow C t₁ t₂ htne h1 h7 hy
    rcases hz with ⟨hy1, hy2, hd13, hd30, hd34, _⟩
    have hw1 : w_i C 1 y = 1 :=
      w_i_eq_of_single C 1 t₁ y h1eq1 (by rw [h1]; decide) hy1
    have hw7 : w_i C 7 y = 0 :=
      w_i_eq_zero_of_single_false C 7 t₂ y h7eq1 (by rw [h7]; decide) hy2
    have hw2 : w_i C 2 y = 0 := w_i_eq_zero_of_count_zero C 2 y h2eq0
    have hw4 : w_i C 4 y = 0 := w_i_eq_zero_of_count_zero C 4 y h4eq0
    have hw6 : w_i C 6 y = 0 := w_i_eq_zero_of_count_zero C 6 y h6eq0
    rcases dRow12_columns07 C y h07 with ⟨hd1, hd2'⟩
    rcases dRow03_columns07 C y h07 with ⟨hd0, hd4'⟩
    have he1 : 2 * w_i C 3 y + count C 5 ≤ 2 * w_i C 5 y + count C 3 := by
      rw [hd1, hd2'] at hd13
      rw [hw1, hw2, hw4, hw6, hw7, h7eq1, h2eq0, h4eq0, h6eq0] at hd13
      omega
    have he2 : count C 3 ≤ 2 * w_i C 3 y := by
      rw [hd2', hd0] at hd30
      rw [hw1, hw2, hw4, hw6, hw7, h7eq1, h2eq0, h6eq0] at hd30
      omega
    have he3 : 2 * w_i C 5 y ≤ count C 5 := by
      rw [hd2', hd4'] at hd34
      rw [hw1, hw2, hw4, hw6, hw7, h7eq1, h2eq0, h6eq0] at hd34
      omega
    have he2' : count C 3 + 1 ≤ 2 * w_i C 3 y := by
      rw [hp3] at he2
      have hsharp := odd_le_even_succ (a := p3) (b := w_i C 3 y) (by omega)
      rw [hp3]
      omega
    have he3' : 2 * w_i C 5 y ≤ count C 5 - 1 := by
      rw [hp5] at he3
      have hsharp := even_le_odd (a := w_i C 5 y) (b := p5) (by omega)
      rw [hp5]
      omega
    have hc1 : count C 5 + 1 ≤ 2 * w_i C 5 y := by omega
    omega


/-- Theorem `thm:odd` (Theorem 11) (2-bit flip): replacing type-1 and type-7 columns by
types 3 and 5 is never worse; equality iff |1|=|7|=1, |2|=|4|=|6|=0 and
|3| or |5| is odd. -/
theorem two_bit_flip {n : ℕ} (C C' : Code n) (t₁ t₂ : Fin n) (hne : t₁ ≠ t₂)
    (h1 : C t₁ = col1) (h7 : C t₂ = col7) (h3 : C' t₁ = col3) (h5 : C' t₂ = col5)
    (hsame : ∀ u : Fin n, u ≠ t₁ → u ≠ t₂ → C' u = C u)
    (h07 : Columns07 C) :
    UniversalBetter C' C ∧
      (UniversalEqual C' C ↔
        count C 1 = 1 ∧ count C 7 = 1 ∧ count C 2 = 0 ∧ count C 4 = 0 ∧
          count C 6 = 0 ∧ (Odd (count C 3) ∨ Odd (count C 5))) ∧
      (UniversalStrictBetter C' C ↔
        ¬ (count C 1 = 1 ∧ count C 7 = 1 ∧ count C 2 = 0 ∧ count C 4 = 0 ∧
          count C 6 = 0 ∧ (Odd (count C 3) ∨ Odd (count C 5)))) := by
  let S : Finset (Word n) := Finset.univ.filter
    (fun y => Z41 C t₁ t₂ y ∨ Z5 C t₁ t₂ y)
  let g : Word n ≃ Word n :=
    Equiv.ofBijective (g2 C t₁ t₂) (g2_bijective C C' t₁ t₂ hne h1 h7)
  have hnotA_of_4 : ∀ y : Word n, Z4 C t₁ t₂ y →
      ¬ (Z1 C t₁ t₂ y ∨ Z2 C t₁ t₂ y ∨ Z5 C t₁ t₂ y) := fun y hz4 =>
    z_34_implies_not_A C t₁ t₂ y (Or.inr hz4)
  have hnotA_of_41 : ∀ y : Word n, Z41 C t₁ t₂ y →
      ¬ (Z1 C t₁ t₂ y ∨ Z2 C t₁ t₂ y ∨ Z5 C t₁ t₂ y) := fun y hy41 =>
    hnotA_of_4 y hy41.1
  have hgt : ∀ y : Word n, y ∈ S → dCode C y > dCode C' (g y) := by
    intro y hyS
    simp [S] at hyS
    change dCode C y > dCode C' (g2 C t₁ t₂ y)
    rcases hyS with hy41 | hy5
    · have hnotA := hnotA_of_41 y hy41
      have hg2 : g2 C t₁ t₂ y = flipTwoBits t₁ t₂ y := by simp [g2, hnotA]
      have hz4 := z_rel_4 C C' t₁ t₂ hne h1 h7 h3 h5 hsame hy41.1
      rcases hz4 with ⟨hdC, hdC'f, _⟩
      rw [hg2, hdC, hdC'f]
      exact hy41.2
    · have hg2 : g2 C t₁ t₂ y = y := by simp [g2, Or.inr (Or.inr hy5)]
      have hz5d := Z5_implies_dRow C t₁ t₂ hne h1 h7 hy5
      rcases hz5d with ⟨hy1, hy2, hd13, hd30, hd34, hdO⟩
      have hz5r := z_rel_5 C C' t₁ t₂ hne h1 h7 h3 h5 hsame hy5
      rcases hz5r with ⟨hdC, hgtP, hdC'⟩
      have hPp : dPp2 C t₁ t₂ y = dP C y - 2 :=
        dPp2_eq_sub_two_of_htrue_hfalse C t₁ t₂ hne h1 h7 y hy1 hy2
      have hRow2_ge_2 : 2 ≤ dRow C 2 y := by
        have hne1 : y t₁ ≠ row C ⟨2, by decide⟩ t₁ := by
          simp [row, colBit, h1, col1, hy1]
        have hne2 : y t₂ ≠ row C ⟨2, by decide⟩ t₂ := by
          simp [row, colBit, h7, col7, hy2]
        change 2 ≤ dRow C ⟨2, by decide⟩ y
        exact dRow_ge_two_of_mismatch C ⟨2, by decide⟩ t₁ t₂ hne y hne1 hne2
      have hPp_lt_O : dPp2 C t₁ t₂ y < dO C y := by
        rw [hPp]
        --change dP C y - 2 < dO C y
        change dRow C 2 y - 2 < dO C y
        omega
      have hPp_lt_P : dPp2 C t₁ t₂ y < dP C y := by
        rw [hPp]
        --change dP C y - 2 < dP C y
        change dRow C 2 y - 2 < dRow C 2 y
        omega
      have hPp_lt_min : dPp2 C t₁ t₂ y < min (dO C y) (dP C y) :=
        lt_min hPp_lt_O hPp_lt_P
      have hrep : C' = replaceColumn (replaceColumn C t₁ col3) t₂ col5 :=
        replace_27_eq C C' t₁ t₂ hne h3 h5 hsame
      have hdC'p : dCode C' y = dPp2 C t₁ t₂ y := by
        rw [hdC']
        rw [hrep]
        change dRow (replaceColumn (replaceColumn C t₁ col3) t₂ col5) ⟨2, by decide⟩ y =
          dRow C ⟨2, by decide⟩ (flipTwoBits t₁ t₂ y)
        rw [dRow_replace_27_2 C t₁ t₂ hne y h1 h7]
      rw [hg2, hdC, hdC'p]
      exact hPp_lt_min
  have heq : ∀ y : Word n, y ∉ S → dCode C y = dCode C' (g y) := by
    intro y hyS
    simp [S] at hyS
    change dCode C y = dCode C' (g2 C t₁ t₂ y)
    have hnot41 : ¬ Z41 C t₁ t₂ y := hyS.1
    have hnot5 : ¬ Z5 C t₁ t₂ y := hyS.2
    rcases z_partition C C t₁ t₂ y with ⟨i, hi, _⟩
    fin_cases i
    · have hz1 : Z1 C t₁ t₂ y := by simpa [ZSet] using hi
      have hg2 : g2 C t₁ t₂ y = y := by simp [g2, Or.inl hz1]
      rw [hg2]
      exact z_rel_1 C C' t₁ t₂ hne h1 h7 h3 h5 hsame hz1
    · have hz2 : Z2 C t₁ t₂ y := by simpa [ZSet] using hi
      have hg2 : g2 C t₁ t₂ y = y := by simp [g2, Or.inr (Or.inl hz2)]
      rw [hg2]
      exact (z_rel_2 C C' t₁ t₂ hne h1 h7 h3 h5 hsame hz2).1
    · have hz3 : Z3 C t₁ t₂ y := by simpa [ZSet] using hi
      have hnotA := z_34_implies_not_A C t₁ t₂ y (Or.inl hz3)
      have hg2 : g2 C t₁ t₂ y = flipTwoBits t₁ t₂ y := by simp [g2, hnotA]
      rw [hg2]
      exact (z_rel_3 C C' t₁ t₂ hne h1 h7 h3 h5 hsame hz3).1
    · have hz4 : Z4 C t₁ t₂ y := by simpa [ZSet] using hi
      have hz4r := z_rel_4 C C' t₁ t₂ hne h1 h7 h3 h5 hsame hz4
      rcases hz4r with ⟨hdC, hdC'f, hdPge⟩
      have hnotA := z_34_implies_not_A C t₁ t₂ y (Or.inr hz4)
      have hg2 : g2 C t₁ t₂ y = flipTwoBits t₁ t₂ y := by simp [g2, hnotA]
      rw [hg2]
      have hmin_le : min (dO C y) (dP C y) ≤ dOp2 C t₁ t₂ y := by
        exact le_of_not_gt (fun hgt => hnot41 ⟨hz4, hgt⟩)
      have hOp_le_O : dOp2 C t₁ t₂ y ≤ dO C y := by
        have hor := Z4_implies_htrue_hfalse C t₁ t₂ hne h1 h7 hz4
        rcases hor with ⟨hy1, hy2⟩
        exact dOp2_le_dO_of_htrue_hfalse C t₁ t₂ hne h1 h7 y hy1 hy2
      have hmin_ge : dOp2 C t₁ t₂ y ≤ min (dO C y) (dP C y) := by
        have hdPge' : dOp2 C t₁ t₂ y ≤ dP C y := by
          rw [hdC'f] at hdPge
          exact hdPge
        exact le_min hOp_le_O hdPge'
      rw [hdC, hdC'f]
      exact le_antisymm hmin_le hmin_ge
    · exfalso
      exact hnot5 (by simpa [ZSet] using hi)
  have hbetter : UniversalBetter C' C := compare_bij C C' S g hgt heq
  have heqiffS : UniversalEqual C' C ↔ S = ∅ := by
    constructor
    · intro hU
      by_contra hSne
      have hS : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hSne
      rcases hS with ⟨y, hy⟩
      have hStrict := compare_bij_strict C C' S g hgt heq ⟨y, hy⟩
      have hgt4 : lambda C' (1 / 4 : ℝ) > lambda C (1 / 4) :=
        hStrict (1 / 4) (by norm_num) (by norm_num)
      have heq4 : lambda C' (1 / 4 : ℝ) = lambda C (1 / 4) :=
        hU (1 / 4) (by norm_num) (by norm_num)
      rw [heq4] at hgt4
      exact (lt_irrefl _ hgt4)
    · intro hSempty
      have heq' : ∀ y : Word n, dCode C y = dCode C' (g y) := by
        intro y
        have hy0 : y ∉ S := by
          rw [hSempty]
          simp
        exact heq y hy0
      exact compare_bij_eq C C' g heq'
  have hSempty : S = ∅ ↔ (∀ y : Word n, ¬ Z41 C t₁ t₂ y ∧ ¬ Z5 C t₁ t₂ y) := by
    constructor
    · intro hSempty y
      have hy0 : ¬ (Z41 C t₁ t₂ y ∨ Z5 C t₁ t₂ y) := by
        intro h
        have hyS : y ∈ S := by simp [S, h]
        rw [hSempty] at hyS
        simp at hyS
      exact ⟨fun h41 => hy0 (Or.inl h41), fun h5 => hy0 (Or.inr h5)⟩
    · intro hAll
      ext y
      constructor
      · intro hyS
        simp [S] at hyS
        rcases hyS with h41 | h5
        · exact False.elim ((hAll y).1 h41)
        · exact False.elim ((hAll y).2 h5)
      · intro hy
        simp at hy
  have hempty_canon : (∀ y : Word n, ¬ Z41 C t₁ t₂ y ∧ ¬ Z5 C t₁ t₂ y) ↔
      (count C 1 = 1 ∧ count C 7 = 1 ∧ count C 2 = 0 ∧ count C 4 = 0 ∧
        count C 6 = 0 ∧ (Odd (count C 3) ∨ Odd (count C 5))) := by
    by_cases h2e : Even (count C 2)
    · by_cases h3e : Even (count C 3)
      · by_cases h4e : Even (count C 4)
        · by_cases h5e : Even (count C 5)
          · -- case 9: all even
            constructor
            · intro hAll
              exfalso
              have hweven : Even (hammingDist (row1 C) (row2 C)) := by
                rw [hammingDist_row1_row2_eq C h07]
                rcases h2e with ⟨a, ha⟩
                rcases h3e with ⟨b, hb⟩
                rcases h4e with ⟨c, hc⟩
                rcases h5e with ⟨d, hd⟩
                exact ⟨a + b + c + d, by omega⟩
              have hnot16 : ¬ (Even (count C 2) ∧ Even (count C 4) ∧
                  Odd (count C 3) ∧ Odd (count C 5)) := by
                intro h
                exact (not_odd_of_even h3e) h.2.2.1
              rcases z5_nonempty C t₁ t₂ hne h1 h7 h07
                (Or.inr (Or.inr ⟨hweven, hnot16⟩)) with ⟨y, hy5⟩
              exact (hAll y).2 hy5
            · intro hcanon
              exfalso
              rcases hcanon with ⟨_, _, _, _, _, h3or5⟩
              rcases h3or5 with h3o | h5o
              · exact (not_odd_of_even h3e) h3o
              · exact (not_odd_of_even h5e) h5o
          · -- case 3: |5| odd, |2|,|3|,|4| even
            have hz3 := z45_empty_case3 C t₁ t₂ hne h1 h7 h07
              ⟨odd_of_not_even h5e, h2e, h3e, h4e⟩
            constructor
            · intro hAll
              rcases (hz3.mp hAll) with ⟨h1c, h7c, h2c, h4c, h6c, h3e', h5o'⟩
              exact ⟨h1c, h7c, h2c, h4c, h6c, Or.inr h5o'⟩
            · intro hcanon
              rcases hcanon with ⟨h1c, h7c, h2c, h4c, h6c, h3or5⟩
              have h5o' : Odd (count C 5) := by
                rcases h3or5 with h3o | h5o
                · exact False.elim (not_odd_of_even h3e h3o)
                · exact h5o
              exact (hz3.mpr ⟨h1c, h7c, h2c, h4c, h6c, h3e, h5o'⟩)
        · by_cases h5e : Even (count C 5)
          · -- case 8: |2|,|3|,|5| even, |4| odd
            constructor
            · intro hAll
              exfalso
              rcases z5_nonempty C t₁ t₂ hne h1 h7 h07
                (Or.inr (Or.inl ⟨h2e, h3e, h5e, odd_of_not_even h4e⟩)) with ⟨y, hy5⟩
              exact (hAll y).2 hy5
            · intro hcanon
              exfalso
              rcases hcanon with ⟨_, _, _, _, _, h3or5⟩
              rcases h3or5 with h3o | h5o
              · exact (not_odd_of_even h3e) h3o
              · exact (not_odd_of_even h5e) h5o
          · -- case 14: |4|,|5| odd
            constructor
            · intro hAll
              exfalso
              have hweven : Even (hammingDist (row1 C) (row2 C)) := by
                rw [hammingDist_row1_row2_eq C h07]
                rcases h2e with ⟨a, ha⟩
                rcases h3e with ⟨b, hb⟩
                have h4o : Odd (count C 4) := odd_of_not_even h4e
                rcases h4o with ⟨c, hc⟩
                have h5o : Odd (count C 5) := odd_of_not_even h5e
                rcases h5o with ⟨d, hd⟩
                exact ⟨a + b + c + d + 1, by omega⟩
              have hnot16 : ¬ (Even (count C 2) ∧ Even (count C 4) ∧
                  Odd (count C 3) ∧ Odd (count C 5)) := by
                intro h
                exact h4e h.2.1
              rcases z5_nonempty C t₁ t₂ hne h1 h7 h07
                (Or.inr (Or.inr ⟨hweven, hnot16⟩)) with ⟨y, hy5⟩
              exact (hAll y).2 hy5
            · intro hcanon
              exfalso
              rcases hcanon with ⟨_, _, _, h4c, _, _⟩
              exact h4e (by rw [h4c]; exact ⟨0, rfl⟩)
      · by_cases h4e : Even (count C 4)
        · by_cases h5e : Even (count C 5)
          · -- case 2: |3| odd, |2|,|4|,|5| even
            have hz2 := z45_empty_case2 C t₁ t₂ hne h1 h7 h07
              ⟨odd_of_not_even h3e, h2e, h4e, h5e⟩
            constructor
            · intro hAll
              rcases (hz2.mp hAll) with ⟨h1c, h7c, h2c, h4c, h6c, h3o', h5e'⟩
              exact ⟨h1c, h7c, h2c, h4c, h6c, Or.inl h3o'⟩
            · intro hcanon
              rcases hcanon with ⟨h1c, h7c, h2c, h4c, h6c, h3or5⟩
              have h3o' : Odd (count C 3) := by
                rcases h3or5 with h3o | h5o
                · exact h3o
                · exact False.elim (not_odd_of_even h5e h5o)
              exact (hz2.mpr ⟨h1c, h7c, h2c, h4c, h6c, h3o', h5e⟩)
          · -- case 16: |2|,|4| even, |3|,|5| odd
            have hweven : Even (hammingDist (row1 C) (row2 C)) := by
              rw [hammingDist_row1_row2_eq C h07]
              rcases h2e with ⟨a, ha⟩
              have h3o : Odd (count C 3) := odd_of_not_even h3e
              rcases h3o with ⟨b, hb⟩
              rcases h4e with ⟨c, hc⟩
              have h5o : Odd (count C 5) := odd_of_not_even h5e
              rcases h5o with ⟨d, hd⟩
              exact ⟨a + b + c + d + 1, by omega⟩
            have h41empty : ∀ y : Word n, ¬ Z41 C t₁ t₂ y :=
              z4_empty_of_even C t₁ t₂ hne h1 h7 h07 hweven
            have hz5iff : (∀ y : Word n, ¬ Z5 C t₁ t₂ y) ↔
                (count C 1 = 1 ∧ count C 7 = 1 ∧ count C 2 = 0 ∧ count C 4 = 0 ∧
                  count C 6 = 0 ∧ Odd (count C 3) ∧ Odd (count C 5)) :=
              z5_empty_case16 C t₁ t₂ hne h1 h7 h07
                ⟨h2e, h4e, odd_of_not_even h3e, odd_of_not_even h5e⟩
            constructor
            · intro hAll
              rcases (hz5iff.mp (fun y => (hAll y).2)) with
                ⟨h1c, h7c, h2c, h4c, h6c, h3o, h5o⟩
              exact ⟨h1c, h7c, h2c, h4c, h6c, Or.inl h3o⟩
            · intro hcanon
              rcases hcanon with ⟨h1c, h7c, h2c, h4c, h6c, h3or5⟩
              intro y
              constructor
              · exact h41empty y
              · exact (hz5iff.mpr ⟨h1c, h7c, h2c, h4c, h6c,
                  odd_of_not_even h3e, odd_of_not_even h5e⟩) y
        · by_cases h5e : Even (count C 5)
          · -- case 12: |3|,|4| odd
            constructor
            · intro hAll
              exfalso
              have hweven : Even (hammingDist (row1 C) (row2 C)) := by
                rw [hammingDist_row1_row2_eq C h07]
                rcases h2e with ⟨a, ha⟩
                have h3o : Odd (count C 3) := odd_of_not_even h3e
                rcases h3o with ⟨b, hb⟩
                have h4o : Odd (count C 4) := odd_of_not_even h4e
                rcases h4o with ⟨c, hc⟩
                rcases h5e with ⟨d, hd⟩
                exact ⟨a + b + c + d + 1, by omega⟩
              have hnot16 : ¬ (Even (count C 2) ∧ Even (count C 4) ∧
                  Odd (count C 3) ∧ Odd (count C 5)) := by
                intro h
                exact h4e h.2.1
              rcases z5_nonempty C t₁ t₂ hne h1 h7 h07
                (Or.inr (Or.inr ⟨hweven, hnot16⟩)) with ⟨y, hy5⟩
              exact (hAll y).2 hy5
            · intro hcanon
              exfalso
              rcases hcanon with ⟨_, _, _, h4c, _, _⟩
              exact h4e (by rw [h4c]; exact ⟨0, rfl⟩)
          · -- case 6: |3|,|4|,|5| odd
            constructor
            · intro hAll
              exfalso
              have hwodd : Odd (hammingDist (row1 C) (row2 C)) := by
                rw [hammingDist_row1_row2_eq C h07]
                rcases h2e with ⟨a, ha⟩
                have h3o : Odd (count C 3) := odd_of_not_even h3e
                rcases h3o with ⟨b, hb⟩
                have h4o : Odd (count C 4) := odd_of_not_even h4e
                rcases h4o with ⟨c, hc⟩
                have h5o : Odd (count C 5) := odd_of_not_even h5e
                rcases h5o with ⟨d, hd⟩
                exact ⟨a + b + c + d + 1, by omega⟩
              rcases z4_nonempty_cases C t₁ t₂ hne h1 h7 h07 hwodd
                (Or.inr (Or.inr (Or.inr ⟨h2e, odd_of_not_even h3e,
                  odd_of_not_even h4e, odd_of_not_even h5e⟩))) with ⟨y, hy41⟩
              exact (hAll y).1 hy41
            · intro hcanon
              exfalso
              rcases hcanon with ⟨_, _, _, h4c, _, _⟩
              exact h4e (by rw [h4c]; exact ⟨0, rfl⟩)
    · by_cases h3e : Even (count C 3)
      · by_cases h4e : Even (count C 4)
        · by_cases h5e : Even (count C 5)
          · -- case 1: |2| odd, |3|,|4|,|5| even
            constructor
            · intro hAll
              exfalso
              have hwodd : Odd (hammingDist (row1 C) (row2 C)) := by
                rw [hammingDist_row1_row2_eq C h07]
                have h2o : Odd (count C 2) := odd_of_not_even h2e
                rcases h2o with ⟨a, ha⟩
                rcases h3e with ⟨b, hb⟩
                rcases h4e with ⟨c, hc⟩
                rcases h5e with ⟨d, hd⟩
                exact ⟨a + b + c + d, by omega⟩
              rcases z4_nonempty_cases C t₁ t₂ hne h1 h7 h07 hwodd
                (Or.inl ⟨odd_of_not_even h2e, h3e, h4e, h5e⟩) with ⟨y, hy41⟩
              exact (hAll y).1 hy41
            · intro hcanon
              exfalso
              rcases hcanon with ⟨_, _, h2c, _, _, _⟩
              exact h2e (by rw [h2c]; exact ⟨0, rfl⟩)
          · -- case 11: |2|,|5| odd
            constructor
            · intro hAll
              exfalso
              have hweven : Even (hammingDist (row1 C) (row2 C)) := by
                rw [hammingDist_row1_row2_eq C h07]
                have h2o : Odd (count C 2) := odd_of_not_even h2e
                rcases h2o with ⟨a, ha⟩
                rcases h3e with ⟨b, hb⟩
                rcases h4e with ⟨c, hc⟩
                have h5o : Odd (count C 5) := odd_of_not_even h5e
                rcases h5o with ⟨d, hd⟩
                exact ⟨a + b + c + d + 1, by omega⟩
              have hnot16 : ¬ (Even (count C 2) ∧ Even (count C 4) ∧
                  Odd (count C 3) ∧ Odd (count C 5)) := by
                intro h
                exact (not_odd_of_even h3e) h.2.2.1
              rcases z5_nonempty C t₁ t₂ hne h1 h7 h07
                (Or.inr (Or.inr ⟨hweven, hnot16⟩)) with ⟨y, hy5⟩
              exact (hAll y).2 hy5
            · intro hcanon
              exfalso
              rcases hcanon with ⟨_, _, h2c, _, _, _⟩
              exact h2e (by rw [h2c]; exact ⟨0, rfl⟩)
        · by_cases h5e : Even (count C 5)
          · -- case 13: |2|,|4| odd
            constructor
            · intro hAll
              exfalso
              have hweven : Even (hammingDist (row1 C) (row2 C)) := by
                rw [hammingDist_row1_row2_eq C h07]
                have h2o : Odd (count C 2) := odd_of_not_even h2e
                rcases h2o with ⟨a, ha⟩
                rcases h3e with ⟨b, hb⟩
                have h4o : Odd (count C 4) := odd_of_not_even h4e
                rcases h4o with ⟨c, hc⟩
                rcases h5e with ⟨d, hd⟩
                exact ⟨a + b + c + d + 1, by omega⟩
              have hnot16 : ¬ (Even (count C 2) ∧ Even (count C 4) ∧
                  Odd (count C 3) ∧ Odd (count C 5)) := by
                intro h
                exact h2e h.1
              rcases z5_nonempty C t₁ t₂ hne h1 h7 h07
                (Or.inr (Or.inr ⟨hweven, hnot16⟩)) with ⟨y, hy5⟩
              exact (hAll y).2 hy5
            · intro hcanon
              exfalso
              rcases hcanon with ⟨_, _, h2c, _, _, _⟩
              exact h2e (by rw [h2c]; exact ⟨0, rfl⟩)
          · -- case 5: |2|,|4|,|5| odd
            constructor
            · intro hAll
              exfalso
              have hwodd : Odd (hammingDist (row1 C) (row2 C)) := by
                rw [hammingDist_row1_row2_eq C h07]
                have h2o : Odd (count C 2) := odd_of_not_even h2e
                rcases h2o with ⟨a, ha⟩
                rcases h3e with ⟨b, hb⟩
                have h4o : Odd (count C 4) := odd_of_not_even h4e
                rcases h4o with ⟨c, hc⟩
                have h5o : Odd (count C 5) := odd_of_not_even h5e
                rcases h5o with ⟨d, hd⟩
                exact ⟨a + b + c + d + 1, by omega⟩
              rcases z4_nonempty_cases C t₁ t₂ hne h1 h7 h07 hwodd
                (Or.inr (Or.inr (Or.inl ⟨odd_of_not_even h2e, h3e,
                  odd_of_not_even h4e, odd_of_not_even h5e⟩))) with ⟨y, hy41⟩
              exact (hAll y).1 hy41
            · intro hcanon
              exfalso
              rcases hcanon with ⟨_, _, h2c, _, _, _⟩
              exact h2e (by rw [h2c]; exact ⟨0, rfl⟩)
      · by_cases h4e : Even (count C 4)
        · by_cases h5e : Even (count C 5)
          · -- case 10: |2|,|3| odd
            constructor
            · intro hAll
              exfalso
              have hweven : Even (hammingDist (row1 C) (row2 C)) := by
                rw [hammingDist_row1_row2_eq C h07]
                have h2o : Odd (count C 2) := odd_of_not_even h2e
                rcases h2o with ⟨a, ha⟩
                have h3o : Odd (count C 3) := odd_of_not_even h3e
                rcases h3o with ⟨b, hb⟩
                rcases h4e with ⟨c, hc⟩
                rcases h5e with ⟨d, hd⟩
                exact ⟨a + b + c + d + 1, by omega⟩
              have hnot16 : ¬ (Even (count C 2) ∧ Even (count C 4) ∧
                  Odd (count C 3) ∧ Odd (count C 5)) := by
                intro h
                exact h2e h.1
              rcases z5_nonempty C t₁ t₂ hne h1 h7 h07
                (Or.inr (Or.inr ⟨hweven, hnot16⟩)) with ⟨y, hy5⟩
              exact (hAll y).2 hy5
            · intro hcanon
              exfalso
              rcases hcanon with ⟨_, _, h2c, _, _, _⟩
              exact h2e (by rw [h2c]; exact ⟨0, rfl⟩)
          · -- case 7: |2|,|3|,|5| odd
            constructor
            · intro hAll
              exfalso
              rcases z5_nonempty C t₁ t₂ hne h1 h7 h07
                (Or.inl ⟨odd_of_not_even h2e, odd_of_not_even h3e,
                  odd_of_not_even h5e, h4e⟩) with ⟨y, hy5⟩
              exact (hAll y).2 hy5
            · intro hcanon
              exfalso
              rcases hcanon with ⟨_, _, h2c, _, _, _⟩
              exact h2e (by rw [h2c]; exact ⟨0, rfl⟩)
        · by_cases h5e : Even (count C 5)
          · -- case 4: |2|,|3|,|4| odd, |5| even
            constructor
            · intro hAll
              exfalso
              have hwodd : Odd (hammingDist (row1 C) (row2 C)) := by
                rw [hammingDist_row1_row2_eq C h07]
                have h2o : Odd (count C 2) := odd_of_not_even h2e
                rcases h2o with ⟨a, ha⟩
                have h3o : Odd (count C 3) := odd_of_not_even h3e
                rcases h3o with ⟨b, hb⟩
                have h4o : Odd (count C 4) := odd_of_not_even h4e
                rcases h4o with ⟨c, hc⟩
                rcases h5e with ⟨d, hd⟩
                exact ⟨a + b + c + d + 1, by omega⟩
              rcases z4_nonempty_cases C t₁ t₂ hne h1 h7 h07 hwodd
                (Or.inr (Or.inl ⟨odd_of_not_even h2e, odd_of_not_even h3e,
                  odd_of_not_even h4e, h5e⟩)) with ⟨y, hy41⟩
              exact (hAll y).1 hy41
            · intro hcanon
              exfalso
              rcases hcanon with ⟨_, _, h2c, _, _, _⟩
              exact h2e (by rw [h2c]; exact ⟨0, rfl⟩)
          · -- case 15: all odd
            constructor
            · intro hAll
              exfalso
              have hweven : Even (hammingDist (row1 C) (row2 C)) := by
                rw [hammingDist_row1_row2_eq C h07]
                have h2o : Odd (count C 2) := odd_of_not_even h2e
                rcases h2o with ⟨a, ha⟩
                have h3o : Odd (count C 3) := odd_of_not_even h3e
                rcases h3o with ⟨b, hb⟩
                have h4o : Odd (count C 4) := odd_of_not_even h4e
                rcases h4o with ⟨c, hc⟩
                have h5o : Odd (count C 5) := odd_of_not_even h5e
                rcases h5o with ⟨d, hd⟩
                exact ⟨a + b + c + d + 2, by omega⟩
              have hnot16 : ¬ (Even (count C 2) ∧ Even (count C 4) ∧
                  Odd (count C 3) ∧ Odd (count C 5)) := by
                intro h
                exact h2e h.1
              rcases z5_nonempty C t₁ t₂ hne h1 h7 h07
                (Or.inr (Or.inr ⟨hweven, hnot16⟩)) with ⟨y, hy5⟩
              exact (hAll y).2 hy5
            · intro hcanon
              exfalso
              rcases hcanon with ⟨_, _, h2c, _, _, _⟩
              exact h2e (by rw [h2c]; exact ⟨0, rfl⟩)
  have hstrict_iff : UniversalStrictBetter C' C ↔
      ¬ (count C 1 = 1 ∧ count C 7 = 1 ∧ count C 2 = 0 ∧ count C 4 = 0 ∧
        count C 6 = 0 ∧ (Odd (count C 3) ∨ Odd (count C 5))) := by
    constructor
    · intro hs hcondA
      have hU : UniversalEqual C' C := heqiffS.mpr (hSempty.mpr (hempty_canon.mpr hcondA))
      have hgt4 : lambda C' (1 / 4 : ℝ) > lambda C (1 / 4) :=
        hs (1 / 4) (by norm_num) (by norm_num)
      have heq4 : lambda C' (1 / 4 : ℝ) = lambda C (1 / 4) :=
        hU (1 / 4) (by norm_num) (by norm_num)
      rw [heq4] at hgt4
      exact (lt_irrefl _ hgt4)
    · intro hnotCondA
      have hSne : S ≠ ∅ := by
        intro hSempty0
        exact hnotCondA (hempty_canon.mp (hSempty.mp hSempty0))
      have hSne' : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hSne
      rcases hSne' with ⟨y, hy⟩
      exact compare_bij_strict C C' S g hgt heq ⟨y, hy⟩
  exact ⟨hbetter, heqiffS.trans (hSempty.trans hempty_canon), hstrict_iff⟩


end N4Code
