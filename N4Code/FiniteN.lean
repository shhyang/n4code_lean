import N4Code.ClassI
import N4Code.ZeroColumn
import N4Code.Performance
import N4Code.Nbig
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases

/-!
# Phase H: finite classification (paper §2.3, `thm:n8` (Theorem 5))

For 2 ≤ n ≤ 8, n ≠ 3, every optimal `(n,4)` code is equivalent to a linear
code; for n = 3 the optimal codes are exactly the five codes of eq. (eq:2)
and their equivalents (`InOptimal3`).  The 4 ≤ n ≤ 8 case verifies the
hypothesis of `thm:condition_optimalcode` (Theorem 4) (every Class-I code with |1| ≥ 3
is improved by the argmin one-column change) via `thm:301` (Theorem 17) and the bound
min{|3|,|5|,|6|} ≤ 1; the n = 2 and n = 3 cases are direct.

The statement stub formerly lived in `Statements.lean`; per the convention
that phase modules own their statement stubs, it now lives here.
-/

namespace N4Code

/-- The `thm:condition_optimalcode` (Theorem 4) hypothesis holds for n ≤ 8: a Class-I
code with |1| ≥ 3 has |3|+|5|+|6| = n − |1| ≤ 5, hence
min{|3|,|5|,|6|} ≤ 1, so `thm:301` (Theorem 17) (`class1_min`) applies. -/
lemma class1_cond_n_le8 {n : ℕ} (hn8 : n ≤ 8) (C : Code n)
    (h : ClassI C) (h1 : 3 ≤ count C 1) (t : Fin n) (ht : C t = col1) :
    UniversalBetter (replaceColumn C t (argminType C)) C := by
  have htot : totalCounts C {1, 3, 5, 6} = n := h.2.2
  have hmin : min (count C 3) (min (count C 5) (count C 6)) ≤ 1 := by
    by_contra hnot
    have h2 : 2 ≤ min (count C 3) (min (count C 5) (count C 6)) := by omega
    have h3 : 2 ≤ count C 3 := le_trans h2 (min_le_left _ _)
    have h5 : 2 ≤ count C 5 := le_trans (le_trans h2 (min_le_right _ _)) (min_le_left _ _)
    have h6 : 2 ≤ count C 6 := le_trans (le_trans h2 (min_le_right _ _)) (min_le_right _ _)
    have hsum : count C 1 + count C 3 + count C 5 + count C 6 = n := by
      calc
        count C 1 + count C 3 + count C 5 + count C 6
            = ∑ i ∈ ({1, 3, 5, 6} : Finset ℕ), count C i := by
              simp [Finset.sum_insert]
              omega
        _ = n := htot
    have hle : count C 3 + count C 5 + count C 6 ≤ 5 := by omega
    have hge : 6 ≤ count C 3 + count C 5 + count C 6 := by omega
    omega
  exact class1_min C t h ht hmin

/-! ## n = 2 (paper `thm:n8` (Theorem 5), first case)

Every universally-optimal `(2,4)` code has four distinct rows (otherwise the
full space `F2` is strictly better via `universalStrictBetter_of_rows_subset`),
hence is a row permutation of `F2`; `F2` is linear (`IsLinear`), so the code
is equivalent to a linear code.
-/

/-- The four 2-bit words, for the n = 2 case analysis. -/
def w00 : Word 2 := fun _ => false

/-- The word (0,1). -/
def w01 : Word 2 := fun t => t.val = 1

/-- The word (1,0). -/
def w10 : Word 2 := fun t => t.val = 0

/-- The word (1,1). -/
def w11 : Word 2 := fun _ => true

/-- Every 2-bit word is one of w00..w11. -/
lemma word2_cases : ∀ y : Word 2, y = w00 ∨ y = w01 ∨ y = w10 ∨ y = w11 := by
  decide

/-- The full (2,4) code (columns of types 3 and 5). -/
def F2 : Code 2 := fun t => if t.val = 0 then col3 else col5

-- native_decide: Contentful · n=2 · checked 2026-08-28
/-- The rows of `F2` are w00..w11 in order. -/
lemma F2_row0 : row F2 0 = w00 := by native_decide
-- native_decide: Contentful · n=2 · checked 2026-08-28
lemma F2_row1 : row F2 1 = w01 := by native_decide
-- native_decide: Contentful · n=2 · checked 2026-08-28
lemma F2_row2 : row F2 2 = w10 := by native_decide
-- native_decide: Contentful · n=2 · checked 2026-08-28
lemma F2_row3 : row F2 3 = w11 := by native_decide

/-- The rows of `F2` are exactly the four words. -/
lemma F2_rows_all (y : Word 2) : ∃ j : Fin 4, row F2 j = y := by
  rcases word2_cases y with hy | hy | hy | hy
  · exact ⟨0, by simpa [F2_row0] using hy.symm⟩
  · exact ⟨1, by simpa [F2_row1] using hy.symm⟩
  · exact ⟨2, by simpa [F2_row2] using hy.symm⟩
  · exact ⟨3, by simpa [F2_row3] using hy.symm⟩

-- native_decide: Contentful · n=2 · checked 2026-08-28
/-- `F2` is a linear code. -/
lemma F2_linear : IsLinear F2 := by
  constructor
  · intro t
    fin_cases t <;> native_decide
  · exact Or.inl ⟨by native_decide, by native_decide⟩

/-- The word set of blocklength 2 has cardinality 4. -/
lemma word2_card : (Finset.univ : Finset (Word 2)).card = 4 := by
  rw [Finset.card_univ]
  dsimp [Word]
  rw [Fintype.card_fun]
  norm_num

/-- A universally-optimal `(2,4)` code has distinct rows: with a repeated row
some word is missing, and the full space is strictly better, contradicting
optimality. -/
lemma n2_opt_distinct {C : Code 2} (hopt : ∀ D : Code 2, UniversalBetter C D) :
    DistinctRows C := by
  by_contra hnd
  have hnew : ∃ j' : Fin 4, ∀ j : Fin 4, row C j ≠ row F2 j' := by
    by_contra hnot
    have hall : ∀ j' : Fin 4, ∃ j : Fin 4, row C j = row F2 j' := by
      intro j'
      by_contra h
      exact hnot ⟨j', by intro j hj; exact h ⟨j, hj⟩⟩
    have himg : (Finset.univ : Finset (Word 2)) ⊆
        (Finset.univ.image (fun j : Fin 4 => row C j)) := by
      intro y hy
      rcases F2_rows_all y with ⟨j', hj'⟩
      rcases hall j' with ⟨j, hj⟩
      exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, by rw [hj, hj']⟩
    have hcard : (Finset.univ.image (fun j : Fin 4 => row C j)).card = 4 := by
      have hle : (Finset.univ.image (fun j : Fin 4 => row C j)).card ≤
          (Finset.univ : Finset (Word 2)).card :=
        Finset.card_le_card (by intro x hx; exact Finset.mem_univ x)
      have hge : (Finset.univ : Finset (Word 2)).card ≤
          (Finset.univ.image (fun j : Fin 4 => row C j)).card := Finset.card_le_card himg
      have hcw : (Finset.univ : Finset (Word 2)).card = 4 := word2_card
      omega
    have hdist' : DistinctRows C := by
      have hinj : Set.InjOn (fun j : Fin 4 => row C j) (Finset.univ : Finset (Fin 4)) := by
        apply (Finset.card_image_iff).mp
        rw [hcard]
        rw [Finset.card_univ]
        norm_num
      intro i j hij hrow
      exact hij (hinj (by simp) (by simp) hrow)
    exact hnd hdist'
  have hsup : ∀ j : Fin 4, ∃ j' : Fin 4, row C j = row F2 j' := by
    intro j
    rcases F2_rows_all (row C j) with ⟨j', hj'⟩
    exact ⟨j', hj'.symm⟩
  have hstrict : UniversalStrictBetter F2 C :=
    universalStrictBetter_of_rows_subset C F2 hsup hnew
  have hoptF2 : UniversalBetter C F2 := hopt F2
  have hgt : lambda F2 (1 / 4 : ℝ) > lambda C (1 / 4 : ℝ) :=
    hstrict (1 / 4 : ℝ) (by norm_num) (by norm_num)
  have hge : lambda C (1 / 4 : ℝ) ≥ lambda F2 (1 / 4 : ℝ) :=
    hoptF2 (1 / 4 : ℝ) (by norm_num) (by norm_num)
  linarith

/-- A `(2,4)` code with distinct rows has all four words as rows, so it is a
row permutation of `F2` (hence equivalent to it). -/
-- native_decide: Contentful · n=2 · checked 2026-08-28
lemma n2_distinct_equiv_F2 {C : Code 2} (hdist : DistinctRows C) :
    Equivalent C F2 := by
  have hsurj : ∀ y : Word 2, ∃ j : Fin 4, row C j = y := by
    intro y
    have hinj : Set.InjOn (fun j : Fin 4 => row C j) (Finset.univ : Finset (Fin 4)) := by
      intro a ha b hb hrow
      by_contra hab
      exact (hdist a b hab) hrow
    have hcard : (Finset.univ.image (fun j : Fin 4 => row C j)).card =
        (Finset.univ : Finset (Word 2)).card := by
      calc
        (Finset.univ.image (fun j : Fin 4 => row C j)).card
            = (Finset.univ : Finset (Fin 4)).card := (Finset.card_image_iff).mpr hinj
        _ = 4 := by rw [Finset.card_univ]; norm_num
        _ = (Finset.univ : Finset (Word 2)).card := by rw [word2_card]
    have himg : (Finset.univ.image (fun j : Fin 4 => row C j)) =
        (Finset.univ : Finset (Word 2)) := by
      apply Finset.eq_of_subset_of_card_le
      · intro x hx
        exact Finset.mem_univ x
      · rw [hcard]
    have hy : y ∈ (Finset.univ.image (fun j : Fin 4 => row C j)) := by
      rw [himg]
      exact Finset.mem_univ y
    rcases Finset.mem_image.mp hy with ⟨j, _, hj⟩
    exact ⟨j, hj⟩
  let ρ0 : Fin 4 → Fin 4 := fun j => Classical.choose (hsurj (row F2 j))
  have hρ : ∀ j : Fin 4, row C (ρ0 j) = row F2 j :=
    fun j => Classical.choose_spec (hsurj (row F2 j))
  have hρinj : Function.Injective ρ0 := by
    intro a b hab
    have hrow : row F2 a = row F2 b := by
      calc
        row F2 a = row C (ρ0 a) := (hρ a).symm
        _ = row C (ρ0 b) := by rw [hab]
        _ = row F2 b := hρ b
    have hinjF2 : Function.Injective (fun j : Fin 4 => row F2 j) := by
      native_decide
    exact hinjF2 hrow
  have hρsurj : Function.Surjective ρ0 := by
    intro j
    rcases F2_rows_all (row C j) with ⟨j', hj'⟩
    refine ⟨j', ?_⟩
    have hrow' : row C (ρ0 j') = row F2 j' := hρ j'
    have heq : row C (ρ0 j') = row C j := hrow'.trans hj'
    have hinjC : Function.Injective (fun k : Fin 4 => row C k) := by
      intro a b hab
      by_contra hab'
      exact (hdist a b hab') hab
    exact hinjC heq
  let ρ : Equiv (Fin 4) (Fin 4) := Equiv.ofBijective ρ0 ⟨hρinj, hρsurj⟩
  refine ⟨ρ, Equiv.refl (Fin 2), fun _ => false, ?_⟩
  intro t
  funext j
  change F2 t j = rowPermute ρ (C t) j
  have hrowj : row C (ρ j) = row F2 j := hρ j
  have hf : (row C (ρ j)) t = (row F2 j) t := congrFun hrowj t
  simpa [row, rowPermute, colBit] using hf.symm

/-- The n = 2 case of `thm:n8` (Theorem 5): every optimal `(2,4)` code is equivalent to
a linear code. -/
lemma n2_optimal_linear (C : Code 2) (hopt : ∀ D : Code 2, UniversalBetter C D) :
    ∃ C' : Code 2, Equivalent C C' ∧ IsLinear C' := by
  have hdist := n2_opt_distinct (C := C) hopt
  exact ⟨F2, n2_distinct_equiv_F2 (C := C) hdist, F2_linear⟩

/-! ## n = 3 (paper `thm:n8` (Theorem 5), second case)

Every optimal `(3,4)` code is equivalent to one of the five codes of
`eq:2`: (1,5,7) (`code135`), (1,3,6) (`code136`), C_A, C(1,1,1), C(1,2,0)
(`InOptimal3`).  This section handles the codes with a type-0 or type-15
column: `thm:0column` (Theorem 6) forces a C0-form code (equivalent to C_A) or a strict
contradiction.  The columns-in-1..14 covering is developed separately.
-/

/-- Flipping one column is an equivalence (used to turn a type-15 column
into a type-0 column). -/
lemma equivalent_replace_flip {n : ℕ} (C : Code n) (t : Fin n) :
    Equivalent C (replaceColumn C t (flipCol (C t))) := by
  refine ⟨Equiv.refl (Fin 4), Equiv.refl (Fin n), fun u => u = t, ?_⟩
  intro u
  by_cases hu : u = t
  · subst u
    simp [replaceColumn]
    change flipCol (C t) = flipCol (C t)
    rfl
  · simp [replaceColumn, hu]
    change C u = C u
    rfl

/-- A C0-form `(3,4)` code has exactly one column of each of the types 0, 5,
6 (`thm:0column` (Theorem 6)'s special form). -/
lemma n3_c0form_counts {C0 : Code 3} (h : C0form C0) :
    count C0 0 = 1 ∧ count C0 5 = 1 ∧ count C0 6 = 1 := by
  rcases h with ⟨hcnt, h5o, h6o⟩
  rcases h5o with ⟨a, ha⟩
  rcases h6o with ⟨b, hb⟩
  rw [ha, hb] at hcnt
  have h0 : count C0 0 = 1 := by omega
  have ha0 : a = 0 := by omega
  have hb0 : b = 0 := by omega
  have h5 : count C0 5 = 1 := by rw [ha, ha0]; norm_num
  have h6 : count C0 6 = 1 := by rw [hb, hb0]; norm_num
  exact ⟨h0, h5, h6⟩

/-- Every column of a C0-form `(3,4)` code has type 0, 5, or 6. -/
lemma n3_c0form_types {C0 : Code 3} (h : C0form C0) (t : Fin 3) :
    colVal (C0 t) = 0 ∨ colVal (C0 t) = 5 ∨ colVal (C0 t) = 6 := by
  rcases h with ⟨hcnt, h5o, h6o⟩
  have htot : totalCounts C0 ({0, 5, 6} : Finset ℕ) = 3 := by
    unfold totalCounts
    simp [Finset.sum_insert]
    omega
  simpa [Finset.mem_insert, Finset.mem_singleton] using
    (colVal_mem_of_totalCounts C0 ({0, 5, 6} : Finset ℕ) htot t)

/-- A column of type i is unique when |i| = 1. -/
lemma colVal_unique_of_count_one {n : ℕ} {C : Code n} {i : ℕ} (t0 : Fin n)
    (ht0 : colVal (C t0) = i) (h1 : count C i = 1) :
    ∀ u : Fin n, colVal (C u) = i → u = t0 := by
  intro u hu
  by_contra hne
  have hu' : u ∈ (Finset.univ.filter fun v : Fin n => colVal (C v) = i) := by
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ u, hu⟩
  have ht0' : t0 ∈ (Finset.univ.filter fun v : Fin n => colVal (C v) = i) := by
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ t0, ht0⟩
  have hsub : ({u, t0} : Finset (Fin n)) ⊆
      (Finset.univ.filter fun v : Fin n => colVal (C v) = i) := by
    intro v hv
    simp at hv
    rcases hv with hv | hv
    · subst v; exact hu'
    · subst v; exact ht0'
  have hcard2 : 2 ≤ ({u, t0} : Finset (Fin n)).card := by
    rw [Finset.card_insert_of_notMem]
    · simp
    · intro hmem
      exact hne (by simpa using hmem)
  have hc : 2 ≤ count C i := by
    simpa [count_eq_card] using le_trans hcard2 (Finset.card_le_card hsub)
  omega

/-- A column of type 0 is unique when |0| = 1 (the col0 form of
`colVal_unique_of_count_one`). -/
-- native_decide: Mechanical · n=any · checked 2026-08-24
lemma col_of_count_one {n : ℕ} {C : Code n} (t0 : Fin n)
    (ht0 : C t0 = col0) (h1 : count C 0 = 1) :
    ∀ u : Fin n, C u = col0 → u = t0 := by
  have hcv0 : colVal (C t0) = 0 := by rw [ht0]; native_decide
  intro u hu
  have hcvu : colVal (C u) = 0 := by rw [hu]; native_decide
  exact colVal_unique_of_count_one (C := C) t0 hcv0 h1 u hcvu

/-- Every Class-III `(3,4)` code is equivalent to `code135` (subclass a,
columns (1,5,7)) or `code136` (subclass b, columns (1,3,6)); both are in the
`thm:n8` (Theorem 5) five-code list. -/
lemma n3_class3_equiv (C : Code 3) (h : ClassIII C) :
    Equivalent C code135 ∨ Equivalent C code136 := by
  rcases h with ⟨htot, hpar⟩
  rcases hpar with hIIIa | hIIIb
  · rcases hIIIa with ⟨h1, h7, h6, h3e, h5o⟩
    have htot' : count C 1 + count C 3 + count C 5 + count C 6 + count C 7 = 3 := by
      unfold totalCounts at htot
      simp [Finset.sum_insert] at htot
      omega
    rcases h3e with ⟨a, ha⟩
    rcases h5o with ⟨b, hb⟩
    have h3z : count C 3 = 0 := by omega
    have h5 : count C 5 = 1 := by omega
    have htypes : ∀ t : Fin 3, colVal (C t) = 1 ∨ colVal (C t) = 5 ∨ colVal (C t) = 7 := by
      intro t
      have htot17 : totalCounts C ({1, 5, 7} : Finset ℕ) = 3 := by
        unfold totalCounts
        simp [Finset.sum_insert]
        omega
      simpa [Finset.mem_insert, Finset.mem_singleton] using
        (colVal_mem_of_totalCounts C ({1, 5, 7} : Finset ℕ) htot17 t)
    rcases exists_col_of_colVal C 1 (by rw [h1]) with ⟨t1, ht1⟩
    rcases exists_col_of_colVal C 5 (by rw [h5]) with ⟨t5, ht5⟩
    rcases exists_col_of_colVal C 7 (by rw [h7]) with ⟨t7, ht7⟩
    have huniq1 : ∀ u : Fin 3, colVal (C u) = 1 → u = t1 := colVal_unique_of_count_one (C := C) t1 ht1 h1
    have huniq5 : ∀ u : Fin 3, colVal (C u) = 5 → u = t5 := colVal_unique_of_count_one (C := C) t5 ht5 h5
    have huniq7 : ∀ u : Fin 3, colVal (C u) = 7 → u = t7 := colVal_unique_of_count_one (C := C) t7 ht7 h7
    have htri : ∀ t : Fin 3, t = t1 ∨ t = t5 ∨ t = t7 := by
      intro t
      rcases htypes t with hv1 | hv5 | hv7
      · left; exact huniq1 t hv1
      · right; left; exact huniq5 t hv5
      · right; right; exact huniq7 t hv7
    let posOf : ℕ → Fin 3 := fun i => if i = 1 then ⟨0, by decide⟩ else if i = 5 then ⟨1, by decide⟩ else ⟨2, by decide⟩
    let toFun : Fin 3 → Fin 3 := fun t => posOf (colVal (C t))
    let invFun : Fin 3 → Fin 3 := fun j => if j.val = 0 then t1 else if j.val = 1 then t5 else t7
    let p : Fin 3 ≃ Fin 3 :=
      { toFun := toFun
        invFun := invFun
        left_inv := by
          intro t
          rcases htri t with ht1c | ht5c | ht7c
          · subst t; simp [toFun, invFun, posOf, ht1]
          · subst t; simp [toFun, invFun, posOf, ht5]
          · subst t; simp [toFun, invFun, posOf, ht7]
        right_inv := by
          intro j
          fin_cases j
          · simp [toFun, invFun, posOf, ht1]
          · simp [toFun, invFun, posOf, ht5]
          · simp [toFun, invFun, posOf, ht7] }
    have heq : Equivalent C code135 := by
      refine ⟨Equiv.refl (Fin 4), p, fun _ => false, ?_⟩
      intro t
      rcases htri t with ht1c | ht5c | ht7c
      · subst t
        have hp : p t1 = ⟨0, by decide⟩ := by simp [p, toFun, posOf, ht1]
        have hc : C t1 = col1 := (colVal_eq_one_iff_col1 (C t1)).mp ht1
        simp [code135, hp, hc]
        change col1 = col1
        rfl
      · subst t
        have hp : p t5 = ⟨1, by decide⟩ := by simp [p, toFun, posOf, ht5]
        have hc : C t5 = col5 := (colVal_eq_five_iff_col5 (C t5)).mp ht5
        simp [code135, hp, hc]
        change col5 = col5
        rfl
      · subst t
        have hp : p t7 = ⟨2, by decide⟩ := by simp [p, toFun, posOf, ht7]
        have hc : C t7 = col7 := (colVal_eq_seven_iff_col7 (C t7)).mp ht7
        simp [code135, hp, hc]
        change col7 = col7
        rfl
    exact Or.inl heq
  · rcases hIIIb with ⟨h1, h5, h7, h3o, h6o⟩
    have htot' : count C 1 + count C 3 + count C 5 + count C 6 + count C 7 = 3 := by
      unfold totalCounts at htot
      simp [Finset.sum_insert] at htot
      omega
    rcases h3o with ⟨a, ha⟩
    rcases h6o with ⟨b, hb⟩
    have h3 : count C 3 = 1 := by omega
    have h6 : count C 6 = 1 := by omega
    have htypes : ∀ t : Fin 3, colVal (C t) = 1 ∨ colVal (C t) = 3 ∨ colVal (C t) = 6 := by
      intro t
      have htot136 : totalCounts C ({1, 3, 6} : Finset ℕ) = 3 := by
        unfold totalCounts
        simp [Finset.sum_insert]
        omega
      simpa [Finset.mem_insert, Finset.mem_singleton] using
        (colVal_mem_of_totalCounts C ({1, 3, 6} : Finset ℕ) htot136 t)
    rcases exists_col_of_colVal C 1 (by rw [h1]) with ⟨t1, ht1⟩
    rcases exists_col_of_colVal C 3 (by rw [h3]) with ⟨t3, ht3⟩
    rcases exists_col_of_colVal C 6 (by rw [h6]) with ⟨t6, ht6⟩
    have huniq1 : ∀ u : Fin 3, colVal (C u) = 1 → u = t1 := colVal_unique_of_count_one (C := C) t1 ht1 h1
    have huniq3 : ∀ u : Fin 3, colVal (C u) = 3 → u = t3 := colVal_unique_of_count_one (C := C) t3 ht3 h3
    have huniq6 : ∀ u : Fin 3, colVal (C u) = 6 → u = t6 := colVal_unique_of_count_one (C := C) t6 ht6 h6
    have htri : ∀ t : Fin 3, t = t1 ∨ t = t3 ∨ t = t6 := by
      intro t
      rcases htypes t with hv1 | hv3 | hv6
      · left; exact huniq1 t hv1
      · right; left; exact huniq3 t hv3
      · right; right; exact huniq6 t hv6
    let posOf : ℕ → Fin 3 := fun i => if i = 1 then ⟨0, by decide⟩ else if i = 3 then ⟨1, by decide⟩ else ⟨2, by decide⟩
    let toFun : Fin 3 → Fin 3 := fun t => posOf (colVal (C t))
    let invFun : Fin 3 → Fin 3 := fun j => if j.val = 0 then t1 else if j.val = 1 then t3 else t6
    let p : Fin 3 ≃ Fin 3 :=
      { toFun := toFun
        invFun := invFun
        left_inv := by
          intro t
          rcases htri t with ht1c | ht3c | ht6c
          · subst t; simp [toFun, invFun, posOf, ht1]
          · subst t; simp [toFun, invFun, posOf, ht3]
          · subst t; simp [toFun, invFun, posOf, ht6]
        right_inv := by
          intro j
          fin_cases j
          · simp [toFun, invFun, posOf, ht1]
          · simp [toFun, invFun, posOf, ht3]
          · simp [toFun, invFun, posOf, ht6] }
    have heq : Equivalent C code136 := by
      refine ⟨Equiv.refl (Fin 4), p, fun _ => false, ?_⟩
      intro t
      rcases htri t with ht1c | ht3c | ht6c
      · subst t
        have hp : p t1 = ⟨0, by decide⟩ := by simp [p, toFun, posOf, ht1]
        have hc : C t1 = col1 := (colVal_eq_one_iff_col1 (C t1)).mp ht1
        simp [code136, hp, hc]
        change col1 = col1
        rfl
      · subst t
        have hp : p t3 = ⟨1, by decide⟩ := by simp [p, toFun, posOf, ht3]
        have hc : C t3 = col3 := (colVal_eq_three_iff_col3 (C t3)).mp ht3
        simp [code136, hp, hc]
        change col3 = col3
        rfl
      · subst t
        have hp : p t6 = ⟨2, by decide⟩ := by simp [p, toFun, posOf, ht6]
        have hc : C t6 = col6 := (colVal_eq_six_iff_col6 (C t6)).mp ht6
        simp [code136, hp, hc]
        change col6 = col6
        rfl
    exact Or.inr heq

/-- A C0-form `(3,4)` code is equivalent to C_A: its three columns have types
0, 5, 6, and swapping rows 1,3 turns the type-6 column into a type-3 column
(C_A = (3,5,0)). -/
-- native_decide: Contentful · n=3 · checked 2026-08-28
lemma n3_c0form_equiv_CA (C0 : Code 3) (h : C0form C0) : Equivalent C0 CA := by
  rcases n3_c0form_counts h with ⟨h0, h5, h6⟩
  have h5pos : 1 ≤ count C0 5 := by rw [h5]
  have h6pos : 1 ≤ count C0 6 := by rw [h6]
  rcases exists_col_of_colVal C0 0 (by rw [h0]) with ⟨t0, ht0⟩
  rcases exists_col_of_colVal C0 5 h5pos with ⟨t5, ht5⟩
  rcases exists_col_of_colVal C0 6 h6pos with ⟨t6, ht6⟩
  have hc0 : C0 t0 = col0 := (colVal_eq_zero_iff_col0 (C0 t0)).mp ht0
  have hc5 : C0 t5 = col5 := (colVal_eq_five_iff_col5 (C0 t5)).mp ht5
  have hc6 : C0 t6 = col6 := (colVal_eq_six_iff_col6 (C0 t6)).mp ht6
  have huniq0 : ∀ u : Fin 3, C0 u = col0 → u = t0 := col_of_count_one (C := C0) t0 hc0 h0
  have huniq5 : ∀ u : Fin 3, C0 u = col5 → u = t5 := by
    intro u hu
    by_contra hne
    have hcv : colVal (C0 u) = 5 := by rw [hu]; native_decide
    have hu' : u ∈ (Finset.univ.filter fun v : Fin 3 => colVal (C0 v) = 5) := by
      rw [Finset.mem_filter]; exact ⟨Finset.mem_univ u, hcv⟩
    have ht5' : t5 ∈ (Finset.univ.filter fun v : Fin 3 => colVal (C0 v) = 5) := by
      rw [Finset.mem_filter]; exact ⟨Finset.mem_univ t5, ht5⟩
    have hsub : ({u, t5} : Finset (Fin 3)) ⊆
        (Finset.univ.filter fun v : Fin 3 => colVal (C0 v) = 5) := by
      intro v hv
      simp at hv
      rcases hv with hv | hv
      · subst v; exact hu'
      · subst v; exact ht5'
    have hcard2 : 2 ≤ ({u, t5} : Finset (Fin 3)).card := by
      rw [Finset.card_insert_of_notMem]
      · simp
      · intro hmem; exact hne (by simpa using hmem)
    have hc : 2 ≤ count C0 5 := by
      simpa [count_eq_card] using le_trans hcard2 (Finset.card_le_card hsub)
    omega
  have huniq6 : ∀ u : Fin 3, C0 u = col6 → u = t6 := by
    intro u hu
    by_contra hne
    have hcv : colVal (C0 u) = 6 := by rw [hu]; native_decide
    have hu' : u ∈ (Finset.univ.filter fun v : Fin 3 => colVal (C0 v) = 6) := by
      rw [Finset.mem_filter]; exact ⟨Finset.mem_univ u, hcv⟩
    have ht6' : t6 ∈ (Finset.univ.filter fun v : Fin 3 => colVal (C0 v) = 6) := by
      rw [Finset.mem_filter]; exact ⟨Finset.mem_univ t6, ht6⟩
    have hsub : ({u, t6} : Finset (Fin 3)) ⊆
        (Finset.univ.filter fun v : Fin 3 => colVal (C0 v) = 6) := by
      intro v hv
      simp at hv
      rcases hv with hv | hv
      · subst v; exact hu'
      · subst v; exact ht6'
    have hcard2 : 2 ≤ ({u, t6} : Finset (Fin 3)).card := by
      rw [Finset.card_insert_of_notMem]
      · simp
      · intro hmem; exact hne (by simpa using hmem)
    have hc : 2 ≤ count C0 6 := by
      simpa [count_eq_card] using le_trans hcard2 (Finset.card_le_card hsub)
    omega
  have htri : ∀ t : Fin 3, t = t0 ∨ t = t5 ∨ t = t6 := by
    intro t
    rcases n3_c0form_types h t with hv0 | hv5 | hv6
    · left; exact huniq0 t ((colVal_eq_zero_iff_col0 (C0 t)).mp hv0)
    · right; left; exact huniq5 t ((colVal_eq_five_iff_col5 (C0 t)).mp hv5)
    · right; right; exact huniq6 t ((colVal_eq_six_iff_col6 (C0 t)).mp hv6)
  have htne05 : t0 ≠ t5 := by
    intro heq
    have hv : colVal (C0 t0) = 5 := by rw [heq]; exact ht5
    norm_num [ht0] at hv
  have htne06 : t0 ≠ t6 := by
    intro heq
    have hv : colVal (C0 t0) = 6 := by rw [heq]; exact ht6
    norm_num [ht0] at hv
  have htne56 : t5 ≠ t6 := by
    intro heq
    have hv : colVal (C0 t5) = 6 := by rw [heq]; exact ht6
    norm_num [ht5] at hv
  let posOf : ℕ → Fin 3 := fun i => if i = 0 then ⟨2, by decide⟩ else if i = 5 then ⟨1, by decide⟩ else ⟨0, by decide⟩
  let toFun : Fin 3 → Fin 3 := fun t => posOf (colVal (C0 t))
  let invFun : Fin 3 → Fin 3 := fun j => if j.val = 2 then t0 else if j.val = 1 then t5 else t6
  let p : Fin 3 ≃ Fin 3 :=
    { toFun := toFun
      invFun := invFun
      left_inv := by
        intro t
        rcases htri t with ht0c | ht5c | ht6c
        · subst t; simp [toFun, invFun, posOf, ht0]
        · subst t; simp [toFun, invFun, posOf, ht5]
        · subst t; simp [toFun, invFun, posOf, ht6]
      right_inv := by
        intro j
        fin_cases j
        · simp [toFun, invFun, posOf, ht6]
        · simp [toFun, invFun, posOf, ht5]
        · simp [toFun, invFun, posOf, ht0] }
  refine ⟨Equiv.swap (1 : Fin 4) (3 : Fin 4), p, fun _ => false, ?_⟩
  intro t
  rcases htri t with ht0c | ht5c | ht6c
  · subst t
    have hp : p t0 = ⟨2, by decide⟩ := by simp [p, toFun, posOf, ht0]
    simp [CA, hp, hc0]
    native_decide
  · subst t
    have hp : p t5 = ⟨1, by decide⟩ := by simp [p, toFun, posOf, ht5]
    simp [CA, hp, hc5]
    native_decide
  · subst t
    have hp : p t6 = ⟨0, by decide⟩ := by simp [p, toFun, posOf, ht6]
    simp [CA, hp, hc6]
    native_decide

/-- An optimal `(3,4)` code with a type-0 column is equivalent to C_A (the
C0-form case of `thm:0column` (Theorem 6)), or is contradicted by `zero_column_strict`. -/
-- native_decide: Contentful · n=3 · checked 2026-08-28
lemma n3_opt_col0 {C : Code 3} (hopt : ∀ D : Code 3, UniversalBetter C D)
    (t : Fin 3) (ht0 : C t = col0) :
    ∃ C' : Code 3, Equivalent C C' ∧ InOptimal3 C' := by
  by_cases hc0 : ∃ C0 : Code 3, Equivalent C C0 ∧
      count C0 0 + count C0 5 + count C0 6 = 3 ∧ Odd (count C0 5) ∧ Odd (count C0 6)
  · rcases hc0 with ⟨C0, hEq, hcnt, h5o, h6o⟩
    have hc0f : C0form C0 := ⟨hcnt, h5o, h6o⟩
    have hCA : Equivalent C0 CA := n3_c0form_equiv_CA C0 hc0f
    exact ⟨CA, equivalent_trans hEq hCA, by simp [InOptimal3]⟩
  · have h0pos : 1 ≤ count C 0 := by
      have hcv : colVal (C t) = 0 := by rw [ht0]; native_decide
      exact count_pos_of_colVal C t hcv
    rcases zero_column_strict C h0pos hc0 with ⟨t', ht'0, s', hs', hstrict⟩
    rcases hstrict (1 / 4 : ℝ) (by norm_num) (by norm_num) with hgt
    have hge := (hopt (replaceColumn C t' s')) (1 / 4 : ℝ) (by norm_num) (by norm_num)
    exfalso
    linarith

/-- An optimal `(3,4)` code with a type-0 or type-15 column is equivalent to
one of the five codes of `thm:n8` (Theorem 5) (the type-15 case flips the column to
type 0, an equivalence, and reduces to `n3_opt_col0`). -/
-- native_decide: Contentful · n=3 · checked 2026-08-28
lemma n3_opt_has_0_or_15 {C : Code 3} (hopt : ∀ D : Code 3, UniversalBetter C D)
    (h : ∃ t : Fin 3, C t = col0 ∨ C t = col15) :
    ∃ C' : Code 3, Equivalent C C' ∧ InOptimal3 C' := by
  rcases h with ⟨t, ht⟩
  rcases ht with ht0 | ht15
  · exact n3_opt_col0 (C := C) hopt t ht0
  · let Ct : Code 3 := replaceColumn C t col0
    have hflip : Ct t = col0 := by simp [Ct, replaceColumn]
    have hfc : flipCol (C t) = col0 := by rw [ht15]; native_decide
    have h1 : Equivalent C (replaceColumn C t (flipCol (C t))) := equivalent_replace_flip C t
    have hcodes : replaceColumn C t (flipCol (C t)) = Ct := by
      ext u
      by_cases hu : u = t <;> simp [Ct, replaceColumn, hu, hfc]
    have hEq : Equivalent C Ct := by
      rw [hcodes] at h1
      exact h1
    have hoptC : ∀ D : Code 3, UniversalBetter Ct D := by
      intro D ε hε0 hε1
      have hl : lambda C ε = lambda Ct ε := (lambda_equiv C Ct hEq ε).symm
      exact le_trans (hopt D ε hε0 hε1) (le_of_eq hl)
    rcases n3_opt_col0 (C := Ct) hoptC t hflip with ⟨C', hEqC, hIn⟩
    exact ⟨C', equivalent_trans hEq hEqC, hIn⟩

/-! ## n = 3: Class-I and Class-II codes are not optimal

The four representatives of Class-I `(3,4)` codes up to equivalence are
(1,3,3), (1,5,5), (1,6,6) (the |1|=1 variants) and (1,1,1); each has a
strictly better code: `C(1,2,0)` = (3,5,5) dCode-dominates the (1,X,X)
variants, and (1,1,3) row-dominates (1,1,1).  Class-II codes equal some
Class-I code (`thm:class2` (Lemma 14)), hence are not optimal either.
-/

/-- General strictness: dCode-wise domination plus a strict point gives
λ_{C'} > λ_C universally. -/
lemma universalStrictBetter_of_dCode_le_lt {n : ℕ} (C C' : Code n)
    (hle : ∀ y : Word n, dCode C' y ≤ dCode C y)
    (hlt : ∃ y : Word n, dCode C' y < dCode C y) :
    UniversalStrictBetter C' C := by
  intro ε hε0 hε1
  have hwle : ∀ y : Word n, weight n ε (dCode C y) ≤ weight n ε (dCode C' y) := by
    intro y
    rcases lt_or_eq_of_le (hle y) with hlt' | heq
    · exact le_of_lt (weight_strictAnti hε0 hε1 hlt')
    · rw [heq]
  have hsum : (∑ y : Word n, weight n ε (dCode C y)) < ∑ y : Word n, weight n ε (dCode C' y) := by
    refine Finset.sum_lt_sum (fun y _ => hwle y) ?_
    rcases hlt with ⟨y, hy⟩
    exact ⟨y, Finset.mem_univ y, weight_strictAnti hε0 hε1 hy⟩
  unfold lambda
  change (1 / 4 : ℝ) * (∑ y : Word n, weight n ε (dCode C' y)) >
    (1 / 4 : ℝ) * (∑ y : Word n, weight n ε (dCode C y))
  have hquarter : 0 < (1 / 4 : ℝ) := by norm_num
  nlinarith [mul_lt_mul_of_pos_left hsum hquarter]

/-- The fiber of type i has exactly tu, tv when |i| = 2. -/
lemma colVal_fiber_eq_two {n : ℕ} {C : Code n} {i : ℕ} (tu tv : Fin n)
    (htu : colVal (C tu) = i) (htv : colVal (C tv) = i) (htne : tu ≠ tv)
    (h2 : count C i = 2) :
    ∀ u : Fin n, colVal (C u) = i → u = tu ∨ u = tv := by
  intro u hu
  by_contra hnot
  have hne1 : u ≠ tu := fun h => hnot (Or.inl h)
  have hne2 : u ≠ tv := fun h => hnot (Or.inr h)
  have hu' : u ∈ (Finset.univ.filter fun v : Fin n => colVal (C v) = i) := by
    rw [Finset.mem_filter]; exact ⟨Finset.mem_univ u, hu⟩
  have htu' : tu ∈ (Finset.univ.filter fun v : Fin n => colVal (C v) = i) := by
    rw [Finset.mem_filter]; exact ⟨Finset.mem_univ tu, htu⟩
  have htv' : tv ∈ (Finset.univ.filter fun v : Fin n => colVal (C v) = i) := by
    rw [Finset.mem_filter]; exact ⟨Finset.mem_univ tv, htv⟩
  have hsub : ({u, tu, tv} : Finset (Fin n)) ⊆
      (Finset.univ.filter fun v : Fin n => colVal (C v) = i) := by
    intro v hv
    simp at hv
    rcases hv with hv | hv | hv
    · subst v; exact hu'
    · subst v; exact htu'
    · subst v; exact htv'
  have hcard3 : 3 ≤ ({u, tu, tv} : Finset (Fin n)).card := by
    have hu_not : u ∉ ({tu, tv} : Finset (Fin n)) := by
      intro hmem
      simp at hmem
      rcases hmem with hmem | hmem
      · exact hne1 hmem
      · exact hne2 hmem
    have h1 : ({u, tu, tv} : Finset (Fin n)).card = ({tu, tv} : Finset (Fin n)).card + 1 := by
      rw [Finset.card_insert_of_notMem hu_not]
    have h2' : ({tu, tv} : Finset (Fin n)).card = 2 := by
      rw [Finset.card_insert_of_notMem (by intro hmem; exact htne (by simpa using hmem))]
      simp
    rw [h1, h2']
  have hc : 3 ≤ count C i := by
    simpa [count_eq_card] using le_trans hcard3 (Finset.card_le_card hsub)
  omega

/-- The code (1, X, X). -/
def code1xx (colX : Column) : Code 3 := fun t => if t.val = 0 then col1 else colX

/-- The code (1,3,3). -/
def code133 : Code 3 := code1xx col3

/-- The code (1,5,5). -/
def code155 : Code 3 := code1xx col5

/-- The code (1,6,6). -/
def code166 : Code 3 := code1xx col6

/-- The code (1,1,1). -/
def code111 : Code 3 := fun _ => col1

/-- The code (1,1,3). -/
def code113 : Code 3 := fun t => if t.val ≤ 1 then col1 else col3

-- native_decide: Contentful · n=3 · checked 2026-08-28
/-- `C(1,2,0)` = (3,5,5) strictly dominates the (1,3,3) variant. -/
lemma n3_strict_133 : UniversalStrictBetter (linearCode 1 2 0) code133 :=
  universalStrictBetter_of_dCode_le_lt code133 (linearCode 1 2 0) (by native_decide) (by native_decide)

-- native_decide: Contentful · n=3 · checked 2026-08-28
/-- `C(1,2,0)` strictly dominates the (1,5,5) variant. -/
lemma n3_strict_155 : UniversalStrictBetter (linearCode 1 2 0) code155 :=
  universalStrictBetter_of_dCode_le_lt code155 (linearCode 1 2 0) (by native_decide) (by native_decide)

-- native_decide: Contentful · n=3 · checked 2026-08-28
/-- `C(1,2,0)` strictly dominates the (1,6,6) variant. -/
lemma n3_strict_166 : UniversalStrictBetter (linearCode 1 2 0) code166 :=
  universalStrictBetter_of_dCode_le_lt code166 (linearCode 1 2 0) (by native_decide) (by native_decide)

-- native_decide: Contentful · n=3 · checked 2026-08-28
/-- (1,1,3) strictly dominates (1,1,1) (row-superset with a new row). -/
lemma n3_strict_111 : UniversalStrictBetter code113 code111 := by
  have hsup : ∀ j : Fin 4, ∃ j' : Fin 4, row code111 j = row code113 j' := by
    intro j
    fin_cases j
    · exact ⟨0, by native_decide⟩
    · exact ⟨1, by native_decide⟩
    · exact ⟨0, by native_decide⟩
    · exact ⟨3, by native_decide⟩
  have hnew : ∃ j' : Fin 4, ∀ j : Fin 4, row code111 j ≠ row code113 j' := by
    refine ⟨2, ?_⟩
    intro j
    fin_cases j <;> native_decide
  exact universalStrictBetter_of_rows_subset code111 code113 hsup hnew

/-- A code with one type-1 column and two type-X columns is a column
permutation of the canonical (1,X,X) code. -/
lemma equiv_code1xx (C : Code 3) (colX : Column) (t1 tu tv : Fin 3)
    (hC1 : C t1 = col1) (hCu : C tu = colX) (hCv : C tv = colX)
    (hall : ∀ t : Fin 3, C t = col1 ∨ C t = colX)
    (huniq1 : ∀ u : Fin 3, C u = col1 → u = t1)
    (huniqX : ∀ u : Fin 3, C u = colX → u = tu ∨ u = tv)
    (ht1u : t1 ≠ tu) (ht1v : t1 ≠ tv) (htuv : tu ≠ tv) :
    Equivalent C (code1xx colX) := by
  have htri : ∀ t : Fin 3, t = t1 ∨ t = tu ∨ t = tv := by
    intro t
    rcases hall t with hv1 | hvX
    · left; exact huniq1 t hv1
    · rcases huniqX t hvX with htu | htv
      · right; left; exact htu
      · right; right; exact htv
  let toFun : Fin 3 → Fin 3 := fun t => if t = t1 then ⟨0, by decide⟩ else if t = tu then ⟨1, by decide⟩ else ⟨2, by decide⟩
  let invFun : Fin 3 → Fin 3 := fun j => if j.val = 0 then t1 else if j.val = 1 then tu else tv
  let p : Fin 3 ≃ Fin 3 :=
    { toFun := toFun
      invFun := invFun
      left_inv := by
        intro t
        rcases htri t with ht1c | htuc | htvc
        · subst t; simp [toFun, invFun]
        · subst t; simp [toFun, invFun, ht1u.symm]
        · subst t; simp [toFun, invFun, ht1v.symm, htuv.symm]
      right_inv := by
        intro j
        fin_cases j
        · simp [toFun, invFun]
        · simp [toFun, invFun, ht1u.symm]
        · simp [toFun, invFun, ht1v.symm, htuv.symm] }
  refine ⟨Equiv.refl (Fin 4), p, fun _ => false, ?_⟩
  intro t
  rcases htri t with ht1c | htuc | htvc
  · subst t
    have hp : p t1 = ⟨0, by decide⟩ := by simp [p, toFun]
    simp [code1xx, hp, hC1]
    change col1 = col1
    rfl
  · subst t
    have hp : p tu = ⟨1, by decide⟩ := by simp [p, toFun, ht1u.symm]
    simp [code1xx, hp, hCu]
    change colX = colX
    rfl
  · subst t
    have hp : p tv = ⟨2, by decide⟩ := by simp [p, toFun, ht1v.symm, htuv.symm]
    simp [code1xx, hp, hCv]
    change colX = colX
    rfl

/-- A code with |1| = 1, |X| = 2 and all columns of types 1 or X is
equivalent to (1,X,X). -/
-- native_decide: Contentful · n=3 · checked 2026-08-28
lemma equiv_1xx_of_counts (C : Code 3) (colX : Column) (i : ℕ)
    (hci : ∀ c : Column, colVal c = i → c = colX)
    (hcolX : colVal colX = i) (hne_i_1 : i ≠ 1)
    (h1 : count C 1 = 1) (hX : count C i = 2)
    (htypes : ∀ t : Fin 3, colVal (C t) = 1 ∨ colVal (C t) = i) :
    Equivalent C (code1xx colX) := by
  have h1pos : 1 ≤ count C 1 := by rw [h1]
  have hXpos : 1 ≤ count C i := by rw [hX]; omega
  rcases exists_col_of_colVal C 1 h1pos with ⟨t1, ht1⟩
  rcases exists_col_of_colVal C i hXpos with ⟨tu, htu⟩
  have hc1 : C t1 = col1 := (colVal_eq_one_iff_col1 (C t1)).mp ht1
  have hcu : C tu = colX := hci (C tu) htu
  have hcardf : (Finset.univ.filter fun t : Fin 3 => colVal (C t) = i).card = 2 := by
    simpa [count_eq_card] using hX
  have htu' : tu ∈ (Finset.univ.filter fun t : Fin 3 => colVal (C t) = i) := by
    rw [Finset.mem_filter]; exact ⟨Finset.mem_univ tu, htu⟩
  have hrest : ((Finset.univ.filter fun t : Fin 3 => colVal (C t) = i).erase tu).card = 1 := by
    rw [Finset.card_erase_of_mem htu']
    omega
  have hpos : 0 < ((Finset.univ.filter fun t : Fin 3 => colVal (C t) = i).erase tu).card := by
    rw [hrest]; norm_num
  rcases Finset.card_pos.mp hpos with ⟨tv, htvm⟩
  have htv' : tv ∈ (Finset.univ.filter fun t : Fin 3 => colVal (C t) = i) := (Finset.mem_erase.mp htvm).2
  have htuv : tv ≠ tu := (Finset.mem_erase.mp htvm).1
  have htv : colVal (C tv) = i := (Finset.mem_filter.mp htv').2
  have hcv : C tv = colX := hci (C tv) htv
  have huniq1 : ∀ u : Fin 3, C u = col1 → u = t1 := by
    intro u hu
    have hcvu : colVal (C u) = 1 := by rw [hu]; native_decide
    exact colVal_unique_of_count_one (C := C) t1 ht1 h1 u hcvu
  have huniqX : ∀ u : Fin 3, C u = colX → u = tu ∨ u = tv := by
    intro u hu
    have hcvu : colVal (C u) = i := by rw [hu, hcolX]
    exact colVal_fiber_eq_two (C := C) tu tv htu htv htuv.symm hX u hcvu
  have hall : ∀ t : Fin 3, C t = col1 ∨ C t = colX := by
    intro t
    rcases htypes t with hv1 | hvi
    · left; exact (colVal_eq_one_iff_col1 (C t)).mp hv1
    · right; exact hci (C t) hvi
  have ht1u : t1 ≠ tu := by
    intro heq
    have hvi : colVal (C t1) = i := by rw [heq]; exact htu
    exact hne_i_1 (hvi.symm.trans ht1)
  have ht1v : t1 ≠ tv := by
    intro heq
    have hvi : colVal (C t1) = i := by rw [heq]; exact htv
    exact hne_i_1 (hvi.symm.trans ht1)
  exact equiv_code1xx C colX t1 tu tv hc1 hcu hcv hall huniq1 huniqX ht1u ht1v htuv.symm

/-- Class-I with |1|=1, |3|=2 has columns only of types 1 and 3. -/
lemma n3_class1_types_133 (C : Code 3) (h : ClassI C) (h1 : count C 1 = 1) (h3 : count C 3 = 2) :
    ∀ t : Fin 3, colVal (C t) = 1 ∨ colVal (C t) = 3 := by
  have hsum : count C 1 + count C 3 + count C 5 + count C 6 = 3 := by
    rcases h with ⟨hodd1, hpar, htot⟩
    unfold totalCounts at htot
    simp [Finset.sum_insert] at htot
    omega
  intro t
  have htot13 : totalCounts C ({1, 3} : Finset ℕ) = 3 := by
    unfold totalCounts
    simp [Finset.sum_insert]
    omega
  simpa [Finset.mem_insert, Finset.mem_singleton] using
    (colVal_mem_of_totalCounts C ({1, 3} : Finset ℕ) htot13 t)

/-- Class-I with |1|=1, |5|=2 has columns only of types 1 and 5. -/
lemma n3_class1_types_155 (C : Code 3) (h : ClassI C) (h1 : count C 1 = 1) (h5 : count C 5 = 2) :
    ∀ t : Fin 3, colVal (C t) = 1 ∨ colVal (C t) = 5 := by
  have hsum : count C 1 + count C 3 + count C 5 + count C 6 = 3 := by
    rcases h with ⟨hodd1, hpar, htot⟩
    unfold totalCounts at htot
    simp [Finset.sum_insert] at htot
    omega
  intro t
  have htot15 : totalCounts C ({1, 5} : Finset ℕ) = 3 := by
    unfold totalCounts
    simp [Finset.sum_insert]
    omega
  simpa [Finset.mem_insert, Finset.mem_singleton] using
    (colVal_mem_of_totalCounts C ({1, 5} : Finset ℕ) htot15 t)

/-- Class-I with |1|=1, |6|=2 has columns only of types 1 and 6. -/
lemma n3_class1_types_166 (C : Code 3) (h : ClassI C) (h1 : count C 1 = 1) (h6 : count C 6 = 2) :
    ∀ t : Fin 3, colVal (C t) = 1 ∨ colVal (C t) = 6 := by
  have hsum : count C 1 + count C 3 + count C 5 + count C 6 = 3 := by
    rcases h with ⟨hodd1, hpar, htot⟩
    unfold totalCounts at htot
    simp [Finset.sum_insert] at htot
    omega
  intro t
  have htot16 : totalCounts C ({1, 6} : Finset ℕ) = 3 := by
    unfold totalCounts
    simp [Finset.sum_insert]
    omega
  simpa [Finset.mem_insert, Finset.mem_singleton] using
    (colVal_mem_of_totalCounts C ({1, 6} : Finset ℕ) htot16 t)

-- native_decide: Contentful · n=3 · checked 2026-08-28
/-- The |3| = 2 variant of Class-I is equivalent to (1,3,3). -/
lemma n3_class1_equiv_133 (C : Code 3) (h : ClassI C) (h1 : count C 1 = 1) (h3 : count C 3 = 2) :
    Equivalent C code133 :=
  equiv_1xx_of_counts C col3 3 (fun c hc => (colVal_eq_three_iff_col3 c).mp hc) (by native_decide) (by norm_num) h1 h3 (n3_class1_types_133 C h h1 h3)

-- native_decide: Contentful · n=3 · checked 2026-08-28
/-- The |5| = 2 variant of Class-I is equivalent to (1,5,5). -/
lemma n3_class1_equiv_155 (C : Code 3) (h : ClassI C) (h1 : count C 1 = 1) (h5 : count C 5 = 2) :
    Equivalent C code155 :=
  equiv_1xx_of_counts C col5 5 (fun c hc => (colVal_eq_five_iff_col5 c).mp hc) (by native_decide) (by norm_num) h1 h5 (n3_class1_types_155 C h h1 h5)

-- native_decide: Contentful · n=3 · checked 2026-08-28
/-- The |6| = 2 variant of Class-I is equivalent to (1,6,6). -/
lemma n3_class1_equiv_166 (C : Code 3) (h : ClassI C) (h1 : count C 1 = 1) (h6 : count C 6 = 2) :
    Equivalent C code166 :=
  equiv_1xx_of_counts C col6 6 (fun c hc => (colVal_eq_six_iff_col6 c).mp hc) (by native_decide) (by norm_num) h1 h6 (n3_class1_types_166 C h h1 h6)

/-- The |1| = 3 Class-I code is (1,1,1) itself. -/
lemma n3_class1_equiv_111 (C : Code 3) (_h : ClassI C) (h1 : count C 1 = 3) :
    Equivalent C code111 := by
  have hall1 : ∀ t : Fin 3, C t = col1 := by
    intro t
    have htot1 : totalCounts C ({1} : Finset ℕ) = 3 := by
      unfold totalCounts
      simp
      omega
    have hm := colVal_mem_of_totalCounts C ({1} : Finset ℕ) htot1 t
    exact (colVal_eq_one_iff_col1 (C t)).mp (by simpa [Finset.mem_singleton] using hm)
  have heq : C = code111 := by
    ext t
    simp [code111, hall1 t]
  rw [heq]
  exact equivalent_refl code111

/-- Class-I `(3,4)` codes are not optimal: each equivalence class has a
strictly better code (`thm:11` (Theorem 16)/`thm:301` (Theorem 17) chain, with dCode-wise and
row-superset witnesses computed for the four representatives). -/
lemma n3_class1_not_optimal {C : Code 3} (h : ClassI C)
    (hopt : ∀ D : Code 3, UniversalBetter C D) : False := by
  have hodd1 : Odd (count C 1) := h.1
  have hpar := h.2.1
  have htot := h.2.2
  have hsum : count C 1 + count C 3 + count C 5 + count C 6 = 3 := by
    unfold totalCounts at htot
    simp [Finset.sum_insert] at htot
    omega
  rcases hodd1 with ⟨a, ha⟩
  have h1cases : count C 1 = 1 ∨ count C 1 = 3 := by omega
  rcases h1cases with h1 | h1
  · rcases hpar with hE | hO
    · rcases hE with ⟨h3e, h5e, h6e⟩
      have hcases : count C 3 = 2 ∨ count C 5 = 2 ∨ count C 6 = 2 := by
        rcases h3e with ⟨a, ha3⟩
        rcases h5e with ⟨b, hb5⟩
        rcases h6e with ⟨c, hc6⟩
        omega
      rcases hcases with h3 | h5 | h6
      · have heq := n3_class1_equiv_133 C h h1 h3
        have hl : lambda C (1 / 4 : ℝ) = lambda code133 (1 / 4 : ℝ) :=
          (lambda_equiv C code133 heq (1 / 4 : ℝ)).symm
        have hstrict : lambda (linearCode 1 2 0) (1 / 4 : ℝ) > lambda code133 (1 / 4 : ℝ) :=
          n3_strict_133 (1 / 4 : ℝ) (by norm_num) (by norm_num)
        have hge : lambda C (1 / 4 : ℝ) ≥ lambda (linearCode 1 2 0) (1 / 4 : ℝ) :=
          hopt (linearCode 1 2 0) (1 / 4 : ℝ) (by norm_num) (by norm_num)
        rw [hl] at hge
        linarith
      · have heq := n3_class1_equiv_155 C h h1 h5
        have hl : lambda C (1 / 4 : ℝ) = lambda code155 (1 / 4 : ℝ) :=
          (lambda_equiv C code155 heq (1 / 4 : ℝ)).symm
        have hstrict : lambda (linearCode 1 2 0) (1 / 4 : ℝ) > lambda code155 (1 / 4 : ℝ) :=
          n3_strict_155 (1 / 4 : ℝ) (by norm_num) (by norm_num)
        have hge : lambda C (1 / 4 : ℝ) ≥ lambda (linearCode 1 2 0) (1 / 4 : ℝ) :=
          hopt (linearCode 1 2 0) (1 / 4 : ℝ) (by norm_num) (by norm_num)
        rw [hl] at hge
        linarith
      · have heq := n3_class1_equiv_166 C h h1 h6
        have hl : lambda C (1 / 4 : ℝ) = lambda code166 (1 / 4 : ℝ) :=
          (lambda_equiv C code166 heq (1 / 4 : ℝ)).symm
        have hstrict : lambda (linearCode 1 2 0) (1 / 4 : ℝ) > lambda code166 (1 / 4 : ℝ) :=
          n3_strict_166 (1 / 4 : ℝ) (by norm_num) (by norm_num)
        have hge : lambda C (1 / 4 : ℝ) ≥ lambda (linearCode 1 2 0) (1 / 4 : ℝ) :=
          hopt (linearCode 1 2 0) (1 / 4 : ℝ) (by norm_num) (by norm_num)
        rw [hl] at hge
        linarith
    · rcases hO with ⟨h3o, h5o, h6o⟩
      rcases h3o with ⟨a, ha3⟩
      rcases h5o with ⟨b, hb5⟩
      rcases h6o with ⟨c, hc6⟩
      exfalso
      omega
  · have heq := n3_class1_equiv_111 C h h1
    have hl : lambda C (1 / 4 : ℝ) = lambda code111 (1 / 4 : ℝ) :=
      (lambda_equiv C code111 heq (1 / 4 : ℝ)).symm
    have hstrict : lambda code113 (1 / 4 : ℝ) > lambda code111 (1 / 4 : ℝ) :=
      n3_strict_111 (1 / 4 : ℝ) (by norm_num) (by norm_num)
    have hge : lambda C (1 / 4 : ℝ) ≥ lambda code113 (1 / 4 : ℝ) :=
      hopt code113 (1 / 4 : ℝ) (by norm_num) (by norm_num)
    rw [hl] at hge
    linarith

/-- Class-II `(3,4)` codes are not optimal: they equal a Class-I code
(`thm:class2` (Lemma 14)), which is not optimal. -/
lemma n3_class2_not_optimal {C : Code 3} (h : ClassII C)
    (hopt : ∀ D : Code 3, UniversalBetter C D) : False := by
  rcases class2_to_class1 C h with ⟨C', hclass1, heq, hcnt⟩
  have hopt' : ∀ D : Code 3, UniversalBetter C' D := by
    intro D ε hε0 hε1
    have h1 : lambda C' ε = lambda C ε := heq ε hε0 hε1
    exact le_trans (hopt D ε hε0 hε1) (le_of_eq h1.symm)
  exact n3_class1_not_optimal (C := C') hclass1 hopt'

/-! ## n = 3: Case A and the Case-B row-swap reduction

Case A: a code with all columns of types 3, 5, 6 is linear (`IsLinear`, then
`linear3_classified` puts it among C_A, C(1,1,1), C(1,2,0) — all in the
five-code list) or is strictly dominated by a linear code
(`degenerate_to_linear_strict`).  Case B (exactly one of |1|,|2|,|4|,|7|
positive, columns in {1..7}) is reduced to the |1| > 0, |2|=|4|=|7|=0 case by
row swaps: swap rows 2,3 maps type 2 to 1; swap rows 1,3 maps type 4 to 1;
swap rows 0,3 maps type 7 to 14 and `flipHighColumns` flips it to 1.
-/

/-- Case A: columns only of types 3, 5, 6 — linear (hence one of the
`thm:n8` (Theorem 5) five codes up to equivalence) or a strictly better linear code
contradicts optimality. -/
lemma n3_columns356 (C : Code 3)
    (hcols : ∀ t : Fin 3, colVal (C t) = 3 ∨ colVal (C t) = 5 ∨ colVal (C t) = 6)
    (hopt : ∀ D : Code 3, UniversalBetter C D) :
    ∃ C' : Code 3, Equivalent C C' ∧ InOptimal3 C' := by
  by_cases hlin : IsLinear C
  · rcases linear3_classified C hlin with hCA | h111 | h120
    · exact ⟨CA, equivalent_symm hCA, by simp [InOptimal3]⟩
    · exact ⟨linearCode 1 1 1, equivalent_symm h111, by simp [InOptimal3]⟩
    · exact ⟨linearCode 1 2 0, equivalent_symm h120, by simp [InOptimal3]⟩
  · have hc1 : count C 1 = 0 := by
      unfold count
      apply Finset.sum_eq_zero
      intro t _
      rcases hcols t with h3 | h5 | h6
      · simp [h3]
      · simp [h5]
      · simp [h6]
    have htot356 : totalCounts C ({3, 5, 6} : Finset ℕ) = 3 := by
      unfold totalCounts count
      rw [Finset.sum_comm]
      calc
        (∑ t : Fin 3, ∑ i ∈ ({3, 5, 6} : Finset ℕ), if colVal (C t) = i then 1 else 0)
            = ∑ t : Fin 3, (1 : ℕ) := by
              apply Finset.sum_congr rfl
              intro t _
              rcases hcols t with h3 | h5 | h6
              · simp [h3]
              · simp [h5]
              · simp [h6]
        _ = 3 := by simp
    have h356 : count C 3 + count C 5 + count C 6 = 3 := by
      unfold totalCounts at htot356
      simp [Finset.sum_insert] at htot356
      omega
    have htot : totalCounts C ({1, 3, 5, 6} : Finset ℕ) = 3 := by
      unfold totalCounts
      simp [Finset.sum_insert, hc1]
      omega
    rcases degenerate_to_linear_strict C (by norm_num : 2 ≤ 3) htot hc1 hlin with ⟨C', hlin', hstrict⟩
    have hgt : lambda C' (1 / 4 : ℝ) > lambda C (1 / 4 : ℝ) :=
      hstrict (1 / 4 : ℝ) (by norm_num) (by norm_num)
    have hge : lambda C (1 / 4 : ℝ) ≥ lambda C' (1 / 4 : ℝ) :=
      hopt C' (1 / 4 : ℝ) (by norm_num) (by norm_num)
    exfalso
    linarith

/-- The 3 columns of a {1..7}-code sum to 3 over types 1..7. -/
lemma n3_columns17_total (C : Code 3)
    (hcols : ∀ t : Fin 3, 1 ≤ colVal (C t) ∧ colVal (C t) ≤ 7) :
    totalCounts C ({1, 2, 3, 4, 5, 6, 7} : Finset ℕ) = 3 := by
  unfold totalCounts count
  rw [Finset.sum_comm]
  calc
    (∑ t : Fin 3, ∑ i ∈ ({1, 2, 3, 4, 5, 6, 7} : Finset ℕ), if colVal (C t) = i then 1 else 0)
        = ∑ t : Fin 3, (1 : ℕ) := by
          apply Finset.sum_congr rfl
          intro u _
          rcases hcols u with ⟨hge, hle⟩
          interval_cases colVal (C u) <;> simp
    _ = 3 := by simp

/-- With |1|=|4|=|7|=0, the columns of a {1..7}-code have types in {2,3,5,6}. -/
lemma n3_caseB_types_236 (C : Code 3)
    (hcols : ∀ t : Fin 3, 1 ≤ colVal (C t) ∧ colVal (C t) ≤ 7)
    (h1 : count C 1 = 0) (h4 : count C 4 = 0) (h7 : count C 7 = 0) (t : Fin 3) :
    colVal (C t) = 2 ∨ colVal (C t) = 3 ∨ colVal (C t) = 5 ∨ colVal (C t) = 6 := by
  have h17 := n3_columns17_total C hcols
  have htot236 : totalCounts C ({2, 3, 5, 6} : Finset ℕ) = 3 := by
    unfold totalCounts
    simp [Finset.sum_insert]
    unfold totalCounts at h17
    simp [Finset.sum_insert] at h17
    omega
  simpa [Finset.mem_insert, Finset.mem_singleton] using
    (colVal_mem_of_totalCounts C ({2, 3, 5, 6} : Finset ℕ) htot236 t)

/-- With |1|=|2|=|7|=0, the columns of a {1..7}-code have types in {3,4,5,6}. -/
lemma n3_caseB_types_346 (C : Code 3)
    (hcols : ∀ t : Fin 3, 1 ≤ colVal (C t) ∧ colVal (C t) ≤ 7)
    (h1 : count C 1 = 0) (h2 : count C 2 = 0) (h7 : count C 7 = 0) (t : Fin 3) :
    colVal (C t) = 3 ∨ colVal (C t) = 4 ∨ colVal (C t) = 5 ∨ colVal (C t) = 6 := by
  have h17 := n3_columns17_total C hcols
  have htot346 : totalCounts C ({3, 4, 5, 6} : Finset ℕ) = 3 := by
    unfold totalCounts
    simp [Finset.sum_insert]
    unfold totalCounts at h17
    simp [Finset.sum_insert] at h17
    omega
  simpa [Finset.mem_insert, Finset.mem_singleton] using
    (colVal_mem_of_totalCounts C ({3, 4, 5, 6} : Finset ℕ) htot346 t)

/-- With |1|=|2|=|4|=0, the columns of a {1..7}-code have types in {3,5,6,7}. -/
lemma n3_caseB_types_3567 (C : Code 3)
    (hcols : ∀ t : Fin 3, 1 ≤ colVal (C t) ∧ colVal (C t) ≤ 7)
    (h1 : count C 1 = 0) (h2 : count C 2 = 0) (h4 : count C 4 = 0) (t : Fin 3) :
    colVal (C t) = 3 ∨ colVal (C t) = 5 ∨ colVal (C t) = 6 ∨ colVal (C t) = 7 := by
  have h17 := n3_columns17_total C hcols
  have htot3567 : totalCounts C ({3, 5, 6, 7} : Finset ℕ) = 3 := by
    unfold totalCounts
    simp [Finset.sum_insert]
    unfold totalCounts at h17
    simp [Finset.sum_insert] at h17
    omega
  simpa [Finset.mem_insert, Finset.mem_singleton] using
    (colVal_mem_of_totalCounts C ({3, 5, 6, 7} : Finset ℕ) htot3567 t)

/-- Case-B reduction for |2| > 0: swapping rows 2,3 maps type 2 to 1, so the
code is equivalent to one with |1| > 0 and columns only in {1,3,5,6}. -/
-- native_decide: Contentful · n=3 · checked 2026-08-28
lemma n3_caseB_col2_reduce (C : Code 3)
    (hcols : ∀ t : Fin 3, 1 ≤ colVal (C t) ∧ colVal (C t) ≤ 7)
    (h2 : 0 < count C 2) (h1 : count C 1 = 0) (h4 : count C 4 = 0) (h7 : count C 7 = 0) :
    ∃ Ct : Code 3, Equivalent C Ct ∧ 0 < count Ct 1 ∧
      (∀ t : Fin 3, colVal (Ct t) = 1 ∨ colVal (Ct t) = 3 ∨ colVal (Ct t) = 5 ∨ colVal (Ct t) = 6) := by
  let Ct : Code 3 := rowPermutedCode rho23 C
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
    rcases n3_caseB_types_236 C hcols h1 h4 h7 t with hv2 | hv3 | hv5 | hv6
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

-- native_decide: Contentful · n=3 · checked 2026-08-28
/-- Case-B reduction for |4| > 0: swapping rows 1,3 maps type 4 to 1. -/
lemma n3_caseB_col4_reduce (C : Code 3)
    (hcols : ∀ t : Fin 3, 1 ≤ colVal (C t) ∧ colVal (C t) ≤ 7)
    (h4 : 0 < count C 4) (h1 : count C 1 = 0) (h2 : count C 2 = 0) (h7 : count C 7 = 0) :
    ∃ Ct : Code 3, Equivalent C Ct ∧ 0 < count Ct 1 ∧
      (∀ t : Fin 3, colVal (Ct t) = 1 ∨ colVal (Ct t) = 3 ∨ colVal (Ct t) = 5 ∨ colVal (Ct t) = 6) := by
  let Ct : Code 3 := rowPermutedCode rho13 C
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
    rcases n3_caseB_types_346 C hcols h1 h2 h7 t with hv3 | hv4 | hv5 | hv6
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

/-- Case-B reduction for |7| > 0: swapping rows 0,3 maps type 7 to 14 and
`flipHighColumns` flips it to 1. -/
-- native_decide: Contentful · n=3 · checked 2026-08-28
lemma n3_caseB_col7_reduce (C : Code 3)
    (hcols : ∀ t : Fin 3, 1 ≤ colVal (C t) ∧ colVal (C t) ≤ 7)
    (h7 : 0 < count C 7) (h1 : count C 1 = 0) (h2 : count C 2 = 0) (h4 : count C 4 = 0) :
    ∃ Ct : Code 3, Equivalent C Ct ∧ 0 < count Ct 1 ∧
      (∀ t : Fin 3, colVal (Ct t) = 1 ∨ colVal (Ct t) = 3 ∨ colVal (Ct t) = 5 ∨ colVal (Ct t) = 6) := by
  let Ct : Code 3 := flipHighColumns (rowPermutedCode rho03 C)
  have hEq : Equivalent C Ct := by
    exact equivalent_trans (rowPermutedCode_equiv rho03 C) (flipHighColumns_equiv (rowPermutedCode rho03 C))
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
    rcases n3_caseB_types_3567 C hcols h1 h2 h4 t with hv3 | hv5 | hv6 | hv7
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

/-! ## n = 3: Case-1 analysis (|1| > 0, columns in {1,3,5,6})

With columns in {1,3,5,6} and |1| > 0, the n=3 counts determine the code up
to equivalence: |1| ∈ {1,2,3}.  The |1|=1 cases land in Class-I (contradiction),
Class-III / the (1,3,5) / (1,5,6) families (equivalent to `code136`), or the
(1,3,5) condition-(iii) exception (equivalent to `code136`); the |1|=2 cases
land in Class-II (contradiction) or the (1,1,5)/(1,1,6) codes (strictly
dominated by the linear code (3,3,5)); |1|=3 is Class-I (contradiction).
This is the n=3 form of the `lm:all` (Lemma 15) Case-1 analysis, with the condition-(iii)
exception mapped into `InOptimal3` via `code136`.
-/

-- generic: a code whose columns are one each of types i,j,k is equivalent to D
-- via row perm ρ and flips f, given the target column values at positions 0,1,2
lemma equiv_types3 (C D : Code 3) (i j k : ℕ) (ρ : Equiv (Fin 4) (Fin 4)) (f : Fin 3 → Bool)
    (t1 t2 t3 : Fin 3)
    (_ht1 : colVal (C t1) = i) (_ht2 : colVal (C t2) = j) (_ht3 : colVal (C t3) = k)
    (huniq1 : ∀ u : Fin 3, colVal (C u) = i → u = t1)
    (huniq2 : ∀ u : Fin 3, colVal (C u) = j → u = t2)
    (huniq3 : ∀ u : Fin 3, colVal (C u) = k → u = t3)
    (htypes : ∀ t : Fin 3, colVal (C t) = i ∨ colVal (C t) = j ∨ colVal (C t) = k)
    (hne12 : t1 ≠ t2) (hne13 : t1 ≠ t3) (hne23 : t2 ≠ t3)
    (hD0 : D 0 = rowPermute ρ (if f t1 then flipCol (C t1) else C t1))
    (hD1 : D 1 = rowPermute ρ (if f t2 then flipCol (C t2) else C t2))
    (hD2 : D 2 = rowPermute ρ (if f t3 then flipCol (C t3) else C t3)) :
    Equivalent C D := by
  have htri : ∀ t : Fin 3, t = t1 ∨ t = t2 ∨ t = t3 := by
    intro t
    rcases htypes t with hv1 | hv2 | hv3
    · left; exact huniq1 t hv1
    · right; left; exact huniq2 t hv2
    · right; right; exact huniq3 t hv3
  let toFun : Fin 3 → Fin 3 := fun t => if t = t1 then ⟨0, by decide⟩ else if t = t2 then ⟨1, by decide⟩ else ⟨2, by decide⟩
  let invFun : Fin 3 → Fin 3 := fun j => if j.val = 0 then t1 else if j.val = 1 then t2 else t3
  let p : Fin 3 ≃ Fin 3 :=
    { toFun := toFun
      invFun := invFun
      left_inv := by
        intro t
        rcases htri t with ht1c | ht2c | ht3c
        · subst t; simp [toFun, invFun]
        · subst t; simp [toFun, invFun, hne12.symm]
        · subst t; simp [toFun, invFun, hne13.symm, hne23.symm]
      right_inv := by
        intro t
        fin_cases t
        · simp [toFun, invFun]
        · simp [toFun, invFun, hne12.symm]
        · simp [toFun, invFun, hne13.symm, hne23.symm] }
  refine ⟨ρ, p, f, ?_⟩
  intro t
  rcases htri t with ht1c | ht2c | ht3c
  · subst t
    have hp : p t1 = ⟨0, by decide⟩ := by simp [p, toFun]
    rw [hp]
    exact hD0
  · subst t
    have hp : p t2 = ⟨1, by decide⟩ := by simp [p, toFun, hne12.symm]
    rw [hp]
    exact hD1
  · subst t
    have hp : p t3 = ⟨2, by decide⟩ := by simp [p, toFun, hne13.symm, hne23.symm]
    rw [hp]
    exact hD2

def rho01 : Equiv (Fin 4) (Fin 4) := Equiv.swap (0 : Fin 4) (1 : Fin 4)

-- (1,3,5) is equivalent to code136 (row swap (0,1) + flip of the col5 column)
-- native_decide: Contentful · n=3 · checked 2026-08-28
lemma n3_135_equiv_136 (C : Code 3)
    (h1 : count C 1 = 1) (h3 : count C 3 = 1) (h5 : count C 5 = 1) (h6 : count C 6 = 0)
    (hcols : ∀ t : Fin 3, colVal (C t) = 1 ∨ colVal (C t) = 3 ∨ colVal (C t) = 5 ∨ colVal (C t) = 6) :
    Equivalent C code136 := by
  have h1pos : 1 ≤ count C 1 := by rw [h1]
  have h3pos : 1 ≤ count C 3 := by rw [h3]
  have h5pos : 1 ≤ count C 5 := by rw [h5]
  rcases exists_col_of_colVal C 1 h1pos with ⟨t1, ht1⟩
  rcases exists_col_of_colVal C 3 h3pos with ⟨t3, ht3⟩
  rcases exists_col_of_colVal C 5 h5pos with ⟨t5, ht5⟩
  have huniq1 : ∀ u : Fin 3, colVal (C u) = 1 → u = t1 := colVal_unique_of_count_one (C := C) t1 ht1 h1
  have huniq3 : ∀ u : Fin 3, colVal (C u) = 3 → u = t3 := colVal_unique_of_count_one (C := C) t3 ht3 h3
  have huniq5 : ∀ u : Fin 3, colVal (C u) = 5 → u = t5 := colVal_unique_of_count_one (C := C) t5 ht5 h5
  have htypes : ∀ t : Fin 3, colVal (C t) = 1 ∨ colVal (C t) = 3 ∨ colVal (C t) = 5 := by
    intro t
    rcases hcols t with hv1 | hv3 | hv5 | hv6
    · left; exact hv1
    · right; left; exact hv3
    · right; right; exact hv5
    · exfalso; have hp : 1 ≤ count C 6 := count_pos_of_colVal C t hv6; omega
  have htne13 : t1 ≠ t3 := by
    intro heq
    have hv : colVal (C t1) = 3 := by rw [heq]; exact ht3
    norm_num [ht1] at hv
  have htne15 : t1 ≠ t5 := by
    intro heq
    have hv : colVal (C t1) = 5 := by rw [heq]; exact ht5
    norm_num [ht1] at hv
  have htne35 : t3 ≠ t5 := by
    intro heq
    have hv : colVal (C t3) = 5 := by rw [heq]; exact ht5
    norm_num [ht3] at hv
  let f135 : Fin 3 → Bool := fun t => t = t5
  have hc1 : C t1 = col1 := (colVal_eq_one_iff_col1 (C t1)).mp ht1
  have hc3 : C t3 = col3 := (colVal_eq_three_iff_col3 (C t3)).mp ht3
  have hc5 : C t5 = col5 := (colVal_eq_five_iff_col5 (C t5)).mp ht5
  have hD0 : code136 0 = rowPermute rho01 (if f135 t1 then flipCol (C t1) else C t1) := by
    simp [code136, f135, htne15, hc1]
    native_decide
  have hD1 : code136 1 = rowPermute rho01 (if f135 t3 then flipCol (C t3) else C t3) := by
    simp [code136, f135, htne35]
    rw [hc3]
    native_decide
  have hD2 : code136 2 = rowPermute rho01 (if f135 t5 then flipCol (C t5) else C t5) := by
    simp [code136, f135]
    rw [hc5]
    native_decide
  exact equiv_types3 C code136 1 3 5 rho01 f135 t1 t3 t5 ht1 ht3 ht5 huniq1 huniq3 huniq5 htypes htne13 htne15 htne35 hD0 hD1 hD2

-- (1,5,6) is equivalent to code136 (row swap (1,2) = rho15 swaps col5 and col3)
-- native_decide: Contentful · n=3 · checked 2026-08-28
lemma n3_156_equiv_136 (C : Code 3)
    (h1 : count C 1 = 1) (h5 : count C 5 = 1) (h6 : count C 6 = 1) (h3 : count C 3 = 0)
    (hcols : ∀ t : Fin 3, colVal (C t) = 1 ∨ colVal (C t) = 3 ∨ colVal (C t) = 5 ∨ colVal (C t) = 6) :
    Equivalent C code136 := by
  have h1pos : 1 ≤ count C 1 := by rw [h1]
  have h5pos : 1 ≤ count C 5 := by rw [h5]
  have h6pos : 1 ≤ count C 6 := by rw [h6]
  rcases exists_col_of_colVal C 1 h1pos with ⟨t1, ht1⟩
  rcases exists_col_of_colVal C 5 h5pos with ⟨t5, ht5⟩
  rcases exists_col_of_colVal C 6 h6pos with ⟨t6, ht6⟩
  have huniq1 : ∀ u : Fin 3, colVal (C u) = 1 → u = t1 := colVal_unique_of_count_one (C := C) t1 ht1 h1
  have huniq5 : ∀ u : Fin 3, colVal (C u) = 5 → u = t5 := colVal_unique_of_count_one (C := C) t5 ht5 h5
  have huniq6 : ∀ u : Fin 3, colVal (C u) = 6 → u = t6 := colVal_unique_of_count_one (C := C) t6 ht6 h6
  have htypes : ∀ t : Fin 3, colVal (C t) = 1 ∨ colVal (C t) = 5 ∨ colVal (C t) = 6 := by
    intro t
    rcases hcols t with hv1 | hv3 | hv5 | hv6
    · left; exact hv1
    · exfalso; have hp : 1 ≤ count C 3 := count_pos_of_colVal C t hv3; omega
    · right; left; exact hv5
    · right; right; exact hv6
  have htne15 : t1 ≠ t5 := by
    intro heq
    have hv : colVal (C t1) = 5 := by rw [heq]; exact ht5
    norm_num [ht1] at hv
  have htne16 : t1 ≠ t6 := by
    intro heq
    have hv : colVal (C t1) = 6 := by rw [heq]; exact ht6
    norm_num [ht1] at hv
  have htne56 : t5 ≠ t6 := by
    intro heq
    have hv : colVal (C t5) = 6 := by rw [heq]; exact ht6
    norm_num [ht5] at hv
  have hc1 : C t1 = col1 := (colVal_eq_one_iff_col1 (C t1)).mp ht1
  have hc5 : C t5 = col5 := (colVal_eq_five_iff_col5 (C t5)).mp ht5
  have hc6 : C t6 = col6 := (colVal_eq_six_iff_col6 (C t6)).mp ht6
  have hD0 : code136 0 = rowPermute rho15 (C t1) := by
    simp [code136, hc1]
    native_decide
  have hD1 : code136 1 = rowPermute rho15 (C t5) := by
    simp [code136, hc5]
    native_decide
  have hD2 : code136 2 = rowPermute rho15 (C t6) := by
    simp [code136, hc6]
    native_decide
  exact equiv_types3 C code136 1 5 6 rho15 (fun _ => false) t1 t5 t6 ht1 ht5 ht6 huniq1 huniq5 huniq6 htypes htne15 htne16 htne56 hD0 hD1 hD2

-- the canonical codes (1,1,X) and (3,3,5)
def code11x (colX : Column) : Code 3 := fun t => if t.val = 2 then colX else col1
def code115 : Code 3 := code11x col5
def code116 : Code 3 := code11x col6
def code335 : Code 3 := fun t => if t.val = 2 then col5 else col3

-- (3,3,5) strictly dominates (1,1,5) and (1,1,6)
-- native_decide: Contentful · n=3 · checked 2026-08-28
lemma n3_strict_115 : UniversalStrictBetter code335 code115 :=
  universalStrictBetter_of_dCode_le_lt code115 code335 (by native_decide) (by native_decide)
-- native_decide: Contentful · n=3 · checked 2026-08-28
lemma n3_strict_116 : UniversalStrictBetter code335 code116 :=
  universalStrictBetter_of_dCode_le_lt code116 code335 (by native_decide) (by native_decide)

-- a code with two type-1 columns and one type-X column is equivalent to (1,1,X)
-- native_decide: Contentful · n=3 · checked 2026-08-28
lemma equiv_11x_of_counts (C : Code 3) (colX : Column) (i : ℕ)
    (hci : ∀ c : Column, colVal c = i → c = colX)
    (hcolX : colVal colX = i) (hne_i_1 : i ≠ 1)
    (h1 : count C 1 = 2) (hX : count C i = 1)
    (htypes : ∀ t : Fin 3, colVal (C t) = 1 ∨ colVal (C t) = i) :
    Equivalent C (code11x colX) := by
  have h1pos : 1 ≤ count C 1 := by rw [h1]; omega
  have hXpos : 1 ≤ count C i := by rw [hX]
  rcases exists_col_of_colVal C 1 h1pos with ⟨t1a, ht1a⟩
  have hcardf : (Finset.univ.filter fun t : Fin 3 => colVal (C t) = 1).card = 2 := by
    simpa [count_eq_card] using h1
  have ht1a' : t1a ∈ (Finset.univ.filter fun t : Fin 3 => colVal (C t) = 1) := by
    rw [Finset.mem_filter]; exact ⟨Finset.mem_univ t1a, ht1a⟩
  have hrest : ((Finset.univ.filter fun t : Fin 3 => colVal (C t) = 1).erase t1a).card = 1 := by
    rw [Finset.card_erase_of_mem ht1a']
    omega
  have hpos : 0 < ((Finset.univ.filter fun t : Fin 3 => colVal (C t) = 1).erase t1a).card := by
    rw [hrest]; norm_num
  rcases Finset.card_pos.mp hpos with ⟨t1b, ht1bm⟩
  have ht1b' : t1b ∈ (Finset.univ.filter fun t : Fin 3 => colVal (C t) = 1) := (Finset.mem_erase.mp ht1bm).2
  have ht1bne : t1b ≠ t1a := (Finset.mem_erase.mp ht1bm).1
  have ht1b : colVal (C t1b) = 1 := (Finset.mem_filter.mp ht1b').2
  rcases exists_col_of_colVal C i hXpos with ⟨tx, htx⟩
  have hc1a : C t1a = col1 := (colVal_eq_one_iff_col1 (C t1a)).mp ht1a
  have hc1b : C t1b = col1 := (colVal_eq_one_iff_col1 (C t1b)).mp ht1b
  have hcx : C tx = colX := hci (C tx) htx
  have huniq1 : ∀ u : Fin 3, colVal (C u) = 1 → u = t1a ∨ u = t1b :=
    colVal_fiber_eq_two (C := C) t1a t1b ht1a ht1b ht1bne.symm h1
  have huniqX : ∀ u : Fin 3, colVal (C u) = i → u = tx :=
    colVal_unique_of_count_one (C := C) tx htx hX
  have hall : ∀ t : Fin 3, C t = col1 ∨ C t = colX := by
    intro t
    rcases htypes t with hv1 | hvi
    · left; exact (colVal_eq_one_iff_col1 (C t)).mp hv1
    · right; exact hci (C t) hvi
  have htri : ∀ t : Fin 3, t = t1a ∨ t = t1b ∨ t = tx := by
    intro t
    rcases hall t with hv1 | hvX
    · have hcv : colVal (C t) = 1 := by rw [hv1]; native_decide
      rcases huniq1 t hcv with ht1a | ht1b
      · left; exact ht1a
      · right; left; exact ht1b
    · have hcv : colVal (C t) = i := by rw [hvX, hcolX]
      right; right; exact huniqX t hcv
  have htne1a : tx ≠ t1a := by
    intro heq
    have hcv : colVal (C t1a) = i := by rw [← heq]; exact htx
    exact hne_i_1 (hcv.symm.trans ht1a)
  have htne1b : tx ≠ t1b := by
    intro heq
    have hcv : colVal (C t1b) = i := by rw [← heq]; exact htx
    exact hne_i_1 (hcv.symm.trans ht1b)
  let toFun : Fin 3 → Fin 3 := fun t => if t = t1a then ⟨0, by decide⟩ else if t = t1b then ⟨1, by decide⟩ else ⟨2, by decide⟩
  let invFun : Fin 3 → Fin 3 := fun j => if j.val = 0 then t1a else if j.val = 1 then t1b else tx
  let p : Fin 3 ≃ Fin 3 :=
    { toFun := toFun
      invFun := invFun
      left_inv := by
        intro t
        rcases htri t with ht1c | ht2c | htxc
        · subst t; simp [toFun, invFun]
        · subst t; simp [toFun, invFun, ht1bne]
        · subst t; simp [toFun, invFun, htne1a, htne1b]
      right_inv := by
        intro j
        fin_cases j
        · simp [toFun, invFun]
        · simp [toFun, invFun, ht1bne]
        · simp [toFun, invFun, htne1a, htne1b] }
  refine ⟨Equiv.refl (Fin 4), p, fun _ => false, ?_⟩
  intro t
  rcases htri t with ht1c | ht2c | htxc
  · subst t
    have hp : p t1a = ⟨0, by decide⟩ := by simp [p, toFun]
    simp [code11x, hp, hc1a]
    change col1 = col1
    rfl
  · subst t
    have hp : p t1b = ⟨1, by decide⟩ := by simp [p, toFun, ht1bne]
    simp [code11x, hp, hc1b]
    change col1 = col1
    rfl
  · subst t
    have hp : p tx = ⟨2, by decide⟩ := by simp [p, toFun, htne1a, htne1b]
    simp [code11x, hp, hcx]
    change colX = colX
    rfl

-- Class-I/II/III derivations from n=3 counts
lemma n3_classI_133 (C : Code 3) (h1 : count C 1 = 1) (h3 : count C 3 = 2)
    (h5 : count C 5 = 0) (h6 : count C 6 = 0) : ClassI C := by
  have htot : totalCounts C ({1, 3, 5, 6} : Finset ℕ) = 3 := by
    unfold totalCounts
    simp [Finset.sum_insert]
    omega
  exact ⟨⟨0, by rw [h1]; rfl⟩, Or.inl ⟨⟨1, by rw [h3]⟩, ⟨0, by rw [h5]⟩, ⟨0, by rw [h6]⟩⟩, htot⟩

lemma n3_classI_155 (C : Code 3) (h1 : count C 1 = 1) (h3 : count C 3 = 0)
    (h5 : count C 5 = 2) (h6 : count C 6 = 0) : ClassI C := by
  have htot : totalCounts C ({1, 3, 5, 6} : Finset ℕ) = 3 := by
    unfold totalCounts
    simp [Finset.sum_insert]
    omega
  exact ⟨⟨0, by rw [h1]; rfl⟩, Or.inl ⟨⟨0, by rw [h3]⟩, ⟨1, by rw [h5]⟩, ⟨0, by rw [h6]⟩⟩, htot⟩

lemma n3_classI_166 (C : Code 3) (h1 : count C 1 = 1) (h3 : count C 3 = 0)
    (h5 : count C 5 = 0) (h6 : count C 6 = 2) : ClassI C := by
  have htot : totalCounts C ({1, 3, 5, 6} : Finset ℕ) = 3 := by
    unfold totalCounts
    simp [Finset.sum_insert]
    omega
  exact ⟨⟨0, by rw [h1]; rfl⟩, Or.inl ⟨⟨0, by rw [h3]⟩, ⟨0, by rw [h5]⟩, ⟨1, by rw [h6]⟩⟩, htot⟩

lemma n3_classI_111 (C : Code 3) (h1 : count C 1 = 3) (h3 : count C 3 = 0)
    (h5 : count C 5 = 0) (h6 : count C 6 = 0) : ClassI C := by
  have htot : totalCounts C ({1, 3, 5, 6} : Finset ℕ) = 3 := by
    unfold totalCounts
    simp [Finset.sum_insert]
    omega
  exact ⟨⟨1, by rw [h1]; rfl⟩, Or.inl ⟨⟨0, by rw [h3]⟩, ⟨0, by rw [h5]⟩, ⟨0, by rw [h6]⟩⟩, htot⟩

lemma n3_classII_113 (C : Code 3) (h1 : count C 1 = 2) (h3 : count C 3 = 1)
    (h5 : count C 5 = 0) (h6 : count C 6 = 0) : ClassII C := by
  have htot : totalCounts C ({1, 3, 5, 6} : Finset ℕ) = 3 := by
    unfold totalCounts
    simp [Finset.sum_insert]
    omega
  exact ⟨by rw [h1]; norm_num, htot,
    Or.inr ⟨⟨1, by rw [h1]⟩, ⟨0, by rw [h3]; rfl⟩, ⟨0, by rw [h5]⟩, ⟨0, by rw [h6]⟩⟩⟩

lemma n3_classIII_136 (C : Code 3) (h1 : count C 1 = 1) (h3 : count C 3 = 1) (h6 : count C 6 = 1)
    (hcols : ∀ t : Fin 3, colVal (C t) = 1 ∨ colVal (C t) = 3 ∨ colVal (C t) = 5 ∨ colVal (C t) = 6) :
    ClassIII C := by
  have h5z : count C 5 = 0 := by
    have htot : totalCounts C ({1, 3, 5, 6} : Finset ℕ) = 3 := by
      unfold totalCounts count
      rw [Finset.sum_comm]
      calc
        (∑ t : Fin 3, ∑ i ∈ ({1, 3, 5, 6} : Finset ℕ), if colVal (C t) = i then 1 else 0)
            = ∑ t : Fin 3, (1 : ℕ) := by
              apply Finset.sum_congr rfl
              intro t _
              rcases hcols t with hv1 | hv3 | hv5 | hv6
              · simp [hv1]
              · simp [hv3]
              · simp [hv5]
              · simp [hv6]
        _ = 3 := by simp
    unfold totalCounts at htot
    simp [Finset.sum_insert] at htot
    omega
  have h7z : count C 7 = 0 := by
    unfold count
    apply Finset.sum_eq_zero
    intro t _
    rcases hcols t with hv1 | hv3 | hv5 | hv6
    · simp [hv1]
    · simp [hv3]
    · simp [hv5]
    · simp [hv6]
  have htot5 : totalCounts C ({1, 3, 5, 6, 7} : Finset ℕ) = 3 := by
    unfold totalCounts
    simp [Finset.sum_insert, h5z, h7z]
    omega
  exact ⟨htot5, Or.inr ⟨h1, h5z, h7z, ⟨0, by rw [h3]; rfl⟩, ⟨0, by rw [h6]; rfl⟩⟩⟩

-- types helpers for the (1,1,X) cases
lemma n3_types_115 (C : Code 3) (hcols : ∀ t : Fin 3, colVal (C t) = 1 ∨ colVal (C t) = 3 ∨ colVal (C t) = 5 ∨ colVal (C t) = 6)
    (h3 : count C 3 = 0) (h6 : count C 6 = 0) :
    ∀ t : Fin 3, colVal (C t) = 1 ∨ colVal (C t) = 5 := by
  intro t
  rcases hcols t with hv1 | hv3 | hv5 | hv6
  · left; exact hv1
  · exfalso; have hp : 1 ≤ count C 3 := count_pos_of_colVal C t hv3; omega
  · right; exact hv5
  · exfalso; have hp : 1 ≤ count C 6 := count_pos_of_colVal C t hv6; omega

lemma n3_types_116 (C : Code 3) (hcols : ∀ t : Fin 3, colVal (C t) = 1 ∨ colVal (C t) = 3 ∨ colVal (C t) = 5 ∨ colVal (C t) = 6)
    (h3 : count C 3 = 0) (h5 : count C 5 = 0) :
    ∀ t : Fin 3, colVal (C t) = 1 ∨ colVal (C t) = 6 := by
  intro t
  rcases hcols t with hv1 | hv3 | hv5 | hv6
  · left; exact hv1
  · exfalso; have hp : 1 ≤ count C 3 := count_pos_of_colVal C t hv3; omega
  · exfalso; have hp : 1 ≤ count C 5 := count_pos_of_colVal C t hv5; omega
  · right; exact hv6

-- Case-1 (|1|>0, columns in {1,3,5,6}): the n=3 count analysis
-- native_decide: Contentful · n=3 · checked 2026-08-28
lemma n3_caseB_analysis (C : Code 3)
    (hcols : ∀ t : Fin 3, colVal (C t) = 1 ∨ colVal (C t) = 3 ∨ colVal (C t) = 5 ∨ colVal (C t) = 6)
    (h1pos : 0 < count C 1)
    (hopt : ∀ D : Code 3, UniversalBetter C D) :
    ∃ C' : Code 3, Equivalent C C' ∧ InOptimal3 C' := by
  have htot : totalCounts C ({1, 3, 5, 6} : Finset ℕ) = 3 := by
    unfold totalCounts count
    rw [Finset.sum_comm]
    calc
      (∑ t : Fin 3, ∑ i ∈ ({1, 3, 5, 6} : Finset ℕ), if colVal (C t) = i then 1 else 0)
          = ∑ t : Fin 3, (1 : ℕ) := by
            apply Finset.sum_congr rfl
            intro t _
            rcases hcols t with hv1 | hv3 | hv5 | hv6
            · simp [hv1]
            · simp [hv3]
            · simp [hv5]
            · simp [hv6]
      _ = 3 := by simp
  have hsum : count C 1 + count C 3 + count C 5 + count C 6 = 3 := by
    unfold totalCounts at htot
    simp [Finset.sum_insert] at htot
    omega
  have h1cases : count C 1 = 1 ∨ count C 1 = 2 ∨ count C 1 = 3 := by omega
  rcases h1cases with h1 | h1 | h1
  · have h356 : count C 3 + count C 5 + count C 6 = 2 := by omega
    by_cases h3z : count C 3 = 0
    · by_cases h5z : count C 5 = 0
      · have h6 : count C 6 = 2 := by omega
        exact False.elim (n3_class1_not_optimal (C := C) (n3_classI_166 C h1 h3z h5z h6) hopt)
      · by_cases h6z : count C 6 = 0
        · have h5 : count C 5 = 2 := by omega
          exact False.elim (n3_class1_not_optimal (C := C) (n3_classI_155 C h1 h3z h5 h6z) hopt)
        · have h5 : count C 5 = 1 := by omega
          have h6 : count C 6 = 1 := by omega
          have hEq : Equivalent C code136 := n3_156_equiv_136 C h1 h5 h6 h3z hcols
          exact ⟨code136, hEq, by simp [InOptimal3]⟩
    · by_cases h6z : count C 6 = 0
      · by_cases h5z : count C 5 = 0
        · have h3 : count C 3 = 2 := by omega
          exact False.elim (n3_class1_not_optimal (C := C) (n3_classI_133 C h1 h3 h5z h6z) hopt)
        · have h3 : count C 3 = 1 := by omega
          have h5 : count C 5 = 1 := by omega
          have hEq : Equivalent C code136 := n3_135_equiv_136 C h1 h3 h5 h6z hcols
          exact ⟨code136, hEq, by simp [InOptimal3]⟩
      · have h3 : count C 3 = 1 := by omega
        have h6 : count C 6 = 1 := by omega
        rcases n3_class3_equiv C (n3_classIII_136 C h1 h3 h6 hcols) with hEq | hEq
        · exact ⟨code135, hEq, by simp [InOptimal3]⟩
        · exact ⟨code136, hEq, by simp [InOptimal3]⟩
  · have h356 : count C 3 + count C 5 + count C 6 = 1 := by omega
    by_cases h3z : count C 3 = 0
    · by_cases h5z : count C 5 = 0
      · have h6 : count C 6 = 1 := by omega
        have hEq : Equivalent C code116 := equiv_11x_of_counts C col6 6
          (fun c hc => (colVal_eq_six_iff_col6 c).mp hc) (by native_decide) (by norm_num) h1 h6 (n3_types_116 C hcols h3z h5z)
        have hl : lambda C (1 / 4 : ℝ) = lambda code116 (1 / 4 : ℝ) :=
          (lambda_equiv C code116 hEq (1 / 4 : ℝ)).symm
        have hstrict : lambda code335 (1 / 4 : ℝ) > lambda code116 (1 / 4 : ℝ) :=
          n3_strict_116 (1 / 4 : ℝ) (by norm_num) (by norm_num)
        have hge : lambda C (1 / 4 : ℝ) ≥ lambda code335 (1 / 4 : ℝ) :=
          hopt code335 (1 / 4 : ℝ) (by norm_num) (by norm_num)
        rw [hl] at hge
        exfalso
        linarith
      · by_cases h6z : count C 6 = 0
        · have h5 : count C 5 = 1 := by omega
          have hEq : Equivalent C code115 := equiv_11x_of_counts C col5 5
            (fun c hc => (colVal_eq_five_iff_col5 c).mp hc) (by native_decide) (by norm_num) h1 h5 (n3_types_115 C hcols h3z h6z)
          have hl : lambda C (1 / 4 : ℝ) = lambda code115 (1 / 4 : ℝ) :=
            (lambda_equiv C code115 hEq (1 / 4 : ℝ)).symm
          have hstrict : lambda code335 (1 / 4 : ℝ) > lambda code115 (1 / 4 : ℝ) :=
            n3_strict_115 (1 / 4 : ℝ) (by norm_num) (by norm_num)
          have hge : lambda C (1 / 4 : ℝ) ≥ lambda code335 (1 / 4 : ℝ) :=
            hopt code335 (1 / 4 : ℝ) (by norm_num) (by norm_num)
          rw [hl] at hge
          exfalso
          linarith
        · exfalso
          omega
    · have h3 : count C 3 = 1 := by omega
      exact False.elim (n3_class2_not_optimal (C := C) (n3_classII_113 C h1 h3 (by omega) (by omega)) hopt)
  · have h3z : count C 3 = 0 := by omega
    have h5z : count C 5 = 0 := by omega
    have h6z : count C 6 = 0 := by omega
    exact False.elim (n3_class1_not_optimal (C := C) (n3_classI_111 C h1 h3z h5z h6z) hopt)

/-! ## n = 3: Case-C (at least two of |1|,|2|,|4|,|7| positive)

The core case |1| > 0 ∧ |7| > 0 uses `thm:odd` (Theorem 11) (`two_bit_flip`): replacing the
type-1 and type-7 columns by 3 and 5 is never worse, with equality iff
Condition-A.  At n=3 Condition-A forces |3|+|5| = 1, so the code is (1,5,7)
(Class-III-a) or (1,3,7), both equivalent to `code135` (the second via the
row swap (1,2) = `rho15`).  If Condition-A fails, the strictness
contradicts optimality.
-/

/-- (1,3,7) is equivalent to (1,5,7) = `code135` (row swap (1,2) swaps
columns 3 and 5). -/
-- native_decide: Contentful · n=3 · checked 2026-08-28
lemma n3_137_equiv_135 (C : Code 3)
    (h1 : count C 1 = 1) (h3 : count C 3 = 1) (h7 : count C 7 = 1)
    (_h5 : count C 5 = 0) (_h2 : count C 2 = 0) (_h4 : count C 4 = 0) (_h6 : count C 6 = 0)
    (hcols : ∀ t : Fin 3, 1 ≤ colVal (C t) ∧ colVal (C t) ≤ 7) :
    Equivalent C code135 := by
  have h1pos : 1 ≤ count C 1 := by rw [h1]
  have h3pos : 1 ≤ count C 3 := by rw [h3]
  have h7pos : 1 ≤ count C 7 := by rw [h7]
  rcases exists_col_of_colVal C 1 h1pos with ⟨t1, ht1⟩
  rcases exists_col_of_colVal C 3 h3pos with ⟨t3, ht3⟩
  rcases exists_col_of_colVal C 7 h7pos with ⟨t7, ht7⟩
  have huniq1 : ∀ u : Fin 3, colVal (C u) = 1 → u = t1 := colVal_unique_of_count_one (C := C) t1 ht1 h1
  have huniq3 : ∀ u : Fin 3, colVal (C u) = 3 → u = t3 := colVal_unique_of_count_one (C := C) t3 ht3 h3
  have huniq7 : ∀ u : Fin 3, colVal (C u) = 7 → u = t7 := colVal_unique_of_count_one (C := C) t7 ht7 h7
  have htypes : ∀ t : Fin 3, colVal (C t) = 1 ∨ colVal (C t) = 3 ∨ colVal (C t) = 7 := by
    intro t
    have hm := colVal_mem_of_totalCounts C ({1, 3, 7} : Finset ℕ) (by
      have h17 := n3_columns17_total C hcols
      unfold totalCounts
      simp [Finset.sum_insert]
      unfold totalCounts at h17
      simp [Finset.sum_insert] at h17
      omega) t
    simpa [Finset.mem_insert, Finset.mem_singleton] using hm
  have htne13 : t1 ≠ t3 := by
    intro heq
    have hv : colVal (C t1) = 3 := by rw [heq]; exact ht3
    norm_num [ht1] at hv
  have htne17 : t1 ≠ t7 := by
    intro heq
    have hv : colVal (C t1) = 7 := by rw [heq]; exact ht7
    norm_num [ht1] at hv
  have htne37 : t3 ≠ t7 := by
    intro heq
    have hv : colVal (C t3) = 7 := by rw [heq]; exact ht7
    norm_num [ht3] at hv
  have hc1 : C t1 = col1 := (colVal_eq_one_iff_col1 (C t1)).mp ht1
  have hc3 : C t3 = col3 := (colVal_eq_three_iff_col3 (C t3)).mp ht3
  have hc7 : C t7 = colOfNat 7 := by rw [← colOfNat_colVal (C t7), ht7]
  have hD0 : code135 0 = rowPermute rho15 (C t1) := by
    simp [code135, hc1]
    native_decide
  have hD1 : code135 1 = rowPermute rho15 (C t3) := by
    simp [code135, hc3]
    native_decide
  have hD2 : code135 2 = rowPermute rho15 (C t7) := by
    simp [code135, hc7]
    native_decide
  exact equiv_types3 C code135 1 3 7 rho15 (fun _ => false) t1 t3 t7 ht1 ht3 ht7 huniq1 huniq3 huniq7 htypes htne13 htne17 htne37 hD0 hD1 hD2

/-- (1,5,7) with Condition-A is Class-III-a. -/
lemma n3_classIII_157 (C : Code 3)
    (h1 : count C 1 = 1) (h7 : count C 7 = 1) (h5 : count C 5 = 1)
    (h3 : count C 3 = 0) (h6 : count C 6 = 0)
    (_h2 : count C 2 = 0) (_h4 : count C 4 = 0)
    (hcols : ∀ t : Fin 3, 1 ≤ colVal (C t) ∧ colVal (C t) ≤ 7) :
    ClassIII C := by
  have htot5 : totalCounts C ({1, 3, 5, 6, 7} : Finset ℕ) = 3 := by
    have h17 := n3_columns17_total C hcols
    unfold totalCounts
    simp [Finset.sum_insert]
    unfold totalCounts at h17
    simp [Finset.sum_insert] at h17
    omega
  exact ⟨htot5, Or.inl ⟨h1, h7, h6, ⟨0, by rw [h3]⟩, ⟨0, by rw [h5]; rfl⟩⟩⟩

/-- The core Case-C: |1| > 0 and |7| > 0.  `thm:odd` (Theorem 11) (`two_bit_flip`) gives a
never-worse code; Condition-A at n=3 forces (1,5,7) (Class-III-a) or (1,3,7),
both equivalent to `code135`, and otherwise the flip is strictly better,
contradicting optimality. -/
lemma n3_caseC_17 (C : Code 3)
    (hcols : ∀ t : Fin 3, 1 ≤ colVal (C t) ∧ colVal (C t) ≤ 7)
    (h1pos : 0 < count C 1) (h7pos : 0 < count C 7)
    (hopt : ∀ D : Code 3, UniversalBetter C D) :
    ∃ C' : Code 3, Equivalent C C' ∧ InOptimal3 C' := by
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
  let C' : Code 3 := replaceColumn (replaceColumn C t1 col3) t7 col5
  have hsame : ∀ u : Fin 3, u ≠ t1 → u ≠ t7 → C' u = C u := by
    intro u hu1 hu7
    simp [C', replaceColumn, hu1, hu7]
  have h07 : Columns07 C := columns07_of_colVal_le7 C (fun t => (hcols t).2)
  have hb := two_bit_flip C C' t1 t7 htne hc1 hc7 (by simp [C', replaceColumn, htne]) (by simp [C', replaceColumn]) hsame h07
  by_cases hcond : count C 1 = 1 ∧ count C 7 = 1 ∧ count C 2 = 0 ∧ count C 4 = 0 ∧
      count C 6 = 0 ∧ (Odd (count C 3) ∨ Odd (count C 5))
  · rcases hcond with ⟨h1eq, h7eq, h2z, h4z, h6z, h35odd⟩
    have h17 := n3_columns17_total C hcols
    have hsum17 : count C 1 + count C 2 + count C 3 + count C 4 + count C 5 + count C 6 + count C 7 = 3 := by
      unfold totalCounts at h17
      simp [Finset.sum_insert] at h17
      omega
    have h35 : count C 3 + count C 5 = 1 := by omega
    rcases h35odd with h3o | h5o
    · rcases h3o with ⟨a, ha⟩
      have h3 : count C 3 = 1 := by omega
      have h5z : count C 5 = 0 := by omega
      have hEq : Equivalent C code135 := n3_137_equiv_135 C h1eq h3 h7eq h5z h2z h4z h6z hcols
      exact ⟨code135, hEq, by simp [InOptimal3]⟩
    · rcases h5o with ⟨a, ha⟩
      have h5 : count C 5 = 1 := by omega
      have h3z : count C 3 = 0 := by omega
      have hclass3 : ClassIII C := n3_classIII_157 C h1eq h7eq h5 h3z h6z h2z h4z hcols
      rcases n3_class3_equiv C hclass3 with hEq | hEq
      · exact ⟨code135, hEq, by simp [InOptimal3]⟩
      · exact ⟨code136, hEq, by simp [InOptimal3]⟩
  · have hne : ¬ UniversalEqual C' C := by
      intro heq
      exact hcond (hb.2.1.mp heq)
    rcases exists_strict_better_of_not_equal (D := C') (C := C) hb.1 hne with ⟨ε, hε0, hε1, hgt⟩
    have hge : lambda C ε ≥ lambda C' ε := hopt C' ε hε0 hε1
    exfalso
    linarith

/-! ## n = 3: Case-C transformations and the covering assembly

The `lm:all` (Lemma 15) Case-2 cover: at least two of |1|,|2|,|4|,|7| positive, columns
in {1..7}.  All configurations reduce by row swaps (and, for |7| = 0, the
flip-types-2,3,6 plus row-swap-(0,2) transformation of Fig. fig:iwla) to the
core `n3_caseC_17` (|1| > 0 ∧ |7| > 0): rho23 swaps types 1↔2 and fixes 7;
rho13 maps 4→1 and fixes 7; rho15 swaps 2↔4 and fixes 1; the flip of types
2,3,6 followed by rho02 maps types 1,2,3,4,5,6,7 to 1,7,6,4,5,3,3.
-/

/-- Lift an `InOptimal3` witness for an equivalent code back to the original. -/
lemma n3_lift_equiv {C Ct : Code 3} (hEq : Equivalent C Ct)
    (hres : ∃ C'' : Code 3, Equivalent Ct C'' ∧ InOptimal3 C'') :
    ∃ C' : Code 3, Equivalent C C' ∧ InOptimal3 C' := by
  rcases hres with ⟨C'', hEqCt, hIn⟩
  exact ⟨C'', equivalent_trans hEq hEqCt, hIn⟩

/-- A column that is neither type 0 nor type 15 has value in 1..14. -/
lemma colVal_1_to_14_of_ne_0_15 {c : Column} (h0 : c ≠ col0) (h15 : c ≠ col15) :
    1 ≤ colVal c ∧ colVal c ≤ 14 := by
  have hle15 := colVal_le_15 c
  have hne0 : colVal c ≠ 0 := by
    intro hv
    exact h0 ((colVal_eq_zero_iff_col0 c).mp hv)
  have hne15 : colVal c ≠ 15 := by
    intro hv
    have hflip0 : colVal (flipCol c) = 0 := by
      rw [colVal_flipCol, hv]
    have hfc0 : flipCol c = col0 := (colVal_eq_zero_iff_col0 (flipCol c)).mp hflip0
    apply h15
    have hff : flipCol (flipCol c) = flipCol col0 := congrArg flipCol hfc0
    have hinv : flipCol (flipCol c) = c := by
      ext j
      simp [flipCol]
    rw [hinv] at hff
    exact hff.trans flipCol_col0
  omega

/-- With |1|=|2|=|4|=|7|=0, the columns of a {1..7}-code have types in {3,5,6}. -/
lemma n3_caseA_types_356 (C : Code 3)
    (hcols : ∀ t : Fin 3, 1 ≤ colVal (C t) ∧ colVal (C t) ≤ 7)
    (h1 : count C 1 = 0) (h2 : count C 2 = 0) (h4 : count C 4 = 0) (h7 : count C 7 = 0)
    (t : Fin 3) :
    colVal (C t) = 3 ∨ colVal (C t) = 5 ∨ colVal (C t) = 6 := by
  have h17 := n3_columns17_total C hcols
  have htot356 : totalCounts C ({3, 5, 6} : Finset ℕ) = 3 := by
    unfold totalCounts
    simp [Finset.sum_insert]
    unfold totalCounts at h17
    simp [Finset.sum_insert] at h17
    omega
  simpa [Finset.mem_insert, Finset.mem_singleton] using
    (colVal_mem_of_totalCounts C ({3, 5, 6} : Finset ℕ) htot356 t)

/-- With |2|=|4|=|7|=0, the columns of a {1..7}-code have types in {1,3,5,6}. -/
lemma n3_case1_types_1356 (C : Code 3)
    (hcols : ∀ t : Fin 3, 1 ≤ colVal (C t) ∧ colVal (C t) ≤ 7)
    (h2 : count C 2 = 0) (h4 : count C 4 = 0) (h7 : count C 7 = 0) (t : Fin 3) :
    colVal (C t) = 1 ∨ colVal (C t) = 3 ∨ colVal (C t) = 5 ∨ colVal (C t) = 6 := by
  have h17 := n3_columns17_total C hcols
  have htot : totalCounts C ({1, 3, 5, 6} : Finset ℕ) = 3 := by
    unfold totalCounts
    simp [Finset.sum_insert]
    unfold totalCounts at h17
    simp [Finset.sum_insert] at h17
    omega
  simpa [Finset.mem_insert, Finset.mem_singleton] using
    (colVal_mem_of_totalCounts C ({1, 3, 5, 6} : Finset ℕ) htot t)

/-- Case-C reduction for |7| > 0 and |2| > 0: the row swap (2,3) maps type 2
to 1 and fixes type 7, so the result has |1| > 0 ∧ |7| > 0. -/
-- native_decide: Contentful · n=3 · checked 2026-08-28
lemma n3_caseC_2_reduce (C : Code 3)
    (hcols : ∀ t : Fin 3, 1 ≤ colVal (C t) ∧ colVal (C t) ≤ 7)
    (h2 : 0 < count C 2) (h7 : 0 < count C 7) :
    ∃ Ct : Code 3, Equivalent C Ct ∧ 0 < count Ct 1 ∧ 0 < count Ct 7 ∧
      (∀ t : Fin 3, 1 ≤ colVal (Ct t) ∧ colVal (Ct t) ≤ 7) := by
  let Ct : Code 3 := rowPermutedCode rho23 C
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

/-- Case-C reduction for |7| > 0 and |4| > 0: the row swap (1,3) maps type 4
to 1 and fixes type 7. -/
-- native_decide: Contentful · n=3 · checked 2026-08-28
lemma n3_caseC_4_reduce (C : Code 3)
    (hcols : ∀ t : Fin 3, 1 ≤ colVal (C t) ∧ colVal (C t) ≤ 7)
    (h4 : 0 < count C 4) (h7 : 0 < count C 7) :
    ∃ Ct : Code 3, Equivalent C Ct ∧ 0 < count Ct 1 ∧ 0 < count Ct 7 ∧
      (∀ t : Fin 3, 1 ≤ colVal (Ct t) ∧ colVal (Ct t) ≤ 7) := by
  let Ct : Code 3 := rowPermutedCode rho13 C
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

/-- Case-C reduction for |1| > 0 and |2| > 0: flip the columns of types 2,3,6
and swap rows 0,2 (Fig. fig:iwla of `lm:all` (Lemma 15)).  The transformation maps types
1,2,3,4,5,6 to 1,7,6,4,5,3 (a type-7 column would map to type 13, which is why
the |7| = 0 hypothesis is needed), so |1| and |7| become positive. -/
-- native_decide: Contentful · n=3 · checked 2026-08-28
lemma n3_caseC_no7_reduce (C : Code 3)
    (hcols : ∀ t : Fin 3, 1 ≤ colVal (C t) ∧ colVal (C t) ≤ 7)
    (h7z : count C 7 = 0)
    (h1 : 0 < count C 1) (h2 : 0 < count C 2) :
    ∃ Ct : Code 3, Equivalent C Ct ∧ 0 < count Ct 1 ∧ 0 < count Ct 7 ∧
      (∀ t : Fin 3, 1 ≤ colVal (Ct t) ∧ colVal (Ct t) ≤ 7) := by
  let Ct : Code 3 := rowPermutedCode rho02 (flip236 C)
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
      have hc : C t = colOfNat (colVal (C t)) := (colOfNat_colVal (C t)).symm
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

/-- Case-C pre-reduction for |1| > 0 and |4| > 0 (|7| = 0): the row swap (1,2)
maps type 4 to 2 and fixes type 1, giving |1| > 0 ∧ |2| > 0 for
`n3_caseC_no7_reduce`. -/
-- native_decide: Contentful · n=3 · checked 2026-08-28
lemma n3_caseC_14_reduce (C : Code 3)
    (hcols : ∀ t : Fin 3, 1 ≤ colVal (C t) ∧ colVal (C t) ≤ 7)
    (h7z : count C 7 = 0)
    (h1 : 0 < count C 1) (h4 : 0 < count C 4) :
    ∃ Ct : Code 3, Equivalent C Ct ∧ 0 < count Ct 1 ∧ 0 < count Ct 2 ∧ count Ct 7 = 0 ∧
      (∀ t : Fin 3, 1 ≤ colVal (Ct t) ∧ colVal (Ct t) ≤ 7) := by
  let Ct : Code 3 := rowPermutedCode rho15 C
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

/-- Case-C pre-reduction for |2| > 0 and |4| > 0 (|7| = 0): the row swap (1,3)
maps type 4 to 1 and fixes type 2. -/
-- native_decide: Contentful · n=3 · checked 2026-08-28
lemma n3_caseC_24_reduce (C : Code 3)
    (hcols : ∀ t : Fin 3, 1 ≤ colVal (C t) ∧ colVal (C t) ≤ 7)
    (h7z : count C 7 = 0)
    (h2 : 0 < count C 2) (h4 : 0 < count C 4) :
    ∃ Ct : Code 3, Equivalent C Ct ∧ 0 < count Ct 1 ∧ 0 < count Ct 2 ∧ count Ct 7 = 0 ∧
      (∀ t : Fin 3, 1 ≤ colVal (Ct t) ∧ colVal (Ct t) ≤ 7) := by
  let Ct : Code 3 := rowPermutedCode rho13 C
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

/-- An optimal `(3,4)` code with columns in {1..7} is equivalent to one of the
five `thm:n8` (Theorem 5) codes.  This is the n = 3 form of the `lm:all` (Lemma 15) covering: Case A
(|1|=|2|=|4|=|7|=0 → columns in {3,5,6} → linear or strictly dominated),
Case-1 (exactly one of |1|,|2|,|4|,|7| positive → reduced to |1| > 0 with
columns in {1,3,5,6} and analyzed by counts), and Case-C (at least two
positive → reduced to |1| > 0 ∧ |7| > 0 and handled by `n3_caseC_17`). -/
lemma n3_opt_columns17 (C : Code 3)
    (hcols : ∀ t : Fin 3, 1 ≤ colVal (C t) ∧ colVal (C t) ≤ 7)
    (hopt : ∀ D : Code 3, UniversalBetter C D) :
    ∃ C' : Code 3, Equivalent C C' ∧ InOptimal3 C' := by
  by_cases hA : count C 1 = 0 ∧ count C 2 = 0 ∧ count C 4 = 0 ∧ count C 7 = 0
  · exact n3_columns356 C (fun t => n3_caseA_types_356 C hcols hA.1 hA.2.1 hA.2.2.1 hA.2.2.2 t) hopt
  ·
    by_cases h7 : 0 < count C 7
    · by_cases h1 : 0 < count C 1
      · exact n3_caseC_17 C hcols h1 h7 hopt
      · have h1z : count C 1 = 0 := by omega
        by_cases h2 : 0 < count C 2
        · rcases n3_caseC_2_reduce C hcols h2 h7 with ⟨Ct, hEqCt, h1', h7', hcolsCt⟩
          exact n3_lift_equiv hEqCt (n3_caseC_17 Ct hcolsCt h1' h7' (opt_of_equiv hopt hEqCt))
        · have h2z : count C 2 = 0 := by omega
          by_cases h4 : 0 < count C 4
          · rcases n3_caseC_4_reduce C hcols h4 h7 with ⟨Ct, hEqCt, h1', h7', hcolsCt⟩
            exact n3_lift_equiv hEqCt (n3_caseC_17 Ct hcolsCt h1' h7' (opt_of_equiv hopt hEqCt))
          · have h4z : count C 4 = 0 := by omega
            rcases n3_caseB_col7_reduce C hcols h7 h1z h2z h4z with ⟨Ct, hEqCt, h1', hcolsCt⟩
            exact n3_lift_equiv hEqCt (n3_caseB_analysis Ct hcolsCt h1' (opt_of_equiv hopt hEqCt))
    · have h7z : count C 7 = 0 := by omega
      by_cases h1 : 0 < count C 1
      · by_cases h2 : 0 < count C 2
        · rcases n3_caseC_no7_reduce C hcols h7z h1 h2 with ⟨Ct, hEqCt, h1', h7', hcolsCt⟩
          exact n3_lift_equiv hEqCt (n3_caseC_17 Ct hcolsCt h1' h7' (opt_of_equiv hopt hEqCt))
        · have h2z : count C 2 = 0 := by omega
          by_cases h4 : 0 < count C 4
          · rcases n3_caseC_14_reduce C hcols h7z h1 h4 with ⟨Ct, hEqCt, h1', h2', h7zCt, hcolsCt⟩
            rcases n3_caseC_no7_reduce Ct hcolsCt h7zCt h1' h2' with ⟨Ct2, hEqCt2, h1'', h7'', hcolsCt2⟩
            exact n3_lift_equiv (equivalent_trans hEqCt hEqCt2)
              (n3_caseC_17 Ct2 hcolsCt2 h1'' h7'' (opt_of_equiv hopt (equivalent_trans hEqCt hEqCt2)))
          · have h4z : count C 4 = 0 := by omega
            exact n3_caseB_analysis C (fun t => n3_case1_types_1356 C hcols h2z h4z h7z t) h1 hopt
      · have h1z : count C 1 = 0 := by omega
        by_cases h2 : 0 < count C 2
        · by_cases h4 : 0 < count C 4
          · rcases n3_caseC_24_reduce C hcols h7z h2 h4 with ⟨Ct, hEqCt, h1', h2', h7zCt, hcolsCt⟩
            rcases n3_caseC_no7_reduce Ct hcolsCt h7zCt h1' h2' with ⟨Ct2, hEqCt2, h1'', h7'', hcolsCt2⟩
            exact n3_lift_equiv (equivalent_trans hEqCt hEqCt2)
              (n3_caseC_17 Ct2 hcolsCt2 h1'' h7'' (opt_of_equiv hopt (equivalent_trans hEqCt hEqCt2)))
          · have h4z : count C 4 = 0 := by omega
            rcases n3_caseB_col2_reduce C hcols h2 h1z h4z h7z with ⟨Ct, hEqCt, h1', hcolsCt⟩
            exact n3_lift_equiv hEqCt (n3_caseB_analysis Ct hcolsCt h1' (opt_of_equiv hopt hEqCt))
        · have h2z : count C 2 = 0 := by omega
          by_cases h4 : 0 < count C 4
          · rcases n3_caseB_col4_reduce C hcols h4 h1z h2z h7z with ⟨Ct, hEqCt, h1', hcolsCt⟩
            exact n3_lift_equiv hEqCt (n3_caseB_analysis Ct hcolsCt h1' (opt_of_equiv hopt hEqCt))
          · have h4z : count C 4 = 0 := by omega
            exact False.elim (hA ⟨h1z, h2z, h4z, h7z⟩)

/-- An optimal `(3,4)` code is equivalent to one of the five codes of `thm:n8` (Theorem 5)
(eq. (eq:2)).  Type-0/15 columns reduce via `thm:0column` (Theorem 6)
(`n3_opt_has_0_or_15`); otherwise `flipHighColumns` normalizes the columns to
{1..7} and `n3_opt_columns17` applies the `lm:all` (Lemma 15) Case-1/Case-2 analysis. -/
lemma n3_opt_columns_114 (C : Code 3) (hopt : ∀ D : Code 3, UniversalBetter C D) :
    ∃ C' : Code 3, Equivalent C C' ∧ InOptimal3 C' := by
  by_cases h015 : ∃ t : Fin 3, C t = col0 ∨ C t = col15
  · exact n3_opt_has_0_or_15 (C := C) hopt h015
  · let C1 : Code 3 := flipHighColumns C
    have hEq1 : Equivalent C C1 := flipHighColumns_equiv C
    have hopt1 : ∀ D : Code 3, UniversalBetter C1 D := opt_of_equiv hopt hEq1
    have hcolsC : ∀ t : Fin 3, 1 ≤ colVal (C t) ∧ colVal (C t) ≤ 14 := by
      intro t
      exact colVal_1_to_14_of_ne_0_15
        (fun heq => h015 ⟨t, Or.inl heq⟩)
        (fun heq => h015 ⟨t, Or.inr heq⟩)
    have hcols1 : ∀ t : Fin 3, 1 ≤ colVal (C1 t) ∧ colVal (C1 t) ≤ 7 := by
      intro t
      have hm := flipHighColumns_mem17 C hcolsC t
      have hm' : colVal (C1 t) = 1 ∨ colVal (C1 t) = 2 ∨ colVal (C1 t) = 3 ∨ colVal (C1 t) = 4 ∨
          colVal (C1 t) = 5 ∨ colVal (C1 t) = 6 ∨ colVal (C1 t) = 7 := by
        simpa [Finset.mem_insert, Finset.mem_singleton] using hm
      rcases hm' with hv1 | hv2 | hv3 | hv4 | hv5 | hv6 | hv7 <;> constructor <;> omega
    rcases n3_opt_columns17 C1 hcols1 hopt1 with ⟨C', hEqC1, hIn⟩
    exact ⟨C', equivalent_trans hEq1 hEqC1, hIn⟩

/-- Theorem `thm:n8` (Theorem 5): for 2 ≤ n ≤ 8, n ≠ 3, all optimal codes are equivalent
to linear codes; for n = 3 the optimal codes are exactly the five listed
codes and their equivalents (`InOptimal3`, eq. (eq:2)).  The n = 2 case is a
direct row-distinctness argument, the n = 3 case is the explicit five-code
classification, and 4 ≤ n ≤ 8 uses `thm:condition_optimalcode` (Theorem 4) with the
hypothesis verified by `class1_cond_n_le8` (`thm:301` (Theorem 17)). -/
theorem optimal_codes_small_n (n : ℕ) (hn2 : 2 ≤ n) (hn8 : n ≤ 8) :
    (n ≠ 3 → ∀ C : Code n, (∀ D : Code n, UniversalBetter C D) →
      ∃ C' : Code n, Equivalent C C' ∧ IsLinear C') ∧
      (n = 3 → ∀ C : Code 3, (∀ D : Code 3, UniversalBetter C D) →
        ∃ C' : Code 3, Equivalent C C' ∧ InOptimal3 C') := by
  constructor
  · intro hn3 C hopt
    by_cases hn2' : n = 2
    · subst n
      exact n2_optimal_linear C hopt
    · -- 4 ≤ n ≤ 8: `thm:condition_optimalcode` (Theorem 4) with the hypothesis verified
      -- by `class1_cond_n_le8` (`thm:301` (Theorem 17))
      have hn4 : n > 3 := by omega
      have hOptAt : OptimalAt C (1 / 4 : ℝ) := fun D => hopt D (1 / 4) (by norm_num) (by norm_num)
      exact condition_optimalcode n hn4 (class1_cond_n_le8 hn8)
        (1 / 4 : ℝ) (by norm_num) (by norm_num) C hOptAt
  · intro hn3eq
    subst n
    exact n3_opt_columns_114

end N4Code
