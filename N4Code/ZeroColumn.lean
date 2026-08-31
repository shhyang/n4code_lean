import N4Code.Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity

/-!
# Phase C: replacing 0-columns (paper §IV-C, `thm:0column` (Theorem 6), `cor:0col` (Corollary 7))

For a code `C` with `C t = col0`, the code `C'` obtained by replacing the
column at `t` by `s'` never has worse performance (`thm:0column` (Theorem 6)).  The rows
split into `O` (where `s'` still has bit 0, the column is unchanged) and `P`
(where `s'` has bit 1, the column changes); the paper's comparison machinery
applies with `d_O = min` over `O` and `d_P = min` over `P`.
-/

open scoped BigOperators

noncomputable section

namespace N4Code

/-! ## Minimum distance over a set of rows -/

/-- `Finset.min'` does not depend on the nonemptiness proof. -/
lemma min'_proof_irrel {s : Finset ℕ} (H1 H2 : s.Nonempty) : s.min' H1 = s.min' H2 :=
  congrArg (fun H : s.Nonempty => s.min' H) (Subsingleton.elim H1 H2)

/-- The minimum Hamming distance from y to the rows in S. -/
def dRowMin {n : ℕ} (C : Code n) (S : Finset (Fin 4)) (hS : S.Nonempty) (y : Word n) : ℕ :=
  (S.image fun i => dRow C i y).min' (hS.image fun i => dRow C i y)

/-- The rows where the new column has bit 1 (the changed rows P). -/
def colOnes (s' : Column) : Finset (Fin 4) := Finset.univ.filter fun i => s' i

/-- The rows where the new column has bit 0 (the unchanged rows O). -/
def colZeros (s' : Column) : Finset (Fin 4) := Finset.univ.filter fun i => ¬ s' i

/-- d_O for the 0 → s' change: minimum over the unchanged rows. -/
def dOc {n : ℕ} (C : Code n) (s' : Column) (hO : (colZeros s').Nonempty) (y : Word n) : ℕ :=
  dRowMin C (colZeros s') hO y

/-- d_P for the 0 → s' change: minimum over the changed rows. -/
def dPc {n : ℕ} (C : Code n) (s' : Column) (hP : (colOnes s').Nonempty) (y : Word n) : ℕ :=
  dRowMin C (colOnes s') hP y

/-- The minimum over S ∪ T is the min of the two minima. -/
lemma dRowMin_union {n : ℕ} (C : Code n) (S T : Finset (Fin 4)) (hS : S.Nonempty)
    (hT : T.Nonempty) (y : Word n) :
    dRowMin C (S ∪ T) (by rcases hS with ⟨i, hi⟩; exact ⟨i, Finset.mem_union_left T hi⟩) y =
      min (dRowMin C S hS y) (dRowMin C T hT y) := by
  unfold dRowMin
  simp only [Finset.image_union]
  rw [Finset.min'_union]

/-- dCode is the minimum over all four rows. -/
lemma dRowMin_univ {n : ℕ} (C : Code n) (y : Word n) :
    dRowMin C (Finset.univ : Finset (Fin 4)) (Finset.univ_nonempty) y = dCode C y := by
  have hle_row : ∀ i : Fin 4, dRowMin C (Finset.univ : Finset (Fin 4)) Finset.univ_nonempty y ≤
      dRow C i y := by
    intro i
    unfold dRowMin
    exact Finset.min'_le ((Finset.univ : Finset (Fin 4)).image fun i => dRow C i y) (dRow C i y)
      (Finset.mem_image.mpr ⟨i, by simp, rfl⟩)
  apply le_antisymm
  · unfold dCode
    change dRowMin C (Finset.univ : Finset (Fin 4)) Finset.univ_nonempty y ≤
        min (dRow C 0 y) (min (dRow C 1 y) (min (dRow C 2 y) (dRow C 3 y)))
    apply le_min
    · exact hle_row 0
    · apply le_min
      · exact hle_row 1
      · apply le_min
        · exact hle_row 2
        · exact hle_row 3
  · unfold dRowMin
    have hm := Finset.min'_mem ((Finset.univ : Finset (Fin 4)).image (fun i => dRow C i y))
      (Finset.univ_nonempty.image (fun i => dRow C i y))
    rcases (Finset.mem_image.mp hm) with ⟨i, hi, hfi⟩
    calc
      dCode C y ≤ dRow C i y := dCode_le_dRow C i y
      _ = (Finset.univ.image (fun i => dRow C i y)).min'
          (Finset.univ_nonempty.image (fun i => dRow C i y)) := by
            simpa [min'_proof_irrel] using hfi

/-- Flipping y at t, where the column at t is all zeros, changes each row
distance by exactly ∓1. -/
lemma dRow_flip_zero {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) (hcol : C t = col0) :
    ∀ i : Fin 4, (y t = true → dRow C i (flipBit t y) = dRow C i y - 1) ∧
      (y t = false → dRow C i (flipBit t y) = dRow C i y + 1) := by
  intro i
  rw [dRow_eq_hammingDist, dRow_eq_hammingDist]
  have ht0 : (row C i) t = false := by
    unfold row
    simp [hcol, colBit, col0]
  constructor
  · intro hyt
    unfold hammingDist hammingWeight
    have hsplit_new := sum_split_at
      (fun u : Fin n => if bitXor (row C i) (flipBit t y) u = true then 1 else 0) t
    have hsplit_old := sum_split_at
      (fun u : Fin n => if bitXor (row C i) y u = true then 1 else 0) t
    have hS : (∑ u ∈ (Finset.univ.erase t),
        if bitXor (row C i) (flipBit t y) u = true then 1 else 0) =
        ∑ u ∈ (Finset.univ.erase t), if bitXor (row C i) y u = true then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro u hu
      have ht : u ≠ t := (Finset.mem_erase.mp hu).1
      simp [bitXor, flipBit, ht]
    have htnew : (if bitXor (row C i) (flipBit t y) t = true then 1 else 0) = 0 := by
      have : bitXor (row C i) (flipBit t y) t = false := by
        simp [bitXor, flipBit, ht0, hyt]
      simp [this]
    have htold : (if bitXor (row C i) y t = true then 1 else 0) = 1 := by
      have : bitXor (row C i) y t = true := by
        simp [bitXor, ht0, hyt]
      simp [this]
    rw [hsplit_new, hsplit_old, hS, htnew, htold]
    omega
  · intro hyt
    unfold hammingDist hammingWeight
    have hsplit_new := sum_split_at
      (fun u : Fin n => if bitXor (row C i) (flipBit t y) u = true then 1 else 0) t
    have hsplit_old := sum_split_at
      (fun u : Fin n => if bitXor (row C i) y u = true then 1 else 0) t
    have hS : (∑ u ∈ (Finset.univ.erase t),
        if bitXor (row C i) (flipBit t y) u = true then 1 else 0) =
        ∑ u ∈ (Finset.univ.erase t), if bitXor (row C i) y u = true then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro u hu
      have ht : u ≠ t := (Finset.mem_erase.mp hu).1
      simp [bitXor, flipBit, ht]
    have htnew : (if bitXor (row C i) (flipBit t y) t = true then 1 else 0) = 1 := by
      have : bitXor (row C i) (flipBit t y) t = true := by
        simp [bitXor, flipBit, ht0, hyt]
      simp [this]
    have htold : (if bitXor (row C i) y t = true then 1 else 0) = 0 := by
      have : bitXor (row C i) y t = false := by
        simp [bitXor, ht0, hyt]
      simp [this]
    rw [hsplit_new, hsplit_old, hS, htnew, htold]

/-- The minimum over S of (f a − 1) is the minimum minus one. -/
lemma min_image_sub_one {α : Type*} {S : Finset α} {f : α → ℕ} (hS : S.Nonempty) :
    (S.image (fun a => f a - 1)).min' (hS.image (fun a => f a - 1)) =
      (S.image f).min' (hS.image f) - 1 := by
  apply le_antisymm
  · have hm : (S.image f).min' (hS.image f) ∈ S.image f := Finset.min'_mem _ _
    rcases (Finset.mem_image.mp hm) with ⟨a, ha, hfa⟩
    have hmem : (fun a => f a - 1) a ∈ S.image (fun a => f a - 1) :=
      Finset.mem_image.mpr ⟨a, ha, rfl⟩
    have hle : (S.image (fun a => f a - 1)).min' (hS.image (fun a => f a - 1)) ≤ f a - 1 :=
      Finset.min'_le (S.image (fun a => f a - 1)) (f a - 1) hmem
    rwa [hfa] at hle
  · apply Finset.le_min'
    intro b hb
    rcases (Finset.mem_image.mp hb) with ⟨a, ha, hba⟩
    have hle : (S.image f).min' (hS.image f) ≤ f a :=
      Finset.min'_le (S.image f) (f a) (Finset.mem_image.mpr ⟨a, ha, rfl⟩)
    rw [← hba]
    exact Nat.sub_le_sub_right hle 1

/-- The minimum over S of (f a + 1) is the minimum plus one. -/
lemma min_image_add_one {α : Type*} {S : Finset α} {f : α → ℕ} (hS : S.Nonempty) :
    (S.image (fun a => f a + 1)).min' (hS.image (fun a => f a + 1)) =
      (S.image f).min' (hS.image f) + 1 := by
  have h := min_image_sub_one (S := S) (f := fun a => f a + 1) hS
  have hcong : (S.image (fun a => (f a + 1) - 1)) = S.image f := by
    apply Finset.image_congr
    intro a _
    simp
  have h' : (S.image (fun a => f a + 1)).min' (hS.image (fun a => f a + 1)) - 1 =
      (S.image f).min' (hS.image f) := by
    simpa [hcong] using h.symm
  have hA : 0 < (S.image (fun a => f a + 1)).min' (hS.image (fun a => f a + 1)) := by
    rw [Finset.lt_min'_iff]
    intro y hy
    rcases (Finset.mem_image.mp hy) with ⟨a, ha, rfl⟩
    omega
  omega

/-- Flipping y at a zero column shifts the minimum over S by exactly ∓1. -/
lemma dRowMin_flip_eq {n : ℕ} (C : Code n) (S : Finset (Fin 4)) (hS : S.Nonempty)
    (t : Fin n) (y : Word n) (hcol : C t = col0) :
    (y t = true → dRowMin C S hS (flipBit t y) = dRowMin C S hS y - 1) ∧
      (y t = false → dRowMin C S hS (flipBit t y) = dRowMin C S hS y + 1) := by
  constructor
  · intro hyt
    unfold dRowMin
    have hshift : (S.image (fun i => dRow C i (flipBit t y))).min'
          (hS.image (fun i => dRow C i (flipBit t y))) =
        (S.image (fun i => dRow C i y)).min' (hS.image (fun i => dRow C i y)) - 1 := by
      have hcong : S.image (fun i => dRow C i (flipBit t y)) =
          S.image (fun i => dRow C i y - 1) := by
        apply Finset.image_congr
        intro i _
        exact (dRow_flip_zero C t y hcol i).1 hyt
      calc
        (S.image (fun i => dRow C i (flipBit t y))).min'
              (hS.image (fun i => dRow C i (flipBit t y)))
            = (S.image (fun i => dRow C i y - 1)).min'
                (hS.image (fun i => dRow C i y - 1)) := by
                simp [hcong]
        _ = (S.image (fun i => dRow C i y)).min' (hS.image (fun i => dRow C i y)) - 1 :=
              min_image_sub_one hS
    rw [hshift]
  · intro hyt
    unfold dRowMin
    have hshift : (S.image (fun i => dRow C i (flipBit t y))).min'
          (hS.image (fun i => dRow C i (flipBit t y))) =
        (S.image (fun i => dRow C i y)).min' (hS.image (fun i => dRow C i y)) + 1 := by
      have hcong : S.image (fun i => dRow C i (flipBit t y)) =
          S.image (fun i => dRow C i y + 1) := by
        apply Finset.image_congr
        intro i _
        exact (dRow_flip_zero C t y hcol i).2 hyt
      calc
        (S.image (fun i => dRow C i (flipBit t y))).min'
              (hS.image (fun i => dRow C i (flipBit t y)))
            = (S.image (fun i => dRow C i y + 1)).min'
                (hS.image (fun i => dRow C i y + 1)) := by
                simp [hcong]
        _ = (S.image (fun i => dRow C i y)).min' (hS.image (fun i => dRow C i y)) + 1 :=
              min_image_add_one hS
    rw [hshift]

/-! ## The 0 → s' comparison -/

/-- Flipping the same bit of both words preserves their distance. -/
lemma hammingDist_flip_flip {n : ℕ} (x y : Word n) (t : Fin n) :
    hammingDist (flipBit t x) (flipBit t y) = hammingDist x y := by
  unfold hammingDist
  congr 1
  funext u
  by_cases ht : u = t <;> simp [bitXor, flipBit, ht]

/-- Replacing the t-th bit of x by b changes the distance to y exactly as
flipping y's t-th bit when b = true, and not at all when b = false. -/
lemma hammingDist_set_bit {n : ℕ} (x : Word n) (t : Fin n) (y : Word n) (b : Bool)
    (hx0 : x t = false) :
    hammingDist (fun u => if u = t then b else x u) y =
      if b = true then hammingDist x (flipBit t y) else hammingDist x y := by
  by_cases hb : b = true
  · have hx : (fun u : Fin n => if u = t then true else x u) = flipBit t x := by
      funext u
      by_cases ht : u = t
      · simp [flipBit, ht, hx0]
      · simp [flipBit, ht]
    rw [hb, hx, ← hammingDist_flip_flip, flipBit_involutive]
    simp
  · have hbf : b = false := by
      cases b <;> simp at hb ⊢
    have hx : (fun u : Fin n => if u = t then false else x u) = x := by
      funext u
      by_cases ht : u = t
      · simp [ht, hx0]
      · simp [ht]
    rw [hbf, hx]
    simp

/-- Replacing the 0-column at t by s' changes row i only if s' has bit 1 there;
then the new distance is the old distance at the flipped word. -/
lemma dRow_replace_zero {n : ℕ} (C : Code n) (t : Fin n) (s' : Column) (hcol : C t = col0)
    (y : Word n) :
    ∀ i : Fin 4, dRow (replaceColumn C t s') i y =
      if s' i then dRow C i (flipBit t y) else dRow C i y := by
  intro i
  rw [dRow_eq_hammingDist, dRow_eq_hammingDist]
  have hrow : row (replaceColumn C t s') i = fun u : Fin n => if u = t then s' i else row C i u := by
    funext u
    by_cases ht : u = t <;> simp [row, replaceColumn, colBit, ht]
  rw [hrow]
  have ht0 : (row C i) t = false := by
    unfold row
    simp [hcol, colBit, col0]
  by_cases hb : s' i = true
  · have hd := hammingDist_set_bit (row C i) t y (s' i) ht0
    rw [hd, hb]
    simp
  · have hs'f : s' i = false := by
      by_contra h
      have htrue : s' i = true := by
        cases hs : s' i
        · exfalso
          exact h hs
        · simp
      exact hb htrue
    have hd := hammingDist_set_bit (row C i) t y (s' i) ht0
    rw [hd, hs'f]
    simp
    rw [dRow_eq_hammingDist]

/-- d_C'(y) = min(d_O(y), d_P(F_t y)) for the 0 → s' change (paper eq. dcp). -/
lemma dCode_replace_0 {n : ℕ} (C : Code n) (t : Fin n) (s' : Column) (hcol : C t = col0)
    (hO : (colZeros s').Nonempty) (hP : (colOnes s').Nonempty) (y : Word n) :
    dCode (replaceColumn C t s') y = min (dOc C s' hO y) (dPc C s' hP (flipBit t y)) := by
  let C' : Code n := replaceColumn C t s'
  have hunion : (Finset.univ : Finset (Fin 4)) = colZeros s' ∪ colOnes s' := by
    ext i
    simp [colZeros, colOnes]
  have hz : dRowMin C' (colZeros s') hO y = dRowMin C (colZeros s') hO y := by
    unfold dRowMin
    have hcong : (colZeros s').image (fun i => dRow C' i y) =
        (colZeros s').image (fun i => dRow C i y) := by
      apply Finset.image_congr
      intro i hi
      have hs' : ¬ s' i := (Finset.mem_filter.mp hi).2
      exact (dRow_replace_zero C t s' hcol y i).trans (by simp [hs'])
    simp [hcong]
  have hp : dRowMin C' (colOnes s') hP y = dRowMin C (colOnes s') hP (flipBit t y) := by
    unfold dRowMin
    have hcong : (colOnes s').image (fun i => dRow C' i y) =
        (colOnes s').image (fun i => dRow C i (flipBit t y)) := by
      apply Finset.image_congr
      intro i hi
      have hs' : s' i := (Finset.mem_filter.mp hi).2
      exact (dRow_replace_zero C t s' hcol y i).trans (by simp [hs'])
    simp [hcong]
  calc
    dCode C' y = dRowMin C' (Finset.univ : Finset (Fin 4)) Finset.univ_nonempty y :=
      (dRowMin_univ C' y).symm
    _ = dRowMin C' (colZeros s' ∪ colOnes s')
        (by rcases hO with ⟨i, hi⟩; exact ⟨i, Finset.mem_union_left (colOnes s') hi⟩) y := by
          simp [hunion]
    _ = min (dRowMin C' (colZeros s') hO y) (dRowMin C' (colOnes s') hP y) := by
          simpa using dRowMin_union C' (colZeros s') (colOnes s') hO hP y
    _ = min (dOc C s' hO y) (dPc C s' hP (flipBit t y)) := by
          rw [hz, hp]
          rfl

/-- The involution g0: identity on d_O ≤ d_P, flip otherwise. -/
def g0 {n : ℕ} (C : Code n) (s' : Column) (hO : (colZeros s').Nonempty)
    (hP : (colOnes s').Nonempty) (t : Fin n) (y : Word n) : Word n :=
  if dOc C s' hO y ≤ dPc C s' hP y then y else flipBit t y

/-- Every row distance is at least one when y has bit 1 at a zero column. -/
lemma dRowMin_ge_one {n : ℕ} (C : Code n) (S : Finset (Fin 4)) (hS : S.Nonempty)
    (t : Fin n) (y : Word n) (hcol : C t = col0) (hyt : y t = true) :
    1 ≤ dRowMin C S hS y := by
  unfold dRowMin
  have hm : (S.image (fun i => dRow C i y)).min' (hS.image (fun i => dRow C i y)) ∈
      S.image (fun i => dRow C i y) := Finset.min'_mem _ _
  rcases (Finset.mem_image.mp hm) with ⟨i, hi, hfi⟩
  rw [← hfi]
  have hd : 1 ≤ dRow C i y := by
    rw [dRow_eq_hammingDist]
    have hneq : row C i ≠ y := by
      intro h
      have : row C i t = y t := congrFun h t
      have hrowt : row C i t = false := by
        unfold row
        simp [hcol, colBit, col0]
      simp [hrowt, hyt] at this
    by_contra hle
    have h0 : hammingDist (row C i) y = 0 := by omega
    exact hneq ((hammingDist_eq_zero_iff (row C i) y).mp h0)
  omega

/-- g0 is an involution. -/
lemma g0_involutive {n : ℕ} (C : Code n) (s' : Column) (hO : (colZeros s').Nonempty)
    (hP : (colOnes s').Nonempty) (t : Fin n) (y : Word n) (hcol : C t = col0) :
    g0 C s' hO hP t (g0 C s' hO hP t y) = y := by
  by_cases hle : dOc C s' hO y ≤ dPc C s' hP y
  · simp [g0, hle]
  · have hgt : dPc C s' hP y < dOc C s' hO y := lt_of_not_ge hle
    have hg0 : g0 C s' hO hP t y = flipBit t y := by
      simp [g0, hle]
    rw [hg0]
    by_cases hyt : y t = true
    · have hdO := (dRowMin_flip_eq C (colZeros s') hO t y hcol).1 hyt
      have hdP := (dRowMin_flip_eq C (colOnes s') hP t y hcol).1 hyt
      have hgt' : dRowMin C (colOnes s') hP y < dRowMin C (colZeros s') hO y := by
        simpa [dOc, dPc] using hgt
      have hle' : ¬ dOc C s' hO (flipBit t y) ≤ dPc C s' hP (flipBit t y) := by
        unfold dOc dPc
        rw [hdO, hdP]
        have hPge : 1 ≤ dRowMin C (colOnes s') hP y :=
          dRowMin_ge_one C (colOnes s') hP t y hcol hyt
        omega
      simp [g0, hle', flipBit_involutive]
    · have hytf : y t = false := by
        simpa using hyt
      have hdO' := (dRowMin_flip_eq C (colZeros s') hO t y hcol).2 hytf
      have hdP' := (dRowMin_flip_eq C (colOnes s') hP t y hcol).2 hytf
      have hgt' : dRowMin C (colOnes s') hP y < dRowMin C (colZeros s') hO y := by
        simpa [dOc, dPc] using hgt
      have hle' : ¬ dOc C s' hO (flipBit t y) ≤ dPc C s' hP (flipBit t y) := by
        unfold dOc dPc
        rw [hdO', hdP']
        omega
      simp [g0, hle', flipBit_involutive]

/-- The set S of words where the new code is strictly closer: y_t = 1 and
d_O(y) = d_P(y) (paper eq. 6). -/
def Y3c {n : ℕ} (C : Code n) (s' : Column) (hO : (colZeros s').Nonempty)
    (hP : (colOnes s').Nonempty) (t : Fin n) (y : Word n) : Prop :=
  y t = true ∧ dOc C s' hO y = dPc C s' hP y

instance decY3c {n : ℕ} (C : Code n) (s' : Column) (hO : (colZeros s').Nonempty)
    (hP : (colOnes s').Nonempty) (t : Fin n) (y : Word n) : Decidable (Y3c C s' hO hP t y) := by
  unfold Y3c
  infer_instance

/-- d_C(y) = min(d_O(y), d_P(y)) for the 0 → s' split. -/
lemma dCode_eq_min_dOc_dPc {n : ℕ} (C : Code n) (s' : Column) (hO : (colZeros s').Nonempty)
    (hP : (colOnes s').Nonempty) (y : Word n) :
    dCode C y = min (dOc C s' hO y) (dPc C s' hP y) := by
  have hunion : (Finset.univ : Finset (Fin 4)) = colZeros s' ∪ colOnes s' := by
    ext i
    simp [colZeros, colOnes]
  calc
    dCode C y = dRowMin C (Finset.univ : Finset (Fin 4)) Finset.univ_nonempty y :=
      (dRowMin_univ C y).symm
    _ = dRowMin C (colZeros s' ∪ colOnes s')
        (by rcases hO with ⟨i, hi⟩; exact ⟨i, Finset.mem_union_left (colOnes s') hi⟩) y := by
          simp [hunion]
    _ = min (dRowMin C (colZeros s') hO y) (dRowMin C (colOnes s') hP y) := by
          simpa using dRowMin_union C (colZeros s') (colOnes s') hO hP y
    _ = min (dOc C s' hO y) (dPc C s' hP y) := by rfl

/-- Words in S (paper eq. 6) come one step closer under the new code. -/
lemma zero_closer {n : ℕ} (C : Code n) (t : Fin n) (s' : Column) (hcol : C t = col0)
    (hO : (colZeros s').Nonempty) (hP : (colOnes s').Nonempty) (y : Word n)
    (hS : Y3c C s' hO hP t y) :
    dCode C y = dCode (replaceColumn C t s') (g0 C s' hO hP t y) + 1 := by
  rcases hS with ⟨hyt, hEq⟩
  have hdC : dCode C y = dOc C s' hO y := by
    rw [dCode_eq_min_dOc_dPc C s' hO hP, hEq]
    simp
  have hg0 : g0 C s' hO hP t y = y := by
    simp [g0, hEq]
  have hdP := (dRowMin_flip_eq C (colOnes s') hP t y hcol).1 hyt
  have hdC' : dCode (replaceColumn C t s') y = dOc C s' hO y - 1 := by
    rw [dCode_replace_0 C t s' hcol hO hP y]
    change min (dOc C s' hO y) (dRowMin C (colOnes s') hP (flipBit t y)) = dOc C s' hO y - 1
    rw [hdP]
    change min (dOc C s' hO y) (dPc C s' hP y - 1) = dOc C s' hO y - 1
    rw [hEq.symm]
    have hPge : 1 ≤ dOc C s' hO y := by
      rw [hEq]
      exact dRowMin_ge_one C (colOnes s') hP t y hcol hyt
    omega
  rw [hdC, hg0, hdC']
  have hPge : 1 ≤ dOc C s' hO y := by
    rw [hEq]
    exact dRowMin_ge_one C (colOnes s') hP t y hcol hyt
  omega

/-- Words outside S keep their distance to the code under g0. -/
lemma zero_equal_off {n : ℕ} (C : Code n) (t : Fin n) (s' : Column) (hcol : C t = col0)
    (hO : (colZeros s').Nonempty) (hP : (colOnes s').Nonempty) (y : Word n)
    (hnot : ¬ Y3c C s' hO hP t y) :
    dCode C y = dCode (replaceColumn C t s') (g0 C s' hO hP t y) := by
  have hdC : dCode C y = min (dOc C s' hO y) (dPc C s' hP y) :=
    dCode_eq_min_dOc_dPc C s' hO hP y
  by_cases hyt : y t = true
  · have hneq : dOc C s' hO y ≠ dPc C s' hP y := by
      intro h
      exact hnot ⟨hyt, h⟩
    by_cases hle : dOc C s' hO y ≤ dPc C s' hP y
    · have hlt : dOc C s' hO y < dPc C s' hP y := lt_of_le_of_ne hle hneq
      have hg0 : g0 C s' hO hP t y = y := by simp [g0, hle]
      have hdP := (dRowMin_flip_eq C (colOnes s') hP t y hcol).1 hyt
      have hdC' : dCode (replaceColumn C t s') y = dOc C s' hO y := by
        rw [dCode_replace_0 C t s' hcol hO hP y]
        change min (dOc C s' hO y) (dRowMin C (colOnes s') hP (flipBit t y)) = dOc C s' hO y
        rw [hdP]
        change min (dOc C s' hO y) (dPc C s' hP y - 1) = dOc C s' hO y
        have hle' : dOc C s' hO y ≤ dPc C s' hP y - 1 := by omega
        rw [min_eq_left hle']
      rw [hdC, hg0, hdC']
      rw [min_eq_left hle]
    · have hgt : dPc C s' hP y < dOc C s' hO y := lt_of_not_ge hle
      have hg0 : g0 C s' hO hP t y = flipBit t y := by simp [g0, hle]
      have hdO := (dRowMin_flip_eq C (colZeros s') hO t y hcol).1 hyt
      have hdC' : dCode (replaceColumn C t s') (flipBit t y) = dPc C s' hP y := by
        rw [dCode_replace_0 C t s' hcol hO hP (flipBit t y)]
        change min (dRowMin C (colZeros s') hO (flipBit t y))
            (dPc C s' hP (flipBit t (flipBit t y))) = dPc C s' hP y
        rw [hdO, flipBit_involutive]
        change min (dOc C s' hO y - 1) (dPc C s' hP y) = dPc C s' hP y
        have hle' : dPc C s' hP y ≤ dOc C s' hO y - 1 := by omega
        rw [min_eq_right hle']
      rw [hdC, hg0, hdC']
      rw [min_eq_right (le_of_lt hgt)]
  · have hytf : y t = false := by
      simpa using hyt
    by_cases hle : dOc C s' hO y ≤ dPc C s' hP y
    · have hg0 : g0 C s' hO hP t y = y := by simp [g0, hle]
      have hdP := (dRowMin_flip_eq C (colOnes s') hP t y hcol).2 hytf
      have hdC' : dCode (replaceColumn C t s') y = dOc C s' hO y := by
        rw [dCode_replace_0 C t s' hcol hO hP y]
        change min (dOc C s' hO y) (dRowMin C (colOnes s') hP (flipBit t y)) = dOc C s' hO y
        rw [hdP]
        change min (dOc C s' hO y) (dPc C s' hP y + 1) = dOc C s' hO y
        rw [min_eq_left (le_trans hle (by omega))]
      rw [hdC, hg0, hdC']
      rw [min_eq_left hle]
    · have hgt : dPc C s' hP y < dOc C s' hO y := lt_of_not_ge hle
      have hg0 : g0 C s' hO hP t y = flipBit t y := by simp [g0, hle]
      have hdO := (dRowMin_flip_eq C (colZeros s') hO t y hcol).2 hytf
      have hdC' : dCode (replaceColumn C t s') (flipBit t y) = dPc C s' hP y := by
        rw [dCode_replace_0 C t s' hcol hO hP (flipBit t y)]
        change min (dRowMin C (colZeros s') hO (flipBit t y))
            (dPc C s' hP (flipBit t (flipBit t y))) = dPc C s' hP y
        rw [hdO, flipBit_involutive]
        change min (dOc C s' hO y + 1) (dPc C s' hP y) = dPc C s' hP y
        rw [min_eq_right (by omega)]
      rw [hdC, hg0, hdC']
      rw [min_eq_right (le_of_lt hgt)]

/-- Theorem `thm:0column` (Theorem 6) engine: replacing a 0-column never worsens λ, and
equality holds exactly when the set Y3c (eq. 6) is empty. -/
theorem zero_column_better {n : ℕ} (C : Code n) (t : Fin n) (s' : Column)
    (hcol : C t = col0) (hO : (colZeros s').Nonempty) (hP : (colOnes s').Nonempty) :
    UniversalBetter (replaceColumn C t s') C ∧
      (UniversalEqual (replaceColumn C t s') C ↔ ∀ y : Word n, ¬ Y3c C s' hO hP t y) := by
  let S : Finset (Word n) := Finset.univ.filter (Y3c C s' hO hP t)
  have hbij : Function.Bijective (g0 C s' hO hP t) := by
    constructor
    · intro a b hab
      calc
        a = g0 C s' hO hP t (g0 C s' hO hP t a) := (g0_involutive C s' hO hP t a hcol).symm
        _ = g0 C s' hO hP t (g0 C s' hO hP t b) := by rw [hab]
        _ = b := g0_involutive C s' hO hP t b hcol
    · intro z
      refine ⟨g0 C s' hO hP t z, ?_⟩
      exact g0_involutive C s' hO hP t z hcol
  let g : Word n ≃ Word n := Equiv.ofBijective (g0 C s' hO hP t) hbij
  have hgt : ∀ y : Word n, y ∈ S → dCode C y > dCode (replaceColumn C t s') (g y) := by
    intro y hy
    have hS : Y3c C s' hO hP t y := (Finset.mem_filter.mp hy).2
    have h := zero_closer C t s' hcol hO hP y hS
    have hlt : dCode (replaceColumn C t s') (g0 C s' hO hP t y) < dCode C y := by
      rw [h]
      omega
    simpa [g] using hlt
  have heq : ∀ y : Word n, y ∉ S → dCode C y = dCode (replaceColumn C t s') (g y) := by
    intro y hy
    have hnot : ¬ Y3c C s' hO hP t y := by
      intro h
      exact hy (Finset.mem_filter.mpr ⟨by simp, h⟩)
    simpa [g] using zero_equal_off C t s' hcol hO hP y hnot
  constructor
  · exact compare_bij C (replaceColumn C t s') S g hgt heq
  · constructor
    · intro heq2 y hS
      have hne : ∃ y : Word n, y ∈ S := ⟨y, Finset.mem_filter.mpr ⟨by simp, hS⟩⟩
      have hstrict := compare_bij_strict C (replaceColumn C t s') S g hgt heq hne
      have hgt' : lambda (replaceColumn C t s') (1 / 4 : ℝ) > lambda C (1 / 4) :=
        hstrict (1 / 4) (by norm_num) (by norm_num)
      have heq' : lambda (replaceColumn C t s') (1 / 4 : ℝ) = lambda C (1 / 4) :=
        heq2 (1 / 4) (by norm_num) (by norm_num)
      exact (lt_irrefl _ (hgt'.trans_eq heq')).elim
    · intro hy3
      have heqall : ∀ y : Word n, dCode C y = dCode (replaceColumn C t s') (g y) := by
        intro y
        by_cases hy : y ∈ S
        · exfalso
          exact hy3 y (Finset.mem_filter.mp hy).2
        · exact heq y hy
      exact compare_bij_eq C (replaceColumn C t s') g heqall

/-- Nonempty `Y3c` forces strict improvement (paper `thm:0column` (Theorem 6) (2) engine). -/
lemma zero_column_strict_of_y3c {n : ℕ} (C : Code n) (t : Fin n) (s' : Column)
    (hcol : C t = col0) (hO : (colZeros s').Nonempty) (hP : (colOnes s').Nonempty)
    {y : Word n} (hy : Y3c C s' hO hP t y) :
    UniversalStrictBetter (replaceColumn C t s') C := by
  let S : Finset (Word n) := Finset.univ.filter (Y3c C s' hO hP t)
  have hbij : Function.Bijective (g0 C s' hO hP t) := by
    constructor
    · intro a b hab
      calc
        a = g0 C s' hO hP t (g0 C s' hO hP t a) := (g0_involutive C s' hO hP t a hcol).symm
        _ = g0 C s' hO hP t (g0 C s' hO hP t b) := by rw [hab]
        _ = b := g0_involutive C s' hO hP t b hcol
    · intro z
      refine ⟨g0 C s' hO hP t z, ?_⟩
      exact g0_involutive C s' hO hP t z hcol
  let g : Word n ≃ Word n := Equiv.ofBijective (g0 C s' hO hP t) hbij
  have hgt : ∀ y : Word n, y ∈ S → dCode C y > dCode (replaceColumn C t s') (g y) := by
    intro y hyS
    have hS : Y3c C s' hO hP t y := (Finset.mem_filter.mp hyS).2
    have h := zero_closer C t s' hcol hO hP y hS
    have hlt : dCode (replaceColumn C t s') (g0 C s' hO hP t y) < dCode C y := by
      rw [h]
      omega
    simpa [g] using hlt
  have heq : ∀ y : Word n, y ∉ S → dCode C y = dCode (replaceColumn C t s') (g y) := by
    intro y hyS
    have hnot : ¬ Y3c C s' hO hP t y := by
      intro hS
      exact hyS (Finset.mem_filter.mpr ⟨by simp, hS⟩)
    simpa [g] using zero_equal_off C t s' hcol hO hP y hnot
  exact compare_bij_strict C (replaceColumn C t s') S g hgt heq
    ⟨y, Finset.mem_filter.mpr ⟨by simp, hy⟩⟩

/-! ## `thm:0column` (Theorem 6) (1): the C0 code has no words in Y3c -/

/-- The per-type weight is at most the per-type count. -/
lemma w_i_le_count {n : ℕ} (C : Code n) (i : ℕ) (y : Word n) : w_i C i y ≤ count C i := by
  rw [w_i_eq_card_onesOn]
  exact le_trans (Finset.card_le_card (by
    intro t ht
    exact (Finset.mem_filter.mp ht).1)) (le_of_eq (fiber_card_eq_count C i))

/-- The per-type weight vanishes when the type does not occur. -/
lemma w_i_eq_zero_of_count_zero {n : ℕ} (C : Code n) (i : ℕ) (y : Word n) (h : count C i = 0) :
    w_i C i y = 0 := by
  rw [w_i_eq_card_onesOn]
  have hfib : (fiber C i).card = 0 := by
    rw [fiber_card_eq_count, h]
  have hfib' : fiber C i = ∅ := Finset.card_eq_zero.mp hfib
  rw [hfib']
  simp [onesOn]

/-- d_j(y) from the types in S only, when all columns are of types in S. -/
lemma dRow_eq_sum_types {n : ℕ} (C : Code n) (j : Fin 4) (y : Word n) (S : Finset ℕ)
    (hSle : S ⊆ Finset.Icc 0 15) (hS : ∀ t : Fin n, colVal (C t) ∈ S) :
    dRow C j y = ∑ i ∈ S, if i.testBit (3 - j.val) then count C i - w_i C i y else w_i C i y := by
  rw [dRow_eq_sum]
  symm
  apply Finset.sum_subset hSle
  intro i hi hnot
  have hcount : count C i = 0 := by
    rw [count_eq_card, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro t ht
    have hcv : colVal (C t) = i := (Finset.mem_filter.mp ht).2
    exact hnot (by simpa [hcv] using hS t)
  have hw : w_i C i y = 0 := w_i_eq_zero_of_count_zero C i y hcount
  simp [hcount, hw]

/-- Row distances of the C0 code (columns only of types 0, 5, 6) — paper
eqs. (0columnc) and (0columnd), published (140)-(143). -/
-- native_decide: Mechanical · n=any · checked 2026-08-27
lemma dRow_C0_formula {n : ℕ} (C : Code n)
    (hC : ∀ u : Fin n, colVal (C u) = 0 ∨ colVal (C u) = 5 ∨ colVal (C u) = 6) :
    ∀ y : Word n,
      dRow C 0 y = w_i C 0 y + w_i C 5 y + w_i C 6 y ∧
      dRow C 1 y = w_i C 0 y + (count C 5 - w_i C 5 y) + (count C 6 - w_i C 6 y) ∧
      dRow C 2 y = w_i C 0 y + w_i C 5 y + (count C 6 - w_i C 6 y) ∧
      dRow C 3 y = w_i C 0 y + (count C 5 - w_i C 5 y) + w_i C 6 y := by
  intro y
  have hS : ∀ t : Fin n, colVal (C t) ∈ ({0, 5, 6} : Finset ℕ) := by
    intro t
    rcases hC t with h | h | h <;> simp [h]
  have hSle : ({0, 5, 6} : Finset ℕ) ⊆ Finset.Icc 0 15 := by
    intro i hi
    simp at hi ⊢
    omega
  have hsum : ∀ j : Fin 4, dRow C j y = ∑ i ∈ ({0, 5, 6} : Finset ℕ),
      if i.testBit (3 - j.val) then count C i - w_i C i y else w_i C i y := by
    intro j
    exact dRow_eq_sum_types C j y {0, 5, 6} hSle hS
  have hb03 : (0 : ℕ).testBit 3 = false := by native_decide
  have hb02 : (0 : ℕ).testBit 2 = false := by native_decide
  have hb01 : (0 : ℕ).testBit 1 = false := by native_decide
  have hb00 : (0 : ℕ).testBit 0 = false := by native_decide
  have hb53 : (5 : ℕ).testBit 3 = false := by native_decide
  have hb52 : (5 : ℕ).testBit 2 = true := by native_decide
  have hb51 : (5 : ℕ).testBit 1 = false := by native_decide
  have hb50 : (5 : ℕ).testBit 0 = true := by native_decide
  have hb63 : (6 : ℕ).testBit 3 = false := by native_decide
  have hb62 : (6 : ℕ).testBit 2 = true := by native_decide
  have hb61 : (6 : ℕ).testBit 1 = true := by native_decide
  have hb60 : (6 : ℕ).testBit 0 = false := by native_decide
  have h0 : dRow C 0 y = w_i C 0 y + w_i C 5 y + w_i C 6 y := by
    rw [hsum (0 : Fin 4)]
    simp [Finset.sum_insert, hb03, hb53, hb63]
    ring
  have h1 : dRow C 1 y = w_i C 0 y + (count C 5 - w_i C 5 y) + (count C 6 - w_i C 6 y) := by
    rw [hsum (1 : Fin 4)]
    simp [Finset.sum_insert, hb02, hb52, hb62]
    ring
  have h2 : dRow C 2 y = w_i C 0 y + w_i C 5 y + (count C 6 - w_i C 6 y) := by
    rw [hsum (2 : Fin 4)]
    simp [Finset.sum_insert, hb01, hb51, hb61]
    ring
  have h3 : dRow C 3 y = w_i C 0 y + (count C 5 - w_i C 5 y) + w_i C 6 y := by
    rw [hsum (3 : Fin 4)]
    simp [Finset.sum_insert]
    ring
  exact ⟨h0, h1, h2, h3⟩

/-- For the C0 code with |5| and |6| odd, no two rows share a distance value
that is no larger than the other two (paper `thm:0column` (Theorem 6) proof). -/
lemma C0_pair_contradiction {n : ℕ} (C : Code n)
    (hC : ∀ u : Fin n, colVal (C u) = 0 ∨ colVal (C u) = 5 ∨ colVal (C u) = 6)
    (h5 : Odd (count C 5)) (h6 : Odd (count C 6)) (y : Word n) :
    (dRow C 0 y ≠ dRow C 2 y) ∧
    (dRow C 0 y ≠ dRow C 3 y) ∧
    (dRow C 1 y ≠ dRow C 2 y) ∧
    (dRow C 1 y ≠ dRow C 3 y) ∧
    (¬ (dRow C 0 y = dRow C 1 y ∧ dRow C 0 y ≤ dRow C 2 y ∧ dRow C 0 y ≤ dRow C 3 y)) ∧
    (¬ (dRow C 2 y = dRow C 3 y ∧ dRow C 2 y ≤ dRow C 0 y ∧ dRow C 2 y ≤ dRow C 1 y)) := by
  rcases dRow_C0_formula C hC y with ⟨h0, h1, h2, h3⟩
  constructor
  · intro h
    have hsum : dRow C 0 y + dRow C 2 y = 2 * w_i C 0 y + 2 * w_i C 5 y + count C 6 := by
      rw [h0, h2]
      omega
    have hodd : Odd (dRow C 0 y + dRow C 2 y) := by
      rw [hsum]
      exact Even.add_odd ⟨w_i C 0 y + w_i C 5 y, by ring⟩ h6
    have hev : Even (dRow C 0 y + dRow C 2 y) := by
      exact ⟨dRow C 0 y, by rw [← h]⟩
    rcases hodd with ⟨k, hk⟩
    rcases hev with ⟨r, hr⟩
    omega
  · constructor
    · intro h
      have hsum : dRow C 0 y + dRow C 3 y = 2 * w_i C 0 y + count C 5 + 2 * w_i C 6 y := by
        rw [h0, h3]
        omega
      have hodd : Odd (dRow C 0 y + dRow C 3 y) := by
        rw [hsum]
        have hre : 2 * w_i C 0 y + count C 5 + 2 * w_i C 6 y =
            (2 * w_i C 0 y + 2 * w_i C 6 y) + count C 5 := by ring
        rw [hre]
        exact Even.add_odd ⟨w_i C 0 y + w_i C 6 y, by ring⟩ h5
      have hev : Even (dRow C 0 y + dRow C 3 y) := by
        exact ⟨dRow C 0 y, by rw [← h]⟩
      rcases hodd with ⟨k, hk⟩
      rcases hev with ⟨r, hr⟩
      omega
    · constructor
      · intro h
        have hsum : dRow C 1 y + dRow C 2 y = 2 * w_i C 0 y + count C 5 + 2 * (count C 6 - w_i C 6 y) := by
          rw [h1, h2]
          omega
        have hodd : Odd (dRow C 1 y + dRow C 2 y) := by
          rw [hsum]
          have hre : 2 * w_i C 0 y + count C 5 + 2 * (count C 6 - w_i C 6 y) =
              (2 * w_i C 0 y + 2 * (count C 6 - w_i C 6 y)) + count C 5 := by ring
          rw [hre]
          exact Even.add_odd ⟨w_i C 0 y + (count C 6 - w_i C 6 y), by ring⟩ h5
        have hev : Even (dRow C 1 y + dRow C 2 y) := by
          exact ⟨dRow C 1 y, by rw [← h]⟩
        rcases hodd with ⟨k, hk⟩
        rcases hev with ⟨r, hr⟩
        omega
      · constructor
        · intro h
          have hsum : dRow C 1 y + dRow C 3 y = 2 * w_i C 0 y + 2 * (count C 5 - w_i C 5 y) + count C 6 := by
            rw [h1, h3]
            omega
          have hodd : Odd (dRow C 1 y + dRow C 3 y) := by
            rw [hsum]
            exact Even.add_odd ⟨w_i C 0 y + (count C 5 - w_i C 5 y), by ring⟩ h6
          have hev : Even (dRow C 1 y + dRow C 3 y) := by
            exact ⟨dRow C 1 y, by rw [← h]⟩
          rcases hodd with ⟨k, hk⟩
          rcases hev with ⟨r, hr⟩
          omega
        · constructor
          · rintro ⟨h, hle2, hle3⟩
            have htwo : count C 5 = 2 * w_i C 5 y := by
              rw [h0, h1] at h
              rw [h0, h2] at hle2
              rw [h0, h3] at hle3
              omega
            rcases h5 with ⟨k5, hk5⟩
            omega
          · rintro ⟨h, hle0, hle1⟩
            have htwo : count C 5 = 2 * w_i C 5 y := by
              rw [h2, h3] at h
              rw [h2, h0] at hle0
              rw [h2, h1] at hle1
              omega
            rcases h5 with ⟨k5, hk5⟩
            omega

/-- The C0 code has no words in Y3c, for any split (paper `thm:0column` (Theorem 6) (1)). -/
lemma y3c_empty_C0 {n : ℕ} (C : Code n) (t : Fin n) (s' : Column)
    (hO : (colZeros s').Nonempty) (hP : (colOnes s').Nonempty)
    (hC : ∀ u : Fin n, colVal (C u) = 0 ∨ colVal (C u) = 5 ∨ colVal (C u) = 6)
    (h5 : Odd (count C 5)) (h6 : Odd (count C 6)) :
    ∀ y : Word n, ¬ Y3c C s' hO hP t y := by
  intro y hy
  rcases hy with ⟨hyt, hEq⟩
  have hdisj : Disjoint (colZeros s') (colOnes s') := by
    rw [Finset.disjoint_left]
    intro k hk hk'
    exact (Finset.mem_filter.mp hk).2 (Finset.mem_filter.mp hk').2
  have huniv : (Finset.univ : Finset (Fin 4)) = colZeros s' ∪ colOnes s' := by
    ext k
    simp [colZeros, colOnes]
  have hmemO := Finset.min'_mem ((colZeros s').image (fun i => dRow C i y))
    (hO.image (fun i => dRow C i y))
  rcases (Finset.mem_image.mp hmemO) with ⟨i, hiO, hdi⟩
  have hmemP := Finset.min'_mem ((colOnes s').image (fun i => dRow C i y))
    (hP.image (fun i => dRow C i y))
  rcases (Finset.mem_image.mp hmemP) with ⟨j, hjP, hdj⟩
  have hEqO : dRow C i y = dOc C s' hO y := by
    simpa [dOc, dRowMin] using hdi
  have hEqP : dRow C j y = dPc C s' hP y := by
    simpa [dPc, dRowMin] using hdj
  have hEq' : dRow C i y = dRow C j y := by
    rw [hEqO, hEq, hEqP]
  have hmin : ∀ k : Fin 4, dRow C i y ≤ dRow C k y := by
    intro k
    by_cases hk : k ∈ colZeros s'
    · have hle : dOc C s' hO y ≤ dRow C k y := by
        unfold dOc
        exact Finset.min'_le ((colZeros s').image (fun i => dRow C i y)) (dRow C k y)
          (Finset.mem_image.mpr ⟨k, hk, rfl⟩)
      rw [hEqO]
      exact hle
    · have hk' : k ∈ colOnes s' := by
        have hunion : k ∈ colZeros s' ∪ colOnes s' := by
          simpa [huniv] using (Finset.mem_univ k)
        exact (Finset.mem_union.mp hunion).resolve_left hk
      have hle : dPc C s' hP y ≤ dRow C k y := by
        unfold dPc
        exact Finset.min'_le ((colOnes s').image (fun i => dRow C i y)) (dRow C k y)
          (Finset.mem_image.mpr ⟨k, hk', rfl⟩)
      rw [hEq', hEqP]
      exact hle
  have hij : i ≠ j := by
    intro h
    have : j ∈ colZeros s' := by simpa [h] using hiO
    exact (Finset.disjoint_left.mp hdisj) this hjP
  rcases C0_pair_contradiction C hC h5 h6 y with ⟨h02, h03, h12, h13, h01, h23⟩
  fin_cases i <;> fin_cases j
  · exfalso
    exact hij rfl
  · exfalso
    apply h01
    exact ⟨hEq', hmin 2, hmin 3⟩
  · exfalso
    exact h02 hEq'
  · exfalso
    exact h03 hEq'
  · exfalso
    apply h01
    refine ⟨hEq'.symm, ?_, ?_⟩
    · calc
        dRow C 0 y = dRow C 1 y := hEq'.symm
        _ ≤ dRow C 2 y := hmin 2
    · calc
        dRow C 0 y = dRow C 1 y := hEq'.symm
        _ ≤ dRow C 3 y := hmin 3
  · exfalso
    exact hij rfl
  · exfalso
    exact h12 hEq'
  · exfalso
    exact h13 hEq'
  · exfalso
    exact h02 hEq'.symm
  · exfalso
    exact h12 hEq'.symm
  · exfalso
    exact hij rfl
  · exfalso
    apply h23
    exact ⟨hEq', hmin 0, hmin 1⟩
  · exfalso
    exact h03 hEq'.symm
  · exfalso
    exact h13 hEq'.symm
  · exfalso
    apply h23
    refine ⟨hEq'.symm, ?_, ?_⟩
    · calc
        dRow C 2 y = dRow C 3 y := hEq'.symm
        _ ≤ dRow C 0 y := hmin 0
    · calc
        dRow C 2 y = dRow C 3 y := hEq'.symm
        _ ≤ dRow C 1 y := hmin 1
  · exfalso
    exact hij rfl

/-- The all-ones column (the flip of col0). -/
def col15 : Column := fun _ => true

/-- Row-permuting by the identity is the identity. -/
lemma rowPermute_refl (c : Column) : rowPermute (Equiv.refl (Fin 4)) c = c := by
  funext j
  rfl

/-- `thm:0column` (Theorem 6) (1) for the C0 code: replacing a 0-column by any s' leaves
λ unchanged. -/
lemma zero_column_C0 {n : ℕ} (C : Code n) (t : Fin n) (h0 : C t = col0)
    (hC : ∀ u : Fin n, colVal (C u) = 0 ∨ colVal (C u) = 5 ∨ colVal (C u) = 6)
    (h5 : Odd (count C 5)) (h6 : Odd (count C 6)) :
    ∀ s' : Column, UniversalEqual (replaceColumn C t s') C := by
  intro s'
  by_cases hs0 : s' = col0
  · subst s'
    exact universalEqual_of_equivalent C (replaceColumn C t col0) (by
      have hrep : replaceColumn C t col0 = C := by
        funext u
        by_cases hu : u = t <;> simp [replaceColumn, hu, h0]
      rw [hrep]
      refine ⟨Equiv.refl (Fin 4), Equiv.refl (Fin n), fun _ => false, ?_⟩
      intro u
      simp [rowPermute_refl])
  · by_cases hs15 : s' = col15
    · subst s'
      exact universalEqual_of_equivalent C (replaceColumn C t col15) (by
        refine ⟨Equiv.refl (Fin 4), Equiv.refl (Fin n), fun u => u = t, ?_⟩
        intro u
        by_cases hu : u = t
        · subst u
          have hflip : flipCol col0 = col15 := by
            funext k
            simp [flipCol, col15, col0]
          simp [h0, hflip, rowPermute_refl, replaceColumn]
        · simp [hu, replaceColumn, rowPermute_refl])
    · have hO : (colZeros s').Nonempty := by
        rw [Finset.Nonempty]
        by_contra h
        have : s' = col15 := by
          funext k
          by_contra hk
          have hfalse : s' k = false := by
            cases hs : s' k
            · rfl
            · exact (hk hs).elim
          exfalso
          exact h ⟨k, by simp [colZeros, hfalse]⟩
        exact hs15 this
      have hP : (colOnes s').Nonempty := by
        rw [Finset.Nonempty]
        by_contra h
        have : s' = col0 := by
          funext k
          by_contra hk
          have htrue : s' k = true := by
            cases hs : s' k
            · exact (hk hs).elim
            · rfl
          exfalso
          exact h ⟨k, by simp [colOnes, htrue]⟩
        exact hs0 this
      have hb := zero_column_better C t s' h0 hO hP
      exact hb.2.mpr (y3c_empty_C0 C t s' hO hP hC h5 h6)

/-- Replacing a column commutes with code equivalence: the modified column at
the corresponding position is the transformed s'. -/
lemma equiv_replaceColumn {n : ℕ} {C C0 : Code n} (h : Equivalent C C0) (t : Fin n)
    (s' : Column) :
    ∃ t' : Fin n, ∃ s'' : Column,
      Equivalent (replaceColumn C t s') (replaceColumn C0 t' s'') := by
  rcases h with ⟨ρ, p, f, hh⟩
  refine ⟨p t, rowPermute ρ (if f t then flipCol s' else s'), ?_⟩
  refine ⟨ρ, p, f, ?_⟩
  intro u
  by_cases hu : u = t
  · subst u
    simp [replaceColumn]
  · have hpu : p u ≠ p t := by
      intro h
      exact hu (p.injective h)
    simp [replaceColumn, hu, hpu, hh u]

/-- Theorem `thm:0column` (Theorem 6) (1): if C is equivalent to the C0 code, then
replacing a 0-column by any s' leaves λ unchanged. -/
-- native_decide: Mechanical · n=any · checked 2026-08-27
theorem zero_column {n : ℕ} (C : Code n) (t : Fin n) (h0 : C t = col0)
    (hC0 : ∃ C0 : Code n, Equivalent C C0 ∧
      count C0 0 + count C0 5 + count C0 6 = n ∧
        Odd (count C0 5) ∧ Odd (count C0 6)) :
    ∀ s' : Column, UniversalEqual (replaceColumn C t s') C := by
  rcases hC0 with ⟨C0, hEq, hcnt, h5, h6⟩
  have hEq_full : Equivalent C C0 := hEq
  rcases hEq with ⟨ρ, p, f, hh⟩
  have hC0struct : ∀ u : Fin n, colVal (C0 u) = 0 ∨ colVal (C0 u) = 5 ∨ colVal (C0 u) = 6 := by
    intro u
    let i : ℕ := colVal (C0 u)
    have hcnti : 1 ≤ count C0 i := by
      have hmem : u ∈ (Finset.univ.filter fun t : Fin n => colVal (C0 t) = i) := by
        simp [i]
      have hcard : 1 ≤ (Finset.univ.filter fun t : Fin n => colVal (C0 t) = i).card := by
        exact Nat.succ_le_of_lt (Finset.card_pos.mpr ⟨u, hmem⟩)
      rw [count_eq_card]
      exact hcard
    by_contra h
    have hS : ({0, 5, 6} : Finset ℕ) ⊆ Finset.Icc 0 15 := by
      intro x hx
      simp at hx ⊢
      omega
    have hsumS : (∑ j ∈ ({0, 5, 6} : Finset ℕ), count C0 j) = n := by
      simp [Finset.sum_insert]
      omega
    have hsumAll : (∑ j ∈ Finset.Icc 0 15, count C0 j) = n := sum_counts_eq_n C0
    have hcomp : (∑ j ∈ Finset.Icc 0 15 \ ({0, 5, 6} : Finset ℕ), count C0 j) = 0 := by
      have hsplit : (∑ j ∈ Finset.Icc 0 15, count C0 j) =
          (∑ j ∈ ({0, 5, 6} : Finset ℕ), count C0 j) +
            ∑ j ∈ Finset.Icc 0 15 \ ({0, 5, 6} : Finset ℕ), count C0 j := by
        rw [← Finset.sum_sdiff hS]
        rw [add_comm]
      omega
    have hile : i ≤ 15 := by
      exact colVal_le_15 (C0 u)
    have hi : i ∈ Finset.Icc 0 15 \ ({0, 5, 6} : Finset ℕ) := by
      rw [Finset.mem_sdiff]
      constructor
      · simp [Finset.mem_Icc, hile]
      · intro hiS
        simp at hiS
        exact h hiS
    have hle : count C0 i ≤ ∑ j ∈ Finset.Icc 0 15 \ ({0, 5, 6} : Finset ℕ), count C0 j := by
      exact Finset.single_le_sum (by intro j _; exact Nat.zero_le _) hi
    have hzero : count C0 i = 0 := by omega
    omega
  intro s'
  have hEq' : Equivalent (replaceColumn C t s')
      (replaceColumn C0 (p t) (rowPermute ρ (if f t then flipCol s' else s'))) := by
    refine ⟨ρ, p, f, ?_⟩
    intro u
    by_cases hu : u = t
    · subst u
      simp [replaceColumn]
    · have hpu : p u ≠ p t := by
        intro h
        exact hu (p.injective h)
      simp [replaceColumn, hu, hpu, hh u]
  have h0' : C0 (p t) = col0 := by
    have hh' : C0 (p t) = rowPermute ρ (if f t then flipCol (C t) else C t) := hh t
    have hf : f t = false := by
      by_contra hft
      have hft' : f t = true := by
        cases hfb : f t
        · exfalso
          exact hft hfb
        · rfl
      have hc : colVal (C0 (p t)) = 15 := by
        have hsub : C0 (p t) = rowPermute ρ (flipCol col0) := by
          rw [hh', hft', h0]
          simp
        have hall : rowPermute ρ (flipCol col0) = col15 := by
          funext k
          simp [rowPermute, flipCol, col0, col15]
        have hcv : colVal col15 = 15 := by native_decide
        rw [hsub, hall]
        exact hcv
      rcases hC0struct (p t) with h0'' | h5'' | h6''
      · omega
      · omega
      · omega
    calc
      C0 (p t) = rowPermute ρ (if f t then flipCol (C t) else C t) := hh'
      _ = rowPermute ρ col0 := by rw [hf, h0]; simp
      _ = col0 := by
        funext k
        simp [rowPermute, col0]
  have heq_all := zero_column_C0 C0 (p t) h0' hC0struct h5 h6
    (rowPermute ρ (if f t then flipCol s' else s'))
  intro ε hε0 hε1
  have hleft : lambda (replaceColumn C0 (p t) (rowPermute ρ (if f t then flipCol s' else s'))) ε =
      lambda C0 ε := heq_all ε hε0 hε1
  have hC : Equivalent C C0 := hEq_full
  calc
    lambda (replaceColumn C t s') ε =
        lambda (replaceColumn C0 (p t) (rowPermute ρ (if f t then flipCol s' else s'))) ε :=
      (lambda_equiv (replaceColumn C t s')
        (replaceColumn C0 (p t) (rowPermute ρ (if f t then flipCol s' else s'))) hEq' ε).symm
    _ = lambda C0 ε := hleft
    _ = lambda C ε := lambda_equiv C C0 hC ε

/-! ## `thm:0column` (Theorem 6) (2): the strict-improvement witness -/

/-- A subset of s of any size k ≤ s.card. -/
lemma exists_subset_card {α : Type*} [DecidableEq α] {s : Finset α} {k : ℕ}
    (hk : k ≤ s.card) : ∃ t : Finset α, t ⊆ s ∧ t.card = k := by
  rcases Finset.powersetCard_nonempty_of_le hk with ⟨t, ht⟩
  exact ⟨t, Finset.mem_powersetCard.mp ht⟩

/-- A word with the prescribed per-type weights, when they are feasible. -/
lemma exists_goodWord {n : ℕ} (C : Code n) (k : ℕ → ℕ)
    (hk : ∀ i ∈ Finset.Icc 0 15, k i ≤ count C i) :
    ∃ y : Word n, ∀ i ∈ Finset.Icc 0 15, w_i C i y = k i := by
  have hcard : 0 < (GoodWords C k).card := by
    rw [goodWords_card, goodTuples_card]
    have hone : 1 ≤ ∏ i ∈ Finset.Icc 0 15, Nat.choose (count C i) (k i) := by
      apply Finset.one_le_prod'
      intro i hi
      exact Nat.succ_le_of_lt (Nat.choose_pos (hk i hi))
    omega
  rcases Finset.card_pos.mp hcard with ⟨y, hy⟩
  exact ⟨y, (goodWord_iff C k y).1 hy⟩

-- native_decide: Mechanical · n=any · checked 2026-08-27
/-- A column with type number 0 is the zero column. -/
lemma colVal_eq_zero_iff_col0 (c : Column) : colVal c = 0 ↔ c = col0 := by
  simpa [show colOfNat 0 = col0 by native_decide] using (colVal_eq_iff_colOfNat c 0 (by norm_num))

/-- Columns07 means all type numbers are at most 7. -/
lemma Columns07_le7 {n : ℕ} (C : Code n) (h : Columns07 C) (t : Fin n) : colVal (C t) ≤ 7 := by
  let z : Fin 4 := ⟨0, by decide⟩
  have hb : (C t) z = false := h t
  let hf : Fin 4 → ℕ := fun j => if C t j then 2 ^ (3 - j.val) else 0
  have hsplit := sum_split_at hf z
  calc
    colVal (C t) = (∑ j : Fin 4, hf j) := by rfl
    _ = (∑ j ∈ (Finset.univ.erase z), hf j) + hf z := hsplit
    _ = (∑ j ∈ (Finset.univ.erase z), hf j) + 0 := by
          simp [hf, hb]
    _ ≤ (∑ j ∈ (Finset.univ.erase z), 2 ^ (3 - j.val)) + 0 := by
          have hle : (∑ j ∈ (Finset.univ.erase z), hf j) ≤
              ∑ j ∈ (Finset.univ.erase z), 2 ^ (3 - j.val) := by
            apply Finset.sum_le_sum
            intro j _
            by_cases hc : C t j <;> simp [hf, hc]
          omega
    _ = 7 := by
          have hsum : (∑ j ∈ (Finset.univ.erase z), 2 ^ (3 - j.val)) = 7 := by
            have huniv : (Finset.univ.erase z : Finset (Fin 4)) =
                ({⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩} : Finset (Fin 4)) := by
              ext j
              fin_cases j <;> simp [z]
            rw [huniv]
            simp
          rw [hsum]

/-- Sum over the type range 0..7. -/
lemma sum_Icc0_7 (f : ℕ → ℕ) : (∑ i ∈ Finset.Icc 0 7, f i) =
    f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 := by
  have h1 : (Finset.Icc 0 7 : Finset ℕ) = {0, 1, 2, 3, 4, 5, 6, 7} := by
    ext i
    constructor
    · intro hi
      simp at hi ⊢
      omega
    · intro hi
      simp at hi ⊢
      omega
  rw [h1]
  simp [Finset.sum_insert]
  ring

/-- Row distances of a word whose only type-1..3 weights vanish, in a
Columns07 code (the paper's eq. (0columna)/(0columnb) shape, published
(149)-(152)). -/
-- native_decide: Mechanical · n=any · checked 2026-08-27
lemma dRow_witness_formula {n : ℕ} (C : Code n) (y : Word n) (h07 : Columns07 C)
    (hw123 : w_i C 1 y = 0 ∧ w_i C 2 y = 0 ∧ w_i C 3 y = 0)
    (_hw815 : ∀ i ∈ Finset.Icc 8 15, w_i C i y = 0) :
    dRow C 0 y = w_i C 0 y + w_i C 4 y + w_i C 5 y + w_i C 6 y + w_i C 7 y ∧
    dRow C 1 y = w_i C 0 y + (count C 4 - w_i C 4 y) + (count C 5 - w_i C 5 y) +
      (count C 6 - w_i C 6 y) + (count C 7 - w_i C 7 y) ∧
    dRow C 2 y = w_i C 0 y + count C 2 + count C 3 + w_i C 4 y + w_i C 5 y +
      (count C 6 - w_i C 6 y) + (count C 7 - w_i C 7 y) ∧
    dRow C 3 y = w_i C 0 y + count C 1 + count C 3 + w_i C 4 y + (count C 5 - w_i C 5 y) +
      w_i C 6 y + (count C 7 - w_i C 7 y) := by
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
  have h13 : (1 : ℕ).testBit 3 = false := by native_decide
  have h23 : (2 : ℕ).testBit 3 = false := by native_decide
  have h33 : (3 : ℕ).testBit 3 = false := by native_decide
  have h43 : (4 : ℕ).testBit 3 = false := by native_decide
  have h53 : (5 : ℕ).testBit 3 = false := by native_decide
  have h63 : (6 : ℕ).testBit 3 = false := by native_decide
  have h73 : (7 : ℕ).testBit 3 = false := by native_decide
  have h12 : (1 : ℕ).testBit 2 = false := by native_decide
  have h22 : (2 : ℕ).testBit 2 = false := by native_decide
  have h32 : (3 : ℕ).testBit 2 = false := by native_decide
  have h42 : (4 : ℕ).testBit 2 = true := by native_decide
  have h52 : (5 : ℕ).testBit 2 = true := by native_decide
  have h62 : (6 : ℕ).testBit 2 = true := by native_decide
  have h72 : (7 : ℕ).testBit 2 = true := by native_decide
  have h11 : (1 : ℕ).testBit 1 = false := by native_decide
  have h21 : (2 : ℕ).testBit 1 = true := by native_decide
  have h31 : (3 : ℕ).testBit 1 = true := by native_decide
  have h41 : (4 : ℕ).testBit 1 = false := by native_decide
  have h51 : (5 : ℕ).testBit 1 = false := by native_decide
  have h61 : (6 : ℕ).testBit 1 = true := by native_decide
  have h71 : (7 : ℕ).testBit 1 = true := by native_decide
  have h10 : (1 : ℕ).testBit 0 = true := by native_decide
  have h20 : (2 : ℕ).testBit 0 = false := by native_decide
  have h30 : (3 : ℕ).testBit 0 = true := by native_decide
  have h40 : (4 : ℕ).testBit 0 = false := by native_decide
  have h50 : (5 : ℕ).testBit 0 = true := by native_decide
  have h60 : (6 : ℕ).testBit 0 = false := by native_decide
  have h70 : (7 : ℕ).testBit 0 = true := by native_decide
  have h0 : dRow C 0 y = w_i C 0 y + w_i C 4 y + w_i C 5 y + w_i C 6 y + w_i C 7 y := by
    rw [hsum (0 : Fin 4), sum_Icc0_7]
    simp [hw123, h13, h23, h33, h43, h53, h63, h73]
  have h1 : dRow C 1 y = w_i C 0 y + (count C 4 - w_i C 4 y) + (count C 5 - w_i C 5 y) +
      (count C 6 - w_i C 6 y) + (count C 7 - w_i C 7 y) := by
    rw [hsum (1 : Fin 4), sum_Icc0_7]
    simp [hw123, h12, h22, h32, h42, h52, h62, h72]
  have h2 : dRow C 2 y = w_i C 0 y + count C 2 + count C 3 + w_i C 4 y + w_i C 5 y +
      (count C 6 - w_i C 6 y) + (count C 7 - w_i C 7 y) := by
    rw [hsum (2 : Fin 4), sum_Icc0_7]
    simp [hw123, h11, h21, h31, h41, h51, h61, h71]
  have h3 : dRow C 3 y = w_i C 0 y + count C 1 + count C 3 + w_i C 4 y + (count C 5 - w_i C 5 y) +
      w_i C 6 y + (count C 7 - w_i C 7 y) := by
    rw [hsum (3 : Fin 4), sum_Icc0_7]
    simp [hw123, h10, h20, h30, h40, h50, h60, h70]
  exact ⟨h0, h1, h2, h3⟩

/-- The nonemptiness proofs for the col5 split (O = {0,2}, P = {1,3}). -/
lemma colZeros_col5_nonempty : (colZeros col5).Nonempty := by
  rw [colZeros]
  exact ⟨⟨0, by decide⟩, by simp [col5]⟩

lemma colOnes_col5_nonempty : (colOnes col5).Nonempty := by
  rw [colOnes]
  exact ⟨⟨1, by decide⟩, by simp [col5]⟩

/-- From a feasible table assignment k, build the witness word and prove
Y3c nonempty for the col5 split (paper Table 0column). -/
lemma witness_from_k {n : ℕ} (C : Code n) (h07 : Columns07 C) (k : ℕ → ℕ)
    (hcnt0 : 1 ≤ count C 0) (hk0 : k 0 = 1)
    (hk03 : k 1 = 0 ∧ k 2 = 0 ∧ k 3 = 0)
    (hk47 : ∀ i ∈ Finset.Icc 4 7, k i ≤ count C i)
    (hk815 : ∀ i ∈ Finset.Icc 8 15, k i = 0)
    (hmid : 2 * (k 4 + k 5 + k 6 + k 7) =
      count C 4 + count C 5 + count C 6 + count C 7)
    (hge2 : 2 * k 6 + 2 * k 7 ≤ count C 2 + count C 3 + count C 6 + count C 7)
    (hge3 : 2 * k 5 + 2 * k 7 ≤ count C 1 + count C 3 + count C 5 + count C 7) :
    ∃ t : Fin n, C t = col0 ∧ ∃ y : Word n, Y3c C col5 colZeros_col5_nonempty
      colOnes_col5_nonempty t y := by
  have hk : ∀ i ∈ Finset.Icc 0 15, k i ≤ count C i := by
    intro i hi
    have hi7 : i ≤ 15 := (Finset.mem_Icc.mp hi).2
    by_cases hi0 : i = 0
    · rw [hi0, hk0]
      omega
    · by_cases hi47 : i ∈ Finset.Icc 4 7
      · exact hk47 i hi47
      · -- i ∈ 1..3 or 8..15: k i = 0
        have hk0' : k i = 0 := by
          rcases hk03 with ⟨h1, h2, h3⟩
          by_cases hi1 : i = 1
          · subst i
            exact h1
          · by_cases hi2 : i = 2
            · subst i
              exact h2
            · by_cases hi3 : i = 3
              · subst i
                exact h3
              · have h8 : 8 ≤ i := by
                  simp [Finset.mem_Icc] at hi47
                  omega
                exact hk815 i (by simp [Finset.mem_Icc, h8, hi7])
        omega
  rcases exists_goodWord C k hk with ⟨y, hy⟩
  have hw0 : w_i C 0 y = 1 := by
    rw [← hk0]
    exact hy 0 (by simp [Finset.mem_Icc])
  have hw1 : w_i C 1 y = 0 := by
    rw [← hk03.1]
    exact hy 1 (by simp [Finset.mem_Icc])
  have hw2 : w_i C 2 y = 0 := by
    rw [← hk03.2.1]
    exact hy 2 (by simp [Finset.mem_Icc])
  have hw3 : w_i C 3 y = 0 := by
    rw [← hk03.2.2]
    exact hy 3 (by simp [Finset.mem_Icc])
  have hw47 : ∀ i ∈ Finset.Icc 4 7, w_i C i y = k i := by
    intro i hi
    exact hy i (by simp [Finset.mem_Icc] at hi ⊢; omega)
  have hw815 : ∀ i ∈ Finset.Icc 8 15, w_i C i y = 0 := by
    intro i hi
    have : k i = 0 := hk815 i hi
    rw [← this]
    exact hy i (by simp [Finset.mem_Icc] at hi ⊢; omega)
  have hform := dRow_witness_formula C y h07 ⟨hw1, hw2, hw3⟩ hw815
  rcases hform with ⟨hd0, hd1, hd2, hd3⟩
  have hw0card : (onesOn (fiber C 0) y).card = 1 := by
    rw [← w_i_eq_card_onesOn, hw0]
  rcases Finset.card_pos.mp (by omega : 0 < (onesOn (fiber C 0) y).card) with ⟨t, ht⟩
  have htmem : t ∈ onesOn (fiber C 0) y := ht
  have ht0 : C t = col0 := by
    have hf : t ∈ fiber C 0 := (Finset.mem_filter.mp htmem).1
    have hcv : colVal (C t) = 0 := (Finset.mem_filter.mp hf).2
    exact (colVal_eq_zero_iff_col0 (C t)).mp hcv
  have hyt : y t = true := (Finset.mem_filter.mp htmem).2
  have hb4 : k 4 ≤ count C 4 := hk47 4 (by simp)
  have hb5 : k 5 ≤ count C 5 := hk47 5 (by simp)
  have hb6 : k 6 ≤ count C 6 := hk47 6 (by simp)
  have hb7 : k 7 ≤ count C 7 := hk47 7 (by simp)
  have htwo : 2 * (k 4 + k 5 + k 6 + k 7) = count C 4 + count C 5 + count C 6 + count C 7 := hmid
  have hd12 : dRow C 0 y = dRow C 1 y := by
    rw [hd0, hd1]
    simp [hw0, hw47 4 (by simp), hw47 5 (by simp), hw47 6 (by simp), hw47 7 (by simp)]
    omega
  have hd12' : dRow C 0 y ≤ dRow C 2 y := by
    rw [hd0, hd2]
    simp [hw0, hw47 4 (by simp), hw47 5 (by simp), hw47 6 (by simp), hw47 7 (by simp)]
    omega
  have hd13' : dRow C 0 y ≤ dRow C 3 y := by
    rw [hd0, hd3]
    simp [hw0, hw47 4 (by simp), hw47 5 (by simp), hw47 6 (by simp), hw47 7 (by simp)]
    omega
  have hd1le3 : dRow C 1 y ≤ dRow C 3 y := by
    rw [← hd12]
    exact hd13'
  have hz : (colZeros col5) = ({⟨0, by decide⟩, ⟨2, by decide⟩} : Finset (Fin 4)) := by
    ext i
    fin_cases i <;> simp [colZeros, col5]
  have hp : (colOnes col5) = ({⟨1, by decide⟩, ⟨3, by decide⟩} : Finset (Fin 4)) := by
    ext i
    fin_cases i <;> simp [colOnes, col5]
  have hdO : dOc C col5 colZeros_col5_nonempty y = dRow C 0 y := by
    unfold dOc dRowMin
    have hmin : ({dRow C 0 y, dRow C 2 y} : Finset ℕ).min' (by simp) =
        min (dRow C 0 y) (dRow C 2 y) := by
      apply le_antisymm
      · apply le_min
        · exact Finset.min'_le ({dRow C 0 y, dRow C 2 y} : Finset ℕ) (dRow C 0 y) (by simp)
        · exact Finset.min'_le ({dRow C 0 y, dRow C 2 y} : Finset ℕ) (dRow C 2 y) (by simp)
      · apply Finset.le_min'
        intro z hz
        simp at hz
        rcases hz with rfl | rfl
        · exact min_le_left _ _
        · exact min_le_right _ _
    simp [hz, hmin, min_eq_left hd12']
  have hdP : dPc C col5 colOnes_col5_nonempty y = dRow C 1 y := by
    unfold dPc dRowMin
    have hmin : ({dRow C 1 y, dRow C 3 y} : Finset ℕ).min' (by simp) =
        min (dRow C 1 y) (dRow C 3 y) := by
      apply le_antisymm
      · apply le_min
        · exact Finset.min'_le ({dRow C 1 y, dRow C 3 y} : Finset ℕ) (dRow C 1 y) (by simp)
        · exact Finset.min'_le ({dRow C 1 y, dRow C 3 y} : Finset ℕ) (dRow C 3 y) (by simp)
      · apply Finset.le_min'
        intro z hz
        simp at hz
        rcases hz with rfl | rfl
        · exact min_le_left _ _
        · exact min_le_right _ _
    simp [hp, hmin, min_eq_left hd1le3]
  refine ⟨t, ht0, y, ?_⟩
  unfold Y3c
  exact ⟨hyt, by rw [hdO, hdP, hd12]⟩

/-- The table weight function: w₀ = 1, types 1–3 and 8–15 vanish, types 4–7
take the table values. -/
def tableK (a4 a5 a6 a7 : ℕ) (i : ℕ) : ℕ :=
  if i = 0 then 1 else if i = 1 ∨ i = 2 ∨ i = 3 then 0
  else if i = 4 then a4 else if i = 5 then a5 else if i = 6 then a6 else if i = 7 then a7 else 0

lemma tableK_0 (a4 a5 a6 a7 : ℕ) : tableK a4 a5 a6 a7 0 = 1 := by
  simp [tableK]

lemma tableK_03 (a4 a5 a6 a7 : ℕ) :
    tableK a4 a5 a6 a7 1 = 0 ∧ tableK a4 a5 a6 a7 2 = 0 ∧ tableK a4 a5 a6 a7 3 = 0 := by
  simp [tableK]

lemma tableK_47 (a4 a5 a6 a7 : ℕ) :
    tableK a4 a5 a6 a7 4 = a4 ∧ tableK a4 a5 a6 a7 5 = a5 ∧
      tableK a4 a5 a6 a7 6 = a6 ∧ tableK a4 a5 a6 a7 7 = a7 := by
  simp [tableK]

lemma tableK_815 (a4 a5 a6 a7 : ℕ) : ∀ i ∈ Finset.Icc 8 15, tableK a4 a5 a6 a7 i = 0 := by
  intro i hi
  have h8 : 8 ≤ i := (Finset.mem_Icc.mp hi).1
  have h15 : i ≤ 15 := (Finset.mem_Icc.mp hi).2
  have h0 : i ≠ 0 := by omega
  have h1 : i ≠ 1 := by omega
  have h2 : i ≠ 2 := by omega
  have h3 : i ≠ 3 := by omega
  have h4 : i ≠ 4 := by omega
  have h5 : i ≠ 5 := by omega
  have h6 : i ≠ 6 := by omega
  have h7 : i ≠ 7 := by omega
  simp [tableK, h0, h1, h2, h3, h4, h5, h6, h7]

lemma tableK_bounds {n : ℕ} (C : Code n) (a4 a5 a6 a7 : ℕ)
    (hcnt0 : 1 ≤ count C 0) (ha4 : a4 ≤ count C 4) (ha5 : a5 ≤ count C 5)
    (ha6 : a6 ≤ count C 6) (ha7 : a7 ≤ count C 7) :
    ∀ i ∈ Finset.Icc 0 15, tableK a4 a5 a6 a7 i ≤ count C i := by
  intro i hi
  have hi7 : i ≤ 15 := (Finset.mem_Icc.mp hi).2
  by_cases hi0 : i = 0
  · rw [hi0, tableK_0]
    exact hcnt0
  · by_cases hi1 : i = 1
    · subst i
      simp [tableK]
    · by_cases hi2 : i = 2
      · subst i
        simp [tableK]
      · by_cases hi3 : i = 3
        · subst i
          simp [tableK]
        · by_cases hi4 : i = 4
          · subst i
            simp [tableK]
            exact ha4
          · by_cases hi5 : i = 5
            · subst i
              simp [tableK]
              exact ha5
            · by_cases hi6 : i = 6
              · subst i
                simp [tableK]
                exact ha6
              · by_cases hi7' : i = 7
                · subst i
                  simp [tableK]
                  exact ha7
                · have h8 : 8 ≤ i := by omega
                  have h0 : i ≠ 0 := by omega
                  have h1 : i ≠ 1 := by omega
                  have h2 : i ≠ 2 := by omega
                  have h3 : i ≠ 3 := by omega
                  have h4 : i ≠ 4 := by omega
                  have h5 : i ≠ 5 := by omega
                  have h6 : i ≠ 6 := by omega
                  have h7 : i ≠ 7 := by omega
                  simp [tableK, h0, h1, h2, h3, h4, h5, h6, h7]

/-! ## The C0 form and the parity table -/

/-- The paper's C0 code condition: only 0,5,6 columns with |5|,|6| odd. -/
def C0form {n : ℕ} (C : Code n) : Prop :=
  count C 0 + count C 5 + count C 6 = n ∧ Odd (count C 5) ∧ Odd (count C 6)

/-- n = 2k implies n / 2 = k. -/
lemma div_two_eq {n k : ℕ} (h : n = 2 * k) : n / 2 = k := by
  rw [h]
  exact Nat.mul_div_right k (by decide : 0 < 2)

/-- Even n gives a linear witness n = 2k. -/
lemma even_two_mul {n : ℕ} (h : Even n) : ∃ k : ℕ, n = 2 * k := by
  rcases h with ⟨k, hk⟩
  exact ⟨k, by rw [hk, two_mul]⟩

/-- Not even means odd. -/
lemma odd_of_not_even {n : ℕ} (h : ¬ Even n) : Odd n := by
  rwa [← Nat.not_even_iff_odd]

/-- The table bounds restricted to types 4..7. -/
lemma tableK_bounds_47 {n : ℕ} (C : Code n) (a4 a5 a6 a7 : ℕ)
    (hcnt0 : 1 ≤ count C 0) (ha4 : a4 ≤ count C 4) (ha5 : a5 ≤ count C 5)
    (ha6 : a6 ≤ count C 6) (ha7 : a7 ≤ count C 7) :
    ∀ i ∈ Finset.Icc 4 7, tableK a4 a5 a6 a7 i ≤ count C i := by
  intro i hi
  exact (tableK_bounds C a4 a5 a6 a7 hcnt0 ha4 ha5 ha6 ha7) i
    (by simp [Finset.mem_Icc] at hi ⊢; omega)

/-- A Columns07 code has all its columns among types 0..7. -/
lemma Columns07_sum_counts {n : ℕ} (C : Code n) (h07 : Columns07 C) :
    (∑ i ∈ Finset.Icc 0 7, count C i) = n := by
  have hsum := sum_counts_eq_n C
  have hzero : ∀ i ∈ Finset.Icc 8 15, count C i = 0 := by
    intro i hi
    rw [count_eq_card]
    apply Finset.card_eq_zero.mpr
    rw [Finset.eq_empty_iff_forall_notMem]
    intro t ht
    have hcv : colVal (C t) = i := (Finset.mem_filter.mp ht).2
    have hle := Columns07_le7 C h07 t
    simp [Finset.mem_Icc] at hi
    omega
  have hS : (Finset.Icc 0 7 : Finset ℕ) ⊆ Finset.Icc 0 15 := by
    intro i hi
    simp [Finset.mem_Icc] at hi ⊢
    omega
  -- Σ_{0..15} = Σ_{0..7} + Σ_{8..15}, and the latter is 0
  have hsplit : (∑ i ∈ Finset.Icc 0 15, count C i) =
      (∑ i ∈ Finset.Icc 0 7, count C i) +
        ∑ i ∈ Finset.Icc 0 15 \ (Finset.Icc 0 7 : Finset ℕ), count C i := by
    rw [← Finset.sum_sdiff hS]
    rw [add_comm]
  have hrest : (∑ i ∈ Finset.Icc 0 15 \ (Finset.Icc 0 7 : Finset ℕ), count C i) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hi8 : 8 ≤ i := by
      rw [Finset.mem_sdiff] at hi
      simp [Finset.mem_Icc] at hi
      omega
    have hi15 : i ≤ 15 := by
      rw [Finset.mem_sdiff] at hi
      simp [Finset.mem_Icc] at hi
      omega
    exact hzero i (by simp [Finset.mem_Icc, hi8, hi15])
  omega

/-- The type range 0..7 splits into {0,5,6} and {1,2,3,4,7}. -/
lemma Icc0_7_eq : (Finset.Icc 0 7 : Finset ℕ) = {0, 5, 6} ∪ {1, 2, 3, 4, 7} := by
  ext i
  constructor
  · intro hi
    simp at hi
    have hi' : i = 0 ∨ i = 5 ∨ i = 6 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 7 := by omega
    rcases hi' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp
  · intro hi
    rcases (Finset.mem_union.mp hi) with hi' | hi'
    · simp at hi' ⊢
      omega
    · simp at hi' ⊢
      omega

/-- The sets {0,5,6} and {1,2,3,4,7} are disjoint. -/
lemma disjoint_056_12347 : Disjoint ({0, 5, 6} : Finset ℕ) ({1, 2, 3, 4, 7} : Finset ℕ) := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  simp at hx hx'
  omega

/-- In a Columns07 code, the C0 form means exactly types 1–4,7 are absent. -/
lemma C0form_iff_Columns07 {n : ℕ} (C : Code n) (h07 : Columns07 C) :
    C0form C ↔ (count C 1 = 0 ∧ count C 2 = 0 ∧ count C 3 = 0 ∧ count C 4 = 0 ∧
      count C 7 = 0 ∧ Odd (count C 5) ∧ Odd (count C 6)) := by
  constructor
  · intro h
    rcases h with ⟨hcnt, h5, h6⟩
    have hsum := Columns07_sum_counts C h07
    -- Σ_{0..7} = n = |0|+|5|+|6| → the rest sum to 0
    have hrest : (∑ i ∈ ({1, 2, 3, 4, 7} : Finset ℕ), count C i) = 0 := by
      have hS : ({1, 2, 3, 4, 7} : Finset ℕ) ⊆ Finset.Icc 0 7 := by
        intro i hi
        simp at hi ⊢
        omega
      have hsplit : (∑ i ∈ Finset.Icc 0 7, count C i) =
          (∑ i ∈ ({0, 5, 6} : Finset ℕ), count C i) +
            ∑ i ∈ ({1, 2, 3, 4, 7} : Finset ℕ), count C i := by
        rw [Icc0_7_eq, Finset.sum_union disjoint_056_12347]
      have hS05 : (∑ i ∈ ({0, 5, 6} : Finset ℕ), count C i) = n := by
        simp [Finset.sum_insert]
        omega
      omega
    have h1 : count C 1 = 0 := by
      have hle : count C 1 ≤ ∑ i ∈ ({1, 2, 3, 4, 7} : Finset ℕ), count C i := by
        exact Finset.single_le_sum (by intro j _; exact Nat.zero_le _) (by simp)
      omega
    have h2 : count C 2 = 0 := by
      have hle : count C 2 ≤ ∑ i ∈ ({1, 2, 3, 4, 7} : Finset ℕ), count C i := by
        exact Finset.single_le_sum (by intro j _; exact Nat.zero_le _) (by simp)
      omega
    have h3 : count C 3 = 0 := by
      have hle : count C 3 ≤ ∑ i ∈ ({1, 2, 3, 4, 7} : Finset ℕ), count C i := by
        exact Finset.single_le_sum (by intro j _; exact Nat.zero_le _) (by simp)
      omega
    have h4 : count C 4 = 0 := by
      have hle : count C 4 ≤ ∑ i ∈ ({1, 2, 3, 4, 7} : Finset ℕ), count C i := by
        exact Finset.single_le_sum (by intro j _; exact Nat.zero_le _) (by simp)
      omega
    have h7 : count C 7 = 0 := by
      have hle : count C 7 ≤ ∑ i ∈ ({1, 2, 3, 4, 7} : Finset ℕ), count C i := by
        exact Finset.single_le_sum (by intro j _; exact Nat.zero_le _) (by simp)
      omega
    exact ⟨h1, h2, h3, h4, h7, h5, h6⟩
  · intro h
    rcases h with ⟨h1, h2, h3, h4, h7, h5, h6⟩
    have hsum := Columns07_sum_counts C h07
    -- Σ_{0..7} = |0|+|5|+|6| since the others vanish
    have hcnt : count C 0 + count C 5 + count C 6 = n := by
      rw [Icc0_7_eq, Finset.sum_union disjoint_056_12347] at hsum
      simp [Finset.sum_insert, h1, h2, h3, h4, h7] at hsum
      omega
    exact ⟨hcnt, h5, h6⟩

/-- Wrapper: the tableK bookkeeping for a feasible table assignment. -/
lemma use_witness {n : ℕ} (C : Code n) (h07 : Columns07 C) (hcnt0 : 1 ≤ count C 0)
    (a4 a5 a6 a7 : ℕ)
    (ha4 : a4 ≤ count C 4) (ha5 : a5 ≤ count C 5) (ha6 : a6 ≤ count C 6)
    (ha7 : a7 ≤ count C 7)
    (hmid : 2 * (a4 + a5 + a6 + a7) = count C 4 + count C 5 + count C 6 + count C 7)
    (hge2 : 2 * a6 + 2 * a7 ≤ count C 2 + count C 3 + count C 6 + count C 7)
    (hge3 : 2 * a5 + 2 * a7 ≤ count C 1 + count C 3 + count C 5 + count C 7) :
    ∃ t : Fin n, C t = col0 ∧ ∃ y : Word n, Y3c C col5 colZeros_col5_nonempty
      colOnes_col5_nonempty t y := by
  let k : ℕ → ℕ := tableK a4 a5 a6 a7
  have hk4 : k 4 = a4 := by simp [k, tableK]
  have hk5 : k 5 = a5 := by simp [k, tableK]
  have hk6 : k 6 = a6 := by simp [k, tableK]
  have hk7 : k 7 = a7 := by simp [k, tableK]
  exact witness_from_k C h07 k hcnt0 (tableK_0 a4 a5 a6 a7) (tableK_03 a4 a5 a6 a7)
    (by simpa [k] using tableK_bounds_47 C a4 a5 a6 a7 hcnt0 ha4 ha5 ha6 ha7)
    (tableK_815 a4 a5 a6 a7)
    (by
      rw [hk4, hk5, hk6, hk7]
      exact hmid)
    (by
      rw [hk6, hk7]
      exact hge2)
    (by
      rw [hk5, hk7]
      exact hge3)

/-- The parity table (paper Table 0column): for a Columns07 code that is not
in the C0 form, with W = |4|+|5|+|6|+|7| even, there is a Y3c witness for the
col5 split. -/
lemma witness_exists_C0form {n : ℕ} (C : Code n) (h07 : Columns07 C)
    (hcnt0 : 1 ≤ count C 0) (hWeven : Even (count C 4 + count C 5 + count C 6 + count C 7))
    (hnotC0 : ¬ C0form C) :
    ∃ t : Fin n, C t = col0 ∧ ∃ y : Word n, Y3c C col5 colZeros_col5_nonempty
      colOnes_col5_nonempty t y := by
  by_cases h4 : Even (count C 4)
  · by_cases h5 : Even (count C 5)
    · by_cases h6 : Even (count C 6)
      · by_cases h7 : Even (count C 7)
        · -- case 1: all even — w = (|4|,|5|,|6|,|7|)/2
          rcases h4 with ⟨a, h4a⟩
          rcases h5 with ⟨b, h5b⟩
          rcases h6 with ⟨c, h6c⟩
          rcases h7 with ⟨d, h7d⟩
          let k : ℕ → ℕ := tableK a b c d
          have hk4 : k 4 = a := by simp [k, tableK]
          have hk5 : k 5 = b := by simp [k, tableK]
          have hk6 : k 6 = c := by simp [k, tableK]
          have hk7 : k 7 = d := by simp [k, tableK]
          have hb4 : a ≤ count C 4 := by omega
          have hb5 : b ≤ count C 5 := by omega
          have hb6 : c ≤ count C 6 := by omega
          have hb7 : d ≤ count C 7 := by omega
          have hmid : 2 * (k 4 + k 5 + k 6 + k 7) = count C 4 + count C 5 + count C 6 + count C 7 := by
            rw [hk4, hk5, hk6, hk7]
            omega
          have hge2 : 2 * k 6 + 2 * k 7 ≤ count C 2 + count C 3 + count C 6 + count C 7 := by
            rw [hk6, hk7]
            omega
          have hge3 : 2 * k 5 + 2 * k 7 ≤ count C 1 + count C 3 + count C 5 + count C 7 := by
            rw [hk5, hk7]
            omega
          exact witness_from_k C h07 k hcnt0 (tableK_0 a b c d) (tableK_03 a b c d)
            (by simpa [k] using tableK_bounds_47 C a b c d hcnt0 hb4 hb5 hb6 hb7)
            (tableK_815 a b c d) hmid hge2 hge3
        · -- (E,E,E,O): one odd — impossible since W even
          exfalso
          rcases hWeven with ⟨m, hm⟩
          rcases h4 with ⟨a, h4a⟩
          rcases h5 with ⟨b, h5b⟩
          rcases h6 with ⟨c, h6c⟩
          have h7o : Odd (count C 7) := (odd_of_not_even h7)
          rcases h7o with ⟨d, h7d⟩
          omega
      · by_cases h7 : Even (count C 7)
        · -- (E,E,O,E): one odd — impossible
          exfalso
          rcases hWeven with ⟨m, hm⟩
          rcases h4 with ⟨a, h4a⟩
          rcases h5 with ⟨b, h5b⟩
          have h6o : Odd (count C 6) := (odd_of_not_even h6)
          rcases h6o with ⟨c, h6c⟩
          rcases h7 with ⟨d, h7d⟩
          omega
        · -- case 7: (E,E,O,O) — w = (0,0,1/2,-1/2)
          rcases h4 with ⟨a, h4a⟩
          rcases h5 with ⟨b, h5b⟩
          have h6o : Odd (count C 6) := (odd_of_not_even h6)
          rcases h6o with ⟨c, h6c⟩
          have h7o : Odd (count C 7) := (odd_of_not_even h7)
          rcases h7o with ⟨d, h7d⟩
          have hb4 : a ≤ count C 4 := by omega
          have hb5 : b ≤ count C 5 := by omega
          have hb6 : c + 1 ≤ count C 6 := by omega
          have hb7 : d ≤ count C 7 := by omega
          have hmid : 2 * (a + b + (c + 1) + d) = count C 4 + count C 5 + count C 6 + count C 7 := by omega
          have hge2 : 2 * (c + 1) + 2 * d ≤ count C 2 + count C 3 + count C 6 + count C 7 := by omega
          have hge3 : 2 * b + 2 * d ≤ count C 1 + count C 3 + count C 5 + count C 7 := by omega
          exact use_witness C h07 hcnt0 a b (c + 1) d hb4 hb5 hb6 hb7 hmid hge2 hge3
    · by_cases h6 : Even (count C 6)
      · by_cases h7 : Even (count C 7)
        · -- (E,O,E,E): one odd — impossible
          exfalso
          rcases hWeven with ⟨m, hm⟩
          rcases h4 with ⟨a, h4a⟩
          have h5o : Odd (count C 5) := (odd_of_not_even h5)
          rcases h5o with ⟨b, h5b⟩
          rcases h6 with ⟨c, h6c⟩
          rcases h7 with ⟨d, h7d⟩
          omega
        · -- case 6: (E,O,E,O) — w = (0,1/2,0,-1/2)
          rcases h4 with ⟨a, h4a⟩
          have h5o : Odd (count C 5) := (odd_of_not_even h5)
          rcases h5o with ⟨b, h5b⟩
          rcases h6 with ⟨c, h6c⟩
          have h7o : Odd (count C 7) := (odd_of_not_even h7)
          rcases h7o with ⟨d, h7d⟩
          have hb4 : a ≤ count C 4 := by omega
          have hb5 : b + 1 ≤ count C 5 := by omega
          have hb6 : c ≤ count C 6 := by omega
          have hb7 : d ≤ count C 7 := by omega
          have hmid : 2 * (a + (b + 1) + c + d) = count C 4 + count C 5 + count C 6 + count C 7 := by omega
          have hge2 : 2 * c + 2 * d ≤ count C 2 + count C 3 + count C 6 + count C 7 := by omega
          have hge3 : 2 * (b + 1) + 2 * d ≤ count C 1 + count C 3 + count C 5 + count C 7 := by omega
          exact use_witness C h07 hcnt0 a (b + 1) c d hb4 hb5 hb6 hb7 hmid hge2 hge3
      · by_cases h7 : Even (count C 7)
        · -- (E,O,O,E): cases 5a, 5b, or the exceptional table-2 case
          by_cases h4pos : 0 < count C 4
          · -- case 5a: w = (|4|/2+1, (|5|-1)/2, (|6|-1)/2, |7|/2)
            rcases h4 with ⟨a, h4a⟩
            have h5o : Odd (count C 5) := (odd_of_not_even h5)
            rcases h5o with ⟨b, h5b⟩
            have h6o : Odd (count C 6) := (odd_of_not_even h6)
            rcases h6o with ⟨c, h6c⟩
            rcases h7 with ⟨d, h7d⟩
            have hb4 : a + 1 ≤ count C 4 := by omega
            have hb5 : b ≤ count C 5 := by omega
            have hb6 : c ≤ count C 6 := by omega
            have hb7 : d ≤ count C 7 := by omega
            have hmid : 2 * ((a + 1) + b + c + d) = count C 4 + count C 5 + count C 6 + count C 7 := by omega
            have hge2 : 2 * c + 2 * d ≤ count C 2 + count C 3 + count C 6 + count C 7 := by omega
            have hge3 : 2 * b + 2 * d ≤ count C 1 + count C 3 + count C 5 + count C 7 := by omega
            exact use_witness C h07 hcnt0 (a + 1) b c d hb4 hb5 hb6 hb7 hmid hge2 hge3
          · by_cases h7pos : 0 < count C 7
            · -- case 5b: w = (|4|/2, (|5|+1)/2, (|6|+1)/2, |7|/2−1)
              rcases h4 with ⟨a, h4a⟩
              have h5o : Odd (count C 5) := (odd_of_not_even h5)
              rcases h5o with ⟨b, h5b⟩
              have h6o : Odd (count C 6) := (odd_of_not_even h6)
              rcases h6o with ⟨c, h6c⟩
              rcases h7 with ⟨d, h7d⟩
              have hb4 : a ≤ count C 4 := by omega
              have hb5 : b + 1 ≤ count C 5 := by omega
              have hb6 : c + 1 ≤ count C 6 := by omega
              have hb7 : d - 1 ≤ count C 7 := by omega
              have hmid : 2 * (a + (b + 1) + (c + 1) + (d - 1)) =
                  count C 4 + count C 5 + count C 6 + count C 7 := by omega
              have hge2 : 2 * (c + 1) + 2 * (d - 1) ≤ count C 2 + count C 3 + count C 6 + count C 7 := by omega
              have hge3 : 2 * (b + 1) + 2 * (d - 1) ≤ count C 1 + count C 3 + count C 5 + count C 7 := by omega
              exact use_witness C h07 hcnt0 a (b + 1) (c + 1) (d - 1) hb4 hb5 hb6 hb7 hmid hge2 hge3
            · -- exceptional: |4| = 0, |7| = 0, |5|,|6| odd → Table 2
              have h40 : count C 4 = 0 := by omega
              have h70 : count C 7 = 0 := by omega
              have h5o : Odd (count C 5) := (odd_of_not_even h5)
              have h6o : Odd (count C 6) := (odd_of_not_even h6)
              rcases h5o with ⟨b, h5b⟩
              rcases h6o with ⟨c, h6c⟩
              -- not C0-form → at least one of |1|,|2|,|3| is positive
              have h123 : 0 < count C 1 + count C 2 + count C 3 := by
                by_contra h
                have hsum0 : count C 1 = 0 ∧ count C 2 = 0 ∧ count C 3 = 0 := by omega
                have hC0 : C0form C := (C0form_iff_Columns07 C h07).mpr
                  ⟨hsum0.1, hsum0.2.1, hsum0.2.2, h40, h70, odd_of_not_even h5, odd_of_not_even h6⟩
                exact hnotC0 hC0
              by_cases h1pos : 0 < count C 1
              · -- Table 2, |1| > 0: w5 = (|5|+1)/2, w6 = (|6|-1)/2
                have hb4 : (0 : ℕ) ≤ count C 4 := by omega
                have hb5 : b + 1 ≤ count C 5 := by omega
                have hb6 : c ≤ count C 6 := by omega
                have hb7 : (0 : ℕ) ≤ count C 7 := by omega
                have hmid : 2 * ((0 : ℕ) + (b + 1) + c + 0) =
                    count C 4 + count C 5 + count C 6 + count C 7 := by omega
                have hge2 : 2 * c + 2 * 0 ≤ count C 2 + count C 3 + count C 6 + count C 7 := by omega
                have hge3 : 2 * (b + 1) + 2 * 0 ≤ count C 1 + count C 3 + count C 5 + count C 7 := by omega
                exact use_witness C h07 hcnt0 0 (b + 1) c 0 hb4 hb5 hb6 hb7 hmid hge2 hge3
              · by_cases h2pos : 0 < count C 2
                · -- Table 2, |2| > 0: w5 = (|5|-1)/2, w6 = (|6|+1)/2
                  have hb4 : (0 : ℕ) ≤ count C 4 := by omega
                  have hb5 : b ≤ count C 5 := by omega
                  have hb6 : c + 1 ≤ count C 6 := by omega
                  have hb7 : (0 : ℕ) ≤ count C 7 := by omega
                  have hmid : 2 * ((0 : ℕ) + b + (c + 1) + 0) =
                      count C 4 + count C 5 + count C 6 + count C 7 := by omega
                  have hge2 : 2 * (c + 1) + 2 * 0 ≤ count C 2 + count C 3 + count C 6 + count C 7 := by omega
                  have hge3 : 2 * b + 2 * 0 ≤ count C 1 + count C 3 + count C 5 + count C 7 := by omega
                  exact use_witness C h07 hcnt0 0 b (c + 1) 0 hb4 hb5 hb6 hb7 hmid hge2 hge3
                · -- Table 2, |3| > 0 (must hold since |1|,|2| = 0 and sum > 0)
                  have h3pos : 0 < count C 3 := by omega
                  have hb4 : (0 : ℕ) ≤ count C 4 := by omega
                  have hb5 : b + 1 ≤ count C 5 := by omega
                  have hb6 : c ≤ count C 6 := by omega
                  have hb7 : (0 : ℕ) ≤ count C 7 := by omega
                  have hmid : 2 * ((0 : ℕ) + (b + 1) + c + 0) =
                      count C 4 + count C 5 + count C 6 + count C 7 := by omega
                  have hge2 : 2 * c + 2 * 0 ≤ count C 2 + count C 3 + count C 6 + count C 7 := by omega
                  have hge3 : 2 * (b + 1) + 2 * 0 ≤ count C 1 + count C 3 + count C 5 + count C 7 := by omega
                  exact use_witness C h07 hcnt0 0 (b + 1) c 0 hb4 hb5 hb6 hb7 hmid hge2 hge3
        · -- (E,O,O,O): three odds — impossible
          exfalso
          rcases hWeven with ⟨m, hm⟩
          rcases h4 with ⟨a, h4a⟩
          have h5o : Odd (count C 5) := (odd_of_not_even h5)
          rcases h5o with ⟨b, h5b⟩
          have h6o : Odd (count C 6) := (odd_of_not_even h6)
          rcases h6o with ⟨c, h6c⟩
          have h7o : Odd (count C 7) := (odd_of_not_even h7)
          rcases h7o with ⟨d, h7d⟩
          omega
  · by_cases h5 : Even (count C 5)
    · by_cases h6 : Even (count C 6)
      · by_cases h7 : Even (count C 7)
        · -- (O,E,E,E): one odd — impossible
          exfalso
          rcases hWeven with ⟨m, hm⟩
          have h4o : Odd (count C 4) := (odd_of_not_even h4)
          rcases h4o with ⟨a, h4a⟩
          rcases h5 with ⟨b, h5b⟩
          rcases h6 with ⟨c, h6c⟩
          rcases h7 with ⟨d, h7d⟩
          omega
        · -- case 4: (O,E,E,O) — w = (1/2,0,0,-1/2)
          have h4o : Odd (count C 4) := (odd_of_not_even h4)
          rcases h4o with ⟨a, h4a⟩
          rcases h5 with ⟨b, h5b⟩
          rcases h6 with ⟨c, h6c⟩
          have h7o : Odd (count C 7) := (odd_of_not_even h7)
          rcases h7o with ⟨d, h7d⟩
          let k : ℕ → ℕ := tableK (a + 1) b c d
          exact witness_from_k C h07 k hcnt0 (tableK_0 (a + 1) b c d) (tableK_03 (a + 1) b c d)
            (tableK_bounds_47 C (a + 1) b c d hcnt0 (by omega) (by omega) (by omega) (by omega))
            (tableK_815 (a + 1) b c d)
            (by simp [k, tableK]; omega)
            (by simp [k, tableK]; omega)
            (by simp [k, tableK]; omega)
      · by_cases h7 : Even (count C 7)
        · -- case 3: (O,E,O,E) — w = (1/2,0,-1/2,0)
          have h4o : Odd (count C 4) := (odd_of_not_even h4)
          rcases h4o with ⟨a, h4a⟩
          rcases h5 with ⟨b, h5b⟩
          have h6o : Odd (count C 6) := (odd_of_not_even h6)
          rcases h6o with ⟨c, h6c⟩
          rcases h7 with ⟨d, h7d⟩
          let k : ℕ → ℕ := tableK (a + 1) b c d
          exact witness_from_k C h07 k hcnt0 (tableK_0 (a + 1) b c d) (tableK_03 (a + 1) b c d)
            (tableK_bounds_47 C (a + 1) b c d hcnt0 (by omega) (by omega) (by omega) (by omega))
            (tableK_815 (a + 1) b c d)
            (by simp [k, tableK]; omega)
            (by simp [k, tableK]; omega)
            (by simp [k, tableK]; omega)
        · -- (O,E,O,O): three odds — impossible
          exfalso
          rcases hWeven with ⟨m, hm⟩
          have h4o : Odd (count C 4) := (odd_of_not_even h4)
          rcases h4o with ⟨a, h4a⟩
          rcases h5 with ⟨b, h5b⟩
          have h6o : Odd (count C 6) := (odd_of_not_even h6)
          rcases h6o with ⟨c, h6c⟩
          have h7o : Odd (count C 7) := (odd_of_not_even h7)
          rcases h7o with ⟨d, h7d⟩
          omega
    · by_cases h6 : Even (count C 6)
      · by_cases h7 : Even (count C 7)
        · -- case 2: (O,O,E,E) — w = (1/2,-1/2,0,0)
          have h4o : Odd (count C 4) := (odd_of_not_even h4)
          rcases h4o with ⟨a, h4a⟩
          have h5o : Odd (count C 5) := (odd_of_not_even h5)
          rcases h5o with ⟨b, h5b⟩
          rcases h6 with ⟨c, h6c⟩
          rcases h7 with ⟨d, h7d⟩
          let k : ℕ → ℕ := tableK (a + 1) b c d
          exact witness_from_k C h07 k hcnt0 (tableK_0 (a + 1) b c d) (tableK_03 (a + 1) b c d)
            (tableK_bounds_47 C (a + 1) b c d hcnt0 (by omega) (by omega) (by omega) (by omega))
            (tableK_815 (a + 1) b c d)
            (by simp [k, tableK]; omega)
            (by simp [k, tableK]; omega)
            (by simp [k, tableK]; omega)
        · -- (O,O,E,O): three odds — impossible
          exfalso
          rcases hWeven with ⟨m, hm⟩
          have h4o : Odd (count C 4) := (odd_of_not_even h4)
          rcases h4o with ⟨a, h4a⟩
          have h5o : Odd (count C 5) := (odd_of_not_even h5)
          rcases h5o with ⟨b, h5b⟩
          rcases h6 with ⟨c, h6c⟩
          have h7o : Odd (count C 7) := (odd_of_not_even h7)
          rcases h7o with ⟨d, h7d⟩
          omega
      · by_cases h7 : Even (count C 7)
        · -- (O,O,O,E): three odds — impossible
          exfalso
          rcases hWeven with ⟨m, hm⟩
          have h4o : Odd (count C 4) := (odd_of_not_even h4)
          rcases h4o with ⟨a, h4a⟩
          have h5o : Odd (count C 5) := (odd_of_not_even h5)
          rcases h5o with ⟨b, h5b⟩
          have h6o : Odd (count C 6) := (odd_of_not_even h6)
          rcases h6o with ⟨c, h6c⟩
          rcases h7 with ⟨d, h7d⟩
          omega
        · -- case 8: (O,O,O,O) — w = (1/2,1/2,-1/2,-1/2)
          have h4o : Odd (count C 4) := (odd_of_not_even h4)
          rcases h4o with ⟨a, h4a⟩
          have h5o : Odd (count C 5) := (odd_of_not_even h5)
          rcases h5o with ⟨b, h5b⟩
          have h6o : Odd (count C 6) := (odd_of_not_even h6)
          rcases h6o with ⟨c, h6c⟩
          have h7o : Odd (count C 7) := (odd_of_not_even h7)
          rcases h7o with ⟨d, h7d⟩
          let k : ℕ → ℕ := tableK (a + 1) (b + 1) c d
          exact witness_from_k C h07 k hcnt0 (tableK_0 (a + 1) (b + 1) c d) (tableK_03 (a + 1) (b + 1) c d)
            (tableK_bounds_47 C (a + 1) (b + 1) c d hcnt0 (by omega) (by omega) (by omega) (by omega))
            (tableK_815 (a + 1) (b + 1) c d)
            (by simp [k, tableK]; omega)
            (by simp [k, tableK]; omega)
            (by simp [k, tableK]; omega)

/-! ## Normalization: an even-distance pair of codewords -/

/-- Sums are additive modulo two. -/
lemma sum_mod_two {α : Type*} (s : Finset α) (f : α → ℕ) :
    (∑ t ∈ s, f t) % 2 = (∑ t ∈ s, f t % 2) % 2 := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a s' has ih
    rw [Finset.sum_insert has, Finset.sum_insert has, Nat.add_mod, ih]
    simp [Nat.add_mod]

/-- The weight of an XOR is additive modulo two. -/
lemma hammingWeight_xor_mod2 {n : ℕ} (x y : Word n) :
    hammingWeight (bitXor x y) % 2 = (hammingWeight x + hammingWeight y) % 2 := by
  unfold hammingWeight
  calc
    (∑ t : Fin n, if bitXor x y t = true then 1 else 0) % 2
        = (∑ t : Fin n, (if bitXor x y t = true then 1 else 0) % 2) % 2 := sum_mod_two _ _
    _ = (∑ t : Fin n, ((if x t = true then 1 else 0) + (if y t = true then 1 else 0)) % 2) % 2 := by
          congr 1
          apply Finset.sum_congr rfl
          intro t _
          cases hx : x t <;> cases hy : y t <;> simp [bitXor, hx, hy]
    _ = (∑ t : Fin n, ((if x t = true then 1 else 0) + (if y t = true then 1 else 0))) % 2 := (sum_mod_two _ _).symm
    _ = ((∑ t : Fin n, if x t = true then 1 else 0) + (∑ t : Fin n, if y t = true then 1 else 0)) % 2 := by
          rw [Finset.sum_add_distrib]

/-- Hamming distance is additive modulo two (triangle parity). -/
lemma hammingDist_mod2 {n : ℕ} (x y z : Word n) :
    hammingDist x z % 2 = (hammingDist x y + hammingDist y z) % 2 := by
  unfold hammingDist
  have hxor : bitXor x z = bitXor (bitXor x y) (bitXor y z) := by
    funext t
    cases hx : x t <;> cases hy : y t <;> cases hz : z t <;> simp [bitXor, hx, hy, hz]
  calc
    hammingWeight (bitXor x z) % 2
        = hammingWeight (bitXor (bitXor x y) (bitXor y z)) % 2 := by rw [hxor]
    _ = (hammingWeight (bitXor x y) + hammingWeight (bitXor y z)) % 2 :=
          hammingWeight_xor_mod2 (bitXor x y) (bitXor y z)

/-- Among the four codewords there are two at even distance. -/
lemma even_pair {n : ℕ} (C : Code n) : ∃ i j : Fin 4, i ≠ j ∧
    Even (hammingDist (row C i) (row C j)) := by
  by_cases h01 : Even (hammingDist (row C 0) (row C 1))
  · exact ⟨0, 1, by decide, h01⟩
  · by_cases h02 : Even (hammingDist (row C 0) (row C 2))
    · exact ⟨0, 2, by decide, h02⟩
    · -- d(0,1) and d(0,2) are odd → d(1,2) is even
      have h01o : Odd (hammingDist (row C 0) (row C 1)) := odd_of_not_even h01
      have h02o : Odd (hammingDist (row C 0) (row C 2)) := odd_of_not_even h02
      rcases h01o with ⟨a, h01a⟩
      rcases h02o with ⟨b, h02b⟩
      have hmod : hammingDist (row C 1) (row C 2) % 2 = 0 := by
        have h := hammingDist_mod2 (row C 1) (row C 0) (row C 2)
        have hsym : hammingDist (row C 1) (row C 0) = hammingDist (row C 0) (row C 1) :=
          hammingDist_symm _ _
        have hzero : (2 * a + 1 + (2 * b + 1)) % 2 = 0 := by
          have hsum : 2 * a + 1 + (2 * b + 1) = 2 * (a + b + 1) := by omega
          rw [hsum, Nat.mul_mod]
          norm_num
        rw [hsym, h01a, h02b, hzero] at h
        exact h
      have h12e : Even (hammingDist (row C 1) (row C 2)) := by
        have hdiv := Nat.div_add_mod (hammingDist (row C 1) (row C 2)) 2
        have hn : hammingDist (row C 1) (row C 2) = 2 * (hammingDist (row C 1) (row C 2) / 2) := by
          rw [hmod, add_zero] at hdiv
          rw [mul_comm] at hdiv
          calc
            hammingDist (row C 1) (row C 2) = hammingDist (row C 1) (row C 2) / 2 * 2 := hdiv.symm
            _ = 2 * (hammingDist (row C 1) (row C 2) / 2) := by rw [mul_comm]
        refine ⟨hammingDist (row C 1) (row C 2) / 2, ?_⟩
        have : 2 * (hammingDist (row C 1) (row C 2) / 2) =
            hammingDist (row C 1) (row C 2) / 2 + hammingDist (row C 1) (row C 2) / 2 := by rw [two_mul]
        rw [← this, ← hn]
      exact ⟨1, 2, by decide, h12e⟩

/-! ## Normalization to row 0 = 0 with an even second row -/

/-- The row permutation sending i to 0 and j to 1. -/
def permEven (i j : Fin 4) : Equiv (Fin 4) (Fin 4) :=
  (Equiv.swap i (0 : Fin 4)).trans (Equiv.swap (Equiv.swap i (0 : Fin 4) j) (1 : Fin 4))

lemma permEven_i (i j : Fin 4) (hij : i ≠ j) : permEven i j i = (0 : Fin 4) := by
  unfold permEven
  have he1i : Equiv.swap i (0 : Fin 4) i = (0 : Fin 4) := Equiv.swap_apply_left i (0 : Fin 4)
  have he1j0 : Equiv.swap i (0 : Fin 4) j ≠ (0 : Fin 4) := by
    rw [Equiv.swap_apply_def]
    by_cases hji : j = i
    · exfalso
      exact hij hji.symm
    · by_cases hj0 : j = (0 : Fin 4)
      · have hi0 : i ≠ (0 : Fin 4) := by
          intro h
          exact hij (h.trans hj0.symm)
        rw [hj0]
        have h0i : (0 : Fin 4) ≠ i := fun h => hji (h.symm.trans hj0.symm).symm
        have hvalue : (if (0 : Fin 4) = i then (0 : Fin 4)
            else if (0 : Fin 4) = (0 : Fin 4) then i else (0 : Fin 4)) = i := by
          simp [h0i]
        rw [hvalue]
        exact hi0
      · simp [hj0, hji]
  calc
    permEven i j i = Equiv.swap (Equiv.swap i (0 : Fin 4) j) (1 : Fin 4)
        (Equiv.swap i (0 : Fin 4) i) := rfl
    _ = Equiv.swap (Equiv.swap i (0 : Fin 4) j) (1 : Fin 4) (0 : Fin 4) := by rw [he1i]
    _ = (0 : Fin 4) := by
      have h01 : (0 : Fin 4) ≠ (1 : Fin 4) := by decide
      exact Equiv.swap_apply_of_ne_of_ne (fun h => he1j0 h.symm) h01

lemma permEven_j (i j : Fin 4) (_hij : i ≠ j) : permEven i j j = (1 : Fin 4) := by
  unfold permEven
  calc
    permEven i j j = Equiv.swap (Equiv.swap i (0 : Fin 4) j) (1 : Fin 4)
        (Equiv.swap i (0 : Fin 4) j) := rfl
    _ = (1 : Fin 4) := Equiv.swap_apply_left (Equiv.swap i (0 : Fin 4) j) (1 : Fin 4)

-- native_decide: Mechanical · n=any · checked 2026-08-27
/-- For n ≤ 7, bit 2 of n is 1 exactly for types 4..7. -/
lemma testBit2_of_le7 (n : ℕ) (hn : n ≤ 7) :
    (n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7) ↔ n.testBit 2 = true := by
  have hk : ∃ k : Fin 8, (k : ℕ) = n := ⟨⟨n, by omega⟩, rfl⟩
  rcases hk with ⟨k, hk⟩
  subst n
  fin_cases k <;> native_decide

/-- The normalized code: rows permuted so the even pair becomes rows 0,1, and
column flips make row 0 all zeros. -/
def normalizeCode {n : ℕ} (C : Code n) (i j : Fin 4) : Code n :=
  fun t => rowPermute (permEven i j).symm (if (row C i) t then flipCol (C t) else C t)

lemma Equivalent_normalize {n : ℕ} (C : Code n) (i j : Fin 4) :
    Equivalent C (normalizeCode C i j) := by
  refine ⟨(permEven i j).symm, Equiv.refl (Fin n), fun t => (row C i) t, ?_⟩
  intro t
  rfl

/-- Row 0 of the normalized code is all zeros. -/
lemma row0_normalize {n : ℕ} (C : Code n) (i j : Fin 4) (hij : i ≠ j) :
    row (normalizeCode C i j) 0 = (fun _ : Fin n => false) := by
  funext t
  have hi : (permEven i j).symm (0 : Fin 4) = i :=
    (Equiv.symm_apply_eq (e := permEven i j) (x := (0 : Fin 4)) (y := i)).mpr
      (permEven_i i j hij).symm
  unfold row colBit normalizeCode rowPermute
  rw [hi]
  by_cases hc : C t i
  · simp [row, colBit, flipCol, hc]
  · simp [row, colBit, hc]

/-- Row 1 of the normalized code is the XOR of the even pair. -/
lemma row1_normalize {n : ℕ} (C : Code n) (i j : Fin 4) (hij : i ≠ j) :
    row (normalizeCode C i j) 1 = bitXor (row C i) (row C j) := by
  funext t
  have hj : (permEven i j).symm (1 : Fin 4) = j :=
    (Equiv.symm_apply_eq (e := permEven i j) (x := (1 : Fin 4)) (y := j)).mpr
      (permEven_j i j hij).symm
  unfold row colBit normalizeCode rowPermute
  rw [hj]
  by_cases hc : C t i
  · simp [row, colBit, flipCol, hc, bitXor]
  · simp [row, colBit, hc, bitXor]

/-- The normalized code has row 0 all zeros. -/
lemma Columns07_normalize {n : ℕ} (C : Code n) (i j : Fin 4) (hij : i ≠ j) :
    Columns07 (normalizeCode C i j) := by
  intro t
  have hrow := congrFun (row0_normalize C i j hij) t
  change colBit 0 (normalizeCode C i j t) = false
  simpa [row, colBit] using hrow

/-- In a Columns07 code, |4|+|5|+|6|+|7| is the weight of row 2. -/
lemma sum_counts_4_7 {n : ℕ} (C : Code n) (h07 : Columns07 C) :
    count C 4 + count C 5 + count C 6 + count C 7 = hammingWeight (row C 1) := by
  have hcomb : count C 4 + count C 5 + count C 6 + count C 7 =
      ∑ t : Fin n, (if colVal (C t) = 4 ∨ colVal (C t) = 5 ∨ colVal (C t) = 6 ∨ colVal (C t) = 7
        then 1 else 0) := by
    unfold count
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t _
    by_cases h4 : colVal (C t) = 4 <;> by_cases h5 : colVal (C t) = 5 <;>
      by_cases h6 : colVal (C t) = 6 <;> by_cases h7 : colVal (C t) = 7 <;>
        simp [h4, h5, h6, h7]
  rw [hcomb]
  unfold hammingWeight row
  change (∑ t : Fin n, if colVal (C t) = 4 ∨ colVal (C t) = 5 ∨ colVal (C t) = 6 ∨ colVal (C t) = 7
      then 1 else 0) =
      ∑ t : Fin n, if colBit 1 (C t) then 1 else 0
  apply Finset.sum_congr rfl
  intro t _
  have hb := colBit_eq_testBit (C t) ⟨1, by decide⟩
  have hle := Columns07_le7 C h07 t
  have hiff : (colVal (C t) = 4 ∨ colVal (C t) = 5 ∨ colVal (C t) = 6 ∨ colVal (C t) = 7) ↔
      colBit 1 (C t) = true := by
    have htb := testBit2_of_le7 (colVal (C t)) hle
    have hb' : colBit 1 (C t) = (colVal (C t)).testBit 2 := by simpa using hb
    rwa [← hb'] at htb
  simp [hiff]

/-- A code with a 0-column has a position with the zero column. -/
lemma exists_col0_of_count_pos {n : ℕ} (C : Code n) (h : 1 ≤ count C 0) :
    ∃ t : Fin n, C t = col0 := by
  rcases (count_pos_iff_exists C 0).mp (by omega : count C 0 > 0) with ⟨t, ht⟩
  exact ⟨t, (colVal_eq_zero_iff_col0 (C t)).mp ht⟩

/-- The normalized code keeps a 0-column. -/
lemma count0_normalize {n : ℕ} (C : Code n) (i j : Fin 4) (_hij : i ≠ j)
    (h : 1 ≤ count C 0) : 1 ≤ count (normalizeCode C i j) 0 := by
  rcases exists_col0_of_count_pos C h with ⟨t, ht⟩
  have ht' : normalizeCode C i j t = col0 := by
    unfold normalizeCode
    have hf : row C i t = false := by
      rw [row, colBit]
      simp [ht, col0]
    have hrp : rowPermute (permEven i j).symm col0 = col0 := by
      funext k
      simp [rowPermute, col0]
    simp [ht, hf, hrp]
  have hmem : t ∈ (Finset.univ.filter fun u : Fin n => colVal (normalizeCode C i j u) = 0) := by
    simp [ht', colVal, col0]
  have hcard : 1 ≤ (Finset.univ.filter fun u : Fin n => colVal (normalizeCode C i j u) = 0).card := by
    exact Nat.succ_le_of_lt (Finset.card_pos.mpr ⟨t, hmem⟩)
  simpa [count_eq_card] using hcard

/-- The normalized code has even W = |4|+|5|+|6|+|7|. -/
lemma even_W_normalize {n : ℕ} (C : Code n) (i j : Fin 4) (hij : i ≠ j)
    (hEven : Even (hammingDist (row C i) (row C j))) :
    Even (count (normalizeCode C i j) 4 + count (normalizeCode C i j) 5 +
      count (normalizeCode C i j) 6 + count (normalizeCode C i j) 7) := by
  have h07 := Columns07_normalize C i j hij
  have hsum := sum_counts_4_7 (normalizeCode C i j) h07
  have hrow := row1_normalize C i j hij
  have hw : hammingWeight (bitXor (row C i) (row C j)) = hammingDist (row C i) (row C j) := rfl
  rw [hsum, hrow, hw]
  exact hEven

/-- The normalized code is not in the C0 form. -/
lemma notC0_normalize {n : ℕ} (C : Code n) (i j : Fin 4)
    (hC0 : ¬ ∃ C0 : Code n, Equivalent C C0 ∧ C0form C0) :
    ¬ C0form (normalizeCode C i j) := by
  intro h
  exact hC0 ⟨normalizeCode C i j, Equivalent_normalize C i j, h⟩

/-! ## Transfer back to the original code -/

/-- A column with exactly two ones has type 3, 5, 6, 9, 10, or 12. -/
lemma colVal_two_bit (c : Column)
    (h : ∃ a b : Fin 4, a ≠ b ∧ (c = fun j : Fin 4 => j = a ∨ j = b)) :
    colVal c = 3 ∨ colVal c = 5 ∨ colVal c = 6 ∨ colVal c = 9 ∨ colVal c = 10 ∨ colVal c = 12 := by
  rcases h with ⟨a, b, hab, hc⟩
  subst c
  have h' : ∀ a b : Fin 4, a ≠ b →
      (colVal (fun j : Fin 4 => j = a ∨ j = b) = 3 ∨
       colVal (fun j : Fin 4 => j = a ∨ j = b) = 5 ∨
       colVal (fun j : Fin 4 => j = a ∨ j = b) = 6 ∨
       colVal (fun j : Fin 4 => j = a ∨ j = b) = 9 ∨
       colVal (fun j : Fin 4 => j = a ∨ j = b) = 10 ∨
       colVal (fun j : Fin 4 => j = a ∨ j = b) = 12) := by
    decide
  exact h' a b hab

/-- Row-permuting the type-5 column gives a two-bit column. -/
lemma colVal_rowPermute_col5 (ρ : Equiv (Fin 4) (Fin 4)) :
    colVal (rowPermute ρ col5) = 3 ∨ colVal (rowPermute ρ col5) = 5 ∨
      colVal (rowPermute ρ col5) = 6 ∨ colVal (rowPermute ρ col5) = 9 ∨
      colVal (rowPermute ρ col5) = 10 ∨ colVal (rowPermute ρ col5) = 12 := by
  have h : rowPermute ρ col5 = fun j : Fin 4 => j = ρ.symm 1 ∨ j = ρ.symm 3 := by
    funext j
    have hv1 : (ρ j).val = 1 ↔ j = ρ.symm 1 := by
      calc
        (ρ j).val = 1 ↔ ρ j = (1 : Fin 4) :=
          (Fin.ext_iff (a := ρ j) (b := (1 : Fin 4))).symm
        _ ↔ j = ρ.symm 1 := (Equiv.eq_symm_apply ρ (x := (1 : Fin 4)) (y := j)).symm
    have hv3 : (ρ j).val = 3 ↔ j = ρ.symm 3 := by
      calc
        (ρ j).val = 3 ↔ ρ j = (3 : Fin 4) :=
          (Fin.ext_iff (a := ρ j) (b := (3 : Fin 4))).symm
        _ ↔ j = ρ.symm 3 := (Equiv.eq_symm_apply ρ (x := (3 : Fin 4)) (y := j)).symm
    simp [col5, rowPermute, hv1, hv3]
  refine colVal_two_bit (rowPermute ρ col5) ⟨ρ.symm 1, ρ.symm 3, ?_, h⟩
  -- ρ⁻¹ 1 ≠ ρ⁻¹ 3 — injective
  intro hEq
  have : (1 : Fin 4) = (3 : Fin 4) := ρ.symm.injective hEq
  exact (by decide : (1 : Fin 4) ≠ (3 : Fin 4)) this

/-- Flipping the type-5 column gives the two-bit column with ones at 0 and 2. -/
lemma flipCol_col5_val (k : Fin 4) :
    (!(col5 k)) = decide (k = (0 : Fin 4) ∨ k = (2 : Fin 4)) := by
  fin_cases k <;> simp [col5]

/-- Row-permuting the flip of the type-5 column gives a two-bit column. -/
lemma colVal_rowPermute_flipCol5 (ρ : Equiv (Fin 4) (Fin 4)) :
    colVal (rowPermute ρ (flipCol col5)) = 3 ∨ colVal (rowPermute ρ (flipCol col5)) = 5 ∨
      colVal (rowPermute ρ (flipCol col5)) = 6 ∨ colVal (rowPermute ρ (flipCol col5)) = 9 ∨
      colVal (rowPermute ρ (flipCol col5)) = 10 ∨ colVal (rowPermute ρ (flipCol col5)) = 12 := by
  have h : rowPermute ρ (flipCol col5) = fun j : Fin 4 => j = ρ.symm 0 ∨ j = ρ.symm 2 := by
    funext j
    have hb0 : (ρ j = (0 : Fin 4)) ↔ j = ρ.symm 0 :=
      (Equiv.eq_symm_apply ρ (x := (0 : Fin 4)) (y := j)).symm
    have hb2 : (ρ j = (2 : Fin 4)) ↔ j = ρ.symm 2 :=
      (Equiv.eq_symm_apply ρ (x := (2 : Fin 4)) (y := j)).symm
    calc
      rowPermute ρ (flipCol col5) j = !(col5 (ρ j)) := by simp [rowPermute, flipCol]
      _ = decide (ρ j = (0 : Fin 4) ∨ ρ j = (2 : Fin 4)) := by
        simpa using (flipCol_col5_val (ρ j))
      _ = decide (j = ρ.symm 0 ∨ j = ρ.symm 2) := by
        simp [hb0, hb2]
  refine colVal_two_bit (rowPermute ρ (flipCol col5)) ⟨ρ.symm 0, ρ.symm 2, ?_, h⟩
  -- ρ⁻¹ 0 ≠ ρ⁻¹ 2 — injective
  intro hEq
  have : (0 : Fin 4) = (2 : Fin 4) := ρ.symm.injective hEq
  exact (by decide : (0 : Fin 4) ≠ (2 : Fin 4)) this


/-- Row permutation composed with its inverse is the identity. -/
lemma rowPermute_symm (ρ : Equiv (Fin 4) (Fin 4)) (c : Column) :
    rowPermute ρ (rowPermute ρ.symm c) = c := by
  funext j
  simp [rowPermute, Equiv.symm_apply_apply]

/-- The zero column is fixed by any row permutation. -/
lemma rowPermute_col0 (ρ : Equiv (Fin 4) (Fin 4)) : rowPermute ρ col0 = col0 := by
  funext k
  simp [rowPermute, col0]

/-- Flipping the zero column gives the all-ones column. -/
lemma flipCol_col0 : flipCol col0 = col15 := by
  funext k
  simp [flipCol, col0, col15]

/-- If normalization leaves a zero column with flip disabled, the original
column is zero. -/
lemma col0_of_normalize_col0 {n : ℕ} (C : Code n) (i j : Fin 4) (t : Fin n)
    (h0n : (normalizeCode C i j) t = col0) (hf : (row C i) t = false) : C t = col0 := by
  set ρ := (permEven i j).symm
  have h : rowPermute ρ (C t) = col0 := by
    unfold normalizeCode at h0n
    simpa [hf] using h0n
  have hinv : C t = rowPermute (permEven i j) col0 := by
    have := congr_arg (rowPermute (permEven i j)) h
    rw [rowPermute_symm] at this
    exact this
  rw [hinv, rowPermute_col0]

/-- A true zero column is never flipped during normalization. -/
lemma row_i_false_of_col0 {n : ℕ} (C : Code n) (i : Fin 4) (t : Fin n) (h0 : C t = col0) :
    (row C i) t = false := by
  simp [row, colBit, h0, col0]

/-! ## Assembling `thm:0column` (Theorem 6) (2) -/

/-- Swapping the bits at two positions of a word. -/
def swapBits {n : ℕ} (t₁ t' : Fin n) (y : Word n) : Word n :=
  fun u => if u = t₁ then y t' else if u = t' then y t₁ else y u

/-- Swapping two bits does not change the Hamming weight. -/
lemma hammingWeight_swapBits {n : ℕ} (t₁ t' : Fin n) (z : Word n) :
    hammingWeight (swapBits t₁ t' z) = hammingWeight z := by
  unfold hammingWeight
  have hfun : swapBits t₁ t' z = fun u : Fin n => z ((Equiv.swap t₁ t') u) := by
    funext u
    by_cases hut : u = t'
    · subst u
      by_cases ht₁ : t' = t₁
      · subst t₁
        simp [swapBits]
      · simp [swapBits, Equiv.swap_apply_right, ht₁]
    · by_cases hu₁ : u = t₁
      · subst u
        simp [swapBits, Equiv.swap_apply_left]
      · simp [swapBits, hu₁, hut, Equiv.swap_apply_of_ne_of_ne hu₁ hut]
  rw [hfun]
  apply Finset.sum_bij (fun u _ => (Equiv.swap t₁ t') u)
  · intro u _
    simp
  · intro a _ b _ hab
    exact (Equiv.swap t₁ t').injective hab
  · intro b _
    exact ⟨(Equiv.swap t₁ t').symm b, by simp, by simp⟩
  · intro u _
    simp

/-- Row-permutation composition. -/
lemma rowPermute_comp (ρ₁ ρ₂ : Equiv (Fin 4) (Fin 4)) (c : Column) :
    rowPermute ρ₁ (rowPermute ρ₂ c) = rowPermute (ρ₁.trans ρ₂) c := by
  funext j
  rfl

/-- Row-permuting by ρ then ρ⁻¹ is the identity. -/
lemma rowPermute_left_inv (ρ : Equiv (Fin 4) (Fin 4)) (c : Column) :
    rowPermute ρ.symm (rowPermute ρ c) = c := by
  funext j
  simp [rowPermute, Equiv.apply_symm_apply]

/-- Flipping commutes with row permutation. -/
lemma flipCol_rowPermute (ρ : Equiv (Fin 4) (Fin 4)) (c : Column) :
    flipCol (rowPermute ρ c) = rowPermute ρ (flipCol c) := by
  funext j
  rfl

/-- `flipCol` is an involution. -/
lemma flipCol_involutive (c : Column) : flipCol (flipCol c) = c := by
  ext j
  simp [flipCol]

/-- Row permutations and flips commute. -/
lemma rowPermute_flipCol (ρ : Equiv (Fin 4) (Fin 4)) (c : Column) :
    rowPermute ρ (flipCol c) = flipCol (rowPermute ρ c) := by
  ext j
  simp [rowPermute, flipCol]

/-- Equivalence is reflexive. -/
lemma equivalent_refl {n : ℕ} (C : Code n) : Equivalent C C := by
  refine ⟨Equiv.refl (Fin 4), Equiv.refl (Fin n), fun _ => false, ?_⟩
  intro t
  change C t = rowPermute (Equiv.refl (Fin 4)) (C t)
  ext j
  simp [rowPermute]

/-- Equivalence is symmetric. -/
lemma equivalent_symm {n : ℕ} {C C' : Code n} (h : Equivalent C C') : Equivalent C' C := by
  rcases h with ⟨ρ, p, f, h⟩
  refine ⟨ρ.symm, p.symm, fun t => f (p.symm t), ?_⟩
  intro t
  have hs : p (p.symm t) = t := p.apply_symm_apply t
  have ht : C' t = rowPermute ρ (if f (p.symm t) then flipCol (C (p.symm t)) else C (p.symm t)) := by
    simpa [hs] using h (p.symm t)
  by_cases hf : f (p.symm t) = true
  · -- flipped case
    have hρ : rowPermute ρ.symm (C' t) = flipCol (C (p.symm t)) := by
      rw [ht]
      simp [hf]
      rw [rowPermute_comp, rowPermute_flipCol]
      have hρρ : ρ.symm.trans ρ = Equiv.refl (Fin 4) := by
        ext j
        simp
      rw [hρρ]
      rfl
    have hCs : C (p.symm t) = flipCol (rowPermute ρ.symm (C' t)) := by
      rw [hρ]
      exact (flipCol_involutive (C (p.symm t))).symm
    have hmain : C (p.symm t) = rowPermute ρ.symm (flipCol (C' t)) := by
      rw [rowPermute_flipCol, hCs]
    simpa [hf] using hmain
  · -- unflipped case
    have hρ : rowPermute ρ.symm (C' t) = C (p.symm t) := by
      rw [ht]
      simp [hf]
      rw [rowPermute_comp]
      have hρρ : ρ.symm.trans ρ = Equiv.refl (Fin 4) := by
        ext j
        simp
      rw [hρρ]
      rfl
    simpa [hf] using hρ.symm

/-- Row-permutation algebra for composing two equivalences (the XOR flip). -/
lemma rowPermute_xor {ρ₁ ρ₂ : Equiv (Fin 4) (Fin 4)} (b₁ b₂ : Bool) (c : Column) :
    rowPermute ρ₂ (if b₂ = true then flipCol (rowPermute ρ₁ (if b₁ = true then flipCol c else c))
        else rowPermute ρ₁ (if b₁ = true then flipCol c else c)) =
      rowPermute (ρ₂.trans ρ₁) (if (b₁ != b₂) = true then flipCol c else c) := by
  by_cases h1 : b₁ = true <;> by_cases h2 : b₂ = true <;>
    simp [h1, h2, rowPermute_flipCol, rowPermute_comp, flipCol_involutive]

/-- Equivalence is transitive. -/
lemma equivalent_trans {n : ℕ} {C₁ C₂ C₃ : Code n} (h12 : Equivalent C₁ C₂)
    (h23 : Equivalent C₂ C₃) : Equivalent C₁ C₃ := by
  rcases h12 with ⟨ρ₁, p₁, f₁, h₁⟩
  rcases h23 with ⟨ρ₂, p₂, f₂, h₂⟩
  refine ⟨ρ₂.trans ρ₁, p₁.trans p₂, fun t => f₁ t != f₂ (p₁ t), ?_⟩
  intro t
  have hp : (p₁.trans p₂) t = p₂ (p₁ t) := rfl
  rw [hp]
  rw [h₂ (p₁ t)]
  rw [h₁ t]
  exact rowPermute_xor (ρ₁ := ρ₁) (ρ₂ := ρ₂) (b₁ := f₁ t) (b₂ := f₂ (p₁ t)) (C₁ t)

/-- Swapping two bits of a word preserves every row distance when the two
positions hold zero columns. -/
lemma dRow_swapBit {n : ℕ} (C : Code n) (j : Fin 4) (t₁ t' : Fin n)
    (h1 : C t₁ = col0) (h' : C t' = col0) (y : Word n) :
    dRow C j (swapBits t₁ t' y) = dRow C j y := by
  unfold dRow hammingDist
  have hxor : bitXor (row C j) (swapBits t₁ t' y) = swapBits t₁ t' (bitXor (row C j) y) := by
    funext u
    by_cases hu₁ : u = t₁ <;> by_cases hut : u = t' <;>
      simp [swapBits, bitXor, row, colBit, col0, h1, h', hu₁, hut]
  calc
    dRow C j (swapBits t₁ t' y) = hammingWeight (bitXor (row C j) (swapBits t₁ t' y)) := rfl
    _ = hammingWeight (swapBits t₁ t' (bitXor (row C j) y)) := by rw [hxor]
    _ = hammingWeight (bitXor (row C j) y) := hammingWeight_swapBits t₁ t' (bitXor (row C j) y)
    _ = dRow C j y := rfl

/-- The minimum over S is unchanged when swapping two zero-column bits. -/
lemma dRowMin_swapBit {n : ℕ} (C : Code n) (S : Finset (Fin 4)) (hS : S.Nonempty)
    (t₁ t' : Fin n) (h1 : C t₁ = col0) (h' : C t' = col0) (y : Word n) :
    dRowMin C S hS (swapBits t₁ t' y) = dRowMin C S hS y := by
  unfold dRowMin
  have hcong : S.image (fun i => dRow C i (swapBits t₁ t' y)) = S.image (fun i => dRow C i y) := by
    apply Finset.image_congr
    intro i _
    exact dRow_swapBit C i t₁ t' h1 h' y
  simp [hcong]

/-- A Y3c witness at one zero column can be moved to any other zero column. -/
lemma Y3c_move {n : ℕ} (C : Code n) (s' : Column) (hO : (colZeros s').Nonempty)
    (hP : (colOnes s').Nonempty) (t₁ t' : Fin n)
    (h1 : C t₁ = col0) (h' : C t' = col0) :
    (∃ y : Word n, Y3c C s' hO hP t' y) → (∃ y : Word n, Y3c C s' hO hP t₁ y) := by
  rintro ⟨y, hy⟩
  refine ⟨swapBits t₁ t' y, ?_⟩
  constructor
  · simpa [swapBits] using hy.1
  · have hdO := dRowMin_swapBit C (colZeros s') hO t₁ t' h1 h' y
    have hdP := dRowMin_swapBit C (colOnes s') hP t₁ t' h1 h' y
    unfold Y3c at hy
    unfold dOc dPc at hy ⊢
    rw [hdO, hdP]
    exact hy.2

/-- Theorem `thm:0column` (Theorem 6) engine, strict version: a Y3c witness gives a
strict improvement. -/
theorem zero_column_strict_better {n : ℕ} (C : Code n) (t : Fin n) (s' : Column)
    (hcol : C t = col0) (hO : (colZeros s').Nonempty) (hP : (colOnes s').Nonempty)
    (hy : ∃ y : Word n, Y3c C s' hO hP t y) :
    UniversalStrictBetter (replaceColumn C t s') C := by
  let S : Finset (Word n) := Finset.univ.filter (Y3c C s' hO hP t)
  have hbij : Function.Bijective (g0 C s' hO hP t) := by
    constructor
    · intro a b hab
      calc
        a = g0 C s' hO hP t (g0 C s' hO hP t a) := (g0_involutive C s' hO hP t a hcol).symm
        _ = g0 C s' hO hP t (g0 C s' hO hP t b) := by rw [hab]
        _ = b := g0_involutive C s' hO hP t b hcol
    · intro z
      refine ⟨g0 C s' hO hP t z, ?_⟩
      exact g0_involutive C s' hO hP t z hcol
  let g : Word n ≃ Word n := Equiv.ofBijective (g0 C s' hO hP t) hbij
  have hgt : ∀ y : Word n, y ∈ S → dCode C y > dCode (replaceColumn C t s') (g y) := by
    intro y hy
    have hS : Y3c C s' hO hP t y := (Finset.mem_filter.mp hy).2
    have h := zero_closer C t s' hcol hO hP y hS
    have hlt : dCode (replaceColumn C t s') (g0 C s' hO hP t y) < dCode C y := by
      rw [h]
      omega
    simpa [g] using hlt
  have heq : ∀ y : Word n, y ∉ S → dCode C y = dCode (replaceColumn C t s') (g y) := by
    intro y hy
    have hnot : ¬ Y3c C s' hO hP t y := by
      intro h
      exact hy (Finset.mem_filter.mpr ⟨by simp, h⟩)
    simpa [g] using zero_equal_off C t s' hcol hO hP y hnot
  have hne : ∃ y : Word n, y ∈ S := by
    rcases hy with ⟨y, hy⟩
    exact ⟨y, Finset.mem_filter.mpr ⟨by simp, hy⟩⟩
  exact compare_bij_strict C (replaceColumn C t s') S g hgt heq hne

/-- A Y3c witness for the col5 split gives a strict improvement. -/
lemma zero_column_strict_witness {n : ℕ} (C : Code n) (t : Fin n) (hcol : C t = col0) :
    (∃ y : Word n, Y3c C col5 colZeros_col5_nonempty colOnes_col5_nonempty t y) →
      UniversalStrictBetter (replaceColumn C t col5) C := by
  rintro hy
  exact zero_column_strict_better C t col5 hcol colZeros_col5_nonempty colOnes_col5_nonempty hy

-- native_decide: Mechanical · n=any · checked 2026-08-27
/-- Flipping all bits of a column complements the type number. -/
lemma colVal_flipCol (c : Column) : colVal (flipCol c) = 15 - colVal c := by
  have hsum : colVal (flipCol c) + colVal c = 15 := by
    unfold colVal flipCol
    rw [← Finset.sum_add_distrib]
    have hterm : ∀ j : Fin 4,
        (if !(c j) then 2 ^ (3 - j.val) else 0) + (if c j then 2 ^ (3 - j.val) else 0) =
          2 ^ (3 - j.val) := by
      intro j
      cases c j <;> simp
    rw [Finset.sum_congr rfl (fun j _ => hterm j)]
    have hsum15 : (∑ j : Fin 4, 2 ^ (3 - j.val)) = 15 := by native_decide
    rw [hsum15]
  have hle : colVal c ≤ 15 := colVal_le_15 c
  omega

/-- Flipping the changed column preserves strict improvement (equivalence). -/
lemma strict_better_flip {n : ℕ} (C : Code n) (t : Fin n) (s : Column)
    (h : UniversalStrictBetter (replaceColumn C t s) C) :
    UniversalStrictBetter (replaceColumn C t (flipCol s)) C := by
  intro ε hε0 hε1
  have hEq : Equivalent (replaceColumn C t s) (replaceColumn C t (flipCol s)) := by
    refine ⟨Equiv.refl (Fin 4), Equiv.refl (Fin n), fun u => decide (u = t), ?_⟩
    intro u
    by_cases hu : u = t
    · subst u
      simp [replaceColumn, rowPermute_refl]
    · simp [replaceColumn, hu, rowPermute_refl]
  have hl : lambda (replaceColumn C t (flipCol s)) ε = lambda (replaceColumn C t s) ε :=
    lambda_equiv (replaceColumn C t s) (replaceColumn C t (flipCol s)) hEq ε
  rw [hl]
  exact h ε hε0 hε1

/-- From a strict improvement by a two-bit column at a zero column, get a
strict improvement by a column of type 3, 5, or 6. -/
lemma strict_better_two_bit_col0 {n : ℕ} (C : Code n) (t : Fin n) (_h0 : C t = col0)
    (s₀ : Column)
    (hs₀ : colVal s₀ = 3 ∨ colVal s₀ = 5 ∨ colVal s₀ = 6 ∨
      colVal s₀ = 9 ∨ colVal s₀ = 10 ∨ colVal s₀ = 12)
    (hstrict : UniversalStrictBetter (replaceColumn C t s₀) C) :
    ∃ s' : Column, (colVal s' = 3 ∨ colVal s' = 5 ∨ colVal s' = 6) ∧
      UniversalStrictBetter (replaceColumn C t s') C := by
  by_cases hle : colVal s₀ ≤ 7
  · have hs₀' : colVal s₀ = 3 ∨ colVal s₀ = 5 ∨ colVal s₀ = 6 := by
      rcases hs₀ with h3 | h5 | h6 | h9 | h10 | h12
      · simp [h3] at hle ⊢
      · simp [h5] at hle ⊢
      · simp [h6] at hle ⊢
      · simp [h9] at hle ⊢
      · simp [h10] at hle ⊢
      · simp [h12] at hle ⊢
    exact ⟨s₀, hs₀', hstrict⟩
  · have hs₀' : colVal s₀ = 9 ∨ colVal s₀ = 10 ∨ colVal s₀ = 12 := by
      rcases hs₀ with h3 | h5 | h6 | h9 | h10 | h12
      · simp [h3] at hle ⊢
      · simp [h5] at hle ⊢
      · simp [h6] at hle ⊢
      · simp [h9] at hle ⊢
      · simp [h10] at hle ⊢
      · simp [h12] at hle ⊢
    have hf : colVal (flipCol s₀) = 3 ∨ colVal (flipCol s₀) = 5 ∨ colVal (flipCol s₀) = 6 := by
      have hfc := colVal_flipCol s₀
      rcases hs₀' with h9 | h10 | h12
      · rw [hfc, h9]
        norm_num
      · rw [hfc, h10]
        norm_num
      · rw [hfc, h12]
        norm_num
    have hflip : UniversalStrictBetter (replaceColumn C t (flipCol s₀)) C :=
      strict_better_flip C t s₀ hstrict
    exact ⟨flipCol s₀, hf, hflip⟩

/-- Transfer a strict improvement from the normalized code back to the
original code at a common zero column. -/
lemma zero_column_strict_transfer {n : ℕ} (C C' : Code n) (ρ : Equiv (Fin 4) (Fin 4))
    (f : Fin n → Bool) (hh : ∀ u : Fin n, C' u = rowPermute ρ (if f u then flipCol (C u) else C u))
    (t : Fin n) (hcolC : C t = col0) (hcolC' : C' t = col0)
    (h : ∃ y : Word n, Y3c C' col5 colZeros_col5_nonempty colOnes_col5_nonempty t y) :
    ∃ s' : Column, (colVal s' = 3 ∨ colVal s' = 5 ∨ colVal s' = 6) ∧
      UniversalStrictBetter (replaceColumn C t s') C := by
  have hStrict' : UniversalStrictBetter (replaceColumn C' t col5) C' :=
    zero_column_strict_witness C' t hcolC' h
  have hft : f t = false := by
    by_contra hf
    have hft' : f t = true := by
      cases hx : f t
      · exfalso
        exact hf hx
      · rfl
    have hh' := hh t
    rw [hcolC, hft'] at hh'
    simp at hh'
    have hc : C' t = col15 := by
      have hrow : rowPermute ρ (flipCol col0) = col15 := by
        funext k
        simp [rowPermute, flipCol, col0, col15]
      rwa [hrow] at hh'
    have h01 : col0 = col15 := hcolC'.symm.trans hc
    have hbad : (false : Bool) = true := congrFun h01 ⟨0, by decide⟩
    simp at hbad
  let s₀ : Column := rowPermute ρ.symm (if f t then flipCol col5 else col5)
  have hEqRep : Equivalent (replaceColumn C' t col5) (replaceColumn C t s₀) := by
    refine ⟨ρ.symm, Equiv.refl (Fin n), f, ?_⟩
    intro u
    by_cases hu : u = t
    · subst u
      simp [s₀, replaceColumn, hft]
    · have hmain : C u = rowPermute ρ.symm (if f u then flipCol (C' u) else C' u) := by
        by_cases hfu : f u
        · have hh' := hh u
          rw [hfu] at hh'
          simp at hh'
          have hrow : rowPermute ρ.symm (C' u) = flipCol (C u) := by
            rw [hh']
            exact rowPermute_left_inv ρ (flipCol (C u))
          calc
            C u = flipCol (flipCol (C u)) := by
              funext j
              simp [flipCol]
            _ = flipCol (rowPermute ρ.symm (C' u)) := by rw [← hrow]
            _ = rowPermute ρ.symm (flipCol (C' u)) := by rw [flipCol_rowPermute ρ.symm (C' u)]
            _ = rowPermute ρ.symm (if f u then flipCol (C' u) else C' u) := by simp [hfu]
        · have hfu' : f u = false := by
            cases hx : f u
            · rfl
            · exfalso
              exact hfu hx
          have hh' := hh u
          rw [hfu'] at hh'
          simp at hh'
          calc
            C u = rowPermute ρ.symm (rowPermute ρ (C u)) := (rowPermute_left_inv ρ (C u)).symm
            _ = rowPermute ρ.symm (C' u) := by rw [← hh']
            _ = rowPermute ρ.symm (if f u then flipCol (C' u) else C' u) := by simp [hfu']
      simp [replaceColumn, hu, hmain]
  have hStrictC : UniversalStrictBetter (replaceColumn C t s₀) C := by
    intro ε hε0 hε1
    have h1 : lambda (replaceColumn C' t col5) ε > lambda C' ε := hStrict' ε hε0 hε1
    have h2 : lambda (replaceColumn C t s₀) ε = lambda (replaceColumn C' t col5) ε :=
      lambda_equiv (replaceColumn C' t col5) (replaceColumn C t s₀) hEqRep ε
    have h3 : lambda C' ε = lambda C ε :=
      lambda_equiv C C' ⟨ρ, Equiv.refl (Fin n), f, hh⟩ ε
    calc
      lambda (replaceColumn C t s₀) ε = lambda (replaceColumn C' t col5) ε := h2
      _ > lambda C' ε := h1
      _ = lambda C ε := h3
  have hs₀ : colVal s₀ = 3 ∨ colVal s₀ = 5 ∨ colVal s₀ = 6 ∨
      colVal s₀ = 9 ∨ colVal s₀ = 10 ∨ colVal s₀ = 12 := by
    rw [show s₀ = rowPermute ρ.symm col5 by simp [s₀, hft]]
    exact colVal_rowPermute_col5 ρ.symm
  exact strict_better_two_bit_col0 C t hcolC s₀ hs₀ hStrictC

/-- Theorem `thm:0column` (Theorem 6) (2): otherwise, for some s' ∈ {3,5,6}, replacing a
0-column strictly improves. -/
theorem zero_column_strict {n : ℕ} (C : Code n) (h0 : count C 0 ≥ 1)
    (hC0 : ¬ ∃ C0 : Code n, Equivalent C C0 ∧
      count C0 0 + count C0 5 + count C0 6 = n ∧
        Odd (count C0 5) ∧ Odd (count C0 6)) :
    ∃ t : Fin n, C t = col0 ∧ ∃ s' : Column,
      (colVal s' = 3 ∨ colVal s' = 5 ∨ colVal s' = 6) ∧
        UniversalStrictBetter (replaceColumn C t s') C := by
  rcases even_pair C with ⟨i, j, hij, hEven⟩
  let C' : Code n := normalizeCode C i j
  let ρ : Equiv (Fin 4) (Fin 4) := (permEven i j).symm
  let f : Fin n → Bool := fun t => (row C i) t
  have hh : ∀ u : Fin n, C' u = rowPermute ρ (if f u then flipCol (C u) else C u) := by
    intro u
    rfl
  have h07 : Columns07 C' := Columns07_normalize C i j hij
  have hcnt0 : 1 ≤ count C' 0 := count0_normalize C i j hij h0
  have hWeven : Even (count C' 4 + count C' 5 + count C' 6 + count C' 7) :=
    even_W_normalize C i j hij hEven
  have hnotC0 : ¬ C0form C' := notC0_normalize C i j (by simpa [C0form] using hC0)
  rcases witness_exists_C0form C' h07 hcnt0 hWeven hnotC0 with ⟨t', ht', hy'⟩
  rcases exists_col0_of_count_pos C h0 with ⟨t, htC⟩
  have htC' : C' t = col0 := by
    have hh' := hh t
    rw [htC] at hh'
    have hf : f t = false := by
      simp [f, row, colBit, htC, col0]
    rw [hf] at hh'
    simp at hh'
    rwa [rowPermute_col0] at hh'
  have hyT : ∃ y : Word n, Y3c C' col5 colZeros_col5_nonempty colOnes_col5_nonempty t y :=
    Y3c_move C' col5 colZeros_col5_nonempty colOnes_col5_nonempty t t' htC' ht' hy'
  exact ⟨t, htC, zero_column_strict_transfer C C' ρ f hh t htC htC' hyT⟩
/-! ## `cor:0col` (Corollary 7): two zero columns -/

/-- The number of weight-2 (two-bit) columns. -/
def twobitCount {n : ℕ} (C : Code n) : ℕ :=
  (Finset.univ.filter fun t : Fin n => colWeight (C t) = 2).card

/-- The number of two-bit columns is invariant under equivalence. -/
lemma twobitCount_equiv {n : ℕ} {C C' : Code n} (h : Equivalent C C') :
    twobitCount C = twobitCount C' := by
  rcases h with ⟨ρ, p, f, hh⟩
  unfold twobitCount
  have hiff : ∀ t : Fin n, colWeight (C' (p t)) = 2 ↔ colWeight (C t) = 2 := by
    intro t
    have hrel : colWeight (C' (p t)) = colWeight (C t) ∨
        colWeight (C' (p t)) = 4 - colWeight (C t) := by
      rw [hh t]
      cases hf : f t <;> simp [colWeight_rowPermute, colWeight_flip]
    constructor
    · intro hw
      rcases hrel with h | h
      · omega
      · have hle : colWeight (C t) ≤ 4 := colWeight_le_4 (C t)
        omega
    · intro hw
      rcases hrel with h | h
      · omega
      · have hle : colWeight (C t) ≤ 4 := colWeight_le_4 (C t)
        omega
  apply Finset.card_bij (fun t _ => p t)
  · intro t ht
    exact Finset.mem_filter.mpr ⟨by simp, (hiff t).mpr (Finset.mem_filter.mp ht).2⟩
  · intro a _ b _ hab
    exact p.injective hab
  · intro b hb
    refine ⟨p.symm b, ?_, by simp⟩
    have hb' : colWeight (C' (p (p.symm b))) = 2 := by simpa using (Finset.mem_filter.mp hb).2
    exact Finset.mem_filter.mpr ⟨by simp, (hiff (p.symm b)).mp hb'⟩

/-- In a C0-form code every column has type 0, 5, or 6. -/
lemma C0form_types {n : ℕ} (C : Code n) (h : C0form C) (t : Fin n) :
    colVal (C t) = 0 ∨ colVal (C t) = 5 ∨ colVal (C t) = 6 := by
  let i : ℕ := colVal (C t)
  have hcnti : 1 ≤ count C i := by
    have hmem : t ∈ (Finset.univ.filter fun u : Fin n => colVal (C u) = i) := by
      simp [i]
    have hcard : 1 ≤ (Finset.univ.filter fun u : Fin n => colVal (C u) = i).card := by
      exact Nat.succ_le_of_lt (Finset.card_pos.mpr ⟨t, hmem⟩)
    rw [count_eq_card]
    exact hcard
  have hS : ({0, 5, 6} : Finset ℕ) ⊆ Finset.Icc 0 15 := by
    intro x hx
    simp at hx ⊢
    omega
  have hcnt0 : count C 0 + count C 5 + count C 6 = n := h.1
  have hsumS : (∑ j ∈ ({0, 5, 6} : Finset ℕ), count C j) = n := by
    have hs : (∑ j ∈ ({0, 5, 6} : Finset ℕ), count C j) = count C 0 + (count C 5 + count C 6) := by
      simp [Finset.sum_insert]
    rw [hs]
    omega
  have hsumAll : (∑ j ∈ Finset.Icc 0 15, count C j) = n := sum_counts_eq_n C
  have hcomp : (∑ j ∈ Finset.Icc 0 15 \ ({0, 5, 6} : Finset ℕ), count C j) = 0 := by
    have hsplit : (∑ j ∈ Finset.Icc 0 15, count C j) =
        (∑ j ∈ ({0, 5, 6} : Finset ℕ), count C j) +
          ∑ j ∈ Finset.Icc 0 15 \ ({0, 5, 6} : Finset ℕ), count C j := by
      rw [← Finset.sum_sdiff hS]
      rw [add_comm]
    omega
  have hile : i ≤ 15 := colVal_le_15 (C t)
  by_contra h
  have hi : i ∈ Finset.Icc 0 15 \ ({0, 5, 6} : Finset ℕ) := by
    rw [Finset.mem_sdiff]
    constructor
    · simp [Finset.mem_Icc, hile]
    · intro hiS
      simp at hiS
      exact h hiS
  have hle : count C i ≤ ∑ j ∈ Finset.Icc 0 15 \ ({0, 5, 6} : Finset ℕ), count C j := by
    exact Finset.single_le_sum (by intro j _; exact Nat.zero_le _) hi
  have hzero : count C i = 0 := by omega
  omega

-- native_decide: Mechanical · n=any · checked 2026-08-27
/-- In a C0-form code, weight 2 exactly means type 5 or 6. -/
lemma colWeight_eq_two_iff_C0form {n : ℕ} (C : Code n) (h : C0form C) (t : Fin n) :
    colWeight (C t) = 2 ↔ colVal (C t) = 5 ∨ colVal (C t) = 6 := by
  rcases C0form_types C h t with h0 | h5 | h6
  · have hw : colWeight (C t) = 0 := by
      rw [← colOfNat_colVal (C t), h0]
      native_decide
    constructor
    · intro h2
      omega
    · intro h56
      omega
  · have hw : colWeight (C t) = 2 := by
      rw [← colOfNat_colVal (C t), h5]
      native_decide
    constructor
    · intro _
      exact Or.inl h5
    · intro _
      exact hw
  · have hw : colWeight (C t) = 2 := by
      rw [← colOfNat_colVal (C t), h6]
      native_decide
    constructor
    · intro _
      exact Or.inr h6
    · intro _
      exact hw

/-- A C0-form code has an even number of two-bit columns. -/
lemma twobitCount_C0form {n : ℕ} (C : Code n) (h : C0form C) :
    Even (twobitCount C) := by
  have hcard : twobitCount C = count C 5 + count C 6 := by
    unfold twobitCount
    rw [count_eq_card C 5, count_eq_card C 6]
    have hdisj : Disjoint (Finset.univ.filter fun t : Fin n => colVal (C t) = 5)
        (Finset.univ.filter fun t : Fin n => colVal (C t) = 6) := by
      rw [Finset.disjoint_filter]
      intro t _ h5 h6
      omega
    have hunion : (Finset.univ.filter fun t : Fin n => colVal (C t) = 5) ∪
        (Finset.univ.filter fun t : Fin n => colVal (C t) = 6) =
        Finset.univ.filter fun t : Fin n => colWeight (C t) = 2 := by
      ext t
      simp
      exact (colWeight_eq_two_iff_C0form C h t).symm
    rw [← hunion, ← Finset.card_union_of_disjoint hdisj]
  rcases h.2.1 with ⟨a, ha⟩
  rcases h.2.2 with ⟨b, hb⟩
  rw [hcard]
  refine ⟨a + b + 1, ?_⟩
  omega

-- native_decide: Mechanical · n=any · checked 2026-08-27
/-- Replacing a zero column by the type-5 column adds one two-bit column. -/
lemma twobitCount_replace_0_5 {n : ℕ} (C : Code n) (t : Fin n) (h0 : C t = col0) :
    twobitCount (replaceColumn C t col5) = twobitCount C + 1 := by
  unfold twobitCount
  rw [Finset.card_filter, Finset.card_filter]
  have hsplit := sum_split_at (fun u : Fin n =>
      if colWeight ((replaceColumn C t col5) u) = 2 then 1 else 0) t
  have hsplitC := sum_split_at (fun u : Fin n =>
      if colWeight (C u) = 2 then 1 else 0) t
  have hcong : (∑ u ∈ (Finset.univ.erase t : Finset (Fin n)),
      if colWeight ((replaceColumn C t col5) u) = 2 then 1 else 0) =
      ∑ u ∈ (Finset.univ.erase t : Finset (Fin n)), if colWeight (C u) = 2 then 1 else 0 := by
    apply Finset.sum_congr rfl
    intro u hu
    have hu' : u ≠ t := (Finset.mem_erase.mp hu).1
    simp [replaceColumn, hu']
  have ht1 : (if colWeight ((replaceColumn C t col5) t) = 2 then 1 else 0) = 1 := by
    have hw : colWeight col5 = 2 := by native_decide
    simp [replaceColumn, hw]
  have ht0 : (if colWeight (C t) = 2 then 1 else 0) = 0 := by
    have hcv : colVal (C t) = 0 := (colVal_eq_zero_iff_col0 (C t)).mpr h0
    have hw : colWeight (C t) = 0 := by
      rw [← colOfNat_colVal (C t), hcv]
      native_decide
    simp [hw]
  calc
    (∑ u : Fin n, if colWeight ((replaceColumn C t col5) u) = 2 then 1 else 0)
        = (∑ u ∈ (Finset.univ.erase t : Finset (Fin n)),
            if colWeight ((replaceColumn C t col5) u) = 2 then 1 else 0) + 1 := by
          rw [hsplit, ht1]
    _ = (∑ u ∈ (Finset.univ.erase t : Finset (Fin n)),
            if colWeight (C u) = 2 then 1 else 0) + 1 := by rw [hcong]
    _ = (∑ u : Fin n, if colWeight (C u) = 2 then 1 else 0) + 1 := by
          rw [hsplitC, ht0]

/-- Replacing a zero column by a nonzero column decreases |0| by one. -/
lemma count_replace_0_nonzero {n : ℕ} (C : Code n) (t : Fin n) (s' : Column)
    (h0 : C t = col0) (hs : s' ≠ col0) :
    count (replaceColumn C t s') 0 = count C 0 - 1 := by
  exact count_replace_dec C t s' 0 (by rw [h0]; native_decide)
    (by intro h; exact hs ((colVal_eq_zero_iff_col0 s').mp h))

-- native_decide: Mechanical · n=any · checked 2026-08-27
/-- A column of type 3, 5, or 6 is not the zero column. -/
lemma col0_ne_of_colVal_356 {s : Column} (h : colVal s = 3 ∨ colVal s = 5 ∨ colVal s = 6) :
    s ≠ col0 := by
  intro hs
  have : colVal s = 0 := by rw [hs]; native_decide
  rcases h with h3 | h5 | h6 <;> omega

/-- Better then strictly better is strictly better. -/
lemma strict_of_better_strict {n : ℕ} (C₁ C₂ C₃ : Code n)
    (h12 : UniversalBetter C₁ C₂) (h23 : UniversalStrictBetter C₂ C₃) :
    UniversalStrictBetter C₁ C₃ := by
  intro ε hε0 hε1
  exact lt_of_lt_of_le (h23 ε hε0 hε1) (h12 ε hε0 hε1)

/-- Corollary `cor:0col` (Corollary 7): with |0| ≥ 2, two 0-columns can be replaced by two
nonzero linear-type columns to strictly improve. -/
-- native_decide: Mechanical · n=any · checked 2026-08-27
theorem two_zero_columns {n : ℕ} (C : Code n) (h : count C 0 ≥ 2) :
    ∃ t₁ t₂ : Fin n, t₁ ≠ t₂ ∧ C t₁ = col0 ∧ C t₂ = col0 ∧
      ∃ s₁ s₂ : Column,
        (colVal s₁ = 3 ∨ colVal s₁ = 5 ∨ colVal s₁ = 6) ∧
        (colVal s₂ = 3 ∨ colVal s₂ = 5 ∨ colVal s₂ = 6) ∧
          UniversalStrictBetter (replaceColumn (replaceColumn C t₁ s₁) t₂ s₂) C := by
  by_cases hC0 : ∃ C0 : Code n, Equivalent C C0 ∧ C0form C0
  · -- case B: C is equivalent to the C0 code
    rcases hC0 with ⟨C0, hEqC0, hC0form⟩
    rcases exists_col0_of_count_pos C (by omega : 1 ≤ count C 0) with ⟨t₁, ht₁⟩
    let Cn : Code n := replaceColumn C t₁ col5
    have hcntn : 1 ≤ count Cn 0 := by
      have hc := count_replace_0_nonzero C t₁ col5 ht₁ (by native_decide : col5 ≠ col0)
      rw [hc]
      have h' : 1 < count C 0 := by omega
      exact Nat.le_pred_of_lt h'
    have hnotC0n : ¬ ∃ C0' : Code n, Equivalent Cn C0' ∧ C0form C0' := by
      intro hb
      rcases hb with ⟨C0', hEqn, hC0form'⟩
      have htw := twobitCount_equiv hEqn
      have hevenC0' : Even (twobitCount C0') := twobitCount_C0form C0' hC0form'
      have htwC : twobitCount Cn = twobitCount C + 1 := twobitCount_replace_0_5 C t₁ ht₁
      have htwC0 : twobitCount C = twobitCount C0 := twobitCount_equiv hEqC0
      have hevenC0 : Even (twobitCount C0) := twobitCount_C0form C0 hC0form
      have hoddn : Odd (twobitCount Cn) := by
        rcases hevenC0 with ⟨k, hk⟩
        rw [htwC, htwC0, hk]
        refine ⟨k, ?_⟩
        omega
      have : Even (twobitCount Cn) := by rwa [← htw] at hevenC0'
      rcases hoddn with ⟨a, ha⟩
      rcases this with ⟨b, hb⟩
      omega
    rcases zero_column_strict Cn hcntn (by simpa [C0form] using hnotC0n) with
      ⟨t₂, ht₂, s₂, hs₂, hstrict₂⟩
    have ht₂C : C t₂ = col0 := by
      -- t₂ is a 0-column of Cn and t₂ ≠ t₁, so it is unchanged in C
      have hne : t₂ ≠ t₁ := by
        intro heq
        subst t₁
        have : Cn t₂ = col0 := ht₂
        simp [Cn, replaceColumn] at this
        have hcv0 : colVal col5 = 0 := by
          rw [this]
          native_decide
        have hcv5 : colVal col5 = 5 := by native_decide
        omega
      simpa [Cn, replaceColumn, hne] using ht₂
    have heq : UniversalEqual Cn C :=
      zero_column C t₁ ht₁ (⟨C0, hEqC0, hC0form⟩) col5
    have hstrictC : UniversalStrictBetter (replaceColumn Cn t₂ s₂) C := by
      intro ε hε0 hε1
      have h1 : lambda (replaceColumn Cn t₂ s₂) ε > lambda Cn ε := hstrict₂ ε hε0 hε1
      have h2 : lambda Cn ε = lambda C ε := heq ε hε0 hε1
      rwa [h2] at h1
    refine ⟨t₁, t₂, ?_, ht₁, ht₂C, col5, s₂, ?_, hs₂, ?_⟩
    · intro heq
      subst t₁
      have : Cn t₂ = col0 := ht₂
      simp [Cn, replaceColumn] at this
      have hcv0 : colVal col5 = 0 := by
        rw [this]
        native_decide
      have hcv5 : colVal col5 = 5 := by native_decide
      omega
    · exact Or.inr (Or.inl (by native_decide : colVal col5 = 5))
    · simpa [Cn] using hstrictC
  · -- case A: C is not equivalent to the C0 code
    rcases zero_column_strict C (by omega : 1 ≤ count C 0) (by simpa [C0form] using hC0) with
      ⟨t₁, ht₁, s₁, hs₁, hstrict₁⟩
    let Cn : Code n := replaceColumn C t₁ s₁
    have hs₁' : s₁ ≠ col0 := col0_ne_of_colVal_356 hs₁
    have hcntn : 1 ≤ count Cn 0 := by
      have hc := count_replace_0_nonzero C t₁ s₁ ht₁ hs₁'
      rw [hc]
      have h' : 1 < count C 0 := by omega
      exact Nat.le_pred_of_lt h'
    rcases exists_col0_of_count_pos Cn hcntn with ⟨t₂, ht₂⟩
    have hne : t₂ ≠ t₁ := by
      intro heq
      subst t₁
      have : Cn t₂ = col0 := ht₂
      simp [Cn, replaceColumn] at this
      exact hs₁' this
    have ht₂C : C t₂ = col0 := by
      simpa [Cn, replaceColumn, hne] using ht₂
    have hbetter : UniversalBetter (replaceColumn Cn t₂ col5) Cn :=
      (zero_column_better Cn t₂ col5 ht₂ colZeros_col5_nonempty colOnes_col5_nonempty).1
    have hstrict : UniversalStrictBetter (replaceColumn Cn t₂ col5) C :=
      strict_of_better_strict _ _ _ hbetter hstrict₁
    refine ⟨t₁, t₂, hne.symm, ht₁, ht₂C, s₁, col5, hs₁, ?_, ?_⟩
    · exact Or.inr (Or.inl (by native_decide : colVal col5 = 5))
    · simpa [Cn] using hstrict

end N4Code
