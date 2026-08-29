import N4Code.Performance
import Mathlib.Tactic.FieldSimp

/-!
# The generic comparison engine

The paper-independent core of the comparison machinery: if a bijection `g`
of the word space maps every word to one at distance at most `dCode C`, then
`C'` is at least as good as `C` (`thm:com` (Lemma 18) of the paper), with strictness
when some word is strictly closer and equality when the distances coincide.
Everything here is stated generically in terms of `dCode`, `weight`, and
`lambda`; no paper-specific column or region machinery is involved, so the
module is reusable by any future code-comparison development.
-/

namespace N4Code

/-- The exact λ-difference behind `thm:com` (Lemma 18). -/
lemma lambda_diff_eq {n : ℕ} (C C' : Code n) (S : Finset (Word n))
    (g : Word n ≃ Word n)
    (_hgt : ∀ y : Word n, y ∈ S → dCode C y > dCode C' (g y))
    (heq : ∀ y : Word n, y ∉ S → dCode C y = dCode C' (g y)) (ε : ℝ) :
    lambda C' ε - lambda C ε =
      (1 / 4 : ℝ) * ∑ y ∈ S, (weight n ε (dCode C' (g y)) - weight n ε (dCode C y)) := by
  unfold lambda
  rw [← mul_sub]
  congr 1
  calc
    (∑ y : Word n, weight n ε (dCode C' y)) - ∑ y : Word n, weight n ε (dCode C y)
        = ∑ y : Word n, (weight n ε (dCode C' (g y)) - weight n ε (dCode C y)) := by
          have hgsum : (∑ y : Word n, weight n ε (dCode C' y)) =
              ∑ y : Word n, weight n ε (dCode C' (g y)) := by
            apply Finset.sum_bij (fun y _ => g.symm y)
            · intro y _; simp
            · intro a _ b _ hab
              exact g.symm.injective hab
            · intro b _
              refine ⟨g b, by simp, by simp⟩
            · intro y _; simp
          rw [hgsum, ← Finset.sum_sub_distrib]
    _ = ∑ y ∈ S, (weight n ε (dCode C' (g y)) - weight n ε (dCode C y)) := by
          have hzero : ∀ y : Word n, y ∉ S →
              weight n ε (dCode C' (g y)) - weight n ε (dCode C y) = 0 := by
            intro y hy
            rw [heq y hy]
            ring
          symm
          apply Finset.sum_subset
          · intro y _; simp
          · intro y _ hy
            exact hzero y hy

/-- Lemma `thm:com` (Lemma 18): a bijection with strictly closer images on S and equality
off S makes C' at least as good as C. -/
theorem compare_bij {n : ℕ} (C C' : Code n) (S : Finset (Word n))
    (g : Word n ≃ Word n)
    (hgt : ∀ y : Word n, y ∈ S → dCode C y > dCode C' (g y))
    (heq : ∀ y : Word n, y ∉ S → dCode C y = dCode C' (g y)) :
    UniversalBetter C' C := by
  intro ε hε0 hε1
  apply sub_nonneg.mp
  rw [lambda_diff_eq C C' S g hgt heq ε]
  have hge : (0 : ℝ) ≤ ∑ y ∈ S,
      (weight n ε (dCode C' (g y)) - weight n ε (dCode C y)) := by
    apply Finset.sum_nonneg
    intro y hy
    exact sub_nonneg.mpr (le_of_lt (weight_strictAnti hε0 hε1 (hgt y hy)))
  exact mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4) hge

/-- Lemma `thm:com` (Lemma 18), strict version: if S is nonempty then C' is strictly
better than C. -/
theorem compare_bij_strict {n : ℕ} (C C' : Code n) (S : Finset (Word n))
    (g : Word n ≃ Word n)
    (hgt : ∀ y : Word n, y ∈ S → dCode C y > dCode C' (g y))
    (heq : ∀ y : Word n, y ∉ S → dCode C y = dCode C' (g y))
    (hne : ∃ y : Word n, y ∈ S) : UniversalStrictBetter C' C := by
  intro ε hε0 hε1
  apply sub_pos.mp
  rw [lambda_diff_eq C C' S g hgt heq ε]
  have hgt0 : (0 : ℝ) < ∑ y ∈ S,
      (weight n ε (dCode C' (g y)) - weight n ε (dCode C y)) := by
    apply Finset.sum_pos'
    · intro y hy
      exact sub_nonneg.mpr (le_of_lt (weight_strictAnti hε0 hε1 (hgt y hy)))
    · rcases hne with ⟨y, hy⟩
      refine ⟨y, hy, ?_⟩
      exact sub_pos.mpr (weight_strictAnti hε0 hε1 (hgt y hy))
  exact mul_pos (by norm_num : (0 : ℝ) < 1 / 4) hgt0

/-- Lemma `thm:com` (Lemma 18), equality version: if the images are always equidistant
then the codes are equally good. -/
theorem compare_bij_eq {n : ℕ} (C C' : Code n) (g : Word n ≃ Word n)
    (heq : ∀ y : Word n, dCode C y = dCode C' (g y)) :
    UniversalEqual C' C := by
  intro ε hε0 hε1
  apply sub_eq_zero.mp
  have hdiff := lambda_diff_eq C C' ∅ g (by intro y hy; simp at hy) (by intro y _; exact heq y) ε
  rw [hdiff]
  simp

end N4Code
