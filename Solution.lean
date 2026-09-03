import N4Code

/-!
# Proved solution

This module imports the full `N4Code` development and proves the same
advertised theorems as `Challenge.lean` using the completed, `sorry`-free
proofs of Theorems 1--5.
-/

theorem N4Code.palomar_thm1 (n : ℕ) (hn : 2 ≤ n) :
    ∀ ε : ℝ, 0 < ε → ε < 1 / 2 →
      ∃ C : N4Code.Code n, (N4Code.IsLinear C ∨ N4Code.ClassI C) ∧ N4Code.OptimalAt C ε := by
  exact N4Code.optimal_in_linear_or_class1 n hn

theorem N4Code.palomar_thm2_residue2 {k : ℕ} (hk : k ≥ 1) :
    ∀ D : N4Code.Code (k + k + (k - 1)), N4Code.IsLinear D →
      ¬ N4Code.Equivalent (N4Code.linearCode k k (k - 1)) D →
        N4Code.UniversalStrictBetter (N4Code.linearCode k k (k - 1)) D := by
  exact N4Code.linear_opt_residue2 hk

theorem N4Code.palomar_thm2_n3 :
    ∀ D : N4Code.Code 3, N4Code.IsLinear D →
      ¬ N4Code.Equivalent N4Code.CA D → ¬ N4Code.Equivalent (N4Code.linearCode 1 1 1) D →
      ¬ N4Code.Equivalent (N4Code.linearCode 1 2 0) D →
        N4Code.UniversalStrictBetter N4Code.CA D ∧
          N4Code.UniversalStrictBetter (N4Code.linearCode 1 1 1) D ∧
            N4Code.UniversalStrictBetter (N4Code.linearCode 1 2 0) D := by
  exact N4Code.linear_opt_n3

theorem N4Code.palomar_thm2_residue0 {k : ℕ} (hk : k ≥ 2) :
    (∀ D : N4Code.Code (k + 1 + k + (k - 1)), N4Code.IsLinear D →
        ¬ N4Code.Equivalent (N4Code.linCode (k + 1) (k + 1) (k - 2) (by omega)) D →
        ¬ N4Code.Equivalent (N4Code.linCode (k + 1) k (k - 1) (by omega)) D →
          N4Code.UniversalStrictBetter
            (N4Code.linCode (k + 1) (k + 1) (k - 2) (by omega)) D) ∧
      (∀ D : N4Code.Code (k + 1 + k + (k - 1)), N4Code.IsLinear D →
        ¬ N4Code.Equivalent (N4Code.linCode (k + 1) (k + 1) (k - 2) (by omega)) D →
        ¬ N4Code.Equivalent (N4Code.linCode (k + 1) k (k - 1) (by omega)) D →
          N4Code.UniversalStrictBetter
            (N4Code.linCode (k + 1) k (k - 1) (by omega)) D) := by
  exact N4Code.linear_opt_residue0 hk

theorem N4Code.palomar_thm2_residue1 {k : ℕ} (hk : k ≥ 1) :
    (∀ D : N4Code.Code (k + 1 + k + k), N4Code.IsLinear D →
        ¬ N4Code.Equivalent (N4Code.linCode (k + 1) k k (by omega)) D →
        ¬ N4Code.Equivalent (N4Code.linCode (k + 2) k (k - 1) (by omega)) D →
          N4Code.UniversalStrictBetter (N4Code.linCode (k + 1) k k (by omega)) D) ∧
      (∀ D : N4Code.Code (k + 1 + k + k), N4Code.IsLinear D →
        ¬ N4Code.Equivalent (N4Code.linCode (k + 1) k k (by omega)) D →
        ¬ N4Code.Equivalent (N4Code.linCode (k + 2) k (k - 1) (by omega)) D →
          N4Code.UniversalStrictBetter
            (N4Code.linCode (k + 2) k (k - 1) (by omega)) D) := by
  exact N4Code.linear_opt_residue1 hk

theorem N4Code.palomar_thm3 (n : ℕ) (hn : n > 3) (C : N4Code.Code n)
    (hnot : ∀ C' : N4Code.Code n, N4Code.Equivalent C C' →
      ¬ (N4Code.IsLinear C' ∨ N4Code.ClassI C' ∨ N4Code.ClassII C')) :
    ∃ D : N4Code.Code n, N4Code.UniversalStrictBetter D C := by
  exact N4Code.universal_strict_better_of_not_class n hn C hnot

theorem N4Code.palomar_thm4 (n : ℕ) (hn : n > 3)
    (hcond : ∀ C : N4Code.Code n, N4Code.ClassI C → N4Code.count C 1 ≥ 3 →
      ∀ t : Fin n, C t = N4Code.col1 →
        N4Code.UniversalBetter (N4Code.replaceColumn C t (N4Code.argminType C)) C) :
    ∀ C : N4Code.Code n,
      (∀ C' : N4Code.Code n, N4Code.Equivalent C C' → ¬ N4Code.IsLinear C') →
        ∃ D : N4Code.Code n, N4Code.UniversalStrictBetter D C := by
  exact N4Code.universal_strict_better_of_not_linear n hn hcond

theorem N4Code.palomar_thm5 (n : ℕ) (hn2 : 2 ≤ n) (hn8 : n ≤ 8) :
    (n ≠ 3 → ∀ C : N4Code.Code n,
      (∀ C' : N4Code.Code n, N4Code.Equivalent C C' → ¬ N4Code.IsLinear C') →
        ∃ D : N4Code.Code n, N4Code.UniversalStrictBetter D C) ∧
      (n = 3 → ∀ C : N4Code.Code 3,
        (∀ C' : N4Code.Code 3, N4Code.Equivalent C C' → ¬ N4Code.InOptimal3 C') →
          ∃ D : N4Code.Code 3, N4Code.UniversalStrictBetter D C) := by
  exact N4Code.optimal_codes_small_n n hn2 hn8
