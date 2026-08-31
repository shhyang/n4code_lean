import N4Code.Definitions
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Choose.Basic

/-!
# Paper theorem statements

Every numbered theorem/lemma/corollary targeted by PLAN.md, stated in Lean.
The paper label appears in the docstring of each declaration; see
`Notation.md` for the paper symbol mapping.  Proofs live in the phase
modules (each phase owns its statements); this file is the paper-numbered
catalogue.  All statements are proved — the library contains no `sorry`.

Conventions:
* A one-column change is assumed to happen at position `t : Fin n` (WLOG, by
  equivalence); hypotheses are `C t = col1`, `C' t = col3`,
  `∀ u ≠ t, C' u = C u`.
* Equality characterizations (`thm:even` (Theorem 8), `thm:odd` (Theorem 11)) assume columns of types
  0..7 only, stated as `Columns07 C`.
* "Universal" relations are `UniversalBetter/StrictBetter/Equal`.
-/

namespace N4Code

/-! ## §3.1 The comparison lemma -/

-- `thm:com` (Lemma 18) (`compare_bij`, `compare_bij_strict`, `compare_bij_eq`) is proved
-- in `N4Code/Compare.lean`; the paper label lives in its docstring there.

-- `lemma:1` (Lemma 19) (partition, distance relations 1)–5), bijection `g1_bijective`),
-- `the:1` (Theorem 20) (`lambda_diff_one_column`), and `cor:1` (Corollary 21) (`cumulative_criterion`,
-- `cumulative_strict`, `cumulative_no_y5`) are proved in `N4Code/Compare.lean`;
-- the paper labels live in the docstrings there.

/-! ## §IV-B–D One-column and zero-column results -/

-- Theorem `thm:even` (Theorem 8) is developed in `N4Code/Reduction.lean` (Phase E) as
-- `one_bit_flip` (comparison part `one_bit_flip_better`, equality part
-- `Y3_empty_iff`); the paper label lives in the docstring there.

-- Corollary `cor:twopo` (Corollary 9) is developed in `N4Code/Reduction.lean` as
-- `only_types_13456`; the paper label lives in its docstring there.

-- Corollary `cor:onepo` (Corollary 10) is developed in `N4Code/Reduction.lean` as
-- `descent_to_linear_or_class1`; the paper label lives in its docstring there.

-- Theorem `thm:0column` (Theorem 6) (1) is proved in `N4Code/ZeroColumn.lean` as
-- `zero_column`; the paper label lives in its docstring there.

-- Theorem `thm:0column` (Theorem 6) (2) is proved in `N4Code/ZeroColumn.lean` as
-- `zero_column_strict`; the paper label lives in its docstring there.

-- Corollary `cor:0col` (Corollary 7) is proved in `N4Code/ZeroColumn.lean` as
-- `two_zero_columns`; the paper label lives in its docstring there.

/-! ## §4 Two-column change -/

-- All §4 statements are developed in `N4Code/TwoColumn.lean` (Phase D):
-- `lemma:2` (Lemma 22) (`z_partition`, `g2_bijective`, `z_rel_1`..`z_rel_5`),
-- `lemma:y4` (Lemma 24) (`z4_empty_of_even`, `z4_nonempty_cases`), `lemma:z5` (Lemma 24)
-- (`z5_nonempty`), `lm:2` (Lemma 25)/`lm:3` (Lemma 26)/`lm:16` (Lemma 27) (`z45_empty_case2`,
-- `z45_empty_case3`, `z5_empty_case16`), and `thm:odd` (Theorem 11) (`two_bit_flip`).
-- The paper labels live in the docstrings there.

/-! ## §3.4 Main reductions -/

-- All §3.4 statements are developed in `N4Code/Reduction.lean` (Phase E):
-- `thm:even` (Theorem 8) (`one_bit_flip`), `cor:twopo` (Corollary 9) (`only_types_13456`),
-- `cor:onepo` (Corollary 10) (`descent_to_linear_or_class1`), `thm:class2` (Lemma 14)
-- (`class2_to_class1`, `class3_to_linear`), `lm:all` (Lemma 15) (`lm_all`),
-- `thm:two` (Theorem 1) (`optimal_in_linear_or_class1`), `thm:nbig3` (Theorem 3)
-- (`universal_strict_better_of_not_class`), and
-- `thm:condition_optimalcode` (Theorem 4) (`universal_strict_better_of_not_linear`).
-- The paper labels live in the docstrings there.

/-! ## §5 Linear codes -/

-- All §5 statements are developed in `N4Code/Linear.lean` (Phase F):
-- `thm:linearcompare` (Theorem 12) (`linear_compare`), `cor:linear1` (Corollary 13) (`linear_cor1`),
-- and `thm:linearopt` (Theorem 2) (`linear_opt_residue2`, `linear_opt_n3`,
-- `linear_opt_residue0`, `linear_opt_residue1`).
-- The paper labels live in the docstrings there.

/-! ## §6 Class-I codes -/

-- Lemma `lemma:cli1` (Lemma 28) is proved in `N4Code/Linear.lean` as
-- `choose_product_inequality`; the paper label lives in its docstring there.

-- All §6 statements are developed in `N4Code/ClassI.lean` (Phase G):
-- `thm:11` (Theorem 16) (`class1_one`) and `thm:301` (Theorem 17) (`class1_min`); the paper labels live
-- in the docstrings there.  The Y3/Y5 characterizations (eq. c13/c15) are
-- proved there as `Y3_iff_col1`/`Y5_iff_col1`.

/-! ## §2.3 Finite classification -/

-- Theorem `thm:n8` (Theorem 5) (`optimal_codes_small_n`) is developed in
-- `N4Code/FiniteN.lean` (Phase H); the paper label lives in its docstring
-- there.

end N4Code
