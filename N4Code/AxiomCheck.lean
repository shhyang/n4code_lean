import N4Code.Definitions
import N4Code.Basic
import N4Code.Performance
import N4Code.Compare
import N4Code.ZeroColumn
import N4Code.TwoColumn
import N4Code.Reduction
import N4Code.ClassI
import N4Code.Linear
import N4Code.FiniteN
import N4Code.Nbig
import N4Code.Statements

/-!
# Axiom audit for the headline theorems

`#print axioms` for every paper headline theorem.  The expected axiom set is
the mathlib-standard trusted base: `propext`, `quot.sound`,
`Classical.choice`, plus `Lean.ofReduceBool` (introduced by `native_decide`,
which this project uses for finite witness checks).  `sorryAx` must never
appear in the final release; `scripts/axioms_check.sh` enforces the
allowlist and fails on `sorryAx`.
-/

namespace N4Code

/-! ### §2.3 Finite classification -/

#print axioms optimal_codes_small_n

/-! ### §IV-B–D One-column and zero-column results -/

#print axioms one_bit_flip
#print axioms only_types_13456
#print axioms descent_to_linear_or_class1
#print axioms zero_column
#print axioms zero_column_strict
#print axioms two_zero_columns

/-! ### §3.4 Main reductions -/

#print axioms class2_to_class1
#print axioms class3_to_linear
#print axioms lm_all
#print axioms optimal_in_linear_or_class1
#print axioms optimal_equivalent_linear_class1_class2
#print axioms condition_optimalcode

/-! ### §4 Two-column change -/

#print axioms two_bit_flip
#print axioms z_partition
#print axioms z4_nonempty_cases
#print axioms z5_nonempty
#print axioms z45_empty_case2
#print axioms z45_empty_case3
#print axioms z5_empty_case16

/-! ### §5 Linear codes -/

#print axioms choose_product_inequality
#print axioms linear_compare
#print axioms linear_cor1
#print axioms linear_opt_residue2
#print axioms linear_opt_n3
#print axioms linear_opt_residue0
#print axioms linear_opt_residue1

/-! ### §6 Class-I codes -/

#print axioms class1_one
#print axioms class1_min
#print axioms Y3_iff_col1
#print axioms Y5_iff_col1

end N4Code
