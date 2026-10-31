import Ex89.Rook
/-! The final theorems for `(40, 42, 58)`. The search is run by `native_decide`, in parallel. -/
namespace Ex89

/-- The whole search for `(40, 42, 58)` finds a contradiction in every case. -/
theorem check_40_42_58 : checkAll 40 42 58 = true := by native_decide

/-- No four-piece dissection of the `58 × 58` square into `40 × 40` and `42 × 42` squares, as long as
each piece goes to one square. -/
theorem no_dissection_40_42_58 : NoDissection 40 42 58 :=
  no_dissection_of_check (by decide) (by decide) (by decide) (by decide) check_40_42_58

/-- **Exercise 89 for `(40, 42, 58)`.** No rookwise connected four-piece dissection exists. -/
theorem no_rook_dissection_40_42_58 : NoRookDissection 40 42 58 :=
  noRook_of_no no_dissection_40_42_58

end Ex89

#print Ex89.check_40_42_58._native.native_decide.ax_1_1
#print axioms Ex89.no_dissection_40_42_58
#print axioms Ex89.no_rook_dissection_40_42_58
