import Ex89.Rook
/-! The final theorems for `(65, 72, 97)`. The search is run by `native_decide`, in parallel. -/
namespace Ex89

/-- The whole search for `(65, 72, 97)` finds a contradiction in every case. -/
theorem check_65_72_97 : checkAll 65 72 97 = true := by native_decide

/-- No four-piece dissection of the `97 × 97` square into `65 × 65` and `72 × 72` squares, as long as
each piece goes to one square. -/
theorem no_dissection_65_72_97 : NoDissection 65 72 97 :=
  no_dissection_of_check (by decide) (by decide) (by decide) (by decide) check_65_72_97

/-- **Exercise 89 for `(65, 72, 97)`.** No rookwise connected four-piece dissection exists. -/
theorem no_rook_dissection_65_72_97 : NoRookDissection 65 72 97 :=
  noRook_of_no no_dissection_65_72_97

end Ex89

#print Ex89.check_65_72_97._native.native_decide.ax_1_1
#print axioms Ex89.no_dissection_65_72_97
#print axioms Ex89.no_rook_dissection_65_72_97
