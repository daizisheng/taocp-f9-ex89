import Ex89.Rook
/-! The final theorems. The search is run by `native_decide`, in parallel. -/
namespace Ex89

/-- The whole search for `(20, 21, 29)` finds a contradiction in every case. -/
theorem check_20_21_29 : checkAll 20 21 29 = true := by native_decide

/-- No four-piece dissection of the `29 × 29` square into `20 × 20` and `21 × 21` squares, as long as
each piece goes to one square. -/
theorem no_dissection_20_21_29 : NoDissection 20 21 29 :=
  no_dissection_of_check (by decide) (by decide) (by decide) (by decide) check_20_21_29

/-- **Exercise 89 for `(20, 21, 29)`.** No rookwise connected four-piece dissection exists. -/
theorem no_rook_dissection_20_21_29 : NoRookDissection 20 21 29 :=
  noRook_of_no no_dissection_20_21_29

end Ex89

#print Ex89.check_20_21_29._native.native_decide.ax_1_1
#print axioms Ex89.no_dissection_20_21_29
#print axioms Ex89.no_rook_dissection_20_21_29
