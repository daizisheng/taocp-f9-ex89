import Ex89.RookCheck
/-! The final theorem for `(33, 56, 65)`. The search is run by `native_decide`, in parallel. -/
namespace Ex89

/-- The whole search for `(33, 56, 65)` finds a contradiction in every case. -/
theorem check_33_56_65 : checkR 33 56 65 = true := by native_decide

/-- **Exercise 89 for `(33, 56, 65)`.** No rookwise connected four-piece dissection exists. -/
theorem no_rook_dissection_33_56_65 : NoRookDissection 33 56 65 :=
  no_rook_of_check (by decide) (by decide) (by decide) (by decide) check_33_56_65

end Ex89

#print Ex89.check_33_56_65._native.native_decide.ax_1_1
#print axioms Ex89.no_rook_dissection_33_56_65
