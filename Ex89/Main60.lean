import Ex89.Rook
/-! The final theorems for `(60, 63, 87)`. The search is run by `native_decide`, in parallel. -/
namespace Ex89

/-- The whole search for `(60, 63, 87)` finds a contradiction in every case. -/
theorem check_60_63_87 : checkAll 60 63 87 = true := by native_decide

/-- No four-piece dissection of the `87 × 87` square into `60 × 60` and `63 × 63` squares, as long as
each piece goes to one square. -/
theorem no_dissection_60_63_87 : NoDissection 60 63 87 :=
  no_dissection_of_check (by decide) (by decide) (by decide) (by decide) check_60_63_87

/-- **Exercise 89 for `(60, 63, 87)`.** No rookwise connected four-piece dissection exists. -/
theorem no_rook_dissection_60_63_87 : NoRookDissection 60 63 87 :=
  noRook_of_no no_dissection_60_63_87

end Ex89

#print Ex89.check_60_63_87._native.native_decide.ax_1_1
#print axioms Ex89.no_dissection_60_63_87
#print axioms Ex89.no_rook_dissection_60_63_87
