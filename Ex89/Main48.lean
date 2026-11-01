import Ex89.Rook
/-! The final theorems for `(40, 42, 58)`. The search is run by `native_decide`, in parallel. -/
namespace Ex89

/-- The whole search for `(40, 42, 58)` finds a contradiction in every case. -/
theorem check_48_55_73 : checkAll 48 55 73 = true := by native_decide

/-- No four-piece dissection of the `58 × 58` square into `40 × 40` and `42 × 42` squares, as long as
each piece goes to one square. -/
theorem no_dissection_48_55_73 : NoDissection 48 55 73 :=
  no_dissection_of_check (by decide) (by decide) (by decide) (by decide) check_48_55_73

/-- **Exercise 89 for `(40, 42, 58)`.** No rookwise connected four-piece dissection exists. -/
theorem no_rook_dissection_48_55_73 : NoRookDissection 48 55 73 :=
  noRook_of_no no_dissection_48_55_73

end Ex89

#print Ex89.check_48_55_73._native.native_decide.ax_1_1
#print axioms Ex89.no_dissection_48_55_73
#print axioms Ex89.no_rook_dissection_48_55_73
