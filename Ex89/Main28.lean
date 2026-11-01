import Ex89.RookCheck
/-! The final theorem for `(28, 45, 53)`. The search is run by `native_decide`, in parallel. -/
namespace Ex89

/-- The whole search for `(28, 45, 53)` finds a contradiction in every case. -/
theorem check_28_45_53 : checkR 28 45 53 = true := by native_decide

/-- **Exercise 89 for `(28, 45, 53)`.** No rookwise connected four-piece dissection exists. -/
theorem no_rook_dissection_28_45_53 : NoRookDissection 28 45 53 :=
  no_rook_of_check (by decide) (by decide) (by decide) (by decide) check_28_45_53

end Ex89

#print Ex89.check_28_45_53._native.native_decide.ax_1_1
#print axioms Ex89.no_rook_dissection_28_45_53
