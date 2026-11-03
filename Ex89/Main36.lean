import Ex89.RookCheck
/-! The final theorem for `(36, 77, 85)`. The search is run by `native_decide`, in parallel. -/
namespace Ex89

/-- The whole search for `(36, 77, 85)` finds a contradiction in every case. -/
theorem check_36_77_85 : checkR 36 77 85 = true := by native_decide

/-- **Exercise 89 for `(36, 77, 85)`.** No rookwise connected four-piece dissection exists. -/
theorem no_rook_dissection_36_77_85 : NoRookDissection 36 77 85 :=
  no_rook_of_check (by decide) (by decide) (by decide) (by decide) check_36_77_85

end Ex89

#print Ex89.check_36_77_85._native.native_decide.ax_1_1
#print axioms Ex89.no_rook_dissection_36_77_85
