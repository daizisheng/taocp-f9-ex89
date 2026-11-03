import Ex89.RookCheck
/-! The final theorem for `(39, 80, 89)`. The search is run by `native_decide`, in parallel. -/
namespace Ex89

/-- The whole search for `(39, 80, 89)` finds a contradiction in every case. -/
theorem check_39_80_89 : checkR 39 80 89 = true := by native_decide

/-- **Exercise 89 for `(39, 80, 89)`.** No rookwise connected four-piece dissection exists. -/
theorem no_rook_dissection_39_80_89 : NoRookDissection 39 80 89 :=
  no_rook_of_check (by decide) (by decide) (by decide) (by decide) check_39_80_89

end Ex89

#print Ex89.check_39_80_89._native.native_decide.ax_1_1
#print axioms Ex89.no_rook_dissection_39_80_89
