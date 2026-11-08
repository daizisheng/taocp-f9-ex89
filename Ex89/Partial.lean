import Ex89.T22.Main
import Ex89.ThreeOne
/-!
# A partial theorem for all Pythagorean triples

Split a `Dissection u v w` by the number of pieces that go to the `u × u` square. Zero pieces or
four pieces cannot be, because then one of the two squares is not covered. Two pieces is the
2+2 theorem `T22.no_two_two`, and three pieces is the 3+1 theorem `ThreeOne.no_three_one`. So only
one piece can go to the `u × u` square. That case, 1+3, is not settled here.
-/
namespace Ex89

theorem fin4_cases (k : Fin 4) : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by
  revert k; decide

/-- A function `Fin 4 → Bool` that takes both values, is `true` at neither exactly two points
nor exactly three points, is `true` at exactly one point. -/
theorem split_count (f : Fin 4 → Bool) (hT : ∃ k, f k = true) (hF : ∃ k, f k = false)
    (h2 : ((List.finRange 4).filter f).length ≠ 2)
    (h3 : ¬ ∃ k, f k = false ∧ ∀ j, j ≠ k → f j = true) :
    ((List.finRange 4).filter f).length = 1 := by
  have hfr : List.finRange 4 = [0, 1, 2, 3] := by decide
  rw [hfr] at h2 ⊢
  obtain ⟨a, ha⟩ := hT
  obtain ⟨b, hb⟩ := hF
  cases c0 : f 0 <;> cases c1 : f 1 <;> cases c2 : f 2 <;> cases c3 : f 3 <;>
    simp [List.filter, c0, c1, c2, c3] at h2 ⊢ <;>
    first
    | (apply h3; refine ⟨0, c0, ?_⟩; intro j hj
       rcases fin4_cases j with rfl | rfl | rfl | rfl <;> simp_all
       done)
    | (apply h3; refine ⟨1, c1, ?_⟩; intro j hj
       rcases fin4_cases j with rfl | rfl | rfl | rfl <;> simp_all
       done)
    | (apply h3; refine ⟨2, c2, ?_⟩; intro j hj
       rcases fin4_cases j with rfl | rfl | rfl | rfl <;> simp_all
       done)
    | (apply h3; refine ⟨3, c3, ?_⟩; intro j hj
       rcases fin4_cases j with rfl | rfl | rfl | rfl <;> simp_all
       done)
    | (rcases fin4_cases a with rfl | rfl | rfl | rfl <;>
       rcases fin4_cases b with rfl | rfl | rfl | rfl <;> simp_all)

/-- Each of the two squares receives at least one piece: its corner cell `(0, 0)` has a preimage. -/
theorem exists_toU {u v w : Nat} (hu : 0 < u) (hv : 0 < v) (D : Dissection u v w) (b : Bool) :
    ∃ k, D.toU k = b := by
  have hs : InSquare (if b then u else v) 0 0 := by
    cases b <;> simp [InSquare] <;> omega
  obtain ⟨x, y, _, _, h, _⟩ := D.surjective b 0 0 hs
  exact ⟨_, h⟩

/-- **Partial theorem.** If `0 < u < v < w`, `u² + v² = w²` and `(u, v, w)` is not a multiple of
`(3, 4, 5)`, then in every `Dissection u v w` exactly one piece goes to the `u × u` square. -/
theorem one_piece_to_u (u v w : Nat) (hu : 0 < u) (huv : u < v) (hvw : v < w)
    (hp : u * u + v * v = w * w) (hn : ¬ ∃ k, u = 3 * k ∧ v = 4 * k ∧ w = 5 * k)
    (D : Dissection u v w) :
    ((List.finRange 4).filter (fun k => D.toU k)).length = 1 :=
  split_count D.toU (exists_toU hu (by omega) D true) (exists_toU hu (by omega) D false)
    (T22.no_two_two u v w hu huv hvw hp hn D)
    (ThreeOne.no_three_one u v w hu huv hvw hp hn D)

#print axioms one_piece_to_u

end Ex89
