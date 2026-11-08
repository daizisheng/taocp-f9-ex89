import Ex89.ThreeOneArith
import Ex89.ThreeOneCore
import Ex89.ThreeOneCount
import Ex89.ThreeOneNormal
/-! # The 3+1 theorem.
The proof is in `PROOF.md`, Part 2: normal form and lemma 1 (`ThreeOneNormal`), row sums (`ThreeOneCount`),
arithmetic (`ThreeOneArith`) and the one-dimensional core, lemmas 2 and 3 (`ThreeOneCore`). -/
namespace Ex89.ThreeOne

/-- The flag of the coordinate that motion `m` sends to `imgY`. -/
def flg (m : Motion) : Bool := if m.sw then m.fx else m.fy

/-- The constant of `srcLine` as an affine map. -/
def cst (m : Motion) (w : Nat) : Int := if flg m then (w : Int) - 1 + m.dy else - m.dy

theorem srcLine_aff (m : Motion) (w : Nat) (r : Int) : srcLine m w r = aff (flg m) (cst m w) r := by
  rcases m with ⟨sw, fx, fy, dx, dy⟩
  cases sw <;> cases fx <;> cases fy <;> simp [srcLine, aff, cst, flg] <;> omega

/-- **3+1 theorem.** If `0 < u < v < w`, `u² + v² = w²` and `(u, v, w)` is not a multiple of
`(3, 4, 5)`, there is no dissection in which exactly three pieces go to the `u × u` square. -/
theorem no_three_one (u v w : Nat) (hu : 0 < u) (huv : u < v) (hvw : v < w)
    (hp : u * u + v * v = w * w) (hn : ¬ ∃ k, u = 3 * k ∧ v = 4 * k ∧ w = 5 * k)
    (D : Dissection u v w) (h31 : ∃ k, D.toU k = false ∧ ∀ j, j ≠ k → D.toU j = true) : False := by
  have h2d := ar_2d huv hvw hp
  have h3d : u ≠ 3 * (w - v) := fun h => hn (ar_3d huv hvw hp h)
  have h3a := ar_3a hu huv hvw hp
  have hwin : 2 * ((w : Int) - u) ≤ u → ((w : Int) - u) + (w - v) < u ∧ 2 * ((w : Int) - u) ≠ u := by
    intro h; have := ar_win hu huv hvw hp (by omega); omega
  have h205 : 2 * (u : Int) = 5 * ((w : Int) - v) → ((w : Int) - v) + 2 * ((w : Int) - u) ≠ u := by
    intro h; have := ar_205 hu huv hvw hp (by omega); omega
  obtain ⟨E, t0, t1, t2, t3, b0, b1, b2, b3, s1, s3⟩ := exists_normal31 hu huv hvw h2d D h31
  have hB : Box31 E := ⟨t0, t1, t2, t3, b0, b1, b2, b3⟩
  have img : ∀ k : Fin 4, k ≠ 0 → ∀ i, 0 < lineCnt E k i →
      ∃ r : Int, 0 ≤ r ∧ r < u ∧ aff (flg (E.motion k)) (cst (E.motion k) w) r = i := by
    intro k hk i h
    obtain ⟨r, h0, h1, h2⟩ := line_img E hB k hk i h
    exact ⟨r, h0, h1, by rw [← srcLine_aff]; exact h2⟩
  have row : ∀ r : Int, 0 ≤ r → r < u →
      (lineCnt E 1 (aff (flg (E.motion 1)) (cst (E.motion 1) w) r) : Int)
        + lineCnt E 2 (aff (flg (E.motion 2)) (cst (E.motion 2) w) r)
        + lineCnt E 3 (aff (flg (E.motion 3)) (cst (E.motion 3) w) r) = u := by
    intro r h0 h1
    have := row_sum E hB r h0 h1
    simp only [srcLine_aff] at this
    omega
  have l1 : ∀ i, lineCnt E 1 i = rowCnt E 1 i := fun i => by simp [lineCnt, s1]
  have l3 : ∀ i, lineCnt E 3 i = colCnt E 3 i := fun i => by simp [lineCnt, s3]
  cases hs2 : (E.motion 2).sw
  · -- case A: piece 2 maps source rows to target rows
    have l2 : ∀ i, lineCnt E 2 i = rowCnt E 2 i := fun i => by simp [lineCnt, hs2]
    refine core u v w (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hwin h205
      (rowCnt E 1) (rowCnt E 2) (colCnt E 3) _ _ _ _ _ _
      (fun y h => row1_out E hB huv hvw y h)
      (fun y h1 h2 => by have := row1_bd E hB huv hvw y h1 h2; omega)
      (fun y h1 h2 => by have := row12 E hB huv hvw y h1 h2; omega)
      (fun y h => row2_out E hB huv hvw y h)
      (fun y h1 h2 => by have := row2_arm E hB huv hvw y h1 h2; omega)
      (fun y h1 h2 => by have := row2_forced E hB huv hvw y h1 h2; omega)
      (fun y h => col3_out E hB huv hvw y h)
      (fun y h1 h2 => by have := col3_bd E hB huv hvw y h1 h2; omega)
      (fun y h => img 1 (by decide) y (by rw [l1]; exact h))
      (fun y h => img 2 (by decide) y (by rw [l2]; exact h))
      (fun y h => img 3 (by decide) y (by rw [l3]; exact h))
      (fun r h0 h1 => by have := row r h0 h1; rw [l1, l2, l3] at this; exact this)
  · -- case B: piece 2 maps source columns to target rows; pieces 3 and 1 swap roles
    have l2 : ∀ i, lineCnt E 2 i = colCnt E 2 i := fun i => by simp [lineCnt, hs2]
    refine core u v w (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hwin h205
      (colCnt E 3) (colCnt E 2) (rowCnt E 1) _ _ _ _ _ _
      (fun y h => col3_out E hB huv hvw y h)
      (fun y h1 h2 => by have := col3_bd E hB huv hvw y h1 h2; omega)
      (fun y h1 h2 => by have := col32 E hB huv hvw y h1 h2; omega)
      (fun y h => col2_out E hB huv hvw y h)
      (fun y h1 h2 => by have := col2_arm E hB huv hvw y h1 h2; omega)
      (fun y h1 h2 => by have := col2_forced E hB huv hvw y h1 h2; omega)
      (fun y h => row1_out E hB huv hvw y h)
      (fun y h1 h2 => by have := row1_bd E hB huv hvw y h1 h2; omega)
      (fun y h => img 3 (by decide) y (by rw [l3]; exact h))
      (fun y h => img 2 (by decide) y (by rw [l2]; exact h))
      (fun y h => img 1 (by decide) y (by rw [l1]; exact h))
      (fun r h0 h1 => by have := row r h0 h1; rw [l1, l2, l3] at this; omega)

end Ex89.ThreeOne

#print axioms Ex89.ThreeOne.no_three_one
