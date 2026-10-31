import Ex89.Normal
/-! A rookwise connected piece cannot cross the empty column between the two squares. -/
namespace Ex89

theorem Motion.stepX (m : Motion) (w a b : Nat) :
    m.imgX w (a + 1) b - m.imgX w a b ≤ 1 ∧ m.imgX w a b - m.imgX w (a + 1) b ≤ 1 := by
  rcases m with ⟨sw, fx, fy, dx, dy⟩
  cases sw <;> cases fx <;> cases fy <;> simp [Motion.imgX] <;> omega

theorem Motion.stepY (m : Motion) (w a b : Nat) :
    m.imgX w a (b + 1) - m.imgX w a b ≤ 1 ∧ m.imgX w a b - m.imgX w a (b + 1) ≤ 1 := by
  rcases m with ⟨sw, fx, fy, dx, dy⟩
  cases sw <;> cases fx <;> cases fy <;> simp [Motion.imgX] <;> omega

/-- Two points of the shape whose first coordinates differ by at most one are in the same square. -/
theorem same_square {u v : Nat} {ox oy a b a' b' : Int} (ho : (u : Int) < ox)
    (h1 : InShape u v ox oy a b) (h2 : InShape u v ox oy a' b') (d1 : a' - a ≤ 1) (d2 : a - a' ≤ 1) :
    InSquare u a b ↔ InSquare u a' b' := by
  simp only [InShape, InSquare] at *
  omega

variable {u v w : Nat} {ox oy : Int}

theorem path_same (R : RookDissection u v w ox oy) (ho : (u : Int) < ox) {x y x' y' : Nat} (hx : x < w) (hy : y < w)
    (p : RookPath w (fun a b => R.piece a b = R.piece x y) x y x' y') :
    x' < w ∧ y' < w ∧ R.piece x' y' = R.piece x y ∧
      (InSquare u ((R.motion (R.piece x y)).imgX w x' y') ((R.motion (R.piece x y)).imgY w x' y') ↔
       InSquare u ((R.motion (R.piece x y)).imgX w x y) ((R.motion (R.piece x y)).imgY w x y)) := by
  induction p with
  | refl => exact ⟨hx, hy, rfl, Iff.rfl⟩
  | @right a b _ h1 hp ih =>
    obtain ⟨i1, i2, i3, i4⟩ := ih
    have m1 := R.maps_into a b i1 i2
    have m2 := R.maps_into (a + 1) b h1 i2
    rw [i3] at m1; rw [hp] at m2
    have := Motion.stepX (R.motion (R.piece x y)) w a b
    exact ⟨h1, i2, hp, (same_square ho m2 m1 (by omega) (by omega)).trans i4⟩
  | @left a b _ hp ih =>
    obtain ⟨i1, i2, i3, i4⟩ := ih
    have ha : a < w := by omega
    have m1 := R.maps_into (a + 1) b i1 i2
    have m2 := R.maps_into a b ha i2
    rw [i3] at m1; rw [hp] at m2
    have := Motion.stepX (R.motion (R.piece x y)) w a b
    exact ⟨ha, i2, hp, (same_square ho m2 m1 (by omega) (by omega)).trans i4⟩
  | @up a b _ h1 hp ih =>
    obtain ⟨i1, i2, i3, i4⟩ := ih
    have m1 := R.maps_into a b i1 i2
    have m2 := R.maps_into a (b + 1) i1 h1
    rw [i3] at m1; rw [hp] at m2
    have := Motion.stepY (R.motion (R.piece x y)) w a b
    exact ⟨i1, h1, hp, (same_square ho m2 m1 (by omega) (by omega)).trans i4⟩
  | @down a b _ hp ih =>
    obtain ⟨i1, i2, i3, i4⟩ := ih
    have hb : b < w := by omega
    have m1 := R.maps_into a (b + 1) i1 i2
    have m2 := R.maps_into a b i1 hb
    rw [i3] at m1; rw [hp] at m2
    have := Motion.stepY (R.motion (R.piece x y)) w a b
    exact ⟨i1, hb, hp, (same_square ho m2 m1 (by omega) (by omega)).trans i4⟩

open Classical in
/-- Piece `k` goes to the `u × u` square. -/
noncomputable def tU (R : RookDissection u v w ox oy) (k : Fin 4) : Bool :=
  decide (∃ x y, x < w ∧ y < w ∧ R.piece x y = k ∧
    InSquare u ((R.motion k).imgX w x y) ((R.motion k).imgY w x y))

theorem tU_iff (R : RookDissection u v w ox oy) (ho : (u : Int) < ox) {x y : Nat} (hx : x < w) (hy : y < w) :
    tU R (R.piece x y) = true ↔
      InSquare u ((R.motion (R.piece x y)).imgX w x y) ((R.motion (R.piece x y)).imgY w x y) := by
  simp only [tU, decide_eq_true_eq]
  constructor
  · rintro ⟨a, b, ha, hb, e, hs⟩
    have hp := R.connected a b x y ha hb hx hy e
    have := path_same R ho ha hb hp
    rw [e] at this
    exact this.2.2.2.2 hs
  · intro h
    exact ⟨x, y, hx, hy, rfl, h⟩

/-- The motion of a piece for the `v × v` square, measured from the corner of that square. -/
def shiftM (m : Motion) (ox oy : Int) : Motion := { m with dx := m.dx - ox, dy := m.dy - oy }

theorem shiftM_X (m : Motion) (ox oy : Int) (w x y : Nat) :
    (shiftM m ox oy).imgX w x y = m.imgX w x y - ox := by
  rcases m with ⟨sw, fx, fy, dx, dy⟩
  cases sw <;> cases fx <;> cases fy <;> simp [shiftM, Motion.imgX] <;> omega

theorem shiftM_Y (m : Motion) (ox oy : Int) (w x y : Nat) :
    (shiftM m ox oy).imgY w x y = m.imgY w x y - oy := by
  rcases m with ⟨sw, fx, fy, dx, dy⟩
  cases sw <;> cases fx <;> cases fy <;> simp [shiftM, Motion.imgY] <;> omega

/-- A rookwise connected dissection gives a dissection with two separate squares. -/
noncomputable def RookDissection.toDissection (R : RookDissection u v w ox oy) (ho : (u : Int) < ox) :
    Dissection u v w where
  piece := R.piece
  motion k := if tU R k then R.motion k else shiftM (R.motion k) ox oy
  toU := tU R
  maps_into x y hx hy := by
    have hm := R.maps_into x y hx hy
    have hi := tU_iff R ho hx hy
    cases ht : tU R (R.piece x y)
    · rw [ht] at hi
      have hn : ¬ InSquare u ((R.motion (R.piece x y)).imgX w x y) ((R.motion (R.piece x y)).imgY w x y) := by
        simpa using hi
      simp only [Bool.false_eq_true, ite_false, shiftM_X, shiftM_Y]
      exact hm.resolve_left hn
    · rw [ht] at hi
      simp only [ite_true]
      exact hi.1 rfl
  injective x y x' y' hx hy hx' hy' hb h1 h2 := by
    apply R.injective x y x' y' hx hy hx' hy'
    · cases ht : tU R (R.piece x y)
      · have ht' : tU R (R.piece x' y') = false := by rw [← hb, ht]
        simp only [ht, ht', Bool.false_eq_true, ite_false, shiftM_X] at h1
        omega
      · have ht' : tU R (R.piece x' y') = true := by rw [← hb, ht]
        simpa only [ht, ht', ite_true] using h1
    · cases ht : tU R (R.piece x y)
      · have ht' : tU R (R.piece x' y') = false := by rw [← hb, ht]
        simp only [ht, ht', Bool.false_eq_true, ite_false, shiftM_Y] at h2
        omega
      · have ht' : tU R (R.piece x' y') = true := by rw [← hb, ht]
        simpa only [ht, ht', ite_true] using h2
  surjective b s t hs := by
    cases b
    · simp only [Bool.false_eq_true, ite_false] at hs
      have hshape : InShape u v ox oy (s + ox) (t + oy) := by
        right
        simp only [InSquare] at hs ⊢
        omega
      obtain ⟨x, y, hx, hy, h1, h2⟩ := R.surjective _ _ hshape
      have hi := tU_iff R ho hx hy
      have hn : tU R (R.piece x y) = false := by
        cases ht : tU R (R.piece x y)
        · rfl
        · exfalso
          have := hi.1 ht
          rw [h1, h2] at this
          simp only [InSquare] at this hs
          omega
      refine ⟨x, y, hx, hy, hn, ?_, ?_⟩
      · simp only [hn, Bool.false_eq_true, ite_false, shiftM_X, h1]; omega
      · simp only [hn, Bool.false_eq_true, ite_false, shiftM_Y, h2]; omega
    · simp only [ite_true] at hs
      obtain ⟨x, y, hx, hy, h1, h2⟩ := R.surjective s t (Or.inl hs)
      have hi := tU_iff R ho hx hy
      have hn : tU R (R.piece x y) = true := hi.2 (by rw [h1, h2]; exact hs)
      exact ⟨x, y, hx, hy, hn, by simp only [hn, ite_true, h1], by simp only [hn, ite_true, h2]⟩

/-- The stronger form implies the target theorem. -/
theorem noRook_of_no {u v w : Nat} (h : NoDissection u v w) : NoRookDissection u v w :=
  fun _ _ ho R => h (R.toDissection ho)

end Ex89
