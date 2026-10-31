import Ex89.Model
/-! Symmetries of a dissection: rotating the source, changing a target, relabeling the pieces. -/
namespace Ex89

theorem Motion.close (m : Motion) {w S x y x' y' : Nat} (h : InSquare S (m.imgX w x y) (m.imgY w x y))
    (h' : InSquare S (m.imgX w x' y') (m.imgY w x' y')) :
    (x : Int) - x' < S ∧ (x' : Int) - x < S ∧ (y : Int) - y' < S ∧ (y' : Int) - y < S := by
  rcases m with ⟨sw, fx, fy, dx, dy⟩
  cases sw <;> cases fx <;> cases fy <;> simp [Motion.imgX, Motion.imgY, InSquare] at * <;> omega

/-- The motion that first rotates the source cell, `(x, y) ↦ (y, w-1-x)`, and then applies `m`. -/
def Motion.rot (m : Motion) : Motion :=
  { sw := !m.sw, fx := !m.fy, fy := m.fx, dx := m.dx, dy := m.dy }

theorem Motion.rot_X (m : Motion) {w x y : Nat} (hx : x < w) :
    m.rot.imgX w x y = m.imgX w y (w - 1 - x) := by
  rcases m with ⟨sw, fx, fy, dx, dy⟩
  cases sw <;> cases fx <;> cases fy <;> simp [Motion.rot, Motion.imgX] <;> omega

theorem Motion.rot_Y (m : Motion) {w x y : Nat} (hx : x < w) :
    m.rot.imgY w x y = m.imgY w y (w - 1 - x) := by
  rcases m with ⟨sw, fx, fy, dx, dy⟩
  cases sw <;> cases fx <;> cases fy <;> simp [Motion.rot, Motion.imgY] <;> omega

/-- Rotate the source square. -/
def Dissection.rot {u v w : Nat} (D : Dissection u v w) : Dissection u v w where
  piece x y := D.piece y (w - 1 - x)
  motion k := (D.motion k).rot
  toU := D.toU
  maps_into x y hx hy := by
    have := D.maps_into y (w - 1 - x) hy (by omega)
    rw [Motion.rot_X _ hx, Motion.rot_Y _ hx]; exact this
  injective x y x' y' hx hy hx' hy' hb h1 h2 := by
    rw [Motion.rot_X _ hx, Motion.rot_X _ hx'] at h1
    rw [Motion.rot_Y _ hx, Motion.rot_Y _ hx'] at h2
    have := D.injective y (w - 1 - x) y' (w - 1 - x') hy (by omega) hy' (by omega) hb h1 h2
    omega
  surjective b s t hs := by
    obtain ⟨x, y, hx, hy, hb, h1, h2⟩ := D.surjective b s t hs
    refine ⟨w - 1 - y, x, by omega, hx, ?_, ?_, ?_⟩
    · have e : w - 1 - (w - 1 - y) = y := by omega
      simpa [e] using hb
    · have e : w - 1 - (w - 1 - y) = y := by omega
      rw [Motion.rot_X _ (by omega), e]; exact h1
    · have e : w - 1 - (w - 1 - y) = y := by omega
      rw [Motion.rot_Y _ (by omega), e]; exact h2

/-- A map of a target square onto itself, with its effect on motions. -/
structure TargetMap (S w : Nat) where
  h1 : Int → Int → Int
  h2 : Int → Int → Int
  T : Motion → Motion
  inv1 : ∀ a b, h1 (h1 a b) (h2 a b) = a
  inv2 : ∀ a b, h2 (h1 a b) (h2 a b) = b
  sq : ∀ a b, InSquare S a b → InSquare S (h1 a b) (h2 a b)
  tX : ∀ m x y, (T m).imgX w x y = h1 (m.imgX w x y) (m.imgY w x y)
  tY : ∀ m x y, (T m).imgY w x y = h2 (m.imgX w x y) (m.imgY w x y)

/-- Apply a map to the target square `b`. -/
def Dissection.mapT {u v w : Nat} (D : Dissection u v w) (b : Bool)
    (M : TargetMap (if b then u else v) w) : Dissection u v w where
  piece := D.piece
  motion k := if D.toU k = b then M.T (D.motion k) else D.motion k
  toU := D.toU
  maps_into x y hx hy := by
    have := D.maps_into x y hx hy
    by_cases hb : D.toU (D.piece x y) = b
    · subst hb
      simp only [ite_true, M.tX, M.tY]
      exact M.sq _ _ this
    · simp only [hb, ite_false]; exact this
  injective x y x' y' hx hy hx' hy' hb h1 h2 := by
    by_cases hc : D.toU (D.piece x y) = b
    · have hc' : D.toU (D.piece x' y') = b := by rw [← hb]; exact hc
      simp only [hc, hc', ite_true, M.tX, M.tY] at h1 h2
      have e1 := M.inv1 ((D.motion (D.piece x y)).imgX w x y) ((D.motion (D.piece x y)).imgY w x y)
      have e2 := M.inv2 ((D.motion (D.piece x y)).imgX w x y) ((D.motion (D.piece x y)).imgY w x y)
      have e3 := M.inv1 ((D.motion (D.piece x' y')).imgX w x' y') ((D.motion (D.piece x' y')).imgY w x' y')
      have e4 := M.inv2 ((D.motion (D.piece x' y')).imgX w x' y') ((D.motion (D.piece x' y')).imgY w x' y')
      rw [h1, h2] at e1 e2
      exact D.injective x y x' y' hx hy hx' hy' hb (e1.symm.trans e3) (e2.symm.trans e4)
    · have hc' : ¬ D.toU (D.piece x' y') = b := by rw [← hb]; exact hc
      simp only [hc, hc', ite_false] at h1 h2
      exact D.injective x y x' y' hx hy hx' hy' hb h1 h2
  surjective c s t hs := by
    by_cases hc : c = b
    · subst hc
      obtain ⟨x, y, hx, hy, hb, h1, h2⟩ := D.surjective c (M.h1 s t) (M.h2 s t) (M.sq _ _ hs)
      refine ⟨x, y, hx, hy, hb, ?_, ?_⟩
      · simp only [hb, ite_true, M.tX, M.tY, h1, h2, M.inv1]
      · simp only [hb, ite_true, M.tX, M.tY, h1, h2, M.inv2]
    · obtain ⟨x, y, hx, hy, hb, h1, h2⟩ := D.surjective c s t hs
      have hn : ¬ D.toU (D.piece x y) = b := by rw [hb]; exact hc
      exact ⟨x, y, hx, hy, hb, by simp only [hn, ite_false, h1], by simp only [hn, ite_false, h2]⟩

/-- Swap the two coordinates of a target. -/
def swapMap (S w : Nat) : TargetMap S w where
  h1 _ b := b
  h2 a _ := a
  T m := { sw := !m.sw, fx := m.fx, fy := m.fy, dx := m.dy, dy := m.dx }
  inv1 _ _ := rfl
  inv2 _ _ := rfl
  sq a b h := by simp only [InSquare] at *; omega
  tX m x y := by
    rcases m with ⟨sw, fx, fy, dx, dy⟩
    cases sw <;> cases fx <;> cases fy <;> simp [Motion.imgX, Motion.imgY]
  tY m x y := by
    rcases m with ⟨sw, fx, fy, dx, dy⟩
    cases sw <;> cases fx <;> cases fy <;> simp [Motion.imgX, Motion.imgY]

/-- Flip the first coordinate of a target. -/
def flipXMap (S w : Nat) : TargetMap S w where
  h1 a _ := (S : Int) - 1 - a
  h2 _ b := b
  T m := if m.sw then { m with fy := !m.fy, dx := (S : Int) - w - m.dx }
         else { m with fx := !m.fx, dx := (S : Int) - w - m.dx }
  inv1 a _ := by show (S : Int) - 1 - ((S : Int) - 1 - a) = a; omega
  inv2 _ _ := rfl
  sq a b h := by simp only [InSquare] at *; omega
  tX m x y := by
    rcases m with ⟨sw, fx, fy, dx, dy⟩
    cases sw <;> cases fx <;> cases fy <;> simp [Motion.imgX] <;> omega
  tY m x y := by
    rcases m with ⟨sw, fx, fy, dx, dy⟩
    cases sw <;> cases fx <;> cases fy <;> simp [Motion.imgY]

/-- Flip the second coordinate of a target. -/
def flipYMap (S w : Nat) : TargetMap S w where
  h1 a _ := a
  h2 _ b := (S : Int) - 1 - b
  T m := if m.sw then { m with fx := !m.fx, dy := (S : Int) - w - m.dy }
         else { m with fy := !m.fy, dy := (S : Int) - w - m.dy }
  inv1 _ _ := rfl
  inv2 _ b := by show (S : Int) - 1 - ((S : Int) - 1 - b) = b; omega
  sq a b h := by simp only [InSquare] at *; omega
  tX m x y := by
    rcases m with ⟨sw, fx, fy, dx, dy⟩
    cases sw <;> cases fx <;> cases fy <;> simp [Motion.imgX]
  tY m x y := by
    rcases m with ⟨sw, fx, fy, dx, dy⟩
    cases sw <;> cases fx <;> cases fy <;> simp [Motion.imgY] <;> omega

/-- Change the piece names. -/
def Dissection.relabel {u v w : Nat} (D : Dissection u v w) (σ τ : Fin 4 → Fin 4)
    (h : ∀ k, τ (σ k) = k) : Dissection u v w where
  piece x y := σ (D.piece x y)
  motion k := D.motion (τ k)
  toU k := D.toU (τ k)
  maps_into x y hx hy := by simpa only [h] using D.maps_into x y hx hy
  injective x y x' y' hx hy hx' hy' hb h1 h2 := by
    simp only [h] at hb h1 h2
    exact D.injective x y x' y' hx hy hx' hy' hb h1 h2
  surjective b s t hs := by
    obtain ⟨x, y, hx, hy, hb, h1, h2⟩ := D.surjective b s t hs
    exact ⟨x, y, hx, hy, by simpa only [h] using hb, by simpa only [h] using h1,
      by simpa only [h] using h2⟩

end Ex89
