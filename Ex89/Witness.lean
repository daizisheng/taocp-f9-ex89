import Ex89.Normal
import Ex89.Rook
/-!
A real example, checked by the kernel: the rookwise connected dissection of the `5 × 5` square into
`3 × 3` and `4 × 4` squares. It shows that the definitions are not empty, so the theorems of this
repository do not hold for a trivial reason. The colors, with the first row at the top, are

```
33000
22000
22000
22211
22221
```
-/
namespace Ex89.Witness

/-- The piece of cell `(x, y)`, as a list of columns. -/
def table : List (List (Fin 4)) := [[2, 2, 2, 2, 3], [2, 2, 2, 2, 3], [2, 2, 0, 0, 0], [2, 1, 0, 0, 0], [1, 1, 0, 0, 0]]

def piece (x y : Nat) : Fin 4 := (table.getD x []).getD y 0

def motion : Fin 4 → Motion
  | 0 => { sw := false, fx := false, fy := false, dx := -2, dy := -2 }
  | 1 => { sw := false, fx := false, fy := false, dx := 3, dy := 1 }
  | 2 => { sw := false, fx := false, fy := false, dx := 4, dy := 0 }
  | 3 => { sw := false, fx := false, fy := false, dx := 6, dy := -1 }

/-- A rook step: `0` right, `1` left, `2` up, `3` down. -/
def step (m a b : Nat) : Option (Nat × Nat) :=
  match m with
  | 0 => some (a + 1, b)
  | 1 => if a = 0 then none else some (a - 1, b)
  | 2 => some (a, b + 1)
  | _ => if b = 0 then none else some (a, b - 1)

/-- Follow rook steps, staying inside piece `k`. -/
def walk (k : Fin 4) : List Nat → Nat → Nat → Option (Nat × Nat)
  | [], a, b => some (a, b)
  | m :: l, a, b =>
    match step m a b with
    | none => none
    | some (c, d) => if c < 5 ∧ d < 5 ∧ piece c d = k then walk k l c d else none

/-- The steps from the first cell of a piece to the cell `(x, y)`. -/
def moves : List (List (List Nat)) :=
  [[[], [2], [2, 2], [2, 2, 2], []],
   [[0], [0, 2], [0, 2, 2], [0, 2, 2, 2], [0]],
   [[0, 0], [0, 0, 2], [], [2], [2, 2]],
   [[0, 0, 0], [], [0], [0, 2], [0, 2, 2]],
   [[0, 3], [0], [0, 0], [0, 0, 2], [0, 0, 2, 2]]]

def hub : List (Nat × Nat) := [(2, 2), (3, 1), (0, 0), (0, 4)]

def hubOf (k : Fin 4) : Nat × Nat := hub.getD k.val (0, 0)
def movesOf (x y : Nat) : List Nat := (moves.getD x []).getD y []

variable {w : Nat} {P : Nat → Nat → Prop}

theorem path_trans {a b c d e f : Nat} (p : RookPath w P a b c d) (q : RookPath w P c d e f) :
    RookPath w P a b e f := by
  induction q with
  | refl => exact p
  | right _ h1 h2 ih => exact .right ih h1 h2
  | left _ h ih => exact .left ih h
  | up _ h1 h2 ih => exact .up ih h1 h2
  | down _ h ih => exact .down ih h

theorem path_inv {a b c d : Nat} (ha : a < w) (hb : b < w) (hP : P a b) (p : RookPath w P a b c d) :
    c < w ∧ d < w ∧ P c d := by
  induction p with
  | refl => exact ⟨ha, hb, hP⟩
  | right _ h1 h2 ih => exact ⟨h1, ih.2.1, h2⟩
  | left _ h ih => exact ⟨by have := ih.1; omega, ih.2.1, h⟩
  | up _ h1 h2 ih => exact ⟨ih.1, h1, h2⟩
  | down _ h ih => exact ⟨ih.1, by have := ih.2.1; omega, h⟩

theorem path_symm {a b c d : Nat} (ha : a < w) (hb : b < w) (hP : P a b) (p : RookPath w P a b c d) :
    RookPath w P c d a b := by
  induction p with
  | refl => exact .refl _ _
  | @right e f q h1 h2 ih =>
    have i := path_inv ha hb hP q
    exact path_trans (.left (.refl _ _) i.2.2) ih
  | @left e f q h ih =>
    have i := path_inv ha hb hP q
    exact path_trans (.right (.refl _ _) i.1 i.2.2) ih
  | @up e f q h1 h2 ih =>
    have i := path_inv ha hb hP q
    exact path_trans (.down (.refl _ _) i.2.2) ih
  | @down e f q h ih =>
    have i := path_inv ha hb hP q
    exact path_trans (.up (.refl _ _) i.2.1 i.2.2) ih

theorem walk_path {k : Fin 4} (l : List Nat) {a b e f : Nat} (h : walk k l a b = some (e, f)) :
    RookPath 5 (fun c d => piece c d = k) a b e f := by
  induction l generalizing a b with
  | nil =>
    simp only [walk, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact .refl _ _
  | cons m l ih =>
    simp only [walk] at h
    split at h
    · simp at h
    next c d hs =>
      split at h
      next hc =>
        obtain ⟨h1, h2, h3⟩ := hc
        refine path_trans ?_ (ih h)
        simp only [step] at hs
        split at hs
        · simp only [Option.some.injEq, Prod.mk.injEq] at hs
          obtain ⟨rfl, rfl⟩ := hs
          exact .right (.refl _ _) h1 h3
        · split at hs
          · simp at hs
          · simp only [Option.some.injEq, Prod.mk.injEq] at hs
            obtain ⟨rfl, rfl⟩ := hs
            obtain ⟨n, rfl⟩ : ∃ n, a = n + 1 := ⟨a - 1, by omega⟩
            exact .left (.refl _ _) (by simpa using h3)
        · simp only [Option.some.injEq, Prod.mk.injEq] at hs
          obtain ⟨rfl, rfl⟩ := hs
          exact .up (.refl _ _) h2 h3
        · split at hs
          · simp at hs
          · simp only [Option.some.injEq, Prod.mk.injEq] at hs
            obtain ⟨rfl, rfl⟩ := hs
            obtain ⟨n, rfl⟩ : ∃ n, b = n + 1 := ⟨b - 1, by omega⟩
            exact .down (.refl _ _) (by simpa using h3)
      · simp at h

instance (s : Nat) (a b : Int) : Decidable (InSquare s a b) := by
  unfold InSquare; infer_instance

instance (u v : Nat) (ox oy a b : Int) : Decidable (InShape u v ox oy a b) := by
  unfold InShape; infer_instance

theorem check_maps : ∀ x, x < 5 → ∀ y, y < 5 →
    InShape 3 4 4 0 ((motion (piece x y)).imgX 5 x y) ((motion (piece x y)).imgY 5 x y) := by
  decide +kernel

/-- Two cells with the same image are equal. -/
def InjAt (x y x' y' : Nat) : Prop :=
  (motion (piece x y)).imgX 5 x y = (motion (piece x' y')).imgX 5 x' y' →
  (motion (piece x y)).imgY 5 x y = (motion (piece x' y')).imgY 5 x' y' → x = x' ∧ y = y'

instance (x y x' y' : Nat) : Decidable (InjAt x y x' y') := by
  unfold InjAt; infer_instance

theorem check_inj : ∀ x, x < 5 → ∀ y, y < 5 → ∀ x', x' < 5 → ∀ y', y' < 5 → InjAt x y x' y' := by
  decide +kernel

theorem check_surjU : ∀ a : Nat, a < 3 → ∀ b : Nat, b < 3 → ∃ x, x < 5 ∧ ∃ y, y < 5 ∧
    (motion (piece x y)).imgX 5 x y = (a : Int) ∧ (motion (piece x y)).imgY 5 x y = (b : Int) := by
  decide +kernel

theorem check_surjV : ∀ a : Nat, a < 4 → ∀ b : Nat, b < 4 → ∃ x, x < 5 ∧ ∃ y, y < 5 ∧
    (motion (piece x y)).imgX 5 x y = (a : Int) + 4 ∧ (motion (piece x y)).imgY 5 x y = (b : Int) := by
  decide +kernel

theorem check_walk : ∀ x, x < 5 → ∀ y, y < 5 →
    walk (piece x y) (movesOf x y) (hubOf (piece x y)).1 (hubOf (piece x y)).2 = some (x, y) := by
  decide +kernel

theorem check_hub : ∀ k : Fin 4, (hubOf k).1 < 5 ∧ (hubOf k).2 < 5 ∧ piece (hubOf k).1 (hubOf k).2 = k := by
  decide +kernel

/-- The dissection of the `5 × 5` square into `3 × 3` and `4 × 4` squares. -/
def rook345 : RookDissection 3 4 5 4 0 where
  piece := piece
  motion := motion
  connected x y x' y' hx hy hx' hy' e := by
    obtain ⟨h1, h2, h3⟩ := check_hub (piece x y)
    have p := walk_path _ (check_walk x hx y hy)
    have q := walk_path _ (check_walk x' hx' y' hy')
    rw [← e] at q
    exact path_trans (path_symm h1 h2 h3 p) q
  maps_into x y hx hy := check_maps x hx y hy
  injective x y x' y' hx hy hx' hy' h1 h2 := check_inj x hx y hy x' hx' y' hy' h1 h2
  surjective s t hs := by
    rcases hs with hs | hs
    · simp only [InSquare] at hs
      obtain ⟨x, hx, y, hy, h1, h2⟩ := check_surjU s.toNat (by omega) t.toNat (by omega)
      exact ⟨x, y, hx, hy, by rw [h1]; omega, by rw [h2]; omega⟩
    · simp only [InSquare] at hs
      obtain ⟨x, hx, y, hy, h1, h2⟩ := check_surjV (s - 4).toNat (by omega) (t - 0).toNat (by omega)
      exact ⟨x, y, hx, hy, by rw [h1]; omega, by rw [h2]; omega⟩

/-- So the definitions have examples. -/
theorem rook_nonempty : Nonempty (RookDissection 3 4 5 4 0) := ⟨rook345⟩

theorem dissection_nonempty : Nonempty (Dissection 3 4 5) :=
  ⟨rook345.toDissection (by decide)⟩

/-- The search does not accept `(3, 4, 5)`. This follows from the example, by the kernel only. -/
theorem checkAll_3_4_5 : checkAll 3 4 5 ≠ true := fun h =>
  no_dissection_of_check (by decide) (by decide) (by decide) (by decide) h
    (rook345.toDissection (by decide))

end Ex89.Witness

#print axioms Ex89.Witness.rook_nonempty
#print axioms Ex89.Witness.checkAll_3_4_5
