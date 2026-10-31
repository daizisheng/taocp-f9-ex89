/-!
# Discrete dissections (TAOCP 7.2.2.8, exercises 86--89)

The definitions in this file are the statement of the theorem, so they are kept short.

A *motion* is one of the eight symmetries of the `w × w` square followed by an integer shift.
This is the form `α β` of Section 7.2.2.8. A dissection of the `w × w` square into squares of
sides `u` and `v` colors the cells with four colors. Each color has one motion and one target
square, and together these give a bijection from the `w × w` square to the two target squares.

The target theorems are `NoRookDissection` and `NoDissection` at the end of this file.
-/

namespace Ex89

/-- A symmetry of the square, given by an optional swap of coordinates and two optional flips,
followed by a shift. -/
structure Motion where
  sw : Bool
  fx : Bool
  fy : Bool
  dx : Int
  dy : Int

/-- First coordinate of the image of cell `(x, y)` of the `w × w` square. -/
def Motion.imgX (m : Motion) (w : Nat) (x y : Nat) : Int :=
  (if m.sw then (if m.fy then (w : Int) - 1 - y else y)
   else (if m.fx then (w : Int) - 1 - x else x)) + m.dx

/-- Second coordinate of the image of cell `(x, y)` of the `w × w` square. -/
def Motion.imgY (m : Motion) (w : Nat) (x y : Nat) : Int :=
  (if m.sw then (if m.fx then (w : Int) - 1 - x else x)
   else (if m.fy then (w : Int) - 1 - y else y)) + m.dy

/-- The point `(a, b)` lies in the `s × s` square with corner at the origin. -/
def InSquare (s : Nat) (a b : Int) : Prop :=
  0 ≤ a ∧ a < s ∧ 0 ≤ b ∧ b < s

/-- The point `(a, b)` lies in the shape `B`: the `u × u` square at the origin or the `v × v`
square with corner `(ox, oy)`. -/
def InShape (u v : Nat) (ox oy a b : Int) : Prop :=
  InSquare u a b ∨ InSquare v (a - ox) (b - oy)

/-- A four-piece dissection of the `w × w` square into two separate squares of sides `u` and `v`.
`toU k` says that piece `k` goes to the `u × u` square, and otherwise it goes to the `v × v` square.
A piece may be disconnected or empty, but all its cells use one motion and go to one square. -/
structure Dissection (u v w : Nat) where
  piece : Nat → Nat → Fin 4
  motion : Fin 4 → Motion
  toU : Fin 4 → Bool
  maps_into : ∀ x y, x < w → y < w →
    InSquare (if toU (piece x y) then u else v)
      ((motion (piece x y)).imgX w x y) ((motion (piece x y)).imgY w x y)
  injective : ∀ x y x' y', x < w → y < w → x' < w → y' < w →
    toU (piece x y) = toU (piece x' y') →
    (motion (piece x y)).imgX w x y = (motion (piece x' y')).imgX w x' y' →
    (motion (piece x y)).imgY w x y = (motion (piece x' y')).imgY w x' y' →
    x = x' ∧ y = y'
  surjective : ∀ (b : Bool) (s t : Int), InSquare (if b then u else v) s t →
    ∃ x y, x < w ∧ y < w ∧ toU (piece x y) = b ∧
      (motion (piece x y)).imgX w x y = s ∧ (motion (piece x y)).imgY w x y = t

/-- Two cells of the `w × w` square are joined by rook steps inside the set `P`. -/
inductive RookPath (w : Nat) (P : Nat → Nat → Prop) : Nat → Nat → Nat → Nat → Prop
  | refl (x y : Nat) : RookPath w P x y x y
  | right {x y a b : Nat} : RookPath w P x y a b → a + 1 < w → P (a + 1) b →
      RookPath w P x y (a + 1) b
  | left {x y a b : Nat} : RookPath w P x y (a + 1) b → P a b → RookPath w P x y a b
  | up {x y a b : Nat} : RookPath w P x y a b → b + 1 < w → P a (b + 1) →
      RookPath w P x y a (b + 1)
  | down {x y a b : Nat} : RookPath w P x y a (b + 1) → P a b → RookPath w P x y a b

/-- A discrete dissection in the sense of exercises 88 and 89. The `w × w` square is colored with
at most four colors, and each color is rookwise connected. Each color has one motion, and the
motions give a bijection from the `w × w` square onto the shape `B`. The shape `B` is the `u × u`
square at the origin together with the `v × v` square whose corner is `(ox, oy)`, where `u < ox`.
So the two squares are separated by at least one empty column. -/
structure RookDissection (u v w : Nat) (ox oy : Int) where
  piece : Nat → Nat → Fin 4
  motion : Fin 4 → Motion
  connected : ∀ x y x' y', x < w → y < w → x' < w → y' < w → piece x y = piece x' y' →
    RookPath w (fun a b => piece a b = piece x y) x y x' y'
  maps_into : ∀ x y, x < w → y < w →
    InShape u v ox oy ((motion (piece x y)).imgX w x y) ((motion (piece x y)).imgY w x y)
  injective : ∀ x y x' y', x < w → y < w → x' < w → y' < w →
    (motion (piece x y)).imgX w x y = (motion (piece x' y')).imgX w x' y' →
    (motion (piece x y)).imgY w x y = (motion (piece x' y')).imgY w x' y' →
    x = x' ∧ y = y'
  surjective : ∀ s t : Int, InShape u v ox oy s t →
    ∃ x y, x < w ∧ y < w ∧
      (motion (piece x y)).imgX w x y = s ∧ (motion (piece x y)).imgY w x y = t

/-- **Target theorem for `(u, v, w)`**: exercise 89 has a negative answer for this triple, for every
placement of the two squares. -/
def NoRookDissection (u v w : Nat) : Prop :=
  ∀ ox oy : Int, (u : Int) < ox → RookDissection u v w ox oy → False

/-- **Stronger form**: no four-piece dissection at all, connected or not, as long as each piece
goes to one square. -/
def NoDissection (u v w : Nat) : Prop := Dissection u v w → False

end Ex89
