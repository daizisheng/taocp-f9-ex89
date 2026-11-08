/-!
# The 2+2 theorem: shared interface

Everything that more than one file of `Ex89/T22/` uses is defined here.

Conventions (the same as in the program that produced the data files):

* Parameters `p : Params` are eleven integers, index `0..10` =
  `d, e, f, t0x, t0y, t1x, t1y, t2x, t2y, t3x, t3y`.
  `u = d+e+f`, `v = d+2e+f`, `w = 2d+2e+f`, `a = d+e`.
* A linear form `LF` is a list of integers `[c₀, …, c₁₀, c₁₁]`; its value is
  `c₀ p₀ + … + c₁₀ p₁₀ + c₁₁` (index `11` is the constant). Shorter lists are padded by zeros,
  entries beyond index 11 are multiplied by `0`.
* An atom `.atom l` means `0 ≤ l.eval p`.
* Slots `k : Fin 4`: slots `0, 2` go to the `v × v` square,
  slots `1, 3` to the `u × u` square; `k` and `partner k = k xor 2` share a target square.
* The motion of slot `k` (from the `w × w` square `W` to the source square) is
  `g_k(x, y) = M_k (x, y) + t_k`, with `M_k = oriM (c.ori k)` and `t_k = (p.tx k, p.ty k)`.
  `c.ori 0 = c.ori 1 = 0` (identity).
-/
namespace Ex89.T22

/-! ## Parameters and linear forms -/

/-- Eleven integer parameters, `x i` for `i < 11`; see the module doc. -/
structure Params where
  x : Nat → Int

namespace Params
variable (p : Params)
def d : Int := p.x 0
def e : Int := p.x 1
def f : Int := p.x 2
def u : Int := p.d + p.e + p.f
def v : Int := p.d + 2 * p.e + p.f
def w : Int := 2 * p.d + 2 * p.e + p.f
def a : Int := p.d + p.e
/-- Translation of slot `k`. -/
def tx (k : Fin 4) : Int := p.x (3 + 2 * k.val)
def ty (k : Fin 4) : Int := p.x (4 + 2 * k.val)
/-- Coordinate `i` of the point `(p₀, …, p₁₀, 1)`; zero beyond. -/
def val (i : Nat) : Int := if i < 11 then p.x i else if i = 11 then 1 else 0
/-- Side of the target square of slot `k`. -/
def side (k : Fin 4) : Int := if k.val % 2 = 0 then p.v else p.u
end Params

/-- A linear form, see the module doc. -/
abbrev LF := List Int

def LF.evalFrom (p : Params) : List Int → Nat → Int
  | [], _ => 0
  | c :: l, i => c * p.val i + LF.evalFrom p l (i + 1)

/-- Value of a linear form. -/
def LF.eval (l : LF) (p : Params) : Int := LF.evalFrom p l 0


/-! ### Linear-form algebra -/

def LF.add : LF → LF → LF
  | [], l => l
  | a :: l, [] => a :: l
  | a :: l, b :: m => (a + b) :: LF.add l m

def LF.smul (c : Int) (l : LF) : LF := l.map (c * ·)
def LF.neg (l : LF) : LF := LF.smul (-1) l
def LF.sub (l m : LF) : LF := LF.add l (LF.neg m)
/-- The constant `c`. -/
def LF.const (c : Int) : LF := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, c]
/-- Add the constant `c`. -/
def LF.addc (l : LF) (c : Int) : LF := LF.add l (LF.const c)
/-- Parameter number `i` (`i < 11`). -/
def LF.var (i : Nat) : LF := List.replicate i 0 ++ [1]

theorem LF.evalFrom_add (p : Params) : ∀ (l m : LF) (i : Nat),
    LF.evalFrom p (LF.add l m) i = LF.evalFrom p l i + LF.evalFrom p m i
  | [], m, i => by simp [LF.add, LF.evalFrom]
  | a :: l, [], i => by simp [LF.add, LF.evalFrom]
  | a :: l, b :: m, i => by
    simp only [LF.add, LF.evalFrom, LF.evalFrom_add p l m (i + 1), Int.add_mul]; omega

theorem LF.evalFrom_smul (p : Params) (c : Int) : ∀ (l : LF) (i : Nat),
    LF.evalFrom p (LF.smul c l) i = c * LF.evalFrom p l i
  | [], i => by simp [LF.smul, LF.evalFrom]
  | a :: l, i => by
    have := LF.evalFrom_smul p c l (i + 1)
    simp only [LF.smul, List.map_cons, LF.evalFrom] at this ⊢
    rw [this, Int.mul_add, Int.mul_assoc]

theorem LF.eval_add (l m : LF) (p : Params) : (LF.add l m).eval p = l.eval p + m.eval p :=
  LF.evalFrom_add p l m 0
theorem LF.eval_smul (c : Int) (l : LF) (p : Params) : (LF.smul c l).eval p = c * l.eval p :=
  LF.evalFrom_smul p c l 0
theorem LF.eval_neg (l : LF) (p : Params) : (LF.neg l).eval p = - l.eval p := by
  simp [LF.neg, LF.eval_smul]
theorem LF.eval_sub (l m : LF) (p : Params) : (LF.sub l m).eval p = l.eval p - m.eval p := by
  simp [LF.sub, LF.eval_add, LF.eval_neg]; omega
theorem LF.eval_const (c : Int) (p : Params) : (LF.const c).eval p = c := by
  simp [LF.const, LF.eval, LF.evalFrom, Params.val]
theorem LF.eval_addc (l : LF) (c : Int) (p : Params) : (LF.addc l c).eval p = l.eval p + c := by
  simp [LF.addc, LF.eval_add, LF.eval_const]
theorem LF.evalFrom_replicate (p : Params) : ∀ (n i : Nat) (l : LF),
    LF.evalFrom p (List.replicate n 0 ++ l) i = LF.evalFrom p l (i + n)
  | 0, i, l => by simp
  | n + 1, i, l => by
    simp only [List.replicate_succ, List.cons_append, LF.evalFrom, Int.zero_mul, Int.zero_add]
    rw [LF.evalFrom_replicate p n (i + 1) l]; congr 1; omega
theorem LF.eval_var (i : Nat) (hi : i < 11) (p : Params) : (LF.var i).eval p = p.x i := by
  simp [LF.var, LF.eval, LF.evalFrom_replicate, LF.evalFrom, Params.val, hi]

/-- Named parameters and the derived lengths as linear forms. -/
def LF.d : LF := LF.var 0
def LF.e : LF := LF.var 1
def LF.f : LF := LF.var 2
def LF.u : LF := [1, 1, 1]
def LF.v : LF := [1, 2, 1]
def LF.w : LF := [2, 2, 1]
def LF.a : LF := [1, 1]
def LF.tx (k : Fin 4) : LF := LF.var (3 + 2 * k.val)
def LF.ty (k : Fin 4) : LF := LF.var (4 + 2 * k.val)
def LF.side (k : Fin 4) : LF := if k.val % 2 = 0 then LF.v else LF.u

theorem LF.eval_d (p : Params) : LF.d.eval p = p.d := LF.eval_var 0 (by omega) p
theorem LF.eval_e (p : Params) : LF.e.eval p = p.e := LF.eval_var 1 (by omega) p
theorem LF.eval_f (p : Params) : LF.f.eval p = p.f := LF.eval_var 2 (by omega) p
theorem LF.eval_u (p : Params) : LF.u.eval p = p.u := by
  simp [LF.u, LF.eval, LF.evalFrom, Params.val, Params.u, Params.d, Params.e, Params.f]; omega
theorem LF.eval_v (p : Params) : LF.v.eval p = p.v := by
  simp [LF.v, LF.eval, LF.evalFrom, Params.val, Params.v, Params.d, Params.e, Params.f]; omega
theorem LF.eval_w (p : Params) : LF.w.eval p = p.w := by
  simp [LF.w, LF.eval, LF.evalFrom, Params.val, Params.w, Params.d, Params.e, Params.f]; omega
theorem LF.eval_a (p : Params) : LF.a.eval p = p.a := by
  simp [LF.a, LF.eval, LF.evalFrom, Params.val, Params.a, Params.d, Params.e]
theorem LF.eval_tx (k : Fin 4) (p : Params) : (LF.tx k).eval p = p.tx k :=
  LF.eval_var _ (by omega) p
theorem LF.eval_ty (k : Fin 4) (p : Params) : (LF.ty k).eval p = p.ty k :=
  LF.eval_var _ (by omega) p
theorem LF.eval_side (k : Fin 4) (p : Params) : (LF.side k).eval p = p.side k := by
  unfold LF.side Params.side; split <;> simp [LF.eval_u, LF.eval_v]

/-! ## Formulas -/

/-- Negation-free formulas over linear atoms `0 ≤ l`. -/
inductive Fml where
  | atom : LF → Fml
  | and : List Fml → Fml
  | or : List Fml → Fml
  deriving Inhabited, Repr

mutual
/-- Truth value of a formula at `p`. -/
def Fml.eval (p : Params) : Fml → Bool
  | .atom l => decide (0 ≤ LF.eval l p)
  | .and fs => Fml.evalAll p fs
  | .or fs => Fml.evalAny p fs
def Fml.evalAll (p : Params) : List Fml → Bool
  | [] => true
  | f :: fs => Fml.eval p f && Fml.evalAll p fs
def Fml.evalAny (p : Params) : List Fml → Bool
  | [] => false
  | f :: fs => Fml.eval p f || Fml.evalAny p fs
end

/-! ## Cases, boxes, motions -/

inductive Kind where
  | diag
  | adj
  deriving DecidableEq, Repr, Inhabited

inductive Region where
  | fat
  | mid
  | thin
  deriving DecidableEq, Repr, Inhabited

/-- `(kind, o2, o3)`: one of the 128 orientation combinations. -/
structure Case where
  kind : Kind
  o2 : Fin 8
  o3 : Fin 8
  deriving DecidableEq, Repr, Inhabited

/-- Orientation index of slot `k`. -/
def Case.ori (c : Case) : Fin 4 → Fin 8
  | 0 => 0
  | 1 => 0
  | 2 => c.o2
  | 3 => c.o3

/-- A 2×2 integer matrix `((m00, m01), (m10, m11))`. -/
structure M2 where
  m00 : Int
  m01 : Int
  m10 : Int
  m11 : Int
  deriving DecidableEq, Repr, Inhabited

/-- The eight orientations. -/
def oriM : Fin 8 → M2
  | 0 => ⟨1, 0, 0, 1⟩
  | 1 => ⟨0, 1, -1, 0⟩
  | 2 => ⟨-1, 0, 0, -1⟩
  | 3 => ⟨0, -1, 1, 0⟩
  | 4 => ⟨0, 1, 1, 0⟩
  | 5 => ⟨-1, 0, 0, 1⟩
  | 6 => ⟨0, -1, -1, 0⟩
  | 7 => ⟨1, 0, 0, -1⟩

/-- A half-open box `[x0, x1) × [y0, y1)`. -/
structure Box where
  x0 : Int
  x1 : Int
  y0 : Int
  y1 : Int

def Box.mem (b : Box) (x y : Int) : Prop := b.x0 ≤ x ∧ x < b.x1 ∧ b.y0 ≤ y ∧ y < b.y1

/-- The corner box of slot `k`. -/
def box (kind : Kind) (p : Params) (k : Fin 4) : Box :=
  match kind, k with
  | .diag, 0 => ⟨0, p.v, 0, p.v⟩
  | .diag, 1 => ⟨0, p.u, p.a, p.w⟩
  | .diag, 2 => ⟨p.d, p.w, p.d, p.w⟩
  | .diag, 3 => ⟨p.a, p.w, 0, p.u⟩
  | .adj, 0 => ⟨0, p.v, 0, p.v⟩
  | .adj, 1 => ⟨p.a, p.w, p.a, p.w⟩
  | .adj, 2 => ⟨0, p.v, p.d, p.w⟩
  | .adj, 3 => ⟨p.a, p.w, 0, p.u⟩

/-- Source coordinates of cell `(x, y)` under slot `k`: `g_k(x, y) = M (x, y) + t_k`. -/
def srcX (c : Case) (p : Params) (k : Fin 4) (x y : Int) : Int :=
  (oriM (c.ori k)).m00 * x + (oriM (c.ori k)).m01 * y + p.tx k
def srcY (c : Case) (p : Params) (k : Fin 4) (x y : Int) : Int :=
  (oriM (c.ori k)).m10 * x + (oriM (c.ori k)).m11 * y + p.ty k

/-- Cell `(x, y)` lies in `W = [0, w)²`. -/
def InW (p : Params) (x y : Int) : Prop := 0 ≤ x ∧ x < p.w ∧ 0 ≤ y ∧ y < p.w

/-- Slot `k` is available at cell `(x, y)`: the cell is in the corner box of `k`, and its image
under `g_k` is in the target square of `k`. -/
def Avail (c : Case) (p : Params) (k : Fin 4) (x y : Int) : Prop :=
  (box c.kind p k).mem x y ∧
    0 ≤ srcX c p k x y ∧ srcX c p k x y < p.side k ∧ 0 ≤ srcY c p k x y ∧ srcY c p k x y < p.side k

/-- The other slot with the same target square. -/
def partner : Fin 4 → Fin 4
  | 0 => 2
  | 1 => 3
  | 2 => 0
  | 3 => 1

/-- **Normal form of a 2+2 dissection** for case `c` and parameters `p`. `σ x y` is the slot of
cell `(x, y)`. Every cell of `W` has its slot available; cells with the same target square have
different images (injective); every cell of each target square is hit (surjective). -/
structure NF (c : Case) (p : Params) where
  σ : Int → Int → Fin 4
  avail : ∀ x y, InW p x y → Avail c p (σ x y) x y
  inj : ∀ x y x' y', InW p x y → InW p x' y' → (σ x y).val % 2 = (σ x' y').val % 2 →
    srcX c p (σ x y) x y = srcX c p (σ x' y') x' y' →
    srcY c p (σ x y) x y = srcY c p (σ x' y') x' y' → x = x' ∧ y = y'
  surj : ∀ (k : Fin 4) (X Y : Int), 0 ≤ X → X < p.side k → 0 ≤ Y → Y < p.side k →
    ∃ x y, InW p x y ∧ (σ x y).val % 2 = k.val % 2 ∧
      srcX c p (σ x y) x y = X ∧ srcY c p (σ x y) x y = Y

/-! ## Regions (Lemma 0) -/

def RegionP : Region → Int → Int → Int → Prop
  | .fat, d, e, f => e < d ∧ d < f ∧ 2 * f ≤ 3 * d ∧ 2 * (f - d) + 1 ≤ d - e
  | .mid, d, e, f => 1 ≤ f ∧ f < d ∧ d < e ∧ 2 * (f - d) + 1 ≤ d - e ∧ 4 * e ≤ 11 * d
  | .thin, d, e, f => f ≤ -1 ∧ d < e ∧ 2 * d + 1 ≤ e + f ∧ 2 * (f - d) + 1 ≤ d - e

/-! ## Lemma data (one table = one region and case, with its lemmas) -/

/-- A vertex `q = M r + c` of a witness, as affine image of the root `r`, with its used slots. -/
structure Vert where
  m : M2
  cx : LF
  cy : LF
  used : List (Fin 4)
  deriving Repr, Inhabited

/-- An edge of an `over` certificate: source cell `g_k(q_p)`; its partner image is the vertex
`q` (`q ≥ 0`, slot `k2`) or lies outside `box (partner k)` (`q = -1`). -/
structure OEdge where
  p : Nat
  k : Fin 4
  q : Int
  k2 : Fin 4
  deriving Repr, Inhabited

inductive LemmaData where
  /-- Shape lemma: tree witness; the root ranges over the representative terms `xs × ys`. -/
  | shape (verts : List Vert) (xs ys : List LF)
  /-- `tpl` tree certificate: conditions rebuilt at `vals`, root `(rx, ry)`. -/
  | tplTree (verts : List Vert) (vals : List Int) (rx ry : Int)
  /-- `tpl` over certificate; `verts` ignore `used`. -/
  | tplOver (verts : List Vert) (edges : List OEdge) (vals : List Int) (rx ry : Int)
  deriving Repr, Inhabited

structure Table where
  region : Region
  case : Case
  lemmas : List LemmaData
  deriving Repr, Inhabited

end Ex89.T22
