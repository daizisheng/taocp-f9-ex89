import Ex89.T22.Defs
import Ex89.T22.Count
/-!
# Formula builders and their soundness

`tableF t` is the formula whose unsatisfiability the residual certificates prove. Every part is
built here from the lemma data, and `tableF_true` shows that it holds at the parameters of any
normal form `NF t.case p` in the region of `t`.

* `regionF`, `domainF` (two-rectangle covering), `cover81F` (every cell of `W` has a slot).
* `lemmaF c L` for the three kinds of lemma data; `lemmaF_false`: an `NF` makes it false.
  - `shape`: closed structure, static closure check `closedOK`, root ranges over `xs × ys`
    (`rootF`, factored by coordinate, constant atoms simplified); contradiction by `G1`.
  - `tplTree`: same structure, condition system `treeSys` (unused slots: first condition violated
    at the certificate point, negated), root eliminated by `elim` (`G3`), then `G1`.
  - `tplOver`: system `overSys` (sources in their squares, partner identities / half edges,
    pairwise separation of same-square sources), `elim`, then pigeonhole `G2`.
-/
namespace Ex89.T22

/-! ## Formulas: evaluation lemmas and negation -/

theorem Fml.evalAll_iff (p : Params) : ∀ fs : List Fml,
    Fml.evalAll p fs = true ↔ ∀ f ∈ fs, f.eval p = true
  | [] => by simp [Fml.evalAll]
  | f :: fs => by simp [Fml.evalAll, Fml.evalAll_iff p fs]

theorem Fml.evalAny_iff (p : Params) : ∀ fs : List Fml,
    Fml.evalAny p fs = true ↔ ∃ f ∈ fs, f.eval p = true
  | [] => by simp [Fml.evalAny]
  | f :: fs => by simp [Fml.evalAny, Fml.evalAny_iff p fs]

theorem Fml.eval_atom (l : LF) (p : Params) : (Fml.atom l).eval p = decide (0 ≤ l.eval p) := by
  simp [Fml.eval]

theorem Fml.eval_and (fs : List Fml) (p : Params) :
    (Fml.and fs).eval p = true ↔ ∀ f ∈ fs, f.eval p = true := by
  simp only [Fml.eval]; exact Fml.evalAll_iff p fs

theorem Fml.eval_or (fs : List Fml) (p : Params) :
    (Fml.or fs).eval p = true ↔ ∃ f ∈ fs, f.eval p = true := by
  simp only [Fml.eval]; exact Fml.evalAny_iff p fs

mutual
/-- Negation normal form negation. -/
def Fml.neg : Fml → Fml
  | .atom l => .atom (LF.addc (LF.neg l) (-1))
  | .and fs => .or (Fml.negL fs)
  | .or fs => .and (Fml.negL fs)
def Fml.negL : List Fml → List Fml
  | [] => []
  | f :: fs => Fml.neg f :: Fml.negL fs
end

mutual
theorem Fml.eval_neg : ∀ (φ : Fml) (p : Params), (Fml.neg φ).eval p = !(φ.eval p)
  | .atom l, p => by
    simp only [Fml.neg, Fml.eval, LF.eval_addc, LF.eval_neg]
    by_cases h : 0 ≤ l.eval p
    · simp [h]; omega
    · simp [h]; omega
  | .and fs, p => by
    simp only [Fml.neg, Fml.eval]; exact Fml.evalAny_negL fs p
  | .or fs, p => by
    simp only [Fml.neg, Fml.eval]; exact Fml.evalAll_negL fs p
theorem Fml.evalAny_negL : ∀ (fs : List Fml) (p : Params),
    Fml.evalAny p (Fml.negL fs) = !(Fml.evalAll p fs)
  | [], p => by simp [Fml.negL, Fml.evalAny, Fml.evalAll]
  | f :: fs, p => by
    simp only [Fml.negL, Fml.evalAny, Fml.evalAll, Fml.eval_neg f p, Fml.evalAny_negL fs p,
      Bool.not_and]
theorem Fml.evalAll_negL : ∀ (fs : List Fml) (p : Params),
    Fml.evalAll p (Fml.negL fs) = !(Fml.evalAny p fs)
  | [], p => by simp [Fml.negL, Fml.evalAny, Fml.evalAll]
  | f :: fs, p => by
    simp only [Fml.negL, Fml.evalAny, Fml.evalAll, Fml.eval_neg f p, Fml.evalAll_negL fs p,
      Bool.not_or]
end

/-- The constant false formula. -/
def Fml.ff : Fml := .or []

theorem Fml.eval_ff (p : Params) : Fml.ff.eval p = false := by simp [Fml.ff, Fml.eval, Fml.evalAny]

/-! ## Linear forms: normalisation, constants -/

/-- Pad to length 12 (forms of length `≤ 12` become exactly 12 long). -/
def LF.norm (l : LF) : LF := LF.add (List.replicate 12 0) l

theorem LF.eval_norm (l : LF) (p : Params) : (LF.norm l).eval p = l.eval p := by
  have h0 : LF.eval (List.replicate 12 0) p = 0 := by
    unfold LF.eval; rw [← List.append_nil (List.replicate 12 0), LF.evalFrom_replicate]; rfl
  rw [LF.norm, LF.eval_add, h0, Int.zero_add]

/-- An atom with a padded form. -/
def mkA (l : LF) : Fml := .atom (LF.norm l)

theorem eval_mkA (l : LF) (p : Params) : (mkA l).eval p = decide (0 ≤ l.eval p) := by
  simp [mkA, Fml.eval, LF.eval_norm]

/-- `some c` if the form is syntactically the constant `c`. -/
def LF.cvalFrom : List Int → Nat → Option Int
  | [], _ => some 0
  | c :: l, i =>
    if i < 11 then (if c == 0 then LF.cvalFrom l (i + 1) else none)
    else if i = 11 then (LF.cvalFrom l (i + 1)).map (c + ·)
    else LF.cvalFrom l (i + 1)

theorem LF.cvalFrom_sound (p : Params) : ∀ (l : List Int) (i : Nat) (v : Int),
    LF.cvalFrom l i = some v → LF.evalFrom p l i = v
  | [], _, v, h => by simp [LF.cvalFrom] at h; simp [LF.evalFrom, h]
  | c :: l, i, v, h => by
    simp only [LF.cvalFrom] at h
    simp only [LF.evalFrom]
    by_cases hi : i < 11
    · rw [if_pos hi] at h
      by_cases hc : c = 0
      · subst hc; simp at h; simp [LF.cvalFrom_sound p l (i + 1) v h]
      · simp [hc] at h
    · rw [if_neg hi] at h
      by_cases hi' : i = 11
      · rw [if_pos hi'] at h
        obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.1 h
        rw [LF.cvalFrom_sound p l (i + 1) w hw]
        simp [Params.val, hi']
      · rw [if_neg hi'] at h
        rw [LF.cvalFrom_sound p l (i + 1) v h]
        have : p.val i = 0 := by simp [Params.val, hi, hi']
        simp [this]

def LF.cval (l : LF) : Option Int := LF.cvalFrom l 0

theorem LF.cval_sound {l : LF} {v : Int} (h : l.cval = some v) (p : Params) : l.eval p = v :=
  LF.cvalFrom_sound p l 0 v h

/-- Constant-true atom. -/
def LF.isTrue (l : LF) : Bool := match l.cval with | some v => decide (0 ≤ v) | none => false
/-- Constant-false atom. -/
def LF.isFalse (l : LF) : Bool := match l.cval with | some v => decide (v < 0) | none => false

theorem LF.isTrue_sound {l : LF} (h : l.isTrue = true) (p : Params) : 0 ≤ l.eval p := by
  unfold LF.isTrue at h
  split at h
  · rename_i v hv; rw [LF.cval_sound hv]; simpa using h
  · exact absurd h (by simp)

theorem LF.isFalse_sound {l : LF} (h : l.isFalse = true) (p : Params) : l.eval p < 0 := by
  unfold LF.isFalse at h
  split at h
  · rename_i v hv; rw [LF.cval_sound hv]; simpa using h
  · exact absurd h (by simp)

/-- Conjunction of atoms: `none` if some atom is constant-false; constant-true atoms dropped. -/
def simpAtoms (ls : List LF) : Option (List LF) :=
  if ls.any LF.isFalse then none else some (ls.filter (fun l => !l.isTrue))

theorem simpAtoms_sound {ls out : List LF} (h : simpAtoms ls = some out) (p : Params)
    (hout : ∀ l ∈ out, 0 ≤ l.eval p) : ∀ l ∈ ls, 0 ≤ l.eval p := by
  unfold simpAtoms at h
  split at h
  · exact absurd h (by simp)
  · intro l hl
    by_cases ht : l.isTrue = true
    · exact LF.isTrue_sound ht p
    · apply hout; rw [← Option.some.inj h]; simp [hl, ht]

/-- A disjunctive clause part: `none` if some atom is constant-true (the clause holds);
otherwise the atoms that are not constant-false. -/
def simpClause (ls : List LF) : Option (List LF) :=
  if ls.any LF.isTrue then none else some (ls.filter (fun l => !l.isFalse))

theorem simpClause_none {ls : List LF} (h : simpClause ls = none) (p : Params) :
    ∃ l ∈ ls, 0 ≤ l.eval p := by
  unfold simpClause at h
  split at h
  · rename_i ha
    obtain ⟨l, hl, ht⟩ := List.any_eq_true.1 ha
    exact ⟨l, hl, LF.isTrue_sound ht p⟩
  · exact absurd h (by simp)

theorem simpClause_some {ls out : List LF} (h : simpClause ls = some out) :
    ∀ l ∈ out, l ∈ ls := by
  unfold simpClause at h
  split at h
  · exact absurd h (by simp)
  · rw [← Option.some.inj h]; intro l hl; exact (List.mem_filter.1 hl).1

/-! ## Constraints in the root -/

/-- Value `co·r + l` of a constraint. -/
theorem Cn.holds_iff (p : Params) (rx ry : Int) (cn : Cn) :
    cn.holds p rx ry ↔ 0 ≤ cn.1.1 * rx + cn.1.2 * ry + cn.2.eval p := Iff.rfl

/-- Negation: `co·r + l ≥ 0` fails iff `-co·r - l - 1 ≥ 0`. -/
def Cn.neg (cn : Cn) : Cn := ((-cn.1.1, -cn.1.2), LF.addc (LF.neg cn.2) (-1))

theorem Cn.holds_neg (p : Params) (rx ry : Int) (cn : Cn) :
    (Cn.neg cn).holds p rx ry ↔ ¬ cn.holds p rx ry := by
  simp only [Cn.neg, Cn.holds, LF.eval_addc, LF.eval_neg, Int.neg_mul]; omega

/-- Substitute linear forms for the root. -/
def Cn.subst (px py : LF) (cn : Cn) : LF :=
  LF.add (LF.add (LF.smul cn.1.1 px) (LF.smul cn.1.2 py)) cn.2
def Cn.substX (px : LF) (cn : Cn) : LF := LF.add (LF.smul cn.1.1 px) cn.2
def Cn.substY (py : LF) (cn : Cn) : LF := LF.add (LF.smul cn.1.2 py) cn.2

theorem Cn.subst_eval (px py : LF) (cn : Cn) (p : Params) :
    (cn.subst px py).eval p = cn.1.1 * px.eval p + cn.1.2 * py.eval p + cn.2.eval p := by
  simp [Cn.subst, LF.eval_add, LF.eval_smul]

/-- `x`-only (or constant), `y`-only, mixed. -/
def Cn.isX (cn : Cn) : Bool := cn.1.2 == 0
def Cn.isY (cn : Cn) : Bool := cn.1.1 == 0 && cn.1.2 != 0

theorem Cn.substX_eval (px : LF) (cn : Cn) (h : cn.isX = true) (p : Params) (ry : Int) :
    0 ≤ (cn.substX px).eval p ↔ cn.holds p (px.eval p) ry := by
  simp [Cn.isX] at h
  simp [Cn.substX, Cn.holds, LF.eval_add, LF.eval_smul, h]

theorem Cn.substY_eval (py : LF) (cn : Cn) (h : cn.isY = true) (p : Params) (rx : Int) :
    0 ≤ (cn.substY py).eval p ↔ cn.holds p rx (py.eval p) := by
  simp [Cn.isY] at h
  simp [Cn.substY, Cn.holds, LF.eval_add, LF.eval_smul, h.1]

/-- Constraint with padded form. -/
def mkC (co : Int × Int) (l : LF) : Cn := (co, LF.norm l)

theorem mkC_holds (p : Params) (rx ry : Int) (co : Int × Int) (l : LF) :
    (mkC co l).holds p rx ry ↔ 0 ≤ co.1 * rx + co.2 * ry + l.eval p := by
  simp [mkC, Cn.holds, LF.eval_norm]

/-! ## Boxes, slot conditions -/

structure BoxLF where
  x0 : LF
  x1 : LF
  y0 : LF
  y1 : LF

def LF.zero : LF := LF.const 0

theorem LF.eval_zero (p : Params) : LF.zero.eval p = 0 := LF.eval_const 0 p

/-- `box` as linear forms. -/
def boxLF : Kind → Fin 4 → BoxLF
  | .diag, 0 => ⟨LF.zero, LF.v, LF.zero, LF.v⟩
  | .diag, 1 => ⟨LF.zero, LF.u, LF.a, LF.w⟩
  | .diag, 2 => ⟨LF.d, LF.w, LF.d, LF.w⟩
  | .diag, 3 => ⟨LF.a, LF.w, LF.zero, LF.u⟩
  | .adj, 0 => ⟨LF.zero, LF.v, LF.zero, LF.v⟩
  | .adj, 1 => ⟨LF.a, LF.w, LF.a, LF.w⟩
  | .adj, 2 => ⟨LF.zero, LF.v, LF.d, LF.w⟩
  | .adj, 3 => ⟨LF.a, LF.w, LF.zero, LF.u⟩

theorem boxLF_eval (kind : Kind) (p : Params) (k : Fin 4) :
    (boxLF kind k).x0.eval p = (box kind p k).x0 ∧ (boxLF kind k).x1.eval p = (box kind p k).x1 ∧
    (boxLF kind k).y0.eval p = (box kind p k).y0 ∧ (boxLF kind k).y1.eval p = (box kind p k).y1 := by
  cases kind <;> revert k <;> apply Fin4.cases <;>
    simp [boxLF, box, LF.eval_zero, LF.eval_u, LF.eval_v, LF.eval_w, LF.eval_a, LF.eval_d]

/-- `q = M r + c` in `W` (the four conditions). -/
def condsW (M : M2) (cx cy : LF) : List Cn :=
  [mkC (M.m00, M.m01) cx, mkC (M.m10, M.m11) cy,
   mkC (-M.m00, -M.m01) (LF.addc (LF.sub LF.w cx) (-1)),
   mkC (-M.m10, -M.m11) (LF.addc (LF.sub LF.w cy) (-1))]

theorem condsW_iff (p : Params) (rx ry : Int) (M : M2) (cx cy : LF) :
    (∀ cn ∈ condsW M cx cy, cn.holds p rx ry) ↔
      InW p (M.m00 * rx + M.m01 * ry + cx.eval p) (M.m10 * rx + M.m11 * ry + cy.eval p) := by
  simp only [condsW, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, mkC_holds, LF.eval_addc,
    LF.eval_sub, LF.eval_w, InW, Int.neg_mul, and_true]
  omega

/-- `q = M r + c` in the box of slot `k` (four conditions). -/
def boxConds (c : Case) (M : M2) (cx cy : LF) (k : Fin 4) : List Cn :=
  let b := boxLF c.kind k
  [mkC (M.m00, M.m01) (LF.sub cx b.x0), mkC (-M.m00, -M.m01) (LF.addc (LF.sub b.x1 cx) (-1)),
   mkC (M.m10, M.m11) (LF.sub cy b.y0), mkC (-M.m10, -M.m11) (LF.addc (LF.sub b.y1 cy) (-1))]

/-- The image of `q = M r + c` under slot `k` lies in the target square (four conditions). -/
def srcConds (c : Case) (M : M2) (cx cy : LF) (k : Fin 4) : List Cn :=
  let G := oriM (c.ori k)
  let coX : Int × Int := (G.m00 * M.m00 + G.m01 * M.m10, G.m00 * M.m01 + G.m01 * M.m11)
  let coY : Int × Int := (G.m10 * M.m00 + G.m11 * M.m10, G.m10 * M.m01 + G.m11 * M.m11)
  let lX := LF.add (LF.add (LF.tx k) (LF.smul G.m00 cx)) (LF.smul G.m01 cy)
  let lY := LF.add (LF.add (LF.ty k) (LF.smul G.m10 cx)) (LF.smul G.m11 cy)
  [mkC coX lX, mkC (-coX.1, -coX.2) (LF.addc (LF.sub (LF.side k) lX) (-1)),
   mkC coY lY, mkC (-coY.1, -coY.2) (LF.addc (LF.sub (LF.side k) lY) (-1))]

/-- Slot `k` available at `q = M r + c` (eight conditions). -/
def slotConds (c : Case) (M : M2) (cx cy : LF) (k : Fin 4) : List Cn :=
  boxConds c M cx cy k ++ srcConds c M cx cy k

theorem boxConds_iff (c : Case) (p : Params) (rx ry : Int) (M : M2) (cx cy : LF) (k : Fin 4) :
    (∀ cn ∈ boxConds c M cx cy k, cn.holds p rx ry) ↔
      (box c.kind p k).mem (M.m00 * rx + M.m01 * ry + cx.eval p)
        (M.m10 * rx + M.m11 * ry + cy.eval p) := by
  obtain ⟨h1, h2, h3, h4⟩ := boxLF_eval c.kind p k
  simp only [boxConds, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, mkC_holds, LF.eval_addc,
    LF.eval_sub, h1, h2, h3, h4, Box.mem, Int.neg_mul, and_true]
  omega

theorem lin_aux (g0 g1 m00 m01 m10 m11 rx ry a b t : Int) :
    (g0 * m00 + g1 * m10) * rx + (g0 * m01 + g1 * m11) * ry + (t + g0 * a + g1 * b) =
      g0 * (m00 * rx + m01 * ry + a) + g1 * (m10 * rx + m11 * ry + b) + t := by
  grind

theorem srcConds_iff (c : Case) (p : Params) (rx ry : Int) (M : M2) (cx cy : LF) (k : Fin 4) :
    (∀ cn ∈ srcConds c M cx cy k, cn.holds p rx ry) ↔
      (0 ≤ srcX c p k (M.m00 * rx + M.m01 * ry + cx.eval p) (M.m10 * rx + M.m11 * ry + cy.eval p) ∧
       srcX c p k (M.m00 * rx + M.m01 * ry + cx.eval p) (M.m10 * rx + M.m11 * ry + cy.eval p)
         < p.side k ∧
       0 ≤ srcY c p k (M.m00 * rx + M.m01 * ry + cx.eval p) (M.m10 * rx + M.m11 * ry + cy.eval p) ∧
       srcY c p k (M.m00 * rx + M.m01 * ry + cx.eval p) (M.m10 * rx + M.m11 * ry + cy.eval p)
         < p.side k) := by
  have key : ∀ (g0 g1 : Int) (t : LF), (g0 * M.m00 + g1 * M.m10) * rx +
      (g0 * M.m01 + g1 * M.m11) * ry + (LF.add (LF.add t (LF.smul g0 cx)) (LF.smul g1 cy)).eval p =
      g0 * (M.m00 * rx + M.m01 * ry + cx.eval p) + g1 * (M.m10 * rx + M.m11 * ry + cy.eval p) +
        t.eval p := by
    intro g0 g1 t; simp only [LF.eval_add, LF.eval_smul]; grind
  have keyn : ∀ (g0 g1 : Int) (t : LF), (-(g0 * M.m00 + g1 * M.m10)) * rx +
      (-(g0 * M.m01 + g1 * M.m11)) * ry +
      (LF.addc (LF.sub (LF.side k) (LF.add (LF.add t (LF.smul g0 cx)) (LF.smul g1 cy))) (-1)).eval p =
      p.side k - (g0 * (M.m00 * rx + M.m01 * ry + cx.eval p) +
        g1 * (M.m10 * rx + M.m11 * ry + cy.eval p) + t.eval p) - 1 := by
    intro g0 g1 t; simp only [LF.eval_add, LF.eval_smul, LF.eval_addc, LF.eval_sub, LF.eval_side]
    grind
  simp only [srcConds, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
    and_true, mkC_holds]
  rw [key, keyn, key, keyn]
  unfold srcX srcY
  simp only [LF.eval_tx, LF.eval_ty]
  omega

theorem slotConds_iff (c : Case) (p : Params) (rx ry : Int) (M : M2) (cx cy : LF) (k : Fin 4) :
    (∀ cn ∈ slotConds c M cx cy k, cn.holds p rx ry) ↔
      Avail c p k (M.m00 * rx + M.m01 * ry + cx.eval p) (M.m10 * rx + M.m11 * ry + cy.eval p) := by
  unfold slotConds Avail
  rw [← boxConds_iff, ← srcConds_iff]
  simp only [List.mem_append]
  constructor
  · intro h; exact ⟨fun cn hc => h cn (Or.inl hc), fun cn hc => h cn (Or.inr hc)⟩
  · rintro ⟨h1, h2⟩ cn (hc | hc)
    · exact h1 cn hc
    · exact h2 cn hc

/-! ## Vertices and the partner map -/

def Vert.qx (v : Vert) (p : Params) (rx ry : Int) : Int := v.m.m00 * rx + v.m.m01 * ry + v.cx.eval p
def Vert.qy (v : Vert) (p : Params) (rx ry : Int) : Int := v.m.m10 * rx + v.m.m11 * ry + v.cy.eval p

/-- `q' = g_{k'}⁻¹ (g_k q)` for `q = M r + c`, as `(M', c'x, c'y)`. -/
def composeV (c : Case) (M : M2) (cx cy : LF) (k k' : Fin 4) : M2 × LF × LF :=
  let A := oriM (c.ori k)
  let B := oriM (c.ori k')
  let a00 := A.m00 * M.m00 + A.m01 * M.m10
  let a01 := A.m00 * M.m01 + A.m01 * M.m11
  let a10 := A.m10 * M.m00 + A.m11 * M.m10
  let a11 := A.m10 * M.m01 + A.m11 * M.m11
  let R : M2 := ⟨B.m00 * a00 + B.m10 * a10, B.m00 * a01 + B.m10 * a11,
    B.m01 * a00 + B.m11 * a10, B.m01 * a01 + B.m11 * a11⟩
  let dx := LF.sub (LF.add (LF.add (LF.tx k) (LF.smul A.m00 cx)) (LF.smul A.m01 cy)) (LF.tx k')
  let dy := LF.sub (LF.add (LF.add (LF.ty k) (LF.smul A.m10 cx)) (LF.smul A.m11 cy)) (LF.ty k')
  (R, LF.norm (LF.add (LF.smul B.m00 dx) (LF.smul B.m10 dy)),
    LF.norm (LF.add (LF.smul B.m01 dx) (LF.smul B.m11 dy)))

theorem composeV_src (c : Case) (p : Params) (M : M2) (cx cy : LF) (k k' : Fin 4) (rx ry : Int) :
    srcX c p k' ((composeV c M cx cy k k').1.m00 * rx + (composeV c M cx cy k k').1.m01 * ry +
        (composeV c M cx cy k k').2.1.eval p)
      ((composeV c M cx cy k k').1.m10 * rx + (composeV c M cx cy k k').1.m11 * ry +
        (composeV c M cx cy k k').2.2.eval p) =
      srcX c p k (M.m00 * rx + M.m01 * ry + cx.eval p) (M.m10 * rx + M.m11 * ry + cy.eval p) ∧
    srcY c p k' ((composeV c M cx cy k k').1.m00 * rx + (composeV c M cx cy k k').1.m01 * ry +
        (composeV c M cx cy k k').2.1.eval p)
      ((composeV c M cx cy k k').1.m10 * rx + (composeV c M cx cy k k').1.m11 * ry +
        (composeV c M cx cy k k').2.2.eval p) =
      srcY c p k (M.m00 * rx + M.m01 * ry + cx.eval p) (M.m10 * rx + M.m11 * ry + cy.eval p) := by
  simp only [composeV, LF.eval_norm, LF.eval_add, LF.eval_smul, LF.eval_sub, LF.eval_tx,
    LF.eval_ty]
  unfold srcX srcY
  generalize oriM (c.ori k) = A
  generalize c.ori k' = o
  revert o
  apply Fin8.cases <;> simp only [oriM] <;> constructor <;> grind

/-- Key of a vertex (for the static closure check). -/
def Vert.key (v : Vert) : M2 × LF × LF := (v.m, LF.norm v.cx, LF.norm v.cy)

def usedB (verts : List Vert) (i : Nat) (k : Fin 4) : Bool := decide (k ∈ (verts.getD i default).used)

/-- For every dart `(i, k)` with `k < 2`, the edge to the vertex `j` (first match) whose affine
data is `g_{partner k}⁻¹ g_k q_i`; `j = verts.length` if there is none. -/
def treeEdges (c : Case) (verts : List Vert) : List ((Nat × Fin 4) × (Nat × Fin 4)) :=
  (List.range verts.length).flatMap (fun i =>
    let v := verts.getD i default
    (allK.filter (fun k => decide (k.val < 2) && decide (k ∈ v.used))).map (fun k =>
      ((i, k), (verts.findIdx (fun w => decide (w.key = composeV c v.m v.cx v.cy k (partner k))),
        partner k))))

/-- Static closure check: the edges pair off all darts, and
`V ≠ E`. -/
def closedOK (c : Case) (verts : List Vert) : Bool :=
  (darts verts.length (usedB verts)).isPerm ((treeEdges c verts).flatMap (fun e => [e.1, e.2])) &&
    (treeEdges c verts).length != verts.length

theorem getD_mem {α : Type} [Inhabited α] {l : List α} {i : Nat} (h : i < l.length) :
    l.getD i default = l[i] := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

/-- A closed structure with `V ≠ E` realised at a root contradicts `NF` (by `G1`). -/
theorem closed_false (c : Case) (p : Params) (N : NF c p) (verts : List Vert)
    (hc : closedOK c verts = true) (rx ry : Int)
    (hv : ∀ v ∈ verts, InW p (v.qx p rx ry) (v.qy p rx ry) ∧
      ∀ k, Avail c p k (v.qx p rx ry) (v.qy p rx ry) ↔ k ∈ v.used) : False := by
  simp only [closedOK, Bool.and_eq_true, List.isPerm_iff, bne_iff_ne, ne_eq] at hc
  obtain ⟨hP, hne⟩ := hc
  apply hne
  apply G1 c p N verts.length (fun i => (verts.getD i default).qx p rx ry)
    (fun i => (verts.getD i default).qy p rx ry) (usedB verts) (treeEdges c verts)
  · intro i hi; rw [getD_mem hi]; exact (hv _ (List.getElem_mem hi)).1
  · intro i hi k; rw [usedB, getD_mem hi, decide_eq_true_iff]
    exact (hv _ (List.getElem_mem hi)).2 k
  · intro e he
    have he2 : e.2 ∈ darts verts.length (usedB verts) :=
      hP.mem_iff.2 (List.mem_flatMap.2 ⟨e, he, by simp⟩)
    simp only [treeEdges, List.mem_flatMap, List.mem_range, List.mem_map, List.mem_filter] at he
    obtain ⟨i, hi, k, _, rfl⟩ := he
    rw [mem_darts] at he2
    simp only at he2 ⊢
    refine ⟨trivial, ?_⟩
    have hj := he2.1
    have hkey := List.findIdx_getElem (w := hj)
    simp only [decide_eq_true_eq] at hkey
    rw [getD_mem hj]
    generalize hJ : verts[verts.findIdx _] = vj at hkey
    simp only [Vert.key] at hkey
    have hm := congrArg Prod.fst hkey
    have hx := congrArg (fun z => z.2.1) hkey
    have hy := congrArg (fun z => z.2.2) hkey
    simp only at hm hx hy
    have ex : vj.cx.eval p = (composeV c (verts.getD i default).m (verts.getD i default).cx
        (verts.getD i default).cy k (partner k)).2.1.eval p := by rw [← LF.eval_norm vj.cx, hx]
    have ey : vj.cy.eval p = (composeV c (verts.getD i default).m (verts.getD i default).cx
        (verts.getD i default).cy k (partner k)).2.2.eval p := by rw [← LF.eval_norm vj.cy, hy]
    have := composeV_src c p (verts.getD i default).m (verts.getD i default).cx
      (verts.getD i default).cy k (partner k) rx ry
    simp only [Vert.qx, Vert.qy, hm, ex, ey]
    exact ⟨this.1.symm, this.2.symm⟩
  · exact hP

/-! ## Vertex condition systems -/

def vPos (c : Case) (v : Vert) : List Cn :=
  condsW v.m v.cx v.cy ++
    (allK.filter (fun k => decide (k ∈ v.used))).flatMap (slotConds c v.m v.cx v.cy)

def vCls (c : Case) (v : Vert) : List (List Cn) :=
  (allK.filter (fun k => !decide (k ∈ v.used))).map (fun k => (slotConds c v.m v.cx v.cy k).map Cn.neg)

theorem vert_facts (c : Case) (p : Params) (rx ry : Int) (v : Vert)
    (h1 : ∀ cn ∈ vPos c v, cn.holds p rx ry) (h2 : ∀ g ∈ vCls c v, ∃ cn ∈ g, cn.holds p rx ry) :
    InW p (v.qx p rx ry) (v.qy p rx ry) ∧
      ∀ k, Avail c p k (v.qx p rx ry) (v.qy p rx ry) ↔ k ∈ v.used := by
  constructor
  · exact (condsW_iff p rx ry v.m v.cx v.cy).1 (fun cn hcn => h1 cn (List.mem_append_left _ hcn))
  · intro k
    constructor
    · intro hav
      refine Classical.byContradiction fun hk => ?_
      obtain ⟨cn, hcn, hh⟩ := h2 _ (List.mem_map.2 ⟨k, List.mem_filter.2 ⟨mem_allK k, by simpa using hk⟩, rfl⟩)
      obtain ⟨cn', hcn', rfl⟩ := List.mem_map.1 hcn
      exact (Cn.holds_neg p rx ry cn').1 hh ((slotConds_iff c p rx ry v.m v.cx v.cy k).2 hav cn' hcn')
    · intro hk
      apply (slotConds_iff c p rx ry v.m v.cx v.cy k).1
      intro cn hcn
      apply h1
      exact List.mem_append_right _ (List.mem_flatMap.2 ⟨k, List.mem_filter.2 ⟨mem_allK k, by simpa using hk⟩, hcn⟩)

/-! ## Root ranging over representative terms (shape lemmas) -/

def Cn.isM (cn : Cn) : Bool := !cn.isX && !cn.isY

def clX (px : LF) (g : List Cn) : Option (List Fml) :=
  (simpClause ((g.filter Cn.isX).map (Cn.substX px))).map (List.map mkA)
def clY (py : LF) (g : List Cn) : Option (List Fml) :=
  (simpClause ((g.filter Cn.isY).map (Cn.substY py))).map (List.map mkA)
def clM (px py : LF) (g : List Cn) : List Fml := (g.filter Cn.isM).map (fun cn => mkA (cn.subst px py))

/-- The clauses at `(px, py)` from their precomputed `x`- and `y`-parts; `none` if some clause is
constant-false. -/
def combine (px py : LF) : List (List Cn) → List (Option (List Fml)) → List (Option (List Fml)) →
    Option (List Fml)
  | g :: gs, a :: as, b :: bs =>
    match a, b with
    | some fa, some fb =>
      if fa.isEmpty && fb.isEmpty && (clM px py g).isEmpty then none
      else (combine px py gs as bs).map (fun r => Fml.or [Fml.or fa, Fml.or fb, Fml.or (clM px py g)] :: r)
    | _, _ => combine px py gs as bs
  | _, _, _ => some []

theorem cl_atoms_mkA {ls : List LF} {p : Params} (h : ∃ f ∈ ls.map mkA, f.eval p = true) :
    ∃ l ∈ ls, 0 ≤ l.eval p := by
  obtain ⟨f, hf, he⟩ := h
  obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hf
  exact ⟨l, hl, by simpa [eval_mkA] using he⟩

theorem clX_sound (px : LF) (g : List Cn) (p : Params) (ry : Int) :
    (clX px g = none → ∃ cn ∈ g, cn.holds p (px.eval p) ry) ∧
    (∀ fa, clX px g = some fa → (∃ f ∈ fa, f.eval p = true) → ∃ cn ∈ g, cn.holds p (px.eval p) ry) := by
  have conv : ∀ l ∈ (g.filter Cn.isX).map (Cn.substX px), 0 ≤ l.eval p →
      ∃ cn ∈ g, cn.holds p (px.eval p) ry := by
    intro l hl h0
    obtain ⟨cn, hcn, rfl⟩ := List.mem_map.1 hl
    obtain ⟨hcn, hx⟩ := List.mem_filter.1 hcn
    exact ⟨cn, hcn, (Cn.substX_eval px cn hx p ry).1 h0⟩
  constructor
  · intro h
    simp only [clX, Option.map_eq_none_iff] at h
    obtain ⟨l, hl, h0⟩ := simpClause_none h p
    exact conv l hl h0
  · intro fa h hf
    simp only [clX, Option.map_eq_some_iff] at h
    obtain ⟨ls, hls, rfl⟩ := h
    obtain ⟨l, hl, h0⟩ := cl_atoms_mkA hf
    exact conv l (simpClause_some hls l hl) h0

theorem clY_sound (py : LF) (g : List Cn) (p : Params) (rx : Int) :
    (clY py g = none → ∃ cn ∈ g, cn.holds p rx (py.eval p)) ∧
    (∀ fb, clY py g = some fb → (∃ f ∈ fb, f.eval p = true) → ∃ cn ∈ g, cn.holds p rx (py.eval p)) := by
  have conv : ∀ l ∈ (g.filter Cn.isY).map (Cn.substY py), 0 ≤ l.eval p →
      ∃ cn ∈ g, cn.holds p rx (py.eval p) := by
    intro l hl h0
    obtain ⟨cn, hcn, rfl⟩ := List.mem_map.1 hl
    obtain ⟨hcn, hy⟩ := List.mem_filter.1 hcn
    exact ⟨cn, hcn, (Cn.substY_eval py cn hy p rx).1 h0⟩
  constructor
  · intro h
    simp only [clY, Option.map_eq_none_iff] at h
    obtain ⟨l, hl, h0⟩ := simpClause_none h p
    exact conv l hl h0
  · intro fb h hf
    simp only [clY, Option.map_eq_some_iff] at h
    obtain ⟨ls, hls, rfl⟩ := h
    obtain ⟨l, hl, h0⟩ := cl_atoms_mkA hf
    exact conv l (simpClause_some hls l hl) h0

theorem clM_sound (px py : LF) (g : List Cn) (p : Params) (h : ∃ f ∈ clM px py g, f.eval p = true) :
    ∃ cn ∈ g, cn.holds p (px.eval p) (py.eval p) := by
  obtain ⟨f, hf, he⟩ := h
  obtain ⟨cn, hcn, rfl⟩ := List.mem_map.1 hf
  refine ⟨cn, (List.mem_filter.1 hcn).1, ?_⟩
  rw [eval_mkA, decide_eq_true_eq, Cn.subst_eval] at he
  exact he

theorem combine_sound (px py : LF) (p : Params) : ∀ (cls : List (List Cn)) (fs : List Fml),
    combine px py cls (cls.map (clX px)) (cls.map (clY py)) = some fs →
    (∀ f ∈ fs, f.eval p = true) → ∀ g ∈ cls, ∃ cn ∈ g, cn.holds p (px.eval p) (py.eval p)
  | [], _, _, _ => by simp
  | g :: gs, fs, h, hfs => by
    simp only [List.map_cons, combine] at h
    have ih := combine_sound px py p gs
    intro g' hg'
    rcases List.mem_cons.1 hg' with rfl | hg'
    · split at h
      · rename_i fa fb ha hb
        split at h
        · exact absurd h (by simp)
        · obtain ⟨r, _, rfl⟩ := Option.map_eq_some_iff.1 h
          have := hfs _ List.mem_cons_self
          simp only [Fml.eval_or, List.mem_cons, List.not_mem_nil, or_false] at this
          obtain ⟨f, hf, hfe⟩ := this
          rcases hf with rfl | rfl | rfl
          · exact (clX_sound px g' p _).2 fa ha ((Fml.eval_or _ _).1 hfe)
          · exact (clY_sound py g' p _).2 fb hb ((Fml.eval_or _ _).1 hfe)
          · exact clM_sound px py g' p ((Fml.eval_or _ _).1 hfe)
      · rename_i hn
        cases ha : clX px g' with
        | none => exact (clX_sound px g' p _).1 ha
        | some fa =>
          cases hb : clY py g' with
          | none => exact (clY_sound py g' p _).1 hb
          | some fb => exact (hn fa fb ha hb).elim
    · split at h
      · split at h
        · exact absurd h (by simp)
        · obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.1 h
          exact ih r hr (fun f hf => hfs f (List.mem_cons_of_mem _ hf)) g' hg'
      · exact ih fs h hfs g' hg'

/-- The root `r = (px, py)` ranges over `xs × ys`: some representative satisfies all `pos`
constraints and some constraint of every clause of `cls`. Factored by coordinate; constant atoms
are simplified (exactly: only constant-true atoms and constant-false alternatives are dropped). -/
def rootF (pos : List Cn) (cls : List (List Cn)) (xs ys : List LF) : Fml :=
  let posX := pos.filter Cn.isX
  let posY := pos.filter Cn.isY
  let posM := pos.filter Cn.isM
  let yd : List (LF × List Fml × List (Option (List Fml))) := ys.filterMap (fun py =>
    (simpAtoms (posY.map (Cn.substY py))).map (fun ay => (py, ay.map mkA, cls.map (clY py))))
  .or (xs.filterMap (fun px =>
    (simpAtoms (posX.map (Cn.substX px))).map (fun ax =>
      let cxs := cls.map (clX px)
      .and (ax.map mkA ++ [.or (yd.filterMap (fun t =>
        (combine px t.1 cls cxs t.2.2).map (fun fs =>
          .and (t.2.1 ++ posM.map (fun cn => mkA (cn.subst px t.1)) ++ fs))))]))))

theorem atoms_mkA {ls : List LF} {p : Params} (h : ∀ f ∈ ls.map mkA, f.eval p = true) :
    ∀ l ∈ ls, 0 ≤ l.eval p := by
  intro l hl
  have := h (mkA l) (List.mem_map.2 ⟨l, hl, rfl⟩)
  simpa [eval_mkA] using this

theorem rootF_sound (pos : List Cn) (cls : List (List Cn)) (xs ys : List LF) (p : Params)
    (h : (rootF pos cls xs ys).eval p = true) :
    ∃ px ∈ xs, ∃ py ∈ ys, (∀ cn ∈ pos, cn.holds p (px.eval p) (py.eval p)) ∧
      ∀ g ∈ cls, ∃ cn ∈ g, cn.holds p (px.eval p) (py.eval p) := by
  simp only [rootF, Fml.eval_or, List.mem_filterMap, Option.map_eq_some_iff] at h
  obtain ⟨_, ⟨px, hpx, ax, hax, rfl⟩, h⟩ := h
  rw [Fml.eval_and] at h
  have hA := atoms_mkA (fun f hf => h f (List.mem_append_left _ hf))
  have hB := h _ (List.mem_append_right _ List.mem_cons_self)
  rw [Fml.eval_or] at hB
  obtain ⟨_, ht, hB⟩ := hB
  simp only [List.mem_filterMap, Option.map_eq_some_iff] at ht
  obtain ⟨t, htm, fs, hfs, rfl⟩ := ht
  obtain ⟨py, hpy, ay, hay, rfl⟩ := htm
  simp only at hfs hB
  rw [Fml.eval_and] at hB
  have hAy := atoms_mkA (fun f hf => hB f (List.mem_append_left _ (List.mem_append_left _ hf)))
  have hM : ∀ f ∈ (pos.filter Cn.isM).map (fun cn => mkA (cn.subst px py)), f.eval p = true :=
    fun f hf => hB f (List.mem_append_left _ (List.mem_append_right _ hf))
  have hC : ∀ f ∈ fs, f.eval p = true := fun f hf => hB f (List.mem_append_right _ hf)
  refine ⟨px, hpx, py, hpy, ?_, combine_sound px py p cls fs hfs hC⟩
  intro cn hcn
  by_cases hx : cn.isX = true
  · have := simpAtoms_sound hax p hA (cn.substX px)
      (List.mem_map.2 ⟨cn, List.mem_filter.2 ⟨hcn, hx⟩, rfl⟩)
    exact (Cn.substX_eval px cn hx p _).1 this
  · by_cases hy : cn.isY = true
    · have := simpAtoms_sound hay p hAy (cn.substY py)
        (List.mem_map.2 ⟨cn, List.mem_filter.2 ⟨hcn, hy⟩, rfl⟩)
      exact (Cn.substY_eval py cn hy p _).1 this
    · have hm : cn.isM = true := by simp [Cn.isM, hx, hy]
      have := hM _ (List.mem_map.2 ⟨cn, List.mem_filter.2 ⟨hcn, hm⟩, rfl⟩)
      rw [eval_mkA, decide_eq_true_eq, Cn.subst_eval] at this
      exact this

/-- Shape lemma formula. -/
def shapeF (c : Case) (verts : List Vert) (xs ys : List LF) : Fml :=
  if closedOK c verts then
    rootF (verts.flatMap (vPos c)).eraseDups (verts.flatMap (vCls c)).eraseDups xs ys
  else Fml.ff

theorem shapeF_false (c : Case) (p : Params) (N : NF c p) (verts : List Vert) (xs ys : List LF) :
    (shapeF c verts xs ys).eval p = false := by
  unfold shapeF
  split
  · rename_i hc
    cases h : (rootF (verts.flatMap (vPos c)).eraseDups (verts.flatMap (vCls c)).eraseDups xs ys).eval p
    · rfl
    · exfalso
      obtain ⟨px, _, py, _, hpos, hcls⟩ := rootF_sound _ _ xs ys p h
      apply closed_false c p N verts hc (px.eval p) (py.eval p)
      intro v hv
      apply vert_facts
      · intro cn hcn
        exact hpos cn (List.mem_eraseDups.2 (List.mem_flatMap.2 ⟨v, hv, hcn⟩))
      · intro g hg
        exact hcls g (List.mem_eraseDups.2 (List.mem_flatMap.2 ⟨v, hv, hg⟩))
  · exact Fml.eval_ff p

/-! ## Certificate helpers -/

/-- Parameters from a list of values. -/
def valsP (vals : List Int) : Params := ⟨fun i => vals.getD i 0⟩

/-- First condition violated at the certificate point. -/
def firstViol (pv : Params) (rx ry : Int) (l : List Cn) : Option Cn :=
  l.find? (fun cn => !decide (cn.holds pv rx ry))

theorem firstViol_mem {pv : Params} {rx ry : Int} {l : List Cn} {cn : Cn}
    (h : firstViol pv rx ry l = some cn) : cn ∈ l := List.mem_of_find?_eq_some h

def optAll {α : Type} : List (Option α) → Option (List α)
  | [] => some []
  | none :: _ => none
  | some a :: l => (optAll l).map (a :: ·)

theorem optAll_map {α β : Type} (f : α → Option β) : ∀ (l : List α) (r : List β),
    optAll (l.map f) = some r → ∀ a ∈ l, ∃ b, f a = some b ∧ b ∈ r
  | [], _, _, a, ha => absurd ha (List.not_mem_nil)
  | x :: l, r, h, a, ha => by
    simp only [List.map_cons] at h
    cases hx : f x with
    | none => rw [hx] at h; simp [optAll] at h
    | some b =>
      rw [hx] at h
      simp only [optAll, Option.map_eq_some_iff] at h
      obtain ⟨r', hr', rfl⟩ := h
      rcases List.mem_cons.1 ha with rfl | ha
      · exact ⟨b, hx, List.mem_cons_self⟩
      · obtain ⟨b', h1, h2⟩ := optAll_map f l r' hr' a ha
        exact ⟨b', h1, List.mem_cons_of_mem _ h2⟩

/-- Conjunction of the eliminated system (`false` if elimination is impossible). -/
def elimF (S : List Cn) : Fml :=
  match elim S with
  | some out => .and (out.map mkA)
  | none => Fml.ff

theorem elimF_sound (S : List Cn) (p : Params) (h : (elimF S).eval p = true) :
    ∃ rx ry : Int, ∀ cn ∈ S, cn.holds p rx ry := by
  unfold elimF at h
  split at h
  · rename_i out hout
    rw [Fml.eval_and] at h
    exact elim_sound S out hout p (atoms_mkA h)
  · rw [Fml.eval_ff] at h; exact absurd h (by simp)

/-! ## `tpl` tree certificates -/

def vSysT (c : Case) (pv : Params) (rx ry : Int) (v : Vert) : Option (List Cn) :=
  (optAll ((allK.filter (fun k => !decide (k ∈ v.used))).map
    (fun k => firstViol pv rx ry (slotConds c v.m v.cx v.cy k)))).map
    (fun ns => vPos c v ++ ns.map Cn.neg)

def treeSys (c : Case) (verts : List Vert) (vals : List Int) (rx ry : Int) : Option (List Cn) :=
  (optAll (verts.map (vSysT c (valsP vals) rx ry))).map List.flatten

def tplTreeF (c : Case) (verts : List Vert) (vals : List Int) (rx ry : Int) : Fml :=
  if closedOK c verts then
    match treeSys c verts vals rx ry with
    | some S => elimF S
    | none => Fml.ff
  else Fml.ff

theorem tplTreeF_false (c : Case) (p : Params) (N : NF c p) (verts : List Vert) (vals : List Int)
    (rx0 ry0 : Int) : (tplTreeF c verts vals rx0 ry0).eval p = false := by
  unfold tplTreeF
  split
  · rename_i hc
    split
    · rename_i S hS
      cases h : (elimF S).eval p
      · rfl
      · exfalso
        obtain ⟨rx, ry, hall⟩ := elimF_sound S p h
        apply closed_false c p N verts hc rx ry
        intro v hv
        simp only [treeSys, Option.map_eq_some_iff] at hS
        obtain ⟨Ss, hSs, rfl⟩ := hS
        obtain ⟨Sv, hSv, hSvm⟩ := optAll_map _ verts Ss hSs v hv
        have hsub : ∀ cn ∈ Sv, cn.holds p rx ry :=
          fun cn hcn => hall cn (List.mem_flatten.2 ⟨Sv, hSvm, hcn⟩)
        simp only [vSysT, Option.map_eq_some_iff] at hSv
        obtain ⟨ns, hns, rfl⟩ := hSv
        apply vert_facts
        · exact fun cn hcn => hsub cn (List.mem_append_left _ hcn)
        · intro g hg
          simp only [vCls, List.mem_map] at hg
          obtain ⟨k, hk, rfl⟩ := hg
          obtain ⟨cn, hcn, hcnm⟩ := optAll_map _ _ ns hns k hk
          exact ⟨Cn.neg cn, List.mem_map.2 ⟨cn, firstViol_mem hcn, rfl⟩,
            hsub _ (List.mem_append_right _ (List.mem_map.2 ⟨cn, hcnm, rfl⟩))⟩
    · exact Fml.eval_ff p
  · exact Fml.eval_ff p

/-! ## `tpl` over certificates -/

/-- `g_k (M r + c)` as `(M', c'x, c'y)`. -/
def srcOfV (c : Case) (M : M2) (cx cy : LF) (k : Fin 4) : M2 × LF × LF :=
  let G := oriM (c.ori k)
  (⟨G.m00 * M.m00 + G.m01 * M.m10, G.m00 * M.m01 + G.m01 * M.m11,
    G.m10 * M.m00 + G.m11 * M.m10, G.m10 * M.m01 + G.m11 * M.m11⟩,
   LF.norm (LF.add (LF.add (LF.tx k) (LF.smul G.m00 cx)) (LF.smul G.m01 cy)),
   LF.norm (LF.add (LF.add (LF.ty k) (LF.smul G.m10 cx)) (LF.smul G.m11 cy)))

theorem srcOfV_eval (c : Case) (p : Params) (M : M2) (cx cy : LF) (k : Fin 4) (rx ry : Int) :
    (srcOfV c M cx cy k).1.m00 * rx + (srcOfV c M cx cy k).1.m01 * ry +
        (srcOfV c M cx cy k).2.1.eval p =
      srcX c p k (M.m00 * rx + M.m01 * ry + cx.eval p) (M.m10 * rx + M.m11 * ry + cy.eval p) ∧
    (srcOfV c M cx cy k).1.m10 * rx + (srcOfV c M cx cy k).1.m11 * ry +
        (srcOfV c M cx cy k).2.2.eval p =
      srcY c p k (M.m00 * rx + M.m01 * ry + cx.eval p) (M.m10 * rx + M.m11 * ry + cy.eval p) := by
  simp only [srcOfV, LF.eval_norm, LF.eval_add, LF.eval_smul, LF.eval_tx, LF.eval_ty]
  unfold srcX srcY
  constructor <;> grind

def edgeCns (c : Case) (pv : Params) (rx ry : Int) (verts : List Vert) (e : OEdge) :
    Option (List Cn) :=
  if e.p < verts.length then
    let v := verts.getD e.p default
    let pk := partner e.k
    let cp := composeV c v.m v.cx v.cy e.k pk
    let base := srcConds c v.m v.cx v.cy e.k
    if 0 ≤ e.q then
      let w := verts.getD e.q.toNat default
      if e.q.toNat < verts.length ∧ e.k2 = pk ∧ cp.1 = w.m then
        let dx := LF.sub cp.2.1 w.cx
        let dy := LF.sub cp.2.2 w.cy
        some (base ++ [mkC (0, 0) dx, mkC (0, 0) (LF.neg dx), mkC (0, 0) dy, mkC (0, 0) (LF.neg dy)])
      else none
    else
      match firstViol pv rx ry (boxConds c cp.1 cp.2.1 cp.2.2 pk) with
      | some cn => some (base ++ [Cn.neg cn])
      | none => none
  else none

/-- A source cell as `(slot, affine map of the root)`. -/
abbrev SrcA := Fin 4 × M2 × LF × LF

def srcA (c : Case) (verts : List Vert) (e : OEdge) : SrcA :=
  let v := verts.getD e.p default
  (e.k, srcOfV c v.m v.cx v.cy e.k)

def SrcA.row (s : SrcA) (i : Bool) : Int × Int :=
  if i then (s.2.1.m10, s.2.1.m11) else (s.2.1.m00, s.2.1.m01)
def SrcA.off (s : SrcA) (i : Bool) : LF := if i then s.2.2.2 else s.2.2.1
def SrcA.val (s : SrcA) (p : Params) (rx ry : Int) (i : Bool) : Int :=
  (s.row i).1 * rx + (s.row i).2 * ry + (s.off i).eval p

def overSeps : List LF :=
  [LF.zero, LF.d, LF.a, LF.u, LF.v, LF.f, LF.e, LF.sub LF.u LF.d, LF.sub LF.v LF.d,
   LF.sub LF.v LF.a, LF.sub LF.u LF.a]

def sepDirect (pv : Params) (rx ry : Int) (s1 s2 : SrcA) (i : Bool) : Option (List Cn) :=
  let co : Int × Int := ((s1.row i).1 - (s2.row i).1, (s1.row i).2 - (s2.row i).2)
  let dv := LF.sub (s1.off i) (s2.off i)
  let dd := s1.val pv rx ry i - s2.val pv rx ry i
  if dd = 0 ∨ (co.1 ≠ 0 ∧ co.2 ≠ 0) then none
  else if 0 < dd then some [mkC co (LF.addc dv (-1))]
  else some [mkC (-co.1, -co.2) (LF.addc (LF.neg dv) (-1))]

def sepLine2 (sl sh : SrcA) (i : Bool) (sp : LF) : List Cn :=
  [mkC (-(sl.row i).1, -(sl.row i).2) (LF.addc (LF.sub sp (sl.off i)) (-1)),
   mkC (sh.row i) (LF.sub (sh.off i) sp)]

def sepLine (pv : Params) (rx ry : Int) (s1 s2 : SrcA) (isp : Bool × LF) : Option (List Cn) :=
  let b := isp.2.eval pv
  let a1 := s1.val pv rx ry isp.1
  let a2 := s2.val pv rx ry isp.1
  if decide (a1 < b) = decide (a2 < b) then none
  else if a1 < b then some (sepLine2 s1 s2 isp.1 isp.2) else some (sepLine2 s2 s1 isp.1 isp.2)

def sepCns (pv : Params) (rx ry : Int) (s1 s2 : SrcA) : Option (List Cn) :=
  if s1.1.val % 2 ≠ s2.1.val % 2 then some []
  else if s1.val pv rx ry false = s2.val pv rx ry false ∧ s1.val pv rx ry true = s2.val pv rx ry true
    then none
  else match sepDirect pv rx ry s1 s2 false with
    | some l => some l
    | none => match sepDirect pv rx ry s1 s2 true with
      | some l => some l
      | none => ([false, true].flatMap (fun i => overSeps.map (i, ·))).findSome?
          (sepLine pv rx ry s1 s2)

theorem sepLine2_sound (p : Params) (rx ry : Int) (sl sh : SrcA) (i : Bool) (sp : LF)
    (h : ∀ cn ∈ sepLine2 sl sh i sp, cn.holds p rx ry) : sl.val p rx ry i ≠ sh.val p rx ry i := by
  have h1 := h _ List.mem_cons_self
  have h2 := h _ (List.mem_cons_of_mem _ List.mem_cons_self)
  simp only [sepLine2, mkC_holds, LF.eval_addc, LF.eval_sub, Int.neg_mul] at h1 h2
  unfold SrcA.val; omega

theorem sepDirect_sound (pv p : Params) (rx0 ry0 rx ry : Int) (s1 s2 : SrcA) (i : Bool) (cs : List Cn)
    (h : sepDirect pv rx0 ry0 s1 s2 i = some cs) (hc : ∀ cn ∈ cs, cn.holds p rx ry) :
    s1.val p rx ry i ≠ s2.val p rx ry i := by
  unfold sepDirect at h
  simp only at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · have := hc _ (by rw [← Option.some.inj h]; exact List.mem_cons_self)
      simp only [mkC_holds, LF.eval_addc, LF.eval_sub, Int.sub_mul] at this
      unfold SrcA.val; omega
    · have := hc _ (by rw [← Option.some.inj h]; exact List.mem_cons_self)
      simp only [mkC_holds, LF.eval_addc, LF.eval_sub, LF.eval_neg, Int.neg_mul, Int.sub_mul] at this
      unfold SrcA.val; omega

theorem sepCns_sound (pv p : Params) (rx0 ry0 rx ry : Int) (s1 s2 : SrcA) (cs : List Cn)
    (h : sepCns pv rx0 ry0 s1 s2 = some cs) (hc : ∀ cn ∈ cs, cn.holds p rx ry)
    (hpar : s1.1.val % 2 = s2.1.val % 2) :
    (s1.val p rx ry false, s1.val p rx ry true) ≠ (s2.val p rx ry false, s2.val p rx ry true) := by
  unfold sepCns at h
  rw [if_neg (by omega)] at h
  split at h
  · exact absurd h (by simp)
  · intro heq
    simp only [Prod.mk.injEq] at heq
    split at h
    · rename_i l hl
      cases h
      exact sepDirect_sound pv p rx0 ry0 rx ry s1 s2 false _ hl hc heq.1
    · split at h
      · rename_i l hl
        cases h
        exact sepDirect_sound pv p rx0 ry0 rx ry s1 s2 true _ hl hc heq.2
      · obtain ⟨isp, _, hisp⟩ := List.exists_of_findSome?_eq_some h
        unfold sepLine at hisp
        simp only at hisp
        split at hisp
        · exact absurd hisp (by simp)
        · have hv : s1.val p rx ry isp.1 = s2.val p rx ry isp.1 := by
            cases isp.1
            · exact heq.1
            · exact heq.2
          split at hisp
          · cases hisp
            exact sepLine2_sound p rx ry s1 s2 isp.1 isp.2 hc hv
          · cases hisp
            exact sepLine2_sound p rx ry s2 s1 isp.1 isp.2 hc hv.symm

/-- Pairs `(l[i], l[j])`, `i < j`. -/
def pairsOf {α : Type} : List α → List (α × α)
  | [] => []
  | a :: l => l.map (a, ·) ++ pairsOf l

theorem pairwise_of_pairsOf {α : Type} (R : α → α → Prop) : ∀ (l : List α),
    (∀ pr ∈ pairsOf l, R pr.1 pr.2) → l.Pairwise R
  | [], _ => List.Pairwise.nil
  | a :: l, h => by
    rw [List.pairwise_cons]
    refine ⟨fun b hb => h (a, b) (List.mem_append_left _ (List.mem_map.2 ⟨b, hb, rfl⟩)),
      pairwise_of_pairsOf R l (fun pr hpr => h pr (List.mem_append_right _ hpr))⟩

def overSys (c : Case) (verts : List Vert) (edges : List OEdge) (vals : List Int) (rx ry : Int) :
    Option (List Cn) :=
  let pv := valsP vals
  match optAll (edges.map (edgeCns c pv rx ry verts)),
      optAll ((pairsOf (edges.map (srcA c verts))).map (fun pr => sepCns pv rx ry pr.1 pr.2)) with
  | some a, some b => some (a.flatten ++ b.flatten)
  | _, _ => none

def tplOverF (c : Case) (verts : List Vert) (edges : List OEdge) (vals : List Int) (rx ry : Int) :
    Fml :=
  if verts.length < edges.length then
    match overSys c verts edges vals rx ry with
    | some S => elimF S
    | none => Fml.ff
  else Fml.ff

theorem tplOverF_false (c : Case) (p : Params) (N : NF c p) (verts : List Vert)
    (edges : List OEdge) (vals : List Int) (rx0 ry0 : Int) :
    (tplOverF c verts edges vals rx0 ry0).eval p = false := by
  unfold tplOverF
  split
  · rename_i hlt
    split
    · rename_i S hS
      cases h : (elimF S).eval p
      · rfl
      · exfalso
        obtain ⟨rx, ry, hall⟩ := elimF_sound S p h
        unfold overSys at hS
        simp only at hS
        split at hS
        · rename_i a b ha hb
          cases hS
          have hE : ∀ e ∈ edges, ∃ l, edgeCns c (valsP vals) rx0 ry0 verts e = some l ∧
              ∀ cn ∈ l, cn.holds p rx ry := by
            intro e he
            obtain ⟨l, hl, hlm⟩ := optAll_map _ edges a ha e he
            exact ⟨l, hl, fun cn hcn => hall cn (List.mem_append_left _ (List.mem_flatten.2 ⟨l, hlm, hcn⟩))⟩
          let pt : SrcA → Fin 4 × Int × Int := fun s => (s.1, s.val p rx ry false, s.val p rx ry true)
          have key := G2 c p N ((edges.map (srcA c verts)).map pt)
            (verts.map (fun v => (v.qx p rx ry, v.qy p rx ry)))
          simp only [List.length_map] at key
          refine absurd (key ?_ ?_ ?_) (by omega)
          · -- sources lie in their squares
            intro s hs
            simp only [List.map_map, List.mem_map] at hs
            obtain ⟨e, he, rfl⟩ := hs
            obtain ⟨l, hl, hlh⟩ := hE e he
            unfold edgeCns at hl
            split at hl
            · rename_i hp
              have hsrc : ∀ cn ∈ srcConds c (verts.getD e.p default).m (verts.getD e.p default).cx
                  (verts.getD e.p default).cy e.k, cn.holds p rx ry := by
                intro cn hcn
                apply hlh
                simp only at hl
                split at hl
                · split at hl
                  · cases hl; exact List.mem_append_left _ hcn
                  · exact absurd hl (by simp)
                · split at hl
                  · cases hl; exact List.mem_append_left _ hcn
                  · exact absurd hl (by simp)
              have := (srcConds_iff c p rx ry _ _ _ e.k).1 hsrc
              have ev := srcOfV_eval c p (verts.getD e.p default).m (verts.getD e.p default).cx
                (verts.getD e.p default).cy e.k rx ry
              simp only [Function.comp, pt, srcA, SrcA.val, SrcA.row, SrcA.off]
              simp only [Bool.false_eq_true, ite_false, ite_true]
              rw [ev.1, ev.2]; exact this
            · exact absurd hl (by simp)
          · -- pairwise distinct
            rw [List.pairwise_map]
            apply pairwise_of_pairsOf
            intro pr hpr hpar
            obtain ⟨cs, hcs, hcsm⟩ := optAll_map _ _ b hb pr hpr
            exact sepCns_sound (valsP vals) p rx0 ry0 rx ry pr.1 pr.2 cs hcs
              (fun cn hcn => hall cn (List.mem_append_right _ (List.mem_flatten.2 ⟨cs, hcsm, hcn⟩))) hpar
          · -- every hitter is a vertex
            intro s hs x y hW hpar hX hY
            simp only [List.map_map, List.mem_map] at hs
            obtain ⟨e, he, rfl⟩ := hs
            obtain ⟨l, hl, hlh⟩ := hE e he
            unfold edgeCns at hl
            split at hl
            · rename_i hp
              generalize hv : verts.getD e.p default = v at hl
              have hvm : v ∈ verts := by rw [← hv, getD_mem hp]; exact List.getElem_mem hp
              have ev := srcOfV_eval c p v.m v.cx v.cy e.k rx ry
              simp only [Function.comp, pt, srcA, SrcA.val, SrcA.row, SrcA.off, hv,
                Bool.false_eq_true, ite_false, ite_true] at hX hY hpar
              rw [ev.1] at hX; rw [ev.2] at hY
              rcases parity_cases _ _ hpar with hσ | hσ
              · rw [hσ] at hX hY
                obtain ⟨rfl, rfl⟩ := src_inj c p e.k _ _ _ _ hX hY
                exact List.mem_map.2 ⟨v, hvm, rfl⟩
              · have hc := composeV_src c p v.m v.cx v.cy e.k (partner e.k) rx ry
                rw [hσ] at hX hY
                rw [← hc.1] at hX; rw [← hc.2] at hY
                obtain ⟨rfl, rfl⟩ := src_inj c p _ _ _ _ _ hX hY
                simp only at hl
                split at hl
                · split at hl
                  · rename_i hq
                    cases hl
                    obtain ⟨hqlt, _, hM⟩ := hq
                    generalize hw : verts.getD e.q.toNat default = w at hM hlh
                    have hwm : w ∈ verts := by rw [← hw, getD_mem hqlt]; exact List.getElem_mem hqlt
                    have h1 := hlh _ (List.mem_append_right _ List.mem_cons_self)
                    have h2 := hlh _ (List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self))
                    have h3 := hlh _ (List.mem_append_right _ (List.mem_cons_of_mem _
                      (List.mem_cons_of_mem _ List.mem_cons_self)))
                    have h4 := hlh _ (List.mem_append_right _ (List.mem_cons_of_mem _
                      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))
                    simp only [mkC_holds, LF.eval_sub, LF.eval_neg] at h1 h2 h3 h4
                    refine List.mem_map.2 ⟨w, hwm, ?_⟩
                    simp only [Vert.qx, Vert.qy, ← hM, Prod.mk.injEq]
                    constructor <;> omega
                  · exact absurd hl (by simp)
                · split at hl
                  · rename_i cn hcn
                    cases hl
                    have hneg := hlh _ (List.mem_append_right _ List.mem_cons_self)
                    rw [Cn.holds_neg] at hneg
                    exfalso; apply hneg
                    have hav := N.avail _ _ hW
                    rw [hσ] at hav
                    exact (boxConds_iff c p rx ry _ _ _ _).2 hav.1 cn (firstViol_mem hcn)
                  · exact absurd hl (by simp)
            · exact absurd hl (by simp)
        · exact absurd hS (by simp)
    · exact Fml.eval_ff p
  · exact Fml.eval_ff p

/-! ## Region -/

/-- `a d + b e + c f + k`. -/
def lfDEF (a b c k : Int) : LF := [a, b, c, 0, 0, 0, 0, 0, 0, 0, 0, k]

theorem lfDEF_eval (a b c k : Int) (p : Params) : (lfDEF a b c k).eval p = a * p.d + b * p.e + c * p.f + k := by
  simp [lfDEF, LF.eval, LF.evalFrom, Params.val, Params.d, Params.e, Params.f]; omega

def regionAtoms : Region → List LF
  | .fat => [lfDEF 1 (-1) 0 (-1), lfDEF (-1) 0 1 (-1), lfDEF 3 0 (-2) 0, lfDEF 3 (-1) (-2) (-1)]
  | .mid => [lfDEF 0 0 1 (-1), lfDEF 1 0 (-1) (-1), lfDEF (-1) 1 0 (-1), lfDEF 3 (-1) (-2) (-1),
             lfDEF 11 (-4) 0 0]
  | .thin => [lfDEF 0 0 (-1) (-1), lfDEF (-1) 1 0 (-1), lfDEF (-2) 1 1 (-1), lfDEF 3 (-1) (-2) (-1)]

/-- The region inequalities and `1 ≤ d`, `1 ≤ e`. -/
def regionF (r : Region) : Fml :=
  .and ((regionAtoms r ++ [lfDEF 1 0 0 (-1), lfDEF 0 1 0 (-1)]).map Fml.atom)

theorem regionF_true (r : Region) (p : Params) (hr : RegionP r p.d p.e p.f) (hd : 1 ≤ p.d)
    (he : 1 ≤ p.e) : (regionF r).eval p = true := by
  rw [regionF, Fml.eval_and]
  intro f hf
  obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hf
  rw [Fml.eval_atom, decide_eq_true_eq]
  cases r <;> simp only [regionAtoms, RegionP] at hl hr <;>
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (try rcases ‹_ ∨ _› with rfl | rfl) <;>
    simp only [lfDEF_eval] <;> omega

theorem region_u (r : Region) (p : Params) (hr : RegionP r p.d p.e p.f) (hd : 1 ≤ p.d)
    (he : 1 ≤ p.e) : 1 ≤ p.u := by
  unfold Params.u; cases r <;> simp only [RegionP] at hr <;> omega

/-! ## Domain: two-rectangle covering of each source square -/

def rowImg (b : BoxLF) (r0 r1 : Int) (t : LF) : LF × LF :=
  let lo := if r0 ≠ 0 then b.x0 else b.y0
  let hi := if r0 ≠ 0 then b.x1 else b.y1
  let sg := if r0 ≠ 0 then r0 else r1
  if 0 < sg then (LF.add lo t, LF.add hi t) else (LF.addc (LF.sub t hi) 1, LF.addc (LF.sub t lo) 1)

/-- `Case.imgrect`: the image of the box of `k` under `g_k`, `[X0, X1) × [Y0, Y1)`. -/
def imgRect (c : Case) (k : Fin 4) : (LF × LF) × (LF × LF) :=
  let b := boxLF c.kind k
  let M := oriM (c.ori k)
  (rowImg b M.m00 M.m01 (LF.tx k), rowImg b M.m10 M.m11 (LF.ty k))

theorem imgRect_mem (c : Case) (p : Params) (k : Fin 4) (x y : Int)
    (h : (box c.kind p k).mem x y) :
    (imgRect c k).1.1.eval p ≤ srcX c p k x y ∧ srcX c p k x y < (imgRect c k).1.2.eval p ∧
    (imgRect c k).2.1.eval p ≤ srcY c p k x y ∧ srcY c p k x y < (imgRect c k).2.2.eval p := by
  obtain ⟨h1, h2, h3, h4⟩ := boxLF_eval c.kind p k
  unfold Box.mem at h
  unfold imgRect srcX srcY
  generalize boxLF c.kind k = b at h1 h2 h3 h4
  generalize c.ori k = o
  revert o
  apply Fin8.cases <;>
    simp [oriM, rowImg, LF.eval_add, LF.eval_addc, LF.eval_sub, LF.eval_tx, LF.eval_ty, h1, h2, h3, h4] <;>
    omega

theorem cov2 (S a0 a1 b0 b1 c0 c1 d0 d1 : Int) (hS : 1 ≤ S)
    (H : ∀ X Y, 0 ≤ X → X < S → 0 ≤ Y → Y < S →
      (a0 ≤ X ∧ X < a1 ∧ b0 ≤ Y ∧ Y < b1) ∨ (c0 ≤ X ∧ X < c1 ∧ d0 ≤ Y ∧ Y < d1)) :
    ((a0 ≤ 0 ∧ S ≤ a1) ∧ (b0 ≤ 0 ∧ S ≤ b1)) ∨ ((c0 ≤ 0 ∧ S ≤ c1) ∧ (d0 ≤ 0 ∧ S ≤ d1)) ∨
    ((b0 ≤ 0 ∧ S ≤ b1) ∧ (d0 ≤ 0 ∧ S ≤ d1) ∧
      ((a0 ≤ 0 ∧ S ≤ c1 ∧ c0 ≤ a1) ∨ (c0 ≤ 0 ∧ S ≤ a1 ∧ a0 ≤ c1))) ∨
    ((a0 ≤ 0 ∧ S ≤ a1) ∧ (c0 ≤ 0 ∧ S ≤ c1) ∧
      ((b0 ≤ 0 ∧ S ≤ d1 ∧ d0 ≤ b1) ∨ (d0 ≤ 0 ∧ S ≤ b1 ∧ b0 ≤ d1))) := by
  have hA := H 0 0 (by omega) (by omega) (by omega) (by omega)
  have hB := H (S - 1) 0 (by omega) (by omega) (by omega) (by omega)
  have hC := H 0 (S - 1) (by omega) (by omega) (by omega) (by omega)
  have hD := H (S - 1) (S - 1) (by omega) (by omega) (by omega) (by omega)
  have p1 := H 0 b1
  have p2 := H 0 d1
  have p3 := H a1 0
  have p4 := H c1 0
  rcases hA with hA | hA <;> rcases hB with hB | hB <;> rcases hC with hC | hC <;>
    rcases hD with hD | hD <;> omega

def le0F (l : LF) : Fml := mkA (LF.neg l)
def geF (l m : LF) : Fml := mkA (LF.sub l m)

def icovF (S a0 a1 b0 b1 : LF) : Fml :=
  .or [.and [le0F a0, geF b1 S, geF a1 b0], .and [le0F b0, geF a1 S, geF b1 a0]]

/-- The two-rectangle covering for the pair `(k0, k1)`. -/
def pairDomF (c : Case) (k0 k1 : Fin 4) : Fml :=
  let S := LF.side k0
  let r1 := imgRect c k0
  let r2 := imgRect c k1
  let fx1 := [le0F r1.1.1, geF r1.1.2 S]
  let fy1 := [le0F r1.2.1, geF r1.2.2 S]
  let fx2 := [le0F r2.1.1, geF r2.1.2 S]
  let fy2 := [le0F r2.2.1, geF r2.2.2 S]
  .or [.and (fx1 ++ fy1), .and (fx2 ++ fy2),
    .and (fy1 ++ fy2 ++ [icovF S r1.1.1 r1.1.2 r2.1.1 r2.1.2]),
    .and (fx1 ++ fx2 ++ [icovF S r1.2.1 r1.2.2 r2.2.1 r2.2.2])]

def domainF (c : Case) : Fml := .and [pairDomF c 0 2, pairDomF c 1 3]

theorem pairDomF_true (c : Case) (p : Params) (N : NF c p) (k0 : Fin 4) (hS : 1 ≤ p.side k0) :
    (pairDomF c k0 (partner k0)).eval p = true := by
  have H : ∀ X Y, 0 ≤ X → X < p.side k0 → 0 ≤ Y → Y < p.side k0 →
      ((imgRect c k0).1.1.eval p ≤ X ∧ X < (imgRect c k0).1.2.eval p ∧
        (imgRect c k0).2.1.eval p ≤ Y ∧ Y < (imgRect c k0).2.2.eval p) ∨
      ((imgRect c (partner k0)).1.1.eval p ≤ X ∧ X < (imgRect c (partner k0)).1.2.eval p ∧
        (imgRect c (partner k0)).2.1.eval p ≤ Y ∧ Y < (imgRect c (partner k0)).2.2.eval p) := by
    intro X Y h1 h2 h3 h4
    obtain ⟨x, y, hW, hpar, hX, hY⟩ := N.surj k0 X Y h1 h2 h3 h4
    have hav := N.avail x y hW
    rcases parity_cases _ _ hpar with hσ | hσ
    · rw [hσ] at hav hX hY
      have := imgRect_mem c p k0 x y hav.1
      rw [hX, hY] at this; exact Or.inl this
    · rw [hσ] at hav hX hY
      have := imgRect_mem c p (partner k0) x y hav.1
      rw [hX, hY] at this; exact Or.inr this
  have := cov2 _ _ _ _ _ _ _ _ _ hS H
  simp only [pairDomF, icovF, le0F, geF, Fml.eval_or, Fml.eval_and, List.mem_cons, List.mem_append,
    List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, exists_eq_or_imp, exists_eq_left,
    eval_mkA, decide_eq_true_eq, LF.eval_neg, LF.eval_sub, LF.eval_side, List.cons_append,
    List.nil_append, false_or, false_implies, implies_true, and_true, exists_eq]
  omega

theorem domainF_true (c : Case) (p : Params) (N : NF c p) (hd : 1 ≤ p.d) (he : 1 ≤ p.e)
    (hu : 1 ≤ p.u) : (domainF c).eval p = true := by
  rw [domainF, Fml.eval_and]
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl
  · exact pairDomF_true c p N 0 (by simp [Params.side, Params.v, Params.u] at hu ⊢; omega)
  · exact pairDomF_true c p N 1 (by simp [Params.side]; exact hu)

/-! ## cover81: every representative cell of `W` has an available slot -/

/-- Lower and upper term lists of `R_k = box_k ∩ g_k⁻¹(S_k)` per coordinate. -/
def rkTerms (c : Case) (k : Fin 4) : (List LF × List LF) × (List LF × List LF) :=
  let b := boxLF c.kind k
  let G := oriM (c.ori k)
  let S := LF.side k
  let step (acc : (List LF × List LF) × (List LF × List LF)) (row : Int × Int × LF) :
      (List LF × List LF) × (List LF × List LF) :=
    let j0 := row.1 ≠ 0
    let sg := if j0 then row.1 else row.2.1
    let t := row.2.2
    let plo := if sg = 1 then LF.neg t else LF.addc (LF.sub t S) 1
    let phi := if sg = 1 then LF.sub S t else LF.addc t 1
    if j0 then ((acc.1.1 ++ [plo], acc.1.2), (acc.2.1 ++ [phi], acc.2.2))
    else ((acc.1.1, acc.1.2 ++ [plo]), (acc.2.1, acc.2.2 ++ [phi]))
  let a0 := (([b.x0], [b.y0]), ([b.x1], [b.y1]))
  step (step a0 (G.m00, G.m01, LF.tx k)) (G.m10, G.m11, LF.ty k)

def c81xs (c : Case) : List LF :=
  ((LF.zero :: allK.flatMap (fun k => (rkTerms c k).1.1 ++ (rkTerms c k).2.1)).map LF.norm).eraseDups
def c81ys (c : Case) : List LF :=
  ((LF.zero :: allK.flatMap (fun k => (rkTerms c k).1.2 ++ (rkTerms c k).2.2)).map LF.norm).eraseDups

def M2.id : M2 := ⟨1, 0, 0, 1⟩

/-- At `(px, py)`: outside `W`, or some slot available. -/
def cellF (c : Case) (px py : LF) : Fml :=
  .or ((condsW M2.id LF.zero LF.zero).map (fun cn => mkA ((Cn.neg cn).subst px py)) ++
    allK.map (fun k => .and ((slotConds c M2.id LF.zero LF.zero k).map (fun cn => mkA (cn.subst px py)))))

def cover81F (c : Case) : Fml :=
  .and ((c81xs c).flatMap (fun px => (c81ys c).map (fun py => cellF c px py)))

theorem mkA_subst (cn : Cn) (px py : LF) (p : Params) :
    (mkA (cn.subst px py)).eval p = decide (cn.holds p (px.eval p) (py.eval p)) := by
  rw [eval_mkA, Cn.subst_eval]; rfl

theorem cellF_true (c : Case) (p : Params) (N : NF c p) (px py : LF) :
    (cellF c px py).eval p = true := by
  have hid : ∀ X Y : Int, M2.id.m00 * X + M2.id.m01 * Y + LF.zero.eval p = X ∧
      M2.id.m10 * X + M2.id.m11 * Y + LF.zero.eval p = Y := by
    intro X Y; simp [M2.id, LF.eval_zero]
  rw [cellF, Fml.eval_or]
  by_cases hW : InW p (px.eval p) (py.eval p)
  · have hav := N.avail _ _ hW
    refine ⟨_, List.mem_append_right _ (List.mem_map.2 ⟨N.σ (px.eval p) (py.eval p), mem_allK _, rfl⟩), ?_⟩
    rw [Fml.eval_and]
    intro f hf
    obtain ⟨cn, hcn, rfl⟩ := List.mem_map.1 hf
    rw [mkA_subst, decide_eq_true_eq]
    have := (slotConds_iff c p (px.eval p) (py.eval p) M2.id LF.zero LF.zero (N.σ (px.eval p) (py.eval p))).2
    rw [(hid _ _).1, (hid _ _).2] at this
    exact this hav cn hcn
  · have : ¬ ∀ cn ∈ condsW M2.id LF.zero LF.zero, cn.holds p (px.eval p) (py.eval p) := by
      rw [condsW_iff, (hid _ _).1, (hid _ _).2]; exact hW
    have ⟨cn, hcn, hn⟩ : ∃ cn ∈ condsW M2.id LF.zero LF.zero, ¬ cn.holds p (px.eval p) (py.eval p) :=
      Classical.byContradiction fun h' => this fun cn hcn =>
        Classical.byContradiction fun hn => h' ⟨cn, hcn, hn⟩
    refine ⟨_, List.mem_append_left _ (List.mem_map.2 ⟨cn, hcn, rfl⟩), ?_⟩
    rw [mkA_subst, decide_eq_true_eq, Cn.holds_neg]; exact hn

theorem cover81F_true (c : Case) (p : Params) (N : NF c p) : (cover81F c).eval p = true := by
  rw [cover81F, Fml.eval_and]
  intro f hf
  obtain ⟨px, _, hf⟩ := List.mem_flatMap.1 hf
  obtain ⟨py, _, rfl⟩ := List.mem_map.1 hf
  exact cellF_true c p N px py

/-! ## Lemmas and tables -/

/-- A formula whose truth contradicts `NF`. -/
def lemmaF (c : Case) : LemmaData → Fml
  | .shape verts xs ys => shapeF c verts xs ys
  | .tplTree verts vals rx ry => tplTreeF c verts vals rx ry
  | .tplOver verts edges vals rx ry => tplOverF c verts edges vals rx ry

theorem lemmaF_false (c : Case) (p : Params) (N : NF c p) (L : LemmaData) :
    (lemmaF c L).eval p = false := by
  cases L with
  | shape verts xs ys => exact shapeF_false c p N verts xs ys
  | tplTree verts vals rx ry => exact tplTreeF_false c p N verts vals rx ry
  | tplOver verts edges vals rx ry => exact tplOverF_false c p N verts edges vals rx ry

def tableF (t : Table) : Fml :=
  .and ([regionF t.region, domainF t.case, cover81F t.case] ++
    t.lemmas.map (fun L => Fml.neg (lemmaF t.case L)))

theorem tableF_true (t : Table) (p : Params) (N : NF t.case p) (hr : RegionP t.region p.d p.e p.f)
    (hd : 1 ≤ p.d) (he : 1 ≤ p.e) : (tableF t).eval p = true := by
  have hu := region_u t.region p hr hd he
  rw [tableF, Fml.eval_and]
  intro f hf
  rcases List.mem_append.1 hf with hf | hf
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl
    · exact regionF_true t.region p hr hd he
    · exact domainF_true t.case p N hd he hu
    · exact cover81F_true t.case p N
  · obtain ⟨L, _, rfl⟩ := List.mem_map.1 hf
    rw [Fml.eval_neg, lemmaF_false t.case p N L]; rfl

end Ex89.T22
