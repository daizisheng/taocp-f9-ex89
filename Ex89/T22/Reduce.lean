import Ex89.T22.Defs
import Ex89.Normal
/-!
# Reduction: a 2+2 dissection gives a normal form `NF c p`

`reduce`: a `Dissection u v w` with exactly two pieces going to the `u × u` square yields a case
`c` and parameters `p` with `d = w - v`, `e = v - u`, `f = 2u - w` and `Nonempty (NF c p)`.

Steps: rotate so that the corner pattern is `F T F T` (diag) or `F F T T` (adj); name each piece
by its corner; make the symmetries of slots `0, 1` the identity (`exists_fixed`).
The slot of the piece at corner `j` is `π j` (diag: `π = id`; adj: `π = (1 2)`).
-/
namespace Ex89.T22
open Ex89

/-! ## Motions as `oriM` + translation -/

/-- ORI index of the linear part of a motion. -/
def oriIdx (m : Motion) : Fin 8 :=
  match m.sw, m.fx, m.fy with
  | false, false, false => 0
  | false, true, true => 2
  | false, true, false => 5
  | false, false, true => 7
  | true, false, false => 4
  | true, true, false => 1
  | true, false, true => 3
  | true, true, true => 6

/-- Translation of a motion in the form `M (x, y) + t`. -/
def transX (w : Nat) (m : Motion) : Int :=
  m.dx + (if (m.sw && m.fy) || (!m.sw && m.fx) then (w : Int) - 1 else 0)
def transY (w : Nat) (m : Motion) : Int :=
  m.dy + (if (m.sw && m.fx) || (!m.sw && m.fy) then (w : Int) - 1 else 0)

theorem imgX_eq (m : Motion) (w x y : Nat) :
    m.imgX w x y = (oriM (oriIdx m)).m00 * x + (oriM (oriIdx m)).m01 * y + transX w m := by
  rcases m with ⟨sw, fx, fy, dx, dy⟩
  cases sw <;> cases fx <;> cases fy <;> simp [Motion.imgX, oriIdx, oriM, transX] <;> omega

theorem imgY_eq (m : Motion) (w x y : Nat) :
    m.imgY w x y = (oriM (oriIdx m)).m10 * x + (oriM (oriIdx m)).m11 * y + transY w m := by
  rcases m with ⟨sw, fx, fy, dx, dy⟩
  cases sw <;> cases fx <;> cases fy <;> simp [Motion.imgY, oriIdx, oriM, transY] <;> omega

theorem oriIdx_id (m : Motion) (h1 : m.sw = false) (h2 : m.fx = false) (h3 : m.fy = false) :
    oriIdx m = 0 := by
  rcases m with ⟨sw, fx, fy, dx, dy⟩
  simp only at h1 h2 h3; subst h1 h2 h3; rfl

/-! ## Parameters -/

/-- The parameters: `d, e, f` and the translations `tx k, ty k` of the slots. -/
def mkP (u v w : Nat) (tx ty : Fin 4 → Int) : Params :=
  ⟨fun i => [(w : Int) - v, (v : Int) - u, 2 * (u : Int) - w,
    tx 0, ty 0, tx 1, ty 1, tx 2, ty 2, tx 3, ty 3].getD i 0⟩

section mkP
variable (u v w : Nat) (tx ty : Fin 4 → Int)
theorem mkP_d : (mkP u v w tx ty).d = (w : Int) - v := rfl
theorem mkP_e : (mkP u v w tx ty).e = (v : Int) - u := rfl
theorem mkP_f : (mkP u v w tx ty).f = 2 * (u : Int) - w := rfl
theorem mkP_u : (mkP u v w tx ty).u = u := by
  simp only [Params.u, mkP_d, mkP_e, mkP_f]; omega
theorem mkP_v : (mkP u v w tx ty).v = v := by
  simp only [Params.v, mkP_d, mkP_e, mkP_f]; omega
theorem mkP_w : (mkP u v w tx ty).w = w := by
  simp only [Params.w, mkP_d, mkP_e, mkP_f]; omega
theorem mkP_a : (mkP u v w tx ty).a = (w : Int) - u := by
  simp only [Params.a, mkP_d, mkP_e]; omega
theorem mkP_tx (k : Fin 4) : (mkP u v w tx ty).tx k = tx k := by
  revert k; apply slot_cases <;> rfl
theorem mkP_ty (k : Fin 4) : (mkP u v w tx ty).ty k = ty k := by
  revert k; apply slot_cases <;> rfl
end mkP

/-! ## The general construction of `NF` -/

theorem nf_of {u v w : Nat} (D : Dissection u v w) (c : Case) (p : Params) (π : Fin 4 → Fin 4)
    (hπ : ∀ k, π (π k) = k)
    (hw : p.w = w) (hu : p.u = u) (hv : p.v = v)
    (hside : ∀ j, D.toU j = decide ((π j).val % 2 = 1))
    (hori : ∀ j, c.ori (π j) = oriIdx (D.motion j))
    (htx : ∀ j, p.tx (π j) = transX w (D.motion j))
    (hty : ∀ j, p.ty (π j) = transY w (D.motion j))
    (hbox : ∀ (x y : Nat), x < w → y < w → (box c.kind p (π (D.piece x y))).mem x y) :
    Nonempty (NF c p) := by
  -- source coordinates are the images of the motion
  have sX : ∀ (j : Fin 4) (x y : Nat), srcX c p (π j) x y = (D.motion j).imgX w x y := by
    intro j x y; rw [imgX_eq, srcX, hori, htx]
  have sY : ∀ (j : Fin 4) (x y : Nat), srcY c p (π j) x y = (D.motion j).imgY w x y := by
    intro j x y; rw [imgY_eq, srcY, hori, hty]
  have sd : ∀ j, p.side (π j) = ((if D.toU j then u else v : Nat) : Int) := by
    intro j; rw [hside j, Params.side]
    by_cases h : (π j).val % 2 = 1
    · simp [h, hu]
    · have h' : (π j).val % 2 = 0 := by omega
      simp [h', hv]
  -- parity of the slot = target square
  have par : ∀ j j', (π j).val % 2 = (π j').val % 2 ↔ D.toU j = D.toU j' := by
    intro j j'; rw [hside, hside]
    constructor
    · intro h; simp [h]
    · intro h; simp only [decide_eq_decide] at h; omega
  have cast : ∀ x : Int, 0 ≤ x → ((x.toNat : Nat) : Int) = x := fun x hx => Int.toNat_of_nonneg hx
  refine ⟨⟨fun x y => π (D.piece x.toNat y.toNat), ?_, ?_, ?_⟩⟩
  · intro x y ⟨h0, h1, h2, h3⟩
    rw [hw] at h1 h3
    have hx : x.toNat < w := by omega
    have hy : y.toNat < w := by omega
    have hb := hbox _ _ hx hy
    have m := D.maps_into _ _ hx hy
    have ex := sX (D.piece x.toNat y.toNat) x.toNat y.toNat
    have ey := sY (D.piece x.toNat y.toNat) x.toNat y.toNat
    rw [cast x h0, cast y h2] at ex ey hb
    refine ⟨hb, ?_⟩
    rw [ex, ey, sd]
    simpa [InSquare] using m
  · intro x y x' y' ⟨h0, h1, h2, h3⟩ ⟨h0', h1', h2', h3'⟩ hpar e1 e2
    rw [hw] at h1 h3 h1' h3'
    have hb := (par _ _).1 hpar
    have ex := sX (D.piece x.toNat y.toNat) x.toNat y.toNat
    have ey := sY (D.piece x.toNat y.toNat) x.toNat y.toNat
    have ex' := sX (D.piece x'.toNat y'.toNat) x'.toNat y'.toNat
    have ey' := sY (D.piece x'.toNat y'.toNat) x'.toNat y'.toNat
    rw [cast x h0, cast y h2] at ex ey
    rw [cast x' h0', cast y' h2'] at ex' ey'
    rw [ex, ex'] at e1
    rw [ey, ey'] at e2
    have := D.injective _ _ _ _ (by omega) (by omega) (by omega) (by omega) hb e1 e2
    omega
  · intro k X Y h0 h1 h2 h3
    have hk := hπ k
    rw [← hk, sd] at h1 h3
    obtain ⟨x, y, hx, hy, hb, e1, e2⟩ :=
      D.surjective (D.toU (π k)) X Y (by simp only [InSquare]; exact ⟨h0, h1, h2, h3⟩)
    refine ⟨x, y, ⟨by omega, by rw [hw]; omega, by omega, by rw [hw]; omega⟩, ?_, ?_, ?_⟩
    · simp only [Int.toNat_natCast]
      rw [← hk]; exact (par _ _).2 hb
    · simp only [Int.toNat_natCast]; rw [sX]; exact e1
    · simp only [Int.toNat_natCast]; rw [sY]; exact e2

/-! ## Corner patterns -/

/-- `exists_canon`, keeping `toU`. -/
theorem exists_canon' {u v w : Nat} (D : Dissection u v w) :
    ∃ D' : Dissection u v w, D'.toU = D.toU ∧ A (pat D' 0) (pat D' 1) (pat D' 2) (pat D' 3) = true := by
  obtain ⟨a1, a2, a3, a4⟩ := pat_rot D
  obtain ⟨b1, b2, b3, b4⟩ := pat_rot D.rot
  obtain ⟨c1, c2, c3, c4⟩ := pat_rot D.rot.rot
  rcases A_rot (pat D 0) (pat D 1) (pat D 2) (pat D 3) with h | h | h | h
  · exact ⟨D, rfl, h⟩
  · exact ⟨D.rot, rfl, by rw [a1, a2, a3, a4]; exact h⟩
  · exact ⟨D.rot.rot, rfl, by rw [b1, b2, b3, b4, a1, a2, a3, a4]; exact h⟩
  · exact ⟨D.rot.rot.rot, rfl, by rw [c1, c2, c3, c4, b1, b2, b3, b4, a1, a2, a3, a4]; exact h⟩

def sel (b0 b1 b2 b3 : Bool) : Fin 4 → Bool
  | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3

def cnt (b0 b1 b2 b3 : Bool) : Nat := ([b0, b1, b2, b3].filter id).length

set_option maxRecDepth 100000 in
theorem pattern22 : ∀ (b0 b1 b2 b3 : Bool) (a0 a1 a2 a3 : Fin 4),
    a0 ≠ a1 → a0 ≠ a2 → a0 ≠ a3 → a1 ≠ a2 → a1 ≠ a3 → a2 ≠ a3 → cnt b0 b1 b2 b3 = 2 →
    A (sel b0 b1 b2 b3 a0) (sel b0 b1 b2 b3 a1) (sel b0 b1 b2 b3 a2) (sel b0 b1 b2 b3 a3) = true →
    (sel b0 b1 b2 b3 a0 = false ∧ sel b0 b1 b2 b3 a1 = true ∧ sel b0 b1 b2 b3 a2 = false ∧
      sel b0 b1 b2 b3 a3 = true) ∨
    (sel b0 b1 b2 b3 a0 = false ∧ sel b0 b1 b2 b3 a1 = false ∧ sel b0 b1 b2 b3 a2 = true ∧
      sel b0 b1 b2 b3 a3 = true) := by decide

theorem sel_eq (t : Fin 4 → Bool) (k : Fin 4) : sel (t 0) (t 1) (t 2) (t 3) k = t k := by
  revert k; apply slot_cases <;> rfl

theorem cnt_eq (t : Fin 4 → Bool) :
    ((List.finRange 4).filter (fun k => t k)).length = cnt (t 0) (t 1) (t 2) (t 3) := by
  simp [List.finRange, List.ofFn, Fin.foldr, Fin.foldr.loop, cnt, List.filter]
  cases t 0 <;> cases t 1 <;> cases t 2 <;> cases t 3 <;> rfl

/-! ## Geometry: a cell of the piece at corner `j` lies in the corner box -/

/-- Cell `(x, y)` is within distance `< S` of corner `j` in both coordinates. -/
def Near (w : Nat) (S : Int) (j : Fin 4) (x y : Nat) : Prop :=
  (x : Int) - cornerX w j < S ∧ (cornerX w j : Int) - x < S ∧
  (y : Int) - cornerY w j < S ∧ (cornerY w j : Int) - y < S

theorem near_piece {u v w : Nat} (D : Dissection u v w) (hw : 0 < w)
    (hc : ∀ k, D.piece (cornerX w k) (cornerY w k) = k) {x y : Nat} (hx : x < w) (hy : y < w) :
    Near w ((if D.toU (D.piece x y) then u else v : Nat) : Int) (D.piece x y) x y := by
  have h1 := D.maps_into x y hx hy
  obtain ⟨cx, cy⟩ := corner_lt w hw (D.piece x y)
  have h2 := D.maps_into _ _ cx cy
  rw [hc] at h2
  have := Motion.close _ h1 h2
  unfold Near; omega

def piAdj : Fin 4 → Fin 4
  | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3

def sideS (u v : Nat) (k : Fin 4) : Int := if k.val % 2 = 1 then u else v

theorem geom_diag (u v w : Nat) (p : Params)
    (hd : p.d = (w : Int) - v) (hu : p.u = u) (hv : p.v = v) (hw : p.w = w) (ha : p.a = (w : Int) - u)
    (j : Fin 4) (x y : Nat) (hx : x < w) (hy : y < w) (h : Near w (sideS u v (id j)) j x y) :
    (box .diag p (id j)).mem x y := by
  revert j; apply slot_cases <;>
    simp only [id, Near, sideS, box, Box.mem, cornerX, cornerY, hd, hu, hv, hw, ha] <;>
    simp <;> omega

theorem geom_adj (u v w : Nat) (p : Params)
    (hd : p.d = (w : Int) - v) (hu : p.u = u) (hv : p.v = v) (hw : p.w = w) (ha : p.a = (w : Int) - u)
    (j : Fin 4) (x y : Nat) (hx : x < w) (hy : y < w) (h : Near w (sideS u v (piAdj j)) j x y) :
    (box .adj p (piAdj j)).mem x y := by
  revert j; apply slot_cases <;>
    simp only [piAdj, Near, sideS, box, Box.mem, cornerX, cornerY, hd, hu, hv, hw, ha] <;>
    simp <;> omega

/-- Finishing step, common to both kinds. -/
theorem finish {u v w : Nat} (hu0 : 0 < u) (huv : u < v) (hvw : v < w) (D : Dissection u v w)
    (kind : Kind) (π : Fin 4 → Fin 4) (hπ : ∀ k, π (π k) = k)
    (hc : ∀ k, D.piece (cornerX w k) (cornerY w k) = k)
    (hside : ∀ j, D.toU j = decide ((π j).val % 2 = 1))
    (hid0 : oriIdx (D.motion (π 0)) = 0) (hid1 : oriIdx (D.motion (π 1)) = 0)
    (hgeom : ∀ (p : Params), p.d = (w : Int) - v → p.u = u → p.v = v → p.w = w →
      p.a = (w : Int) - u → ∀ (j : Fin 4) (x y : Nat), x < w → y < w →
      Near w (sideS u v (π j)) j x y → (box kind p (π j)).mem x y) :
    ∃ (c : Case) (p : Params), p.d = (w:Int) - v ∧ p.e = (v:Int) - u ∧ p.f = 2*(u:Int) - w ∧
      Nonempty (NF c p) := by
  let c : Case := ⟨kind, oriIdx (D.motion (π 2)), oriIdx (D.motion (π 3))⟩
  let p := mkP u v w (fun k => transX w (D.motion (π k))) (fun k => transY w (D.motion (π k)))
  refine ⟨c, p, mkP_d .., mkP_e .., mkP_f .., ?_⟩
  have hw0 : 0 < w := by omega
  have hori' : ∀ k, c.ori k = oriIdx (D.motion (π k)) := by
    apply slot_cases
    · exact hid0.symm
    · exact hid1.symm
    · rfl
    · rfl
  apply nf_of D c p π hπ (mkP_w ..) (mkP_u ..) (mkP_v ..) hside
  · intro j; rw [hori', hπ]
  · intro j; rw [mkP_tx, hπ]
  · intro j; rw [mkP_ty, hπ]
  · intro x y hx hy
    apply hgeom p (mkP_d ..) (mkP_u ..) (mkP_v ..) (mkP_w ..) (mkP_a ..) _ x y hx hy
    have h := near_piece D hw0 hc hx hy
    have e : ((if D.toU (D.piece x y) then u else v : Nat) : Int) = sideS u v (π (D.piece x y)) := by
      rw [hside, sideS]
      by_cases h : (π (D.piece x y)).val % 2 = 1 <;> simp [h]
    rwa [e] at h

/-! ## The main reduction -/

theorem reduce (u v w : Nat) (hu : 0 < u) (huv : u < v) (hvw : v < w) (D : Dissection u v w)
    (h22 : ((List.finRange 4).filter (fun k => D.toU k)).length = 2) :
    ∃ (c : Case) (p : Params), p.d = (w:Int) - v ∧ p.e = (v:Int) - u ∧ p.f = 2*(u:Int) - w ∧
      Nonempty (NF c p) := by
  have huw : u < w := by omega
  have hw0 : 0 < w := by omega
  obtain ⟨D1, hD1, hA⟩ := exists_canon' D
  rw [cnt_eq, ← hD1] at h22
  obtain ⟨E, es, ec⟩ := exists_named D1 huw hvw
  have hpat := pattern22 _ _ _ _ _ _ _ _
    (corner_ne D1 huw hvw 0 1 (by decide)) (corner_ne D1 huw hvw 0 2 (by decide))
    (corner_ne D1 huw hvw 0 3 (by decide)) (corner_ne D1 huw hvw 1 2 (by decide))
    (corner_ne D1 huw hvw 1 3 (by decide)) (corner_ne D1 huw hvw 2 3 (by decide)) h22
  simp only [sel_eq] at hpat
  have hpat := hpat hA
  simp only [pat] at es
  have e0 := es 0; have e1 := es 1; have e2 := es 2; have e3 := es 3
  rcases hpat with ⟨f0, f1, f2, f3⟩ | ⟨f0, f1, f2, f3⟩
  · -- diag, pattern `F T F T`; slot = corner
    rw [f0] at e0; rw [f1] at e1; rw [f2] at e2; rw [f3] at e3
    obtain ⟨E1, p1, t1, o1, a1, b1, c1⟩ := exists_fixed E 0
    obtain ⟨E2, p2, t2, o2, a2, b2, c2⟩ := exists_fixed E1 1
    have hc : ∀ k, E2.piece (cornerX w k) (cornerY w k) = k := by intro k; rw [p2, p1]; exact ec k
    have o : E1.toU 0 ≠ E1.toU 1 := by rw [t1, e0, e1]; simp
    have m0 := o2 0 o
    refine finish hu huv hvw E2 .diag id (fun _ => rfl) hc ?_ ?_ ?_ ?_
    · rw [t2, t1]; apply slot_cases <;> simp [e0, e1, e2, e3] <;> decide
    · show oriIdx (E2.motion 0) = 0
      rw [m0]; exact oriIdx_id _ a1 b1 c1
    · exact oriIdx_id _ a2 b2 c2
    · intro p hd hu' hv hw ha j x y hx hy h
      exact geom_diag u v w p hd hu' hv hw ha j x y hx hy h
  · -- adj, pattern `F F T T`; slots 0,1,2,3 = corners 0,2,1,3
    rw [f0] at e0; rw [f1] at e1; rw [f2] at e2; rw [f3] at e3
    obtain ⟨E1, p1, t1, o1, a1, b1, c1⟩ := exists_fixed E 0
    obtain ⟨E2, p2, t2, o2, a2, b2, c2⟩ := exists_fixed E1 2
    have hc : ∀ k, E2.piece (cornerX w k) (cornerY w k) = k := by intro k; rw [p2, p1]; exact ec k
    have o : E1.toU 0 ≠ E1.toU 2 := by rw [t1, e0, e2]; simp
    have m0 := o2 0 o
    refine finish hu huv hvw E2 .adj piAdj (by apply slot_cases <;> rfl) hc ?_ ?_ ?_ ?_
    · rw [t2, t1]; apply slot_cases <;> simp [piAdj, e0, e1, e2, e3] <;> decide
    · show oriIdx (E2.motion 0) = 0
      rw [m0]; exact oriIdx_id _ a1 b1 c1
    · exact oriIdx_id _ a2 b2 c2
    · intro p hd hu' hv hw ha j x y hx hy h
      exact geom_adj u v w p hd hu' hv hw ha j x y hx hy h

end Ex89.T22
