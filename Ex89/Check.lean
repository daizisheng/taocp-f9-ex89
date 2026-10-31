import Ex89.Model
/-!
The search program. It rebuilds the search of `proof-20-21-29` for any `(u, v, w)`.
Each corner of the `w × w` square lies in its own piece, called slot `k` below.
-/
namespace Ex89

def allSlots : List (Fin 4) := [0, 1, 2, 3]

def cornerX (w : Nat) : Fin 4 → Nat
  | 0 => 0 | 1 => 0 | 2 => w - 1 | 3 => w - 1
def cornerY (w : Nat) : Fin 4 → Nat
  | 0 => 0 | 1 => w - 1 | 2 => w - 1 | 3 => 0

/-- The side of the target square `b`. -/
def sideOf (u v : Nat) (b : Bool) : Nat := if b then u else v

/-- A cell of a piece with side `S` that contains corner `k` is close to that corner. -/
def reach (w S : Nat) (k : Fin 4) (x y : Nat) : Bool :=
  decide (x < cornerX w k + S) && decide (cornerX w k < x + S) &&
  decide (y < cornerY w k + S) && decide (cornerY w k < y + S)

structure Cfg where
  u : Nat
  v : Nat
  w : Nat
  /-- `side k` is the target square of slot `k`. -/
  side : Fin 4 → Bool
  /-- `ids k` means that the symmetry of slot `k` is the identity. -/
  ids : Fin 4 → Bool
  /-- `fixed k` means that slot `k` is the whole square, unmoved. -/
  fixed : Fin 4 → Bool

def Cfg.S (c : Cfg) (k : Fin 4) : Nat := sideOf c.u c.v (c.side k)

/-- Only the piece in slot `k` can contain the cell. -/
def Cfg.isPriv (c : Cfg) (k : Fin 4) (x y : Nat) : Bool :=
  reach c.w (c.S k) k x y &&
    allSlots.all fun j => j == k || !reach c.w (c.S j) j x y

def grid (w : Nat) : List (Nat × Nat) :=
  (List.range w).flatMap fun x => (List.range w).map fun y => (x, y)

def Cfg.priv (c : Cfg) (k : Fin 4) : List (Nat × Nat) :=
  (grid c.w).filter fun p => c.isPriv k p.1 p.2

/-- The private cells of all four slots. They are computed once, by `Cfg.mkPv`. -/
abbrev Pv := Fin 4 → List (Nat × Nat)

def Cfg.mkPv (c : Cfg) : Pv :=
  let a0 := c.priv 0; let a1 := c.priv 1; let a2 := c.priv 2; let a3 := c.priv 3
  fun k => match k with
    | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3

def inSq (S : Nat) (a b : Int) : Bool :=
  decide (0 ≤ a) && decide (a < S) && decide (0 ≤ b) && decide (b < S)

def bools : List Bool := [false, true]

/-- All motions that send a corner of the `w × w` square into a square of side `S`. -/
def motions (w S : Nat) : List Motion :=
  bools.flatMap fun sw => bools.flatMap fun fx => bools.flatMap fun fy =>
    (List.range (w + S)).flatMap fun (i : Nat) => (List.range (w + S)).map fun (j : Nat) =>
      { sw, fx, fy, dx := (i : Int) - w, dy := (j : Int) - w }

def idMotion : Motion := { sw := false, fx := false, fy := false, dx := 0, dy := 0 }

/-- The possible placements of slot `k`. -/
def Cfg.L (c : Cfg) (pv : Pv) (k : Fin 4) : List Motion :=
  if c.fixed k then [idMotion] else
  (motions c.w (c.S k)).filter fun m =>
    (!c.ids k || (!m.sw && !m.fx && !m.fy)) &&
    (pv k).all fun p => inSq (c.S k) (m.imgX c.w p.1 p.2) (m.imgY c.w p.1 p.2)

/-- The cell of the `w × w` square that `m` sends to `(a, b)`, if there is one. -/
def pre (w : Nat) (m : Motion) (a b : Int) : Option (Nat × Nat) :=
  let a' := a - m.dx
  let b' := b - m.dy
  let p := if m.sw then b' else a'
  let q := if m.sw then a' else b'
  let x := if m.fx then (w : Int) - 1 - p else p
  let y := if m.fy then (w : Int) - 1 - q else q
  if 0 ≤ x ∧ x < w ∧ 0 ≤ y ∧ y < w then some (x.toNat, y.toNat) else none

/-- No private cell of slot `l` lands on a private cell's image of slot `k`. -/
def Cfg.ptd (c : Cfg) (pv : Pv) (k l : Fin 4) (mk ml : Motion) : Bool :=
  (pv l).all fun p =>
    match pre c.w mk (ml.imgX c.w p.1 p.2) (ml.imgY c.w p.1 p.2) with
    | some r => !c.isPriv k r.1 r.2
    | none => true

/-- These motions reach all four corners of a square of side `S`. -/
def cornersOk (w S : Nat) (ms : List Motion) : Bool :=
  [((0 : Int), (0 : Int)), (0, (S : Int) - 1), ((S : Int) - 1, 0), ((S : Int) - 1, (S : Int) - 1)].all
    fun t => ms.any fun m => (pre w m t.1 t.2).isSome

/-! ### Propagation in the bipartite graph between source and target cells -/

def get (a : Array Bool) (i : Nat) : Bool := a.getD i false
def set (a : Array Bool) (i : Nat) : Array Bool := a.setIfInBounds i true

structure St where
  mS : Array Bool
  mT : Array Bool
  cnt : Nat

def St.add (s : St) (i j : Nat) : St :=
  { mS := set s.mS i, mT := set s.mT j, cnt := s.cnt + 1 }

/-- The number of a target cell. -/
def tcode (u v : Nat) (b : Bool) (a c : Nat) : Nat :=
  if b then a * u + c else u * u + a * v + c

/-- A problem: the four motions. -/
abbrev Q := Fin 4 → Motion

def srcCands (c : Cfg) (q : Q) (st : St) (x y : Nat) : List Nat :=
  (allSlots.filterMap fun k =>
    let a := (q k).imgX c.w x y
    let b := (q k).imgY c.w x y
    if inSq (c.S k) a b then some (tcode c.u c.v (c.side k) a.toNat b.toNat) else none).filter
      fun t => !get st.mT t

def srcStep (c : Cfg) (q : Q) (st : St) (x y : Nat) : Option St :=
  if get st.mS (x * c.w + y) then some st else
  match srcCands c q st x y with
  | [] => none
  | [t] => some (st.add (x * c.w + y) t)
  | _ => some st

def tgtCands (c : Cfg) (q : Q) (st : St) (b : Bool) (a e : Nat) : List (Nat × Nat) :=
  (allSlots.filterMap fun k =>
    if c.side k == b then pre c.w (q k) a e else none).filter
      fun r => !get st.mS (r.1 * c.w + r.2)

def tgtStep (c : Cfg) (q : Q) (st : St) (b : Bool) (a e : Nat) : Option St :=
  let t := tcode c.u c.v b a e
  if get st.mT t then some st else
  match tgtCands c q st b a e with
  | [] => none
  | [r] => some (st.add (r.1 * c.w + r.2) t)
  | _ => some st

def passS (c : Cfg) (q : Q) : List (Nat × Nat) → St → Option St
  | [], st => some st
  | p :: ps, st =>
    match srcStep c q st p.1 p.2 with
    | none => none
    | some st' => passS c q ps st'

def passT (c : Cfg) (q : Q) (b : Bool) : List (Nat × Nat) → St → Option St
  | [], st => some st
  | p :: ps, st =>
    match tgtStep c q st b p.1 p.2 with
    | none => none
    | some st' => passT c q b ps st'

/-- `true` means that propagation finds a contradiction. -/
def dead (c : Cfg) (q : Q) (gU gV : List (Nat × Nat)) (gW : List (Nat × Nat)) : Nat → St → Bool
  | 0, _ => false
  | n + 1, st =>
    match passS c q gW st with
    | none => true
    | some s1 =>
      match passT c q true gU s1 with
      | none => true
      | some s2 =>
        match passT c q false gV s2 with
        | none => true
        | some s3 => if s3.cnt == st.cnt then false else dead c q gU gV gW n s3

def St.init (c : Cfg) : St :=
  { mS := Array.replicate (c.w * c.w) false,
    mT := Array.replicate (c.u * c.u + c.v * c.v) false, cnt := 0 }

/-- Test a list in parallel. -/
def parAll {α : Type} (l : List α) (f : α → Bool) : Bool :=
  (l.map fun x => Task.spawn fun _ => f x).all fun t => t.get

theorem parAll_eq {α : Type} (l : List α) (f : α → Bool) : parAll l f = l.all f := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [parAll, List.map_cons, List.all_cons] at ih ⊢
    rw [ih]; rfl

/-- `a`, `b` go to one square and `c`, `d` go to the other one. -/
def Cfg.pairs (cf : Cfg) (pv : Pv) (a b : Fin 4) : List (Motion × Motion) :=
  let Lb := cf.L pv b
  (cf.L pv a).flatMap fun p => (Lb.filter fun r =>
    cf.ptd pv a b p r && cornersOk cf.w (cf.S a) [p, r]).map fun r => (p, r)

def mk22 (a b c : Fin 4) (pa pb pc pd : Motion) : Q :=
  fun k => if k = a then pa else if k = b then pb else if k = c then pc else pd

def check22 (cf : Cfg) (a b c d : Fin 4) : Bool :=
  let gW := grid cf.w; let gU := grid cf.u; let gV := grid cf.v
  let pv := cf.mkPv
  let P2 := cf.pairs pv c d
  parAll (cf.pairs pv a b) fun pq => P2.all fun rs =>
    dead cf (mk22 a b c pq.1 pq.2 rs.1 rs.2) gU gV gW (cf.w * cf.w) (St.init cf)

/-- Slot 0 is one whole square, and slots 1, 2, 3 go to the other square. -/
def check13 (cf : Cfg) : Bool :=
  let gW := grid cf.w; let gU := grid cf.u; let gV := grid cf.v
  let pv := cf.mkPv
  let L2 := cf.L pv 2; let L3 := cf.L pv 3
  parAll (cf.L pv 1) fun p1 =>
    let l2 := L2.filter fun p2 => cf.ptd pv 1 2 p1 p2
    let l3 := L3.filter fun p3 => cf.ptd pv 3 1 p3 p1
    l2.all fun p2 =>
      (l3.filter fun p3 => cf.ptd pv 3 2 p3 p2 && cornersOk cf.w (cf.S 1) [p1, p2, p3]).all fun p3 =>
        dead cf (mk22 0 1 2 idMotion p1 p2 p3) gU gV gW (cf.w * cf.w) (St.init cf)

def cfgDiag (u v w : Nat) : Cfg :=
  { u, v, w, side := fun k => k == 1 || k == 3, ids := fun k => k == 0 || k == 1, fixed := fun _ => false }
def cfgAdj (u v w : Nat) : Cfg :=
  { u, v, w, side := fun k => k == 2 || k == 3, ids := fun k => k == 0 || k == 2, fixed := fun _ => false }
/-- One piece fills the `u × u` square. -/
def cfgU (u v w : Nat) : Cfg :=
  { u, v, w, side := fun k => k == 0, ids := fun k => k == 1, fixed := fun k => k == 0 }
/-- One piece fills the `v × v` square. -/
def cfgV (u v w : Nat) : Cfg :=
  { u, v, w, side := fun k => k != 0, ids := fun k => k == 1, fixed := fun k => k == 0 }

/-- The whole search. -/
def checkAll (u v w : Nat) : Bool :=
  check22 (cfgDiag u v w) 0 2 1 3 && check22 (cfgAdj u v w) 0 1 2 3 &&
  check13 (cfgU u v w) && check13 (cfgV u v w)

end Ex89
