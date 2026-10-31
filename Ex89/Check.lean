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

/-! ### Propagation in the bipartite graph between source and target cells

Source cells have numbers below `nS`, and target cells have numbers below `nT`. The table `img`
of a placement sends a source cell `i` to `j + 1` when the placement moves `i` to the target cell
`j`, and it gives `0` when it moves `i` outside its target. The table `pre` is the inverse. -/

structure Tab where
  img : Array Nat
  pre : Array Nat

def get (a : Array Bool) (i : Nat) : Bool := a.getD i false
def set (a : Array Bool) (i : Nat) : Array Bool := a.setIfInBounds i true

structure St where
  mS : Array Bool
  mT : Array Bool
  cnt : Nat

def St.add (s : St) (i j : Nat) : St :=
  { mS := set s.mS i, mT := set s.mT j, cnt := s.cnt + 1 }

structure Q where
  t0 : Tab
  t1 : Tab
  t2 : Tab
  t3 : Tab

@[inline] def live (m : Array Bool) (c : Nat) : Bool := c != 0 && !get m (c - 1)

/-- Count the live candidates among four, and keep the last one. No list is allocated. -/
@[inline] def count4 (m : Array Bool) (a b c d : Nat) : Nat × Nat :=
  let (k, l) := if live m a then (1, a) else (0, 0)
  let (k, l) := if live m b then (k + 1, b) else (k, l)
  let (k, l) := if live m c then (k + 1, c) else (k, l)
  if live m d then (k + 1, d) else (k, l)

@[inline] def stepS (q : Q) (st : St) (i : Nat) : Option St :=
  if get st.mS i then some st else
  match count4 st.mT (q.t0.img.getD i 0) (q.t1.img.getD i 0) (q.t2.img.getD i 0) (q.t3.img.getD i 0) with
  | (0, _) => none
  | (1, c) => some (st.add i (c - 1))
  | _ => some st

@[inline] def stepT (q : Q) (st : St) (j : Nat) : Option St :=
  if get st.mT j then some st else
  match count4 st.mS (q.t0.pre.getD j 0) (q.t1.pre.getD j 0) (q.t2.pre.getD j 0) (q.t3.pre.getD j 0) with
  | (0, _) => none
  | (1, c) => some (st.add (c - 1) j)
  | _ => some st

def passS (q : Q) : List Nat → St → Option St
  | [], st => some st
  | i :: l, st =>
    match stepS q st i with
    | none => none
    | some st' => passS q l st'

def passT (q : Q) : List Nat → St → Option St
  | [], st => some st
  | j :: l, st =>
    match stepT q st j with
    | none => none
    | some st' => passT q l st'

/-- `true` means that propagation finds a contradiction. -/
def dead (q : Q) (rS rT : List Nat) : Nat → St → Bool
  | 0, _ => false
  | n + 1, st =>
    match passS q rS st with
    | none => true
    | some s1 =>
      match passT q rT s1 with
      | none => true
      | some s2 => if s2.cnt == st.cnt then false else dead q rS rT n s2

def St.init (nS nT : Nat) : St :=
  { mS := Array.replicate nS false, mT := Array.replicate nT false, cnt := 0 }

/-- The number of a target cell. -/
def tcode (u v : Nat) (b : Bool) (a c : Nat) : Nat :=
  if b then a * u + c else u * u + a * v + c

/-- The tables of motion `m` of slot `k`. -/
def Cfg.mkTab (c : Cfg) (k : Fin 4) (m : Motion) : Tab :=
  let S := c.S k
  let b := c.side k
  { img := Array.ofFn (n := c.w * c.w) fun i =>
      let x := i.val / c.w; let y := i.val % c.w
      let A := m.imgX c.w x y; let B := m.imgY c.w x y
      if inSq S A B then tcode c.u c.v b A.toNat B.toNat + 1 else 0,
    pre := Array.ofFn (n := c.u * c.u + c.v * c.v) fun j =>
      let inU := decide (j.val < c.u * c.u)
      if inU == b then
        let j' := if b then j.val else j.val - c.u * c.u
        match pre c.w m ((j' / S : Nat) : Int) ((j' % S : Nat) : Int) with
        | some r => r.1 * c.w + r.2 + 1
        | none => 0
      else 0 }

/-- A placement with its tables. -/
structure Pack where
  m : Motion
  t : Tab

/-- Private cells, in table form: the numbers of the private cells of each slot, and a table
that says whether a cell is private to a slot. -/
structure PT where
  codes : Fin 4 → List Nat
  isP : Fin 4 → Array Bool

def Cfg.privTab (c : Cfg) (k : Fin 4) : Array Bool :=
  Array.ofFn (n := c.w * c.w) fun i => c.isPriv k (i.val / c.w) (i.val % c.w)

def Cfg.mkPT (c : Cfg) (pv : Pv) : PT :=
  let c0 := (pv 0).map fun p => p.1 * c.w + p.2
  let c1 := (pv 1).map fun p => p.1 * c.w + p.2
  let c2 := (pv 2).map fun p => p.1 * c.w + p.2
  let c3 := (pv 3).map fun p => p.1 * c.w + p.2
  let t0 := c.privTab 0; let t1 := c.privTab 1; let t2 := c.privTab 2; let t3 := c.privTab 3
  { codes := fun k => match k with | 0 => c0 | 1 => c1 | 2 => c2 | 3 => c3,
    isP := fun k => match k with | 0 => t0 | 1 => t1 | 2 => t2 | 3 => t3 }

/-- No private cell of slot `l` lands on the image of a private cell of slot `k`. -/
def ptd (pt : PT) (k l : Fin 4) (tk tl : Tab) : Bool :=
  let isK := pt.isP k
  (pt.codes l).all fun i =>
    let c := tl.img.getD i 0
    c == 0 || (let s := tk.pre.getD (c - 1) 0; s == 0 || !isK.getD (s - 1) false)

/-- The numbers of the four corners of the target square of slot `k`. -/
def Cfg.tcorners (c : Cfg) (k : Fin 4) : List Nat :=
  let S := c.S k
  let b := c.side k
  [tcode c.u c.v b 0 0, tcode c.u c.v b 0 (S - 1), tcode c.u c.v b (S - 1) 0, tcode c.u c.v b (S - 1) (S - 1)]

/-- These placements reach all four corners. -/
def cornersOk (cs : List Nat) (ms : List Tab) : Bool :=
  cs.all fun t => ms.any fun m => m.pre.getD t 0 != 0

/-- Test a list in parallel. -/
def parAll {α : Type} (l : List α) (f : α → Bool) : Bool :=
  (l.map fun x => Task.spawn fun _ => f x).all fun t => t.get

theorem parAll_eq {α : Type} (l : List α) (f : α → Bool) : parAll l f = l.all f := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [parAll, List.map_cons, List.all_cons] at ih ⊢
    rw [ih]; rfl

/-- Apply a function to a list in parallel. -/
def parMap {α β : Type} (l : List α) (f : α → β) : List β :=
  (l.map fun x => Task.spawn fun _ => f x).map fun t => t.get

theorem parMap_eq {α β : Type} (l : List α) (f : α → β) : parMap l f = l.map f := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [parMap, List.map_cons] at ih ⊢
    rw [ih]; rfl

def Cfg.packs (cf : Cfg) (pv : Pv) (k : Fin 4) : List Pack :=
  parMap (cf.L pv k) fun m => { m, t := cf.mkTab k m }

/-- `a`, `b` go to one square and `c`, `d` go to the other one. -/
def Cfg.pairs (cf : Cfg) (pv : Pv) (pt : PT) (a b : Fin 4) : List (Pack × Pack) :=
  let Lb := cf.packs pv b
  let cs := cf.tcorners a
  (cf.packs pv a).flatMap fun p => (Lb.filter fun r =>
    ptd pt a b p.t r.t && cornersOk cs [p.t, r.t]).map fun r => (p, r)

def Cfg.nS (cf : Cfg) : Nat := cf.w * cf.w
def Cfg.nT (cf : Cfg) : Nat := cf.u * cf.u + cf.v * cf.v

def check22 (cf : Cfg) (a b c d : Fin 4) : Bool :=
  let rS := List.range cf.nS; let rT := List.range cf.nT
  let pv := cf.mkPv
  let pt := cf.mkPT pv
  let tP2 := Task.spawn fun _ => cf.pairs pv pt c d
  let P1 := cf.pairs pv pt a b
  let P2 := tP2.get
  parAll P1 fun pq => P2.all fun rs =>
    dead ⟨pq.1.t, pq.2.t, rs.1.t, rs.2.t⟩ rS rT cf.nS (St.init cf.nS cf.nT)

/-- A number for a motion, used to mark motions in a table. Two motions with the same number would
only make the search test more cases, so the correctness of the search does not depend on it. -/
def motionId (w : Nat) (m : Motion) : Nat :=
  ((m.dx + w).toNat * (2 * w) + (m.dy + w).toNat) * 8 +
    (if m.sw then 4 else 0) + (if m.fx then 2 else 0) + (if m.fy then 1 else 0)

/-- Mark the motions of a list. -/
def maskOf (n w : Nat) (l : List Pack) : Array Bool :=
  l.foldl (fun a p => set a (motionId w p.m % n)) (Array.replicate n false)

/-- Slot 0 is one whole square, and slots 1, 2, 3 go to the other square. -/
def check13 (cf : Cfg) : Bool :=
  let rS := List.range cf.nS; let rT := List.range cf.nT
  let pv := cf.mkPv
  let t0 := cf.mkTab 0 idMotion
  let L2 := cf.packs pv 2; let L3 := cf.packs pv 3
  let n := 32 * cf.w * cf.w + 8
  let pt := cf.mkPT pv
  let cs := cf.tcorners 1
  let P23 := parMap L2 fun p2 => (p2, L3.filter fun p3 => ptd pt 3 2 p3.t p2.t)
  parAll (cf.packs pv 1) fun p1 =>
    let mask := maskOf n cf.w (L3.filter fun p3 => ptd pt 3 1 p3.t p1.t)
    P23.all fun e =>
      !ptd pt 1 2 p1.t e.1.t ||
      e.2.all fun p3 =>
        !get mask (motionId cf.w p3.m % n) ||
        !cornersOk cs [p1.t, e.1.t, p3.t] ||
        dead ⟨t0, p1.t, e.1.t, p3.t⟩ rS rT cf.nS (St.init cf.nS cf.nT)

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

/-- One of the four cases. -/
def checkCase (u v w : Nat) : Nat → Bool
  | 0 => check22 (cfgDiag u v w) 0 2 1 3
  | 1 => check22 (cfgAdj u v w) 0 1 2 3
  | 2 => check13 (cfgU u v w)
  | _ => check13 (cfgV u v w)

/-- Test a list in parallel, with one dedicated thread for each element. -/
def parAllD {α : Type} (l : List α) (f : α → Bool) : Bool :=
  (l.map fun x => Task.spawn (prio := Task.Priority.dedicated) fun _ => f x).all fun t => t.get

theorem parAllD_eq {α : Type} (l : List α) (f : α → Bool) : parAllD l f = l.all f := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [parAllD, List.map_cons, List.all_cons] at ih ⊢
    rw [ih]; rfl

/-- The whole search. The four cases run at the same time. -/
def checkAll (u v w : Nat) : Bool :=
  parAllD [0, 1, 2, 3] (checkCase u v w)

theorem checkAll_eq (u v w : Nat) : checkAll u v w =
    (check22 (cfgDiag u v w) 0 2 1 3 && check22 (cfgAdj u v w) 0 1 2 3 &&
     check13 (cfgU u v w) && check13 (cfgV u v w)) := by
  simp [checkAll, parAllD_eq, checkCase, Bool.and_assoc]

end Ex89
