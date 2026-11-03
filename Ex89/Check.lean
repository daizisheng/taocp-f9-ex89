import Ex89.Model
/-!
The search program. It rebuilds the search of `proof-20-21-29` for any `(u, v, w)`.
Each corner of the `w × w` square lies in its own piece, called slot `k` below.
-/
namespace Ex89

unsafe def persistImpl {α : Type} (a : α) : α := unsafeBaseIO (Runtime.markPersistent a)

/-- The identity function. In the compiled program the value is also marked as persistent: its
reference count is never updated again, so that the threads do not fight over one cache line.
The proofs see only the identity. -/
@[implemented_by persistImpl] def persist {α : Type} (a : α) : α := a

theorem persist_eq {α : Type} (a : α) : persist a = a := rfl

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

/-- The four lists. They are kept apart from `pvOf`, because the compiler would turn a definition of
`Pv` with `let`s into a function that computes the lists again at each call. -/
def Cfg.pv4 (c : Cfg) : List (Nat × Nat) × List (Nat × Nat) × List (Nat × Nat) × List (Nat × Nat) :=
  (c.priv 0, c.priv 1, c.priv 2, c.priv 3)

def pvOf (a : List (Nat × Nat) × List (Nat × Nat) × List (Nat × Nat) × List (Nat × Nat)) : Pv :=
  fun k => match k with
    | 0 => a.1 | 1 => a.2.1 | 2 => a.2.2.1 | 3 => a.2.2.2

def Cfg.mkPv (c : Cfg) : Pv := pvOf c.pv4

def inSq (S : Nat) (a b : Int) : Bool :=
  decide (0 ≤ a) && decide (a < S) && decide (0 ≤ b) && decide (b < S)

def bools : List Bool := [false, true]

/-- All motions that send a corner of the `w × w` square into a square of side `S`. -/
def motions (w S : Nat) : List Motion :=
  bools.flatMap fun sw => bools.flatMap fun fx => bools.flatMap fun fy =>
    (List.range (w + S)).flatMap fun (i : Nat) => (List.range (w + S)).map fun (j : Nat) =>
      { sw, fx, fy, dx := (i : Int) - w, dy := (j : Int) - w }

def idMotion : Motion := { sw := false, fx := false, fy := false, dx := 0, dy := 0 }

/-- Cut a list into pieces of length `n`. -/
def chunksF {α : Type} (n : Nat) : Nat → List α → List (List α)
  | 0, l => [l]
  | f + 1, l =>
    match l with
    | [] => []
    | a :: t => (a :: t).take n :: chunksF n f ((a :: t).drop n)

theorem flatten_chunksF {α : Type} (n f : Nat) (l : List α) : (chunksF n f l).flatten = l := by
  induction f generalizing l with
  | zero => simp [chunksF]
  | succ f ih =>
    cases l with
    | nil => rfl
    | cons a t =>
      simp only [chunksF, List.flatten_cons, ih, List.take_append_drop]

/-- Filter a list in parallel, by pieces. -/
def parFilterM (p : Motion → Bool) (l : List Motion) : List Motion :=
  (((chunksF 512 l.length l).map fun c => Task.spawn fun _ => c.filter p).map Task.get).flatten

theorem filter_flatten_eq (p : Motion → Bool) (ch : List (List Motion)) :
    (ch.map (List.filter p)).flatten = ch.flatten.filter p := by
  induction ch with
  | nil => rfl
  | cons c ch ih => simp only [List.map_cons, List.flatten_cons, List.filter_append, ih]

theorem parFilterM_eq (p : Motion → Bool) (l : List Motion) : parFilterM p l = l.filter p := by
  have e : ∀ ch : List (List Motion), (ch.map fun c => Task.spawn fun _ => c.filter p).map Task.get =
      ch.map (List.filter p) := by
    intro ch
    induction ch with
    | nil => rfl
    | cons c ch ih => simp only [List.map_cons, ih]; rfl
  unfold parFilterM
  rw [e (chunksF 512 l.length l), filter_flatten_eq, flatten_chunksF]

/-- The possible placements of slot `k`. -/
def Cfg.L (c : Cfg) (pv : Pv) (k : Fin 4) : List Motion :=
  if c.fixed k then [idMotion] else
  parFilterM (fun m =>
    (!c.ids k || (!m.sw && !m.fx && !m.fy)) &&
    (pv k).all fun p => inSq (c.S k) (m.imgX c.w p.1 p.2) (m.imgY c.w p.1 p.2))
    (motions c.w (c.S k))

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
  (parMap (cf.packs pv a) fun p => (Lb.filter fun r =>
    ptd pt a b p.t r.t && cornersOk cs [p.t, r.t]).map fun r => (p, r)).flatten

theorem Cfg.pairs_eq (cf : Cfg) (pv : Pv) (pt : PT) (a b : Fin 4) :
    cf.pairs pv pt a b = (cf.packs pv a).flatMap fun p => ((cf.packs pv b).filter fun r =>
      ptd pt a b p.t r.t && cornersOk (cf.tcorners a) [p.t, r.t]).map fun r => (p, r) := by
  simp only [Cfg.pairs, parMap_eq, List.flatMap_def]

def Cfg.nS (cf : Cfg) : Nat := cf.w * cf.w
def Cfg.nT (cf : Cfg) : Nat := cf.u * cf.u + cf.v * cf.v

/-- A number for a motion, used to mark motions in a table. Two motions with the same number would
only make the search test more cases, so the correctness of the search does not depend on it. -/
def motionId (w : Nat) (m : Motion) : Nat :=
  ((m.dx + w).toNat * (2 * w) + (m.dy + w).toNat) * 8 +
    (if m.sw then 4 else 0) + (if m.fx then 2 else 0) + (if m.fy then 1 else 0)

/-- Mark the motions of a list. -/
def maskOf (n w : Nat) (l : List Pack) : Array Bool :=
  l.foldl (fun a p => set a (motionId w p.m % n)) (Array.replicate n false)

/-! ### The cover test

Every source cell has an image and every target cell has a preimage, under one of the four motions.
A number `e < n` stands for source cell `e`, and a number `n ≤ e` for target cell `e - n`. -/

/-- The motion with table `t` reaches `e`. -/
def hitE (n : Nat) (t : Tab) (e : Nat) : Bool :=
  if e < n then t.img.getD e 0 != 0 else t.pre.getD (e - n) 0 != 0

/-- Slot 0 fills its square with the identity, so the cells of that square belong to slot 0. Another
motion can only use the other cells: it reaches a target cell only through one of them. -/
def hitL (n : Nat) (t0 t : Tab) (e : Nat) : Bool :=
  if e < n then t.img.getD e 0 != 0
  else
    let p := t.pre.getD (e - n) 0
    p != 0 && t0.img.getD (p - 1) 0 == 0

/-- No motion among these three reaches `e`. -/
def uncov (n N : Nat) (t0 t1 t3 : Tab) (e : Nat) : Bool :=
  decide (e < N) && !hitE n t0 e && !hitL n t0 t1 e && !hitL n t0 t3 e

/-- No motion among these four reaches `e`. -/
def missQ (n N : Nat) (t0 t1 t2 t3 : Tab) (e : Nat) : Bool :=
  uncov n N t0 t1 t3 e && !hitL n t0 t2 e

/-- The first number that the three placements do not reach, found in the words from the top. Only
used to choose a number, which is then checked by `missQ`. -/
def firstMiss (fw a b c : Array Nat) : Nat → Option Nat
  | 0 => none
  | i + 1 =>
    let f := fw.getD i 0
    let w := f ^^^ (f &&& (a.getD i 0 ||| b.getD i 0 ||| c.getD i 0))
    if w == 0 then firstMiss fw a b c i else some (i * 60 + w.log2)

/-- A number that no motion reaches, if `firstMiss` finds one. -/
def witQ (n N : Nat) (t0 t1 t2 t3 : Tab) (e : Option Nat) : Bool :=
  match e with
  | none => false
  | some e => missQ n N t0 t1 t2 t3 e

/-- The numbers below `N` that satisfy `f`, in words of 60 bits. -/
def wordsOf (N : Nat) (f : Nat → Bool) : Array Nat :=
  Array.ofFn (n := N / 60 + 1) fun h => (List.range 60).foldl (fun c i =>
    if decide (h.val * 60 + i < N) && f (h.val * 60 + i) then c ||| (1 <<< i) else c) 0

/-- A placement with the numbers that it reaches, as words. These are only used to choose numbers,
which are then checked. -/
structure PB where
  p : Pack
  w : Array Nat

def mkPB (N : Nat) (p : Pack) (f : Nat → Bool) : PB := ⟨p, wordsOf N f⟩

/-! ### Pair forcing

Two motions must fill one square by themselves. This forces many cells to belong to the pair. The
result for a pair is `F`, cells that must belong to it, and `AL`, cells that can belong to it. For the
two pairs of a dissection, `F` and `F'` are disjoint, and `AL` and `AL'` together are everything. -/

/-- The number of the edge from cell `p` to motion `s` of the pair. -/
@[inline] def eIdx (p : Nat) (s : Bool) : Nat := p * 2 + (if s then 1 else 0)

@[inline] def tabS (t0 t1 : Tab) (s : Bool) : Tab := if s then t1 else t0

def clr (a : Array Bool) (i : Nat) : Array Bool := a.setIfInBounds i false

structure PFS where
  alive : Array Bool
  forced : Array Bool

/-- Cell `p` certainly belongs to motion `s`: it does not belong to the other one. -/
def pfForce (st : PFS) (p : Nat) (s : Bool) : PFS :=
  { alive := clr st.alive (eIdx p (!s)), forced := set st.forced p }

/-- A target cell has to be filled by one of its two possible cells. -/
def pfT (t0 t1 : Tab) (st : PFS) (o : Nat) : Option PFS :=
  let p0 := t0.pre.getD o 0
  let p1 := t1.pre.getD o 0
  let c0 := p0 != 0 && get st.alive (eIdx (p0 - 1) false)
  let c1 := p1 != 0 && get st.alive (eIdx (p1 - 1) true)
  if c0 then (if c1 then some st else some (pfForce st (p0 - 1) false))
  else (if c1 then some (pfForce st (p1 - 1) true) else none)

/-- Cell `p` belongs to motion `s`, so nothing else goes to its image. -/
def pfOther (t0 t1 : Tab) (st : PFS) (p : Nat) (s : Bool) : PFS :=
  let t := (tabS t0 t1 s).img.getD p 0
  let p' := (tabS t0 t1 (!s)).pre.getD (t - 1) 0
  if t != 0 && p' != 0 && p' - 1 != p && (tabS t0 t1 (!s)).img.getD (p' - 1) 0 == t then
    { st with alive := clr st.alive (eIdx (p' - 1) (!s)) }
  else st

/-- A forced cell needs one of its two motions. -/
def pfS (t0 t1 : Tab) (st : PFS) (p : Nat) : Option PFS :=
  if !get st.forced p then some st else
  let c0 := get st.alive (eIdx p false)
  let c1 := get st.alive (eIdx p true)
  if c0 then (if c1 then some st else some (pfOther t0 t1 st p false))
  else (if c1 then some (pfOther t0 t1 st p true) else none)

def pfPassT (t0 t1 : Tab) : List Nat → PFS → Option PFS
  | [], st => some st
  | o :: l, st =>
    match pfT t0 t1 st o with
    | none => none
    | some st' => pfPassT t0 t1 l st'

def pfPassS (t0 t1 : Tab) : List Nat → PFS → Option PFS
  | [], st => some st
  | p :: l, st =>
    match pfS t0 t1 st p with
    | none => none
    | some st' => pfPassS t0 t1 l st'

def pfCount (st : PFS) : Nat :=
  st.alive.foldl (fun c b => if b then c else c + 1) 0 + st.forced.foldl (fun c b => if b then c + 1 else c) 0

def pfLoop (t0 t1 : Tab) (os rS : List Nat) : Nat → PFS → Option PFS
  | 0, st => some st
  | n + 1, st =>
    match pfPassT t0 t1 os st with
    | none => none
    | some s1 =>
      match pfPassS t0 t1 rS s1 with
      | none => none
      | some s2 => if pfCount s2 == pfCount st then some s2 else pfLoop t0 t1 os rS n s2

/-- The numbers `p` below `2 ^ d` such that `lo + p` satisfies `f`, as the bits of a number. Halving
keeps most of the work on small numbers. -/
def bitsD (f : Nat → Bool) : Nat → Nat → Nat
  | 0, lo => if f lo then 1 else 0
  | d + 1, lo => bitsD f d lo ||| (bitsD f d (lo + 2 ^ d) <<< 2 ^ d)

/-- The set of the numbers below `n` that satisfy `f`, as the bits of a number. -/
def bitsUpTo (f : Nat → Bool) (n : Nat) : Nat :=
  bitsD (fun p => decide (p < n) && f p) (n.log2 + 1) 0

/-- A pair with its two sets. -/
structure PFR where
  pq : Pack × Pack
  F : Nat
  AL : Nat

/-- Cell `p` is private to a slot other than `k`. -/
def otherP (pt : PT) (k : Fin 4) (p : Nat) : Bool :=
  allSlots.any fun j => j != k && (pt.isP j).getD p false

/-- The table of `otherP`, computed once for all pairs. -/
def otherTab (n : Nat) (pt : PT) (k : Fin 4) : Array Bool :=
  Array.ofFn (n := n) fun p => otherP pt k p.val

def pfAlive0 (n : Nat) (oa ob : Array Bool) (t0 t1 : Tab) : Array Bool :=
  Array.ofFn (n := 2 * n) fun e =>
    (tabS t0 t1 (e.val % 2 == 1)).img.getD (e.val / 2) 0 != 0 &&
      !(if e.val % 2 == 1 then ob else oa).getD (e.val / 2) false

def pfForced0 (n : Nat) (pt : PT) (ka kb : Fin 4) : Array Bool :=
  Array.ofFn (n := n) fun p => (pt.isP ka).getD p.val false || (pt.isP kb).getD p.val false

/-- The test for one pair. `none` means that this pair is impossible. -/
def pairForce (n : Nat) (pt : PT) (ka kb : Fin 4) (oa ob : Array Bool) (os rS : List Nat)
    (pq : Pack × Pack) : Option PFR :=
  let t0 := pq.1.t
  let t1 := pq.2.t
  match pfLoop t0 t1 os rS (4 * n) ⟨pfAlive0 n oa ob t0 t1, pfForced0 n pt ka kb⟩ with
  | none => none
  | some st => some
    { pq,
      F := bitsUpTo (get st.forced) n,
      AL := bitsUpTo (fun p => get st.alive (eIdx p false) || get st.alive (eIdx p true)) n }

/-- `a`, `b` go to one square and `c`, `d` go to the other one. The function `ord` gives the order of
the tables, and `test` is the test for one quadruple of placements. -/
def check22G (cf : Cfg) (a b c d : Fin 4) (ord : Tab → Tab → Tab → Tab → Q)
    (test : Cfg → Q → List Nat → List Nat → Bool) : Bool :=
  let cf := persist cf
  let n := cf.nS
  let rS := persist (List.range cf.nS); let rT := persist (List.range cf.nT)
  let pv := pvOf (persist cf.pv4)
  let pt := persist (cf.mkPT pv)
  let os1 := persist (rT.filter fun j => decide (j < cf.u * cf.u) == cf.side a)
  let os2 := persist (rT.filter fun j => decide (j < cf.u * cf.u) == cf.side c)
  let full := persist (bitsUpTo (fun _ => true) n)
  let oa := persist (otherTab n pt a); let ob := persist (otherTab n pt b)
  let oc := persist (otherTab n pt c); let od := persist (otherTab n pt d)
  let tP2 := Task.spawn fun _ => (parMap (cf.pairs pv pt c d) (pairForce n pt c d oc od os2 rS)).filterMap id
  let P1 := persist ((parMap (cf.pairs pv pt a b) (pairForce n pt a b oa ob os1 rS)).filterMap id)
  let P2 := persist tP2.get
  parAll P1 fun x => P2.all fun y =>
    (x.F &&& y.F) != 0 || (x.AL ||| y.AL) != full ||
    test cf (ord x.pq.1.t x.pq.2.t y.pq.1.t y.pq.2.t) rS rT

def deadP (cf : Cfg) (q : Q) (rS rT : List Nat) : Bool :=
  dead q rS rT cf.nS (St.init cf.nS cf.nT)

def check22 (cf : Cfg) (a b c d : Fin 4) : Bool :=
  check22G cf a b c d (fun x y z t => ⟨x, y, z, t⟩) deadP

/-- The indices of the elements of `A` that satisfy `f`, as the bits of a number. -/
def colBits (A : Array PB) (f : PB → Bool) : Nat :=
  bitsUpTo (fun j => match A[j]? with | some p => f p | none => false) A.size

/-- A number that no motion of the first two reaches cuts down the third placements. Each number is
checked, so nothing is assumed about the choice of the numbers. -/
def narrowOne (n N : Nat) (t0 t1 t3 : Tab) (cols : Array Nat) (al e : Nat) : Nat :=
  if uncov n N t0 t1 t3 e then al &&& cols.getD e 0 else al

/-- All numbers of one word. -/
def narrowWord (n N : Nat) (t0 t1 t3 : Tab) (cols : Array Nat) : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, al => al
  | k + 1, b, w, al =>
    if al == 0 || w == 0 then al
    else
      let h := w.log2
      narrowWord n N t0 t1 t3 cols k b (w ^^^ (1 <<< h)) (narrowOne n N t0 t1 t3 cols al (b + h))

/-- All words, from the top: the target cells have the highest numbers, and they kill the most. -/
def narrowW (n N : Nat) (t0 t1 t3 : Tab) (cols fw a c : Array Nat) : Nat → Nat → Nat
  | 0, al => al
  | i + 1, al =>
    if al == 0 then al
    else
      let f := fw.getD i 0
      let w := f ^^^ (f &&& (a.getD i 0 ||| c.getD i 0))
      narrowW n N t0 t1 t3 cols fw a c i (narrowWord n N t0 t1 t3 cols 3 (i * 60) w al)

/-! ### Collisions

Two cells `c1` and `c3` are possible only for the motions of slots 1 and 3, in this order, and they
have the same image. Then slot 2 must reach one of them. In the same way, two target cells that only
slots 1 and 3 can reach, in this order, from the same cell: slot 2 must reach one of them. -/

/-- The source form of a collision. -/
def collS (n : Nat) (t0 t1 t3 : Tab) (c1 c3 : Nat) : Bool :=
  decide (c1 < n) && decide (c3 < n) && c1 != c3 && t0.img.getD c1 0 == 0 && t0.img.getD c3 0 == 0 &&
  t1.img.getD c1 0 != 0 && t3.img.getD c1 0 == 0 && t3.img.getD c3 0 != 0 && t1.img.getD c3 0 == 0 &&
  t1.img.getD c1 0 == t3.img.getD c3 0

/-- The target form of a collision. -/
def collT (n N : Nat) (t0 t1 t3 : Tab) (e1 e3 : Nat) : Bool :=
  decide (n ≤ e1) && decide (n ≤ e3) && decide (e1 < N) && decide (e3 < N) &&
  !hitE n t0 e1 && !hitE n t0 e3 && !hitL n t0 t3 e1 && !hitL n t0 t1 e3 &&
  t1.pre.getD (e1 - n) 0 != 0 && t1.pre.getD (e1 - n) 0 == t3.pre.getD (e3 - n) 0

def collOK (n N : Nat) (t0 t1 t3 : Tab) (e : Nat × Nat) : Bool :=
  collS n t0 t1 t3 e.1 e.2 || collT n N t0 t1 t3 e.1 e.2

/-- Cut down the third placements by one collision. -/
def applyColl (n N : Nat) (t0 t1 t3 : Tab) (cols : Array Nat) (al : Nat) (e : Nat × Nat) : Nat :=
  if al != 0 && collOK n N t0 t1 t3 e then al &&& (cols.getD e.1 0 ||| cols.getD e.2 0) else al

/-- All collisions of two motions. Nothing is assumed about this list. -/
def collList (n m : Nat) (t0 t1 t3 : Tab) : List (Nat × Nat) := Id.run do
  let mut mk := Array.replicate (m + 1) 0
  let mut out : List (Nat × Nat) := []
  for c in [0:n] do
    if t0.img.getD c 0 != 0 then continue
    let a := t1.img.getD c 0
    let b := t3.img.getD c 0
    if a != 0 && b == 0 then mk := mk.setIfInBounds a (c + 1)
    if a != 0 && b != 0 && a != b then out := (n + a - 1, n + b - 1) :: out
  for c in [0:n] do
    if t0.img.getD c 0 != 0 then continue
    let a := t1.img.getD c 0
    let b := t3.img.getD c 0
    if a == 0 && b != 0 then
      let d := mk.getD b 0
      if d != 0 && d - 1 != c then out := (d - 1, c) :: out
  return out

/-- `f` holds on all bits of `r`. Out of fuel, the answer is `false`. -/
def allBits (f : Nat → Bool) : Nat → Nat → Bool
  | 0, r => r == 0
  | k + 1, r =>
    if r == 0 then true
    else
      let e := r.log2
      f e && allBits f k (r ^^^ (1 <<< e))

/-- Slot 0 is one whole square, and slots 1, 2, 3 go to the other square. The possible placements of
slot 2 are kept as the bits of a number. They must fit with the placements of slots 1 and 3, and must
reach each number that those two do not reach. -/
def check13G (cf : Cfg) (test : Cfg → Q → List Nat → List Nat → Bool) : Bool :=
  let cf := persist cf
  let n := cf.nS
  let N := cf.nS + cf.nT
  let rS := persist (List.range cf.nS); let rT := persist (List.range cf.nT)
  let pv := pvOf (persist cf.pv4)
  let t0 := persist (cf.mkTab 0 idMotion)
  let bit : Pack → PB := fun p => mkPB N p (hitL n t0 p.t)
  let A := persist (parMap (cf.packs pv 2) bit).toArray
  let L3P := persist (cf.packs pv 3)
  let sz := 32 * cf.w * cf.w + 8
  let pt := persist (cf.mkPT pv)
  let cs := persist (cf.tcorners 1)
  let cols := persist (parMap (List.range N) fun e => colBits A fun p => hitL n t0 p.p.t e).toArray
  let fw := persist (wordsOf N fun e => !hitE n t0 e)
  let L3 := persist (parMap L3P fun p3 => (bit p3, colBits A fun p => ptd pt 3 2 p3.t p.p.t))
  let P1M := persist (parMap (cf.packs pv 1) fun p1 =>
    (bit p1, colBits A (fun p => ptd pt 1 2 p1.t p.p.t),
      maskOf sz cf.w (L3P.filter fun p3 => ptd pt 3 1 p3.t p1.t)))
  let CH := persist (chunksF 256 L3.length L3)
  -- One task for each first piece and each short part of the third pieces: the amount of work
  -- depends very much on the first piece, so one task for each first piece would be unbalanced.
  parAll (P1M.flatMap fun pm => CH.map fun ch => (pm, ch)) fun x =>
    let b1 := x.1.1
    let c1 := x.1.2.1
    let mask := x.1.2.2
    x.2.all fun y =>
      let b3 := y.1
      !get mask (motionId cf.w b3.p.m % sz) ||
      allBits (fun j => match A[j]? with
        | none => true
        | some b2 =>
          witQ n N t0 b1.p.t b2.p.t b3.p.t (firstMiss fw b1.w b2.w b3.w (N / 60 + 1)) ||
          !cornersOk cs [b1.p.t, b2.p.t, b3.p.t] ||
          test cf ⟨t0, b1.p.t, b2.p.t, b3.p.t⟩ rS rT)
        (A.size + 1)
        (let al := narrowW n N t0 b1.p.t b3.p.t cols fw b1.w b3.w (N / 60 + 1) (c1 &&& y.2)
         if al == 0 then 0 else
         (collList n cf.nT t0 b1.p.t b3.p.t).foldl (applyColl n N t0 b1.p.t b3.p.t cols) al)

def check13 (cf : Cfg) : Bool := check13G cf deadP

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
