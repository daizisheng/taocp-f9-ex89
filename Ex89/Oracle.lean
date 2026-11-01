import Ex89.Match
/-!
The oracle of `Ex89.Match`: a matching, strong components, breadth-first search and cut vertices.
Nothing is proved about this file, and nothing needs to be. Its answers are only hints that are
checked by `applyPot`, `applyReach` and `applyCut`, so a bug here can only make the test weaker.
-/
namespace Ex89

@[inline] def nget (a : Array Nat) (i : Nat) : Nat := a.getD i 0
@[inline] def nset (a : Array Nat) (i v : Nat) : Array Nat := a.setIfInBounds i v

/-! ### Matching -/

structure MS where
  mW : Array Nat
  mT : Array Nat
  vis : Array Nat
  stamp : Nat

mutual
  /-- Try to give source cell `i` a target, starting with slot `k`. -/
  partial def augK (q : Q) (a : Array Bool) (i k : Nat) (s : MS) : Bool × MS :=
    if k ≥ 4 then (false, s)
    else if ok a i k then
      let c := imgAt q i k
      if c == 0 then augK q a i (k + 1) s
      else
        let t := c - 1
        if nget s.vis t == s.stamp then augK q a i (k + 1) s
        else
          let s := { s with vis := nset s.vis t s.stamp }
          let o := nget s.mT t
          let (r, s) := if o == 0 then (true, s) else augK q a (o - 1) 0 s
          if r then (true, { s with mT := nset s.mT t (i + 1), mW := nset s.mW i (t + 1) })
          else augK q a i (k + 1) s
    else augK q a i (k + 1) s
end

/-- The first unmatched cell, if the search for a perfect matching fails. -/
partial def matchAll (x : Ctx) (q : Q) (a : Array Bool) (i : Nat) (s : MS) : Option Nat × MS :=
  if i ≥ x.n then (none, s)
  else if nget s.mW i != 0 then matchAll x q a (i + 1) s
  else
    let s := { s with stamp := s.stamp + 1 }
    let (r, s) := augK q a i 0 s
    if r then matchAll x q a (i + 1) s else (some i, s)

/-! ### Strong components of the graph on source cells: `i → j` when `i` may take the target of `j` -/

structure TS where
  idx : Array Nat
  low : Array Nat
  onS : Array Bool
  st : List Nat
  cnt : Nat
  comp : Array Nat
  nc : Nat

mutual
  partial def tjK (q : Q) (a : Array Bool) (mT : Array Nat) (i k : Nat) (s : TS) : TS :=
    if k ≥ 4 then s
    else if !ok a i k then tjK q a mT i (k + 1) s
    else
      let c := imgAt q i k
      let o := if c == 0 then 0 else nget mT (c - 1)
      if o == 0 || o - 1 == i then tjK q a mT i (k + 1) s
      else
        let j := o - 1
        if nget s.idx j == 0 then
          let s := tjV q a mT j s
          tjK q a mT i (k + 1) { s with low := nset s.low i (min (nget s.low i) (nget s.low j)) }
        else if get s.onS j then
          tjK q a mT i (k + 1) { s with low := nset s.low i (min (nget s.low i) (nget s.idx j)) }
        else tjK q a mT i (k + 1) s

  partial def tjV (q : Q) (a : Array Bool) (mT : Array Nat) (i : Nat) (s : TS) : TS :=
    let n := s.cnt + 1
    let s := { s with idx := nset s.idx i n, low := nset s.low i n, cnt := n,
                      st := i :: s.st, onS := s.onS.setIfInBounds i true }
    let s := tjK q a mT i 0 s
    if nget s.low i == nget s.idx i then tjPop i s else s

  partial def tjPop (i : Nat) (s : TS) : TS :=
    match s.st with
    | [] => s
    | j :: l =>
      let s := { s with st := l, onS := s.onS.setIfInBounds j false, comp := nset s.comp j s.nc }
      if j == i then { s with nc := s.nc + 1 } else tjPop i s
end

partial def tjAll (x : Ctx) (q : Q) (a : Array Bool) (mT : Array Nat) (i : Nat) (s : TS) : TS :=
  if i ≥ x.n then s
  else if nget s.idx i != 0 then tjAll x q a mT (i + 1) s
  else tjAll x q a mT (i + 1) (tjV q a mT i s)

/-- The potentials: from a set that violates Hall's condition, or from the strong components. -/
def potOf (x : Ctx) (q : Q) (a : Array Bool) : Array Nat × Array Nat :=
  let s0 : MS := { mW := Array.replicate x.n 0, mT := Array.replicate x.m 0,
                   vis := Array.replicate x.m 0, stamp := 0 }
  match matchAll x q a 0 s0 with
  | (some i, s) =>
    let lt := Array.ofFn (n := x.m) fun t => if nget s.vis t.val == s.stamp then 0 else 1
    let lw0 := Array.replicate x.n 1
    let lw1 := nset lw0 i 0
    let lw := x.rT.foldl (fun l t =>
      if nget s.vis t == s.stamp && nget s.mT t != 0 then nset l (nget s.mT t - 1) 0 else l) lw1
    (lw, lt)
  | (none, s) =>
    let t0 : TS := { idx := Array.replicate x.n 0, low := Array.replicate x.n 0,
                     onS := Array.replicate x.n false, st := [], cnt := 0,
                     comp := Array.replicate x.n 0, nc := 0 }
    let t := tjAll x q a s.mT 0 t0
    let lt := Array.ofFn (n := x.m) fun e =>
      let o := nget s.mT e.val
      if o == 0 then 0 else nget t.comp (o - 1)
    (t.comp, lt)

/-! ### Search inside one slot -/

/-- The cells reached from the corner of slot `k`, without passing through cell `b`. -/
partial def bfs (x : Ctx) (a : Array Bool) (k b : Nat) (todo : List Nat) (seen : Array Bool) : Array Bool :=
  match todo with
  | [] => seen
  | i :: l =>
    let (l, seen) := (nbrs x.w x.n i).foldl (fun (r : List Nat × Array Bool) j =>
      if j != b && ok a j k && !get r.2 j then (j :: r.1, r.2.setIfInBounds j true) else r) (l, seen)
    bfs x a k b l seen

def reachOf (x : Ctx) (a : Array Bool) (k b : Nat) : Array Bool :=
  let c := x.cc k
  bfs x a k b [c] ((Array.replicate x.n false).setIfInBounds c true)

structure AS where
  disc : Array Nat
  low : Array Nat
  /-- A forced cell of the subtree, plus one. -/
  has : Array Nat
  cnt : Nat
  /-- The cut vertices, with a forced cell behind each of them. -/
  out : List (Nat × Nat)

mutual
  partial def artList (x : Ctx) (a : Array Bool) (k r par i : Nat) (l : List Nat) (s : AS) : AS :=
    match l with
    | [] => s
    | j :: l =>
      if !ok a j k || j == par then artList x a k r par i l s
      else if nget s.disc j != 0 then
        artList x a k r par i l { s with low := nset s.low i (min (nget s.low i) (nget s.disc j)) }
      else
        let s := artV x a k r i j s
        let lj := nget s.low j
        let s := { s with low := nset s.low i (min (nget s.low i) lj) }
        let hj := nget s.has j
        let s := if hj != 0 && nget s.has i == 0 then { s with has := nset s.has i hj } else s
        let s := if hj != 0 && lj ≥ nget s.disc i && i != r then
          { s with out := (i, hj - 1) :: s.out } else s
        artList x a k r par i l s

  partial def artV (x : Ctx) (a : Array Bool) (k r par i : Nat) (s : AS) : AS :=
    let n := s.cnt + 1
    let s := { s with disc := nset s.disc i n, low := nset s.low i n, cnt := n }
    let s := if onlyOK a i k then { s with has := nset s.has i (i + 1) } else s
    artList x a k r par i (nbrs x.w x.n i) s
end

/-- Cut vertices of slot `k` that are not yet forced, each with its proof set. -/
def cutsOf (x : Ctx) (a : Array Bool) (k : Nat) : List (Nat × Nat × Array Bool) :=
  let r := x.cc k
  let s0 : AS := { disc := Array.replicate x.n 0, low := Array.replicate x.n 0,
                   has := Array.replicate x.n 0, cnt := 0, out := [] }
  let s := artV x a k r x.n r s0
  (s.out.filter fun e => !onlyOK a e.1 k).map fun e => (e.1, e.2, reachOf x a k e.1)

/-! ### The cell for branching: fewest slots, then closest to the boundary, then smallest number -/

def pickOf (x : Ctx) (a : Array Bool) : Option Nat :=
  let w := x.w
  let r := x.rS.foldl (fun (best : Option (Nat × Nat × Nat)) i =>
    let c := slots4.foldl (fun c k => if ok a i k then c + 1 else c) 0
    if c ≤ 1 then best
    else
      let u := i / w; let v := i % w
      let d := min (min u v) (min (w - 1 - u) (w - 1 - v))
      match best with
      | none => some (c, d, i)
      | some (c', d', _) => if c < c' || (c == c' && d < d') then some (c, d, i) else best) none
  r.map fun e => e.2.2

def mkOrc (x : Ctx) (q : Q) : Orc :=
  { pot := potOf x q,
    reach := fun a k => reachOf x a k x.n,
    cuts := cutsOf x,
    pick := pickOf x }

/-- The number of the corner of slot `k`. -/
def ccOf (w : Nat) (k : Nat) : Nat :=
  match k with
  | 0 => 0
  | 1 => w - 1
  | 2 => (w - 1) * w + (w - 1)
  | _ => (w - 1) * w

def Cfg.ctx (c : Cfg) : Ctx :=
  { w := c.w, n := c.w * c.w, m := c.u * c.u + c.v * c.v,
    rS := List.range (c.w * c.w), rT := List.range (c.u * c.u + c.v * c.v), cc := ccOf c.w }

/-- The whole test for one quadruple, with the tables in the order of the slots. -/
def testRook (c : Cfg) (q : Q) : Bool :=
  let x := c.ctx
  rookDead x q (mkOrc x q) (4 * x.n) 400 (alive0 x q)

end Ex89
