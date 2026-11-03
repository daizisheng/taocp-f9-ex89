import Ex89.Match
/-!
The oracle of `Ex89.Match`: a matching, strong components, breadth-first search and cut vertices.
Nothing is proved about this file, and nothing needs to be. Its answers are only hints that are
checked by `applyPot`, `applyReach` and `applyCut`, so a bug here can only make the test weaker.
-/
namespace Ex89

@[inline] def nget (a : Array Nat) (i : Nat) : Nat := a.getD i 0
@[inline] def nset (a : Array Nat) (i v : Nat) : Array Nat := a.setIfInBounds i v
@[inline] def bget (a : Array Bool) (i : Nat) : Bool := a.getD i false

/-- The images of all cells in all slots, in one array. -/
def imgFlat (n : Nat) (q : Q) : Array Nat :=
  Array.ofFn (n := n * 4) fun e => imgAt q (e.val / 4) (e.val % 4)

/-! ### Matching and strong components, with explicit stacks -/

/-- The first free target of each cell. These loops are tail calls with many arguments, which the
compiler turns into loops without allocation, unlike `for` with several mutable variables. -/
partial def greedyLoop (imgF : Array Nat) (a : Array Bool) (n i k : Nat) (mW mT : Array Nat) :
    Array Nat × Array Nat :=
  if i ≥ n then (mW, mT)
  else if k ≥ 4 || nget mW i != 0 then greedyLoop imgF a n (i + 1) 0 mW mT
  else
    let e := i * 4 + k
    if bget a e then
      let t := nget imgF e
      if t != 0 && nget mT (t - 1) == 0 then
        greedyLoop imgF a n (i + 1) 0 (nset mW i t) (nset mT (t - 1) (i + 1))
      else greedyLoop imgF a n i (k + 1) mW mT
    else greedyLoop imgF a n i (k + 1) mW mT

/-- The cells with only one slot left take their targets first, so that no other cell takes them. -/
partial def forcedLoop (imgF : Array Nat) (a : Array Bool) (n i : Nat) (mW mT : Array Nat) :
    Array Nat × Array Nat :=
  if i ≥ n then (mW, mT)
  else
    let e0 := bget a (i * 4)
    let e1 := bget a (i * 4 + 1)
    let e2 := bget a (i * 4 + 2)
    let e3 := bget a (i * 4 + 3)
    let c := (if e0 then 1 else 0) + (if e1 then 1 else 0) + (if e2 then 1 else 0) + (if e3 then 1 else 0)
    if c == 1 then
      let k := if e0 then 0 else if e1 then 1 else if e2 then 2 else 3
      let t := nget imgF (i * 4 + k)
      if t != 0 && nget mT (t - 1) == 0 then
        forcedLoop imgF a n (i + 1) (nset mW i t) (nset mT (t - 1) (i + 1))
      else forcedLoop imgF a n (i + 1) mW mT
    else forcedLoop imgF a n (i + 1) mW mT

structure AugS where
  sp : Nat
  stC : Array Nat
  stK : Array Nat
  stT : Array Nat
  vis : Array Nat
  deriving Nonempty

/-- Depth-first search for an augmenting path from the cell on the stack. At the end, `sp` is zero if
there is none. -/
partial def augLoop (imgF : Array Nat) (a : Array Bool) (mT : Array Nat) (stamp sp : Nat)
    (stC stK stT vis : Array Nat) : AugS :=
  if sp == 0 then ⟨0, stC, stK, stT, vis⟩
  else
    let c := nget stC (sp - 1)
    let k := nget stK (sp - 1)
    if k ≥ 4 then augLoop imgF a mT stamp (sp - 1) stC stK stT vis
    else
      let stK := nset stK (sp - 1) (k + 1)
      let e := c * 4 + k
      if bget a e then
        let t := nget imgF e
        if t != 0 && nget vis (t - 1) != stamp then
          let vis := nset vis (t - 1) stamp
          let stT := nset stT (sp - 1) (t - 1)
          let o := nget mT (t - 1)
          if o == 0 then ⟨sp, stC, stK, stT, vis⟩
          else
            augLoop imgF a mT stamp (sp + 1) (nset stC sp (o - 1)) (nset stK sp 0) stT vis
        else augLoop imgF a mT stamp sp stC stK stT vis
      else augLoop imgF a mT stamp sp stC stK stT vis

partial def commitLoop (f sp : Nat) (stC stT mW mT : Array Nat) : Array Nat × Array Nat :=
  if f ≥ sp then (mW, mT)
  else
    let c := nget stC f
    let t := nget stT f
    commitLoop (f + 1) sp stC stT (nset mW c (t + 1)) (nset mT t (c + 1))

/-- Augment from all unmatched cells. -/
partial def matchLoop (imgF : Array Nat) (a : Array Bool) (n i stamp : Nat)
    (mW mT stC stK stT vis : Array Nat) : Option Nat × Array Nat × Array Nat × Nat :=
  if i ≥ n then (none, mW, mT, stamp)
  else if nget mW i != 0 then matchLoop imgF a n (i + 1) stamp mW mT stC stK stT vis
  else
    let st := stamp + 1
    let r := augLoop imgF a mT st 1 (nset stC 0 i) (nset stK 0 0) stT vis
    if r.sp == 0 then (some i, r.vis, mT, st)
    else
      let (mW, mT) := commitLoop 0 r.sp r.stC r.stT mW mT
      matchLoop imgF a n (i + 1) st mW mT r.stC r.stK r.stT r.vis

/-- A perfect matching, or the cell where the search fails together with the targets it visited. -/
def matchF (n m : Nat) (imgF : Array Nat) (a : Array Bool) : Option Nat × Array Nat × Array Nat × Nat :=
  let (mW, mT) := forcedLoop imgF a n 0 (Array.replicate n 0) (Array.replicate m 0)
  let (mW, mT) := greedyLoop imgF a n 0 0 mW mT
  matchLoop imgF a n 0 0 mW mT (Array.replicate (n + 1) 0) (Array.replicate (n + 1) 0)
    (Array.replicate (n + 1) 0) (Array.replicate m 0)

/-- Pop one strong component. -/
partial def popLoop (i nc sp : Nat) (st : Array Nat) (onS : Array Bool) (comp : Array Nat) :
    Nat × Array Bool × Array Nat :=
  let j := nget st (sp - 1)
  let onS := onS.setIfInBounds j false
  let comp := nset comp j nc
  if j == i then (sp - 1, onS, comp) else popLoop i nc (sp - 1) st onS comp

/-- Tarjan's algorithm with explicit stacks. A component that finishes first gets a smaller number. -/
partial def sccLoop (imgF : Array Nat) (a : Array Bool) (mT : Array Nat) (n r d cnt nc sp : Nat)
    (idx low : Array Nat) (onS : Array Bool) (comp st cS cK : Array Nat) : Array Nat :=
  if d == 0 then
    if r ≥ n then comp
    else if nget idx r != 0 then sccLoop imgF a mT n (r + 1) 0 cnt nc sp idx low onS comp st cS cK
    else
      sccLoop imgF a mT n (r + 1) 1 (cnt + 1) nc (sp + 1) (nset idx r (cnt + 1)) (nset low r (cnt + 1))
        (onS.setIfInBounds r true) comp (nset st sp r) (nset cS 0 r) (nset cK 0 0)
  else
    let i := nget cS (d - 1)
    let k := nget cK (d - 1)
    if k < 4 then
      let cK := nset cK (d - 1) (k + 1)
      let e := i * 4 + k
      if bget a e then
        let c := nget imgF e
        let o := if c == 0 then 0 else nget mT (c - 1)
        if o != 0 && o - 1 != i then
          let j := o - 1
          if nget idx j == 0 then
            sccLoop imgF a mT n r (d + 1) (cnt + 1) nc (sp + 1) (nset idx j (cnt + 1)) (nset low j (cnt + 1))
              (onS.setIfInBounds j true) comp (nset st sp j) (nset cS d j) (nset cK d 0)
          else if bget onS j then
            sccLoop imgF a mT n r d cnt nc sp idx (nset low i (min (nget low i) (nget idx j))) onS comp st cS cK
          else sccLoop imgF a mT n r d cnt nc sp idx low onS comp st cS cK
        else sccLoop imgF a mT n r d cnt nc sp idx low onS comp st cS cK
      else sccLoop imgF a mT n r d cnt nc sp idx low onS comp st cS cK
    else
      let li := nget low i
      let low := if d ≥ 2 then
        let p := nget cS (d - 2)
        nset low p (min (nget low p) li)
      else low
      if li == nget idx i then
        let (sp, onS, comp) := popLoop i nc sp st onS comp
        sccLoop imgF a mT n r (d - 1) cnt (nc + 1) sp idx low onS comp st cS cK
      else sccLoop imgF a mT n r (d - 1) cnt nc sp idx low onS comp st cS cK

def sccF (n : Nat) (imgF : Array Nat) (a : Array Bool) (mT : Array Nat) : Array Nat :=
  sccLoop imgF a mT n 0 0 0 0 0 (Array.replicate n 0) (Array.replicate n 0) (Array.replicate n false)
    (Array.replicate n 0) (Array.replicate (n + 1) 0) (Array.replicate (n + 1) 0) (Array.replicate (n + 1) 0)

/-- The potentials: from a set that violates Hall's condition, or from the strong components. -/
def potOf (x : Ctx) (imgF : Array Nat) (a : Array Bool) : Array Nat × Array Nat :=
  match matchF x.n x.m imgF a with
  | (some i, vis, mT, stamp) =>
    let lt := Array.ofFn (n := x.m) fun t => if nget vis t.val == stamp then 0 else 1
    let lw0 := Array.replicate x.n 1
    let lw1 := nset lw0 i 0
    let lw := x.rT.foldl (fun l t =>
      if nget vis t == stamp && nget mT t != 0 then nset l (nget mT t - 1) 0 else l) lw1
    (lw, lt)
  | (none, _, mT, _) =>
    let comp := sccF x.n imgF a mT
    let lt := Array.ofFn (n := x.m) fun e =>
      let o := nget mT e.val
      if o == 0 then 0 else nget comp (o - 1)
    (comp, lt)

/-! ### Search inside one slot -/

/-- The neighbor of cell `i` in direction `d`, plus one, or `0`. -/
@[inline] def nbrF (w n i d : Nat) : Nat :=
  match d with
  | 0 => if i % w != 0 then i else 0
  | 1 => if (i + 1) % w != 0 && decide (i + 1 < n) then i + 2 else 0
  | 2 => if w ≤ i then i - w + 1 else 0
  | _ => if i + w < n then i + w + 1 else 0

/-- Stack search from the corner of a slot. -/
partial def reachLoop (a : Array Bool) (w n k b sp d : Nat) (st : Array Nat) (seen : Array Bool) : Array Bool :=
  if sp == 0 then seen
  else
    let i := nget st (sp - 1)
    if d ≥ 4 then reachLoop a w n k b (sp - 1) 0 st seen
    else
      let f := nbrF w n i d
      if f != 0 && f - 1 != b && bget a ((f - 1) * 4 + k) && !bget seen (f - 1) then
        reachLoop a w n k b (sp + 1) 0 (nset st sp (f - 1)) (seen.setIfInBounds (f - 1) true)
      else reachLoop a w n k b sp (d + 1) st seen

/-- The cells reached from the corner of slot `k`, without passing through cell `b`. A cell that is
pushed is explored first, and its parent is explored again later: the set `seen` makes that cheap. -/
def reachOf (x : Ctx) (a : Array Bool) (k b : Nat) : Array Bool :=
  let c := x.cc k
  reachLoop a x.w x.n k b 1 0 (nset (Array.replicate (x.n + 1) 0) 0 c)
    ((Array.replicate x.n false).setIfInBounds c true)

@[inline] def fixedAt (a : Array Bool) (i k : Nat) : Bool :=
  (k == 0 || !bget a (i * 4)) && (k == 1 || !bget a (i * 4 + 1)) &&
    (k == 2 || !bget a (i * 4 + 2)) && (k == 3 || !bget a (i * 4 + 3))

/-- Cut vertices by depth-first search with an explicit stack. -/
partial def artLoop (a : Array Bool) (w n k r cnt sp : Nat) (disc low has cS cP cD : Array Nat)
    (out : List (Nat × Nat)) : List (Nat × Nat) :=
  if sp == 0 then out
  else
    let i := nget cS (sp - 1)
    let d := nget cD (sp - 1)
    if d < 4 then
      let cD := nset cD (sp - 1) (d + 1)
      let f := nbrF w n i d
      if f == 0 then artLoop a w n k r cnt sp disc low has cS cP cD out
      else
        let j := f - 1
        if bget a (j * 4 + k) && j != nget cP (sp - 1) then
          if nget disc j != 0 then
            artLoop a w n k r cnt sp disc (nset low i (min (nget low i) (nget disc j))) has cS cP cD out
          else
            artLoop a w n k r (cnt + 1) (sp + 1) (nset disc j (cnt + 1)) (nset low j (cnt + 1))
              (if fixedAt a j k then nset has j (j + 1) else has) (nset cS sp j) (nset cP sp i) (nset cD sp 0) out
        else artLoop a w n k r cnt sp disc low has cS cP cD out
    else if sp == 1 then out
    else
      let p := nget cS (sp - 2)
      let lj := nget low i
      let hj := nget has i
      let low := nset low p (min (nget low p) lj)
      let hp := nget has p
      let has := if hj != 0 && hp == 0 then nset has p hj else has
      let out := if hj != 0 && lj ≥ nget disc p && p != r then (p, hj - 1) :: out else out
      artLoop a w n k r cnt (sp - 1) disc low has cS cP cD out

/-- Cut vertices of slot `k` that are not yet forced, each with a forced cell behind it. -/
def cutList (x : Ctx) (a : Array Bool) (k : Nat) : List (Nat × Nat) :=
  let r := x.cc k
  artLoop a x.w x.n k r 1 1 (nset (Array.replicate x.n 0) r 1) (nset (Array.replicate x.n 0) r 1)
    (if fixedAt a r k then nset (Array.replicate x.n 0) r (r + 1) else Array.replicate x.n 0)
    (nset (Array.replicate (x.n + 1) 0) 0 r) (nset (Array.replicate (x.n + 1) 0) 0 x.n)
    (Array.replicate (x.n + 1) 0) []

def cutsOf (x : Ctx) (a : Array Bool) (k : Nat) : List (Nat × Nat × Array Bool) :=
  ((cutList x a k).filter fun e => !onlyOK a e.1 k).map fun e => (e.1, e.2, reachOf x a k e.1)

/-! ### Finding a crossing

Take two slots and the cells that may hold one of them. On the boundary of a face of this set, the
fixed cells of the two slots cannot alternate. This code walks around the faces, and it finds closing
walks by breadth-first search. `crossBad` checks the answer. -/

/-- The number of each cell in the grid of a view, for all slots: the source view is the cell itself.
The grid has a border, so a step never leaves it. Plus one; `0` means no image. -/
def tgtFlat (x : Ctx) (q : Q) (imgF : Array Nat) : Array Nat :=
  let W := x.tlim + 2
  Array.ofFn (n := x.n * 4) fun e =>
    if nget imgF e.val == 0 then 0
    else
      let c := x.tc (nget imgF e.val - 1)
      (c.1.toNat + 1) * W + (c.2.toNat + 1) + 1

/-- The grid of a view for two slots, in one pass. -/
structure GridF where
  inH : Array Bool
  lab : Array Nat
  who : Array Nat
  cells : Array Nat
  na : Nat
  nb : Nat
  deriving Nonempty

@[inline] def cnt4F (a : Array Bool) (i : Nat) : Nat :=
  (if bget a (i * 4) then 1 else 0) + (if bget a (i * 4 + 1) then 1 else 0) +
  (if bget a (i * 4 + 2) then 1 else 0) + (if bget a (i * 4 + 3) then 1 else 0)

partial def gridLoop (a : Array Bool) (tgF : Array Nat) (tv : Bool) (w W n ka kb i na nb : Nat)
    (inH : Array Bool) (lab who cells : Array Nat) : GridF :=
  if i ≥ n then ⟨inH, lab, who, cells, na, nb⟩
  else
    let aa := bget a (i * 4 + ka)
    let ab := bget a (i * 4 + kb)
    if !aa && !ab then gridLoop a tgF tv w W n ka kb (i + 1) na nb inH lab who cells
    else
      let fixed := cnt4F a i == 1
      let src := (i / w + 1) * W + (i % w + 1)
      let (inH, cells, lab, who, na) :=
        if aa then
          let g := if tv then nget tgF (i * 4 + ka) - 1 else src
          let new := !bget inH g
          let inH := if new then inH.setIfInBounds g true else inH
          let cells := if new then cells.push g else cells
          if fixed then (inH, cells, nset lab g 1, nset who g i, na + 1) else (inH, cells, lab, who, na)
        else (inH, cells, lab, who, na)
      let (inH, cells, lab, who, nb) :=
        if ab then
          let g := if tv then nget tgF (i * 4 + kb) - 1 else src
          let new := !bget inH g
          let inH := if new then inH.setIfInBounds g true else inH
          let cells := if new then cells.push g else cells
          if fixed then (inH, cells, nset lab g 2, nset who g i, nb + 1) else (inH, cells, lab, who, nb)
        else (inH, cells, lab, who, nb)
      gridLoop a tgF tv w W n ka kb (i + 1) na nb inH lab who cells

@[inline] def stepF (W d c : Nat) : Nat :=
  match d with
  | 0 => c + W
  | 1 => c + 1
  | 2 => c - W
  | _ => c - 1

/-- The result of a walk around one face boundary. -/
structure WalkF where
  vis : Array Bool
  first : Nat
  last : Nat
  runs : Nat
  r1 : Nat
  r2 : Nat
  r3 : Nat
  r4 : Nat
  deriving Nonempty

/-- Walk along a boundary, and note the first cell of each of the first four runs of fixed cells. -/
partial def walkLoop (inH : Array Bool) (lab who : Array Nat) (W c d first last runs r1 r2 r3 r4 : Nat)
    (vis : Array Bool) : WalkF :=
  if bget vis (c * 4 + d) then ⟨vis, first, last, runs, r1, r2, r3, r4⟩
  else
    let vis := vis.setIfInBounds (c * 4 + d) true
    let l := nget lab c
    let isNew := l != 0 && l != last
    let runs' := if isNew then runs + 1 else runs
    let first' := if isNew && runs' == 1 then l else first
    let last' := if isNew then l else last
    let r1' := if isNew && runs' == 1 then nget who c else r1
    let r2' := if isNew && runs' == 2 then nget who c else r2
    let r3' := if isNew && runs' == 3 then nget who c else r3
    let r4' := if isNew && runs' == 4 then nget who c else r4
    let r := (d + 1) % 4
    let ac := stepF W r c
    let bc := stepF W d ac
    if bget inH bc then walkLoop inH lab who W bc ((d + 3) % 4) first' last' runs' r1' r2' r3' r4' vis
    else if bget inH ac then walkLoop inH lab who W ac d first' last' runs' r1' r2' r3' r4' vis
    else walkLoop inH lab who W c r first' last' runs' r1' r2' r3' r4' vis

/-- Start a walk at every boundary side of every cell of the grid. -/
partial def faceLoop (inH : Array Bool) (lab who cells : Array Nat) (W j d : Nat) (vis : Array Bool)
    (out : List (Nat × Nat × Nat × Nat)) : List (Nat × Nat × Nat × Nat) :=
  if j ≥ cells.size then out
  else if d ≥ 4 then faceLoop inH lab who cells W (j + 1) 0 vis out
  else
    let c0 := nget cells j
    if bget inH (stepF W d c0) || bget vis (c0 * 4 + d) then faceLoop inH lab who cells W j (d + 1) vis out
    else
      let r := walkLoop inH lab who W c0 d 0 0 0 0 0 0 0 vis
      let n := if r.runs ≥ 2 && r.first == r.last then r.runs - 1 else r.runs
      let out := if n ≥ 4 then
          (if r.first == 1 then (r.r1, r.r3, r.r2, r.r4) else (r.r2, r.r4, r.r1, r.r3)) :: out
        else out
      faceLoop inH lab who cells W j (d + 1) r.vis out

/-- All alternations of fixed cells on the face boundaries, for two slots: `a1, a2, b1, b2`. -/
def faceQuads (x : Ctx) (a : Array Bool) (tgF : Array Nat) (tv : Bool) (ka kb : Nat) :
    List (Nat × Nat × Nat × Nat) :=
  let W := (if tv then x.tlim else x.w) + 2
  let N := W * W
  let g := gridLoop a tgF tv x.w W x.n ka kb 0 0 0 (Array.replicate N false) (Array.replicate N 0)
    (Array.replicate N 0) (Array.mkEmpty 1024)
  -- An alternation needs two fixed cells of each slot.
  if g.na < 2 || g.nb < 2 then []
  else faceLoop g.inH g.lab g.who g.cells W 0 0 (Array.replicate (N * 4) false) []

def dirX (d : Nat) : Int := match d with | 0 => 1 | 2 => -1 | _ => 0
def dirY (d : Nat) : Int := match d with | 1 => 1 | 3 => -1 | _ => 0

open NoCross in
/-- A walk from `s` to `t`, with all coordinates in `[-1, lim]`, using only allowed edges. -/
def bfsWalk (lim : Nat) (s t : Cell) (allowed : Cell → Cell → Bool) : Option (List Cell) := Id.run do
  let W := lim + 2
  let code : Cell → Nat := fun c => (c.1 + 1).toNat * W + (c.2 + 1).toNat
  let cell : Nat → Cell := fun n => (((n / W : Nat) : Int) - 1, ((n % W : Nat) : Int) - 1)
  let mut prev := Array.replicate (W * W) 0
  prev := prev.setIfInBounds (code s) (code s + 1)
  let mut queue : Array Nat := #[code s]
  let mut head := 0
  while head < queue.size do
    let n := queue.getD head 0
    head := head + 1
    let p := cell n
    if p == t then break
    for d in [0:4] do
      let r : Cell := (p.1 + dirX d, p.2 + dirY d)
      if r.1 < -1 || r.2 < -1 || r.1 > (lim : Int) || r.2 > (lim : Int) then continue
      let m := code r
      if prev.getD m 0 != 0 then continue
      if allowed p r then
        prev := prev.setIfInBounds m (n + 1)
        queue := queue.push m
  if prev.getD (code t) 0 == 0 then return none
  let mut path : List Cell := []
  let mut n := code t
  let mut fuel := W * W + 1
  while fuel > 0 do
    fuel := fuel - 1
    path := cell n :: path
    if n == code s then break
    n := prev.getD n 0 - 1
  return some path

open NoCross in
/-- The certificate for an alternation, if the closing walks exist and cross an odd number of times. -/
def certOf (x : Ctx) (q : Q) (a : Array Bool) (tv : Bool) (ka kb : Nat)
    (e : Nat × Nat × Nat × Nat) : Option XC :=
  let (a1, a2, b1, b2) := e
  let lim := if tv then x.tlim else x.w
  let mA := occMask x q a tv ka
  let mB := occMask x q a tv kb
  let pa := posV x q tv ka
  let pb := posV x q tv kb
  match bfsWalk lim (pa a2) (pa a1) (fun p r =>
      let d := dualC p r; !(get mB (pcode x d.1) && get mB (pcode x d.2))),
    bfsWalk lim (pb b2) (pb b1) (fun p r =>
      let d := dualS p r; !(get mA (pcode x d.1) && get mA (pcode x d.2))) with
  | some La, some Lb =>
    let c : XC := { tv, ka, kb, a1, a2, b1, b2, Ka := La.tail, Kb := Lb.tail }
    if crossBad x q a c then some c else none
  | _, _ => none

def crossOf (x : Ctx) (q : Q) (tgF : Array Nat) (a : Array Bool) : Option XC := Id.run do
  for tv in [false, true] do
    for (ka, kb) in [(1, 2), (1, 3), (2, 3)] do
      for e in faceQuads x a tgF tv ka kb do
        if let some c := certOf x q a tv ka kb e then
          return some c
  return none

/-! ### Branching along the perimeter

The boundary arcs of the L shape come first, then the perimeter of the `v × v` square. This is only
a choice of order, so nothing needs to be proved about it. -/

/-- The three arcs of the L shape between the corners of slots 1, 2 and 3. -/
def arcsOf (u w : Nat) : List (Array Nat) :=
  let m := w - 1
  let a0 := (List.range w).map fun t => t * w + m
  let a1 := (List.range w).map fun t => m * w + (m - t)
  let a2 := ((List.range (w - u)).map fun t => (m - t) * w) ++
    ((List.range (u - 1)).map fun t => u * w + (t + 1)) ++
    ((List.range (u + 1)).map fun t => (u - t) * w + u) ++
    ((List.range (m - u)).map fun t => u + 1 + t)
  [a0.toArray, a1.toArray, a2.toArray]

/-- The perimeter of the `v × v` square. -/
def perOf (u v : Nat) : Array Nat :=
  let off := u * u
  let S := v
  (((List.range S).map fun t => off + t * S) ++
   ((List.range (S - 1)).map fun t => off + (S - 1) * S + (t + 1)) ++
   ((List.range (S - 1)).map fun t => off + (S - 2 - t) * S + (S - 1)) ++
   ((List.range (S - 2)).map fun t => off + (S - 2 - t))).toArray

def cnt4 (a : Array Bool) (i : Nat) : Nat :=
  slots4.foldl (fun c k => if ok a i k then c + 1 else c) 0

/-- The middle of the longest undecided run on an arc. -/
def arcPick (a : Array Bool) (arcs : List (Array Nat)) : Option Nat := Id.run do
  let mut bl := 0
  let mut bc : Option Nat := none
  for arc in arcs do
    let mut i0 : Option Nat := none
    for i in [0:arc.size + 1] do
      let und := decide (i < arc.size) && decide (2 ≤ cnt4 a (arc.getD i 0))
      match i0 with
      | none => if und then i0 := some i
      | some s =>
        if !und then
          if i - s > bl then
            bl := i - s
            bc := some (arc.getD ((s + i) / 2) 0)
          i0 := none
  return bc

/-- An undecided cell behind the first undecided cell of the target perimeter. -/
def perPick (q : Q) (a : Array Bool) (per : Array Nat) : Option Nat := Id.run do
  for t in per do
    let mut n := 0
    let mut cc : Option Nat := none
    for k in [1, 2, 3] do
      let p := preAtQ q t k
      if p != 0 && ok a (p - 1) k then
        n := n + 1
        if 2 ≤ cnt4 a (p - 1) then cc := some (p - 1)
    if n > 1 && cc.isSome then return cc
  return none

/-- Prefer a cell with neighbors fixed to several slots. -/
def scorePick (x : Ctx) (a : Array Bool) : Option Nat := Id.run do
  let mut bs := 0
  let mut best : Option Nat := none
  for i in x.rS do
    let c := cnt4 a i
    if c < 2 then continue
    let mut f := 0
    let mut ad := 0
    let mut seen : List Nat := []
    for j in nbrs x.w x.n i do
      if cnt4 a j == 1 then
        ad := ad + 1
        for k in slots4 do
          if ok a j k && !seen.contains k then
            seen := k :: seen
            f := f + 1
    let s := f * 100 + (if c == 2 then 50 else 0) + ad + 1
    if s > bs then
      bs := s
      best := some i
  return best

def pickPer (x : Ctx) (q : Q) (arcs : List (Array Nat)) (per : Array Nat) (a : Array Bool) : Option Nat :=
  match arcPick a arcs with
  | some i => some i
  | none =>
    match perPick q a per with
    | some i => some i
    | none => scorePick x a

def mkOrc (x : Ctx) (q : Q) (u v : Nat) : Orc :=
  let arcs := arcsOf u x.w
  let per := perOf u v
  let imgF := imgFlat x.n q
  let tgF := tgtFlat x q imgF
  { pot := potOf x imgF,
    reach := fun a k => reachOf x a k x.n,
    cuts := cutsOf x,
    pick := pickPer x q arcs per,
    cross := crossOf x q tgF }

/-- The number of the corner of slot `k`. -/
def ccOf (w : Nat) (k : Nat) : Nat :=
  match k with
  | 0 => 0
  | 1 => w - 1
  | 2 => (w - 1) * w + (w - 1)
  | _ => (w - 1) * w

/-- The place of target cell `t`. The `v × v` square lies to the right of the `u × u` square. -/
def tcOf (u v t : Nat) : NoCross.Cell :=
  if t < u * u then ((t / u : Nat), (t % u : Nat))
  else (((t - u * u) / v + u + 2 : Nat), ((t - u * u) % v : Nat))

def Cfg.ctx (c : Cfg) : Ctx :=
  { w := c.w, n := c.w * c.w, m := c.u * c.u + c.v * c.v,
    rS := List.range (c.w * c.w), rT := List.range (c.u * c.u + c.v * c.v), cc := ccOf c.w,
    tc := tcOf c.u c.v, tlim := c.u + c.v + 3 }

/-- The whole test for one quadruple, with the tables in the order of the slots. -/
def testRook (c : Cfg) (q : Q) : Bool :=
  let x := c.ctx
  rookTest x q (mkOrc x q c.u c.v) (4 * x.n) 400 30000 (alive0 x q)

end Ex89
