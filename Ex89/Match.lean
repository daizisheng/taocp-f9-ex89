import Ex89.Prop
import Ex89.NoCross
/-!
A stronger test for one quadruple of placements. It uses three rules.

* **Potentials.** Give numbers to the source cells and to the target cells, such that along every
  possible edge the number of the target is at most the number of the source. Summing along the
  true bijection shows that the sum on the target side is at most the sum on the source side, and
  that no true edge has a slack bigger than the difference of the sums. This one lemma contains
  Hall's condition and the removal of the edges that lie in no perfect matching.
* **Connectivity.** A set of cells that contains the corner of a piece and is closed under rook
  steps inside the possible cells of that piece contains the whole piece.
* **Branching** on the slot of one cell.

The numbers, the closed sets and the choice of a cell come from an untrusted oracle `Orc`. Every
theorem below holds for every oracle, because each answer is checked before it is used. So nothing
needs to be proved about the matching and search code that computes the oracle.
-/
namespace Ex89

/-- The image table of slot `k` at source cell `i`. -/
def imgAt (q : Q) (i k : Nat) : Nat :=
  match k with
  | 0 => q.t0.img.getD i 0
  | 1 => q.t1.img.getD i 0
  | 2 => q.t2.img.getD i 0
  | _ => q.t3.img.getD i 0

def slots4 : List Nat := [0, 1, 2, 3]

/-- Edge `(i, k)` says that source cell `i` may belong to slot `k`. -/
def ok (a : Array Bool) (i k : Nat) : Bool := a.getD (i * 4 + k) false

def clearE (a : Array Bool) (i k : Nat) : Array Bool := a.setIfInBounds (i * 4 + k) false

/-- Remove all edges that satisfy `p`. -/
def prune (rS : List Nat) (a : Array Bool) (p : Nat → Nat → Bool) : Array Bool :=
  rS.foldl (fun a i => slots4.foldl (fun a k => if p i k then clearE a i k else a) a) a

/-- The sum of `f` over a list. -/
def sumF (f : Nat → Nat) : List Nat → Nat
  | [] => 0
  | x :: l => f x + sumF f l

/-- The rook neighbors of a cell of the `w × w` square, with `n = w * w`. -/
def nbrs (w n i : Nat) : List Nat :=
  let l0 : List Nat := if i + w < n then [i + w] else []
  let l1 : List Nat := if w ≤ i then (i - w) :: l0 else l0
  let l2 : List Nat := if (i + 1) % w != 0 && decide (i + 1 < n) then (i + 1) :: l1 else l1
  if i % w != 0 then (i - 1) :: l2 else l2

/-- The data of the problem. -/
structure Ctx where
  w : Nat
  n : Nat
  m : Nat
  rS : List Nat
  rT : List Nat
  /-- The cell of the corner of slot `k`. -/
  cc : Nat → Nat
  /-- The place of a target cell in the plane. -/
  tc : Nat → NoCross.Cell
  /-- Target cells have coordinates below this bound. Only the oracle uses it. -/
  tlim : Nat

/-! ### The three checked rules -/

def tget (L : Array Nat) (i : Nat) : Nat := L.getD i 0

/-- Along every possible edge, the number of the target is at most the number of the source. -/
def potOK (x : Ctx) (q : Q) (a : Array Bool) (LW LT : Array Nat) : Bool :=
  x.rS.all fun i => slots4.all fun k =>
    !ok a i k || (let c := imgAt q i k; c != 0 && decide (tget LT (c - 1) ≤ tget LW i))

/-- `none` means a contradiction. -/
def applyPot (x : Ctx) (q : Q) (a : Array Bool) (LW LT : Array Nat) : Option (Array Bool) :=
  if potOK x q a LW LT then
    let sw := sumF (tget LW) x.rS
    let st := sumF (tget LT) x.rT
    if sw < st then none
    else
      let d := sw - st
      some (prune x.rS a fun i k =>
        ok a i k && decide (tget LT (imgAt q i k - 1) + d < tget LW i))
  else some a

/-- `seen` is closed under rook steps inside the possible cells of slot `k`, apart from cell `b`. -/
def closedOK (x : Ctx) (a : Array Bool) (k : Nat) (seen : Array Bool) (b : Nat) : Bool :=
  get seen (x.cc k) && x.rS.all fun i =>
    !get seen i || (nbrs x.w x.n i).all fun j => j == b || !ok a j k || get seen j

/-- Cells outside a closed set do not belong to slot `k`. The value `x.n` for `b` excludes nothing. -/
def applyReach (x : Ctx) (a : Array Bool) (k : Nat) (seen : Array Bool) : Array Bool :=
  if closedOK x a k seen x.n then
    prune x.rS a fun i k' => k' == k && ok a i k && !get seen i
  else a

/-- Cell `i` has only slot `k` left. -/
def onlyOK (a : Array Bool) (i k : Nat) : Bool :=
  slots4.all fun k' => k' == k || !ok a i k'

/-- Keep only slot `k` at cell `i`. -/
def restrict (a : Array Bool) (i k : Nat) : Array Bool :=
  slots4.foldl (fun a k' => if k' == k then a else clearE a i k') a

/-- Cell `b` separates the corner of slot `k` from the cell `f` of slot `k`, so `b` is in slot `k`. -/
def applyCut (x : Ctx) (a : Array Bool) (e : Nat × Nat × Nat × Array Bool) : Array Bool :=
  let (b, k, f, seen) := e
  if decide (b < x.n) && decide (f < x.n) && decide (k < 4) && onlyOK a f k && !get seen f &&
      closedOK x a k seen b then
    restrict a b k
  else a

/-! ### The crossing rule -/

open NoCross in
/-- A source cell in the plane. -/
def cellOf (w i : Nat) : Cell := ((i / w : Nat), (i % w : Nat))

open NoCross in
/-- Where cell `i` lies if it belongs to slot `k`: in the source, or in the target when `tv`. -/
def posV (x : Ctx) (q : Q) (tv : Bool) (k i : Nat) : Cell :=
  if tv then x.tc (imgAt q i k - 1) else cellOf x.w i

/-- The size of the table of possible places. -/
def occSize (x : Ctx) : Nat := (2 * x.w + 6) * (2 * x.w + 6)

open NoCross in
/-- A number for a place. Two places may get the same number, which only makes the test weaker. -/
def pcode (x : Ctx) (c : Cell) : Nat :=
  ((c.1 + 1).toNat * (2 * x.w + 6) + (c.2 + 1).toNat) % occSize x

/-- The places that slot `k` may occupy. -/
def occMask (x : Ctx) (q : Q) (a : Array Bool) (tv : Bool) (k : Nat) : Array Bool :=
  x.rS.foldl (fun m i => if ok a i k then m.setIfInBounds (pcode x (posV x q tv k i)) true else m)
    (Array.replicate (occSize x) false)

/-- A proposed crossing: closing walks `Ka` and `Kb` for slots `ka` and `kb`. -/
structure XC where
  tv : Bool
  ka : Nat
  kb : Nat
  a1 : Nat
  a2 : Nat
  b1 : Nat
  b2 : Nat
  Ka : List NoCross.Cell
  Kb : List NoCross.Cell

namespace NoCross

instance (p q : Cell) : Decidable (Adj p q) := by unfold Adj; infer_instance

/-- `IsWalk`, as a computation. -/
def isWalkB : List Cell → Bool
  | [] => true
  | [_] => true
  | p :: q :: l => decide (Adj p q) && isWalkB (q :: l)

theorem isWalkB_sound : ∀ {l : List Cell}, isWalkB l = true → IsWalk l
  | [], _ => trivial
  | [_], _ => trivial
  | _ :: q :: l, h => by
      simp only [isWalkB, Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨h.1, isWalkB_sound (l := q :: l) h.2⟩

end NoCross

open NoCross in
/-- `true` means that no rookwise connected dissection has the possible cells `a`: the fixed cells
of two slots alternate, and the closing walks cross an odd number of times. -/
def crossBad (x : Ctx) (q : Q) (a : Array Bool) (e : XC) : Bool :=
  let pa := posV x q e.tv e.ka
  let pb := posV x q e.tv e.kb
  let Wa := pa e.a2 :: e.Ka
  let Wb := pb e.b2 :: e.Kb
  decide (e.ka < 4) && decide (e.kb < 4) && decide (e.ka ≠ e.kb) &&
  decide (e.a1 < x.n) && decide (e.a2 < x.n) && decide (e.b1 < x.n) && decide (e.b2 < x.n) &&
  onlyOK a e.a1 e.ka && onlyOK a e.a2 e.ka && onlyOK a e.b1 e.kb && onlyOK a e.b2 e.kb &&
  isWalkB Wa && isWalkB Wb && decide (Wa.getLast? = some (pa e.a1)) &&
  decide (Wb.getLast? = some (pb e.b1)) &&
  (let mA := occMask x q a e.tv e.ka
   let mB := occMask x q a e.tv e.kb
   (edges Wa).all (fun f => let d := dualC f.1 f.2; !(get mB (pcode x d.1) && get mB (pcode x d.2))) &&
   (edges Wb).all (fun f => let d := dualS f.1 f.2; !(get mA (pcode x d.1) && get mA (pcode x d.2)))) &&
  crossE (edges Wa) (edges Wb)

/-- The untrusted oracle. -/
structure Orc where
  pot : Array Bool → Array Nat × Array Nat
  reach : Array Bool → Nat → Array Bool
  cuts : Array Bool → Nat → List (Nat × Nat × Array Bool)
  pick : Array Bool → Option Nat
  cross : Array Bool → Option XC

def countA (a : Array Bool) : Nat := a.foldl (fun c b => if b then c + 1 else c) 0

/-- The preimage table of slot `k` at target cell `t`. Only a hint: the image is checked. -/
def preAtQ (q : Q) (t k : Nat) : Nat :=
  match k with
  | 0 => q.t0.pre.getD t 0
  | 1 => q.t1.pre.getD t 0
  | 2 => q.t2.pre.getD t 0
  | _ => q.t3.pre.getD t 0

/-- Cell `i` has only slot `k` left, so no other cell goes to its image. -/
def applyFixedAt (q : Q) (a : Array Bool) (i : Nat) : Array Bool :=
  let k := (slots4.filter (ok a i)).headD 0
  if onlyOK a i k then
    let c := imgAt q i k
    if c == 0 then a
    else
      slots4.foldl (fun a l =>
        let p := preAtQ q (c - 1) l
        if p != 0 && p - 1 != i && imgAt q (p - 1) l == c then clearE a (p - 1) l else a) a
  else a

def applyFixed (x : Ctx) (q : Q) (a : Array Bool) : Array Bool :=
  x.rS.foldl (applyFixedAt q) a

/-- One round of the rules, cheapest first: a later rule runs only if the earlier ones changed nothing. -/
def round (x : Ctx) (q : Q) (o : Orc) (a : Array Bool) : Option (Array Bool) :=
  let a1 := applyFixed x q a
  let n := countA a
  if countA a1 != n then some a1 else
  if (o.cross a1).any (crossBad x q a1) then none else
  let a2 := slots4.foldl (fun a k => applyReach x a k (o.reach a k)) a1
  if countA a2 != n then some a2 else
  let a3 := slots4.foldl (fun a k =>
    (o.cuts a k).foldl (fun a e => applyCut x a (e.1, k, e.2.1, e.2.2)) a) a2
  if countA a3 != n then some a3 else
  let p := o.pot a3
  applyPot x q a3 p.1 p.2

/-- Repeat the rounds until nothing changes. -/
def fixL (x : Ctx) (q : Q) (o : Orc) : Nat → Array Bool → Option (Array Bool)
  | 0, a => some a
  | n + 1, a =>
    match round x q o a with
    | none => none
    | some a' => if countA a' == countA a then some a' else fixL x q o n a'

/-- A contradiction without branching. -/
def killed (x : Ctx) (q : Q) (o : Orc) (nf : Nat) (a : Array Bool) : Bool :=
  match fixL x q o nf a with
  | none => true
  | some _ => false

/-- Failed literals: if slot `k` at cell `i` gives a contradiction, then remove it. -/
def probeAll (x : Ctx) (q : Q) (o : Orc) (nf : Nat) (a : Array Bool) : Array Bool :=
  x.rS.foldl (fun a i => if onlyOK a i ((slots4.filter (ok a i)).headD 0) then a else
    slots4.foldl (fun a k =>
      if ok a i k && killed x q o nf (restrict a i k) then clearE a i k else a) a) a

/-- `true` means that no rookwise connected dissection uses these placements. The search visits at
most `fuel` nodes and then gives up, with the answer `false`. -/
def rookDead (x : Ctx) (q : Q) (o : Orc) (nf : Nat) : Nat → Nat → Array Bool → Bool × Nat
  | 0, f, _ => (false, f)
  | d + 1, f, a =>
    if f == 0 then (false, 0) else
    match fixL x q o nf a with
    | none => (true, f - 1)
    | some a' =>
      match o.pick a' with
      | none => (false, f - 1)
      | some i =>
        slots4.foldl (fun r k =>
          if !r.1 then r
          else if !ok a' i k then r
          else rookDead x q o nf d r.2 (restrict a' i k)) (decide (i < x.n), f - 1)

/-- First a search without probing. If it gives up, then probe at the root and search again. -/
def rookTest (x : Ctx) (q : Q) (o : Orc) (nf d budget : Nat) (a : Array Bool) : Bool :=
  (rookDead x q o nf d budget a).1 ||
    (probeRounds x q o nf 8 a)
where
  probeRounds (x : Ctx) (q : Q) (o : Orc) (nf : Nat) : Nat → Array Bool → Bool
    | 0, a => (rookDead x q o nf d (100 * budget) a).1
    | n + 1, a =>
      let a1 := probeAll x q o nf a
      if killed x q o nf a1 then true
      else if countA a1 == countA a then (rookDead x q o nf d (100 * budget) a1).1
      else probeRounds x q o nf n a1

/-- The possible edges at the start: the images inside the target, with the corners decided. -/
def alive0 (x : Ctx) (q : Q) : Array Bool :=
  let a0 := Array.ofFn (n := x.n * 4) fun e => imgAt q (e.val / 4) (e.val % 4) != 0
  slots4.foldl (fun a k => restrict a (x.cc k) k) a0

/-! ### Soundness -/

/-- The true dissection, seen from the search. -/
structure TA (x : Ctx) (q : Q) (sl τ : Nat → Nat) : Prop where
  hS : x.rS = List.range x.n
  hT : x.rT = List.range x.m
  slot_lt : ∀ i, i < x.n → sl i < 4
  img : ∀ i, i < x.n → imgAt q i (sl i) = τ i + 1
  τ_lt : ∀ i, i < x.n → τ i < x.m
  inj : ∀ i i', i < x.n → i' < x.n → τ i = τ i' → i = i'
  surj : ∀ j, j < x.m → ∃ i, i < x.n ∧ τ i = j
  /-- Each slot contains its corner. -/
  corner : ∀ k, k < 4 → x.cc k < x.n ∧ sl (x.cc k) = k
  /-- A set that contains the corner of slot `k` and is closed under rook steps inside slot `k`
  contains all of slot `k`. -/
  conn : ∀ k, k < 4 → ∀ P : Nat → Bool, P (x.cc k) = true →
    (∀ i j, i < x.n → P i = true → j ∈ nbrs x.w x.n i → sl j = k → P j = true) →
    ∀ i, i < x.n → sl i = k → P i = true
  w_pos : 0 < x.w
  /-- Rook neighbors in one slot stay adjacent in the target. -/
  tadj : ∀ i j, i < x.n → j ∈ nbrs x.w x.n i → sl j = sl i →
    NoCross.Adj (x.tc (τ i)) (x.tc (τ j))
  /-- Different target cells have different places. -/
  tinj : ∀ t t', t < x.m → t' < x.m → x.tc t = x.tc t' → t = t'

/-- All true edges are still possible. -/
def Al (x : Ctx) (sl : Nat → Nat) (a : Array Bool) : Prop := ∀ i, i < x.n → ok a i (sl i) = true

theorem ok_clearE_of_ne {a : Array Bool} {i k i' k' : Nat} (hk : k < 4) (hk' : k' < 4)
    (h : ¬ (i = i' ∧ k = k')) : ok (clearE a i' k') i k = ok a i k := by
  have hne : i' * 4 + k' ≠ i * 4 + k := by
    intro e
    apply h
    omega
  simp [ok, clearE, Array.getD_eq_getD_getElem?, hne]

theorem mem_slots4 {k : Nat} (h : k ∈ slots4) : k < 4 := by
  simp only [slots4, List.mem_cons, List.not_mem_nil, or_false] at h
  omega

theorem mem_slots4' {k : Nat} (h : k < 4) : k ∈ slots4 := by
  simp only [slots4, List.mem_cons, List.not_mem_nil, or_false]
  omega

/-- Pruning at one cell keeps a true edge. -/
theorem prune_slots {i0 k0 : Nat} (hk0 : k0 < 4) (p : Nat → Nat → Bool) (i : Nat)
    (hp : i = i0 → p i k0 = false) (l : List Nat) (hl : ∀ k ∈ l, k < 4) (a : Array Bool)
    (h : ok a i0 k0 = true) :
    ok (l.foldl (fun a k => if p i k then clearE a i k else a) a) i0 k0 = true := by
  induction l generalizing a with
  | nil => exact h
  | cons k l ih =>
    simp only [List.foldl_cons]
    apply ih (fun k hk => hl k (by simp [hk]))
    split
    next hpk =>
      have hkl : k < 4 := hl k (by simp)
      by_cases e : i0 = i ∧ k0 = k
      · obtain ⟨rfl, rfl⟩ := e
        rw [hp rfl] at hpk
        simp at hpk
      · rw [ok_clearE_of_ne hk0 hkl e]; exact h
    next => exact h

theorem prune_ok {i0 k0 : Nat} (hk0 : k0 < 4) (p : Nat → Nat → Bool) (hp : p i0 k0 = false)
    (l : List Nat) (a : Array Bool) (h : ok a i0 k0 = true) : ok (prune l a p) i0 k0 = true := by
  induction l generalizing a with
  | nil => exact h
  | cons i l ih =>
    simp only [prune, List.foldl_cons]
    apply ih
    apply prune_slots hk0 p i (fun e => by rw [e]; exact hp) slots4
      (fun _ h => mem_slots4 h) a h

variable {x : Ctx} {q : Q} {sl τ : Nat → Nat}

theorem TA.prune_Al (T : TA x q sl τ) {a : Array Bool} (h : Al x sl a) (p : Nat → Nat → Bool)
    (hp : ∀ i, i < x.n → p i (sl i) = false) : Al x sl (prune x.rS a p) :=
  fun i hi => prune_ok (T.slot_lt i hi) p (hp i hi) _ a (h i hi)

/-! Sums along the bijection -/

theorem sumF_perm (f : Nat → Nat) {l l' : List Nat} (h : l.Perm l') : sumF f l = sumF f l' := by
  induction h with
  | nil => rfl
  | cons a _ ih => simp [sumF, ih]
  | swap a b l => simp only [sumF]; omega
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem sumF_map (f τ : Nat → Nat) (l : List Nat) : sumF f (l.map τ) = sumF (fun i => f (τ i)) l := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [sumF, ih]

theorem sumF_le {g h : Nat → Nat} (l : List Nat) (H : ∀ i ∈ l, g i ≤ h i) : sumF g l ≤ sumF h l := by
  induction l with
  | nil => exact Nat.le_refl _
  | cons a l ih =>
    have h1 := H a (by simp)
    have h2 := ih (fun i hi => H i (by simp [hi]))
    simp only [sumF]; omega

theorem sumF_slack {g h : Nat → Nat} (l : List Nat) (H : ∀ i ∈ l, g i ≤ h i) {i : Nat} (hi : i ∈ l) :
    h i + sumF g l ≤ g i + sumF h l := by
  induction l with
  | nil => simp at hi
  | cons a l ih =>
    have h1 := H a (by simp)
    have h2 := sumF_le l (fun i hi => H i (by simp [hi]))
    simp only [sumF]
    rcases List.mem_cons.1 hi with rfl | hi'
    · omega
    · have := ih (fun i hi => H i (by simp [hi])) hi'
      omega

theorem TA.perm (T : TA x q sl τ) : ((List.range x.n).map τ).Perm (List.range x.m) := by
  have d1 : ((List.range x.n).map τ).Nodup := by
    have d0 : (List.range x.n).Nodup := List.nodup_range
    refine List.pairwise_map.2 (List.Pairwise.imp_of_mem (R := fun a b => a ≠ b) ?_ d0)
    intro a b ha hb hab e
    exact hab (T.inj a b (List.mem_range.1 ha) (List.mem_range.1 hb) e)
  have d2 : (List.range x.m).Nodup := List.nodup_range
  rw [List.perm_ext_iff_of_nodup d1 d2]
  intro j
  simp only [List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩; exact T.τ_lt i hi
  · intro hj
    obtain ⟨i, hi, e⟩ := T.surj j hj
    exact ⟨i, hi, e⟩

theorem TA.sum_eq (T : TA x q sl τ) (f : Nat → Nat) :
    sumF (fun i => f (τ i)) x.rS = sumF f x.rT := by
  rw [T.hS, T.hT, ← sumF_map]
  exact sumF_perm f T.perm

/-- The potential rule. -/
theorem TA.applyPot (T : TA x q sl τ) {a : Array Bool} (h : Al x sl a) (LW LT : Array Nat) :
    ∃ a', Ex89.applyPot x q a LW LT = some a' ∧ Al x sl a' := by
  unfold Ex89.applyPot
  split
  next hok =>
    have hb : ∀ i ∈ x.rS, tget LT (τ i) ≤ tget LW i := by
      intro i hi
      have hi' : i < x.n := by rw [T.hS] at hi; exact List.mem_range.1 hi
      simp only [potOK, List.all_eq_true] at hok
      have := hok i hi (sl i) (mem_slots4' (T.slot_lt i hi'))
      rw [h i hi', T.img i hi'] at this
      simpa using this
    have hsum := T.sum_eq (tget LT)
    have hle : sumF (fun i => tget LT (τ i)) x.rS ≤ sumF (tget LW) x.rS := sumF_le _ hb
    simp only []
    rw [if_neg (Nat.not_lt.2 (by omega))]
    refine ⟨_, rfl, T.prune_Al h _ ?_⟩
    intro i hi
    have hm : i ∈ x.rS := by rw [T.hS]; exact List.mem_range.2 hi
    have hs := sumF_slack (g := fun i => tget LT (τ i)) (h := tget LW) x.rS hb hm
    rw [T.img i hi]
    simp only [Nat.add_sub_cancel, Bool.and_eq_false_iff, decide_eq_false_iff_not]
    right
    omega
  next => exact ⟨a, rfl, h⟩

theorem nbrs_lt {w n i j : Nat} (hi : i < n) (hj : j ∈ nbrs w n i) : j < n := by
  unfold nbrs at hj
  simp only at hj
  have h0 : ∀ j, j ∈ (if i + w < n then [i + w] else ([] : List Nat)) → j < n := by
    intro j h; split at h <;> simp at h; omega
  have h1 : ∀ j, j ∈ (if w ≤ i then (i - w) :: (if i + w < n then [i + w] else ([] : List Nat))
      else (if i + w < n then [i + w] else ([] : List Nat))) → j < n := by
    intro j h; split at h
    · rcases List.mem_cons.1 h with rfl | h
      · omega
      · exact h0 j h
    · exact h0 j h
  generalize hL : (if w ≤ i then (i - w) :: (if i + w < n then [i + w] else ([] : List Nat))
      else (if i + w < n then [i + w] else ([] : List Nat))) = L at h1 hj
  have h2 : ∀ j, j ∈ (if ((i + 1) % w != 0 && decide (i + 1 < n)) = true then (i + 1) :: L else L) → j < n := by
    intro j h; split at h
    next hc =>
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      rcases List.mem_cons.1 h with rfl | h
      · exact hc.2
      · exact h1 j h
    · exact h1 j h
  split at hj
  · rcases List.mem_cons.1 hj with rfl | h
    · omega
    · exact h2 j h
  · exact h2 j hj

theorem TA.closed_all (T : TA x q sl τ) {a : Array Bool} (h : Al x sl a) {k : Nat} (hk : k < 4)
    {seen : Array Bool} {b : Nat} (hc : closedOK x a k seen b = true) (hb : sl b ≠ k ∨ x.n ≤ b)
    {i : Nat} (hi : i < x.n) (hs : sl i = k) : get seen i = true := by
  simp only [closedOK, Bool.and_eq_true, List.all_eq_true] at hc
  refine T.conn k hk (fun i => get seen i) hc.1 ?_ i hi hs
  intro i j hi' hP hj hsj
  have hclo := hc.2 i (by rw [T.hS]; exact List.mem_range.2 hi')
  rw [hP] at hclo
  simp only [Bool.not_true, Bool.false_or, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hclo
  have hjn : j < x.n := nbrs_lt hi' hj
  have := hclo j hj
  rcases this with (e | e) | e
  · have e' : j = b := by simpa using e
    subst e'
    rcases hb with hb | hb
    · exact absurd hsj hb
    · omega
  · have := h j hjn
    rw [hsj] at this
    rw [this] at e
    simp at e
  · exact e

theorem TA.applyReach (T : TA x q sl τ) {a : Array Bool} (h : Al x sl a) {k : Nat} (hk : k < 4)
    (seen : Array Bool) : Al x sl (Ex89.applyReach x a k seen) := by
  unfold Ex89.applyReach
  split
  next hc =>
    apply T.prune_Al h
    intro i hi
    by_cases e : sl i = k
    · have := T.closed_all h hk hc (Or.inr (Nat.le_refl _)) hi e
      simp [this]
    · have : (sl i == k) = false := by simpa using e
      simp [this]
  next => exact h

theorem ok_restrict {a : Array Bool} {i k i0 k0 : Nat} (hk0 : k0 < 4) (hne : i0 = i → k0 = k)
    (h : ok a i0 k0 = true) : ok (restrict a i k) i0 k0 = true := by
  unfold restrict
  have key : ∀ (l : List Nat), (∀ k ∈ l, k < 4) → ∀ a : Array Bool, ok a i0 k0 = true →
      ok (l.foldl (fun a k' => if k' == k then a else clearE a i k') a) i0 k0 = true := by
    intro l
    induction l with
    | nil => intro _ a h; exact h
    | cons k' l ih =>
      intro hl a h
      simp only [List.foldl_cons]
      apply ih (fun k hk => hl k (by simp [hk]))
      split
      · exact h
      next hb =>
        have hk' : k' < 4 := hl k' (by simp)
        have hkk : k' ≠ k := by simpa using hb
        rw [ok_clearE_of_ne hk0 hk']
        · exact h
        · rintro ⟨rfl, rfl⟩
          exact hkk (hne rfl)
  exact key _ (fun _ h => mem_slots4 h) a h

theorem TA.restrict_Al {a : Array Bool} (h : Al x sl a) {i k : Nat}
    (T : TA x q sl τ) (hik : i < x.n → sl i = k) : Al x sl (restrict a i k) := by
  intro i0 hi0
  apply ok_restrict (T.slot_lt i0 hi0) _ (h i0 hi0)
  rintro rfl
  exact hik hi0

theorem TA.only_slot {a : Array Bool} (T : TA x q sl τ) (h : Al x sl a) {f k : Nat} (hf : f < x.n)
    (ho : onlyOK a f k = true) : sl f = k := by
  simp only [onlyOK, List.all_eq_true] at ho
  have := ho (sl f) (mem_slots4' (T.slot_lt f hf))
  rw [h f hf] at this
  simpa using this

theorem TA.applyCut (T : TA x q sl τ) {a : Array Bool} (h : Al x sl a) (e : Nat × Nat × Nat × Array Bool) :
    Al x sl (Ex89.applyCut x a e) := by
  obtain ⟨b, k, f, seen⟩ := e
  unfold Ex89.applyCut
  simp only
  split
  next hc =>
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hc
    obtain ⟨⟨⟨⟨⟨hb, hf⟩, hk⟩, ho⟩, hs⟩, hcl⟩ := hc
    apply T.restrict_Al h
    intro _
    apply Classical.byContradiction
    intro hne
    have hsf := T.only_slot h hf ho
    have := T.closed_all h hk hcl (Or.inl hne) hf hsf
    rw [hs] at this
    simp at this
  next => exact h

/-! ### Soundness of the crossing rule -/

section Crossing
open NoCross

theorem div_mod_of {w q r : Nat} (hr : r < w) : (w * q + r) / w = q ∧ (w * q + r) % w = r := by
  have hw : 0 < w := by omega
  constructor
  · rw [Nat.mul_add_div hw, Nat.div_eq_of_lt hr]; simp
  · rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hr]

/-- Rook neighbors are adjacent in the plane. -/
theorem nbrs_adj {w n i j : Nat} (hw : 0 < w) (h : j ∈ nbrs w n i) :
    Adj (cellOf w i) (cellOf w j) := by
  have hcases : (i % w ≠ 0 ∧ j = i - 1) ∨ ((i + 1) % w ≠ 0 ∧ j = i + 1) ∨ (w ≤ i ∧ j = i - w) ∨
      (j = i + w) := by
    unfold nbrs at h
    simp only at h
    by_cases c1 : (i % w != 0) = true <;>
    by_cases c2 : ((i + 1) % w != 0 && decide (i + 1 < n)) = true <;>
    by_cases c3 : w ≤ i <;> by_cases c4 : i + w < n <;>
    simp only [c1, c2, c3, c4, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at h <;>
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at c1 c2 <;>
    grind
  have hi := Nat.div_add_mod i w
  have hr := Nat.mod_lt i hw
  have mk : ∀ {q' r' : Nat}, r' < w → j = w * q' + r' → j / w = q' ∧ j % w = r' := by
    intro q' r' h1 h2; rw [h2]; exact div_mod_of h1
  generalize hq : i / w = q at *
  generalize hrr : i % w = r at *
  have hci : cellOf w i = ((q : Int), (r : Int)) := by simp [cellOf, hq, hrr]
  rw [hci]
  rcases hcases with ⟨h1, e⟩ | ⟨h1, e⟩ | ⟨h1, e⟩ | e
  · obtain ⟨d1, d2⟩ := mk (q' := q) (r' := r - 1) (by omega) (by omega)
    simp only [cellOf, Adj]
    rw [d1, d2]
    omega
  · have hlt : r + 1 < w := by
      apply Classical.byContradiction
      intro hn
      have hrw : r + 1 = w := by omega
      apply h1
      have : i + 1 = w * (q + 1) := by rw [Nat.mul_add]; omega
      rw [this]; simp
    obtain ⟨d1, d2⟩ := mk (q' := q) (r' := r + 1) hlt (by omega)
    simp only [cellOf, Adj]
    rw [d1, d2]
    omega
  · have hq1 : 1 ≤ q := by
      apply Classical.byContradiction
      intro hn
      have : q = 0 := by omega
      subst this
      simp at hi
      omega
    obtain ⟨d1, d2⟩ := mk (q' := q - 1) (r' := r) hr (by
      obtain ⟨t, rfl⟩ : ∃ t, q = t + 1 := ⟨q - 1, by omega⟩
      rw [Nat.mul_add] at hi
      simp only [Nat.add_sub_cancel]
      omega)
    simp only [cellOf, Adj]
    rw [d1, d2]
    omega
  · obtain ⟨d1, d2⟩ := mk (q' := q + 1) (r' := r) hr (by rw [Nat.mul_add]; omega)
    simp only [cellOf, Adj]
    rw [d1, d2]
    omega

theorem cellOf_inj {w i j : Nat} (h : cellOf w i = cellOf w j) : i = j := by
  simp only [cellOf, Prod.mk.injEq, Int.natCast_inj] at h
  rw [← Nat.div_add_mod i w, ← Nat.div_add_mod j w, h.1, h.2]

theorem occMask_mem (x : Ctx) (q : Q) (a : Array Bool) (tv : Bool) (k : Nat) {i : Nat}
    (hi : i ∈ x.rS) (h : ok a i k = true) :
    get (occMask x q a tv k) (pcode x (posV x q tv k i)) = true := by
  have hpos : 0 < occSize x := by unfold occSize; exact Nat.mul_pos (by omega) (by omega)
  have hlt : ∀ c, pcode x c < occSize x := fun c => Nat.mod_lt _ hpos
  have key : ∀ (l : List Nat) (m : Array Bool), m.size = occSize x →
      (i ∈ l ∨ get m (pcode x (posV x q tv k i)) = true) →
      get (l.foldl (fun m i => if ok a i k then m.setIfInBounds (pcode x (posV x q tv k i)) true else m) m)
        (pcode x (posV x q tv k i)) = true := by
    intro l
    induction l with
    | nil =>
      intro m _ h
      simpa using h
    | cons t l ih =>
      intro m hm h'
      simp only [List.foldl_cons]
      split
      next hok =>
        apply ih _ (by simpa using hm)
        by_cases ht : t = i
        · subst ht
          right
          unfold get
          rw [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds_self_of_lt (by rw [hm]; exact hlt _)]
          rfl
        · rcases h' with h' | h'
          · left; exact (List.mem_cons.1 h').resolve_left (fun e => ht e.symm)
          · right
            by_cases hc : pcode x (posV x q tv k t) = pcode x (posV x q tv k i)
            · unfold get
              rw [← hc, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds_self_of_lt (by rw [hm]; exact hlt _)]
              rfl
            · unfold get at h' ⊢
              rw [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds_ne hc, ← Array.getD_eq_getD_getElem?]
              exact h'
      next hok =>
        apply ih _ hm
        rcases h' with h' | h'
        · rcases List.mem_cons.1 h' with rfl | h'
          · exact absurd h hok
          · left; exact h'
        · right; exact h'
  exact key _ _ (by simp) (Or.inl hi)

/-- The crossing rule never fires on the possible cells of a true dissection. -/
theorem TA.crossBad (T : TA x q sl τ) {a : Array Bool} (h : Al x sl a) (e : XC) :
    Ex89.crossBad x q a e = false := by
  rw [Bool.eq_false_iff]
  intro hb
  simp only [Ex89.crossBad, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hb
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hka, hkb⟩, hne⟩, ha1⟩, ha2⟩, hb1⟩, hb2⟩, oa1⟩, oa2⟩, ob1⟩, ob2⟩, wa⟩, wb⟩, la⟩, lb⟩,
    ea, eb⟩, hx⟩ := hb
  have sa1 := T.only_slot h ha1 oa1
  have sa2 := T.only_slot h ha2 oa2
  have sb1 := T.only_slot h hb1 ob1
  have sb2 := T.only_slot h hb2 ob2
  have hview : ∀ (k i j : Nat), i < x.n → sl i = k → j ∈ nbrs x.w x.n i → sl j = k →
      Adj (posV x q e.tv k i) (posV x q e.tv k j) := by
    intro k i j hi hs hj hsj
    have hjn : j < x.n := nbrs_lt hi hj
    unfold posV
    split
    · have e1 := T.img i hi
      have e2 := T.img j hjn
      rw [hs] at e1
      rw [hsj] at e2
      rw [e1, e2]
      simpa using T.tadj i j hi hj (hsj.trans hs.symm)
    · exact nbrs_adj T.w_pos hj
  have walk : ∀ {k i j : Nat}, k < 4 → i < x.n → sl i = k → j < x.n → sl j = k →
      ∃ L : List Cell, IsWalk L ∧ L.head? = some (posV x q e.tv k i) ∧
        L.getLast? = some (posV x q e.tv k j) ∧
        ∀ c ∈ L, ∃ t, t < x.n ∧ sl t = k ∧ posV x q e.tv k t = c := by
    intro k i j hk hi hsi hj hsj
    exact piece_walk (T.conn k hk) (fun _ _ hi hj => nbrs_lt hi hj) (T.corner k hk)
      (fun i j hi hs hj hsj => hview k i j hi hs hj hsj) hi hsi hj hsj
  obtain ⟨Pa, wPa, h1a, h2a, inA⟩ := walk hka ha1 sa1 ha2 sa2
  obtain ⟨Pb, wPb, h1b, h2b, inB⟩ := walk hkb hb1 sb1 hb2 sb2
  let A : Cell → Prop := fun c => ∃ t, t < x.n ∧ sl t = e.ka ∧ posV x q e.tv e.ka t = c
  let B : Cell → Prop := fun c => ∃ t, t < x.n ∧ sl t = e.kb ∧ posV x q e.tv e.kb t = c
  have hAB : ∀ c, A c → B c → False := by
    rintro c ⟨t, ht, st, pt⟩ ⟨t', ht', st', pt'⟩
    have eq : t = t' := by
      have := pt.trans pt'.symm
      unfold posV at this
      split at this
      · have e1 := T.img t ht
        have e2 := T.img t' ht'
        rw [st] at e1
        rw [st'] at e2
        rw [e1, e2] at this
        simp only [Nat.add_sub_cancel] at this
        exact T.inj _ _ ht ht' (T.tinj _ _ (T.τ_lt t ht) (T.τ_lt t' ht') this)
      · exact cellOf_inj this
    subst eq
    exact hne (st.symm.trans st')
  have hS : ∀ {i}, i < x.n → i ∈ x.rS := by
    intro i hi; rw [T.hS]; exact List.mem_range.2 hi
  have occ : ∀ {k c}, (∃ t, t < x.n ∧ sl t = k ∧ posV x q e.tv k t = c) →
      get (occMask x q a e.tv k) (pcode x c) = true := by
    rintro k c ⟨t, ht, st, rfl⟩
    apply occMask_mem x q a e.tv k (hS ht)
    have := h t ht
    rwa [st] at this
  have edgeB : ∀ f ∈ edges (posV x q e.tv e.ka e.a2 :: e.Ka),
      ¬ (B (dualC f.1 f.2).1 ∧ B (dualC f.1 f.2).2) := by
    intro f hf hBB
    have := ea f hf
    simp only [occ hBB.1, occ hBB.2] at this
    simp at this
  have edgeA : ∀ f ∈ edges (posV x q e.tv e.kb e.b2 :: e.Kb),
      ¬ (A (dualS f.1 f.2).1 ∧ A (dualS f.1 f.2).2) := by
    intro f hf hAA
    have := eb f hf
    simp only [occ hAA.1, occ hAA.2] at this
    simp at this
  have := no_cross_edge hAB wPa wPb h1a h2a h1b h2b (isWalkB_sound wa) (isWalkB_sound wb) la lb
    inA inB edgeB edgeA
  rw [this] at hx
  simp at hx

end Crossing

theorem TA.applyFixedAt (T : TA x q sl τ) {a : Array Bool} (h : Al x sl a) {i : Nat} (hi : i < x.n) :
    Al x sl (Ex89.applyFixedAt q a i) := by
  unfold Ex89.applyFixedAt
  simp only
  split
  next ho =>
    split
    · exact h
    next hc =>
      have hk : (slots4.filter (ok a i)).headD 0 < 4 := by
        cases hf : slots4.filter (ok a i) with
        | nil => simp
        | cons y l =>
          have : y ∈ slots4 := (List.mem_filter.1 (by rw [hf]; simp)).1
          simpa using mem_slots4 this
      have hs := T.only_slot h hi ho
      have himg := T.img i hi
      rw [hs] at himg
      generalize imgAt q i ((slots4.filter (ok a i)).headD 0) = c at hc himg ⊢
      have key : ∀ (l : List Nat), (∀ k ∈ l, k < 4) → ∀ a : Array Bool, Al x sl a →
          Al x sl (l.foldl (fun a l =>
            if (preAtQ q (c - 1) l != 0 && preAtQ q (c - 1) l - 1 != i &&
                imgAt q (preAtQ q (c - 1) l - 1) l == c) = true
            then clearE a (preAtQ q (c - 1) l - 1) l else a) a) := by
        intro l
        induction l with
        | nil => intro _ a h; exact h
        | cons k l ih =>
          intro hl a h
          simp only [List.foldl_cons]
          apply ih (fun k hk => hl k (by simp [hk]))
          split
          next hcond =>
            simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hcond
            obtain ⟨⟨_, hne⟩, hi2⟩ := hcond
            intro i0 hi0
            rw [ok_clearE_of_ne (T.slot_lt i0 hi0) (hl k (by simp))]
            · exact h i0 hi0
            · rintro ⟨e1, e2⟩
              have h1 := T.img i0 hi0
              have h3 : imgAt q i0 k = c := by rw [e1]; exact hi2
              rw [e2, h3, himg] at h1
              have h2 : τ i = τ i0 := by omega
              have := T.inj _ _ hi hi0 h2
              rw [e1] at this
              exact hne this.symm
          next => exact h
      exact key slots4 (fun _ h => mem_slots4 h) a h
  next => exact h

theorem TA.applyFixed (T : TA x q sl τ) {a : Array Bool} (h : Al x sl a) :
    Al x sl (Ex89.applyFixed x q a) := by
  unfold Ex89.applyFixed
  have key : ∀ (l : List Nat), (∀ i ∈ l, i < x.n) → ∀ a : Array Bool, Al x sl a →
      Al x sl (l.foldl (Ex89.applyFixedAt q) a) := by
    intro l
    induction l with
    | nil => intro _ a h; exact h
    | cons i l ih =>
      intro hl a h
      simp only [List.foldl_cons]
      exact ih (fun k hk => hl k (by simp [hk])) _ (T.applyFixedAt h (hl i (by simp)))
  exact key _ (fun i hi => by rw [T.hS] at hi; exact List.mem_range.1 hi) a h

theorem TA.round (T : TA x q sl τ) {a : Array Bool} (h : Al x sl a) (o : Orc) :
    ∃ a', Ex89.round x q o a = some a' ∧ Al x sl a' := by
  have s2 : ∀ (l : List Nat), (∀ k ∈ l, k < 4) → ∀ a : Array Bool, Al x sl a →
      Al x sl (l.foldl (fun a k => Ex89.applyReach x a k (o.reach a k)) a) := by
    intro l
    induction l with
    | nil => intro _ a h; exact h
    | cons k l ih =>
      intro hl a h
      simp only [List.foldl_cons]
      exact ih (fun k hk => hl k (by simp [hk])) _ (T.applyReach h (hl k (by simp)) _)
  have s3 : ∀ (l : List (Nat × Nat × Array Bool)) (k : Nat) (a : Array Bool), Al x sl a →
      Al x sl (l.foldl (fun a e => Ex89.applyCut x a (e.1, k, e.2.1, e.2.2)) a) := by
    intro l k
    induction l with
    | nil => intro a h; exact h
    | cons e l ih =>
      intro a h
      simp only [List.foldl_cons]
      exact ih _ (T.applyCut h _)
  have s4 : ∀ (l : List Nat) (a : Array Bool), Al x sl a →
      Al x sl (l.foldl (fun a k => (o.cuts a k).foldl
        (fun a e => Ex89.applyCut x a (e.1, k, e.2.1, e.2.2)) a) a) := by
    intro l
    induction l with
    | nil => intro a h; exact h
    | cons k l ih =>
      intro a h
      simp only [List.foldl_cons]
      exact ih _ (s3 _ _ _ h)
  have h1 := T.applyFixed h
  have h2 := s2 slots4 (fun _ h => mem_slots4 h) _ h1
  have h3 := s4 slots4 _ h2
  have hcr : (o.cross (Ex89.applyFixed x q a)).any (Ex89.crossBad x q (Ex89.applyFixed x q a)) = false := by
    cases o.cross (Ex89.applyFixed x q a) with
    | none => rfl
    | some e => simpa using T.crossBad h1 e
  unfold Ex89.round
  simp only [hcr, Bool.false_eq_true, if_false]
  split
  · exact ⟨_, rfl, h1⟩
  · split
    · exact ⟨_, rfl, h2⟩
    · split
      · exact ⟨_, rfl, h3⟩
      · exact T.applyPot h3 _ _

theorem TA.fixL (T : TA x q sl τ) (o : Orc) (n : Nat) {a : Array Bool} (h : Al x sl a) :
    ∃ a', Ex89.fixL x q o n a = some a' ∧ Al x sl a' := by
  induction n generalizing a with
  | zero => exact ⟨a, rfl, h⟩
  | succ n ih =>
    obtain ⟨a1, e1, h1⟩ := T.round h o
    simp only [Ex89.fixL, e1]
    split
    · exact ⟨a1, rfl, h1⟩
    · exact ih h1

/-- `killed` never fires on the possible cells of a true dissection. -/
theorem TA.killed (T : TA x q sl τ) (o : Orc) (nf : Nat) {a : Array Bool} (h : Al x sl a) :
    Ex89.killed x q o nf a = false := by
  obtain ⟨a1, e1, _⟩ := T.fixL o nf h
  simp only [Ex89.killed, e1]

theorem TA.probeAll (T : TA x q sl τ) (o : Orc) (nf : Nat) {a : Array Bool} (h : Al x sl a) :
    Al x sl (Ex89.probeAll x q o nf a) := by
  have inner : ∀ (i : Nat) (l : List Nat), (∀ k ∈ l, k < 4) → ∀ a : Array Bool, Al x sl a →
      Al x sl (l.foldl (fun a k =>
        if ok a i k && Ex89.killed x q o nf (restrict a i k) then clearE a i k else a) a) := by
    intro i l
    induction l with
    | nil => intro _ a h; exact h
    | cons k l ih =>
      intro hl a h
      simp only [List.foldl_cons]
      apply ih (fun k hk => hl k (by simp [hk]))
      split
      next hc =>
        simp only [Bool.and_eq_true] at hc
        intro i0 hi0
        have hk : k < 4 := hl k (by simp)
        rw [ok_clearE_of_ne (T.slot_lt i0 hi0) hk]
        · exact h i0 hi0
        · rintro ⟨rfl, e⟩
          have hA : Al x sl (restrict a i0 k) := T.restrict_Al h (fun _ => e)
          rw [T.killed o nf hA] at hc
          simp at hc
      next => exact h
  unfold Ex89.probeAll
  have outer : ∀ (l : List Nat) (a : Array Bool), Al x sl a →
      Al x sl (l.foldl (fun a i => if onlyOK a i ((slots4.filter (ok a i)).headD 0) then a else
        slots4.foldl (fun a k =>
          if ok a i k && Ex89.killed x q o nf (restrict a i k) then clearE a i k else a) a) a) := by
    intro l
    induction l with
    | nil => intro a h; exact h
    | cons i l ih =>
      intro a h
      simp only [List.foldl_cons]
      apply ih
      split
      · exact h
      · exact inner i _ (fun _ h => mem_slots4 h) a h
  exact outer _ a h

/-- The main theorem of this file: the test never succeeds when a true dissection exists. -/
theorem TA.rookDead (T : TA x q sl τ) (o : Orc) (nf d f : Nat) {a : Array Bool} (h : Al x sl a) :
    (Ex89.rookDead x q o nf d f a).1 = false := by
  induction d generalizing a f with
  | zero => rfl
  | succ d ih =>
    obtain ⟨a1, e1, h1⟩ := T.fixL o nf h
    simp only [Ex89.rookDead, e1]
    split
    · rfl
    split
    · rfl
    next i _ =>
      -- A false value stays false, and the true slot makes the value false.
      have stay : ∀ (l : List Nat) (r : Bool × Nat), r.1 = false →
          (l.foldl (fun r k =>
            if !r.1 then r
            else if !ok a1 i k then r
            else Ex89.rookDead x q o nf d r.2 (restrict a1 i k)) r).1 = false := by
        intro l
        induction l with
        | nil => intro r hr; exact hr
        | cons k l ihl =>
          intro r hr
          simp only [List.foldl_cons]
          apply ihl
          simp [hr]
      have key : ∀ (l : List Nat) (r : Bool × Nat), (r.1 = false ∨ (i < x.n ∧ sl i ∈ l)) →
          (l.foldl (fun r k =>
            if !r.1 then r
            else if !ok a1 i k then r
            else Ex89.rookDead x q o nf d r.2 (restrict a1 i k)) r).1 = false := by
        intro l
        induction l with
        | nil =>
          intro r hr
          rcases hr with hr | ⟨_, hr⟩
          · exact hr
          · simp at hr
        | cons k l ihl =>
          intro r hr
          simp only [List.foldl_cons]
          rcases hr with hr | ⟨hi, hm⟩
          · exact stay _ _ (by simp [hr])
          · by_cases hk : k = sl i
            · apply stay
              subst hk
              rw [h1 i hi]
              by_cases hr1 : r.1 = true
              · simp only [hr1, Bool.not_true, Bool.false_eq_true, if_false, Bool.not_true]
                exact ih _ (T.restrict_Al h1 (fun _ => rfl))
              · simp [Bool.eq_false_iff.2 hr1]
            · apply ihl
              right
              exact ⟨hi, (List.mem_cons.1 hm).resolve_left (fun e => hk e.symm)⟩
      apply key
      by_cases hi : i < x.n
      · exact Or.inr ⟨hi, mem_slots4' (T.slot_lt i hi)⟩
      · left; simp [hi]

/-- The whole test never succeeds when a true dissection exists. -/
theorem TA.rookTest (T : TA x q sl τ) (o : Orc) (nf d b : Nat) {a : Array Bool} (h : Al x sl a) :
    Ex89.rookTest x q o nf d b a = false := by
  have key : ∀ (n : Nat) (a : Array Bool), Al x sl a →
      Ex89.rookTest.probeRounds d b x q o nf n a = false := by
    intro n
    induction n with
    | zero => intro a h; exact T.rookDead o nf d _ h
    | succ n ih =>
      intro a h
      have h1 := T.probeAll o nf h
      simp only [Ex89.rookTest.probeRounds, T.killed o nf h1, Bool.false_eq_true, if_false]
      split
      · exact T.rookDead o nf d _ h1
      · exact ih _ h1
  simp only [Ex89.rookTest, T.rookDead o nf d _ h, Bool.false_or]
  exact key _ _ h

theorem TA.alive_base (T : TA x q sl τ) :
    Al x sl (Array.ofFn (n := x.n * 4) fun e => imgAt q (e.val / 4) (e.val % 4) != 0) := by
  intro i hi
  have hk := T.slot_lt i hi
  have himg := T.img i hi
  have hlt : i * 4 + sl i < x.n * 4 := by
    have : (i + 1) * 4 ≤ x.n * 4 := Nat.mul_le_mul_right 4 hi
    rw [Nat.add_mul] at this
    omega
  have e1 : (i * 4 + sl i) / 4 = i := by omega
  have e2 : (i * 4 + sl i) % 4 = sl i := by omega
  unfold ok
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, dite_cond_eq_true (eq_true hlt)]
  simp only [Option.getD_some, e1, e2, himg]
  simp

theorem TA.alive0 (T : TA x q sl τ) : Al x sl (Ex89.alive0 x q) := by
  have key : ∀ (l : List Nat), (∀ k ∈ l, k < 4) → ∀ a : Array Bool, Al x sl a →
      Al x sl (l.foldl (fun a k => restrict a (x.cc k) k) a) := by
    intro l
    induction l with
    | nil => intro _ a h; exact h
    | cons k l ih =>
      intro hl a h
      simp only [List.foldl_cons]
      apply ih (fun k hk => hl k (by simp [hk]))
      apply T.restrict_Al h
      intro _
      exact (T.corner k (hl k (by simp))).2
  unfold Ex89.alive0
  exact key _ (fun _ h => mem_slots4 h) _ T.alive_base

end Ex89
