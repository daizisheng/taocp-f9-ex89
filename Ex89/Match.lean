import Ex89.Prop
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

/-- The untrusted oracle. -/
structure Orc where
  pot : Array Bool → Array Nat × Array Nat
  reach : Array Bool → Nat → Array Bool
  cuts : Array Bool → Nat → List (Nat × Nat × Array Bool)
  pick : Array Bool → Option Nat

def countA (a : Array Bool) : Nat := a.foldl (fun c b => if b then c + 1 else c) 0

/-- One round of all rules. -/
def round (x : Ctx) (q : Q) (o : Orc) (a : Array Bool) : Option (Array Bool) :=
  let p := o.pot a
  match applyPot x q a p.1 p.2 with
  | none => none
  | some a1 =>
    let a2 := slots4.foldl (fun a k => applyReach x a k (o.reach a k)) a1
    some (slots4.foldl (fun a k =>
      (o.cuts a k).foldl (fun a e => applyCut x a (e.1, k, e.2.1, e.2.2)) a) a2)

/-- Repeat the rounds until nothing changes. -/
def fixL (x : Ctx) (q : Q) (o : Orc) : Nat → Array Bool → Option (Array Bool)
  | 0, a => some a
  | n + 1, a =>
    match round x q o a with
    | none => none
    | some a' => if countA a' == countA a then some a' else fixL x q o n a'

/-- `true` means that no rookwise connected dissection uses these placements. -/
def rookDead (x : Ctx) (q : Q) (o : Orc) (nf : Nat) : Nat → Array Bool → Bool
  | 0, _ => false
  | d + 1, a =>
    match fixL x q o nf a with
    | none => true
    | some a' =>
      match o.pick a' with
      | none => false
      | some i => decide (i < x.n) &&
        slots4.all fun k => !ok a' i k || rookDead x q o nf d (restrict a' i k)

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

theorem TA.round (T : TA x q sl τ) {a : Array Bool} (h : Al x sl a) (o : Orc) :
    ∃ a', Ex89.round x q o a = some a' ∧ Al x sl a' := by
  unfold Ex89.round
  obtain ⟨a1, e1, h1⟩ := T.applyPot h (o.pot a).1 (o.pot a).2
  simp only [e1]
  refine ⟨_, rfl, ?_⟩
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
  exact s4 _ _ (s2 _ (fun _ h => mem_slots4 h) _ h1)

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

/-- The main theorem of this file: the test never succeeds when a true dissection exists. -/
theorem TA.rookDead (T : TA x q sl τ) (o : Orc) (nf d : Nat) {a : Array Bool} (h : Al x sl a) :
    Ex89.rookDead x q o nf d a = false := by
  induction d generalizing a with
  | zero => rfl
  | succ d ih =>
    obtain ⟨a1, e1, h1⟩ := T.fixL o nf h
    simp only [Ex89.rookDead, e1]
    split
    · rfl
    next i _ =>
      by_cases hi : i < x.n
      · rw [Bool.eq_false_iff]
        intro hall
        simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true,
          Bool.not_eq_true'] at hall
        have hsl := mem_slots4' (T.slot_lt i hi)
        rcases hall.2 (sl i) hsl with e | e
        · rw [h1 i hi] at e; simp at e
        · rw [ih (T.restrict_Al h1 (fun _ => rfl))] at e
          simp at e
      · simp [hi]

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
