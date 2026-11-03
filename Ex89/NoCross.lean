/-!
# Two disjoint connected sets of cells cannot cross

Take a rook walk `C` on the cell centers and a rook walk `D` on the same grid shifted a little.
An edge of `C` and an edge of `D` cross only if they share a cell. Two closed curves in general
position cross an even number of times. So if a walk through `A` and a walk through `B` are closed
up outside `A` and `B`, the two closing parts cross an even number of times.

The checker needs only this last statement, for closing parts that it computes.

Coordinates: the center of cell `(x, y)` is `(2x, 2y)` and its shifted point is `(2x+1, 2y+1)`.
-/

namespace Ex89.NoCross

abbrev Cell := Int × Int

/-- Rook adjacency. -/
def Adj (p q : Cell) : Prop :=
  (p.1 = q.1 ∧ (p.2 = q.2 + 1 ∨ q.2 = p.2 + 1)) ∨ (p.2 = q.2 ∧ (p.1 = q.1 + 1 ∨ q.1 = p.1 + 1))

/-- Consecutive cells of the list are rook neighbors. -/
def IsWalk : List Cell → Prop
  | [] => True
  | [_] => True
  | p :: q :: l => Adj p q ∧ IsWalk (q :: l)

/-- The edges of a walk. -/
def edges : List Cell → List (Cell × Cell)
  | [] => []
  | [_] => []
  | p :: q :: l => (p, q) :: edges (q :: l)

/-- The center edge `p q` crosses the shifted edge `r s`.
A horizontal center edge in column `x` at height `h` crosses the shifted vertical edge in column `x`
from `h - 1` to `h`. A vertical center edge in column `x` from `y` to `y + 1` crosses the shifted
horizontal edge at height `y` from `x - 1` to `x`. -/
def Cross (p q r s : Cell) : Prop :=
  (p.2 = q.2 ∧ r.1 = s.1 ∧ min p.1 q.1 = r.1 ∧ min r.2 s.2 + 1 = p.2) ∨
  (p.1 = q.1 ∧ r.2 = s.2 ∧ min r.1 s.1 + 1 = p.1 ∧ min p.2 q.2 = r.2)

instance (p q r s : Cell) : Decidable (Cross p q r s) := by unfold Cross; infer_instance

/-- An edge that crosses shares a cell with the other edge. -/
theorem Cross.share {p q r s : Cell} (hpq : Adj p q) (hrs : Adj r s) (h : Cross p q r s) :
    p = r ∨ p = s ∨ q = r ∨ q = s := by
  obtain ⟨p1, p2⟩ := p; obtain ⟨q1, q2⟩ := q; obtain ⟨r1, r2⟩ := r; obtain ⟨s1, s2⟩ := s
  simp only [Adj, Cross, Prod.mk.injEq] at *
  omega

/-- The upward ray from the shifted point of `r` meets the center edge `p q`. -/
def Ray (p q r : Cell) : Bool :=
  decide (p.2 = q.2 ∧ min p.1 q.1 = r.1 ∧ r.2 + 1 ≤ p.2)

/-- The part of the column to the right of `r` above it, used for a horizontal step. -/
def InU (r s c : Cell) : Bool :=
  decide (r.2 = s.2 ∧ c.1 = max r.1 s.1 ∧ r.2 + 1 ≤ c.2)

/-- One center edge and one shifted step: the ray changes exactly by the crossing,
up to a term that sums to zero around the closed center walk. -/
theorem ray_step {p q r s : Cell} (hpq : Adj p q) (hrs : Adj r s) :
    (Ray p q r ^^ Ray p q s) = (decide (Cross p q r s) ^^ (InU r s p ^^ InU r s q)) := by
  obtain ⟨p1, p2⟩ := p; obtain ⟨q1, q2⟩ := q; obtain ⟨r1, r2⟩ := r; obtain ⟨s1, s2⟩ := s
  simp only [Adj, Ray, Cross, InU] at *
  by_cases h1 : p2 = q2 <;> by_cases h2 : r2 = s2 <;> simp only [h1, h2] <;> grind

/-- Exclusive or of a list of booleans. -/
def xorAll : List Bool → Bool
  | [] => false
  | b :: l => b ^^ xorAll l

@[simp] theorem xorAll_nil : xorAll [] = false := rfl
@[simp] theorem xorAll_cons (b : Bool) (l : List Bool) : xorAll (b :: l) = (b ^^ xorAll l) := rfl

theorem xorAll_append (a b : List Bool) : xorAll (a ++ b) = (xorAll a ^^ xorAll b) := by
  induction a with
  | nil => simp
  | cons x a ih => simp [ih]

theorem xor_comm4 (a b c d : Bool) : ((a ^^ b) ^^ (c ^^ d)) = ((a ^^ c) ^^ (b ^^ d)) := by
  revert a b c d; decide

/-- The last element of a nonempty list does not depend on the default. -/
theorem getD_indep (z : Cell) (l : List Cell) (a b : Cell) :
    (z :: l).getLast?.getD a = (z :: l).getLast?.getD b := by
  induction l generalizing z with
  | nil => rfl
  | cons y l ih => simpa [List.getLast?_cons_cons] using ih y

/-- Parity of the crossings between the edge lists `E` and `F`. -/
def crossE (E F : List (Cell × Cell)) : Bool :=
  xorAll (E.flatMap fun e => F.map fun f => decide (Cross e.1 e.2 f.1 f.2))

/-- Parity of the rays from `r` over the edge list `E`. -/
def rayE (E : List (Cell × Cell)) (r : Cell) : Bool :=
  xorAll (E.map fun e => Ray e.1 e.2 r)

/-- Parity of the crossings of the edge list `E` with one shifted edge. -/
def crossOne (E : List (Cell × Cell)) (r s : Cell) : Bool :=
  xorAll (E.map fun e => decide (Cross e.1 e.2 r s))

/-- The `InU` term telescopes along a walk. -/
theorem xor_inU {r s : Cell} : ∀ {l : List Cell} (c : Cell), l ≠ [] → l.head? = some c →
    xorAll ((edges l).map fun e => (InU r s e.1 ^^ InU r s e.2)) =
      (InU r s c ^^ InU r s (l.getLast?.getD c))
  | [], _, h, _ => absurd rfl h
  | [x], c, _, hc => by
      simp at hc; subst hc; simp [edges]
  | x :: y :: l, c, _, hc => by
      simp at hc; subst hc
      have ih := xor_inU (r := r) (s := s) (l := y :: l) y (by simp) rfl
      have hlast : (x :: y :: l).getLast?.getD x = (y :: l).getLast?.getD y := by
        rw [List.getLast?_cons_cons]; exact getD_indep y l x y
      simp only [edges, List.map_cons, xorAll_cons, ih, hlast]
      cases InU r s x <;> cases InU r s y <;> simp

/-- All edges of a walk are between neighbors. -/
theorem edges_adj : ∀ {l : List Cell}, IsWalk l → ∀ e ∈ edges l, Adj e.1 e.2
  | [], _, _, he => by simp [edges] at he
  | [_], _, _, he => by simp [edges] at he
  | _ :: y :: l, h, e, he => by
      simp only [edges, List.mem_cons] at he
      rcases he with rfl | he
      · exact h.1
      · exact edges_adj (l := y :: l) h.2 e he

/-- Along one shifted step, the ray from a closed center walk changes exactly by the crossings. -/
theorem ray_change {C : List Cell} (hC : IsWalk C) (c : Cell) (hhead : C.head? = some c)
    (hlast : C.getLast? = some c) {r s : Cell} (hrs : Adj r s) :
    (rayE (edges C) r ^^ rayE (edges C) s) = crossOne (edges C) r s := by
  have key : ∀ E : List (Cell × Cell), (∀ e ∈ E, Adj e.1 e.2) →
      (rayE E r ^^ rayE E s) =
        (crossOne E r s ^^ xorAll (E.map fun e => (InU r s e.1 ^^ InU r s e.2))) := by
    intro E hE
    induction E with
    | nil => simp [rayE, crossOne]
    | cons e E ih =>
        have h1 := ih (fun x hx => hE x (List.mem_cons_of_mem _ hx))
        have h2 := ray_step (hE e (List.mem_cons_self ..)) hrs
        simp only [rayE, crossOne, List.map_cons, xorAll_cons] at h1 ⊢
        rw [xor_comm4, h2, h1, xor_comm4]
  have hne : C ≠ [] := by
    intro h; simp [h] at hhead
  rw [key _ (edges_adj hC), xor_inU c hne hhead, hlast]
  simp

/-- Parity of crossings of the center edges `E` with a shifted walk telescopes. -/
theorem cross_walk {E : List (Cell × Cell)}
    (hstep : ∀ r s, Adj r s → (rayE E r ^^ rayE E s) = crossOne E r s) :
    ∀ {l : List Cell} (d : Cell), IsWalk l → l.head? = some d →
      xorAll ((edges l).map fun f => crossOne E f.1 f.2) =
        (rayE E d ^^ rayE E (l.getLast?.getD d))
  | [], _, _, h => by simp at h
  | [x], d, _, h => by
      simp at h; subst h; simp [edges]
  | x :: y :: l, d, hw, h => by
      simp at h; subst h
      have ih := cross_walk hstep (l := y :: l) y hw.2 rfl
      have hlast : (x :: y :: l).getLast?.getD x = (y :: l).getLast?.getD y := by
        rw [List.getLast?_cons_cons]; exact getD_indep y l x y
      simp only [edges, List.map_cons, xorAll_cons, ih, hlast, ← hstep x y hw.1]
      cases rayE E x <;> cases rayE E y <;> simp

/-- Exchange the order of a double exclusive or. -/
theorem xor_swap (E F : List (Cell × Cell)) :
    crossE E F = xorAll (F.map fun f => crossOne E f.1 f.2) := by
  induction E with
  | nil =>
      simp only [crossE, List.flatMap_nil, xorAll_nil, crossOne, List.map_nil]
      induction F with
      | nil => rfl
      | cons f F ih => simpa using ih
  | cons e E ih =>
      have h1 : crossE (e :: E) F =
          (xorAll (F.map fun f => decide (Cross e.1 e.2 f.1 f.2)) ^^ crossE E F) := by
        simp [crossE, List.flatMap_cons, xorAll_append]
      have h2 : ∀ F : List (Cell × Cell),
          xorAll (F.map fun f => crossOne (e :: E) f.1 f.2) =
            (xorAll (F.map fun f => decide (Cross e.1 e.2 f.1 f.2)) ^^
              xorAll (F.map fun f => crossOne E f.1 f.2)) := by
        intro F
        induction F with
        | nil => simp
        | cons f F ih2 =>
            simp only [List.map_cons, xorAll_cons, ih2]
            have : crossOne (e :: E) f.1 f.2 =
                (decide (Cross e.1 e.2 f.1 f.2) ^^ crossOne E f.1 f.2) := rfl
            rw [this, xor_comm4]
      rw [h1, ih, h2]

/-- **Two closed curves in general position cross an even number of times.** -/
theorem closed_even {C D : List Cell} (hC : IsWalk C) (hD : IsWalk D) {c d : Cell}
    (hc1 : C.head? = some c) (hc2 : C.getLast? = some c)
    (hd1 : D.head? = some d) (hd2 : D.getLast? = some d) :
    crossE (edges C) (edges D) = false := by
  rw [xor_swap, cross_walk (fun r s h => ray_change hC c hc1 hc2 h) d hD hd1, hd2]
  simp

/-- Appending parts of the first curve. -/
theorem crossE_append_left (E₁ E₂ F : List (Cell × Cell)) :
    crossE (E₁ ++ E₂) F = (crossE E₁ F ^^ crossE E₂ F) := by
  simp [crossE, List.flatMap_append, xorAll_append]

/-- Appending parts of the second curve. -/
theorem crossE_append_right (E F₁ F₂ : List (Cell × Cell)) :
    crossE E (F₁ ++ F₂) = (crossE E F₁ ^^ crossE E F₂) := by
  rw [xor_swap, xor_swap, xor_swap, List.map_append, xorAll_append]

/-- No edge pair crosses, so the parity is zero. -/
theorem crossE_eq_false {E F : List (Cell × Cell)}
    (h : ∀ e ∈ E, ∀ f ∈ F, ¬ Cross e.1 e.2 f.1 f.2) : crossE E F = false := by
  have one : ∀ (e : Cell × Cell) (F : List (Cell × Cell)), (∀ f ∈ F, ¬ Cross e.1 e.2 f.1 f.2) →
      xorAll (F.map fun f => decide (Cross e.1 e.2 f.1 f.2)) = false := by
    intro e F hF
    induction F with
    | nil => rfl
    | cons f F ih =>
        simp only [List.map_cons, xorAll_cons, decide_eq_false (hF f (List.mem_cons_self ..)),
          Bool.false_xor]
        exact ih fun g hg => hF g (List.mem_cons_of_mem _ hg)
  induction E with
  | nil => simp [crossE]
  | cons e E ih =>
      have h1 : crossE (e :: E) F =
          (xorAll (F.map fun f => decide (Cross e.1 e.2 f.1 f.2)) ^^ crossE E F) := by
        simp [crossE, List.flatMap_cons, xorAll_append]
      rw [h1, one e F (h e (List.mem_cons_self ..)),
        ih fun x hx f hf => h x (List.mem_cons_of_mem _ hx) f hf]
      rfl

/-- The cells of an edge belong to the walk. -/
theorem mem_of_edges : ∀ {l : List Cell} {e : Cell × Cell}, e ∈ edges l → e.1 ∈ l ∧ e.2 ∈ l
  | [], _, h => by simp [edges] at h
  | [_], _, h => by simp [edges] at h
  | x :: y :: l, e, h => by
      simp only [edges, List.mem_cons] at h
      rcases h with rfl | h
      · simp
      · have := mem_of_edges (l := y :: l) h
        exact ⟨List.mem_cons_of_mem _ this.1, List.mem_cons_of_mem _ this.2⟩

/-- Joining two walks at a common cell. -/
theorem join_walk : ∀ {l : List Cell} {c : Cell} {k : List Cell},
    IsWalk l → l.getLast? = some c → IsWalk (c :: k) →
      IsWalk (l ++ k) ∧ edges (l ++ k) = edges l ++ edges (c :: k)
  | [], _, _, _, h, _ => by simp at h
  | [x], c, k, _, h, hk => by
      simp at h; subst h; exact ⟨hk, by simp [edges]⟩
  | x :: y :: l, c, k, hw, h, hk => by
      rw [List.getLast?_cons_cons] at h
      have ih := join_walk (l := y :: l) hw.2 h hk
      refine ⟨⟨hw.1, ih.1⟩, ?_⟩
      show (x, y) :: edges ((y :: l) ++ k) = (x, y) :: edges (y :: l) ++ edges (c :: k)
      rw [ih.2]; rfl

/-- **Non-crossing.** `Pa` runs from `a1` to `a2` inside `A` and `Pb` runs from `b1` to `b2` inside
`B`, where `A` and `B` are disjoint. The walk `a2 :: Ka` ends at `a1` and avoids `B`, and the walk
`b2 :: Kb` ends at `b1` and avoids `A`. Then the two closing walks cross an even number of times. -/
theorem no_cross {A B : Cell → Prop} (hAB : ∀ c, A c → B c → False)
    {Pa Pb Ka Kb : List Cell} {a1 a2 b1 b2 : Cell}
    (hPa : IsWalk Pa) (hPb : IsWalk Pb)
    (ha1 : Pa.head? = some a1) (ha2 : Pa.getLast? = some a2)
    (hb1 : Pb.head? = some b1) (hb2 : Pb.getLast? = some b2)
    (hKa : IsWalk (a2 :: Ka)) (hKb : IsWalk (b2 :: Kb))
    (ha3 : (a2 :: Ka).getLast? = some a1) (hb3 : (b2 :: Kb).getLast? = some b1)
    (inA : ∀ c ∈ Pa, A c) (inB : ∀ c ∈ Pb, B c)
    (outB : ∀ c ∈ a2 :: Ka, ¬ B c) (outA : ∀ c ∈ b2 :: Kb, ¬ A c) :
    crossE (edges (a2 :: Ka)) (edges (b2 :: Kb)) = false := by
  obtain ⟨wC, eC⟩ := join_walk hPa ha2 hKa
  obtain ⟨wD, eD⟩ := join_walk hPb hb2 hKb
  have hne1 : Pa ≠ [] := by intro h; simp [h] at ha1
  have hne2 : Pb ≠ [] := by intro h; simp [h] at hb1
  have hhC : (Pa ++ Ka).head? = some a1 := by
    cases Pa with
    | nil => simp at ha1
    | cons x l => simpa using ha1
  have hhD : (Pb ++ Kb).head? = some b1 := by
    cases Pb with
    | nil => simp at hb1
    | cons x l => simpa using hb1
  have hlC : (Pa ++ Ka).getLast? = some a1 := by
    cases Ka with
    | nil =>
        simp only [List.append_nil]
        have : a2 = a1 := by simpa using ha3
        rw [ha2, this]
    | cons z l =>
        rw [List.getLast?_append]
        rw [List.getLast?_cons_cons] at ha3
        simp [ha3]
  have hlD : (Pb ++ Kb).getLast? = some b1 := by
    cases Kb with
    | nil =>
        simp only [List.append_nil]
        have : b2 = b1 := by simpa using hb3
        rw [hb2, this]
    | cons z l =>
        rw [List.getLast?_append]
        rw [List.getLast?_cons_cons] at hb3
        simp [hb3]
  have main := closed_even wC wD hhC hlC hhD hlD
  rw [eC, eD, crossE_append_left, crossE_append_right, crossE_append_right] at main
  have disj : ∀ {E F : List (Cell × Cell)}, (∀ e ∈ E, Adj e.1 e.2) → (∀ f ∈ F, Adj f.1 f.2) →
      (∀ e ∈ E, ∀ f ∈ F, e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2) → crossE E F = false := by
    intro E F hE hF h
    apply crossE_eq_false
    intro e he f hf hc
    have := Cross.share (hE e he) (hF f hf) hc
    have hh := h e he f hf
    grind
  have ne_of : ∀ {P Q : Cell → Prop} {x y : Cell}, P x → Q y → (∀ c, P c → Q c → False) → x ≠ y := by
    intro P Q x y hx hy hPQ h
    subst h; exact hPQ _ hx hy
  have h1 : crossE (edges Pa) (edges Pb) = false := by
    apply disj (edges_adj hPa) (edges_adj hPb)
    intro e he f hf
    have a := mem_of_edges he; have b := mem_of_edges hf
    exact ⟨ne_of (inA _ a.1) (inB _ b.1) hAB, ne_of (inA _ a.1) (inB _ b.2) hAB,
      ne_of (inA _ a.2) (inB _ b.1) hAB, ne_of (inA _ a.2) (inB _ b.2) hAB⟩
  have h2 : crossE (edges Pa) (edges (b2 :: Kb)) = false := by
    apply disj (edges_adj hPa) (edges_adj hKb)
    intro e he f hf
    have a := mem_of_edges he; have b := mem_of_edges hf
    have oa := fun c hc => outA c hc
    refine ⟨?_, ?_, ?_, ?_⟩ <;> intro h
    · exact oa _ b.1 (h ▸ inA _ a.1)
    · exact oa _ b.2 (h ▸ inA _ a.1)
    · exact oa _ b.1 (h ▸ inA _ a.2)
    · exact oa _ b.2 (h ▸ inA _ a.2)
  have h3 : crossE (edges (a2 :: Ka)) (edges Pb) = false := by
    apply disj (edges_adj hKa) (edges_adj hPb)
    intro e he f hf
    have a := mem_of_edges he; have b := mem_of_edges hf
    refine ⟨?_, ?_, ?_, ?_⟩ <;> intro h
    · exact outB _ a.1 (h ▸ inB _ b.1)
    · exact outB _ a.1 (h ▸ inB _ b.2)
    · exact outB _ a.2 (h ▸ inB _ b.1)
    · exact outB _ a.2 (h ▸ inB _ b.2)
  rw [h1, h2, h3] at main
  simpa using main

/-! ### The form used by the checker: a closing walk may pass through a cell of the other set, as
long as it crosses no edge of that set. This also covers two sets that touch only diagonally. -/

/-- The two cells of the shifted edge that crosses the center edge `p q`. -/
def dualC (p q : Cell) : Cell × Cell :=
  if p.2 = q.2 then ((min p.1 q.1, p.2 - 1), (min p.1 q.1, p.2))
  else ((p.1 - 1, min p.2 q.2), (p.1, min p.2 q.2))

/-- The two cells of the center edge that crosses the shifted edge `r s`. -/
def dualS (r s : Cell) : Cell × Cell :=
  if r.1 = s.1 then ((r.1, min r.2 s.2 + 1), (r.1 + 1, min r.2 s.2 + 1))
  else ((min r.1 s.1 + 1, r.2), (min r.1 s.1 + 1, r.2 + 1))

/-- A shifted edge that crosses a center edge has the cells of `dualC`. -/
theorem cross_dualC {p q r s : Cell} (hpq : Adj p q) (hrs : Adj r s) (h : Cross p q r s) :
    (r = (dualC p q).1 ∨ r = (dualC p q).2) ∧ (s = (dualC p q).1 ∨ s = (dualC p q).2) := by
  obtain ⟨p1, p2⟩ := p; obtain ⟨q1, q2⟩ := q; obtain ⟨r1, r2⟩ := r; obtain ⟨s1, s2⟩ := s
  simp only [Adj, Cross, dualC] at *
  split <;> simp only [Prod.mk.injEq] <;> omega

/-- A center edge that crosses a shifted edge has the cells of `dualS`. -/
theorem cross_dualS {p q r s : Cell} (hpq : Adj p q) (hrs : Adj r s) (h : Cross p q r s) :
    (p = (dualS r s).1 ∨ p = (dualS r s).2) ∧ (q = (dualS r s).1 ∨ q = (dualS r s).2) := by
  obtain ⟨p1, p2⟩ := p; obtain ⟨q1, q2⟩ := q; obtain ⟨r1, r2⟩ := r; obtain ⟨s1, s2⟩ := s
  simp only [Adj, Cross, dualS] at *
  split <;> simp only [Prod.mk.injEq] <;> omega

/-- **Non-crossing, edge form.** `Pa` runs from `a1` to `a2` inside `A` and `Pb` runs from `b1` to
`b2` inside `B`, where `A` and `B` are disjoint. For every edge of the walk `a2 :: Ka`, the shifted
edge across it does not lie in `B`. For every edge of `b2 :: Kb`, the center edge across it does not
lie in `A`. Then the two closing walks cross an even number of times. -/
theorem no_cross_edge {A B : Cell → Prop} (hAB : ∀ c, A c → B c → False)
    {Pa Pb Ka Kb : List Cell} {a1 a2 b1 b2 : Cell}
    (hPa : IsWalk Pa) (hPb : IsWalk Pb)
    (ha1 : Pa.head? = some a1) (ha2 : Pa.getLast? = some a2)
    (hb1 : Pb.head? = some b1) (hb2 : Pb.getLast? = some b2)
    (hKa : IsWalk (a2 :: Ka)) (hKb : IsWalk (b2 :: Kb))
    (ha3 : (a2 :: Ka).getLast? = some a1) (hb3 : (b2 :: Kb).getLast? = some b1)
    (inA : ∀ c ∈ Pa, A c) (inB : ∀ c ∈ Pb, B c)
    (edgeB : ∀ e ∈ edges (a2 :: Ka), ¬ (B (dualC e.1 e.2).1 ∧ B (dualC e.1 e.2).2))
    (edgeA : ∀ f ∈ edges (b2 :: Kb), ¬ (A (dualS f.1 f.2).1 ∧ A (dualS f.1 f.2).2)) :
    crossE (edges (a2 :: Ka)) (edges (b2 :: Kb)) = false := by
  obtain ⟨wC, eC⟩ := join_walk hPa ha2 hKa
  obtain ⟨wD, eD⟩ := join_walk hPb hb2 hKb
  have hhC : (Pa ++ Ka).head? = some a1 := by
    cases Pa with
    | nil => simp at ha1
    | cons x l => simpa using ha1
  have hhD : (Pb ++ Kb).head? = some b1 := by
    cases Pb with
    | nil => simp at hb1
    | cons x l => simpa using hb1
  have hlC : (Pa ++ Ka).getLast? = some a1 := by
    cases Ka with
    | nil =>
        simp only [List.append_nil]
        have : a2 = a1 := by simpa using ha3
        rw [ha2, this]
    | cons z l =>
        rw [List.getLast?_append]
        rw [List.getLast?_cons_cons] at ha3
        simp [ha3]
  have hlD : (Pb ++ Kb).getLast? = some b1 := by
    cases Kb with
    | nil =>
        simp only [List.append_nil]
        have : b2 = b1 := by simpa using hb3
        rw [hb2, this]
    | cons z l =>
        rw [List.getLast?_append]
        rw [List.getLast?_cons_cons] at hb3
        simp [hb3]
  have main := closed_even wC wD hhC hlC hhD hlD
  rw [eC, eD, crossE_append_left, crossE_append_right, crossE_append_right] at main
  have h1 : crossE (edges Pa) (edges Pb) = false := by
    apply crossE_eq_false
    intro e he f hf hc
    have a := mem_of_edges he; have b := mem_of_edges hf
    rcases Cross.share (edges_adj hPa e he) (edges_adj hPb f hf) hc with h | h | h | h
    · exact hAB _ (inA _ a.1) (h ▸ inB _ b.1)
    · exact hAB _ (inA _ a.1) (h ▸ inB _ b.2)
    · exact hAB _ (inA _ a.2) (h ▸ inB _ b.1)
    · exact hAB _ (inA _ a.2) (h ▸ inB _ b.2)
  have h2 : crossE (edges Pa) (edges (b2 :: Kb)) = false := by
    apply crossE_eq_false
    intro e he f hf hc
    have a := mem_of_edges he
    have d := cross_dualS (edges_adj hPa e he) (edges_adj hKb f hf) hc
    have hp := inA _ a.1; have hq := inA _ a.2
    refine edgeA f hf ?_
    -- The two ends of `e` are the two different cells of the dual edge.
    have hne : e.1 ≠ e.2 := by
      have := edges_adj hPa e he
      obtain ⟨⟨x1, y1⟩, ⟨x2, y2⟩⟩ := e
      simp only [Adj, Ne, Prod.mk.injEq] at *
      omega
    rcases d.1 with d1 | d1 <;> rcases d.2 with d2 | d2
    · exact absurd (d1.trans d2.symm) hne
    · exact ⟨d1 ▸ hp, d2 ▸ hq⟩
    · exact ⟨d2 ▸ hq, d1 ▸ hp⟩
    · exact absurd (d1.trans d2.symm) hne
  have h3 : crossE (edges (a2 :: Ka)) (edges Pb) = false := by
    apply crossE_eq_false
    intro e he f hf hc
    have b := mem_of_edges hf
    have d := cross_dualC (edges_adj hKa e he) (edges_adj hPb f hf) hc
    have hr := inB _ b.1; have hs := inB _ b.2
    refine edgeB e he ?_
    have hne : f.1 ≠ f.2 := by
      have := edges_adj hPb f hf
      obtain ⟨⟨x1, y1⟩, ⟨x2, y2⟩⟩ := f
      simp only [Adj, Ne, Prod.mk.injEq] at *
      omega
    rcases d.1 with d1 | d1 <;> rcases d.2 with d2 | d2
    · exact absurd (d1.trans d2.symm) hne
    · exact ⟨d1 ▸ hr, d2 ▸ hs⟩
    · exact ⟨d2 ▸ hs, d1 ▸ hr⟩
    · exact absurd (d1.trans d2.symm) hne
  rw [h1, h2, h3] at main
  simpa using main

/-! ### Walks inside a connected piece -/

theorem Adj.symm {p q : Cell} (h : Adj p q) : Adj q p := by
  obtain ⟨p1, p2⟩ := p; obtain ⟨q1, q2⟩ := q
  simp only [Adj] at *
  omega

/-- A walk read backwards is a walk. -/
theorem isWalk_reverse : ∀ {l : List Cell}, IsWalk l → IsWalk l.reverse
  | [], _ => trivial
  | [_], _ => trivial
  | x :: y :: l, h => by
      have ih := isWalk_reverse (l := y :: l) h.2
      have hl : (y :: l).reverse.getLast? = some y := by simp
      have := (join_walk (k := [x]) ih hl ⟨h.1.symm, trivial⟩).1
      simpa using this

/-- A set of numbered cells that is connected by the closure property `conn` has a walk from any
of its cells to any other, for a view `pos` of the cells that keeps neighbors adjacent. -/
theorem piece_walk {n : Nat} {sl : Nat → Nat} {nb : Nat → List Nat} {pos : Nat → Cell} {k c0 : Nat}
    (conn : ∀ P : Nat → Bool, P c0 = true →
      (∀ i j, i < n → P i = true → j ∈ nb i → sl j = k → P j = true) →
      ∀ i, i < n → sl i = k → P i = true)
    (hnb : ∀ i j, i < n → j ∈ nb i → j < n)
    (hc0 : c0 < n ∧ sl c0 = k)
    (hadj : ∀ i j, i < n → sl i = k → j ∈ nb i → sl j = k → Adj (pos i) (pos j))
    {i j : Nat} (hi : i < n) (hsi : sl i = k) (hj : j < n) (hsj : sl j = k) :
    ∃ L : List Cell, IsWalk L ∧ L.head? = some (pos i) ∧ L.getLast? = some (pos j) ∧
      ∀ c ∈ L, ∃ t, t < n ∧ sl t = k ∧ pos t = c := by
  classical
  have key : ∀ t, t < n → sl t = k → ∃ L : List Cell, IsWalk L ∧ L.head? = some (pos c0) ∧
      L.getLast? = some (pos t) ∧ ∀ c ∈ L, ∃ t, t < n ∧ sl t = k ∧ pos t = c := by
    let Q : Nat → Prop := fun t => t < n ∧ sl t = k ∧ ∃ L : List Cell, IsWalk L ∧
      L.head? = some (pos c0) ∧ L.getLast? = some (pos t) ∧
      ∀ c ∈ L, ∃ t, t < n ∧ sl t = k ∧ pos t = c
    have := conn (fun t => decide (Q t)) ?_ ?_
    · intro t ht hs
      have h := this t ht hs
      simp only [decide_eq_true_eq] at h
      exact h.2.2
    · simp only [decide_eq_true_eq]
      refine ⟨hc0.1, hc0.2, [pos c0], trivial, by simp, by simp, ?_⟩
      intro c hc
      simp only [List.mem_singleton] at hc
      exact ⟨c0, hc0.1, hc0.2, hc.symm⟩
    · intro a b ha hP hb hsb
      simp only [decide_eq_true_eq] at hP ⊢
      obtain ⟨_, hsa, L, hL, h1, h2, h3⟩ := hP
      have hbn := hnb a b ha hb
      have hA := hadj a b ha hsa hb hsb
      obtain ⟨w, _⟩ := join_walk (k := [pos b]) hL h2 ⟨hA, trivial⟩
      refine ⟨hbn, hsb, L ++ [pos b], w, ?_, by simp, ?_⟩
      · cases L with
        | nil => simp at h1
        | cons x l => simpa using h1
      · intro c hc
        rcases List.mem_append.1 hc with hc | hc
        · exact h3 c hc
        · simp only [List.mem_singleton] at hc
          exact ⟨b, hbn, hsb, hc.symm⟩
  obtain ⟨L1, w1, a1, b1, c1⟩ := key i hi hsi
  obtain ⟨L2, w2, a2, b2, c2⟩ := key j hj hsj
  have hrev := isWalk_reverse w1
  have hlast : L1.reverse.getLast? = some (pos c0) := by
    rw [List.getLast?_reverse]; exact a1
  have hd : L2 = pos c0 :: L2.tail := by
    cases L2 with
    | nil => simp at a2
    | cons x l => simp at a2; simp [a2]
  rw [hd] at w2
  obtain ⟨w, _⟩ := join_walk hrev hlast w2
  refine ⟨L1.reverse ++ L2.tail, w, ?_, ?_, ?_⟩
  · cases hL : L1.reverse with
    | nil =>
        rw [hL] at hlast; simp at hlast
    | cons x l =>
        have : L1.reverse.head? = some (pos i) := by rw [List.head?_reverse]; exact b1
        rw [hL] at this
        simpa using this
  · cases hT : L2.tail with
    | nil =>
        rw [hT] at hd
        rw [hd] at b2
        have e : pos c0 = pos j := by simpa using b2
        simp only [List.append_nil]; rw [hlast, e]
    | cons z l =>
        rw [hd, hT] at b2
        rw [List.getLast?_cons_cons] at b2
        rw [List.getLast?_append]
        simp [b2]
  · intro c hc
    rcases List.mem_append.1 hc with hc | hc
    · exact c1 c (List.mem_reverse.1 hc)
    · exact c2 c (List.mem_of_mem_tail hc)

end Ex89.NoCross
