import Ex89.Rook
import Ex89.Oracle
/-!
The search for rookwise connected dissections. It is the search of `Ex89.Check`, and when
propagation finds no contradiction it applies the stronger test of `Ex89.Match`.
-/
namespace Ex89

/-- All cells of one color are joined by rook steps inside that color. -/
def ConnP (w : Nat) (p : Nat → Nat → Fin 4) : Prop :=
  ∀ x y x' y', x < w → y < w → x' < w → y' < w → p x y = p x' y' →
    RookPath w (fun a b => p a b = p x y) x y x' y'

/-! ### The search -/

@[inline] def deadR (c : Cfg) (q : Q) (rS rT : List Nat) : Bool :=
  dead q rS rT c.nS (St.init c.nS c.nT) || testRook c q

def check22R (cf : Cfg) (a b e d : Fin 4) (ord : Tab → Tab → Tab → Tab → Q) : Bool :=
  let cf := persist cf
  let rS := persist (List.range cf.nS); let rT := persist (List.range cf.nT)
  let pv := persist cf.mkPv
  let pt := persist (cf.mkPT pv)
  let tP2 := Task.spawn fun _ => cf.pairs pv pt e d
  let P1 := persist (cf.pairs pv pt a b)
  let P2 := persist tP2.get
  parAll P1 fun pq => P2.all fun rs =>
    deadR cf (ord pq.1.t pq.2.t rs.1.t rs.2.t) rS rT

def check13R (cf : Cfg) : Bool :=
  let cf := persist cf
  let rS := persist (List.range cf.nS); let rT := persist (List.range cf.nT)
  let pv := persist cf.mkPv
  let t0 := persist (cf.mkTab 0 idMotion)
  let L2 := persist (cf.packs pv 2); let L3 := persist (cf.packs pv 3)
  let n := 32 * cf.w * cf.w + 8
  let pt := persist (cf.mkPT pv)
  let cs := persist (cf.tcorners 1)
  let P23 := persist (parMap L2 fun p2 => (p2, L3.filter fun p3 => ptd pt 3 2 p3.t p2.t))
  let P1M := persist (parMap (cf.packs pv 1) fun p1 =>
    (p1, maskOf n cf.w (L3.filter fun p3 => ptd pt 3 1 p3.t p1.t)))
  let CH := persist (chunksF 256 P23.length P23)
  parAll (P1M.flatMap fun pm => CH.map fun ch => (pm, ch)) fun x =>
    let p1 := x.1.1
    let mask := x.1.2
    x.2.all fun e =>
      !ptd pt 1 2 p1.t e.1.t ||
      e.2.all fun p3 =>
        !get mask (motionId cf.w p3.m % n) ||
        !cornersOk cs [p1.t, e.1.t, p3.t] ||
        deadR cf ⟨t0, p1.t, e.1.t, p3.t⟩ rS rT

def ordDiag (ta tb te td : Tab) : Q := ⟨ta, te, tb, td⟩
def ordAdj (ta tb te td : Tab) : Q := ⟨ta, tb, te, td⟩

def caseR (u v w : Nat) : Nat → Bool
  | 0 => check22R (cfgDiag u v w) 0 2 1 3 ordDiag
  | 1 => check22R (cfgAdj u v w) 0 1 2 3 ordAdj
  | 2 => check13R (cfgU u v w)
  | _ => check13R (cfgV u v w)

/-- The whole search for rookwise connected dissections. -/
def checkR (u v w : Nat) : Bool := parAllD [0, 1, 2, 3] (caseR u v w)

theorem checkR_eq (u v w : Nat) : checkR u v w =
    (check22R (cfgDiag u v w) 0 2 1 3 ordDiag && check22R (cfgAdj u v w) 0 1 2 3 ordAdj &&
     check13R (cfgU u v w) && check13R (cfgV u v w)) := by
  simp [checkR, parAllD_eq, caseR, Bool.and_assoc]

/-! ### Rook neighbors -/

theorem nbrs_right {w a b : Nat} (ha : a + 1 < w) (hb : b < w) :
    (a + 1) * w + b ∈ nbrs w (w * w) (a * w + b) := by
  have e : a * w + b + w = (a + 1) * w + b := by rw [Nat.add_mul]; omega
  have hlt : (a + 1) * w + b < w * w := code_lt ha hb
  unfold nbrs
  simp only [e, hlt, ite_true]
  split <;> split <;> split <;> simp

theorem nbrs_left {w a b : Nat} (_hb : b < w) (_h : a + 1 < w) :
    a * w + b ∈ nbrs w (w * w) ((a + 1) * w + b) := by
  have e : (a + 1) * w + b - w = a * w + b := by rw [Nat.add_mul]; omega
  have hle : w ≤ (a + 1) * w + b := by rw [Nat.add_mul]; omega
  unfold nbrs
  simp only [hle, ite_true, e]
  split
  · split <;> simp
  · split <;> simp

theorem nbrs_up {w a b : Nat} (ha : a < w) (hb : b + 1 < w) :
    a * w + (b + 1) ∈ nbrs w (w * w) (a * w + b) := by
  have hm : (a * w + b + 1) % w = b + 1 := by
    rw [Nat.add_assoc, Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hb]
  have hlt : a * w + b + 1 < w * w := by
    have := code_lt ha hb
    omega
  have hc : ((a * w + b + 1) % w != 0 && decide (a * w + b + 1 < w * w)) = true := by
    simp [hm, hlt]
  have e : a * w + (b + 1) = a * w + b + 1 := by omega
  unfold nbrs
  simp only [hc, ite_true, e]
  split <;> simp

theorem nbrs_down {w a b : Nat} (hb : b + 1 < w) :
    a * w + b ∈ nbrs w (w * w) (a * w + (b + 1)) := by
  have hm : (a * w + (b + 1)) % w = b + 1 := by
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hb]
  have e : a * w + (b + 1) - 1 = a * w + b := by omega
  have hc : ((a * w + (b + 1)) % w != 0) = true := by simp [hm]
  unfold nbrs
  simp only [hc, ite_true, e]
  simp

/-! ### The true dissection, seen from the search -/

variable {c : Cfg} {D : Dissection c.u c.v c.w}

/-- The tables of the true motions, in the order of the slots. -/
def trueQ (c : Cfg) (D : Dissection c.u c.v c.w) : Q :=
  ⟨c.mkTab 0 (D.motion 0), c.mkTab 1 (D.motion 1), c.mkTab 2 (D.motion 2), c.mkTab 3 (D.motion 3)⟩

theorem imgAt_trueQ (c : Cfg) (D : Dissection c.u c.v c.w) (i : Nat) (k : Fin 4) :
    imgAt (trueQ c D) i k.val = (c.mkTab k (D.motion k)).img.getD i 0 := by
  revert k
  apply slot_cases <;> rfl

def trueSl (c : Cfg) (D : Dissection c.u c.v c.w) (i : Nat) : Nat :=
  (D.piece (i / c.w) (i % c.w)).val

def trueTau (c : Cfg) (D : Dissection c.u c.v c.w) (i : Nat) : Nat :=
  let x := i / c.w; let y := i % c.w
  tcode c.u c.v (c.side (D.piece x y)) ((D.motion (D.piece x y)).imgX c.w x y).toNat
    ((D.motion (D.piece x y)).imgY c.w x y).toNat

theorem Fits.code_eq (_F : Fits c D) {x y : Nat} (hx : x < c.w) (hy : y < c.w) :
    (x * c.w + y) / c.w = x ∧ (x * c.w + y) % c.w = y := by
  have hi := code_lt hx hy
  obtain ⟨_, h2, h3⟩ := code_split hi
  have := code_inj hy h2 (h3.symm : x * c.w + y = _)
  exact ⟨this.1.symm, this.2.symm⟩

theorem ccOf_eq (w : Nat) (k : Fin 4) : ccOf w k.val = cornerX w k * w + cornerY w k := by
  revert k
  apply slot_cases <;> simp [ccOf, cornerX, cornerY]

theorem Fits.trueEdge (_F : Fits c D) {i : Nat} (hi : i < c.w * c.w) : TrueEdge c D i (trueTau c D i) := by
  obtain ⟨hx, hy, he⟩ := code_split hi
  exact ⟨_, _, hx, hy, he.symm, rfl⟩

theorem Fits.toTA (F : Fits c D) (hC : ConnP c.w D.piece) :
    TA c.ctx (trueQ c D) (trueSl c D) (trueTau c D) := by
  have hqq : ∀ k, c.mkTab k (D.motion k) = (trueQ c D).t0 ∨ c.mkTab k (D.motion k) = (trueQ c D).t1 ∨
      c.mkTab k (D.motion k) = (trueQ c D).t2 ∨ c.mkTab k (D.motion k) = (trueQ c D).t3 := by
    apply slot_cases <;> simp [trueQ]
  have G := F.graph (trueQ c D) hqq
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i _; exact (D.piece _ _).isLt
  · intro i hi
    have hi' : i < c.w * c.w := hi
    obtain ⟨hx, hy, _⟩ := code_split hi'
    have hm := F.maps hx hy
    have hin := (inSq_iff _ _ _).2 hm
    show imgAt (trueQ c D) i (D.piece (i / c.w) (i % c.w)).val = _
    rw [imgAt_trueQ, mkTab_img c _ _ hi', hin]
    simp [trueTau]
  · intro i hi
    have hi' : i < c.w * c.w := hi
    obtain ⟨hx, hy, _⟩ := code_split hi'
    obtain ⟨m1, m2, m3, m4⟩ := F.maps hx hy
    apply tcode_lt
    · rw [sideOf_eq]; omega
    · rw [sideOf_eq]; omega
  · intro i i' hi hi' e
    have h1 := F.trueEdge (i := i) hi
    have h2 := F.trueEdge (i := i') hi'
    rw [← e] at h2
    exact G.inj _ _ _ h1 h2
  · intro j hj
    obtain ⟨i, hi, hR, _⟩ := G.bwd j hj
    refine ⟨i, hi, ?_⟩
    exact G.func _ _ _ (F.trueEdge (i := i) hi) hR
  · intro k hk
    obtain ⟨cx, cy⟩ := F.corner_lt ⟨k, hk⟩
    have e := ccOf_eq c.w ⟨k, hk⟩
    have e' : c.ctx.cc k = cornerX c.w ⟨k, hk⟩ * c.w + cornerY c.w ⟨k, hk⟩ := e
    obtain ⟨d1, d2⟩ := F.code_eq cx cy
    refine ⟨by rw [e']; exact code_lt cx cy, ?_⟩
    show (D.piece (c.ctx.cc k / c.w) (c.ctx.cc k % c.w)).val = k
    rw [e', d1, d2, F.hcorner]
  · intro k hk P hP hclo i hi hs
    have hi' : i < c.w * c.w := hi
    obtain ⟨hx, hy, he⟩ := code_split hi'
    let K : Fin 4 := ⟨k, hk⟩
    obtain ⟨cx, cy⟩ := F.corner_lt K
    have e0 : c.ctx.cc k = cornerX c.w K * c.w + cornerY c.w K := ccOf_eq c.w K
    have hpk : D.piece (i / c.w) (i % c.w) = K := Fin.ext hs
    have hcK := F.hcorner K
    have hp := hC _ _ _ _ cx cy hx hy (by rw [hcK, hpk])
    rw [hcK] at hp
    have key : ∀ a b, RookPath c.w (fun a b => D.piece a b = K) (cornerX c.w K) (cornerY c.w K) a b →
        a < c.w ∧ b < c.w ∧ D.piece a b = K ∧ P (a * c.w + b) = true := by
      intro a b p
      have ssl : ∀ a b, a < c.w → b < c.w → D.piece a b = K → trueSl c D (a * c.w + b) = k := by
        intro a b h1 h2 h3
        obtain ⟨d1, d2⟩ := F.code_eq h1 h2
        show (D.piece ((a * c.w + b) / c.w) ((a * c.w + b) % c.w)).val = k
        rw [d1, d2, h3]
      induction p with
      | refl => exact ⟨cx, cy, hcK, by rw [← e0]; exact hP⟩
      | @right a b _ h1 hq ih =>
        obtain ⟨i1, i2, _, i4⟩ := ih
        have hlt := code_lt i1 i2
        exact ⟨h1, i2, hq, hclo _ _ hlt i4 (nbrs_right h1 i2) (ssl _ _ h1 i2 hq)⟩
      | @left a b _ hq ih =>
        obtain ⟨i1, i2, _, i4⟩ := ih
        have ha : a < c.w := by omega
        have hlt := code_lt i1 i2
        exact ⟨ha, i2, hq, hclo _ _ hlt i4 (nbrs_left i2 i1) (ssl _ _ ha i2 hq)⟩
      | @up a b _ h1 hq ih =>
        obtain ⟨i1, i2, _, i4⟩ := ih
        have hlt := code_lt i1 i2
        exact ⟨i1, h1, hq, hclo _ _ hlt i4 (nbrs_up i1 h1) (ssl _ _ i1 h1 hq)⟩
      | @down a b _ hq ih =>
        obtain ⟨i1, i2, _, i4⟩ := ih
        have hb : b < c.w := by omega
        have hlt := code_lt i1 i2
        exact ⟨i1, hb, hq, hclo _ _ hlt i4 (nbrs_down i2) (ssl _ _ i1 hb hq)⟩
    have := (key _ _ hp).2.2.2
    rw [he] at this
    exact this

theorem Fits.not_deadR (F : Fits c D) (hC : ConnP c.w D.piece) :
    deadR c (trueQ c D) (List.range c.nS) (List.range c.nT) = false := by
  have hqq : ∀ k, c.mkTab k (D.motion k) = (trueQ c D).t0 ∨ c.mkTab k (D.motion k) = (trueQ c D).t1 ∨
      c.mkTab k (D.motion k) = (trueQ c D).t2 ∨ c.mkTab k (D.motion k) = (trueQ c D).t3 := by
    apply slot_cases <;> simp [trueQ]
  have T := F.toTA hC
  simp only [deadR, testRook, F.not_dead _ hqq, Bool.false_or]
  exact T.rookDead _ _ _ T.alive0

theorem Fits.check22R_false (F : Fits c D) (hC : ConnP c.w D.piece) {a b e d : Fin 4}
    {ord : Tab → Tab → Tab → Tab → Q}
    (hord : ord (c.mkTab a (D.motion a)) (c.mkTab b (D.motion b)) (c.mkTab e (D.motion e))
      (c.mkTab d (D.motion d)) = trueQ c D)
    (h1 : a ≠ b) (h2 : e ≠ d) (s1 : c.side a = c.side b) (s2 : c.side e = c.side d)
    (g1 : ∀ j, c.side j = c.side a → j = a ∨ j = b) (g2 : ∀ j, c.side j = c.side e → j = e ∨ j = d)
    (h : check22R c a b e d ord = true) : False := by
  have hs : ∀ (f : Unit → List (Pack × Pack)), (Task.spawn f).get = f () := fun _ => rfl
  simp only [check22R, persist_eq, hs, parAll_eq, List.all_eq_true] at h
  have := h _ (F.pair_mem h1 s1 g1) _ (F.pair_mem h2 s2 g2)
  simp only [hord] at this
  rw [F.not_deadR hC] at this
  simp at this

theorem Fits.check13R_false (F : Fits c D) (hC : ConnP c.w D.piece)
    (s1 : c.side 1 = c.side 2) (s2 : c.side 1 = c.side 3)
    (g : ∀ j, c.side j = c.side 1 → j = 1 ∨ j = 2 ∨ j = 3) (hf : c.fixed 0 = true)
    (h : check13R c = true) : False := by
  simp only [check13R, persist_eq, parAll_eq, parMap_eq, List.all_eq_true] at h
  have hd := F.not_deadR hC
  have h0 := F.hfix 0 hf
  have hQ : trueQ c D = ⟨c.mkTab 0 idMotion, c.mkTab 1 (D.motion 1), c.mkTab 2 (D.motion 2),
      c.mkTab 3 (D.motion 3)⟩ := by simp [trueQ, h0]
  rw [hQ] at hd
  let P1 : Pack := ⟨D.motion 1, c.mkTab 1 (D.motion 1)⟩
  let P2 : Pack := ⟨D.motion 2, c.mkTab 2 (D.motion 2)⟩
  let P3 : Pack := ⟨D.motion 3, c.mkTab 3 (D.motion 3)⟩
  have h31 : P3 ∈ (c.packs c.mkPv 3).filter fun p3 => ptd (c.mkPT c.mkPv) 3 1 p3.t P1.t :=
    List.mem_filter.2 ⟨F.pack_mem 3, F.ptd_true (by decide) (by rw [s2])⟩
  have h32 : P3 ∈ (c.packs c.mkPv 3).filter fun p3 => ptd (c.mkPT c.mkPv) 3 2 p3.t P2.t :=
    List.mem_filter.2 ⟨F.pack_mem 3, F.ptd_true (by decide) (by rw [← s2, s1])⟩
  have hc : cornersOk (c.tcorners 1) [P1.t, P2.t, P3.t] = true := F.corners_true 1 (by
    intro j hj
    rcases g j hj with rfl | rfl | rfl <;> simp [P1, P2, P3])
  have hp12 : ptd (c.mkPT c.mkPv) 1 2 P1.t P2.t = true := F.ptd_true (by decide) s1
  have hE : (P2, (c.packs c.mkPv 3).filter fun p3 => ptd (c.mkPT c.mkPv) 3 2 p3.t P2.t) ∈
      (c.packs c.mkPv 2).map fun p2 => (p2, (c.packs c.mkPv 3).filter
        fun p3 => ptd (c.mkPT c.mkPv) 3 2 p3.t p2.t) :=
    List.mem_map.2 ⟨P2, F.pack_mem 2, rfl⟩
  have hE2 : (P2, (c.packs c.mkPv 3).filter fun p3 => ptd (c.mkPT c.mkPv) 3 2 p3.t P2.t) ∈
      (chunksF 256 ((c.packs c.mkPv 2).map fun p2 => (p2, (c.packs c.mkPv 3).filter
        fun p3 => ptd (c.mkPT c.mkPv) 3 2 p3.t p2.t)).length
        ((c.packs c.mkPv 2).map fun p2 => (p2, (c.packs c.mkPv 3).filter
        fun p3 => ptd (c.mkPT c.mkPv) 3 2 p3.t p2.t))).flatten := by
    rw [flatten_chunksF]; exact hE
  obtain ⟨ch, hch, he⟩ := List.mem_flatten.1 hE2
  have := h ((P1, maskOf (32 * c.w * c.w + 8) c.w ((c.packs c.mkPv 3).filter
      fun p3 => ptd (c.mkPT c.mkPv) 3 1 p3.t P1.t)), ch)
    (List.mem_flatMap.2 ⟨_, List.mem_map.2 ⟨P1, F.pack_mem 1, rfl⟩, List.mem_map.2 ⟨ch, hch, rfl⟩⟩) _ he
  simp only [hp12, Bool.not_true, Bool.false_or, List.all_eq_true] at this
  have := this P3 h32
  rw [get_maskOf (by omega) h31, hc] at this
  simp only [Bool.not_true, Bool.false_or] at this
  rw [hd] at this
  simp at this

/-! ### Connectivity survives the normal form -/

theorem ConnP.path_rot {w : Nat} {p : Nat → Nat → Fin 4} {C : Fin 4} {a0 b0 a b : Nat}
    (ha0 : a0 < w) (hb0 : b0 < w) (P : RookPath w (fun a b => p a b = C) a0 b0 a b) :
    a < w ∧ b < w ∧ RookPath w (fun c d => p d (w - 1 - c) = C) (w - 1 - b0) a0 (w - 1 - b) a := by
  induction P with
  | refl => exact ⟨ha0, hb0, RookPath.refl _ _⟩
  | @right a b _ h1 hq ih =>
    obtain ⟨i1, i2, ih⟩ := ih
    have e : w - 1 - (w - 1 - b) = b := by omega
    exact ⟨h1, i2, RookPath.up ih h1 (by simpa only [e] using hq)⟩
  | @left a b _ hq ih =>
    obtain ⟨i1, i2, ih⟩ := ih
    have e : w - 1 - (w - 1 - b) = b := by omega
    exact ⟨by omega, i2, RookPath.down ih (by simpa only [e] using hq)⟩
  | @up a b _ h1 hq ih =>
    obtain ⟨i1, i2, ih⟩ := ih
    have e0 : w - 1 - b = (w - 1 - (b + 1)) + 1 := by omega
    have e : w - 1 - (w - 1 - (b + 1)) = b + 1 := by omega
    rw [e0] at ih
    exact ⟨i1, h1, RookPath.left ih (by simpa only [e] using hq)⟩
  | @down a b _ hq ih =>
    obtain ⟨i1, i2, ih⟩ := ih
    have e0 : w - 1 - b = (w - 1 - (b + 1)) + 1 := by omega
    have e : w - 1 - (w - 1 - b) = b := by omega
    refine ⟨i1, by omega, ?_⟩
    rw [e0]
    refine RookPath.right ih (by omega) ?_
    rw [← e0]
    simpa only [e] using hq

theorem ConnP.rot {u v w : Nat} {D : Dissection u v w} (h : ConnP w D.piece) : ConnP w D.rot.piece := by
  intro x y x' y' hx hy hx' hy' e
  have hp := h y (w - 1 - x) y' (w - 1 - x') hy (by omega) hy' (by omega) e
  obtain ⟨_, _, q⟩ := ConnP.path_rot (a0 := y) (b0 := w - 1 - x) hy (by omega) hp
  have e1 : w - 1 - (w - 1 - x) = x := by omega
  have e2 : w - 1 - (w - 1 - x') = x' := by omega
  rw [e1, e2] at q
  exact q

theorem exists_canonC {u v w : Nat} (D : Dissection u v w) (hC : ConnP w D.piece) :
    ∃ D' : Dissection u v w, A (pat D' 0) (pat D' 1) (pat D' 2) (pat D' 3) = true ∧ ConnP w D'.piece := by
  obtain ⟨a1, a2, a3, a4⟩ := pat_rot D
  obtain ⟨b1, b2, b3, b4⟩ := pat_rot D.rot
  obtain ⟨c1, c2, c3, c4⟩ := pat_rot D.rot.rot
  have r1 := ConnP.rot hC
  have r2 := ConnP.rot r1
  have r3 := ConnP.rot r2
  rcases A_rot (pat D 0) (pat D 1) (pat D 2) (pat D 3) with h | h | h | h
  · exact ⟨D, h, hC⟩
  · exact ⟨D.rot, by rw [a1, a2, a3, a4]; exact h, r1⟩
  · exact ⟨D.rot.rot, by rw [b1, b2, b3, b4, a1, a2, a3, a4]; exact h, r2⟩
  · exact ⟨D.rot.rot.rot, by rw [c1, c2, c3, c4, b1, b2, b3, b4, a1, a2, a3, a4]; exact h, r3⟩

theorem path_mono {w : Nat} {P P' : Nat → Nat → Prop} (hPP : ∀ a b, P a b → P' a b) {x y a b : Nat}
    (p : RookPath w P x y a b) : RookPath w P' x y a b := by
  induction p with
  | refl => exact RookPath.refl _ _
  | right _ h1 hq ih => exact RookPath.right ih h1 (hPP _ _ hq)
  | left _ hq ih => exact RookPath.left ih (hPP _ _ hq)
  | up _ h1 hq ih => exact RookPath.up ih h1 (hPP _ _ hq)
  | down _ hq ih => exact RookPath.down ih (hPP _ _ hq)

theorem exists_namedC {u v w : Nat} (D : Dissection u v w) (huw : u < w) (hvw : v < w)
    (hC : ConnP w D.piece) :
    ∃ D' : Dissection u v w, (∀ k, D'.toU k = pat D k) ∧
      (∀ k, D'.piece (cornerX w k) (cornerY w k) = k) ∧ ConnP w D'.piece := by
  let a : Fin 4 → Fin 4 := fun k => D.piece (cornerX w k) (cornerY w k)
  obtain ⟨h1, h2⟩ := perm_facts (a 0) (a 1) (a 2) (a 3)
    (corner_ne D huw hvw _ _ (by decide)) (corner_ne D huw hvw _ _ (by decide))
    (corner_ne D huw hvw _ _ (by decide)) (corner_ne D huw hvw _ _ (by decide))
    (corner_ne D huw hvw _ _ (by decide)) (corner_ne D huw hvw _ _ (by decide))
  have htau : ∀ k, tauOf (a 0) (a 1) (a 2) (a 3) k = a k := by apply slot_cases <;> rfl
  refine ⟨D.relabel _ _ h1, ?_, ?_, ?_⟩
  · intro k
    show D.toU (tauOf (a 0) (a 1) (a 2) (a 3) k) = _
    rw [htau]; rfl
  · intro k
    show sigOf (a 0) (a 1) (a 2) (a k) = k
    have := h2 k
    rw [htau] at this
    exact this
  · intro x y x' y' hx hy hx' hy' e
    have e' : D.piece x y = D.piece x' y' := by
      have := congrArg (tauOf (a 0) (a 1) (a 2) (a 3)) e
      simpa only [Dissection.relabel, h1] using this
    refine path_mono ?_ (hC x y x' y' hx hy hx' hy' e')
    intro c d hcd
    simp only [Dissection.relabel, hcd]

/-- **The soundness of the search for rookwise connected dissections.** -/
theorem no_rook_of_check {u v w : Nat} (hu : 0 < u) (hv : 0 < v) (huw : u < w) (hvw : v < w)
    (h : checkR u v w = true) : NoRookDissection u v w := by
  intro ox oy ho R
  have hw : 0 < w := by omega
  have c0 : ConnP w (R.toDissection ho).piece := R.connected
  rw [checkR_eq] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨hd, ha⟩, hU⟩, hV⟩ := h
  obtain ⟨D, hA, cD⟩ := exists_canonC (R.toDissection ho) c0
  obtain ⟨E, es, ec, cE⟩ := exists_namedC D huw hvw cD
  have e0 := es 0; have e1 := es 1; have e2 := es 2; have e3 := es 3
  rcases h0 : pat D 0 <;> rcases h1 : pat D 1 <;> rcases h2 : pat D 2 <;> rcases h3 : pat D 3 <;>
    simp [h0, h1, h2, h3, A] at hA <;> rw [h0] at e0 <;> rw [h1] at e1 <;> rw [h2] at e2 <;> rw [h3] at e3
  · obtain ⟨x, y, _, _, hb, _⟩ := E.surjective true 0 0 (by simp only [ite_true, InSquare]; omega)
    have : ∀ k, E.toU k = false := by apply slot_cases <;> assumption
    rw [this] at hb; simp at hb
  · -- pattern `F F T T`
    obtain ⟨E1, p1, t1, o1, a1, b1, c1⟩ := exists_fixed E 0
    obtain ⟨E2, p2, t2, o2, a2, b2, c2⟩ := exists_fixed E1 2
    have hc : ∀ k, E2.piece (cornerX w k) (cornerY w k) = k := by intro k; rw [p2, p1]; exact ec k
    have o : E1.toU 0 ≠ E1.toU 2 := by rw [t1, e0, e2]; simp
    have m0 := o2 0 o
    refine Fits.check22R_false (c := cfgAdj u v w) (D := E2) ⟨?_, hc, ?_, ?_, hu, hv, huw, hvw⟩
      (by show ConnP w E2.piece; rw [p2, p1]; exact cE)
      (a := 0) (b := 1) (e := 2) (d := 3) (ord := ordAdj) rfl (by decide) (by decide) rfl rfl
      (by apply slot_cases <;> simp [cfgAdj]) (by apply slot_cases <;> simp [cfgAdj]) ha
    · rw [t2, t1]; apply slot_cases <;> simp [cfgAdj, e0, e1, e2, e3]
    · apply slot_cases <;> intro hk <;> simp_all [cfgAdj]
    · intro k hk; simp [cfgAdj] at hk
  · -- pattern `F T F T`
    obtain ⟨E1, p1, t1, o1, a1, b1, c1⟩ := exists_fixed E 0
    obtain ⟨E2, p2, t2, o2, a2, b2, c2⟩ := exists_fixed E1 1
    have hc : ∀ k, E2.piece (cornerX w k) (cornerY w k) = k := by intro k; rw [p2, p1]; exact ec k
    have o : E1.toU 0 ≠ E1.toU 1 := by rw [t1, e0, e1]; simp
    have m0 := o2 0 o
    refine Fits.check22R_false (c := cfgDiag u v w) (D := E2) ⟨?_, hc, ?_, ?_, hu, hv, huw, hvw⟩
      (by show ConnP w E2.piece; rw [p2, p1]; exact cE)
      (a := 0) (b := 2) (e := 1) (d := 3) (ord := ordDiag) rfl (by decide) (by decide) rfl rfl
      (by apply slot_cases <;> simp [cfgDiag]) (by apply slot_cases <;> simp [cfgDiag]) hd
    · rw [t2, t1]; apply slot_cases <;> simp [cfgDiag, e0, e1, e2, e3]
    · apply slot_cases <;> intro hk <;> simp_all [cfgDiag]
    · intro k hk; simp [cfgDiag] at hk
  · -- pattern `F T T T`
    obtain ⟨E1, p1, t1, o1, a1, b1, c1⟩ := exists_fixed E 0
    obtain ⟨E2, p2, t2, o2, a2, b2, c2⟩ := exists_fixed E1 1
    have hc : ∀ k, E2.piece (cornerX w k) (cornerY w k) = k := by intro k; rw [p2, p1]; exact ec k
    have o : E1.toU 0 ≠ E1.toU 1 := by rw [t1, e0, e1]; simp
    have m0 := o2 0 o
    have hz : E2.motion 0 = idMotion := by
      apply fixed_zero E2 hw 0 (hc 0) (by simp [cornerX, cornerY])
      · rw [t2, t1, e0]; simpa using hv
      · rw [t2, t1, e0]
        apply slot_cases <;> simp [e1, e2, e3]
      · rw [m0]; exact a1
      · rw [m0]; exact b1
      · rw [m0]; exact c1
    refine Fits.check13R_false (c := cfgV u v w) (D := E2) ⟨?_, hc, ?_, ?_, hu, hv, huw, hvw⟩
      (by show ConnP w E2.piece; rw [p2, p1]; exact cE)
      rfl rfl (by apply slot_cases <;> simp [cfgV]) rfl hV
    · rw [t2, t1]; apply slot_cases <;> simp [cfgV, e0, e1, e2, e3]
    · apply slot_cases <;> intro hk <;> simp_all [cfgV]
    · apply slot_cases <;> intro hk <;> simp_all [cfgV]
  · -- pattern `T F F F`
    obtain ⟨E1, p1, t1, o1, a1, b1, c1⟩ := exists_fixed E 0
    obtain ⟨E2, p2, t2, o2, a2, b2, c2⟩ := exists_fixed E1 1
    have hc : ∀ k, E2.piece (cornerX w k) (cornerY w k) = k := by intro k; rw [p2, p1]; exact ec k
    have o : E1.toU 0 ≠ E1.toU 1 := by rw [t1, e0, e1]; simp
    have m0 := o2 0 o
    have hz : E2.motion 0 = idMotion := by
      apply fixed_zero E2 hw 0 (hc 0) (by simp [cornerX, cornerY])
      · rw [t2, t1, e0]; simpa using hu
      · rw [t2, t1, e0]
        apply slot_cases <;> simp [e1, e2, e3]
      · rw [m0]; exact a1
      · rw [m0]; exact b1
      · rw [m0]; exact c1
    refine Fits.check13R_false (c := cfgU u v w) (D := E2) ⟨?_, hc, ?_, ?_, hu, hv, huw, hvw⟩
      (by show ConnP w E2.piece; rw [p2, p1]; exact cE)
      rfl rfl (by apply slot_cases <;> simp [cfgU]) rfl hU
    · rw [t2, t1]; apply slot_cases <;> simp [cfgU, e0, e1, e2, e3]
    · apply slot_cases <;> intro hk <;> simp_all [cfgU]
    · apply slot_cases <;> intro hk <;> simp_all [cfgU]
  · obtain ⟨x, y, _, _, hb, _⟩ := E.surjective false 0 0 (by simp only [Bool.false_eq_true, ite_false, InSquare]; omega)
    have : ∀ k, E.toU k = true := by apply slot_cases <;> assumption
    rw [this] at hb; simp at hb

end Ex89
