import Ex89.T22.Defs
/-!
# Generic counting theorems for the 2+2 lemmas

* **G1** (`G1`, closed structure): a list of `V` cells `q_i` with prescribed available slot sets,
  together with a perfect matching `es` of its darts into "full edges" whose two ends hit the same
  source cell, forces `es.length = V` in any normal form `NF`.  (Double counting of
  `x(i,k) = [σ(q_i) = k]`, see `PROOF.md`, section 3.4.)
* **G2** (`G2`, pigeonhole): pairwise distinct source cells, all of whose possible hitters lie in
  a list `P`, are at most `P.length` many.
* **G3** (`elim_sound`, root elimination): if every atom produced by `elim S` holds, the
  constraint system `S` (each constraint `c·r + l ≥ 0` touches one coordinate of the root, with
  coefficient `±1` or `±2`) has an integer solution `r`.
-/
namespace Ex89.T22

/-! ## Small finite facts -/

theorem Fin4.cases {P : Fin 4 → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) : ∀ k, P k
  | ⟨0, _⟩ => h0
  | ⟨1, _⟩ => h1
  | ⟨2, _⟩ => h2
  | ⟨3, _⟩ => h3

theorem Fin8.cases {P : Fin 8 → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) (h4 : P 4)
    (h5 : P 5) (h6 : P 6) (h7 : P 7) : ∀ k, P k
  | ⟨0, _⟩ => h0
  | ⟨1, _⟩ => h1
  | ⟨2, _⟩ => h2
  | ⟨3, _⟩ => h3
  | ⟨4, _⟩ => h4
  | ⟨5, _⟩ => h5
  | ⟨6, _⟩ => h6
  | ⟨7, _⟩ => h7

theorem partner_ne (k : Fin 4) : partner k ≠ k := by revert k; decide
theorem partner_partner (k : Fin 4) : partner (partner k) = k := by revert k; decide
theorem partner_parity (k : Fin 4) : (partner k).val % 2 = k.val % 2 := by revert k; decide
theorem parity_cases (s k : Fin 4) (h : s.val % 2 = k.val % 2) : s = k ∨ s = partner k := by
  revert s k; decide

theorem side_partner (p : Params) (k : Fin 4) : p.side (partner k) = p.side k := by
  revert k; apply Fin4.cases <;> rfl

theorem side_of_parity (p : Params) (s k : Fin 4) (h : s.val % 2 = k.val % 2) :
    p.side s = p.side k := by
  rcases parity_cases s k h with rfl | rfl
  · rfl
  · exact side_partner p k

/-- The motions are injective (the orientation matrices are invertible). -/
theorem src_inj (c : Case) (p : Params) (k : Fin 4) (x y x' y' : Int)
    (hx : srcX c p k x y = srcX c p k x' y') (hy : srcY c p k x y = srcY c p k x' y') :
    x = x' ∧ y = y' := by
  unfold srcX at hx; unfold srcY at hy
  generalize c.ori k = o at hx hy
  revert o
  apply Fin8.cases <;> intro hx hy <;> simp [oriM] at hx hy <;> omega

/-! ## G1: closed structures -/

def allK : List (Fin 4) := [0, 1, 2, 3]

theorem mem_allK (k : Fin 4) : k ∈ allK := by revert k; decide

/-- The darts `(i, k)`, `i < V`, `k` a used slot of vertex `i`. -/
def darts (V : Nat) (used : Nat → Fin 4 → Bool) : List (Nat × Fin 4) :=
  (List.range V).flatMap (fun i => (allK.filter (used i)).map (fun k => (i, k)))

theorem mem_darts {V : Nat} {used : Nat → Fin 4 → Bool} {d : Nat × Fin 4} :
    d ∈ darts V used ↔ d.1 < V ∧ used d.1 d.2 = true := by
  obtain ⟨i, k⟩ := d
  simp only [darts, List.mem_flatMap, List.mem_range, List.mem_map, List.mem_filter,
    Prod.mk.injEq]
  constructor
  · rintro ⟨a, ha, b, ⟨_, hb⟩, rfl, rfl⟩; exact ⟨ha, hb⟩
  · rintro ⟨hi, hu⟩; exact ⟨i, hi, k, ⟨mem_allK k, hu⟩, rfl, rfl⟩

theorem sum_filter_ind (u : Fin 4 → Bool) (s : Fin 4) (hs : u s = true) :
    ((allK.filter u).map (fun k => if s = k then 1 else 0)).sum = 1 := by
  revert hs
  cases h0 : u 0 <;> cases h1 : u 1 <;> cases h2 : u 2 <;> cases h3 : u 3 <;>
    revert s <;> apply Fin4.cases <;> simp [allK, List.filter, h0, h1, h2, h3]

theorem sum_darts (V : Nat) (used : Nat → Fin 4 → Bool) (x : Nat × Fin 4 → Nat)
    (hx : ∀ i < V, ((allK.filter (used i)).map (fun k => x (i, k))).sum = 1) :
    ((darts V used).map x).sum = V := by
  induction V with
  | zero => simp [darts]
  | succ n ih =>
    have := ih (fun i hi => hx i (by omega))
    simp only [darts, List.range_succ, List.flatMap_append, List.map_append,
      List.sum_append_nat] at this ⊢
    rw [this]
    have h := hx n (by omega)
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_map] at h ⊢
    rw [show (x ∘ fun k => (n, k)) = (fun k => x (n, k)) from rfl, h]

theorem sum_pairs (es : List ((Nat × Fin 4) × (Nat × Fin 4))) (x : Nat × Fin 4 → Nat)
    (h : ∀ e ∈ es, x e.1 + x e.2 = 1) :
    ((es.flatMap (fun e => [e.1, e.2])).map x).sum = es.length := by
  induction es with
  | nil => simp
  | cons e es ih =>
    simp only [List.flatMap_cons, List.map_append, List.sum_append_nat, List.length_cons]
    rw [ih (fun e' he' => h e' (List.mem_cons_of_mem _ he'))]
    have := h e List.mem_cons_self
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    omega

/-- **G1.** Vertices `q_i = (qx i, qy i)`, `i < V`, lie in `W` and have exactly the slots
`used i` available.  `es` is a list of pairs of darts (`(i,k)`, `(j, partner k)`) whose two ends
have the same source cell, and the darts are exactly the ends of `es` (as a multiset).  Then
`es.length = V`. -/
theorem G1 (c : Case) (p : Params) (N : NF c p) (V : Nat) (qx qy : Nat → Int)
    (used : Nat → Fin 4 → Bool) (es : List ((Nat × Fin 4) × (Nat × Fin 4)))
    (hW : ∀ i < V, InW p (qx i) (qy i))
    (hA : ∀ i < V, ∀ k, Avail c p k (qx i) (qy i) ↔ used i k = true)
    (hE : ∀ e ∈ es, e.2.2 = partner e.1.2 ∧
      srcX c p e.1.2 (qx e.1.1) (qy e.1.1) = srcX c p e.2.2 (qx e.2.1) (qy e.2.1) ∧
      srcY c p e.1.2 (qx e.1.1) (qy e.1.1) = srcY c p e.2.2 (qx e.2.1) (qy e.2.1))
    (hP : (darts V used).Perm (es.flatMap (fun e => [e.1, e.2]))) :
    es.length = V := by
  let x : Nat × Fin 4 → Nat := fun d => if N.σ (qx d.1) (qy d.1) = d.2 then 1 else 0
  have h1 : ((darts V used).map x).sum = V := by
    apply sum_darts
    intro i hi
    exact sum_filter_ind (used i) _ ((hA i hi _).1 (N.avail _ _ (hW i hi)))
  have h2 : ((darts V used).map x).sum = es.length := by
    rw [(hP.map x).sum_nat]
    apply sum_pairs
    intro e he
    obtain ⟨⟨i, k⟩, ⟨j, k'⟩⟩ := e
    have hm1 : (i, k) ∈ darts V used :=
      hP.mem_iff.2 (List.mem_flatMap.2 ⟨_, he, by simp⟩)
    have hm2 : (j, k') ∈ darts V used :=
      hP.mem_iff.2 (List.mem_flatMap.2 ⟨_, he, by simp⟩)
    rw [mem_darts] at hm1 hm2
    obtain ⟨hk', hsx, hsy⟩ := hE _ he
    simp only at hk' hsx hsy
    subst hk'
    have hav : Avail c p k (qx i) (qy i) := (hA i hm1.1 k).2 hm1.2
    obtain ⟨_, h0X, hXs, h0Y, hYs⟩ := hav
    obtain ⟨z1, z2, hzW, hzpar, hzX, hzY⟩ :=
      N.surj k _ _ h0X hXs h0Y hYs
    have hWi := hW i hm1.1
    have hWj := hW j hm2.1
    simp only [x]
    -- the source cell is hit by q_i (via k) or by q_j (via partner k), not both
    have hnot : ¬ (N.σ (qx i) (qy i) = k ∧ N.σ (qx j) (qy j) = partner k) := by
      rintro ⟨hi, hj⟩
      have := N.inj _ _ _ _ hWi hWj (by rw [hi, hj, partner_parity]) (by rw [hi, hj, hsx])
        (by rw [hi, hj, hsy])
      obtain ⟨e1, e2⟩ := this
      rw [← e1, ← e2, hi] at hj; exact partner_ne k hj.symm
    rcases parity_cases _ _ hzpar with hσ | hσ
    · have hσ' := hσ
      rw [hσ] at hzX hzY
      obtain ⟨e1, e2⟩ := src_inj c p k _ _ _ _ hzX hzY
      rw [e1, e2] at hσ'
      by_cases hj : N.σ (qx j) (qy j) = partner k
      · exact absurd ⟨hσ', hj⟩ hnot
      · simp [hσ', hj]
    · have hσ' := hσ
      rw [hσ] at hzX hzY
      rw [hsx] at hzX; rw [hsy] at hzY
      obtain ⟨e1, e2⟩ := src_inj c p _ _ _ _ _ hzX hzY
      rw [e1, e2] at hσ'
      by_cases hi : N.σ (qx i) (qy i) = k
      · exact absurd ⟨hi, hσ'⟩ hnot
      · simp [hσ', hi]
  omega

/-! ## G2: pigeonhole -/

/-- **G2.** `srcs` are source cells `(k, X, Y)` (in the target square of `k`), pairwise distinct
when they belong to the same square (`k` mod 2); every cell that can hit one of them lies in `P`.
Then there are at most `P.length` of them. -/
theorem G2 (c : Case) (p : Params) (N : NF c p) (srcs : List (Fin 4 × Int × Int))
    (P : List (Int × Int))
    (hS : ∀ s ∈ srcs, 0 ≤ s.2.1 ∧ s.2.1 < p.side s.1 ∧ 0 ≤ s.2.2 ∧ s.2.2 < p.side s.1)
    (hD : srcs.Pairwise (fun a b => a.1.val % 2 = b.1.val % 2 → a.2 ≠ b.2))
    (hH : ∀ s ∈ srcs, ∀ x y, InW p x y → (N.σ x y).val % 2 = s.1.val % 2 →
      srcX c p (N.σ x y) x y = s.2.1 → srcY c p (N.σ x y) x y = s.2.2 → (x, y) ∈ P) :
    srcs.length ≤ P.length := by
  classical
  let Hit : Fin 4 × Int × Int → Int × Int → Prop := fun s z =>
    InW p z.1 z.2 ∧ (N.σ z.1 z.2).val % 2 = s.1.val % 2 ∧
      srcX c p (N.σ z.1 z.2) z.1 z.2 = s.2.1 ∧ srcY c p (N.σ z.1 z.2) z.1 z.2 = s.2.2
  have hex : ∀ s ∈ srcs, ∃ z, Hit s z := by
    intro s hs
    obtain ⟨h1, h2, h3, h4⟩ := hS s hs
    obtain ⟨x, y, hxy⟩ := N.surj s.1 _ _ h1 h2 h3 h4
    exact ⟨(x, y), hxy⟩
  let hit : Fin 4 × Int × Int → Int × Int := fun s =>
    if h : ∃ z, Hit s z then Classical.choose h else (0, 0)
  have hhit : ∀ s ∈ srcs, Hit s (hit s) := by
    intro s hs
    have h := hex s hs
    simp only [hit, dif_pos h]
    exact Classical.choose_spec h
  have hnd : (srcs.map hit).Nodup := by
    rw [List.Nodup, List.pairwise_map]
    refine hD.imp_of_mem ?_
    intro a b ha hb hab heq
    have h1 := hhit a ha
    have h2 := hhit b hb
    rw [← heq] at h2
    generalize hit a = z at h1 h2
    obtain ⟨_, pa, xa, ya⟩ := h1
    obtain ⟨_, pb, xb, yb⟩ := h2
    apply hab (by omega)
    exact Prod.ext (xa.symm.trans xb) (ya.symm.trans yb)
  have hsub : srcs.map hit ⊆ P := by
    intro z hz
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hz
    obtain ⟨h1, h2, h3, h4⟩ := hhit s hs
    exact hH s hs _ _ h1 h2 h3 h4
  have := List.Nodup.length_le_of_subset hnd hsub
  simpa using this

/-! ## G3: root elimination -/

/-- A constraint `co.1 * rx + co.2 * ry + l ≥ 0` on the root `(rx, ry)`. -/
abbrev Cn := (Int × Int) × LF

def Cn.holds (p : Params) (rx ry : Int) (cn : Cn) : Prop :=
  0 ≤ cn.1.1 * rx + cn.1.2 * ry + cn.2.eval p

instance (p : Params) (rx ry : Int) (cn : Cn) : Decidable (cn.holds p rx ry) := by
  unfold Cn.holds; infer_instance

/-- Combination of a lower bound `c1 r + l1 ≥ 0` and an upper bound `-c2 r + l2 ≥ 0`. -/
def pairVal (c1 a1 c2 a2 : Int) : Int :=
  if c1 = 1 ∧ c2 = 1 then a1 + a2
  else if c1 = 2 ∧ c2 = 1 then a1 + 2 * a2
  else if c1 = 1 ∧ c2 = 2 then 2 * a1 + a2
  else a1 + a2 - 1

def pairLF (c1 : Int) (l1 : LF) (c2 : Int) (l2 : LF) : LF :=
  if c1 = 1 ∧ c2 = 1 then LF.add l1 l2
  else if c1 = 2 ∧ c2 = 1 then LF.add l1 (LF.smul 2 l2)
  else if c1 = 1 ∧ c2 = 2 then LF.add (LF.smul 2 l1) l2
  else LF.addc (LF.add l1 l2) (-1)

theorem pairLF_eval (c1 : Int) (l1 : LF) (c2 : Int) (l2 : LF) (p : Params) :
    (pairLF c1 l1 c2 l2).eval p = pairVal c1 (l1.eval p) c2 (l2.eval p) := by
  unfold pairLF pairVal
  by_cases h1 : c1 = 1 ∧ c2 = 1
  · rw [if_pos h1, if_pos h1, LF.eval_add]
  · rw [if_neg h1, if_neg h1]
    by_cases h2 : c1 = 2 ∧ c2 = 1
    · rw [if_pos h2, if_pos h2, LF.eval_add, LF.eval_smul]
    · rw [if_neg h2, if_neg h2]
      by_cases h3 : c1 = 1 ∧ c2 = 2
      · rw [if_pos h3, if_pos h3, LF.eval_add, LF.eval_smul]
      · rw [if_neg h3, if_neg h3, LF.eval_addc, LF.eval_add]; omega

/-- Coefficient of coordinate `ix` (`false` = x, `true` = y) and of the other coordinate. -/
def Cn.coef (ix : Bool) (cn : Cn) : Int := if ix then cn.1.2 else cn.1.1
def Cn.other (ix : Bool) (cn : Cn) : Int := if ix then cn.1.1 else cn.1.2

def lowsOf (ix : Bool) (S : List Cn) : List (Int × LF) :=
  S.filterMap (fun cn => if cn.other ix = 0 ∧ 0 < cn.coef ix then some (cn.coef ix, cn.2) else none)
def highsOf (ix : Bool) (S : List Cn) : List (Int × LF) :=
  S.filterMap (fun cn => if cn.other ix = 0 ∧ cn.coef ix < 0 then some (-cn.coef ix, cn.2) else none)
def constsOf (S : List Cn) : List LF :=
  S.filterMap (fun cn => if cn.1.1 = 0 ∧ cn.1.2 = 0 then some cn.2 else none)

def pairsFor (ix : Bool) (S : List Cn) : List LF :=
  (lowsOf ix S).eraseDups.flatMap (fun lo => (highsOf ix S).eraseDups.map
    (fun hi => pairLF lo.1 lo.2 hi.1 hi.2))

def coefOK (cn : Cn) : Bool :=
  (cn.1.1 == 0 || cn.1.2 == 0) && cn.1.1.natAbs ≤ 2 && cn.1.2.natAbs ≤ 2

/-- `l` is (syntactically) a nonnegative constant. -/
def LF.isNNConstFrom : List Int → Nat → Bool
  | [], _ => true
  | c :: l, i => (if i < 11 then c == 0 else if i = 11 then decide (0 ≤ c) else true) &&
      LF.isNNConstFrom l (i + 1)

theorem LF.isNNConstFrom_sound (p : Params) : ∀ (l : List Int) (i : Nat),
    LF.isNNConstFrom l i = true → 0 ≤ LF.evalFrom p l i
  | [], _, _ => by simp [LF.evalFrom]
  | c :: l, i, h => by
    simp only [LF.isNNConstFrom, Bool.and_eq_true] at h
    have ih := LF.isNNConstFrom_sound p l (i + 1) h.2
    have h1 := h.1
    simp only [LF.evalFrom]
    have : 0 ≤ c * p.val i := by
      unfold Params.val
      by_cases hi : i < 11
      · simp [hi] at h1; simp [h1]
      · by_cases hi' : i = 11
        · simp [hi, hi'] at h1 ⊢; omega
        · simp [hi, hi']
    omega

/-- Lexicographic order on linear forms (for deduplication only). -/
def lexLe : List Int → List Int → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: l, b :: m => decide (a < b) || (a == b && lexLe l m)

def dedupAdj : List LF → List LF
  | [] => []
  | [a] => [a]
  | a :: b :: l => if a == b then dedupAdj (b :: l) else a :: dedupAdj (b :: l)

theorem mem_dedupAdj : ∀ (l : List LF) (a : LF), a ∈ l → a ∈ dedupAdj l
  | [], _, h => h
  | [x], _, h => h
  | x :: y :: l, a, h => by
    simp only [dedupAdj]
    have ih := mem_dedupAdj (y :: l) a
    rcases List.mem_cons.1 h with rfl | h'
    · split
      · rename_i hab; have : a = y := by simpa using hab
        subst this; exact ih List.mem_cons_self
      · exact List.mem_cons_self
    · split
      · exact ih h'
      · exact List.mem_cons_of_mem _ (ih h')

def dedupLF (l : List LF) : List LF := dedupAdj (l.mergeSort lexLe)

theorem mem_dedupLF {l : List LF} {a : LF} (h : a ∈ l) : a ∈ dedupLF l :=
  mem_dedupAdj _ _ ((List.mergeSort_perm l lexLe).mem_iff.2 h)

/-- **Root elimination.** `none` if some constraint involves both root coordinates or a
coefficient of absolute value `> 2`; otherwise the parameter conditions (`≥ 0` each). -/
def elim (S : List Cn) : Option (List LF) :=
  if S.all coefOK then
    some (dedupLF ((constsOf S ++ pairsFor false S ++ pairsFor true S).filter
      (fun l => !LF.isNNConstFrom l 0)))
  else none

theorem list_max (l : List Int) (h : l ≠ []) : ∃ m ∈ l, ∀ x ∈ l, x ≤ m := by
  induction l with
  | nil => exact absurd rfl h
  | cons a l ih =>
    by_cases hl : l = []
    · subst hl; exact ⟨a, by simp, by simp⟩
    · obtain ⟨m, hm, hmax⟩ := ih hl
      by_cases ham : a ≤ m
      · exact ⟨m, List.mem_cons_of_mem _ hm, by
          intro x hx; rcases List.mem_cons.1 hx with rfl | hx
          · exact ham
          · exact hmax x hx⟩
      · exact ⟨a, List.mem_cons_self, by
          intro x hx; rcases List.mem_cons.1 hx with rfl | hx
          · exact Int.le_refl _
          · have := hmax x hx; omega⟩

theorem list_min (l : List Int) (h : l ≠ []) : ∃ m ∈ l, ∀ x ∈ l, m ≤ x := by
  obtain ⟨m, hm, hmax⟩ := list_max (l.map (- ·)) (by simpa using h)
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hm
  refine ⟨a, ha, fun x hx => ?_⟩
  have := hmax (-x) (List.mem_map.2 ⟨x, hx, rfl⟩); omega

/-- One-dimensional elimination: lower bounds `c r + a ≥ 0`, upper bounds `-c r + a ≥ 0`,
`c ∈ {1, 2}`. -/
theorem oneDim (L H : List (Int × Int)) (hL : ∀ x ∈ L, x.1 = 1 ∨ x.1 = 2)
    (hH : ∀ x ∈ H, x.1 = 1 ∨ x.1 = 2)
    (hP : ∀ a ∈ L, ∀ b ∈ H, 0 ≤ pairVal a.1 a.2 b.1 b.2) :
    ∃ r : Int, (∀ a ∈ L, 0 ≤ a.1 * r + a.2) ∧ (∀ b ∈ H, 0 ≤ -b.1 * r + b.2) := by
  by_cases hLe : L = []
  · subst hLe
    by_cases hHe : H = []
    · subst hHe; exact ⟨0, by simp, by simp⟩
    · obtain ⟨m, hm, hmin⟩ := list_min (H.map (fun b => b.2 / b.1)) (by simpa using hHe)
      refine ⟨m, by simp, fun b hb => ?_⟩
      have h1 := hmin _ (List.mem_map.2 ⟨b, hb, rfl⟩)
      rcases hH b hb with h | h <;> rw [h] at h1 ⊢ <;> (try simp at h1) <;> omega
  · obtain ⟨m, hm, hmax⟩ := list_max (L.map (fun a => -(a.2 / a.1))) (by simpa using hLe)
    obtain ⟨a0, ha0, rfl⟩ := List.mem_map.1 hm
    refine ⟨-(a0.2 / a0.1), fun a ha => ?_, fun b hb => ?_⟩
    · have h1 := hmax _ (List.mem_map.2 ⟨a, ha, rfl⟩)
      rcases hL a ha with h | h <;> rw [h] at h1 ⊢ <;> (try simp at h1 ⊢) <;> omega
    · have h1 := hP a0 ha0 b hb
      unfold pairVal at h1
      rcases hL a0 ha0 with h | h <;> rcases hH b hb with h' | h' <;> rw [h, h'] at h1 ⊢ <;>
        (try simp at h1 ⊢) <;> omega

theorem mem_lowsOf {ix : Bool} {S : List Cn} {x : Int × LF} :
    x ∈ lowsOf ix S ↔ ∃ cn ∈ S, cn.other ix = 0 ∧ 0 < cn.coef ix ∧ x = (cn.coef ix, cn.2) := by
  simp only [lowsOf, List.mem_filterMap]
  constructor
  · rintro ⟨cn, hcn, h⟩
    split at h
    · rename_i hc; exact ⟨cn, hcn, hc.1, hc.2, (Option.some.inj h).symm⟩
    · exact absurd h (by simp)
  · rintro ⟨cn, hcn, h1, h2, rfl⟩
    exact ⟨cn, hcn, by simp [h1, h2]⟩

theorem mem_highsOf {ix : Bool} {S : List Cn} {x : Int × LF} :
    x ∈ highsOf ix S ↔ ∃ cn ∈ S, cn.other ix = 0 ∧ cn.coef ix < 0 ∧ x = (-cn.coef ix, cn.2) := by
  simp only [highsOf, List.mem_filterMap]
  constructor
  · rintro ⟨cn, hcn, h⟩
    split at h
    · rename_i hc; exact ⟨cn, hcn, hc.1, hc.2, (Option.some.inj h).symm⟩
    · exact absurd h (by simp)
  · rintro ⟨cn, hcn, h1, h2, rfl⟩
    exact ⟨cn, hcn, by simp [h1, h2]⟩

/-- Existence of a root coordinate for coordinate `ix`. -/
theorem elim_coord (S : List Cn) (p : Params) (hok : ∀ cn ∈ S, coefOK cn = true)
    (ix : Bool) (hpairs : ∀ l ∈ pairsFor ix S, 0 ≤ l.eval p) :
    ∃ r : Int, ∀ cn ∈ S, cn.other ix = 0 → cn.coef ix ≠ 0 →
      0 ≤ cn.coef ix * r + cn.2.eval p := by
  let L := (lowsOf ix S).map (fun x => (x.1, x.2.eval p))
  let H := (highsOf ix S).map (fun x => (x.1, x.2.eval p))
  have hc : ∀ cn ∈ S, cn.coef ix ≠ 0 → cn.other ix = 0 →
      cn.coef ix = 1 ∨ cn.coef ix = 2 ∨ cn.coef ix = -1 ∨ cn.coef ix = -2 := by
    intro cn hcn h1 _
    have := hok cn hcn
    simp only [coefOK, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at this
    unfold Cn.coef at h1 ⊢
    cases ix <;> simp at h1 ⊢ <;> omega
  obtain ⟨r, hr1, hr2⟩ := oneDim L H
    (by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
      obtain ⟨cn, hcn, h1, h2, rfl⟩ := mem_lowsOf.1 hy
      have := hc cn hcn (by omega) h1; simp; omega)
    (by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
      obtain ⟨cn, hcn, h1, h2, rfl⟩ := mem_highsOf.1 hy
      have := hc cn hcn (by omega) h1; simp; omega)
    (by
      intro a ha b hb
      obtain ⟨a', ha', rfl⟩ := List.mem_map.1 ha
      obtain ⟨b', hb', rfl⟩ := List.mem_map.1 hb
      have := hpairs (pairLF a'.1 a'.2 b'.1 b'.2) (by
        simp only [pairsFor, List.mem_flatMap, List.mem_map]
        exact ⟨a', List.mem_eraseDups.2 ha', b', List.mem_eraseDups.2 hb', rfl⟩)
      rw [pairLF_eval] at this; exact this)
  refine ⟨r, fun cn hcn ho hne => ?_⟩
  by_cases hpos : 0 < cn.coef ix
  · have := hr1 (cn.coef ix, cn.2.eval p)
      (List.mem_map.2 ⟨(cn.coef ix, cn.2), mem_lowsOf.2 ⟨cn, hcn, ho, hpos, rfl⟩, rfl⟩)
    exact this
  · have hneg : cn.coef ix < 0 := by omega
    have := hr2 (-cn.coef ix, cn.2.eval p)
      (List.mem_map.2 ⟨(-cn.coef ix, cn.2), mem_highsOf.2 ⟨cn, hcn, ho, hneg, rfl⟩, rfl⟩)
    simp only [Int.neg_neg] at this
    exact this

/-- **G3.** If `elim S = some out` and all atoms of `out` hold at `p`, the system `S` has an
integer root. -/
theorem elim_sound (S : List Cn) (out : List LF) (h : elim S = some out) (p : Params)
    (hout : ∀ l ∈ out, 0 ≤ l.eval p) : ∃ rx ry : Int, ∀ cn ∈ S, cn.holds p rx ry := by
  unfold elim at h
  split at h
  · rename_i hall
    have hok : ∀ cn ∈ S, coefOK cn = true := List.all_eq_true.1 hall
    have hraw : ∀ l ∈ constsOf S ++ pairsFor false S ++ pairsFor true S, 0 ≤ l.eval p := by
      intro l hl
      by_cases hc : LF.isNNConstFrom l 0 = true
      · exact LF.isNNConstFrom_sound p l 0 hc
      · apply hout
        rw [← Option.some.inj h]
        apply mem_dedupLF
        exact List.mem_filter.2 ⟨hl, by simpa using hc⟩
    obtain ⟨rx, hx⟩ := elim_coord S p hok false (fun l hl => hraw l (by simp [hl]))
    obtain ⟨ry, hy⟩ := elim_coord S p hok true (fun l hl => hraw l (by simp [hl]))
    refine ⟨rx, ry, fun cn hcn => ?_⟩
    have hc := hok cn hcn
    simp only [coefOK, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
    unfold Cn.holds
    by_cases h1 : cn.1.1 = 0
    · by_cases h2 : cn.1.2 = 0
      · have := hraw cn.2 (by
          simp only [List.mem_append]; left; left
          simp only [constsOf, List.mem_filterMap]
          exact ⟨cn, hcn, by simp [h1, h2]⟩)
        rw [h1, h2]; omega
      · have := hy cn hcn (by simp [Cn.other, h1]) (by simp [Cn.coef, h2])
        simp only [Cn.coef, ite_true] at this
        rw [h1]; omega
    · have h2 : cn.1.2 = 0 := by omega
      have := hx cn hcn (by simp [Cn.other, h2]) (by simp [Cn.coef, h1])
      simp only [Cn.coef] at this
      rw [h2]; simp at this ⊢; omega
  · exact absurd h (by simp)

end Ex89.T22
