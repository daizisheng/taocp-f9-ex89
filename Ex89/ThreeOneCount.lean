import Ex89.Model
/-! # 3+1 theorem: counting cells on source lines, and the row-sum identity. -/
namespace Ex89.ThreeOne

/-- Number of `i < n` with `p i`. -/
def cnt : Nat → (Nat → Bool) → Nat
  | 0, _ => 0
  | n + 1, p => cnt n p + (if p n then 1 else 0)

/-! ### Generic counting toolkit -/

theorem cnt_succ (n : Nat) (p : Nat → Bool) :
    cnt (n + 1) p = cnt n p + (if p n then 1 else 0) := rfl

theorem cnt_congr {n : Nat} {p q : Nat → Bool} (h : ∀ i, i < n → p i = q i) :
    cnt n p = cnt n q := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [cnt_succ, cnt_succ, ih (fun i hi => h i (by omega)), h n (by omega)]

theorem cnt_le (n : Nat) (p : Nat → Bool) : cnt n p ≤ n := by
  induction n with
  | zero => exact Nat.le_refl 0
  | succ n ih => rw [cnt_succ]; split <;> omega

theorem cnt_true (n : Nat) : cnt n (fun _ => true) = n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [cnt_succ, ih]; simp

theorem cnt_false {n : Nat} {p : Nat → Bool} (h : ∀ i, i < n → p i = false) : cnt n p = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [cnt_succ, ih (fun i hi => h i (by omega)), h n (by omega)]; simp

theorem cnt_add (n m : Nat) (p : Nat → Bool) :
    cnt (n + m) p = cnt n p + cnt m (fun i => p (n + i)) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [show n + (m + 1) = (n + m) + 1 by omega, cnt_succ, cnt_succ, ih]; omega

theorem cnt_mono {n : Nat} {p q : Nat → Bool} (h : ∀ i, i < n → p i = true → q i = true) :
    cnt n p ≤ cnt n q := by
  induction n with
  | zero => exact Nat.le_refl 0
  | succ n ih =>
    rw [cnt_succ, cnt_succ]
    have := ih (fun i hi => h i (by omega))
    have hn := h n (by omega)
    cases hp : p n <;> cases hq : q n <;> simp_all <;> omega

theorem cnt_or {n : Nat} {p q : Nat → Bool} (h : ∀ i, i < n → ¬ (p i = true ∧ q i = true)) :
    cnt n (fun i => p i || q i) = cnt n p + cnt n q := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [cnt_succ, cnt_succ, cnt_succ, ih (fun i hi => h i (by omega))]
    have hn := h n (by omega)
    cases hp : p n <;> cases hq : q n <;> simp_all <;> omega

theorem cnt_pos {n : Nat} {p : Nat → Bool} (h : 0 < cnt n p) : ∃ i, i < n ∧ p i = true := by
  induction n with
  | zero => exact absurd h (Nat.lt_irrefl 0)
  | succ n ih =>
    rw [cnt_succ] at h
    cases hp : p n
    · simp [hp] at h
      obtain ⟨i, hi, h'⟩ := ih h
      exact ⟨i, by omega, h'⟩
    · exact ⟨n, by omega, hp⟩

/-- Lower bound: `p` holds on `[0, m)`. -/
theorem cnt_lower {n m : Nat} {p : Nat → Bool} (hm : m ≤ n) (h : ∀ i, i < m → p i = true) :
    m ≤ cnt n p := by
  have e := cnt_add m (n - m) p
  rw [show m + (n - m) = n by omega] at e
  rw [e, cnt_congr (q := fun _ => true) h, cnt_true]; omega

/-- Upper bound: `p` fails on `[m, n)`. -/
theorem cnt_upper {n m : Nat} {p : Nat → Bool} (hm : m ≤ n)
    (h : ∀ i, m ≤ i → i < n → p i = false) : cnt n p ≤ m := by
  have e := cnt_add m (n - m) p
  rw [show m + (n - m) = n by omega] at e
  rw [e, cnt_false (fun i hi => h (m + i) (by omega) (by omega))]
  have := cnt_le m p; omega

/-- `p` fails on `[0, m)`: at most `n - m`. -/
theorem cnt_upper' {n m : Nat} {p : Nat → Bool} (hm : m ≤ n)
    (h : ∀ i, i < m → p i = false) : cnt n p ≤ n - m := by
  have e := cnt_add m (n - m) p
  rw [show m + (n - m) = n by omega] at e
  rw [e, cnt_false h]
  have := cnt_le (n - m) (fun i => p (m + i)); omega

/-- `p` fails on `[0, m)` and holds on `[m, n)`: exactly `n - m`. -/
theorem cnt_exact {n m : Nat} {p : Nat → Bool} (hm : m ≤ n)
    (h0 : ∀ i, i < m → p i = false) (h1 : ∀ i, m ≤ i → i < n → p i = true) :
    cnt n p = n - m := by
  have e := cnt_add m (n - m) p
  rw [show m + (n - m) = n by omega] at e
  rw [e, cnt_false h0, cnt_congr (q := fun _ => true) (fun i hi => h1 (m + i) (by omega) (by omega)),
    cnt_true]; omega

theorem cnt_remove {M j0 : Nat} {q : Nat → Bool} (hj : j0 < M) (hq : q j0 = true) :
    cnt M (fun j => q j && decide (j ≠ j0)) + 1 = cnt M q := by
  induction M with
  | zero => omega
  | succ M ih =>
    rw [cnt_succ, cnt_succ]
    by_cases h : j0 = M
    · subst h
      rw [cnt_congr (q := q) (fun i hi => by simp; omega)]
      simp [hq]
    · rw [← ih (by omega)]
      simp [Ne.symm h]
      omega

/-- Pigeonhole: a relation that maps `{i < n | p i}` injectively into `{j < M | q j}`. -/
theorem cnt_pigeon (R : Nat → Nat → Prop) {n M : Nat} {p : Nat → Bool} :
    ∀ {q : Nat → Bool},
    (∀ i, i < n → p i = true → ∃ j, j < M ∧ q j = true ∧ R i j) →
    (∀ i i' j, i < n → i' < n → p i = true → p i' = true → R i j → R i' j → i = i') →
    cnt n p ≤ cnt M q := by
  induction n with
  | zero => intro q _ _; exact Nat.zero_le _
  | succ n ih =>
    intro q hex hinj
    rw [cnt_succ]
    cases hp : p n
    · simp
      exact ih (fun i hi h => hex i (by omega) h)
        (fun i i' j hi hi' => hinj i i' j (by omega) (by omega))
    · obtain ⟨j0, hj0, hq0, hR0⟩ := hex n (by omega) hp
      have := ih (q := fun j => q j && decide (j ≠ j0))
        (fun i hi h => by
          obtain ⟨j, hj, hqj, hR⟩ := hex i (by omega) h
          refine ⟨j, hj, ?_, hR⟩
          have : j ≠ j0 := by
            intro e; subst e
            have := hinj i n j (by omega) (by omega) h hp hR hR0; omega
          simp [hqj, this])
        (fun i i' j hi hi' => hinj i i' j (by omega) (by omega))
      have := cnt_remove hj0 hq0
      simp; omega

theorem ct_disj {k k' : Fin 4} (hk : k ≠ k') (f : Nat → Fin 4) (i : Nat) :
    ¬ (decide (f i = k) = true ∧ decide (f i = k') = true) := by
  intro ⟨a, b⟩; simp at a b; exact hk (a ▸ b)

theorem ct_if_pos {c : Prop} [Decidable c] {α : Type} {a b : α} (h : c) :
    (if c then a else b) = a := by simp [h]


variable {u v w : Nat}

/-- Cells of piece `k` in source row `i` (zero if `i` is outside the square). -/
def rowCnt (D : Dissection u v w) (k : Fin 4) (i : Int) : Nat :=
  if 0 ≤ i ∧ i < w then cnt w (fun x => decide (D.piece x i.toNat = k)) else 0

/-- Cells of piece `k` in source column `i` (zero if `i` is outside the square). -/
def colCnt (D : Dissection u v w) (k : Fin 4) (i : Int) : Nat :=
  if 0 ≤ i ∧ i < w then cnt w (fun y => decide (D.piece i.toNat y = k)) else 0

/-- The source line that motion `m` sends to target row `r` (the cells with `imgY = r`):
a row if `m.sw = false`, a column if `m.sw = true`. -/
def srcLine (m : Motion) (w : Nat) (r : Int) : Int :=
  if (if m.sw then m.fx else m.fy) then (w : Int) - 1 - (r - m.dy) else r - m.dy

/-- Cells of piece `k` on its source line `i`. -/
def lineCnt (D : Dissection u v w) (k : Fin 4) (i : Int) : Nat :=
  if (D.motion k).sw then colCnt D k i else rowCnt D k i

/-- Normal form of a 3+1 dissection: piece 0 is the `v × v` square at the origin (identity),
pieces 1, 2, 3 lie in the `u × u` boxes at the corners `(0, w-1)`, `(w-1, w-1)`, `(w-1, 0)`. -/
structure Box31 (D : Dissection u v w) : Prop where
  t0 : D.toU 0 = false
  t1 : D.toU 1 = true
  t2 : D.toU 2 = true
  t3 : D.toU 3 = true
  b0 : ∀ x y, x < w → y < w → (D.piece x y = 0 ↔ x < v ∧ y < v)
  b1 : ∀ x y, x < w → y < w → D.piece x y = 1 → x < u
  b2 : ∀ x y, x < w → y < w → D.piece x y = 2 → w - u ≤ x ∧ w - u ≤ y
  b3 : ∀ x y, x < w → y < w → D.piece x y = 3 → y < u

/-! ### Motions and source lines -/

theorem ct_fin4 (k : Fin 4) : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by
  revert k; decide

/-- The source line of the target row of a cell is the cell's column (`sw`) or row. -/
theorem ct_srcLine_img (m : Motion) (w x y : Nat) :
    srcLine m w (m.imgY w x y) = if m.sw then (x : Int) else y := by
  obtain ⟨sw, fx, fy, dx, dy⟩ := m
  cases sw <;> cases fx <;> cases fy <;> simp [srcLine, Motion.imgY] <;> omega

/-- The cells of a source line go to the target row. -/
theorem ct_img_srcLine (m : Motion) (w : Nat) (r : Int) (j : Nat) (h : 0 ≤ srcLine m w r) :
    m.imgY w (if m.sw then (srcLine m w r).toNat else j)
      (if m.sw then j else (srcLine m w r).toNat) = r := by
  have e := Int.toNat_of_nonneg h
  revert e h
  generalize (srcLine m w r).toNat = t
  obtain ⟨sw, fx, fy, dx, dy⟩ := m
  cases sw <;> cases fx <;> cases fy <;> simp [srcLine, Motion.imgY] <;> omega

theorem ct_toU (D : Dissection u v w) (hB : Box31 D) (k : Fin 4) (hk : k ≠ 0) :
    D.toU k = true := by
  rcases ct_fin4 k with h | h | h | h <;> subst h
  · exact absurd rfl hk
  · exact hB.t1
  · exact hB.t2
  · exact hB.t3

/-! ### Cells of a source line, and the index set `[0, 3w)` -/

/-- Source line of piece `k` for target row `r`. -/
def ct_L (D : Dissection u v w) (r : Int) (k : Fin 4) : Int := srcLine (D.motion k) w r
/-- The `j`-th cell of that line: first coordinate. -/
def ct_x (D : Dissection u v w) (r : Int) (k : Fin 4) (j : Nat) : Nat :=
  if (D.motion k).sw then (ct_L D r k).toNat else j
/-- The `j`-th cell of that line: second coordinate. -/
def ct_y (D : Dissection u v w) (r : Int) (k : Fin 4) (j : Nat) : Nat :=
  if (D.motion k).sw then j else (ct_L D r k).toNat
/-- The `j`-th cell of the line lies in the square and belongs to piece `k`. -/
def ct_ok (D : Dissection u v w) (r : Int) (k : Fin 4) (j : Nat) : Bool :=
  decide (0 ≤ ct_L D r k ∧ ct_L D r k < w) && decide (D.piece (ct_x D r k j) (ct_y D r k j) = k)

theorem ct_ok_line (D : Dissection u v w) (r : Int) (k : Fin 4) :
    cnt w (ct_ok D r k) = lineCnt D k (srcLine (D.motion k) w r) := by
  show _ = lineCnt D k (ct_L D r k)
  unfold lineCnt colCnt rowCnt
  by_cases hc : 0 ≤ ct_L D r k ∧ ct_L D r k < w
  · cases hs : (D.motion k).sw <;> simp only [hc, and_self, ite_true] <;>
      exact cnt_congr (fun j _ => by simp [ct_ok, ct_x, ct_y, hs, hc])
  · cases hs : (D.motion k).sw <;> simp only [hc, ite_false] <;>
      exact cnt_false (fun j _ => by simp [ct_ok, hc])

theorem ct_ok_spec (D : Dissection u v w) (r : Int) (k : Fin 4) (j : Nat) (hj : j < w)
    (h : ct_ok D r k j = true) :
    ct_x D r k j < w ∧ ct_y D r k j < w ∧ D.piece (ct_x D r k j) (ct_y D r k j) = k ∧
      (D.motion k).imgY w (ct_x D r k j) (ct_y D r k j) = r := by
  simp only [ct_ok, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h0, h1⟩, hp⟩ := h
  have e := Int.toNat_of_nonneg h0
  refine ⟨?_, ?_, hp, ?_⟩
  · unfold ct_x; split <;> omega
  · unfold ct_y; split <;> omega
  · exact ct_img_srcLine (D.motion k) w r j h0

theorem ct_ok_of (D : Dissection u v w) (r : Int) (k : Fin 4) (x y : Nat) (hx : x < w) (hy : y < w)
    (hp : D.piece x y = k) (hr : (D.motion k).imgY w x y = r) :
    ∃ j, j < w ∧ ct_x D r k j = x ∧ ct_y D r k j = y ∧ ct_ok D r k j = true := by
  have e : ct_L D r k = if (D.motion k).sw then (x : Int) else y := by
    rw [ct_L, ← hr, ct_srcLine_img]
  cases hs : (D.motion k).sw
  · simp only [hs] at e
    refine ⟨x, hx, by simp [ct_x, hs], by simp [ct_y, hs, e], ?_⟩
    simp [ct_ok, ct_x, ct_y, hs, e, hp]; omega
  · simp only [hs] at e
    refine ⟨y, hy, by simp [ct_x, hs, e], by simp [ct_y, hs], ?_⟩
    simp [ct_ok, ct_x, ct_y, hs, e, hp]; omega

theorem ct_cell_inj (D : Dissection u v w) (r : Int) (k : Fin 4) (j j' : Nat)
    (h1 : ct_x D r k j = ct_x D r k j') (h2 : ct_y D r k j = ct_y D r k j') : j = j' := by
  unfold ct_x at h1; unfold ct_y at h2
  cases hs : (D.motion k).sw <;> simp [hs] at h1 h2 <;> assumption

/-- Piece of index `i < 3w`. -/
def ct_k (w i : Nat) : Fin 4 := if i < w then 1 else if i < 2 * w then 2 else 3
/-- Position of index `i < 3w` along its line. -/
def ct_j (w i : Nat) : Nat := if i < w then i else if i < 2 * w then i - w else i - 2 * w

theorem ct_j_lt (w i : Nat) (h : i < 3 * w) : ct_j w i < w := by
  unfold ct_j; split
  · assumption
  · split <;> omega

theorem ct_k_ne (w i : Nat) : ct_k w i ≠ 0 := by
  unfold ct_k; split
  · decide
  · split <;> decide

theorem ct_idx_inj (w i i' : Nat) (hk : ct_k w i = ct_k w i') (hj : ct_j w i = ct_j w i') :
    i = i' := by
  unfold ct_k at hk; unfold ct_j at hj
  by_cases a1 : i < w <;> by_cases a2 : i < 2 * w <;> by_cases b1 : i' < w <;>
    by_cases b2 : i' < 2 * w <;> simp [a1, a2, b1, b2] at hk hj <;> omega

theorem ct_idx_surj (w : Nat) (k : Fin 4) (hk : k ≠ 0) (j : Nat) (hj : j < w) :
    ∃ i, i < 3 * w ∧ ct_k w i = k ∧ ct_j w i = j := by
  rcases ct_fin4 k with h | h | h | h <;> subst h
  · exact absurd rfl hk
  · exact ⟨j, by omega, by simp [ct_k, hj], by simp [ct_j, hj]⟩
  · refine ⟨w + j, by omega, ?_, ?_⟩
    · simp [ct_k, show ¬ w + j < w by omega, show w + j < 2 * w by omega]
    · simp [ct_j, show ¬ w + j < w by omega, show w + j < 2 * w by omega]
  · refine ⟨2 * w + j, by omega, ?_, ?_⟩
    · simp [ct_k, show ¬ 2 * w + j < w by omega, show ¬ 2 * w + j < 2 * w by omega]
    · simp [ct_j, show ¬ 2 * w + j < w by omega, show ¬ 2 * w + j < 2 * w by omega]

/-- Valid indices: the cells of pieces 1, 2, 3 that go to target row `r`. -/
def ct_Q (D : Dissection u v w) (r : Int) (i : Nat) : Bool := ct_ok D r (ct_k w i) (ct_j w i)

theorem ct_split3 (D : Dissection u v w) (r : Int) :
    cnt (3 * w) (ct_Q D r) = cnt w (ct_ok D r 1) + cnt w (ct_ok D r 2) + cnt w (ct_ok D r 3) := by
  rw [show 3 * w = w + w + w by omega, cnt_add, cnt_add]
  rw [cnt_congr (n := w) (p := ct_Q D r) (q := ct_ok D r 1)
      (fun i hi => by simp [ct_Q, ct_k, ct_j, hi]),
    cnt_congr (n := w) (p := fun i => ct_Q D r (w + i)) (q := ct_ok D r 2)
      (fun i hi => by
        simp [ct_Q, ct_k, ct_j, show ¬ w + i < w by omega, show w + i < 2 * w by omega]),
    cnt_congr (n := w) (p := fun i => ct_Q D r (w + w + i)) (q := ct_ok D r 3)
      (fun i hi => by
        simp [ct_Q, ct_k, ct_j, show ¬ w + w + i < w by omega,
          show ¬ w + w + i < 2 * w by omega]; congr 2 <;> omega)]

/-- Image abscissa of index `i`. -/
def ct_X (D : Dissection u v w) (r : Int) (i : Nat) : Int :=
  (D.motion (ct_k w i)).imgX w (ct_x D r (ct_k w i) (ct_j w i)) (ct_y D r (ct_k w i) (ct_j w i))

section
variable (D : Dissection u v w) (hB : Box31 D)
include hB

theorem ct_X_inj (r : Int) (i i' : Nat) (hi : i < 3 * w) (hi' : i' < 3 * w)
    (hq : ct_Q D r i = true) (hq' : ct_Q D r i' = true) (hX : ct_X D r i = ct_X D r i') :
    i = i' := by
  obtain ⟨ax, ay, ap, aY⟩ := ct_ok_spec D r _ _ (ct_j_lt w i hi) hq
  obtain ⟨bx,by', bp, bY⟩ := ct_ok_spec D r _ _ (ct_j_lt w i' hi') hq'
  obtain ⟨ex, ey⟩ := D.injective _ _ _ _ ax ay bx by'
    (by rw [ap, bp, ct_toU D hB _ (ct_k_ne w i), ct_toU D hB _ (ct_k_ne w i')])
    (by rw [ap, bp]; exact hX) (by rw [ap, bp, aY, bY])
  have hk : ct_k w i = ct_k w i' := by rw [← ap, ← bp, ex, ey]
  rw [← hk] at ex ey
  exact ct_idx_inj w i i' hk (ct_cell_inj D r _ _ _ ex ey)

theorem ct_rowsum_cnt (r : Int) (h0 : 0 ≤ r) (h1 : r < u) : cnt (3 * w) (ct_Q D r) = u := by
  apply Nat.le_antisymm
  · have := cnt_pigeon (fun i s => ct_X D r i = (s : Int)) (n := 3 * w) (M := u)
      (p := ct_Q D r) (q := fun _ => true)
      (fun i hi hq => by
        obtain ⟨ax, ay, ap, _⟩ := ct_ok_spec D r _ _ (ct_j_lt w i hi) hq
        have hm := D.maps_into _ _ ax ay
        rw [ap, ct_toU D hB _ (ct_k_ne w i)] at hm
        simp only [ite_true, InSquare] at hm
        refine ⟨(ct_X D r i).toNat, ?_, rfl, ?_⟩
        · unfold ct_X; omega
        · unfold ct_X; omega)
      (fun i i' s hi hi' hq hq' e e' => ct_X_inj D hB r i i' hi hi' hq hq' (by rw [e, e']))
    rwa [cnt_true] at this
  · have := cnt_pigeon (fun s i => ct_X D r i = (s : Int)) (n := u) (M := 3 * w)
      (p := fun _ => true) (q := ct_Q D r)
      (fun s hs _ => by
        obtain ⟨x, y, hx, hy, ht, hX, hY⟩ :=
          D.surjective true s r (by simp only [ite_true, InSquare]; omega)
        generalize hk : D.piece x y = k at ht hX hY
        have hk0 : k ≠ 0 := by intro e; subst e; rw [hB.t0] at ht; exact absurd ht (by decide)
        obtain ⟨j, hj, ejx, ejy, hok⟩ := ct_ok_of D r k x y hx hy hk hY
        obtain ⟨i, hi, eik, eij⟩ := ct_idx_surj w k hk0 j hj
        refine ⟨i, hi, ?_, ?_⟩
        · simp only [ct_Q, eik, eij, hok]
        · simp only [ct_X, eik, eij, ejx, ejy, hX])
      (fun s s' i _ _ _ _ e e' => by rw [e] at e'; exact_mod_cast e')
    rwa [cnt_true] at this

/-- **Row sums.** Every row of the `u × u` target receives exactly `u` cells. -/
theorem row_sum (r : Int) (h0 : 0 ≤ r) (h1 : r < u) :
    lineCnt D 1 (srcLine (D.motion 1) w r) + lineCnt D 2 (srcLine (D.motion 2) w r)
      + lineCnt D 3 (srcLine (D.motion 3) w r) = u := by
  rw [← ct_ok_line, ← ct_ok_line, ← ct_ok_line, ← ct_split3]
  exact ct_rowsum_cnt D hB r h0 h1

/-- A nonempty source line of a `u`-piece goes to a row of the target. -/
theorem line_img (k : Fin 4) (hk : k ≠ 0) (i : Int) (h : 0 < lineCnt D k i) :
    ∃ r : Int, 0 ≤ r ∧ r < u ∧ srcLine (D.motion k) w r = i := by
  have key : ∀ x y, x < w → y < w → D.piece x y = k →
      (if (D.motion k).sw then (x : Int) else y) = i →
      ∃ r : Int, 0 ≤ r ∧ r < u ∧ srcLine (D.motion k) w r = i := by
    intro x y hx hy hp hi
    have hm := D.maps_into x y hx hy
    rw [hp, ct_toU D hB k hk] at hm
    simp only [ite_true, InSquare] at hm
    exact ⟨_, hm.2.2.1, hm.2.2.2, by rw [ct_srcLine_img, hi]⟩
  unfold lineCnt colCnt rowCnt at h
  by_cases hc : 0 ≤ i ∧ i < w
  · cases hs : (D.motion k).sw <;> simp only [hs, hc, and_self, ite_true, Bool.false_eq_true,
      ite_false] at h
    · obtain ⟨x, hx, hp⟩ := cnt_pos h
      exact key x i.toNat hx (by omega) (by simpa using hp) (by simp [hs]; omega)
    · obtain ⟨y, hy, hp⟩ := cnt_pos h
      exact key i.toNat y (by omega) hy (by simpa using hp) (by simp [hs]; omega)
  · cases hs : (D.motion k).sw <;> simp [hc] at h


-- `hvw` is part of the stated interface even where a proof does not use it.
set_option linter.unusedSectionVars false

variable (huv : u < v) (hvw : v < w)
include huv hvw

omit hvw in
/-- What each piece looks like, from the `Box31` fields. -/
theorem ct_info (x y : Nat) (hx : x < w) (hy : y < w) :
    (D.piece x y = 0 ∧ x < v ∧ y < v) ∨ (D.piece x y = 1 ∧ x < u ∧ v ≤ y) ∨
    (D.piece x y = 2 ∧ w - u ≤ x ∧ w - u ≤ y ∧ (v ≤ x ∨ v ≤ y)) ∨
    (D.piece x y = 3 ∧ y < u ∧ v ≤ x) := by
  have h0 := hB.b0 x y hx hy
  rcases ct_fin4 (D.piece x y) with h | h | h | h
  · exact Or.inl ⟨h, h0.1 h⟩
  · have := hB.b1 x y hx hy h
    have : ¬ (x < v ∧ y < v) := fun c => absurd (h0.2 c) (by rw [h]; decide)
    exact Or.inr (Or.inl ⟨h, by omega, by omega⟩)
  · have := hB.b2 x y hx hy h
    have : ¬ (x < v ∧ y < v) := fun c => absurd (h0.2 c) (by rw [h]; decide)
    exact Or.inr (Or.inr (Or.inl ⟨h, by omega, by omega, by omega⟩))
  · have := hB.b3 x y hx hy h
    have : ¬ (x < v ∧ y < v) := fun c => absurd (h0.2 c) (by rw [h]; decide)
    exact Or.inr (Or.inr (Or.inr ⟨h, by omega, by omega⟩))

macro "ct_tac" D:term:max hB:term:max huv:term:max x:term:max y:term:max : tactic =>
  `(tactic| (rcases ct_info $D $hB $huv $x $y (by omega) (by omega) with
      ⟨hp, h'⟩ | ⟨hp, h'⟩ | ⟨hp, h'⟩ | ⟨hp, h'⟩ <;> simp [hp] <;> omega))

-- Source rows (pieces 1 and 2).
theorem row1_out (i : Int) (h : ¬ ((v : Int) ≤ i ∧ i < w)) : rowCnt D 1 i = 0 := by
  unfold rowCnt; split
  · rename_i hc
    have e := Int.toNat_of_nonneg hc.1
    generalize i.toNat = y at *
    exact cnt_false fun x hx => by ct_tac D hB huv x y
  · rfl
theorem row1_bd (i : Int) (h1 : (v : Int) ≤ i) (h2 : i < w) :
    w - u ≤ rowCnt D 1 i ∧ rowCnt D 1 i ≤ u := by
  unfold rowCnt; rw [ct_if_pos (by omega)]
  have e := Int.toNat_of_nonneg (show 0 ≤ i by omega)
  generalize i.toNat = y at *
  exact ⟨cnt_lower (by omega) fun x hx => by ct_tac D hB huv x y,
    cnt_upper (by omega) fun x hx hx' => by ct_tac D hB huv x y⟩
theorem row12 (i : Int) (h1 : (v : Int) ≤ i) (h2 : i < w) : rowCnt D 1 i + rowCnt D 2 i = w := by
  unfold rowCnt; rw [ct_if_pos (by omega), ct_if_pos (by omega)]
  have e := Int.toNat_of_nonneg (show 0 ≤ i by omega)
  generalize i.toNat = y at *
  rw [← cnt_or fun x _ => ct_disj (by decide) (fun x => D.piece x y) x,
    cnt_congr (q := fun _ => true) fun x hx => by ct_tac D hB huv x y, cnt_true]
theorem row2_out (i : Int) (h : ¬ ((w : Int) - u ≤ i ∧ i < w)) : rowCnt D 2 i = 0 := by
  unfold rowCnt; split
  · rename_i hc
    have e := Int.toNat_of_nonneg hc.1
    generalize i.toNat = y at *
    exact cnt_false fun x hx => by ct_tac D hB huv x y
  · rfl
theorem row2_arm (i : Int) (h1 : (w : Int) - u ≤ i) (h2 : i < v) : rowCnt D 2 i ≤ w - v := by
  unfold rowCnt; rw [ct_if_pos (by omega)]
  have e := Int.toNat_of_nonneg (show 0 ≤ i by omega)
  generalize i.toNat = y at *
  exact cnt_upper' (by omega) fun x hx => by ct_tac D hB huv x y
theorem row2_forced (i : Int) (h1 : (u : Int) ≤ i) (h2 : i < v) : rowCnt D 2 i = w - v := by
  unfold rowCnt; rw [ct_if_pos (by omega)]
  have e := Int.toNat_of_nonneg (show 0 ≤ i by omega)
  generalize i.toNat = y at *
  exact cnt_exact (by omega) (fun x hx => by ct_tac D hB huv x y)
    (fun x hx hx' => by ct_tac D hB huv x y)

-- Source columns (pieces 3 and 2).
theorem col3_out (i : Int) (h : ¬ ((v : Int) ≤ i ∧ i < w)) : colCnt D 3 i = 0 := by
  unfold colCnt; split
  · rename_i hc
    have e := Int.toNat_of_nonneg hc.1
    generalize i.toNat = x at *
    exact cnt_false fun y hy => by ct_tac D hB huv x y
  · rfl
theorem col3_bd (i : Int) (h1 : (v : Int) ≤ i) (h2 : i < w) :
    w - u ≤ colCnt D 3 i ∧ colCnt D 3 i ≤ u := by
  unfold colCnt; rw [ct_if_pos (by omega)]
  have e := Int.toNat_of_nonneg (show 0 ≤ i by omega)
  generalize i.toNat = x at *
  exact ⟨cnt_lower (by omega) fun y hy => by ct_tac D hB huv x y,
    cnt_upper (by omega) fun y hy hy' => by ct_tac D hB huv x y⟩
theorem col32 (i : Int) (h1 : (v : Int) ≤ i) (h2 : i < w) : colCnt D 3 i + colCnt D 2 i = w := by
  unfold colCnt; rw [ct_if_pos (by omega), ct_if_pos (by omega)]
  have e := Int.toNat_of_nonneg (show 0 ≤ i by omega)
  generalize i.toNat = x at *
  rw [← cnt_or fun y _ => ct_disj (by decide) (fun y => D.piece x y) y,
    cnt_congr (q := fun _ => true) fun y hy => by ct_tac D hB huv x y, cnt_true]
theorem col2_out (i : Int) (h : ¬ ((w : Int) - u ≤ i ∧ i < w)) : colCnt D 2 i = 0 := by
  unfold colCnt; split
  · rename_i hc
    have e := Int.toNat_of_nonneg hc.1
    generalize i.toNat = x at *
    exact cnt_false fun y hy => by ct_tac D hB huv x y
  · rfl
theorem col2_arm (i : Int) (h1 : (w : Int) - u ≤ i) (h2 : i < v) : colCnt D 2 i ≤ w - v := by
  unfold colCnt; rw [ct_if_pos (by omega)]
  have e := Int.toNat_of_nonneg (show 0 ≤ i by omega)
  generalize i.toNat = x at *
  exact cnt_upper' (by omega) fun y hy => by ct_tac D hB huv x y
theorem col2_forced (i : Int) (h1 : (u : Int) ≤ i) (h2 : i < v) : colCnt D 2 i = w - v := by
  unfold colCnt; rw [ct_if_pos (by omega)]
  have e := Int.toNat_of_nonneg (show 0 ≤ i by omega)
  generalize i.toNat = x at *
  exact cnt_exact (by omega) (fun y hy => by ct_tac D hB huv x y)
    (fun y hy hy' => by ct_tac D hB huv x y)

end
end Ex89.ThreeOne
