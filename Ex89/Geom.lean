import Ex89.Sym
import Ex89.Check
/-! Facts about motions and the tables. -/
namespace Ex89

theorem inSq_iff (S : Nat) (a b : Int) : inSq S a b = true ↔ InSquare S a b := by
  simp [inSq, InSquare, and_assoc]

theorem pre_img (m : Motion) {w x y : Nat} (hx : x < w) (hy : y < w) :
    pre w m (m.imgX w x y) (m.imgY w x y) = some (x, y) := by
  rcases m with ⟨sw, fx, fy, dx, dy⟩
  cases sw <;> cases fx <;> cases fy <;>
    simp [pre, Motion.imgX, Motion.imgY] <;>
    omega

theorem pre_some (m : Motion) {w : Nat} {a b : Int} {r : Nat × Nat} (h : pre w m a b = some r) :
    r.1 < w ∧ r.2 < w ∧ m.imgX w r.1 r.2 = a ∧ m.imgY w r.1 r.2 = b := by
  rcases m with ⟨sw, fx, fy, dx, dy⟩
  rcases r with ⟨x, y⟩
  cases sw <;> cases fx <;> cases fy <;>
    simp only [pre, ↓reduceIte, Bool.false_eq_true] at h <;>
    split at h <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h <;>
    (obtain ⟨e1, e2⟩ := h; simp [Motion.imgX, Motion.imgY]; omega)

theorem Motion.shift_bound (m : Motion) {w S x y : Nat} (hx : x < w) (hy : y < w)
    (h : InSquare S (m.imgX w x y) (m.imgY w x y)) :
    -(w : Int) ≤ m.dx ∧ m.dx < S ∧ -(w : Int) ≤ m.dy ∧ m.dy < S := by
  rcases m with ⟨sw, fx, fy, dx, dy⟩
  cases sw <;> cases fx <;> cases fy <;> simp [Motion.imgX, Motion.imgY, InSquare] at * <;> omega

theorem mem_motions (m : Motion) {w S : Nat} (h : -(w : Int) ≤ m.dx ∧ m.dx < S ∧ -(w : Int) ≤ m.dy ∧ m.dy < S) :
    m ∈ motions w S := by
  rcases m with ⟨sw, fx, fy, dx, dy⟩
  obtain ⟨h1, h2, h3, h4⟩ := h
  simp only at h1 h2 h3 h4
  simp only [motions, List.mem_flatMap, List.mem_map, List.mem_range]
  refine ⟨sw, by cases sw <;> simp [bools], fx, by cases fx <;> simp [bools], fy,
    by cases fy <;> simp [bools], (dx + w).toNat, by omega, (dy + w).toNat, by omega, ?_⟩
  simp only [Motion.mk.injEq, true_and]
  omega

theorem slot_cases (P : Fin 4 → Prop) (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) (k : Fin 4) : P k := by
  match k with
  | ⟨0, _⟩ => exact h0
  | ⟨1, _⟩ => exact h1
  | ⟨2, _⟩ => exact h2
  | ⟨3, _⟩ => exact h3

theorem mem_allSlots (k : Fin 4) : k ∈ allSlots := by
  revert k; decide

theorem Cfg.mkPv_eq (c : Cfg) (k : Fin 4) : c.mkPv k = c.priv k := by
  revert k
  apply slot_cases <;> rfl

theorem mem_grid {w : Nat} {p : Nat × Nat} : p ∈ grid w ↔ p.1 < w ∧ p.2 < w := by
  rcases p with ⟨x, y⟩
  simp [grid, List.mem_flatMap, List.mem_map]

theorem code_lt {w x y : Nat} (hx : x < w) (hy : y < w) : x * w + y < w * w := by
  have : (x + 1) * w ≤ w * w := Nat.mul_le_mul_right w hx
  rw [Nat.add_mul, Nat.one_mul] at this
  omega

theorem code_inj {w x y x' y' : Nat} (hy : y < w) (hy' : y' < w) (h : x * w + y = x' * w + y') :
    x = x' ∧ y = y' := by
  have hw : 0 < w := by omega
  have e1 : (x * w + y) / w = x := by
    rw [Nat.mul_comm, Nat.mul_add_div hw, Nat.div_eq_of_lt hy]; simp
  have e2 : (x' * w + y') / w = x' := by
    rw [Nat.mul_comm, Nat.mul_add_div hw, Nat.div_eq_of_lt hy']; simp
  have e3 : (x * w + y) % w = y := by
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hy]
  have e4 : (x' * w + y') % w = y' := by
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hy']
  constructor
  · rw [← e1, ← e2, h]
  · rw [← e3, ← e4, h]

theorem code_split {w i : Nat} (hi : i < w * w) :
    i / w < w ∧ i % w < w ∧ i / w * w + i % w = i := by
  have hw : 0 < w := by
    cases w with
    | zero => simp at hi
    | succ n => omega
  refine ⟨Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at hi), Nat.mod_lt _ hw, ?_⟩
  have := Nat.div_add_mod i w
  rw [Nat.mul_comm] at this
  exact this

theorem tcode_lt {u v : Nat} {b : Bool} {a c : Nat} (ha : a < sideOf u v b) (hc : c < sideOf u v b) :
    tcode u v b a c < u * u + v * v := by
  cases b
  · have := code_lt (w := v) (x := a) (y := c) (by simpa [sideOf] using ha) (by simpa [sideOf] using hc)
    simp only [tcode, if_neg (Bool.false_ne_true)]
    simp at this ⊢
    omega
  · have := code_lt (w := u) (x := a) (y := c) (by simpa [sideOf] using ha) (by simpa [sideOf] using hc)
    simp only [tcode]
    simp
    omega

theorem tcode_inj {u v : Nat} {b b' : Bool} {a c a' c' : Nat}
    (ha : a < sideOf u v b) (hc : c < sideOf u v b) (ha' : a' < sideOf u v b') (hc' : c' < sideOf u v b')
    (h : tcode u v b a c = tcode u v b' a' c') : b = b' ∧ a = a' ∧ c = c' := by
  cases b <;> cases b' <;> simp [tcode, sideOf] at h ha hc ha' hc' ⊢
  · have := code_inj (w := v) hc hc' (x := a) (x' := a') (by omega)
    omega
  · have := code_lt ha' hc'
    omega
  · have := code_lt ha hc
    omega
  · have := code_inj hc hc' h
    omega

end Ex89
