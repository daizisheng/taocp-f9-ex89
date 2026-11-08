/-! # 3+1 theorem: arithmetic facts about Pythagorean triples (core Lean, no Mathlib).
Notation in comments: `d = w - v`, `a = w - u`. -/
namespace Ex89.ThreeOne

/-- `x < y → x*x < y*y`. -/
theorem ar_sq_lt {x y : Nat} (h : x < y) : x * x < y * y :=
  Nat.mul_self_lt_mul_self h

/-- `x ≤ y → x*x ≤ y*y`. -/
theorem ar_sq_le {x y : Nat} (h : x ≤ y) : x * x ≤ y * y :=
  Nat.mul_self_le_mul_self h

/-- Key identity: with `w = v + d`, `u² = 2vd + d²`. -/
theorem ar_key {u v d : Nat} (hp : u * u + v * v = (v + d) * (v + d)) :
    u * u = 2 * (v * d) + d * d := by grind

/-- Squares mod 5: `5 ∣ v*v → 5 ∣ v`. -/
theorem ar_mod5 {v : Nat} (h : (v * v) % 5 = 0) : v % 5 = 0 := by
  rw [Nat.mul_mod] at h
  have : v % 5 < 5 := Nat.mod_lt _ (by decide)
  generalize v % 5 = r at h this ⊢
  match r, this with
  | 0, _ => rfl
  | 1, _ => simp at h
  | 2, _ => simp at h
  | 3, _ => simp at h
  | 4, _ => simp at h

/-- `v² = 5k²` forces `k = 0`. -/
theorem ar_no5 : ∀ k v : Nat, v * v = 5 * (k * k) → k = 0 := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    intro v hv
    have hv5 : v % 5 = 0 := ar_mod5 (by rw [hv]; simp [Nat.mul_mod_right])
    obtain ⟨m, rfl⟩ : ∃ m, v = 5 * m := ⟨v / 5, by omega⟩
    have hk : k * k = 5 * (m * m) := by grind
    have hk5 : k % 5 = 0 := ar_mod5 (by rw [hk]; simp [Nat.mul_mod_right])
    obtain ⟨n, rfl⟩ : ∃ n, k = 5 * n := ⟨k / 5, by omega⟩
    have hm : m * m = 5 * (n * n) := by grind
    cases n with
    | zero => rfl
    | succ n' =>
      have := ih (n' + 1) (by omega) m hm
      omega

/-- `2d < u`. -/
theorem ar_2d {u v w : Nat} (huv : u < v) (hvw : v < w) (hp : u * u + v * v = w * w) :
    2 * (w - v) < u := by
  obtain ⟨d, rfl⟩ : ∃ d, w = v + d := ⟨w - v, by omega⟩
  have hd : 0 < d := by omega
  have e := ar_key hp
  rw [show v + d - v = d by omega]
  refine Nat.lt_of_not_le fun hle => ?_
  have h1 : u * u ≤ (2 * d) * (2 * d) := ar_sq_le hle
  have h1' : (2 * d) * (2 * d) = 4 * (d * d) := by grind
  have h2 : (2 * v) * d ≤ (3 * d) * d := by
    have : (2 * v) * d = 2 * (v * d) := by grind
    have : (3 * d) * d = 3 * (d * d) := by grind
    omega
  have h3 : 2 * v ≤ 3 * d := Nat.le_of_mul_le_mul_right h2 hd
  have h4 : v * v ≤ v * (2 * d) := Nat.mul_le_mul_left _ (by omega)
  have h4' : v * (2 * d) = 2 * (v * d) := by grind
  have h5 := ar_sq_lt huv
  omega

/-- `u = 3d` only for multiples of `(3,4,5)`. -/
theorem ar_3d {u v w : Nat} (huv : u < v) (hvw : v < w) (hp : u * u + v * v = w * w)
    (h : u = 3 * (w - v)) : ∃ k, u = 3 * k ∧ v = 4 * k ∧ w = 5 * k := by
  obtain ⟨d, rfl⟩ : ∃ d, w = v + d := ⟨w - v, by omega⟩
  have hd : 0 < d := by omega
  have e := ar_key hp
  rw [show v + d - v = d by omega] at h
  subst h
  have h1 : v * d = (4 * d) * d := by
    have : 3 * d * (3 * d) = 9 * (d * d) := by grind
    have : (4 * d) * d = 4 * (d * d) := by grind
    omega
  have h2 : v = 4 * d := Nat.eq_of_mul_eq_mul_right hd h1
  exact ⟨d, rfl, h2, by omega⟩

/-- `3a > u`. -/
theorem ar_3a {u v w : Nat} (hu : 0 < u) (huv : u < v) (hvw : v < w) (hp : u * u + v * v = w * w) :
    u < 3 * (w - u) := by
  refine Nat.lt_of_not_le fun hle => ?_
  have h0 : 3 * w ≤ 4 * u := by omega
  have h1 : (3 * w) * (3 * w) ≤ (4 * u) * (4 * u) := ar_sq_le h0
  have : (3 * w) * (3 * w) = 9 * (w * w) := by grind
  have : (4 * u) * (4 * u) = 16 * (u * u) := by grind
  have h5 := ar_sq_lt huv
  omega

/-- In the window `2a ≤ u`: `κ = u - a - d > 0` and `2a ≠ u`. -/
theorem ar_win {u v w : Nat} (hu : 0 < u) (huv : u < v) (hvw : v < w) (hp : u * u + v * v = w * w)
    (h : 2 * (w - u) ≤ u) : (w - u) + (w - v) < u ∧ 2 * (w - u) ≠ u := by
  obtain ⟨a, rfl⟩ : ∃ a, w = u + a := ⟨w - u, by omega⟩
  have ha : 0 < a := by omega
  rw [show u + a - u = a by omega] at h ⊢
  constructor
  · refine Nat.lt_of_not_le fun hle => ?_
    have hv : v ≤ 2 * a := by omega
    have h1 : v * v ≤ (2 * a) * (2 * a) := ar_sq_le hv
    have e : v * v = (2 * u + a) * a := by grind
    have : (2 * a) * (2 * a) = (4 * a) * a := by grind
    have h2 : 2 * u + a ≤ 4 * a := Nat.le_of_mul_le_mul_right (by omega) ha
    omega
  · intro heq
    obtain ⟨k, rfl⟩ : ∃ k, u = 2 * k := ⟨u / 2, by omega⟩
    have hak : a = k := by omega
    subst hak
    have : v * v = 5 * (a * a) := by grind
    have := ar_no5 a v this
    omega

/-- If `2u = 5d` (the `(20,21,29)` family) then `d + 2a ≠ u`. -/
theorem ar_205 {u v w : Nat} (hu : 0 < u) (huv : u < v) (hvw : v < w) (hp : u * u + v * v = w * w)
    (h : 2 * u = 5 * (w - v)) : (w - v) + 2 * (w - u) ≠ u := by
  obtain ⟨d, rfl⟩ : ∃ d, w = v + d := ⟨w - v, by omega⟩
  have hd : 0 < d := by omega
  have e := ar_key hp
  rw [show v + d - v = d by omega] at h ⊢
  have h1 : (2 * u) * (2 * u) = (5 * d) * (5 * d) := by rw [h]
  have : (2 * u) * (2 * u) = 4 * (u * u) := by grind
  have : (5 * d) * (5 * d) = 25 * (d * d) := by grind
  have h2 : (8 * v) * d = (21 * d) * d := by
    have : (8 * v) * d = 8 * (v * d) := by grind
    have : (21 * d) * d = 21 * (d * d) := by grind
    omega
  have h3 : 8 * v = 21 * d := Nat.eq_of_mul_eq_mul_right hd h2
  omega

end Ex89.ThreeOne
