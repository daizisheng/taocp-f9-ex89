/-! # 3+1 theorem: the one-dimensional core (row sums only).
See `PROOF.md`, section 2.4. Everything here is about integers and line counts;
the dissection itself does not appear. -/
namespace Ex89.ThreeOne

/-- An affine map of slope `±1`: `r ↦ c - r` if `e`, else `r ↦ r + c`. -/
def aff (e : Bool) (c r : Int) : Int := if e then c - r else r + c

/-- Start of the band `{r | v ≤ aff e c r < w}`. -/
def co_bs (e : Bool) (c v w : Int) : Int := if e then c - w + 1 else v - c

theorem co_band (e : Bool) (c v w r : Int) :
    (v ≤ aff e c r ∧ aff e c r < w) ↔ (co_bs e c v w ≤ r ∧ r < co_bs e c v w + (w - v)) := by
  cases e <;> simp [aff, co_bs] <;> omega

theorem co_bandin (e : Bool) (c u v w : Int) (hvw : v < w)
    (h : ∀ y, v ≤ y → y < w → ∃ r, 0 ≤ r ∧ r < u ∧ aff e c r = y) :
    0 ≤ co_bs e c v w ∧ co_bs e c v w + (w - v) ≤ u := by
  obtain ⟨r0, h00, h01, h0⟩ := h v (by omega) hvw
  obtain ⟨r1, h10, h11, h1⟩ := h (w - 1) (by omega) (by omega)
  cases e <;> simp [aff, co_bs] at * <;> omega

/-- Step (e) of the proof: the three rows of the matching argument. -/
theorem co_e (A1 A2 A3 g : Int → Int) (u w X rz r rf jz jo : Int)
    (s : A1 rz + A2 rz + A3 rz = u) (s1 : A1 rz = 0) (s2 : A2 rz = w - g jz) (s3 : A3 rz = 0)
    (t : A1 r + A2 r + A3 r = u) (t1 : A1 r = g jz) (t2 : A2 r = w - g jo) (t3 : A3 r = 0)
    (f : A1 rf + A2 rf + A3 rf = u) (f1 : A1 rf = g jo) (f2 : A2 rf = X) (f3 : A3 rf = 0) :
    2 * (w - u) + X = u := by omega

set_option maxHeartbeats 4000000 in
theorem co_case5 (u v w d a : Int) (hd : d = w - v) (ha : a = w - u) (hu : 0 < u) (huv : u < v)
    (hvw : v < w) (h2d : 2 * d < u) (h3d : u ≠ 3 * d) (h3a : u < 3 * a)
    (hwin : 2 * a ≤ u → a + d < u ∧ 2 * a ≠ u)
    (h205 : 2 * u = 5 * d → d + 2 * a ≠ u)
    (A1 A2 A3 g ρ : Int → Int) (e1 : Bool) (p q s : Int)
    (hp : 0 ≤ p ∧ p + d ≤ u) (hq : 0 ≤ q ∧ q + d ≤ u) (hs : 0 ≤ s ∧ s + d ≤ u)
    (hρ : ∀ j, ρ j = if e1 then q + d - 1 - j else q + j)
    (hsum : ∀ r, 0 ≤ r → r < u → A1 r + A2 r + A3 r = u)
    (hg : ∀ j, 0 ≤ j → j < d → a ≤ g j ∧ g j ≤ u)
    (h1in : ∀ r, q ≤ r → r < q + d → a ≤ A1 r)
    (h1out : ∀ r, ¬ (q ≤ r ∧ r < q + d) → A1 r = 0)
    (h1g : ∀ j, 0 ≤ j → j < d → A1 (ρ j) = g j)
    (h2in : ∀ j, 0 ≤ j → j < d → A2 (p + j) = w - g j)
    (h2inb : ∀ r, p ≤ r → r < p + d → a ≤ A2 r)
    (h2lo : ∀ r, r < p → 0 ≤ A2 r ∧ A2 r ≤ d)
    (h2p1 : A2 (p - 1) = d)
    (h2top : ∀ r, p + d ≤ r → A2 r = 0)
    (h3in : ∀ r, s ≤ r → r < s + d → a ≤ A3 r)
    (h3out : ∀ r, ¬ (s ≤ r ∧ r < s + d) → A3 r = 0)
    (R : ∀ r, 0 ≤ r → r < u → A1 r + A2 r + A3 r = u ∧
      ((q ≤ r ∧ r < q + d ∧ a ≤ A1 r) ∨ ((r < q ∨ q + d ≤ r) ∧ A1 r = 0)) ∧
      ((p ≤ r ∧ r < p + d ∧ a ≤ A2 r) ∨ (r < p ∧ 0 ≤ A2 r ∧ A2 r ≤ d) ∨
        (p + d ≤ r ∧ A2 r = 0)) ∧
      ((s ≤ r ∧ r < s + d ∧ a ≤ A3 r) ∨ ((r < s ∨ s + d ≤ r) ∧ A3 r = 0)))
    (E : a + d < u → ∀ j, 0 ≤ j → j < d →
      (((q ≤ p + j ∧ p + j < q + d) ∨ (s ≤ p + j ∧ p + j < s + d)) ∨
        ((p ≤ ρ j ∧ ρ j < p + d) ∨ (s ≤ ρ j ∧ ρ j < s + d))) ∧
      (((p + j < q ∨ q + d ≤ p + j) ∧ (p + j < s ∨ s + d ≤ p + j)) ∨
        ((ρ j < p ∨ p + d ≤ ρ j) ∧ (ρ j < s ∨ s + d ≤ ρ j))))
    (h0 : q ≤ 0 ∧ 0 < q + d) (h1 : p ≤ (u - 1) ∧ (u - 1) < p + d) (cd : (q ≤ d ∧ d < q + d) ∨ (p ≤ d ∧ d < p + d) ∨ (s ≤ d ∧ d < s + d)) (cdd : (q ≤ (u - d - 1) ∧ (u - d - 1) < q + d) ∨ (p ≤ (u - d - 1) ∧ (u - d - 1) < p + d) ∨ (s ≤ (u - d - 1) ∧ (u - d - 1) < s + d)) : False := by
  have hdpos : 0 < d := by omega
  have hapos : 0 < a := by omega
  have H205 : ∀ _x : Unit, 2 * u = 5 * d → d + 2 * a ≠ u := fun _ => h205
  clear h205
  have P : p = u - d ∧ q = 0 ∧ u - 2 * d ≤ s ∧ s ≤ d := by omega
  clear h0 h1 cd cdd
  have h2a : 2 * a ≤ u := by
    have := R (d - 1) (by omega) (by omega); have := R (u - d) (by omega) (by omega); omega
  obtain ⟨hk, h2a'⟩ := hwin h2a
  have hτ : u < 3 * d := by omega
  have H2a : ∀ _x : Unit, 2 * a ≠ u := fun _ => h2a'
  clear hwin h3d h2a'
  have E' := E hk
  cases e1
  · have i : ∀ j, ρ j = q + j := fun j => by simpa using hρ j
    have ea := E' (s + 2 * d - u) (by omega) (by omega)
    have := i (s + 2 * d - u)
    by_cases hsd : s < d
    · have eb := E' s (by omega) hsd; have := i s; omega
    · omega
  · have i : ∀ j, ρ j = q + d - 1 - j := fun j => by simpa using hρ j
    have ea := E' (d - 1) (by omega) (by omega); have := i (d - 1); omega

set_option maxHeartbeats 4000000 in
theorem co_case3 (u v w d a : Int) (hd : d = w - v) (ha : a = w - u) (hu : 0 < u) (huv : u < v)
    (hvw : v < w) (h2d : 2 * d < u) (h3d : u ≠ 3 * d) (h3a : u < 3 * a)
    (hwin : 2 * a ≤ u → a + d < u ∧ 2 * a ≠ u)
    (h205 : 2 * u = 5 * d → d + 2 * a ≠ u)
    (A1 A2 A3 g ρ : Int → Int) (e1 : Bool) (p q s : Int)
    (hp : 0 ≤ p ∧ p + d ≤ u) (hq : 0 ≤ q ∧ q + d ≤ u) (hs : 0 ≤ s ∧ s + d ≤ u)
    (hρ : ∀ j, ρ j = if e1 then q + d - 1 - j else q + j)
    (hsum : ∀ r, 0 ≤ r → r < u → A1 r + A2 r + A3 r = u)
    (hg : ∀ j, 0 ≤ j → j < d → a ≤ g j ∧ g j ≤ u)
    (h1in : ∀ r, q ≤ r → r < q + d → a ≤ A1 r)
    (h1out : ∀ r, ¬ (q ≤ r ∧ r < q + d) → A1 r = 0)
    (h1g : ∀ j, 0 ≤ j → j < d → A1 (ρ j) = g j)
    (h2in : ∀ j, 0 ≤ j → j < d → A2 (p + j) = w - g j)
    (h2inb : ∀ r, p ≤ r → r < p + d → a ≤ A2 r)
    (h2lo : ∀ r, r < p → 0 ≤ A2 r ∧ A2 r ≤ d)
    (h2p1 : A2 (p - 1) = d)
    (h2top : ∀ r, p + d ≤ r → A2 r = 0)
    (h3in : ∀ r, s ≤ r → r < s + d → a ≤ A3 r)
    (h3out : ∀ r, ¬ (s ≤ r ∧ r < s + d) → A3 r = 0)
    (R : ∀ r, 0 ≤ r → r < u → A1 r + A2 r + A3 r = u ∧
      ((q ≤ r ∧ r < q + d ∧ a ≤ A1 r) ∨ ((r < q ∨ q + d ≤ r) ∧ A1 r = 0)) ∧
      ((p ≤ r ∧ r < p + d ∧ a ≤ A2 r) ∨ (r < p ∧ 0 ≤ A2 r ∧ A2 r ≤ d) ∨
        (p + d ≤ r ∧ A2 r = 0)) ∧
      ((s ≤ r ∧ r < s + d ∧ a ≤ A3 r) ∨ ((r < s ∨ s + d ≤ r) ∧ A3 r = 0)))
    (E : a + d < u → ∀ j, 0 ≤ j → j < d →
      (((q ≤ p + j ∧ p + j < q + d) ∨ (s ≤ p + j ∧ p + j < s + d)) ∨
        ((p ≤ ρ j ∧ ρ j < p + d) ∨ (s ≤ ρ j ∧ ρ j < s + d))) ∧
      (((p + j < q ∨ q + d ≤ p + j) ∧ (p + j < s ∨ s + d ≤ p + j)) ∨
        ((ρ j < p ∨ p + d ≤ ρ j) ∧ (ρ j < s ∨ s + d ≤ ρ j))))
    (h0 : q ≤ 0 ∧ 0 < q + d) (h1 : s ≤ (u - 1) ∧ (u - 1) < s + d) (cd : (q ≤ d ∧ d < q + d) ∨ (p ≤ d ∧ d < p + d) ∨ (s ≤ d ∧ d < s + d)) (cdd : (q ≤ (u - d - 1) ∧ (u - d - 1) < q + d) ∨ (p ≤ (u - d - 1) ∧ (u - d - 1) < p + d) ∨ (s ≤ (u - d - 1) ∧ (u - d - 1) < s + d)) : False := by
  have hdpos : 0 < d := by omega
  have hapos : 0 < a := by omega
  have H205 : ∀ _x : Unit, 2 * u = 5 * d → d + 2 * a ≠ u := fun _ => h205
  clear h205
  have P : q = 0 ∧ s = u - d ∧ u - 2 * d ≤ p ∧ p ≤ d := by omega
  clear h0 h1 cd cdd
  have h2a : 2 * a ≤ u := by
    have := R (d - 1) (by omega) (by omega); have := R (u - d) (by omega) (by omega); omega
  obtain ⟨hk, h2a'⟩ := hwin h2a
  have hτ : u < 3 * d := by omega
  have H2a : ∀ _x : Unit, 2 * a ≠ u := fun _ => h2a'
  clear hwin h3d h2a'
  have E' := E hk
  cases e1
  · have i : ∀ j, ρ j = q + j := fun j => by simpa using hρ j
    have ea := E' 0 (by omega) (by omega); have := i 0
    have eb := E' (d - 1) (by omega) (by omega); have := i (d - 1)
    have hl : 0 < d - p ∧ p + 2 * d - u = 0 := by omega
    clear ea eb
    have ec := E' p (by omega) (by omega); have := i p
    have ed := E' (d - p) (by omega) (by omega); have := i (d - p)
    have hmp : 2 * p = d := by omega
    clear ec ed
    have h5 : 2 * u = 5 * d := by omega
    have := i (d - 1); have := i (p - 1)
    have key := co_e A1 A2 A3 g u w d (p + (d - 1)) (ρ (d - 1)) (ρ (p - 1)) (d - 1) (p - 1)
      (hsum _ (by omega) (by omega)) (h1out _ (by omega)) (h2in _ (by omega) (by omega))
      (h3out _ (by omega)) (hsum _ (by omega) (by omega)) (h1g _ (by omega) (by omega))
      ((congrArg A2 (show ρ (d - 1) = p + (p - 1) by omega)).trans (h2in _ (by omega) (by omega)))
      (h3out _ (by omega)) (hsum _ (by omega) (by omega)) (h1g _ (by omega) (by omega))
      ((congrArg A2 (show ρ (p - 1) = p - 1 by omega)).trans h2p1) (h3out _ (by omega))
    have := H205 () h5
    omega
  · have i : ∀ j, ρ j = q + d - 1 - j := fun j => by simpa using hρ j
    have ea := E' 0 (by omega) (by omega); have := i 0; omega

set_option maxHeartbeats 4000000 in
theorem co_case2 (u v w d a : Int) (hd : d = w - v) (ha : a = w - u) (hu : 0 < u) (huv : u < v)
    (hvw : v < w) (h2d : 2 * d < u) (h3d : u ≠ 3 * d) (h3a : u < 3 * a)
    (hwin : 2 * a ≤ u → a + d < u ∧ 2 * a ≠ u)
    (h205 : 2 * u = 5 * d → d + 2 * a ≠ u)
    (A1 A2 A3 g ρ : Int → Int) (e1 : Bool) (p q s : Int)
    (hp : 0 ≤ p ∧ p + d ≤ u) (hq : 0 ≤ q ∧ q + d ≤ u) (hs : 0 ≤ s ∧ s + d ≤ u)
    (hρ : ∀ j, ρ j = if e1 then q + d - 1 - j else q + j)
    (hsum : ∀ r, 0 ≤ r → r < u → A1 r + A2 r + A3 r = u)
    (hg : ∀ j, 0 ≤ j → j < d → a ≤ g j ∧ g j ≤ u)
    (h1in : ∀ r, q ≤ r → r < q + d → a ≤ A1 r)
    (h1out : ∀ r, ¬ (q ≤ r ∧ r < q + d) → A1 r = 0)
    (h1g : ∀ j, 0 ≤ j → j < d → A1 (ρ j) = g j)
    (h2in : ∀ j, 0 ≤ j → j < d → A2 (p + j) = w - g j)
    (h2inb : ∀ r, p ≤ r → r < p + d → a ≤ A2 r)
    (h2lo : ∀ r, r < p → 0 ≤ A2 r ∧ A2 r ≤ d)
    (h2p1 : A2 (p - 1) = d)
    (h2top : ∀ r, p + d ≤ r → A2 r = 0)
    (h3in : ∀ r, s ≤ r → r < s + d → a ≤ A3 r)
    (h3out : ∀ r, ¬ (s ≤ r ∧ r < s + d) → A3 r = 0)
    (R : ∀ r, 0 ≤ r → r < u → A1 r + A2 r + A3 r = u ∧
      ((q ≤ r ∧ r < q + d ∧ a ≤ A1 r) ∨ ((r < q ∨ q + d ≤ r) ∧ A1 r = 0)) ∧
      ((p ≤ r ∧ r < p + d ∧ a ≤ A2 r) ∨ (r < p ∧ 0 ≤ A2 r ∧ A2 r ≤ d) ∨
        (p + d ≤ r ∧ A2 r = 0)) ∧
      ((s ≤ r ∧ r < s + d ∧ a ≤ A3 r) ∨ ((r < s ∨ s + d ≤ r) ∧ A3 r = 0)))
    (E : a + d < u → ∀ j, 0 ≤ j → j < d →
      (((q ≤ p + j ∧ p + j < q + d) ∨ (s ≤ p + j ∧ p + j < s + d)) ∨
        ((p ≤ ρ j ∧ ρ j < p + d) ∨ (s ≤ ρ j ∧ ρ j < s + d))) ∧
      (((p + j < q ∨ q + d ≤ p + j) ∧ (p + j < s ∨ s + d ≤ p + j)) ∨
        ((ρ j < p ∨ p + d ≤ ρ j) ∧ (ρ j < s ∨ s + d ≤ ρ j))))
    (h0 : p ≤ 0 ∧ 0 < p + d) (h1 : q ≤ (u - 1) ∧ (u - 1) < q + d) (cd : (q ≤ d ∧ d < q + d) ∨ (p ≤ d ∧ d < p + d) ∨ (s ≤ d ∧ d < s + d)) (cdd : (q ≤ (u - d - 1) ∧ (u - d - 1) < q + d) ∨ (p ≤ (u - d - 1) ∧ (u - d - 1) < p + d) ∨ (s ≤ (u - d - 1) ∧ (u - d - 1) < s + d)) : False := by
  have hdpos : 0 < d := by omega
  have hapos : 0 < a := by omega
  have H205 : ∀ _x : Unit, 2 * u = 5 * d → d + 2 * a ≠ u := fun _ => h205
  clear h205
  have P : p = 0 ∧ q = u - d ∧ u - 2 * d ≤ s ∧ s ≤ d := by omega
  clear h0 h1 cd cdd
  have h2a : 2 * a ≤ u := by
    have := R (d - 1) (by omega) (by omega); have := R (u - d) (by omega) (by omega); omega
  obtain ⟨hk, h2a'⟩ := hwin h2a
  have hτ : u < 3 * d := by omega
  have H2a : ∀ _x : Unit, 2 * a ≠ u := fun _ => h2a'
  clear hwin h3d h2a'
  have E' := E hk
  cases e1
  · have i : ∀ j, ρ j = q + j := fun j => by simpa using hρ j
    have ea := E' (s + 2 * d - u) (by omega) (by omega)
    have := i (s + 2 * d - u)
    by_cases hsd : s < d
    · have eb := E' s (by omega) hsd; have := i s; omega
    · omega
  · have i : ∀ j, ρ j = q + d - 1 - j := fun j => by simpa using hρ j
    have ea := E' 0 (by omega) (by omega); have := i 0; omega

set_option maxHeartbeats 4000000 in
theorem co_case1 (u v w d a : Int) (hd : d = w - v) (ha : a = w - u) (hu : 0 < u) (huv : u < v)
    (hvw : v < w) (h2d : 2 * d < u) (h3d : u ≠ 3 * d) (h3a : u < 3 * a)
    (hwin : 2 * a ≤ u → a + d < u ∧ 2 * a ≠ u)
    (h205 : 2 * u = 5 * d → d + 2 * a ≠ u)
    (A1 A2 A3 g ρ : Int → Int) (e1 : Bool) (p q s : Int)
    (hp : 0 ≤ p ∧ p + d ≤ u) (hq : 0 ≤ q ∧ q + d ≤ u) (hs : 0 ≤ s ∧ s + d ≤ u)
    (hρ : ∀ j, ρ j = if e1 then q + d - 1 - j else q + j)
    (hsum : ∀ r, 0 ≤ r → r < u → A1 r + A2 r + A3 r = u)
    (hg : ∀ j, 0 ≤ j → j < d → a ≤ g j ∧ g j ≤ u)
    (h1in : ∀ r, q ≤ r → r < q + d → a ≤ A1 r)
    (h1out : ∀ r, ¬ (q ≤ r ∧ r < q + d) → A1 r = 0)
    (h1g : ∀ j, 0 ≤ j → j < d → A1 (ρ j) = g j)
    (h2in : ∀ j, 0 ≤ j → j < d → A2 (p + j) = w - g j)
    (h2inb : ∀ r, p ≤ r → r < p + d → a ≤ A2 r)
    (h2lo : ∀ r, r < p → 0 ≤ A2 r ∧ A2 r ≤ d)
    (h2p1 : A2 (p - 1) = d)
    (h2top : ∀ r, p + d ≤ r → A2 r = 0)
    (h3in : ∀ r, s ≤ r → r < s + d → a ≤ A3 r)
    (h3out : ∀ r, ¬ (s ≤ r ∧ r < s + d) → A3 r = 0)
    (R : ∀ r, 0 ≤ r → r < u → A1 r + A2 r + A3 r = u ∧
      ((q ≤ r ∧ r < q + d ∧ a ≤ A1 r) ∨ ((r < q ∨ q + d ≤ r) ∧ A1 r = 0)) ∧
      ((p ≤ r ∧ r < p + d ∧ a ≤ A2 r) ∨ (r < p ∧ 0 ≤ A2 r ∧ A2 r ≤ d) ∨
        (p + d ≤ r ∧ A2 r = 0)) ∧
      ((s ≤ r ∧ r < s + d ∧ a ≤ A3 r) ∨ ((r < s ∨ s + d ≤ r) ∧ A3 r = 0)))
    (E : a + d < u → ∀ j, 0 ≤ j → j < d →
      (((q ≤ p + j ∧ p + j < q + d) ∨ (s ≤ p + j ∧ p + j < s + d)) ∨
        ((p ≤ ρ j ∧ ρ j < p + d) ∨ (s ≤ ρ j ∧ ρ j < s + d))) ∧
      (((p + j < q ∨ q + d ≤ p + j) ∧ (p + j < s ∨ s + d ≤ p + j)) ∨
        ((ρ j < p ∨ p + d ≤ ρ j) ∧ (ρ j < s ∨ s + d ≤ ρ j))))
    (h0 : p ≤ 0 ∧ 0 < p + d) (h1 : s ≤ (u - 1) ∧ (u - 1) < s + d) (cd : (q ≤ d ∧ d < q + d) ∨ (p ≤ d ∧ d < p + d) ∨ (s ≤ d ∧ d < s + d)) (cdd : (q ≤ (u - d - 1) ∧ (u - d - 1) < q + d) ∨ (p ≤ (u - d - 1) ∧ (u - d - 1) < p + d) ∨ (s ≤ (u - d - 1) ∧ (u - d - 1) < s + d)) : False := by
  have hdpos : 0 < d := by omega
  have hapos : 0 < a := by omega
  have H205 : ∀ _x : Unit, 2 * u = 5 * d → d + 2 * a ≠ u := fun _ => h205
  clear h205
  have P : p = 0 ∧ s = u - d ∧ u - 2 * d ≤ q ∧ q ≤ d := by omega
  clear h0 h1 cd cdd
  have h2a : 2 * a ≤ u := by
    have := R (d - 1) (by omega) (by omega); have := R (u - d) (by omega) (by omega); omega
  obtain ⟨hk, h2a'⟩ := hwin h2a
  have hτ : u < 3 * d := by omega
  have H2a : ∀ _x : Unit, 2 * a ≠ u := fun _ => h2a'
  clear hwin h3d h2a'
  have E' := E hk
  cases e1
  · have i : ∀ j, ρ j = q + j := fun j => by simpa using hρ j
    have ea := E' 0 (by omega) (by omega); have := i 0
    have eb := E' (d - 1) (by omega) (by omega); have := i (d - 1)
    have hl : q < d ∧ q + 2 * d - u = 0 := by omega
    clear ea eb
    have ec := E' q (by omega) (by omega); have := i q
    have ed := E' (d - q) (by omega) (by omega); have := i (d - q)
    have hmq : 2 * q = d := by omega
    clear ec ed
    have := i (0); have := i (d - q)
    have key := co_e A1 A2 A3 g u w 0 (p + (0)) (ρ (0)) (ρ (d - q)) (0) (d - q)
      (hsum _ (by omega) (by omega)) (h1out _ (by omega)) (h2in _ (by omega) (by omega))
      (h3out _ (by omega)) (hsum _ (by omega) (by omega)) (h1g _ (by omega) (by omega))
      ((congrArg A2 (show ρ (0) = p + (d - q) by omega)).trans (h2in _ (by omega) (by omega)))
      (h3out _ (by omega)) (hsum _ (by omega) (by omega)) (h1g _ (by omega) (by omega))
      (h2top _ (by omega)) (h3out _ (by omega))
    have := H2a ()
    omega
  · have i : ∀ j, ρ j = q + d - 1 - j := fun j => by simpa using hρ j
    have ea := E' (d - 1) (by omega) (by omega); have := i (d - 1); omega

set_option maxHeartbeats 4000000 in
theorem co_case4 (u v w d a : Int) (hd : d = w - v) (ha : a = w - u) (hu : 0 < u) (huv : u < v)
    (hvw : v < w) (h2d : 2 * d < u) (h3d : u ≠ 3 * d) (h3a : u < 3 * a)
    (hwin : 2 * a ≤ u → a + d < u ∧ 2 * a ≠ u)
    (h205 : 2 * u = 5 * d → d + 2 * a ≠ u)
    (A1 A2 A3 g ρ : Int → Int) (e1 : Bool) (p q s : Int)
    (hp : 0 ≤ p ∧ p + d ≤ u) (hq : 0 ≤ q ∧ q + d ≤ u) (hs : 0 ≤ s ∧ s + d ≤ u)
    (hρ : ∀ j, ρ j = if e1 then q + d - 1 - j else q + j)
    (hsum : ∀ r, 0 ≤ r → r < u → A1 r + A2 r + A3 r = u)
    (hg : ∀ j, 0 ≤ j → j < d → a ≤ g j ∧ g j ≤ u)
    (h1in : ∀ r, q ≤ r → r < q + d → a ≤ A1 r)
    (h1out : ∀ r, ¬ (q ≤ r ∧ r < q + d) → A1 r = 0)
    (h1g : ∀ j, 0 ≤ j → j < d → A1 (ρ j) = g j)
    (h2in : ∀ j, 0 ≤ j → j < d → A2 (p + j) = w - g j)
    (h2inb : ∀ r, p ≤ r → r < p + d → a ≤ A2 r)
    (h2lo : ∀ r, r < p → 0 ≤ A2 r ∧ A2 r ≤ d)
    (h2p1 : A2 (p - 1) = d)
    (h2top : ∀ r, p + d ≤ r → A2 r = 0)
    (h3in : ∀ r, s ≤ r → r < s + d → a ≤ A3 r)
    (h3out : ∀ r, ¬ (s ≤ r ∧ r < s + d) → A3 r = 0)
    (R : ∀ r, 0 ≤ r → r < u → A1 r + A2 r + A3 r = u ∧
      ((q ≤ r ∧ r < q + d ∧ a ≤ A1 r) ∨ ((r < q ∨ q + d ≤ r) ∧ A1 r = 0)) ∧
      ((p ≤ r ∧ r < p + d ∧ a ≤ A2 r) ∨ (r < p ∧ 0 ≤ A2 r ∧ A2 r ≤ d) ∨
        (p + d ≤ r ∧ A2 r = 0)) ∧
      ((s ≤ r ∧ r < s + d ∧ a ≤ A3 r) ∨ ((r < s ∨ s + d ≤ r) ∧ A3 r = 0)))
    (E : a + d < u → ∀ j, 0 ≤ j → j < d →
      (((q ≤ p + j ∧ p + j < q + d) ∨ (s ≤ p + j ∧ p + j < s + d)) ∨
        ((p ≤ ρ j ∧ ρ j < p + d) ∨ (s ≤ ρ j ∧ ρ j < s + d))) ∧
      (((p + j < q ∨ q + d ≤ p + j) ∧ (p + j < s ∨ s + d ≤ p + j)) ∨
        ((ρ j < p ∨ p + d ≤ ρ j) ∧ (ρ j < s ∨ s + d ≤ ρ j))))
    (h0 : s ≤ 0 ∧ 0 < s + d) (h1 : q ≤ (u - 1) ∧ (u - 1) < q + d) (cd : (q ≤ d ∧ d < q + d) ∨ (p ≤ d ∧ d < p + d) ∨ (s ≤ d ∧ d < s + d)) (cdd : (q ≤ (u - d - 1) ∧ (u - d - 1) < q + d) ∨ (p ≤ (u - d - 1) ∧ (u - d - 1) < p + d) ∨ (s ≤ (u - d - 1) ∧ (u - d - 1) < s + d)) : False := by
  have hdpos : 0 < d := by omega
  have hapos : 0 < a := by omega
  have H205 : ∀ _x : Unit, 2 * u = 5 * d → d + 2 * a ≠ u := fun _ => h205
  clear h205
  have P : s = 0 ∧ q = u - d ∧ u - 2 * d ≤ p ∧ p ≤ d := by omega
  clear h0 h1 cd cdd
  have h2a : 2 * a ≤ u := by
    have := R (d - 1) (by omega) (by omega); have := R (u - d) (by omega) (by omega); omega
  obtain ⟨hk, h2a'⟩ := hwin h2a
  have hτ : u < 3 * d := by omega
  have H2a : ∀ _x : Unit, 2 * a ≠ u := fun _ => h2a'
  clear hwin h3d h2a'
  have E' := E hk
  cases e1
  · have i : ∀ j, ρ j = q + j := fun j => by simpa using hρ j
    have ea := E' 0 (by omega) (by omega); have := i 0
    have eb := E' (d - 1) (by omega) (by omega); have := i (d - 1)
    have hl : p = d ∧ 0 < p + 2 * d - u := by omega
    clear ea eb
    have ec := E' (p + 2 * d - u) (by omega) (by omega); have := i (p + 2 * d - u)
    have ed := E' (d - (p + 2 * d - u)) (by omega) (by omega); have := i (d - (p + 2 * d - u))
    have hη : 2 * (p + 2 * d - u) = d := by omega
    clear ec ed
    have := i (0); have := i (p + 2 * d - u)
    have key := co_e A1 A2 A3 g u w 0 (p + (0)) (ρ (0)) (ρ (p + 2 * d - u)) (0) (p + 2 * d - u)
      (hsum _ (by omega) (by omega)) (h1out _ (by omega)) (h2in _ (by omega) (by omega))
      (h3out _ (by omega)) (hsum _ (by omega) (by omega)) (h1g _ (by omega) (by omega))
      ((congrArg A2 (show ρ (0) = p + (p + 2 * d - u) by omega)).trans (h2in _ (by omega) (by omega)))
      (h3out _ (by omega)) (hsum _ (by omega) (by omega)) (h1g _ (by omega) (by omega))
      (h2top _ (by omega)) (h3out _ (by omega))
    have := H2a ()
    omega
  · have i : ∀ j, ρ j = q + d - 1 - j := fun j => by simpa using hρ j
    have ea := E' (d - 1) (by omega) (by omega); have := i (d - 1); omega

set_option maxHeartbeats 4000000 in
theorem co_case6 (u v w d a : Int) (hd : d = w - v) (ha : a = w - u) (hu : 0 < u) (huv : u < v)
    (hvw : v < w) (h2d : 2 * d < u) (h3d : u ≠ 3 * d) (h3a : u < 3 * a)
    (hwin : 2 * a ≤ u → a + d < u ∧ 2 * a ≠ u)
    (h205 : 2 * u = 5 * d → d + 2 * a ≠ u)
    (A1 A2 A3 g ρ : Int → Int) (e1 : Bool) (p q s : Int)
    (hp : 0 ≤ p ∧ p + d ≤ u) (hq : 0 ≤ q ∧ q + d ≤ u) (hs : 0 ≤ s ∧ s + d ≤ u)
    (hρ : ∀ j, ρ j = if e1 then q + d - 1 - j else q + j)
    (hsum : ∀ r, 0 ≤ r → r < u → A1 r + A2 r + A3 r = u)
    (hg : ∀ j, 0 ≤ j → j < d → a ≤ g j ∧ g j ≤ u)
    (h1in : ∀ r, q ≤ r → r < q + d → a ≤ A1 r)
    (h1out : ∀ r, ¬ (q ≤ r ∧ r < q + d) → A1 r = 0)
    (h1g : ∀ j, 0 ≤ j → j < d → A1 (ρ j) = g j)
    (h2in : ∀ j, 0 ≤ j → j < d → A2 (p + j) = w - g j)
    (h2inb : ∀ r, p ≤ r → r < p + d → a ≤ A2 r)
    (h2lo : ∀ r, r < p → 0 ≤ A2 r ∧ A2 r ≤ d)
    (h2p1 : A2 (p - 1) = d)
    (h2top : ∀ r, p + d ≤ r → A2 r = 0)
    (h3in : ∀ r, s ≤ r → r < s + d → a ≤ A3 r)
    (h3out : ∀ r, ¬ (s ≤ r ∧ r < s + d) → A3 r = 0)
    (R : ∀ r, 0 ≤ r → r < u → A1 r + A2 r + A3 r = u ∧
      ((q ≤ r ∧ r < q + d ∧ a ≤ A1 r) ∨ ((r < q ∨ q + d ≤ r) ∧ A1 r = 0)) ∧
      ((p ≤ r ∧ r < p + d ∧ a ≤ A2 r) ∨ (r < p ∧ 0 ≤ A2 r ∧ A2 r ≤ d) ∨
        (p + d ≤ r ∧ A2 r = 0)) ∧
      ((s ≤ r ∧ r < s + d ∧ a ≤ A3 r) ∨ ((r < s ∨ s + d ≤ r) ∧ A3 r = 0)))
    (E : a + d < u → ∀ j, 0 ≤ j → j < d →
      (((q ≤ p + j ∧ p + j < q + d) ∨ (s ≤ p + j ∧ p + j < s + d)) ∨
        ((p ≤ ρ j ∧ ρ j < p + d) ∨ (s ≤ ρ j ∧ ρ j < s + d))) ∧
      (((p + j < q ∨ q + d ≤ p + j) ∧ (p + j < s ∨ s + d ≤ p + j)) ∨
        ((ρ j < p ∨ p + d ≤ ρ j) ∧ (ρ j < s ∨ s + d ≤ ρ j))))
    (h0 : s ≤ 0 ∧ 0 < s + d) (h1 : p ≤ (u - 1) ∧ (u - 1) < p + d) (cd : (q ≤ d ∧ d < q + d) ∨ (p ≤ d ∧ d < p + d) ∨ (s ≤ d ∧ d < s + d)) (cdd : (q ≤ (u - d - 1) ∧ (u - d - 1) < q + d) ∨ (p ≤ (u - d - 1) ∧ (u - d - 1) < p + d) ∨ (s ≤ (u - d - 1) ∧ (u - d - 1) < s + d)) : False := by
  have hdpos : 0 < d := by omega
  have hapos : 0 < a := by omega
  have H205 : ∀ _x : Unit, 2 * u = 5 * d → d + 2 * a ≠ u := fun _ => h205
  clear h205
  have P : s = 0 ∧ p = u - d ∧ u - 2 * d ≤ q ∧ q ≤ d := by omega
  clear h0 h1 cd cdd
  have h2a : 2 * a ≤ u := by
    have := R (d - 1) (by omega) (by omega); have := R (u - d) (by omega) (by omega); omega
  obtain ⟨hk, h2a'⟩ := hwin h2a
  have hτ : u < 3 * d := by omega
  have H2a : ∀ _x : Unit, 2 * a ≠ u := fun _ => h2a'
  clear hwin h3d h2a'
  have E' := E hk
  cases e1
  · have i : ∀ j, ρ j = q + j := fun j => by simpa using hρ j
    have ea := E' 0 (by omega) (by omega); have := i 0
    have eb := E' (d - 1) (by omega) (by omega); have := i (d - 1)
    have hl : q = d ∧ 0 < q + 2 * d - u := by omega
    clear ea eb
    have ec := E' (q + 2 * d - u) (by omega) (by omega); have := i (q + 2 * d - u)
    have ed := E' (d - (q + 2 * d - u)) (by omega) (by omega); have := i (d - (q + 2 * d - u))
    have hη : 2 * (q + 2 * d - u) = d := by omega
    clear ec ed
    have h5 : 2 * u = 5 * d := by omega
    have := i (d - 1); have := i (d - (q + 2 * d - u) - 1)
    have key := co_e A1 A2 A3 g u w d (p + (d - 1)) (ρ (d - 1)) (ρ (d - (q + 2 * d - u) - 1)) (d - 1) (d - (q + 2 * d - u) - 1)
      (hsum _ (by omega) (by omega)) (h1out _ (by omega)) (h2in _ (by omega) (by omega))
      (h3out _ (by omega)) (hsum _ (by omega) (by omega)) (h1g _ (by omega) (by omega))
      ((congrArg A2 (show ρ (d - 1) = p + (d - (q + 2 * d - u) - 1) by omega)).trans (h2in _ (by omega) (by omega)))
      (h3out _ (by omega)) (hsum _ (by omega) (by omega)) (h1g _ (by omega) (by omega))
      ((congrArg A2 (show ρ (d - (q + 2 * d - u) - 1) = p - 1 by omega)).trans h2p1) (h3out _ (by omega))
    have := H205 () h5
    omega
  · have i : ∀ j, ρ j = q + d - 1 - j := fun j => by simpa using hρ j
    have ea := E' 0 (by omega) (by omega); have := i 0; omega

/-- The purely combinatorial core: line counts abstracted to functions on rows. -/
theorem co_combi (u v w d a : Int) (hd : d = w - v) (ha : a = w - u) (hu : 0 < u) (huv : u < v)
    (hvw : v < w) (h2d : 2 * d < u) (h3d : u ≠ 3 * d) (h3a : u < 3 * a)
    (hwin : 2 * a ≤ u → a + d < u ∧ 2 * a ≠ u)
    (h205 : 2 * u = 5 * d → d + 2 * a ≠ u)
    (A1 A2 A3 g ρ : Int → Int) (e1 : Bool) (p q s : Int)
    (hp : 0 ≤ p ∧ p + d ≤ u) (hq : 0 ≤ q ∧ q + d ≤ u) (hs : 0 ≤ s ∧ s + d ≤ u)
    (hρ : ∀ j, ρ j = if e1 then q + d - 1 - j else q + j)
    (hsum : ∀ r, 0 ≤ r → r < u → A1 r + A2 r + A3 r = u)
    (hg : ∀ j, 0 ≤ j → j < d → a ≤ g j ∧ g j ≤ u)
    (h1in : ∀ r, q ≤ r → r < q + d → a ≤ A1 r)
    (h1out : ∀ r, ¬ (q ≤ r ∧ r < q + d) → A1 r = 0)
    (h1g : ∀ j, 0 ≤ j → j < d → A1 (ρ j) = g j)
    (h2in : ∀ j, 0 ≤ j → j < d → A2 (p + j) = w - g j)
    (h2inb : ∀ r, p ≤ r → r < p + d → a ≤ A2 r)
    (h2lo : ∀ r, r < p → 0 ≤ A2 r ∧ A2 r ≤ d)
    (h2p1 : A2 (p - 1) = d)
    (h2top : ∀ r, p + d ≤ r → A2 r = 0)
    (h3in : ∀ r, s ≤ r → r < s + d → a ≤ A3 r)
    (h3out : ∀ r, ¬ (s ≤ r ∧ r < s + d) → A3 r = 0) : False := by
  have hdpos : 0 < d := by omega
  have hapos : 0 < a := by omega
  have R : ∀ r, 0 ≤ r → r < u → A1 r + A2 r + A3 r = u ∧
      ((q ≤ r ∧ r < q + d ∧ a ≤ A1 r) ∨ ((r < q ∨ q + d ≤ r) ∧ A1 r = 0)) ∧
      ((p ≤ r ∧ r < p + d ∧ a ≤ A2 r) ∨ (r < p ∧ 0 ≤ A2 r ∧ A2 r ≤ d) ∨
        (p + d ≤ r ∧ A2 r = 0)) ∧
      ((s ≤ r ∧ r < s + d ∧ a ≤ A3 r) ∨ ((r < s ∨ s + d ≤ r) ∧ A3 r = 0)) := by
    intro r h0 h1
    refine ⟨hsum r h0 h1, ?_, ?_, ?_⟩
    · by_cases h : q ≤ r ∧ r < q + d
      · exact Or.inl ⟨h.1, h.2, h1in r h.1 h.2⟩
      · exact Or.inr ⟨by omega, h1out r h⟩
    · by_cases h : p ≤ r ∧ r < p + d
      · exact Or.inl ⟨h.1, h.2, h2inb r h.1 h.2⟩
      · by_cases h' : r < p
        · exact Or.inr (Or.inl ⟨h', h2lo r h'⟩)
        · exact Or.inr (Or.inr ⟨by omega, h2top r (by omega)⟩)
    · by_cases h : s ≤ r ∧ r < s + d
      · exact Or.inl ⟨h.1, h.2, h3in r h.1 h.2⟩
      · exact Or.inr ⟨by omega, h3out r h⟩
  -- Step 1: coverage.
  have cov : ∀ r, 0 ≤ r → r < u →
      (q ≤ r ∧ r < q + d) ∨ (p ≤ r ∧ r < p + d) ∨ (s ≤ r ∧ r < s + d) := by
    intro r h0 h1; have := R r h0 h1; omega
  -- Step 4: pointwise equivalence, written as `(L ∨ R) ∧ (¬L ∨ ¬R)` with atoms only.
  have E : a + d < u → ∀ j, 0 ≤ j → j < d →
      (((q ≤ p + j ∧ p + j < q + d) ∨ (s ≤ p + j ∧ p + j < s + d)) ∨
        ((p ≤ ρ j ∧ ρ j < p + d) ∨ (s ≤ ρ j ∧ ρ j < s + d))) ∧
      (((p + j < q ∨ q + d ≤ p + j) ∧ (p + j < s ∨ s + d ≤ p + j)) ∨
        ((ρ j < p ∨ p + d ≤ ρ j) ∧ (ρ j < s ∨ s + d ≤ ρ j))) := by
    intro hk j hj0 hj1
    have hρb : q ≤ ρ j ∧ ρ j < q + d := by rw [hρ j]; split <;> omega
    have r2 := R (p + j) (by omega) (by omega)
    have r1 := R (ρ j) (by omega) (by omega)
    have := h2in j hj0 hj1
    have := h1g j hj0 hj1
    have := hg j hj0 hj1
    omega
  -- Step 2: standard position.
  have c0 := cov 0 (by omega) (by omega)
  have cu := cov (u - 1) (by omega) (by omega)
  have cd := cov d (by omega) (by omega)
  have cdd := cov (u - d - 1) (by omega) (by omega)
  clear cov
  -- Step 3 (overlap) is done inside each case.
  rcases c0 with h0 | h0 | h0
  · -- B1 = lo
    rcases cu with h1 | h1 | h1
    · omega
    · -- case 5: B2h = hi, B1 = lo, B3 = mid
      exact co_case5 u v w d a hd ha hu huv hvw h2d h3d h3a hwin h205 A1 A2 A3 g ρ e1 p q s hp hq hs hρ hsum hg h1in h1out h1g h2in h2inb h2lo h2p1 h2top h3in h3out R E h0 h1 cd cdd
    · -- case 3: B2h = mid, B1 = lo, B3 = hi
      exact co_case3 u v w d a hd ha hu huv hvw h2d h3d h3a hwin h205 A1 A2 A3 g ρ e1 p q s hp hq hs hρ hsum hg h1in h1out h1g h2in h2inb h2lo h2p1 h2top h3in h3out R E h0 h1 cd cdd
  · -- B2h = lo
    rcases cu with h1 | h1 | h1
    · -- case 2: B2h = lo, B1 = hi, B3 = mid
      exact co_case2 u v w d a hd ha hu huv hvw h2d h3d h3a hwin h205 A1 A2 A3 g ρ e1 p q s hp hq hs hρ hsum hg h1in h1out h1g h2in h2inb h2lo h2p1 h2top h3in h3out R E h0 h1 cd cdd
    · omega
    · -- case 1: B2h = lo, B1 = mid, B3 = hi
      exact co_case1 u v w d a hd ha hu huv hvw h2d h3d h3a hwin h205 A1 A2 A3 g ρ e1 p q s hp hq hs hρ hsum hg h1in h1out h1g h2in h2inb h2lo h2p1 h2top h3in h3out R E h0 h1 cd cdd
  · -- B3 = lo
    rcases cu with h1 | h1 | h1
    · -- case 4: B2h = mid, B1 = hi, B3 = lo
      exact co_case4 u v w d a hd ha hu huv hvw h2d h3d h3a hwin h205 A1 A2 A3 g ρ e1 p q s hp hq hs hρ hsum hg h1in h1out h1g h2in h2inb h2lo h2p1 h2top h3in h3out R E h0 h1 cd cdd
    · -- case 6: B2h = hi, B1 = mid, B3 = lo
      exact co_case6 u v w d a hd ha hu huv hvw h2d h3d h3a hwin h205 A1 A2 A3 g ρ e1 p q s hp hq hs hρ hsum hg h1in h1out h1g h2in h2inb h2lo h2p1 h2top h3in h3out R E h0 h1 cd cdd
    · omega

/-- The core lemma with `σ₂` increasing (`e2 = false`). -/
theorem co_core_inc (u v w : Int) (hu : 0 < u) (huv : u < v) (hvw : v < w)
    (h2d : 2 * (w - v) < u) (h3d : u ≠ 3 * (w - v)) (h3a : u < 3 * (w - u))
    (hwin : 2 * (w - u) ≤ u → (w - u) + (w - v) < u ∧ 2 * (w - u) ≠ u)
    (h205 : 2 * u = 5 * (w - v) → (w - v) + 2 * (w - u) ≠ u)
    (F1 F2 F3 : Int → Nat) (e1 e3 : Bool) (c1 c2 c3 : Int)
    (f1out : ∀ y, ¬ (v ≤ y ∧ y < w) → F1 y = 0)
    (f1bd : ∀ y, v ≤ y → y < w → w - u ≤ (F1 y : Int) ∧ (F1 y : Int) ≤ u)
    (f12 : ∀ y, v ≤ y → y < w → (F1 y : Int) + F2 y = w)
    (f2out : ∀ y, ¬ (w - u ≤ y ∧ y < w) → F2 y = 0)
    (f2arm : ∀ y, w - u ≤ y → y < v → (F2 y : Int) ≤ w - v)
    (f2forced : ∀ y, u ≤ y → y < v → (F2 y : Int) = w - v)
    (f3out : ∀ y, ¬ (v ≤ y ∧ y < w) → F3 y = 0)
    (f3bd : ∀ y, v ≤ y → y < w → w - u ≤ (F3 y : Int) ∧ (F3 y : Int) ≤ u)
    (img1 : ∀ y, 0 < F1 y → ∃ r, 0 ≤ r ∧ r < u ∧ aff e1 c1 r = y)
    (img2 : ∀ y, 0 < F2 y → ∃ r, 0 ≤ r ∧ r < u ∧ aff false c2 r = y)
    (img3 : ∀ y, 0 < F3 y → ∃ r, 0 ≤ r ∧ r < u ∧ aff e3 c3 r = y)
    (row : ∀ r, 0 ≤ r → r < u →
      (F1 (aff e1 c1 r) : Int) + F2 (aff false c2 r) + F3 (aff e3 c3 r) = u) :
    False := by
  have hb1 := co_bandin e1 c1 u v w hvw (fun y h1 h2 => img1 y (by have := f1bd y h1 h2; omega))
  have hb3 := co_bandin e3 c3 u v w hvw (fun y h1 h2 => img3 y (by have := f3bd y h1 h2; omega))
  have hb2 := co_bandin false c2 u v w hvw (fun y h1 h2 => img2 y
    (by have := f1bd y h1 h2; have := f12 y h1 h2; omega))
  simp only [co_bs, Bool.false_eq_true, ite_false] at hb2
  have a2 : ∀ r, aff false c2 r = r + c2 := fun r => rfl
  refine co_combi u v w (w - v) (w - u) rfl rfl hu huv hvw h2d h3d h3a hwin h205
    (fun r => (F1 (aff e1 c1 r) : Int)) (fun r => (F2 (r + c2) : Int)) (fun r => (F3 (aff e3 c3 r) : Int))
    (fun j => (F1 (v + j) : Int)) (fun j => if e1 then c1 - v - j else v + j - c1) e1
    (v - c2) (co_bs e1 c1 v w) (co_bs e3 c3 v w) (by omega) hb1 hb3 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro j; cases e1 <;> simp [co_bs] <;> omega
  · intro r h0 h1; have := row r h0 h1; rw [a2] at this; exact this
  · intro j h0 h1; exact f1bd (v + j) (by omega) (by omega)
  · intro r h0 h1
    have := (co_band e1 c1 v w r).2 ⟨h0, h1⟩
    exact (f1bd _ this.1 this.2).1
  · intro r h
    have : ¬ (v ≤ aff e1 c1 r ∧ aff e1 c1 r < w) := fun h' => h ((co_band e1 c1 v w r).1 h')
    simp [f1out _ this]
  · intro j h0 h1
    have : aff e1 c1 (if e1 then c1 - v - j else v + j - c1) = v + j := by
      cases e1 <;> simp [aff] <;> omega
    simp only [this]
  · intro j h0 h1
    have e : v - c2 + j + c2 = v + j := by omega
    simp only [e]; have := f12 (v + j) (by omega) (by omega); omega
  · intro r h0 h1
    have := f12 (r + c2) (by omega) (by omega); have := f1bd (r + c2) (by omega) (by omega); omega
  · intro r h
    by_cases h' : w - u ≤ r + c2
    · have := f2arm (r + c2) h' (by omega); omega
    · have := f2out (r + c2) (by omega); omega
  · have e : v - c2 - 1 + c2 = v - 1 := by omega
    simp only [e]; have := f2forced (v - 1) (by omega) (by omega); omega
  · intro r h; have := f2out (r + c2) (by omega); simp [this]
  · intro r h0 h1
    have := (co_band e3 c3 v w r).2 ⟨h0, h1⟩
    exact (f3bd _ this.1 this.2).1
  · intro r h
    have : ¬ (v ≤ aff e3 c3 r ∧ aff e3 c3 r < w) := fun h' => h ((co_band e3 c3 v w r).1 h')
    simp [f3out _ this]

/-- Reversing the target rows keeps the affine form. -/
def co_fc (e : Bool) (c u : Int) : Int := if e then c - u + 1 else c + u - 1

theorem co_flip (e : Bool) (c u r : Int) : aff (!e) (co_fc e c u) r = aff e c (u - 1 - r) := by
  cases e <;> simp [aff, co_fc] <;> omega

/-- **Core lemma.** `F1`, `F2`, `F3` are the line counts of the three pieces, as functions of the
source line index; `aff e_k c_k r` is the source line of piece `k` that goes to target row `r`.
Notation: `a = w - u`, `d = w - v`. -/
theorem core (u v w : Int) (hu : 0 < u) (huv : u < v) (hvw : v < w)
    (h2d : 2 * (w - v) < u) (h3d : u ≠ 3 * (w - v)) (h3a : u < 3 * (w - u))
    (hwin : 2 * (w - u) ≤ u → (w - u) + (w - v) < u ∧ 2 * (w - u) ≠ u)
    (h205 : 2 * u = 5 * (w - v) → (w - v) + 2 * (w - u) ≠ u)
    (F1 F2 F3 : Int → Nat) (e1 e2 e3 : Bool) (c1 c2 c3 : Int)
    (f1out : ∀ y, ¬ (v ≤ y ∧ y < w) → F1 y = 0)
    (f1bd : ∀ y, v ≤ y → y < w → w - u ≤ (F1 y : Int) ∧ (F1 y : Int) ≤ u)
    (f12 : ∀ y, v ≤ y → y < w → (F1 y : Int) + F2 y = w)
    (f2out : ∀ y, ¬ (w - u ≤ y ∧ y < w) → F2 y = 0)
    (f2arm : ∀ y, w - u ≤ y → y < v → (F2 y : Int) ≤ w - v)
    (f2forced : ∀ y, u ≤ y → y < v → (F2 y : Int) = w - v)
    (f3out : ∀ y, ¬ (v ≤ y ∧ y < w) → F3 y = 0)
    (f3bd : ∀ y, v ≤ y → y < w → w - u ≤ (F3 y : Int) ∧ (F3 y : Int) ≤ u)
    (img1 : ∀ y, 0 < F1 y → ∃ r, 0 ≤ r ∧ r < u ∧ aff e1 c1 r = y)
    (img2 : ∀ y, 0 < F2 y → ∃ r, 0 ≤ r ∧ r < u ∧ aff e2 c2 r = y)
    (img3 : ∀ y, 0 < F3 y → ∃ r, 0 ≤ r ∧ r < u ∧ aff e3 c3 r = y)
    (row : ∀ r, 0 ≤ r → r < u →
      (F1 (aff e1 c1 r) : Int) + F2 (aff e2 c2 r) + F3 (aff e3 c3 r) = u) :
    False := by
  cases e2
  · exact co_core_inc u v w hu huv hvw h2d h3d h3a hwin h205 F1 F2 F3 e1 e3 c1 c2 c3
      f1out f1bd f12 f2out f2arm f2forced f3out f3bd img1 img2 img3 row
  · have im : ∀ (F : Int → Nat) (e : Bool) (c : Int),
        (∀ y, 0 < F y → ∃ r, 0 ≤ r ∧ r < u ∧ aff e c r = y) →
        ∀ y, 0 < F y → ∃ r, 0 ≤ r ∧ r < u ∧ aff (!e) (co_fc e c u) r = y := by
      intro F e c h y hy
      obtain ⟨r, h0, h1, h2⟩ := h y hy
      refine ⟨u - 1 - r, by omega, by omega, ?_⟩
      rw [co_flip, show u - 1 - (u - 1 - r) = r by omega]; exact h2
    refine co_core_inc u v w hu huv hvw h2d h3d h3a hwin h205 F1 F2 F3 (!e1) (!e3)
      (co_fc e1 c1 u) (co_fc true c2 u) (co_fc e3 c3 u)
      f1out f1bd f12 f2out f2arm f2forced f3out f3bd (im F1 e1 c1 img1) (im F2 true c2 img2)
      (im F3 e3 c3 img3) ?_
    intro r h0 h1
    have := row (u - 1 - r) (by omega) (by omega)
    rw [co_flip, co_flip, show aff false (co_fc true c2 u) r = aff true c2 (u - 1 - r) from co_flip true c2 u r]
    exact this

end Ex89.ThreeOne
