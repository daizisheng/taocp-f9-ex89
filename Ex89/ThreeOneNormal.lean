import Ex89.Normal
/-! # 3+1 theorem: normal form and the strip lemma (lemma 1).
Reuses `Ex89/Sym.lean` and `Ex89/Normal.lean`. -/
namespace Ex89.ThreeOne
open Ex89

/-- Lower end of the band of images of `t ∈ [v, w)` under `t ↦ (if f then w-1-t else t) + c`. -/
def nf_lo (v : Nat) (f : Bool) (c : Int) : Int := if f then c else (v : Int) + c

theorem nf_Y_y (m : Motion) {v w x y : Nat} (hs : m.sw = false) (h1 : v ≤ y) (h2 : y < w) :
    nf_lo v m.fy m.dy ≤ m.imgY w x y ∧ m.imgY w x y < nf_lo v m.fy m.dy + ((w : Int) - v) := by
  rcases m with ⟨sw, fx, fy, dx, dy⟩
  simp only at hs; subst hs
  cases fy <;> simp [Motion.imgY, nf_lo] <;> omega

theorem nf_X_x (m : Motion) {v w x y : Nat} (hs : m.sw = false) (h1 : v ≤ x) (h2 : x < w) :
    nf_lo v m.fx m.dx ≤ m.imgX w x y ∧ m.imgX w x y < nf_lo v m.fx m.dx + ((w : Int) - v) := by
  rcases m with ⟨sw, fx, fy, dx, dy⟩
  simp only at hs; subst hs
  cases fx <;> simp [Motion.imgX, nf_lo] <;> omega

theorem nf_X_y (m : Motion) {v w x y : Nat} (hs : m.sw = true) (h1 : v ≤ y) (h2 : y < w) :
    nf_lo v m.fy m.dx ≤ m.imgX w x y ∧ m.imgX w x y < nf_lo v m.fy m.dx + ((w : Int) - v) := by
  rcases m with ⟨sw, fx, fy, dx, dy⟩
  simp only at hs; subst hs
  cases fy <;> simp [Motion.imgX, nf_lo] <;> omega

theorem nf_Y_x (m : Motion) {v w x y : Nat} (hs : m.sw = true) (h1 : v ≤ x) (h2 : x < w) :
    nf_lo v m.fx m.dy ≤ m.imgY w x y ∧ m.imgY w x y < nf_lo v m.fx m.dy + ((w : Int) - v) := by
  rcases m with ⟨sw, fx, fy, dx, dy⟩
  simp only at hs; subst hs
  cases fx <;> simp [Motion.imgY, nf_lo] <;> omega

/-- Row band and column band of a piece made of a top arm (`y ≥ v`) and a right arm (`x ≥ v`). -/
def nf_rowB (v : Nat) (m : Motion) : Int := if m.sw then nf_lo v m.fx m.dy else nf_lo v m.fy m.dy
def nf_colB (v : Nat) (m : Motion) : Int := if m.sw then nf_lo v m.fy m.dx else nf_lo v m.fx m.dx

theorem nf_arm (m : Motion) {v w x y : Nat} (hx : x < w) (hy : y < w) (h : v ≤ x ∨ v ≤ y) :
    (nf_rowB v m ≤ m.imgY w x y ∧ m.imgY w x y < nf_rowB v m + ((w : Int) - v)) ∨
    (nf_colB v m ≤ m.imgX w x y ∧ m.imgX w x y < nf_colB v m + ((w : Int) - v)) := by
  rcases m with ⟨sw, fx, fy, dx, dy⟩
  cases sw <;> cases fx <;> cases fy <;>
    simp [Motion.imgX, Motion.imgY, nf_rowB, nf_colB, nf_lo] <;> omega

theorem nf_fin4 (k : Fin 4) : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by
  revert k; decide

theorem nf_cover : ∀ a0 a1 a2 a3 k : Fin 4, a0 ≠ a1 → a0 ≠ a2 → a0 ≠ a3 → a1 ≠ a2 → a1 ≠ a3 →
    a2 ≠ a3 → k = a0 ∨ k = a1 ∨ k = a2 ∨ k = a3 := by decide

/-- Two integer intervals of length `d` do not cover `[0, u)` when `2d < u`. -/
theorem nf_gap (p q d u : Int) (hd : 0 ≤ d) (h : 2 * d < u) :
    ∃ r, 0 ≤ r ∧ r < u ∧ ¬ (p ≤ r ∧ r < p + d) ∧ ¬ (q ≤ r ∧ r < q + d) := by
  by_cases h0 : (p ≤ 0 ∧ 0 < p + d) ∨ (q ≤ 0 ∧ 0 < q + d)
  · by_cases h1 : p ≤ 0 ∧ 0 < p + d
    · by_cases h2 : q ≤ p + d ∧ p + d < q + d
      · exact ⟨q + d, by omega, by omega, by omega, by omega⟩
      · exact ⟨p + d, by omega, by omega, by omega, h2⟩
    · by_cases h2 : p ≤ q + d ∧ q + d < p + d
      · exact ⟨p + d, by omega, by omega, by omega, by omega⟩
      · exact ⟨q + d, by omega, by omega, h2, by omega⟩
  · exact ⟨0, by omega, by omega, by omega, by omega⟩

/-- A cell of a `u`-piece is close to the corner cell of that piece. -/
theorem nf_box {u v w : Nat} (E : Dissection u v w) (k : Fin 4) {cx cy x y : Nat}
    (hcx : cx < w) (hcy : cy < w) (hc : E.piece cx cy = k) (ht : E.toU k = true)
    (hx : x < w) (hy : y < w) (h : E.piece x y = k) :
    (x : Int) - cx < u ∧ (cx : Int) - x < u ∧ (y : Int) - cy < u ∧ (cy : Int) - y < u := by
  have m1 := E.maps_into x y hx hy
  have m2 := E.maps_into cx cy hcx hcy
  rw [h, ht] at m1; simp only [↓reduceIte] at m1
  rw [hc, ht] at m2; simp only [↓reduceIte] at m2
  exact Motion.close _ m1 m2

/-- Step 1: rotate, name the pieces by corners, make the motion of piece 0 the identity. -/
theorem nf_stage1 {u v w : Nat} (hu : 0 < u) (huv : u < v) (hvw : v < w) (D : Dissection u v w)
    (h31 : ∃ k, D.toU k = false ∧ ∀ j, j ≠ k → D.toU j = true) :
    ∃ E : Dissection u v w, E.toU 0 = false ∧ E.toU 1 = true ∧ E.toU 2 = true ∧
      E.toU 3 = true ∧ (∀ k, E.piece (cornerX w k) (cornerY w k) = k) ∧ E.motion 0 = idMotion := by
  have huw : u < w := by omega
  have hw : 0 < w := by omega
  have hrot : ∃ D' : Dissection u v w, (∃ k, D'.toU k = false ∧ ∀ j, j ≠ k → D'.toU j = true) ∧
      pat D' 0 = false := by
    obtain ⟨k, hk, hj⟩ := h31
    have hcov := nf_cover _ _ _ _ k
      (corner_ne D huw hvw 0 1 (by decide)) (corner_ne D huw hvw 0 2 (by decide))
      (corner_ne D huw hvw 0 3 (by decide)) (corner_ne D huw hvw 1 2 (by decide))
      (corner_ne D huw hvw 1 3 (by decide)) (corner_ne D huw hvw 2 3 (by decide))
    obtain ⟨a1, a2, a3, a4⟩ := pat_rot D
    obtain ⟨b1, b2, b3, b4⟩ := pat_rot D.rot
    obtain ⟨c1, c2, c3, c4⟩ := pat_rot D.rot.rot
    rcases hcov with e | e | e | e
    · exact ⟨D, ⟨k, hk, hj⟩, by unfold pat; rw [← e]; exact hk⟩
    · exact ⟨D.rot, ⟨k, hk, hj⟩, by rw [a1]; unfold pat; rw [← e]; exact hk⟩
    · exact ⟨D.rot.rot, ⟨k, hk, hj⟩, by rw [b1, a2]; unfold pat; rw [← e]; exact hk⟩
    · exact ⟨D.rot.rot.rot, ⟨k, hk, hj⟩, by rw [c1, b2, a3]; unfold pat; rw [← e]; exact hk⟩
  obtain ⟨D', ⟨k, hk, hj⟩, hp0⟩ := hrot
  have hk0 : D'.piece (cornerX w 0) (cornerY w 0) = k := by
    by_cases hne : D'.piece (cornerX w 0) (cornerY w 0) = k
    · exact hne
    · have := hj _ hne
      unfold pat at hp0
      rw [this] at hp0
      exact absurd hp0 (by decide)
  have hpi : ∀ i : Fin 4, i ≠ 0 → pat D' i = true := by
    intro i hi; unfold pat; apply hj; rw [← hk0]; exact corner_ne D' huw hvw i 0 hi
  obtain ⟨E, es, ec⟩ := exists_named D' huw hvw
  have e0 : E.toU 0 = false := by rw [es]; exact hp0
  have e1 : E.toU 1 = true := by rw [es]; exact hpi 1 (by decide)
  have e2 : E.toU 2 = true := by rw [es]; exact hpi 2 (by decide)
  have e3 : E.toU 3 = true := by rw [es]; exact hpi 3 (by decide)
  obtain ⟨E1, p1, t1, _, a1, b1, c1⟩ := exists_fixed E 0
  have hc : ∀ k, E1.piece (cornerX w k) (cornerY w k) = k := by intro k; rw [p1]; exact ec k
  have hz : E1.motion 0 = idMotion := by
    apply fixed_zero E1 hw 0 (hc 0) (by simp [cornerX, cornerY])
    · rw [t1, e0]; simpa using (show 0 < v by omega)
    · rw [t1, e0]
      apply slot_cases <;> simp [e1, e2, e3]
    · exact a1
    · exact b1
    · exact c1
  exact ⟨E1, by rw [t1]; exact e0, by rw [t1]; exact e1, by rw [t1]; exact e2,
    by rw [t1]; exact e3, hc, hz⟩

/-- Lemma 1 (strips): the strips of pieces 1 and 3 are not parallel in the `u`-target. -/
theorem nf_strip {u v w : Nat} (huv : u < v) (hvw : v < w) (h2d : 2 * (w - v) < u)
    (E : Dissection u v w) (t0 : E.toU 0 = false)
    (hp0 : ∀ x y, x < w → y < w → (E.piece x y = 0 ↔ x < v ∧ y < v))
    (hp1 : ∀ x y, x < w → y < w → E.piece x y = 1 → x < u)
    (hp3 : ∀ x y, x < w → y < w → E.piece x y = 3 → y < u) :
    (E.motion 1).sw ≠ (E.motion 3).sw := by
  intro hs
  have hv1 : ∀ x y, x < w → y < w → E.piece x y ≠ 0 → v ≤ x ∨ v ≤ y := by
    intro x y hx hy hne
    by_cases hc : v ≤ x ∨ v ≤ y
    · exact hc
    · exact absurd ((hp0 x y hx hy).2 (by omega)) hne
  obtain ⟨R, C, hRC⟩ : ∃ R C : Int, ∀ x y, x < w → y < w → (E.piece x y = 1 ∨ E.piece x y = 3) →
      (R ≤ (E.motion (E.piece x y)).imgY w x y ∧
        (E.motion (E.piece x y)).imgY w x y < R + ((w : Int) - v)) ∨
      (C ≤ (E.motion (E.piece x y)).imgX w x y ∧
        (E.motion (E.piece x y)).imgX w x y < C + ((w : Int) - v)) := by
    cases h1 : (E.motion 1).sw
    · have h3 : (E.motion 3).sw = false := by rw [← hs, h1]
      refine ⟨nf_lo v (E.motion 1).fy (E.motion 1).dy, nf_lo v (E.motion 3).fx (E.motion 3).dx, ?_⟩
      intro x y hx hy h
      rcases h with h | h
      · have a := hp1 x y hx hy h
        have b := hv1 x y hx hy (by rw [h]; decide)
        rw [h]; left; exact nf_Y_y (E.motion 1) (x := x) h1 (by omega) hy
      · have a := hp3 x y hx hy h
        have b := hv1 x y hx hy (by rw [h]; decide)
        rw [h]; right; exact nf_X_x (E.motion 3) (y := y) h3 (by omega) hx
    · have h3 : (E.motion 3).sw = true := by rw [← hs, h1]
      refine ⟨nf_lo v (E.motion 3).fx (E.motion 3).dy, nf_lo v (E.motion 1).fy (E.motion 1).dx, ?_⟩
      intro x y hx hy h
      rcases h with h | h
      · have a := hp1 x y hx hy h
        have b := hv1 x y hx hy (by rw [h]; decide)
        rw [h]; right; exact nf_X_y (E.motion 1) (x := x) h1 (by omega) hy
      · have a := hp3 x y hx hy h
        have b := hv1 x y hx hy (by rw [h]; decide)
        rw [h]; left; exact nf_Y_x (E.motion 3) (y := y) h3 (by omega) hx
  have hall : ∀ x y, x < w → y < w → E.piece x y ≠ 0 →
      ((R ≤ (E.motion (E.piece x y)).imgY w x y ∧
        (E.motion (E.piece x y)).imgY w x y < R + ((w : Int) - v)) ∨
       (nf_rowB v (E.motion 2) ≤ (E.motion (E.piece x y)).imgY w x y ∧
        (E.motion (E.piece x y)).imgY w x y < nf_rowB v (E.motion 2) + ((w : Int) - v))) ∨
      ((C ≤ (E.motion (E.piece x y)).imgX w x y ∧
        (E.motion (E.piece x y)).imgX w x y < C + ((w : Int) - v)) ∨
       (nf_colB v (E.motion 2) ≤ (E.motion (E.piece x y)).imgX w x y ∧
        (E.motion (E.piece x y)).imgX w x y < nf_colB v (E.motion 2) + ((w : Int) - v))) := by
    intro x y hx hy hne
    rcases nf_fin4 (E.piece x y) with h | h | h | h
    · exact absurd h hne
    · have := hRC x y hx hy (Or.inl h); omega
    · have := nf_arm (E.motion 2) hx hy (hv1 x y hx hy hne)
      rw [h]; omega
    · have := hRC x y hx hy (Or.inr h); omega
  obtain ⟨r, r0, r1, r2, r3⟩ := nf_gap R (nf_rowB v (E.motion 2)) ((w : Int) - v) u (by omega) (by omega)
  obtain ⟨c, c0, c1, c2, c3⟩ := nf_gap C (nf_colB v (E.motion 2)) ((w : Int) - v) u (by omega) (by omega)
  obtain ⟨x, y, hx, hy, hb, e1, e2⟩ := E.surjective true c r
    (by simp only [↓reduceIte, InSquare]; omega)
  have hne : E.piece x y ≠ 0 := by
    intro h; rw [h, t0] at hb; exact absurd hb (by decide)
  have := hall x y hx hy hne
  rw [e1, e2] at this
  omega


/-- **Normal form + lemma 1.** A 3+1 dissection can be brought to the normal form: piece 0 is the
`v × v` square at the origin, pieces 1, 2, 3 sit at the corners `(0,w-1)`, `(w-1,w-1)`, `(w-1,0)`;
moreover (lemma 1, strips) the strips of pieces 1 and 3 are parallel and, after transposing the
`u × u` target, both are target rows: `(motion 1).sw = false`, `(motion 3).sw = true`. -/
theorem exists_normal31 {u v w : Nat} (hu : 0 < u) (huv : u < v) (hvw : v < w)
    (h2d : 2 * (w - v) < u) (D : Dissection u v w)
    (h31 : ∃ k, D.toU k = false ∧ ∀ j, j ≠ k → D.toU j = true) :
    ∃ E : Dissection u v w, E.toU 0 = false ∧ E.toU 1 = true ∧ E.toU 2 = true ∧ E.toU 3 = true ∧
      (∀ x y, x < w → y < w → (E.piece x y = 0 ↔ x < v ∧ y < v)) ∧
      (∀ x y, x < w → y < w → E.piece x y = 1 → x < u) ∧
      (∀ x y, x < w → y < w → E.piece x y = 2 → w - u ≤ x ∧ w - u ≤ y) ∧
      (∀ x y, x < w → y < w → E.piece x y = 3 → y < u) ∧
      (E.motion 1).sw = false ∧ (E.motion 3).sw = true := by
  obtain ⟨E, t0, t1, t2, t3, hc, hz⟩ := nf_stage1 hu huv hvw D h31
  have hk0 : ∀ j, E.toU j = false → j = 0 := by
    intro j hj
    rcases nf_fin4 j with h | h | h | h <;> subst h
    · rfl
    · rw [t1] at hj; exact absurd hj (by decide)
    · rw [t2] at hj; exact absurd hj (by decide)
    · rw [t3] at hj; exact absurd hj (by decide)
  have hp0 : ∀ x y, x < w → y < w → (E.piece x y = 0 ↔ x < v ∧ y < v) := by
    intro x y hx hy
    constructor
    · intro h
      have m := E.maps_into x y hx hy
      rw [h, t0, hz] at m
      simp [InSquare, Motion.imgX, Motion.imgY, idMotion] at m
      omega
    · intro ⟨h1, h2⟩
      obtain ⟨x', y', hx', hy', hb, e1, e2⟩ := E.surjective false x y
        (by simp only [Bool.false_eq_true, ite_false, InSquare]; omega)
      have h0 := hk0 _ hb
      rw [h0, hz] at e1 e2
      simp [Motion.imgX, Motion.imgY, idMotion] at e1 e2
      have ex : x' = x := by omega
      have ey : y' = y := by omega
      rw [← ex, ← ey]; exact h0
  have c1 : E.piece 0 (w - 1) = 1 := by have := hc 1; simpa [cornerX, cornerY] using this
  have c2 : E.piece (w - 1) (w - 1) = 2 := by have := hc 2; simpa [cornerX, cornerY] using this
  have c3 : E.piece (w - 1) 0 = 3 := by have := hc 3; simpa [cornerX, cornerY] using this
  have hp1 : ∀ x y, x < w → y < w → E.piece x y = 1 → x < u := by
    intro x y hx hy h
    have := nf_box E 1 (by omega) (by omega) c1 t1 hx hy h
    omega
  have hp2 : ∀ x y, x < w → y < w → E.piece x y = 2 → w - u ≤ x ∧ w - u ≤ y := by
    intro x y hx hy h
    have := nf_box E 2 (by omega) (by omega) c2 t2 hx hy h
    omega
  have hp3 : ∀ x y, x < w → y < w → E.piece x y = 3 → y < u := by
    intro x y hx hy h
    have := nf_box E 3 (by omega) (by omega) c3 t3 hx hy h
    omega
  have hs := nf_strip huv hvw h2d E t0 hp0 hp1 hp3
  cases hs1 : (E.motion 1).sw
  · have hs3 : (E.motion 3).sw = true := by
      cases h : (E.motion 3).sw
      · rw [hs1, h] at hs; exact absurd rfl hs
      · rfl
    exact ⟨E, t0, t1, t2, t3, hp0, hp1, hp2, hp3, hs1, hs3⟩
  · have hs3 : (E.motion 3).sw = false := by
      cases h : (E.motion 3).sw
      · rfl
      · rw [hs1, h] at hs; exact absurd rfl hs
    refine ⟨E.mapT true (swapMap _ w), t0, t1, t2, t3, hp0, hp1, hp2, hp3, ?_, ?_⟩
    · simp [Dissection.mapT, swapMap, t1, hs1]
    · simp [Dissection.mapT, swapMap, t3, hs3]

end Ex89.ThreeOne
