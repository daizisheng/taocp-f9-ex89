import Ex89.Sound
/-! Every dissection can be brought to the normal form of one of the four configurations. -/
namespace Ex89

/-- The target square of the piece at corner `k`. -/
def pat {u v w : Nat} (D : Dissection u v w) (k : Fin 4) : Bool :=
  D.toU (D.piece (cornerX w k) (cornerY w k))

theorem pat_rot {u v w : Nat} (D : Dissection u v w) :
    pat D.rot 0 = pat D 1 ∧ pat D.rot 1 = pat D 2 ∧ pat D.rot 2 = pat D 3 ∧ pat D.rot 3 = pat D 0 := by
  have e : w - 1 - (w - 1) = 0 := by omega
  simp [pat, Dissection.rot, cornerX, cornerY, e]

def A (b0 b1 b2 b3 : Bool) : Bool :=
  (b0 == b1 && b1 == b2 && b2 == b3) ||
  (!b0 && b1 && !b2 && b3) || (!b0 && !b1 && b2 && b3) ||
  (b0 && !b1 && !b2 && !b3) || (!b0 && b1 && b2 && b3)

theorem A_rot : ∀ b0 b1 b2 b3 : Bool,
    A b0 b1 b2 b3 ∨ A b1 b2 b3 b0 ∨ A b2 b3 b0 b1 ∨ A b3 b0 b1 b2 := by decide

theorem exists_canon {u v w : Nat} (D : Dissection u v w) :
    ∃ D' : Dissection u v w, A (pat D' 0) (pat D' 1) (pat D' 2) (pat D' 3) = true := by
  obtain ⟨a1, a2, a3, a4⟩ := pat_rot D
  obtain ⟨b1, b2, b3, b4⟩ := pat_rot D.rot
  obtain ⟨c1, c2, c3, c4⟩ := pat_rot D.rot.rot
  rcases A_rot (pat D 0) (pat D 1) (pat D 2) (pat D 3) with h | h | h | h
  · exact ⟨D, h⟩
  · exact ⟨D.rot, by rw [a1, a2, a3, a4]; exact h⟩
  · exact ⟨D.rot.rot, by rw [b1, b2, b3, b4, a1, a2, a3, a4]; exact h⟩
  · exact ⟨D.rot.rot.rot, by rw [c1, c2, c3, c4, b1, b2, b3, b4, a1, a2, a3, a4]; exact h⟩

theorem corner_far (w : Nat) (hw : 0 < w) (i j : Fin 4) (h : i ≠ j) :
    ((cornerX w i : Int) - cornerX w j = w - 1 ∨ (cornerX w j : Int) - cornerX w i = w - 1 ∨
     (cornerY w i : Int) - cornerY w j = w - 1 ∨ (cornerY w j : Int) - cornerY w i = w - 1) := by
  revert i j
  apply slot_cases <;> (apply slot_cases <;> intro h <;>
    first
      | exact absurd rfl h
      | (simp only [cornerX, cornerY]; omega))

theorem corner_lt (w : Nat) (hw : 0 < w) (k : Fin 4) : cornerX w k < w ∧ cornerY w k < w := by
  revert k
  apply slot_cases <;> simp [cornerX, cornerY] <;> omega

theorem corner_ne {u v w : Nat} (D : Dissection u v w) (huw : u < w) (hvw : v < w) (i j : Fin 4)
    (h : i ≠ j) : D.piece (cornerX w i) (cornerY w i) ≠ D.piece (cornerX w j) (cornerY w j) := by
  intro e
  have hw : 0 < w := by omega
  obtain ⟨a1, a2⟩ := corner_lt w hw i
  obtain ⟨b1, b2⟩ := corner_lt w hw j
  have m1 := D.maps_into _ _ a1 a2
  have m2 := D.maps_into _ _ b1 b2
  rw [← e] at m2
  have := Motion.close _ m1 m2
  have hS : (if D.toU (D.piece (cornerX w i) (cornerY w i)) = true then u else v) < w := by
    split <;> omega
  have := corner_far w hw i j h
  omega

def tauOf (a0 a1 a2 a3 : Fin 4) : Fin 4 → Fin 4
  | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3
def sigOf (a0 a1 a2 : Fin 4) (k : Fin 4) : Fin 4 :=
  if k = a0 then 0 else if k = a1 then 1 else if k = a2 then 2 else 3

def permOk (a0 a1 a2 a3 : Fin 4) : Bool :=
  a0 == a1 || a0 == a2 || a0 == a3 || a1 == a2 || a1 == a3 || a2 == a3 ||
  (allSlots.all fun k => tauOf a0 a1 a2 a3 (sigOf a0 a1 a2 k) == k &&
    sigOf a0 a1 a2 (tauOf a0 a1 a2 a3 k) == k)

set_option maxRecDepth 100000 in
theorem permOk_all : ∀ a0 a1 a2 a3 : Fin 4, permOk a0 a1 a2 a3 = true := by decide

theorem perm_facts (a0 a1 a2 a3 : Fin 4) (h1 : a0 ≠ a1) (h2 : a0 ≠ a2) (h3 : a0 ≠ a3) (h4 : a1 ≠ a2)
    (h5 : a1 ≠ a3) (h6 : a2 ≠ a3) :
    (∀ k, tauOf a0 a1 a2 a3 (sigOf a0 a1 a2 k) = k) ∧ (∀ i, sigOf a0 a1 a2 (tauOf a0 a1 a2 a3 i) = i) := by
  have := permOk_all a0 a1 a2 a3
  simp only [permOk, h1, h2, h3, h4, h5, h6, beq_iff_eq, Bool.or_eq_true, List.all_eq_true,
    Bool.and_eq_true, beq_self_eq_true, false_or, or_false, reduceCtorEq, Bool.false_eq_true] at this
  exact ⟨fun k => (this k (mem_allSlots k)).1, fun k => (this k (mem_allSlots k)).2⟩

/-- Name each piece by its corner. -/
theorem exists_named {u v w : Nat} (D : Dissection u v w) (huw : u < w) (hvw : v < w) :
    ∃ D' : Dissection u v w, (∀ k, D'.toU k = pat D k) ∧
      ∀ k, D'.piece (cornerX w k) (cornerY w k) = k := by
  let a : Fin 4 → Fin 4 := fun k => D.piece (cornerX w k) (cornerY w k)
  obtain ⟨h1, h2⟩ := perm_facts (a 0) (a 1) (a 2) (a 3)
    (corner_ne D huw hvw _ _ (by decide)) (corner_ne D huw hvw _ _ (by decide))
    (corner_ne D huw hvw _ _ (by decide)) (corner_ne D huw hvw _ _ (by decide))
    (corner_ne D huw hvw _ _ (by decide)) (corner_ne D huw hvw _ _ (by decide))
  have htau : ∀ k, tauOf (a 0) (a 1) (a 2) (a 3) k = a k := by apply slot_cases <;> rfl
  refine ⟨D.relabel _ _ h1, ?_, ?_⟩
  · intro k
    show D.toU (tauOf (a 0) (a 1) (a 2) (a 3) k) = _
    rw [htau]; rfl
  · intro k
    show sigOf (a 0) (a 1) (a 2) (a k) = k
    have := h2 k
    rw [htau] at this
    exact this

/-- Make the symmetry of slot `k` the identity, by changing only the target square of slot `k`. -/
theorem exists_fixed {u v w : Nat} (D : Dissection u v w) (k : Fin 4) :
    ∃ D' : Dissection u v w, D'.piece = D.piece ∧ D'.toU = D.toU ∧
      (∀ j, D.toU j ≠ D.toU k → D'.motion j = D.motion j) ∧
      (D'.motion k).sw = false ∧ (D'.motion k).fx = false ∧ (D'.motion k).fy = false := by
  -- first the swap
  have s1 : ∃ D1 : Dissection u v w, D1.piece = D.piece ∧ D1.toU = D.toU ∧
      (∀ j, D.toU j ≠ D.toU k → D1.motion j = D.motion j) ∧ (D1.motion k).sw = false := by
    cases hs : (D.motion k).sw with
    | false => exact ⟨D, rfl, rfl, fun _ _ => rfl, hs⟩
    | true =>
      refine ⟨D.mapT (D.toU k) (swapMap _ _), rfl, rfl, ?_, ?_⟩
      · intro j hj; simp [Dissection.mapT, hj]
      · simp [Dissection.mapT, swapMap, hs]
  obtain ⟨D1, p1, t1, o1, h1⟩ := s1
  have s2 : ∃ D2 : Dissection u v w, D2.piece = D.piece ∧ D2.toU = D.toU ∧
      (∀ j, D.toU j ≠ D.toU k → D2.motion j = D.motion j) ∧
      (D2.motion k).sw = false ∧ (D2.motion k).fx = false := by
    cases hf : (D1.motion k).fx with
    | false => exact ⟨D1, p1, t1, o1, h1, hf⟩
    | true =>
      have hk : D1.toU k = D.toU k := by rw [t1]
      refine ⟨D1.mapT (D1.toU k) (flipXMap _ _), p1, t1, ?_, ?_, ?_⟩
      · intro j hj
        have : D1.toU j ≠ D1.toU k := by rw [t1]; exact hj
        simp only [Dissection.mapT, this, ite_false]
        exact o1 j hj
      · simp [Dissection.mapT, flipXMap, h1]
      · simp [Dissection.mapT, flipXMap, h1, hf]
  obtain ⟨D2, p2, t2, o2, h2, h2'⟩ := s2
  cases hg : (D2.motion k).fy with
  | false => exact ⟨D2, p2, t2, o2, h2, h2', hg⟩
  | true =>
    refine ⟨D2.mapT (D2.toU k) (flipYMap _ _), p2, t2, ?_, ?_, ?_, ?_⟩
    · intro j hj
      have : D2.toU j ≠ D2.toU k := by rw [t2]; exact hj
      simp only [Dissection.mapT, this, ite_false]
      exact o2 j hj
    · simp [Dissection.mapT, flipYMap, h2]
    · simp [Dissection.mapT, flipYMap, h2, h2']
    · simp [Dissection.mapT, flipYMap, h2, hg]

/-- A piece alone in its target square, with identity symmetry, does not move. -/
theorem fixed_zero {u v w : Nat} (D : Dissection u v w) (hw : 0 < w) (k : Fin 4) (hc : D.piece (cornerX w k) (cornerY w k) = k)
    (h0 : cornerX w k = 0 ∧ cornerY w k = 0)
    (hS : 0 < (if D.toU k then u else v))
    (halone : ∀ j, D.toU j = D.toU k → j = k)
    (h1 : (D.motion k).sw = false) (h2 : (D.motion k).fx = false) (h3 : (D.motion k).fy = false) :
    D.motion k = idMotion := by
  obtain ⟨cx, cy⟩ := corner_lt w hw k
  have m := D.maps_into _ _ cx cy
  rw [hc, h0.1, h0.2] at m
  obtain ⟨x, y, _, _, hb, e1, e2⟩ := D.surjective (D.toU k) 0 0 (by simp only [InSquare]; omega)
  have := halone _ hb
  rw [this] at e1 e2
  rcases hm : D.motion k with ⟨sw, fx, fy, dx, dy⟩
  rw [hm] at m e1 e2 h1 h2 h3
  simp only at h1 h2 h3
  subst h1 h2 h3
  simp [Motion.imgX, Motion.imgY, InSquare] at m e1 e2
  simp only [idMotion, Motion.mk.injEq, true_and]
  omega

theorem no_dissection_of_check {u v w : Nat} (hu : 0 < u) (hv : 0 < v) (huw : u < w) (hvw : v < w)
    (h : checkAll u v w = true) : NoDissection u v w := by
  intro D0
  have hw : 0 < w := by omega
  simp only [checkAll, Bool.and_eq_true] at h
  obtain ⟨⟨⟨hd, ha⟩, hU⟩, hV⟩ := h
  obtain ⟨D, hA⟩ := exists_canon D0
  obtain ⟨E, es, ec⟩ := exists_named D huw hvw
  have e0 := es 0; have e1 := es 1; have e2 := es 2; have e3 := es 3
  -- all cases of the pattern
  rcases h0 : pat D 0 <;> rcases h1 : pat D 1 <;> rcases h2 : pat D 2 <;> rcases h3 : pat D 3 <;>
    simp [h0, h1, h2, h3, A] at hA <;> rw [h0] at e0 <;> rw [h1] at e1 <;> rw [h2] at e2 <;> rw [h3] at e3
  · -- all pieces go to the `v × v` square
    obtain ⟨x, y, _, _, hb, _⟩ := E.surjective true 0 0 (by simp only [ite_true, InSquare]; omega)
    have : ∀ k, E.toU k = false := by apply slot_cases <;> assumption
    rw [this] at hb; simp at hb
  · -- pattern `F F T T`
    obtain ⟨E1, p1, t1, o1, a1, b1, c1⟩ := exists_fixed E 0
    obtain ⟨E2, p2, t2, o2, a2, b2, c2⟩ := exists_fixed E1 2
    have hc : ∀ k, E2.piece (cornerX w k) (cornerY w k) = k := by intro k; rw [p2, p1]; exact ec k
    have o : E1.toU 0 ≠ E1.toU 2 := by rw [t1, e0, e2]; simp
    have m0 := o2 0 o
    refine Fits.check22_false (c := cfgAdj u v w) (D := E2) ⟨?_, hc, ?_, ?_, hu, hv, huw, hvw⟩
      (a := 0) (b := 1) (e := 2) (d := 3) (by decide) (by decide) (by decide) rfl rfl (by apply slot_cases <;> simp [cfgAdj]) (by apply slot_cases <;> simp [cfgAdj]) ha
    · rw [t2, t1]; apply slot_cases <;> simp [cfgAdj, e0, e1, e2, e3]
    · apply slot_cases <;> intro hk <;> simp_all [cfgAdj]
    · intro k hk; simp [cfgAdj] at hk
  · -- pattern `F T F T`
    obtain ⟨E1, p1, t1, o1, a1, b1, c1⟩ := exists_fixed E 0
    obtain ⟨E2, p2, t2, o2, a2, b2, c2⟩ := exists_fixed E1 1
    have hc : ∀ k, E2.piece (cornerX w k) (cornerY w k) = k := by intro k; rw [p2, p1]; exact ec k
    have o : E1.toU 0 ≠ E1.toU 1 := by rw [t1, e0, e1]; simp
    have m0 := o2 0 o
    refine Fits.check22_false (c := cfgDiag u v w) (D := E2) ⟨?_, hc, ?_, ?_, hu, hv, huw, hvw⟩
      (a := 0) (b := 2) (e := 1) (d := 3) (by decide) (by decide) (by decide) rfl rfl (by apply slot_cases <;> simp [cfgDiag]) (by apply slot_cases <;> simp [cfgDiag]) hd
    · rw [t2, t1]; apply slot_cases <;> simp [cfgDiag, e0, e1, e2, e3]
    · apply slot_cases <;> intro hk <;> simp_all [cfgDiag]
    · intro k hk; simp [cfgDiag] at hk
  · -- pattern `F T T T`: slot 0 fills the `v × v` square
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
    refine Fits.check13_false (c := cfgV u v w) (D := E2) ⟨?_, hc, ?_, ?_, hu, hv, huw, hvw⟩
      rfl rfl (by apply slot_cases <;> simp [cfgV]) rfl hV
    · rw [t2, t1]; apply slot_cases <;> simp [cfgV, e0, e1, e2, e3]
    · apply slot_cases <;> intro hk <;> simp_all [cfgV]
    · apply slot_cases <;> intro hk <;> simp_all [cfgV]
  · -- pattern `T F F F`: slot 0 fills the `u × u` square
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
    refine Fits.check13_false (c := cfgU u v w) (D := E2) ⟨?_, hc, ?_, ?_, hu, hv, huw, hvw⟩
      rfl rfl (by apply slot_cases <;> simp [cfgU]) rfl hU
    · rw [t2, t1]; apply slot_cases <;> simp [cfgU, e0, e1, e2, e3]
    · apply slot_cases <;> intro hk <;> simp_all [cfgU]
    · apply slot_cases <;> intro hk <;> simp_all [cfgU]
  · -- all pieces go to the `u × u` square
    obtain ⟨x, y, _, _, hb, _⟩ := E.surjective false 0 0 (by simp only [Bool.false_eq_true, ite_false, InSquare]; omega)
    have : ∀ k, E.toU k = true := by apply slot_cases <;> assumption
    rw [this] at hb; simp at hb

end Ex89
