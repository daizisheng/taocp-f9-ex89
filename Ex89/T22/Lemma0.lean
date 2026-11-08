import Ex89.T22.Defs

/-!
# Lemma 0: parameters of a non-3:4:5 Pythagorean triple and the three regions

`u = d+e+f`, `v = d+2e+f`, `w = 2d+2e+f`. The Pythagorean equation becomes
`(e+f)² = 2d(d+e)`; for a non-`3:4:5` triple the parameters lie in one of the regions
`fat`, `mid`, `thin` of `Defs.RegionP`. Thin `adj` has no normal form.
-/
namespace Ex89.T22

/-! ## Small sign lemmas -/

theorem L0.sq_nonneg (t : Int) : 0 ≤ t * t := by
  rcases Int.le_total 0 t with h | h
  · exact Int.mul_nonneg h h
  · have h' : 0 ≤ -t := by omega
    have := Int.mul_nonneg h' h'
    have e : (-t) * (-t) = t * t := by grind
    omega

theorem L0.sq_pos (t : Int) (h : t ≠ 0) : 0 < t * t := by
  rcases Int.lt_or_gt_of_ne h with h | h
  · have h' : 0 < -t := by omega
    have := Int.mul_pos h' h'
    have e : (-t) * (-t) = t * t := by grind
    omega
  · exact Int.mul_pos h h

/-- If `2 d K = s²` with `d ≥ 1` then `K ≥ 0`, and `K = 0` forces `s = 0`. -/
theorem L0.nonneg_of_sq (d K s : Int) (hd : 1 ≤ d) (h : 2 * d * K = s * s) :
    0 ≤ K ∧ (K = 0 → s = 0) := by
  constructor
  · apply Classical.byContradiction
    intro hK
    have := Int.mul_lt_mul_of_pos_left (show K < 0 by omega) (show (0:Int) < 2 * d by omega)
    have := L0.sq_nonneg s
    rw [Int.mul_zero] at *
    omega
  · intro hK
    apply Classical.byContradiction
    intro hs
    have := L0.sq_pos s hs
    rw [hK, Int.mul_zero] at h
    omega

/-- `3 n²` is not a square for `n ≥ 1` (natural numbers, by descent). -/
theorem L0.not_sq_three_nat : ∀ (n m : Nat), 0 < n → m * m = 3 * (n * n) → False := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro m hn h
    have hm3 : m % 3 = 0 := by
      have hmod : (m * m) % 3 = ((m % 3) * (m % 3)) % 3 := Nat.mul_mod _ _ _
      rw [h] at hmod
      have : m % 3 < 3 := Nat.mod_lt _ (by omega)
      rcases (show m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 by omega) with r | r | r <;>
        rw [r] at hmod <;> simp at hmod <;> omega
    obtain ⟨q, rfl⟩ : ∃ q, m = 3 * q := ⟨m / 3, by omega⟩
    have h2 : n * n = 3 * (q * q) := by
      have : 3 * (3 * (q * q)) = 3 * (n * n) := by rw [← h]; grind
      omega
    have hn3 : n % 3 = 0 := by
      have hmod : (n * n) % 3 = ((n % 3) * (n % 3)) % 3 := Nat.mul_mod _ _ _
      rw [h2] at hmod
      rcases (show n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 by omega) with r | r | r <;>
        rw [r] at hmod <;> simp at hmod <;> omega
    obtain ⟨r, rfl⟩ : ∃ r, n = 3 * r := ⟨n / 3, by omega⟩
    have h3 : q * q = 3 * (r * r) := by
      have : 3 * (3 * (r * r)) = 3 * (q * q) := by rw [← h2]; grind
      omega
    exact ih r (by omega) q (by omega) h3

theorem L0.not_sq_three (d m : Int) (hd : 1 ≤ d) (h : m * m = 3 * (d * d)) : False := by
  have hm : m * m = ((m.natAbs * m.natAbs : Nat) : Int) := Int.natAbs_mul_self.symm
  have hd' : d * d = ((d.natAbs * d.natAbs : Nat) : Int) := Int.natAbs_mul_self.symm
  rw [hm, hd'] at h
  have : m.natAbs * m.natAbs = 3 * (d.natAbs * d.natAbs) := by omega
  exact L0.not_sq_three_nat d.natAbs m.natAbs (by omega) this

/-! ## Main statements -/

/-- Pythagoras in the parameters u = d+e+f, v = d+2e+f, w = 2d+2e+f. -/
theorem pyth_iff (d e f : Int) :
    (d+e+f)*(d+e+f) + (d+2*e+f)*(d+2*e+f) = (2*d+2*e+f)*(2*d+2*e+f) ↔ (e+f)*(e+f) = 2*d*(d+e) := by
  constructor <;> intro h <;> grind

/-- From a Nat triple to parameter facts. -/
theorem params_of_triple (u v w : Nat) (h1 : 0 < u) (h2 : u < v) (h3 : v < w) (hp : u*u + v*v = w*w)
    (hn : ¬ ∃ k, u = 3*k ∧ v = 4*k ∧ w = 5*k) (d e f : Int)
    (hd : d = (w:Int) - v) (he : e = (v:Int) - u) (hf : f = 2*(u:Int) - w) :
    1 ≤ d ∧ 1 ≤ e ∧ 1 ≤ d + e + f ∧ (e+f)*(e+f) = 2*d*(d+e) ∧ ¬ (d = e ∧ e = f) := by
  have hpi : (u:Int)*u + (v:Int)*v = (w:Int)*w := by
    have := congrArg (fun n : Nat => (n : Int)) hp
    simpa [Int.natCast_add, Int.natCast_mul] using this
  have hu : (u:Int) = d+e+f := by omega
  have hv : (v:Int) = d+2*e+f := by omega
  have hw : (w:Int) = 2*d+2*e+f := by omega
  rw [hu, hv, hw] at hpi
  refine ⟨by omega, by omega, by omega, (pyth_iff d e f).1 hpi, ?_⟩
  rintro ⟨rfl, rfl⟩
  exact hn ⟨w - v, by omega, by omega, by omega⟩

/-- Lemma 0: the three regions (`RegionP` is in `Defs`). -/
theorem lemma0 (d e f : Int) (hd : 1 ≤ d) (he : 1 ≤ e) (hu : 1 ≤ d + e + f)
    (hp : (e+f)*(e+f) = 2*d*(d+e)) (hn : ¬ (d = e ∧ e = f)) :
    RegionP .fat d e f ∨ RegionP .mid d e f ∨ RegionP .thin d e f := by
  -- K = (d-e) - 2(f-d) ≥ 1
  have hK : 2 * (f - d) + 1 ≤ d - e := by
    have hid : 2 * d * ((d - e) - 2 * (f - d)) = (2*d - e - f) * (2*d - e - f) := by grind
    obtain ⟨h0, hz⟩ := L0.nonneg_of_sq d _ _ hd hid
    apply Classical.byContradiction
    intro hlt
    have := hz (by omega)
    exact hn ⟨by omega, by omega⟩
  rcases Int.lt_trichotomy f d with hfd | hfd | hfd
  · -- f < d: first e + f > 0
    have hpos : 0 < e + f := by
      apply Classical.byContradiction
      intro hs
      have h1 := Int.mul_self_le_mul_self (show 0 ≤ -(e+f) by omega) (show -(e+f) ≤ d - 1 by omega)
      have h2 : (-(e+f)) * (-(e+f)) = (e+f)*(e+f) := by grind
      have h3 : 2*d*(d+e) = (d-1)*(d-1) + d*d + 2*d*e + 2*d - 1 := by grind
      have h4 := Int.mul_pos (show (0:Int) < d by omega) (show (0:Int) < e by omega)
      have h5 := L0.sq_nonneg d
      grind
    have hed : d < e := by
      apply Classical.byContradiction
      intro hle
      -- a = d - e ≥ 0, b = d - f ≥ 1, (a+b)² = 2d(a+2b)
      have hid : (2*d - e - f) * (2*d - e - f) = 2 * d * ((d - e) + 2 * (d - f)) := by grind
      have h1 := Int.mul_lt_mul_of_pos_left (show 2*d - e - f < 2 * d by omega)
        (show (0:Int) < 2*d - e - f by omega)
      have h2 := Int.mul_lt_mul_of_pos_left (show 2*d - e - f < (d - e) + 2 * (d - f) by omega)
        (show (0:Int) < 2 * d by omega)
      grind
    rcases Int.lt_trichotomy f 0 with hf0 | hf0 | hf0
    · -- thin
      right; right
      refine ⟨by omega, hed, ?_, hK⟩
      apply Classical.byContradiction
      intro hlt
      have h1 := Int.mul_self_le_mul_self (show 0 ≤ e + f by omega) (show e + f ≤ 2 * d by omega)
      have h2 := Int.mul_lt_mul_of_pos_left (show d < e by omega) (show (0:Int) < 2 * d by omega)
      grind
    · -- f = 0 is impossible
      exfalso
      subst hf0
      exact L0.not_sq_three d (e - d) hd (by grind)
    · -- mid
      right; left
      refine ⟨by omega, hfd, hed, hK, ?_⟩
      apply Classical.byContradiction
      intro hlt
      have h1 := Int.mul_self_lt_mul_self (show 0 ≤ e by omega) (show e < e + f by omega)
      have h2 := Int.mul_self_le_mul_self (show 0 ≤ 7 * d + 1 by omega)
        (show 7 * d + 1 ≤ 4 * (e - d) by omega)
      have h3 := L0.sq_nonneg d
      grind
  · -- f = d: then e = d, excluded
    exfalso
    subst f
    -- 2d(x) = -x² with x = e - d ≤ -1, so x = -2d, e = -d
    have hid : 2 * d * (d - e) = (d - e) * (d - e) := by grind
    have hx : 2 * d = d - e := by
      have h0 : (d - e) ≠ 0 := by omega
      have : (d - e) * (2 * d) = (d - e) * (d - e) := by rw [← hid]; grind
      exact Int.eq_of_mul_eq_mul_left h0 this
    omega
  · -- f > d: fat
    left
    refine ⟨by omega, hfd, ?_, hK⟩
    apply Classical.byContradiction
    intro hlt
    have h1 := Int.mul_self_le_mul_self (show 0 ≤ 2 * e + 3 * d + 1 by omega)
      (show 2 * e + 3 * d + 1 ≤ 2 * (e + f) by omega)
    have h2 : (2*e+3*d+1)*(2*e+3*d+1) = 8*d*(d+e) + (2*e+d)*(2*e+d) + 4*e + 6*d + 1 := by grind
    have h3 := L0.sq_nonneg (2*e+d)
    grind

/-- Thin adj has no normal form: the cell (v, u) has no available slot. -/
theorem thin_adj (c : Case) (p : Params) (hk : c.kind = .adj) (hf : p.f ≤ -1) (hd : 1 ≤ p.d)
    (he : 1 ≤ p.e) (hu : 1 ≤ p.u) (N : NF c p) : False := by
  have hW : InW p p.v p.u := by
    simp only [InW, Params.u, Params.v, Params.w] at *; omega
  have hA := N.avail _ _ hW
  generalize N.σ p.v p.u = k at hA
  obtain ⟨hb, -⟩ := hA
  rw [hk] at hb
  match k with
  | 0 | 1 | 2 | 3 => simp only [box, Box.mem, Params.u, Params.v, Params.w, Params.a] at hb; omega
