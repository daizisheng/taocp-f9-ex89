import Ex89.T22.Defs

/-!
# Thin region, `diag`, `o2 ∈ {0, 4}`: the chain argument (Lemmas TF-T, TF-F)

See `PROOF.md`, section 3.7. Notation: `g_0(x,y) = (x+e1, y+f1)`;
for `o2 = 0`, `g_2(x,y) = (x-d-e2, y-d-f2)`; for `o2 = 4`, `g_2(x,y) = (y-d-f2, x-d-e2)`.

Structure of the file:
* arithmetic: partial sums `psum`, crossing index, the staircase lemma `stair`;
* `chain_principle`: a chain of cells outside the U boxes along which slot `k` must propagate;
* NF facts (corners, bounds `≤ u-d`, the corner conditions of the two-rectangle covering);
* the cases (TF-T: A and its transpose / 180° rotation / both, B and its transpose;
  TF-F: A and its three symmetric versions, strip case and its transpose).
  Symmetric versions are proved directly (the chain is written in rotated/transposed
  coordinates), not via a transformation of `NF`.
-/
namespace Ex89.T22
namespace TF

/-! ## Arithmetic -/

/-- Partial sums `psum f j = f 0 + … + f (j-1)`. -/
def psum (f : Nat → Int) : Nat → Int
  | 0 => 0
  | j + 1 => psum f j + f j

@[simp] theorem psum_zero (f : Nat → Int) : psum f 0 = 0 := rfl
@[simp] theorem psum_succ (f : Nat → Int) (j : Nat) : psum f (j + 1) = psum f j + f j := rfl

theorem psum_mono (f : Nat → Int) (hf : ∀ j, 0 ≤ f j) {i j : Nat} (h : i ≤ j) :
    psum f i ≤ psum f j := by
  induction j with
  | zero => have : i = 0 := by omega
            subst this; omega
  | succ j ih =>
    rcases Nat.lt_or_ge i (j + 1) with h' | h'
    · have := ih (by omega); have := hf j; simp; omega
    · have : i = j + 1 := by omega
      subst this; omega

theorem psum_ge (f : Nat → Int) (hf : ∀ j, 1 ≤ f j) (j : Nat) : (j : Int) ≤ psum f j := by
  induction j with
  | zero => simp
  | succ j ih => have := hf j; simp; omega

theorem psum_nonneg (f : Nat → Int) (hf : ∀ j, 0 ≤ f j) (j : Nat) : 0 ≤ psum f j := by
  have := psum_mono f hf (Nat.zero_le j); simpa using this

/-- An integer sequence increasing by at least one per step crosses every level above `g 0`. -/
theorem exists_cross (g : Nat → Int) (hg : ∀ j, g j + 1 ≤ g (j + 1)) (u : Int) (h0 : g 0 < u) :
    ∃ k, g k < u ∧ u ≤ g (k + 1) := by
  apply Classical.byContradiction
  intro H
  have hall : ∀ k, g k < u := by
    intro k
    induction k with
    | zero => exact h0
    | succ k ih =>
      by_cases h : u ≤ g (k + 1)
      · exact absurd ⟨k, ih, h⟩ H
      · omega
  have hge : ∀ k : Nat, g 0 + k ≤ g k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => have := hg k; push_cast; omega
  have h1 := hall (u - g 0).toNat
  have h2 := hge (u - g 0).toNat
  omega

/-- **Staircase lemma.** Two increasing sequences `x0 + Σ sx`, `y0 + Σ sy` with `Σ sy ≤ Σ sx`;
for a suitable start `y0 ∈ [0, u)`, at every index both are `< u` or both are `≥ u`. -/
theorem stair (sx sy : Nat → Int) (hx : ∀ j, 1 ≤ sx j) (hy : ∀ j, 1 ≤ sy j)
    (hxy : ∀ j, psum sy j ≤ psum sx j) (u x0 : Int) (hx0 : 0 ≤ x0) (hxu : x0 < u) :
    ∃ y0, 0 ≤ y0 ∧ y0 < u ∧ ∀ j, (x0 + psum sx j < u ∧ y0 + psum sy j < u) ∨
      (u ≤ x0 + psum sx j ∧ u ≤ y0 + psum sy j) := by
  obtain ⟨k, hk1, hk2⟩ := exists_cross (fun j => x0 + psum sx j)
    (fun j => by have := hx j; simp; omega) u (by simp; omega)
  have hyk1 := hy k
  have hx' : ∀ j, 0 ≤ sx j := fun j => by have := hx j; omega
  have hy' : ∀ j, 0 ≤ sy j := fun j => by have := hy j; omega
  have hyk := psum_ge sy hy (k + 1)
  have hxyk := hxy k
  have hsyk := psum_succ sy k
  have hm1 := Int.le_max_left 0 (u - psum sy (k + 1))
  have hm2 := Int.le_max_right 0 (u - psum sy (k + 1))
  have hm3 : max 0 (u - psum sy (k + 1)) = 0 ∨ max 0 (u - psum sy (k + 1)) = u - psum sy (k + 1) := by
    omega
  generalize max 0 (u - psum sy (k + 1)) = y0 at hm1 hm2 hm3
  refine ⟨y0, by omega, by omega, fun j => ?_⟩
  rcases Nat.lt_or_ge k j with h | h
  · have h1 := psum_mono sx hx' (show k + 1 ≤ j by omega)
    have h2 := psum_mono sy hy' (show k + 1 ≤ j by omega)
    right; omega
  · have h1 := psum_mono sx hx' h
    have h2 := psum_mono sy hy' h
    left; omega

/-! ## Unfolding `Avail` -/

/-- Cell outside both U boxes of `diag`. -/
def OutU (p : Params) (x y : Int) : Prop := ¬ (x < p.u ∧ p.a ≤ y) ∧ ¬ (p.a ≤ x ∧ y < p.u)

theorem avail0 (c : Case) (p : Params) (hk : c.kind = .diag) (x y : Int) :
    Avail c p 0 x y ↔ (0 ≤ x ∧ x < p.v ∧ 0 ≤ y ∧ y < p.v) ∧
      0 ≤ x + p.tx 0 ∧ x + p.tx 0 < p.v ∧ 0 ≤ y + p.ty 0 ∧ y + p.ty 0 < p.v := by
  simp [Avail, hk, box, Box.mem, srcX, srcY, Case.ori, oriM, Params.side]

theorem avail2_id (c : Case) (p : Params) (hk : c.kind = .diag) (ho : c.o2 = 0) (x y : Int) :
    Avail c p 2 x y ↔ (p.d ≤ x ∧ x < p.w ∧ p.d ≤ y ∧ y < p.w) ∧
      0 ≤ x + p.tx 2 ∧ x + p.tx 2 < p.v ∧ 0 ≤ y + p.ty 2 ∧ y + p.ty 2 < p.v := by
  simp [Avail, hk, box, Box.mem, srcX, srcY, Case.ori, oriM, Params.side, ho]

theorem avail2_sw (c : Case) (p : Params) (hk : c.kind = .diag) (ho : c.o2 = 4) (x y : Int) :
    Avail c p 2 x y ↔ (p.d ≤ x ∧ x < p.w ∧ p.d ≤ y ∧ y < p.w) ∧
      0 ≤ y + p.tx 2 ∧ y + p.tx 2 < p.v ∧ 0 ≤ x + p.ty 2 ∧ x + p.ty 2 < p.v := by
  simp [Avail, hk, box, Box.mem, srcX, srcY, Case.ori, oriM, Params.side, ho]

theorem src0 (c : Case) (p : Params) (x y : Int) :
    srcX c p 0 x y = x + p.tx 0 ∧ srcY c p 0 x y = y + p.ty 0 := by
  simp [srcX, srcY, Case.ori, oriM]

theorem src2_id (c : Case) (p : Params) (ho : c.o2 = 0) (x y : Int) :
    srcX c p 2 x y = x + p.tx 2 ∧ srcY c p 2 x y = y + p.ty 2 := by
  simp [srcX, srcY, Case.ori, oriM, ho]

theorem src2_sw (c : Case) (p : Params) (ho : c.o2 = 4) (x y : Int) :
    srcX c p 2 x y = y + p.tx 2 ∧ srcY c p 2 x y = x + p.ty 2 := by
  simp [srcX, srcY, Case.ori, oriM, ho]

theorem fin4_cases (k : Fin 4) : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by
  match k with
  | 0 => simp
  | 1 => simp
  | 2 => simp
  | 3 => simp

/-- Outside the U boxes only the V slots `0, 2` are possible. -/
theorem slot_even (c : Case) (p : Params) (hk : c.kind = .diag) (N : NF c p) (x y : Int)
    (hW : InW p x y) (hT : OutU p x y) : N.σ x y = 0 ∨ N.σ x y = 2 := by
  have hav := N.avail x y hW
  rcases fin4_cases (N.σ x y) with h | h | h | h
  · exact Or.inl h
  · rw [h] at hav
    simp [Avail, hk, box, Box.mem] at hav
    simp [OutU] at hT; omega
  · exact Or.inr h
  · rw [h] at hav
    simp [Avail, hk, box, Box.mem] at hav
    simp [OutU] at hT; omega

/-! ## The chain principle -/

/-- **Chain principle.** `{k, k'} = {0, 2}`. Cells `q j` outside the U boxes with
`g_{k'}(q (j+1)) = g_k(q j)`; slot `k'` is not available at `q 0`; while slot `k` is available
at `q j`, `q (j+1)` stays in `W`; slot `k` is not available at some `q n`. Then no normal form. -/
theorem chain_principle (c : Case) (p : Params) (hk : c.kind = .diag) (N : NF c p)
    (k k' : Fin 4) (hkk : (k = 0 ∧ k' = 2) ∨ (k = 2 ∧ k' = 0)) (q : Nat → Int × Int)
    (h0 : InW p (q 0).1 (q 0).2) (hT : ∀ j, OutU p (q j).1 (q j).2)
    (h0' : ¬ Avail c p k' (q 0).1 (q 0).2)
    (hrel : ∀ j, srcX c p k' (q (j+1)).1 (q (j+1)).2 = srcX c p k (q j).1 (q j).2 ∧
                 srcY c p k' (q (j+1)).1 (q (j+1)).2 = srcY c p k (q j).1 (q j).2)
    (hstep : ∀ j, InW p (q j).1 (q j).2 → Avail c p k (q j).1 (q j).2 →
                 InW p (q (j+1)).1 (q (j+1)).2)
    (hend : ∃ n, ¬ Avail c p k (q n).1 (q n).2) : False := by
  have hpar : k'.val % 2 = k.val % 2 := by rcases hkk with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> subst h1 h2 <;> rfl
  have hne : k ≠ k' := by rcases hkk with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> subst h1 h2 <;> decide
  -- the only even slots are `k` and `k'`
  have hev : ∀ j, InW p (q j).1 (q j).2 → N.σ (q j).1 (q j).2 = k ∨ N.σ (q j).1 (q j).2 = k' := by
    intro j hW
    rcases slot_even c p hk N _ _ hW (hT j) with h | h <;>
      rcases hkk with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> subst h1 h2 <;> simp [h]
  have key : ∀ j, InW p (q j).1 (q j).2 ∧ N.σ (q j).1 (q j).2 = k := by
    intro j
    induction j with
    | zero =>
      refine ⟨h0, ?_⟩
      rcases hev 0 h0 with h | h
      · exact h
      · exact absurd (h ▸ N.avail _ _ h0) h0'
    | succ j ih =>
      obtain ⟨hW, hσ⟩ := ih
      have hav : Avail c p k (q j).1 (q j).2 := hσ ▸ N.avail _ _ hW
      have hW' := hstep j hW hav
      refine ⟨hW', ?_⟩
      rcases hev (j+1) hW' with h | h
      · exact h
      · exfalso
        have hi := N.inj _ _ _ _ hW' hW (by rw [h, hσ]; exact hpar)
          (by rw [h, hσ]; exact (hrel j).1) (by rw [h, hσ]; exact (hrel j).2)
        have : q (j+1) = q j := Prod.ext hi.1 hi.2
        rw [this, hσ] at h
        exact hne h
  obtain ⟨n, hn⟩ := hend
  obtain ⟨hW, hσ⟩ := key n
  exact hn (hσ ▸ N.avail _ _ hW)

/-! ## Facts from the normal form -/

theorem dims (p : Params) : p.u = p.d + p.e + p.f ∧ p.v = p.d + 2 * p.e + p.f ∧
    p.w = 2 * p.d + 2 * p.e + p.f ∧ p.a = p.d + p.e := ⟨rfl, rfl, rfl, rfl⟩

/-- A cell outside the U boxes and outside the box of slot 2 has slot 0. -/
theorem forced0 (c : Case) (p : Params) (hk : c.kind = .diag) (N : NF c p) (x y : Int)
    (hW : InW p x y) (hT : OutU p x y) (h2 : x < p.d ∨ y < p.d) : Avail c p 0 x y := by
  have hav := N.avail x y hW
  rcases slot_even c p hk N x y hW hT with h | h <;> rw [h] at hav
  · exact hav
  · simp [Avail, hk, box, Box.mem] at hav; omega

/-- A cell outside the U boxes and outside the box of slot 0 has slot 2. -/
theorem forced2 (c : Case) (p : Params) (hk : c.kind = .diag) (N : NF c p) (x y : Int)
    (hW : InW p x y) (hT : OutU p x y) (h0 : p.v ≤ x ∨ p.v ≤ y) : Avail c p 2 x y := by
  have hav := N.avail x y hW
  rcases slot_even c p hk N x y hW hT with h | h <;> rw [h] at hav
  · simp [Avail, hk, box, Box.mem] at hav; omega
  · exact hav

/-- Surjectivity onto the `v × v` square, split by slot. -/
theorem surjV (c : Case) (p : Params) (N : NF c p) (X Y : Int)
    (h1 : 0 ≤ X) (h2 : X < p.v) (h3 : 0 ≤ Y) (h4 : Y < p.v) :
    ∃ x y, InW p x y ∧ ((N.σ x y = 0 ∧ x + p.tx 0 = X ∧ y + p.ty 0 = Y) ∨
      (N.σ x y = 2 ∧ srcX c p 2 x y = X ∧ srcY c p 2 x y = Y)) := by
  obtain ⟨x, y, hW, hpar, hX, hY⟩ := N.surj 0 X Y h1 (by simpa [Params.side] using h2) h3
    (by simpa [Params.side] using h4)
  refine ⟨x, y, hW, ?_⟩
  rcases fin4_cases (N.σ x y) with h | h | h | h <;> rw [h] at hpar hX hY
  · left; exact ⟨h, by simpa [srcX, Case.ori, oriM] using hX, by simpa [srcY, Case.ori, oriM] using hY⟩
  · exact absurd hpar (by decide)
  · right; exact ⟨h, hX, hY⟩
  · exact absurd hpar (by decide)

/-- Bounds on `g_0 = (x + e1, y + f1)`: `0 ≤ e1, f1 ≤ u - d`. -/
theorem bounds0 (c : Case) (p : Params) (hk : c.kind = .diag)
    (hr : RegionP .thin p.d p.e p.f) (hd : 1 ≤ p.d) (N : NF c p) :
    0 ≤ p.tx 0 ∧ p.tx 0 ≤ p.u - p.d ∧ 0 ≤ p.ty 0 ∧ p.ty 0 ≤ p.u - p.d := by
  have hD := dims p
  simp only [RegionP] at hr
  have h00 := forced0 c p hk N 0 0 (by simp [InW]; omega) (by simp [OutU]; omega) (by omega)
  have h10 := forced0 c p hk N (p.a - 1) 0 (by simp [InW]; omega) (by simp [OutU]; omega) (by omega)
  have h01 := forced0 c p hk N 0 (p.a - 1) (by simp [InW]; omega) (by simp [OutU]; omega) (by omega)
  rw [avail0 c p hk] at h00 h10 h01
  omega

/-- `o2 = 0`: `g_2 = (x - d - e2, y - d - f2)` with `0 ≤ e2, f2 ≤ u - d`. -/
theorem bounds2_id (c : Case) (p : Params) (hk : c.kind = .diag) (ho : c.o2 = 0)
    (hr : RegionP .thin p.d p.e p.f) (hd : 1 ≤ p.d) (N : NF c p) :
    -p.u ≤ p.tx 2 ∧ p.tx 2 ≤ -p.d ∧ -p.u ≤ p.ty 2 ∧ p.ty 2 ≤ -p.d := by
  have hD := dims p
  simp only [RegionP] at hr
  have h1 := forced2 c p hk N (p.w - 1) (p.w - 1) (by simp [InW]; omega) (by simp [OutU]; omega) (by omega)
  have h2 := forced2 c p hk N p.u (p.w - 1) (by simp [InW]; omega) (by simp [OutU]; omega) (by omega)
  have h3 := forced2 c p hk N (p.w - 1) p.u (by simp [InW]; omega) (by simp [OutU]; omega) (by omega)
  rw [avail2_id c p hk ho] at h1 h2 h3
  omega

/-- `o2 = 4`: `g_2 = (y - d - f2, x - d - e2)` with `0 ≤ e2, f2 ≤ u - d`. -/
theorem bounds2_sw (c : Case) (p : Params) (hk : c.kind = .diag) (ho : c.o2 = 4)
    (hr : RegionP .thin p.d p.e p.f) (hd : 1 ≤ p.d) (N : NF c p) :
    -p.u ≤ p.tx 2 ∧ p.tx 2 ≤ -p.d ∧ -p.u ≤ p.ty 2 ∧ p.ty 2 ≤ -p.d := by
  have hD := dims p
  simp only [RegionP] at hr
  have h1 := forced2 c p hk N (p.w - 1) (p.w - 1) (by simp [InW]; omega) (by simp [OutU]; omega) (by omega)
  have h2 := forced2 c p hk N p.u (p.w - 1) (by simp [InW]; omega) (by simp [OutU]; omega) (by omega)
  have h3 := forced2 c p hk N (p.w - 1) p.u (by simp [InW]; omega) (by simp [OutU]; omega) (by omega)
  rw [avail2_sw c p hk ho] at h1 h2 h3
  omega

/-- Corner conditions of the two-rectangle covering, `o2 = 0`:
`e1 > 0 → f2 = 0` and `f1 > 0 → e2 = 0`. -/
theorem cover_id (c : Case) (p : Params) (hk : c.kind = .diag) (ho : c.o2 = 0)
    (hr : RegionP .thin p.d p.e p.f) (hd : 1 ≤ p.d) (N : NF c p) :
    (0 < p.tx 0 → p.ty 2 = -p.d) ∧ (0 < p.ty 0 → p.tx 2 = -p.d) := by
  have hD := dims p
  have hb := bounds2_id c p hk ho hr hd N
  simp only [RegionP] at hr
  constructor
  · intro he1
    obtain ⟨x, y, hW, h⟩ := surjV c p N 0 (p.v - 1) (by omega) (by omega) (by omega) (by omega)
    obtain ⟨h2x, h2y⟩ := src2_id c p ho x y
    simp only [InW] at hW
    rcases h with ⟨_, h1, _⟩ | ⟨_, h1, h3⟩ <;> omega
  · intro hf1
    obtain ⟨x, y, hW, h⟩ := surjV c p N (p.v - 1) 0 (by omega) (by omega) (by omega) (by omega)
    obtain ⟨h2x, h2y⟩ := src2_id c p ho x y
    simp only [InW] at hW
    rcases h with ⟨_, _, h1⟩ | ⟨_, h1, h3⟩ <;> omega

/-- Corner conditions of the two-rectangle covering, `o2 = 4`
(`t2 = (-d-f2, -d-e2)`): `e1 > 0 → e2 = 0` and `f1 > 0 → f2 = 0`. -/
theorem cover_sw (c : Case) (p : Params) (hk : c.kind = .diag) (ho : c.o2 = 4)
    (hr : RegionP .thin p.d p.e p.f) (hd : 1 ≤ p.d) (N : NF c p) :
    (0 < p.tx 0 → p.ty 2 = -p.d) ∧ (0 < p.ty 0 → p.tx 2 = -p.d) := by
  have hD := dims p
  have hb := bounds2_sw c p hk ho hr hd N
  simp only [RegionP] at hr
  constructor
  · intro he1
    obtain ⟨x, y, hW, h⟩ := surjV c p N 0 (p.v - 1) (by omega) (by omega) (by omega) (by omega)
    obtain ⟨h2x, h2y⟩ := src2_sw c p ho x y
    simp only [InW] at hW
    rcases h with ⟨_, h1, _⟩ | ⟨_, h1, h3⟩ <;> omega
  · intro hf1
    obtain ⟨x, y, hW, h⟩ := surjV c p N (p.v - 1) 0 (by omega) (by omega) (by omega) (by omega)
    obtain ⟨h2x, h2y⟩ := src2_sw c p ho x y
    simp only [InW] at hW
    rcases h with ⟨_, _, h1⟩ | ⟨_, h1, h3⟩ <;> omega

theorem psum_le (f g : Nat → Int) (h : ∀ j, f j ≤ g j) (j : Nat) : psum f j ≤ psum g j := by
  induction j with
  | zero => simp
  | succ j ih => have := h j; simp; omega

/-! ## TF-T (o2 = 0, h a translation) -/

/-- TF-T, case A: `e2 = f2 = 0`, `f1 ≤ e1`. Chain `q_j = (j s, y0 + j t)` along slot 0. -/
theorem caseTA (c : Case) (p : Params) (hk : c.kind = .diag) (ho : c.o2 = 0)
    (hr : RegionP .thin p.d p.e p.f) (hd : 1 ≤ p.d) (N : NF c p)
    (he2 : p.tx 2 = -p.d) (hf2 : p.ty 2 = -p.d) (hfe : p.ty 0 ≤ p.tx 0) : False := by
  have hD := dims p
  have hb := bounds0 c p hk hr hd N
  simp only [RegionP] at hr
  obtain ⟨y0, hy0, hy0u, hst⟩ := stair (fun _ => p.d + p.tx 0) (fun _ => p.d + p.ty 0)
    (fun _ => by omega) (fun _ => by omega) (psum_le _ _ (fun _ => by omega)) p.u 0
    (Int.le_refl 0) (by omega)
  have hnn := psum_nonneg (fun _ => p.d + p.ty 0) (fun _ => by omega)
  have hge := psum_ge (fun _ => p.d + p.tx 0) (fun _ => by omega)
  apply chain_principle c p hk N 0 2 (Or.inl ⟨rfl, rfl⟩)
    (fun j => (0 + psum (fun _ => p.d + p.tx 0) j, y0 + psum (fun _ => p.d + p.ty 0) j))
  · simp [InW]; omega
  · intro j; have := hst j; have := hnn j; simp only [OutU]; omega
  · rw [avail2_id c p hk ho]; simp; omega
  · intro j
    obtain ⟨a1, a2⟩ := src0 c p
      (0 + psum (fun _ => p.d + p.tx 0) j) (y0 + psum (fun _ => p.d + p.ty 0) j)
    obtain ⟨b1, b2⟩ := src2_id c p ho
      (0 + psum (fun _ => p.d + p.tx 0) (j+1)) (y0 + psum (fun _ => p.d + p.ty 0) (j+1))
    simp only [psum_succ] at b1 b2 ⊢
    rw [a1, a2, b1, b2]; omega
  · intro j hW hav
    rw [avail0 c p hk] at hav
    simp only [InW, psum_succ] at hW hav ⊢
    omega
  · refine ⟨p.v.toNat, ?_⟩
    rw [avail0 c p hk]; have := hge p.v.toNat; simp only; omega

/-- TF-T, case A transposed: `e2 = f2 = 0`, `e1 ≤ f1`. Chain `q_j = (y0 + j s, j t)`. -/
theorem caseTAT (c : Case) (p : Params) (hk : c.kind = .diag) (ho : c.o2 = 0)
    (hr : RegionP .thin p.d p.e p.f) (hd : 1 ≤ p.d) (N : NF c p)
    (he2 : p.tx 2 = -p.d) (hf2 : p.ty 2 = -p.d) (hfe : p.tx 0 ≤ p.ty 0) : False := by
  have hD := dims p
  have hb := bounds0 c p hk hr hd N
  simp only [RegionP] at hr
  obtain ⟨y0, hy0, hy0u, hst⟩ := stair (fun _ => p.d + p.ty 0) (fun _ => p.d + p.tx 0)
    (fun _ => by omega) (fun _ => by omega) (psum_le _ _ (fun _ => by omega)) p.u 0
    (Int.le_refl 0) (by omega)
  have hnn := psum_nonneg (fun _ => p.d + p.tx 0) (fun _ => by omega)
  have hge := psum_ge (fun _ => p.d + p.ty 0) (fun _ => by omega)
  apply chain_principle c p hk N 0 2 (Or.inl ⟨rfl, rfl⟩)
    (fun j => (y0 + psum (fun _ => p.d + p.tx 0) j, 0 + psum (fun _ => p.d + p.ty 0) j))
  · simp [InW]; omega
  · intro j; have := hst j; have := hnn j; simp only [OutU]; omega
  · rw [avail2_id c p hk ho]; simp; omega
  · intro j
    obtain ⟨a1, a2⟩ := src0 c p
      (y0 + psum (fun _ => p.d + p.tx 0) j) (0 + psum (fun _ => p.d + p.ty 0) j)
    obtain ⟨b1, b2⟩ := src2_id c p ho
      (y0 + psum (fun _ => p.d + p.tx 0) (j+1)) (0 + psum (fun _ => p.d + p.ty 0) (j+1))
    simp only [psum_succ] at b1 b2 ⊢
    rw [a1, a2, b1, b2]; omega
  · intro j hW hav
    rw [avail0 c p hk] at hav
    simp only [InW, psum_succ] at hW hav ⊢
    omega
  · refine ⟨p.v.toNat, ?_⟩
    rw [avail0 c p hk]; have := hge p.v.toNat; simp only; omega

/-- TF-T, case A rotated by 180°: `e1 = f1 = 0`, `f2 ≤ e2`. Chain
`q_j = (w-1 - j s, w-1 - y0 - j t)`, `s = d+e2`, `t = d+f2`, along slot 2. -/
theorem caseTAR (c : Case) (p : Params) (hk : c.kind = .diag) (ho : c.o2 = 0)
    (hr : RegionP .thin p.d p.e p.f) (hd : 1 ≤ p.d) (N : NF c p)
    (he1 : p.tx 0 = 0) (hf1 : p.ty 0 = 0) (hfe : p.tx 2 ≤ p.ty 2) : False := by
  have hD := dims p
  have hb := bounds2_id c p hk ho hr hd N
  simp only [RegionP] at hr
  obtain ⟨y0, hy0, hy0u, hst⟩ := stair (fun _ => -p.tx 2) (fun _ => -p.ty 2)
    (fun _ => by omega) (fun _ => by omega) (psum_le _ _ (fun _ => by omega)) p.u 0
    (Int.le_refl 0) (by omega)
  have hnn := psum_nonneg (fun _ => -p.ty 2) (fun _ => by omega)
  have hge := psum_ge (fun _ => -p.tx 2) (fun _ => by omega)
  apply chain_principle c p hk N 2 0 (Or.inr ⟨rfl, rfl⟩)
    (fun j => (p.w - 1 - (0 + psum (fun _ => -p.tx 2) j),
               p.w - 1 - (y0 + psum (fun _ => -p.ty 2) j)))
  · simp [InW]; omega
  · intro j; have := hst j; have := hnn j; simp only [OutU]; omega
  · rw [avail0 c p hk]; simp; omega
  · intro j
    obtain ⟨a1, a2⟩ := src2_id c p ho
      (p.w - 1 - (0 + psum (fun _ => -p.tx 2) j)) (p.w - 1 - (y0 + psum (fun _ => -p.ty 2) j))
    obtain ⟨b1, b2⟩ := src0 c p
      (p.w - 1 - (0 + psum (fun _ => -p.tx 2) (j+1)))
      (p.w - 1 - (y0 + psum (fun _ => -p.ty 2) (j+1)))
    simp only [psum_succ] at b1 b2 ⊢
    rw [a1, a2, b1, b2]; omega
  · intro j hW hav
    rw [avail2_id c p hk ho] at hav
    simp only [InW, psum_succ] at hW hav ⊢
    omega
  · refine ⟨p.w.toNat, ?_⟩
    rw [avail2_id c p hk ho]; have := hge p.w.toNat; simp only; omega

/-- TF-T, case A rotated and transposed: `e1 = f1 = 0`, `e2 ≤ f2`. -/
theorem caseTART (c : Case) (p : Params) (hk : c.kind = .diag) (ho : c.o2 = 0)
    (hr : RegionP .thin p.d p.e p.f) (hd : 1 ≤ p.d) (N : NF c p)
    (he1 : p.tx 0 = 0) (hf1 : p.ty 0 = 0) (hfe : p.ty 2 ≤ p.tx 2) : False := by
  have hD := dims p
  have hb := bounds2_id c p hk ho hr hd N
  simp only [RegionP] at hr
  obtain ⟨y0, hy0, hy0u, hst⟩ := stair (fun _ => -p.ty 2) (fun _ => -p.tx 2)
    (fun _ => by omega) (fun _ => by omega) (psum_le _ _ (fun _ => by omega)) p.u 0
    (Int.le_refl 0) (by omega)
  have hnn := psum_nonneg (fun _ => -p.tx 2) (fun _ => by omega)
  have hge := psum_ge (fun _ => -p.ty 2) (fun _ => by omega)
  apply chain_principle c p hk N 2 0 (Or.inr ⟨rfl, rfl⟩)
    (fun j => (p.w - 1 - (y0 + psum (fun _ => -p.tx 2) j),
               p.w - 1 - (0 + psum (fun _ => -p.ty 2) j)))
  · simp [InW]; omega
  · intro j; have := hst j; have := hnn j; simp only [OutU]; omega
  · rw [avail0 c p hk]; simp; omega
  · intro j
    obtain ⟨a1, a2⟩ := src2_id c p ho
      (p.w - 1 - (y0 + psum (fun _ => -p.tx 2) j)) (p.w - 1 - (0 + psum (fun _ => -p.ty 2) j))
    obtain ⟨b1, b2⟩ := src0 c p
      (p.w - 1 - (y0 + psum (fun _ => -p.tx 2) (j+1)))
      (p.w - 1 - (0 + psum (fun _ => -p.ty 2) (j+1)))
    simp only [psum_succ] at b1 b2 ⊢
    rw [a1, a2, b1, b2]; omega
  · intro j hW hav
    rw [avail2_id c p hk ho] at hav
    simp only [InW, psum_succ] at hW hav ⊢
    omega
  · refine ⟨p.w.toNat, ?_⟩
    rw [avail2_id c p hk ho]; have := hge p.w.toNat; simp only; omega

/-- Choice of the start `x0` in case B: a start `< D` such that the progression
`x0 + j s` never lands in `[L - E, L)`. -/
theorem choose_x0 (s L D E : Int) (hE : 0 ≤ E) (hs : E < s) (hDE : E < D) (hLE : E < L)
    (hLs : L < D → L ≤ s) :
    ∃ x0, 0 ≤ x0 ∧ x0 < D ∧ ∀ j, x0 + psum (fun _ => s) j < L →
      x0 + psum (fun _ => s) j < L - E := by
  have hs' : ∀ j, 0 ≤ (fun _ => s : Nat → Int) j := fun _ => by simp only; omega
  by_cases hb : L < D
  · refine ⟨0, by omega, by omega, fun j hj => ?_⟩
    cases j with
    | zero => simp; omega
    | succ j =>
      have := psum_nonneg _ hs' j
      simp at hj ⊢; have := hLs hb; omega
  · obtain ⟨k, hk1, hk2⟩ := exists_cross (fun j => psum (fun _ => s) j)
      (fun j => by simp; omega) (L - D + 1) (by simp; omega)
    simp only [psum_succ] at hk2
    have hm1 := Int.le_max_left 0 (L - psum (fun _ => s) (k + 1))
    have hm2 := Int.le_max_right 0 (L - psum (fun _ => s) (k + 1))
    have hm3 : max 0 (L - psum (fun _ => s) (k + 1)) = 0 ∨
        max 0 (L - psum (fun _ => s) (k + 1)) = L - psum (fun _ => s) (k + 1) := by omega
    simp only [psum_succ] at hm1 hm2 hm3
    generalize max 0 (L - (psum (fun _ => s) k + s)) = x0 at hm1 hm2 hm3
    refine ⟨x0, hm1, by omega, fun j hj => ?_⟩
    rcases Nat.lt_or_ge k j with h | h
    · have := psum_mono _ hs' (show k + 1 ≤ j by omega)
      simp only [psum_succ] at this; omega
    · have := psum_mono _ hs' h
      omega

/-- TF-T, case B: `f1 = f2 = 0`, `e1, e2 ≥ 1`. Chain `q_j = (x0 + j s, y0 + j d)`,
`s = d + e1 + e2`, along slot 0. -/
theorem caseTB (c : Case) (p : Params) (hk : c.kind = .diag) (ho : c.o2 = 0)
    (hr : RegionP .thin p.d p.e p.f) (hd : 1 ≤ p.d) (N : NF c p)
    (hf1 : p.ty 0 = 0) (hf2 : p.ty 2 = -p.d) (he1 : 1 ≤ p.tx 0) (he2 : p.tx 2 ≤ -p.d - 1) :
    False := by
  have hD := dims p
  have hb := bounds0 c p hk hr hd N
  have hb2 := bounds2_id c p hk ho hr hd N
  simp only [RegionP] at hr
  obtain ⟨x0, hx0, hx0D, hx0L⟩ := choose_x0 (p.tx 0 - p.tx 2) (p.v - p.tx 0) (-p.tx 2)
    (-p.tx 2 - p.d) (by omega) (by omega) (by omega) (by omega) (by omega)
  obtain ⟨y0, hy0, hy0u, hst⟩ := stair (fun _ => p.tx 0 - p.tx 2) (fun _ => p.d)
    (fun _ => by omega) (fun _ => by omega) (psum_le _ _ (fun _ => by omega)) p.u x0
    hx0 (by omega)
  have hnn := psum_nonneg (fun _ => p.d) (fun _ => by omega)
  have hnn' := psum_nonneg (fun _ => p.tx 0 - p.tx 2) (fun _ => by omega)
  have hge := psum_ge (fun _ => p.tx 0 - p.tx 2) (fun _ => by omega)
  apply chain_principle c p hk N 0 2 (Or.inl ⟨rfl, rfl⟩)
    (fun j => (x0 + psum (fun _ => p.tx 0 - p.tx 2) j, y0 + psum (fun _ => p.d) j))
  · simp [InW]; omega
  · intro j; have := hst j; have := hnn j; simp only [OutU]; omega
  · rw [avail2_id c p hk ho]; simp; omega
  · intro j
    obtain ⟨a1, a2⟩ := src0 c p
      (x0 + psum (fun _ => p.tx 0 - p.tx 2) j) (y0 + psum (fun _ => p.d) j)
    obtain ⟨b1, b2⟩ := src2_id c p ho
      (x0 + psum (fun _ => p.tx 0 - p.tx 2) (j+1)) (y0 + psum (fun _ => p.d) (j+1))
    simp only [psum_succ] at b1 b2 ⊢
    rw [a1, a2, b1, b2]; omega
  · intro j hW hav
    rw [avail0 c p hk] at hav
    have := hx0L j
    have := hnn' j
    simp only [InW, psum_succ] at hW hav ⊢
    omega
  · refine ⟨p.v.toNat, ?_⟩
    rw [avail0 c p hk]; have := hge p.v.toNat; simp only; omega

/-- TF-T, case B transposed: `e1 = e2 = 0`, `f1, f2 ≥ 1`. -/
theorem caseTBT (c : Case) (p : Params) (hk : c.kind = .diag) (ho : c.o2 = 0)
    (hr : RegionP .thin p.d p.e p.f) (hd : 1 ≤ p.d) (N : NF c p)
    (he1 : p.tx 0 = 0) (he2 : p.tx 2 = -p.d) (hf1 : 1 ≤ p.ty 0) (hf2 : p.ty 2 ≤ -p.d - 1) :
    False := by
  have hD := dims p
  have hb := bounds0 c p hk hr hd N
  have hb2 := bounds2_id c p hk ho hr hd N
  simp only [RegionP] at hr
  obtain ⟨x0, hx0, hx0D, hx0L⟩ := choose_x0 (p.ty 0 - p.ty 2) (p.v - p.ty 0) (-p.ty 2)
    (-p.ty 2 - p.d) (by omega) (by omega) (by omega) (by omega) (by omega)
  obtain ⟨y0, hy0, hy0u, hst⟩ := stair (fun _ => p.ty 0 - p.ty 2) (fun _ => p.d)
    (fun _ => by omega) (fun _ => by omega) (psum_le _ _ (fun _ => by omega)) p.u x0
    hx0 (by omega)
  have hnn := psum_nonneg (fun _ => p.d) (fun _ => by omega)
  have hnn' := psum_nonneg (fun _ => p.ty 0 - p.ty 2) (fun _ => by omega)
  have hge := psum_ge (fun _ => p.ty 0 - p.ty 2) (fun _ => by omega)
  apply chain_principle c p hk N 0 2 (Or.inl ⟨rfl, rfl⟩)
    (fun j => (y0 + psum (fun _ => p.d) j, x0 + psum (fun _ => p.ty 0 - p.ty 2) j))
  · simp [InW]; omega
  · intro j; have := hst j; have := hnn j; simp only [OutU]; omega
  · rw [avail2_id c p hk ho]; simp; omega
  · intro j
    obtain ⟨a1, a2⟩ := src0 c p
      (y0 + psum (fun _ => p.d) j) (x0 + psum (fun _ => p.ty 0 - p.ty 2) j)
    obtain ⟨b1, b2⟩ := src2_id c p ho
      (y0 + psum (fun _ => p.d) (j+1)) (x0 + psum (fun _ => p.ty 0 - p.ty 2) (j+1))
    simp only [psum_succ] at b1 b2 ⊢
    rw [a1, a2, b1, b2]; omega
  · intro j hW hav
    rw [avail0 c p hk] at hav
    have := hx0L j
    have := hnn' j
    simp only [InW, psum_succ] at hW hav ⊢
    omega
  · refine ⟨p.v.toNat, ?_⟩
    rw [avail0 c p hk]; have := hge p.v.toNat; simp only; omega

/-! ## TF-F (o2 = 4, h with a diagonal flip) -/

/-- Alternating steps `a, b, a, b, …`. -/
def alt (a b : Int) (i : Nat) : Int := if i % 2 = 0 then a else b

theorem alt_even (a b : Int) {i : Nat} (h : i % 2 = 0) : alt a b i = a := by simp [alt, h]
theorem alt_odd (a b : Int) {i : Nat} (h : i % 2 = 1) : alt a b i = b := by simp [alt, h]

theorem psum_alt (a b : Int) (j : Nat) :
    psum (alt a b) j - psum (alt b a) j = if j % 2 = 0 then 0 else a - b := by
  induction j with
  | zero => simp
  | succ j ih =>
    rcases Nat.mod_two_eq_zero_or_one j with h | h
    · have h' : (j + 1) % 2 = 1 := by omega
      simp only [psum_succ, alt_even _ _ h, h'] at ih ⊢; simp [h] at ih; simp; omega
    · have h' : (j + 1) % 2 = 0 := by omega
      simp only [psum_succ, alt_odd _ _ h, h'] at ih ⊢; simp [h] at ih; simp; omega

theorem psum_alt_le (a b : Int) (hab : b ≤ a) (j : Nat) : psum (alt b a) j ≤ psum (alt a b) j := by
  have := psum_alt a b j
  split at this <;> omega

theorem alt_ge (a b m : Int) (ha : m ≤ a) (hb : m ≤ b) (i : Nat) : m ≤ alt a b i := by
  unfold alt; split <;> omega

/-- The flip chain: even indices `(X_j, Y_j)`, odd indices `(Y_j, X_j)`. -/
def flipq (X Y : Nat → Int) (j : Nat) : Int × Int := if j % 2 = 0 then (X j, Y j) else (Y j, X j)

theorem flipq_even (X Y : Nat → Int) {j : Nat} (h : j % 2 = 0) : flipq X Y j = (X j, Y j) := by
  simp [flipq, h]
theorem flipq_odd (X Y : Nat → Int) {j : Nat} (h : j % 2 = 1) : flipq X Y j = (Y j, X j) := by
  simp [flipq, h]

/-- TF-F, case A: `e2 = f2 = 0`, `f1 ≤ e1`; `h(x,y) = (y + α, x + β)`, `α = d+f1`, `β = d+e1`.
Chain `q_0 = (0, y0)`, `q_{j+1} = h(q_j)`, along slot 0. -/
theorem caseFA (c : Case) (p : Params) (hk : c.kind = .diag) (ho : c.o2 = 4)
    (hr : RegionP .thin p.d p.e p.f) (hd : 1 ≤ p.d) (N : NF c p)
    (he2 : p.ty 2 = -p.d) (hf2 : p.tx 2 = -p.d) (hfe : p.ty 0 ≤ p.tx 0) : False := by
  have hD := dims p
  have hb := bounds0 c p hk hr hd N
  simp only [RegionP] at hr
  -- normalized steps: x gets β, α, β, …; y gets α, β, α, …
  have hsx := alt_ge (p.d + p.tx 0) (p.d + p.ty 0) 1 (by omega) (by omega)
  have hsy := alt_ge (p.d + p.ty 0) (p.d + p.tx 0) 1 (by omega) (by omega)
  obtain ⟨y0, hy0, hy0u, hst⟩ := stair (alt (p.d + p.tx 0) (p.d + p.ty 0))
    (alt (p.d + p.ty 0) (p.d + p.tx 0)) hsx hsy (psum_alt_le _ _ (by omega)) p.u 0
    (Int.le_refl 0) (by omega)
  have hnx := psum_ge _ hsx
  have hny := psum_ge _ hsy
  apply chain_principle c p hk N 0 2 (Or.inl ⟨rfl, rfl⟩)
    (flipq (fun j => 0 + psum (alt (p.d + p.tx 0) (p.d + p.ty 0)) j)
           (fun j => y0 + psum (alt (p.d + p.ty 0) (p.d + p.tx 0)) j))
  · simp [flipq, InW]; omega
  · intro j; have := hst j; have := hnx j; have := hny j
    rcases Nat.mod_two_eq_zero_or_one j with h | h
    · rw [flipq_even _ _ h]; simp only [OutU]; omega
    · rw [flipq_odd _ _ h]; simp only [OutU]; omega
  · rw [flipq_even _ _ (by rfl), avail2_sw c p hk ho]; simp; omega
  · intro j
    rcases Nat.mod_two_eq_zero_or_one j with h | h
    · have h' : (j + 1) % 2 = 1 := by omega
      rw [flipq_even _ _ h, flipq_odd _ _ h', (src0 c p _ _).1, (src0 c p _ _).2,
        (src2_sw c p ho _ _).1, (src2_sw c p ho _ _).2]
      simp only [psum_succ, alt_even _ _ h]; omega
    · have h' : (j + 1) % 2 = 0 := by omega
      rw [flipq_odd _ _ h, flipq_even _ _ h', (src0 c p _ _).1, (src0 c p _ _).2,
        (src2_sw c p ho _ _).1, (src2_sw c p ho _ _).2]
      simp only [psum_succ, alt_odd _ _ h]; omega
  · intro j hW hav
    have := hnx j; have := hny j
    rcases Nat.mod_two_eq_zero_or_one j with h | h
    · have h' : (j + 1) % 2 = 1 := by omega
      rw [flipq_even _ _ h, avail0 c p hk] at hav
      rw [flipq_even _ _ h] at hW
      rw [flipq_odd _ _ h']
      simp only [InW, psum_succ, alt_even _ _ h] at hW hav ⊢
      omega
    · have h' : (j + 1) % 2 = 0 := by omega
      rw [flipq_odd _ _ h, avail0 c p hk] at hav
      rw [flipq_odd _ _ h] at hW
      rw [flipq_even _ _ h']
      simp only [InW, psum_succ, alt_odd _ _ h] at hW hav ⊢
      omega
  · refine ⟨p.v.toNat, ?_⟩
    have := hnx p.v.toNat; have := hny p.v.toNat
    rcases Nat.mod_two_eq_zero_or_one p.v.toNat with h | h
    · rw [flipq_even _ _ h, avail0 c p hk]; simp only; omega
    · rw [flipq_odd _ _ h, avail0 c p hk]; simp only; omega

/-- TF-F, case A transposed: `e2 = f2 = 0`, `e1 ≤ f1`; chain starts at `(y0, 0)`. -/
theorem caseFAT (c : Case) (p : Params) (hk : c.kind = .diag) (ho : c.o2 = 4)
    (hr : RegionP .thin p.d p.e p.f) (hd : 1 ≤ p.d) (N : NF c p)
    (he2 : p.ty 2 = -p.d) (hf2 : p.tx 2 = -p.d) (hfe : p.tx 0 ≤ p.ty 0) : False := by
  have hD := dims p
  have hb := bounds0 c p hk hr hd N
  simp only [RegionP] at hr
  have hsx := alt_ge (p.d + p.ty 0) (p.d + p.tx 0) 1 (by omega) (by omega)
  have hsy := alt_ge (p.d + p.tx 0) (p.d + p.ty 0) 1 (by omega) (by omega)
  obtain ⟨y0, hy0, hy0u, hst⟩ := stair (alt (p.d + p.ty 0) (p.d + p.tx 0))
    (alt (p.d + p.tx 0) (p.d + p.ty 0)) hsx hsy (psum_alt_le _ _ (by omega)) p.u 0
    (Int.le_refl 0) (by omega)
  have hnx := psum_ge _ hsx
  have hny := psum_ge _ hsy
  apply chain_principle c p hk N 0 2 (Or.inl ⟨rfl, rfl⟩)
    (flipq (fun j => y0 + psum (alt (p.d + p.tx 0) (p.d + p.ty 0)) j) (fun j => 0 + psum (alt (p.d + p.ty 0) (p.d + p.tx 0)) j))
  · simp [flipq, InW]; omega
  · intro j; have := hst j; have := hnx j; have := hny j
    rcases Nat.mod_two_eq_zero_or_one j with h | h
    · rw [flipq_even _ _ h]; simp only [OutU]; omega
    · rw [flipq_odd _ _ h]; simp only [OutU]; omega
  · rw [flipq_even _ _ (by rfl), avail2_sw c p hk ho]; simp; omega
  · intro j
    rcases Nat.mod_two_eq_zero_or_one j with h | h
    · have h' : (j + 1) % 2 = 1 := by omega
      rw [flipq_even _ _ h, flipq_odd _ _ h', (src0 c p _ _).1, (src0 c p _ _).2,
        (src2_sw c p ho _ _).1, (src2_sw c p ho _ _).2]
      simp only [psum_succ, alt_even _ _ h]; omega
    · have h' : (j + 1) % 2 = 0 := by omega
      rw [flipq_odd _ _ h, flipq_even _ _ h', (src0 c p _ _).1, (src0 c p _ _).2,
        (src2_sw c p ho _ _).1, (src2_sw c p ho _ _).2]
      simp only [psum_succ, alt_odd _ _ h]; omega
  · intro j hW hav
    have := hnx j; have := hny j
    rcases Nat.mod_two_eq_zero_or_one j with h | h
    · have h' : (j + 1) % 2 = 1 := by omega
      rw [flipq_even _ _ h, avail0 c p hk] at hav
      rw [flipq_even _ _ h] at hW
      rw [flipq_odd _ _ h']
      simp only [InW, psum_succ, alt_even _ _ h] at hW hav ⊢
      omega
    · have h' : (j + 1) % 2 = 0 := by omega
      rw [flipq_odd _ _ h, avail0 c p hk] at hav
      rw [flipq_odd _ _ h] at hW
      rw [flipq_even _ _ h']
      simp only [InW, psum_succ, alt_odd _ _ h] at hW hav ⊢
      omega
  · refine ⟨p.v.toNat, ?_⟩
    have := hnx p.v.toNat; have := hny p.v.toNat
    rcases Nat.mod_two_eq_zero_or_one p.v.toNat with h | h
    · rw [flipq_even _ _ h, avail0 c p hk]; simp only; omega
    · rw [flipq_odd _ _ h, avail0 c p hk]; simp only; omega

/-- TF-F, case A rotated by 180°: `e1 = f1 = 0`, `f2 ≤ e2`; chain along slot 2 in rotated coordinates. -/
theorem caseFAR (c : Case) (p : Params) (hk : c.kind = .diag) (ho : c.o2 = 4)
    (hr : RegionP .thin p.d p.e p.f) (hd : 1 ≤ p.d) (N : NF c p)
    (he1 : p.tx 0 = 0) (hf1 : p.ty 0 = 0) (hfe : p.ty 2 ≤ p.tx 2) : False := by
  have hD := dims p
  have hb := bounds2_sw c p hk ho hr hd N
  simp only [RegionP] at hr
  have hsx := alt_ge (-p.ty 2) (-p.tx 2) 1 (by omega) (by omega)
  have hsy := alt_ge (-p.tx 2) (-p.ty 2) 1 (by omega) (by omega)
  obtain ⟨y0, hy0, hy0u, hst⟩ := stair (alt (-p.ty 2) (-p.tx 2))
    (alt (-p.tx 2) (-p.ty 2)) hsx hsy (psum_alt_le _ _ (by omega)) p.u 0
    (Int.le_refl 0) (by omega)
  have hnx := psum_ge _ hsx
  have hny := psum_ge _ hsy
  apply chain_principle c p hk N 2 0 (Or.inr ⟨rfl, rfl⟩)
    (flipq (fun j => p.w - 1 - (0 + psum (alt (-p.ty 2) (-p.tx 2)) j)) (fun j => p.w - 1 - (y0 + psum (alt (-p.tx 2) (-p.ty 2)) j)))
  · simp [flipq, InW]; omega
  · intro j; have := hst j; have := hnx j; have := hny j
    rcases Nat.mod_two_eq_zero_or_one j with h | h
    · rw [flipq_even _ _ h]; simp only [OutU]; omega
    · rw [flipq_odd _ _ h]; simp only [OutU]; omega
  · rw [flipq_even _ _ (by rfl), avail0 c p hk]; simp; omega
  · intro j
    rcases Nat.mod_two_eq_zero_or_one j with h | h
    · have h' : (j + 1) % 2 = 1 := by omega
      rw [flipq_even _ _ h, flipq_odd _ _ h', (src0 c p _ _).1, (src0 c p _ _).2,
        (src2_sw c p ho _ _).1, (src2_sw c p ho _ _).2]
      simp only [psum_succ, alt_even _ _ h]; omega
    · have h' : (j + 1) % 2 = 0 := by omega
      rw [flipq_odd _ _ h, flipq_even _ _ h', (src0 c p _ _).1, (src0 c p _ _).2,
        (src2_sw c p ho _ _).1, (src2_sw c p ho _ _).2]
      simp only [psum_succ, alt_odd _ _ h]; omega
  · intro j hW hav
    have := hnx j; have := hny j
    rcases Nat.mod_two_eq_zero_or_one j with h | h
    · have h' : (j + 1) % 2 = 1 := by omega
      rw [flipq_even _ _ h, avail2_sw c p hk ho] at hav
      rw [flipq_even _ _ h] at hW
      rw [flipq_odd _ _ h']
      simp only [InW, psum_succ, alt_even _ _ h] at hW hav ⊢
      omega
    · have h' : (j + 1) % 2 = 0 := by omega
      rw [flipq_odd _ _ h, avail2_sw c p hk ho] at hav
      rw [flipq_odd _ _ h] at hW
      rw [flipq_even _ _ h']
      simp only [InW, psum_succ, alt_odd _ _ h] at hW hav ⊢
      omega
  · refine ⟨p.w.toNat, ?_⟩
    have := hnx p.w.toNat; have := hny p.w.toNat
    rcases Nat.mod_two_eq_zero_or_one p.w.toNat with h | h
    · rw [flipq_even _ _ h, avail2_sw c p hk ho]; simp only; omega
    · rw [flipq_odd _ _ h, avail2_sw c p hk ho]; simp only; omega

/-- TF-F, case A rotated and transposed: `e1 = f1 = 0`, `e2 ≤ f2`. -/
theorem caseFART (c : Case) (p : Params) (hk : c.kind = .diag) (ho : c.o2 = 4)
    (hr : RegionP .thin p.d p.e p.f) (hd : 1 ≤ p.d) (N : NF c p)
    (he1 : p.tx 0 = 0) (hf1 : p.ty 0 = 0) (hfe : p.tx 2 ≤ p.ty 2) : False := by
  have hD := dims p
  have hb := bounds2_sw c p hk ho hr hd N
  simp only [RegionP] at hr
  have hsx := alt_ge (-p.tx 2) (-p.ty 2) 1 (by omega) (by omega)
  have hsy := alt_ge (-p.ty 2) (-p.tx 2) 1 (by omega) (by omega)
  obtain ⟨y0, hy0, hy0u, hst⟩ := stair (alt (-p.tx 2) (-p.ty 2))
    (alt (-p.ty 2) (-p.tx 2)) hsx hsy (psum_alt_le _ _ (by omega)) p.u 0
    (Int.le_refl 0) (by omega)
  have hnx := psum_ge _ hsx
  have hny := psum_ge _ hsy
  apply chain_principle c p hk N 2 0 (Or.inr ⟨rfl, rfl⟩)
    (flipq (fun j => p.w - 1 - (y0 + psum (alt (-p.ty 2) (-p.tx 2)) j)) (fun j => p.w - 1 - (0 + psum (alt (-p.tx 2) (-p.ty 2)) j)))
  · simp [flipq, InW]; omega
  · intro j; have := hst j; have := hnx j; have := hny j
    rcases Nat.mod_two_eq_zero_or_one j with h | h
    · rw [flipq_even _ _ h]; simp only [OutU]; omega
    · rw [flipq_odd _ _ h]; simp only [OutU]; omega
  · rw [flipq_even _ _ (by rfl), avail0 c p hk]; simp; omega
  · intro j
    rcases Nat.mod_two_eq_zero_or_one j with h | h
    · have h' : (j + 1) % 2 = 1 := by omega
      rw [flipq_even _ _ h, flipq_odd _ _ h', (src0 c p _ _).1, (src0 c p _ _).2,
        (src2_sw c p ho _ _).1, (src2_sw c p ho _ _).2]
      simp only [psum_succ, alt_even _ _ h]; omega
    · have h' : (j + 1) % 2 = 0 := by omega
      rw [flipq_odd _ _ h, flipq_even _ _ h', (src0 c p _ _).1, (src0 c p _ _).2,
        (src2_sw c p ho _ _).1, (src2_sw c p ho _ _).2]
      simp only [psum_succ, alt_odd _ _ h]; omega
  · intro j hW hav
    have := hnx j; have := hny j
    rcases Nat.mod_two_eq_zero_or_one j with h | h
    · have h' : (j + 1) % 2 = 1 := by omega
      rw [flipq_even _ _ h, avail2_sw c p hk ho] at hav
      rw [flipq_even _ _ h] at hW
      rw [flipq_odd _ _ h']
      simp only [InW, psum_succ, alt_even _ _ h] at hW hav ⊢
      omega
    · have h' : (j + 1) % 2 = 0 := by omega
      rw [flipq_odd _ _ h, avail2_sw c p hk ho] at hav
      rw [flipq_odd _ _ h] at hW
      rw [flipq_even _ _ h']
      simp only [InW, psum_succ, alt_odd _ _ h] at hW hav ⊢
      omega
  · refine ⟨p.w.toNat, ?_⟩
    have := hnx p.w.toNat; have := hny p.w.toNat
    rcases Nat.mod_two_eq_zero_or_one p.w.toNat with h | h
    · rw [flipq_even _ _ h, avail2_sw c p hk ho]; simp only; omega
    · rw [flipq_odd _ _ h, avail2_sw c p hk ho]; simp only; omega

/-- TF-F, strip case: `e1, f2 ≥ 1`, `f1 = e2 = 0`. The cell `(v-e1-1, d+f2)` must carry
slot 2 (it is the only preimage of the source `(0, v-e1-1-d)`) and slot 0 (only preimage of
`(v-1, d+f2)`). -/
theorem caseFS (c : Case) (p : Params) (hk : c.kind = .diag) (ho : c.o2 = 4)
    (hr : RegionP .thin p.d p.e p.f) (hd : 1 ≤ p.d) (N : NF c p)
    (he1 : 1 ≤ p.tx 0) (hf1 : p.ty 0 = 0) (he2 : p.ty 2 = -p.d) (hf2 : p.tx 2 ≤ -p.d - 1) :
    False := by
  have hD := dims p
  have hb := bounds0 c p hk hr hd N
  have hb2 := bounds2_sw c p hk ho hr hd N
  simp only [RegionP] at hr
  obtain ⟨x, y, hW, h⟩ := surjV c p N 0 (p.v - p.tx 0 - 1 - p.d) (by omega) (by omega)
    (by omega) (by omega)
  obtain ⟨x', y', hW', h'⟩ := surjV c p N (p.v - 1) (-p.tx 2) (by omega) (by omega)
    (by omega) (by omega)
  have s1 := src2_sw c p ho x y
  have s2 := src2_sw c p ho x' y'
  simp only [InW] at hW hW'
  rcases h with ⟨_, h1, _⟩ | ⟨hs, h1, h2⟩
  · omega
  rcases h' with ⟨hs', h1', h2'⟩ | ⟨_, h1', _⟩
  · have hx : x = x' := by omega
    have hy : y = y' := by omega
    rw [hx, hy, hs'] at hs; exact absurd hs (by decide)
  · omega

/-- TF-F, strip case transposed: `f1, e2 ≥ 1`, `e1 = f2 = 0`. -/
theorem caseFST (c : Case) (p : Params) (hk : c.kind = .diag) (ho : c.o2 = 4)
    (hr : RegionP .thin p.d p.e p.f) (hd : 1 ≤ p.d) (N : NF c p)
    (he1 : p.tx 0 = 0) (hf1 : 1 ≤ p.ty 0) (hf2 : p.tx 2 = -p.d) (he2 : p.ty 2 ≤ -p.d - 1) :
    False := by
  have hD := dims p
  have hb := bounds0 c p hk hr hd N
  have hb2 := bounds2_sw c p hk ho hr hd N
  simp only [RegionP] at hr
  obtain ⟨x, y, hW, h⟩ := surjV c p N (p.v - p.ty 0 - 1 - p.d) 0 (by omega) (by omega)
    (by omega) (by omega)
  obtain ⟨x', y', hW', h'⟩ := surjV c p N (-p.ty 2) (p.v - 1) (by omega) (by omega)
    (by omega) (by omega)
  have s1 := src2_sw c p ho x y
  have s2 := src2_sw c p ho x' y'
  simp only [InW] at hW hW'
  rcases h with ⟨_, _, h1⟩ | ⟨hs, h1, h2⟩
  · omega
  rcases h' with ⟨hs', h1', h2'⟩ | ⟨_, _, h1'⟩
  · have hx : x = x' := by omega
    have hy : y = y' := by omega
    rw [hx, hy, hs'] at hs; exact absurd hs (by decide)
  · omega

end TF

set_option linter.unusedVariables false in
open TF in
/-- **Lemma TF.** Thin region (`2u < w`), `diag`, slot 2 with identity or diagonal-flip
orientation: there is no normal form. (`hp`, `he` are not needed.) -/
theorem thin_diag_tf (c : Case) (p : Params) (hk : c.kind = .diag) (ho : c.o2 = 0 ∨ c.o2 = 4)
    (hr : RegionP .thin p.d p.e p.f) (hd : 1 ≤ p.d) (he : 1 ≤ p.e)
    (hp : (p.e+p.f)*(p.e+p.f) = 2*p.d*(p.d+p.e)) (N : NF c p) : False := by
  have hb := bounds0 c p hk hr hd N
  rcases ho with ho | ho
  · have hb2 := bounds2_id c p hk ho hr hd N
    obtain ⟨c1, c2⟩ := cover_id c p hk ho hr hd N
    by_cases h22 : p.tx 2 = -p.d ∧ p.ty 2 = -p.d
    · by_cases hfe : p.ty 0 ≤ p.tx 0
      · exact caseTA c p hk ho hr hd N h22.1 h22.2 hfe
      · exact caseTAT c p hk ho hr hd N h22.1 h22.2 (by omega)
    · by_cases h11 : p.tx 0 = 0 ∧ p.ty 0 = 0
      · by_cases hfe : p.tx 2 ≤ p.ty 2
        · exact caseTAR c p hk ho hr hd N h11.1 h11.2 hfe
        · exact caseTART c p hk ho hr hd N h11.1 h11.2 (by omega)
      · by_cases he2 : p.tx 2 = -p.d
        · -- then f2 > 0, so e1 = 0, f1 > 0
          have hf2 : p.ty 2 ≤ -p.d - 1 := by omega
          have he1 : p.tx 0 = 0 := by
            apply Classical.byContradiction; intro h; have := c1 (by omega); omega
          exact caseTBT c p hk ho hr hd N he1 he2 (by omega) hf2
        · have hf1 : p.ty 0 = 0 := by
            apply Classical.byContradiction; intro h; have := c2 (by omega); omega
          have hf2 : p.ty 2 = -p.d := by
            apply Classical.byContradiction; intro h; have := c1 (by omega); omega
          exact caseTB c p hk ho hr hd N hf1 hf2 (by omega) (by omega)
  · have hb2 := bounds2_sw c p hk ho hr hd N
    obtain ⟨c1, c2⟩ := cover_sw c p hk ho hr hd N
    by_cases h22 : p.tx 2 = -p.d ∧ p.ty 2 = -p.d
    · by_cases hfe : p.ty 0 ≤ p.tx 0
      · exact caseFA c p hk ho hr hd N h22.2 h22.1 hfe
      · exact caseFAT c p hk ho hr hd N h22.2 h22.1 (by omega)
    · by_cases h11 : p.tx 0 = 0 ∧ p.ty 0 = 0
      · by_cases hfe : p.ty 2 ≤ p.tx 2
        · exact caseFAR c p hk ho hr hd N h11.1 h11.2 hfe
        · exact caseFART c p hk ho hr hd N h11.1 h11.2 (by omega)
      · by_cases he1 : p.tx 0 = 0
        · -- f1 > 0, so f2 = 0 (tx2 = -d), hence e2 > 0
          have hf2 := c2 (by omega)
          exact caseFST c p hk ho hr hd N he1 (by omega) hf2 (by omega)
        · have he2 := c1 (by omega)
          have hf1 : p.ty 0 = 0 := by
            apply Classical.byContradiction; intro h; have := c2 (by omega); omega
          exact caseFS c p hk ho hr hd N (by omega) hf1 he2 (by omega)

end Ex89.T22
