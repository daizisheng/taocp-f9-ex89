import Ex89.Prop
import Ex89.Geom
/-! If a dissection fits a configuration, then the search of that configuration must fail. -/
namespace Ex89

/-- A dissection in the normal form of a configuration. -/
structure Fits (c : Cfg) (D : Dissection c.u c.v c.w) : Prop where
  hside : ∀ k, D.toU k = c.side k
  hcorner : ∀ k, D.piece (cornerX c.w k) (cornerY c.w k) = k
  hid : ∀ k, c.ids k = true → (D.motion k).sw = false ∧ (D.motion k).fx = false ∧ (D.motion k).fy = false
  hfix : ∀ k, c.fixed k = true → D.motion k = idMotion
  hu : 0 < c.u
  hv : 0 < c.v
  huw : c.u < c.w
  hvw : c.v < c.w

variable {c : Cfg} {D : Dissection c.u c.v c.w}

theorem Fits.w_pos (F : Fits c D) : 0 < c.w := by have := F.hu; have := F.huw; omega

theorem Fits.corner_lt (F : Fits c D) (k : Fin 4) : cornerX c.w k < c.w ∧ cornerY c.w k < c.w := by
  have := F.w_pos
  revert k
  apply slot_cases <;> simp [cornerX, cornerY] <;> omega

theorem Fits.maps (F : Fits c D) {x y : Nat} (hx : x < c.w) (hy : y < c.w) :
    InSquare (c.S (D.piece x y)) ((D.motion (D.piece x y)).imgX c.w x y)
      ((D.motion (D.piece x y)).imgY c.w x y) := by
  have := D.maps_into x y hx hy
  rw [F.hside] at this
  simpa [Cfg.S, sideOf] using this

theorem Fits.reach_piece (F : Fits c D) {x y : Nat} (hx : x < c.w) (hy : y < c.w) :
    reach c.w (c.S (D.piece x y)) (D.piece x y) x y = true := by
  have h1 := F.maps hx hy
  have hc := F.hcorner (D.piece x y)
  obtain ⟨cx, cy⟩ := F.corner_lt (D.piece x y)
  have h2 := F.maps cx cy
  rw [hc] at h2
  have := Motion.close _ h1 h2
  simp only [reach, Bool.and_eq_true, decide_eq_true_eq]
  omega

theorem Fits.priv_piece (F : Fits c D) {k : Fin 4} {x y : Nat} (hx : x < c.w) (hy : y < c.w)
    (h : c.isPriv k x y = true) : D.piece x y = k := by
  simp only [Cfg.isPriv, Bool.and_eq_true, List.all_eq_true] at h
  have h1 := h.2 _ (mem_allSlots (D.piece x y))
  have h2 := F.reach_piece hx hy
  rw [h2] at h1
  simpa using h1

theorem Fits.mem_priv (F : Fits c D) {k : Fin 4} {p : Nat × Nat} (h : p ∈ c.mkPv k) :
    p.1 < c.w ∧ p.2 < c.w ∧ D.piece p.1 p.2 = k ∧ c.isPriv k p.1 p.2 = true := by
  rw [Cfg.mkPv_eq] at h
  simp only [Cfg.priv, List.mem_filter, mem_grid] at h
  exact ⟨h.1.1, h.1.2, F.priv_piece h.1.1 h.1.2 h.2, h.2⟩

theorem Fits.maps_k (F : Fits c D) {k : Fin 4} {x y : Nat} (hx : x < c.w) (hy : y < c.w)
    (h : D.piece x y = k) :
    InSquare (c.S k) ((D.motion k).imgX c.w x y) ((D.motion k).imgY c.w x y) := by
  subst h; exact F.maps hx hy

theorem Fits.mem_L (F : Fits c D) (k : Fin 4) : D.motion k ∈ c.L c.mkPv k := by
  unfold Cfg.L
  split
  next hf => simp [F.hfix k hf]
  next =>
    obtain ⟨cx, cy⟩ := F.corner_lt k
    simp only [parFilterM_eq, List.mem_filter, Bool.and_eq_true, List.all_eq_true]
    refine ⟨mem_motions _ (Motion.shift_bound _ cx cy (F.maps_k cx cy (F.hcorner k))), ?_, ?_⟩
    · cases hi : c.ids k
      · simp
      · have := F.hid k hi
        simp [this.1, this.2.1, this.2.2]
    · intro p hp
      obtain ⟨h1, h2, h3, _⟩ := F.mem_priv hp
      exact (inSq_iff _ _ _).2 (F.maps_k h1 h2 h3)

/-! ### The tables contain all true edges -/

theorem mkTab_img (c : Cfg) (k : Fin 4) (m : Motion) {i : Nat} (hi : i < c.w * c.w) :
    (c.mkTab k m).img.getD i 0 =
      if inSq (c.S k) (m.imgX c.w (i / c.w) (i % c.w)) (m.imgY c.w (i / c.w) (i % c.w)) then
        tcode c.u c.v (c.side k) (m.imgX c.w (i / c.w) (i % c.w)).toNat
          (m.imgY c.w (i / c.w) (i % c.w)).toNat + 1 else 0 := by
  simp [Cfg.mkTab, Array.getD_eq_getD_getElem?, hi]

theorem mkTab_pre (c : Cfg) (k : Fin 4) (m : Motion) {j : Nat} (hj : j < c.u * c.u + c.v * c.v) :
    (c.mkTab k m).pre.getD j 0 =
      if decide (j < c.u * c.u) == c.side k then
        match pre c.w m (((if c.side k then j else j - c.u * c.u) / c.S k : Nat) : Int)
            (((if c.side k then j else j - c.u * c.u) % c.S k : Nat) : Int) with
        | some r => r.1 * c.w + r.2 + 1
        | none => 0
      else 0 := by
  simp only [Cfg.mkTab]
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, dite_cond_eq_true (eq_true hj)]
  rfl

/-- The true edges. -/
def TrueEdge (c : Cfg) (D : Dissection c.u c.v c.w) (i j : Nat) : Prop :=
  ∃ x y, x < c.w ∧ y < c.w ∧ i = x * c.w + y ∧
    j = tcode c.u c.v (c.side (D.piece x y)) ((D.motion (D.piece x y)).imgX c.w x y).toNat
      ((D.motion (D.piece x y)).imgY c.w x y).toNat

theorem sideOf_eq (c : Cfg) (k : Fin 4) : sideOf c.u c.v (c.side k) = c.S k := rfl

theorem tcode_decode {u v : Nat} {b : Bool} {a e : Nat} (ha : a < sideOf u v b) (he : e < sideOf u v b) :
    decide (tcode u v b a e < u * u) = b ∧
    (if b then tcode u v b a e else tcode u v b a e - u * u) / sideOf u v b = a ∧
    (if b then tcode u v b a e else tcode u v b a e - u * u) % sideOf u v b = e := by
  cases b
  · simp only [sideOf, Bool.false_eq_true, ite_false] at ha he
    have e0 : tcode u v false a e - u * u = a * v + e := by simp [tcode]; omega
    have hv : 0 < v := by omega
    refine ⟨by simp [tcode]; omega, ?_, ?_⟩
    · simp only [Bool.false_eq_true, ite_false, e0, sideOf]
      rw [Nat.mul_comm, Nat.mul_add_div hv, Nat.div_eq_of_lt he]; simp
    · simp only [Bool.false_eq_true, ite_false, e0, sideOf]
      rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt he]
  · simp only [sideOf, ite_true] at ha he
    have hu : 0 < u := by omega
    have := code_lt ha he
    refine ⟨by simp [tcode]; omega, ?_, ?_⟩
    · simp only [ite_true, tcode, sideOf]
      rw [Nat.mul_comm, Nat.mul_add_div hu, Nat.div_eq_of_lt he]; simp
    · simp only [ite_true, tcode, sideOf]
      rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt he]

/-- The inverse table at the number of a target cell. -/
theorem mkTab_pre_tcode (c : Cfg) (k : Fin 4) (m : Motion) {a e : Nat}
    (ha : a < c.S k) (he : e < c.S k) :
    (c.mkTab k m).pre.getD (tcode c.u c.v (c.side k) a e) 0 =
      match pre c.w m (a : Int) (e : Int) with
      | some r => r.1 * c.w + r.2 + 1
      | none => 0 := by
  have hl : tcode c.u c.v (c.side k) a e < c.u * c.u + c.v * c.v := tcode_lt ha he
  obtain ⟨d1, d2, d3⟩ := tcode_decode (u := c.u) (v := c.v) (b := c.side k) ha he
  rw [mkTab_pre c k m hl, d1]
  simp only [beq_self_eq_true, ite_true]
  have e0 : c.S k = sideOf c.u c.v (c.side k) := rfl
  rw [e0, d2, d3]

theorem Fits.graph (F : Fits c D) (q : Q)
    (hq : ∀ k, c.mkTab k (D.motion k) = q.t0 ∨ c.mkTab k (D.motion k) = q.t1 ∨
      c.mkTab k (D.motion k) = q.t2 ∨ c.mkTab k (D.motion k) = q.t3) :
    Graph q c.nS c.nT (TrueEdge c D) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i hi
    have hi' : i < c.w * c.w := hi
    obtain ⟨hx, hy, he⟩ := code_split hi'
    have hm := F.maps hx hy
    obtain ⟨m1, m2, m3, m4⟩ := id hm
    have hin : inSq (c.S (D.piece (i / c.w) (i % c.w)))
        ((D.motion (D.piece (i / c.w) (i % c.w))).imgX c.w (i / c.w) (i % c.w))
        ((D.motion (D.piece (i / c.w) (i % c.w))).imgY c.w (i / c.w) (i % c.w)) = true :=
      (inSq_iff _ _ _).2 hm
    refine ⟨tcode c.u c.v (c.side (D.piece (i / c.w) (i % c.w))) _ _, ?_,
      ⟨_, _, hx, hy, he.symm, rfl⟩, ?_⟩
    · apply tcode_lt
      · rw [sideOf_eq]; omega
      · rw [sideOf_eq]; omega
    · have hval := mkTab_img c (D.piece (i / c.w) (i % c.w)) (D.motion (D.piece (i / c.w) (i % c.w))) hi'
      rw [hin] at hval
      simp only [ite_true] at hval
      rcases hq (D.piece (i / c.w) (i % c.w)) with h | h | h | h <;> rw [h] at hval <;> simp [hval]
  · intro j hj
    have hj' : j < c.u * c.u + c.v * c.v := hj
    -- decode the target cell
    have hdec : ∃ b a e, a < sideOf c.u c.v b ∧ e < sideOf c.u c.v b ∧
        j = tcode c.u c.v b a e ∧ decide (j < c.u * c.u) = b ∧
        (if b then j else j - c.u * c.u) / sideOf c.u c.v b = a ∧
        (if b then j else j - c.u * c.u) % sideOf c.u c.v b = e := by
      by_cases hc : j < c.u * c.u
      · obtain ⟨h1, h2, h3⟩ := code_split hc
        exact ⟨true, j / c.u, j % c.u, h1, h2, h3.symm, by simp [hc], rfl, rfl⟩
      · have hc' : j - c.u * c.u < c.v * c.v := by omega
        obtain ⟨h1, h2, h3⟩ := code_split hc'
        refine ⟨false, (j - c.u * c.u) / c.v, (j - c.u * c.u) % c.v, h1, h2, ?_, by simp [hc], rfl, rfl⟩
        simp only [tcode, Bool.false_eq_true, ite_false]
        omega
    obtain ⟨b, a, e, ha, he, hjc, hb, hd1, hd2⟩ := hdec
    have hSq : InSquare (if b then c.u else c.v) (a : Int) (e : Int) := by
      simp only [sideOf] at ha he
      simp only [InSquare]
      omega
    obtain ⟨x, y, hx, hy, hc, h1, h2⟩ := D.surjective b a e hSq
    rw [F.hside] at hc
    refine ⟨x * c.w + y, code_lt hx hy, ⟨x, y, hx, hy, rfl, ?_⟩, ?_⟩
    · rw [h1, h2, hc]; simpa using hjc
    · have hval := mkTab_pre c (D.piece x y) (D.motion (D.piece x y)) hj'
      have e0 : c.S (D.piece x y) = sideOf c.u c.v b := by rw [← sideOf_eq, hc]
      have hcond : (decide (j < c.u * c.u) == c.side (D.piece x y)) = true := by rw [hb, hc]; simp
      rw [hcond, hc, e0, hd1, hd2, ← h1, ← h2, pre_img _ hx hy] at hval
      simp only [ite_true] at hval
      rcases hq (D.piece x y) with h | h | h | h <;> rw [h] at hval <;> simp [hval]
  · rintro i j j' ⟨x, y, hx, hy, e1, e2⟩ ⟨x', y', _, hy', e3, e4⟩
    have := code_inj hy hy' (e1.symm.trans e3)
    obtain ⟨rfl, rfl⟩ := this
    rw [e2, e4]
  · rintro i i' j ⟨x, y, hx, hy, e1, e2⟩ ⟨x', y', hx', hy', e3, e4⟩
    have hm := F.maps hx hy
    have hm' := F.maps hx' hy'
    obtain ⟨m1, m2, m3, m4⟩ := id hm
    obtain ⟨m1', m2', m3', m4'⟩ := id hm'
    have := tcode_inj (by rw [sideOf_eq]; omega) (by rw [sideOf_eq]; omega)
      (by rw [sideOf_eq]; omega) (by rw [sideOf_eq]; omega) (e2.symm.trans e4)
    obtain ⟨b1, b2, b3⟩ := this
    have := D.injective x y x' y' hx hy hx' hy' (by rw [F.hside, F.hside, b1]) (by omega) (by omega)
    rw [e1, e3, this.1, this.2]

theorem Fits.not_dead (F : Fits c D) (q : Q)
    (hq : ∀ k, c.mkTab k (D.motion k) = q.t0 ∨ c.mkTab k (D.motion k) = q.t1 ∨
      c.mkTab k (D.motion k) = q.t2 ∨ c.mkTab k (D.motion k) = q.t3) :
    dead q (List.range c.nS) (List.range c.nT) c.nS (St.init c.nS c.nT) = false :=
  dead_false (F.graph q hq) _ _ (fun _ h => List.mem_range.1 h) (fun _ h => List.mem_range.1 h) _ (inv_init _ _ _)

theorem Fits.code_nat (F : Fits c D) {x y : Nat} (hx : x < c.w) (hy : y < c.w) :
    ((D.motion (D.piece x y)).imgX c.w x y).toNat < c.S (D.piece x y) ∧
    ((D.motion (D.piece x y)).imgY c.w x y).toNat < c.S (D.piece x y) ∧
    (((D.motion (D.piece x y)).imgX c.w x y).toNat : Int) = (D.motion (D.piece x y)).imgX c.w x y ∧
    (((D.motion (D.piece x y)).imgY c.w x y).toNat : Int) = (D.motion (D.piece x y)).imgY c.w x y := by
  obtain ⟨m1, m2, m3, m4⟩ := F.maps hx hy
  omega

/-- The table of private cells. -/
theorem get_privTab (c : Cfg) (k : Fin 4) {x y : Nat} (hx : x < c.w) (hy : y < c.w) :
    (c.privTab k).getD (x * c.w + y) false = c.isPriv k x y := by
  have hi := code_lt hx hy
  obtain ⟨h1, h2, h3⟩ := code_split hi
  have e := code_inj hy h2 (h3.symm : x * c.w + y = (x * c.w + y) / c.w * c.w + (x * c.w + y) % c.w)
  simp only [Cfg.privTab]
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, dite_cond_eq_true (eq_true hi)]
  simp only [Option.getD_some]
  rw [← e.1, ← e.2]

theorem mkPT_codes (c : Cfg) (pv : Pv) (k : Fin 4) :
    (c.mkPT pv).codes k = (pv k).map fun p => p.1 * c.w + p.2 := by
  revert k; apply slot_cases <;> rfl

theorem mkPT_isP (c : Cfg) (pv : Pv) (k : Fin 4) : (c.mkPT pv).isP k = c.privTab k := by
  revert k; apply slot_cases <;> rfl

theorem Fits.ptd_true (F : Fits c D) {k l : Fin 4} (hne : k ≠ l) (hs : c.side k = c.side l) :
    ptd (c.mkPT c.mkPv) k l (c.mkTab k (D.motion k)) (c.mkTab l (D.motion l)) = true := by
  simp only [ptd, List.all_eq_true]
  intro i hi
  rw [mkPT_codes, List.mem_map] at hi
  obtain ⟨p, hp, rfl⟩ := hi
  obtain ⟨h1, h2, h3, h4⟩ := F.mem_priv hp
  have hin := F.maps_k h1 h2 h3
  have hlt := code_lt h1 h2
  have hval := mkTab_img c l (D.motion l) hlt
  obtain ⟨_, q2, q3⟩ := code_split hlt
  have ee := code_inj h2 q2 (q3.symm : p.1 * c.w + p.2 = _)
  rw [← ee.1, ← ee.2, (inSq_iff _ _ _).2 hin] at hval
  simp only [ite_true] at hval
  rw [hval]
  obtain ⟨n1, n2, n3, n4⟩ := F.code_nat h1 h2
  rw [h3] at n1 n2 n3 n4
  have nk1 : ((D.motion l).imgX c.w p.1 p.2).toNat < c.S k := by
    have : c.S k = c.S l := by simp only [Cfg.S, hs]
    omega
  have nk2 : ((D.motion l).imgY c.w p.1 p.2).toNat < c.S k := by
    have : c.S k = c.S l := by simp only [Cfg.S, hs]
    omega
  have hpre := mkTab_pre_tcode c k (D.motion k) nk1 nk2
  rw [hs, n3, n4] at hpre
  simp only [Nat.add_sub_cancel]
  rw [hpre, Bool.or_eq_true]
  right
  split
  next r hr =>
    obtain ⟨r1, r2, e1, e2⟩ := pre_some _ hr
    simp only [Nat.add_sub_cancel, mkPT_isP]
    rw [get_privTab c k r1 r2]
    cases hP : c.isPriv k r.1 r.2 with
    | false => simp
    | true =>
      exfalso
      have h5 := F.priv_piece r1 r2 hP
      have := D.injective r.1 r.2 p.1 p.2 r1 r2 h1 h2
        (by rw [h5, h3, F.hside, F.hside, hs])
        (by rw [h5, h3]; exact e1) (by rw [h5, h3]; exact e2)
      apply hne
      rw [← h5, ← h3, this.1, this.2]
  next => simp

theorem Fits.corners_true (F : Fits c D) (k : Fin 4) {ms : List Tab}
    (hm : ∀ j, c.side j = c.side k → c.mkTab j (D.motion j) ∈ ms) :
    cornersOk (c.tcorners k) ms = true := by
  have key : ∀ a e : Nat, a < c.S k → e < c.S k →
      (ms.any fun m => m.pre.getD (tcode c.u c.v (c.side k) a e) 0 != 0) = true := by
    intro a e ha he
    have hS : InSquare (if c.side k then c.u else c.v) (a : Int) (e : Int) := by
      have ha' : a < (if c.side k then c.u else c.v) := ha
      have he' : e < (if c.side k then c.u else c.v) := he
      simp only [InSquare]; omega
    obtain ⟨x, y, hx, hy, hb, h1, h2⟩ := D.surjective (c.side k) a e hS
    rw [F.hside] at hb
    rw [List.any_eq_true]
    refine ⟨_, hm _ hb, ?_⟩
    have e0 : c.S (D.piece x y) = c.S k := by simp only [Cfg.S, hb]
    have hpre := mkTab_pre_tcode c (D.piece x y) (D.motion (D.piece x y)) (a := a) (e := e) (by omega) (by omega)
    rw [hb, ← h1, ← h2, pre_img _ hx hy] at hpre
    simp only [hpre]
    simp
  have hS : 0 < c.S k := by
    have := F.hu; have := F.hv
    simp only [Cfg.S, sideOf]; split <;> omega
  simp only [cornersOk, Cfg.tcorners, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
  exact ⟨key _ _ hS hS, key _ _ hS (by omega), key _ _ (by omega) hS, key _ _ (by omega) (by omega)⟩

theorem Fits.pack_mem (F : Fits c D) (k : Fin 4) :
    (⟨D.motion k, c.mkTab k (D.motion k)⟩ : Pack) ∈ c.packs c.mkPv k := by
  simp only [Cfg.packs, parMap_eq, List.mem_map]
  exact ⟨_, F.mem_L k, rfl⟩

theorem Fits.pair_mem (F : Fits c D) {a b : Fin 4} (hne : a ≠ b) (hs : c.side a = c.side b)
    (hgroup : ∀ j, c.side j = c.side a → j = a ∨ j = b) :
    ((⟨D.motion a, c.mkTab a (D.motion a)⟩ : Pack), (⟨D.motion b, c.mkTab b (D.motion b)⟩ : Pack)) ∈
      c.pairs c.mkPv (c.mkPT c.mkPv) a b := by
  simp only [Cfg.pairs_eq, List.mem_flatMap, List.mem_map, List.mem_filter, Bool.and_eq_true, Prod.mk.injEq]
  refine ⟨_, F.pack_mem a, _, ⟨F.pack_mem b, F.ptd_true hne hs, ?_⟩, rfl, rfl⟩
  apply F.corners_true
  intro j hj
  rcases hgroup j hj with rfl | rfl <;> simp

/-! ### Soundness of pair forcing -/

section PairForce

theorem get_clr_ne {a : Array Bool} {i j : Nat} (h : i ≠ j) : get (clr a i) j = get a j := by
  unfold get clr
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds_ne h, ← Array.getD_eq_getD_getElem?]

theorem get_set_imp {a : Array Bool} {i j : Nat} (h : get (set a i) j = true) :
    j = i ∨ get a j = true := by
  by_cases hi : i < a.size
  · rw [get_set hi] at h
    simpa using h
  · right
    have : set a i = a := by simp [set, Array.setIfInBounds, hi]
    rwa [this] at h

theorem eIdx_inj {p p' : Nat} {s s' : Bool} (h : eIdx p s = eIdx p' s') : p = p' ∧ s = s' := by
  unfold eIdx at h
  cases s <;> cases s' <;> simp at h ⊢ <;> omega

/-- What is true of the pair of a true dissection. `In p s` says that cell `p` belongs to motion `s`. -/
structure PFT (t0 t1 : Tab) (os : List Nat) (In : Nat → Bool → Prop) (τ : Nat → Nat) : Prop where
  excl : ∀ p, In p false → In p true → False
  img : ∀ p s, In p s → (tabS t0 t1 s).img.getD p 0 = τ p + 1
  inj : ∀ p p' s s', In p s → In p' s' → τ p = τ p' → p = p'
  tgt : ∀ o ∈ os, ∃ p s, In p s ∧ (tabS t0 t1 s).pre.getD o 0 = p + 1

/-- The invariant: true edges stay alive, and forced cells belong to the pair. -/
structure PFI (In : Nat → Bool → Prop) (st : PFS) : Prop where
  alive : ∀ p s, In p s → get st.alive (eIdx p s) = true
  forced : ∀ p, get st.forced p = true → In p false ∨ In p true

variable {t0 t1 : Tab} {os : List Nat} {In : Nat → Bool → Prop} {τ : Nat → Nat} {st : PFS}

theorem PFT.ne_of (P : PFT t0 t1 os In τ) {p : Nat} {s s' : Bool} (h : In p s) (h' : In p s') : s = s' := by
  cases s <;> cases s' <;> first | rfl | exact (P.excl p h h').elim | exact (P.excl p h' h).elim

theorem PFT.force (P : PFT t0 t1 os In τ) (I : PFI In st) {p : Nat} {s : Bool} (h : In p s) :
    PFI In (pfForce st p s) := by
  constructor
  · intro j s' hj
    show get (clr st.alive (eIdx p (!s))) (eIdx j s') = true
    rw [get_clr_ne]
    · exact I.alive j s' hj
    · intro e
      obtain ⟨rfl, rfl⟩ := eIdx_inj e
      have := P.ne_of h hj
      cases s <;> simp at this
  · intro j hj
    rcases get_set_imp hj with rfl | hj
    · cases s
      · exact Or.inl h
      · exact Or.inr h
    · exact I.forced j hj

theorem PFT.pfT_some (P : PFT t0 t1 os In τ) (I : PFI In st) {o : Nat} (ho : o ∈ os) :
    ∃ st', pfT t0 t1 st o = some st' ∧ PFI In st' := by
  obtain ⟨p, s, hin, hpre⟩ := P.tgt o ho
  have hal := I.alive p s hin
  unfold pfT
  simp only
  cases s with
  | false =>
    have hp0 : t0.pre.getD o 0 = p + 1 := hpre
    have c0 : ((t0.pre.getD o 0 != 0) && get st.alive (eIdx (t0.pre.getD o 0 - 1) false)) = true := by
      rw [hp0]; simpa using hal
    rw [if_pos c0]
    split
    · exact ⟨st, rfl, I⟩
    · refine ⟨_, rfl, ?_⟩
      rw [hp0]
      exact P.force I hin
  | true =>
    have hp1 : t1.pre.getD o 0 = p + 1 := hpre
    have c1 : ((t1.pre.getD o 0 != 0) && get st.alive (eIdx (t1.pre.getD o 0 - 1) true)) = true := by
      rw [hp1]; simpa using hal
    rw [if_pos c1]
    split
    · exact ⟨st, rfl, I⟩
    · refine ⟨_, rfl, ?_⟩
      rw [hp1]
      exact P.force I hin

theorem PFT.other (P : PFT t0 t1 os In τ) (I : PFI In st) {p : Nat} {s : Bool} (h : In p s) :
    PFI In (pfOther t0 t1 st p s) := by
  unfold pfOther
  simp only
  split
  next hc =>
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hc
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hc
    constructor
    · intro j s' hj
      show get (clr st.alive _) _ = true
      rw [get_clr_ne]
      · exact I.alive j s' hj
      · intro e
        obtain ⟨e1, e2⟩ := eIdx_inj e
        subst e1 e2
        have a1 := P.img _ _ hj
        have a2 := P.img _ _ h
        have e3 := a1.symm.trans (h4.trans a2)
        exact h3 (P.inj _ _ _ _ hj h (Nat.succ.inj e3))
    · exact I.forced
  next => exact I

theorem PFT.pfS_some (P : PFT t0 t1 os In τ) (I : PFI In st) (p : Nat) :
    ∃ st', pfS t0 t1 st p = some st' ∧ PFI In st' := by
  unfold pfS
  by_cases hf : get st.forced p = true
  · simp only [hf, Bool.not_true, Bool.false_eq_true, if_false]
    rcases I.forced p hf with h | h
    · have c0 := I.alive p false h
      rw [if_pos c0]
      split
      · exact ⟨st, rfl, I⟩
      · exact ⟨_, rfl, P.other I h⟩
    · have c1 := I.alive p true h
      by_cases c0 : get st.alive (eIdx p false) = true
      · rw [if_pos c0, if_pos c1]; exact ⟨st, rfl, I⟩
      · rw [if_neg c0, if_pos c1]; exact ⟨_, rfl, P.other I h⟩
  · simp only [Bool.not_eq_true] at hf
    simp only [hf, Bool.not_false, if_true]
    exact ⟨st, rfl, I⟩

theorem PFT.passT (P : PFT t0 t1 os In τ) {l : List Nat} (hl : ∀ o ∈ l, o ∈ os) (I : PFI In st) :
    ∃ st', pfPassT t0 t1 l st = some st' ∧ PFI In st' := by
  induction l generalizing st with
  | nil => exact ⟨st, rfl, I⟩
  | cons o l ih =>
    obtain ⟨s1, e1, i1⟩ := P.pfT_some I (hl o (by simp))
    simp only [pfPassT, e1]
    exact ih (fun o ho => hl o (by simp [ho])) i1

theorem PFT.passS (P : PFT t0 t1 os In τ) (l : List Nat) (I : PFI In st) :
    ∃ st', pfPassS t0 t1 l st = some st' ∧ PFI In st' := by
  induction l generalizing st with
  | nil => exact ⟨st, rfl, I⟩
  | cons o l ih =>
    obtain ⟨s1, e1, i1⟩ := P.pfS_some I o
    simp only [pfPassS, e1]
    exact ih i1

theorem PFT.loop (P : PFT t0 t1 os In τ) (rS : List Nat) (n : Nat) (I : PFI In st) :
    ∃ st', pfLoop t0 t1 os rS n st = some st' ∧ PFI In st' := by
  induction n generalizing st with
  | zero => exact ⟨st, rfl, I⟩
  | succ n ih =>
    obtain ⟨s1, e1, i1⟩ := P.passT (fun _ h => h) I
    obtain ⟨s2, e2, i2⟩ := P.passS rS i1
    simp only [pfLoop, e1, e2]
    split
    · exact ⟨s2, rfl, i2⟩
    · exact ih i2

theorem testBit_bitsD (f : Nat → Bool) (d lo p : Nat) :
    (bitsD f d lo).testBit p = (decide (p < 2 ^ d) && f (lo + p)) := by
  induction d generalizing lo p with
  | zero =>
    simp only [bitsD]
    by_cases hp : p = 0
    · subst hp
      cases hf : f lo <;> simp [hf]
    · have h1 : (decide (p < 2 ^ 0)) = false := by simp; omega
      rw [h1]
      split
      · cases p with
        | zero => exact absurd rfl hp
        | succ q => simp [Nat.testBit_succ]
      · simp
  | succ d ih =>
    simp only [bitsD, Nat.testBit_or, ih, Nat.testBit_shiftLeft]
    have e2 : 2 ^ (d + 1) = 2 * 2 ^ d := by rw [Nat.pow_succ]; omega
    by_cases hp : p < 2 ^ d
    · have h1 : ¬ (2 ^ d ≤ p) := by omega
      have h2 : p < 2 ^ (d + 1) := by omega
      simp [hp, h1, h2]
    · have h1 : 2 ^ d ≤ p := by omega
      have e3 : lo + 2 ^ d + (p - 2 ^ d) = lo + p := by omega
      have h4 : (decide (p - 2 ^ d < 2 ^ d)) = decide (p < 2 ^ (d + 1)) := by
        simp only [decide_eq_decide]; omega
      simp [hp, h1, e3, h4]

theorem testBit_bitsUpTo (f : Nat → Bool) (n p : Nat) :
    (bitsUpTo f n).testBit p = (decide (p < n) && f p) := by
  unfold bitsUpTo
  rw [testBit_bitsD]
  have hn : n < 2 ^ (n.log2 + 1) := Nat.lt_log2_self
  by_cases hp : p < n
  · have : p < 2 ^ (n.log2 + 1) := by omega
    simp [hp, this]
  · simp [hp]

end PairForce

theorem Fits.isP_piece (F : Fits c D) {j : Fin 4} {p : Nat} (hp : p < c.w * c.w)
    (h : ((c.mkPT c.mkPv).isP j).getD p false = true) : D.piece (p / c.w) (p % c.w) = j := by
  obtain ⟨hx, hy, he⟩ := code_split hp
  rw [mkPT_isP, ← he, get_privTab c j hx hy] at h
  exact F.priv_piece hx hy h

/-- The number of the target cell of a source cell. -/
def trueTau (c : Cfg) (D : Dissection c.u c.v c.w) (i : Nat) : Nat :=
  let x := i / c.w; let y := i % c.w
  tcode c.u c.v (c.side (D.piece x y)) ((D.motion (D.piece x y)).imgX c.w x y).toNat
    ((D.motion (D.piece x y)).imgY c.w x y).toNat

theorem Fits.trueEdge (_F : Fits c D) {i : Nat} (hi : i < c.w * c.w) : TrueEdge c D i (trueTau c D i) := by
  obtain ⟨hx, hy, he⟩ := code_split hi
  exact ⟨_, _, hx, hy, he.symm, rfl⟩

theorem Fits.img_true (F : Fits c D) {i : Nat} (hi : i < c.w * c.w) {k : Fin 4}
    (hk : D.piece (i / c.w) (i % c.w) = k) :
    (c.mkTab k (D.motion k)).img.getD i 0 = trueTau c D i + 1 := by
  subst hk
  obtain ⟨hx, hy, _⟩ := code_split hi
  have hin := (inSq_iff _ _ _).2 (F.maps hx hy)
  rw [mkTab_img c _ _ hi, hin]
  simp [trueTau]

/-- Each target cell is reached from its true source cell, through the table of its piece. -/
theorem Fits.true_pre (F : Fits c D) {j : Nat} (hj' : j < c.u * c.u + c.v * c.v) :
    ∃ x y, x < c.w ∧ y < c.w ∧ c.side (D.piece x y) = decide (j < c.u * c.u) ∧
      (c.mkTab (D.piece x y) (D.motion (D.piece x y))).pre.getD j 0 = x * c.w + y + 1 := by
  have hdec : ∃ b a e, a < sideOf c.u c.v b ∧ e < sideOf c.u c.v b ∧
      j = tcode c.u c.v b a e ∧ decide (j < c.u * c.u) = b ∧
      (if b then j else j - c.u * c.u) / sideOf c.u c.v b = a ∧
      (if b then j else j - c.u * c.u) % sideOf c.u c.v b = e := by
    by_cases hc : j < c.u * c.u
    · obtain ⟨h1, h2, h3⟩ := code_split hc
      exact ⟨true, j / c.u, j % c.u, h1, h2, h3.symm, by simp [hc], rfl, rfl⟩
    · have hc' : j - c.u * c.u < c.v * c.v := by omega
      obtain ⟨h1, h2, h3⟩ := code_split hc'
      refine ⟨false, (j - c.u * c.u) / c.v, (j - c.u * c.u) % c.v, h1, h2, ?_, by simp [hc], rfl, rfl⟩
      simp only [tcode, Bool.false_eq_true, ite_false]
      omega
  obtain ⟨b, a, e, ha, he, hjc, hb, hd1, hd2⟩ := hdec
  have hSq : InSquare (if b then c.u else c.v) (a : Int) (e : Int) := by
    simp only [sideOf] at ha he
    simp only [InSquare]
    omega
  obtain ⟨x, y, hx, hy, hc, h1, h2⟩ := D.surjective b a e hSq
  rw [F.hside] at hc
  refine ⟨x, y, hx, hy, by rw [hc, hb], ?_⟩
  have hval := mkTab_pre c (D.piece x y) (D.motion (D.piece x y)) hj'
  have e0 : c.S (D.piece x y) = sideOf c.u c.v b := by rw [← sideOf_eq, hc]
  have hcond : (decide (j < c.u * c.u) == c.side (D.piece x y)) = true := by rw [hb, hc]; simp
  rw [hcond, hc, e0, hd1, hd2, ← h1, ← h2, pre_img _ hx hy] at hval
  simpa using hval

/-- The result of pair forcing for a true pair. -/
theorem Fits.pairForce_true (F : Fits c D) {a b : Fin 4} (h1 : a ≠ b)
    (g1 : ∀ j, c.side j = c.side a → j = a ∨ j = b) (s1 : c.side a = c.side b) :
    ∃ r, pairForce c.nS (c.mkPT c.mkPv) a b (otherTab c.nS (c.mkPT c.mkPv) a) (otherTab c.nS (c.mkPT c.mkPv) b)
        ((List.range c.nT).filter fun j => decide (j < c.u * c.u) == c.side a) (List.range c.nS)
        ((⟨D.motion a, c.mkTab a (D.motion a)⟩ : Pack), (⟨D.motion b, c.mkTab b (D.motion b)⟩ : Pack)) = some r ∧
      r.pq = ((⟨D.motion a, c.mkTab a (D.motion a)⟩ : Pack), (⟨D.motion b, c.mkTab b (D.motion b)⟩ : Pack)) ∧
      (∀ p, p < c.nS → (D.piece (p / c.w) (p % c.w) = a ∨ D.piece (p / c.w) (p % c.w) = b) → r.AL.testBit p = true) ∧
      (∀ p, c.nS ≤ p → r.AL.testBit p = false) ∧
      (∀ p, r.F.testBit p = true → D.piece (p / c.w) (p % c.w) = a ∨ D.piece (p / c.w) (p % c.w) = b) := by
  let t0 := c.mkTab a (D.motion a)
  let t1 := c.mkTab b (D.motion b)
  let In : Nat → Bool → Prop := fun p s => p < c.nS ∧ D.piece (p / c.w) (p % c.w) = if s then b else a
  have hqq : ∀ k, c.mkTab k (D.motion k) = (⟨c.mkTab k (D.motion k), c.mkTab k (D.motion k),
      c.mkTab 0 (D.motion 0), c.mkTab 0 (D.motion 0)⟩ : Q).t0 := fun _ => rfl
  have hinj : ∀ i i', i < c.nS → i' < c.nS → trueTau c D i = trueTau c D i' → i = i' := by
    intro i i' hi hi' e
    have G := F.graph ⟨c.mkTab 0 (D.motion 0), c.mkTab 1 (D.motion 1), c.mkTab 2 (D.motion 2),
      c.mkTab 3 (D.motion 3)⟩ (by apply slot_cases <;> simp)
    have e1 := F.trueEdge (i := i) hi
    have e2 := F.trueEdge (i := i') hi'
    rw [← e] at e2
    exact G.inj _ _ _ e1 e2
  have P : PFT t0 t1 ((List.range c.nT).filter fun j => decide (j < c.u * c.u) == c.side a) In (trueTau c D) := by
    constructor
    · rintro p ⟨_, e1⟩ ⟨_, e2⟩
      simp only [Bool.false_eq_true, if_false, if_true] at e1 e2
      exact h1 (e1.symm.trans e2)
    · rintro p s ⟨hp, e⟩
      cases s
      · exact F.img_true hp e
      · exact F.img_true hp e
    · rintro p p' s s' ⟨hp, _⟩ ⟨hp', _⟩ e
      exact hinj _ _ hp hp' e
    · intro o ho
      simp only [List.mem_filter, List.mem_range, beq_iff_eq] at ho
      obtain ⟨x, y, hx, hy, hs, hpre⟩ := F.true_pre (j := o) ho.1
      have hlt := code_lt hx hy
      obtain ⟨_, q2, q3⟩ := code_split hlt
      have ee := code_inj hy q2 (q3.symm : x * c.w + y = _)
      rcases g1 (D.piece x y) (by rw [hs, ho.2]) with e | e
      · refine ⟨x * c.w + y, false, ⟨hlt, ?_⟩, ?_⟩
        · simp only [Bool.false_eq_true, if_false]; rw [← ee.1, ← ee.2]; exact e
        · rw [e] at hpre; exact hpre
      · refine ⟨x * c.w + y, true, ⟨hlt, ?_⟩, ?_⟩
        · simp only [if_true]; rw [← ee.1, ← ee.2]; exact e
        · rw [e] at hpre; exact hpre
  have hother : ∀ p s, In p s → otherP (c.mkPT c.mkPv) (if s then b else a) p = false := by
    rintro p s ⟨hp, e⟩
    rw [Bool.eq_false_iff]
    intro hc
    simp only [otherP, List.any_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq] at hc
    obtain ⟨j, _, hj, hP⟩ := hc
    exact hj ((F.isP_piece hp hP).symm.trans e)
  have I0 : PFI In ⟨pfAlive0 c.nS (otherTab c.nS (c.mkPT c.mkPv) a) (otherTab c.nS (c.mkPT c.mkPv) b) t0 t1,
      pfForced0 c.nS (c.mkPT c.mkPv) a b⟩ := by
    constructor
    · intro p s hin
      have hp : p < c.nS := hin.1
      have hlt : eIdx p s < 2 * c.nS := by unfold eIdx; split <;> omega
      have d1 : eIdx p s / 2 = p := by unfold eIdx; split <;> omega
      have d2 : (eIdx p s % 2 == 1) = s := by unfold eIdx; cases s <;> simp <;> omega
      show get (pfAlive0 c.nS (otherTab c.nS (c.mkPT c.mkPv) a) (otherTab c.nS (c.mkPT c.mkPv) b) t0 t1) (eIdx p s) = true
      unfold get pfAlive0
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, dif_pos hlt]
      simp only [Option.getD_some, d1, d2]
      have hi := P.img p s hin
      have ho := hother p s hin
      have hget : ∀ k, (otherTab c.nS (c.mkPT c.mkPv) k).getD p false = otherP (c.mkPT c.mkPv) k p := by
        intro k
        unfold otherTab
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, dif_pos hp]
        rfl
      cases s <;> simp_all
    · intro p hp
      show In p false ∨ In p true
      have hget : get (pfForced0 c.nS (c.mkPT c.mkPv) a b) p = true := hp
      unfold get pfForced0 at hget
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn] at hget
      split at hget
      next hlt =>
        simp only [Option.getD_some, Bool.or_eq_true] at hget
        rcases hget with h | h
        · exact Or.inl ⟨hlt, by simpa using F.isP_piece hlt h⟩
        · exact Or.inr ⟨hlt, by simpa using F.isP_piece hlt h⟩
      next => simp at hget
  obtain ⟨st, e, I⟩ := P.loop (List.range c.nS) (4 * c.nS) I0
  refine ⟨PFR.mk ((⟨D.motion a, c.mkTab a (D.motion a)⟩ : Pack), (⟨D.motion b, c.mkTab b (D.motion b)⟩ : Pack))
      (bitsUpTo (get st.forced) c.nS)
      (bitsUpTo (fun p => get st.alive (eIdx p false) || get st.alive (eIdx p true)) c.nS),
    ?_, rfl, ?_, ?_, ?_⟩
  · unfold pairForce
    simp only
    rw [show pfLoop _ _ _ _ _ _ = some st from e]
  · intro p hp hor
    simp only [testBit_bitsUpTo, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true]
    refine ⟨hp, ?_⟩
    rcases hor with h | h
    · exact Or.inl (I.alive p false ⟨hp, by simpa using h⟩)
    · exact Or.inr (I.alive p true ⟨hp, by simpa using h⟩)
  · intro p hp
    simp only [testBit_bitsUpTo, Bool.and_eq_false_iff, decide_eq_false_iff_not]
    exact Or.inl (by omega)
  · intro p hp
    simp only [testBit_bitsUpTo, Bool.and_eq_true, decide_eq_true_eq] at hp
    rcases I.forced p hp.2 with h | h
    · left; simpa using h.2
    · right; simpa using h.2

theorem Fits.check22G_false (F : Fits c D) {a b e d : Fin 4}
    (hall : ∀ k : Fin 4, k = a ∨ k = b ∨ k = e ∨ k = d)
    (hd : a ≠ e ∧ a ≠ d ∧ b ≠ e ∧ b ≠ d)
    (h1 : a ≠ b) (h2 : e ≠ d) (s1 : c.side a = c.side b) (s2 : c.side e = c.side d)
    (g1 : ∀ j, c.side j = c.side a → j = a ∨ j = b) (g2 : ∀ j, c.side j = c.side e → j = e ∨ j = d)
    {ord : Tab → Tab → Tab → Tab → Q} {test : Cfg → Q → List Nat → List Nat → Bool}
    (ht : test c (ord (c.mkTab a (D.motion a)) (c.mkTab b (D.motion b)) (c.mkTab e (D.motion e))
      (c.mkTab d (D.motion d))) (List.range c.nS) (List.range c.nT) = false)
    (h : check22G c a b e d ord test = true) : False := by
  have hs : ∀ (f : Unit → List PFR), (Task.spawn f).get = f () := fun _ => rfl
  simp only [check22G, persist_eq, hs, parAll_eq, parMap_eq, List.all_eq_true,
    show pvOf c.pv4 = c.mkPv from rfl] at h
  obtain ⟨x, ex, xp, xa, xb, xf⟩ := F.pairForce_true h1 g1 s1
  obtain ⟨y, ey, yp, ya, yb, yf⟩ := F.pairForce_true h2 g2 s2
  have mx : x ∈ ((c.pairs c.mkPv (c.mkPT c.mkPv) a b).map (pairForce c.nS (c.mkPT c.mkPv) a b
      (otherTab c.nS (c.mkPT c.mkPv) a) (otherTab c.nS (c.mkPT c.mkPv) b) ((List.range c.nT).filter fun j => decide (j < c.u * c.u) == c.side a) (List.range c.nS))).filterMap id :=
    List.mem_filterMap.2 ⟨_, List.mem_map.2 ⟨_, F.pair_mem h1 s1 g1, ex⟩, rfl⟩
  have my : y ∈ ((c.pairs c.mkPv (c.mkPT c.mkPv) e d).map (pairForce c.nS (c.mkPT c.mkPv) e d
      (otherTab c.nS (c.mkPT c.mkPv) e) (otherTab c.nS (c.mkPT c.mkPv) d) ((List.range c.nT).filter fun j => decide (j < c.u * c.u) == c.side e) (List.range c.nS))).filterMap id :=
    List.mem_filterMap.2 ⟨_, List.mem_map.2 ⟨_, F.pair_mem h2 s2 g2, ey⟩, rfl⟩
  have key := h x mx y my
  have z1 : (x.F &&& y.F) = 0 := by
    apply Nat.eq_of_testBit_eq
    intro p
    simp only [Nat.testBit_and, Nat.zero_testBit, Bool.and_eq_false_iff]
    by_cases hx : x.F.testBit p = true
    · right
      rw [Bool.eq_false_iff]
      intro hy
      rcases xf p hx with e1 | e1 <;> rcases yf p hy with e2 | e2 <;> rw [e1] at e2
      · exact hd.1 e2
      · exact hd.2.1 e2
      · exact hd.2.2.1 e2
      · exact hd.2.2.2 e2
    · left; simpa using hx
  have z2 : (x.AL ||| y.AL) = bitsUpTo (fun _ => true) c.nS := by
    apply Nat.eq_of_testBit_eq
    intro p
    rw [testBit_bitsUpTo, Nat.testBit_or]
    by_cases hp : p < c.nS
    · simp only [hp, decide_true, Bool.and_true, Bool.or_eq_true]
      rcases hall (D.piece (p / c.w) (p % c.w)) with e1 | e1 | e1 | e1
      · rw [xa p hp (Or.inl e1)]; simp
      · rw [xa p hp (Or.inr e1)]; simp
      · rw [ya p hp (Or.inl e1)]; simp
      · rw [ya p hp (Or.inr e1)]; simp
    · have hge : c.nS ≤ p := by omega
      simp [xb p hge, yb p hge, hp]
  simp only [z1, z2, xp, yp, ht] at key
  simp at key

theorem Fits.check22_false (F : Fits c D) {a b e d : Fin 4}
    (hall : ∀ k : Fin 4, k = a ∨ k = b ∨ k = e ∨ k = d)
    (hd : a ≠ e ∧ a ≠ d ∧ b ≠ e ∧ b ≠ d)
    (h1 : a ≠ b) (h2 : e ≠ d) (s1 : c.side a = c.side b) (s2 : c.side e = c.side d)
    (g1 : ∀ j, c.side j = c.side a → j = a ∨ j = b) (g2 : ∀ j, c.side j = c.side e → j = e ∨ j = d)
    (h : check22 c a b e d = true) : False :=
  F.check22G_false hall hd h1 h2 s1 s2 g1 g2 (F.not_dead _ (by
      intro k
      rcases hall k with rfl | rfl | rfl | rfl <;> simp)) h

theorem get_maskOf {n w : Nat} (hn : 0 < n) {l : List Pack} {p : Pack} (hp : p ∈ l) :
    get (maskOf n w l) (motionId w p.m % n) = true := by
  have key : ∀ (l : List Pack) (a : Array Bool), a.size = n →
      (p ∈ l ∨ get a (motionId w p.m % n) = true) →
      get (l.foldl (fun a p => set a (motionId w p.m % n)) a) (motionId w p.m % n) = true := by
    intro l
    induction l with
    | nil =>
      intro a _ h
      simpa using h
    | cons r l ih =>
      intro a ha h
      simp only [List.foldl_cons]
      apply ih _ (by rw [size_set]; exact ha)
      by_cases hr : p ∈ l
      · exact Or.inl hr
      · right
        have hi : motionId w r.m % n < a.size := by rw [ha]; exact Nat.mod_lt _ hn
        rw [get_set hi]
        rcases h with h | h
        · simp only [List.mem_cons] at h
          rcases h with h | h
          · subst h; simp
          · exact absurd h hr
        · simp [h]
  exact key l _ (by simp) (Or.inl hp)

/-- A cell with an image under the identity of slot 0 belongs to slot 0. -/
theorem Fits.t0_piece (F : Fits c D) (hf : c.fixed 0 = true) (g0 : ∀ j, c.side j = c.side 0 → j = 0)
    {i : Nat} (hi : i < c.w * c.w) (h : (c.mkTab 0 idMotion).img.getD i 0 ≠ 0) :
    D.piece (i / c.w) (i % c.w) = 0 := by
  have h0 := F.hfix 0 hf
  obtain ⟨hx, hy, _⟩ := code_split hi
  rw [mkTab_img c 0 idMotion hi] at h
  split at h
  next hin =>
    have hS := (inSq_iff _ _ _).1 hin
    obtain ⟨m1, m2, m3, m4⟩ := hS
    have ex : idMotion.imgX c.w (i / c.w) (i % c.w) = ((i / c.w : Nat) : Int) := by
      simp [idMotion, Motion.imgX]
    have ey : idMotion.imgY c.w (i / c.w) (i % c.w) = ((i % c.w : Nat) : Int) := by
      simp [idMotion, Motion.imgY]
    rw [ex] at m1 m2
    rw [ey] at m3 m4
    have hSq : InSquare (if c.side 0 then c.u else c.v) ((i / c.w : Nat) : Int) ((i % c.w : Nat) : Int) := by
      have hs : c.S 0 = if c.side 0 then c.u else c.v := by
        simp only [Cfg.S, sideOf]
      rw [hs] at m2 m4
      exact ⟨m1, m2, m3, m4⟩
    obtain ⟨x, y, hx', hy', hc, h1, h2⟩ := D.surjective (c.side 0) _ _ hSq
    rw [F.hside] at hc
    have hp := g0 _ hc
    rw [hp, h0] at h1 h2
    have e1 : x = i / c.w := by
      simp only [idMotion, Motion.imgX] at h1
      simp at h1
      omega
    have e2 : y = i % c.w := by
      simp only [idMotion, Motion.imgY] at h2
      simp at h2
      omega
    rw [← e1, ← e2]
    exact hp
  next => simp at h

/-- Every number is reached by one of the four true motions. -/
theorem Fits.missQ_false (F : Fits c D) (hf : c.fixed 0 = true) (g0 : ∀ j, c.side j = c.side 0 → j = 0)
    (e : Nat) :
    missQ c.nS (c.nS + c.nT) (c.mkTab 0 idMotion) (c.mkTab 1 (D.motion 1)) (c.mkTab 2 (D.motion 2))
      (c.mkTab 3 (D.motion 3)) e = false := by
  have h0 := F.hfix 0 hf
  rw [Bool.eq_false_iff]
  intro hm
  simp only [missQ, uncov, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hm
  obtain ⟨⟨⟨⟨hN, a0⟩, a1⟩, a3⟩, a2⟩ := hm
  by_cases he : e < c.nS
  · have hval := F.img_true (i := e) he (k := D.piece (e / c.w) (e % c.w)) rfl
    have hne : (c.mkTab (D.piece (e / c.w) (e % c.w)) (D.motion (D.piece (e / c.w) (e % c.w)))).img.getD e 0 ≠ 0 := by
      rw [hval]; omega
    generalize D.piece (e / c.w) (e % c.w) = k at hne
    simp only [hitE, hitL, he, if_true, bne_eq_false_iff_eq] at a0 a1 a2 a3
    revert k
    apply slot_cases <;> intro hne
    · rw [h0] at hne; exact hne a0
    · exact hne a1
    · exact hne a2
    · exact hne a3
  · have hj : e - c.nS < c.u * c.u + c.v * c.v := by
      have : c.nT = c.u * c.u + c.v * c.v := rfl
      omega
    obtain ⟨x, y, hx, hy, _, hpre⟩ := F.true_pre hj
    have hlt := code_lt hx hy
    obtain ⟨_, q2, q3⟩ := code_split hlt
    have ee := code_inj hy q2 (q3.symm : x * c.w + y = _)
    have hz : D.piece x y ≠ 0 → (c.mkTab 0 idMotion).img.getD (x * c.w + y) 0 = 0 := by
      intro hk
      apply Classical.byContradiction
      intro hn
      apply hk
      have := F.t0_piece hf g0 hlt hn
      rwa [← ee.1, ← ee.2] at this
    generalize D.piece x y = k at hpre hz
    simp only [hitE, hitL, he, if_false, Bool.and_eq_false_iff, bne_eq_false_iff_eq,
      beq_eq_false_iff_ne, ne_eq] at a0 a1 a2 a3
    revert k
    apply slot_cases <;> intro hpre hz
    · rw [h0] at hpre; rw [hpre] at a0; simp at a0
    · rw [hpre] at a1
      rcases a1 with a1 | a1
      · simp at a1
      · exact a1 (by simpa using hz (by decide))
    · rw [hpre] at a2
      rcases a2 with a2 | a2
      · simp at a2
      · exact a2 (by simpa using hz (by decide))
    · rw [hpre] at a3
      rcases a3 with a3 | a3
      · simp at a3
      · exact a3 (by simpa using hz (by decide))

/-- A target cell that slot 0 does not reach comes from a cell of another slot. -/
theorem Fits.target_slot (F : Fits c D) (hf : c.fixed 0 = true) (g0 : ∀ j, c.side j = c.side 0 → j = 0)
    {e : Nat} (h1 : c.nS ≤ e) (h2 : e < c.nS + c.nT)
    (h3 : hitE c.nS (c.mkTab 0 idMotion) e = false) :
    ∃ (p : Nat) (k : Fin 4), D.piece (p / c.w) (p % c.w) = k ∧ k ≠ 0 ∧
      (c.mkTab k (D.motion k)).pre.getD (e - c.nS) 0 = p + 1 ∧
      hitL c.nS (c.mkTab 0 idMotion) (c.mkTab k (D.motion k)) e = true := by
  have h0 := F.hfix 0 hf
  have hj : e - c.nS < c.u * c.u + c.v * c.v := by
    have : c.nT = c.u * c.u + c.v * c.v := rfl
    omega
  obtain ⟨x, y, hx, hy, _, hpre⟩ := F.true_pre hj
  have hlt := code_lt hx hy
  obtain ⟨_, q2, q3⟩ := code_split hlt
  have ee := code_inj hy q2 (q3.symm : x * c.w + y = _)
  have hk0 : D.piece x y ≠ 0 := by
    intro hk
    rw [hk, h0] at hpre
    have he : ¬ e < c.nS := by omega
    simp only [hitE, he, if_false, bne_eq_false_iff_eq] at h3
    rw [hpre] at h3
    simp at h3
  have hz : (c.mkTab 0 idMotion).img.getD (x * c.w + y) 0 = 0 := by
    apply Classical.byContradiction
    intro hn
    apply hk0
    have := F.t0_piece hf g0 hlt hn
    rwa [← ee.1, ← ee.2] at this
  refine ⟨x * c.w + y, D.piece x y, by rw [← ee.1, ← ee.2], hk0, hpre, ?_⟩
  have he : ¬ e < c.nS := by omega
  simp [hitL, he, hpre, hz]

/-- The source form of a collision: slot 2 reaches one of the two cells. -/
theorem Fits.collS_true (F : Fits c D) (hf : c.fixed 0 = true) {c1 c3 : Nat}
    (h : collS c.nS (c.mkTab 0 idMotion) (c.mkTab 1 (D.motion 1)) (c.mkTab 3 (D.motion 3)) c1 c3 = true) :
    hitL c.nS (c.mkTab 0 idMotion) (c.mkTab 2 (D.motion 2)) c1 = true ∨
    hitL c.nS (c.mkTab 0 idMotion) (c.mkTab 2 (D.motion 2)) c3 = true := by
  have h0 := F.hfix 0 hf
  simp only [collS, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨l1, l3⟩, hne⟩, z1⟩, z3⟩, a1⟩, a3⟩, b3⟩, b1⟩, heq⟩ := h
  apply Classical.byContradiction
  intro hn
  simp only [not_or, Bool.not_eq_true] at hn
  obtain ⟨n1, n3⟩ := hn
  simp only [hitL, l1, l3, if_true, bne_eq_false_iff_eq] at n1 n3
  have slot1 : D.piece (c1 / c.w) (c1 % c.w) = 1 := by
    have hval := F.img_true (i := c1) l1 (k := D.piece (c1 / c.w) (c1 % c.w)) rfl
    have hne0 : (c.mkTab (D.piece (c1 / c.w) (c1 % c.w)) (D.motion (D.piece (c1 / c.w) (c1 % c.w)))).img.getD c1 0 ≠ 0 := by
      rw [hval]; omega
    generalize D.piece (c1 / c.w) (c1 % c.w) = k at hne0
    revert k
    apply slot_cases <;> intro hne0
    · rw [h0] at hne0; exact absurd z1 hne0
    · rfl
    · exact absurd n1 hne0
    · exact absurd a3 hne0
  have slot3 : D.piece (c3 / c.w) (c3 % c.w) = 3 := by
    have hval := F.img_true (i := c3) l3 (k := D.piece (c3 / c.w) (c3 % c.w)) rfl
    have hne0 : (c.mkTab (D.piece (c3 / c.w) (c3 % c.w)) (D.motion (D.piece (c3 / c.w) (c3 % c.w)))).img.getD c3 0 ≠ 0 := by
      rw [hval]; omega
    generalize D.piece (c3 / c.w) (c3 % c.w) = k at hne0
    revert k
    apply slot_cases <;> intro hne0
    · rw [h0] at hne0; exact absurd z3 hne0
    · exact absurd b1 hne0
    · exact absurd n3 hne0
    · rfl
  have v1 := F.img_true (i := c1) l1 slot1
  have v3 := F.img_true (i := c3) l3 slot3
  rw [v1, v3] at heq
  have G := F.graph ⟨c.mkTab 0 (D.motion 0), c.mkTab 1 (D.motion 1), c.mkTab 2 (D.motion 2),
    c.mkTab 3 (D.motion 3)⟩ (by apply slot_cases <;> simp)
  have e1 := F.trueEdge (i := c1) l1
  have e3 := F.trueEdge (i := c3) l3
  have ee : trueTau c D c1 = trueTau c D c3 := by omega
  rw [← ee] at e3
  exact hne (G.inj _ _ _ e1 e3)

/-- The target form of a collision: slot 2 reaches one of the two target cells. -/
theorem Fits.collT_true (F : Fits c D) (hf : c.fixed 0 = true) (g0 : ∀ j, c.side j = c.side 0 → j = 0)
    {e1 e3 : Nat}
    (h : collT c.nS (c.nS + c.nT) (c.mkTab 0 idMotion) (c.mkTab 1 (D.motion 1)) (c.mkTab 3 (D.motion 3)) e1 e3 = true) :
    hitL c.nS (c.mkTab 0 idMotion) (c.mkTab 2 (D.motion 2)) e1 = true ∨
    hitL c.nS (c.mkTab 0 idMotion) (c.mkTab 2 (D.motion 2)) e3 = true := by
  simp only [collT, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', bne_iff_ne, ne_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨l1, l3⟩, u1⟩, u3⟩, n01⟩, n03⟩, n31⟩, n13⟩, hp0⟩, heq⟩ := h
  apply Classical.byContradiction
  intro hn
  simp only [not_or, Bool.not_eq_true] at hn
  obtain ⟨n1, n3⟩ := hn
  obtain ⟨p, k, ep, hk, hpre, hhit⟩ := F.target_slot hf g0 l1 u1 n01
  obtain ⟨p', k', ep', hk', hpre', hhit'⟩ := F.target_slot hf g0 l3 u3 n03
  have k1 : k = 1 := by
    revert ep hk hpre hhit
    revert k
    apply slot_cases <;> intro _ hk _ hhit
    · exact absurd rfl hk
    · rfl
    · rw [n1] at hhit; simp at hhit
    · rw [n31] at hhit; simp at hhit
  have k3 : k' = 3 := by
    revert ep' hk' hpre' hhit'
    revert k'
    apply slot_cases <;> intro _ hk _ hhit
    · exact absurd rfl hk
    · rw [n13] at hhit; simp at hhit
    · rw [n3] at hhit; simp at hhit
    · rfl
  subst k1 k3
  rw [hpre, hpre'] at heq
  have : p = p' := by omega
  subst this
  rw [ep] at ep'
  exact absurd ep' (by decide)

theorem testBit_applyColl {n N : Nat} {t0 t1 t3 : Tab} {cols : Array Nat} {j : Nat}
    (hP : ∀ e, collOK n N t0 t1 t3 e = true →
      (cols.getD e.1 0).testBit j = true ∨ (cols.getD e.2 0).testBit j = true)
    (l : List (Nat × Nat)) {al : Nat} (h : al.testBit j = true) :
    (l.foldl (applyColl n N t0 t1 t3 cols) al).testBit j = true := by
  induction l generalizing al with
  | nil => exact h
  | cons e l ih =>
    simp only [List.foldl_cons]
    apply ih
    unfold applyColl
    split
    next hc =>
      simp only [Bool.and_eq_true] at hc
      rw [Nat.testBit_and, h, Nat.testBit_or, Bool.true_and]
      rcases hP e hc.2 with h' | h'
      · rw [h']; rfl
      · rw [h', Bool.or_true]
    next => exact h

theorem testBit_colBits {A : Array PB} {f : PB → Bool} {j : Nat} {p : PB} (h : A[j]? = some p)
    (hf : f p = true) : (colBits A f).testBit j = true := by
  obtain ⟨hlt, e⟩ := Array.getElem?_eq_some_iff.1 h
  simp [colBits, testBit_bitsUpTo, hlt, e, hf]

theorem testBit_narrowOne {n N : Nat} {t0 t1 t3 : Tab} {cols : Array Nat} {j : Nat}
    (hP : ∀ e, uncov n N t0 t1 t3 e = true → (cols.getD e 0).testBit j = true) (e : Nat)
    {al : Nat} (h : al.testBit j = true) : (narrowOne n N t0 t1 t3 cols al e).testBit j = true := by
  unfold narrowOne
  split
  next hu =>
    rw [Nat.testBit_and, h, hP e hu]
    rfl
  next => exact h

theorem testBit_narrowWord {n N : Nat} {t0 t1 t3 : Tab} {cols : Array Nat} {j : Nat}
    (hP : ∀ e, uncov n N t0 t1 t3 e = true → (cols.getD e 0).testBit j = true) (k b w : Nat)
    {al : Nat} (h : al.testBit j = true) : (narrowWord n N t0 t1 t3 cols k b w al).testBit j = true := by
  induction k generalizing al w with
  | zero => exact h
  | succ k ih =>
    simp only [narrowWord]
    split
    · exact h
    · exact ih _ (testBit_narrowOne hP _ h)

theorem testBit_narrowW {n N : Nat} {t0 t1 t3 : Tab} {cols fw a c : Array Nat} {j : Nat}
    (hP : ∀ e, uncov n N t0 t1 t3 e = true → (cols.getD e 0).testBit j = true) (i : Nat)
    {al : Nat} (h : al.testBit j = true) : (narrowW n N t0 t1 t3 cols fw a c i al).testBit j = true := by
  induction i generalizing al with
  | zero => exact h
  | succ i ih =>
    simp only [narrowW]
    split
    · exact h
    · exact ih (testBit_narrowWord hP _ _ _ h)

theorem allBits_sound {f : Nat → Bool} {k r : Nat} (h : allBits f k r = true) {j : Nat}
    (hj : r.testBit j = true) : f j = true := by
  induction k generalizing r with
  | zero =>
    have : r = 0 := by simpa [allBits] using h
    subst this
    simp at hj
  | succ k ih =>
    simp only [allBits] at h
    split at h
    next h0 =>
      have : r = 0 := by simpa using h0
      subst this
      simp at hj
    next =>
      simp only [Bool.and_eq_true] at h
      by_cases e : j = r.log2
      · rw [e]; exact h.1
      · apply ih h.2
        rw [Nat.testBit_xor, hj, Nat.one_shiftLeft, Nat.testBit_two_pow]
        simp [Ne.symm e]

theorem Fits.check13G_false (F : Fits c D)
    (s1 : c.side 1 = c.side 2) (s2 : c.side 1 = c.side 3)
    (g : ∀ j, c.side j = c.side 1 → j = 1 ∨ j = 2 ∨ j = 3) (hf : c.fixed 0 = true)
    (h01 : c.side 0 ≠ c.side 1)
    {test : Cfg → Q → List Nat → List Nat → Bool}
    (ht : test c ⟨c.mkTab 0 idMotion, c.mkTab 1 (D.motion 1), c.mkTab 2 (D.motion 2),
      c.mkTab 3 (D.motion 3)⟩ (List.range c.nS) (List.range c.nT) = false)
    (h : check13G c test = true) : False := by
  simp only [check13G, persist_eq, parAll_eq, parMap_eq, List.all_eq_true,
    show pvOf c.pv4 = c.mkPv from rfl] at h
  have g0 : ∀ j, c.side j = c.side 0 → j = 0 := by
    apply slot_cases <;> intro hj
    · rfl
    · exact absurd hj.symm h01
    · rw [← s1] at hj; exact absurd hj.symm h01
    · rw [← s2] at hj; exact absurd hj.symm h01
  have hm := F.missQ_false hf g0
  have hw : ∀ r, witQ c.nS (c.nS + c.nT) (c.mkTab 0 idMotion) (c.mkTab 1 (D.motion 1)) (c.mkTab 2 (D.motion 2))
      (c.mkTab 3 (D.motion 3)) r = false := by
    intro r
    cases r with
    | none => rfl
    | some e => exact hm e
  let P1 : Pack := ⟨D.motion 1, c.mkTab 1 (D.motion 1)⟩
  let P2 : Pack := ⟨D.motion 2, c.mkTab 2 (D.motion 2)⟩
  let P3 : Pack := ⟨D.motion 3, c.mkTab 3 (D.motion 3)⟩
  let pt := c.mkPT c.mkPv
  let bit : Pack → PB := fun p => mkPB (c.nS + c.nT) p (hitL c.nS (c.mkTab 0 idMotion) p.t)
  let A : Array PB := ((c.packs c.mkPv 2).map bit).toArray
  have h31 : P3 ∈ (c.packs c.mkPv 3).filter fun p3 => ptd pt 3 1 p3.t P1.t :=
    List.mem_filter.2 ⟨F.pack_mem 3, F.ptd_true (by decide) (by rw [s2])⟩
  have hc : cornersOk (c.tcorners 1) [P1.t, P2.t, P3.t] = true := F.corners_true 1 (by
    intro j hj
    rcases g j hj with rfl | rfl | rfl <;> simp [P1, P2, P3])
  have hp12 : ptd pt 1 2 P1.t P2.t = true := F.ptd_true (by decide) s1
  have hp32 : ptd pt 3 2 P3.t P2.t = true := F.ptd_true (by decide) (by rw [← s2, s1])
  -- The place of the true placement of slot 2.
  obtain ⟨j0, hj0⟩ : ∃ j, A[j]? = some (bit P2) := by
    have : bit P2 ∈ A := by
      simpa [A] using List.mem_map.2 ⟨P2, F.pack_mem 2, rfl⟩
    obtain ⟨j, hj⟩ := Array.mem_iff_getElem?.1 this
    exact ⟨j, hj⟩
  let y3 : PB × Nat := (bit P3, colBits A fun p => ptd pt 3 2 P3.t p.p.t)
  have hE : y3 ∈ (c.packs c.mkPv 3).map (fun p3 => (bit p3, colBits A fun p => ptd pt 3 2 p3.t p.p.t)) :=
    List.mem_map.2 ⟨P3, F.pack_mem 3, rfl⟩
  have hE2 : y3 ∈ (chunksF 256 ((c.packs c.mkPv 3).map
      (fun p3 => (bit p3, colBits A fun p => ptd pt 3 2 p3.t p.p.t))).length
      ((c.packs c.mkPv 3).map (fun p3 => (bit p3, colBits A fun p => ptd pt 3 2 p3.t p.p.t)))).flatten := by
    rw [flatten_chunksF]; exact hE
  obtain ⟨ch, hch, he⟩ := List.mem_flatten.1 hE2
  have := h ((bit P1, colBits A (fun p => ptd pt 1 2 P1.t p.p.t),
      maskOf (32 * c.w * c.w + 8) c.w ((c.packs c.mkPv 3).filter fun p3 => ptd pt 3 1 p3.t P1.t)), ch)
    (List.mem_flatMap.2 ⟨_, List.mem_map.2 ⟨P1, F.pack_mem 1, rfl⟩, List.mem_map.2 ⟨ch, hch, rfl⟩⟩) _ he
  have hmask : get (maskOf (32 * c.w * c.w + 8) c.w ((c.packs c.mkPv 3).filter
      fun p3 => ptd pt 3 1 p3.t P1.t)) (motionId c.w y3.1.p.m % (32 * c.w * c.w + 8)) = true :=
    get_maskOf (n := 32 * c.w * c.w + 8) (w := c.w) (by omega) h31
  simp only [hmask, Bool.not_true, Bool.false_or] at this
  -- The true placement of slot 2 survives the narrowing.
  have hbitOf : ∀ {e}, e < c.nS + c.nT → hitL c.nS (c.mkTab 0 idMotion) (c.mkTab 2 (D.motion 2)) e = true →
      (((List.range (c.nS + c.nT)).map fun e => colBits A fun p =>
        hitL c.nS (c.mkTab 0 idMotion) p.p.t e).toArray.getD e 0).testBit j0 = true := by
    intro e hlt hit
    rw [Array.getD_eq_getD_getElem?]
    simp only [List.getElem?_toArray, List.getElem?_map, List.getElem?_range hlt, Option.map_some,
      Option.getD_some]
    exact testBit_colBits hj0 hit
  have hcol : ∀ e, uncov c.nS (c.nS + c.nT) (c.mkTab 0 idMotion) P1.t P3.t e = true →
      (((List.range (c.nS + c.nT)).map fun e => colBits A fun p =>
        hitL c.nS (c.mkTab 0 idMotion) p.p.t e).toArray.getD e 0).testBit j0 = true := by
    intro e hu
    have hlt : e < c.nS + c.nT := by
      simp only [uncov, Bool.and_eq_true, decide_eq_true_eq] at hu
      exact hu.1.1.1
    have hh : uncov c.nS (c.nS + c.nT) (c.mkTab 0 idMotion) (c.mkTab 1 (D.motion 1))
        (c.mkTab 3 (D.motion 3)) e = true := hu
    have hit := hm e
    simp only [missQ, hh, Bool.true_and, Bool.not_eq_false'] at hit
    exact hbitOf hlt hit
  have hbit0 : ∀ fw a c' i, _ := fun fw a c' i => testBit_narrowW (fw := fw) (a := a) (c := c') hcol i
    (al := colBits A (fun p => ptd pt 1 2 P1.t p.p.t) &&& colBits A (fun p => ptd pt 3 2 P3.t p.p.t)) (by
      rw [Nat.testBit_and, testBit_colBits hj0 hp12, testBit_colBits hj0 hp32]
      rfl)
  have hbit2 : ∀ al, al.testBit j0 = true → (if (al == 0) = true then 0 else
      (collList c.nS c.nT (c.mkTab 0 idMotion) P1.t P3.t).foldl
        (applyColl c.nS (c.nS + c.nT) (c.mkTab 0 idMotion) P1.t P3.t
          ((List.range (c.nS + c.nT)).map fun e => colBits A fun p =>
            hitL c.nS (c.mkTab 0 idMotion) p.p.t e).toArray) al).testBit j0 = true := by
    intro al hal
    have hne : ¬ (al == 0) = true := by
      intro h0
      have : al = 0 := by simpa using h0
      subst this
      simp at hal
    rw [if_neg hne]
    apply testBit_applyColl _ _ hal
    intro e hc
    simp only [collOK, Bool.or_eq_true] at hc
    rcases hc with hc | hc
    · have hS : collS c.nS (c.mkTab 0 idMotion) (c.mkTab 1 (D.motion 1)) (c.mkTab 3 (D.motion 3)) e.1 e.2 = true := hc
      have l13 : e.1 < c.nS ∧ e.2 < c.nS := by
        simp only [collS, Bool.and_eq_true, decide_eq_true_eq] at hS
        exact hS.1.1.1.1.1.1.1.1
      rcases F.collS_true hf hS with h' | h'
      · exact Or.inl (hbitOf (by omega) h')
      · exact Or.inr (hbitOf (by omega) h')
    · have hT : collT c.nS (c.nS + c.nT) (c.mkTab 0 idMotion) (c.mkTab 1 (D.motion 1)) (c.mkTab 3 (D.motion 3)) e.1 e.2 = true := hc
      have l13 : e.1 < c.nS + c.nT ∧ e.2 < c.nS + c.nT := by
        simp only [collT, Bool.and_eq_true, decide_eq_true_eq] at hT
        exact ⟨hT.1.1.1.1.1.1.1.2, hT.1.1.1.1.1.1.2⟩
      rcases F.collT_true hf g0 hT with h' | h'
      · exact Or.inl (hbitOf l13.1 h')
      · exact Or.inr (hbitOf l13.2 h')
  have key := allBits_sound this (hbit2 _ (hbit0 _ _ _ _))
  have hj1 : ((c.packs c.mkPv 2).map bit).toArray[j0]? = some (bit P2) := hj0
  simp only [bit] at hj1 key
  simp only [hj1] at key
  simp only [bit, mkPB, P1, P2, P3, y3] at key hc
  simp only [hw, hc, ht] at key
  simp at key

theorem Fits.check13_false (F : Fits c D)
    (s1 : c.side 1 = c.side 2) (s2 : c.side 1 = c.side 3)
    (g : ∀ j, c.side j = c.side 1 → j = 1 ∨ j = 2 ∨ j = 3) (hf : c.fixed 0 = true)
    (h01 : c.side 0 ≠ c.side 1)
    (h : check13 c = true) : False := by
  have h0 := F.hfix 0 hf
  refine F.check13G_false s1 s2 g hf h01 ?_ h
  apply F.not_dead
  intro k
  revert k
  apply slot_cases <;> simp [h0]

end Ex89
