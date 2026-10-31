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
    simp only [List.mem_filter, Bool.and_eq_true, List.all_eq_true]
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
  simp only [Cfg.pairs, List.mem_flatMap, List.mem_map, List.mem_filter, Bool.and_eq_true, Prod.mk.injEq]
  refine ⟨_, F.pack_mem a, _, ⟨F.pack_mem b, F.ptd_true hne hs, ?_⟩, rfl, rfl⟩
  apply F.corners_true
  intro j hj
  rcases hgroup j hj with rfl | rfl <;> simp

theorem Fits.check22_false (F : Fits c D) {a b e d : Fin 4}
    (hall : ∀ k : Fin 4, k = a ∨ k = b ∨ k = e ∨ k = d)
    (h1 : a ≠ b) (h2 : e ≠ d) (s1 : c.side a = c.side b) (s2 : c.side e = c.side d)
    (g1 : ∀ j, c.side j = c.side a → j = a ∨ j = b) (g2 : ∀ j, c.side j = c.side e → j = e ∨ j = d)
    (h : check22 c a b e d = true) : False := by
  have hs : ∀ (f : Unit → List (Pack × Pack)), (Task.spawn f).get = f () := fun _ => rfl
  simp only [check22, hs, parAll_eq, List.all_eq_true] at h
  have := h _ (F.pair_mem h1 s1 g1) _ (F.pair_mem h2 s2 g2)
  have hd := F.not_dead ⟨c.mkTab a (D.motion a), c.mkTab b (D.motion b), c.mkTab e (D.motion e),
    c.mkTab d (D.motion d)⟩ (by
      intro k
      rcases hall k with rfl | rfl | rfl | rfl <;> simp)
  simp_all

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

theorem Fits.check13_false (F : Fits c D)
    (s1 : c.side 1 = c.side 2) (s2 : c.side 1 = c.side 3)
    (g : ∀ j, c.side j = c.side 1 → j = 1 ∨ j = 2 ∨ j = 3) (hf : c.fixed 0 = true)
    (h : check13 c = true) : False := by
  simp only [check13, parAll_eq, parMap_eq, List.all_eq_true, List.mem_map] at h
  have hd := F.not_dead ⟨c.mkTab 0 (D.motion 0), c.mkTab 1 (D.motion 1), c.mkTab 2 (D.motion 2),
    c.mkTab 3 (D.motion 3)⟩ (by
      intro k
      revert k
      apply slot_cases <;> simp)
  have h0 := F.hfix 0 hf
  rw [h0] at hd
  let P1 : Pack := ⟨D.motion 1, c.mkTab 1 (D.motion 1)⟩
  let P2 : Pack := ⟨D.motion 2, c.mkTab 2 (D.motion 2)⟩
  let P3 : Pack := ⟨D.motion 3, c.mkTab 3 (D.motion 3)⟩
  have h31 : P3 ∈ (c.packs c.mkPv 3).filter fun p3 => ptd (c.mkPT c.mkPv) 3 1 p3.t P1.t :=
    List.mem_filter.2 ⟨F.pack_mem 3, F.ptd_true (by decide) (by rw [s2])⟩
  have h32 : P3 ∈ (c.packs c.mkPv 3).filter fun p3 => ptd (c.mkPT c.mkPv) 3 2 p3.t P2.t :=
    List.mem_filter.2 ⟨F.pack_mem 3, F.ptd_true (by decide) (by rw [← s2, s1])⟩
  have hc : cornersOk (c.tcorners 1) [P1.t, P2.t, P3.t] = true := F.corners_true 1 (by
    intro j hj
    rcases g j hj with rfl | rfl | rfl <;> simp [P1, P2, P3])
  have hp12 : ptd (c.mkPT c.mkPv) 1 2 P1.t P2.t = true := F.ptd_true (by decide) s1
  have := h P1 (F.pack_mem 1) _ ⟨P2, F.pack_mem 2, rfl⟩
  simp only [hp12, Bool.not_true, Bool.false_or, List.all_eq_true] at this
  have := this P3 h32
  rw [get_maskOf (by omega) h31, hc] at this
  simp only [Bool.not_true, Bool.false_or] at this
  rw [hd] at this
  simp at this

end Ex89
