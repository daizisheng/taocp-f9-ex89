import Ex89.Check
/-!
Soundness of propagation. This part has no geometry. Let `R i j` be a bijection between source
cells and target cells, such that each true edge appears in some table. Then `dead` cannot return
`true`.
-/
namespace Ex89

theorem get_set {a : Array Bool} {i j : Nat} (h : i < a.size) :
    get (set a i) j = (j == i || get a j) := by
  by_cases e : j = i
  · subst e
    simp [get, set, h]
  · simp [get, set, Array.getD_eq_getD_getElem?, e, Ne.symm e]

theorem size_set (a : Array Bool) (i : Nat) : (set a i).size = a.size := by
  simp [set]

/-- The true edges, with the tables that contain them. -/
structure Graph (q : Q) (nS nT : Nat) (R : Nat → Nat → Prop) : Prop where
  fwd : ∀ i, i < nS → ∃ j, j < nT ∧ R i j ∧
    (j + 1) ∈ [q.t0.img.getD i 0, q.t1.img.getD i 0, q.t2.img.getD i 0, q.t3.img.getD i 0]
  bwd : ∀ j, j < nT → ∃ i, i < nS ∧ R i j ∧
    (i + 1) ∈ [q.t0.pre.getD j 0, q.t1.pre.getD j 0, q.t2.pre.getD j 0, q.t3.pre.getD j 0]
  func : ∀ i j j', R i j → R i j' → j = j'
  inj : ∀ i i' j, R i j → R i' j → i = i'

/-- The invariant: an edge is known at one end if and only if it is known at the other end. -/
structure Inv (nS nT : Nat) (R : Nat → Nat → Prop) (st : St) : Prop where
  szS : st.mS.size = nS
  szT : st.mT.size = nT
  eqv : ∀ i j, i < nS → j < nT → R i j → get st.mS i = get st.mT j

theorem Inv.add {nS nT : Nat} {R : Nat → Nat → Prop} {st : St} (h : Inv nS nT R st)
    (func : ∀ i j j', R i j → R i j' → j = j') (inj : ∀ i i' j, R i j → R i' j → i = i')
    {i j : Nat} (hi : i < nS) (hj : j < nT) (hR : R i j) : Inv nS nT R (st.add i j) := by
  refine ⟨by simp [St.add, size_set, h.szS], by simp [St.add, size_set, h.szT], ?_⟩
  intro i' j' hi' hj' hR'
  simp only [St.add]
  rw [get_set (by rw [h.szS]; exact hi), get_set (by rw [h.szT]; exact hj)]
  by_cases e : i' = i
  · subst e
    have := func _ _ _ hR hR'
    subst this
    simp
  · have e' : j' ≠ j := fun ej => e (inj _ _ _ hR' (ej ▸ hR))
    have a1 : (i' == i) = false := by simpa using e
    have a2 : (j' == j) = false := by simpa using e'
    rw [a1, a2, h.eqv i' j' hi' hj' hR']

/-- A live candidate is counted, and if it is the only one, it is the one that is kept. -/
theorem count4_spec (m : Array Bool) {a b c d x : Nat} (hx : x ∈ [a, b, c, d]) (hl : live m x = true) :
    (count4 m a b c d).1 ≠ 0 ∧ ((count4 m a b c d).1 = 1 → (count4 m a b c d).2 = x) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  cases h1 : live m a <;> cases h2 : live m b <;> cases h3 : live m c <;> cases h4 : live m d <;>
    rcases hx with rfl | rfl | rfl | rfl <;> simp_all [count4]

theorem stepS_sound {q : Q} {nS nT : Nat} {R : Nat → Nat → Prop} (G : Graph q nS nT R) {st : St}
    (h : Inv nS nT R st) {i : Nat} (hi : i < nS) :
    ∃ st', stepS q st i = some st' ∧ Inv nS nT R st' := by
  unfold stepS
  by_cases hg : get st.mS i = true
  · exact ⟨st, by simp [hg], h⟩
  obtain ⟨j, hj, hR, hm⟩ := G.fwd i hi
  have hl : live st.mT (j + 1) = true := by
    have : get st.mT j = false := by
      rw [← h.eqv i j hi hj hR]; simpa using hg
    simp [live, this]
  obtain ⟨s1, s2⟩ := count4_spec st.mT hm hl
  simp only [hg]
  generalize count4 st.mT _ _ _ _ = r at s1 s2 ⊢
  rcases r with ⟨k, c⟩
  simp only at s1 s2
  match k, s1, s2 with
  | 0, s1, _ => exact absurd rfl s1
  | 1, _, s2 =>
    have e : c - 1 = j := by have := s2 rfl; omega
    exact ⟨st.add i (c - 1), rfl, by rw [e]; exact h.add G.func G.inj hi hj hR⟩
  | _ + 2, _, _ => exact ⟨st, rfl, h⟩

theorem stepT_sound {q : Q} {nS nT : Nat} {R : Nat → Nat → Prop} (G : Graph q nS nT R) {st : St}
    (h : Inv nS nT R st) {j : Nat} (hj : j < nT) :
    ∃ st', stepT q st j = some st' ∧ Inv nS nT R st' := by
  unfold stepT
  by_cases hg : get st.mT j = true
  · exact ⟨st, by simp [hg], h⟩
  obtain ⟨i, hi, hR, hm⟩ := G.bwd j hj
  have hl : live st.mS (i + 1) = true := by
    have : get st.mS i = false := by
      rw [h.eqv i j hi hj hR]; simpa using hg
    simp [live, this]
  obtain ⟨s1, s2⟩ := count4_spec st.mS hm hl
  simp only [hg]
  generalize count4 st.mS _ _ _ _ = r at s1 s2 ⊢
  rcases r with ⟨k, c⟩
  simp only at s1 s2
  match k, s1, s2 with
  | 0, s1, _ => exact absurd rfl s1
  | 1, _, s2 =>
    have e : c - 1 = i := by have := s2 rfl; omega
    exact ⟨st.add (c - 1) j, rfl, by rw [e]; exact h.add G.func G.inj hi hj hR⟩
  | _ + 2, _, _ => exact ⟨st, rfl, h⟩

theorem passS_sound {q : Q} {nS nT : Nat} {R : Nat → Nat → Prop} (G : Graph q nS nT R)
    (l : List Nat) (hl : ∀ i ∈ l, i < nS) {st : St} (h : Inv nS nT R st) :
    ∃ st', passS q l st = some st' ∧ Inv nS nT R st' := by
  induction l generalizing st with
  | nil => exact ⟨st, rfl, h⟩
  | cons i l ih =>
    obtain ⟨s1, e1, h1⟩ := stepS_sound G h (hl i (by simp))
    obtain ⟨s2, e2, h2⟩ := ih (fun a ha => hl a (by simp [ha])) h1
    exact ⟨s2, by simp [passS, e1, e2], h2⟩

theorem passT_sound {q : Q} {nS nT : Nat} {R : Nat → Nat → Prop} (G : Graph q nS nT R)
    (l : List Nat) (hl : ∀ j ∈ l, j < nT) {st : St} (h : Inv nS nT R st) :
    ∃ st', passT q l st = some st' ∧ Inv nS nT R st' := by
  induction l generalizing st with
  | nil => exact ⟨st, rfl, h⟩
  | cons i l ih =>
    obtain ⟨s1, e1, h1⟩ := stepT_sound G h (hl i (by simp))
    obtain ⟨s2, e2, h2⟩ := ih (fun a ha => hl a (by simp [ha])) h1
    exact ⟨s2, by simp [passT, e1, e2], h2⟩

/-- Propagation never finds a contradiction when the true edges exist. -/
theorem dead_false {q : Q} {nS nT : Nat} {R : Nat → Nat → Prop} (G : Graph q nS nT R)
    (rS rT : List Nat) (hS : ∀ i ∈ rS, i < nS) (hT : ∀ j ∈ rT, j < nT) (n : Nat) {st : St}
    (h : Inv nS nT R st) : dead q rS rT n st = false := by
  induction n generalizing st with
  | zero => rfl
  | succ n ih =>
    obtain ⟨s1, e1, h1⟩ := passS_sound G rS hS h
    obtain ⟨s2, e2, h2⟩ := passT_sound G rT hT h1
    simp only [dead, e1, e2]
    split
    · rfl
    · exact ih h2

theorem inv_init (nS nT : Nat) (R : Nat → Nat → Prop) : Inv nS nT R (St.init nS nT) := by
  refine ⟨by simp [St.init], by simp [St.init], ?_⟩
  intro i j hi hj _
  simp [St.init, get, Array.getD_eq_getD_getElem?, hi, hj]

end Ex89
