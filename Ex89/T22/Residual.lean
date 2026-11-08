import Ex89.T22.Defs
import Std.Data.HashMap

/-!
# Residual certificates

A certificate proves that a formula `φ : Fml` is false at every integer point `p`.
The checker keeps a state: an array `G` of literals (linear forms known to be `≥ 0` at `p`),
an array `A` of formulas known to be true at `p` (`A[0] = φ`), and a lookup map `M` used only
as an oracle (every answer it gives is re-verified, so its contents play no role in soundness).

Certificate nodes (`Cert`):
* `farkas ps`: the non-negative combination `Σ cₖ G[iₖ]` is a negative constant;
* `split h c₁ c₂`: `c₁` under `0 ≤ h`, `c₂` under `0 ≤ -h-1` (exhaustive over the integers);
* `derive ps c`: push the non-negative combination `Σ cₖ G[iₖ]`;
* `assume s path c`: the subformula `nav A[s] path` (path through `.and` children) is true; push it;
* `cases s path cs`: `nav A[s] path` is an `.or`; branch `j` pushes its child `j`;
* `refute s h`: `A[s]` is false on the cell, by the hint `h`.

Hints (`Hint`): `auto` (automatic: an atom is refuted by a negative constant or by the tightest
literal of `G` in the opposite direction, found through `M`; an `.and` by its first automatically
refutable child; an `.or` by all children), `andH i h`, `orH hs`, `farkas μ ps`
(`μ l + Σ cₖ G[iₖ]` is a negative constant).

Main theorem: `checkCert_sound`.
-/
namespace Ex89.T22

/-! ## Constant linear forms -/

/-- All coefficients with index `< 11` (counting from `i`) vanish. -/
def LF.lin0 : List Int → Nat → Bool
  | [], _ => true
  | c :: l, i => (decide (11 ≤ i) || c == 0) && LF.lin0 l (i + 1)

/-- The constant coefficient (index `11`, counting from `i`). -/
def LF.cst : List Int → Nat → Int
  | [], _ => 0
  | c :: l, i => (if i = 11 then c else 0) + LF.cst l (i + 1)

theorem LF.evalFrom_of_lin0 (p : Params) : ∀ (l : List Int) (i : Nat),
    LF.lin0 l i = true → LF.evalFrom p l i = LF.cst l i
  | [], _, _ => by simp [LF.evalFrom, LF.cst]
  | c :: l, i, h => by
    simp only [LF.lin0, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    simp only [LF.evalFrom, LF.cst, LF.evalFrom_of_lin0 p l (i + 1) h.2]
    rcases h.1 with h1 | h1
    · by_cases h11 : i = 11
      · subst h11; simp [Params.val]
      · have : p.val i = 0 := by simp [Params.val]; omega
        simp [this, h11]
    · subst h1; by_cases h11 : i = 11 <;> simp [h11]

/-- `l` is a negative constant. -/
def LF.negConst (l : LF) : Bool := LF.lin0 l 0 && decide (LF.cst l 0 < 0)

theorem LF.eval_neg_of_negConst {l : LF} (h : LF.negConst l = true) (p : Params) : l.eval p < 0 := by
  simp only [LF.negConst, Bool.and_eq_true, decide_eq_true_eq] at h
  unfold LF.eval; rw [LF.evalFrom_of_lin0 p l 0 h.1]; exact h.2

/-- The literal `-h-1 ≥ 0`, i.e. `h < 0`. -/
def LF.negLit (h : LF) : LF := LF.addc (LF.neg h) (-1)

theorem LF.eval_negLit (h : LF) (p : Params) : (LF.negLit h).eval p = - h.eval p - 1 := by
  simp [LF.negLit, LF.eval_addc, LF.eval_neg]; omega

/-! ## Checker state -/

/-- Normalised direction: `(key, s, c)` with `l = s·(key·x) + c` on the first 11 coordinates,
`key` primitive. Only used as a lookup key (heuristic). -/
def LF.dirOf (l : LF) : Option (List Int × Int × Int) :=
  let lin := (List.range 11).map (fun i => l.getD i 0)
  let s : Nat := lin.foldl (fun g c => Nat.gcd g c.natAbs) 0
  if s = 0 then none else some (lin.map (fun c => c / (s : Int)), (s : Int), l.getD 11 0)

structure RState where
  G : Array LF
  M : Std.HashMap (List Int) (Nat × Int × Int)
  A : Array Fml

/-- Push a literal; record it in `M` if it is the tightest one in its direction. -/
def RState.pushLit (st : RState) (l : LF) : RState :=
  let M := match l.dirOf with
    | none => st.M
    | some (key, s, c) =>
      match st.M.get? key with
      | some (_, n', d') => if n' * s < (-c) * d' then st.M.insert key (st.G.size, -c, s) else st.M
      | none => st.M.insert key (st.G.size, -c, s)
  { G := st.G.push l, M := M, A := st.A }

/-- Push a formula: atoms go to `G`, the rest to `A`. -/
def RState.pushF (st : RState) : Fml → RState
  | .atom l => st.pushLit l
  | f => { st with A := st.A.push f }

/-- `Σ c G[i]`. -/
def combo (G : Array LF) : List (Nat × Int) → LF
  | [] => []
  | (i, c) :: ps => LF.add (LF.smul c (G.getD i [])) (combo G ps)

def allNonneg : List (Nat × Int) → Bool
  | [] => true
  | (_, c) :: ps => decide (0 ≤ c) && allNonneg ps

/-- `μ l + λ g` is a negative constant with `μ, λ ≥ 0`: refutes `l ≥ 0` given `g ≥ 0`. -/
def refutes2 (l g : LF) (mu lam : Int) : Bool :=
  decide (0 ≤ mu) && decide (0 ≤ lam) && LF.negConst (LF.add (LF.smul mu l) (LF.smul lam g))

/-- Automatic refutation of an atom. -/
def RState.autoAtom (st : RState) (l : LF) : Bool :=
  match l.dirOf with
  | none => LF.negConst l
  | some (key, a, _) =>
    match st.M.get? (key.map (fun c => -c)) with
    | none => false
    | some (i, _, s) => refutes2 l (st.G.getD i []) s a

mutual
def RState.autoF (st : RState) : Fml → Bool
  | .atom l => st.autoAtom l
  | .and fs => st.autoAny fs
  | .or fs => st.autoAll fs
def RState.autoAny (st : RState) : List Fml → Bool
  | [] => false
  | f :: fs => st.autoF f || st.autoAny fs
def RState.autoAll (st : RState) : List Fml → Bool
  | [] => true
  | f :: fs => st.autoF f && st.autoAll fs
end

/-! ## Hints and certificates -/

mutual
inductive Hint where
  | auto
  | andH (i : Nat) (h : Hint)
  | orH (hs : Hints)
  | farkas (mu : Int) (ps : List (Nat × Int))
inductive Hints where
  | nil
  | cons (h : Hint) (hs : Hints)
end

instance : Inhabited Hint := ⟨.auto⟩
instance : Inhabited Hints := ⟨.nil⟩

mutual
inductive Cert where
  | farkas (ps : List (Nat × Int))
  | split (h : LF) (c₁ c₂ : Cert)
  | derive (ps : List (Nat × Int)) (c : Cert)
  | assume (s : Nat) (path : List Nat) (c : Cert)
  | cases (s : Nat) (path : List Nat) (cs : Certs)
  | refute (s : Nat) (h : Hint)
inductive Certs where
  | nil
  | cons (c : Cert) (cs : Certs)
end

instance : Inhabited Cert := ⟨.farkas []⟩
instance : Inhabited Certs := ⟨.nil⟩

/-- Descend through `.and` children. -/
def nav : Fml → List Nat → Fml
  | f, [] => f
  | .and fs, j :: js => nav (fs.getD j (.and [])) js
  | _, _ :: _ => .and []

mutual
def RState.hintF (st : RState) : Fml → Hint → Bool
  | f, .auto => st.autoF f
  | .and fs, .andH i h => st.hintF (fs.getD i (.and [])) h
  | .or fs, .orH hs => st.hintAll fs hs
  | .atom l, .farkas mu ps =>
    decide (0 ≤ mu) && allNonneg ps && LF.negConst (LF.add (LF.smul mu l) (combo st.G ps))
  | _, _ => false
def RState.hintAll (st : RState) : List Fml → Hints → Bool
  | [], .nil => true
  | f :: fs, .cons h hs => st.hintF f h && st.hintAll fs hs
  | _, _ => false
end

mutual
def RState.chk (st : RState) : Cert → Bool
  | .farkas ps => allNonneg ps && LF.negConst (combo st.G ps)
  | .split h c₁ c₂ => (st.pushLit h).chk c₁ && (st.pushLit (LF.negLit h)).chk c₂
  | .derive ps c => allNonneg ps && (st.pushLit (combo st.G ps)).chk c
  | .assume s path c => (st.pushF (nav (st.A.getD s (.and [])) path)).chk c
  | .cases s path cs =>
    match nav (st.A.getD s (.and [])) path with
    | .or fs => st.chkCases fs cs
    | _ => false
  | .refute s h => st.hintF (st.A.getD s (.and [])) h
def RState.chkCases (st : RState) : List Fml → Certs → Bool
  | [], .nil => true
  | f :: fs, .cons c cs => (st.pushF f).chk c && st.chkCases fs cs
  | _, _ => false
end

/-- The checker. -/
def checkCert (φ : Fml) (c : Cert) : Bool :=
  RState.chk { G := #[], M := {}, A := #[φ] } c

/-! ## Soundness -/

/-- The state is true at `p`. -/
def RState.Ok (st : RState) (p : Params) : Prop :=
  (∀ i, 0 ≤ (st.G.getD i []).eval p) ∧ (∀ i, (st.A.getD i (.and [])).eval p = true)

theorem LF.eval_nil (p : Params) : LF.eval [] p = 0 := rfl

theorem Fml.eval_and_nil (p : Params) : (Fml.and []).eval p = true := by
  simp [Fml.eval, Fml.evalAll]

theorem array_getD_push {α : Type} (a : Array α) (x d : α) (i : Nat) :
    (a.push x).getD i d = if i < a.size then a.getD i d else if i = a.size then x else d := by
  simp only [Array.getD, Array.size_push]
  by_cases h : i < a.size
  · simp [h, Array.getElem_push_lt, show i < a.size + 1 by omega]
  · by_cases h' : i = a.size
    · subst h'; simp
    · simp [h, h', show ¬ i < a.size + 1 by omega]

theorem RState.Ok.pushLit {st : RState} {p : Params} (h : st.Ok p) {l : LF} (hl : 0 ≤ l.eval p) :
    (st.pushLit l).Ok p := by
  refine ⟨fun i => ?_, h.2⟩
  show 0 ≤ ((st.G.push l).getD i []).eval p
  rw [array_getD_push]
  by_cases h1 : i < st.G.size
  · simp only [h1, ↓reduceIte]; exact h.1 i
  · simp only [h1, ↓reduceIte]
    by_cases h2 : i = st.G.size
    · simp only [h2, ↓reduceIte]; exact hl
    · simp only [h2, ↓reduceIte]; exact Int.le_refl 0

theorem RState.Ok.pushF {st : RState} {p : Params} (h : st.Ok p) {f : Fml} (hf : f.eval p = true) :
    (st.pushF f).Ok p := by
  cases f with
  | atom l =>
    simp only [RState.pushF]; apply h.pushLit
    simpa [Fml.eval] using hf
  | and fs =>
    refine ⟨h.1, fun i => ?_⟩
    show ((st.A.push _).getD i _).eval p = true
    rw [array_getD_push]
    by_cases h1 : i < st.A.size
    · simp only [h1, ↓reduceIte]; exact h.2 i
    · simp only [h1, ↓reduceIte]
      by_cases h2 : i = st.A.size
      · simp only [h2, ↓reduceIte]; exact hf
      · simp only [h2, ↓reduceIte]; exact Fml.eval_and_nil p
  | or fs =>
    refine ⟨h.1, fun i => ?_⟩
    show ((st.A.push _).getD i _).eval p = true
    rw [array_getD_push]
    by_cases h1 : i < st.A.size
    · simp only [h1, ↓reduceIte]; exact h.2 i
    · simp only [h1, ↓reduceIte]
      by_cases h2 : i = st.A.size
      · simp only [h2, ↓reduceIte]; exact hf
      · simp only [h2, ↓reduceIte]; exact Fml.eval_and_nil p

theorem combo_nonneg {G : Array LF} {p : Params} (hG : ∀ i, 0 ≤ (G.getD i []).eval p) :
    ∀ ps, allNonneg ps = true → 0 ≤ (combo G ps).eval p
  | [], _ => by simp [combo, LF.eval_nil]
  | (i, c) :: ps, h => by
    simp only [allNonneg, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [combo, LF.eval_add, LF.eval_smul]
    have := combo_nonneg hG ps h.2
    have := Int.mul_nonneg h.1 (hG i)
    omega

theorem refutes2_sound {l g : LF} {mu lam : Int} (h : refutes2 l g mu lam = true) {p : Params}
    (hg : 0 ≤ g.eval p) : l.eval p < 0 := by
  simp only [refutes2, Bool.and_eq_true, decide_eq_true_eq] at h
  have hn := LF.eval_neg_of_negConst h.2 p
  simp only [LF.eval_add, LF.eval_smul] at hn
  have h2 := Int.mul_nonneg h.1.2 hg
  rcases Int.lt_or_le (l.eval p) 0 with hl | hl
  · exact hl
  · have := Int.mul_nonneg h.1.1 hl; omega

theorem RState.autoAtom_sound {st : RState} {p : Params} (h : st.Ok p) {l : LF}
    (ha : st.autoAtom l = true) : l.eval p < 0 := by
  unfold RState.autoAtom at ha
  split at ha
  · exact LF.eval_neg_of_negConst ha p
  · split at ha
    · exact absurd ha (by simp)
    · exact refutes2_sound ha (h.1 _)

mutual
theorem RState.autoF_sound {st : RState} {p : Params} (h : st.Ok p) :
    ∀ f, st.autoF f = true → f.eval p = false
  | .atom l, ha => by
    simp only [RState.autoF] at ha
    have := st.autoAtom_sound h ha
    simp [Fml.eval]; omega
  | .and fs, ha => by
    simp only [RState.autoF] at ha
    simp only [Fml.eval]; exact RState.autoAny_sound h fs ha
  | .or fs, ha => by
    simp only [RState.autoF] at ha
    simp only [Fml.eval]; exact RState.autoAll_sound h fs ha
theorem RState.autoAny_sound {st : RState} {p : Params} (h : st.Ok p) :
    ∀ fs, st.autoAny fs = true → Fml.evalAll p fs = false
  | [], ha => by simp [RState.autoAny] at ha
  | f :: fs, ha => by
    simp only [RState.autoAny, Bool.or_eq_true] at ha
    simp only [Fml.evalAll, Bool.and_eq_false_iff]
    rcases ha with ha | ha
    · exact Or.inl (RState.autoF_sound h f ha)
    · exact Or.inr (RState.autoAny_sound h fs ha)
theorem RState.autoAll_sound {st : RState} {p : Params} (h : st.Ok p) :
    ∀ fs, st.autoAll fs = true → Fml.evalAny p fs = false
  | [], _ => by simp [Fml.evalAny]
  | f :: fs, ha => by
    simp only [RState.autoAll, Bool.and_eq_true] at ha
    simp only [Fml.evalAny, Bool.or_eq_false_iff]
    exact ⟨RState.autoF_sound h f ha.1, RState.autoAll_sound h fs ha.2⟩
end

theorem evalAll_getD {p : Params} : ∀ (fs : List Fml) (i : Nat) (d : Fml),
    Fml.evalAll p fs = true → d.eval p = true → (fs.getD i d).eval p = true
  | [], _, _, _, hd => by simpa using hd
  | f :: fs, 0, _, h, _ => by
    simp only [Fml.evalAll, Bool.and_eq_true] at h; simpa using h.1
  | f :: fs, i + 1, d, h, hd => by
    simp only [Fml.evalAll, Bool.and_eq_true] at h
    simpa using evalAll_getD fs i d h.2 hd

theorem nav_true {p : Params} : ∀ (f : Fml) (path : List Nat), f.eval p = true → (nav f path).eval p = true
  | f, [], h => by simpa [nav] using h
  | .and fs, j :: js, h => by
    simp only [nav]
    apply nav_true
    exact evalAll_getD fs j _ (by simpa [Fml.eval] using h) (Fml.eval_and_nil p)
  | .atom _, _ :: _, _ => by simp [nav, Fml.eval_and_nil]
  | .or _, _ :: _, _ => by simp [nav, Fml.eval_and_nil]

mutual
theorem RState.hintF_sound {st : RState} {p : Params} (h : st.Ok p) :
    ∀ (f : Fml) (hn : Hint), st.hintF f hn = true → f.eval p = false
  | f, .auto, hh => by
    simp only [RState.hintF] at hh; exact RState.autoF_sound h f hh
  | .and fs, .andH i hn, hh => by
    simp only [RState.hintF] at hh
    have hf := RState.hintF_sound h _ hn hh
    simp only [Fml.eval]
    cases hall : Fml.evalAll p fs
    · rfl
    · have := evalAll_getD fs i _ hall (Fml.eval_and_nil p)
      rw [hf] at this; exact absurd this (by simp)
  | .or fs, .orH hs, hh => by
    simp only [RState.hintF] at hh
    simp only [Fml.eval]; exact RState.hintAll_sound h fs hs hh
  | .atom l, .farkas mu ps, hh => by
    simp only [RState.hintF, Bool.and_eq_true, decide_eq_true_eq] at hh
    have hn := LF.eval_neg_of_negConst hh.2 p
    simp only [LF.eval_add, LF.eval_smul] at hn
    have hc := combo_nonneg h.1 ps hh.1.2
    simp only [Fml.eval, decide_eq_false_iff_not, Int.not_le]
    rcases Int.lt_or_le (l.eval p) 0 with hl | hl
    · exact hl
    · have := Int.mul_nonneg hh.1.1 hl; omega
  | .atom _, .andH _ _, hh => by simp [RState.hintF] at hh
  | .atom _, .orH _, hh => by simp [RState.hintF] at hh
  | .and _, .orH _, hh => by simp [RState.hintF] at hh
  | .and _, .farkas _ _, hh => by simp [RState.hintF] at hh
  | .or _, .andH _ _, hh => by simp [RState.hintF] at hh
  | .or _, .farkas _ _, hh => by simp [RState.hintF] at hh
theorem RState.hintAll_sound {st : RState} {p : Params} (h : st.Ok p) :
    ∀ (fs : List Fml) (hs : Hints), st.hintAll fs hs = true → Fml.evalAny p fs = false
  | [], .nil, _ => by simp [Fml.evalAny]
  | f :: fs, .cons hn hs, hh => by
    simp only [RState.hintAll, Bool.and_eq_true] at hh
    simp only [Fml.evalAny, Bool.or_eq_false_iff]
    exact ⟨RState.hintF_sound h f hn hh.1, RState.hintAll_sound h fs hs hh.2⟩
  | [], .cons _ _, hh => by simp [RState.hintAll] at hh
  | _ :: _, .nil, hh => by simp [RState.hintAll] at hh
end

theorem negLit_or (h : LF) (p : Params) : 0 ≤ h.eval p ∨ 0 ≤ (LF.negLit h).eval p := by
  rw [LF.eval_negLit]; omega

mutual
theorem RState.chk_sound {p : Params} : ∀ (st : RState) (c : Cert), st.chk c = true → st.Ok p → False
  | st, .farkas ps, hc, h => by
    simp only [RState.chk, Bool.and_eq_true] at hc
    have := LF.eval_neg_of_negConst hc.2 p
    have := combo_nonneg h.1 ps hc.1
    omega
  | st, .split hl c₁ c₂, hc, h => by
    simp only [RState.chk, Bool.and_eq_true] at hc
    rcases negLit_or hl p with h1 | h1
    · exact RState.chk_sound _ c₁ hc.1 (h.pushLit h1)
    · exact RState.chk_sound _ c₂ hc.2 (h.pushLit h1)
  | st, .derive ps c, hc, h => by
    simp only [RState.chk, Bool.and_eq_true] at hc
    exact RState.chk_sound _ c hc.2 (h.pushLit (combo_nonneg h.1 ps hc.1))
  | st, .assume s path c, hc, h => by
    simp only [RState.chk] at hc
    exact RState.chk_sound _ c hc (h.pushF (nav_true _ path (h.2 s)))
  | st, .cases s path cs, hc, h => by
    simp only [RState.chk] at hc
    have hn := nav_true _ path (h.2 s) (p := p)
    split at hc
    · rename_i fs heq
      rw [heq] at hn
      exact RState.chkCases_sound st fs cs hc h (by simpa [Fml.eval] using hn)
    · exact absurd hc (by simp)
  | st, .refute s hn, hc, h => by
    simp only [RState.chk] at hc
    have := RState.hintF_sound h _ hn hc
    rw [h.2 s] at this; exact absurd this (by simp)
theorem RState.chkCases_sound {p : Params} : ∀ (st : RState) (fs : List Fml) (cs : Certs),
    st.chkCases fs cs = true → st.Ok p → Fml.evalAny p fs = true → False
  | _, [], .nil, _, _, ha => by simp [Fml.evalAny] at ha
  | st, f :: fs, .cons c cs, hc, h, ha => by
    simp only [RState.chkCases, Bool.and_eq_true] at hc
    simp only [Fml.evalAny, Bool.or_eq_true] at ha
    rcases ha with ha | ha
    · exact RState.chk_sound _ c hc.1 (h.pushF ha)
    · exact RState.chkCases_sound st fs cs hc.2 h ha
  | _, [], .cons _ _, hc, _, _ => by simp [RState.chkCases] at hc
  | _, _ :: _, .nil, hc, _, _ => by simp [RState.chkCases] at hc
end

/-- **Soundness of the residual checker.** -/
theorem checkCert_sound (φ : Fml) (c : Cert) (h : checkCert φ c = true) (p : Params) :
    φ.eval p = false := by
  cases hφ : φ.eval p
  · rfl
  · exfalso
    refine RState.chk_sound (p := p) _ c h ⟨fun i => ?_, fun i => ?_⟩
    · simp [Array.getD, LF.eval_nil]
    · simp only [Array.getD]
      split
      · rename_i hi
        have : i = 0 := by simp at hi; omega
        subst this; simpa using hφ
      · exact Fml.eval_and_nil p


/-! ## Parsers (trusted only through `native_decide`; no proofs about them are needed) -/

namespace ResParse

partial def skipWs (b : ByteArray) (i : Nat) : Nat :=
  if h : i < b.size then
    let c := b[i]
    if c == 32 || c == 10 || c == 13 || c == 9 then skipWs b (i + 1) else i
  else i

partial def digits (b : ByteArray) (i : Nat) (acc : Nat) : Nat × Nat :=
  if h : i < b.size then
    let c := b[i]
    if 48 ≤ c && c ≤ 57 then digits b (i + 1) (acc * 10 + (c - 48).toNat) else (acc, i)
  else (acc, i)

/-- Compact numbers: continuation bytes `97..126` (base 30, most significant first), then one
terminal byte `48..95` (base 48). -/
partial def cdigits (b : ByteArray) (i : Nat) (acc : Nat) : Nat × Nat :=
  if h : i < b.size then
    let c := b[i]
    if 97 ≤ c && c ≤ 126 then cdigits b (i + 1) (acc * 30 + (c - 97).toNat)
    else (acc * 48 + (c - 48).toNat, i + 1)
  else (acc, i)

/-- `cz`: compact encoding (signed numbers zigzag-coded), otherwise decimal text. -/
def readNat (cz : Bool) (b : ByteArray) (i : Nat) : Nat × Nat :=
  if cz then cdigits b (skipWs b i) 0 else digits b (skipWs b i) 0

def readInt (cz : Bool) (b : ByteArray) (i : Nat) : Int × Nat :=
  let i := skipWs b i
  if cz then
    let (z, j) := cdigits b i 0
    (if z % 2 == 0 then ((z / 2 : Nat) : Int) else -(((z + 1) / 2 : Nat) : Int), j)
  else if b.get! i == 45 then let (n, j) := digits b (i + 1) 0; (-(n : Int), j)
  else let (n, j) := digits b i 0; ((n : Int), j)

/-- Next non-blank byte. -/
def readChar (b : ByteArray) (i : Nat) : UInt8 × Nat :=
  let i := skipWs b i; (b.get! i, i + 1)

/-- A token of non-blank bytes. -/
partial def readWord (b : ByteArray) (i : Nat) : String × Nat :=
  let i := skipWs b i
  let rec go (j : Nat) : Nat := if j < b.size && !(b.get! j == 32 || b.get! j == 10 || b.get! j == 13 || b.get! j == 9) then go (j + 1) else j
  let j := go i
  (String.fromUTF8! (b.extract i j), j)

def readInts (cz : Bool) (b : ByteArray) (i : Nat) : Nat → List Int × Nat
  | 0 => ([], i)
  | n + 1 => let (x, i) := readInt cz b i; let (xs, i) := readInts cz b i n; (x :: xs, i)

def readNats (cz : Bool) (b : ByteArray) (i : Nat) : Nat → List Nat × Nat
  | 0 => ([], i)
  | n + 1 => let (x, i) := readNat cz b i; let (xs, i) := readNats cz b i n; (x :: xs, i)

def readPairs (cz : Bool) (b : ByteArray) (i : Nat) : Nat → List (Nat × Int) × Nat
  | 0 => ([], i)
  | n + 1 =>
    let (x, i) := readNat cz b i; let (c, i) := readInt cz b i
    let (xs, i) := readPairs cz b i n; ((x, c) :: xs, i)

mutual
partial def hint (cz : Bool) (b : ByteArray) (i : Nat) : Hint × Nat :=
  let (c, i) := readChar b i
  if c == 63 then (.auto, i)                                   -- '?'
  else if c == 110 then                                        -- 'n'
    let (k, i) := readNat cz b i; let (h, i) := hint cz b i; (.andH k h, i)
  else if c == 111 then                                        -- 'o'
    let (m, i) := readNat cz b i; let (hs, i) := hints cz b i m; (.orH hs, i)
  else if c == 102 then                                        -- 'f'
    let (mu, i) := readInt cz b i; let (n, i) := readNat cz b i; let (ps, i) := readPairs cz b i n
    (.farkas mu ps, i)
  else (.auto, b.size + 1)
partial def hints (cz : Bool) (b : ByteArray) (i : Nat) : Nat → Hints × Nat
  | 0 => (.nil, i)
  | m + 1 => let (h, i) := hint cz b i; let (hs, i) := hints cz b i m; (.cons h hs, i)
end

mutual
partial def cert (cz : Bool) (b : ByteArray) (i : Nat) : Cert × Nat :=
  let (c, i) := readChar b i
  if c == 70 then                                              -- 'F'
    let (n, i) := readNat cz b i; let (ps, i) := readPairs cz b i n; (.farkas ps, i)
  else if c == 83 then                                         -- 'S'
    let (h, i) := readInts cz b i 12; let (c₁, i) := cert cz b i; let (c₂, i) := cert cz b i
    (.split h c₁ c₂, i)
  else if c == 68 then                                         -- 'D'
    let (n, i) := readNat cz b i; let (ps, i) := readPairs cz b i n; let (c, i) := cert cz b i
    (.derive ps c, i)
  else if c == 65 then                                         -- 'A'
    let (s, i) := readNat cz b i; let (n, i) := readNat cz b i; let (p, i) := readNats cz b i n
    let (c, i) := cert cz b i; (.assume s p c, i)
  else if c == 67 then                                         -- 'C'
    let (s, i) := readNat cz b i; let (n, i) := readNat cz b i; let (p, i) := readNats cz b i n
    let (m, i) := readNat cz b i; let (cs, i) := certs cz b i m; (.cases s p cs, i)
  else if c == 82 then                                         -- 'R'
    let (s, i) := readNat cz b i; let (h, i) := hint cz b i; (.refute s h, i)
  else (.farkas [], b.size + 1)
partial def certs (cz : Bool) (b : ByteArray) (i : Nat) : Nat → Certs × Nat
  | 0 => (.nil, i)
  | m + 1 => let (c, i) := cert cz b i; let (cs, i) := certs cz b i m; (.cons c cs, i)
end

/-- Formula in prefix text (`a c0 .. c11`, `& n`, `| n`). -/
partial def fml (b : ByteArray) (i : Nat) : Fml × Nat :=
  let (c, i) := readChar b i
  if c == 97 then let (l, i) := readInts false b i 12; (.atom l, i)
  else
    let (n, i) := readNat false b i
    let rec go (k : Nat) (i : Nat) (acc : Array Fml) : Array Fml × Nat :=
      if k = 0 then (acc, i) else let (f, i) := fml b i; go (k - 1) i (acc.push f)
    let (fs, i) := go n i #[]
    if c == 38 then (.and fs.toList, i) else (.or fs.toList, i)

/-- Skip the rest of the line (used for headers). -/
partial def skipLine (b : ByteArray) (i : Nat) : Nat :=
  if i < b.size then (if b.get! i == 10 then i + 1 else skipLine b (i + 1)) else i

/-- A certificate file: blocks `T <tag>` followed by one certificate each. -/
partial def certFile (b : ByteArray) (i : Nat) (acc : Array (String × Cert)) : Array (String × Cert) :=
  let j := skipWs b i
  if j ≥ b.size then acc
  else
    let (t, j) := readChar b j      -- 'T' (decimal text) or 'U' (compact)
    let (tag, j) := readWord b j
    let (c, j) := cert (t == 85) b j
    certFile b j (acc.push (tag, c))

end ResParse

/-- Parse one certificate (the text after its header). -/
def Cert.parse (s : String) : Cert := (ResParse.cert false s.toUTF8 0).1

/-- Parse a formula in prefix text, skipping a first header line starting with `T`. -/
def Fml.parseText (s : String) : Fml :=
  let b := s.toUTF8
  let i := ResParse.skipWs b 0
  let i := if b.get! i == 84 then ResParse.skipLine b i else i
  (ResParse.fml b i).1

/-- Parse a certificate file with blocks `T <tag> <cert>`. -/
def parseCertFile (s : String) : List (String × Cert) := (ResParse.certFile s.toUTF8 0 #[]).toList

/-! ## Integration: certificates keyed by table tag -/

def Region.tag : Region → String
  | .fat => "fat" | .mid => "mid" | .thin => "thin"
def Kind.tag : Kind → String
  | .diag => "diag" | .adj => "adj"
/-- `"region-kind-o2-o3"`, the key of the certificate files. -/
def Table.tag (t : Table) : String :=
  t.region.tag ++ "-" ++ t.case.kind.tag ++ "-" ++ toString t.case.o2.val ++ "-" ++ toString t.case.o3.val

/-- The certificate of `tag` (a failing one if absent). -/
def certFor (cs : List (String × Cert)) (tag : String) : Cert := (cs.lookup tag).getD default

/-- Check every table of `ts` against its certificate. -/
def checkAllCerts (F : Table → Fml) (cs : List (String × Cert)) (ts : List Table) : Bool :=
  ts.all fun t => checkCert (F t) (certFor cs t.tag)

theorem checkAllCerts_sound {F : Table → Fml} {cs : List (String × Cert)} {ts : List Table}
    (h : checkAllCerts F cs ts = true) {t : Table} (ht : t ∈ ts) (p : Params) : (F t).eval p = false := by
  simp only [checkAllCerts, List.all_eq_true] at h
  exact checkCert_sound _ _ (h t ht) p

end Ex89.T22
