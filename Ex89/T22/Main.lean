import Ex89.T22.Lemma0
import Ex89.T22.Reduce
import Ex89.T22.Thin
import Ex89.T22.Sem
import Ex89.T22.Residual
import Ex89.T22.Parse
/-!
# The 2+2 theorem

If `0 < u < v < w`, `u² + v² = w²` and `(u, v, w)` is not a multiple of `(3, 4, 5)`, then there is no
`Dissection u v w` in which exactly two pieces go to the `u × u` square.
-/
namespace Ex89.T22

/-- The table keys handled by the residual certificates: fat and mid (both kinds, all 64
orientations), thin diag with `o2 ∉ {0, 4}`. -/
def ResKey (r : Region) (c : Case) : Prop :=
  r ≠ .thin ∨ (c.kind = .diag ∧ c.o2 ≠ 0 ∧ c.o2 ≠ 4)

instance (r : Region) (c : Case) : Decidable (ResKey r c) := by unfold ResKey; infer_instance

/-- The residual certificates (the data files `data/t22_res_*.txt`). -/
def resCerts : List (String × Cert) :=
  parseCertFile (include_str "../../data/t22_res_0.txt") ++
  parseCertFile (include_str "../../data/t22_res_1.txt") ++
  parseCertFile (include_str "../../data/t22_res_2.txt")

/-- Every residual key has a table, and every table's certificate checks. -/
def resOK : Bool :=
  checkAllCerts tableF resCerts tables &&
  [Region.fat, Region.mid, Region.thin].all fun r => [Kind.diag, Kind.adj].all fun k =>
    (List.finRange 8).all fun o2 => (List.finRange 8).all fun o3 =>
      !(decide (ResKey r ⟨k, o2, o3⟩)) ||
        tables.any fun t => decide (t.region = r) && decide (t.case = ⟨k, o2, o3⟩)

theorem resOK_true : resOK = true := by native_decide

/-- **Residual**: for every key some table's formula is unsatisfiable. -/
theorem residual (r : Region) (c : Case) (hk : ResKey r c) :
    ∃ t : Table, t.region = r ∧ t.case = c ∧ ∀ p, (tableF t).eval p = false := by
  have h := resOK_true
  simp only [resOK, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨hc, hk'⟩ := h
  have hr : r ∈ [Region.fat, Region.mid, Region.thin] := by cases r <;> simp
  have hkd : c.kind ∈ [Kind.diag, Kind.adj] := by cases c.kind <;> simp
  have := hk' r hr c.kind hkd c.o2 (List.mem_finRange _) c.o3 (List.mem_finRange _)
  have hc' : (⟨c.kind, c.o2, c.o3⟩ : Case) = c := rfl
  rw [hc'] at this
  simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, List.any_eq_true,
    Bool.and_eq_true, decide_eq_true_eq] at this
  rcases this with h1 | ⟨t, ht, h2, h3⟩
  · exact absurd hk h1
  · exact ⟨t, h2, h3, fun p => checkAllCerts_sound hc ht p⟩

theorem no_two_two (u v w : Nat) (hu : 0 < u) (huv : u < v) (hvw : v < w)
    (hp : u * u + v * v = w * w) (hn : ¬ ∃ k, u = 3 * k ∧ v = 4 * k ∧ w = 5 * k)
    (D : Dissection u v w)
    (h22 : ((List.finRange 4).filter (fun k => D.toU k)).length = 2) : False := by
  obtain ⟨c, p, hd, he, hf, ⟨N⟩⟩ := reduce u v w hu huv hvw D h22
  obtain ⟨d1, e1, u1, hpy, hne⟩ := params_of_triple u v w hu huv hvw hp hn p.d p.e p.f hd he hf
  have hu1 : 1 ≤ p.u := by simp only [Params.u]; exact u1
  have use : ∀ r, RegionP r p.d p.e p.f → ResKey r c → False := by
    intro r hr hk
    obtain ⟨t, htr, htc, ht⟩ := residual r c hk
    subst htr htc
    have := tableF_true t p N hr d1 e1
    rw [ht p] at this
    exact Bool.false_ne_true this
  rcases lemma0 p.d p.e p.f d1 e1 u1 hpy hne with h | h | h
  · exact use .fat h (Or.inl (by decide))
  · exact use .mid h (Or.inl (by decide))
  · cases hk : c.kind with
    | adj => exact thin_adj c p hk h.1 d1 e1 hu1 N
    | diag =>
      by_cases ho : c.o2 = 0 ∨ c.o2 = 4
      · exact thin_diag_tf c p hk ho h d1 e1 hpy N
      · exact use .thin h (Or.inr ⟨hk, fun e => ho (Or.inl e), fun e => ho (Or.inr e)⟩)

#print axioms no_two_two

end Ex89.T22
