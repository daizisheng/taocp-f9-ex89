# The partial theorem: only 1+3 dissections can exist

This file explains the proofs in [`Ex89/Partial.lean`](Ex89/Partial.lean),
[`Ex89/ThreeOne.lean`](Ex89/ThreeOne.lean) and [`Ex89/T22/`](Ex89/T22). The Lean files are the
proof. This text is a guide to them.

Throughout, `0 < u < v < w`, `u^2 + v^2 = w^2`, and `(u, v, w)` is not a multiple of `(3, 4, 5)`.
`W` is the `w × w` square, `S_u` and `S_v` are the two target squares. A `Dissection u v w` is the
structure of [`Ex89/Model.lean`](Ex89/Model.lean): four pieces, possibly disconnected, each with one
motion and one target square, forming a bijection from `W` onto the two squares.

## Part 1. The split by the number of pieces

Count the pieces that go to `S_u`.

- **Zero or four.** The cell `(0, 0)` of `S_u` and the cell `(0, 0)` of `S_v` both have preimages,
  so each square receives at least one piece (`exists_toU`).
- **Two.** This is the 2+2 theorem `Ex89.T22.no_two_two` (Part 3).
- **Three.** This is the 3+1 theorem `Ex89.ThreeOne.no_three_one` (Part 2).

So exactly one piece goes to `S_u`. This is `Ex89.one_piece_to_u`. The case 1+3 itself is not
settled here.

A fact used by both parts: every piece contains a corner of `W`, and the four corners lie in four
different pieces. Two corners differ by `w - 1 ≥ v` in some coordinate, while two cells of one piece
differ by less than the side of its target square in each coordinate (`Motion.close` in
[`Ex89/Normal.lean`](Ex89/Normal.lean)). The cells of the piece at a corner therefore lie in a
*corner box*: the square of side `u` or `v` at that corner.

## Part 2. The 3+1 theorem

Write `d = w - v` and `a = w - u`. Then `u^2 = d (w + v)` and `0 < d < a < u`.

### 2.1 Normal form

Number the corners `0 = (0, 0)`, `1 = (0, w-1)`, `2 = (w-1, w-1)`, `3 = (w-1, 0)`. Rotate `W` so
that the only piece going to `S_v` contains corner 0, and name each piece by its corner. Apply a
symmetry of `S_v` so that the motion of piece 0 has no rotation or flip. Cell `(0, 0)` is in piece
0 and its image is a cell of `S_v`, so the motion of piece 0 is the identity, and by surjectivity
piece 0 is all of `[0, v)^2`.

Piece `k` (`k = 1, 2, 3`) lies in the corner box of side `u` at corner `k`, and outside `[0, v)^2`:

- piece 1 has `x < u` and `y ≥ v`; piece 3 has `y < u` and `x ≥ v`;
- piece 2 has `x, y ≥ a`, and `x ≥ v` or `y ≥ v`.

In the rows `y ≥ v`, the cells with `x < a` are in piece 1 and those with `x ≥ u` are in piece 2.
In the columns `x ≥ v`, the cells with `y < a` are in piece 3 and those with `y ≥ u` are in piece 2.
The cells with `u ≤ y < v` and `x ≥ v` are in piece 2. (File `ThreeOneNormal.lean`.)

### 2.2 Arithmetic

All of these follow from `u^2 + v^2 = w^2` with `0 < u < v < w` (file `ThreeOneArith.lean`).

- `2d < u`. This is `4d < w + v`, that is `3w < 5v`, which follows from `w^2 < 2v^2`.
- If `u = 3d`, then `9d = w + v`, and `(u, v, w) = d (3, 4, 5)`.
- `3a > u`. This is `4u < 3w`, which follows from `16 u^2 < 9 w^2`, that is `7 u^2 < 9 v^2`.
- If `2a ≤ u`, that is `3u ≥ 2w`, then `5u > 3w`. If moreover `v ≤ 2(w - u)`, then
  `(w + u)(w - u) = v^2 ≤ 4 (w - u)^2`, so `w + u ≤ 4(w - u)` and `5u ≤ 3w`, a contradiction. So
  `κ = u - a - d > 0`. Also `2a ≠ u`: otherwise `u = 2k`, `w = 3k` and `v^2 = 5k^2`.
- If `2u = 5d`, then `4d(w + v) = 25 d^2` gives `8v = 21d`, and `8(d + 2a - u) = 2d > 0`. So
  `d + 2a ≠ u`.

### 2.3 Bands and row sums

A motion with `sw = false` sends source rows to target rows; with `sw = true` it sends source
columns to target rows. In both cases the map of line numbers is `t ↦ ±t + c`. So a set of `d`
consecutive source lines goes to a *band* of `d` consecutive target lines.

The cells of piece 1 lie in the rows `[v, w)`, those of piece 3 in the columns `[v, w)`, and those
of piece 2 in the rows `[v, w)` (its upper arm) or the columns `[v, w)` (its right arm). So the
image of piece 1 lies in one band of `S_u`, the image of piece 3 in one band, and the two arms of
piece 2 give one band in each direction. If `sw_1 = sw_3`, two bands run in each direction. Since
`2d < u`, some row and some column of `S_u` miss these bands, and the cell where they cross has no
preimage. So `sw_1 ≠ sw_3`. After transposing `S_u` if needed, the bands of pieces 1 and 3 are bands
of rows.

For a row `r` of `S_u`, the cells of piece `k` that go to row `r` are the cells of piece `k` on one
source line `σ_k(r) = ±r + c_k`. Let `F_k(i)` be the number of cells of piece `k` on source line `i`
(zero if `i` is out of range). The bijection onto `S_u` gives the *row sum*

    F_1(σ_1 r) + F_2(σ_2 r) + F_3(σ_3 r) = u.

If `sw_2 = false`, `F_1`, `F_2`, `F_3` are the row counts of pieces 1 and 2 and the column count of
piece 3. If `sw_2 = true`, they are the column counts of pieces 3 and 2 and the row count of piece
1. By 2.1, the same facts hold in both cases:

- (F1) `F_1(y) = 0` for `y ∉ [v, w)`; `a ≤ F_1(y) ≤ u` and `F_1(y) + F_2(y) = w` for `y ∈ [v, w)`.
- (F2) `F_2(y) = 0` for `y ∉ [a, w)`; `F_2(y) ≤ d` for `y ∈ [a, v)`; `F_2(y) = d` for `y ∈ [u, v)`.
- (F3) `F_3(x) = 0` for `x ∉ [v, w)`; `a ≤ F_3(x) ≤ u` for `x ∈ [v, w)`.
- (Img) If `F_k(i) > 0`, then `σ_k^{-1}(i)` is a row of `S_u`.

This is how the 3+1 proof avoids a diagonal reflection: both cases satisfy the same
one-dimensional hypotheses. (File `ThreeOneCount.lean`.)

### 2.4 The one-dimensional core

The core lemma `core` in `ThreeOneCore.lean` derives a contradiction from the row sums, (F1)–(F3),
(Img) and the facts of 2.2. Its hypotheses mention only integers and three counting functions; the
dissection does not appear.

**Step 0.** If `σ_2` is decreasing, renumber the rows by `r ↦ u - 1 - r`. So `σ_2(r) = r + c_2`.

**Bands.** Let `B1`, `B2`, `B3` be the sets of rows `r` with `σ_k(r) ∈ [v, w)`. Each is an interval
of length `d` inside `[0, u)`. Write `B2 = [p, p + d)`. In a row of `B1` or `B3` the term of that
piece is at least `a`; in a row of `B2` the term `F_2 = w - F_1 ≥ a`. Below `B2` (`r < p`) the term
`F_2` is at most `d`, and equals `d` in row `p - 1`. Above `B2` it is zero.

**Step 1.** A row outside all three bands has row sum at most `d < u`. So the bands cover `[0, u)`,
and `3d ≥ u`. Since `u ≠ 3d`, `3d > u`.

**Step 2.** The band containing row 0 is `lo = [0, d)`, the band containing row `u - 1` is
`hi = [u - d, u)`, and these are disjoint. The third band `mid = [m, m + d)` covers rows `d` and
`u - d - 1`, so `u - 2d ≤ m ≤ d`. Let `λ = d - m` and `η = m + 2d - u`. Then `λ, η ≥ 0` and
`λ + η = 3d - u`, which lies strictly between 0 and `d`.

**Step 3.** Some row lies in two bands, so `2a ≤ u`. By 2.2, `κ > 0` and `2a ≠ u`.

**Step 4.** For a row `y ∈ [v, w)` of the upper arm, let `r_2 = σ_2^{-1}(y)` and
`r_1 = σ_1^{-1}(y)`. Then

    r_2 ∈ B1 ∪ B3   if and only if   r_1 ∉ B2 ∪ B3.

If `r_2 ∉ B1 ∪ B3`, row `r_2` has only the term `F_2(y) = u`, so `F_1(y) = a`; if also
`r_1 ∉ B2 ∪ B3`, the row sum of `r_1` is `a + F_2(σ_2 r_1)`, which is at most `a + d < u` or equal
to `a`. If `r_2 ∈ B1 ∪ B3`, the row sum of `r_2` is at least `a + w - F_1(y)`, so `F_1(y) ≥ 2a`; if
also `r_1 ∈ B2 ∪ B3`, the row sum of `r_1` is at least `3a > u`.

**Step 5.** If `σ_2^{-1}(y_O) = σ_1^{-1}(y_Z) = r ∉ B3` and `σ_2^{-1}(y_Z) ∉ B1 ∪ B3`, then
`F_1(y_O) = 2a`. Indeed `F_1(y_Z) = a` as in step 4, and the row sum of `r` is
`a + (w - F_1(y_O)) = u`.

**Step 6.** `(B2, B1, B3)` is a permutation of `(lo, mid, hi)`, and `σ_1` is increasing or
decreasing: 12 cases. With `j = y - v`, step 4 is an equivalence about `j`, `λ`, `η` and `m`. In the
six cases with `σ_1` decreasing it fails at `j = 0` or `j = d - 1`. In the cases
`(lo, hi, mid)` and `(hi, lo, mid)` it gives `m = η`, so `d = 3d - u`, a contradiction. In the four
remaining cases it gives `d = 2(3d - u)`, that is `2u = 5d`. Then step 5 applies to a suitable pair
`y_O`, `y_Z`, and the term of piece 1 in row `σ_1^{-1}(y_O)` is `2a`. This row is outside `B3`, and
it lies either above `B2`, where its row sum gives `u = 2a`, or is row `p - 1`, where its row sum
gives `u = 2a + d`. Both contradict 2.2.

For example, `(20, 21, 29)` has `2u = 5d`, and in the case `(hi, mid, lo)` the numbers are `d = 8`,
`m = 8`, `η = 4`.

### 2.5 Assembly

`no_three_one` combines 2.1–2.4: the arithmetic of 2.2, the normal form of 2.1, the bands of 2.3
with `sw_1 = false`, `sw_3 = true`, and the core lemma applied in the case `sw_2 = false` or
`sw_2 = true`. No `native_decide` is used.

## Part 3. The 2+2 theorem

### 3.1 Parameters and Lemma 0

Let `d = w - v`, `e = v - u`, `f = 2u - w`. Then `u = d + e + f`, `v = d + 2e + f`,
`w = 2d + 2e + f`, `a = w - u = d + e`, and `d, e ≥ 1`. The equation `u^2 + v^2 = w^2` becomes

    (e + f)^2 = 2d (d + e).

Put `δ = d - e`, `κ = f - d` and `t = δ - κ`. The equation gives `δ - 2κ = t^2 / (2d) ≥ 0`, with
equality only if `d = e = f`, which is the `3:4:5` case. So `2(f - d) + 1 ≤ d - e`. Also `f ≠ 0`,
since `w = 2u` would give `v^2 = 3u^2`. The parameters then lie in one of three regions
(`RegionP` in `Ex89/T22/Defs.lean`, proved in `Lemma0.lean`):

- **fat**: `e < d < f`, `2f ≤ 3d`;
- **mid**: `1 ≤ f < d < e`, `4e ≤ 11d`;
- **thin**: `f ≤ -1`, `d < e`, `e + f ≥ 2d + 1`;

each together with `2(f - d) + 1 ≤ d - e`.

### 3.2 Normal form

The two pieces going to `S_v` contain two corners of `W`. Rotate `W` so that these corners are
`(0, 0)` and `(w-1, w-1)` (kind `diag`) or `(0, 0)` and `(0, w-1)` (kind `adj`). Call the pieces
*slots* `0, 1, 2, 3`: slots 0 and 2 go to `S_v`, slots 1 and 3 to `S_u`. Each slot `k` has a corner
box `box_k` and a motion `g_k(x, y) = M_k (x, y) + t_k` from `W` to its target square. Symmetries
of the two targets make `M_0` and `M_1` the identity. `M_2` and `M_3` are two of the eight
orientations, numbered `o2` and `o3`. This gives `2 × 8 × 8 = 128` cases `(kind, o2, o3)`. The
parameters are `d`, `e`, `f` and the eight integers of `t_0, …, t_3`.

A dissection gives a *normal form* `NF c p` (`Reduce.lean`): a map `σ` from cells of `W` to slots
such that

- (avail) the slot `k = σ(q)` is *available* at `q`: `q ∈ box_k` and `g_k(q)` lies in the target
  square of `k`;
- (inj) two cells whose slots have the same target and whose images are equal are equal;
- (surj) every cell of each target square is the image of some cell under its slot.

All later steps use only `NF`.

### 3.3 The tables

For the fat and mid regions there are 128 cases each, and for the thin region the 48 cases with
`kind = diag` and `o2 ∉ {0, 4}`; 304 *tables* in all. The other thin cases are treated by hand in
3.7. Each table `t` has a list of lemmas, and a formula

    tableF t = regionF ∧ domainF ∧ cover81F ∧ ¬lemma_1 ∧ … ∧ ¬lemma_n

built from linear inequalities in the 11 parameters (`Sem.lean`).

- `regionF`: the inequalities of the region.
- `domainF`: the *two-rectangle covering*. Each target square is covered by the images of the two
  slots that go to it, `g_k(box_k) ∩ S`. If two rectangles cover a square, one of them is the whole
  square, or both span it in the same direction and their intervals in the other direction meet.
- `cover81F`: a list of cells of `W`, with coordinates given by linear forms in the parameters,
  each of which has an available slot.
- `lemma_i`: a formula whose truth contradicts `NF` (3.4–3.6).

`tableF_true` shows that `NF` and the region imply `tableF t`. A *residual certificate* shows that
`tableF t` is false for every integer point. Together these refute every normal form of the table.

### 3.4 Closed structures (G1)

A *closed structure* is a list of `V` cells `q_i = M_i r + c_i`, where `r` is an integer *root* and
the `c_i` are linear in the parameters, together with a set `U_i` of slots for each cell, such that

- the slots available at `q_i` are exactly those of `U_i`;
- the *darts* `(i, k)` with `k ∈ U_i` pair off into `E` *edges* `{(i, k), (j, k ⊕ 2)}` with
  `g_k(q_i) = g_{k⊕2}(q_j)`. (`k ⊕ 2` is the other slot with the same target.)

**G1.** If a closed structure exists at the parameters of a normal form, then `V = E`.

Proof. Let `x(i, k) = 1` if `σ(q_i) = k` and 0 otherwise. For each cell, `σ(q_i)` is available, so
`Σ_{k ∈ U_i} x(i, k) = 1`. For each edge `{(i, k), (j, k ⊕ 2)}` the source cell
`s = g_k(q_i)` lies in the target square, so by (surj) some cell hits it, with slot `k` or `k ⊕ 2`.
That cell is `q_i` or `q_j`, and by (inj) only one of the two hits `s`; if `q_i` and `q_j` are the
same cell, `σ` takes one value there. So `x(i, k) + x(j, k ⊕ 2) = 1`. Summing over cells gives `V`,
summing over edges gives `E`, and both sums count every dart once. ∎

No assumption that the `q_i` are distinct, or that the structure is connected, is needed. So a
closed structure with `V ≠ E` contradicts `NF`. The structures in the data are trees, with
`V = E + 1`. (File `Count.lean`, theorem `G1`.)

### 3.5 Pigeonhole (G2) and root elimination (G3)

**G2.** If `V + 1` source cells of one target square are pairwise distinct, and every cell that can
hit one of them is among `V` listed cells, then there is no normal form: by (surj) each source cell
has a preimage among the listed cells, and these preimages are distinct.

**G3.** The conditions on the root `r = (r_x, r_y)` are linear constraints, each with one
coordinate of `r` and coefficient `±1` or `±2`. `elim` turns them into linear inequalities in the
parameters alone: for every lower and upper bound on the same coordinate, the lower bound is at
most the upper bound. When both coefficients are `±2` this is not enough for an integer root, and
`elim` uses the stronger inequality `lower ≤ upper - 1` instead. If all of these inequalities hold,
an integer root exists (`elim_sound`).

### 3.6 The three kinds of lemma, and the residual certificates

The lemma data is the file `data/t22_lemmas.txt`: 304 tables with 3039 lemmas in all.

- `shape` (2683 lemmas): a closed structure with `V = E + 1`. The root ranges over a finite list of
  representative values, each a linear form in the parameters. The formula says that for some
  representative all the conditions hold. Any list of representatives is sound, since each one is a
  separate root. A static check `closedOK` confirms that the darts pair off.
- `tplTree` (212 lemmas): a closed structure with `V = E + 1`, stored as a certificate (cells, a
  point of the parameters and a root). The conditions are rebuilt in Lean; a slot outside `U_i`
  contributes the negation of the first of its conditions that fails at the stored point. The root
  is eliminated by G3, and G1 gives the contradiction.
- `tplOver` (144 lemmas): `V + 1` source cells and `V` cells, stored the same way. The conditions say
  that the source cells lie in their square, that each possible preimage is a listed cell or lies
  outside its box, and that the source cells are pairwise distinct, each pair separated by an
inequality on one coordinate. G3 removes
  the root and G2 gives the contradiction.

`lemmaF_false` proves, for every lemma of each kind and whatever its data, that a normal form makes
its formula false. So nothing about the data needs to be trusted: a wrong lemma can only make a
residual certificate fail.

The residual certificates (`data/t22_res_0.txt`, `t22_res_1.txt`, `t22_res_2.txt`) prove that
`tableF t` has no integer solution, one certificate per table. A certificate is a tree. Its nodes
split on `h ≥ 0` or `h ≤ -1` for a linear form `h`, branch on the children of a disjunction, add
consequences, or close a branch by a Farkas combination: a non-negative integer combination of the
known inequalities that is a negative constant. The checker `checkCert` and its soundness theorem
`checkCert_sound` are in `Residual.lean`. `resOK` in `Main.lean` checks all 304 certificates and
that every table key of 3.3 has a table; it is evaluated by `native_decide`.

### 3.7 The thin region by hand

**Kind `adj`.** The cell `(v, u)` lies in `W` and in no corner box, since `u < a` in the thin
region (`thin_adj` in `Lemma0.lean`).

**Kind `diag`, `o2 ∈ {0, 4}`** (`Thin.lean`). Let `T` be the cells of `W` outside the boxes of
slots 1 and 3; only slots 0 and 2 can cover them, and `T ⊇ [0, a)^2 ∪ [u, w)^2`. Let
`h = g_2^{-1} g_0`. For `o2 = 0`, `h` is a translation by `τ`; for `o2 = 4` it is a diagonal flip
followed by a translation, and `h^2` is a translation.

*Chain principle.* Suppose `q_0, …, q_n` are cells of `T`, `q_{i+1} = h(q_i)`, slot 2 is not
available at `q_0`, and slot 0 is not available at `q_n`. Then `σ(q_0) = 0`. If `σ(q_i) = 0` and
`σ(q_{i+1}) = 2`, the two cells hit the same source cell, which contradicts (inj); so
`σ(q_{i+1}) = 0` for all `i`, and slot 0 is not available at `q_n`, a contradiction.

The rest of `Thin.lean` builds such a chain in every case. Write `g_0(x, y) = (x + e_1, y + f_1)`;
`e_1, f_1 ≥ 0` because the corner `(0, 0)` is covered, and `e_1, f_1, e_2, f_2 ≤ u - d`. The
two-rectangle covering leaves a few structures for `(e_1, f_1, e_2, f_2)`. The cases below, with
their rotated and transposed versions, cover all of them; the versions are proved directly, in
rotated or transposed coordinates.

- `o2 = 0`, `e_2 = f_2 = 0`, `s ≥ t` where `τ = (s, t)`: choose `k` with `ks < u ≤ (k+1)s`, start at
  `q_0 = (0, max(0, u - (k+1)t))` and step by `τ`. The first `k + 1` cells lie in `[0, a)^2`, the
  later ones in `[u, w)^2`, so all lie in `T`.
- `o2 = 0`, `f_1 = f_2 = 0`: the same, with the starting `x` chosen so that the chain stays in `W`.
- `o2 = 4`, `e_2 = f_2 = 0`: the chain alternates its two step lengths between the coordinates; the
  partial sums of `x` dominate those of `y`, and the same choice of start works, since `T` is
  symmetric under transposition.
- `o2 = 4`, strip case (`e_1, f_2 ≥ 1`, `f_1 = e_2 = 0`, or its transpose): two strips of cells are
  forced to slot 2 and to slot 0, and the cell where they cross would be hit by two source cells.

### 3.8 Assembly

`no_two_two` in `Main.lean`: `reduce` gives a normal form; `params_of_triple` and `lemma0` place
the parameters in a region; thin `adj` and thin `diag` with `o2 ∈ {0, 4}` are refuted by 3.7; every
other case has a table, refuted by `tableF_true` and its residual certificate.

## Where the data came from

The lemmas were found by a counterexample-guided search: a solver proposed a parameter point not
yet refuted, the actual cover problem at that point was solved to find a small closed structure or
an overfull set of source cells, and this structure was written as a lemma with symbolic
coordinates. The residual certificates were produced by an SMT solver and a linear programming
solver. None of these programs is part of this repository, and no theorem depends on them: every
lemma and every certificate is checked in Lean.
