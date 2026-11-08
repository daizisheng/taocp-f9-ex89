import Ex89.T22.Defs
/-!
# The 2+2 theorem: lemma data file → `List Table`, and `Fml` export

`data/t22_lemmas.txt` is produced by a search program that is not part of this repository. It is read with
`include_str` and parsed here. **Nothing about the parser is proved**: the main theorem quantifies over
the parsed `tables`, and every fact used about them is checked by `native_decide`; a wrong parse can only
make such a check fail.

Format (whitespace-separated tokens; newlines only for readability):

* file   := `N` n table^n `E`
* table  := `T` region kind o2 o3 m lemma^m          (region ∈ fat/mid/thin, kind ∈ diag/adj)
* lemma  := `S` nv vert^nv nx lf^nx ny lf^ny          (`LemmaData.shape`)
          | `P` nv vert^nv lf11 rx ry                  (`LemmaData.tplTree`; `lf11` = the 11 `vals`)
          | `O` nv vert^nv ne edge^ne lf11 rx ry       (`LemmaData.tplOver`; verts have nu = 0)
* vert   := m00 m01 m10 m11 lf12 lf12 nu k^nu         (`Vert`: M, cx, cy, used)
* edge   := p k q k2                                   (`OEdge`; q = -1 for a half edge, then k2 = k xor 2)
* lf12   := 12 integers (coefficients of d e f t0x t0y t1x t1y t2x t2y t3x t3y, then the constant)
-/
namespace Ex89.T22
namespace Parse

/-- Parser monad: position in the byte array. -/
abbrev PM := StateT Nat (Except String)

@[inline] def isWs (c : UInt8) : Bool := c == 32 || c == 10 || c == 13 || c == 9

partial def skipWs (b : ByteArray) (i : Nat) : Nat :=
  if h : i < b.size then (if isWs b[i] then skipWs b (i + 1) else i) else i

partial def digits (b : ByteArray) (i acc : Nat) (nd : Nat) : Nat × Nat × Nat :=
  if h : i < b.size then
    let c := b[i]
    if 48 ≤ c && c ≤ 57 then digits b (i + 1) (10 * acc + (c - 48).toNat) (nd + 1) else (acc, i, nd)
  else (acc, i, nd)

partial def wordEnd (b : ByteArray) (i : Nat) : Nat :=
  if h : i < b.size then (if isWs b[i] then i else wordEnd b (i + 1)) else i

def int (b : ByteArray) : PM Int := do
  let i := skipWs b (← get)
  let (ng, i) := if h : i < b.size then (if b[i] == 45 then (true, i + 1) else (false, i)) else (false, i)
  let (v, j, nd) := digits b i 0 0
  if nd == 0 then throw s!"integer expected at byte {i}"
  set j
  return if ng then -(v : Int) else (v : Int)

def nat (b : ByteArray) : PM Nat := do
  let v ← int b
  if v < 0 then throw s!"natural number expected, got {v}"
  return v.toNat

def word (b : ByteArray) : PM String := do
  let i := skipWs b (← get)
  let j := wordEnd b i
  if j == i then throw s!"word expected at byte {i}"
  set j
  let mut s := ""
  for k in [i:j] do s := s.push (Char.ofNat b[k]!.toNat)
  return s

def expect (b : ByteArray) (w : String) : PM Unit := do
  let w' ← word b
  if w' != w then throw s!"expected '{w}', got '{w'}'"

def fin (b : ByteArray) (n : Nat) : PM (Fin n) := do
  let v ← nat b
  if h : v < n then return ⟨v, h⟩ else throw s!"value {v} not below {n}"

def many {α : Type} (n : Nat) (p : PM α) : PM (List α) := do
  let mut a : Array α := Array.mkEmpty n
  for _ in [0:n] do a := a.push (← p)
  return a.toList

def lf (b : ByteArray) : PM LF := many 12 (int b)

def vert (b : ByteArray) : PM Vert := do
  let m00 ← int b; let m01 ← int b; let m10 ← int b; let m11 ← int b
  let cx ← lf b; let cy ← lf b
  let nu ← nat b; let used ← many nu (fin b 4)
  return { m := ⟨m00, m01, m10, m11⟩, cx, cy, used }

def oedge (b : ByteArray) : PM OEdge := do
  let p ← nat b; let k ← fin b 4; let q ← int b; let k2 ← fin b 4
  return { p, k, q, k2 }

def verts (b : ByteArray) : PM (List Vert) := do many (← nat b) (vert b)

def lemma (b : ByteArray) : PM LemmaData := do
  match ← word b with
  | "S" =>
    let vs ← verts b
    let xs ← many (← nat b) (lf b)
    let ys ← many (← nat b) (lf b)
    return .shape vs xs ys
  | "P" =>
    let vs ← verts b; let vals ← many 11 (int b); let rx ← int b; let ry ← int b
    return .tplTree vs vals rx ry
  | "O" =>
    let vs ← verts b; let es ← many (← nat b) (oedge b)
    let vals ← many 11 (int b); let rx ← int b; let ry ← int b
    return .tplOver vs es vals rx ry
  | w => throw s!"unknown lemma tag '{w}'"

def region (b : ByteArray) : PM Region := do
  match ← word b with
  | "fat" => return .fat
  | "mid" => return .mid
  | "thin" => return .thin
  | w => throw s!"unknown region '{w}'"

def kind (b : ByteArray) : PM Kind := do
  match ← word b with
  | "diag" => return .diag
  | "adj" => return .adj
  | w => throw s!"unknown kind '{w}'"

def table (b : ByteArray) : PM Table := do
  expect b "T"
  let r ← region b; let k ← kind b; let o2 ← fin b 8; let o3 ← fin b 8
  let ls ← many (← nat b) (lemma b)
  return { region := r, case := ⟨k, o2, o3⟩, lemmas := ls }

def file (b : ByteArray) : PM (List Table) := do
  expect b "N"
  let ts ← many (← nat b) (table b)
  expect b "E"
  if skipWs b (← get) != b.size then throw "trailing data"
  return ts

end Parse

/-- Parse the lemma data file. -/
def parseTables (s : String) : Except String (List Table) :=
  (Parse.file s.toUTF8).run' 0

/-- The lemma data. -/
def lemmaText : String := include_str "../../data/t22_lemmas.txt"

/-- The parsed tables (empty on a parse error, which makes every coverage check fail). -/
def tables : List Table :=
  match parseTables lemmaText with
  | .ok ts => ts
  | .error _ => []

/-- The 304 (region, case) keys: fat and mid for all 128 cases; thin for diag with `o2 ∉ {0, 4}`
(thin-adj is excluded by Lemma 0, thin-diag `o2 ∈ {0,4}` by the chain argument). -/
def allKeys : List (Region × Case) :=
  let cases (k : Kind) : List Case :=
    (List.finRange 8).flatMap fun o2 => (List.finRange 8).map fun o3 => ⟨k, o2, o3⟩
  ((cases .diag ++ cases .adj).map ((Region.fat, ·))) ++
  ((cases .diag ++ cases .adj).map ((Region.mid, ·))) ++
  ((cases .diag).filter (fun c => c.o2.val != 0 && c.o2.val != 4)).map ((Region.thin, ·))

/-- Number of lemmas in all tables. -/
def lemmaCount : Nat := tables.foldl (fun n t => n + t.lemmas.length) 0

/-- Smoke test of `include_str` + `native_decide` at the full data size. -/
theorem tables_cover :
    (allKeys.length == 304 &&
      allKeys.all fun k => tables.any fun t => t.region == k.1 && t.case == k.2) = true := by
  native_decide

/-! ## `Fml` export (prefix text, used by the certificate generator) -/

/-- Exactly 12 coefficients: pad with `0`, drop entries beyond index 11. -/
def LF.pad12 (l : LF) : List Int := (l ++ List.replicate 12 0).take 12

/-- Append the dump of `f` to `s`, each token preceded by one space. -/
partial def Fml.dumpTo (s : String) : Fml → String
  | .atom l => (LF.pad12 l).foldl (fun s c => (s.push ' ') ++ toString c) (s ++ " a")
  | .and fs => fs.foldl Fml.dumpTo (s ++ " & " ++ toString fs.length)
  | .or fs => fs.foldl Fml.dumpTo (s ++ " | " ++ toString fs.length)

/-- Prefix text of a formula: `a c0 … c11`, `& n f₁ … fₙ`, `| n f₁ … fₙ`, single spaces. -/
def Fml.dump (f : Fml) : String :=
  let s := Fml.dumpTo "" f
  String.Pos.Raw.extract s ⟨1⟩ ⟨s.utf8ByteSize⟩

/-- Streaming version of `Fml.dump` (same text), for large formulas. -/
partial def Fml.dumpIO (h : IO.FS.Stream) (first : Bool) : Fml → IO Unit
  | .atom l =>
    h.putStr ((LF.pad12 l).foldl (fun s c => (s.push ' ') ++ toString c) (if first then "a" else " a"))
  | .and fs => do
    h.putStr ((if first then "& " else " & ") ++ toString fs.length)
    for f in fs do Fml.dumpIO h false f
  | .or fs => do
    h.putStr ((if first then "| " else " | ") ++ toString fs.length)
    for f in fs do Fml.dumpIO h false f

end Ex89.T22
