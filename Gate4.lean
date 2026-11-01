import Ex89.RookCheck
open Ex89
/-- `checkR` on triples with a known answer. -/
def main (args : List String) : IO Unit := do
  let [u, v, w] := args.map String.toNat! | IO.println "usage: u v w"
  let t0 ← IO.monoMsNow
  let r ← IO.lazyPure fun _ => checkR u v w
  let t1 ← IO.monoMsNow
  IO.eprintln s!"checkR {u} {v} {w} = {r}  ({t1 - t0} ms)"
  (← IO.getStderr).flush
  IO.Process.exit 0
