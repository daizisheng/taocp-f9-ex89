import Ex89.Check
open Ex89
def main (a : List String) : IO Unit := do
  let [us, vs, ws] := a.map String.toNat! | IO.println "usage"
  let t0 ← IO.monoMsNow
  let r ← IO.lazyPure fun _ => checkAll us vs ws
  IO.println s!"checkAll = {r && true}  ({(← IO.monoMsNow) - t0} ms)"
