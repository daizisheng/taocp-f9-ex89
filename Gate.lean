import Ex89.Check
open Ex89
def lens (c : Cfg) : List Nat := let pv := c.mkPv; [(c.L pv 0).length,(c.L pv 1).length,(c.L pv 2).length,(c.L pv 3).length]
def timed (n : String) (f : Unit → Bool) : IO Unit := do
  let t0 ← IO.monoMsNow
  let r ← IO.lazyPure f
  let e := r && true
  IO.println s!"{n} = {e}  ({(← IO.monoMsNow) - t0} ms)"
def main (a : List String) : IO Unit := do
  let [us, vs, ws] := a.map String.toNat! | IO.println "usage"
  IO.println (lens (cfgDiag us vs ws)); IO.println (lens (cfgAdj us vs ws))
  IO.println (lens (cfgU us vs ws)); IO.println (lens (cfgV us vs ws))
  let c := cfgDiag us vs ws; let pv := c.mkPv
  IO.println ((c.pairs pv 0 2).length,(c.pairs pv 1 3).length)
  let c := cfgAdj us vs ws; let pv := c.mkPv
  IO.println ((c.pairs pv 0 1).length,(c.pairs pv 2 3).length)
  timed "diag" fun _ => check22 (cfgDiag us vs ws) 0 2 1 3
  timed "adj " fun _ => check22 (cfgAdj us vs ws) 0 1 2 3
  timed "1+3 " fun _ => check13 (cfgU us vs ws)
  timed "3+1 " fun _ => check13 (cfgV us vs ws)
