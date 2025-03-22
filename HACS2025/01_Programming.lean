
/-
Lean is a general purpose programming language:
===============================================
-/

import Std

def histogram (filename : String) : IO Unit := do
  let ls ← IO.FS.lines filename
  let mut counts : Std.TreeMap String Nat := .empty
  for l in ls do
    counts := counts.insert l (counts[l]?.getD 0 + 1)
  let entries := counts.toArray.qsort (·.2 > ·.2)
  for (line, count) in entries do
    if count > 1 then
      IO.println s!"{count}: {line}"

-- #eval histogram "lake-manifest.json"
