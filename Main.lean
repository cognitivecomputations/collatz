import Collatz

def main : IO Unit := do
  IO.println s!"Hello, {hello}!"
  let test : Prop := ∃ k, collatzIter 5 k = 1
  IO.println s!"Test: {test}"
