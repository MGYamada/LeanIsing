import LeanIsing.App
import LeanIsing.QuantumApp

def main (args : List String) : IO UInt32 :=
  if args.contains "--quantum" then
    LeanIsing.QuantumApp.main (args.filter (· != "--quantum"))
  else
    LeanIsing.App.main args
