import Muffin

def muffin := addmuffin 2 8

def main : IO Unit :=
  IO.println s!"Hello, {muffin} Muffins!"

#eval main
