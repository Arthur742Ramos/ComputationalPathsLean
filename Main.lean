import ComputationalPaths.Basic

open ComputationalPaths

def main : IO Unit := do
  IO.println s!"{libraryName} library version {libraryVersion}"
  IO.println s!"Repository: {libraryRepository}"
  IO.println s!"Core import: import {libraryCoreEntrypoint}"
  IO.println s!"Full import: import {libraryFullEntrypoint}"
  IO.println s!"Executable: lake exe {libraryExecutableName}"
