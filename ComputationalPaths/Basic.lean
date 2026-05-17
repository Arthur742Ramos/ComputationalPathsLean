/-
# Core exports for the Computational Paths library

Import this file to access the foundational definitions for computational
paths.  Additional modules provide rewrite systems and higher-structure
constructions.  This module also exposes lightweight repository metadata used
by the executable smoke entrypoint.
-/

/- Core computational-path exports. -/
import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.SimpleEquiv
import ComputationalPaths.Path.Rewrite.Step
import ComputationalPaths.Path.Rewrite.Rw
import ComputationalPaths.Path.Rewrite.RwEq
import ComputationalPaths.Path.Rewrite.Quot
import ComputationalPaths.Path.Groupoid

namespace ComputationalPaths

/- Library metadata kept dependency-free so `ComputationalPaths.Basic` remains lightweight. -/

/-- Human-readable library name for the executable smoke entrypoint. -/
def libraryName : String := "Computational Paths"

/-- Library version marker. Keep in sync with `lakefile.lean` package version. -/
def libraryVersion : String := "0.1.0"

/-- Repository slug shown by the executable entrypoint. -/
def libraryRepository : String := "Arthur742Ramos/ComputationalPathsLean"

/-- Compact import for the stable core path and rewrite surface. -/
def libraryCoreEntrypoint : String := "ComputationalPaths.Basic"

/-- Full-library import hub for broad companion material. -/
def libraryFullEntrypoint : String := "ComputationalPaths"

/-- Lake executable name for the smoke entrypoint. -/
def libraryExecutableName : String := "computational_paths"

end ComputationalPaths
