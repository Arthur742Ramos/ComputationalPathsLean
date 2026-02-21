/-
# Core exports for the Computational Paths library

Import this file to access the foundational definitions for computational
paths.  Additional modules provide rewrite systems and higher-structure
constructions.
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.SimpleEquiv
import ComputationalPaths.Path.Rewrite.Step
import ComputationalPaths.Path.Rewrite.Rw
import ComputationalPaths.Path.Rewrite.RwEq
import ComputationalPaths.Path.Rewrite.Quot
import ComputationalPaths.Path.Groupoid

namespace ComputationalPaths

/-- Library version marker.  Bump as the formalisation progresses. -/
def libraryVersion : String := "0.1.0"

end ComputationalPaths
