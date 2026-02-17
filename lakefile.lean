import Lake
open Lake DSL

package «ComputationalPaths» where
  leanOptions := #[]

@[default_target]
lean_lib «ComputationalPaths» where
  globs := #[.submodules `ComputationalPaths]
