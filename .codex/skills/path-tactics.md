# Path Tactics

Use these when you’re stuck in an `RwEq` proof and the goal is mostly groupoid laws / cancellation / reassociation.

- Import: `ComputationalPaths.Path.Rewrite.PathTactic`
- First try: `path_auto`
- Cleanup step: `path_simp` (kills `trans refl _`, `trans _ refl`, trivial cancellations)
- If sides differ only by parentheses: `path_normalize`, then retry `path_auto`
- Prefer `calc` chains with the project’s `÷` notation for readability

