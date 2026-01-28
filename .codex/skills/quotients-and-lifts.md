# Quotients & Lifts

Use this checklist when writing or refactoring code that maps out of a quotient or proves equalities in quotient types.

- To define `Quot r → B`, use `Quot.lift f (by intro a b hab; ...)`.
- The “respects relation” obligation usually comes from a lemma of the form `r a b → f a = f b`.
- To prove equality inside a quotient, use `Quot.sound` with a proof of the underlying relation.
- For nested quotients, prefer nested `Quot.lift` + `funext` + `Quot.ind` (Lean 4 often lacks convenient `liftOn2` helpers).

Useful repo examples:
- `ComputationalPaths/Path/CompPath/CircleCompPath.lean` uses `Quot.lift` for an `encode`-style map.
