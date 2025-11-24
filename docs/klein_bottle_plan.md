# Klein bottle π₁ roadmap

This note records the concrete steps needed to finish the fundamental-group calculation following [De Oliveira, Ramos (2019)](https://arxiv.org/pdf/1906.09107).

1. Encode words ^m b^n as pairs (m, n) using the existing KleinBottleWord structure.
2. Prove that multiplication and inversion of normal forms matches the semidirect-law ^m b^n ⋅ a^{m'} b^{n'} = a^{m+m'} b^{(-1)^{m'} n + n'}.
3. Show that kleinDecode sends (m, n) to the corresponding loop class ^m ⋅ b^n and is a group homomorphism.
4. Identify the action of  on  via conjugation (ba⁻¹ = b⁻¹) and package it as a ℤ ⋊ ℤ description.
5. Mirror the encode/decode proof from the torus case to obtain π₁(K) ≅ ℤ ⋊ ℤ.

Step 2 expands into the following concrete lemmas inside `ComputationalPaths/Path/HIT/KleinBottle.lean`:

- `kleinLoopBClass_zpow_mul_loopAClass : b^n ⋅ a = a ⋅ b^{-n}` (already true for `Nat`-powers; extend to `Int`).
- `kleinSign_succ : kleinSign (m + 1) = -kleinSign m`, giving the parity toggle used in the semidirect exponent.
- `kleinLoopBClass_zpow_mul_loopAClass_zpow : b^n ⋅ a^m = a^m ⋅ b^{kleinSign m ⋅ n}` proved by induction on `m` (using the previous two lemmas).

Once the commuting lemma is in place, Step 3 becomes a bookkeeping exercise:

- Rewrite `KleinBottleWord.toLoopQuot` via the `LoopQuot.zpow` presentation (`toLoopQuot_eq_zpow` is already available).
- Use the commuting lemma to normalize `toLoopQuot w₁ ⋅ toLoopQuot w₂`, then collapse the `a`- and `b`-parts with `LoopQuot.zpow_add` to read off the pair `(w₁.a + w₂.a, kleinSign w₂.a * w₁.b + w₂.b)`.
- Package this as `KleinBottleWord.toLoopQuot_mul` and, via `toPair/ofPair`, obtain `kleinDecode_pairMul`.

Lean tips
- Reuse the LoopQuot lemmas from ComputationalPaths/Path/Homotopy/Loops.lean to control z-powers.
- Normal-form arithmetic can be handled in KleinBottleWord to keep heavy rewrites outside the LoopQuot level.
- Once the algebra is discharged, we can follow the 	orusPiOneEquivIntProd template for the final equivalence.
