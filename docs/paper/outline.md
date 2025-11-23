# Computational Paths Paper Outline

1. **Abstract** – high-level motivation, summary of contributions (Lean mechanisms, rewriting toolkit, fundamental group computations).
2. **Introduction** – background on equality in Martin-Löf type theory, computational paths programme, Lean project goals, summary of main results (Lean developments + topological examples), overview of paper structure.
3. **Identity Types and Computational Paths**
   - 3.1 Identity types in intensional Martin-Löf type theory (cite Martin-Löf, Hofmann–Streicher, van den Berg–Garner, HoTT book).
   - 3.2 Explicit computational paths and rewrite sequences (cite de Queiroz–de Oliveira–Ramos SAJL 2016).
   - 3.3 The LNDEQ rewrite system, Knuth–Bendix completion, normalization/confluence (cite SAJL paper + Ramos thesis).
4. **Lean 4 Formalization Infrastructure**
   - 4.1 Path syntax, rewrite closures (`Rw`, `RwEq`), quotient `PathRwQuot`.
   - 4.2 Contextual congruences, substitution transport, dependent contexts.
   - 4.3 Termination witnesses and automation (`Termination.Witness`, `Confluence.Join`).
   - 4.4 Tooling & connection to Lean’s metaprogramming (cite de Moura et al. 2015 for Lean).
5. **Homotopical Applications**
   - 5.1 Weak bicategory & two-groupoid packaging.
   - 5.2 Encode–decode proof of 𝜋₁(S¹) ≅ ℤ.
   - 5.3 Torus π₁(T²) ≅ ℤ × ℤ.
   - 5.4 Interfaces for future HITs / univalence specializations (cite HoTT book + Awodey 2012).
6. **Labelled Natural Deduction and Fundamental Groups**
   - Bridge to Veras–Ramos–de Queiroz–de Oliveira 2019 labelled natural deduction method.
   - How Lean formalization re-derives Klein bottle and higher-genus cases.
7. **Evaluation**
   - Proof artefacts (files/LOC), reusability, automation coverage, run-time (lake build stats), comparison to HoTT proof mechanisations.
8. **Related Work** – computational paths line, HoTT/Agda/Coq formalizations, type-theoretic presentations of π₁, rewriting-based equality.
9. **Future Directions** – general HIT semantics, automation for dependent contexts, integration with cubical Lean.
10. **Conclusion** – recap contributions, emphasise Lean as reference implementation.

## References to include
- de Queiroz, de Oliveira, Ramos (2016) SAJL article.
- Veras, Ramos, de Queiroz, de Oliveira (2019) arXiv:1906.09107.
- Hofmann & Streicher (1994) groupoid model.
- van den Berg & Garner (2011) weak ω-groupoids.
- Lumsdaine (2009) weak ω-categories from type theory.
- Awodey (2012) Type Theory and Homotopy.
- Univalent Foundations Program (2013) HoTT book.
- de Moura et al. (2015) Lean system description.
- Martin-Löf (1984) Intuitionistic Type Theory (optional).
- Additional references for transport/rewriting if needed (Ramos thesis, etc.).
