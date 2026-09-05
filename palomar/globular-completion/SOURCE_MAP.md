# Source and claim correspondence

## Source version

The accepted manuscript is *Computational Paths Form a Weak omega-Groupoid:
A Constructive Proof*, by Arthur F. Ramos, Tiago M. L. de Veras,
Ruy J. G. B. de Queiroz, and Anjolina G. de Oliveira.

The privately supplied PDF has 49 pages and SHA-256
`f53d7b1241de79a216d4cd2c37a17f173142d21cf96204115c2535b1dd0a6109`.
The public [arXiv locator](https://arxiv.org/abs/2512.00657) identifies an earlier
24-page version, not that accepted PDF. The manuscript is not embedded in this
repository. No claim of its public availability or publisher licensing is made.

## Adaptation, not an unchanged formalization

| Source or predecessor | This package | Exact relationship |
| --- | --- | --- |
| Accepted Definitions 3.9 and 3.12 | CellDerivation, extend, tower | Retains an explicit automatic-premise filler; recursively enforces parallel boundaries at every dimension |
| Accepted Section 4 | source_globular, target_globular | Checks the two globular identities on the actual recursive family |
| Accepted Section 5 | identityCell_boundary, inverseCell_boundary, compose_boundary | All-dimensional identities/inverses and higher vertical composition; not a full all-dimensional horizontal structure |
| Accepted Theorem 6.3 and higher pattern | inhabited_iff_parallel, higher_filling | Chosen parallel filling, explicitly relative to the completion constructors |
| Accepted Theorem 7.9 | pentagon_distinct_connected | Retains two explicit distinct rewrite routes and joins their bundled 2-cells |
| Accepted Theorem 10.1 | Not selected | No full operadic weak omega-groupoid theorem |
| Accepted Theorem 10.2 | Excluded | No identification with identity-type omega-groupoids |
| Accepted Section 11.1 | Divergence disclosed | Path is a trace-decorated Eq record, not the claimed deep embedding |
| Repair at 48eb008f27e485894b17a224a64f379e90711e1f | Recursive tower definitions | Same construction, now standalone and accompanied by the interpretation and functoriality theorems |

The new layerwise universal property and functorial extension are mathematical
additions to this adaptation, not claims attributed to the accepted paper.

## Code correspondence

Path, Step, RwEq, RwEq.stepCount, pentagonLeft, and pentagonRight are the
definitions from the earlier standalone extract at
`c5b35d854c4271f5216d33539526a28648d7dde9`, with namespace and documentation
changes. The seven Step constructors are visible in the Challenge.
Unused operations and the flawed old higher tail are not imported.

The generator syntax differs from the manuscript's full list of named
meta-step constructors: this package uses only the chosen parallel generator,
identity, inversion and composition. It does not claim a bijection between
all source meta-derivations and its expressions. Groupoid-law comparisons can
be formed one dimension higher by the chosen generator.

There is no import bridge masquerading as a correspondence theorem. The
exact retained syntax is visible in the submitted statement. The preserved
2-skeleton is an explicit definition, and pentagon_distinct_connected proves
a concrete non-identification property.

## Related higher-category results

[Lumsdaine](https://arxiv.org/abs/0812.0409) and
[van den Berg and Garner](https://arxiv.org/abs/0812.0298) concern the stronger
identity-type higher-category constructions. They are background, not results
reproved by this package. A generator connecting parallel expressions must
not be confused with an operadic action or with equality of those expressions.

