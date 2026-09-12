# Certified preimages of finite-torus loop classes

Status: implemented research prototype. No publication, registry acceptance,
independent expert review, or mathematical priority is claimed.

This development was incubated in the focused
[TopologicalComputationalPaths](https://github.com/Arthur742Ramos/TopologicalComputationalPaths)
repository. This integrated version separates the reusable integer-matrix
checker from its finite-torus interpretation and validates both in the main
library's Lean 4.33 environment.

## Problem and semantics

Let `T^n = (R/Z)^n`, based at zero. An integer `m`-by-`n` matrix `A` induces a
continuous map `T^n → T^m`. For a target winding vector `z : Z^m`, the problem
is to describe all based loop homotopy classes mapped to the class of the
standard loop with winding `z`.

This is a preimage problem for homotopy classes. It is not pointwise path
lifting, a claim that every matrix map is a covering, or a finite encoding of
arbitrary black-box continuous paths. The existing winding classifier proves
that integer vectors represent every based loop class.

## Checked certificate

The topology-independent module
[`CertifiedIntegerMatrixPreimage.lean`](../ComputationalPaths/Path/Algebra/CertifiedIntegerMatrixPreimage.lean)
accepts integer data `(L, Linv, R, T, d)` and checks:

1. `Linv * L = I`;
2. `L * A = diag(d) * T`;
3. `L * A * R = diag(d)`; and
4. row `T i` is zero whenever `d i = 0`.

No ordered or positive Smith factors are required. After validation, the solver
computes `y = Lz`. A row for which `d i` does not divide `y i` is an explicit
obstruction. Otherwise it returns

```text
x0 = R (y / d),       K = I - R T,
solutions = { x0 + K v | v in Z^n }.
```

Here `0 ∣ y` means `y = 0`, and the candidate uses `0 / 0 = 0`. Lean proves
that `A * x0 = z`, that the image of `K` is exactly the integer kernel of `A`,
and that `K` is idempotent. The parameters need not be unique: `K` is a finite
kernel-generating projection, not necessarily a basis.

The zero-row condition is essential. The adversarial suite includes a modified
certificate that satisfies the first three identities but falsifies the fourth;
the executable checker rejects it.

## Topological bridge

[`CertifiedTorusPreimage.lean`](../ComputationalPaths/Path/Topology/CertifiedTorusPreimage.lean)
uses the concrete finite-torus classifier to prove:

- the computed vector defines an actual standard loop whose image is the target
  standard loop;
- matrix preimages are equivalent to preimages of quotient loop classes;
- every successful result describes all topological preimage classes; and
- every returned failed row proves the topological preimage is empty.

[`CertifiedTorusPreimageExistence.lean`](../ComputationalPaths/Path/Topology/CertifiedTorusPreimageExistence.lean)
uses Mathlib's noncomputable Smith-basis theory to prove that a valid certificate
exists for every rectangular integer matrix, including empty and rank-deficient
cases. This existence proof is not used to execute the solver.

The worked application in
[`TorusConstraintApplication.lean`](../ComputationalPaths/Path/Topology/TorusConstraintApplication.lean)
solves a simultaneous four-observation, three-source problem for all parameters
and proves that inconsistent redundant observations have no loop-class preimage.

## Trust and reproduction

The optional producer in `scripts/torus-preimage-certificate.py` uses the pinned
SymPy 1.14 Smith decomposition to propose certificate data. Python, SymPy, and
JSON are outside the trusted proof boundary. With `--verify`, the command builds
the Lean dependency and asks Lean to check the generated certificate, literal
answer, kernel matrix, obstruction data, and topological result before adding a
verification field to the JSON output.

```bash
python3 -m pip install -r scripts/requirements-torus-preimage.txt
scripts/check-torus-preimage.sh
python3 scripts/torus-preimage-certificate.py \
  examples/torus-preimage-coupled.json --verify
```

The quality gate checks 13 generated edge-case fixtures, five deterministic
benchmark fixtures, adversarial certificate mutations, exact regeneration
parity, and 100 seeded known-image producer cases. Only the checked-in Lean
fixtures are kernel-replayed; the randomized Python cases are supporting tests.
The gate forbids `sorry`, `admit`, custom axioms, `native_decide`, and
`Lean.ofReduceBool` in this boundary.

## Contribution boundary

Finite-torus winding and Smith normal form are classical mathematics. Verified
Smith algorithms also predate this development, including Cano et al.'s Coq
formalization and Divason's AFP entry. The contribution here is the integrated
certificate interface: it separates untrusted production from a small checker,
returns positive witnesses or explicit negative rows, describes every solution,
and connects those results to fixed topological semantics across all finite
dimensions and ranks.

Producer correctness and termination, asymptotic complexity, minimality of the
solution representation, mathematical novelty, and research significance are
not claimed. Those questions require separate analysis and independent review.
