# Goal: Perfect metadata-J theory paper

## User Request

Improve the current manuscript into the strongest possible mathematics/theory
paper. Center it on the metadata-fiber criterion for J, and develop any missing
computational-path theory in Lean when that strengthens the paper.

## Refined Goal

Produce a focused 15–20 page theory paper whose central contribution is a
general classification of when equality decorated with observable metadata
admits unrestricted based elimination with propositional beta. Formalize the
abstract total-space/J equivalence, metadata-fiber criterion, motive-factorization
result, and computational-trace corollary in Lean. Preserve the existing raw
de Bruijn calculus as a separately buildable companion manuscript rather than
letting it obscure the conceptual theorem.

## Acceptance Criteria

- [ ] A new public Lean module defines a generic equality refinement
  `R_M(a,b) = Σ h : a = b, M b h`, its based total space, a data structure for
  unrestricted based elimination with propositional beta, and an appropriate
  contractibility notion with explicit universe parameters.
- [ ] Lean proves unrestricted based elimination with propositional beta is
  equivalent to contractibility of the based total space, in both directions,
  without `sorry`, custom axioms, or hidden assumptions.
- [ ] Lean constructs the equivalence
  `(Σ b, Σ h : a = b, M b h) ≃ M a rfl`, proves contractibility is invariant
  under equivalence, and derives the named metadata-fiber criterion:
  unrestricted based elimination with propositional beta exists iff
  `M a rfl` is contractible.
- [ ] Lean proves a motive-factorization theorem: motives that factor through
  the projection to equality admit elimination even when unrestricted
  metadata-sensitive J fails.
- [ ] Lean proves `Path a b` is equivalent to the corresponding equality
  refinement with list-valued trace metadata and derives the no-J result from
  the generic metadata-fiber criterion, not only from a bespoke empty-trace
  motive.
- [ ] The trace corollary distinguishes the empty reflexive trace from a
  singleton well-formed reflexive step and explicitly shows that enforcing
  composability alone does not make visible trace metadata contractible.
- [ ] The new module contains substantive computational-path evidence,
  including a nontrivial `Path.trans` or `RwEq` certificate, and is exported
  from `ComputationalPaths.Path`.
- [ ] The main paper at `paper/adequacy/main.tex` is reorganized to 15–20 pages.
  The metadata-fiber criterion appears in the abstract and by page 2, receives
  a complete mathematical proof in the main text, and is clearly distinguished
  from the standard total-space/identity-space contraction argument.
- [ ] The paper characterizes the largest explicitly supported class of
  motives as equality-projection/factorizing motives and explains the two
  remedies for metadata-sensitive failure: restrict motives or hide/quotient
  metadata.
- [ ] The paper gives several mathematically meaningful examples beyond raw
  lists, such as derivation histories, costs, certificates, normalization logs,
  or proof labels, classifying which admit unrestricted J and which do not.
- [ ] The computational trace application is the principal case study. The
  paper states precisely that visible noncanonical reflexive metadata, not
  non-composability, causes the obstruction.
- [ ] The raw scoped-calculus material is preserved as a separately buildable
  companion manuscript or appendix source, while the focused main paper uses
  no more than a concise supporting discussion of that formal interface.
- [ ] The final exposition is a mathematics/type-theory paper, not a Lean paper.
  Formalization occupies at most one page and cites a stable theorem-bearing
  commit; a future Zenodo DOI is mentioned without a fake placeholder.
- [ ] The paper explicitly excludes full MLTT/HoTT modeling, univalence, HITs,
  and any claim that trace-carrying `Path` is the HoTT identity type.
- [ ] The focused paper and companion both compile with clean references and no
  meaningful overfull boxes; the focused PDF is between 15 and 20 pages.
- [ ] `lake build`, `python3 scripts/check_invariants.py`, `git diff --check`,
  and clean `latexmk` builds all succeed.
- [ ] An independent Inspector judges the mathematical statements, Lean
  correspondence, paper integration, and exposition to satisfy every criterion.

## Scope Boundaries

**In scope:**
- Generic theory of equality refinements by visible metadata.
- Based elimination with propositional beta and contractibility.
- Equality-projection motives and metadata hiding/quotienting.
- Formal Lean proofs of the headline abstract results and trace instance.
- A concise paper centered on the classification theorem.
- Preservation of the raw-calculus manuscript as a companion artifact.

**Out of scope:**
- Judgmental-beta classification unless it is separately and honestly proved.
- Full MLTT, HoTT, univalence, higher inductive types, normalization, or
  initiality.
- Claiming the metadata criterion itself replaces standard identity types.
- Claiming absolute historical priority without verified sources.
- Deleting the existing raw-calculus work merely to meet the page target.
- Turning the main paper into an implementation or proof-assistant report.

## Applicable Project Conventions

**Quality gate command:**
- `lake build`
- `python3 scripts/check_invariants.py`
- `git diff --check`
- `cd paper/adequacy && latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex`
- Build the companion manuscript independently with the same LaTeX checks.

**Commit convention:**
- Conventional commits are preferred.
- Builder commits use `feat(paths): [B] ...` or `docs(paper): [B] ...` and
  trailer `Assisted-by: OpenAI:GPT-5.6-Sol`.
- Inspector commits use `chore(paths): [I] ...` and trailer
  `Assisted-by: OpenAI:GPT-5.6-Luna`.

**Guidelines:**
- `AGENTS.md`
- No additional `CONSTITUTION.md` or guideline directory applies.

**Rules:**
- Zero `sorry`, `admit`, or custom `axiom`.
- Maintain genuine `Path` integration and substantive `RwEq` evidence.
- Do not use decorative certificates or success-shaped placeholders.
- Keep source syntax, ambient equality, trace records, and HoTT identity
  conceptually distinct.
- Use the formal artifact as verification of the mathematical theory, not as
  the paper’s primary motivation.
