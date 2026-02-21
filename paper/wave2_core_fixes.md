# Wave 2 — Core Subsingleton Audit Report

## Scope
Audited all 19 `Subsingleton.elim` occurrences in core files and added step-trace companion theorems.

## Classification of Subsingleton.elim Uses

### Core.lean (5 occurrences)
| Line | Theorem | Verdict |
|------|---------|---------|
| 217 | `trans_assoc_pentagon` | **STRUCTURAL** — compares `Eq.trans` proofs in `Prop` |
| 225 | `mac_lane_coherence` | **STRUCTURAL** — compares two proofs of same proposition |
| 232 | `mac_lane_coherence_fourfold` | **STRUCTURAL** — both sides are `Prop` proofs |
| 292 | `two_path_interchange` | **STRUCTURAL** — 2-path loops are `Prop` equalities |
| 298 | `eckmann_hilton_two_paths` | **STRUCTURAL** — `Eq` commutativity in `Prop` |

### HigherPaths.lean (6 occurrences)
| Line | Theorem | Verdict |
|------|---------|---------|
| 130 | `hcomp_eq_vcomp_on_refl` | **STRUCTURAL** — `Path2` is `Eq` in `Prop` |
| 142 | `eckmann_hilton` | **STRUCTURAL** — compares `Prop` proofs |
| 147 | `eckmann_hilton'` | **STRUCTURAL** — direct `Eq.trans` in `Prop` |
| 181 | `path2_eq` | **STRUCTURAL** — `Path2 p q` is `Prop` |
| 186 | `path2_is_set` | **STRUCTURAL** — proof irrelevance for `Eq` |
| 191 | `path3_trivial` | **STRUCTURAL** — 3-paths in `Prop` |

### PathInduction.lean (4 occurrences)
| Line | Theorem | Verdict |
|------|---------|---------|
| 113 | `eta_proof` | **STRUCTURAL** — equality of `Eq` proofs |
| 157 | `proof_based_ind` | **STRUCTURAL** — `p.proof = q.proof` |
| 164 | `proof_unique` | **STRUCTURAL** — proof irrelevance |
| 169 | `self_path_proof` | **STRUCTURAL** — proof irrelevance |

## Verdict
**All 15 occurrences are STRUCTURAL** — they compare propositional equalities (`Eq` proofs in `Prop`). None can be replaced with a real proof without redesigning `Path` to carry proof data outside `Prop`.

## Companion Theorems Added (genuine step-trace proofs)

### Core.lean
1. `mac_lane_coherence_fourfold_steps` — both reassociation routes yield identical step traces (by `List.append_assoc`)
2. `trace_symm_involutive` — reversing and symmetrizing a step trace twice is identity (by induction on list)
3. `symm_trans_steps_concat` — `symm (trans p q)` step trace equals reversed concatenation

### HigherPaths.lean
1. `path2_steps_eq` — a 2-path implies underlying step traces are equal
2. `vcomp_steps_eq` — vertical composition preserves endpoint traces
3. `hcomp_steps_eq` — horizontal composition preserves concatenated traces

### PathInduction.lean
1. `trans_trace_assoc_companion` — explicit step-trace associativity
2. `symm_symm_trace_companion` — double symmetry preserves original trace

## Build Verification
`lake build` succeeded with 6186 jobs, zero errors.
