# Routing Rules

## Signal → Agent Mapping

| Signal | Route To | Notes |
|--------|----------|-------|
| Architecture, scope, design decisions | Holden | Review authority on all code |
| Lean 4 code, Path/RwEq proofs, new modules, encode-decode | Naomi | Primary implementer |
| Build verification, sorry audit, axiom audit, proof checking | Amos | Verification and quality |
| Documentation, README, paper, module headers | Avasarala | All docs and paper work |
| "Team" or multi-domain | Holden + relevant agents | Holden coordinates |
| New space construction (S¹, T², etc.) | Naomi (impl) + Amos (verify) | Parallel |
| Armada deployment | Naomi (impl) + Amos (audit) + Holden (review) | Full pipeline |
| Quick factual question about codebase | Direct (no spawn) | Coordinator answers |

## Review Gates

- All new Lean files must pass Amos verification (no sorry, no axiom)
- Architecture changes require Holden approval
- Documentation changes reviewed by Avasarala
