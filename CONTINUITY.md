# CONTINUITY.md

## Goal
- Remove legacy axiomatic-space wording from non-Lean documentation, reflecting computational paths only
- Keep build clean after documentation updates

## Constraints/Assumptions
- No questions unless blocked; follow repo conventions
- Must run `~/.elan/bin/lake build` after documentation updates
- Keep messaging consistent with computational paths (no legacy axiomatic-space references)

## Key Decisions
- Update non-Lean docs to remove/replace legacy axiomatic-space mentions with computational paths phrasing

## State
- **Done**: Updated non-Lean docs to remove legacy axiomatic-space references; `~/.elan/bin/lake build` clean
- **Now**: Await next request
- **Next**: None

## Working Set
- Commands: `~/.elan/bin/lake build`
- Search for: legacy axiomatic-space wording around constructors/recursors
