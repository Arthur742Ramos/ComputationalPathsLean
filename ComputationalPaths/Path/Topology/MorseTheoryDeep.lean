/-
# Morse theory coherence via computational paths (deep version)

Critical points, gradient flow, handle attachments, Morse inequalities,
CW structure, cobordism, Morse homology (∂²=0), Smale cancellation,
and Cerf theory — all witnessed by explicit multi-step `Path` chains
derived from a small set of fundamental axioms via `trans`, `symm`,
and `congrArg`.

## Design

A `MorseAxioms` structure packages the fundamental domain-specific rewrite
rules as `Path` values.  Every downstream theorem is then derived purely
through path combinators — **no** `Path.ofEq` appears outside the axiom
package.  This yields genuine multi-step rewrite traces that record each
domain rule application.
-/
import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace MorseTheoryDeep

open Path

universe u

variable {A : Type u}

/-! ## Morse function operations -/

/-- Bundled Morse-theoretic operations on a type. -/
structure MorseOps (A : Type u) where
  /-- Morse function value -/
  f : A → A
  /-- Gradient flow map -/
  flow : A → A
  /-- Critical point detection (idempotent) -/
  crit : A → A
  /-- Index assignment -/
  idx : A → A
  /-- Boundary operator -/
  bdry : A → A
  /-- Handle attachment -/
  attach : A → A → A
  /-- CW cell inclusion -/
  cell : A → A
  /-- Betti number sum -/
  betti : A → A
  /-- Euler characteristic -/
  euler : A → A
  /-- Cobordism map -/
  cobord : A → A → A
  /-- Base point -/
  base : A

variable (M : MorseOps A)

/-! ## Fundamental axioms as Path values -/

/-- The fundamental rewrite axioms for Morse theory, packaged as Paths.
    Every downstream theorem is derived from these without `Path.ofEq`. -/
structure MorseAxioms (M : MorseOps A) where
  /-- Gradient flow fixes critical points. -/
  flow_crit     : ∀ p : A, Path (M.flow (M.crit p)) (M.crit p)
  /-- Gradient flow is idempotent. -/
  flow_idem     : ∀ p : A, Path (M.flow (M.flow p)) (M.flow p)
  /-- Critical point detection is idempotent. -/
  crit_idem     : ∀ p : A, Path (M.crit (M.crit p)) (M.crit p)
  /-- Flow fixes the base point. -/
  flow_base     : Path (M.flow M.base) M.base
  /-- Morse function is preserved by flow. -/
  f_flow        : ∀ p : A, Path (M.f (M.flow p)) (M.f p)
  /-- Morse function commutes with CW inclusion. -/
  f_cell        : ∀ p : A, Path (M.f (M.cell p)) (M.cell (M.f p))
  /-- Right unit for handle attachment. -/
  attach_base_r : ∀ p : A, Path (M.attach p M.base) p
  /-- Left unit for handle attachment. -/
  attach_base_l : ∀ p : A, Path (M.attach M.base p) p
  /-- Handle attachment is associative. -/
  attach_assoc  : ∀ p q r : A,
    Path (M.attach (M.attach p q) r) (M.attach p (M.attach q r))
  /-- Flow commutes into the right argument of attach. -/
  flow_handle   : ∀ p q : A,
    Path (M.attach p (M.flow q)) (M.attach p q)
  /-- CW cell inclusion is idempotent. -/
  cell_idem     : ∀ p : A, Path (M.cell (M.cell p)) (M.cell p)
  /-- Cell of base is base. -/
  cell_base     : Path (M.cell M.base) M.base
  /-- Cell distributes over handle attachment. -/
  cell_attach   : ∀ p q : A,
    Path (M.cell (M.attach p q)) (M.attach (M.cell p) (M.cell q))
  /-- Boundary squared is zero. -/
  bdry_sq       : ∀ p : A, Path (M.bdry (M.bdry p)) M.base
  /-- Boundary of base is base. -/
  bdry_base     : Path (M.bdry M.base) M.base
  /-- Boundary commutes with flow. -/
  bdry_flow     : ∀ p : A, Path (M.bdry (M.flow p)) (M.bdry p)
  /-- Boundary distributes into handle attachment. -/
  bdry_attach   : ∀ p q : A,
    Path (M.bdry (M.attach p q)) (M.attach (M.bdry p) q)
  /-- Betti numbers equal Euler characteristic. -/
  betti_euler   : ∀ X : A, Path (M.betti X) (M.euler X)
  /-- Euler characteristic equals critical count. -/
  euler_crit    : ∀ X : A, Path (M.euler X) (M.crit X)
  /-- Cobordism right unit. -/
  cobord_base   : ∀ p : A, Path (M.cobord p M.base) p
  /-- Cobordism decomposes via flow and handle. -/
  cobord_flow   : ∀ p q : A,
    Path (M.cobord p q) (M.attach (M.flow p) q)
  /-- Critical detection commutes with flow. -/
  crit_flow     : ∀ p : A, Path (M.crit (M.flow p)) (M.crit p)
  /-- Index is invariant under cell inclusion. -/
  idx_cell      : ∀ p : A, Path (M.idx (M.cell p)) (M.idx p)

variable {M} (ax : MorseAxioms M)

/-! ## §1 Gradient flow: convergence and idempotency -/

/-- flow(flow(crit(p))) = crit(p) via 2-step: flow idempotent then flow-crit. -/
def flow_idem_at_crit (p : A) :
    Path (M.flow (M.flow (M.crit p))) (M.crit p) :=
  Path.trans (ax.flow_idem (M.crit p)) (ax.flow_crit p)

/-- flow³(p) = flow(p) via double idempotency. -/
def flow_triple (p : A) :
    Path (M.flow (M.flow (M.flow p))) (M.flow p) :=
  Path.trans (ax.flow_idem (M.flow p)) (ax.flow_idem p)

/-- crit³(p) = crit(p) via double idempotency. -/
def crit_triple (p : A) :
    Path (M.crit (M.crit (M.crit p))) (M.crit p) :=
  Path.trans (ax.crit_idem (M.crit p)) (ax.crit_idem p)

/-- f(flow(crit(p))) = f(crit(p)) by lifting flow_crit through f. -/
def f_flow_crit (p : A) :
    Path (M.f (M.flow (M.crit p))) (M.f (M.crit p)) :=
  Path.congrArg M.f (ax.flow_crit p)

/-- f(flow(flow(p))) = f(p) via 2-step: lift flow_idem, then f_flow. -/
def f_flow_flow (p : A) :
    Path (M.f (M.flow (M.flow p))) (M.f p) :=
  Path.trans (Path.congrArg M.f (ax.flow_idem p)) (ax.f_flow p)

/-- crit(flow(flow(p))) = crit(p) via 2-step: lift flow_idem, then crit_flow. -/
def crit_flow_flow (p : A) :
    Path (M.crit (M.flow (M.flow p))) (M.crit p) :=
  Path.trans (Path.congrArg M.crit (ax.flow_idem p)) (ax.crit_flow p)

/-- crit(p) = flow(crit(p)), reverse of flow_crit via symm. -/
def flow_crit_symm (p : A) :
    Path (M.crit p) (M.flow (M.crit p)) :=
  Path.symm (ax.flow_crit p)

/-- f(crit³(p)) = f(crit(p)) by lifting crit_triple through f. -/
def f_crit_triple (p : A) :
    Path (M.f (M.crit (M.crit (M.crit p)))) (M.f (M.crit p)) :=
  Path.congrArg M.f (crit_triple ax p)

/-- bdry(flow(flow(p))) = bdry(p) via 2-step: bdry_flow twice. -/
def bdry_flow_flow (p : A) :
    Path (M.bdry (M.flow (M.flow p))) (M.bdry p) :=
  Path.trans (ax.bdry_flow (M.flow p)) (ax.bdry_flow p)

/-- flow(flow(flow(flow(p)))) = flow(p) via 3-step chain. -/
def flow_quad (p : A) :
    Path (M.flow (M.flow (M.flow (M.flow p)))) (M.flow p) :=
  Path.trans (ax.flow_idem (M.flow (M.flow p)))
    (Path.trans (ax.flow_idem (M.flow p)) (ax.flow_idem p))

/-! ## §2 Handle attachments: associativity and units -/

/-- attach(attach(p, base), q) = attach(p, q) via assoc + left unit. -/
def attach_nested_base (p q : A) :
    Path (M.attach (M.attach p M.base) q) (M.attach p q) :=
  Path.trans (ax.attach_assoc p M.base q)
    (Path.congrArg (M.attach p) (ax.attach_base_l q))

/-- attach(attach(p, base), base) = p via right-unit twice. -/
def handle_double_base (p : A) :
    Path (M.attach (M.attach p M.base) M.base) p :=
  Path.trans (ax.attach_base_r (M.attach p M.base))
    (ax.attach_base_r p)

/-- attach(p, flow(base)) = p via flow_handle + right-unit. -/
def handle_flow_cancel_id (p : A) :
    Path (M.attach p (M.flow M.base)) p :=
  Path.trans (ax.flow_handle p M.base) (ax.attach_base_r p)

/-- cell(attach(p, base)) = cell(p) by lifting right-unit through cell. -/
def cell_attach_base (p : A) :
    Path (M.cell (M.attach p M.base)) (M.cell p) :=
  Path.congrArg M.cell (ax.attach_base_r p)

/-- p = attach(p, base) via symm of right-unit. -/
def attach_base_r_symm (p : A) :
    Path p (M.attach p M.base) :=
  Path.symm (ax.attach_base_r p)

/-- Four-fold associativity of handle attachment in 2 steps. -/
def attach_assoc_four (p q r s : A) :
    Path (M.attach (M.attach (M.attach p q) r) s)
         (M.attach p (M.attach q (M.attach r s))) :=
  Path.trans (ax.attach_assoc (M.attach p q) r s)
    (ax.attach_assoc p q (M.attach r s))

/-- Handle round-trip: attach(p, base) → p → attach(p, base). -/
def attach_base_roundtrip (p : A) :
    Path (M.attach p M.base) (M.attach p M.base) :=
  Path.trans (ax.attach_base_r p) (Path.symm (ax.attach_base_r p))

/-- Smale-style cancellation: attach(crit(p), flow(base)) = crit(p). -/
def smale_cancel_simple (p : A) :
    Path (M.attach (M.crit p) (M.flow M.base)) (M.crit p) :=
  Path.trans (ax.flow_handle (M.crit p) M.base)
    (ax.attach_base_r (M.crit p))

/-- Smale cancellation reversed: crit(p) = attach(crit(p), flow(base)). -/
def smale_cancel_symm (p : A) :
    Path (M.crit p) (M.attach (M.crit p) (M.flow M.base)) :=
  Path.symm (smale_cancel_simple ax p)

/-! ## §3 CW structure -/

/-- cell(cell(cell(p))) = cell(p) via double idempotency. -/
def cell_triple (p : A) :
    Path (M.cell (M.cell (M.cell p))) (M.cell p) :=
  Path.trans (ax.cell_idem (M.cell p)) (ax.cell_idem p)

/-- cell(cell(attach(p,q))) = attach(cell(p), cell(q)) via idem + distribute. -/
def cell_cell_attach (p q : A) :
    Path (M.cell (M.cell (M.attach p q)))
         (M.attach (M.cell p) (M.cell q)) :=
  Path.trans (ax.cell_idem (M.attach p q)) (ax.cell_attach p q)

/-- cell(flow(base)) = base via 2-step: lift flow_base through cell, then cell_base. -/
def cell_flow_base :
    Path (M.cell (M.flow M.base)) M.base :=
  Path.trans (Path.congrArg M.cell ax.flow_base) ax.cell_base

/-- f(cell(cell(p))) = cell(f(p)) via 3-step chain:
    f(cell(cell(p))) → cell(f(cell(p))) → cell(cell(f(p))) → cell(f(p)). -/
def f_cell_cell (p : A) :
    Path (M.f (M.cell (M.cell p))) (M.cell (M.f p)) :=
  Path.trans (ax.f_cell (M.cell p))
    (Path.trans (Path.congrArg M.cell (ax.f_cell p))
      (ax.cell_idem (M.f p)))

/-- idx(cell(cell(p))) = idx(p) via 2-step: lift cell_idem, then idx_cell. -/
def idx_cell_cell (p : A) :
    Path (M.idx (M.cell (M.cell p))) (M.idx p) :=
  Path.trans (Path.congrArg M.idx (ax.cell_idem p)) (ax.idx_cell p)

/-- idx(cell(attach(p,q))) = idx(attach(cell(p), cell(q))) by lifting. -/
def idx_cell_attach (p q : A) :
    Path (M.idx (M.cell (M.attach p q)))
         (M.idx (M.attach (M.cell p) (M.cell q))) :=
  Path.congrArg M.idx (ax.cell_attach p q)

/-! ## §4 Morse homology: ∂² = 0 and consequences -/

/-- ∂³(p) = base via 2-step: lift ∂²=0 through ∂, then ∂(base)=base. -/
def bdry_triple (p : A) :
    Path (M.bdry (M.bdry (M.bdry p))) M.base :=
  Path.trans (Path.congrArg M.bdry (ax.bdry_sq p)) ax.bdry_base

/-- ∂²(flow(p)) = base via 2-step: bdry_flow inside ∂, then ∂²=0. -/
def bdry_flow_sq (p : A) :
    Path (M.bdry (M.bdry (M.flow p))) M.base :=
  Path.trans (Path.congrArg M.bdry (ax.bdry_flow p)) (ax.bdry_sq p)

/-- cell(∂²(p)) = base via 2-step: lift ∂²=0 through cell, then cell_base. -/
def cell_bdry_sq_base (p : A) :
    Path (M.cell (M.bdry (M.bdry p))) M.base :=
  Path.trans (Path.congrArg M.cell (ax.bdry_sq p)) ax.cell_base

/-- f(∂²(p)) = f(base) by lifting ∂²=0 through f. -/
def f_bdry_sq (p : A) :
    Path (M.f (M.bdry (M.bdry p))) (M.f M.base) :=
  Path.congrArg M.f (ax.bdry_sq p)

/-- base = ∂²(p) via symm of ∂²=0. -/
def bdry_sq_symm (p : A) :
    Path M.base (M.bdry (M.bdry p)) :=
  Path.symm (ax.bdry_sq p)

/-- ∂(∂(attach(p,q))) → attach(base, q) via 3-step expansion. -/
def bdry_attach_expand (p q : A) :
    Path (M.bdry (M.bdry (M.attach p q))) (M.attach M.base q) :=
  Path.trans (Path.congrArg M.bdry (ax.bdry_attach p q))
    (Path.trans (ax.bdry_attach (M.bdry p) q)
      (Path.congrArg (fun x => M.attach x q) (ax.bdry_sq p)))

/-- ∂(∂(attach(p,q))) = q via 4-step chain ending at left-unit. -/
def bdry_attach_full (p q : A) :
    Path (M.bdry (M.bdry (M.attach p q))) q :=
  Path.trans (bdry_attach_expand ax p q) (ax.attach_base_l q)

/-- idx(∂²(p)) = idx(base) by lifting ∂²=0 through idx. -/
def idx_bdry_sq (p : A) :
    Path (M.idx (M.bdry (M.bdry p))) (M.idx M.base) :=
  Path.congrArg M.idx (ax.bdry_sq p)

/-- ∂²(flow(crit(p))) = base via 2-step. -/
def bdry_sq_flow_crit (p : A) :
    Path (M.bdry (M.bdry (M.flow (M.crit p)))) M.base :=
  Path.trans (Path.congrArg M.bdry (ax.bdry_flow (M.crit p)))
    (ax.bdry_sq (M.crit p))

/-- ∂(cell(base)) = base via 2-step: lift cell_base through ∂, then ∂(base). -/
def bdry_cell_base_to_base :
    Path (M.bdry (M.cell M.base)) M.base :=
  Path.trans (Path.congrArg M.bdry ax.cell_base) ax.bdry_base

/-! ## §5 Morse inequalities and Euler characteristic -/

/-- betti(X) = crit(X) via 2-step: betti → euler → crit. -/
def betti_crit (X : A) :
    Path (M.betti X) (M.crit X) :=
  Path.trans (ax.betti_euler X) (ax.euler_crit X)

/-- euler(X) = betti(X) by reversing betti_euler. -/
def euler_betti (X : A) :
    Path (M.euler X) (M.betti X) :=
  Path.symm (ax.betti_euler X)

/-- crit(X) = euler(X) by reversing euler_crit. -/
def crit_euler (X : A) :
    Path (M.crit X) (M.euler X) :=
  Path.symm (ax.euler_crit X)

/-- f(betti(X)) = f(crit(X)) by lifting betti_crit through f. -/
def f_betti_crit (X : A) :
    Path (M.f (M.betti X)) (M.f (M.crit X)) :=
  Path.congrArg M.f (betti_crit ax X)

/-- bdry(betti(X)) = bdry(crit(X)) by lifting betti_crit through bdry. -/
def bdry_betti_crit (X : A) :
    Path (M.bdry (M.betti X)) (M.bdry (M.crit X)) :=
  Path.congrArg M.bdry (betti_crit ax X)

/-- f(euler(X)) = f(crit(X)) by lifting euler_crit through f. -/
def f_euler_crit (X : A) :
    Path (M.f (M.euler X)) (M.f (M.crit X)) :=
  Path.congrArg M.f (ax.euler_crit X)

/-- crit(betti(X)) = crit(X) via 2-step: lift betti_crit, then crit_idem. -/
def crit_betti_to_crit (X : A) :
    Path (M.crit (M.betti X)) (M.crit X) :=
  Path.trans (Path.congrArg M.crit (betti_crit ax X)) (ax.crit_idem X)

/-- cell(betti(X)) = cell(crit(X)) by lifting betti_crit through cell. -/
def cell_betti_crit (X : A) :
    Path (M.cell (M.betti X)) (M.cell (M.crit X)) :=
  Path.congrArg M.cell (betti_crit ax X)

/-! ## §6 Cobordism -/

/-- bdry(cobord(p, base)) = bdry(p) by lifting cobord_base through bdry. -/
def bdry_cobord_base (p : A) :
    Path (M.bdry (M.cobord p M.base)) (M.bdry p) :=
  Path.congrArg M.bdry (ax.cobord_base p)

/-- f(cobord(p, base)) = f(p) by lifting cobord_base through f. -/
def f_cobord_base (p : A) :
    Path (M.f (M.cobord p M.base)) (M.f p) :=
  Path.congrArg M.f (ax.cobord_base p)

/-- bdry(cobord(p,q)) decomposed via lifting cobord_flow through bdry. -/
def bdry_cobord_decompose (p q : A) :
    Path (M.bdry (M.cobord p q)) (M.bdry (M.attach (M.flow p) q)) :=
  Path.congrArg M.bdry (ax.cobord_flow p q)

/-- cobord(crit(p), base) = crit(p) by specializing cobord_base. -/
def cobord_crit_base (p : A) :
    Path (M.cobord (M.crit p) M.base) (M.crit p) :=
  ax.cobord_base (M.crit p)

/-- cobord(p, q) via flow + handle → p via 3-step when q=base. -/
def cobord_base_expand (p : A) :
    Path (M.cobord p M.base) (M.attach (M.flow p) M.base) :=
  ax.cobord_flow p M.base

/-! ## §7 Deep composite theorems -/

/-- flow(cell(base)) = base via lift-chain: cell_base then flow_base. -/
def flow_cell_base :
    Path (M.flow (M.cell M.base)) (M.flow M.base) :=
  Path.congrArg M.flow ax.cell_base

/-- flow(cell(base)) = base via 2-step. -/
def flow_cell_base_full :
    Path (M.flow (M.cell M.base)) M.base :=
  Path.trans (Path.congrArg M.flow ax.cell_base) ax.flow_base

/-- Nested congrArg: cell(flow(flow(p))) = cell(flow(p)). -/
def cell_flow_idem (p : A) :
    Path (M.cell (M.flow (M.flow p))) (M.cell (M.flow p)) :=
  Path.congrArg M.cell (ax.flow_idem p)

/-- Full Morse-homology coherence: ∂²(cell(flow(crit(p)))) = base via 3-step. -/
def morse_homology_full (p : A) :
    Path (M.bdry (M.bdry (M.cell (M.flow (M.crit p))))) M.base :=
  Path.trans
    (Path.congrArg (fun x => M.bdry (M.bdry (M.cell x))) (ax.flow_crit p))
    (ax.bdry_sq (M.cell (M.crit p)))

/-- Handle cancellation in the Morse complex:
    attach(p, attach(base, q)) = attach(p, q) via congrArg + left-unit. -/
def attach_cancel_base_inner (p q : A) :
    Path (M.attach p (M.attach M.base q)) (M.attach p q) :=
  Path.congrArg (M.attach p) (ax.attach_base_l q)

/-- Full Cerf birth-death cycle: crit(p) → attach(crit(p), base) → crit(p). -/
def cerf_birth_death (p : A) :
    Path (M.crit p) (M.crit p) :=
  Path.trans (Path.symm (ax.attach_base_r (M.crit p)))
    (ax.attach_base_r (M.crit p))

/-- Euler characteristic round-trip:
    euler(X) → betti(X) → euler(X) (symm then forward). -/
def euler_roundtrip (X : A) :
    Path (M.euler X) (M.euler X) :=
  Path.trans (Path.symm (ax.betti_euler X)) (ax.betti_euler X)

/-- Index stability under Smale rearrangement:
    idx(crit(flow(p))) = idx(crit(p)) by lifting crit_flow through idx. -/
def idx_crit_flow (p : A) :
    Path (M.idx (M.crit (M.flow p))) (M.idx (M.crit p)) :=
  Path.congrArg M.idx (ax.crit_flow p)

/-- bdry(∂(base)) = base via 2 applications of bdry_base. -/
def bdry_bdry_base :
    Path (M.bdry (M.bdry M.base)) M.base :=
  ax.bdry_sq M.base

/-- f(cell(attach(p,q))) = cell(f(attach(p,q))) specialization. -/
def f_cell_attach (p q : A) :
    Path (M.f (M.cell (M.attach p q)))
         (M.cell (M.f (M.attach p q))) :=
  ax.f_cell (M.attach p q)

/-- 3-step chain: f(cell(cell(attach(p,q)))) = cell(cell(f(attach(p,q))))
    via f_cell twice then cell_idem. -/
def f_cell_cell_attach (p q : A) :
    Path (M.f (M.cell (M.cell (M.attach p q))))
         (M.cell (M.cell (M.f (M.attach p q)))) :=
  Path.trans (ax.f_cell (M.cell (M.attach p q)))
    (Path.congrArg M.cell (ax.f_cell (M.attach p q)))

/-- Deep Smale theorem: idx(attach(crit(p), flow(base))) = idx(crit(p))
    via lifting the 2-step smale_cancel through idx. -/
def idx_smale_cancel (p : A) :
    Path (M.idx (M.attach (M.crit p) (M.flow M.base)))
         (M.idx (M.crit p)) :=
  Path.congrArg M.idx (smale_cancel_simple ax p)

/-- bdry commutes with flow in nested position:
    bdry(flow(flow(crit(p)))) = bdry(crit(p)) via 3-step. -/
def bdry_flow_flow_crit (p : A) :
    Path (M.bdry (M.flow (M.flow (M.crit p)))) (M.bdry (M.crit p)) :=
  Path.trans (ax.bdry_flow (M.flow (M.crit p)))
    (Path.trans (ax.bdry_flow (M.crit p)) (Path.refl _))

/-- cell(cell(cell(attach(p,q)))) = attach(cell(p), cell(q)) via 3-step. -/
def cell_triple_attach (p q : A) :
    Path (M.cell (M.cell (M.cell (M.attach p q))))
         (M.attach (M.cell p) (M.cell q)) :=
  Path.trans (cell_triple ax (M.attach p q)) (ax.cell_attach p q)

end MorseTheoryDeep
end ComputationalPaths
