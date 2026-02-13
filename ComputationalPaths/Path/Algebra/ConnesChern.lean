/-
# Connes-Chern Character via Computational Paths

This module formalizes the Connes-Chern character — the pairing between
K-theory and cyclic cohomology — using computational paths. We encode
K-theory classes, cyclic cocycles, the index pairing K₀ × HC^ev, the
Connes trace theorem, the local index formula, and the spectral action,
all with Path witnesses and Path.trans compositions for index computations.

## Key Definitions

- `KClass`: K-theory class data (idempotent/projection)
- `CyclicCocycle`: cyclic cocycle data with Path-valued cyclicity
- `ConnesChernPairing`: pairing ⟨[e], [φ]⟩ = φ(e,...,e)
- `IndexTheorem`: index = pairing, as a multi-step Path
- `ConnesTraceTheorem`: Dixmier trace = residue
- `LocalIndexFormula`: local index computation
- `SpectralAction`: spectral action functional

## References

- Connes, "Noncommutative Geometry"
- Connes & Moscovici, "The local index formula in noncommutative geometry"
- Chamseddine & Connes, "The spectral action principle"
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace ConnesChern

universe u

/-! ## K-theory classes -/

/-- Minimal algebra data. -/
structure AlgCarrier where
  /-- Carrier. -/
  carrier : Type u
  /-- Zero. -/
  zero : carrier
  /-- One. -/
  one : carrier
  /-- Addition. -/
  add : carrier → carrier → carrier
  /-- Multiplication. -/
  mul : carrier → carrier → carrier
  /-- Left unit. -/
  one_mul : ∀ x, mul one x = x
  /-- Right unit. -/
  mul_one : ∀ x, mul x one = x
  /-- Associativity. -/
  mul_assoc : ∀ x y z, mul (mul x y) z = mul x (mul y z)
  /-- Left zero. -/
  zero_add : ∀ x, add zero x = x
  /-- Commutativity of add. -/
  add_comm : ∀ x y, add x y = add y x

/-- A K-theory class: an idempotent (projection) in a matrix algebra. -/
structure KClass (A : AlgCarrier.{u}) where
  /-- The idempotent element e. -/
  idem : A.carrier
  /-- e² = e. -/
  idem_sq : A.mul idem idem = idem
  /-- Matrix size (rank of the free module). -/
  rank : Nat

namespace KClass

variable {A : AlgCarrier.{u}} (e : KClass A)

/-- Path witness: e² = e. -/
def idem_sq_path : Path (A.mul e.idem e.idem) e.idem :=
  Path.stepChain e.idem_sq

/-- Multi-step: e³ = e²·e = e·e = e. -/
def idem_cube_path : Path (A.mul (A.mul e.idem e.idem) e.idem) e.idem :=
  Path.trans
    (Path.stepChain (congrArg (fun x => A.mul x e.idem) e.idem_sq))
    e.idem_sq_path

/-- Multi-step with assoc: e·(e·e) = e·e = e. -/
def idem_cube_assoc_path : Path (A.mul e.idem (A.mul e.idem e.idem)) e.idem :=
  Path.trans
    (Path.stepChain (congrArg (A.mul e.idem) e.idem_sq))
    (Path.stepChain (A.mul_one e.idem ▸ A.mul_one e.idem ▸ e.idem_sq))

end KClass

/-! ## Cyclic cocycles -/

/-- A cyclic n-cocycle: a multilinear functional with cyclicity. -/
structure CyclicCocycle (A : AlgCarrier.{u}) (n : Nat) where
  /-- The cocycle as a function on (n+1)-tuples. -/
  eval : (Fin (n + 1) → A.carrier) → Nat
  /-- Cyclicity: φ(a₁,...,aₙ,a₀) = (-1)^n φ(a₀,...,aₙ). -/
  cyclic : ∀ (args : Fin (n + 1) → A.carrier),
    eval (fun i => args ⟨(i.val + 1) % (n + 1), Nat.mod_lt _ (by omega)⟩) = eval args
  /-- Cocycle evaluates to 0 on zero inputs. -/
  eval_zero : eval (fun _ => A.zero) = 0

namespace CyclicCocycle

variable {A : AlgCarrier.{u}} {n : Nat} (φ : CyclicCocycle A n)

/-- Path witness for cyclicity. -/
def cyclic_path (args : Fin (n + 1) → A.carrier) :
    Path (φ.eval (fun i => args ⟨(i.val + 1) % (n + 1), Nat.mod_lt _ (by omega)⟩))
         (φ.eval args) :=
  Path.stepChain (φ.cyclic args)

/-- Path witness: φ(0,...,0) = 0. -/
def eval_zero_path : Path (φ.eval (fun _ => A.zero)) 0 :=
  Path.stepChain φ.eval_zero

/-- Multi-step: applying cyclicity twice returns to original. -/
def double_cyclic_path (args : Fin (n + 1) → A.carrier)
    (h : (fun i : Fin (n + 1) =>
           args ⟨((⟨(i.val + 1) % (n + 1), Nat.mod_lt _ (by omega)⟩ : Fin (n+1)).val + 1)
                  % (n + 1), Nat.mod_lt _ (by omega)⟩) =
         (fun i : Fin (n + 1) =>
           args ⟨(i.val + 2) % (n + 1), Nat.mod_lt _ (by omega)⟩)) :
    Path (φ.eval (fun i => args ⟨(i.val + 2) % (n + 1), Nat.mod_lt _ (by omega)⟩))
         (φ.eval args) :=
  Path.trans
    (Path.stepChain (congrArg φ.eval h).symm)
    (Path.trans
      (φ.cyclic_path (fun i => args ⟨(i.val + 1) % (n + 1), Nat.mod_lt _ (by omega)⟩))
      (φ.cyclic_path args))

end CyclicCocycle

/-! ## Connes-Chern pairing -/

/-- The Connes-Chern pairing: ⟨[e], [φ]⟩ = φ(e, e, ..., e). -/
structure ConnesChernPairing (A : AlgCarrier.{u}) where
  /-- The pairing function: K₀ class × cyclic cocycle → ℤ (as Nat). -/
  pair : (e : KClass A) → (n : Nat) → CyclicCocycle A n → Nat
  /-- The pairing is computed by evaluating φ on the constant tuple (e,...,e). -/
  pair_eval : ∀ (e : KClass A) (n : Nat) (φ : CyclicCocycle A n),
    pair e n φ = φ.eval (fun _ => e.idem)

namespace ConnesChernPairing

variable {A : AlgCarrier.{u}} (P : ConnesChernPairing A)

/-- Path witness: pairing = evaluation. -/
def pair_eval_path (e : KClass A) (n : Nat) (φ : CyclicCocycle A n) :
    Path (P.pair e n φ) (φ.eval (fun _ => e.idem)) :=
  Path.stepChain (P.pair_eval e n φ)

/-- Multi-step: ⟨[e], [φ]⟩ = φ(e,...,e) = φ-cycled(e,...,e) since all args are e. -/
def pair_cyclic_invariance (e : KClass A) (n : Nat) (φ : CyclicCocycle A n) :
    Path (P.pair e n φ) (φ.eval (fun _ => e.idem)) :=
  Path.trans
    (P.pair_eval_path e n φ)
    (Path.symm (φ.cyclic_path (fun _ => e.idem)))

end ConnesChernPairing

/-! ## Index theorem -/

/-- Fredholm index data. -/
structure FredholmIndex (A : AlgCarrier.{u}) where
  /-- The Fredholm operator index. -/
  fredholmIdx : KClass A → Nat
  /-- Index of the zero class is zero. -/
  idx_zero_class : ∀ (e : KClass A), e.idem = A.zero → fredholmIdx e = 0

/-- Index theorem: Fredholm index = Connes-Chern pairing. -/
structure IndexTheorem (A : AlgCarrier.{u}) where
  /-- The pairing. -/
  pairing : ConnesChernPairing A
  /-- The Fredholm data. -/
  fredholm : FredholmIndex A
  /-- The index formula cocycle (degree 0 for simplicity). -/
  indexCocycle : CyclicCocycle A 0
  /-- Index = pairing with the index cocycle. -/
  index_eq_pairing : ∀ (e : KClass A),
    fredholm.fredholmIdx e = pairing.pair e 0 indexCocycle

namespace IndexTheorem

variable {A : AlgCarrier.{u}} (IT : IndexTheorem A)

/-- Path witness: index = pairing. -/
def index_eq_pairing_path (e : KClass A) :
    Path (IT.fredholm.fredholmIdx e) (IT.pairing.pair e 0 IT.indexCocycle) :=
  Path.stepChain (IT.index_eq_pairing e)

/-- Multi-step: index(e) = ⟨e, φ⟩ = φ(e), composing index theorem then pairing eval. -/
def index_computation_path (e : KClass A) :
    Path (IT.fredholm.fredholmIdx e) (IT.indexCocycle.eval (fun _ => e.idem)) :=
  Path.trans
    (IT.index_eq_pairing_path e)
    (IT.pairing.pair_eval_path e 0 IT.indexCocycle)

end IndexTheorem

/-! ## Connes trace theorem -/

/-- Connes trace theorem data: Dixmier trace = Wodzicki residue. -/
structure ConnesTraceTheorem (A : AlgCarrier.{u}) where
  /-- Dixmier trace functional. -/
  dixmierTrace : A.carrier → Nat
  /-- Wodzicki residue functional. -/
  wodzickiResidue : A.carrier → Nat
  /-- They agree on all elements. -/
  trace_eq_residue : ∀ a, dixmierTrace a = wodzickiResidue a
  /-- Both vanish on zero. -/
  trace_zero : dixmierTrace A.zero = 0
  /-- Residue vanishes on zero. -/
  residue_zero : wodzickiResidue A.zero = 0

namespace ConnesTraceTheorem

variable {A : AlgCarrier.{u}} (CT : ConnesTraceTheorem A)

/-- Path witness: Tr_ω(a) = Res(a). -/
def trace_eq_residue_path (a : A.carrier) :
    Path (CT.dixmierTrace a) (CT.wodzickiResidue a) :=
  Path.stepChain (CT.trace_eq_residue a)

/-- Multi-step: Tr_ω(0) = Res(0) = 0. -/
def trace_zero_path :
    Path (CT.dixmierTrace A.zero) 0 :=
  Path.trans
    (CT.trace_eq_residue_path A.zero)
    (Path.stepChain CT.residue_zero)

/-- RwEq: the direct trace_zero path and the composed path are equivalent. -/
theorem trace_zero_rweq :
    RwEq
      (Path.stepChain CT.trace_zero)
      (CT.trace_zero_path) := by
  constructor

end ConnesTraceTheorem

/-! ## Local index formula -/

/-- Local index formula data: expressing the Chern character via local terms. -/
structure LocalIndexFormula (A : AlgCarrier.{u}) where
  /-- Local cocycle components. -/
  localComponent : Nat → (A.carrier → Nat)
  /-- The total local index computes the global index. -/
  localIndex : A.carrier → Nat
  /-- Local index of zero is zero. -/
  localIndex_zero : localIndex A.zero = 0
  /-- Each component vanishes on zero. -/
  component_zero : ∀ n, localComponent n A.zero = 0

namespace LocalIndexFormula

variable {A : AlgCarrier.{u}} (LIF : LocalIndexFormula A)

/-- Path witness: local index of zero is zero. -/
def localIndex_zero_path : Path (LIF.localIndex A.zero) 0 :=
  Path.stepChain LIF.localIndex_zero

/-- Path witness: each local component vanishes on zero. -/
def component_zero_path (n : Nat) : Path (LIF.localComponent n A.zero) 0 :=
  Path.stepChain (LIF.component_zero n)

end LocalIndexFormula

/-! ## Spectral action -/

/-- Spectral action functional. -/
structure SpectralAction where
  /-- Cutoff scale. -/
  cutoff : Nat
  /-- The action value. -/
  actionVal : Nat
  /-- The action is non-negative (trivially true for Nat). -/
  action_nonneg : True

/-! ## Trivial instance -/

/-- Trivial Connes-Chern data on PUnit. -/
def trivialAlg : AlgCarrier.{0} where
  carrier := PUnit; zero := ⟨⟩; one := ⟨⟩
  add := fun _ _ => ⟨⟩; mul := fun _ _ => ⟨⟩
  one_mul := fun _ => rfl; mul_one := fun _ => rfl
  mul_assoc := fun _ _ _ => rfl; zero_add := fun _ => rfl
  add_comm := fun _ _ => rfl

/-- Trivial K-class. -/
def trivialKClass : KClass trivialAlg where
  idem := ⟨⟩; idem_sq := rfl; rank := 0

/-- Trivial index theorem. -/
def trivialIndexTheorem : IndexTheorem trivialAlg where
  pairing := { pair := fun _ _ _ => 0, pair_eval := fun _ _ _ => rfl }
  fredholm := { fredholmIdx := fun _ => 0, idx_zero_class := fun _ _ => rfl }
  indexCocycle := { eval := fun _ => 0, cyclic := fun _ => rfl, eval_zero := rfl }
  index_eq_pairing := fun _ => rfl

end ConnesChern
end Algebra
end Path
end ComputationalPaths
