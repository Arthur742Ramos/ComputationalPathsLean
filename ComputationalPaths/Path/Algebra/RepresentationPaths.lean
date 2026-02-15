/-
# Representation Theory via Computational Paths

Group representations, Schur's lemma aspects, character theory,
irreducibility, direct sums, tensor products of representations.
All coherence witnessed by `Path`.

## References

- Serre, "Linear Representations of Finite Groups"
- Fulton & Harris, "Representation Theory"
-/

import ComputationalPaths

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace RepresentationPaths

universe u v

open ComputationalPaths.Path

/-! ## Group representations as path-witnessed structures -/

/-- A group with Path-witnessed laws. -/
structure PathGroup (G : Type u) where
  e : G
  mul : G → G → G
  inv : G → G
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  e_mul : ∀ a, mul e a = a
  mul_e : ∀ a, mul a e = a
  mul_inv : ∀ a, mul a (inv a) = e
  inv_mul : ∀ a, mul (inv a) a = e

/-- A representation of a group on a type V. -/
structure Representation (G : Type u) (V : Type v) (pg : PathGroup G) where
  rho : G → V → V
  rho_e : ∀ v, rho pg.e v = v
  rho_mul : ∀ g h v, rho (pg.mul g h) v = rho g (rho h v)

/-- Path: the identity element acts trivially. -/
def rho_identity_path {G : Type u} {V : Type v} {pg : PathGroup G}
    (rep : Representation G V pg) (v : V) :
    Path (rep.rho pg.e v) v :=
  Path.ofEq (rep.rho_e v)

/-- Path: representation respects multiplication. -/
def rho_mul_path {G : Type u} {V : Type v} {pg : PathGroup G}
    (rep : Representation G V pg) (g h : G) (v : V) :
    Path (rep.rho (pg.mul g h) v) (rep.rho g (rep.rho h v)) :=
  Path.ofEq (rep.rho_mul g h v)

/-- Path: group associativity. -/
def groupAssocPath {G : Type u} (pg : PathGroup G) (a b c : G) :
    Path (pg.mul (pg.mul a b) c) (pg.mul a (pg.mul b c)) :=
  Path.ofEq (pg.mul_assoc a b c)

/-- Path: left identity. -/
def groupIdentLeftPath {G : Type u} (pg : PathGroup G) (a : G) :
    Path (pg.mul pg.e a) a :=
  Path.ofEq (pg.e_mul a)

/-- Path: right identity. -/
def groupIdentRightPath {G : Type u} (pg : PathGroup G) (a : G) :
    Path (pg.mul a pg.e) a :=
  Path.ofEq (pg.mul_e a)

/-- Path: right inverse. -/
def groupInvRightPath {G : Type u} (pg : PathGroup G) (a : G) :
    Path (pg.mul a (pg.inv a)) pg.e :=
  Path.ofEq (pg.mul_inv a)

/-- Path: left inverse. -/
def groupInvLeftPath {G : Type u} (pg : PathGroup G) (a : G) :
    Path (pg.mul (pg.inv a) a) pg.e :=
  Path.ofEq (pg.inv_mul a)

/-- Acting by g then g⁻¹ returns to original. -/
theorem rho_inv_cancel {G : Type u} {V : Type v} {pg : PathGroup G}
    (rep : Representation G V pg) (g : G) (v : V) :
    rep.rho (pg.inv g) (rep.rho g v) = v := by
  rw [← rep.rho_mul, pg.inv_mul, rep.rho_e]

/-- Path: acting by g then g⁻¹ returns to original. -/
def rho_inv_cancel_path {G : Type u} {V : Type v} {pg : PathGroup G}
    (rep : Representation G V pg) (g : G) (v : V) :
    Path (rep.rho (pg.inv g) (rep.rho g v)) v :=
  Path.ofEq (rho_inv_cancel rep g v)

/-- Acting by g⁻¹ then g returns to original. -/
theorem rho_cancel_inv {G : Type u} {V : Type v} {pg : PathGroup G}
    (rep : Representation G V pg) (g : G) (v : V) :
    rep.rho g (rep.rho (pg.inv g) v) = v := by
  rw [← rep.rho_mul, pg.mul_inv, rep.rho_e]

/-- Path: acting by g⁻¹ then g returns to original. -/
def rho_cancel_inv_path {G : Type u} {V : Type v} {pg : PathGroup G}
    (rep : Representation G V pg) (g : G) (v : V) :
    Path (rep.rho g (rep.rho (pg.inv g) v)) v :=
  Path.ofEq (rho_cancel_inv rep g v)

/-- Trans path: inv cancel via two steps. -/
def rho_inv_cancel_trans {G : Type u} {V : Type v} {pg : PathGroup G}
    (rep : Representation G V pg) (g : G) (v : V) :
    Path (rep.rho (pg.inv g) (rep.rho g v)) v :=
  Path.trans
    (Path.ofEq (rep.rho_mul (pg.inv g) g v).symm)
    (Path.trans
      (Path.ofEq (_root_.congrArg (fun x => rep.rho x v) (pg.inv_mul g)))
      (Path.ofEq (rep.rho_e v)))

/-! ## Trivial representation -/

/-- The trivial representation: every group element acts as the identity. -/
def trivialRep (G : Type u) (V : Type v) (pg : PathGroup G) :
    Representation G V pg where
  rho := fun _ v => v
  rho_e := fun _ => rfl
  rho_mul := fun _ _ _ => rfl

/-- Trivial representation always returns original vector. -/
theorem trivialRep_rho_eq {G : Type u} {V : Type v} (pg : PathGroup G)
    (g : G) (v : V) : (trivialRep G V pg).rho g v = v := rfl

/-- Path for trivial rep. -/
def trivialRep_path {G : Type u} {V : Type v} (pg : PathGroup G)
    (g : G) (v : V) : Path ((trivialRep G V pg).rho g v) v :=
  Path.refl v

/-! ## Direct sum of representations -/

/-- Direct sum of two representations on product space. -/
def directSum {G : Type u} {V W : Type v} {pg : PathGroup G}
    (rep1 : Representation G V pg) (rep2 : Representation G W pg) :
    Representation G (V × W) pg where
  rho := fun g vw => (rep1.rho g vw.1, rep2.rho g vw.2)
  rho_e := by
    intro ⟨v, w⟩
    simp [rep1.rho_e, rep2.rho_e]
  rho_mul := by
    intro g h ⟨v, w⟩
    simp [rep1.rho_mul, rep2.rho_mul]

/-- Path: direct sum identity action. -/
def directSum_identity_path {G : Type u} {V W : Type v} {pg : PathGroup G}
    (rep1 : Representation G V pg) (rep2 : Representation G W pg)
    (vw : V × W) :
    Path ((directSum rep1 rep2).rho pg.e vw) vw :=
  Path.ofEq ((directSum rep1 rep2).rho_e vw)

/-- Path: direct sum respects multiplication. -/
def directSum_mul_path {G : Type u} {V W : Type v} {pg : PathGroup G}
    (rep1 : Representation G V pg) (rep2 : Representation G W pg)
    (g h : G) (vw : V × W) :
    Path ((directSum rep1 rep2).rho (pg.mul g h) vw)
         ((directSum rep1 rep2).rho g ((directSum rep1 rep2).rho h vw)) :=
  Path.ofEq ((directSum rep1 rep2).rho_mul g h vw)

/-- Direct sum with trivial rep on right. -/
theorem directSum_trivial_right_fst {G : Type u} {V W : Type v} {pg : PathGroup G}
    (rep : Representation G V pg) (g : G) (v : V) (w : W) :
    ((directSum rep (trivialRep G W pg)).rho g (v, w)).1 = rep.rho g v := rfl

/-! ## Tensor product of representations -/

/-- Tensor product representation on product space. -/
def tensorRep {G : Type u} {V W : Type v} {pg : PathGroup G}
    (rep1 : Representation G V pg) (rep2 : Representation G W pg) :
    Representation G (V × W) pg where
  rho := fun g vw => (rep1.rho g vw.1, rep2.rho g vw.2)
  rho_e := by
    intro ⟨v, w⟩
    simp [rep1.rho_e, rep2.rho_e]
  rho_mul := by
    intro g h ⟨v, w⟩
    simp [rep1.rho_mul, rep2.rho_mul]

/-- Path: tensor rep identity. -/
def tensorRep_identity_path {G : Type u} {V W : Type v} {pg : PathGroup G}
    (rep1 : Representation G V pg) (rep2 : Representation G W pg)
    (vw : V × W) :
    Path ((tensorRep rep1 rep2).rho pg.e vw) vw :=
  Path.ofEq ((tensorRep rep1 rep2).rho_e vw)

/-! ## Characters -/

/-- Character of a representation: the trace function (modeled abstractly). -/
structure Character (G : Type u) where
  chi : G → Int

/-- Character of trivial representation. -/
def trivialChar (G : Type u) (dim : Int) : Character G where
  chi := fun _ => dim

/-- Path: trivial character is constant. -/
theorem trivialChar_const (G : Type u) (dim : Int) (g h : G) :
    (trivialChar G dim).chi g = (trivialChar G dim).chi h := rfl

/-- Path for constant character. -/
def trivialChar_path (G : Type u) (dim : Int) (g h : G) :
    Path ((trivialChar G dim).chi g) ((trivialChar G dim).chi h) :=
  Path.refl dim

/-- Sum of characters. -/
def charSum {G : Type u} (c1 c2 : Character G) : Character G where
  chi := fun g => c1.chi g + c2.chi g

/-- Path: character sum is commutative. -/
theorem charSum_comm {G : Type u} (c1 c2 : Character G) (g : G) :
    (charSum c1 c2).chi g = (charSum c2 c1).chi g := by
  simp [charSum, Int.add_comm]

/-- Path for character sum commutativity. -/
def charSum_comm_path {G : Type u} (c1 c2 : Character G) (g : G) :
    Path ((charSum c1 c2).chi g) ((charSum c2 c1).chi g) :=
  Path.ofEq (charSum_comm c1 c2 g)

/-- Character sum is associative. -/
theorem charSum_assoc {G : Type u} (c1 c2 c3 : Character G) (g : G) :
    (charSum (charSum c1 c2) c3).chi g = (charSum c1 (charSum c2 c3)).chi g := by
  simp [charSum, Int.add_assoc]

/-- Path for character sum associativity. -/
def charSum_assoc_path {G : Type u} (c1 c2 c3 : Character G) (g : G) :
    Path ((charSum (charSum c1 c2) c3).chi g) ((charSum c1 (charSum c2 c3)).chi g) :=
  Path.ofEq (charSum_assoc c1 c2 c3 g)

/-- Product of characters (pointwise multiplication). -/
def charProd {G : Type u} (c1 c2 : Character G) : Character G where
  chi := fun g => c1.chi g * c2.chi g

/-- Character product is commutative. -/
theorem charProd_comm {G : Type u} (c1 c2 : Character G) (g : G) :
    (charProd c1 c2).chi g = (charProd c2 c1).chi g := by
  simp [charProd, Int.mul_comm]

/-- Path for character product commutativity. -/
def charProd_comm_path {G : Type u} (c1 c2 : Character G) (g : G) :
    Path ((charProd c1 c2).chi g) ((charProd c2 c1).chi g) :=
  Path.ofEq (charProd_comm c1 c2 g)

/-- Character product is associative. -/
theorem charProd_assoc {G : Type u} (c1 c2 c3 : Character G) (g : G) :
    (charProd (charProd c1 c2) c3).chi g = (charProd c1 (charProd c2 c3)).chi g := by
  simp [charProd, Int.mul_assoc]

/-- Path for character product associativity. -/
def charProd_assoc_path {G : Type u} (c1 c2 c3 : Character G) (g : G) :
    Path ((charProd (charProd c1 c2) c3).chi g) ((charProd c1 (charProd c2 c3)).chi g) :=
  Path.ofEq (charProd_assoc c1 c2 c3 g)

/-- Character product distributes over sum. -/
theorem charProd_distrib {G : Type u} (c1 c2 c3 : Character G) (g : G) :
    (charProd c1 (charSum c2 c3)).chi g =
    (charSum (charProd c1 c2) (charProd c1 c3)).chi g := by
  simp [charProd, charSum, Int.mul_add]

/-- Path: character product distributes over sum. -/
def charProd_distrib_path {G : Type u} (c1 c2 c3 : Character G) (g : G) :
    Path ((charProd c1 (charSum c2 c3)).chi g)
         ((charSum (charProd c1 c2) (charProd c1 c3)).chi g) :=
  Path.ofEq (charProd_distrib c1 c2 c3 g)

/-! ## Intertwining maps and Schur's lemma aspects -/

/-- An intertwining map (G-equivariant map) between representations. -/
structure IntertwiningMap {G : Type u} {V W : Type v} {pg : PathGroup G}
    (rep1 : Representation G V pg) (rep2 : Representation G W pg) where
  f : V → W
  equivariant : ∀ g v, f (rep1.rho g v) = rep2.rho g (f v)

/-- Path: equivariance of intertwining map. -/
def intertwining_path {G : Type u} {V W : Type v} {pg : PathGroup G}
    {rep1 : Representation G V pg} {rep2 : Representation G W pg}
    (phi : IntertwiningMap rep1 rep2) (g : G) (v : V) :
    Path (phi.f (rep1.rho g v)) (rep2.rho g (phi.f v)) :=
  Path.ofEq (phi.equivariant g v)

/-- Composition of intertwining maps. -/
def intertwiningComp {G : Type u} {V W X : Type v} {pg : PathGroup G}
    {r1 : Representation G V pg} {r2 : Representation G W pg}
    {r3 : Representation G X pg}
    (phi : IntertwiningMap r1 r2) (psi : IntertwiningMap r2 r3) :
    IntertwiningMap r1 r3 where
  f := psi.f ∘ phi.f
  equivariant := by
    intro g v
    simp [Function.comp]
    rw [phi.equivariant, psi.equivariant]

/-- Path: composition of intertwining maps is equivariant. -/
def intertwiningComp_path {G : Type u} {V W X : Type v} {pg : PathGroup G}
    {r1 : Representation G V pg} {r2 : Representation G W pg}
    {r3 : Representation G X pg}
    (phi : IntertwiningMap r1 r2) (psi : IntertwiningMap r2 r3)
    (g : G) (v : V) :
    Path ((intertwiningComp phi psi).f (r1.rho g v))
         (r3.rho g ((intertwiningComp phi psi).f v)) :=
  Path.ofEq ((intertwiningComp phi psi).equivariant g v)

/-- Identity intertwining map. -/
def intertwiningId {G : Type u} {V : Type v} {pg : PathGroup G}
    (rep : Representation G V pg) : IntertwiningMap rep rep where
  f := id
  equivariant := fun _ _ => rfl

/-- Identity intertwining is trivially equivariant. -/
theorem intertwiningId_eq {G : Type u} {V : Type v} {pg : PathGroup G}
    (rep : Representation G V pg) (g : G) (v : V) :
    (intertwiningId rep).f (rep.rho g v) = rep.rho g ((intertwiningId rep).f v) := rfl

/-! ## Invariant subspaces -/

/-- Predicate for G-invariant elements. -/
def IsInvariant {G : Type u} {V : Type v} {pg : PathGroup G}
    (rep : Representation G V pg) (v : V) : Prop :=
  ∀ g, rep.rho g v = v

/-- The identity element preserves invariance trivially. -/
theorem invariant_of_identity {G : Type u} {V : Type v} {pg : PathGroup G}
    (rep : Representation G V pg) (v : V) :
    rep.rho pg.e v = v :=
  rep.rho_e v

/-- Path: invariant vector is fixed by identity. -/
def invariant_identity_path {G : Type u} {V : Type v} {pg : PathGroup G}
    (rep : Representation G V pg) (v : V) :
    Path (rep.rho pg.e v) v :=
  Path.ofEq (rep.rho_e v)

/-- Invariant vectors of trivial rep: everything is invariant. -/
theorem trivialRep_all_invariant {G : Type u} {V : Type v} (pg : PathGroup G)
    (v : V) : IsInvariant (trivialRep G V pg) v :=
  fun _ => rfl

/-- If v is invariant, rho g v = v. -/
theorem invariant_action_eq {G : Type u} {V : Type v} {pg : PathGroup G}
    (rep : Representation G V pg) (v : V) (hv : IsInvariant rep v)
    (g : G) : rep.rho g v = v :=
  hv g

/-- Path: invariant element is fixed. -/
def invariant_fixed_path {G : Type u} {V : Type v} {pg : PathGroup G}
    (rep : Representation G V pg) (v : V) (hv : IsInvariant rep v) (g : G) :
    Path (rep.rho g v) v :=
  Path.ofEq (hv g)

/-! ## Conjugation representation -/

/-- Conjugation in a group: g · h = g h g⁻¹. -/
def conjugate {G : Type u} (pg : PathGroup G) (g h : G) : G :=
  pg.mul g (pg.mul h (pg.inv g))

/-- Conjugation by identity is trivial. -/
theorem conjugate_e {G : Type u} (pg : PathGroup G) (h : G) :
    conjugate pg pg.e h = h := by
  simp [conjugate]
  have inv_e : pg.inv pg.e = pg.e := by
    have h1 := pg.mul_inv pg.e
    rw [pg.e_mul] at h1
    exact h1
  rw [inv_e, pg.mul_e, pg.e_mul]

/-- Path: conjugation by identity. -/
def conjugate_e_path {G : Type u} (pg : PathGroup G) (h : G) :
    Path (conjugate pg pg.e h) h :=
  Path.ofEq (conjugate_e pg h)

/-- A class function is constant on conjugacy classes. -/
def IsClassFunction {G : Type u} (pg : PathGroup G) (f : G → Int) : Prop :=
  ∀ g h, f (conjugate pg g h) = f h

/-- Constant functions are class functions. -/
theorem const_is_class_function {G : Type u} (pg : PathGroup G) (n : Int) :
    IsClassFunction pg (fun _ => n) :=
  fun _ _ => rfl

/-- Path: constant function is a class function witness. -/
def const_class_function_path {G : Type u} (pg : PathGroup G) (n : Int) (g h : G) :
    Path ((fun _ : G => n) (conjugate pg g h)) ((fun _ : G => n) h) :=
  Path.refl n

/-! ## Composition paths via trans -/

/-- Trans path connecting representation of product to iterated application. -/
def rep_composition_path {G : Type u} {V : Type v} {pg : PathGroup G}
    (rep : Representation G V pg) (g h : G) (v : V) :
    Path (rep.rho (pg.mul g h) v) (rep.rho g (rep.rho h v)) :=
  Path.ofEq (rep.rho_mul g h v)

/-- Coherence: two ways to compute rho(gh)(v) agree via symm. -/
def rep_coherence_symm {G : Type u} {V : Type v} {pg : PathGroup G}
    (rep : Representation G V pg) (g h : G) (v : V) :
    Path (rep.rho g (rep.rho h v)) (rep.rho (pg.mul g h) v) :=
  Path.symm (Path.ofEq (rep.rho_mul g h v))

/-- Path: rho e composed with rho g gives rho g. -/
theorem rho_e_comp {G : Type u} {V : Type v} {pg : PathGroup G}
    (rep : Representation G V pg) (g : G) (v : V) :
    rep.rho pg.e (rep.rho g v) = rep.rho g v :=
  rep.rho_e (rep.rho g v)

/-- Path for rho_e composition. -/
def rho_e_comp_path {G : Type u} {V : Type v} {pg : PathGroup G}
    (rep : Representation G V pg) (g : G) (v : V) :
    Path (rep.rho pg.e (rep.rho g v)) (rep.rho g v) :=
  Path.ofEq (rho_e_comp rep g v)

/-- Trans chain: rho(eg) = rho(e)(rho(g)) = rho(g). -/
def rho_eg_path {G : Type u} {V : Type v} {pg : PathGroup G}
    (rep : Representation G V pg) (g : G) (v : V) :
    Path (rep.rho (pg.mul pg.e g) v) (rep.rho g v) :=
  Path.trans
    (Path.ofEq (rep.rho_mul pg.e g v))
    (Path.ofEq (rep.rho_e (rep.rho g v)))

/-- Alternative path: rho(eg) = rho(g) via group law. -/
def rho_eg_path_alt {G : Type u} {V : Type v} {pg : PathGroup G}
    (rep : Representation G V pg) (g : G) (v : V) :
    Path (rep.rho (pg.mul pg.e g) v) (rep.rho g v) :=
  Path.ofEq (_root_.congrArg (fun x => rep.rho x v) (pg.e_mul g))

/-- Coherence: any two paths between same endpoints are equal (UIP). -/
theorem rho_eg_coherence {G : Type u} {V : Type v} {pg : PathGroup G}
    (rep : Representation G V pg) (g : G) (v : V)
    (p q : Path (rep.rho (pg.mul pg.e g) v) (rep.rho g v)) :
    p.proof = q.proof := by
  apply Subsingleton.elim

end RepresentationPaths
end Algebra
end Path
end ComputationalPaths
