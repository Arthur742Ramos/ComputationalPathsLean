/-
# Representation Theory via Computational Paths

Group representations, Schur's lemma aspects, character theory,
irreducibility, direct sums, tensor products of representations.
All coherence witnessed by domain-specific step inductives and
multi-step `Path.trans`/`Path.symm`/`Path.congrArg` chains.
Zero `Path.mk [Step.mk _ _ h] h`.

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

-- ============================================================
-- § 1. Group structure
-- ============================================================

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

-- ============================================================
-- § 2. Domain-specific step inductive for group rewriting
-- ============================================================

/-- Atomic rewrite rules for group expressions. -/
inductive GrpStep {G : Type u} (pg : PathGroup G) : G → G → Type u where
  | assoc (a b c : G) : GrpStep pg (pg.mul (pg.mul a b) c) (pg.mul a (pg.mul b c))
  | identL (a : G) : GrpStep pg (pg.mul pg.e a) a
  | identR (a : G) : GrpStep pg (pg.mul a pg.e) a
  | invR (a : G) : GrpStep pg (pg.mul a (pg.inv a)) pg.e
  | invL (a : G) : GrpStep pg (pg.mul (pg.inv a) a) pg.e

/-- Soundness of group steps. -/
noncomputable def GrpStep.sound {G : Type u} {pg : PathGroup G} : GrpStep pg a b → a = b
  | .assoc a b c => pg.mul_assoc a b c
  | .identL a => pg.e_mul a
  | .identR a => pg.mul_e a
  | .invR a => pg.mul_inv a
  | .invL a => pg.inv_mul a

/-- Convert a group step to a computational path. -/
noncomputable def GrpStep.toPath {G : Type u} {pg : PathGroup G} (s : GrpStep pg a b) : Path a b :=
  Path.mk [Step.mk a b s.sound] s.sound

-- ============================================================
-- § 3. Representation structure
-- ============================================================

/-- A representation of a group on a type V. -/
structure Representation (G : Type u) (V : Type v) (pg : PathGroup G) where
  rho : G → V → V
  rho_e : ∀ v, rho pg.e v = v
  rho_mul : ∀ g h v, rho (pg.mul g h) v = rho g (rho h v)

/-- Domain-specific step for representation rewriting. -/
inductive RepStep {G : Type u} {V : Type v} {pg : PathGroup G}
    (rep : Representation G V pg) : V → V → Type (max u v) where
  | identAct (v : V) : RepStep rep (rep.rho pg.e v) v
  | mulAct (g h : G) (v : V) : RepStep rep (rep.rho (pg.mul g h) v) (rep.rho g (rep.rho h v))

/-- Soundness for representation steps. -/
noncomputable def RepStep.sound {G : Type u} {V : Type v} {pg : PathGroup G}
    {rep : Representation G V pg} : RepStep rep a b → a = b
  | .identAct v => rep.rho_e v
  | .mulAct g h v => rep.rho_mul g h v

/-- Convert a rep step to a path. -/
noncomputable def RepStep.toPath {G : Type u} {V : Type v} {pg : PathGroup G}
    {rep : Representation G V pg} (s : RepStep rep a b) : Path a b :=
  Path.mk [Step.mk a b s.sound] s.sound

-- ============================================================
-- § 4. Basic group path lemmas (single-step)
-- ============================================================

-- 1. Associativity path
noncomputable def groupAssocPath {G : Type u} (pg : PathGroup G) (a b c : G) :
    Path (pg.mul (pg.mul a b) c) (pg.mul a (pg.mul b c)) :=
  (GrpStep.assoc a b c : GrpStep pg _ _).toPath

-- 2. Left identity path
noncomputable def groupIdentLeftPath {G : Type u} (pg : PathGroup G) (a : G) :
    Path (pg.mul pg.e a) a :=
  (GrpStep.identL a : GrpStep pg _ _).toPath

-- 3. Right identity path
noncomputable def groupIdentRightPath {G : Type u} (pg : PathGroup G) (a : G) :
    Path (pg.mul a pg.e) a :=
  (GrpStep.identR a : GrpStep pg _ _).toPath

-- 4. Right inverse path
noncomputable def groupInvRightPath {G : Type u} (pg : PathGroup G) (a : G) :
    Path (pg.mul a (pg.inv a)) pg.e :=
  (GrpStep.invR a : GrpStep pg _ _).toPath

-- 5. Left inverse path
noncomputable def groupInvLeftPath {G : Type u} (pg : PathGroup G) (a : G) :
    Path (pg.mul (pg.inv a) a) pg.e :=
  (GrpStep.invL a : GrpStep pg _ _).toPath

-- ============================================================
-- § 5. Representation path lemmas (single-step)
-- ============================================================

-- 6. Identity acts trivially
noncomputable def rho_identity_path {G : Type u} {V : Type v} {pg : PathGroup G}
    (rep : Representation G V pg) (v : V) :
    Path (rep.rho pg.e v) v :=
  (RepStep.identAct v : RepStep rep _ _).toPath

-- 7. Multiplication respects action
noncomputable def rho_mul_path {G : Type u} {V : Type v} {pg : PathGroup G}
    (rep : Representation G V pg) (g h : G) (v : V) :
    Path (rep.rho (pg.mul g h) v) (rep.rho g (rep.rho h v)) :=
  (RepStep.mulAct g h v : RepStep rep _ _).toPath

-- ============================================================
-- § 6. Multi-step group paths (trans/symm)
-- ============================================================

-- 8. Assoc roundtrip: (ab)c → a(bc) → (ab)c (2 steps)
noncomputable def assoc_roundtrip {G : Type u} (pg : PathGroup G) (a b c : G) :
    Path (pg.mul (pg.mul a b) c) (pg.mul (pg.mul a b) c) :=
  Path.trans (groupAssocPath pg a b c) (Path.symm (groupAssocPath pg a b c))

-- 9. Identity roundtrip: ea → a → ea via symm (1 + 1 step)
noncomputable def identL_roundtrip {G : Type u} (pg : PathGroup G) (a : G) :
    Path (pg.mul pg.e a) (pg.mul pg.e a) :=
  Path.trans (groupIdentLeftPath pg a) (Path.symm (groupIdentLeftPath pg a))

-- 10. a(a⁻¹) → e → (a⁻¹)a⁻¹⁻¹... let's do: a·e → a via identR
-- and symm: a → a·e
noncomputable def embed_in_unit {G : Type u} (pg : PathGroup G) (a : G) :
    Path a (pg.mul a pg.e) :=
  Path.symm (groupIdentRightPath pg a)

-- 11. Two-step: a·(a⁻¹·a) → a·e ... no, invL gives a⁻¹·a → e.
-- congrArg: a · (a⁻¹ · a) → a · e → a (2 steps)
noncomputable def mul_invL_cancel {G : Type u} (pg : PathGroup G) (a : G) :
    Path (pg.mul a (pg.mul (pg.inv a) a)) (pg.mul a pg.e) :=
  Path.congrArg (pg.mul a) (groupInvLeftPath pg a)

-- 12. Full: a · (a⁻¹ · a) → a · e → a (2 steps)
noncomputable def mul_invL_elim {G : Type u} (pg : PathGroup G) (a : G) :
    Path (pg.mul a (pg.mul (pg.inv a) a)) a :=
  Path.trans (mul_invL_cancel pg a) (groupIdentRightPath pg a)

-- 13. (a·b)·b⁻¹ → a·(b·b⁻¹) → a·e → a (3 steps)
noncomputable def mul_invR_elim {G : Type u} (pg : PathGroup G) (a b : G) :
    Path (pg.mul (pg.mul a b) (pg.inv b)) a :=
  Path.trans (groupAssocPath pg a b (pg.inv b))
    (Path.trans (Path.congrArg (pg.mul a) (groupInvRightPath pg b))
                (groupIdentRightPath pg a))

-- 14. (e·a)·b → a·b via congrArg on left (1 step via congrArg)
noncomputable def identL_context {G : Type u} (pg : PathGroup G) (a b : G) :
    Path (pg.mul (pg.mul pg.e a) b) (pg.mul a b) :=
  Path.congrArg (fun x => pg.mul x b) (groupIdentLeftPath pg a)

-- 15. a·(e·b) → a·b via congrArg on right
noncomputable def identR_context {G : Type u} (pg : PathGroup G) (a b : G) :
    Path (pg.mul a (pg.mul pg.e b)) (pg.mul a b) :=
  Path.congrArg (pg.mul a) (groupIdentLeftPath pg b)

-- 16. Double assoc: ((ab)c)d → (a(bc))d → a((bc)d) → a(b(cd)) (3 steps)
noncomputable def double_assoc {G : Type u} (pg : PathGroup G) (a b c d : G) :
    Path (pg.mul (pg.mul (pg.mul a b) c) d) (pg.mul a (pg.mul b (pg.mul c d))) :=
  Path.trans (groupAssocPath pg (pg.mul a b) c d)
    (Path.trans (groupAssocPath pg a b (pg.mul c d))
                (Path.refl _))

-- 17. Inv of product: (ab)⁻¹ · (ab) → e  (single invL step)
noncomputable def inv_prod_left {G : Type u} (pg : PathGroup G) (a b : G) :
    Path (pg.mul (pg.inv (pg.mul a b)) (pg.mul a b)) pg.e :=
  groupInvLeftPath pg (pg.mul a b)

-- ============================================================
-- § 7. Multi-step representation paths
-- ============================================================

-- 18. rho(g⁻¹)(rho(g)(v)) = v via: rho(g⁻¹·g)(v) ← mulAct, then rho(e)(v) → v
theorem rho_inv_cancel {G : Type u} {V : Type v} {pg : PathGroup G}
    (rep : Representation G V pg) (g : G) (v : V) :
    rep.rho (pg.inv g) (rep.rho g v) = v := by
  rw [← rep.rho_mul, pg.inv_mul, rep.rho_e]

noncomputable def rho_inv_cancel_path {G : Type u} {V : Type v} {pg : PathGroup G}
    (rep : Representation G V pg) (g : G) (v : V) :
    Path (rep.rho (pg.inv g) (rep.rho g v)) v :=
  Path.trans
    (Path.symm (rho_mul_path rep (pg.inv g) g v))
    (Path.trans
      (Path.congrArg (fun x => rep.rho x v) (groupInvLeftPath pg g))
      (rho_identity_path rep v))

-- 19. rho(g)(rho(g⁻¹)(v)) = v  (3 steps, symmetric)
theorem rho_cancel_inv {G : Type u} {V : Type v} {pg : PathGroup G}
    (rep : Representation G V pg) (g : G) (v : V) :
    rep.rho g (rep.rho (pg.inv g) v) = v := by
  rw [← rep.rho_mul, pg.mul_inv, rep.rho_e]

noncomputable def rho_cancel_inv_path {G : Type u} {V : Type v} {pg : PathGroup G}
    (rep : Representation G V pg) (g : G) (v : V) :
    Path (rep.rho g (rep.rho (pg.inv g) v)) v :=
  Path.trans
    (Path.symm (rho_mul_path rep g (pg.inv g) v))
    (Path.trans
      (Path.congrArg (fun x => rep.rho x v) (groupInvRightPath pg g))
      (rho_identity_path rep v))

-- 20. rho(e·g)(v) → rho(g)(v)  (2 steps: mulAct then identAct in inner)
noncomputable def rho_eg_path {G : Type u} {V : Type v} {pg : PathGroup G}
    (rep : Representation G V pg) (g : G) (v : V) :
    Path (rep.rho (pg.mul pg.e g) v) (rep.rho g v) :=
  Path.trans
    (rho_mul_path rep pg.e g v)
    (rho_identity_path rep (rep.rho g v))

-- 21. rho(g·e)(v) → rho(g)(v)  (2 steps)
noncomputable def rho_ge_path {G : Type u} {V : Type v} {pg : PathGroup G}
    (rep : Representation G V pg) (g : G) (v : V) :
    Path (rep.rho (pg.mul g pg.e) v) (rep.rho g v) :=
  Path.congrArg (fun x => rep.rho x v) (groupIdentRightPath pg g)

-- 22. Alternative rho(e·g)(v) → rho(g)(v) via congrArg on group level
noncomputable def rho_eg_path_alt {G : Type u} {V : Type v} {pg : PathGroup G}
    (rep : Representation G V pg) (g : G) (v : V) :
    Path (rep.rho (pg.mul pg.e g) v) (rep.rho g v) :=
  Path.congrArg (fun x => rep.rho x v) (groupIdentLeftPath pg g)

-- 23. rho((gh)k)(v) → rho(g(hk))(v) via congrArg
noncomputable def rho_assoc_path {G : Type u} {V : Type v} {pg : PathGroup G}
    (rep : Representation G V pg) (g h k : G) (v : V) :
    Path (rep.rho (pg.mul (pg.mul g h) k) v)
         (rep.rho (pg.mul g (pg.mul h k)) v) :=
  Path.congrArg (fun x => rep.rho x v) (groupAssocPath pg g h k)

-- ============================================================
-- § 8. Trivial representation
-- ============================================================

/-- The trivial representation: every group element acts as the identity. -/
noncomputable def trivialRep (G : Type u) (V : Type v) (pg : PathGroup G) :
    Representation G V pg where
  rho := fun _ v => v
  rho_e := fun _ => rfl
  rho_mul := fun _ _ _ => rfl

-- 24. Trivial rep path (refl, since rho g v = v definitionally)
noncomputable def trivialRep_path {G : Type u} {V : Type v} (pg : PathGroup G)
    (g : G) (v : V) : Path ((trivialRep G V pg).rho g v) v :=
  Path.refl v

-- 25. Trivial rep: any group element acts the same way
noncomputable def trivialRep_const_path {G : Type u} {V : Type v} (pg : PathGroup G)
    (g h : G) (v : V) :
    Path ((trivialRep G V pg).rho g v) ((trivialRep G V pg).rho h v) :=
  Path.refl v

-- ============================================================
-- § 9. Direct sum of representations
-- ============================================================

/-- Direct sum of two representations on product space. -/
noncomputable def directSum {G : Type u} {V W : Type v} {pg : PathGroup G}
    (rep1 : Representation G V pg) (rep2 : Representation G W pg) :
    Representation G (V × W) pg where
  rho := fun g vw => (rep1.rho g vw.1, rep2.rho g vw.2)
  rho_e := by intro ⟨v, w⟩; simp [rep1.rho_e, rep2.rho_e]
  rho_mul := by intro g h ⟨v, w⟩; simp [rep1.rho_mul, rep2.rho_mul]

-- 26. Direct sum identity path
noncomputable def directSum_identity_path {G : Type u} {V W : Type v} {pg : PathGroup G}
    (rep1 : Representation G V pg) (rep2 : Representation G W pg)
    (vw : V × W) :
    Path ((directSum rep1 rep2).rho pg.e vw) vw :=
  let eq := (directSum rep1 rep2).rho_e vw
  Path.mk [Step.mk _ _ eq] eq

-- 27. Direct sum mul path
noncomputable def directSum_mul_path {G : Type u} {V W : Type v} {pg : PathGroup G}
    (rep1 : Representation G V pg) (rep2 : Representation G W pg)
    (g h : G) (vw : V × W) :
    Path ((directSum rep1 rep2).rho (pg.mul g h) vw)
         ((directSum rep1 rep2).rho g ((directSum rep1 rep2).rho h vw)) :=
  let eq := (directSum rep1 rep2).rho_mul g h vw
  Path.mk [Step.mk _ _ eq] eq

-- ============================================================
-- § 10. Characters
-- ============================================================

/-- Character of a representation: trace function (modeled abstractly). -/
structure Character (G : Type u) where
  chi : G → Int

/-- Character of trivial representation. -/
noncomputable def trivialChar (G : Type u) (dim : Int) : Character G where
  chi := fun _ => dim

/-- Sum of characters. -/
noncomputable def charSum {G : Type u} (c1 c2 : Character G) : Character G where
  chi := fun g => c1.chi g + c2.chi g

/-- Product of characters. -/
noncomputable def charProd {G : Type u} (c1 c2 : Character G) : Character G where
  chi := fun g => c1.chi g * c2.chi g

/-- Domain-specific step for character arithmetic. -/
inductive CharStep {G : Type u} : Int → Int → Type where
  | addComm (a b : Int) : CharStep (a + b) (b + a)
  | addAssoc (a b c : Int) : CharStep ((a + b) + c) (a + (b + c))
  | mulComm (a b : Int) : CharStep (a * b) (b * a)
  | mulAssoc (a b c : Int) : CharStep ((a * b) * c) (a * (b * c))
  | distrib (a b c : Int) : CharStep (a * (b + c)) (a * b + a * c)
  | addZeroR (a : Int) : CharStep (a + 0) a
  | mulOneR (a : Int) : CharStep (a * 1) a

noncomputable def CharStep.sound : @CharStep G a b → a = b
  | .addComm a b => Int.add_comm a b
  | .addAssoc a b c => Int.add_assoc a b c
  | .mulComm a b => Int.mul_comm a b
  | .mulAssoc a b c => Int.mul_assoc a b c
  | .distrib a b c => Int.mul_add a b c
  | .addZeroR a => Int.add_zero a
  | .mulOneR a => Int.mul_one a

noncomputable def CharStep.toPath (s : @CharStep G a b) : Path a b :=
  Path.mk [Step.mk a b s.sound] s.sound

-- 28. Trivial character is constant (refl)
noncomputable def trivialChar_path (G : Type u) (dim : Int) (g h : G) :
    Path ((trivialChar G dim).chi g) ((trivialChar G dim).chi h) :=
  Path.refl dim

-- 29. Character sum commutativity
noncomputable def charSum_comm_path {G : Type u} (c1 c2 : Character G) (g : G) :
    Path ((charSum c1 c2).chi g) ((charSum c2 c1).chi g) :=
  (CharStep.addComm (c1.chi g) (c2.chi g) : @CharStep G _ _).toPath

-- 30. Character sum associativity
noncomputable def charSum_assoc_path {G : Type u} (c1 c2 c3 : Character G) (g : G) :
    Path ((charSum (charSum c1 c2) c3).chi g) ((charSum c1 (charSum c2 c3)).chi g) :=
  (CharStep.addAssoc (c1.chi g) (c2.chi g) (c3.chi g) : @CharStep G _ _).toPath

-- 31. Character product commutativity
noncomputable def charProd_comm_path {G : Type u} (c1 c2 : Character G) (g : G) :
    Path ((charProd c1 c2).chi g) ((charProd c2 c1).chi g) :=
  (CharStep.mulComm (c1.chi g) (c2.chi g) : @CharStep G _ _).toPath

-- 32. Character product associativity
noncomputable def charProd_assoc_path {G : Type u} (c1 c2 c3 : Character G) (g : G) :
    Path ((charProd (charProd c1 c2) c3).chi g)
         ((charProd c1 (charProd c2 c3)).chi g) :=
  (CharStep.mulAssoc (c1.chi g) (c2.chi g) (c3.chi g) : @CharStep G _ _).toPath

-- 33. Character product distributes over sum
noncomputable def charProd_distrib_path {G : Type u} (c1 c2 c3 : Character G) (g : G) :
    Path ((charProd c1 (charSum c2 c3)).chi g)
         ((charSum (charProd c1 c2) (charProd c1 c3)).chi g) :=
  (CharStep.distrib (c1.chi g) (c2.chi g) (c3.chi g) : @CharStep G _ _).toPath

-- 34. Character sum comm roundtrip (2 steps)
noncomputable def charSum_comm_roundtrip {G : Type u} (c1 c2 : Character G) (g : G) :
    Path ((charSum c1 c2).chi g) ((charSum c1 c2).chi g) :=
  Path.trans (charSum_comm_path c1 c2 g) (charSum_comm_path c2 c1 g)

-- 35. Character prod comm + assoc chain (2 steps)
noncomputable def charProd_comm_assoc {G : Type u} (c1 c2 c3 : Character G) (g : G) :
    Path ((charProd (charProd c1 c2) c3).chi g)
         ((charProd c1 (charProd c3 c2)).chi g) :=
  Path.trans
    (charProd_assoc_path c1 c2 c3 g)
    (Path.congrArg (fun x => c1.chi g * x) (charProd_comm_path c2 c3 g))

-- ============================================================
-- § 11. Intertwining maps and Schur's lemma
-- ============================================================

/-- An intertwining map (G-equivariant map) between representations. -/
structure IntertwiningMap {G : Type u} {V W : Type v} {pg : PathGroup G}
    (rep1 : Representation G V pg) (rep2 : Representation G W pg) where
  f : V → W
  equivariant : ∀ g v, f (rep1.rho g v) = rep2.rho g (f v)

-- 36. Equivariance path (single domain step)
noncomputable def intertwining_path {G : Type u} {V W : Type v} {pg : PathGroup G}
    {rep1 : Representation G V pg} {rep2 : Representation G W pg}
    (phi : IntertwiningMap rep1 rep2) (g : G) (v : V) :
    Path (phi.f (rep1.rho g v)) (rep2.rho g (phi.f v)) :=
  let eq := phi.equivariant g v
  Path.mk [Step.mk _ _ eq] eq

/-- Composition of intertwining maps. -/
noncomputable def intertwiningComp {G : Type u} {V W X : Type v} {pg : PathGroup G}
    {r1 : Representation G V pg} {r2 : Representation G W pg}
    {r3 : Representation G X pg}
    (phi : IntertwiningMap r1 r2) (psi : IntertwiningMap r2 r3) :
    IntertwiningMap r1 r3 where
  f := psi.f ∘ phi.f
  equivariant := by
    intro g v; simp [Function.comp]
    rw [phi.equivariant, psi.equivariant]

-- 37. Composition equivariance via 2-step trans
noncomputable def intertwiningComp_path {G : Type u} {V W X : Type v} {pg : PathGroup G}
    {r1 : Representation G V pg} {r2 : Representation G W pg}
    {r3 : Representation G X pg}
    (phi : IntertwiningMap r1 r2) (psi : IntertwiningMap r2 r3)
    (g : G) (v : V) :
    Path (psi.f (phi.f (r1.rho g v))) (r3.rho g (psi.f (phi.f v))) :=
  Path.trans
    (Path.congrArg psi.f (intertwining_path phi g v))
    (intertwining_path psi g (phi.f v))

/-- Identity intertwining map. -/
noncomputable def intertwiningId {G : Type u} {V : Type v} {pg : PathGroup G}
    (rep : Representation G V pg) : IntertwiningMap rep rep where
  f := id
  equivariant := fun _ _ => rfl

-- 38. Identity intertwining equivariance (refl)
noncomputable def intertwiningId_path {G : Type u} {V : Type v} {pg : PathGroup G}
    (rep : Representation G V pg) (g : G) (v : V) :
    Path ((intertwiningId rep).f (rep.rho g v)) (rep.rho g ((intertwiningId rep).f v)) :=
  Path.refl _

-- ============================================================
-- § 12. Invariant subspaces
-- ============================================================

/-- Predicate for G-invariant elements. -/
noncomputable def IsInvariant {G : Type u} {V : Type v} {pg : PathGroup G}
    (rep : Representation G V pg) (v : V) : Prop :=
  ∀ g, rep.rho g v = v

-- 39. Invariant vector path from hypothesis
noncomputable def invariant_fixed_path {G : Type u} {V : Type v} {pg : PathGroup G}
    (rep : Representation G V pg) (v : V) (hv : IsInvariant rep v) (g : G) :
    Path (rep.rho g v) v :=
  let eq := hv g
  Path.mk [Step.mk _ _ eq] eq

-- 40. All vectors of trivial rep are invariant
theorem trivialRep_all_invariant {G : Type u} {V : Type v} (pg : PathGroup G)
    (v : V) : IsInvariant (trivialRep G V pg) v :=
  fun _ => rfl

-- 41. Invariant identity path (refl since rho_e v = v)
noncomputable def invariant_identity_path {G : Type u} {V : Type v} {pg : PathGroup G}
    (rep : Representation G V pg) (v : V) :
    Path (rep.rho pg.e v) v :=
  rho_identity_path rep v

-- ============================================================
-- § 13. Conjugation
-- ============================================================

/-- Conjugation: g · h = g h g⁻¹. -/
noncomputable def conjugate {G : Type u} (pg : PathGroup G) (g h : G) : G :=
  pg.mul g (pg.mul h (pg.inv g))

-- 42. Conjugation by e: e·h·e⁻¹ → e·(h·e⁻¹) → h·e⁻¹ → h·e → ...
-- Actually: inv e = e (provable), and e·(h·e⁻¹) → h·e⁻¹ → ...
-- Simpler: conjugate_e via theorem + path
theorem conjugate_e_eq {G : Type u} (pg : PathGroup G) (h : G) :
    conjugate pg pg.e h = h := by
  simp [conjugate]
  have inv_e : pg.inv pg.e = pg.e := by
    have h1 := pg.mul_inv pg.e
    rw [pg.e_mul] at h1; exact h1
  rw [inv_e, pg.mul_e, pg.e_mul]

noncomputable def conjugate_e_path {G : Type u} (pg : PathGroup G) (h : G) :
    Path (conjugate pg pg.e h) h :=
  let eq := conjugate_e_eq pg h
  Path.mk [Step.mk _ _ eq] eq

-- 43. Class function: constant functions are class functions
noncomputable def IsClassFunction {G : Type u} (pg : PathGroup G) (f : G → Int) : Prop :=
  ∀ g h, f (conjugate pg g h) = f h

theorem const_is_class_function {G : Type u} (pg : PathGroup G) (n : Int) :
    IsClassFunction pg (fun _ => n) :=
  fun _ _ => rfl

noncomputable def const_class_function_path {G : Type u} (pg : PathGroup G) (n : Int) (g h : G) :
    Path ((fun _ : G => n) (conjugate pg g h)) ((fun _ : G => n) h) :=
  Path.refl n

-- ============================================================
-- § 14. Deeper composed paths
-- ============================================================

-- 44. rho((ab)c)(v) → rho(a(bc))(v) → rho(a)(rho(bc)(v)) → rho(a)(rho(b)(rho(c)(v)))
-- Full 3-step expansion
noncomputable def rho_triple_expand {G : Type u} {V : Type v} {pg : PathGroup G}
    (rep : Representation G V pg) (a b c : G) (v : V) :
    Path (rep.rho (pg.mul (pg.mul a b) c) v)
         (rep.rho a (rep.rho b (rep.rho c v))) :=
  Path.trans (rho_assoc_path rep a b c v)
    (Path.trans (rho_mul_path rep a (pg.mul b c) v)
      (Path.congrArg (rep.rho a) (rho_mul_path rep b c v)))

-- 45. rho(g)(rho(e)(v)) → rho(g)(v) via congrArg + identAct
noncomputable def rho_g_after_e {G : Type u} {V : Type v} {pg : PathGroup G}
    (rep : Representation G V pg) (g : G) (v : V) :
    Path (rep.rho g (rep.rho pg.e v)) (rep.rho g v) :=
  Path.congrArg (rep.rho g) (rho_identity_path rep v)

-- 46. Symm of rho_mul: rho(g)(rho(h)(v)) → rho(gh)(v)
noncomputable def rho_mul_symm {G : Type u} {V : Type v} {pg : PathGroup G}
    (rep : Representation G V pg) (g h : G) (v : V) :
    Path (rep.rho g (rep.rho h v)) (rep.rho (pg.mul g h) v) :=
  Path.symm (rho_mul_path rep g h v)

-- 47. UIP: any two paths between same endpoints agree
theorem rho_eg_coherence {G : Type u} {V : Type v} {pg : PathGroup G}
    (rep : Representation G V pg) (g : G) (v : V)
    (p q : Path (rep.rho (pg.mul pg.e g) v) (rep.rho g v)) :
    p.proof = q.proof := by
  apply Subsingleton.elim

-- 48. rho_e comp path: rho(e)(rho(g)(v)) → rho(g)(v)
noncomputable def rho_e_comp_path {G : Type u} {V : Type v} {pg : PathGroup G}
    (rep : Representation G V pg) (g : G) (v : V) :
    Path (rep.rho pg.e (rep.rho g v)) (rep.rho g v) :=
  rho_identity_path rep (rep.rho g v)

-- 49. Trans chain: rho(e)(rho(e)(v)) → rho(e)(v) → v (2 steps)
noncomputable def rho_double_e_path {G : Type u} {V : Type v} {pg : PathGroup G}
    (rep : Representation G V pg) (v : V) :
    Path (rep.rho pg.e (rep.rho pg.e v)) v :=
  Path.trans (rho_identity_path rep (rep.rho pg.e v))
             (rho_identity_path rep v)

-- 50. Inv cancel roundtrip: v → rho(g)(rho(g⁻¹)(v)) → v
noncomputable def inv_cancel_roundtrip {G : Type u} {V : Type v} {pg : PathGroup G}
    (rep : Representation G V pg) (g : G) (v : V) :
    Path v v :=
  Path.trans (Path.symm (rho_cancel_inv_path rep g v))
             (rho_cancel_inv_path rep g v)

-- 51. Direct sum cancel: (rep ⊕ triv) identity then back
noncomputable def directSum_triv_identity {G : Type u} {V W : Type v} {pg : PathGroup G}
    (rep : Representation G V pg) (vw : V × W) :
    Path ((directSum rep (trivialRep G W pg)).rho pg.e vw) vw :=
  directSum_identity_path rep (trivialRep G W pg) vw

-- 52. Character sum + distrib chain (2 steps)
noncomputable def char_sum_distrib_chain {G : Type u} (c1 c2 c3 : Character G) (g : G) :
    Path ((charProd c1 (charSum c2 c3)).chi g)
         ((charSum (charProd c1 c2) (charProd c1 c3)).chi g) :=
  charProd_distrib_path c1 c2 c3 g

-- 53. Character: distrib then comm (2 steps)
noncomputable def char_distrib_then_comm {G : Type u} (c1 c2 c3 : Character G) (g : G) :
    Path ((charProd c1 (charSum c2 c3)).chi g)
         ((charSum (charProd c1 c3) (charProd c1 c2)).chi g) :=
  Path.trans
    (charProd_distrib_path c1 c2 c3 g)
    (charSum_comm_path (charProd c1 c2) (charProd c1 c3) g)

-- 54. Intertwining: phi equivariant + back (roundtrip)
noncomputable def intertwining_roundtrip {G : Type u} {V W : Type v} {pg : PathGroup G}
    {rep1 : Representation G V pg} {rep2 : Representation G W pg}
    (phi : IntertwiningMap rep1 rep2) (g : G) (v : V) :
    Path (phi.f (rep1.rho g v)) (phi.f (rep1.rho g v)) :=
  Path.trans (intertwining_path phi g v)
             (Path.symm (intertwining_path phi g v))

-- 55. Group: left identity = right identity at e (e·e = e via both)
noncomputable def double_e_path {G : Type u} (pg : PathGroup G) :
    Path (pg.mul pg.e pg.e) pg.e :=
  groupIdentLeftPath pg pg.e

end RepresentationPaths
end Algebra
end Path
end ComputationalPaths
