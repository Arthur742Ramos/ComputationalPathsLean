/-
  ComputationalPaths/Path/Algebra/OperadCoherenceDeep.lean

  Operads and Coherence via Computational Paths

  All composition/associativity coherence via Path.trans, symmetry via Path.symm,
  functoriality via Path.congrArg. 80 theorems/definitions.
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths.OperadCoherence

open Path

universe u v w

-- ============================================================
-- Section 1: Basic Operad Structure
-- ============================================================

/-- An operad: operations indexed by arity, composition, identity. -/
structure Operad (C : Type u) where
  Ops : Nat → C
  identity : C
  compose : C → C → C
  arity : C → Nat

/-- Operadic composition γ. -/
noncomputable def operadGamma {C : Type u} (O : Operad C) (f g : C) : C := O.compose f g

/-- Identity element of an operad. -/
noncomputable def operadId {C : Type u} (O : Operad C) : C := O.identity

-- ============================================================
-- Section 2: Operadic Composition — Unitality and Associativity
-- ============================================================

/-- Right unitality witness. -/
structure OperadRightUnit {C : Type u} (O : Operad C) where
  witness : (f : C) → Path (O.compose f O.identity) f

/-- Left unitality witness. -/
structure OperadLeftUnit {C : Type u} (O : Operad C) where
  witness : (f : C) → Path (O.compose O.identity f) f

/-- Associativity witness for operadic composition. -/
structure OperadAssoc {C : Type u} (O : Operad C) where
  witness : (f g h : C) → Path (O.compose (O.compose f g) h) (O.compose f (O.compose g h))

/-- Def 1: Composing left unit then right unit yields a composite path. -/
noncomputable def operad_unit_compose {C : Type u} (O : Operad C)
    (lu : OperadLeftUnit O) (ru : OperadRightUnit O) (f : C) :
    Path (O.compose (O.compose O.identity f) O.identity) f :=
  Path.trans (congrArg (fun x => O.compose x O.identity) (lu.witness f)) (ru.witness f)

/-- Def 2: Associativity path is invertible via symm. -/
noncomputable def operad_assoc_invertible {C : Type u} (O : Operad C)
    (oa : OperadAssoc O) (f g h : C) :
    Path (O.compose f (O.compose g h)) (O.compose (O.compose f g) h) :=
  Path.symm (oa.witness f g h)

/-- Theorem 3: Double inversion of associativity recovers original. -/
theorem operad_assoc_symm_symm {C : Type u} (O : Operad C)
    (oa : OperadAssoc O) (f g h : C) :
    symm (symm (oa.witness f g h)) = oa.witness f g h :=
  symm_symm (oa.witness f g h)

/-- Theorem 4: trans_refl_right for right unit. -/
theorem operad_runit_trans_refl {C : Type u} (O : Operad C)
    (ru : OperadRightUnit O) (f : C) :
    trans (ru.witness f) (refl f) = ru.witness f :=
  trans_refl_right (ru.witness f)

/-- Theorem 5: trans_refl_left for left unit. -/
theorem operad_lunit_trans_refl {C : Type u} (O : Operad C)
    (lu : OperadLeftUnit O) (f : C) :
    trans (refl (O.compose O.identity f)) (lu.witness f) = lu.witness f :=
  trans_refl_left (lu.witness f)

/-- Def 6: Associativity is transitive — two assoc witnesses chained. -/
noncomputable def operad_assoc_chain {C : Type u} (O : Operad C) (oa : OperadAssoc O)
    (f g h k : C) :
    Path (O.compose (O.compose (O.compose f g) h) k)
         (O.compose f (O.compose g (O.compose h k))) :=
  Path.trans (oa.witness (O.compose f g) h k) (oa.witness f g (O.compose h k))

/-- Theorem 7: Refl composed with assoc. -/
theorem operad_refl_trans_assoc {C : Type u} (O : Operad C)
    (oa : OperadAssoc O) (f g h : C) :
    trans (refl (O.compose (O.compose f g) h)) (oa.witness f g h) = oa.witness f g h :=
  trans_refl_left (oa.witness f g h)

-- ============================================================
-- Section 3: Symmetric Operad Structure
-- ============================================================

/-- A permutation on finite sets. -/
structure OperadPerm (n : Nat) where
  apply : Fin n → Fin n
  inv   : Fin n → Fin n

/-- Symmetric operad: operad with permutation action. -/
structure SymOperad (C : Type u) extends Operad C where
  permAction : {n : Nat} → OperadPerm n → C → C

/-- Equivariance data. -/
structure Equivariance {C : Type u} (O : SymOperad C) where
  witness : (n : Nat) → (s : OperadPerm n) → (f g : C) →
    Path (O.permAction s (O.compose f g)) (O.compose (O.permAction s f) g)

/-- Def 8: Equivariance path is reversible. -/
noncomputable def equivariance_symm {C : Type u} (O : SymOperad C) (E : Equivariance O)
    (n : Nat) (s : OperadPerm n) (f g : C) :
    Path (O.compose (O.permAction s f) g) (O.permAction s (O.compose f g)) :=
  Path.symm (E.witness n s f g)

/-- Theorem 9: Double symmetry of equivariance. -/
theorem equivariance_symm_symm {C : Type u} (O : SymOperad C) (E : Equivariance O)
    (n : Nat) (s : OperadPerm n) (f g : C) :
    symm (symm (E.witness n s f g)) = E.witness n s f g :=
  symm_symm (E.witness n s f g)

/-- Theorem 10: Equivariance trans with refl. -/
theorem equivariance_trans_refl {C : Type u} (O : SymOperad C) (E : Equivariance O)
    (n : Nat) (s : OperadPerm n) (f g : C) :
    trans (E.witness n s f g) (refl (O.compose (O.permAction s f) g)) = E.witness n s f g :=
  trans_refl_right (E.witness n s f g)

/-- Perm action identity data. -/
structure PermIdentity {C : Type u} (O : SymOperad C) where
  idPerm : {n : Nat} → OperadPerm n
  witness : (n : Nat) → (f : C) → Path (O.permAction (idPerm (n := n)) f) f

/-- Def 11: Perm identity path inversion. -/
noncomputable def perm_id_inv {C : Type u} (O : SymOperad C) (pid : PermIdentity O)
    (n : Nat) (f : C) :
    Path f (O.permAction (pid.idPerm (n := n)) f) :=
  Path.symm (pid.witness n f)

/-- Theorem 12: Perm identity double symm. -/
theorem perm_id_symm_symm {C : Type u} (O : SymOperad C) (pid : PermIdentity O)
    (n : Nat) (f : C) :
    symm (symm (pid.witness n f)) = pid.witness n f :=
  symm_symm (pid.witness n f)

-- ============================================================
-- Section 4: Algebras over an Operad
-- ============================================================

/-- An algebra over an operad. -/
structure OperadAlgebra {C : Type u} (O : Operad C) (A : Type v) where
  action : C → A → A
  unit_act : (a : A) → Path (action O.identity a) a
  comp_act : (f g : C) → (a : A) →
    Path (action (O.compose f g) a) (action f (action g a))

/-- Theorem 13: Algebra unit action double symm. -/
theorem algebra_unit_symm_symm {C : Type u} {O : Operad C} {A : Type v}
    (alg : OperadAlgebra O A) (a : A) :
    symm (symm (alg.unit_act a)) = alg.unit_act a :=
  symm_symm (alg.unit_act a)

/-- Theorem 14: Algebra comp_act double symm. -/
theorem algebra_comp_symm_symm {C : Type u} {O : Operad C} {A : Type v}
    (alg : OperadAlgebra O A) (f g : C) (a : A) :
    symm (symm (alg.comp_act f g a)) = alg.comp_act f g a :=
  symm_symm (alg.comp_act f g a)

/-- Def 15: Composing unit then comp_act paths. -/
noncomputable def algebra_unit_then_comp {C : Type u} {O : Operad C} {A : Type v}
    (alg : OperadAlgebra O A) (g : C) (a : A) :
    Path (alg.action (O.compose O.identity g) a) (alg.action g a) :=
  Path.trans (alg.comp_act O.identity g a)
    (congrArg (fun x => x) (alg.unit_act (alg.action g a)))

/-- Theorem 16: Algebra unit_act trans_refl. -/
theorem algebra_unit_trans_refl {C : Type u} {O : Operad C} {A : Type v}
    (alg : OperadAlgebra O A) (a : A) :
    trans (alg.unit_act a) (refl a) = alg.unit_act a :=
  trans_refl_right (alg.unit_act a)

/-- Def 17: Algebra action inverse. -/
noncomputable def algebra_unit_inv {C : Type u} {O : Operad C} {A : Type v}
    (alg : OperadAlgebra O A) (a : A) :
    Path a (alg.action O.identity a) :=
  Path.symm (alg.unit_act a)

/-- Theorem 18: Algebra comp trans refl left. -/
theorem algebra_comp_refl_trans {C : Type u} {O : Operad C} {A : Type v}
    (alg : OperadAlgebra O A) (f g : C) (a : A) :
    trans (refl (alg.action (O.compose f g) a)) (alg.comp_act f g a) =
    alg.comp_act f g a :=
  trans_refl_left (alg.comp_act f g a)

-- ============================================================
-- Section 5: Operad Morphisms
-- ============================================================

/-- A morphism between operads. -/
structure OperadMorphism {C : Type u} (src tgt : Operad C) where
  map : C → C
  pres_id : Path (map src.identity) tgt.identity
  pres_comp : (f g : C) → Path (map (src.compose f g)) (tgt.compose (map f) (map g))

/-- Def 19: Morphism identity preservation reversed. -/
noncomputable def morphism_pres_id_symm {C : Type u} {src tgt : Operad C}
    (m : OperadMorphism src tgt) :
    Path tgt.identity (m.map src.identity) :=
  Path.symm m.pres_id

/-- Def 20: Composition preservation reversed. -/
noncomputable def morphism_pres_comp_inv {C : Type u} {src tgt : Operad C}
    (m : OperadMorphism src tgt) (f g : C) :
    Path (tgt.compose (m.map f) (m.map g)) (m.map (src.compose f g)) :=
  Path.symm (m.pres_comp f g)

/-- Identity morphism on an operad. -/
noncomputable def operadMorphismId {C : Type u} (O : Operad C) : OperadMorphism O O where
  map := id
  pres_id := Path.refl O.identity
  pres_comp := fun f g => Path.refl (O.compose f g)

/-- Theorem 21: Identity morphism pres_id is refl. -/
theorem id_morphism_pres_id {C : Type u} (O : Operad C) :
    (operadMorphismId O).pres_id = Path.refl O.identity :=
  rfl

/-- Def 22: congrArg applied to morphism map. -/
noncomputable def morphism_congrArg {C : Type u} {src tgt : Operad C}
    (m : OperadMorphism src tgt)
    {a b : C} (p : Path a b) :
    Path (m.map a) (m.map b) :=
  Path.congrArg m.map p

/-- Theorem 23: Morphism map commutes with trans. -/
theorem morphism_congrArg_trans {C : Type u} {src tgt : Operad C}
    (m : OperadMorphism src tgt)
    {a b c : C} (p : Path a b) (q : Path b c) :
    congrArg m.map (trans p q) = trans (congrArg m.map p) (congrArg m.map q) :=
  congrArg_trans m.map p q

/-- Theorem 24: Morphism map commutes with symm. -/
theorem morphism_congrArg_symm {C : Type u} {src tgt : Operad C}
    (m : OperadMorphism src tgt)
    {a b : C} (p : Path a b) :
    congrArg m.map (symm p) = symm (congrArg m.map p) :=
  congrArg_symm m.map p

/-- Composition of operad morphisms. -/
noncomputable def operadMorphismComp {C : Type u} {O1 O2 O3 : Operad C}
    (m1 : OperadMorphism O1 O2) (m2 : OperadMorphism O2 O3) :
    OperadMorphism O1 O3 where
  map := m2.map ∘ m1.map
  pres_id := Path.trans (congrArg m2.map m1.pres_id) m2.pres_id
  pres_comp := fun f g =>
    Path.trans (congrArg m2.map (m1.pres_comp f g)) (m2.pres_comp (m1.map f) (m1.map g))

/-- Theorem 25: Composition preserves id coherently. -/
theorem morphism_comp_pres_id {C : Type u} {O1 O2 O3 : Operad C}
    (m1 : OperadMorphism O1 O2) (m2 : OperadMorphism O2 O3) :
    (operadMorphismComp m1 m2).pres_id =
    Path.trans (congrArg m2.map m1.pres_id) m2.pres_id :=
  rfl

/-- Theorem 26: Identity morphism pres_comp is refl. -/
theorem id_morphism_pres_comp {C : Type u} (O : Operad C) (f g : C) :
    (operadMorphismId O).pres_comp f g = Path.refl (O.compose f g) :=
  rfl

/-- Theorem 27: Morphism pres_id double symm. -/
theorem morphism_pres_id_symm_symm {C : Type u} {src tgt : Operad C}
    (m : OperadMorphism src tgt) :
    symm (symm m.pres_id) = m.pres_id :=
  symm_symm m.pres_id

/-- Theorem 28: Morphism pres_comp double symm. -/
theorem morphism_pres_comp_symm_symm {C : Type u} {src tgt : Operad C}
    (m : OperadMorphism src tgt) (f g : C) :
    symm (symm (m.pres_comp f g)) = m.pres_comp f g :=
  symm_symm (m.pres_comp f g)

-- ============================================================
-- Section 6: Free Operad on a Collection
-- ============================================================

/-- A collection assigns a type to each arity. -/
structure Collection (C : Type u) where
  ops : Nat → C
  arityOf : C → Nat

/-- Free operad terms. -/
inductive FreeOperadTerm (C : Type u) where
  | gen  : C → FreeOperadTerm C
  | unit : FreeOperadTerm C
  | comp : FreeOperadTerm C → FreeOperadTerm C → FreeOperadTerm C

/-- Def 29: Generator embedding preserves paths. -/
noncomputable def freeOperad_gen_path {C : Type u} {a b : C} (p : Path a b) :
    Path (FreeOperadTerm.gen a) (FreeOperadTerm.gen b) :=
  Path.congrArg FreeOperadTerm.gen p

/-- Def 30: Free operad comp functorial in first arg. -/
noncomputable def freeOperad_comp_left {C : Type u}
    {f1 f2 : FreeOperadTerm C} (g : FreeOperadTerm C)
    (p : Path f1 f2) :
    Path (FreeOperadTerm.comp f1 g) (FreeOperadTerm.comp f2 g) :=
  Path.congrArg (fun x => FreeOperadTerm.comp x g) p

/-- Def 31: Free operad comp functorial in second arg. -/
noncomputable def freeOperad_comp_right {C : Type u}
    (f : FreeOperadTerm C) {g1 g2 : FreeOperadTerm C}
    (p : Path g1 g2) :
    Path (FreeOperadTerm.comp f g1) (FreeOperadTerm.comp f g2) :=
  Path.congrArg (fun x => FreeOperadTerm.comp f x) p

/-- Theorem 32: Gen embedding commutes with trans. -/
theorem freeOperad_gen_trans {C : Type u} {a b c : C}
    (p : Path a b) (q : Path b c) :
    congrArg FreeOperadTerm.gen (trans p q) =
    trans (congrArg FreeOperadTerm.gen p) (congrArg FreeOperadTerm.gen q) :=
  congrArg_trans FreeOperadTerm.gen p q

/-- Theorem 33: Gen embedding commutes with symm. -/
theorem freeOperad_gen_symm {C : Type u} {a b : C} (p : Path a b) :
    congrArg FreeOperadTerm.gen (symm p) =
    symm (congrArg FreeOperadTerm.gen p) :=
  congrArg_symm FreeOperadTerm.gen p

/-- Theorem 34: Comp left functor commutes with trans. -/
theorem freeOperad_comp_left_trans {C : Type u}
    {f1 f2 f3 : FreeOperadTerm C} (g : FreeOperadTerm C)
    (p : Path f1 f2) (q : Path f2 f3) :
    congrArg (fun x => FreeOperadTerm.comp x g) (trans p q) =
    trans (congrArg (fun x => FreeOperadTerm.comp x g) p)
          (congrArg (fun x => FreeOperadTerm.comp x g) q) :=
  congrArg_trans (fun x => FreeOperadTerm.comp x g) p q

/-- Theorem 35: Comp right functor commutes with symm. -/
theorem freeOperad_comp_right_symm {C : Type u}
    (f : FreeOperadTerm C) {g1 g2 : FreeOperadTerm C}
    (p : Path g1 g2) :
    congrArg (fun x => FreeOperadTerm.comp f x) (symm p) =
    symm (congrArg (fun x => FreeOperadTerm.comp f x) p) :=
  congrArg_symm (fun x => FreeOperadTerm.comp f x) p

-- ============================================================
-- Section 7: A∞ Operad Structure
-- ============================================================

/-- A∞ operad: associahedra-indexed operations. -/
structure AInfOperad (C : Type u) where
  mu : Nat → C
  compose : C → C → C
  identity : C
  assocPath : (n m : Nat) → Path (compose (mu n) (mu m)) (mu (n + m - 1))

/-- Def 36: A∞ associativity path. -/
noncomputable def aInf_assoc {C : Type u} (O : AInfOperad C) (n m : Nat) :
    Path (O.compose (O.mu n) (O.mu m)) (O.mu (n + m - 1)) :=
  O.assocPath n m

/-- Def 37: A∞ associativity path reversal. -/
noncomputable def aInf_assoc_symm {C : Type u} (O : AInfOperad C) (n m : Nat) :
    Path (O.mu (n + m - 1)) (O.compose (O.mu n) (O.mu m)) :=
  Path.symm (O.assocPath n m)

/-- Theorem 38: A∞ double symmetry. -/
theorem aInf_assoc_symm_symm {C : Type u} (O : AInfOperad C) (n m : Nat) :
    symm (symm (O.assocPath n m)) = O.assocPath n m :=
  symm_symm (O.assocPath n m)

/-- Theorem 39: A∞ trans_refl_right. -/
theorem aInf_assoc_trans_refl {C : Type u} (O : AInfOperad C) (n m : Nat) :
    trans (O.assocPath n m) (refl (O.mu (n + m - 1))) = O.assocPath n m :=
  trans_refl_right (O.assocPath n m)

/-- Theorem 40: A∞ refl_trans. -/
theorem aInf_refl_trans_assoc {C : Type u} (O : AInfOperad C) (n m : Nat) :
    trans (refl (O.compose (O.mu n) (O.mu m))) (O.assocPath n m) = O.assocPath n m :=
  trans_refl_left (O.assocPath n m)

-- ============================================================
-- Section 8: E∞ Operad Structure
-- ============================================================

/-- E∞ operad: contractible operation spaces. -/
structure EInfOperad (C : Type u) where
  space : Nat → C
  compose : C → C → C
  identity : C
  permAct : C → C
  contractible : (n : Nat) → (x y : C) → Path x y

/-- Def 41: E∞ path between any two. -/
noncomputable def eInf_path {C : Type u} (O : EInfOperad C) (n : Nat) (x y : C) :
    Path x y :=
  O.contractible n x y

/-- Def 42: E∞ commutativity. -/
noncomputable def eInf_commute {C : Type u} (O : EInfOperad C) (n : Nat) (f g : C) :
    Path (O.compose f g) (O.compose g f) :=
  O.contractible n _ _

/-- Def 43: E∞ perm triviality. -/
noncomputable def eInf_perm_trivial {C : Type u} (O : EInfOperad C) (n : Nat) (f : C) :
    Path (O.permAct f) f :=
  O.contractible n _ _

/-- Def 44: E∞ unit absorption. -/
noncomputable def eInf_unit {C : Type u} (O : EInfOperad C) (n : Nat) (f : C) :
    Path (O.compose O.identity f) f :=
  O.contractible n _ _

/-- Def 45: E∞ associativity. -/
noncomputable def eInf_assoc {C : Type u} (O : EInfOperad C) (n : Nat) (f g h : C) :
    Path (O.compose (O.compose f g) h) (O.compose f (O.compose g h)) :=
  O.contractible n _ _

-- ============================================================
-- Section 9: May's Recognition Principle
-- ============================================================

/-- May's recognition principle. -/
structure MayRecognition (C : Type u) (A : Type v) where
  operad : Operad C
  space : A
  action : C → A → A
  deloop : A → A
  recognition : Path (deloop (action operad.identity space)) space

/-- Def 46: Recognition path reversed. -/
noncomputable def may_recognition_inv {C : Type u} {A : Type v} (M : MayRecognition C A) :
    Path M.space (M.deloop (M.action M.operad.identity M.space)) :=
  Path.symm M.recognition

/-- Theorem 47: Double symm of recognition. -/
theorem may_recognition_symm_symm {C : Type u} {A : Type v} (M : MayRecognition C A) :
    symm (symm M.recognition) = M.recognition :=
  symm_symm M.recognition

/-- Theorem 48: Recognition trans_refl. -/
theorem may_recognition_trans_refl {C : Type u} {A : Type v} (M : MayRecognition C A) :
    trans M.recognition (refl M.space) = M.recognition :=
  trans_refl_right M.recognition

/-- Theorem 49: Recognition refl_trans. -/
theorem may_recognition_refl_trans {C : Type u} {A : Type v} (M : MayRecognition C A) :
    trans (refl (M.deloop (M.action M.operad.identity M.space))) M.recognition = M.recognition :=
  trans_refl_left M.recognition

-- ============================================================
-- Section 10: Boardman-Vogt Tensor Product
-- ============================================================

/-- BV tensor product of operads. -/
structure BVTensor (C : Type u) where
  left : Operad C
  right : Operad C
  tensor_ops : Nat → C
  tensor_compose : C → C → C
  interchange : (f1 f2 g1 g2 : C) →
    Path (tensor_compose (left.compose f1 f2) (right.compose g1 g2))
         (tensor_compose (tensor_compose f1 g1) (tensor_compose f2 g2))

/-- Def 50: BV interchange reversed. -/
noncomputable def bv_interchange_symm {C : Type u} (BV : BVTensor C) (f1 f2 g1 g2 : C) :
    Path (BV.tensor_compose (BV.tensor_compose f1 g1) (BV.tensor_compose f2 g2))
         (BV.tensor_compose (BV.left.compose f1 f2) (BV.right.compose g1 g2)) :=
  Path.symm (BV.interchange f1 f2 g1 g2)

/-- Theorem 51: BV interchange double symm. -/
theorem bv_interchange_symm_symm {C : Type u} (BV : BVTensor C) (f1 f2 g1 g2 : C) :
    symm (symm (BV.interchange f1 f2 g1 g2)) = BV.interchange f1 f2 g1 g2 :=
  symm_symm (BV.interchange f1 f2 g1 g2)

/-- Def 52: BV interchange applied via congrArg. -/
noncomputable def bv_interchange_congrArg {C : Type u} (BV : BVTensor C) (f1 f2 g1 g2 : C)
    (h : C → C) :
    Path (h (BV.tensor_compose (BV.left.compose f1 f2) (BV.right.compose g1 g2)))
         (h (BV.tensor_compose (BV.tensor_compose f1 g1) (BV.tensor_compose f2 g2))) :=
  congrArg h (BV.interchange f1 f2 g1 g2)

/-- Theorem 53: BV interchange trans_refl_right. -/
theorem bv_interchange_trans_refl {C : Type u} (BV : BVTensor C) (f1 f2 g1 g2 : C) :
    trans (BV.interchange f1 f2 g1 g2)
      (refl (BV.tensor_compose (BV.tensor_compose f1 g1) (BV.tensor_compose f2 g2))) =
    BV.interchange f1 f2 g1 g2 :=
  trans_refl_right (BV.interchange f1 f2 g1 g2)

-- ============================================================
-- Section 11: Pentagon and Triangle Coherence
-- ============================================================

/-- Pentagon coherence data. -/
structure PentagonData (C : Type u) where
  compose : C → C → C
  assoc : (a b c : C) → Path (compose (compose a b) c) (compose a (compose b c))

/-- Def 54: Pentagon — one route around the associahedron. -/
noncomputable def pentagon_route_one {C : Type u} (P : PentagonData C) (a b c d : C) :
    Path (P.compose (P.compose (P.compose a b) c) d)
         (P.compose (P.compose a b) (P.compose c d)) :=
  P.assoc (P.compose a b) c d

/-- Def 55: Pentagon — second segment via congrArg. -/
noncomputable def pentagon_route_two {C : Type u} (P : PentagonData C) (a b c d : C) :
    Path (P.compose (P.compose a b) (P.compose c d))
         (P.compose a (P.compose b (P.compose c d))) :=
  P.assoc a b (P.compose c d)

/-- Def 56: Pentagon composite path. -/
noncomputable def pentagon_composite {C : Type u} (P : PentagonData C) (a b c d : C) :
    Path (P.compose (P.compose (P.compose a b) c) d)
         (P.compose a (P.compose b (P.compose c d))) :=
  Path.trans (pentagon_route_one P a b c d) (pentagon_route_two P a b c d)

/-- Triangle coherence data. -/
structure TriangleData (C : Type u) where
  compose : C → C → C
  identity : C
  assoc : (a b c : C) → Path (compose (compose a b) c) (compose a (compose b c))
  leftUnit : (a : C) → Path (compose identity a) a
  rightUnit : (a : C) → Path (compose a identity) a

/-- Def 57: Triangle — direct route. -/
noncomputable def triangle_direct {C : Type u} (T : TriangleData C) (a b : C) :
    Path (T.compose (T.compose a T.identity) b) (T.compose a b) :=
  congrArg (fun x => T.compose x b) (T.rightUnit a)

/-- Def 58: Triangle — indirect route. -/
noncomputable def triangle_indirect {C : Type u} (T : TriangleData C) (a b : C) :
    Path (T.compose (T.compose a T.identity) b) (T.compose a (T.compose T.identity b)) :=
  T.assoc a T.identity b

/-- Def 59: Triangle — second leg of indirect. -/
noncomputable def triangle_indirect_leg2 {C : Type u} (T : TriangleData C) (a b : C) :
    Path (T.compose a (T.compose T.identity b)) (T.compose a b) :=
  congrArg (T.compose a) (T.leftUnit b)

/-- Def 60: Triangle — full indirect composite. -/
noncomputable def triangle_indirect_full {C : Type u} (T : TriangleData C) (a b : C) :
    Path (T.compose (T.compose a T.identity) b) (T.compose a b) :=
  Path.trans (triangle_indirect T a b) (triangle_indirect_leg2 T a b)

-- ============================================================
-- Section 12: Path Algebra Coherence
-- ============================================================

/-- Theorem 61: Triple path composition associativity. -/
theorem triple_path_assoc {C : Type u} {a b c d : C}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    trans (trans p q) r = trans p (trans q r) :=
  trans_assoc p q r

/-- Theorem 62: Left identity. -/
theorem path_left_id {C : Type u} {a b : C} (p : Path a b) :
    trans (refl a) p = p :=
  trans_refl_left p

/-- Theorem 63: Right identity. -/
theorem path_right_id {C : Type u} {a b : C} (p : Path a b) :
    trans p (refl b) = p :=
  trans_refl_right p

/-- Theorem 64: Double inverse is identity. -/
theorem path_double_inv {C : Type u} {a b : C} (p : Path a b) :
    symm (symm p) = p :=
  symm_symm p

/-- Theorem 65: Symm of trans. -/
theorem path_symm_trans {C : Type u} {a b c : C}
    (p : Path a b) (q : Path b c) :
    symm (trans p q) = trans (symm q) (symm p) :=
  symm_trans p q

-- ============================================================
-- Section 13: Functoriality of congrArg
-- ============================================================

/-- Theorem 66: congrArg distributes over trans. -/
theorem cong_distributes_trans {C D : Type u} (f : C → D)
    {a b c : C} (p : Path a b) (q : Path b c) :
    congrArg f (trans p q) = trans (congrArg f p) (congrArg f q) :=
  congrArg_trans f p q

/-- Theorem 67: congrArg distributes over symm. -/
theorem cong_distributes_symm {C D : Type u} (f : C → D)
    {a b : C} (p : Path a b) :
    congrArg f (symm p) = symm (congrArg f p) :=
  congrArg_symm f p

/-- Theorem 68: congrArg preserves refl. -/
theorem cong_refl {C D : Type u} (f : C → D) (a : C) :
    congrArg f (refl a) = refl (f a) :=
  rfl

/-- Theorem 69: Composition of congrArg. -/
theorem cong_comp_rev {C D E : Type u} (f : D → E) (g : C → D)
    {a b : C} (p : Path a b) :
    congrArg (fun x => f (g x)) p = congrArg f (congrArg g p) :=
  congrArg_comp f g p

-- ============================================================
-- Section 14: Colored Operads (Multicategories)
-- ============================================================

/-- A colored operad. -/
structure ColoredOperad (Color : Type u) (C : Type v) where
  ops : List Color → Color → C
  identity : Color → C
  compose : C → C → C

/-- Colored operad unitality witness. -/
structure ColoredUnit {Color : Type u} {C : Type v} (O : ColoredOperad Color C) where
  witness : (c : Color) → Path (O.compose (O.identity c) (O.identity c)) (O.identity c)

/-- Def 70: Colored unit path reversed. -/
noncomputable def colored_unit_inv {Color : Type u} {C : Type v}
    (O : ColoredOperad Color C) (cu : ColoredUnit O) (c : Color) :
    Path (O.identity c) (O.compose (O.identity c) (O.identity c)) :=
  Path.symm (cu.witness c)

/-- Theorem 71: Colored unit double symm. -/
theorem colored_unit_symm_symm {Color : Type u} {C : Type v}
    (O : ColoredOperad Color C) (cu : ColoredUnit O) (c : Color) :
    symm (symm (cu.witness c)) = cu.witness c :=
  symm_symm (cu.witness c)

-- ============================================================
-- Section 15: Operad 2-Cells
-- ============================================================

/-- A 2-cell between operad morphisms. -/
structure OperadTwoCell {C : Type u} {O1 O2 : Operad C}
    (m1 m2 : OperadMorphism O1 O2) where
  component : (c : C) → Path (m1.map c) (m2.map c)

/-- Identity 2-cell. -/
noncomputable def operadTwoCellId {C : Type u} {O1 O2 : Operad C}
    (m : OperadMorphism O1 O2) : OperadTwoCell m m where
  component := fun c => Path.refl (m.map c)

/-- Theorem 72: Identity 2-cell component is refl. -/
theorem two_cell_id_component {C : Type u} {O1 O2 : Operad C}
    (m : OperadMorphism O1 O2) (c : C) :
    (operadTwoCellId m).component c = refl (m.map c) :=
  rfl

/-- Vertical composition of 2-cells. -/
noncomputable def operadTwoCellVComp {C : Type u} {O1 O2 : Operad C}
    {m1 m2 m3 : OperadMorphism O1 O2}
    (alpha : OperadTwoCell m1 m2) (beta : OperadTwoCell m2 m3) :
    OperadTwoCell m1 m3 where
  component := fun c => Path.trans (alpha.component c) (beta.component c)

/-- Theorem 73: VComp with id on left. -/
theorem vcomp_id_left {C : Type u} {O1 O2 : Operad C}
    {m1 m2 : OperadMorphism O1 O2} (alpha : OperadTwoCell m1 m2) (c : C) :
    (operadTwoCellVComp (operadTwoCellId m1) alpha).component c = alpha.component c :=
  trans_refl_left (alpha.component c)

/-- Theorem 74: VComp with id on right. -/
theorem vcomp_id_right {C : Type u} {O1 O2 : Operad C}
    {m1 m2 : OperadMorphism O1 O2} (alpha : OperadTwoCell m1 m2) (c : C) :
    (operadTwoCellVComp alpha (operadTwoCellId m2)).component c = alpha.component c :=
  trans_refl_right (alpha.component c)

/-- Inverse 2-cell. -/
noncomputable def operadTwoCellInv {C : Type u} {O1 O2 : Operad C}
    {m1 m2 : OperadMorphism O1 O2}
    (alpha : OperadTwoCell m1 m2) : OperadTwoCell m2 m1 where
  component := fun c => Path.symm (alpha.component c)

/-- Theorem 75: VComp assoc. -/
theorem vcomp_assoc {C : Type u} {O1 O2 : Operad C}
    {m1 m2 m3 m4 : OperadMorphism O1 O2}
    (alpha : OperadTwoCell m1 m2) (beta : OperadTwoCell m2 m3)
    (gamma : OperadTwoCell m3 m4) (c : C) :
    (operadTwoCellVComp (operadTwoCellVComp alpha beta) gamma).component c =
    (operadTwoCellVComp alpha (operadTwoCellVComp beta gamma)).component c :=
  trans_assoc (alpha.component c) (beta.component c) (gamma.component c)

-- ============================================================
-- Section 16: Operadic Suspension / Desuspension
-- ============================================================

/-- Operadic suspension data. -/
structure OperadSuspension (C : Type u) where
  base : Operad C
  suspend : C → C
  desuspend : C → C
  susp_desusp : (c : C) → Path (suspend (desuspend c)) c
  desusp_susp : (c : C) → Path (desuspend (suspend c)) c

/-- Theorem 76: Susp-desusp double symm. -/
theorem susp_desusp_symm_symm {C : Type u} (S : OperadSuspension C) (c : C) :
    symm (symm (S.susp_desusp c)) = S.susp_desusp c :=
  symm_symm (S.susp_desusp c)

/-- Def 77: Suspension functoriality. -/
noncomputable def susp_functorial {C : Type u} (S : OperadSuspension C)
    {a b : C} (p : Path a b) :
    Path (S.suspend a) (S.suspend b) :=
  congrArg S.suspend p

/-- Def 78: Desuspension functoriality. -/
noncomputable def desusp_functorial {C : Type u} (S : OperadSuspension C)
    {a b : C} (p : Path a b) :
    Path (S.desuspend a) (S.desuspend b) :=
  congrArg S.desuspend p

/-- Theorem 79: Suspend preserves trans. -/
theorem susp_preserves_trans {C : Type u} (S : OperadSuspension C)
    {a b c : C} (p : Path a b) (q : Path b c) :
    congrArg S.suspend (trans p q) =
    trans (congrArg S.suspend p) (congrArg S.suspend q) :=
  congrArg_trans S.suspend p q

/-- Theorem 80: Suspend preserves symm. -/
theorem susp_preserves_symm {C : Type u} (S : OperadSuspension C)
    {a b : C} (p : Path a b) :
    congrArg S.suspend (symm p) = symm (congrArg S.suspend p) :=
  congrArg_symm S.suspend p

end ComputationalPaths.OperadCoherence
