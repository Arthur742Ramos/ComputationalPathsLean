import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths
namespace Path
namespace Foundations
namespace ToposLogic

universe u v

structure Category where
  Obj : Type u
  Hom : Obj → Obj → Type v
  id : (A : Obj) → Hom A A
  comp : {A B C : Obj} → Hom A B → Hom B C → Hom A C

def homSet (C : Category) (A B : C.Obj) : Type v := C.Hom A B
def idHom (C : Category) (A : C.Obj) : C.Hom A A := C.id A
def composeHom (C : Category) {A B D : C.Obj} (f : C.Hom A B) (g : C.Hom B D) : C.Hom A D :=
  C.comp f g

structure Topos where
  cat : Category
  terminal : cat.Obj
  omega : cat.Obj
  truth : cat.Hom terminal omega
  falsity : cat.Hom terminal omega
  andOp : cat.Hom omega omega
  orOp : cat.Hom omega omega
  impOp : cat.Hom omega omega

def omegaObj (T : Topos) : T.cat.Obj := T.omega
def terminalObj (T : Topos) : T.cat.Obj := T.terminal
def truthArrow (T : Topos) : T.cat.Hom (terminalObj T) (omegaObj T) := T.truth
def falsityArrow (T : Topos) : T.cat.Hom (terminalObj T) (omegaObj T) := T.falsity
def andArrow (T : Topos) : T.cat.Hom (omegaObj T) (omegaObj T) := T.andOp
def orArrow (T : Topos) : T.cat.Hom (omegaObj T) (omegaObj T) := T.orOp
def impArrow (T : Topos) : T.cat.Hom (omegaObj T) (omegaObj T) := T.impOp

structure MitchellBenabou (T : Topos) where
  Term : Type u
  Formula : Type u
  interpTerm : Term → T.cat.Obj
  interpFormula : Formula → T.cat.Hom T.terminal T.omega

def mbInterpretTerm {T : Topos} (L : MitchellBenabou T) (t : L.Term) : T.cat.Obj := L.interpTerm t
def mbInterpretFormula {T : Topos} (L : MitchellBenabou T)
    (φ : L.Formula) : T.cat.Hom T.terminal T.omega := L.interpFormula φ

structure KripkeJoyalModel (T : Topos) where
  World : Type u
  le : World → World → Prop
  forces : World → Prop → Prop

def kripkeForces {T : Topos} (K : KripkeJoyalModel T) (w : K.World) (P : Prop) : Prop :=
  K.forces w P
def kripkeOrder {T : Topos} (K : KripkeJoyalModel T) (w₁ w₂ : K.World) : Prop := K.le w₁ w₂

structure GeometricTheory where
  sort : Type u
  axiomSet : Type u

def geometricSorts (G : GeometricTheory) : Type u := G.sort
def geometricAxiomSet (G : GeometricTheory) : Type u := G.axiomSet

structure ClassifyingTopos where
  base : Topos
  theory : GeometricTheory

def classifyingObject (C : ClassifyingTopos) : Topos := C.base
def classifyingTheory (C : ClassifyingTopos) : GeometricTheory := C.theory

structure BarrWitness (C : ClassifyingTopos) where
  hasCover : Prop
  barrTheorem : Prop

def barrCovering {C : ClassifyingTopos} (B : BarrWitness C) : Prop := B.hasCover
def barrRefinement {C : ClassifyingTopos} (B : BarrWitness C) : Prop := B.barrTheorem

def logicPathChain (P : Prop) : Path P P := Path.trans (Path.refl P) (Path.refl P)
def internalTruthPath (T : Topos) : Path (truthArrow T) (truthArrow T) := Path.refl (truthArrow T)

theorem homSet_id {C : Category} (A : C.Obj) : homSet C A A = C.Hom A A := rfl

theorem composeHom_def {C : Category} {A B D : C.Obj} (f : C.Hom A B) (g : C.Hom B D) :
    composeHom C f g = C.comp f g := rfl

theorem omegaObj_def (T : Topos) : omegaObj T = T.omega := rfl

theorem terminalObj_def (T : Topos) : terminalObj T = T.terminal := rfl

theorem truthArrow_def (T : Topos) : truthArrow T = T.truth := rfl

theorem falsityArrow_def (T : Topos) : falsityArrow T = T.falsity := rfl

theorem andArrow_def (T : Topos) : andArrow T = T.andOp := rfl

theorem orArrow_def (T : Topos) : orArrow T = T.orOp := rfl

theorem impArrow_def (T : Topos) : impArrow T = T.impOp := rfl

theorem mbInterpretTerm_def {T : Topos} (L : MitchellBenabou T) (t : L.Term) :
    mbInterpretTerm L t = L.interpTerm t := rfl

theorem mbInterpretFormula_def {T : Topos} (L : MitchellBenabou T) (φ : L.Formula) :
    mbInterpretFormula L φ = L.interpFormula φ := rfl

theorem kripkeForces_def {T : Topos} (K : KripkeJoyalModel T) (w : K.World) (P : Prop) :
    kripkeForces K w P = K.forces w P := rfl

theorem kripkeOrder_def {T : Topos} (K : KripkeJoyalModel T) (w₁ w₂ : K.World) :
    kripkeOrder K w₁ w₂ = K.le w₁ w₂ := rfl

theorem geometricSorts_def (G : GeometricTheory) : geometricSorts G = G.sort := rfl

theorem geometricAxiomSet_def (G : GeometricTheory) : geometricAxiomSet G = G.axiomSet := rfl

theorem classifyingObject_def (C : ClassifyingTopos) : classifyingObject C = C.base := rfl

theorem classifyingTheory_def (C : ClassifyingTopos) : classifyingTheory C = C.theory := rfl

theorem barrCovering_def {C : ClassifyingTopos} (B : BarrWitness C) : barrCovering B = B.hasCover := rfl

theorem barrRefinement_def {C : ClassifyingTopos} (B : BarrWitness C) :
    barrRefinement B = B.barrTheorem := rfl

theorem logicPathChain_toEq (P : Prop) : (logicPathChain P).toEq = rfl := rfl

theorem internalTruthPath_toEq (T : Topos) : (internalTruthPath T).toEq = rfl := rfl

end ToposLogic
end Foundations
end Path
end ComputationalPaths
