/- 
# Higher Topos Theory via Computational Paths

Synthetic higher-topos structures encoded with computational paths:
infinity-topoi, Giraud-style axioms, descent, hypercompleteness, shape,
Postnikov towers, truncation, infinity-sheaves, classifying objects,
modalities, and lex localizations.
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths.Path.Algebra.HigherToposTheoryDeep

open ComputationalPaths.Path

universe u

structure InfinityToposOps (X : Type u) where
  sheafify : X → X
  hyperComplete : X → X
  shape : X → X
  postnikov : Nat → X → X
  truncate : Nat → X → X
  classify : X → X
  modal : X → X
  lexLocalize : X → X

structure GiraudInfinityAxioms (X : Type u) (Ops : InfinityToposOps X) where
  descentUnit : (x : X) → Path x (Ops.sheafify x)
  sheafIdem : (x : X) → Path (Ops.sheafify (Ops.sheafify x)) (Ops.sheafify x)
  hyperIdem : (x : X) → Path (Ops.hyperComplete (Ops.hyperComplete x)) (Ops.hyperComplete x)
  shapeModal : (x : X) → Path (Ops.shape (Ops.modal x)) (Ops.shape x)
  classifyingUnit : (x : X) → Path x (Ops.classify x)
  modalityIdem : (x : X) → Path (Ops.modal (Ops.modal x)) (Ops.modal x)
  lexIdem : (x : X) → Path (Ops.lexLocalize (Ops.lexLocalize x)) (Ops.lexLocalize x)
  truncIdem : ∀ n : Nat, ∀ x : X, Path (Ops.truncate n (Ops.truncate n x)) (Ops.truncate n x)
  postnikovStep : ∀ n : Nat, ∀ x : X, Path (Ops.postnikov (Nat.succ n) x) (Ops.truncate n x)
  sheafModalComm : (x : X) → Path (Ops.modal (Ops.sheafify x)) (Ops.sheafify (Ops.modal x))
  lexSheafComm : (x : X) → Path (Ops.lexLocalize (Ops.sheafify x)) (Ops.sheafify (Ops.lexLocalize x))

structure SymGamWitness (X : Type u) where
  SymObj : X
  GamObj : X
  SymToGam : Path SymObj GamObj

variable {X : Type u}

def infinitySheaf (Ops : InfinityToposOps X) (x : X) : X := Ops.sheafify x
def hyperObject (Ops : InfinityToposOps X) (x : X) : X := Ops.hyperComplete x
def shapeObject (Ops : InfinityToposOps X) (x : X) : X := Ops.shape x
def postnikovObject (Ops : InfinityToposOps X) (n : Nat) (x : X) : X := Ops.postnikov n x
def truncatedObject (Ops : InfinityToposOps X) (n : Nat) (x : X) : X := Ops.truncate n x
def classifyingObject (Ops : InfinityToposOps X) (x : X) : X := Ops.classify x
def modalityObject (Ops : InfinityToposOps X) (x : X) : X := Ops.modal x
def lexLocalizationObject (Ops : InfinityToposOps X) (x : X) : X := Ops.lexLocalize x

theorem infinity_sheaf_def (Ops : InfinityToposOps X) (x : X) :
    infinitySheaf Ops x = Ops.sheafify x := rfl

theorem hyper_object_def (Ops : InfinityToposOps X) (x : X) :
    hyperObject Ops x = Ops.hyperComplete x := rfl

theorem shape_object_def (Ops : InfinityToposOps X) (x : X) :
    shapeObject Ops x = Ops.shape x := rfl

theorem postnikov_object_def (Ops : InfinityToposOps X) (n : Nat) (x : X) :
    postnikovObject Ops n x = Ops.postnikov n x := rfl

theorem truncated_object_def (Ops : InfinityToposOps X) (n : Nat) (x : X) :
    truncatedObject Ops n x = Ops.truncate n x := rfl

theorem classifying_object_def (Ops : InfinityToposOps X) (x : X) :
    classifyingObject Ops x = Ops.classify x := rfl

theorem modality_object_def (Ops : InfinityToposOps X) (x : X) :
    modalityObject Ops x = Ops.modal x := rfl

theorem lex_localization_object_def (Ops : InfinityToposOps X) (x : X) :
    lexLocalizationObject Ops x = Ops.lexLocalize x := rfl

theorem descent_unit_double_symm (Ops : InfinityToposOps X)
    (Ax : GiraudInfinityAxioms X Ops) (x : X) :
    Path.symm (Path.symm (Ax.descentUnit x)) = Ax.descentUnit x :=
  Path.symm_symm _

theorem descent_unit_refl_left (Ops : InfinityToposOps X)
    (Ax : GiraudInfinityAxioms X Ops) (x : X) :
    Path.trans (Path.refl x) (Ax.descentUnit x) = Ax.descentUnit x :=
  Path.trans_refl_left _

theorem descent_unit_refl_right (Ops : InfinityToposOps X)
    (Ax : GiraudInfinityAxioms X Ops) (x : X) :
    Path.trans (Ax.descentUnit x) (Path.refl (Ops.sheafify x)) = Ax.descentUnit x :=
  Path.trans_refl_right _

theorem descent_unit_symm_trans (Ops : InfinityToposOps X)
    (Ax : GiraudInfinityAxioms X Ops) (x : X) :
    Path.symm (Path.trans (Ax.descentUnit x) (Path.symm (Ax.descentUnit x))) =
      Path.trans
        (Path.symm (Path.symm (Ax.descentUnit x)))
        (Path.symm (Ax.descentUnit x)) :=
  Path.symm_trans _ _

theorem descent_unit_congrArg_symm (Ops : InfinityToposOps X)
    (Ax : GiraudInfinityAxioms X Ops) (x : X) :
    Path.congrArg Ops.modal (Path.symm (Ax.descentUnit x)) =
      Path.symm (Path.congrArg Ops.modal (Ax.descentUnit x)) :=
  Path.congrArg_symm Ops.modal (Ax.descentUnit x)

theorem descent_unit_congrArg_trans (Ops : InfinityToposOps X)
    (Ax : GiraudInfinityAxioms X Ops) (x : X) :
    Path.congrArg Ops.modal (Path.trans (Ax.descentUnit x) (Path.symm (Ax.descentUnit x))) =
      Path.trans
        (Path.congrArg Ops.modal (Ax.descentUnit x))
        (Path.congrArg Ops.modal (Path.symm (Ax.descentUnit x))) :=
  Path.congrArg_trans Ops.modal _ _

theorem descent_unit_three_assoc (Ops : InfinityToposOps X)
    (Ax : GiraudInfinityAxioms X Ops) (x : X) :
    Path.trans
      (Path.trans (Ax.descentUnit x) (Path.symm (Ax.descentUnit x)))
      (Ax.descentUnit x) =
    Path.trans
      (Ax.descentUnit x)
      (Path.trans (Path.symm (Ax.descentUnit x)) (Ax.descentUnit x)) :=
  Path.trans_assoc _ _ _

theorem descent_unit_roundtrip_toEq (Ops : InfinityToposOps X)
    (Ax : GiraudInfinityAxioms X Ops) (x : X) :
    (Path.trans (Ax.descentUnit x) (Path.symm (Ax.descentUnit x))).toEq = rfl := by
  simp

theorem descent_unit_backtrack_toEq (Ops : InfinityToposOps X)
    (Ax : GiraudInfinityAxioms X Ops) (x : X) :
    (Path.trans (Path.symm (Ax.descentUnit x)) (Ax.descentUnit x)).toEq = rfl := by
  simp

theorem descent_unit_modal_image (Ops : InfinityToposOps X)
    (Ax : GiraudInfinityAxioms X Ops) (x : X) :
    Path.congrArg Ops.modal (Ax.descentUnit x) = Path.congrArg Ops.modal (Ax.descentUnit x) :=
  rfl

theorem descent_unit_lex_image (Ops : InfinityToposOps X)
    (Ax : GiraudInfinityAxioms X Ops) (x : X) :
    Path.congrArg Ops.lexLocalize (Ax.descentUnit x) =
      Path.congrArg Ops.lexLocalize (Ax.descentUnit x) :=
  rfl

theorem sheaf_idem_double_symm (Ops : InfinityToposOps X)
    (Ax : GiraudInfinityAxioms X Ops) (x : X) :
    Path.symm (Path.symm (Ax.sheafIdem x)) = Ax.sheafIdem x :=
  Path.symm_symm _

theorem sheaf_idem_refl_left (Ops : InfinityToposOps X)
    (Ax : GiraudInfinityAxioms X Ops) (x : X) :
    Path.trans (Path.refl (Ops.sheafify (Ops.sheafify x))) (Ax.sheafIdem x) = Ax.sheafIdem x :=
  Path.trans_refl_left _

theorem sheaf_idem_refl_right (Ops : InfinityToposOps X)
    (Ax : GiraudInfinityAxioms X Ops) (x : X) :
    Path.trans (Ax.sheafIdem x) (Path.refl (Ops.sheafify x)) = Ax.sheafIdem x :=
  Path.trans_refl_right _

theorem sheaf_idem_symm_trans (Ops : InfinityToposOps X)
    (Ax : GiraudInfinityAxioms X Ops) (x : X) :
    Path.symm (Path.trans (Ax.sheafIdem x) (Path.symm (Ax.sheafIdem x))) =
      Path.trans (Path.symm (Path.symm (Ax.sheafIdem x))) (Path.symm (Ax.sheafIdem x)) :=
  Path.symm_trans _ _

theorem sheaf_idem_congrArg_modal (Ops : InfinityToposOps X)
    (Ax : GiraudInfinityAxioms X Ops) (x : X) :
    Path.congrArg Ops.modal (Ax.sheafIdem x) = Path.congrArg Ops.modal (Ax.sheafIdem x) :=
  rfl

theorem sheaf_idem_congrArg_lex (Ops : InfinityToposOps X)
    (Ax : GiraudInfinityAxioms X Ops) (x : X) :
    Path.congrArg Ops.lexLocalize (Ax.sheafIdem x) =
      Path.congrArg Ops.lexLocalize (Ax.sheafIdem x) :=
  rfl

theorem sheaf_idem_three_assoc (Ops : InfinityToposOps X)
    (Ax : GiraudInfinityAxioms X Ops) (x : X) :
    Path.trans
      (Path.trans (Ax.sheafIdem x) (Path.symm (Ax.sheafIdem x)))
      (Ax.sheafIdem x) =
    Path.trans
      (Ax.sheafIdem x)
      (Path.trans (Path.symm (Ax.sheafIdem x)) (Ax.sheafIdem x)) :=
  Path.trans_assoc _ _ _

theorem sheaf_idem_roundtrip_toEq (Ops : InfinityToposOps X)
    (Ax : GiraudInfinityAxioms X Ops) (x : X) :
    (Path.trans (Ax.sheafIdem x) (Path.symm (Ax.sheafIdem x))).toEq = rfl := by
  simp

theorem hyper_idem_double_symm (Ops : InfinityToposOps X)
    (Ax : GiraudInfinityAxioms X Ops) (x : X) :
    Path.symm (Path.symm (Ax.hyperIdem x)) = Ax.hyperIdem x :=
  Path.symm_symm _

theorem hyper_idem_refl_left (Ops : InfinityToposOps X)
    (Ax : GiraudInfinityAxioms X Ops) (x : X) :
    Path.trans (Path.refl (Ops.hyperComplete (Ops.hyperComplete x))) (Ax.hyperIdem x) =
      Ax.hyperIdem x :=
  Path.trans_refl_left _

theorem hyper_idem_refl_right (Ops : InfinityToposOps X)
    (Ax : GiraudInfinityAxioms X Ops) (x : X) :
    Path.trans (Ax.hyperIdem x) (Path.refl (Ops.hyperComplete x)) = Ax.hyperIdem x :=
  Path.trans_refl_right _

theorem hyper_idem_symm_trans (Ops : InfinityToposOps X)
    (Ax : GiraudInfinityAxioms X Ops) (x : X) :
    Path.symm (Path.trans (Ax.hyperIdem x) (Path.symm (Ax.hyperIdem x))) =
      Path.trans (Path.symm (Path.symm (Ax.hyperIdem x))) (Path.symm (Ax.hyperIdem x)) :=
  Path.symm_trans _ _

theorem hyper_idem_congrArg_shape (Ops : InfinityToposOps X)
    (Ax : GiraudInfinityAxioms X Ops) (x : X) :
    Path.congrArg Ops.shape (Path.symm (Ax.hyperIdem x)) =
      Path.symm (Path.congrArg Ops.shape (Ax.hyperIdem x)) :=
  Path.congrArg_symm Ops.shape (Ax.hyperIdem x)

theorem hyper_idem_congrArg_modal (Ops : InfinityToposOps X)
    (Ax : GiraudInfinityAxioms X Ops) (x : X) :
    Path.congrArg Ops.modal (Path.trans (Ax.hyperIdem x) (Path.symm (Ax.hyperIdem x))) =
      Path.trans
        (Path.congrArg Ops.modal (Ax.hyperIdem x))
        (Path.congrArg Ops.modal (Path.symm (Ax.hyperIdem x))) :=
  Path.congrArg_trans Ops.modal _ _

theorem hyper_idem_three_assoc (Ops : InfinityToposOps X)
    (Ax : GiraudInfinityAxioms X Ops) (x : X) :
    Path.trans
      (Path.trans (Ax.hyperIdem x) (Path.symm (Ax.hyperIdem x)))
      (Ax.hyperIdem x) =
    Path.trans
      (Ax.hyperIdem x)
      (Path.trans (Path.symm (Ax.hyperIdem x)) (Ax.hyperIdem x)) :=
  Path.trans_assoc _ _ _

theorem hyper_idem_roundtrip_toEq (Ops : InfinityToposOps X)
    (Ax : GiraudInfinityAxioms X Ops) (x : X) :
    (Path.trans (Ax.hyperIdem x) (Path.symm (Ax.hyperIdem x))).toEq = rfl := by
  simp

theorem shape_modal_double_symm (Ops : InfinityToposOps X)
    (Ax : GiraudInfinityAxioms X Ops) (x : X) :
    Path.symm (Path.symm (Ax.shapeModal x)) = Ax.shapeModal x :=
  Path.symm_symm _

theorem shape_modal_refl_left (Ops : InfinityToposOps X)
    (Ax : GiraudInfinityAxioms X Ops) (x : X) :
    Path.trans (Path.refl (Ops.shape (Ops.modal x))) (Ax.shapeModal x) = Ax.shapeModal x :=
  Path.trans_refl_left _

theorem shape_modal_refl_right (Ops : InfinityToposOps X)
    (Ax : GiraudInfinityAxioms X Ops) (x : X) :
    Path.trans (Ax.shapeModal x) (Path.refl (Ops.shape x)) = Ax.shapeModal x :=
  Path.trans_refl_right _

theorem shape_modal_symm_trans (Ops : InfinityToposOps X)
    (Ax : GiraudInfinityAxioms X Ops) (x : X) :
    Path.symm (Path.trans (Ax.shapeModal x) (Path.symm (Ax.shapeModal x))) =
      Path.trans (Path.symm (Path.symm (Ax.shapeModal x))) (Path.symm (Ax.shapeModal x)) :=
  Path.symm_trans _ _

theorem shape_modal_congrArg_lex (Ops : InfinityToposOps X)
    (Ax : GiraudInfinityAxioms X Ops) (x : X) :
    Path.congrArg Ops.lexLocalize (Path.symm (Ax.shapeModal x)) =
      Path.symm (Path.congrArg Ops.lexLocalize (Ax.shapeModal x)) :=
  Path.congrArg_symm Ops.lexLocalize (Ax.shapeModal x)

theorem shape_modal_congrArg_classify (Ops : InfinityToposOps X)
    (Ax : GiraudInfinityAxioms X Ops) (x : X) :
    Path.congrArg Ops.classify (Path.trans (Ax.shapeModal x) (Path.symm (Ax.shapeModal x))) =
      Path.trans
        (Path.congrArg Ops.classify (Ax.shapeModal x))
        (Path.congrArg Ops.classify (Path.symm (Ax.shapeModal x))) :=
  Path.congrArg_trans Ops.classify _ _

theorem shape_modal_three_assoc (Ops : InfinityToposOps X)
    (Ax : GiraudInfinityAxioms X Ops) (x : X) :
    Path.trans
      (Path.trans (Ax.shapeModal x) (Path.symm (Ax.shapeModal x)))
      (Ax.shapeModal x) =
    Path.trans
      (Ax.shapeModal x)
      (Path.trans (Path.symm (Ax.shapeModal x)) (Ax.shapeModal x)) :=
  Path.trans_assoc _ _ _

theorem trunc_idem_double_symm (Ops : InfinityToposOps X)
    (Ax : GiraudInfinityAxioms X Ops) (n : Nat) (x : X) :
    Path.symm (Path.symm (Ax.truncIdem n x)) = Ax.truncIdem n x :=
  Path.symm_symm _

theorem trunc_idem_refl_left (Ops : InfinityToposOps X)
    (Ax : GiraudInfinityAxioms X Ops) (n : Nat) (x : X) :
    Path.trans (Path.refl (Ops.truncate n (Ops.truncate n x))) (Ax.truncIdem n x) =
      Ax.truncIdem n x :=
  Path.trans_refl_left _

theorem trunc_idem_refl_right (Ops : InfinityToposOps X)
    (Ax : GiraudInfinityAxioms X Ops) (n : Nat) (x : X) :
    Path.trans (Ax.truncIdem n x) (Path.refl (Ops.truncate n x)) = Ax.truncIdem n x :=
  Path.trans_refl_right _

theorem trunc_idem_symm_trans (Ops : InfinityToposOps X)
    (Ax : GiraudInfinityAxioms X Ops) (n : Nat) (x : X) :
    Path.symm (Path.trans (Ax.truncIdem n x) (Path.symm (Ax.truncIdem n x))) =
      Path.trans
        (Path.symm (Path.symm (Ax.truncIdem n x)))
        (Path.symm (Ax.truncIdem n x)) :=
  Path.symm_trans _ _

theorem trunc_idem_congrArg_modal (Ops : InfinityToposOps X)
    (Ax : GiraudInfinityAxioms X Ops) (n : Nat) (x : X) :
    Path.congrArg Ops.modal (Path.symm (Ax.truncIdem n x)) =
      Path.symm (Path.congrArg Ops.modal (Ax.truncIdem n x)) :=
  Path.congrArg_symm Ops.modal (Ax.truncIdem n x)

theorem trunc_idem_three_assoc (Ops : InfinityToposOps X)
    (Ax : GiraudInfinityAxioms X Ops) (n : Nat) (x : X) :
    Path.trans
      (Path.trans (Ax.truncIdem n x) (Path.symm (Ax.truncIdem n x)))
      (Ax.truncIdem n x) =
    Path.trans
      (Ax.truncIdem n x)
      (Path.trans (Path.symm (Ax.truncIdem n x)) (Ax.truncIdem n x)) :=
  Path.trans_assoc _ _ _

theorem trunc_idem_roundtrip_toEq (Ops : InfinityToposOps X)
    (Ax : GiraudInfinityAxioms X Ops) (n : Nat) (x : X) :
    (Path.trans (Ax.truncIdem n x) (Path.symm (Ax.truncIdem n x))).toEq = rfl := by
  simp

theorem postnikov_step_double_symm (Ops : InfinityToposOps X)
    (Ax : GiraudInfinityAxioms X Ops) (n : Nat) (x : X) :
    Path.symm (Path.symm (Ax.postnikovStep n x)) = Ax.postnikovStep n x :=
  Path.symm_symm _

theorem postnikov_step_refl_left (Ops : InfinityToposOps X)
    (Ax : GiraudInfinityAxioms X Ops) (n : Nat) (x : X) :
    Path.trans (Path.refl (Ops.postnikov (Nat.succ n) x)) (Ax.postnikovStep n x) =
      Ax.postnikovStep n x :=
  Path.trans_refl_left _

theorem postnikov_step_refl_right (Ops : InfinityToposOps X)
    (Ax : GiraudInfinityAxioms X Ops) (n : Nat) (x : X) :
    Path.trans (Ax.postnikovStep n x) (Path.refl (Ops.truncate n x)) = Ax.postnikovStep n x :=
  Path.trans_refl_right _

theorem postnikov_step_symm_trans (Ops : InfinityToposOps X)
    (Ax : GiraudInfinityAxioms X Ops) (n : Nat) (x : X) :
    Path.symm (Path.trans (Ax.postnikovStep n x) (Path.symm (Ax.postnikovStep n x))) =
      Path.trans
        (Path.symm (Path.symm (Ax.postnikovStep n x)))
        (Path.symm (Ax.postnikovStep n x)) :=
  Path.symm_trans _ _

theorem postnikov_step_congrArg_shape (Ops : InfinityToposOps X)
    (Ax : GiraudInfinityAxioms X Ops) (n : Nat) (x : X) :
    Path.congrArg Ops.shape (Path.symm (Ax.postnikovStep n x)) =
      Path.symm (Path.congrArg Ops.shape (Ax.postnikovStep n x)) :=
  Path.congrArg_symm Ops.shape (Ax.postnikovStep n x)

theorem postnikov_step_roundtrip_toEq (Ops : InfinityToposOps X)
    (Ax : GiraudInfinityAxioms X Ops) (n : Nat) (x : X) :
    (Path.trans (Ax.postnikovStep n x) (Path.symm (Ax.postnikovStep n x))).toEq = rfl := by
  simp

theorem classifying_unit_double_symm (Ops : InfinityToposOps X)
    (Ax : GiraudInfinityAxioms X Ops) (x : X) :
    Path.symm (Path.symm (Ax.classifyingUnit x)) = Ax.classifyingUnit x :=
  Path.symm_symm _

theorem classifying_unit_refl_left (Ops : InfinityToposOps X)
    (Ax : GiraudInfinityAxioms X Ops) (x : X) :
    Path.trans (Path.refl x) (Ax.classifyingUnit x) = Ax.classifyingUnit x :=
  Path.trans_refl_left _

theorem classifying_unit_refl_right (Ops : InfinityToposOps X)
    (Ax : GiraudInfinityAxioms X Ops) (x : X) :
    Path.trans (Ax.classifyingUnit x) (Path.refl (Ops.classify x)) = Ax.classifyingUnit x :=
  Path.trans_refl_right _

theorem classifying_unit_symm_trans (Ops : InfinityToposOps X)
    (Ax : GiraudInfinityAxioms X Ops) (x : X) :
    Path.symm (Path.trans (Ax.classifyingUnit x) (Path.symm (Ax.classifyingUnit x))) =
      Path.trans
        (Path.symm (Path.symm (Ax.classifyingUnit x)))
        (Path.symm (Ax.classifyingUnit x)) :=
  Path.symm_trans _ _

theorem classifying_unit_congrArg_modal (Ops : InfinityToposOps X)
    (Ax : GiraudInfinityAxioms X Ops) (x : X) :
    Path.congrArg Ops.modal (Path.symm (Ax.classifyingUnit x)) =
      Path.symm (Path.congrArg Ops.modal (Ax.classifyingUnit x)) :=
  Path.congrArg_symm Ops.modal (Ax.classifyingUnit x)

theorem classifying_unit_three_assoc (Ops : InfinityToposOps X)
    (Ax : GiraudInfinityAxioms X Ops) (x : X) :
    Path.trans
      (Path.trans (Ax.classifyingUnit x) (Path.symm (Ax.classifyingUnit x)))
      (Ax.classifyingUnit x) =
    Path.trans
      (Ax.classifyingUnit x)
      (Path.trans (Path.symm (Ax.classifyingUnit x)) (Ax.classifyingUnit x)) :=
  Path.trans_assoc _ _ _

theorem modality_idem_double_symm (Ops : InfinityToposOps X)
    (Ax : GiraudInfinityAxioms X Ops) (x : X) :
    Path.symm (Path.symm (Ax.modalityIdem x)) = Ax.modalityIdem x :=
  Path.symm_symm _

theorem modality_idem_refl_left (Ops : InfinityToposOps X)
    (Ax : GiraudInfinityAxioms X Ops) (x : X) :
    Path.trans (Path.refl (Ops.modal (Ops.modal x))) (Ax.modalityIdem x) = Ax.modalityIdem x :=
  Path.trans_refl_left _

theorem modality_idem_refl_right (Ops : InfinityToposOps X)
    (Ax : GiraudInfinityAxioms X Ops) (x : X) :
    Path.trans (Ax.modalityIdem x) (Path.refl (Ops.modal x)) = Ax.modalityIdem x :=
  Path.trans_refl_right _

theorem modality_idem_symm_trans (Ops : InfinityToposOps X)
    (Ax : GiraudInfinityAxioms X Ops) (x : X) :
    Path.symm (Path.trans (Ax.modalityIdem x) (Path.symm (Ax.modalityIdem x))) =
      Path.trans (Path.symm (Path.symm (Ax.modalityIdem x))) (Path.symm (Ax.modalityIdem x)) :=
  Path.symm_trans _ _

theorem lex_idem_double_symm (Ops : InfinityToposOps X)
    (Ax : GiraudInfinityAxioms X Ops) (x : X) :
    Path.symm (Path.symm (Ax.lexIdem x)) = Ax.lexIdem x :=
  Path.symm_symm _

theorem lex_idem_refl_left (Ops : InfinityToposOps X)
    (Ax : GiraudInfinityAxioms X Ops) (x : X) :
    Path.trans (Path.refl (Ops.lexLocalize (Ops.lexLocalize x))) (Ax.lexIdem x) = Ax.lexIdem x :=
  Path.trans_refl_left _

theorem lex_idem_refl_right (Ops : InfinityToposOps X)
    (Ax : GiraudInfinityAxioms X Ops) (x : X) :
    Path.trans (Ax.lexIdem x) (Path.refl (Ops.lexLocalize x)) = Ax.lexIdem x :=
  Path.trans_refl_right _

theorem lex_idem_symm_trans (Ops : InfinityToposOps X)
    (Ax : GiraudInfinityAxioms X Ops) (x : X) :
    Path.symm (Path.trans (Ax.lexIdem x) (Path.symm (Ax.lexIdem x))) =
      Path.trans (Path.symm (Path.symm (Ax.lexIdem x))) (Path.symm (Ax.lexIdem x)) :=
  Path.symm_trans _ _

theorem sheaf_modal_comm_double_symm (Ops : InfinityToposOps X)
    (Ax : GiraudInfinityAxioms X Ops) (x : X) :
    Path.symm (Path.symm (Ax.sheafModalComm x)) = Ax.sheafModalComm x :=
  Path.symm_symm _

theorem lex_sheaf_comm_double_symm (Ops : InfinityToposOps X)
    (Ax : GiraudInfinityAxioms X Ops) (x : X) :
    Path.symm (Path.symm (Ax.lexSheafComm x)) = Ax.lexSheafComm x :=
  Path.symm_symm _

theorem sym_gam_double_symm (w : SymGamWitness X) :
    Path.symm (Path.symm w.SymToGam) = w.SymToGam :=
  Path.symm_symm _

theorem sym_gam_refl_left (w : SymGamWitness X) :
    Path.trans (Path.refl w.SymObj) w.SymToGam = w.SymToGam :=
  Path.trans_refl_left _

theorem sym_gam_refl_right (w : SymGamWitness X) :
    Path.trans w.SymToGam (Path.refl w.GamObj) = w.SymToGam :=
  Path.trans_refl_right _

theorem sym_gam_symm_trans (w : SymGamWitness X) :
    Path.symm (Path.trans w.SymToGam (Path.symm w.SymToGam)) =
      Path.trans (Path.symm (Path.symm w.SymToGam)) (Path.symm w.SymToGam) :=
  Path.symm_trans _ _

theorem sym_gam_roundtrip_toEq (w : SymGamWitness X) :
    (Path.trans w.SymToGam (Path.symm w.SymToGam)).toEq = rfl := by
  simp

theorem sym_gam_backtrack_toEq (w : SymGamWitness X) :
    (Path.trans (Path.symm w.SymToGam) w.SymToGam).toEq = rfl := by
  simp

end ComputationalPaths.Path.Algebra.HigherToposTheoryDeep
