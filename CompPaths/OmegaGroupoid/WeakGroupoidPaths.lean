import CompPaths.Core

namespace CompPaths
namespace OmegaGroupoid

open ComputationalPaths
open ComputationalPaths.Path

universe u

namespace WeakLayer

variable {X : Type u}

abbrev Cell (x y : X) : Type u := Path x y

@[simp] def id (x : X) : Cell x x := Path.refl x

@[simp] def comp {x y z : X} (p : Cell x y) (q : Cell y z) : Cell x z :=
  Path.trans p q

@[simp] def inv {x y : X} (p : Cell x y) : Cell y x :=
  Path.symm p

@[simp] theorem assoc {x y z w : X} (p : Cell x y) (q : Cell y z) (r : Cell z w) :
    RwEq (comp (comp p q) r) (comp p (comp q r)) :=
  rweq_tt p q r

@[simp] theorem id_left {x y : X} (p : Cell x y) :
    RwEq (comp (id x) p) p :=
  rweq_cmpA_refl_left p

@[simp] theorem id_right {x y : X} (p : Cell x y) :
    RwEq (comp p (id y)) p :=
  rweq_cmpA_refl_right p

@[simp] theorem inv_left {x y : X} (p : Cell x y) :
    RwEq (comp (inv p) p) (id y) :=
  rweq_cmpA_inv_left p

@[simp] theorem inv_right {x y : X} (p : Cell x y) :
    RwEq (comp p (inv p)) (id x) :=
  rweq_cmpA_inv_right p

def coherence {x y : X} {p q : Cell x y} (h₁ h₂ : RwEq p q) : h₁ = h₂ :=
  Subsingleton.elim h₁ h₂

def pentagonWitness {x y z w v : X}
    (p : Cell x y) (q : Cell y z) (r : Cell z w) (s : Cell w v) :
    (RwEq.trans (assoc (comp p q) r s) (assoc p q (comp r s))) =
      (RwEq.trans
        (rweq_trans_congr_left s (assoc p q r))
        (RwEq.trans (assoc p (comp q r) s)
          (rweq_trans_congr_right p (assoc q r s)))) :=
  coherence _ _

def triangleWitness {x y z : X} (p : Cell x y) (q : Cell y z) :
    (RwEq.trans (assoc p (id y) q) (rweq_trans_congr_right p (id_left q))) =
      (rweq_trans_congr_left q (id_right p)) :=
  coherence _ _

def inverseUnitWitness {x y : X} (p : Cell x y) :
    (RwEq.trans
      (assoc p (inv p) p)
      (RwEq.trans
        (rweq_trans_congr_right p (inv_left p))
        (id_right p))) =
      (RwEq.trans
        (rweq_trans_congr_left p (inv_right p))
        (id_left p)) :=
  coherence _ _

end WeakLayer

section Levels

variable {A : Type u}

abbrev Cell1 (a b : A) : Type u := WeakLayer.Cell (X := A) a b

abbrev Cell2 {a b : A} (p q : Cell1 a b) : Type u :=
  WeakLayer.Cell (X := Cell1 a b) p q

abbrev Cell3 {a b : A} {p q : Cell1 a b} (α β : Cell2 p q) : Type u :=
  WeakLayer.Cell (X := Cell2 p q) α β

theorem level1_groupoid {a b c d : A}
    (p : Cell1 a b) (q : Cell1 b c) (r : Cell1 c d) :
    RwEq (WeakLayer.comp (WeakLayer.comp p q) r)
      (WeakLayer.comp p (WeakLayer.comp q r)) :=
  WeakLayer.assoc p q r

theorem level2_groupoid {a b : A} {p q r s : Cell1 a b}
    (α : Cell2 p q) (β : Cell2 q r) (γ : Cell2 r s) :
    RwEq (WeakLayer.comp (WeakLayer.comp α β) γ)
      (WeakLayer.comp α (WeakLayer.comp β γ)) :=
  WeakLayer.assoc α β γ

theorem level3_groupoid {a b : A} {p q : Cell1 a b} {α β γ δ : Cell2 p q}
    (φ : Cell3 α β) (ψ : Cell3 β γ) (χ : Cell3 γ δ) :
    RwEq (WeakLayer.comp (WeakLayer.comp φ ψ) χ)
      (WeakLayer.comp φ (WeakLayer.comp ψ χ)) :=
  WeakLayer.assoc φ ψ χ

def level1_pentagon {a b c d e : A}
    (p : Cell1 a b) (q : Cell1 b c) (r : Cell1 c d) (s : Cell1 d e) :
    (RwEq.trans (WeakLayer.assoc (WeakLayer.comp p q) r s)
      (WeakLayer.assoc p q (WeakLayer.comp r s))) =
      (RwEq.trans
        (rweq_trans_congr_left s (WeakLayer.assoc p q r))
        (RwEq.trans (WeakLayer.assoc p (WeakLayer.comp q r) s)
          (rweq_trans_congr_right p (WeakLayer.assoc q r s)))) :=
  WeakLayer.pentagonWitness p q r s

def level1_triangle {a b c : A} (p : Cell1 a b) (q : Cell1 b c) :
    (RwEq.trans (WeakLayer.assoc p (WeakLayer.id b) q)
      (rweq_trans_congr_right p (WeakLayer.id_left q))) =
      (rweq_trans_congr_left q (WeakLayer.id_right p)) :=
  WeakLayer.triangleWitness p q

def level1_inverse_unit {a b : A} (p : Cell1 a b) :
    (RwEq.trans
      (WeakLayer.assoc p (WeakLayer.inv p) p)
      (RwEq.trans
        (rweq_trans_congr_right p (WeakLayer.inv_left p))
        (WeakLayer.id_right p))) =
      (RwEq.trans
        (rweq_trans_congr_left p (WeakLayer.inv_right p))
        (WeakLayer.id_left p)) :=
  WeakLayer.inverseUnitWitness p

end Levels

end OmegaGroupoid
end CompPaths
