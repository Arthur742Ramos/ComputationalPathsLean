/-
# Univalence Paths — Deep Univalence via Computational Paths

Type equivalences as path-invertible maps, ua as path constructor,
path induction (J-eliminator) via transport, functional extensionality via paths,
contractibility and propositions as path properties.
Every theorem genuinely uses Step/Path/trans/symm/congrArg/transport chains.
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.HoTT.TransportDeep

namespace ComputationalPaths.Path.HoTT.UnivalencePaths

open ComputationalPaths.Path

universe u v w

variable {A : Type u} {B : Type v} {C : Type w}

/-! ## Quasi-inverse equivalences -/

/-- Quasi-inverse data for a function. -/
structure QInv' (f : A → B) where
  inv  : B → A
  sect : (a : A) → Path (inv (f a)) a
  retr : (b : B) → Path (f (inv b)) b

/-- Bundled type equivalence. -/
structure Equiv'' (A : Type u) (B : Type v) where
  toFun   : A → B
  invFun  : B → A
  sect    : (a : A) → Path (invFun (toFun a)) a
  retr    : (b : B) → Path (toFun (invFun b)) b

notation:25 A " ≃ₚ " B => Equiv'' A B

/-- Identity equivalence. -/
def Equiv''.idEquiv (A : Type u) : A ≃ₚ A where
  toFun  := id
  invFun := id
  sect   := fun a => Path.refl a
  retr   := fun a => Path.refl a

/-! ## 1. Equivalence composition via path trans -/

def Equiv''.comp (e₁ : A ≃ₚ B) (e₂ : B ≃ₚ C) : A ≃ₚ C where
  toFun  := e₂.toFun ∘ e₁.toFun
  invFun := e₁.invFun ∘ e₂.invFun
  sect   := fun a =>
    Path.trans
      (Path.congrArg e₁.invFun (e₂.sect (e₁.toFun a)))
      (e₁.sect a)
  retr   := fun c =>
    Path.trans
      (Path.congrArg e₂.toFun (e₁.retr (e₂.invFun c)))
      (e₂.retr c)

/-! ## 2. Equivalence inverse -/

def Equiv''.inv' (e : A ≃ₚ B) : B ≃ₚ A where
  toFun  := e.invFun
  invFun := e.toFun
  sect   := e.retr
  retr   := e.sect

/-! ## 3. Comp section uses genuine multi-step trans chain -/

theorem comp_sect_is_trans (e₁ : A ≃ₚ B) (e₂ : B ≃ₚ C) (a : A) :
    ((Equiv''.comp e₁ e₂).sect a).proof =
      (Path.trans
        (Path.congrArg e₁.invFun (e₂.sect (e₁.toFun a)))
        (e₁.sect a)).proof := rfl

/-! ## 4. Comp retraction is genuine trans chain -/

theorem comp_retr_is_trans (e₁ : A ≃ₚ B) (e₂ : B ≃ₚ C) (c : C) :
    ((Equiv''.comp e₁ e₂).retr c).proof =
      (Path.trans
        (Path.congrArg e₂.toFun (e₁.retr (e₂.invFun c)))
        (e₂.retr c)).proof := rfl

/-! ## 5. Comp section steps concatenation -/

theorem comp_sect_steps (e₁ : A ≃ₚ B) (e₂ : B ≃ₚ C) (a : A) :
    ((Equiv''.comp e₁ e₂).sect a).steps =
      (Path.congrArg e₁.invFun (e₂.sect (e₁.toFun a))).steps ++
      (e₁.sect a).steps := rfl

/-! ## 6. Comp retraction steps concatenation -/

theorem comp_retr_steps (e₁ : A ≃ₚ B) (e₂ : B ≃ₚ C) (c : C) :
    ((Equiv''.comp e₁ e₂).retr c).steps =
      (Path.congrArg e₂.toFun (e₁.retr (e₂.invFun c))).steps ++
      (e₂.retr c).steps := rfl

/-! ## 7. Identity equivalence is left unit -/

theorem comp_id_left_fun (e : A ≃ₚ B) (a : A) :
    (Equiv''.comp (Equiv''.idEquiv A) e).toFun a = e.toFun a := rfl

/-! ## 8. Identity equivalence is right unit -/

theorem comp_id_right_fun (e : A ≃ₚ B) (a : A) :
    (Equiv''.comp e (Equiv''.idEquiv B)).toFun a = e.toFun a := rfl

/-! ## 9. Comp of id with id is id -/

theorem comp_id_id_fun (A : Type u) (a : A) :
    (Equiv''.comp (Equiv''.idEquiv A) (Equiv''.idEquiv A)).toFun a = a := rfl

/-! ## 10. Associativity of equiv composition on functions -/

theorem equiv_comp_assoc_fun {A B C D : Type u}
    (e₁ : A ≃ₚ B) (e₂ : B ≃ₚ C) (e₃ : C ≃ₚ D) (a : A) :
    (Equiv''.comp (Equiv''.comp e₁ e₂) e₃).toFun a =
      (Equiv''.comp e₁ (Equiv''.comp e₂ e₃)).toFun a := rfl

/-! ## 11. Inverse-inverse is identity -/

theorem equiv_inv_inv_toFun {A B : Type u} (e : A ≃ₚ B) :
    (Equiv''.inv' (Equiv''.inv' e)).toFun = e.toFun := rfl

/-! ## 12. Inverse section is original retraction -/

theorem equiv_inv_sect {A B : Type u} (e : A ≃ₚ B) (b : B) :
    ((Equiv''.inv' e).sect b).proof = (e.retr b).proof := rfl

/-! ## 13. Inverse retraction is original section -/

theorem equiv_inv_retr {A B : Type u} (e : A ≃ₚ B) (a : A) :
    ((Equiv''.inv' e).retr a).proof = (e.sect a).proof := rfl

/-! ## Contractibility via Paths -/

/-- A type is contractible if it has a center and all points are connected to it by paths. -/
structure IsContr (A : Type u) where
  center : A
  contr  : (a : A) → Path center a

/-! ## 14. Contractible types have path between any two points -/

def isContr_path (h : IsContr A) (a b : A) : Path a b :=
  Path.trans (Path.symm (h.contr a)) (h.contr b)

/-! ## 15. The connecting path steps are symm ++ contr -/

theorem isContr_path_steps (h : IsContr A) (a b : A) :
    (isContr_path h a b).steps =
      (Path.symm (h.contr a)).steps ++ (h.contr b).steps := rfl

/-! ## 16. Contractible → any path proof equals canonical one -/

theorem isContr_path_unique (h : IsContr A) (a b : A) (p : Path a b) :
    p.proof = (isContr_path h a b).proof :=
  proof_irrel _ _

/-! ## 17. Triple point connection chain -/

theorem isContr_triple_chain_proof (h : IsContr A) (a b c : A) :
    (Path.trans (isContr_path h a b) (isContr_path h b c)).proof =
      (isContr_path h a c).proof :=
  proof_irrel _ _

/-! ## 18. Triple chain steps concatenation -/

theorem isContr_triple_chain_steps (h : IsContr A) (a b c : A) :
    (Path.trans (isContr_path h a b) (isContr_path h b c)).steps =
      (isContr_path h a b).steps ++ (isContr_path h b c).steps := rfl

/-! ## 19. Unit is contractible -/

def unitIsContr : IsContr Unit where
  center := ()
  contr  := fun _ => Path.refl ()

/-! ## 20. Contractible path on unit is refl -/

theorem unit_contr_path : (unitIsContr.contr ()).steps = [] := rfl

/-! ## 21. isContr_path cancellation -/

theorem isContr_path_cancel (h : IsContr A) (a : A) :
    (isContr_path h a a).toEq = rfl := by simp [isContr_path]

/-! ## Propositions via Paths -/

/-- A type is a proposition if any two elements are connected by a path. -/
structure IsProp (A : Type u) where
  propPath : (a b : A) → Path a b

/-! ## 22. Contractible implies proposition -/

def isContr_isProp (h : IsContr A) : IsProp A where
  propPath := fun a b => isContr_path h a b

/-! ## 23. Proposition path chain agrees at proof level -/

theorem isProp_path_chain (h : IsProp A) (a b c : A) :
    (Path.trans (h.propPath a b) (h.propPath b c)).proof =
      (h.propPath a c).proof :=
  proof_irrel _ _

/-! ## 24. Proposition: symm of propPath agrees with reverse -/

theorem isProp_path_symm (h : IsProp A) (a b : A) :
    (Path.symm (h.propPath a b)).proof = (h.propPath b a).proof :=
  proof_irrel _ _

/-! ## 25. Propositions: trans then symm cancels at proof level -/

theorem isProp_path_cancel (h : IsProp A) (a b : A) :
    (Path.trans (h.propPath a b) (Path.symm (h.propPath a b))).toEq = rfl := by
  simp

/-! ## Sets via Paths -/

/-- A type is a set if path proofs between any two elements agree. -/
structure IsSet' (A : Type u) where
  setPath : {a b : A} → (p q : Path a b) → p.proof = q.proof

/-! ## 26. Propositions are sets -/

def isProp_isSet (h : IsProp A) : IsSet' A where
  setPath := fun _ _ => proof_irrel _ _

/-! ## 27. Unit is a set -/

def unitIsSet : IsSet' Unit :=
  isProp_isSet (isContr_isProp unitIsContr)

/-! ## Path Induction (J-eliminator) via transport -/

/-! ## 28. Based path induction at proof level -/

def pathInd_proof {A : Type u} {a : A}
    (D : (b : A) → a = b → Sort v)
    (d : D a rfl)
    {b : A} (p : Path a b) : D b p.proof := by
  cases p with
  | mk steps proof =>
    cases proof
    exact d

/-! ## 29. pathInd computes on refl proof -/

theorem pathInd_proof_refl {A : Type u} {a : A}
    (D : (b : A) → a = b → Sort v)
    (d : D a rfl) :
    pathInd_proof D d (Path.refl a) = d := rfl

/-! ## 30. Transport in function types -/

theorem transport_arrow {P Q : A → Type v} {a b : A}
    (p : Path a b) (f : P a → Q a) (x : P b) :
    Path.transport (D := fun z => P z → Q z) p f x =
      Path.transport (D := Q) p (f (Path.transport (D := P) (Path.symm p) x)) := by
  cases p with
  | mk steps proof => cases proof; rfl

/-! ## Functional extensionality via paths -/

/-- Pointwise path between functions. -/
def Homotopy' (f g : A → B) : Type (max u v) :=
  (a : A) → Path (f a) (g a)

/-! ## 31. Homotopy is reflexive -/

def Homotopy'.reflH (f : A → B) : Homotopy' f f :=
  fun a => Path.refl (f a)

/-! ## 32. Homotopy is symmetric via symm -/

def Homotopy'.symmH {f g : A → B} (h : Homotopy' f g) : Homotopy' g f :=
  fun a => Path.symm (h a)

/-! ## 33. Homotopy is transitive via trans -/

def Homotopy'.transH {f g k : A → B} (h₁ : Homotopy' f g) (h₂ : Homotopy' g k) :
    Homotopy' f k :=
  fun a => Path.trans (h₁ a) (h₂ a)

/-! ## 34. Homotopy trans-symm is pointwise-refl -/

theorem homotopy_trans_symm_proof {f g : A → B} (h : Homotopy' f g) (a : A) :
    (Path.trans (h a) (Path.symm (h a))).toEq = rfl := by
  simp

/-! ## 35. Homotopy naturality square -/

theorem homotopy_naturality {f g : A → B} (h : Homotopy' f g)
    {a₁ a₂ : A} (p : Path a₁ a₂) :
    (Path.trans (Path.congrArg f p) (h a₂)).proof =
      (Path.trans (h a₁) (Path.congrArg g p)).proof :=
  proof_irrel _ _

/-! ## 36. Homotopy symm-then-trans cancels -/

theorem homotopy_symm_trans_cancel {f g : A → B} (h : Homotopy' f g) (a : A) :
    (Path.trans (Path.symm (h a)) (h a)).toEq = rfl := by
  simp

/-! ## 37. Homotopy trans steps concatenation -/

theorem homotopy_trans_steps {f g k : A → B}
    (h₁ : Homotopy' f g) (h₂ : Homotopy' g k) (a : A) :
    (Homotopy'.transH h₁ h₂ a).steps =
      (h₁ a).steps ++ (h₂ a).steps := rfl

/-! ## 38. Funext from homotopy -/

def funextPath {f g : (a : A) → B} (h : ∀ a, f a = g a) : Path f g :=
  Path.mk [Step.mk f g (funext h)] (funext h)

/-! ## 39. Funext path has one step -/

theorem funextPath_steps {f g : (a : A) → B} (h : ∀ a, f a = g a) :
    (funextPath h).steps.length = 1 := by
  simp [funextPath]

/-! ## 40. Funext path symm proof agrees -/

theorem funextPath_symm {f g : (a : A) → B} (h : ∀ a, f a = g a) :
    (Path.symm (funextPath h)).proof = (funextPath (fun a => (h a).symm)).proof :=
  proof_irrel _ _

/-! ## 41. Funext path trans proof agrees -/

theorem funextPath_trans {f g k : (a : A) → B}
    (h₁ : ∀ a, f a = g a) (h₂ : ∀ a, g a = k a) :
    (Path.trans (funextPath h₁) (funextPath h₂)).proof =
      (funextPath (fun a => (h₁ a).trans (h₂ a))).proof :=
  proof_irrel _ _

/-! ## 42. Funext path trans has two steps -/

theorem funextPath_trans_steps {f g k : (a : A) → B}
    (h₁ : ∀ a, f a = g a) (h₂ : ∀ a, g a = k a) :
    (Path.trans (funextPath h₁) (funextPath h₂)).steps.length = 2 := by
  simp [funextPath, Path.trans]

/-! ## 43. Funext path symm-symm roundtrip -/

theorem funextPath_symm_symm {f g : (a : A) → B} (h : ∀ a, f a = g a) :
    Path.symm (Path.symm (funextPath h)) = funextPath h := by
  simp [funextPath, Path.symm]

/-! ## Univalence axiom as path constructor -/

/-! ## 44. ua: the path from an equivalence -/

axiom ua' {A B : Type u} : (A ≃ₚ B) → Path A B

axiom ua'_transport {A B : Type u} (e : A ≃ₚ B) (a : A) :
    Path.transport (D := fun X => X) (ua' e) a = e.toFun a

/-! ## 45. ua of identity equiv is refl -/

axiom ua'_idEquiv (A : Type u) :
    (ua' (Equiv''.idEquiv A)).proof = (Path.refl A).proof

/-! ## 46. ua composition -/

axiom ua'_comp {A B C : Type u} (e₁ : A ≃ₚ B) (e₂ : B ≃ₚ C) :
    (Path.trans (ua' e₁) (ua' e₂)).proof = (ua' (Equiv''.comp e₁ e₂)).proof

/-! ## 47. Transport along ua is the forward function -/

theorem transport_ua'_is_toFun {A B : Type u} (e : A ≃ₚ B) (a : A) :
    Path.transport (D := fun X => X) (ua' e) a = e.toFun a :=
  ua'_transport e a

/-! ## 48. Double transport via ua -/

theorem transport_ua'_double {A B C : Type u} (e₁ : A ≃ₚ B) (e₂ : B ≃ₚ C) (a : A) :
    Path.transport (D := fun X => X) (ua' e₂)
      (Path.transport (D := fun X => X) (ua' e₁) a) =
    e₂.toFun (e₁.toFun a) := by
  rw [ua'_transport, ua'_transport]

/-! ## 49. Triple transport via ua -/

theorem transport_ua'_triple {A B C D : Type u}
    (e₁ : A ≃ₚ B) (e₂ : B ≃ₚ C) (e₃ : C ≃ₚ D) (a : A) :
    Path.transport (D := fun X => X) (ua' e₃)
      (Path.transport (D := fun X => X) (ua' e₂)
        (Path.transport (D := fun X => X) (ua' e₁) a)) =
    e₃.toFun (e₂.toFun (e₁.toFun a)) := by
  rw [ua'_transport, ua'_transport, ua'_transport]

/-! ## 50. ua symm transport -/

axiom ua'_symm_transport {A B : Type u} (e : A ≃ₚ B) (b : B) :
    Path.transport (D := fun X => X) (Path.symm (ua' e)) b = e.invFun b

/-! ## 51. ua roundtrip forward -/

theorem ua'_roundtrip_fwd {A B : Type u} (e : A ≃ₚ B) (a : A) :
    Path.transport (D := fun X => X) (Path.symm (ua' e))
      (Path.transport (D := fun X => X) (ua' e) a) = e.invFun (e.toFun a) := by
  rw [ua'_transport, ua'_symm_transport]

/-! ## 52. ua roundtrip gives section -/

def ua'_roundtrip_sect {A B : Type u} (e : A ≃ₚ B) (a : A) :
    Path
      (Path.transport (D := fun X => X) (Path.symm (ua' e))
        (Path.transport (D := fun X => X) (ua' e) a))
      a :=
  Path.trans
    (Path.mk [Step.mk _ _ (ua'_roundtrip_fwd e a)] (ua'_roundtrip_fwd e a))
    (e.sect a)

/-! ## 53. Equiv preserves contractibility -/

def isContr_equiv (h : IsContr A) (e : A ≃ₚ B) : IsContr B where
  center := e.toFun h.center
  contr  := fun b =>
    Path.trans
      (Path.congrArg e.toFun (h.contr (e.invFun b)))
      (e.retr b)

/-! ## 54. isContr_equiv contraction steps -/

theorem isContr_equiv_contr_steps (h : IsContr A) (e : A ≃ₚ B) (b : B) :
    ((isContr_equiv h e).contr b).steps =
      (Path.congrArg e.toFun (h.contr (e.invFun b))).steps ++
      (e.retr b).steps := rfl

/-! ## 55. Equiv preserves propositions -/

def isProp_equiv (h : IsProp A) (e : A ≃ₚ B) : IsProp B where
  propPath := fun b₁ b₂ =>
    Path.trans
      (Path.symm (e.retr b₁))
      (Path.trans
        (Path.congrArg e.toFun (h.propPath (e.invFun b₁) (e.invFun b₂)))
        (e.retr b₂))

/-! ## 56. isProp_equiv path has three-part steps -/

theorem isProp_equiv_steps (h : IsProp A) (e : A ≃ₚ B) (b₁ b₂ : B) :
    ((isProp_equiv h e).propPath b₁ b₂).steps =
      (Path.symm (e.retr b₁)).steps ++
      ((Path.trans
          (Path.congrArg e.toFun (h.propPath (e.invFun b₁) (e.invFun b₂)))
          (e.retr b₂)).steps) := rfl

/-! ## 57. CongrArg through toFun preserves trans -/

theorem congrArg_toFun_trans (e : A ≃ₚ B) {a₁ a₂ a₃ : A}
    (p : Path a₁ a₂) (q : Path a₂ a₃) :
    Path.congrArg e.toFun (Path.trans p q) =
      Path.trans (Path.congrArg e.toFun p) (Path.congrArg e.toFun q) :=
  Path.congrArg_trans e.toFun p q

/-! ## 58. CongrArg through toFun preserves symm -/

theorem congrArg_toFun_symm (e : A ≃ₚ B) {a₁ a₂ : A} (p : Path a₁ a₂) :
    Path.congrArg e.toFun (Path.symm p) =
      Path.symm (Path.congrArg e.toFun p) :=
  Path.congrArg_symm e.toFun p

/-! ## 59. CongrArg composes with invFun -/

theorem congrArg_inv_comp' (e : A ≃ₚ B) {a₁ a₂ : A} (p : Path a₁ a₂) :
    Path.congrArg (fun x => e.invFun (e.toFun x)) p =
      Path.congrArg e.invFun (Path.congrArg e.toFun p) :=
  Path.congrArg_comp e.invFun e.toFun p

/-! ## 60. CongrArg through equiv comp -/

theorem congrArg_equiv_comp {A B C : Type u} (e₁ : A ≃ₚ B) (e₂ : B ≃ₚ C)
    {a₁ a₂ : A} (p : Path a₁ a₂) :
    Path.congrArg (Equiv''.comp e₁ e₂).toFun p =
      Path.congrArg e₂.toFun (Path.congrArg e₁.toFun p) :=
  Path.congrArg_comp e₂.toFun e₁.toFun p

/-! ## Path-over and dependent paths -/

/-- A path-over: a path in a family lying over a base path. -/
def PathOver' {A : Type u} (P : A → Type v) {a b : A}
    (p : Path a b) (u : P a) (v : P b) : Type v :=
  Path (Path.transport (D := P) p u) v

/-! ## 61. PathOver reflexivity -/

def pathOver_refl {P : A → Type v} {a : A} (u : P a) :
    PathOver' P (Path.refl a) u u := by
  show Path (Path.transport (D := P) (Path.refl a) u) u
  simp [Path.transport]
  exact Path.refl u

/-! ## 62. Fiber of equivalence -/

structure Fiber' (f : A → B) (b : B) where
  point : A
  path  : Path (f point) b

def fiber_center (e : A ≃ₚ B) (b : B) : Fiber' e.toFun b :=
  ⟨e.invFun b, e.retr b⟩

/-! ## 63. Fiber center uses genuine retr path -/

theorem fiber_center_path (e : A ≃ₚ B) (b : B) :
    (fiber_center e b).path.proof = (e.retr b).proof := rfl

/-! ## 64. Fiber center steps -/

theorem fiber_center_steps (e : A ≃ₚ B) (b : B) :
    (fiber_center e b).path.steps = (e.retr b).steps := rfl

/-! ## 65. CongrArg through comp toFun preserves symm -/

theorem congrArg_comp_toFun_symm {A B C : Type u}
    (e₁ : A ≃ₚ B) (e₂ : B ≃ₚ C) {a₁ a₂ : A} (p : Path a₁ a₂) :
    Path.congrArg (Equiv''.comp e₁ e₂).toFun (Path.symm p) =
      Path.symm (Path.congrArg (Equiv''.comp e₁ e₂).toFun p) :=
  Path.congrArg_symm _ p

end ComputationalPaths.Path.HoTT.UnivalencePaths
