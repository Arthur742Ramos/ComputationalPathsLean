/-
# Deep path groupoid: objects as types, morphisms as Paths

Morphisms are Paths, 2-morphisms are paths-between-paths,
functoriality of path operations, natural transformations between
path functors, Yoneda for path groupoids. All derived from trans/symm/congrArg/Step.
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace Path
namespace PathGroupoidDeep

universe u v w

variable {A : Type u} {B : Type v} {C : Type w}

/-! ## Path groupoid: objects and morphisms -/

/-- A path functor: a function on objects plus the induced map on paths. -/
structure PathFunctor (A : Type u) (B : Type v) where
  obj : A → B
  map : {a b : A} → Path a b → Path (obj a) (obj b)
  map_refl : ∀ (a : A), map (Path.refl a) = Path.refl (obj a)
  map_trans : ∀ {a b c : A} (p : Path a b) (q : Path b c),
    map (Path.trans p q) = Path.trans (map p) (map q)

/-- 1. The identity path functor. -/
def PathFunctor.id : PathFunctor A A where
  obj := fun a => a
  map := fun p => p
  map_refl := fun _ => rfl
  map_trans := fun _ _ => rfl

/-- 2. Composition of path functors. -/
def PathFunctor.comp (F : PathFunctor A B) (G : PathFunctor B C) :
    PathFunctor A C where
  obj := fun a => G.obj (F.obj a)
  map := fun p => G.map (F.map p)
  map_refl := fun a => by
    calc G.map (F.map (Path.refl a))
        = G.map (Path.refl (F.obj a)) := _root_.congrArg G.map (F.map_refl a)
      _ = Path.refl (G.obj (F.obj a)) := G.map_refl (F.obj a)
  map_trans := fun p q => by
    calc G.map (F.map (Path.trans p q))
        = G.map (Path.trans (F.map p) (F.map q)) :=
          _root_.congrArg G.map (F.map_trans p q)
      _ = Path.trans (G.map (F.map p)) (G.map (F.map q)) :=
          G.map_trans (F.map p) (F.map q)

/-- 3. congrArg induces a path functor. -/
def congrArgFunctor (f : A → B) : PathFunctor A B where
  obj := f
  map := fun p => Path.congrArg f p
  map_refl := fun a => by simp
  map_trans := fun p q => Path.congrArg_trans f p q

/-- 4. A path functor preserves symm at the toEq level. -/
theorem PathFunctor.map_symm_toEq (F : PathFunctor A B)
    {a b : A} (p : Path a b) :
    (F.map (Path.symm p)).toEq = (Path.symm (F.map p)).toEq := by
  simp

/-- 5. Path functor identity: comp F id = F at obj level. -/
theorem PathFunctor.comp_id_obj (F : PathFunctor A B) (a : A) :
    (PathFunctor.comp F PathFunctor.id).obj a = F.obj a := rfl

/-- 6. Path functor identity: comp id F = F at obj level. -/
theorem PathFunctor.id_comp_obj (F : PathFunctor A B) (a : A) :
    (PathFunctor.comp PathFunctor.id F).obj a = F.obj a := rfl

/-! ## Natural transformations between path functors -/

/-- A natural transformation between path functors:
    for each object a, a path component a : Path (F.obj a) (G.obj a),
    satisfying naturality. -/
structure PathNatTrans (F G : PathFunctor A B) where
  component : (a : A) → Path (F.obj a) (G.obj a)
  naturality : ∀ {a b : A} (p : Path a b),
    Path.trans (F.map p) (component b) = Path.trans (component a) (G.map p)

/-- 7. Identity natural transformation. -/
def PathNatTrans.id (F : PathFunctor A B) : PathNatTrans F F where
  component := fun a => Path.refl (F.obj a)
  naturality := fun p => by simp

/-- 8. Vertical composition of natural transformations. -/
def PathNatTrans.vcomp {F G H : PathFunctor A B}
    (η : PathNatTrans F G) (θ : PathNatTrans G H) : PathNatTrans F H where
  component := fun a => Path.trans (η.component a) (θ.component a)
  naturality := fun {a b} p => by
    calc Path.trans (F.map p) (Path.trans (η.component b) (θ.component b))
        = Path.trans (Path.trans (F.map p) (η.component b)) (θ.component b) :=
          (Path.trans_assoc (F.map p) (η.component b) (θ.component b)).symm
      _ = Path.trans (Path.trans (η.component a) (G.map p)) (θ.component b) :=
          _root_.congrArg (fun t => Path.trans t (θ.component b)) (η.naturality p)
      _ = Path.trans (η.component a) (Path.trans (G.map p) (θ.component b)) :=
          Path.trans_assoc (η.component a) (G.map p) (θ.component b)
      _ = Path.trans (η.component a) (Path.trans (θ.component a) (H.map p)) :=
          _root_.congrArg (fun t => Path.trans (η.component a) t) (θ.naturality p)
      _ = Path.trans (Path.trans (η.component a) (θ.component a)) (H.map p) :=
          (Path.trans_assoc (η.component a) (θ.component a) (H.map p)).symm

/-- 9. Left identity for natural transformation composition. -/
theorem PathNatTrans.vcomp_id_left {F G : PathFunctor A B}
    (η : PathNatTrans F G) :
    (PathNatTrans.vcomp (PathNatTrans.id F) η).component =
      η.component := by
  funext a; simp [PathNatTrans.vcomp, PathNatTrans.id]

/-- 10. Right identity for natural transformation composition. -/
theorem PathNatTrans.vcomp_id_right {F G : PathFunctor A B}
    (η : PathNatTrans F G) :
    (PathNatTrans.vcomp η (PathNatTrans.id G)).component =
      η.component := by
  funext a; simp [PathNatTrans.vcomp, PathNatTrans.id]

/-- 11. Associativity of natural transformation composition. -/
theorem PathNatTrans.vcomp_assoc {F G H K : PathFunctor A B}
    (η : PathNatTrans F G) (θ : PathNatTrans G H) (ι : PathNatTrans H K) :
    (PathNatTrans.vcomp (PathNatTrans.vcomp η θ) ι).component =
      (PathNatTrans.vcomp η (PathNatTrans.vcomp θ ι)).component := by
  funext a
  exact Path.trans_assoc (η.component a) (θ.component a) (ι.component a)

/-! ## Yoneda-like constructions for path groupoids -/

/-- 12. Precomposition with a path: given p : Path a b, produces
    Path b c → Path a c by trans. -/
def precomp {a b : A} (p : Path a b) {c : A} (q : Path b c) : Path a c :=
  Path.trans p q

/-- 13. Postcomposition with a path: given q : Path b c, produces
    Path a b → Path a c by trans. -/
def postcomp {b c : A} (q : Path b c) {a : A} (p : Path a b) : Path a c :=
  Path.trans p q

/-- 14. Precomposition is functorial: preserves trans. -/
theorem precomp_trans {a b c d : A} (p : Path a b)
    (q : Path b c) (r : Path c d) :
    precomp p (Path.trans q r) = Path.trans (precomp p q) r :=
  (Path.trans_assoc p q r).symm

/-- 15. Postcomposition is functorial: preserves trans. -/
theorem postcomp_trans {a b c d : A}
    (q : Path c d) (p₁ : Path a b) (p₂ : Path b c) :
    postcomp q (Path.trans p₁ p₂) = Path.trans p₁ (postcomp q p₂) :=
  Path.trans_assoc p₁ p₂ q

/-- 16. Precomposition with refl is identity. -/
theorem precomp_refl {a b : A} (q : Path a b) :
    precomp (Path.refl a) q = q :=
  Path.trans_refl_left q

/-- 17. Postcomposition with refl is identity. -/
theorem postcomp_refl {a b : A} (p : Path a b) :
    postcomp (Path.refl b) p = p :=
  Path.trans_refl_right p

/-- 18. Yoneda lemma (path version): evaluation at refl recovers the path. -/
theorem yoneda_eval {a b : A} (p : Path b a) :
    precomp p (Path.refl a) = p :=
  Path.trans_refl_right p

/-- 19. Yoneda naturality: precomp p commutes with postcomp. -/
theorem yoneda_naturality {a b c d : A}
    (p : Path b a) (q : Path a c) (r : Path c d) :
    postcomp r (precomp p q) = precomp p (postcomp r q) :=
  Path.trans_assoc p q r

/-! ## Functoriality of specific path operations -/

/-- 20. Path.symm is contravariant:
    symm (trans p q) = trans (symm q) (symm p). -/
theorem symm_contravariant {a b c : A}
    (p : Path a b) (q : Path b c) :
    Path.symm (Path.trans p q) = Path.trans (Path.symm q) (Path.symm p) :=
  Path.symm_trans p q

/-- 21. Path.symm preserves refl. -/
theorem symm_preserves_refl (a : A) :
    Path.symm (Path.refl a) = Path.refl a :=
  Path.symm_refl a

/-- 22. congrArg is a strict functor: preserves refl. -/
theorem congrArg_preserves_refl (f : A → B) (a : A) :
    Path.congrArg f (Path.refl a) = Path.refl (f a) := by simp

/-- 23. congrArg is a strict functor: preserves trans. -/
theorem congrArg_preserves_trans (f : A → B)
    {a b c : A} (p : Path a b) (q : Path b c) :
    Path.congrArg f (Path.trans p q) =
      Path.trans (Path.congrArg f p) (Path.congrArg f q) :=
  Path.congrArg_trans f p q

/-- 24. congrArg is a strict functor: preserves symm. -/
theorem congrArg_preserves_symm (f : A → B)
    {a b : A} (p : Path a b) :
    Path.congrArg f (Path.symm p) = Path.symm (Path.congrArg f p) :=
  Path.congrArg_symm f p

/-- 25. congrArg composition: (f ∘ g) preserves paths. -/
theorem congrArg_comp_preserves {C : Type w}
    (f : B → C) (g : A → B) {a b : A} (p : Path a b) :
    Path.congrArg (fun x => f (g x)) p =
      Path.congrArg f (Path.congrArg g p) :=
  Path.congrArg_comp f g p

/-! ## 2-morphisms as paths-between-paths -/

/-- 26. Two 2-morphisms (equalities between paths) compose vertically. -/
theorem two_mor_vcomp {a b : A} {p q r : Path a b}
    (α : p = q) (β : q = r) :
    Eq.trans α β = (α ▸ β : p = r) := by
  cases α; rfl

/-- 27. Whiskering a 2-morphism on the right is congrArg. -/
theorem whisker_right_eq {a b c : A} (p : Path a b)
    {q r : Path b c} (α : q = r) :
    _root_.congrArg (fun t => Path.trans p t) α =
      Path.whiskerRight p α := rfl

/-- 28. Whiskering a 2-morphism on the left is congrArg. -/
theorem whisker_left_eq {a b c : A}
    {p q : Path a b} (α : p = q) (r : Path b c) :
    _root_.congrArg (fun t => Path.trans t r) α =
      Path.whiskerLeft α r := rfl

/-! ## Groupoid inverse coherence -/

/-- 29. Right cancellation: trans p (symm p) has trivial toEq. -/
theorem right_cancel_toEq {a b : A} (p : Path a b) :
    (Path.trans p (Path.symm p)).toEq = rfl := by simp

/-- 30. Left cancellation: trans (symm p) p has trivial toEq. -/
theorem left_cancel_toEq {a b : A} (p : Path a b) :
    (Path.trans (Path.symm p) p).toEq = rfl := by simp

/-- 31. Triple cancellation chain. -/
theorem triple_cancel_toEq {a b c : A}
    (p : Path a b) (q : Path b c) :
    (Path.trans (Path.symm q) (Path.trans (Path.symm p) (Path.trans p q))).toEq = rfl := by
  simp

/-- 32. congrArg functor preserves cancellation. -/
theorem congrArg_cancel_toEq {a b : A} (f : A → B) (p : Path a b) :
    (Path.trans (Path.congrArg f p) (Path.congrArg f (Path.symm p))).toEq = rfl := by
  simp

/-! ## Path algebra identities -/

/-- 33. Mac Lane coherence for all reassociations of 4-fold composition. -/
theorem four_assoc_coherence {a b c d e : A}
    (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e)
    (h₁ h₂ : Path.trans (Path.trans (Path.trans p q) r) s =
      Path.trans p (Path.trans q (Path.trans r s))) :
    h₁ = h₂ :=
  Subsingleton.elim h₁ h₂

/-- 34. Transport along ofEq path computes correctly. -/
theorem transport_ofEq_compute {D : A → Sort v}
    {a b : A} (h : a = b) (x : D a) :
    Path.transport (D := D) (Path.ofEq h) x = Eq.mp (_root_.congrArg D h) x :=
  Path.transport_ofEq h x

/-- 35. Five-fold associativity via iterated trans_assoc. -/
theorem five_assoc {a b c d e f : A}
    (p : Path a b) (q : Path b c) (r : Path c d)
    (s : Path d e) (t : Path e f) :
    Path.trans (Path.trans (Path.trans (Path.trans p q) r) s) t =
      Path.trans p (Path.trans q (Path.trans r (Path.trans s t))) := by
  calc Path.trans (Path.trans (Path.trans (Path.trans p q) r) s) t
      = Path.trans (Path.trans (Path.trans p q) r) (Path.trans s t) :=
        Path.trans_assoc _ s t
    _ = Path.trans (Path.trans p q) (Path.trans r (Path.trans s t)) :=
        Path.trans_assoc _ r _
    _ = Path.trans p (Path.trans q (Path.trans r (Path.trans s t))) :=
        Path.trans_assoc p q _

/-- 36. congrArg of five-fold composition splits at the end. -/
theorem congrArg_five_trans {a b c d e f : A}
    (g : A → B)
    (p : Path a b) (q : Path b c) (r : Path c d)
    (s : Path d e) (t : Path e f) :
    Path.congrArg g (Path.trans (Path.trans (Path.trans (Path.trans p q) r) s) t) =
      Path.trans (Path.congrArg g (Path.trans (Path.trans (Path.trans p q) r) s))
                 (Path.congrArg g t) :=
  Path.congrArg_trans g _ t

/-- 37. Step metadata: a single-step path has exactly one step. -/
theorem ofEq_steps_length {a b : A} (h : a = b) :
    (Path.ofEq h).steps.length = 1 := by simp [Path.ofEq]

/-- 38. Step metadata: refl path has zero steps. -/
theorem refl_steps_empty (a : A) :
    (Path.refl a).steps = [] := rfl

/-- 39. Step metadata: trans concatenates step lists. -/
theorem trans_steps_append {a b c : A}
    (p : Path a b) (q : Path b c) :
    (Path.trans p q).steps = p.steps ++ q.steps := rfl

/-- 40. Step metadata: symm reverses and inverts steps. -/
theorem symm_steps_reverse {a b : A} (p : Path a b) :
    (Path.symm p).steps = p.steps.reverse.map Step.symm := rfl

/-- 41. congrArg maps steps through Step.map. -/
theorem congrArg_steps_map (f : A → B) {a b : A} (p : Path a b) :
    (Path.congrArg f p).steps = p.steps.map (Step.map f) := rfl

/-! ## Inverse natural transformation -/

/-- 42. Inverse natural transformation component is symm. -/
theorem PathNatTrans.inv_component_toEq {F G : PathFunctor A B}
    (η : PathNatTrans F G) (a : A) :
    (Path.symm (η.component a)).toEq = (η.component a).toEq.symm := by simp

/-- 43. Composing with inverse component yields trivial toEq. -/
theorem PathNatTrans.right_inv_toEq {F G : PathFunctor A B}
    (η : PathNatTrans F G) (a : A) :
    (Path.trans (η.component a) (Path.symm (η.component a))).toEq = rfl := by simp

/-- 44. Composing inverse then original yields trivial toEq. -/
theorem PathNatTrans.left_inv_toEq {F G : PathFunctor A B}
    (η : PathNatTrans F G) (a : A) :
    (Path.trans (Path.symm (η.component a)) (η.component a)).toEq = rfl := by simp

/-! ## Additional deep path groupoid theorems -/

/-- 45. Path between congrArg f p and congrArg f q when p = q. -/
theorem congrArg_path_eq (f : A → B) {a b : A} {p q : Path a b}
    (h : p = q) : Path.congrArg f p = Path.congrArg f q :=
  _root_.congrArg (Path.congrArg f) h

/-- 46. Transport is natural w.r.t. path composition. -/
theorem transport_natural {D : A → Sort v}
    {a b c : A} (p : Path a b) (q : Path b c) (x : D a) :
    Path.transport (D := D) (Path.trans p q) x =
      Path.transport q (Path.transport p x) :=
  Path.transport_trans p q x

/-- 47. Constant transport is trivial. -/
theorem transport_const_path {D : Type v} {a b : A}
    (p : Path a b) (x : D) :
    Path.transport (D := fun _ => D) p x = x :=
  Path.transport_const p x

/-- 48. Precomp distributes over symm. -/
theorem precomp_symm {a b c : A} (p : Path a b) (q : Path b c) :
    Path.symm (precomp p q) = Path.trans (Path.symm q) (Path.symm p) :=
  Path.symm_trans p q

/-- 49. Double symm for a trans chain. -/
theorem double_symm_trans {a b c : A} (p : Path a b) (q : Path b c) :
    Path.symm (Path.symm (Path.trans p q)) = Path.trans p q :=
  Path.symm_symm (Path.trans p q)

/-- 50. Transport along the identity path functor is identity. -/
theorem id_functor_map_eq {a b : A} (p : Path a b) :
    (PathFunctor.id (A := A)).map p = p := rfl

end PathGroupoidDeep
end Path
end ComputationalPaths
