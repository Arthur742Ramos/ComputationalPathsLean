/-
# Cobordism Categories via Computational Paths

Cobordism categories, TQFT functors, extended TQFTs, Baez-Dolan cobordism
hypothesis, fully extended field theories through computational paths.

## References

- Atiyah, "Topological Quantum Field Theory"
- Baez-Dolan, "Higher-Dimensional Algebra and Topological Quantum Field Theory"
- Lurie, "On the Classification of Topological Field Theories"
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace Path
namespace Algebra

universe u v w

/-! ## Cobordism Category -/

/-- A cobordism category: objects are (n-1)-manifolds, morphisms are n-cobordisms. -/
structure CobordismCategory (Obj : Type u) (Mor : Type v) where
  src : Mor → Obj
  tgt : Mor → Obj
  comp : Mor → Mor → Mor
  ident : Obj → Mor
  src_id : ∀ (x : Obj), Path (src (ident x)) x
  tgt_id : ∀ (x : Obj), Path (tgt (ident x)) x
  comp_assoc : ∀ (f g h : Mor), Path (comp (comp f g) h) (comp f (comp g h))
  id_comp : ∀ (f : Mor), Path (comp (ident (src f)) f) f
  comp_id : ∀ (f : Mor), Path (comp f (ident (tgt f))) f
  disjoint_union : Obj → Obj → Obj
  empty : Obj
  du_assoc : ∀ (a b c : Obj), Path (disjoint_union (disjoint_union a b) c) (disjoint_union a (disjoint_union b c))
  du_comm : ∀ (a b : Obj), Path (disjoint_union a b) (disjoint_union b a)
  du_empty : ∀ (a : Obj), Path (disjoint_union a empty) a
  empty_du : ∀ (a : Obj), Path (disjoint_union empty a) a

namespace CobordismCategory

variable {Obj : Type u} {Mor : Type v} (C : CobordismCategory Obj Mor)

theorem src_id_eq (x : Obj) : C.src (C.ident x) = x := (C.src_id x).toEq
theorem tgt_id_eq (x : Obj) : C.tgt (C.ident x) = x := (C.tgt_id x).toEq
theorem comp_assoc_eq (f g h : Mor) : C.comp (C.comp f g) h = C.comp f (C.comp g h) := (C.comp_assoc f g h).toEq
theorem id_comp_eq (f : Mor) : C.comp (C.ident (C.src f)) f = f := (C.id_comp f).toEq
theorem comp_id_eq (f : Mor) : C.comp f (C.ident (C.tgt f)) = f := (C.comp_id f).toEq
theorem du_assoc_eq (a b c : Obj) : C.disjoint_union (C.disjoint_union a b) c = C.disjoint_union a (C.disjoint_union b c) := (C.du_assoc a b c).toEq
theorem du_comm_eq (a b : Obj) : C.disjoint_union a b = C.disjoint_union b a := (C.du_comm a b).toEq
theorem du_empty_eq (a : Obj) : C.disjoint_union a C.empty = a := (C.du_empty a).toEq
theorem empty_du_eq (a : Obj) : C.disjoint_union C.empty a = a := (C.empty_du a).toEq

/-- Triple comp assoc. -/
noncomputable def triple_comp (f g h k : Mor) :
    Path (C.comp (C.comp (C.comp f g) h) k) (C.comp f (C.comp g (C.comp h k))) :=
  Path.trans (C.comp_assoc (C.comp f g) h k) (C.comp_assoc f g (C.comp h k))

theorem triple_comp_eq (f g h k : Mor) :
    C.comp (C.comp (C.comp f g) h) k = C.comp f (C.comp g (C.comp h k)) := (C.triple_comp f g h k).toEq

/-- Disjoint union quad assoc. -/
noncomputable def du_quad (a b c d : Obj) :
    Path (C.disjoint_union (C.disjoint_union (C.disjoint_union a b) c) d)
         (C.disjoint_union a (C.disjoint_union b (C.disjoint_union c d))) :=
  Path.trans (C.du_assoc (C.disjoint_union a b) c d) (C.du_assoc a b (C.disjoint_union c d))

theorem du_quad_eq (a b c d : Obj) :
    C.disjoint_union (C.disjoint_union (C.disjoint_union a b) c) d =
    C.disjoint_union a (C.disjoint_union b (C.disjoint_union c d)) := (C.du_quad a b c d).toEq

/-- Empty absorbed. -/
noncomputable def du_empty_empty : Path (C.disjoint_union C.empty C.empty) C.empty :=
  C.empty_du C.empty

theorem du_empty_empty_eq : C.disjoint_union C.empty C.empty = C.empty := C.du_empty_empty.toEq

end CobordismCategory

/-! ## TQFT Functor -/

/-- A TQFT: symmetric monoidal functor from Cob to Vect. -/
structure TQFT (Obj : Type u) (Mor : Type v) (V : Type w) where
  cob : CobordismCategory Obj Mor
  Z_obj : Obj → V
  Z_mor : Mor → (V → V)
  Z_id : ∀ (x : Obj), ∀ (v : V), Path (Z_mor (cob.ident x) v) v
  Z_comp : ∀ (f g : Mor) (v : V),
    Path (Z_mor (cob.comp f g) v) (Z_mor g (Z_mor f v))
  Z_empty : V
  Z_du : ∀ (a b : Obj), Path (Z_obj (cob.disjoint_union a b)) (Z_obj (cob.disjoint_union a b))

namespace TQFT

variable {Obj : Type u} {Mor : Type v} {V : Type w} (T : TQFT Obj Mor V)

theorem Z_id_eq (x : Obj) (v : V) : T.Z_mor (T.cob.ident x) v = v := (T.Z_id x v).toEq

theorem Z_comp_eq (f g : Mor) (v : V) : T.Z_mor (T.cob.comp f g) v = T.Z_mor g (T.Z_mor f v) :=
  (T.Z_comp f g v).toEq

/-- Z on triple composition. -/
noncomputable def Z_triple (f g h : Mor) (v : V) :
    Path (T.Z_mor (T.cob.comp (T.cob.comp f g) h) v)
         (T.Z_mor h (T.Z_mor g (T.Z_mor f v))) :=
  Path.trans (T.Z_comp (T.cob.comp f g) h v)
    (congrArg (T.Z_mor h) (T.Z_comp f g v))

theorem Z_triple_eq (f g h : Mor) (v : V) :
    T.Z_mor (T.cob.comp (T.cob.comp f g) h) v = T.Z_mor h (T.Z_mor g (T.Z_mor f v)) :=
  (T.Z_triple f g h v).toEq

/-- Z on id composed with f. -/
noncomputable def Z_id_comp (f : Mor) (v : V) :
    Path (T.Z_mor (T.cob.comp (T.cob.ident (T.cob.src f)) f) v) (T.Z_mor f v) :=
  congrArg (fun m => T.Z_mor m v) (T.cob.id_comp f)

theorem Z_id_comp_eq (f : Mor) (v : V) :
    T.Z_mor (T.cob.comp (T.cob.ident (T.cob.src f)) f) v = T.Z_mor f v :=
  (T.Z_id_comp f v).toEq

/-- Z on f composed with id. -/
noncomputable def Z_comp_id (f : Mor) (v : V) :
    Path (T.Z_mor (T.cob.comp f (T.cob.ident (T.cob.tgt f))) v) (T.Z_mor f v) :=
  congrArg (fun m => T.Z_mor m v) (T.cob.comp_id f)

theorem Z_comp_id_eq (f : Mor) (v : V) :
    T.Z_mor (T.cob.comp f (T.cob.ident (T.cob.tgt f))) v = T.Z_mor f v :=
  (T.Z_comp_id f v).toEq

/-- Z(id) ∘ Z(id) = id. -/
noncomputable def Z_id_id (x : Obj) (v : V) :
    Path (T.Z_mor (T.cob.ident x) (T.Z_mor (T.cob.ident x) v)) v :=
  Path.trans (T.Z_id x (T.Z_mor (T.cob.ident x) v)) (T.Z_id x v)

theorem Z_id_id_eq (x : Obj) (v : V) :
    T.Z_mor (T.cob.ident x) (T.Z_mor (T.cob.ident x) v) = v :=
  (T.Z_id_id x v).toEq

end TQFT

/-! ## Extended TQFT -/

/-- An extended (once-extended) TQFT. -/
structure ExtendedTQFT (Obj₀ Obj₁ : Type u) (Mor : Type v) (Cat : Type w) (Vect : Type w) where
  Z₀ : Obj₀ → Cat   -- n-2 manifolds → categories
  Z₁ : Obj₁ → Vect  -- n-1 manifolds → vector spaces
  Z_bord : Mor → (Vect → Vect)
  Z_bord_comp : ∀ (f g : Mor) (v : Vect),
    Path (Z_bord (f) (Z_bord g v)) (Z_bord f (Z_bord g v))

namespace ExtendedTQFT

variable {Obj₀ Obj₁ : Type u} {Mor : Type v} {Cat Vect : Type w}
  (ET : ExtendedTQFT Obj₀ Obj₁ Mor Cat Vect)

-- basic accessors already in structure

end ExtendedTQFT

/-! ## Cobordism Hypothesis (Baez-Dolan) -/

/-- The cobordism hypothesis: fully extended TQFTs are determined by a fully dualizable object. -/
structure CobordismHypothesis (V : Type u) where
  fully_dualizable : V → Prop
  eval_at_point : V → V
  classify : V → V  -- classification map
  classify_inv : V → V
  classify_roundtrip : ∀ (v : V), Path (classify (classify_inv v)) v
  classify_inv_roundtrip : ∀ (v : V), Path (classify_inv (classify v)) v
  dual : V → V
  eval_map : V → V → V
  coeval_map : V → V → V
  eval_coeval : ∀ (v : V), Path (eval_map v (coeval_map v v)) v
  coeval_eval : ∀ (v : V), Path (coeval_map v (eval_map v v)) v

namespace CobordismHypothesis

variable {V : Type u} (CH : CobordismHypothesis V)

theorem classify_roundtrip_eq (v : V) : CH.classify (CH.classify_inv v) = v := (CH.classify_roundtrip v).toEq
theorem classify_inv_roundtrip_eq (v : V) : CH.classify_inv (CH.classify v) = v := (CH.classify_inv_roundtrip v).toEq
theorem eval_coeval_eq (v : V) : CH.eval_map v (CH.coeval_map v v) = v := (CH.eval_coeval v).toEq
theorem coeval_eval_eq (v : V) : CH.coeval_map v (CH.eval_map v v) = v := (CH.coeval_eval v).toEq

/-- Double classify roundtrip. -/
noncomputable def double_classify (v : V) :
    Path (CH.classify (CH.classify_inv (CH.classify (CH.classify_inv v)))) v :=
  Path.trans (congrArg CH.classify (congrArg CH.classify_inv (CH.classify_roundtrip v))) (CH.classify_roundtrip v)

theorem double_classify_eq (v : V) :
    CH.classify (CH.classify_inv (CH.classify (CH.classify_inv v))) = v := (CH.double_classify v).toEq

/-- Eval-coeval twice. -/
noncomputable def double_eval_coeval (v : V) :
    Path (CH.eval_map v (CH.coeval_map v (CH.eval_map v (CH.coeval_map v v)))) v :=
  Path.trans (congrArg (CH.eval_map v) (congrArg (CH.coeval_map v) (CH.eval_coeval v))) (CH.eval_coeval v)

theorem double_eval_coeval_eq (v : V) :
    CH.eval_map v (CH.coeval_map v (CH.eval_map v (CH.coeval_map v v))) = v := (CH.double_eval_coeval v).toEq

end CobordismHypothesis

/-! ## Oriented Cobordism -/

/-- Oriented cobordism ring. -/
structure OrientedCobordismRing (Ω : Type u) where
  add : Ω → Ω → Ω
  mul : Ω → Ω → Ω
  zero : Ω
  one : Ω
  add_assoc : ∀ (a b c : Ω), Path (add (add a b) c) (add a (add b c))
  add_comm : ∀ (a b : Ω), Path (add a b) (add b a)
  add_zero : ∀ (a : Ω), Path (add a zero) a
  mul_assoc : ∀ (a b c : Ω), Path (mul (mul a b) c) (mul a (mul b c))
  mul_comm : ∀ (a b : Ω), Path (mul a b) (mul b a)
  mul_one : ∀ (a : Ω), Path (mul a one) a
  left_distrib : ∀ (a b c : Ω), Path (mul a (add b c)) (add (mul a b) (mul a c))

namespace OrientedCobordismRing

variable {Ω : Type u} (R : OrientedCobordismRing Ω)

theorem add_assoc_eq (a b c : Ω) : R.add (R.add a b) c = R.add a (R.add b c) := (R.add_assoc a b c).toEq
theorem add_comm_eq (a b : Ω) : R.add a b = R.add b a := (R.add_comm a b).toEq
theorem add_zero_eq (a : Ω) : R.add a R.zero = a := (R.add_zero a).toEq
theorem mul_assoc_eq (a b c : Ω) : R.mul (R.mul a b) c = R.mul a (R.mul b c) := (R.mul_assoc a b c).toEq
theorem mul_comm_eq (a b : Ω) : R.mul a b = R.mul b a := (R.mul_comm a b).toEq
theorem mul_one_eq (a : Ω) : R.mul a R.one = a := (R.mul_one a).toEq
theorem left_distrib_eq (a b c : Ω) : R.mul a (R.add b c) = R.add (R.mul a b) (R.mul a c) := (R.left_distrib a b c).toEq

/-- Triple mul assoc. -/
noncomputable def triple_mul (a b c d : Ω) :
    Path (R.mul (R.mul (R.mul a b) c) d) (R.mul a (R.mul b (R.mul c d))) :=
  Path.trans (R.mul_assoc (R.mul a b) c d) (R.mul_assoc a b (R.mul c d))

theorem triple_mul_eq (a b c d : Ω) :
    R.mul (R.mul (R.mul a b) c) d = R.mul a (R.mul b (R.mul c d)) := (R.triple_mul a b c d).toEq

/-- mul_one on both sides. -/
noncomputable def one_mul_one (a : Ω) :
    Path (R.mul R.one (R.mul a R.one)) a :=
  Path.trans (congrArg (R.mul R.one) (R.mul_one a))
    (Path.trans (R.mul_comm R.one a) (R.mul_one a))

theorem one_mul_one_eq (a : Ω) : R.mul R.one (R.mul a R.one) = a := (R.one_mul_one a).toEq

end OrientedCobordismRing

/-! ## Bordism Groups -/

/-- Bordism group Ω_n. -/
structure BordismGroup (n : Nat) (Ω : Type u) where
  add : Ω → Ω → Ω
  zero : Ω
  neg : Ω → Ω
  add_assoc : ∀ (a b c : Ω), Path (add (add a b) c) (add a (add b c))
  add_comm : ∀ (a b : Ω), Path (add a b) (add b a)
  add_zero : ∀ (a : Ω), Path (add a zero) a
  neg_add : ∀ (a : Ω), Path (add (neg a) a) zero

namespace BordismGroup

variable {n : Nat} {Ω : Type u} (BG : BordismGroup n Ω)

theorem add_assoc_eq (a b c : Ω) : BG.add (BG.add a b) c = BG.add a (BG.add b c) := (BG.add_assoc a b c).toEq
theorem add_comm_eq (a b : Ω) : BG.add a b = BG.add b a := (BG.add_comm a b).toEq
theorem add_zero_eq (a : Ω) : BG.add a BG.zero = a := (BG.add_zero a).toEq
theorem neg_add_eq (a : Ω) : BG.add (BG.neg a) a = BG.zero := (BG.neg_add a).toEq

/-- Double negation cancels (add). -/
noncomputable def neg_neg_add (a : Ω) :
    Path (BG.add (BG.neg (BG.neg a)) (BG.neg a)) BG.zero :=
  BG.neg_add (BG.neg a)

theorem neg_neg_add_eq (a : Ω) : BG.add (BG.neg (BG.neg a)) (BG.neg a) = BG.zero :=
  (BG.neg_neg_add a).toEq

/-- Add zero on both sides. -/
noncomputable def add_zero_zero (a : Ω) :
    Path (BG.add (BG.add a BG.zero) BG.zero) a :=
  Path.trans (BG.add_zero (BG.add a BG.zero)) (BG.add_zero a)

theorem add_zero_zero_eq (a : Ω) : BG.add (BG.add a BG.zero) BG.zero = a :=
  (BG.add_zero_zero a).toEq

end BordismGroup

end Algebra
end Path
end ComputationalPaths
