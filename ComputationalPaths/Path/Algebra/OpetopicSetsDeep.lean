/- 
  ComputationalPaths/Path/Algebra/OpetopicSetsDeep.lean

  Opetopic sets via computational paths:
  opetopes as higher-dimensional pasting diagrams, zoom complexes, opetopic types,
  composition via universal cells, identities, opetopic categories, Baez-Dolan
  hypothesis structure, multitopes, and coherence laws for opetopic composition.
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths.OpetopicSetsDeep

open Path

universe u v w

/-! ## Elementary path witnesses -/

def edgePath {A : Type u} {a b : A} (h : a = b) : Path a b :=
  Path.mk [Step.mk a b h] h

def reflPathViaMk {A : Type u} (a : A) : Path a a :=
  Path.mk [] rfl

@[simp] theorem edgePath_toEq {A : Type u} {a b : A} (h : a = b) :
    toEq (edgePath h) = h := rfl

@[simp] theorem edgePath_refl {A : Type u} (a : A) :
    edgePath (rfl : a = a) = Path.mk [Step.mk a a rfl] rfl := rfl

@[simp] theorem edgePath_symm_toEq {A : Type u} {a b : A} (h : a = b) :
    toEq (symm (edgePath h)) = h.symm := rfl

@[simp] theorem edgePath_trans_toEq {A : Type u} {a b c : A}
    (h₁ : a = b) (h₂ : b = c) :
    toEq (trans (edgePath h₁) (edgePath h₂)) = Eq.trans h₁ h₂ := rfl

theorem edgePath_symm_symm {A : Type u} {a b : A} (h : a = b) :
    symm (symm (edgePath h)) = edgePath h := by
  simpa using symm_symm (edgePath h)

theorem edgePath_trans_refl_left {A : Type u} {a b : A} (p : Path a b) :
    trans (refl a) p = p :=
  trans_refl_left p

theorem edgePath_trans_refl_right {A : Type u} {a b : A} (p : Path a b) :
    trans p (refl b) = p :=
  trans_refl_right p

theorem edgePath_trans_assoc {A : Type u} {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    trans (trans p q) r = trans p (trans q r) :=
  trans_assoc p q r

theorem edgePath_symm_trans {A : Type u} {a b c : A}
    (p : Path a b) (q : Path b c) :
    symm (trans p q) = trans (symm q) (symm p) :=
  symm_trans p q

theorem edgePath_congrArg_trans {A : Type u} {B : Type v}
    (f : A → B) {a b c : A} (p : Path a b) (q : Path b c) :
    congrArg f (trans p q) = trans (congrArg f p) (congrArg f q) :=
  congrArg_trans f p q

theorem edgePath_congrArg_symm {A : Type u} {B : Type v}
    (f : A → B) {a b : A} (p : Path a b) :
    congrArg f (symm p) = symm (congrArg f p) :=
  congrArg_symm f p

@[simp] theorem reflPathViaMk_eq_refl {A : Type u} (a : A) :
    reflPathViaMk a = refl a := rfl

@[simp] theorem reflPathViaMk_toEq {A : Type u} (a : A) :
    toEq (reflPathViaMk a) = rfl := rfl

/-! ## Opetopic types and composition -/

structure OpetopicType (A : Type u) where
  Gam : A → A → A
  Id : A
  assoc : (x y z : A) → Path (Gam (Gam x y) z) (Gam x (Gam y z))
  id_left : (x : A) → Path (Gam Id x) x
  id_right : (x : A) → Path (Gam x Id) x

def assocSym {A : Type u} (O : OpetopicType A) (x y z : A) :
    Path (O.Gam x (O.Gam y z)) (O.Gam (O.Gam x y) z) :=
  symm (O.assoc x y z)

def assocChain {A : Type u} (O : OpetopicType A) (x y z w : A) :
    Path (O.Gam (O.Gam (O.Gam x y) z) w) (O.Gam x (O.Gam y (O.Gam z w))) :=
  trans (O.assoc (O.Gam x y) z w) (O.assoc x y (O.Gam z w))

def coherenceRouteLeft {A : Type u} (O : OpetopicType A) (x y z w : A) :
    Path (O.Gam (O.Gam (O.Gam x y) z) w) (O.Gam x (O.Gam y (O.Gam z w))) :=
  trans (trans (O.assoc (O.Gam x y) z w) (O.assoc x y (O.Gam z w)))
    (refl (O.Gam x (O.Gam y (O.Gam z w))))

def coherenceRouteRight {A : Type u} (O : OpetopicType A) (x y z w : A) :
    Path (O.Gam (O.Gam (O.Gam x y) z) w) (O.Gam x (O.Gam y (O.Gam z w))) :=
  trans (O.assoc (O.Gam x y) z w)
    (trans (O.assoc x y (O.Gam z w)) (refl (O.Gam x (O.Gam y (O.Gam z w)))))

theorem assoc_symm_symm {A : Type u} (O : OpetopicType A) (x y z : A) :
    symm (symm (O.assoc x y z)) = O.assoc x y z :=
  symm_symm (O.assoc x y z)

theorem assoc_trans_refl {A : Type u} (O : OpetopicType A) (x y z : A) :
    trans (O.assoc x y z) (refl (O.Gam x (O.Gam y z))) = O.assoc x y z :=
  trans_refl_right (O.assoc x y z)

theorem assoc_refl_trans {A : Type u} (O : OpetopicType A) (x y z : A) :
    trans (refl (O.Gam (O.Gam x y) z)) (O.assoc x y z) = O.assoc x y z :=
  trans_refl_left (O.assoc x y z)

theorem assoc_symm_trans {A : Type u} (O : OpetopicType A) (x y z : A) :
    symm (trans (O.assoc x y z) (refl (O.Gam x (O.Gam y z)))) =
      trans (symm (refl (O.Gam x (O.Gam y z)))) (symm (O.assoc x y z)) := by
  simpa using symm_trans (O.assoc x y z) (refl (O.Gam x (O.Gam y z)))

theorem assoc_chain_reassoc {A : Type u} (O : OpetopicType A) (x y z w : A) :
    trans (trans (O.assoc (O.Gam x y) z w) (O.assoc x y (O.Gam z w)))
      (refl (O.Gam x (O.Gam y (O.Gam z w)))) =
    trans (O.assoc (O.Gam x y) z w)
      (trans (O.assoc x y (O.Gam z w)) (refl (O.Gam x (O.Gam y (O.Gam z w))))) :=
  trans_assoc (O.assoc (O.Gam x y) z w) (O.assoc x y (O.Gam z w))
    (refl (O.Gam x (O.Gam y (O.Gam z w))))

theorem assoc_chain_trans_refl {A : Type u} (O : OpetopicType A) (x y z w : A) :
    trans (assocChain O x y z w) (refl (O.Gam x (O.Gam y (O.Gam z w)))) =
      assocChain O x y z w :=
  trans_refl_right (assocChain O x y z w)

theorem assoc_chain_refl_trans {A : Type u} (O : OpetopicType A) (x y z w : A) :
    trans (refl (O.Gam (O.Gam (O.Gam x y) z) w)) (assocChain O x y z w) =
      assocChain O x y z w :=
  trans_refl_left (assocChain O x y z w)

theorem assoc_chain_symm_symm {A : Type u} (O : OpetopicType A) (x y z w : A) :
    symm (symm (assocChain O x y z w)) = assocChain O x y z w :=
  symm_symm (assocChain O x y z w)

theorem id_left_symm_symm {A : Type u} (O : OpetopicType A) (x : A) :
    symm (symm (O.id_left x)) = O.id_left x :=
  symm_symm (O.id_left x)

theorem id_right_symm_symm {A : Type u} (O : OpetopicType A) (x : A) :
    symm (symm (O.id_right x)) = O.id_right x :=
  symm_symm (O.id_right x)

theorem id_left_trans_refl {A : Type u} (O : OpetopicType A) (x : A) :
    trans (O.id_left x) (refl x) = O.id_left x :=
  trans_refl_right (O.id_left x)

theorem id_right_trans_refl {A : Type u} (O : OpetopicType A) (x : A) :
    trans (O.id_right x) (refl x) = O.id_right x :=
  trans_refl_right (O.id_right x)

theorem id_left_refl_trans {A : Type u} (O : OpetopicType A) (x : A) :
    trans (refl (O.Gam O.Id x)) (O.id_left x) = O.id_left x :=
  trans_refl_left (O.id_left x)

theorem id_right_refl_trans {A : Type u} (O : OpetopicType A) (x : A) :
    trans (refl (O.Gam x O.Id)) (O.id_right x) = O.id_right x :=
  trans_refl_left (O.id_right x)

def whisker_assoc {A : Type u} (O : OpetopicType A) (f : A → A) (x y z : A) :
    Path (f (O.Gam (O.Gam x y) z)) (f (O.Gam x (O.Gam y z))) :=
  congrArg f (O.assoc x y z)

theorem whisker_assoc_trans {A : Type u} (O : OpetopicType A) (f : A → A) (x y z : A) :
    congrArg f (trans (O.assoc x y z) (refl (O.Gam x (O.Gam y z)))) =
      trans (congrArg f (O.assoc x y z)) (congrArg f (refl (O.Gam x (O.Gam y z)))) := by
  simpa using congrArg_trans f (O.assoc x y z) (refl (O.Gam x (O.Gam y z)))

theorem whisker_assoc_symm {A : Type u} (O : OpetopicType A) (f : A → A) (x y z : A) :
    congrArg f (symm (O.assoc x y z)) = symm (congrArg f (O.assoc x y z)) :=
  congrArg_symm f (O.assoc x y z)

theorem id_left_whisker_symm {A : Type u} (O : OpetopicType A) (f : A → A) (x : A) :
    congrArg f (symm (O.id_left x)) = symm (congrArg f (O.id_left x)) :=
  congrArg_symm f (O.id_left x)

theorem id_right_whisker_trans {A : Type u} (O : OpetopicType A) (f : A → A) (x : A) :
    congrArg f (trans (O.id_right x) (refl x)) =
      trans (congrArg f (O.id_right x)) (congrArg f (refl x)) := by
  simpa using congrArg_trans f (O.id_right x) (refl x)

theorem coherence_routes_agree {A : Type u} (O : OpetopicType A) (x y z w : A) :
    coherenceRouteLeft O x y z w = coherenceRouteRight O x y z w :=
  assoc_chain_reassoc O x y z w

/-! ## Zoom complexes -/

structure ZoomComplex (A : Type u) where
  zoom : Nat → A → A
  contract : (n : Nat) → (x : A) → Path (zoom (n + 1) x) (zoom n x)

def zoom_congr {A : Type u} (Z : ZoomComplex A) (n : Nat) {x y : A}
    (p : Path x y) : Path (Z.zoom n x) (Z.zoom n y) :=
  congrArg (fun t => Z.zoom n t) p

def contractTwo {A : Type u} (Z : ZoomComplex A) (n : Nat) (x : A) :
    Path (Z.zoom (n + 2) x) (Z.zoom n x) :=
  trans (Z.contract (n + 1) x) (Z.contract n x)

def contractThree {A : Type u} (Z : ZoomComplex A) (n : Nat) (x : A) :
    Path (Z.zoom (n + 3) x) (Z.zoom n x) :=
  trans (Z.contract (n + 2) x) (contractTwo Z n x)

theorem zoom_congr_trans {A : Type u} (Z : ZoomComplex A) (n : Nat)
    {x y z : A} (p : Path x y) (q : Path y z) :
    zoom_congr Z n (trans p q) = trans (zoom_congr Z n p) (zoom_congr Z n q) := by
  simpa [zoom_congr] using congrArg_trans (fun t => Z.zoom n t) p q

theorem zoom_congr_symm {A : Type u} (Z : ZoomComplex A) (n : Nat)
    {x y : A} (p : Path x y) :
    zoom_congr Z n (symm p) = symm (zoom_congr Z n p) := by
  simpa [zoom_congr] using congrArg_symm (fun t => Z.zoom n t) p

theorem contract_symm_symm {A : Type u} (Z : ZoomComplex A) (n : Nat) (x : A) :
    symm (symm (Z.contract n x)) = Z.contract n x :=
  symm_symm (Z.contract n x)

theorem contract_trans_refl {A : Type u} (Z : ZoomComplex A) (n : Nat) (x : A) :
    trans (Z.contract n x) (refl (Z.zoom n x)) = Z.contract n x :=
  trans_refl_right (Z.contract n x)

theorem contract_refl_trans {A : Type u} (Z : ZoomComplex A) (n : Nat) (x : A) :
    trans (refl (Z.zoom (n + 1) x)) (Z.contract n x) = Z.contract n x :=
  trans_refl_left (Z.contract n x)

theorem contract_two_trans_refl {A : Type u} (Z : ZoomComplex A) (n : Nat) (x : A) :
    trans (contractTwo Z n x) (refl (Z.zoom n x)) = contractTwo Z n x :=
  trans_refl_right (contractTwo Z n x)

theorem contract_two_refl_trans {A : Type u} (Z : ZoomComplex A) (n : Nat) (x : A) :
    trans (refl (Z.zoom (n + 2) x)) (contractTwo Z n x) = contractTwo Z n x :=
  trans_refl_left (contractTwo Z n x)

theorem contract_three_assoc {A : Type u} (Z : ZoomComplex A) (n : Nat) (x : A) :
    trans (trans (Z.contract (n + 2) x) (Z.contract (n + 1) x)) (Z.contract n x) =
      trans (Z.contract (n + 2) x) (trans (Z.contract (n + 1) x) (Z.contract n x)) :=
  trans_assoc (Z.contract (n + 2) x) (Z.contract (n + 1) x) (Z.contract n x)

theorem contract_three_symm_symm {A : Type u} (Z : ZoomComplex A) (n : Nat) (x : A) :
    symm (symm (contractThree Z n x)) = contractThree Z n x :=
  symm_symm (contractThree Z n x)

theorem contract_two_symm_trans {A : Type u} (Z : ZoomComplex A) (n : Nat) (x : A) :
    symm (trans (Z.contract (n + 1) x) (Z.contract n x)) =
      trans (symm (Z.contract n x)) (symm (Z.contract (n + 1) x)) :=
  symm_trans (Z.contract (n + 1) x) (Z.contract n x)

theorem contract_whisker_trans {A : Type u} (Z : ZoomComplex A) (f : A → A) (n : Nat) (x : A) :
    congrArg f (trans (Z.contract (n + 1) x) (Z.contract n x)) =
      trans (congrArg f (Z.contract (n + 1) x)) (congrArg f (Z.contract n x)) := by
  simpa using congrArg_trans f (Z.contract (n + 1) x) (Z.contract n x)

theorem contract_whisker_symm {A : Type u} (Z : ZoomComplex A) (f : A → A) (n : Nat) (x : A) :
    congrArg f (symm (contractTwo Z n x)) = symm (congrArg f (contractTwo Z n x)) :=
  congrArg_symm f (contractTwo Z n x)

theorem contract_three_trans_refl {A : Type u} (Z : ZoomComplex A) (n : Nat) (x : A) :
    trans (contractThree Z n x) (refl (Z.zoom n x)) = contractThree Z n x :=
  trans_refl_right (contractThree Z n x)

/-! ## Universal cells and opetopic composition -/

structure UniversalCell {A : Type u} (O : OpetopicType A) where
  src : A
  tgt : A
  mediator : A
  leftFactor : Path (O.Gam src mediator) tgt
  rightFactor : Path (O.Gam mediator src) tgt

def composeViaUniversal {A : Type u} (O : OpetopicType A) (U : UniversalCell O) :
    Path (O.Gam U.src U.mediator) (O.Gam U.mediator U.src) :=
  trans U.leftFactor (symm U.rightFactor)

theorem left_factor_symm_symm {A : Type u} (O : OpetopicType A) (U : UniversalCell O) :
    symm (symm U.leftFactor) = U.leftFactor :=
  symm_symm U.leftFactor

theorem right_factor_symm_symm {A : Type u} (O : OpetopicType A) (U : UniversalCell O) :
    symm (symm U.rightFactor) = U.rightFactor :=
  symm_symm U.rightFactor

theorem left_factor_trans_refl {A : Type u} (O : OpetopicType A) (U : UniversalCell O) :
    trans U.leftFactor (refl U.tgt) = U.leftFactor :=
  trans_refl_right U.leftFactor

theorem right_factor_refl_trans {A : Type u} (O : OpetopicType A) (U : UniversalCell O) :
    trans (refl (O.Gam U.mediator U.src)) U.rightFactor = U.rightFactor :=
  trans_refl_left U.rightFactor

theorem compose_via_universal_symm {A : Type u} (O : OpetopicType A) (U : UniversalCell O) :
    symm (composeViaUniversal O U) = trans U.rightFactor (symm U.leftFactor) := by
  unfold composeViaUniversal
  calc
    symm (trans U.leftFactor (symm U.rightFactor))
        = trans (symm (symm U.rightFactor)) (symm U.leftFactor) :=
          symm_trans U.leftFactor (symm U.rightFactor)
    _ = trans U.rightFactor (symm U.leftFactor) := by
          simpa using congrArg (fun t => trans t (symm U.leftFactor)) (symm_symm U.rightFactor)

theorem compose_via_universal_symm_symm {A : Type u} (O : OpetopicType A) (U : UniversalCell O) :
    symm (symm (composeViaUniversal O U)) = composeViaUniversal O U :=
  symm_symm (composeViaUniversal O U)

theorem compose_via_universal_trans_refl {A : Type u} (O : OpetopicType A) (U : UniversalCell O) :
    trans (composeViaUniversal O U) (refl (O.Gam U.mediator U.src)) = composeViaUniversal O U :=
  trans_refl_right (composeViaUniversal O U)

theorem compose_via_universal_refl_trans {A : Type u} (O : OpetopicType A) (U : UniversalCell O) :
    trans (refl (O.Gam U.src U.mediator)) (composeViaUniversal O U) = composeViaUniversal O U :=
  trans_refl_left (composeViaUniversal O U)

theorem compose_via_universal_whisker_trans {A : Type u} (O : OpetopicType A)
    (U : UniversalCell O) (f : A → A) :
    congrArg f (trans U.leftFactor (symm U.rightFactor)) =
      trans (congrArg f U.leftFactor) (congrArg f (symm U.rightFactor)) := by
  simpa using congrArg_trans f U.leftFactor (symm U.rightFactor)

theorem compose_via_universal_whisker_symm {A : Type u} (O : OpetopicType A)
    (U : UniversalCell O) (f : A → A) :
    congrArg f (symm (composeViaUniversal O U)) =
      symm (congrArg f (composeViaUniversal O U)) :=
  congrArg_symm f (composeViaUniversal O U)

/-! ## Opetopic categories -/

structure OpetopicCategory (Obj : Type u) (Mor : Type v) where
  src : Mor → Obj
  tgt : Mor → Obj
  Id : Obj → Mor
  Gam : Mor → Mor → Mor
  assoc : (f g h : Mor) → Path (Gam (Gam f g) h) (Gam f (Gam g h))
  id_left : (f : Mor) → Path (Gam (Id (src f)) f) f
  id_right : (f : Mor) → Path (Gam f (Id (tgt f))) f

def catAssocChain {Obj : Type u} {Mor : Type v} (C : OpetopicCategory Obj Mor)
    (f g h k : Mor) : Path (C.Gam (C.Gam (C.Gam f g) h) k) (C.Gam f (C.Gam g (C.Gam h k))) :=
  trans (C.assoc (C.Gam f g) h k) (C.assoc f g (C.Gam h k))

theorem cat_assoc_symm_symm {Obj : Type u} {Mor : Type v}
    (C : OpetopicCategory Obj Mor) (f g h : Mor) :
    symm (symm (C.assoc f g h)) = C.assoc f g h :=
  symm_symm (C.assoc f g h)

theorem cat_assoc_trans_refl {Obj : Type u} {Mor : Type v}
    (C : OpetopicCategory Obj Mor) (f g h : Mor) :
    trans (C.assoc f g h) (refl (C.Gam f (C.Gam g h))) = C.assoc f g h :=
  trans_refl_right (C.assoc f g h)

theorem cat_assoc_refl_trans {Obj : Type u} {Mor : Type v}
    (C : OpetopicCategory Obj Mor) (f g h : Mor) :
    trans (refl (C.Gam (C.Gam f g) h)) (C.assoc f g h) = C.assoc f g h :=
  trans_refl_left (C.assoc f g h)

theorem cat_assoc_chain_assoc {Obj : Type u} {Mor : Type v}
    (C : OpetopicCategory Obj Mor) (f g h k : Mor) :
    trans (trans (C.assoc (C.Gam f g) h k) (C.assoc f g (C.Gam h k)))
      (refl (C.Gam f (C.Gam g (C.Gam h k)))) =
    trans (C.assoc (C.Gam f g) h k)
      (trans (C.assoc f g (C.Gam h k)) (refl (C.Gam f (C.Gam g (C.Gam h k))))) :=
  trans_assoc (C.assoc (C.Gam f g) h k) (C.assoc f g (C.Gam h k))
    (refl (C.Gam f (C.Gam g (C.Gam h k))))

theorem cat_id_left_symm_symm {Obj : Type u} {Mor : Type v}
    (C : OpetopicCategory Obj Mor) (f : Mor) :
    symm (symm (C.id_left f)) = C.id_left f :=
  symm_symm (C.id_left f)

theorem cat_id_right_symm_symm {Obj : Type u} {Mor : Type v}
    (C : OpetopicCategory Obj Mor) (f : Mor) :
    symm (symm (C.id_right f)) = C.id_right f :=
  symm_symm (C.id_right f)

theorem cat_whisker_assoc_trans {Obj : Type u} {Mor : Type v}
    (C : OpetopicCategory Obj Mor) (m : Mor → Mor) (f g h : Mor) :
    congrArg m (trans (C.assoc f g h) (refl (C.Gam f (C.Gam g h)))) =
      trans (congrArg m (C.assoc f g h)) (congrArg m (refl (C.Gam f (C.Gam g h)))) := by
  simpa using congrArg_trans m (C.assoc f g h) (refl (C.Gam f (C.Gam g h)))

theorem cat_whisker_assoc_symm {Obj : Type u} {Mor : Type v}
    (C : OpetopicCategory Obj Mor) (m : Mor → Mor) (f g h : Mor) :
    congrArg m (symm (C.assoc f g h)) = symm (congrArg m (C.assoc f g h)) :=
  congrArg_symm m (C.assoc f g h)

theorem cat_assoc_symm_trans {Obj : Type u} {Mor : Type v}
    (C : OpetopicCategory Obj Mor) (f g h : Mor) :
    symm (trans (C.assoc f g h) (refl (C.Gam f (C.Gam g h)))) =
      trans (symm (refl (C.Gam f (C.Gam g h)))) (symm (C.assoc f g h)) := by
  simpa using symm_trans (C.assoc f g h) (refl (C.Gam f (C.Gam g h)))

/-! ## Baez-Dolan hypothesis and multitopes -/

structure BaezDolanHypothesis (A : Type u) where
  Sym : Nat → A
  Gam : A → A → A
  unit : A
  universal : (m n : Nat) → Path (Gam (Sym m) (Sym n)) (Sym (m + n))
  unit_left : (n : Nat) → Path (Gam unit (Sym n)) (Sym n)
  unit_right : (n : Nat) → Path (Gam (Sym n) unit) (Sym n)

theorem universal_symm_symm {A : Type u} (B : BaezDolanHypothesis A) (m n : Nat) :
    symm (symm (B.universal m n)) = B.universal m n :=
  symm_symm (B.universal m n)

theorem universal_trans_refl {A : Type u} (B : BaezDolanHypothesis A) (m n : Nat) :
    trans (B.universal m n) (refl (B.Sym (m + n))) = B.universal m n :=
  trans_refl_right (B.universal m n)

theorem universal_refl_trans {A : Type u} (B : BaezDolanHypothesis A) (m n : Nat) :
    trans (refl (B.Gam (B.Sym m) (B.Sym n))) (B.universal m n) = B.universal m n :=
  trans_refl_left (B.universal m n)

theorem unit_left_symm_symm {A : Type u} (B : BaezDolanHypothesis A) (n : Nat) :
    symm (symm (B.unit_left n)) = B.unit_left n :=
  symm_symm (B.unit_left n)

theorem unit_right_symm_symm {A : Type u} (B : BaezDolanHypothesis A) (n : Nat) :
    symm (symm (B.unit_right n)) = B.unit_right n :=
  symm_symm (B.unit_right n)

theorem universal_whisker_trans {A : Type u} (B : BaezDolanHypothesis A)
    (f : A → A) (m n : Nat) :
    congrArg f (trans (B.universal m n) (refl (B.Sym (m + n)))) =
      trans (congrArg f (B.universal m n)) (congrArg f (refl (B.Sym (m + n)))) := by
  simpa using congrArg_trans f (B.universal m n) (refl (B.Sym (m + n)))

theorem universal_whisker_symm {A : Type u} (B : BaezDolanHypothesis A)
    (f : A → A) (m n : Nat) :
    congrArg f (symm (B.universal m n)) = symm (congrArg f (B.universal m n)) :=
  congrArg_symm f (B.universal m n)

theorem universal_symm_trans {A : Type u} (B : BaezDolanHypothesis A) (m n : Nat) :
    symm (trans (B.universal m n) (refl (B.Sym (m + n)))) =
      trans (symm (refl (B.Sym (m + n)))) (symm (B.universal m n)) := by
  simpa using symm_trans (B.universal m n) (refl (B.Sym (m + n)))

inductive Multitope (A : Type u) where
  | atom : A → Multitope A
  | unit : Multitope A
  | join : Multitope A → Multitope A → Multitope A

def multitopeMap {A : Type u} {B : Type v} (f : A → B) : Multitope A → Multitope B
  | .atom a => .atom (f a)
  | .unit => .unit
  | .join x y => .join (multitopeMap f x) (multitopeMap f y)

theorem atom_congr_trans {A : Type u} {a b c : A}
    (p : Path a b) (q : Path b c) :
    congrArg Multitope.atom (trans p q) =
      trans (congrArg Multitope.atom p) (congrArg Multitope.atom q) :=
  congrArg_trans Multitope.atom p q

theorem atom_congr_symm {A : Type u} {a b : A}
    (p : Path a b) :
    congrArg Multitope.atom (symm p) = symm (congrArg Multitope.atom p) :=
  congrArg_symm Multitope.atom p

theorem join_left_congr_trans {A : Type u} (m : Multitope A)
    {x y z : Multitope A} (p : Path x y) (q : Path y z) :
    congrArg (fun t => Multitope.join t m) (trans p q) =
      trans (congrArg (fun t => Multitope.join t m) p)
        (congrArg (fun t => Multitope.join t m) q) :=
  congrArg_trans (fun t => Multitope.join t m) p q

theorem join_left_congr_symm {A : Type u} (m : Multitope A)
    {x y : Multitope A} (p : Path x y) :
    congrArg (fun t => Multitope.join t m) (symm p) =
      symm (congrArg (fun t => Multitope.join t m) p) :=
  congrArg_symm (fun t => Multitope.join t m) p

theorem join_right_congr_trans {A : Type u} (m : Multitope A)
    {x y z : Multitope A} (p : Path x y) (q : Path y z) :
    congrArg (fun t => Multitope.join m t) (trans p q) =
      trans (congrArg (fun t => Multitope.join m t) p)
        (congrArg (fun t => Multitope.join m t) q) :=
  congrArg_trans (fun t => Multitope.join m t) p q

theorem join_right_congr_symm {A : Type u} (m : Multitope A)
    {x y : Multitope A} (p : Path x y) :
    congrArg (fun t => Multitope.join m t) (symm p) =
      symm (congrArg (fun t => Multitope.join m t) p) :=
  congrArg_symm (fun t => Multitope.join m t) p

theorem multitope_map_id {A : Type u} (m : Multitope A) :
    multitopeMap (fun x => x) m = m := by
  induction m with
  | atom a => rfl
  | unit => rfl
  | join x y ihx ihy =>
      simp [multitopeMap, ihx, ihy]

theorem multitope_map_comp {A : Type u} {B : Type v} {C : Type w}
    (f : A → B) (g : B → C) (m : Multitope A) :
    multitopeMap (fun x => g (f x)) m = multitopeMap g (multitopeMap f m) := by
  induction m with
  | atom a => rfl
  | unit => rfl
  | join x y ihx ihy =>
      simp [multitopeMap, ihx, ihy]

end ComputationalPaths.OpetopicSetsDeep
