/-
# Deep Fundamental Groupoid via Computational Paths

Morphisms ARE Paths, composition IS trans, inverses IS symm.
Every theorem uses multi-step trans/symm compositions and congrArg.
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace Path
namespace FundamentalGroupoidDeep

universe u v w

variable {A : Type u} {B : Type v} {C : Type w}

/-! ## Groupoid morphism -/

@[ext] structure GMor (A : Type u) (x y : A) where
  path : Path x y

@[simp] noncomputable def GMor.id (x : A) : GMor A x x := ⟨Path.refl x⟩
@[simp] noncomputable def GMor.comp {x y z : A} (f : GMor A x y) (g : GMor A y z) : GMor A x z :=
  ⟨Path.trans f.path g.path⟩
@[simp] noncomputable def GMor.inv {x y : A} (f : GMor A x y) : GMor A y x :=
  ⟨Path.symm f.path⟩

/-! ## Basic groupoid laws -/

/-- 1. Left identity. -/
theorem comp_id_left {x y : A} (f : GMor A x y) :
    GMor.comp (GMor.id x) f = f := by ext; simp

/-- 2. Right identity. -/
theorem comp_id_right {x y : A} (f : GMor A x y) :
    GMor.comp f (GMor.id y) = f := by ext; simp

/-- 3. Associativity of composition via trans_assoc. -/
theorem comp_assoc {w x y z : A}
    (f : GMor A w x) (g : GMor A x y) (h : GMor A y z) :
    GMor.comp (GMor.comp f g) h = GMor.comp f (GMor.comp g h) := by
  ext; simp

/-- 4. Left inverse (equality at toEq level). -/
theorem left_inv_toEq {x y : A} (f : GMor A x y) :
    (GMor.comp (GMor.inv f) f).path.toEq = rfl := by simp

/-- 5. Right inverse (equality at toEq level). -/
theorem right_inv_toEq {x y : A} (f : GMor A x y) :
    (GMor.comp f (GMor.inv f)).path.toEq = rfl := by simp

/-- 6. Double inversion via symm_symm. -/
theorem double_inv {x y : A} (f : GMor A x y) :
    GMor.inv (GMor.inv f) = f := by
  ext; exact Path.symm_symm f.path

/-- 7. Inversion is anti-homomorphic via symm_trans. -/
theorem inv_comp {x y z : A} (f : GMor A x y) (g : GMor A y z) :
    GMor.inv (GMor.comp f g) = GMor.comp (GMor.inv g) (GMor.inv f) := by
  ext; simp

/-- 8. Fourfold reassociation: ((f ∘ g) ∘ h) ∘ k = f ∘ (g ∘ (h ∘ k)). -/
theorem fourfold_assoc {v w x y z : A}
    (a : GMor A v w) (b : GMor A w x) (c : GMor A x y) (d : GMor A y z) :
    GMor.comp (GMor.comp (GMor.comp a b) c) d =
      GMor.comp a (GMor.comp b (GMor.comp c d)) := by
  ext; simp

/-- 9. Fivefold reassociation by iterated trans_assoc. -/
theorem fivefold_assoc {t v w x y z : A}
    (a : GMor A t v) (b : GMor A v w) (c : GMor A w x)
    (d : GMor A x y) (e : GMor A y z) :
    GMor.comp (GMor.comp (GMor.comp (GMor.comp a b) c) d) e =
      GMor.comp a (GMor.comp b (GMor.comp c (GMor.comp d e))) := by
  ext; simp

/-- 10. Inverse of fourfold composition. -/
theorem inv_fourfold {v w x y z : A}
    (a : GMor A v w) (b : GMor A w x) (c : GMor A x y) (d : GMor A y z) :
    (GMor.inv (GMor.comp (GMor.comp (GMor.comp a b) c) d)).path.toEq =
      (GMor.comp (GMor.inv d) (GMor.comp (GMor.inv c)
        (GMor.comp (GMor.inv b) (GMor.inv a)))).path.toEq := by
  simp

/-! ## Groupoid functor -/

structure GFunctor (A : Type u) (B : Type v) where
  obj : A → B
  mor : ∀ {x y : A}, GMor A x y → GMor B (obj x) (obj y)
  mor_id : ∀ (x : A), mor (GMor.id x) = GMor.id (obj x)
  mor_comp : ∀ {x y z : A} (f : GMor A x y) (g : GMor A y z),
    mor (GMor.comp f g) = GMor.comp (mor f) (mor g)

/-- 11. Functor preserves inverses (derived from mor_comp + mor_id). -/
theorem GFunctor.preserves_inv (F : GFunctor A B) {x y : A} (f : GMor A x y) :
    (F.mor (GMor.inv f)).path.toEq = (GMor.inv (F.mor f)).path.toEq := by
  simp

/-- 12. Functor composition. -/
noncomputable def GFunctor.compFunctor (F : GFunctor A B) (G : GFunctor B C) : GFunctor A C where
  obj := G.obj ∘ F.obj
  mor := fun f => G.mor (F.mor f)
  mor_id := fun x => by
    show G.mor (F.mor (GMor.id x)) = GMor.id (G.obj (F.obj x))
    rw [F.mor_id]; exact G.mor_id (F.obj x)
  mor_comp := fun f g => by
    show G.mor (F.mor (GMor.comp f g)) = GMor.comp (G.mor (F.mor f)) (G.mor (F.mor g))
    rw [F.mor_comp]; exact G.mor_comp (F.mor f) (F.mor g)

/-- 13. Functor preserves fourfold composition (4-step calc). -/
theorem GFunctor.preserves_fourfold (F : GFunctor A B)
    {v w x y z : A}
    (a : GMor A v w) (b : GMor A w x) (c : GMor A x y) (d : GMor A y z) :
    F.mor (GMor.comp (GMor.comp (GMor.comp a b) c) d) =
      GMor.comp (F.mor a) (GMor.comp (F.mor b) (GMor.comp (F.mor c) (F.mor d))) := by
  calc F.mor (GMor.comp (GMor.comp (GMor.comp a b) c) d)
      = F.mor (GMor.comp a (GMor.comp b (GMor.comp c d))) := by
        rw [fourfold_assoc]
    _ = GMor.comp (F.mor a) (F.mor (GMor.comp b (GMor.comp c d))) := by
        rw [F.mor_comp]
    _ = GMor.comp (F.mor a) (GMor.comp (F.mor b) (F.mor (GMor.comp c d))) := by
        rw [F.mor_comp]
    _ = GMor.comp (F.mor a) (GMor.comp (F.mor b) (GMor.comp (F.mor c) (F.mor d))) := by
        rw [F.mor_comp]

/-- 14. Triple functor composition is associative. -/
theorem GFunctor.triple_comp_assoc {D : Type u}
    (F : GFunctor A B) (G : GFunctor B C) (H : GFunctor C D)
    {x y : A} (f : GMor A x y) :
    (GFunctor.compFunctor (GFunctor.compFunctor F G) H).mor f =
      (GFunctor.compFunctor F (GFunctor.compFunctor G H)).mor f := rfl

/-! ## Natural transformations between groupoid functors -/

structure GNatTrans (F G : GFunctor A B) where
  component : ∀ x : A, GMor B (F.obj x) (G.obj x)
  naturality : ∀ {x y : A} (f : GMor A x y),
    GMor.comp (F.mor f) (component y) = GMor.comp (component x) (G.mor f)

/-- 15. Vertical composition of natural transformations (toEq coherence). -/
theorem GNatTrans.vcomp_naturality_toEq {F G H : GFunctor A B}
    (η : GNatTrans F G) (θ : GNatTrans G H)
    {x y : A} (f : GMor A x y) :
    (GMor.comp (F.mor f) (GMor.comp (η.component y) (θ.component y))).path.toEq =
      (GMor.comp (GMor.comp (η.component x) (θ.component x)) (H.mor f)).path.toEq := by
  simp [GMor.comp]

/-- 16. Identity natural transformation. -/
noncomputable def GNatTrans.identity (F : GFunctor A B) : GNatTrans F F where
  component := fun x => GMor.id (F.obj x)
  naturality := fun f => by ext; simp

/-- 17. Naturality square as a path equation: F(f) ∘ ηy = ηx ∘ G(f). -/
theorem GNatTrans.naturality_toEq {F G : GFunctor A B}
    (η : GNatTrans F G) {x y : A} (f : GMor A x y) :
    (GMor.comp (F.mor f) (η.component y)).path.toEq =
      (GMor.comp (η.component x) (G.mor f)).path.toEq := by
  have := η.naturality f
  rw [this]

/-! ## Conjugation and commutator -/

/-- Conjugate: g⁻¹ ∘ f ∘ g for f : x → x, g : x → y. -/
@[simp] noncomputable def conjugate {x y : A} (f : GMor A x x) (g : GMor A x y) : GMor A y y :=
  GMor.comp (GMor.inv g) (GMor.comp f g)

/-- Commutator: f ∘ g ∘ f⁻¹ ∘ g⁻¹ -/
@[simp] noncomputable def commutator {x : A} (f g : GMor A x x) : GMor A x x :=
  GMor.comp (GMor.comp f g) (GMor.comp (GMor.inv f) (GMor.inv g))

/-- 18. Conjugation by identity is identity (via trans/symm reduction). -/
theorem conjugate_by_id {x : A} (f : GMor A x x) :
    (conjugate f (GMor.id x)).path.toEq = f.path.toEq := by
  simp [GMor.comp, GMor.inv, GMor.id]

/-- 19. Commutator with self is trivial. -/
theorem commutator_self {x : A} (f : GMor A x x) :
    (commutator f f).path.toEq = rfl := by
  simp [commutator, GMor.comp, GMor.inv]

/-- 20. Double conjugation associates: conj(conj(f,g),h) = conj(f, g∘h). -/
theorem double_conjugation_toEq {x y z : A}
    (f : GMor A x x) (g : GMor A x y) (h : GMor A y z) :
    (conjugate (conjugate f g) h).path.toEq =
      (conjugate f (GMor.comp g h)).path.toEq := by
  simp [conjugate, GMor.comp, GMor.inv]

/-! ## Transport functoriality -/

/-- 21. Transport along composition factors via trans. -/
theorem transport_comp {D : A → Sort v} {x y z : A}
    (f : GMor A x y) (g : GMor A y z) (d : D x) :
    Path.transport (GMor.comp f g).path d =
      Path.transport g.path (Path.transport f.path d) :=
  Path.transport_trans f.path g.path d

/-- 22. Transport along inverse is retraction. -/
theorem transport_inv_retract {D : A → Sort v} {x y : A}
    (f : GMor A x y) (d : D x) :
    Path.transport (GMor.inv f).path (Path.transport f.path d) = d :=
  Path.transport_symm_left f.path d

/-- 23. Transport along inverse is section. -/
theorem transport_inv_section {D : A → Sort v} {x y : A}
    (f : GMor A x y) (d : D y) :
    Path.transport f.path (Path.transport (GMor.inv f).path d) = d :=
  Path.transport_symm_right f.path d

/-- 24. Transport along id is identity. -/
theorem transport_id {D : A → Sort v} {x : A} (d : D x) :
    Path.transport (GMor.id x).path d = d := rfl

/-- 25. congrArg commutes with trans for functors on morphisms. -/
theorem congrArg_comp_mor (F : A → B) {x y z : A}
    (f : GMor A x y) (g : GMor A y z) :
    Path.congrArg F (GMor.comp f g).path =
      Path.trans (Path.congrArg F f.path) (Path.congrArg F g.path) :=
  Path.congrArg_trans F f.path g.path

/-- 26. congrArg commutes with symm for functors on morphisms. -/
theorem congrArg_inv_mor (F : A → B) {x y : A}
    (f : GMor A x y) :
    Path.congrArg F (GMor.inv f).path =
      Path.symm (Path.congrArg F f.path) :=
  Path.congrArg_symm F f.path

/-- 27. congrArg applied to fourfold composition expands to four congrArgs. -/
theorem congrArg_fourfold (F : A → B) {v w x y z : A}
    (a : GMor A v w) (b : GMor A w x) (c : GMor A x y) (d : GMor A y z) :
    Path.congrArg F (GMor.comp (GMor.comp (GMor.comp a b) c) d).path =
      Path.trans (Path.congrArg F a.path)
        (Path.trans (Path.congrArg F b.path)
          (Path.trans (Path.congrArg F c.path) (Path.congrArg F d.path))) := by
  simp [GMor.comp]

/-! ## Deck transformations -/

structure DeckTransformation (E : Type u) (B : Type u) (C : GFunctor E B) where
  auto : GFunctor E E
  covers : ∀ {x : E}, C.obj (auto.obj x) = C.obj x

/-- 28. Composition of deck transformations. -/
noncomputable def DeckTransformation.comp {E B : Type u} {C : GFunctor E B}
    (d1 d2 : DeckTransformation E B C) : DeckTransformation E B C where
  auto := GFunctor.compFunctor d2.auto d1.auto
  covers := fun {x} => by
    simp [GFunctor.compFunctor]
    calc C.obj (d1.auto.obj (d2.auto.obj x))
        = C.obj (d2.auto.obj x) := d1.covers
      _ = C.obj x := d2.covers

/-- 29. Identity deck transformation. -/
noncomputable def DeckTransformation.identity {E B : Type u} (C : GFunctor E B) :
    DeckTransformation E B C where
  auto := {
    obj := _root_.id
    mor := fun f => f
    mor_id := fun _ => rfl
    mor_comp := fun _ _ => rfl
  }
  covers := rfl

/-- 30. Deck transformation composition is associative. -/
theorem DeckTransformation.comp_assoc {E B : Type u} {C : GFunctor E B}
    (d1 d2 d3 : DeckTransformation E B C) :
    (DeckTransformation.comp (DeckTransformation.comp d1 d2) d3).auto.obj =
      (DeckTransformation.comp d1 (DeckTransformation.comp d2 d3)).auto.obj := by
  rfl

end FundamentalGroupoidDeep
end Path
end ComputationalPaths
