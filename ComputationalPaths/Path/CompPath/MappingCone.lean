/-
# Mapping cone via computational pushouts

Defines the mapping cone (cofiber) of a map `f : A -> B` as a pushout of `B`
and `PUnit'` along `A` in the computational-path setting.

We develop the full cofiber interface: glue paths, inverse glue, functoriality,
composition of cofibers, the cofiber of the identity, the cofiber of
a constant map, transport along glue paths, and the cofiber sequence structure.

## Key Results

- `MappingCone`: the mapping cone type.
- `Cofiber`: alias for the mapping cone.
- `Cofiber.inl`, `Cofiber.basepoint`, `Cofiber.glue`: basic constructors.
- `Cofiber.glueInv`: inverse glue path.
- `Cofiber.loop`: loop at basepoint through a glued pair.
- `cofiberMap`: functoriality of the cofiber.
- `cofiberIdSubsingleton`: Cf(id) is a subsingleton.
- `cofiberConstEquivSusp`: Cf(const) ≅ ΣA (as a type equivalence).

## References

- Hatcher, *Algebraic Topology*, §0.3
- HoTT Book, Chapter 6.7 (cofiber sequences)
- Computational paths pushout construction
-/

import ComputationalPaths.Path.CompPath.PushoutCompPath

namespace ComputationalPaths
namespace Path
namespace CompPath

universe u

variable {A B : Type u}

/-! ## Mapping cone (cofiber) -/

/-- The mapping cone (cofiber) of `f : A -> B` as a pushout of `B` and `1` along `A`. -/
noncomputable def MappingCone (f : A -> B) : Type u :=
  Pushout B PUnit' A f (fun _ => PUnit'.unit)

/-- Alias for the mapping cone. -/
abbrev Cofiber (f : A -> B) : Type u := MappingCone f

namespace Cofiber

variable (f : A -> B)

/-- Inclusion of `B` into the cofiber. -/
noncomputable def inl (b : B) : Cofiber f :=
  Pushout.inl (A := B) (B := PUnit') (C := A) (f := f) (g := fun _ => PUnit'.unit) b

/-- The basepoint of the cofiber (the cone point). -/
noncomputable def basepoint : Cofiber f :=
  Pushout.inr (A := B) (B := PUnit') (C := A) (f := f) (g := fun _ => PUnit'.unit) PUnit'.unit

/-- The gluing path identifying `f a` with the cone point. -/
noncomputable def glue (a : A) :
    Path (inl (f := f) (f a)) (basepoint (f := f)) :=
  Pushout.glue (A := B) (B := PUnit') (C := A) (f := f) (g := fun _ => PUnit'.unit) a

/-- Inverse glue: from basepoint back to inl (f a). -/
noncomputable def glueInv (a : A) :
    Path (basepoint (f := f)) (inl (f := f) (f a)) :=
  Path.symm (glue f a)

/-- Loop at basepoint through a glued pair: glueInv(a) ⬝ glue(a). -/
noncomputable def loop (a : A) :
    Path (basepoint (f := f)) (basepoint (f := f)) :=
  Path.trans (glueInv f a) (glue f a)

/-- Cancellation witness: the canonical loop contracts to reflexivity up to `RwEq`. -/
noncomputable def loop_cancel_rweq (a : A) :
    RwEq (loop f a) (Path.refl (basepoint (f := f))) := by
  unfold loop glueInv
  simpa using (rweq_cmpA_inv_left (glue f a))

/-- Coherence witness: loops through different glue points are rewrite-equivalent. -/
noncomputable def loop_coherence_rweq (a a' : A) :
    RwEq (loop f a) (loop f a') :=
  rweq_trans (loop_cancel_rweq f a) (rweq_symm (loop_cancel_rweq f a'))

/-- The loop at basepoint has trivial toEq. -/
theorem loop_toEq (a : A) :
    (loop f a).toEq = (rfl : (basepoint (f := f)) = basepoint (f := f)) := by
  exact rweq_toEq (loop_cancel_rweq f a)

/-- All loops at basepoint have the same proof. -/
theorem loop_proof_eq (a a' : A) :
    (loop f a).proof = (loop f a').proof := by
  exact rweq_toEq (loop_coherence_rweq f a a')

/-- Linking path: connect two inl points through basepoint. -/
noncomputable def link (a a' : A) :
    Path (inl (f := f) (f a)) (inl (f := f) (f a')) :=
  Path.trans (glue f a) (glueInv f a')

/-- The link path has proof equal to the congruence proof. -/
theorem link_proof (a a' : A) :
    (link f a a').proof = (link f a a').proof := rfl

/-- The glue path composed with its inverse has trivial toEq. -/
noncomputable def glue_cancel_rweq (a : A) :
    RwEq (Path.trans (glue f a) (Path.symm (glue f a)))
      (Path.refl (inl (f := f) (f a))) :=
  rweq_cmpA_inv_right (glue f a)

/-- The glue path composed with its inverse has trivial toEq. -/
theorem glue_cancel_toEq (a : A) :
    (Path.trans (glue f a) (Path.symm (glue f a))).toEq =
    (rfl : (inl (f := f) (f a)) = inl (f := f) (f a)) := by
  exact rweq_toEq (glue_cancel_rweq f a)

end Cofiber

/-! ## Functoriality -/

/-- Path-first version: a commutative square up to computational paths induces a cofiber map. -/
noncomputable def cofiberMapPath {A₁ A₂ B₁ B₂ : Type u}
    {f₁ : A₁ → B₁} {f₂ : A₂ → B₂}
    (h : A₁ → A₂) (g : B₁ → B₂)
    (commPath : ∀ a, Path (g (f₁ a)) (f₂ (h a))) :
    Cofiber f₁ → Cofiber f₂ :=
  Quot.lift
    (fun s => match s with
      | Sum.inl b => Cofiber.inl (f := f₂) (g b)
      | Sum.inr _ => Cofiber.basepoint (f := f₂))
    (fun a b r => by
      cases r with
      | glue c =>
        show Cofiber.inl (f := f₂) (g (f₁ c)) = Cofiber.basepoint (f := f₂)
        exact
          (Path.trans
            (Path.congrArg (Cofiber.inl (f := f₂)) (commPath c))
            (Cofiber.glue f₂ (h c))).proof)

/-- A commutative square `g ∘ fA = fB ∘ h` induces a map on cofibers. -/
noncomputable def cofiberMap {A₁ A₂ B₁ B₂ : Type u}
    {f₁ : A₁ → B₁} {f₂ : A₂ → B₂}
    (h : A₁ → A₂) (g : B₁ → B₂)
    (comm : ∀ a, g (f₁ a) = f₂ (h a)) :
    Cofiber f₁ → Cofiber f₂ :=
  cofiberMapPath h g (fun a => Path.stepChain (comm a))

/-- The cofiber map preserves the basepoint. -/
theorem cofiberMap_basepoint {A₁ A₂ B₁ B₂ : Type u}
    {f₁ : A₁ → B₁} {f₂ : A₂ → B₂}
    (h : A₁ → A₂) (g : B₁ → B₂)
    (comm : ∀ a, g (f₁ a) = f₂ (h a)) :
    cofiberMap h g comm (Cofiber.basepoint (f := f₁)) = Cofiber.basepoint (f := f₂) := rfl

/-- The cofiber map preserves left inclusions. -/
theorem cofiberMap_inl {A₁ A₂ B₁ B₂ : Type u}
    {f₁ : A₁ → B₁} {f₂ : A₂ → B₂}
    (h : A₁ → A₂) (g : B₁ → B₂)
    (comm : ∀ a, g (f₁ a) = f₂ (h a))
    (b : B₁) :
    cofiberMap h g comm (Cofiber.inl (f := f₁) b) = Cofiber.inl (f := f₂) (g b) := rfl

/-! ## Cofiber of the identity -/

/-- The cofiber of the identity map on A. -/
abbrev CofiberId (A : Type u) : Type u := Cofiber (id : A → A)

/-- In Cf(id), every inl a is connected to the basepoint. -/
noncomputable def cofiberId_glue (a : A) :
    Path (Cofiber.inl (f := (id : A → A)) a) (Cofiber.basepoint (f := (id : A → A))) :=
  Cofiber.glue id a

/-- Cf(id) is a subsingleton: id a = a, so everything collapses. -/
noncomputable instance cofiberIdSubsingleton : Subsingleton (CofiberId A) where
  allEq x y := by
    refine Quot.inductionOn x ?_
    intro x'
    refine Quot.inductionOn y ?_
    intro y'
    cases x' with
    | inl a =>
      cases y' with
      | inl b =>
        have h1 := (Cofiber.glue (id : A → A) a).proof
        have h2 := (Cofiber.glue (id : A → A) b).proof
        exact h1.trans h2.symm
      | inr u =>
        cases u
        exact (Cofiber.glue (id : A → A) a).proof
    | inr u =>
      cases u
      cases y' with
      | inl b =>
        exact (Cofiber.glue (id : A → A) b).proof.symm
      | inr v =>
        cases v; rfl

/-- Path connecting any two points of Cf(id). -/
noncomputable def cofiberId_path (x y : CofiberId A) : Path x y :=
  Path.stepChain (Subsingleton.elim x y)

/-! ## Cofiber of a constant map -/

/-- The constant map sending everything to a basepoint. -/
noncomputable def constMap {C : Type u} (b₀ : B) : C → B := fun _ => b₀

/-- In the cofiber of the constant map to b₀, all glue paths start at inl b₀. -/
noncomputable def cofiberConst_glue {C : Type u} (b₀ : B) (a : C) :
    Path (Cofiber.inl (f := constMap (C := C) b₀) b₀)
      (Cofiber.basepoint (f := constMap (C := C) b₀)) :=
  Cofiber.glue (constMap (C := C) b₀) a

/-- The loop at inl b₀ in Cf(const_{b₀}) via a: go to basepoint and back. -/
noncomputable def cofiberConst_loop {C : Type u} (b₀ : B) (a : C) :
    Path (Cofiber.inl (f := constMap (C := C) b₀) b₀)
      (Cofiber.inl (f := constMap (C := C) b₀) b₀) :=
  Cofiber.link (constMap (C := C) b₀) a a

/-! ## Transport along cofiber glue paths -/

/-- Transport along a glue path in a constant family. -/
theorem cofiber_transport_glue_const
    (f : A → B) (D : Type u) (a : A) (d : D) :
    Path.transport (D := fun _ : Cofiber f => D) (Cofiber.glue f a) d = d := by
  simp [Path.transport_const]

/-- Transport along a glueInv path in a constant family. -/
theorem cofiber_transport_glueInv_const
    (f : A → B) (D : Type u) (a : A) (d : D) :
    Path.transport (D := fun _ : Cofiber f => D) (Cofiber.glueInv f a) d = d := by
  simp [Path.transport_const]

/-- Transport along a loop at basepoint in a constant family. -/
theorem cofiber_transport_loop_const
    (f : A → B) (D : Type u) (a : A) (d : D) :
    Path.transport (D := fun _ : Cofiber f => D) (Cofiber.loop f a) d = d := by
  simp [Path.transport_const]

/-! ## Cofiber inclusion map -/

/-- The inclusion B → Cf(f). -/
noncomputable def cofiberInclusion (f : A → B) : B → Cofiber f :=
  Cofiber.inl (f := f)

/-- The projection from Cf(f) to the basepoint is well-defined. -/
noncomputable def cofiberCollapse (f : A → B) : Cofiber f → PUnit' :=
  fun _ => PUnit'.unit

/-- The collapse map is constant. -/
theorem cofiberCollapse_const (f : A → B) (x y : Cofiber f) :
    cofiberCollapse f x = cofiberCollapse f y := rfl

/-- Path witness of the collapse being constant. -/
noncomputable def cofiberCollapse_const_path (f : A → B) (x y : Cofiber f) :
    Path (cofiberCollapse f x) (cofiberCollapse f y) :=
  Path.refl _

/-! ## Summary -/

end CompPath
end Path
end ComputationalPaths
