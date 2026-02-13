 /-
 # Gray-category structure for computational paths
 
 This module extends the path `TwoCategory` interface with an explicit
 computational-path witness for interchange, yielding a lightweight Gray-category
 layer with pentagon/triangle coherence inherited as 3-cells.
 -/
 
 import ComputationalPaths.Path.TwoCategory
 
 namespace ComputationalPaths
 namespace Path
 
 universe u
 
 /-- A semistrict Gray-category: a `TwoCategory` equipped with an explicit
 computational-path 3-cell for interchange coherence. -/
 structure GrayCategory (Obj : Type u) extends TwoCategory (Obj := Obj) where
   interchange_path :
     ∀ {a b c : Obj} {f₀ f₁ f₂ : Hom a b} {g₀ g₁ g₂ : Hom b c}
       (η₁ : TwoCell f₀ f₁) (η₂ : TwoCell f₁ f₂)
       (θ₁ : TwoCell g₀ g₁) (θ₂ : TwoCell g₁ g₂),
       CellPath
         (vcomp (hcomp η₁ θ₁) (hcomp η₂ θ₂))
         (hcomp (vcomp η₁ η₂) (vcomp θ₁ θ₂))
 
 namespace GrayCategory
 
 variable {Obj : Type u}
 
 /-- Pentagon coherence as a computational-path 3-cell. -/
 def pentagonPath (G : GrayCategory (Obj := Obj))
     {a b c d e : Obj}
     (f : G.Hom a b) (g : G.Hom b c) (h : G.Hom c d) (k : G.Hom d e) :
     CellPath
       (TwoCategory.pentagonLeftRoute G.toTwoCategory f g h k)
       (TwoCategory.pentagonRightRoute G.toTwoCategory f g h k) :=
   TwoCategory.pentagonPath G.toTwoCategory f g h k
 
 /-- Triangle coherence as a computational-path 3-cell. -/
 def trianglePath (G : GrayCategory (Obj := Obj))
     {a b c : Obj} (f : G.Hom a b) (g : G.Hom b c) :
     CellPath
       (TwoCategory.triangleLeftRoute G.toTwoCategory f g)
       (TwoCategory.triangleRightRoute G.toTwoCategory f g) :=
   TwoCategory.trianglePath G.toTwoCategory f g
 
 /-- Interchange coherence as a computational-path 3-cell. -/
 def interchangePath (G : GrayCategory (Obj := Obj))
     {a b c : Obj} {f₀ f₁ f₂ : G.Hom a b} {g₀ g₁ g₂ : G.Hom b c}
     (η₁ : G.TwoCell f₀ f₁) (η₂ : G.TwoCell f₁ f₂)
     (θ₁ : G.TwoCell g₀ g₁) (θ₂ : G.TwoCell g₁ g₂) :
     CellPath
       (G.vcomp (G.hcomp η₁ θ₁) (G.hcomp η₂ θ₂))
       (G.hcomp (G.vcomp η₁ η₂) (G.vcomp θ₁ θ₂)) :=
   G.interchange_path η₁ η₂ θ₁ θ₂
 
 end GrayCategory
 
 /-- Computational paths carry a canonical Gray-category structure. -/
 def pathGrayCategory (A : Type u) : GrayCategory (Obj := A) where
   toTwoCategory := pathTwoCategory A
   interchange_path := by
     intro a b c f₀ f₁ f₂ g₀ g₁ g₂ η₁ η₂ θ₁ θ₂
     exact
       CellPath.ofEq
         ((pathTwoCategory A).interchange
           (a := a) (b := b) (c := c)
           (f₀ := f₀) (f₁ := f₁) (f₂ := f₂)
           (g₀ := g₀) (g₁ := g₁) (g₂ := g₂)
           (η₁ := η₁) (η₂ := η₂) (θ₁ := θ₁) (θ₂ := θ₂))
 
 /-- Forgetting 3-cell data recovers the path 2-category. -/
 @[simp] theorem pathGrayCategory_to_twoCategory (A : Type u) :
     (pathGrayCategory A).toTwoCategory = pathTwoCategory A := by
   rfl
 
 end Path
 end ComputationalPaths
