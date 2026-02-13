 /-
 # Tricategory layer for computational paths
 
 This module adds a lightweight tricategory interface over `GrayCategory`, with
 explicit 4-cell witnesses (`CellPath` between 3-cells) for pentagon and
 triangle coherence.
 -/
 
 import ComputationalPaths.Path.GrayCategory
 
 namespace ComputationalPaths
 namespace Path
 
 universe u
 
 /-- A minimal tricategory interface extending `GrayCategory` with 4-cell
 coherence witnesses comparing pentagon and triangle 3-cells. -/
 structure Tricategory (Obj : Type u) extends GrayCategory (Obj := Obj) where
   pentagonator :
     ∀ {a b c d e : Obj}
       (f : Hom a b) (g : Hom b c) (h : Hom c d) (k : Hom d e),
       CellPath
         (TwoCategory.pentagonPath toGrayCategory.toTwoCategory f g h k)
         (GrayCategory.pentagonPath toGrayCategory f g h k)
   triangulator :
     ∀ {a b c : Obj} (f : Hom a b) (g : Hom b c),
       CellPath
         (TwoCategory.trianglePath toGrayCategory.toTwoCategory f g)
         (GrayCategory.trianglePath toGrayCategory f g)
 
 namespace Tricategory
 
 variable {Obj : Type u}
 
 /-- Pentagon coherence 4-cell in a tricategory. -/
 def pentagonatorPath (T : Tricategory (Obj := Obj))
     {a b c d e : Obj}
     (f : T.Hom a b) (g : T.Hom b c) (h : T.Hom c d) (k : T.Hom d e) :
     CellPath
       (TwoCategory.pentagonPath T.toGrayCategory.toTwoCategory f g h k)
       (GrayCategory.pentagonPath T.toGrayCategory f g h k) :=
   T.pentagonator f g h k
 
 /-- Triangle coherence 4-cell in a tricategory. -/
 def triangulatorPath (T : Tricategory (Obj := Obj))
     {a b c : Obj} (f : T.Hom a b) (g : T.Hom b c) :
     CellPath
       (TwoCategory.trianglePath T.toGrayCategory.toTwoCategory f g)
       (GrayCategory.trianglePath T.toGrayCategory f g) :=
   T.triangulator f g
 
 end Tricategory
 
 /-- Computational paths carry a canonical tricategory structure. -/
 def pathTricategory (A : Type u) : Tricategory (Obj := A) where
   toGrayCategory := pathGrayCategory A
   pentagonator := by
     intro a b c d e f g h k
     exact CellPath.ofEq (by rfl)
   triangulator := by
     intro a b c f g
     exact CellPath.ofEq (by rfl)
 
 /-- Forgetting 4-cell data recovers the path Gray-category. -/
 @[simp] theorem pathTricategory_to_grayCategory (A : Type u) :
     (pathTricategory A).toGrayCategory = pathGrayCategory A := by
   rfl
 
 end Path
 end ComputationalPaths
