import ComputationalPaths.Path.OmegaGroupoid.GlobularPasting

open ComputationalPaths
open ComputationalPaths.Path
open ComputationalPaths.Path.OmegaFoundations

/-! Incremental audit. This checks the foundations only; it is not yet a
completion gate for the full weak omega-groupoid theorem. -/

example (G : GlobularSet) (n k : Nat) (c : G.Cell (n + (k + 2))) :
    G.sourceIter (k + 1) (G.source c) = G.sourceIter (k + 1) (G.target c) :=
  G.sourceIter_globular k c

example (G : GlobularSet) {n : Nat} (p q : G.Cell (n + 1))
    (h : G.target p = G.source q) :
    GlobularSet.Parallel G n (G.source p) (G.target q) :=
  (G.compositeBoundary p q h).parallel

example (G : GlobularSet) : GlobularSet.Contraction (GlobularSet.Map.id G) :=
  GlobularSet.Contraction.identity G

noncomputable example {A : Type} {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    RwEq (Path.trans (Path.trans p q) r) (Path.trans p (Path.trans q r)) :=
  (associatorCell p q r).2.2.2.2

#print axioms GlobularSet.sourceIter_globular
#print axioms GlobularSet.targetIter_globular
#print axioms GlobularSet.compositeBoundary
#print axioms GlobularSet.Contraction.comp
#print axioms associatorCell

example (G : GlobularSet) (n : Nat) (c : Pasting n G) :
    Pasting.source (Pasting.identity c) = c := Pasting.source_identity G c

example (G : GlobularSet) (c : Pasting 7 G) :
    Pasting.target (Pasting.identity c) = c := Pasting.target_identity G c

#print axioms GlobularSet.hom
#print axioms GlobularSet.Map.hom
#print axioms Pasting.globular
#print axioms Pasting.identities

example {G H K : GlobularSet} (f : GlobularSet.Map G H) (g : GlobularSet.Map H K)
    (n : Nat) (c : Pasting n G) :
    Pasting.map g (Pasting.map f c) = Pasting.map (GlobularSet.Map.comp g f) c :=
  Pasting.map_comp f g c

#print axioms Pasting.pastingFunctor

example {O : Type} {E F D : O → O → Type}
    (f : {a b : O} → E a b → Chain F a b)
    (g : {a b : O} → F a b → Chain D a b) {a b : O} (p : Chain E a b) :
    (p.bind f).bind g = p.bind (fun e => (f e).bind g) := Chain.bind_assoc f g p

#print axioms Chain.bind_assoc
#print axioms evalPathChain_bind

example (G : GlobularSet) (n : Nat) (c d : G.Cell n)
    (h : Pasting.singleton c = Pasting.singleton d) : c = d :=
  Pasting.singleton_injective G h

example (G : GlobularSet) (c : G.Cell 8) :
    Pasting.source (Pasting.singleton c) = Pasting.singleton (G.source c) :=
  Pasting.source_singleton G c

example {G H : GlobularSet} (f : GlobularSet.Map G H) (n : Nat) (c : G.Cell n) :
    Pasting.map f (Pasting.singleton c) = Pasting.singleton (f.app c) :=
  Pasting.map_singleton f c

#print axioms Pasting.singleton_injective
#print axioms Pasting.singletonGlobular
#print axioms Pasting.singleton_natural

example {G : GlobularSet} (n : Nat) {a b c d : G.Cell 0}
    (p : Pasting.Horizontal n G a b) (q : Pasting.Horizontal n G b c)
    (r : Pasting.Horizontal n G c d) :
    Pasting.horizontal (Pasting.horizontal p q) r =
      Pasting.horizontal p (Pasting.horizontal q r) := Pasting.horizontal_assoc p q r

example {G : GlobularSet} {a b c : G.Cell 0}
    (p : Pasting.Horizontal 8 G a b) (q : Pasting.Horizontal 8 G b c) :
    (Pasting.globular G).sourceZero (n := 9) (Pasting.pack (Pasting.horizontal p q)) = a :=
  Pasting.sourceZero_pack _

#print axioms Pasting.horizontal_assoc
#print axioms Pasting.source_horizontal
#print axioms Pasting.target_horizontal
#print axioms Pasting.identity_horizontal
#print axioms Pasting.map_horizontal
#print axioms Pasting.sourceZero_pack

example {G : GlobularSet} (n : Nat) (p q : Pasting (n + 1) G)
    (h : Pasting.target p = Pasting.source q) :
    Pasting.source (Pasting.vertical p q h) = Pasting.source p :=
  Pasting.source_vertical p q h

example {G : GlobularSet} (p q : Pasting 9 G)
    (h : Pasting.target p = Pasting.source q) :
    Pasting.target (Pasting.vertical p q h) = Pasting.target q :=
  Pasting.target_vertical p q h

#print axioms Chain.zipOver
#print axioms Chain.map_zipOver_left
#print axioms Chain.map_zipOver_right
#print axioms Chain.zipOver_append
#print axioms Pasting.vertical
#print axioms Pasting.verticalCell

example {G : GlobularSet} (n : Nat) (p : Pasting (n + 1) G) :
    Pasting.vertical (Pasting.identity (Pasting.source p)) p
      (Pasting.target_identity G (Pasting.source p)) = p := Pasting.vertical_left_unit p

example {G : GlobularSet} (p q r : Pasting 9 G)
    (h : Pasting.target p = Pasting.source q) (k : Pasting.target q = Pasting.source r) :
    Pasting.vertical (Pasting.vertical p q h) r ((Pasting.target_vertical p q h).trans k) =
      Pasting.vertical p (Pasting.vertical q r k) (h.trans (Pasting.source_vertical q r k).symm) :=
  Pasting.vertical_assoc p q r h k

#print axioms Chain.zipOver_map_left
#print axioms Chain.zipOver_map_right
#print axioms Chain.zipOver_assoc
#print axioms Pasting.vertical_left_unit
#print axioms Pasting.vertical_right_unit
#print axioms Pasting.vertical_assoc
#print axioms Pasting.pack_verticalFibre
#print axioms Pasting.vertical_horizontal_interchange

example {G : GlobularSet} (k n : Nat) (p q : Pasting (n + k + 1) G)
    (h : Pasting.targetAt k n p = Pasting.sourceAt k n q) :
    Pasting.sourceAt k n (Pasting.composeAt k n p q h) = Pasting.sourceAt k n p :=
  Pasting.sourceAt_composeAt k n p q h

example {G : GlobularSet} (p q r : Pasting 9 G)
    (h : Pasting.targetAt 4 4 p = Pasting.sourceAt 4 4 q)
    (j : Pasting.targetAt 4 4 q = Pasting.sourceAt 4 4 r) :
    Pasting.composeAt 4 4 (Pasting.composeAt 4 4 p q h) r
      ((Pasting.targetAt_composeAt 4 4 p q h).trans j) =
    Pasting.composeAt 4 4 p (Pasting.composeAt 4 4 q r j)
      (h.trans (Pasting.sourceAt_composeAt 4 4 q r j).symm) :=
  Pasting.composeAt_assoc 4 4 p q r h j

#print axioms Pasting.sourceAt_adjacent
#print axioms Pasting.targetAt_adjacent
#print axioms Pasting.composeAt
#print axioms Pasting.sourceAt_composeAt
#print axioms Pasting.targetAt_composeAt
#print axioms Pasting.sourceAt_identityAt
#print axioms Pasting.targetAt_identityAt
#print axioms Pasting.composeAt_left_unit
#print axioms Pasting.composeAt_right_unit
#print axioms Pasting.composeAt_assoc

example {G : GlobularSet} (k n : Nat) (p : Pasting (n + k + 1) G) :
    Pasting.sourceAt k n p = (Pasting.globular G).sourceIter (n := k) (n + 1)
      (Pasting.reindex (by omega) p) := Pasting.sourceAt_eq_sourceIter k n p

example {G : GlobularSet} (p : Pasting 9 G) :
    Pasting.targetAt 4 4 p = (Pasting.globular G).targetIter (n := 4) 5 p :=
  Pasting.targetAt_eq_targetIter 4 4 p

#print axioms Pasting.sourceAt_step
#print axioms Pasting.targetAt_step
#print axioms Pasting.sourceAt_globular
#print axioms Pasting.targetAt_globular
#print axioms Pasting.sourceAt_lower
#print axioms Pasting.targetAt_lower
#print axioms Pasting.sourceAt_eq_sourceIter
#print axioms Pasting.targetAt_eq_targetIter

example {G H : GlobularSet} (f : GlobularSet.Map G H) (k n : Nat)
    (p q : Pasting (n + k + 1) G) (h : Pasting.targetAt k n p = Pasting.sourceAt k n q) :
    Pasting.map f (Pasting.composeAt k n p q h) =
      Pasting.composeAt k n (Pasting.map f p) (Pasting.map f q)
        ((Pasting.targetAt_map k n f p).trans
          ((_root_.congrArg (Pasting.map f) h).trans (Pasting.sourceAt_map k n f q).symm)) :=
  Pasting.map_composeAt_natural k n f p q h

#print axioms Chain.map_zipOver
#print axioms Chain.mapAlong_zipOver
#print axioms Pasting.sourceAt_map
#print axioms Pasting.targetAt_map
#print axioms Pasting.map_identityAt
#print axioms Pasting.map_composeAt_natural
