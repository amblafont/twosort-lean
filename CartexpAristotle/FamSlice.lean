module

public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.CategoryTheory.Whiskering

/-!
# The cartesian colax slice of categories over `Fam`

* `Fam` is the category of families of types: an object is an index type `I` together with a
  family `X : I → Type`, and a morphism `(I, X) ⟶ (J, Y)` is a map `f : I → J` on the base
  together with maps `X i → Y (f i)` on the fibres.
* A morphism of families is *cartesian* (`Fam.Hom.IsCartesian`) if each of its maps between
  fibres `X i → Y (f i)` is the identity function (in particular `X i = Y (f i)`). The map on base
  types is arbitrary.
* `FamSlice` is the cartesian colax slice category of categories over `Fam`.  An object is a
  category `C` with a functor `F : C ⥤ Fam`.  A morphism from `F : C ⥤ Fam` to `G : D ⥤ Fam` is a
  functor `H : C ⥤ D` together with a natural transformation `n : H ⋙ G ⟶ F` all of whose
  components are cartesian.
-/

@[expose] public section

universe w v u

open CategoryTheory

/-- A family of types: an index type together with a type for every index. -/
structure Fam where
  /-- The base (index) type. -/
  base : Type w
  /-- The fibre over each index. -/
  fiber : base → Type w

namespace Fam

/-- A morphism of families: a map on base types, and maps between the corresponding fibres. -/
@[ext]
structure Hom (X Y : Fam.{w}) where
  /-- The map on base types. -/
  base : X.base → Y.base
  /-- The maps on fibres. -/
  fiber : ∀ i, X.fiber i → Y.fiber (base i)

instance : Category Fam.{w} where
  Hom := Hom
  id X := ⟨id, fun _ x => x⟩
  comp f g := ⟨g.base ∘ f.base, fun i x => g.fiber (f.base i) (f.fiber i x)⟩

@[simp] lemma id_base (X : Fam.{w}) : (𝟙 X : Hom X X).base = id := rfl
@[simp] lemma id_fiber (X : Fam.{w}) (i : X.base) (x : X.fiber i) :
    (𝟙 X : Hom X X).fiber i x = x := rfl
@[simp] lemma comp_base {X Y Z : Fam.{w}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g : Hom X Z).base = (g : Hom Y Z).base ∘ (f : Hom X Y).base := rfl
@[simp] lemma comp_fiber {X Y Z : Fam.{w}} (f : X ⟶ Y) (g : Y ⟶ Z) (i : X.base)
    (x : X.fiber i) :
    (f ≫ g : Hom X Z).fiber i x =
      (g : Hom Y Z).fiber ((f : Hom X Y).base i) ((f : Hom X Y).fiber i x) := rfl

/-- A morphism of families is *cartesian* if each of its maps between fibres is the identity
function. The map on base types is arbitrary. Since the fibres `X.fiber i` and
`Y.fiber (f.base i)` are a priori different types, this is stated as: for every index `i` the two
fibres are equal, and along this equality the fibre map is the identity. -/
def Hom.IsCartesian {X Y : Fam.{w}} (f : X ⟶ Y) : Prop :=
  ∀ i, ∃ h : X.fiber i = Y.fiber ((f : Hom X Y).base i),
    ∀ x, (f : Hom X Y).fiber i x = cast h x

lemma Hom.isCartesian_id (X : Fam.{w}) : Hom.IsCartesian (𝟙 X) :=
  fun _ => ⟨rfl, fun _ => rfl⟩

lemma Hom.IsCartesian.comp {X Y Z : Fam.{w}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : f.IsCartesian) (hg : g.IsCartesian) : (f ≫ g).IsCartesian := by
  intro i
  obtain ⟨h₁, hf⟩ := hf i
  obtain ⟨h₂, hg⟩ := hg ((f : Hom X Y).base i)
  refine ⟨h₁.trans h₂, fun x => ?_⟩
  simp only [comp_fiber, hf, hg, cast_cast]

end Fam

/-- A natural transformation into a `Fam`-valued functor is *pointwise cartesian* if each of its
components is a cartesian morphism of families. -/
def CategoryTheory.NatTrans.IsPointwiseCartesian {C : Type u} [Category.{v} C]
    {F G : C ⥤ Fam.{w}} (n : F ⟶ G) : Prop :=
  ∀ c, (n.app c).IsCartesian

/-- An object of the cartesian colax slice over `Fam`: a category equipped with a functor
to `Fam`. -/
structure FamSlice where
  /-- The underlying category. -/
  cat : Cat.{v, u}
  /-- The functor to `Fam`. -/
  F : cat ⥤ Fam.{w}

namespace FamSlice

/-- A morphism `(C, F) ⟶ (D, G)` in the cartesian colax slice over `Fam`: a functor `H : C ⥤ D`
together with a pointwise cartesian natural transformation `H ⋙ G ⟶ F`. -/
structure Hom (X Y : FamSlice.{w, v, u}) where
  /-- The functor between the underlying categories. -/
  functor : X.cat ⥤ Y.cat
  /-- The natural transformation `H ⋙ G ⟶ F`. -/
  nat : functor ⋙ Y.F ⟶ X.F
  /-- Every component of the natural transformation is cartesian. -/
  isPointwiseCartesian : nat.IsPointwiseCartesian

/-- The identity morphism. -/
def Hom.id (X : FamSlice.{w, v, u}) : Hom X X where
  functor := 𝟭 X.cat
  nat := 𝟙 X.F
  isPointwiseCartesian _ := Fam.Hom.isCartesian_id _

/-- Composition of morphisms: functors compose, and the natural transformations are pasted
as `whiskerLeft H m ≫ n`. -/
def Hom.comp {X Y Z : FamSlice.{w, v, u}} (f : Hom X Y) (g : Hom Y Z) : Hom X Z where
  functor := f.functor ⋙ g.functor
  nat := Functor.whiskerLeft f.functor g.nat ≫ f.nat
  isPointwiseCartesian c :=
    (g.isPointwiseCartesian (f.functor.obj c)).comp (f.isPointwiseCartesian c)

instance : Category FamSlice.{w, v, u} where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp f := by
    rcases f with ⟨H, n, hn⟩
    simp only [Hom.comp, Hom.id]
    congr 1
  comp_id f := by
    rcases f with ⟨H, n, hn⟩
    simp only [Hom.comp, Hom.id]
    congr 1
  assoc f g h := by
    simp only [Hom.comp]
    congr 1

end FamSlice
