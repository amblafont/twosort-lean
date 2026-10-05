module

public import CartexpAristotle.ColaxSliceCart
public import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
# From `ColaxSliceCart` to the slice of categories over `Fam`

To an object `F : C ⥤ Fam` of `ColaxSliceCart` we associate its *cartesian comma category*
`ColaxSliceCart.CartComma F`: an object is a cartesian morphism of families `f : F c ⟶ T` (for some
`c : C` and `T : Fam`), and a morphism `(c, T, f) ⟶ (c', T', f')` is a pair `u : c ⟶ c'`,
`v : T ⟶ T'` with `F u ≫ f' = f ≫ v` (the full subcategory of the comma category `F ↓ 𝟭 Fam`
on the cartesian morphisms). It comes with the projection `(c, T, f) ↦ T` to `Fam`, which makes
it an object of the slice category `Over (Cat.of Fam)`.

A morphism `(H, n) : (C, F) ⟶ (D, G)` of `ColaxSliceCart` (so `n : H ⋙ G ⟶ F` is pointwise cartesian)
induces the functor `(c, T, f) ↦ (H c, T, n_c ≫ f)`, which commutes strictly with the projections
to `Fam`. This gives the functor `ColaxSliceCart.toOver : ColaxSliceCart ⥤ Over (Cat.of Fam)`.

To make the cartesian comma category live in the same universe as `Fam` itself, we take the
underlying categories of `ColaxSliceCart` in `Cat.{w, w+1}`, the universe of `Fam.{w}`.

## References

* [Paper, §4.2, Thm. `thm:characterisation-models-two-sortification`]: `CartComma F` is the
  full subcategory `F/_c Fam` of the comma category `F/Fam` spanned by the cartesian morphisms.
* [Paper, §4.2, Prop. `prop:semantic-twosort-functor`]: the mapping `F ↦ (F/_c Fam → Fam)` extends to
  a functor `CAT //_c Fam → CAT/Fam` (`ColaxSliceCart.toOver`). That it is a `Lexp`-functor is
  proved in `CartexpAristotle.SemanticTwoSortFunctor`.
-/

@[expose] public section

universe w v u

open CategoryTheory

namespace ColaxSliceCart

variable (X : ColaxSliceCart.{w, v, u})

/-- An object of the cartesian comma category of `X = (C, F)`: an object `c : C`, a family `T`
and a cartesian morphism of families `F c ⟶ T`.

[Paper, §4.2, Thm. `thm:characterisation-models-two-sortification`]: `F/_c Fam`. -/
structure CartComma where
  /-- The object of the underlying category. -/
  obj : X.cat
  /-- The target family. -/
  tgt : Fam.{w}
  /-- The cartesian morphism `F c ⟶ T`. -/
  hom : X.F.obj obj ⟶ tgt
  /-- The morphism is cartesian. -/
  isCartesian : hom.IsCartesian

namespace CartComma

variable {X}

/-- A morphism of the cartesian comma category: a commutative square
`F c ⟶ T`, `F c' ⟶ T'` with sides `F u` and `v`. -/
@[ext]
structure Hom (a b : CartComma X) where
  /-- The morphism in the underlying category. -/
  left : a.obj ⟶ b.obj
  /-- The morphism between target families. -/
  right : a.tgt ⟶ b.tgt
  /-- The square commutes. -/
  w : X.F.map left ≫ b.hom = a.hom ≫ right := by cat_disch

attribute [reassoc] Hom.w

instance : Category (CartComma X) where
  Hom := Hom
  id a := ⟨𝟙 _, 𝟙 _, by simp⟩
  comp f g := ⟨f.left ≫ g.left, f.right ≫ g.right, by
    rw [Functor.map_comp, Category.assoc, g.w, f.w_assoc]⟩

@[simp] lemma id_left (a : CartComma X) : (𝟙 a : Hom a a).left = 𝟙 _ := rfl
@[simp] lemma id_right (a : CartComma X) : (𝟙 a : Hom a a).right = 𝟙 _ := rfl
@[simp] lemma comp_left {a b c : CartComma X} (f : a ⟶ b) (g : b ⟶ c) :
    (f ≫ g : Hom a c).left = (f : Hom a b).left ≫ (g : Hom b c).left := rfl
@[simp] lemma comp_right {a b c : CartComma X} (f : a ⟶ b) (g : b ⟶ c) :
    (f ≫ g : Hom a c).right = (f : Hom a b).right ≫ (g : Hom b c).right := rfl

variable (X) in
/-- The projection `(c, T, f) ↦ T` of the cartesian comma category to `Fam`. -/
def proj : CartComma X ⥤ Fam.{w} where
  obj a := a.tgt
  map f := (f : Hom _ _).right

variable {Y : ColaxSliceCart.{w, v, u}}

/-- The functor between cartesian comma categories induced by a morphism `(H, n)` of `ColaxSliceCart`:
`(c, T, f) ↦ (H c, T, n_c ≫ f)`. -/
def map (g : X ⟶ Y) : CartComma X ⥤ CartComma Y where
  obj a := ⟨g.functor.obj a.obj, a.tgt, g.nat.app a.obj ≫ a.hom,
    (g.isPointwiseCartesian a.obj).comp a.isCartesian⟩
  map {a b} f := ⟨g.functor.map (f : Hom a b).left, (f : Hom a b).right, by
    have h := g.nat.naturality f.left
    simp only [Functor.comp_map] at h
    change Y.F.map (g.functor.map f.left) ≫ g.nat.app b.obj ≫ b.hom = _
    rw [← Category.assoc, h, Category.assoc, f.w, Category.assoc]⟩

lemma map_proj (g : X ⟶ Y) : map g ⋙ proj Y = proj X := rfl

lemma map_id (X : ColaxSliceCart.{w, v, u}) : map (𝟙 X) = 𝟭 (CartComma X) := rfl

lemma map_comp {Z : ColaxSliceCart.{w, v, u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    map (f ≫ g) = map f ⋙ map g := rfl

end CartComma

/-- The cartesian comma category of `X = (C, F)`, as an object of the slice of categories
over `Fam`, via the projection `(c, T, f) ↦ T`. -/
def toOverObj (X : ColaxSliceCart.{w, w, w + 1}) : Over (Cat.of Fam.{w}) :=
  Over.mk ((CartComma.proj X).toCatHom : Cat.of (CartComma X) ⟶ Cat.of Fam.{w})

/-- The functor from `ColaxSliceCart` to the slice of categories over `Fam`, sending `F : C ⥤ Fam` to
its cartesian comma category, whose objects are the cartesian morphisms of families `F c ⟶ T`,
together with the projection `(c, T, f) ↦ T`. A morphism `(H, n)` is sent to the functor
`(c, T, f) ↦ (H c, T, n_c ≫ f)`, which commutes strictly with the projections.

[Paper, §4.2, Prop. `prop:semantic-twosort-functor`]: `F ↦ (F/_c Fam → Fam)`. -/
def toOver : ColaxSliceCart.{w, w, w + 1} ⥤ Over (Cat.of Fam.{w}) where
  obj := toOverObj
  map g := Over.homMk (CartComma.map g).toCatHom rfl
  map_id _ := rfl
  map_comp _ _ := rfl

end ColaxSliceCart
