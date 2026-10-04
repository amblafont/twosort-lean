module

public import CartexpAristotle.FamSlice
public import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
# From `FamSlice` to the slice of categories over `Fam`

To an object `F : C ⥤ Fam` of `FamSlice` we associate its *cartesian comma category*
`FamSlice.CartComma F`: an object is a cartesian morphism of families `f : F c ⟶ T` (for some
`c : C` and `T : Fam`), and a morphism `(c, T, f) ⟶ (c', T', f')` is a pair `u : c ⟶ c'`,
`v : T ⟶ T'` with `F u ≫ f' = f ≫ v` (the full subcategory of the comma category `F ↓ 𝟭 Fam`
on the cartesian morphisms). It comes with the projection `(c, T, f) ↦ T` to `Fam`, which makes
it an object of the slice category `Over (Cat.of Fam)`.

A morphism `(H, n) : (C, F) ⟶ (D, G)` of `FamSlice` (so `n : H ⋙ G ⟶ F` is pointwise cartesian)
induces the functor `(c, T, f) ↦ (H c, T, n_c ≫ f)`, which commutes strictly with the projections
to `Fam`. This gives the functor `FamSlice.toOver : FamSlice ⥤ Over (Cat.of Fam)`.

To make the cartesian comma category live in the same universe as `Fam` itself, we take the
underlying categories of `FamSlice` in `Cat.{w, w+1}`, the universe of `Fam.{w}`.
-/

@[expose] public section

universe w v u

open CategoryTheory

namespace FamSlice

variable (X : FamSlice.{w, v, u})

/-- An object of the cartesian comma category of `X = (C, F)`: an object `c : C`, a family `T`
and a cartesian morphism of families `F c ⟶ T`. -/
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

variable {Y : FamSlice.{w, v, u}}

/-- The functor between cartesian comma categories induced by a morphism `(H, n)` of `FamSlice`:
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

lemma map_id (X : FamSlice.{w, v, u}) : map (𝟙 X) = 𝟭 (CartComma X) := rfl

lemma map_comp {Z : FamSlice.{w, v, u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    map (f ≫ g) = map f ⋙ map g := rfl

end CartComma

/-- The cartesian comma category of `X = (C, F)`, as an object of the slice of categories
over `Fam`, via the projection `(c, T, f) ↦ T`. -/
def toOverObj (X : FamSlice.{w, w, w + 1}) : Over (Cat.of Fam.{w}) :=
  Over.mk ((CartComma.proj X).toCatHom : Cat.of (CartComma X) ⟶ Cat.of Fam.{w})

/-- The functor from `FamSlice` to the slice of categories over `Fam`, sending `F : C ⥤ Fam` to
its cartesian comma category, whose objects are the cartesian morphisms of families `F c ⟶ T`,
together with the projection `(c, T, f) ↦ T`. A morphism `(H, n)` is sent to the functor
`(c, T, f) ↦ (H c, T, n_c ≫ f)`, which commutes strictly with the projections. -/
def toOver : FamSlice.{w, w, w + 1} ⥤ Over (Cat.of Fam.{w}) where
  obj := toOverObj
  map g := Over.homMk (CartComma.map g).toCatHom rfl
  map_id _ := rfl
  map_comp _ _ := rfl

end FamSlice
