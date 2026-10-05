/-
Copyright (c) 2026 Lean Contributor. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Contributor
-/
import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks
import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
import Mathlib.CategoryTheory.Adjunction.Limits
import CartexpAristotle.Lexp

/-!
# The 2-category `CompExp` of complete categories with an exponentiable arrow

`CompExp` is the variant of the 2-category `Lexp` in which pullbacks are replaced by
(`w`-small) wide pullbacks:

* an object is a category with a terminal object and all wide pullbacks indexed by types in
  `Type w`, together with an exponentiable arrow;
* a morphism is a functor preserving the terminal object and these wide pullbacks, which preserves
  the exponentiable arrow and sends the chosen arrow of the domain to an arrow isomorphic to the
  chosen arrow of the codomain;
* 2-cells are the 2-cells of `Lexp` between the underlying `Lexp`-morphisms.

Since pullbacks are wide pullbacks indexed by a two-element type, every object of `CompExp` has an
underlying object of `Lexp` (`CompExp.toLexp`), and every morphism an underlying morphism of `Lexp`
(`CompExp.Hom.toHom`). For convenience the structures extend those of `Lexp`; the (redundant)
pullback fields can be filled in automatically from wide pullbacks with the constructors
`CompExp.of` and `CompExp.Hom.mk'`.

A category with a terminal object and all `w`-small wide pullbacks has all `w`-small limits
(`CompExp.hasLimitsOfSize`), so every object of `CompExp` is a complete category.

Like `Lexp`, `CompExp` is a strict 2-category (`CompExp.bicategory`, `CompExp.bicategory.strict`).
-/

open CategoryTheory Limits

universe w v u

/-- A category with a terminal object and all `w`-small wide pullbacks (hence all `w`-small limits,
see `CompExp.hasLimitsOfSize`), with a chosen exponentiable arrow.

This is an object of `Lexp` (the pullbacks of which are wide pullbacks) together with all
`w`-small wide pullbacks. -/
structure CompExp extends Lexp.{v, u} where
  [hasWidePullbacks : HasWidePullbacks.{w} carrier]

attribute [instance] CompExp.hasWidePullbacks

namespace CompExp

instance : CoeSort CompExp.{w, v, u} (Type u) := ⟨fun A => A.carrier⟩

/-- A functor preserving `w`-small wide pullbacks preserves pullbacks. -/
lemma preservesPullbacks_of_preservesWidePullbacks {C : Type*} [Category C] {D : Type*}
    [Category D] (F : C ⥤ D) [∀ J : Type w, PreservesLimitsOfShape (WidePullbackShape J) F] :
    PreservesLimitsOfShape WalkingCospan F :=
  preservesLimitsOfShape_of_equiv
    (WidePullbackShape.equivalenceOfEquiv _ (Equiv.ulift.{w} : ULift.{w} WalkingPair ≃ _)) F

/-- Build an object of `CompExp` from a category with a terminal object, all `w`-small wide
pullbacks and an exponentiable arrow (the pullbacks are derived from the wide pullbacks). -/
abbrev of (C : Type u) [Category.{v} C] [HasWidePullbacks.{w} C] [HasTerminal C] {X Y : C}
    (p : Y ⟶ X) [IsExpArr p] : CompExp.{w, v, u} where
  carrier := C
  arr := p

/-- A morphism of `CompExp`: a morphism of the underlying objects of `Lexp` whose functor also
preserves `w`-small wide pullbacks. -/
structure Hom (A B : CompExp.{w, v, u}) extends Lexp.Hom A.toLexp B.toLexp where
  [preservesWidePullbacks : ∀ J : Type w, PreservesLimitsOfShape (WidePullbackShape J) functor]

attribute [instance] Hom.preservesWidePullbacks

/-- Build a morphism of `CompExp` from a functor preserving the terminal object and `w`-small wide
pullbacks (the preservation of pullbacks is derived), preserving the exponentiable arrow. -/
abbrev Hom.mk' {A B : CompExp.{w, v, u}} (F : A.carrier ⥤ B.carrier)
    [∀ J : Type w, PreservesLimitsOfShape (WidePullbackShape J) F]
    [PreservesLimitsOfShape (Discrete PEmpty.{1}) F]
    (pres : letI := preservesPullbacks_of_preservesWidePullbacks.{w} F; FunctorPreserves A.arr F)
    (iso : Arrow.mk (F.map A.arr) ≅ Arrow.mk B.arr) : Hom A B :=
  letI := preservesPullbacks_of_preservesWidePullbacks.{w} F
  { functor := F
    preservesArr := pres
    iso := iso }

lemma Hom.ext {A B : CompExp.{w, v, u}} {F G : Hom A B} (h : F.toHom = G.toHom) : F = G := by
  cases F; cases G
  cases h
  rfl

/-- The identity morphism. -/
@[reducible] noncomputable def Hom.id (A : CompExp.{w, v, u}) : Hom A A where
  toHom := Lexp.Hom.id A.toLexp
  preservesWidePullbacks _ := inferInstanceAs (PreservesLimitsOfShape _ (𝟭 A.carrier))

/-- Composition of morphisms. -/
@[reducible] noncomputable def Hom.comp {A B C : CompExp.{w, v, u}} (F : Hom A B)
    (G : Hom B C) : Hom A C where
  toHom := Lexp.Hom.comp F.toHom G.toHom
  preservesWidePullbacks _ :=
    inferInstanceAs (PreservesLimitsOfShape _ (F.functor ⋙ G.functor))

noncomputable instance : CategoryStruct CompExp.{w, v, u} where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp

/-- The underlying morphism of `Lexp`, as a morphism of the category structure of `Lexp`. -/
abbrev Hom.toLexpHom {A B : CompExp.{w, v, u}} (F : A ⟶ B) : A.toLexp ⟶ B.toLexp := F.toHom

@[simp] lemma Hom.comp_toHom {A B C : CompExp.{w, v, u}} (F : A ⟶ B) (G : B ⟶ C) :
    (F ≫ G).toLexpHom = F.toLexpHom ≫ G.toLexpHom := rfl

@[simp] lemma Hom.id_toHom (A : CompExp.{w, v, u}) :
    (𝟙 A : A ⟶ A).toLexpHom = 𝟙 A.toLexp := rfl

@[simp] lemma Hom.comp_functor {A B C : CompExp.{w, v, u}} (F : A ⟶ B) (G : B ⟶ C) :
    (F ≫ G).functor = F.functor ⋙ G.functor := rfl

@[simp] lemma Hom.id_functor (A : CompExp.{w, v, u}) : (𝟙 A : A ⟶ A).functor = 𝟭 A.carrier :=
  rfl

/-- The 2-cells of `CompExp` are the 2-cells of `Lexp` between the underlying morphisms. -/
instance homCategory (A B : CompExp.{w, v, u}) : Category (A ⟶ B) where
  Hom F G := F.toLexpHom ⟶ G.toLexpHom
  id F := 𝟙 F.toLexpHom
  comp α β := (α ≫ β : _ ⟶ _)
  id_comp := fun f => Category.id_comp (obj := A.toLexp ⟶ B.toLexp) f
  comp_id := fun f => Category.comp_id (obj := A.toLexp ⟶ B.toLexp) f
  assoc := fun f g h => Category.assoc (obj := A.toLexp ⟶ B.toLexp) f g h

/-- The underlying 2-cell of `Lexp` of a 2-cell of `CompExp`. -/
abbrev Hom₂.toHom₂ {A B : CompExp.{w, v, u}} {F G : A ⟶ B} (η : F ⟶ G) : F.toLexpHom ⟶ G.toLexpHom := η

/-- The functor from a hom-category of `CompExp` to the corresponding hom-category of `Lexp`. -/
@[simps]
def homForget (A B : CompExp.{w, v, u}) : (A ⟶ B) ⥤ (A.toLexp ⟶ B.toLexp) where
  obj F := F.toLexpHom
  map η := η

/-- The functor between hom-categories is fully faithful: `CompExp` is a locally full
sub-2-category of `Lexp`. -/
def homForgetFullyFaithful (A B : CompExp.{w, v, u}) : (homForget A B).FullyFaithful where
  preimage η := η

lemma eqToHom_toHom₂ {A B : CompExp.{w, v, u}} {F G : A ⟶ B} (h : F = G) :
    Hom₂.toHom₂ (eqToHom h) = eqToHom (congrArg Hom.toLexpHom h) := by
  subst h
  rfl

/-- Isomorphisms of morphisms of `CompExp` from isomorphisms of the underlying morphisms of
`Lexp`. -/
def Hom.isoMk {A B : CompExp.{w, v, u}} {F G : A ⟶ B} (e : F.toLexpHom ≅ G.toLexpHom) : F ≅ G where
  hom := e.hom
  inv := e.inv
  hom_inv_id := e.hom_inv_id
  inv_hom_id := e.inv_hom_id

lemma Hom.isoMk_eq_eqToIso {A B : CompExp.{w, v, u}} {F G : A ⟶ B}
    (e : F.toLexpHom ≅ G.toLexpHom) (h : F = G) (he : e = eqToIso (congrArg Hom.toLexpHom h)) :
    Hom.isoMk e = eqToIso h := by
  subst h; subst he; rfl

/-- The isomorphism of underlying morphisms of `Lexp` of an isomorphism in `CompExp`. -/
def Hom.isoToHom {A B : CompExp.{w, v, u}} {F G : A ⟶ B} (e : F ≅ G) : F.toLexpHom ≅ G.toLexpHom where
  hom := e.hom
  inv := e.inv
  hom_inv_id := e.hom_inv_id
  inv_hom_id := e.inv_hom_id

/-- `CompExp` is a 2-category. -/
noncomputable instance bicategory : Bicategory.{max v u, max v u} CompExp.{w, v, u} where
  whiskerLeft F _ _ η := Lexp.Hom₂.whiskerLeft F.toLexpHom η
  whiskerRight η H := Lexp.Hom₂.whiskerRight η H.toLexpHom
  associator F G H := Hom.isoMk (F := (F ≫ G) ≫ H) (G := F ≫ G ≫ H)
    (Bicategory.associator F.toLexpHom G.toLexpHom H.toLexpHom)
  leftUnitor F := Hom.isoMk (F := 𝟙 _ ≫ F) (G := F) (Bicategory.leftUnitor F.toLexpHom)
  rightUnitor F := Hom.isoMk (F := F ≫ 𝟙 _) (G := F) (Bicategory.rightUnitor F.toLexpHom)
  whiskerLeft_id F G := Bicategory.whiskerLeft_id F.toLexpHom G.toLexpHom
  whiskerLeft_comp F _ _ _ η θ := Bicategory.whiskerLeft_comp F.toLexpHom η θ
  id_whiskerLeft {_ _ f g} η := Bicategory.id_whiskerLeft (f := Hom.toLexpHom f)
    (g := Hom.toLexpHom g) η
  comp_whiskerLeft F G _ _ η := Bicategory.comp_whiskerLeft F.toLexpHom G.toLexpHom η
  id_whiskerRight F G := Bicategory.id_whiskerRight F.toLexpHom G.toLexpHom
  comp_whiskerRight η θ H := Bicategory.comp_whiskerRight η θ H.toLexpHom
  whiskerRight_id {_ _ f g} η := Bicategory.whiskerRight_id (f := Hom.toLexpHom f)
    (g := Hom.toLexpHom g) η
  whiskerRight_comp η G H := Bicategory.whiskerRight_comp η G.toLexpHom H.toLexpHom
  whisker_assoc F _ _ η H := Bicategory.whisker_assoc F.toLexpHom η H.toLexpHom
  whisker_exchange {_ _ _ f g h i} η θ := Bicategory.whisker_exchange (f := Hom.toLexpHom f)
    (g := Hom.toLexpHom g) (h := Hom.toLexpHom h) (i := Hom.toLexpHom i) η θ
  pentagon F G H I := Bicategory.pentagon F.toLexpHom G.toLexpHom H.toLexpHom I.toLexpHom
  triangle F G := Bicategory.triangle F.toLexpHom G.toLexpHom

/-- `CompExp` is a strict 2-category. -/
instance bicategory.strict : Bicategory.Strict CompExp.{w, v, u} where
  id_comp F := Hom.ext (Bicategory.Strict.id_comp (Hom.toLexpHom F))
  comp_id F := Hom.ext (Bicategory.Strict.comp_id (Hom.toLexpHom F))
  assoc F G H := Hom.ext (Bicategory.Strict.assoc (Hom.toLexpHom F) (Hom.toLexpHom G) (Hom.toLexpHom H))
  leftUnitor_eqToIso F :=
    Hom.isoMk_eq_eqToIso _ _ (Bicategory.Strict.leftUnitor_eqToIso (Hom.toLexpHom F))
  rightUnitor_eqToIso F :=
    Hom.isoMk_eq_eqToIso _ _ (Bicategory.Strict.rightUnitor_eqToIso (Hom.toLexpHom F))
  associator_eqToIso F G H :=
    Hom.isoMk_eq_eqToIso _ _ (Bicategory.Strict.associator_eqToIso (Hom.toLexpHom F)
      (Hom.toLexpHom G) (Hom.toLexpHom H))

noncomputable instance category : Category.{max v u} CompExp.{w, v, u} :=
  StrictBicategory.category CompExp.{w, v, u}

/-! ### Completeness -/

/-- **Every object of `CompExp` is complete**: a category with a terminal object and all `w`-small
wide pullbacks has all `w`-small limits. -/
instance hasLimitsOfSize (A : CompExp.{w, v, u}) : HasLimitsOfSize.{w, w} A.carrier :=
  Adjunction.has_limits_of_equivalence (Over.equivalenceOfIsTerminal terminalIsTerminal).inverse

end CompExp
