/-
Copyright (c) 2026 Lean Contributor. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Contributor
-/
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import CartexpAristotle.PartialExponentiability

/-!
# The 2-category of categories with a chosen exponentiable arrow

Objects are categories with pullbacks and a terminal object, equipped with an exponentiable
arrow (`IsExpArr`). Morphisms are functors preserving pullbacks and the terminal object, which
preserve the exponentiable arrow (`FunctorPreserves`) and send the chosen arrow of the domain to
an arrow isomorphic to the chosen arrow of the codomain. 2-cells are natural transformations
between the underlying functors that are compatible with the chosen isomorphisms (`Hom₂`),
making `Lexp` a strict 2-category.

## References

* [Paper, §2.2, Thm. `thm:uemura`] (Uemura's bi-initiality theorem) defines the 2-category
  `Lexp`: objects are `Lexp`-categories (a Lex-category with an exponentiable morphism
  `p : Y → X`), morphisms are `Lexp`-functors (preserving finite limits, `p` up to isomorphism, and
  pushforwards along `p`), and 2-cells are natural transformations. Here 2-cells are additionally
  required to be compatible with the chosen isomorphisms `F(p) ≅ p'` (`Hom₂`).
* [Paper, §2.1, Def. `def:exp-mor`] (exponentiable morphisms) is `IsExpArr`, and
  [Paper, §2.1, Def. `def:preserves-pushforwards`] (preservation of pushforwards), in the
  equivalent form of [Paper, §2.1, Lemma `lem:preservation_pushforward`], is `FunctorPreserves`;
  both are in `CartexpAristotle.PartialExponentiability`.
-/

open CategoryTheory Limits

universe v u

/-- A category with pullbacks and a terminal object, with a chosen exponentiable arrow.

[Paper, §2.2, Thm. `thm:uemura`]: a `Lexp`-category. -/
structure Lexp where
  /-- The underlying type of objects. -/
  carrier : Type u
  [cat : Category.{v} carrier]
  [hasPullbacks : HasPullbacks carrier]
  [hasTerminal : HasTerminal carrier]
  {dom cod : carrier}
  /-- The chosen exponentiable arrow. -/
  arr : dom ⟶ cod
  [isExpArr : IsExpArr arr]

attribute [instance] Lexp.cat Lexp.hasPullbacks Lexp.hasTerminal
  Lexp.isExpArr

namespace Lexp

instance : CoeSort Lexp.{v, u} (Type u) := ⟨carrier⟩

/-- Two proofs that a functor preserves exponentiable arrows are equal. -/
instance {C : Type*} [Category C] {D : Type*} [Category D] {X Y : C} (u : Y ⟶ X) (F : C ⥤ D)
    [PreservesLimitsOfShape WalkingCospan F] : Subsingleton (FunctorPreserves u F) where
  allEq p₀ p₁ := by
    refine isProp_FunctorPreserves u F p₀ p₁ fun c d univ d' f Kuf g => ?_
    let U₀ := p₀.functor_preserves d univ
    let U₁ := p₁.functor_preserves d univ
    change U₀.mor g = U₁.mor g
    let _ := U₁
    exact mor_unique (d1 := functor_on F d) g _ (U₀.isSlice g) (U₀.comm g)

/-- A morphism of `Lexp`: a functor preserving pullbacks and the terminal object, preserving
the exponentiable arrow, together with an isomorphism between the image of the chosen arrow and
the target's chosen arrow.

[Paper, §2.2, Thm. `thm:uemura`]: a `Lexp`-functor. -/
structure Hom (A B : Lexp.{v, u}) where
  /-- The underlying functor. -/
  functor : A ⥤ B
  [preservesPullbacks : PreservesLimitsOfShape WalkingCospan functor]
  [preservesTerminal : PreservesLimitsOfShape (Discrete PEmpty.{1}) functor]
  [preservesArr : FunctorPreserves A.arr functor]
  iso : Arrow.mk (functor.map A.arr) ≅ Arrow.mk B.arr

attribute [instance] Hom.preservesPullbacks Hom.preservesTerminal Hom.preservesArr

lemma Hom.ext' {A B : Lexp.{v, u}} {F G : Hom A B} (h : F.functor = G.functor)
    (hl : F.iso.hom.left = eqToHom (congrArg (fun H => H.obj A.dom) h) ≫ G.iso.hom.left)
    (hr : F.iso.hom.right = eqToHom (congrArg (fun H => H.obj A.cod) h) ≫ G.iso.hom.right) :
    F = G := by
  cases F; cases G
  cases h
  congr 1
  · exact Subsingleton.elim _ _
  · exact Iso.ext (CommaMorphism.ext (by simpa using hl) (by simpa using hr))

/-- The identity morphism. -/
@[reducible] noncomputable def Hom.id (A : Lexp.{v, u}) : Hom A A where
  functor := 𝟭 A
  iso := Iso.refl _

/-- Composition of morphisms. -/
@[reducible] noncomputable def Hom.comp {A B C : Lexp.{v, u}} (F : Hom A B)
    (G : Hom B C) : Hom A C :=
  have := functor_preserves_iso B.arr (F.functor.map A.arr) G.functor F.iso
  { functor := F.functor ⋙ G.functor
    preservesArr := functor_preserves_comp A.arr F.functor G.functor
    iso := G.functor.mapArrow.mapIso F.iso ≪≫ G.iso }

noncomputable instance : CategoryStruct Lexp.{v, u} where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp

/-- A 2-cell between morphisms of `Lexp`: a natural transformation between the underlying
functors, compatible with the isomorphisms to the chosen arrow of the target.

[Paper, §2.2, Thm. `thm:uemura`]: a 2-cell of `Lexp` (compatible with the chosen isomorphisms). -/
@[ext] structure Hom₂ {A B : Lexp.{v, u}} (F G : A ⟶ B) where
  /-- The underlying natural transformation. -/
  nat : F.functor ⟶ G.functor
  left_comm : nat.app A.dom ≫ G.iso.hom.left = F.iso.hom.left
  right_comm : nat.app A.cod ≫ G.iso.hom.right = F.iso.hom.right

instance homCategory (A B : Lexp.{v, u}) : Category (A ⟶ B) where
  Hom F G := Hom₂ F G
  id F := ⟨𝟙 F.functor, by simp, by simp⟩
  comp α β := ⟨α.nat ≫ β.nat, by simp [← α.left_comm, ← β.left_comm],
    by simp [← α.right_comm, ← β.right_comm]⟩

/-- Isomorphisms of morphisms from natural isomorphisms of the underlying functors compatible
with the isomorphisms to the chosen arrow of the target. -/
def Hom.isoMk {A B : Lexp.{v, u}} {F G : A ⟶ B} (e : F.functor ≅ G.functor)
    (hl : e.hom.app A.dom ≫ G.iso.hom.left = F.iso.hom.left)
    (hr : e.hom.app A.cod ≫ G.iso.hom.right = F.iso.hom.right) : F ≅ G where
  hom := ⟨e.hom, hl, hr⟩
  inv := ⟨e.inv, by rw [← hl]; simp, by rw [← hr]; simp⟩
  hom_inv_id := Hom₂.ext e.hom_inv_id
  inv_hom_id := Hom₂.ext e.inv_hom_id

@[simp] lemma Hom₂.id_nat {A B : Lexp.{v, u}} (F : A ⟶ B) :
    (𝟙 F : F ⟶ F).nat = 𝟙 F.functor := rfl

@[simp] lemma Hom₂.comp_nat {A B : Lexp.{v, u}} {F G H : A ⟶ B} (α : F ⟶ G) (β : G ⟶ H) :
    (α ≫ β).nat = α.nat ≫ β.nat := rfl

@[simp] lemma Hom₂.isoMk_hom_nat {A B : Lexp.{v, u}} {F G : A ⟶ B} (e : F.functor ≅ G.functor)
    (hl hr) : (Hom.isoMk e hl hr).hom.nat = e.hom := rfl

@[simp] lemma Hom₂.isoMk_inv_nat {A B : Lexp.{v, u}} {F G : A ⟶ B} (e : F.functor ≅ G.functor)
    (hl hr) : (Hom.isoMk e hl hr).inv.nat = e.inv := rfl

@[simp] lemma Hom₂.eqToHom_nat {A B : Lexp.{v, u}} {F G : A ⟶ B} (h : F = G) :
    (eqToHom h).nat = eqToHom (congrArg Hom.functor h) := by
  subst h
  rfl

lemma Hom.isoMk_eq_eqToIso {A B : Lexp.{v, u}} {F G : A ⟶ B} (e : F.functor ≅ G.functor)
    (hl hr) (h : F = G) (he : e.hom = eqToHom (congrArg Hom.functor h)) :
    Hom.isoMk e hl hr = eqToIso h := by
  subst h
  exact Iso.ext (Hom₂.ext he)

@[simp] lemma Hom.comp_functor {A B C : Lexp.{v, u}} (F : A ⟶ B) (G : B ⟶ C) :
    (F ≫ G).functor = F.functor ⋙ G.functor := rfl

@[simp] lemma Hom.id_functor (A : Lexp.{v, u}) : (𝟙 A : A ⟶ A).functor = 𝟭 A := rfl

@[simp] lemma Hom.comp_iso_hom_left {A B C : Lexp.{v, u}} (F : A ⟶ B) (G : B ⟶ C) :
    (F ≫ G).iso.hom.left = G.functor.map F.iso.hom.left ≫ G.iso.hom.left := rfl

@[simp] lemma Hom.comp_iso_hom_right {A B C : Lexp.{v, u}} (F : A ⟶ B) (G : B ⟶ C) :
    (F ≫ G).iso.hom.right = G.functor.map F.iso.hom.right ≫ G.iso.hom.right := rfl

@[simp] lemma Hom.id_iso_hom_left (A : Lexp.{v, u}) : (𝟙 A : A ⟶ A).iso.hom.left = 𝟙 _ := rfl

@[simp] lemma Hom.id_iso_hom_right (A : Lexp.{v, u}) :
    (𝟙 A : A ⟶ A).iso.hom.right = 𝟙 _ := rfl

/-- Whiskering a 2-cell on the left by a morphism. -/
def Hom₂.whiskerLeft {A B C : Lexp.{v, u}} (F : A ⟶ B) {G H : B ⟶ C} (η : G ⟶ H) :
    F ≫ G ⟶ F ≫ H :=
  ⟨Functor.whiskerLeft F.functor η.nat, by
    simp [← η.left_comm], by simp [← η.right_comm]⟩

@[simp] lemma Hom₂.whiskerLeft_nat {A B C : Lexp.{v, u}} (F : A ⟶ B) {G H : B ⟶ C}
    (η : G ⟶ H) : (Hom₂.whiskerLeft F η).nat = Functor.whiskerLeft F.functor η.nat := rfl

/-- Whiskering a 2-cell on the right by a morphism. -/
def Hom₂.whiskerRight {A B C : Lexp.{v, u}} {F G : A ⟶ B} (η : F ⟶ G) (H : B ⟶ C) :
    F ≫ H ⟶ G ≫ H :=
  ⟨Functor.whiskerRight η.nat H.functor, by
    simp [← η.left_comm], by simp [← η.right_comm]⟩

@[simp] lemma Hom₂.whiskerRight_nat {A B C : Lexp.{v, u}} {F G : A ⟶ B} (η : F ⟶ G)
    (H : B ⟶ C) : (Hom₂.whiskerRight η H).nat = Functor.whiskerRight η.nat H.functor := rfl

/-- `Lexp` is a 2-category. -/
noncomputable instance bicategory : Bicategory.{max v u, max v u} Lexp.{v, u} where
  whiskerLeft F _ _ η := Hom₂.whiskerLeft F η
  whiskerRight η H := Hom₂.whiskerRight η H
  associator F G H := Hom.isoMk (F := (F ≫ G) ≫ H) (G := F ≫ G ≫ H)
    (Functor.associator F.functor G.functor H.functor) (by simp) (by simp)
  leftUnitor F := Hom.isoMk (F := 𝟙 _ ≫ F) (G := F) (Functor.leftUnitor F.functor)
    (by simp) (by simp)
  rightUnitor F := Hom.isoMk (F := F ≫ 𝟙 _) (G := F) (Functor.rightUnitor F.functor)
    (by simp) (by simp)
  id_whiskerLeft := by intros; refine Hom₂.ext (NatTrans.ext (funext fun x => ?_)); simp
  comp_whiskerLeft := by intros; refine Hom₂.ext (NatTrans.ext (funext fun x => ?_)); simp
  id_whiskerRight := by intros; refine Hom₂.ext (NatTrans.ext (funext fun x => ?_)); simp
  comp_whiskerRight := by intros; refine Hom₂.ext (NatTrans.ext (funext fun x => ?_)); simp
  whiskerRight_id := by intros; refine Hom₂.ext (NatTrans.ext (funext fun x => ?_)); simp
  whiskerRight_comp := by intros; refine Hom₂.ext (NatTrans.ext (funext fun x => ?_)); simp
  whisker_assoc := by intros; refine Hom₂.ext (NatTrans.ext (funext fun x => ?_)); simp
  whisker_exchange := by intros; refine Hom₂.ext (NatTrans.ext (funext fun x => ?_)); simp
  pentagon := by intros; refine Hom₂.ext (NatTrans.ext (funext fun x => ?_)); simp
  triangle := by intros; refine Hom₂.ext (NatTrans.ext (funext fun x => ?_)); simp

/-- `Lexp` is a strict 2-category. -/
instance bicategory.strict : Bicategory.Strict Lexp.{v, u} where
  id_comp _ := Hom.ext' rfl (by simp) (by simp)
  comp_id _ := Hom.ext' rfl (by simp) (by simp)
  assoc _ _ _ := Hom.ext' rfl (by simp) (by simp)
  leftUnitor_eqToIso F :=
    Hom.isoMk_eq_eqToIso _ _ _ _ (by ext; simp)
  rightUnitor_eqToIso F :=
    Hom.isoMk_eq_eqToIso _ _ _ _ (by ext; simp)
  associator_eqToIso F G H :=
    Hom.isoMk_eq_eqToIso _ _ _ _ (by ext; simp)

noncomputable instance category : Category.{max v u} Lexp.{v, u} :=
  StrictBicategory.category Lexp.{v, u}

end Lexp
