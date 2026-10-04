/-
Copyright (c) 2026 Lean Contributor. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Contributor
-/
import CartexpAristotle.TwoSortification
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected

/-!
# The counit of the two-sortification functor

Let `FinGat` be a bi-initial object of `ExpArrCat`, with chosen exponentiable arrow
`p : Y ⟶ X`, and let `Φ` be the endofunctor of `ExpArrCat` from `ExpArrEndofunctor`. The chosen
arrow of `Φ FinGat = FinGat / P X` is the pullback `p' : Y' ⟶ Y ×_X P X` of `p` along the counit
`ε : Y ×_X P X ⟶ X`:

```
Y' ──fst──▶ Y
│p'         │p
▼           ▼
Y ×_X P X ─ε─▶ X
```

We define a natural transformation (`ExpArrCat.twoSortCounit`)
`twoSortification ⋙ Over.forget (P X) ⟶ 𝟭 FinGat`
whose components at `Y` and `X` are the horizontal sides of this pullback square, transported
along the identification of the image of `p` under the two-sortification functor with `p'`.
It is obtained from `ExpArrCat.IsBiInitial.existsUnique_natTrans`, and is unique with this
property (`ExpArrCat.twoSortCounit_unique`).
-/

open CategoryTheory Limits SliceExp

universe u

namespace ExpArrCat

/-- The pullback square defining the chosen arrow of `Φ A`, as a morphism of arrows from
`p' : Y' ⟶ Y ×_X P X` to `p : Y ⟶ X`. -/
noncomputable def ΦchosenSquare (A : ExpArrCat.{u, u}) : Arrow.mk (su' A.arr) ⟶ Arrow.mk A.arr :=
  Arrow.homMk (pullback.fst A.arr (sE A.arr)) (sE A.arr) (shpb A.arr).w

@[simp] lemma ΦchosenSquare_left (A : ExpArrCat.{u, u}) :
    (ΦchosenSquare A).left = pullback.fst A.arr (sE A.arr) := rfl

@[simp] lemma ΦchosenSquare_right (A : ExpArrCat.{u, u}) :
    (ΦchosenSquare A).right = sE A.arr := rfl

variable {FinGat : ExpArrCat.{u, u}} (hFinGat : IsBiInitial FinGat)

/-- The composite of the two-sortification functor `FinGat ⥤ Φ FinGat = FinGat / P X` with the
projection `FinGat / P X ⥤ FinGat`. -/
noncomputable abbrev twoSortProj : FinGat.carrier ⥤ FinGat.carrier :=
  (twoSortification hFinGat).functor ⋙ Over.forget (sZ FinGat.arr)

instance : PreservesLimitsOfShape WalkingCospan (twoSortProj hFinGat) := by
  haveI : PreservesLimitsOfShape WalkingCospan
      ((twoSortification hFinGat).functor) := (twoSortification hFinGat).preservesPullbacks
  haveI : PreservesLimitsOfShape WalkingCospan (Over.forget (sZ FinGat.arr)) :=
    Over.preservesLimitsOfShape_forget_of_isConnected
  exact comp_preservesLimitsOfShape _ _

/-- The square from the image of `p` under `twoSortProj` to `p`: the image under the projection of
the identification of the image of `p` with `p'`, followed by the pullback square defining `p'`. -/
noncomputable def twoSortSquare :
    Arrow.mk ((twoSortProj hFinGat).map FinGat.arr) ⟶ Arrow.mk FinGat.arr :=
  Arrow.homMk ((twoSortification hFinGat).iso.hom.left.left ≫ (ΦchosenSquare FinGat).left)
    ((twoSortification hFinGat).iso.hom.right.left ≫ (ΦchosenSquare FinGat).right) (by
      have h := congrArg CommaMorphism.left (twoSortification hFinGat).iso.hom.w
      have h' := (ΦchosenSquare FinGat).w
      simp only [Arrow.mk_left, Arrow.mk_right, Arrow.mk_hom, Functor.id_obj, Functor.id_map]
        at h h' ⊢
      erw [Over.comp_left, Over.comp_left] at h
      rw [Category.assoc, h', ← Category.assoc, ← Category.assoc]
      congr 1)

lemma twoSortSquare_left : (twoSortSquare hFinGat).left =
    (twoSortification hFinGat).iso.hom.left.left ≫ pullback.fst FinGat.arr (sE FinGat.arr) := rfl

lemma twoSortSquare_right : (twoSortSquare hFinGat).right =
    (twoSortification hFinGat).iso.hom.right.left ≫ sE FinGat.arr := rfl

/-- The square `twoSortSquare` is a pullback square. -/
lemma twoSortSquare_isPullback :
    IsPullback (twoSortSquare hFinGat).left ((twoSortProj hFinGat).map FinGat.arr) FinGat.arr
      (twoSortSquare hFinGat).right := by
  let e := (Over.forget (sZ FinGat.arr)).mapArrow.mapIso (twoSortification hFinGat).iso
  have h₁ : IsPullback e.hom.left ((twoSortProj hFinGat).map FinGat.arr) (su' FinGat.arr)
      e.hom.right :=
    IsPullback.of_horiz_isIso ⟨e.hom.w⟩
  exact h₁.paste_horiz (shpb FinGat.arr)

/-- Existence and uniqueness of a natural transformation `twoSortProj ⟶ 𝟭 FinGat` extending the
square `twoSortSquare`. -/
theorem existsUnique_twoSortCounit :
    ∃! α : twoSortProj hFinGat ⟶ (𝟙 FinGat : FinGat ⟶ FinGat).functor,
      α.app FinGat.dom = (twoSortSquare hFinGat).left ∧
        α.app FinGat.cod = (twoSortSquare hFinGat).right :=
  hFinGat.existsUnique_natTrans (twoSortProj hFinGat) (𝟙 FinGat) (twoSortSquare hFinGat)
    (twoSortSquare_isPullback hFinGat)

/-- **The counit of the two-sortification functor**: the natural transformation from the composite
of the two-sortification functor `FinGat ⥤ Φ FinGat` and the projection `Φ FinGat ⥤ FinGat` to the
identity functor of `FinGat`, extending the pullback square defining the chosen arrow of
`Φ FinGat`. -/
noncomputable def twoSortCounit : twoSortProj hFinGat ⟶ 𝟭 FinGat.carrier :=
  (existsUnique_twoSortCounit hFinGat).exists.choose

/-- The component of `twoSortCounit` at the domain `Y` of the chosen arrow is the upper side of
the pullback square defining `p'`. -/
theorem twoSortCounit_app_dom : (twoSortCounit hFinGat).app FinGat.dom =
    (twoSortification hFinGat).iso.hom.left.left ≫ pullback.fst FinGat.arr (sE FinGat.arr) :=
  (existsUnique_twoSortCounit hFinGat).exists.choose_spec.1

/-- The component of `twoSortCounit` at the codomain `X` of the chosen arrow is the counit
`ε : Y ×_X P X ⟶ X`, the lower side of the pullback square defining `p'`. -/
theorem twoSortCounit_app_cod : (twoSortCounit hFinGat).app FinGat.cod =
    (twoSortification hFinGat).iso.hom.right.left ≫ sE FinGat.arr :=
  (existsUnique_twoSortCounit hFinGat).exists.choose_spec.2

/-- `twoSortCounit` is the unique natural transformation with these components. -/
theorem twoSortCounit_unique (α : twoSortProj hFinGat ⟶ 𝟭 FinGat.carrier)
    (hY : α.app FinGat.dom =
      (twoSortification hFinGat).iso.hom.left.left ≫ pullback.fst FinGat.arr (sE FinGat.arr))
    (hX : α.app FinGat.cod = (twoSortification hFinGat).iso.hom.right.left ≫ sE FinGat.arr) :
    α = twoSortCounit hFinGat :=
  (existsUnique_twoSortCounit hFinGat).unique ⟨hY, hX⟩
    ⟨twoSortCounit_app_dom hFinGat, twoSortCounit_app_cod hFinGat⟩



omit hFinGat in
private lemma arrow_eqToHom_left_left {C : Type*} [Category C] {Z : C} {a b : Arrow (Over Z)}
    (h : a = b) : (eqToHom h).left.left = eqToHom (congrArg (fun a : Arrow _ => a.left.left) h) := by
  subst h; rfl

omit hFinGat in
private lemma arrow_eqToHom_right_left {C : Type*} [Category C] {Z : C} {a b : Arrow (Over Z)}
    (h : a = b) :
    (eqToHom h).right.left = eqToHom (congrArg (fun a : Arrow _ => a.right.left) h) := by
  subst h; rfl

/-- Since the two-sortification functor is strict, the component of `twoSortCounit` at `Y` is,
up to the identification `twoSortProj Y = Y'`, exactly the upper side
`Y' ⟶ Y` of the pullback square defining `p'`. -/
theorem twoSortCounit_app_dom_eq :
    ∃ h : (twoSortProj hFinGat).obj FinGat.dom = sY' FinGat.arr,
      (twoSortCounit hFinGat).app FinGat.dom =
        eqToHom h ≫ pullback.fst FinGat.arr (sE FinGat.arr) := by
  obtain ⟨h, hiso⟩ := twoSortification_isStrict hFinGat
  refine ⟨congrArg (fun a : Arrow _ => a.left.left) h, ?_⟩
  rw [twoSortCounit_app_dom, hiso]
  exact congrArg (· ≫ _) (arrow_eqToHom_left_left h)

/-- Since the two-sortification functor is strict, the component of `twoSortCounit` at `X` is,
up to the identification `twoSortProj X = Y ×_X P X`, exactly the counit
`ε : Y ×_X P X ⟶ X`, the lower side of the pullback square defining `p'`. -/
theorem twoSortCounit_app_cod_eq :
    ∃ h : (twoSortProj hFinGat).obj FinGat.cod = (sX FinGat.arr).Pbk.pullback,
      (twoSortCounit hFinGat).app FinGat.cod = eqToHom h ≫ sE FinGat.arr := by
  obtain ⟨h, hiso⟩ := twoSortification_isStrict hFinGat
  refine ⟨congrArg (fun a : Arrow _ => a.right.left) h, ?_⟩
  rw [twoSortCounit_app_cod, hiso]
  exact congrArg (· ≫ _) (arrow_eqToHom_right_left h)

end ExpArrCat
