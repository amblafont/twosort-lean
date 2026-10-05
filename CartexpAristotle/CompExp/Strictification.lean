/-
Copyright (c) 2026 Lean Contributor. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Contributor
-/
import CartexpAristotle.CompExp.UniversalNatTrans
import CartexpAristotle.BiInitialDomCod

/-!
# Strict morphisms out of a bi-initial `CompExp`

This is the analogue for `CompExp` of `CartexpAristotle.Strictification`,
`CartexpAristotle.BiInitialDomCod` and the first part of `CartexpAristotle.TwoSortification`.

* `CompExp.strictify`: the strictification of a morphism of `CompExp` (the strictification of the
  underlying morphism of `Lexp`, which still preserves wide pullbacks, being isomorphic to the
  original functor).
* `CompExp.twoExp`: the two-element linear order (which has all limits), with the arrow `⊥ ⟶ ⊤`.
* `CompExp.IsBiInitial.dom_ne_cod`: the domain and codomain of the chosen arrow of a bi-initial
  `CompExp` are different (it maps to `twoExp`).
* `CompExp.IsBiInitial.strictHom`: the chosen strict morphism out of a bi-initial `CompExp`.

## References

* [Paper, §2.2, Prop. `prop:strictification`], adapted to `CompExp`.
-/

open CategoryTheory Limits

universe w v u

namespace Lexp.TwoCat

variable {J : Type*} [Category J]

open Classical in
/-- The limit cone in the two-element linear order: the meet of all objects of the diagram. -/
noncomputable def limCone (K : J ⥤ TwoCat.{u}) : Cone K where
  pt := ⟨decide (∀ j, (K.obj j).val = true)⟩
  π :=
    { app := fun j => homOfLE' (by
        rw [Bool.le_iff_imp]
        intro h
        exact (decide_eq_true_iff.1 h) j)
      naturality := fun _ _ _ => Subsingleton.elim _ _ }

/-- The meet of all objects of the diagram is a limit. -/
noncomputable def limConeIsLimit (K : J ⥤ TwoCat.{u}) : IsLimit (limCone K) where
  lift s := homOfLE' (by
    classical
    rw [Bool.le_iff_imp]
    intro h
    exact decide_eq_true_iff.2 fun j => (Bool.le_iff_imp.1 (le_of_hom' (s.π.app j))) h)
  fac _ _ := Subsingleton.elim _ _
  uniq _ _ _ := Subsingleton.elim _ _

instance hasLimitsOfShape : HasLimitsOfShape J TwoCat.{u} where
  has_limit K := ⟨⟨⟨limCone K, limConeIsLimit K⟩⟩⟩

end Lexp.TwoCat

namespace CompExp

/-- The object of `CompExp` given by the two-element linear order with chosen arrow `⊥ ⟶ ⊤`. -/
def twoExp : CompExp.{w, v, u} where
  toLexp := Lexp.twoExp.{v, u}
  hasWidePullbacks _ := inferInstanceAs (HasLimitsOfShape _ Lexp.TwoCat.{u})

/-- **The domain and codomain of the chosen exponentiable arrow of a bi-initial `CompExp` are
different.** -/
theorem IsBiInitial.dom_ne_cod {A : CompExp.{w, v, u}} (hA : IsBiInitial A) : A.dom ≠ A.cod := by
  intro h
  obtain ⟨F⟩ := hA.nonempty_hom twoExp.{w, v, u}
  have f : (Lexp.TwoCat.top : Lexp.TwoCat.{u}) ⟶ Lexp.TwoCat.bot :=
    F.iso.inv.right ≫ eqToHom (congrArg F.functor.obj h.symm) ≫ F.iso.hom.left
  exact absurd (Lexp.TwoCat.le_of_hom' f) (by decide)

section Strictify

variable {A B : CompExp.{w, v, u}} (F : A ⟶ B)

/-- The natural isomorphism underlying an invertible 2-cell of `Lexp`. -/
def _root_.Lexp.Hom₂.natIsoOfIso' {A B : Lexp.{v, u}} {F G : A ⟶ B} (e : F ≅ G) :
    F.functor ≅ G.functor where
  hom := e.hom.nat
  inv := e.inv.nat
  hom_inv_id := congrArg Lexp.Hom₂.nat e.hom_inv_id
  inv_hom_id := congrArg Lexp.Hom₂.nat e.inv_hom_id

/-- The strict morphism of `CompExp` isomorphic to `F`. -/
noncomputable def strictify (h : A.dom ≠ A.cod) : A ⟶ B where
  toHom := Lexp.strictify F.toLexpHom h
  preservesWidePullbacks _ :=
    preservesLimitsOfShape_of_natIso
      (Lexp.Hom₂.natIsoOfIso' (Lexp.strictifyIso F.toLexpHom h))

lemma strictify_isStrict (h : A.dom ≠ A.cod) : (strictify F h).toLexpHom.IsStrict :=
  Lexp.strictify_isStrict _ h

/-- The invertible 2-cell between `F` and its strictification. -/
noncomputable def strictifyIso (h : A.dom ≠ A.cod) : F ≅ strictify F h :=
  Hom.isoMk (Lexp.strictifyIso F.toLexpHom h)

end Strictify

namespace IsBiInitial

variable {A : CompExp.{w, v, u}} (hA : IsBiInitial A) (B : CompExp.{w, v, u})

/-- The chosen strict morphism out of a bi-initial `CompExp`: the strictification of some
morphism `A ⟶ B`.

[Paper, §2.2, Prop. `prop:strictification`]. -/
noncomputable def strictHom : A ⟶ B :=
  strictify (Classical.choice (hA.nonempty_hom B)) hA.dom_ne_cod

/-- The chosen morphism out of a bi-initial object is strict. -/
theorem strictHom_isStrict : (hA.strictHom B).toLexpHom.IsStrict :=
  strictify_isStrict _ _

/-- Every morphism out of a bi-initial object is isomorphic to the chosen strict one. -/
theorem nonempty_iso_strictHom (F : A ⟶ B) : Nonempty (F ≅ hA.strictHom B) :=
  hA.nonempty_iso _ _

/-- The invertible 2-cell between a morphism out of a bi-initial object and the chosen strict one
is unique. -/
theorem subsingleton_iso_strictHom (F : A ⟶ B) : Subsingleton (F ≅ hA.strictHom B) :=
  ⟨fun _ _ => Iso.ext (hA.hom₂_ext _ _)⟩

end IsBiInitial

end CompExp
