/-
Copyright (c) 2026 Lean Contributor. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Contributor
-/
import CartexpAristotle.TwoSortification
import CartexpAristotle.BiInitialInduction
import CartexpAristotle.InitialModelUnique

/-!
# The images of the model functor have initial objects

Let `FinGat` be a bi-initial object of `ExpArrCat` and `M : FinGat ⟶ CatExp` the model functor.
We show that for every object `a` of `FinGat`, the category `M a` has an initial object, assuming
that the hom-types of `FinGat` are `w`-small. The initial object is the term model of `a`,
constructed in `CartexpAristotle.InitialModel` following the appendix ("Initial models of GATs"),
and shown to be initial in `CartexpAristotle.InitialModelUnique`.

The lemmas below also record the individual closure properties of the objects whose models have
an initial object (isomorphisms, terminal object, `Y`, `X`, exponentials, pullbacks).
-/

open CategoryTheory Limits

universe w

namespace ExpArrCat

open FamOverExpArr PointedForget

section Lemmas

/-- Having an initial object is invariant under isomorphism in `Cat`. -/
lemma hasInitial_of_catIso {C D : Cat.{w, w + 1}} (e : C ≅ D) [HasInitial C] : HasInitial D :=
  IsInitial.hasInitial (IsInitial.isInitialObj (Cat.equivOfIso e).functor _ initialIsInitial)

/-- A terminal object of `Cat` has an initial object. -/
lemma hasInitial_of_isTerminal {T : Cat.{w, w + 1}} (hT : IsTerminal T) : HasInitial T := by
  have hd : IsDiscrete (ShrinkHoms.{w + 1} PUnit.{w + 2}) := {
    subsingleton _ _ := { allEq _ _ := eq_of_comp_right_eq (congrFun rfl) }
    eq_of_hom _ := rfl }
  have h1 : IsTerminal (Cat.of.{w, w + 1} (ShrinkHoms.{w + 1} PUnit.{w + 2})) :=
    Cat.isTerminalOfUniqueOfIsDiscrete
  have : HasInitial (Cat.of.{w, w + 1} (ShrinkHoms.{w + 1} PUnit.{w + 2})) :=
    IsInitial.hasInitial (X := (default : ShrinkHoms.{w + 1} PUnit.{w + 2})) (IsInitial.ofUniqueHom
      (fun Y => eqToHom (Subsingleton.elim (α := ShrinkHoms.{w + 1} PUnit.{w + 2}) _ _))
      (fun _ _ => (hd.subsingleton _ _).elim _ _))
  exact hasInitial_of_catIso (h1.uniqueUpToIso hT)

/-- Pointed types have an initial object. -/
instance hasInitial_pointed : HasInitial Pointed.{w} :=
  IsInitial.hasInitial (X := ⟨PUnit, PUnit.unit⟩) (IsInitial.ofUniqueHom
    (fun Y => ⟨fun _ => Y.point, rfl⟩)
    (fun Y m => by apply Pointed.Hom.ext; funext x; exact m.map_point))

/-- Formal coproducts have an initial object (the empty family). -/
instance hasInitial_formalCoproduct (C : Type (w + 1)) [Category.{w} C] :
    HasInitial (FormalCoproduct.{w} C) :=
  IsInitial.hasInitial (X := ⟨PEmpty, PEmpty.elim⟩) (IsInitial.ofUniqueHom
    (fun Y => ⟨PEmpty.elim, fun i => i.elim⟩)
    (fun Y m => by
      obtain ⟨f, φ⟩ := m
      have : f = PEmpty.elim := funext fun i => i.elim
      subst this
      congr
      funext i; exact i.elim))

end Lemmas

variable {FinGat : ExpArrCat.{w + 1, w + 2}} (hFinGat : IsBiInitial FinGat)

/-- The underlying functor of the model functor. -/
noncomputable abbrev modelFun : FinGat.carrier ⥤ Cat.{w, w + 1} := (modelFunctor hFinGat).functor

/-- The property of an object of `FinGat` that its image under the model functor has an initial
object. -/
def ModelHasInitial (a : FinGat.carrier) : Prop := HasInitial ((modelFun hFinGat).obj a)

lemma modelHasInitial_of_iso {a b : FinGat.carrier} (i : a ≅ b) (ha : ModelHasInitial hFinGat a) :
    ModelHasInitial hFinGat b :=
  have : HasInitial ((modelFun hFinGat).obj a) := ha
  hasInitial_of_catIso ((modelFun hFinGat).mapIso i)

lemma modelHasInitial_terminal : ModelHasInitial hFinGat (⊤_ FinGat.carrier) :=
  hasInitial_of_isTerminal (T := (modelFun hFinGat).obj _)
    (IsTerminal.isTerminalObj (modelFunctor hFinGat).functor _ terminalIsTerminal)

lemma modelHasInitial_dom : ModelHasInitial hFinGat FinGat.dom :=
  @hasInitial_of_catIso (Cat.of Pointed.{w}) ((modelFun hFinGat).obj FinGat.dom)
    (Comma.leftIso (modelFunctor hFinGat).iso).symm (inferInstanceAs (HasInitial Pointed.{w}))

lemma modelHasInitial_cod : ModelHasInitial hFinGat FinGat.cod :=
  @hasInitial_of_catIso (Cat.of (Type w)) ((modelFun hFinGat).obj FinGat.cod)
    (Comma.rightIso (modelFunctor hFinGat).iso).symm (inferInstanceAs (HasInitial (Type w)))

lemma modelHasInitial_exp (c : FinGat.carrier) (hc : ModelHasInitial hFinGat c) :
    ModelHasInitial hFinGat (IsExpArr.isExpArrowData (u := FinGat.arr) c).P := by
  have : HasInitial ((modelFun hFinGat).obj c) := hc
  let M := modelFunctor hFinGat
  let d := IsExpArr.isExpArrowData (u := FinGat.arr) c
  haveI : Universal (functor_on M.functor d) :=
    FunctorPreserves.functor_preserves d (IsExpArr.isExpArrow c)
  let d₂ : Data CatExp.{w}.arr (M.functor.obj c) := lift_arrow_iso M.iso (functor_on M.functor d)
  haveI : Universal d₂ := lift_arrow_iso_univ M.iso (functor_on M.functor d)
  let e := IsExpArr.isExpArrowData (u := CatExp.{w}.arr) (M.functor.obj c)
  haveI : Universal e := IsExpArr.isExpArrow _
  haveI : IsIso (canonical_mor d₂ e) := isIso_canonical_mor d₂ e
  have i : (Cat.of (FormalCoproduct.{w} ((modelFun hFinGat).obj c)) : Cat.{w, w + 1}) ≅
      (modelFun hFinGat).obj d.P := asIso (canonical_mor d₂ e)
  exact @hasInitial_of_catIso _ _ i (hasInitial_formalCoproduct _)

/-- **The images of the model functor have initial objects.** For every object `a` of a
bi-initial `FinGat` whose hom-types are `w`-small, the category `M a` has an initial object, where
`M` is the model functor. The initial object is the term model
`ExpArrCat.InitialModel.zero (modelFunctor hFinGat) hFinGat`. -/
theorem modelFunctor_hasInitial [LocallySmall.{w} FinGat.carrier] (a : FinGat.carrier) :
    HasInitial ((modelFun hFinGat).obj a) :=
  (InitialModel.isInitialZero (a := a) (modelFunctor hFinGat) hFinGat).hasInitial

/-
The earlier inductive approach (via `ExpArrCat.IsBiInitial.induction`) needed the following
closure property, which was left unproved. It does not follow from the closure hypotheses
`h₁ h₂ hS` alone, since a pullback of categories with initial objects need not have an initial
object. The statement above
is instead proved directly (the term-model construction of the appendix), so this lemma is no
longer needed.

lemma modelHasInitial_pullback {W X₁ X₂ S : FinGat.carrier} {fst : W ⟶ X₁} {snd : W ⟶ X₂}
    {f : X₁ ⟶ S} {g : X₂ ⟶ S} (hpb : IsPullback fst snd f g) (h₁ : ModelHasInitial hFinGat X₁)
    (h₂ : ModelHasInitial hFinGat X₂) (hS : ModelHasInitial hFinGat S) :
    ModelHasInitial hFinGat W := by
  sorry
-/

end ExpArrCat
