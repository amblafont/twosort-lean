/-
Copyright (c) 2026 Lean Contributor. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Contributor
-/
import CartexpAristotle.FinGAT
import CartexpAristotle.SliceExponentiable
import Mathlib.CategoryTheory.Limits.FullSubcategory
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks

/-!
# Induction over the objects of a bi-initial `ExpArrCat`

Let `A` be a bi-initial object of `ExpArrCat`, with chosen exponentiable arrow `p : Y ⟶ X`.
Every property `Q` of objects of `A` which

* is invariant under isomorphism,
* holds for the terminal object,
* is closed under pullbacks,
* is closed under the chosen exponentials along `p`, and
* holds for `Y` and `X`

holds for every object of `A` (`ExpArrCat.IsBiInitial.induction`).

The proof: the full subcategory on the objects satisfying `Q` is again an object of `ExpArrCat`
(`ExpArrCat.InductiveProperty.subExp`), and its inclusion into `A` is a morphism of `ExpArrCat`.
By bi-initiality there is a morphism `s` from `A` to it, and the composite of `s` with the
inclusion is isomorphic to the identity of `A`; so every object of `A` is isomorphic to an object
satisfying `Q`.
-/

open CategoryTheory Limits

universe v u

namespace ExpArrCat

/-- A property of objects of an `ExpArrCat` which is closed under all the constructions of
`ExpArrCat` (isomorphisms, the terminal object, pullbacks, the chosen exponentials along the
chosen arrow) and holds for the domain and codomain of the chosen arrow. -/
structure InductiveProperty (A : ExpArrCat.{v, u}) (Q : A.carrier → Prop) : Prop where
  of_iso : ∀ {a b : A.carrier}, (a ≅ b) → Q a → Q b
  terminal : Q (⊤_ A.carrier)
  pullback : ∀ {W X₁ X₂ S : A.carrier} {fst : W ⟶ X₁} {snd : W ⟶ X₂} {f : X₁ ⟶ S}
    {g : X₂ ⟶ S}, IsPullback fst snd f g → Q X₁ → Q X₂ → Q S → Q W
  exp : ∀ c : A.carrier, Q c → Q (IsExpArr.isExpArrowData (u := A.arr) c).P
  dom : Q A.dom
  cod : Q A.cod

namespace InductiveProperty

variable {A : ExpArrCat.{v, u}} {Q : A.carrier → Prop} (hQ : InductiveProperty A Q)

/-- The property `Q` as an `ObjectProperty`. -/
abbrev prop (_ : InductiveProperty A Q) : ObjectProperty A.carrier := Q

instance : (hQ.prop).IsClosedUnderIsomorphisms := ⟨fun e h => hQ.of_iso e h⟩

include hQ in
lemma prop_pullback {X₁ X₂ S : A.carrier} (f : X₁ ⟶ S) (g : X₂ ⟶ S) (h₁ : Q X₁) (h₂ : Q X₂)
    (hS : Q S) : Q (Limits.pullback f g) :=
  hQ.pullback (IsPullback.of_hasPullback f g) h₁ h₂ hS

instance closedCospan : (hQ.prop).IsClosedUnderLimitsOfShape WalkingCospan :=
  ObjectProperty.IsClosedUnderLimitsOfShape.mk' (by
    rintro _ ⟨F, hF⟩
    refine hQ.of_iso (HasLimit.isoOfNatIso (diagramIsoCospan F)).symm ?_
    exact hQ.prop_pullback _ _ (hF _) (hF _) (hF _))

instance closedEmpty : (hQ.prop).IsClosedUnderLimitsOfShape (Discrete PEmpty.{1}) :=
  ObjectProperty.IsClosedUnderLimitsOfShape.mk' (by
    rintro _ ⟨F, hF⟩
    exact hQ.of_iso (HasLimit.isoOfNatIso (Functor.emptyExt (Functor.empty.{0} _) F))
      hQ.terminal)

/-- The full subcategory on the objects satisfying `Q`. -/
abbrev Sub := (hQ.prop).FullSubcategory

instance : HasPullbacks hQ.Sub := inferInstanceAs (HasLimitsOfShape WalkingCospan hQ.Sub)

instance : HasTerminal hQ.Sub := inferInstanceAs (HasLimitsOfShape (Discrete PEmpty.{1}) hQ.Sub)

instance : PreservesLimitsOfShape WalkingCospan (hQ.prop).ι := ⟨fun {_} => inferInstance⟩

instance : PreservesLimitsOfShape (Discrete PEmpty.{1}) (hQ.prop).ι := ⟨fun {_} => inferInstance⟩

/-- The domain of the chosen arrow, as an object of the full subcategory. -/
abbrev subDom : hQ.Sub := ⟨A.dom, hQ.dom⟩

/-- The codomain of the chosen arrow, as an object of the full subcategory. -/
abbrev subCod : hQ.Sub := ⟨A.cod, hQ.cod⟩

/-- The chosen arrow, as an arrow of the full subcategory. -/
abbrev subArr : hQ.subDom ⟶ hQ.subCod := ObjectProperty.homMk A.arr

/-- The chosen exponential `Data` of `A`, for an object `c` of `A`. -/
noncomputable abbrev cData (c : A.carrier) : Data A.arr c := IsExpArr.isExpArrowData c

/-- The chosen pullback in the full subcategory. -/
noncomputable def subPbk (c : hQ.Sub) :
    ChosenPullback hQ.subArr (ObjectProperty.homMk (cData c.obj).pi :
      (⟨(cData c.obj).P, hQ.exp _ c.property⟩ : hQ.Sub) ⟶ hQ.subCod) where
  pullback := ⟨(cData c.obj).Pbk.pullback,
    hQ.pullback (cData c.obj).Pbk.isPullback hQ.dom (hQ.exp _ c.property) hQ.cod⟩
  p₁ := ObjectProperty.homMk (cData c.obj).Pbk.p₁
  p₂ := ObjectProperty.homMk (cData c.obj).Pbk.p₂
  condition := by ext; exact (cData c.obj).Pbk.condition
  isLimit := isLimitOfIsLimitPullbackConeMap (hQ.prop).ι _ (cData c.obj).Pbk.isLimit

/-- The exponential `Data` in the full subcategory. -/
noncomputable def subData (c : hQ.Sub) : Data hQ.subArr c where
  P := ⟨(cData c.obj).P, hQ.exp _ c.property⟩
  pi := ObjectProperty.homMk (cData c.obj).pi
  Pbk := hQ.subPbk c
  epsilon := ObjectProperty.homMk (cData c.obj).epsilon

lemma FBF_subData_hom (c : hQ.Sub) {d : hQ.Sub} {f : d ⟶ (hQ.subData c).P} {h : d ⟶ hQ.subCod}
    (K : ChosenPullback hQ.subArr h) (e : h = f ≫ (hQ.subData c).pi) :
    (FBF_on_mor (hQ.subData c) K e).hom =
      FBF_on_mor (cData c.obj) (functPullback (hQ.prop).ι K)
        (congrArg InducedCategory.Hom.hom e) := by
  apply (cData c.obj).Pbk.hom_ext
  · have h1 := congrArg InducedCategory.Hom.hom (SliceExp.FBF_on_mor_fst (hQ.subData c) K e)
    simp only [ObjectProperty.FullSubcategory.comp_hom] at h1
    erw [h1, SliceExp.FBF_on_mor_fst]
    rfl
  · have h2 := congrArg InducedCategory.Hom.hom (SliceExp.FBF_on_mor_snd (hQ.subData c) K e)
    simp only [ObjectProperty.FullSubcategory.comp_hom] at h2
    erw [h2, SliceExp.FBF_on_mor_snd]
    rfl

/-- The exponential `Data` in the full subcategory is universal. -/
noncomputable instance subUniv (c : hQ.Sub) : Universal (hQ.subData c) where
  mor {_ f K} g := ObjectProperty.homMk
    (Universal.mor (data := cData c.obj) (Kuf := functPullback (hQ.prop).ι K) g.hom)
  isSlice {_ f K} g := by
    ext
    exact Universal.isSlice (data := cData c.obj) (Kuf := functPullback (hQ.prop).ι K) g.hom
  comm {_ f K} g := by
    ext
    rw [ObjectProperty.FullSubcategory.comp_hom, FBF_subData_hom]
    exact Universal.comm (data := cData c.obj) (Kuf := functPullback (hQ.prop).ι K) g.hom
  uniq {_ f g h} K ef eg H := by
    ext
    refine Universal.uniq (data := cData c.obj) (functPullback (hQ.prop).ι K)
      (congrArg InducedCategory.Hom.hom ef) (congrArg InducedCategory.Hom.hom eg) ?_
    have H' := congrArg InducedCategory.Hom.hom H
    simp only [ObjectProperty.FullSubcategory.comp_hom, FBF_subData_hom] at H'
    exact H'

noncomputable instance : IsExpArr hQ.subArr where
  isExpArrowData := hQ.subData
  isExpArrow := hQ.subUniv

/-- The full subcategory on the objects satisfying `Q`, as an object of `ExpArrCat`. -/
noncomputable def subExp : ExpArrCat.{v, u} where
  carrier := hQ.Sub
  arr := hQ.subArr

/-- The inclusion of the full subcategory preserves the chosen exponentiable arrow. -/
noncomputable def ιPreserves : FunctorPreserves hQ.subArr (hQ.prop).ι :=
  functor_preserves_1_is_enough _ _ hQ.subData hQ.subUniv (fun c =>
    lift_arrow_iso_univ_helper (Iso.refl (Arrow.mk A.arr)) (cData c.obj)
      (pi' := (functor_on (hQ.prop).ι (hQ.subData c)).pi) (by simp; rfl)
      (w := (functor_on (hQ.prop).ι (hQ.subData c)).Pbk.p₁)
      (functor_on (hQ.prop).ι (hQ.subData c)).Pbk.condition
      (functor_on (hQ.prop).ι (hQ.subData c)).Pbk.isLimit (by simp; rfl))

/-- The inclusion of the full subcategory, as a morphism of `ExpArrCat`. -/
noncomputable def ιHom : hQ.subExp ⟶ A where
  functor := (hQ.prop).ι
  preservesPullbacks := inferInstanceAs (PreservesLimitsOfShape WalkingCospan (hQ.prop).ι)
  preservesTerminal := inferInstanceAs (PreservesLimitsOfShape (Discrete PEmpty.{1}) (hQ.prop).ι)
  preservesArr := hQ.ιPreserves
  iso := Iso.refl _

end InductiveProperty

/-- **Induction over the objects of a bi-initial `ExpArrCat`.** A property of objects which is
invariant under isomorphism, holds for the terminal object, is closed under pullbacks and under
the chosen exponentials along the chosen arrow `p : Y ⟶ X`, and holds for `Y` and `X`, holds for
every object. -/
theorem IsBiInitial.induction {A : ExpArrCat.{v, u}} (hA : IsBiInitial A) {Q : A.carrier → Prop}
    (hQ : InductiveProperty A Q) (a : A.carrier) : Q a := by
  obtain ⟨s⟩ := hA.nonempty_hom hQ.subExp
  obtain ⟨e⟩ := hA.nonempty_iso (s ≫ hQ.ιHom) (𝟙 A)
  have i : (s.functor.obj a).obj ≅ a :=
    { hom := e.hom.nat.app a
      inv := e.inv.nat.app a
      hom_inv_id := congrArg (fun t => t.nat.app a) e.hom_inv_id
      inv_hom_id := congrArg (fun t => t.nat.app a) e.inv_hom_id }
  exact hQ.of_iso i (s.functor.obj a).property

end ExpArrCat
