/-
Copyright (c) 2026 Lean Contributor. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Contributor
-/
import CartexpAristotle.TwoSortFFGamma
import CartexpAristotle.TwoSortificationFullyFaithful

/-!
# Two-sortification is fully faithful: reading off morphisms from the initial model

Let `FinGat` be bi-initial with `w`-small hom-types, `T` the two-sortification functor and `M`
the model functor. We apply the results of `CartexpAristotle.TwoSortFFGamma` to the morphism
`GT = T ≫ Φ M : FinGat ⟶ Φ CatLexp`, which sends a theory `Γ` to the category of models of the
two-sortified theory `T Γ` over families of types (the functor `Γ ↦ Mod (T Γ)` of the appendix).

For a morphism `h : T a ⟶ T X` (resp. `h : T a ⟶ T Y`) and a model `K` of `T a`, the image of `K`
by `h` is a family with an index `Rd K h` (resp. a pointed type `Qd K h`). For the initial model
`Z` of `T a` (from `CartexpAristotle.InitialModel`), these determine `h`
(`Rd_zero_injective`, `Qd_zero_injective`): this is the computation of the initial model
(Proposition "initial-value-fam" of the appendix).

## References

* [Paper, App. C.2, Prop. `prop:initial-object-two-sortification`] and
  [Paper, App. C.3, Prop. `prop:initial-value-fam`]: only the consequence needed for fullness is
  proved, namely that a morphism `T Ω ⟶ T X` (resp. `T Ω ⟶ T Y`) is determined by its value on the
  initial model (`Rd_zero_injective`, `Qd_zero_injective`).
* `GT = T ≫ Φ M` is the functor `Γ ↦ Mod(T Γ)` of [Paper, §4.2, Cor.
  `cor:models-two-sortification-lexp-functor`], used here instead of `TWb` of
  [Paper, App. C.1, Notation before Prop. `prop:model-faithful`].
-/

open CategoryTheory Limits

universe w

namespace Lexp

namespace TwoSortFF

open SemanticTwoSortFunctor PointedForget SliceExp InitialModel

noncomputable section

variable {FinGat : Lexp.{w + 1, w + 2}} (hFinGat : IsBiInitial FinGat)

/-- The two-sortification functor. -/
abbrev Tw : FinGat ⟶ Φobj.{w + 1, w + 2} FinGat := twoSortification.{w + 1, w + 2} hFinGat

/-- The model functor. -/
abbrev Mf : FinGat ⟶ CatLexp.{w} := modelFunctor hFinGat

/-- The functor `Γ ↦ Mod (T Γ)`, over families of types.

[Paper, §4.2, Cor. `cor:models-two-sortification-lexp-functor`]: `Γ ↦ Mod(T Γ)`. -/
abbrev GT : FinGat ⟶ C₀.{w} := Tw hFinGat ≫ Φmap.{w + 1, w + 2} (Mf hFinGat)

/-- The action of a morphism `h : T a ⟶ T Γ` on the models. -/
abbrev GmH {a Γ : FinGat.carrier} (h : (Tw hFinGat).functor.obj a ⟶ (Tw hFinGat).functor.obj Γ) :
    GL (GT hFinGat) a ⥤ GL (GT hFinGat) Γ :=
  ((Φfun.{w + 1, w + 2} (Mf hFinGat)).map h).left.toFunctor

variable {hFinGat} {a : FinGat.carrier}

lemma famF_mapH_obj {Γ : FinGat.carrier}
    (h : (Tw hFinGat).functor.obj a ⟶ (Tw hFinGat).functor.obj Γ) (K : GL (GT hFinGat) a) :
    (famF (GT hFinGat) Γ).obj ((GmH hFinGat h).obj K) = (famF (GT hFinGat) a).obj K :=
  Functor.congr_obj (congrArg Cat.Hom.toFunctor (Over.w ((Φfun.{w + 1, w + 2} (Mf hFinGat)).map h))) K

lemma famF_mapH_heq {Γ : FinGat.carrier}
    (h : (Tw hFinGat).functor.obj a ⟶ (Tw hFinGat).functor.obj Γ) {K K' : GL (GT hFinGat) a}
    (m : K ⟶ K') :
    (famF (GT hFinGat) Γ).map ((GmH hFinGat h).map m) ≍ (famF (GT hFinGat) a).map m := by
  have := Functor.congr_hom (congrArg Cat.Hom.toFunctor (Over.w ((Φfun.{w + 1, w + 2} (Mf hFinGat)).map h))) m
  exact (heq_of_eq this).trans (CatPullback.conj_heq _ _ _)

/-- The image of the model `K` by `h : T a ⟶ T X`, as a family with an index. -/
abbrev Rd (K : GL (GT hFinGat) a) (h : (Tw hFinGat).functor.obj a ⟶ (Tw hFinGat).functor.obj FinGat.cod) :
    (idx (Type w)).Elements :=
  (isoX (GT hFinGat)).obj ((GmH hFinGat h).obj K)

/-- The image of the model `K` by `h : T a ⟶ T Y`, as a pointed type. -/
abbrev Qd (K : GL (GT hFinGat) a) (h : (Tw hFinGat).functor.obj a ⟶ (Tw hFinGat).functor.obj FinGat.dom) :
    Pointed.{w} :=
  (gY (GT hFinGat)).obj ((GmH hFinGat h).obj K)

/-- The morphism `T a ⟶ Y` corresponding to `h : T a ⟶ T X`. -/
abbrev AX (h : (Tw hFinGat).functor.obj a ⟶ (Tw hFinGat).functor.obj FinGat.cod) :
    ((Tw hFinGat).functor.obj a).left ⟶ FinGat.dom :=
  h.left ≫ (Tw hFinGat).iso.hom.right.left ≫ (dX FinGat).Pbk.p₁

/-- The morphism `T a ⟶ Y` corresponding to `h : T a ⟶ T Y`. -/
abbrev AY (h : (Tw hFinGat).functor.obj a ⟶ (Tw hFinGat).functor.obj FinGat.dom) :
    ((Tw hFinGat).functor.obj a).left ⟶ FinGat.dom :=
  h.left ≫ (Tw hFinGat).iso.hom.left.left ≫ pullback.fst FinGat.arr (sE FinGat.arr)

lemma elToPt_Rd (K : GL (GT hFinGat) a)
    (h : (Tw hFinGat).functor.obj a ⟶ (Tw hFinGat).functor.obj FinGat.cod) :
    (elToPt (idx (Type w))).obj (Rd K h) =
      (pt (Mf hFinGat)).obj (((Mf hFinGat).functor.map (AX h)).toFunctor.obj K) := by
  have e : ((Φfun.{w + 1, w + 2} (Mf hFinGat)).map h).left ≫ (GT hFinGat).iso.hom.right.left ≫
      (sX U.{w}).Pbk.p₁ = (Mf hFinGat).functor.map (AX h) ≫ (Mf hFinGat).iso.hom.left := by
    change (Mf hFinGat).functor.map h.left ≫ ((Mf hFinGat).functor.map
      (Tw hFinGat).iso.hom.right.left ≫ (ιX (Mf hFinGat)).hom) ≫ _ = _
    simp only [Category.assoc]
    erw [ιX_fst]
    rw [AX, Functor.map_comp, Functor.map_comp]
    simp only [Category.assoc]
  exact Functor.congr_obj (congrArg Cat.Hom.toFunctor e) K

lemma fst_Qd (K : GL (GT hFinGat) a)
    (h : (Tw hFinGat).functor.obj a ⟶ (Tw hFinGat).functor.obj FinGat.dom) :
    Qd K h = (pt (Mf hFinGat)).obj (((Mf hFinGat).functor.map (AY h)).toFunctor.obj K) := by
  have e : ((Φfun.{w + 1, w + 2} (Mf hFinGat)).map h).left ≫ (GT hFinGat).iso.hom.left.left ≫
      pullback.fst U.{w} (sE U.{w}) = (Mf hFinGat).functor.map (AY h) ≫
        (Mf hFinGat).iso.hom.left := by
    change (Mf hFinGat).functor.map h.left ≫ ((Mf hFinGat).functor.map
      (Tw hFinGat).iso.hom.left.left ≫ (ιY (Mf hFinGat)).hom) ≫ _ = _
    simp only [Category.assoc]
    erw [ιY_fst]
    rw [AY, Functor.map_comp, Functor.map_comp]
    simp only [Category.assoc]
  exact Functor.congr_obj (congrArg Cat.Hom.toFunctor e) K

variable [LocallySmall.{w} FinGat.carrier]

omit [LocallySmall.{w} FinGat.carrier] in
lemma Tw_iso_left_su' : (Tw hFinGat).iso.hom.left.left ≫ su' FinGat.arr =
    ((Tw hFinGat).functor.map FinGat.arr).left ≫ (Tw hFinGat).iso.hom.right.left :=
  congrArg CommaMorphism.left (Tw hFinGat).iso.hom.w

omit [LocallySmall.{w} FinGat.carrier] in
lemma Tw_iso_right_sW : (Tw hFinGat).iso.hom.right.left ≫ (dX FinGat).Pbk.p₂ =
    ((Tw hFinGat).functor.obj FinGat.cod).hom :=
  Over.w (Tw hFinGat).iso.hom.right

omit [LocallySmall.{w} FinGat.carrier] in
lemma AX_arr (h : (Tw hFinGat).functor.obj a ⟶ (Tw hFinGat).functor.obj FinGat.cod) :
    AX h ≫ FinGat.arr = ((Tw hFinGat).functor.obj a).hom ≫ (dX FinGat).pi := by
  simp only [AX, Category.assoc]
  rw [(dX FinGat).Pbk.condition, ← Category.assoc ((Tw hFinGat).iso.hom.right.left),
    Tw_iso_right_sW, ← Category.assoc, Over.w h]

omit [LocallySmall.{w} FinGat.carrier] in
lemma AY_arr (h : (Tw hFinGat).functor.obj a ⟶ (Tw hFinGat).functor.obj FinGat.dom) :
    AY h ≫ FinGat.arr = (h ≫ (Tw hFinGat).functor.map FinGat.arr).left ≫
      (Tw hFinGat).iso.hom.right.left ≫ sE FinGat.arr := by
  simp only [AY, Category.assoc]
  rw [pullback.condition, ← Category.assoc ((Tw hFinGat).iso.hom.left.left), Tw_iso_left_su']
  change _ = (h.left ≫ ((Tw hFinGat).functor.map FinGat.arr).left) ≫ _
  simp only [Category.assoc]

/-- The initial model of `T a`. -/
abbrev Zm (a : FinGat.carrier) : GL (GT hFinGat) a :=
  zero (a := ((Tw hFinGat).functor.obj a).left) (Mf hFinGat) hFinGat

lemma pt_zero (A : ((Tw hFinGat).functor.obj a).left ⟶ FinGat.dom) :
    (pt (Mf hFinGat)).obj (((Mf hFinGat).functor.map A).toFunctor.obj (Zm (hFinGat := hFinGat) a)) =
      (⟨Tm _ (A ≫ FinGat.arr), tm _ A⟩ : Pointed.{w}) := by
  rw [← alpha_obj]
  exact Functor.congr_obj (congrArg Cat.Hom.toFunctor (alpha_left (Mf hFinGat) hFinGat)) A

/-- The image of the initial model by `h : T a ⟶ T X` determines `h`.

Consequence of [Paper, App. C.3, Prop. `prop:initial-value-fam`]. -/
lemma Rd_zero_injective
    {h h' : (Tw hFinGat).functor.obj a ⟶ (Tw hFinGat).functor.obj FinGat.cod}
    (e : Rd (Zm a) h = Rd (Zm a) h') : h = h' := by
  have e1 := congrArg (elToPt (idx (Type w))).obj e
  rw [elToPt_Rd, elToPt_Rd, pt_zero, pt_zero] at e1
  have hA : AX h = AX h' :=
    eq_of_tm_heq _ ((AX_arr h).trans (AX_arr h').symm) (point_heq_of_eq e1)
  refine Over.OverMorphism.ext ?_
  have : h.left ≫ (Tw hFinGat).iso.hom.right.left = h'.left ≫ (Tw hFinGat).iso.hom.right.left := by
    apply (dX FinGat).Pbk.hom_ext
    · simpa [AX] using hA
    · rw [Category.assoc, Category.assoc, Tw_iso_right_sW, Over.w h, Over.w h']
  exact (cancel_mono _).1 this

/-- The image of the initial model by `h : T a ⟶ T Y` determines `h`, given `h ≫ T p`.

Consequence of [Paper, App. C.3, Prop. `prop:initial-value-fam`]. -/
lemma Qd_zero_injective
    {h h' : (Tw hFinGat).functor.obj a ⟶ (Tw hFinGat).functor.obj FinGat.dom}
    (hp : h ≫ (Tw hFinGat).functor.map FinGat.arr = h' ≫ (Tw hFinGat).functor.map FinGat.arr)
    (e : (Qd (Zm a) h).point ≍ (Qd (Zm a) h').point) : h = h' := by
  have e₁ := (fst_Qd (Zm a) h).trans (pt_zero (AY h))
  have e₂ := (fst_Qd (Zm a) h').trans (pt_zero (AY h'))
  have hA : AY h = AY h' :=
    eq_of_tm_heq _ (by rw [AY_arr, AY_arr, hp])
      (((point_heq_of_eq e₁).symm.trans e).trans (point_heq_of_eq e₂))
  refine Over.OverMorphism.ext ?_
  have : h.left ≫ (Tw hFinGat).iso.hom.left.left = h'.left ≫ (Tw hFinGat).iso.hom.left.left := by
    apply pullback.hom_ext
    · simpa [AY] using hA
    · rw [Category.assoc, Category.assoc, Tw_iso_left_su', ← Category.assoc, ← Category.assoc]
      change (h ≫ (Tw hFinGat).functor.map FinGat.arr).left ≫ _ =
        (h' ≫ (Tw hFinGat).functor.map FinGat.arr).left ≫ _
      rw [hp]
  exact (cancel_mono _).1 this

end

end TwoSortFF

end Lexp
