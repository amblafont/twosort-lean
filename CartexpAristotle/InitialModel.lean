/-
Copyright (c) 2026 Lean Contributor. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Contributor
-/
import CartexpAristotle.FinGAT
import CartexpAristotle.FamOverExpArr
import CartexpAristotle.Collage
import CartexpAristotle.PointifyPullback

/-!
# Initial models

Let `A` (`FinGat`) be a bi-initial object of `ExpArrCat`, with chosen exponentiable arrow
`p : Y ⟶ X`, whose hom-types are `w`-small, and let `G : A ⟶ CatExp` be a morphism of `ExpArrCat`
(e.g. the model functor). For every object `a` of `A`, the category `G a` (the models of `a`) has
an initial object.

We follow the appendix ("Initial models of GATs"):
* **Existence of the candidate.** By the universal property of `A` with respect to natural
  transformations (`ExpArrCat.IsBiInitial.existsUnique_natTrans_iso`), there is a unique natural
  transformation `α` from `Γ ↦ Disc (a ⟶ Γ)` to `G` whose components at `Y` and `X` are given by
  the term models: `A' : a ⟶ X` is sent to (a set isomorphic to) the set `Tm A'` of `t : a ⟶ Y`
  with `t ≫ p = A'`, and `t : a ⟶ Y` is sent to `Tm (t ≫ p)` pointed by `t`.
  The candidate initial model is `0 = α_a (𝟙 a)`.
* **Morphisms out of `0`.** For a model `ω`, a morphism `0 ⟶ ω` is encoded as a natural
  transformation out of the collage of `Γ ↦ (σ ↦ G σ ω)`; again such a natural transformation is
  unique, which gives existence and uniqueness of the morphism.
-/

open CategoryTheory Limits

universe w

namespace ExpArrCat

open FamOverExpArr PointedForget

/-- A functor sending pullback squares to pullback squares preserves pullbacks. -/
lemma preservesPullbacks_of_isPullback {C : Type*} [Category C] [HasPullbacks C] {D : Type*}
    [Category D] (F : C ⥤ D)
    (h : ∀ ⦃W X₁ X₂ S : C⦄ ⦃fst : W ⟶ X₁⦄ ⦃snd : W ⟶ X₂⦄ ⦃f : X₁ ⟶ S⦄ ⦃g : X₂ ⟶ S⦄,
      IsPullback fst snd f g → IsPullback (F.map fst) (F.map snd) (F.map f) (F.map g)) :
    PreservesLimitsOfShape WalkingCospan F := by
  constructor
  intro K
  haveI : PreservesLimit (cospan (K.map WalkingCospan.Hom.inl) (K.map WalkingCospan.Hom.inr)) F := by
    apply preservesLimit_of_preserves_limit_cone (pullbackIsPullback _ _)
    apply (isLimitMapConePullbackConeEquiv _ _).symm _
    exact (h (IsPullback.of_hasPullback _ _)).isLimit
  exact preservesLimit_of_iso_diagram F (diagramIsoCospan K).symm

namespace InitialModel

noncomputable section

lemma types_eqToHom_heq {α β : Type w} (h : α = β) (x : α) : (eqToHom h : α ⟶ β) x ≍ x := by
  subst h; rfl

section Setup

variable {A : ExpArrCat.{w + 1, w + 2}} (G : A ⟶ CatExp.{w})

/-- The category of models of `Y`. -/
abbrev MY : Cat.{w, w + 1} := G.functor.obj A.dom

/-- The category of models of `X`. -/
abbrev MX : Cat.{w, w + 1} := G.functor.obj A.cod

/-- The identification of `G Y` with pointed types. -/
abbrev pt : MY G ⥤ Pointed.{w} := G.iso.hom.left.toFunctor

/-- The identification of `G X` with types. -/
abbrev el : MX G ⥤ Type w := G.iso.hom.right.toFunctor

lemma hw : pt G ⋙ forget Pointed = (G.functor.map A.arr).toFunctor ⋙ el G :=
  congrArg Cat.Hom.toFunctor G.iso.hom.w

/-- The distinguished element of `el (G p e)` for `e : G Y`. -/
def mpt (e : MY G) : (el G).obj ((G.functor.map A.arr).toFunctor.obj e) :=
  elPt (pt G) (G.functor.map A.arr).toFunctor (hw G) e

lemma mpt_map {e e' : MY G} (u : e ⟶ e') :
    (el G).map ((G.functor.map A.arr).toFunctor.map u) (mpt G e) = mpt G e' :=
  elPt_map _ _ _ u

lemma pt_eq : pt G = pointify ((G.functor.map A.arr).toFunctor ⋙ el G) (mpt G)
    (fun f => mpt_map G f) := by
  refine CategoryTheory.Functor.hext (fun e => (pointed_mk_cast _ _ _).symm) fun e e' u => ?_
  refine pointed_hom_heq (pointed_mk_cast _ _ _).symm (pointed_mk_cast _ _ _).symm _ _ ?_
  intro x x' hx
  exact heq_map (hw G) u x x' hx

lemma isPullback_G : IsPullback G.iso.hom.left (G.functor.map A.arr) U G.iso.hom.right :=
  IsPullback.of_horiz_isIso ⟨G.iso.hom.w⟩

lemma critG : PointifyCrit (G.functor.map A.arr) G.iso.hom.right (mpt G) := by
  refine pointifyCrit_of_isPullback _ _ _ (fun f => mpt_map G f) ?_
  have : pointifyHom (G.functor.map A.arr) G.iso.hom.right (mpt G) (fun f => mpt_map G f) =
      G.iso.hom.left := Cat.Hom.ext (pt_eq G).symm
  rw [this]
  exact isPullback_G G

end Setup

section Terms

variable {A : ExpArrCat.{w + 1, w + 2}} [LocallySmall.{w} A.carrier] (a : A.carrier)

/-- The set of terms of sort `B`: morphisms `t : a ⟶ Y` with `t ≫ p = B`, shrunk to `Type w`. -/
def Tm (B : a ⟶ A.cod) : Type w := Shrink.{w} {t : a ⟶ A.dom // t ≫ A.arr = B}

/-- The term given by `t : a ⟶ Y`. -/
def tm (t : a ⟶ A.dom) : Tm a (t ≫ A.arr) := equivShrink _ ⟨t, rfl⟩

/-- The morphism `a ⟶ Y` underlying a term. -/
def tmOf {B : a ⟶ A.cod} (s : Tm a B) : {t : a ⟶ A.dom // t ≫ A.arr = B} :=
  (equivShrink _).symm s

lemma tm_heq {t : a ⟶ A.dom} {B : a ⟶ A.cod} (h : t ≫ A.arr = B) :
    tm a t ≍ (equivShrink {t' : a ⟶ A.dom // t' ≫ A.arr = B} ⟨t, h⟩) := by
  subst h; rfl

lemma tm_tmOf {B : a ⟶ A.cod} (s : Tm a B) : tm a (tmOf a s).1 ≍ s := by
  refine (tm_heq a (tmOf a s).2).trans ?_
  simp [tmOf]

lemma val_eq_of_heq {B B' : a ⟶ A.cod} (hB : B = B') (u : {t : a ⟶ A.dom // t ≫ A.arr = B})
    (u' : {t : a ⟶ A.dom // t ≫ A.arr = B'})
    (h : equivShrink _ u ≍ equivShrink _ u') : u.1 = u'.1 := by
  subst hB
  rw [(equivShrink _).injective (eq_of_heq h)]

lemma eq_of_tm_heq {t t' : a ⟶ A.dom} (hB : t ≫ A.arr = t' ≫ A.arr) (h : tm a t ≍ tm a t') :
    t = t' :=
  val_eq_of_heq a hB ⟨t, rfl⟩ ⟨t', rfl⟩ h

lemma eq_of_tm_heq' {t : a ⟶ A.dom} {B : a ⟶ A.cod} (s : Tm a B) (hB : t ≫ A.arr = B)
    (h : tm a t ≍ s) : t = (tmOf a s).1 := by
  refine val_eq_of_heq a hB ⟨t, rfl⟩ (tmOf a s) (h.trans ?_)
  simp [tmOf]

end Terms

section StepA

variable {A : ExpArrCat.{w + 1, w + 2}} [LocallySmall.{w} A.carrier] (a : A.carrier)

/-- The functor `Γ ↦ Disc (a ⟶ Γ)`. -/
abbrev H : A.carrier ⥤ Cat.{w, w + 1} := homDiscFunctor.{w} a

instance preservesPullbacks_H : PreservesLimitsOfShape WalkingCospan (H a) :=
  preservesPullbacks_of_isPullback _ fun _ _ _ _ _ _ _ _ h => homDiscFunctor_isPullback a h

/-- The sorts of the term model, as a functor on `Disc (a ⟶ X)`. -/
def f0Right : (H a).obj A.cod ⟶ Cat.of (Type w) :=
  (Disc.functor (fun B : a ⟶ A.cod => Tm a B)).toCatHom

lemma f0_sec_map {x y : (H a).obj A.dom} (f : x ⟶ y) :
    (f0Right a).toFunctor.map (((H a).map A.arr).toFunctor.map f) (tm a x) = tm a y := by
  obtain ⟨⟨rfl⟩⟩ := f
  rfl

/-- The pointed sets of the term model, as a functor on `Disc (a ⟶ Y)`. -/
abbrev f0Left : (H a).obj A.dom ⟶ Cat.of Pointed.{w} :=
  pointifyHom ((H a).map A.arr) (f0Right a) (fun t => tm a t) (fun f => f0_sec_map a f)

/-- The square at `p` defining the term model. -/
def f0 : Arrow.mk ((H a).map A.arr) ⟶ Arrow.mk CatExp.{w}.arr :=
  Arrow.homMk (f0Left a) (f0Right a) (pointifyHom_comm _ _ _ _)

lemma f0_crit : PointifyCrit ((H a).map A.arr) (f0Right a) (fun t => tm a t) := by
  constructor
  · intro B z
    refine ⟨(tmOf a z).1, ⟨(tmOf a z).2, tm_tmOf a z⟩, fun t ht => ?_⟩
    exact eq_of_tm_heq' a z ht.1 ht.2
  · intro t t' h hcond
    have hB : t ≫ A.arr = t' ≫ A.arr := Disc.eq_of_hom h
    have e : t = t' := by
      refine eq_of_tm_heq a hB ?_
      rw [← hcond]
      exact (types_eqToHom_heq (congrArg (fun B => Tm a B) hB) (tm a t)).symm
    exact ⟨Disc.homOfEq e, Disc.hom_ext _ _, fun _ _ => Disc.hom_ext _ _⟩

lemma hf0 : IsPullback (f0 a).left ((H a).map A.arr) CatExp.{w}.arr (f0 a).right :=
  isPullback_pointify ((H a).map A.arr) (f0Right a) (fun t => tm a t) (fun f => f0_sec_map a f)
    (f0_crit a)

variable {a} (G : A ⟶ CatExp.{w}) (hA : IsBiInitial A)
include hA

lemma existsUnique_alpha : ∃! α : H a ⟶ G.functor, α.app A.dom ≫ G.iso.hom.left = (f0 a).left ∧
    α.app A.cod ≫ G.iso.hom.right = (f0 a).right :=
  haveI := preservesPullbacks_H a
  IsBiInitial.existsUnique_natTrans_iso.{w + 1, w + 2} hA (H a) G (f0 a) (hf0 a)

/-- The natural transformation from `Disc (a ⟶ -)` to the models defining the term model. -/
def alpha : H a ⟶ G.functor := (existsUnique_alpha G hA).exists.choose

lemma alpha_left : (alpha G hA).app A.dom ≫ G.iso.hom.left = (f0 a).left :=
  (existsUnique_alpha G hA).exists.choose_spec.1

lemma alpha_right : (alpha G hA).app A.cod ≫ G.iso.hom.right = (f0 a).right :=
  (existsUnique_alpha G hA).exists.choose_spec.2

lemma alpha_unique (α : H a ⟶ G.functor) (h₁ : α.app A.dom ≫ G.iso.hom.left = (f0 a).left)
    (h₂ : α.app A.cod ≫ G.iso.hom.right = (f0 a).right) : α = alpha G hA :=
  (existsUnique_alpha G hA).unique ⟨h₁, h₂⟩ (existsUnique_alpha G hA).exists.choose_spec

/-- **The initial model** (the term model) of `a`. -/
def zero : ↑(show Cat.{w, w + 1} from G.functor.obj a) := ((alpha G hA).app a).toFunctor.obj (𝟙 a)

lemma alpha_obj {Γ : A.carrier} (σ : a ⟶ Γ) :
    ((alpha G hA).app Γ).toFunctor.obj σ = (G.functor.map σ).toFunctor.obj (zero G hA) := by
  have := Functor.congr_obj (congrArg Cat.Hom.toFunctor ((alpha G hA).naturality σ)) (𝟙 a)
  simp only [Cat.Hom.comp_toFunctor, Functor.comp_obj] at this
  change _ = (G.functor.map σ).toFunctor.obj (((alpha G hA).app a).toFunctor.obj (𝟙 a))
  rw [← this]
  change ((alpha G hA).app Γ).toFunctor.obj σ = ((alpha G hA).app Γ).toFunctor.obj (𝟙 a ≫ σ)
  rw [Category.id_comp]

lemma el_alpha (B : a ⟶ A.cod) :
    (el G).obj (((alpha G hA).app A.cod).toFunctor.obj B) = Tm a B :=
  Functor.congr_obj (congrArg Cat.Hom.toFunctor (alpha_right G hA)) B

lemma mpt_alpha (t : a ⟶ A.dom) :
    mpt G (((alpha G hA).app A.dom).toFunctor.obj t) ≍ tm a t := by
  have h : (pt G).obj (((alpha G hA).app A.dom).toFunctor.obj t) = (⟨Tm a (t ≫ A.arr), tm a t⟩ :
      Pointed.{w}) := Functor.congr_obj (congrArg Cat.Hom.toFunctor (alpha_left G hA)) t
  rw [pt_eq] at h
  exact point_heq_of_eq h

end StepA

end

end InitialModel

end ExpArrCat
