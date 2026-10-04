/-
Copyright (c) 2026 Lean Contributor. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Contributor
-/
import CartexpAristotle.TwoSortFFSetup

/-!
# Models of two-sortified theories: the family of terms and the collage

We continue `CartexpAristotle.TwoSortFFSetup`. Fix an object `a` of `A` (the theory `Ω` of the
appendix) and a model `K` of `G a`.

* `TmFam a`: the family of terms of `a`, `(Tm B)_{B : a ⟶ X}` (the family `Tm_Ω` of the
  appendix), with `TmS b` the terms of sort `b`.
* `ixX G B K`, `elY G t K`: the interpretation in `K` of a sort `B : a ⟶ X` (an index of the family
  of `K`) and of a term `t : a ⟶ Y` (an element of the corresponding fibre).
* `psiF G K : TmFam a ⟶ famF G a K`: the interpretation of all sorts and terms of `a` in `K`.
* `D G K`: the functor `Γ ↦ Collage (σ ↦ G σ K)` over families of types, where the sorts `σ` lie
  over `TmFam a` and the arrows `σ ⟶ e` lie over `psiF G K` followed by the family of the arrow.
-/

open CategoryTheory Limits

universe w

namespace ExpArrCat

namespace TwoSortFF

open FamOverExpArr PointedForget SliceExp

noncomputable section

section Terms

variable {A : ExpArrCat.{w + 1, w + 2}} [LocallySmall.{w} A.carrier] (a : A.carrier)

/-- A sort of `a`, shrunk to `Type w`. -/
abbrev shX (B : a ⟶ A.cod) : Shrink.{w} (a ⟶ A.cod) := equivShrink _ B

/-- The sort of `a` underlying a shrunk sort. -/
abbrev unX (b : Shrink.{w} (a ⟶ A.cod)) : a ⟶ A.cod := (equivShrink _).symm b

/-- The terms of sort `b`. -/
def TmS (b : Shrink.{w} (a ⟶ A.cod)) : Type w :=
  Shrink.{w} {t : a ⟶ A.dom // equivShrink _ (t ≫ A.arr) = b}

/-- The term given by `t : a ⟶ Y`. -/
def tmS (t : a ⟶ A.dom) : TmS a (shX a (t ≫ A.arr)) := equivShrink _ ⟨t, rfl⟩

/-- The morphism `a ⟶ Y` underlying a term. -/
def tmSOf {b : Shrink.{w} (a ⟶ A.cod)} (s : TmS a b) :
    {t : a ⟶ A.dom // equivShrink _ (t ≫ A.arr) = b} :=
  (equivShrink _).symm s

lemma tmSOf_arr {b : Shrink.{w} (a ⟶ A.cod)} (s : TmS a b) : (tmSOf a s).1 ≫ A.arr = unX a b :=
  ((Equiv.symm_apply_eq _).2 (tmSOf a s).2.symm).symm

lemma tmS_heq {t : a ⟶ A.dom} {b : Shrink.{w} (a ⟶ A.cod)} (h : equivShrink _ (t ≫ A.arr) = b) :
    tmS a t ≍ (equivShrink {t' : a ⟶ A.dom // equivShrink _ (t' ≫ A.arr) = b} ⟨t, h⟩) := by
  subst h; rfl

lemma tmS_tmSOf {b : Shrink.{w} (a ⟶ A.cod)} (s : TmS a b) : tmS a (tmSOf a s).1 ≍ s := by
  refine (tmS_heq a (tmSOf a s).2).trans ?_
  simp [tmSOf]

lemma valS_eq_of_heq {b b' : Shrink.{w} (a ⟶ A.cod)} (hb : b = b')
    (u : {t : a ⟶ A.dom // equivShrink _ (t ≫ A.arr) = b})
    (u' : {t : a ⟶ A.dom // equivShrink _ (t ≫ A.arr) = b'})
    (h : equivShrink _ u ≍ equivShrink _ u') : u.1 = u'.1 := by
  subst hb
  rw [(equivShrink _).injective (eq_of_heq h)]

lemma eq_of_tmS_heq {t t' : a ⟶ A.dom} (hB : t ≫ A.arr = t' ≫ A.arr) (h : tmS a t ≍ tmS a t') :
    t = t' :=
  valS_eq_of_heq a (congrArg _ hB) ⟨t, rfl⟩ ⟨t', rfl⟩ h

lemma eq_of_tmS_heq' {t : a ⟶ A.dom} {b : Shrink.{w} (a ⟶ A.cod)} (s : TmS a b)
    (hb : shX a (t ≫ A.arr) = b) (h : tmS a t ≍ s) : t = (tmSOf a s).1 := by
  refine valS_eq_of_heq a hb ⟨t, rfl⟩ (tmSOf a s) (h.trans ?_)
  simp [tmSOf]

/-- The family of terms of `a`: the family `(Tm B)_{B : a ⟶ X}`. -/
def TmFam : FormalCoproduct.{w} (Type w) := ⟨Shrink.{w} (a ⟶ A.cod), TmS a⟩

end Terms

section Readouts

variable {A : ExpArrCat.{w + 1, w + 2}} (G : A ⟶ C₀.{w}) {a : A.carrier}

lemma famF_map_obj {Γ Γ' : A.carrier} (σ : Γ ⟶ Γ') (K : GL G Γ) :
    (famF G Γ').obj ((Gm G σ).obj K) = (famF G Γ).obj K :=
  Functor.congr_obj (congrArg Cat.Hom.toFunctor (Over.w (G.functor.map σ))) K

lemma famF_map_heq {Γ Γ' : A.carrier} (σ : Γ ⟶ Γ') {x y : GL G Γ} (f : x ⟶ y) :
    (famF G Γ').map ((Gm G σ).map f) ≍ (famF G Γ).map f := by
  have := Functor.congr_hom (congrArg Cat.Hom.toFunctor (Over.w (G.functor.map σ))) f
  exact (heq_of_eq this).trans (CatPullback.conj_heq _ _ _)

lemma isoX_fst (e : GL G A.cod) : ((isoX G).obj e).1 = (famF G A.cod).obj e :=
  Functor.congr_obj (congrArg Cat.Hom.toFunctor (isoX_hom G)) e

lemma ixX_eq (B : a ⟶ A.cod) (K : GL G a) :
    ((isoX G).obj ((Gm G B).obj K)).1 = (famF G a).obj K :=
  (isoX_fst G _).trans (famF_map_obj G B K)

/-- The interpretation of a sort `B : a ⟶ X` in a model `K`: an index of the family of `K`. -/
def ixX (B : a ⟶ A.cod) (K : GL G a) : ((famF G a).obj K).I :=
  cast (congrArg FormalCoproduct.I (ixX_eq G B K)) ((isoX G).obj ((Gm G B).obj K)).2

lemma ixX_heq (B : a ⟶ A.cod) (K : GL G a) : ixX G B K ≍ ((isoX G).obj ((Gm G B).obj K)).2 :=
  cast_heq _ _

lemma fc_obj_cast {F F' : FormalCoproduct.{w} (Type w)} (h : F = F') (i : F.I) :
    F.obj i = F'.obj (cast (congrArg FormalCoproduct.I h) i) := by
  subst h; rfl

lemma gX_obj_eq (B : a ⟶ A.cod) (K : GL G a) :
    (gX G).obj ((Gm G B).obj K) = ((famF G a).obj K).obj (ixX G B K) :=
  fc_obj_cast (ixX_eq G B K) _

lemma Gm_comp_obj {Γ Γ' Γ'' : A.carrier} (σ : Γ ⟶ Γ') (τ : Γ' ⟶ Γ'') (K : GL G Γ) :
    (Gm G (σ ≫ τ)).obj K = (Gm G τ).obj ((Gm G σ).obj K) :=
  Functor.congr_obj (congrArg (fun F => F.left.toFunctor) (G.functor.map_comp σ τ)) K

lemma Gm_id_obj (Γ : A.carrier) (K : GL G Γ) : (Gm G (𝟙 Γ)).obj K = K :=
  Functor.congr_obj (congrArg (fun F => F.left.toFunctor) (G.functor.map_id Γ)) K

/-- The interpretation of a term `t : a ⟶ Y` in a model `K`: an element of the fibre of the
family of `K` at the interpretation of the sort `t ≫ p`. -/
def elY (t : a ⟶ A.dom) (K : GL G a) : ((famF G a).obj K).obj (ixX G (t ≫ A.arr) K) :=
  cast ((congrArg (gX G).obj (Gm_comp_obj G t A.arr K)).symm.trans (gX_obj_eq G _ K))
    (mptG G ((Gm G t).obj K))

lemma elY_heq (t : a ⟶ A.dom) (K : GL G a) : elY G t K ≍ mptG G ((Gm G t).obj K) :=
  cast_heq _ _

variable [LocallySmall.{w} A.carrier]

/-- The interpretation in `K` of all sorts and terms of `a`, as a morphism of families. -/
def psiF (K : GL G a) : TmFam a ⟶ (famF G a).obj K where
  f b := ixX G (unX a b) K
  φ _ := fun s => cast (congrArg (fun B => ((famF G a).obj K).obj (ixX G B K)) (tmSOf_arr a s))
    (elY G (tmSOf a s).1 K)

lemma psiF_f (K : GL G a) (b : Shrink.{w} (a ⟶ A.cod)) : (psiF G K).f b = ixX G (unX a b) K := rfl

lemma psiF_φ_heq (K : GL G a) {b : Shrink.{w} (a ⟶ A.cod)} (s : TmS a b) :
    (psiF G K).φ b s ≍ elY G (tmSOf a s).1 K :=
  cast_heq _ _

end Readouts

section Collage

variable {A : ExpArrCat.{w + 1, w + 2}} [LocallySmall.{w} A.carrier] (G : A ⟶ C₀.{w})
  {a : A.carrier} (K : GL G a)

/-- The model `K` as a natural transformation `Disc (a ⟶ -) ⟶ G`, `σ ↦ G σ K`. -/
def betaZ : homDiscFunctor.{w} a ⟶ G.functor ⋙ Over.forget 𝔽.{w} where
  app Γ := (Disc.functor (fun σ : a ⟶ Γ => (Gm G σ).obj K)).toCatHom
  naturality Γ Γ' τ := by
    ext1
    refine CategoryTheory.Functor.ext (fun σ => ?_) (fun σ σ' f => ?_)
    · exact Gm_comp_obj G σ τ K
    · have h := Disc.eq_of_hom f
      subst h
      rw [Disc.hom_ext f (𝟙 _)]
      simp

/-- The structure maps of the arrows `σ ⟶ e` of the collage. -/
def kappa (Γ : A.carrier) :
    (Functor.const (Disc (a ⟶ Γ))).obj (TmFam a) ⟶ ((betaZ G K).app Γ).toFunctor ⋙ famF G Γ where
  app σ := psiF G K ≫ eqToHom (famF_map_obj G σ K).symm
  naturality σ σ' f := by
    have h := Disc.eq_of_hom f
    subst h
    rw [Disc.hom_ext f (𝟙 _)]
    simp

/-- The functor from the collage at `Γ` to families of types. -/
def ell (Γ : A.carrier) : Collage ((betaZ G K).app Γ).toFunctor ⥤ FormalCoproduct.{w} (Type w) :=
  Collage.lift ((Functor.const (Disc (a ⟶ Γ))).obj (TmFam a)) (famF G Γ) (kappa G K Γ)

lemma ell_w {Γ Γ' : A.carrier} (τ : Γ ⟶ Γ') :
    (Collage.functor (betaZ G K)).map τ ≫ (ell G K Γ').toCatHom = (ell G K Γ).toCatHom := by
  refine Cat.Hom.ext (CategoryTheory.Functor.hext ?_ ?_)
  · rintro (σ | e)
    · rfl
    · exact famF_map_obj G τ e
  · rintro (σ | e) (σ' | e') f
    · have h := Disc.eq_of_hom (S := a ⟶ Γ) f
      subst h
      have : f = 𝟙 _ := Disc.hom_ext (S := a ⟶ Γ) _ _
      subst this
      exact HEq.rfl
    · change (psiF G K ≫ eqToHom _) ≫ (famF G Γ').map (eqToHom _ ≫ (Gm G τ).map f) ≍
        (psiF G K ≫ eqToHom _) ≫ (famF G Γ).map f
      rw [Functor.map_comp, eqToHom_map, Category.assoc, Category.assoc]
      refine InitialModel.comp_heq_comp rfl rfl (famF_map_obj G τ e') HEq.rfl ?_
      refine (eqToHom_comp_heq' _ _).trans ?_
      refine (eqToHom_comp_heq' _ _).trans ?_
      exact (famF_map_heq G τ f).trans (eqToHom_comp_heq' _ _).symm
    · exact PEmpty.elim f
    · exact famF_map_heq G τ f

/-- The functor `Γ ↦ Collage (σ ↦ G σ K)` to the slice over families of types. -/
def D : A.carrier ⥤ Over 𝔽.{w} where
  obj Γ := Over.mk (ell G K Γ).toCatHom
  map τ := Over.homMk ((Collage.functor (betaZ G K)).map τ) (ell_w G K τ)
  map_id Γ := Over.OverMorphism.ext ((Collage.functor (betaZ G K)).map_id Γ)
  map_comp σ τ := Over.OverMorphism.ext ((Collage.functor (betaZ G K)).map_comp σ τ)

lemma D_forget : D G K ⋙ Over.forget 𝔽.{w} = Collage.functor (betaZ G K) := rfl

end Collage

end

end TwoSortFF

end ExpArrCat
