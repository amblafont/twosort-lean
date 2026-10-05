/-
Copyright (c) 2026 Lean Contributor. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Contributor
-/
import CartexpAristotle.TwoSortFFSquare

/-!
# Models of two-sortified theories: the model `M_Ω` and its morphisms

We continue `CartexpAristotle.TwoSortFFSquare`. By bi-initiality, there is a unique natural
transformation `gammaT : D G K ⟶ G` restricting to the square `sq G K` at `p`. It restricts to the
identity on the second part of the collage (`gammaT_obj_inr`). This yields:

* the model `MOmega G K hA = gammaT_a (inl (𝟙 a))` of `G a` (the object `M_Ω` of
  Proposition "model-faithful" of the appendix): its family is `TmFam a` (`famF_MOmega`), and the
  image of `MOmega` by `G B` (resp. `G t`) is the family of terms with the index `B` (resp. with the
  index `t ≫ p` and the element `t`) (`isoX_MOmega`, `gY_MOmega`);
* a morphism `jHom : MOmega G K hA ⟶ K` whose image on families is the interpretation `psiF G K` of
  the sorts and terms of `a` in `K` (`famF_jHom`).

## References

* [Paper, App. C.1, Prop. `prop:model-faithful`]: `MOmega` is the object `M_Ω`, with
  `famF_MOmega`, `isoX_MOmega`, `gY_MOmega` giving the two items of the proposition.
* `jHom` is used instead of the colax-slice argument of
  [Paper, App. C.2, Prop. `prop:section-terms-two-sortification`].
-/

open CategoryTheory Limits

universe w

namespace Lexp

namespace TwoSortFF

open SemanticTwoSortFunctor PointedForget SliceExp

noncomputable section

variable {A : Lexp.{w + 1, w + 2}} [LocallySmall.{w} A.carrier] (G : A ⟶ C₀.{w})
  {a : A.carrier} (K : GL G a) (hA : IsBiInitial A)

include hA in
lemma existsUnique_gammaT : ∃! γ : D G K ⟶ G.functor,
    γ.app A.dom ≫ G.iso.hom.left = (sq G K).left ∧
      γ.app A.cod ≫ G.iso.hom.right = (sq G K).right :=
  haveI := preservesPullbacks_D G K
  IsBiInitial.existsUnique_natTrans_iso.{w + 1, w + 2} hA (D G K) G (sq G K) (isPullback_sq G K)

/-- The natural transformation out of the collage given by bi-initiality. -/
def gammaT : D G K ⟶ G.functor := (existsUnique_gammaT G K hA).exists.choose

lemma gammaT_left : (gammaT G K hA).app A.dom ≫ G.iso.hom.left = sqY G K :=
  (existsUnique_gammaT G K hA).exists.choose_spec.1

lemma gammaT_right : (gammaT G K hA).app A.cod ≫ G.iso.hom.right = sqX G K :=
  (existsUnique_gammaT G K hA).exists.choose_spec.2

/-- The inclusion of `G` into the collage. -/
def iota₂ : G.functor ⟶ D G K where
  app Γ := Over.homMk (Collage.incl₂ ((betaZ G K).app Γ).toFunctor).toCatHom rfl
  naturality _ _ _ := Over.OverMorphism.ext rfl

omit [LocallySmall.{w} A.carrier] in
lemma isPullback_G₀ : IsPullback G.iso.hom.left (G.functor.map A.arr) C₀.{w}.arr G.iso.hom.right :=
  IsPullback.of_horiz_isIso ⟨G.iso.hom.w⟩

lemma iota₂_sqY : (iota₂ G K).app A.dom ≫ sqY G K = G.iso.hom.left := by
  refine Over.OverMorphism.ext ?_
  change (Collage.incl₂ _).toCatHom ≫ RY G K = G.iso.hom.left.left
  apply pullback.hom_ext
  · rw [Category.assoc, RY_fst]
    exact Cat.Hom.ext (gY_eq G).symm
  · rw [Category.assoc, RY_su', isoY_su']
    rfl

lemma gamma_restrict₂ : iota₂ G K ≫ gammaT G K hA = 𝟙 G.functor := by
  have hu := IsBiInitial.existsUnique_natTrans_iso.{w + 1, w + 2} hA G.functor G G.iso.hom
    (isPullback_G₀ G)
  refine hu.unique ⟨?_, ?_⟩ ⟨by simp, by simp⟩
  · rw [NatTrans.comp_app, Category.assoc, gammaT_left]
    exact iota₂_sqY G K
  · rw [NatTrans.comp_app, Category.assoc, gammaT_right]
    exact Over.OverMorphism.ext rfl

lemma gammaT_obj_inr (e : GL G a) : ((gammaT G K hA).app a).left.toFunctor.obj (.inr e) = e :=
  Functor.congr_obj (congrArg (fun (T : G.functor ⟶ G.functor) => (T.app a).left.toFunctor)
    (gamma_restrict₂ G K hA)) e

/-- **The model `M_Ω`** of the appendix: the image of `inl (𝟙 a)`.

[Paper, App. C.1, Prop. `prop:model-faithful`]: the object `M_Ω`. -/
def MOmega : GL G a := ((gammaT G K hA).app a).left.toFunctor.obj (.inl (𝟙 a))

lemma famF_MOmega : (famF G a).obj (MOmega G K hA) = TmFam a :=
  Functor.congr_obj (congrArg Cat.Hom.toFunctor (Over.w ((gammaT G K hA).app a))) (.inl (𝟙 a))

lemma Gm_MOmega {Γ : A.carrier} (σ : a ⟶ Γ) :
    (Gm G σ).obj (MOmega G K hA) = ((gammaT G K hA).app Γ).left.toFunctor.obj (.inl σ) := by
  have h := Functor.congr_obj (congrArg (fun T => T.left.toFunctor)
    ((gammaT G K hA).naturality σ)) (.inl (𝟙 a))
  refine h.symm.trans ?_
  change ((gammaT G K hA).app Γ).left.toFunctor.obj (.inl (𝟙 a ≫ σ)) = _
  rw [Category.id_comp]

/-- The image of `M_Ω` by `G B` is the family of terms with the index `B`. -/
lemma isoX_MOmega (B : a ⟶ A.cod) : (isoX G).obj ((Gm G B).obj (MOmega G K hA)) = tmElt B := by
  rw [Gm_MOmega]
  exact Functor.congr_obj (congrArg (fun T => T.left.toFunctor) (gammaT_right G K hA)) (.inl B)

/-- The image of `M_Ω` by `G t` is the family of terms with the index `t ≫ p` and the
element `t`. -/
lemma gY_MOmega (t : a ⟶ A.dom) : (gY G).obj ((Gm G t).obj (MOmega G K hA)) =
    (⟨TmS a (shX a (t ≫ A.arr)), tmS a t⟩ : Pointed.{w}) := by
  rw [Gm_MOmega]
  have h₁ := Functor.congr_obj (congrArg (fun T => T.left.toFunctor) (gammaT_left G K hA)) (.inl t)
  have h₂ := Functor.congr_obj (congrArg Cat.Hom.toFunctor (RY_fst G K)) (.inl t)
  change (pullback.fst U.{w} (sE U.{w})).toFunctor.obj
    ((isoY G).obj (((gammaT G K hA).app A.dom).left.toFunctor.obj (.inl t))) = _
  exact (congrArg _ h₁).trans h₂

/-- The canonical morphism from `inl (𝟙 a)` to `inr K` in the collage at `a`. -/
def crossT : Collage.Hom ((betaZ G K).app a).toFunctor (.inl (𝟙 a)) (.inr K) :=
  (eqToHom (Gm_id_obj G a K) : (Gm G (𝟙 a)).obj K ⟶ K)

/-- The morphism from `M_Ω` to `K`. -/
def jHom : MOmega G K hA ⟶ K :=
  ((gammaT G K hA).app a).left.toFunctor.map (X := .inl (𝟙 a)) (Y := .inr K) (crossT G K) ≫
    eqToHom (gammaT_obj_inr G K hA K)

/-- The image of `jHom` on families is the interpretation of the sorts and terms of `a`
in `K`. -/
lemma famF_jHom : (famF G a).map (jHom G K hA) = eqToHom (famF_MOmega G K hA) ≫ psiF G K := by
  have h := Functor.congr_hom (congrArg Cat.Hom.toFunctor (Over.w ((gammaT G K hA).app a)))
    (X := .inl (𝟙 a)) (Y := .inr K) (crossT G K)
  simp only [Cat.Hom.comp_toFunctor, Functor.comp_map] at h
  rw [jHom, Functor.map_comp, h]
  change (eqToHom _ ≫ ((psiF G K ≫ eqToHom _) ≫ (famF G a).map (eqToHom _)) ≫ eqToHom _) ≫
    (famF G a).map (eqToHom _) = _
  simp [eqToHom_map]

end

end TwoSortFF

end Lexp
