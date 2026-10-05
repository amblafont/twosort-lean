/-
Copyright (c) 2026 Lean Contributor. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Contributor
-/
import CartexpAristotle.InitialModel

/-!
# Morphisms out of the initial model

We continue `CartexpAristotle.InitialModel`. Fix a model `ω` of `a`. It determines the natural
transformation `beta ω : Disc (a ⟶ -) ⟶ G`, `σ ↦ G σ ω`, and we consider the collage
`K ω = Collage.functor (beta ω)`. A natural transformation `K ω ⟶ G` restricting to the term model
on `Disc (a ⟶ -)` and to the identity on `G` amounts to a morphism `zero ⟶ ω`. Such natural
transformations are unique by bi-initiality, which shows that `zero` is initial.

## References

* [Paper, App. B, Prop. `prop:initial-model-gat-morphism-existence`]: the morphism
  `toModel : 0_Ω ⟶ ω` (the morphism `i` of the paper). The paper obtains it from a natural
  transformation into `cod_- ∘ M` ([Paper, App. B, Prop. `prop:arrow-functor-lexp`]); here
  it comes from a natural transformation out of a collage instead.
-/

open CategoryTheory Limits

universe w

namespace Lexp

namespace InitialModel

open SemanticTwoSortFunctor PointedForget

noncomputable section

lemma functor_map_eqToHom_heq {C : Type*} [Category C] (F : C ⥤ Type w) {x y : C} (h : x = y)
    (z : F.obj x) : F.map (eqToHom h) z ≍ z := by
  subst h; simp

lemma functor_map_heq {C : Type*} [Category C] (F : C ⥤ Type w) {x x' y y' : C} (hx : x = x')
    (hy : y = y') {f : x ⟶ y} {f' : x' ⟶ y'} (hf : f ≍ f') {z : F.obj x} {z' : F.obj x'}
    (hz : z ≍ z') : F.map f z ≍ F.map f' z' := by
  subst hx hy; cases hf; cases hz; rfl

variable {A : Lexp.{w + 1, w + 2}} [LocallySmall.{w} A.carrier] {a : A.carrier}
  (G : A ⟶ CatLexp.{w})

/-- The category of models of `a`. -/
abbrev Mod (a : A.carrier) : Cat.{w, w + 1} := G.functor.obj a

section Beta

variable (ω : Mod G a)

/-- The model `ω` as a natural transformation `Disc (a ⟶ -) ⟶ G`. -/
def beta : H a ⟶ G.functor where
  app Γ := (Disc.functor (fun σ : a ⟶ Γ => (G.functor.map σ).toFunctor.obj ω)).toCatHom
  naturality Γ Γ' τ := by
    ext1
    refine CategoryTheory.Functor.ext (fun σ => ?_) (fun σ σ' f => ?_)
    · exact Functor.congr_obj (congrArg Cat.Hom.toFunctor (G.functor.map_comp σ τ)) ω
    · have h := Disc.eq_of_hom f
      subst h
      rw [Disc.hom_ext f (𝟙 _)]
      simp

/-- The collage of `beta ω`. -/
abbrev K : A.carrier ⥤ Cat.{w, w + 1} := Collage.functor (beta G ω)

instance preservesPullbacks_K : PreservesLimitsOfShape WalkingCospan (K G ω) :=
  preservesPullbacks_of_isPullback _ fun _ _ _ _ _ _ _ _ h =>
    Collage.functor_isPullback _ h.w (homDiscFunctor_isPullback a h) (h.map G.functor)

lemma beta_nat_obj (t : a ⟶ A.dom) :
    (G.functor.map (t ≫ A.arr)).toFunctor.obj ω =
      (G.functor.map A.arr).toFunctor.obj ((G.functor.map t).toFunctor.obj ω) :=
  Functor.congr_obj (congrArg Cat.Hom.toFunctor (G.functor.map_comp t A.arr)) ω

/-- The interpretation in `ω` of a term of sort `B`. -/
def termAt {B : a ⟶ A.cod} (s : Tm a B) : (el G).obj ((G.functor.map B).toFunctor.obj ω) :=
  cast (congrArg (el G).obj ((beta_nat_obj G ω _).symm.trans
    (congrArg (fun B => (G.functor.map B).toFunctor.obj ω) (tmOf a s).2)))
    (mpt G ((G.functor.map (tmOf a s).1).toFunctor.obj ω))

lemma termAt_heq {B : a ⟶ A.cod} (s : Tm a B) :
    termAt G ω s ≍ mpt G ((G.functor.map (tmOf a s).1).toFunctor.obj ω) :=
  cast_heq _ _

lemma termAt_heq' (t : a ⟶ A.dom) {B : a ⟶ A.cod} (s : Tm a B) (hB : t ≫ A.arr = B)
    (hs : tm a t ≍ s) : termAt G ω s ≍ mpt G ((G.functor.map t).toFunctor.obj ω) := by
  rw [eq_of_tm_heq' a s hB hs]
  exact termAt_heq G ω s

/-- The interpretation of terms, as a natural transformation. -/
def termNat : (Disc.functor (fun B : a ⟶ A.cod => Tm a B) : Disc (a ⟶ A.cod) ⥤ Type w) ⟶
    ((beta G ω).app A.cod).toFunctor ⋙ el G where
  app B := fun s => termAt G ω s
  naturality B B' f := by
    have h := Disc.eq_of_hom f
    subst h
    rw [Disc.hom_ext f (𝟙 _)]
    simp

/-- The right component of the square at `p` for the collage. -/
def f1Right : (K G ω).obj A.cod ⟶ Cat.of (Type w) :=
  (Collage.lift (Disc.functor (fun B : a ⟶ A.cod => Tm a B)) (el G) (termNat G ω)).toCatHom

/-- The distinguished elements over the collage at `Y`. -/
def sec : (x : (K G ω).obj A.dom) →
    (f1Right G ω).toFunctor.obj (((K G ω).map A.arr).toFunctor.obj x)
  | .inl t => tm a t
  | .inr e => mpt G e

lemma sec_map {x y : (K G ω).obj A.dom} (f : x ⟶ y) :
    (f1Right G ω).toFunctor.map (((K G ω).map A.arr).toFunctor.map f) (sec G ω x) = sec G ω y := by
  rcases x with t | e <;> rcases y with t' | e'
  · obtain ⟨⟨rfl⟩⟩ := f
    rfl
  · change (el G).map (eqToHom _ ≫ (G.functor.map A.arr).toFunctor.map f)
      (termAt G ω (tm a t)) = mpt G e'
    rw [Functor.map_comp, types_comp_apply]
    have : (el G).map (eqToHom (beta_nat_obj G ω t)) (termAt G ω (tm a t)) =
        mpt G ((G.functor.map t).toFunctor.obj ω) :=
      eq_of_heq ((functor_map_eqToHom_heq _ _ _).trans
        (termAt_heq' G ω t (tm a t) rfl HEq.rfl))
    rw [this]
    exact mpt_map G f
  · exact PEmpty.elim f
  · exact mpt_map G f

/-- The left component of the square at `p` for the collage. -/
abbrev f1Left : (K G ω).obj A.dom ⟶ Cat.of Pointed.{w} :=
  pointifyHom ((K G ω).map A.arr) (f1Right G ω) (sec G ω) (fun f => sec_map G ω f)

/-- The square at `p` for the collage. -/
def f1 : Arrow.mk ((K G ω).map A.arr) ⟶ Arrow.mk CatLexp.{w}.arr :=
  Arrow.homMk (f1Left G ω) (f1Right G ω) (pointifyHom_comm _ _ _ _)

lemma f1_crit : PointifyCrit ((K G ω).map A.arr) (f1Right G ω) (sec G ω) := by
  constructor
  · intro x z
    rcases x with B | e'
    · refine ⟨.inl (tmOf a z).1, ⟨congrArg Sum.inl (tmOf a z).2, tm_tmOf a z⟩, ?_⟩
      rintro (t | e) ⟨h₁, h₂⟩
      · exact congrArg Sum.inl (eq_of_tm_heq' a z (Sum.inl.inj h₁) h₂)
      · cases h₁
    · obtain ⟨e, ⟨he₁, he₂⟩, hu⟩ := (critG G).obj e' z
      refine ⟨.inr e, ⟨congrArg Sum.inr he₁, he₂⟩, ?_⟩
      rintro (t | e'') ⟨h₁, h₂⟩
      · cases h₁
      · exact congrArg Sum.inr (hu e'' ⟨Sum.inr.inj h₁, h₂⟩)
  · intro x y h hcond
    rcases x with t | e <;> rcases y with t' | e'
    · have hB : t ≫ A.arr = t' ≫ A.arr := Disc.eq_of_hom h
      change (f1Right G ω).toFunctor.map h (tm a t) = tm a t' at hcond
      have e : t = t' := by
        refine eq_of_tm_heq a hB ?_
        rw [← hcond]
        exact (types_eqToHom_heq (congrArg (fun B => Tm a B) hB) (tm a t)).symm
      exact ⟨Disc.homOfEq e, Disc.hom_ext _ _, fun _ _ => Disc.hom_ext _ _⟩
    · have c := beta_nat_obj G ω t
      have hcond' : (el G).map (eqToHom c.symm ≫ h) (mpt G ((G.functor.map t).toFunctor.obj ω)) =
          mpt G e' := by
        rw [Functor.map_comp, types_comp_apply]
        have : (el G).map (eqToHom c.symm) (mpt G ((G.functor.map t).toFunctor.obj ω)) =
            termAt G ω (tm a t) :=
          eq_of_heq ((functor_map_eqToHom_heq _ _ _).trans
            (termAt_heq' G ω t (tm a t) rfl HEq.rfl).symm)
        rw [this]
        exact hcond
      obtain ⟨k, hk, hu⟩ := (critG G).hom _ _ _ hcond'
      refine ⟨(k : Collage.Hom ((beta G ω).app A.dom).toFunctor (.inl t) (.inr e')), ?_, fun k' hk' => hu k' ?_⟩
      · change eqToHom _ ≫ (G.functor.map A.arr).toFunctor.map k = h
        rw [hk]; simp
      · change eqToHom _ ≫ (G.functor.map A.arr).toFunctor.map k' = h at hk'
        rw [← hk']; simp
    · exact PEmpty.elim h
    · exact (critG G).hom e e' h hcond

lemma hf1 : IsPullback (f1 G ω).left ((K G ω).map A.arr) CatLexp.{w}.arr (f1 G ω).right :=
  isPullback_pointify _ (f1Right G ω) (sec G ω) (fun f => sec_map G ω f) (f1_crit G ω)

lemma map_id_obj : (G.functor.map (𝟙 a)).toFunctor.obj ω = ω :=
  Functor.congr_obj (congrArg Cat.Hom.toFunctor (G.functor.map_id a)) ω

/-- The canonical morphism from `inl (𝟙 a)` to `inr ω` in the collage at `a`. -/
def crossHom : Collage.Hom ((beta G ω).app a).toFunctor (.inl (𝟙 a)) (.inr ω) :=
  (eqToHom (map_id_obj G ω) : (G.functor.map (𝟙 a)).toFunctor.obj ω ⟶ ω)

end Beta

section Gamma

variable (hA : HasUniversalNatTrans G) (ω : Mod G a)
include hA

lemma existsUnique_gamma : ∃! γ : K G ω ⟶ G.functor,
    γ.app A.dom ≫ G.iso.hom.left = (f1 G ω).left ∧ γ.app A.cod ≫ G.iso.hom.right = (f1 G ω).right :=
  haveI := preservesPullbacks_K G ω
  hA.existsUnique_iso (K G ω) (f1 G ω) (hf1 G ω)

/-- The natural transformation out of the collage given by bi-initiality. -/
def gamma : K G ω ⟶ G.functor := (existsUnique_gamma G hA ω).exists.choose

lemma gamma_left : (gamma G hA ω).app A.dom ≫ G.iso.hom.left = (f1 G ω).left :=
  (existsUnique_gamma G hA ω).exists.choose_spec.1

lemma gamma_right : (gamma G hA ω).app A.cod ≫ G.iso.hom.right = (f1 G ω).right :=
  (existsUnique_gamma G hA ω).exists.choose_spec.2

lemma gamma_unique (γ : K G ω ⟶ G.functor) (h₁ : γ.app A.dom ≫ G.iso.hom.left = (f1 G ω).left)
    (h₂ : γ.app A.cod ≫ G.iso.hom.right = (f1 G ω).right) : γ = gamma G hA ω :=
  (existsUnique_gamma G hA ω).unique ⟨h₁, h₂⟩ (existsUnique_gamma G hA ω).exists.choose_spec

lemma gamma_restrict₁ : Collage.ι₁ (beta G ω) ≫ gamma G hA ω = alpha G hA := by
  refine alpha_unique G hA _ ?_ ?_
  · rw [NatTrans.comp_app, Category.assoc]
    change _ ≫ ((gamma G hA ω).app A.dom ≫ G.iso.hom.left) = _
    rw [gamma_left]; rfl
  · rw [NatTrans.comp_app, Category.assoc]
    change _ ≫ ((gamma G hA ω).app A.cod ≫ G.iso.hom.right) = _
    rw [gamma_right]; rfl

lemma gamma_restrict₂ : Collage.ι₂ (beta G ω) ≫ gamma G hA ω = 𝟙 G.functor := by
  have hu := hA.existsUnique_iso G.functor G.iso.hom
    (isPullback_G G)
  refine hu.unique ⟨?_, ?_⟩ ⟨by simp, by simp⟩
  · rw [NatTrans.comp_app, Category.assoc]
    change _ ≫ ((gamma G hA ω).app A.dom ≫ G.iso.hom.left) = _
    rw [gamma_left]
    exact Cat.Hom.ext (pt_eq G).symm
  · rw [NatTrans.comp_app, Category.assoc]
    change _ ≫ ((gamma G hA ω).app A.cod ≫ G.iso.hom.right) = _
    rw [gamma_right]; rfl

lemma gamma_obj_inl (σ : a ⟶ a) :
    ((gamma G hA ω).app a).toFunctor.obj (.inl σ) = ((alpha G hA).app a).toFunctor.obj σ :=
  Functor.congr_obj (congrArg Cat.Hom.toFunctor
    (congrArg (fun T => NatTrans.app T a) (gamma_restrict₁ G hA ω))) σ

lemma gamma_obj_inr (e : Mod G a) : ((gamma G hA ω).app a).toFunctor.obj (.inr e) = e :=
  Functor.congr_obj (congrArg Cat.Hom.toFunctor
    (congrArg (fun T => NatTrans.app T a) (gamma_restrict₂ G hA ω))) e

/-- **Existence** of a morphism from the initial model to `ω`.

[Paper, App. B, Prop. `prop:initial-model-gat-morphism-existence`]: the morphism `i : 0_Ω ⟶ ω`. -/
def toModel : zero G hA ⟶ ω :=
  eqToHom (gamma_obj_inl G hA ω (𝟙 a)).symm ≫ ((gamma G hA ω).app a).toFunctor.map (X := .inl (𝟙 a)) (Y := .inr ω) (crossHom G ω) ≫
    eqToHom (gamma_obj_inr G hA ω ω)

end Gamma

end

end InitialModel

end Lexp
