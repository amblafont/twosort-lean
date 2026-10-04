/-
Copyright (c) 2026 Lean Contributor. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Contributor
-/
import CartexpAristotle.InitialModelMorphisms

/-!
# The initial model is initial

Every morphism `g : zero ⟶ ω` induces a natural transformation `gammaOf g : K ω ⟶ G` satisfying
the conditions characterising `gamma ω`; hence `gammaOf g = gamma ω`, and `g` is recovered from
`gamma ω`. This gives uniqueness of morphisms out of `zero`.
-/

open CategoryTheory Limits

universe w

namespace ExpArrCat

namespace InitialModel

open FamOverExpArr PointedForget CatPullback

noncomputable section

lemma comp_heq_comp {C : Type*} [Category C] {x x' y y' z z' : C} (hx : x = x') (hy : y = y')
    (hz : z = z') {f : x ⟶ y} {f' : x' ⟶ y'} {g : y ⟶ z} {g' : y' ⟶ z'} (hf : f ≍ f')
    (hg : g ≍ g') : f ≫ g ≍ f' ≫ g' := by
  subst hx hy hz; cases hf; cases hg; rfl

lemma comp_eqToHom_heq' {C : Type*} [Category C] {x y z : C} (f : x ⟶ y) (e : y = z) :
    (f ≫ eqToHom e) ≍ f := by
  subst e; simp

variable {A : ExpArrCat.{w + 1, w + 2}} [LocallySmall.{w} A.carrier] {a : A.carrier}
  (G : A ⟶ CatExp.{w})

lemma map_comp_heq {Γ Γ' Γ'' : A.carrier} (σ : Γ ⟶ Γ') (τ : Γ' ⟶ Γ'') {x y : (show Cat.{w, w + 1} from G.functor.obj Γ)}
    (g : x ⟶ y) : (G.functor.map (σ ≫ τ)).toFunctor.map g ≍
      (G.functor.map τ).toFunctor.map ((G.functor.map σ).toFunctor.map g) :=
  (heq_of_eq (Functor.congr_hom (congrArg Cat.Hom.toFunctor (G.functor.map_comp σ τ)) g)).trans
    (conj_heq _ _ _)

variable (hA : IsBiInitial A) {ω : Mod G a} (g : zero G hA ⟶ ω)

/-- The components of `g` along the morphisms `σ : a ⟶ Γ`. -/
def theta (Γ : A.carrier) :
    ((alpha G hA).app Γ).toFunctor ⟶ ((beta G ω).app Γ).toFunctor ⋙ 𝟭 _ where
  app σ := eqToHom (alpha_obj G hA σ) ≫ (G.functor.map σ).toFunctor.map g
  naturality σ σ' f := by
    have h := Disc.eq_of_hom f
    subst h
    rw [Disc.hom_ext f (𝟙 _)]
    simp

/-- The components of the natural transformation induced by `g`. -/
def gammaOfApp (Γ : A.carrier) : (K G ω).obj Γ ⟶ G.functor.obj Γ :=
  (Collage.lift ((alpha G hA).app Γ).toFunctor (𝟭 _) (theta G hA g Γ)).toCatHom

lemma alpha_nat_obj {Γ Γ' : A.carrier} (τ : Γ ⟶ Γ') (σ : a ⟶ Γ) :
    ((alpha G hA).app Γ').toFunctor.obj (σ ≫ τ) =
      (G.functor.map τ).toFunctor.obj (((alpha G hA).app Γ).toFunctor.obj σ) :=
  Functor.congr_obj (congrArg Cat.Hom.toFunctor ((alpha G hA).naturality τ)) σ

/-- The natural transformation `K ω ⟶ G` induced by `g`. -/
def gammaOf : K G ω ⟶ G.functor where
  app := gammaOfApp G hA g
  naturality Γ Γ' τ := by
    ext1
    refine CategoryTheory.Functor.hext ?_ ?_
    · rintro (σ | e)
      · exact alpha_nat_obj G hA τ σ
      · rfl
    · rintro (σ | e) (σ' | e') f
      · have hσ : σ = σ' := Disc.eq_of_hom (S := a ⟶ Γ) f
        subst hσ
        have : f = 𝟙 _ := Disc.hom_ext (S := a ⟶ Γ) _ _
        subst this
        rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
        exact congr_arg_heq (fun x => 𝟙 x) (alpha_nat_obj G hA τ σ)
      · have hx : ((alpha G hA).app Γ').toFunctor.obj (σ ≫ τ) =
            (G.functor.map τ).toFunctor.obj ((G.functor.map σ).toFunctor.obj (zero G hA)) :=
          (alpha_nat_obj G hA τ σ).trans (congrArg _ (alpha_obj G hA σ))
        have hy : (G.functor.map (σ ≫ τ)).toFunctor.obj ω =
            (G.functor.map τ).toFunctor.obj ((G.functor.map σ).toFunctor.obj ω) :=
          Functor.congr_obj (congrArg Cat.Hom.toFunctor (G.functor.map_comp σ τ)) ω
        refine HEq.trans (b := (G.functor.map τ).toFunctor.map ((G.functor.map σ).toFunctor.map g) ≫
          (G.functor.map τ).toFunctor.map f) ?_ ?_
        · exact comp_heq_comp hx hy rfl ((eqToHom_comp_heq' _ _).trans (map_comp_heq G σ τ g))
            (eqToHom_comp_heq' _ _)
        · change _ ≍ (G.functor.map τ).toFunctor.map
            ((eqToHom (alpha_obj G hA σ) ≫ (G.functor.map σ).toFunctor.map g) ≫ f)
          rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, eqToHom_map,
            Category.assoc]
          exact (eqToHom_comp_heq' _ _).symm
      · exact PEmpty.elim f
      · exact HEq.rfl

lemma map_heq_of_eq {Γ : A.carrier} {B B' : a ⟶ Γ} (h : B = B') :
    (G.functor.map B).toFunctor.map g ≍ (G.functor.map B').toFunctor.map g := by
  subst h; rfl

lemma map_comp_obj {Γ Γ' Γ'' : A.carrier} (σ : Γ ⟶ Γ') (τ : Γ' ⟶ Γ'')
    (x : (show Cat.{w, w + 1} from G.functor.obj Γ)) :
    (G.functor.map (σ ≫ τ)).toFunctor.obj x =
      (G.functor.map τ).toFunctor.obj ((G.functor.map σ).toFunctor.obj x) :=
  Functor.congr_obj (congrArg Cat.Hom.toFunctor (G.functor.map_comp σ τ)) x

/-- The key computation: `g` acts on the interpretation of terms as expected. -/
lemma el_theta {B : a ⟶ A.cod} (z : (el G).obj (((alpha G hA).app A.cod).toFunctor.obj B))
    (s : Tm a B) (h : z ≍ s) : (el G).map ((theta G hA g A.cod).app B) z = termAt G ω s := by
  set t := (tmOf a s).1
  have ht : t ≫ A.arr = B := (tmOf a s).2
  refine eq_of_heq (HEq.trans ?_ (termAt_heq G ω s).symm)
  have m := mpt_map G ((G.functor.map t).toFunctor.map g)
  refine HEq.trans ?_ (heq_of_eq m)
  refine functor_map_heq (el G) ?_ ?_ ?_ ?_
  · exact (alpha_obj G hA B).trans ((congrArg (fun B => (G.functor.map B).toFunctor.obj (zero G hA))
      ht.symm).trans (map_comp_obj G t A.arr _))
  · exact (congrArg (fun B => (G.functor.map B).toFunctor.obj ω) ht.symm).trans
      (map_comp_obj G t A.arr _)
  · exact (eqToHom_comp_heq' _ _).trans ((map_heq_of_eq G hA g ht.symm).trans
      (map_comp_heq G t A.arr g))
  · exact ((h.trans (tm_tmOf a s).symm).trans (mpt_alpha G hA t).symm).trans
      (congr_arg_heq (mpt G) (alpha_obj G hA t))

lemma gammaOf_right : (gammaOf G hA g).app A.cod ≫ G.iso.hom.right = f1Right G ω := by
  ext1
  refine CategoryTheory.Functor.hext ?_ ?_
  · rintro (B | e)
    · exact el_alpha G hA B
    · rfl
  · rintro (B | e) (B' | e') f
    · have hB : B = B' := Disc.eq_of_hom (S := a ⟶ A.cod) f
      subst hB
      have : f = 𝟙 _ := Disc.hom_ext (S := a ⟶ A.cod) _ _
      subst this
      rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
      exact congr_arg_heq (fun x => 𝟙 x) (el_alpha G hA B)
    · change (el G).map ((theta G hA g A.cod).app B ≫ f) ≍ (termNat G ω).app B ≫ (el G).map f
      rw [CategoryTheory.Functor.map_comp]
      refine Function.hfunext (el_alpha G hA B) fun z s h => ?_
      change (el G).map f ((el G).map ((theta G hA g A.cod).app B) z) ≍
        (el G).map f (termAt G ω s)
      rw [el_theta G hA g z s h]
    · exact PEmpty.elim f
    · exact HEq.rfl

lemma gammaOf_left : (gammaOf G hA g).app A.dom ≫ G.iso.hom.left = (f1 G ω).left := by
  ext1
  change ((gammaOf G hA g).app A.dom).toFunctor ⋙ pt G = _
  rw [pt_eq]
  change pointify (((gammaOf G hA g).app A.dom).toFunctor ⋙ (G.functor.map A.arr).toFunctor ⋙ el G)
    (fun x => mpt G (((gammaOf G hA g).app A.dom).toFunctor.obj x)) (fun f => mpt_map G _) = _
  change _ = pointify (((K G ω).map A.arr).toFunctor ⋙ (f1Right G ω).toFunctor) (sec G ω)
    (fun f => sec_map G ω f)
  refine pointify_ext ?_ ?_
  · have h₁ := congrArg Cat.Hom.toFunctor ((gammaOf G hA g).naturality A.arr)
    have h₂ := congrArg Cat.Hom.toFunctor (gammaOf_right G hA g)
    simp only [Cat.Hom.comp_toFunctor] at h₁ h₂
    change _ = ((K G ω).map A.arr).toFunctor ⋙ (f1Right G ω).toFunctor
    rw [← h₂, ← Functor.assoc, ← h₁]
    rfl
  · rintro (t | e)
    · exact mpt_alpha G hA t
    · exact HEq.rfl

lemma gammaOf_eq : gammaOf G hA g = gamma G hA ω :=
  gamma_unique G hA ω _ (gammaOf_left G hA g) (gammaOf_right G hA g)

lemma gammaOf_crossHom : ((gammaOf G hA g).app a).toFunctor.map (X := .inl (𝟙 a)) (Y := .inr ω)
    (crossHom G ω) ≍ g := by
  change (theta G hA g a).app (𝟙 a) ≫ crossHom G ω ≍ g
  change (eqToHom (alpha_obj G hA (𝟙 a)) ≫ (G.functor.map (𝟙 a)).toFunctor.map g) ≫
    eqToHom (map_id_obj G ω) ≍ g
  rw [Category.assoc]
  refine (eqToHom_comp_heq' _ _).trans ((comp_eqToHom_heq' _ _).trans ?_)
  exact (heq_of_eq (Functor.congr_hom (congrArg Cat.Hom.toFunctor (G.functor.map_id a)) g)).trans
    (conj_heq _ _ _)

/-- **Uniqueness** of morphisms out of the initial model. -/
lemma hom_eq_toModel : g = toModel G hA ω := by
  refine eq_of_heq ((gammaOf_crossHom G hA g).symm.trans ?_)
  rw [gammaOf_eq]
  exact (conj_heq _ _ _).symm

/-- **The initial model is initial.** -/
def isInitialZero : IsInitial (zero (a := a) G hA) :=
  IsInitial.ofUniqueHom (fun ω => toModel G hA ω) (fun ω g => hom_eq_toModel G hA g)

end

end InitialModel

end ExpArrCat
