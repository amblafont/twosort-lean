/-
Copyright (c) 2026 Lean Contributor. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Contributor
-/
import CartexpAristotle.ExpArrCat

/-!
# Strict morphisms of `ExpArrCat`

A morphism `F : A ⟶ B` of `ExpArrCat` is *strict* when its isomorphism `F.iso` between the
image of the chosen arrow of `A` and the chosen arrow of `B` is an identity, i.e. an `eqToIso`.

We show that, when the domain and codomain of the chosen arrow of `A` are distinct, every
morphism `A ⟶ B` is isomorphic (by an invertible 2-cell) to a strict one.
-/

open CategoryTheory Limits

universe v u

section Transport

variable {C : Type*} [Category C] {D : Type*} [Category D] {X Y : C} {u : Y ⟶ X}

/-- Universality of `Data` is invariant under postcomposing the counit with an isomorphism. -/
@[reducible]
noncomputable def universal_epsilon_iso {c c' : C} (d : Data u c) [Universal d] (φ : c ≅ c') :
    Universal (⟨d.P, d.pi, d.Pbk, d.epsilon ≫ φ.hom⟩ : Data u c') where
  mor g := Universal.mor (data := d) (g ≫ φ.inv)
  isSlice g := Universal.isSlice (data := d) (g ≫ φ.inv)
  comm g := by
    have h := Universal.comm (data := d) (g ≫ φ.inv)
    change g = FBF_on_mor d _ _ ≫ d.epsilon ≫ φ.hom
    rw [← Category.assoc, ← h]
    simp
  uniq Kufp eq_fp eq_gp eq := by
    refine Universal.uniq (data := d) Kufp eq_fp eq_gp ?_
    have := congrArg (· ≫ φ.inv) eq
    simpa using this

/-- If `d₂` is isomorphic over `X` to a universal `d₁` compatibly with the counits,
then `d₂` is universal. -/
@[reducible]
noncomputable def universal_of_iso {c : C} (d₁ : Data u c) [Universal d₁] (d₂ : Data u c)
    (φ : d₂.P ≅ d₁.P) (hpi : d₂.pi = φ.hom ≫ d₁.pi)
    (heps : d₂.epsilon = FBF_on_mor d₁ d₂.Pbk hpi ≫ d₁.epsilon) : Universal d₂ :=
  have h : canonical_mor d₁ d₂ = φ.hom := (mor_unique d₂.epsilon φ.hom hpi heps).symm
  have : IsIso (canonical_mor d₁ d₂) := by rw [h]; infer_instance
  canonical_mor_iso_lift d₁ d₂

/-- Preservation of an exponentiable arrow is invariant under natural isomorphism. -/
@[reducible]
noncomputable def functorPreserves_of_natIso (F G : C ⥤ D) (e : F ≅ G)
    [PreservesLimitsOfShape WalkingCospan F] [PreservesLimitsOfShape WalkingCospan G]
    [FunctorPreserves u F] : FunctorPreserves u G where
  functor_preserves {c} d univ := by
    have hF := FunctorPreserves.functor_preserves (u := u) (F := F) d univ
    let i : Arrow.mk (F.map u) ≅ Arrow.mk (G.map u) :=
      Arrow.isoMk (e.app Y) (e.app X) (by simp)
    have h₁ := lift_arrow_iso_univ i (functor_on F d)
    let D₁ : Data (G.map u) (G.obj c) :=
      ⟨F.obj d.P, (lift_arrow_iso i (functor_on F d)).pi, (lift_arrow_iso i (functor_on F d)).Pbk,
        (lift_arrow_iso i (functor_on F d)).epsilon ≫ (e.app c).hom⟩
    have h₂ : Universal D₁ :=
      universal_epsilon_iso (lift_arrow_iso i (functor_on F d)) (e.app c)
    refine universal_of_iso (d₁ := D₁) (d₂ := functor_on G d) (φ := (e.app d.P).symm) ?_ ?_
    · simp [D₁, functor_on, lift_arrow_iso, i]
    · change G.map d.epsilon = _ ≫ F.map d.epsilon ≫ e.hom.app c
      have hl : FBF_on_mor D₁ (f := e.inv.app d.P) (functor_on G d).Pbk
          (by simp [D₁, functor_on, lift_arrow_iso, i]) = e.inv.app d.Pbk.pullback := by
        apply ChosenPullback.hom_ext D₁.Pbk
        · simp [D₁, FBF_on_mor, pullbackMor1, lift_arrow_iso, functor_on, functPullback, i]
        · simp [D₁, FBF_on_mor, pullbackMor1, lift_arrow_iso, functor_on, functPullback, i]
      erw [hl]
      simp

end Transport

namespace ExpArrCat

/-- A morphism of `ExpArrCat` is strict when its isomorphism of arrows is an identity. -/
def Hom.IsStrict {A B : ExpArrCat.{v, u}} (F : A ⟶ B) : Prop :=
  ∃ h : Arrow.mk (F.functor.map A.arr) = Arrow.mk B.arr, F.iso = eqToIso h

section Strictify

variable {A B : ExpArrCat.{v, u}} (F : A ⟶ B)

open Classical in
/-- The new object assignment, with an isomorphism from the old one. -/
noncomputable def strictObj (X : A) : Σ Y : B, F.functor.obj X ≅ Y :=
  if hX : X = A.dom then ⟨B.dom, eqToIso (congrArg F.functor.obj hX) ≪≫ Comma.leftIso F.iso⟩
  else if hX' : X = A.cod then
    ⟨B.cod, eqToIso (congrArg F.functor.obj hX') ≪≫ Comma.rightIso F.iso⟩
  else ⟨F.functor.obj X, Iso.refl _⟩

lemma strictObj_dom : strictObj F A.dom = ⟨B.dom, Comma.leftIso F.iso⟩ := by
  simp [strictObj]

lemma strictObj_cod (h : A.dom ≠ A.cod) :
    strictObj F A.cod = ⟨B.cod, Comma.rightIso F.iso⟩ := by
  simp [strictObj, Ne.symm h]

/-- The strictified functor. -/
noncomputable def strictFunctor : A ⥤ B :=
  F.functor.copyObj (fun X => (strictObj F X).1) (fun X => (strictObj F X).2)

/-- The strictified functor is isomorphic to the original one. -/
noncomputable def strictFunctorIso : F.functor ≅ strictFunctor F :=
  F.functor.isoCopyObj _ _

private lemma arrow_eq_aux (s : Σ Y : B, F.functor.obj A.dom ≅ Y)
    (t : Σ Y : B, F.functor.obj A.cod ≅ Y) (hs : s = ⟨B.dom, Comma.leftIso F.iso⟩)
    (ht : t = ⟨B.cod, Comma.rightIso F.iso⟩) :
    Arrow.mk (s.2.inv ≫ F.functor.map A.arr ≫ t.2.hom) = Arrow.mk B.arr := by
  subst hs ht
  have := F.iso.hom.w
  congr 1
  simp only [Comma.leftIso, Comma.rightIso, Functor.mapIso_inv, Comma.fst_map,
    Functor.mapIso_hom, Comma.snd_map]
  have h2 := F.iso.inv_hom_id
  have h3 : F.iso.inv.left ≫ F.iso.hom.left = 𝟙 _ := congrArg CommaMorphism.left h2
  simp only [Functor.id_obj, Functor.id_map, Arrow.mk_left, Arrow.mk_right, Arrow.mk_hom]
    at this
  rw [← this, ← Category.assoc, h3]
  exact Category.id_comp _

lemma strictFunctor_arrow (h : A.dom ≠ A.cod) :
    Arrow.mk ((strictFunctor F).map A.arr) = Arrow.mk B.arr :=
  arrow_eq_aux F _ _ (strictObj_dom F) (strictObj_cod F h)

private lemma left_aux (s : Σ Y : B, F.functor.obj A.dom ≅ Y)
    (t : Σ Y : B, F.functor.obj A.cod ≅ Y) (hs : s = ⟨B.dom, Comma.leftIso F.iso⟩)
    (ht : t = ⟨B.cod, Comma.rightIso F.iso⟩)
    (H : Arrow.mk (s.2.inv ≫ F.functor.map A.arr ≫ t.2.hom) = Arrow.mk B.arr) :
    s.2.hom ≫ (eqToHom H).left = F.iso.hom.left := by
  subst hs ht
  have key : ∀ (X Y : Arrow B) (H : X = Y), (eqToHom H).left = eqToHom (congrArg Comma.left H) := by
    rintro _ _ rfl; rfl
  rw [key]
  simp [Comma.leftIso]

private lemma right_aux (s : Σ Y : B, F.functor.obj A.dom ≅ Y)
    (t : Σ Y : B, F.functor.obj A.cod ≅ Y) (hs : s = ⟨B.dom, Comma.leftIso F.iso⟩)
    (ht : t = ⟨B.cod, Comma.rightIso F.iso⟩)
    (H : Arrow.mk (s.2.inv ≫ F.functor.map A.arr ≫ t.2.hom) = Arrow.mk B.arr) :
    t.2.hom ≫ (eqToHom H).right = F.iso.hom.right := by
  subst hs ht
  have key : ∀ (X Y : Arrow B) (H : X = Y),
      (eqToHom H).right = eqToHom (congrArg Comma.right H) := by
    rintro _ _ rfl; rfl
  rw [key]
  simp [Comma.rightIso]

/-- The strict morphism isomorphic to `F`. -/
noncomputable def strictify (h : A.dom ≠ A.cod) : A ⟶ B :=
  letI : PreservesLimitsOfShape WalkingCospan (strictFunctor F) :=
    preservesLimitsOfShape_of_natIso (strictFunctorIso F)
  letI : PreservesLimitsOfShape (Discrete PEmpty.{1}) (strictFunctor F) :=
    preservesLimitsOfShape_of_natIso (strictFunctorIso F)
  letI : FunctorPreserves A.arr (strictFunctor F) :=
    functorPreserves_of_natIso _ _ (strictFunctorIso F)
  { functor := strictFunctor F
    iso := eqToIso (strictFunctor_arrow F h) }

lemma strictify_isStrict (h : A.dom ≠ A.cod) : (strictify F h).IsStrict :=
  ⟨strictFunctor_arrow F h, rfl⟩

/-- The invertible 2-cell between `F` and its strictification. -/
noncomputable def strictifyIso (h : A.dom ≠ A.cod) : F ≅ strictify F h :=
  Hom.isoMk (strictFunctorIso F)
    (left_aux F _ _ (strictObj_dom F) (strictObj_cod F h) (strictFunctor_arrow F h))
    (right_aux F _ _ (strictObj_dom F) (strictObj_cod F h) (strictFunctor_arrow F h))

end Strictify

/-- If the domain and codomain of the chosen arrow of `A` are distinct, every morphism
`F : A ⟶ B` of `ExpArrCat` is isomorphic, by an invertible 2-cell, to a strict morphism. -/
theorem exists_strict_iso {A B : ExpArrCat.{v, u}} (F : A ⟶ B) (h : A.dom ≠ A.cod) :
    ∃ G : A ⟶ B, G.IsStrict ∧ Nonempty (F ≅ G) :=
  ⟨strictify F h, strictify_isStrict F h, ⟨strictifyIso F h⟩⟩

end ExpArrCat
