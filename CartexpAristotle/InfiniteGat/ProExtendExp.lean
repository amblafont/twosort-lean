/-
Copyright (c) 2026 Lean Contributor. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Contributor
-/
import CartexpAristotle.InfiniteGat.ProExponentiable
import CartexpAristotle.Strictification

/-!
# The extension of a `Lexp`-functor preserves pushforwards

Let `C` be a small category with finite limits, `p : Y ⟶ X` an exponentiable arrow of `C`, `D` a
category with all small limits and `F : C ⥤ D` a functor preserving finite limits and
pushforwards along `p`. Then `proExtend F : Pro C ⥤ D` preserves pushforwards along
`(proYoneda C).map p` (`proExtend_functorPreserves`).

## References

* [Paper, App., Prop. `prop:lift-lexp-functor`] (preservation of pushforwards).
-/

open CategoryTheory Limits Opposite Functor SliceExp

universe w u

namespace InfiniteGat

section FunctorOnComp

variable {E₁ E₂ E₃ : Type*} [Category E₁] [Category E₂] [Category E₃]
  (F : E₁ ⥤ E₂) (G : E₂ ⥤ E₃) [PreservesLimitsOfShape WalkingCospan F]
  [PreservesLimitsOfShape WalkingCospan G]

lemma functor_on_comp {X Y : E₁} {u : Y ⟶ X} {c : E₁} (d : Data u c) :
    functor_on G (functor_on F d) = functor_on (F ⋙ G) d := by
  simp only [functor_on]
  congr 1

end FunctorOnComp

variable {C : Type w} [SmallCategory C] [HasFiniteLimits C] {X Y : C} (p : Y ⟶ X) [IsExpArr p]
  {D : Type u} [Category.{w} D] [HasLimitsOfSize.{w, w} D] (F : C ⥤ D) [PreservesFiniteLimits F]
  [FunctorPreserves p F]

instance : PreservesLimitsOfShape WalkingCospan (proExtend F) :=
  preservesLimitsOfShape_of_equiv
    (WidePullbackShape.equivalenceOfEquiv _ (Equiv.ulift.{w} : ULift.{w} WalkingPair ≃ _)) _

instance : PreservesLimitsOfShape (Discrete PEmpty.{1}) (proExtend F) :=
  preservesLimitsOfShape_of_equiv (Discrete.equivalence (Equiv.ulift.{w} : ULift.{w} PEmpty ≃ _)) _

/-- `proYoneda C ⋙ proExtend F` preserves pushforwards along `p`. -/
noncomputable instance : FunctorPreserves p (proYoneda C ⋙ proExtend F) :=
  functorPreserves_of_natIso F _ (proExtendIso F).symm

variable (A : Pro C)

/-- The image of the stage data under `proExtend F` is universal. -/
noncomputable def proExtendStageUniversal (j : StructuredArrow A (proYoneda C)) :
    Universal (functor_on (proExtend F) (proD p A j)) := by
  have h : Universal (functor_on (proYoneda C ⋙ proExtend F) (expD p j.right)) :=
    FunctorPreserves.functor_preserves _ inferInstance
  rw [← functor_on_comp] at h
  exact h

/-- **The image under `proExtend F` of the pushforward data of `A` is universal.** -/
noncomputable def proExtend_universal : Universal (functor_on (proExtend F) (proExpData p A)) := by
  haveI : Nonempty (StructuredArrow A (proYoneda C)) := IsCofiltered.nonempty
  haveI : ∀ j, Universal (functor_on (proExtend F) (proD p A j)) :=
    fun j => proExtendStageUniversal p F A j
  have hτpi : ∀ {j j' : StructuredArrow A (proYoneda C)} (t : j ⟶ j'),
      (functor_on (proExtend F) (proD p A j)).pi = (proExtend F).map (proτ p A t) ≫
        (functor_on (proExtend F) (proD p A j')).pi := fun t => by
    change (proExtend F).map _ = _ ≫ (proExtend F).map _
    rw [← Functor.map_comp, ← proτpi]
  have hhpi : ∀ j, (functor_on (proExtend F) (proExpData p A)).pi =
      (proExtend F).map (proExpH p A j) ≫ (functor_on (proExtend F) (proD p A j)).pi :=
    fun j => by
      change (proExtend F).map _ = _ ≫ (proExtend F).map _
      rw [← Functor.map_comp, ← proExpH_pi]
      rfl
  have hA := isLimitOfPreserves (proExtend F) (proYonedaCodenseAt A)
  have hP := isLimitOfPreserves (proExtend F) (limit.isLimit (proPDiagram p A))
  refine Universal.ofLimit (fun t => (proExtend F).map (proγ A t))
    (fun j => (proExtend F).map j.hom) (fun j => functor_on (proExtend F) (proD p A j))
    (fun t => (proExtend F).map (proτ p A t)) hτpi (fun t => ?_)
    (functor_on (proExtend F) (proExpData p A)) (fun j => (proExtend F).map (proExpH p A j))
    hhpi (fun t => ?_) (fun f f' h => ?_) (fun j => ?_) (fun m hm => ?_) (fun m m' h => ?_)
  · dsimp only
    erw [functor_on_FBF' (proExtend F) (proD p A _) (proD p A _).Pbk (proτpi p A t)]
    change (proExtend F).map _ ≫ (proExtend F).map _ = (proExtend F).map _ ≫ (proExtend F).map _
    rw [← Functor.map_comp, ← Functor.map_comp, proτε]
  · rw [← Functor.map_comp, StructuredArrow.w t]
  · exact hA.hom_ext (fun j => by simpa using h j)
  · dsimp only
    erw [functor_on_FBF' (proExtend F) (proD p A j) (proExpData p A).Pbk (proExpH_pi p A j)]
    change (proExtend F).map _ ≫ (proExtend F).map _ = (proExtend F).map _ ≫ (proExtend F).map _
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg _ (proExpEps_fac p A j)
  · refine ⟨hP.lift ⟨_,
      { app := m
        naturality := fun _ _ t => by
          dsimp
          rw [Category.id_comp]
          exact (hm t).symm }⟩, fun j => hP.fac _ j⟩
  · exact hP.hom_ext h

/-- **`proExtend F` preserves pushforwards along `(proYoneda C).map p`.**

[Paper, App., Prop. `prop:lift-lexp-functor`]. -/
noncomputable instance proExtend_functorPreserves :
    FunctorPreserves ((proYoneda C).map p) (proExtend F) :=
  functor_preserves_1_is_enough _ _ (proExpData p) (proExpUniversal p) (proExtend_universal p F)

end InfiniteGat
