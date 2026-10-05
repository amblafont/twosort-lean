/-
Copyright (c) 2026 Lean Contributor. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Contributor
-/
import Mathlib

/-!
# Functors preserving the terminal object and wide pullbacks preserve all limits

A functor out of a category with a terminal object and all `w`-small wide pullbacks which preserves
the terminal object and the `w`-small wide pullbacks preserves all `w`-small limits
(`preservesLimitsOfSize_of_preservesWidePullbacks`). Hence the morphisms of `CompExp` are exactly
the limit-preserving functors (preserving the exponentiable arrow).
-/

open CategoryTheory Limits

universe w v₁ v₂ u₁ u₂

namespace InfiniteGat

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  [HasTerminal C] [HasWidePullbacks.{w} C] (G : C ⥤ D)
  [PreservesLimitsOfShape (Discrete PEmpty.{1}) G]
  [∀ J : Type w, PreservesLimitsOfShape (WidePullbackShape J) G]

/-- A functor preserving the terminal object and `w`-small wide pullbacks preserves `w`-small
products. -/
lemma preservesProducts_of_preservesWidePullbacks (J : Type w) :
    PreservesLimitsOfShape (Discrete J) G := by
  constructor
  intro K
  let objs : J → C := fun j => K.obj ⟨j⟩
  let arrows : ∀ j, objs j ⟶ ⊤_ C := fun _ => terminal.from _
  let c : Fan objs := Fan.mk (widePullback (⊤_ C) objs arrows) (WidePullback.π arrows)
  have hc : IsLimit c := mkFanLimit c
    (fun s => WidePullback.lift (terminal.from _) s.proj (fun _ => terminal.hom_ext _ _))
    (fun s j => by simp [c])
    (fun s m hm => WidePullback.hom_ext _ _ _ (fun j => by simpa [c] using hm j)
      (terminal.hom_ext _ _))
  have hT : IsTerminal (G.obj (⊤_ C)) := terminalIsTerminal.isTerminalObj G
  have hL := isLimitOfPreserves G (limit.isLimit (WidePullbackShape.wideCospan (⊤_ C) objs arrows))
  let lift : ∀ s : Cone (Discrete.functor objs ⋙ G),
      Cone (WidePullbackShape.wideCospan (⊤_ C) objs arrows ⋙ G) := fun s =>
    WidePullbackShape.mkCone (hT.from s.pt) (fun j => s.π.app ⟨j⟩) (fun _ => hT.hom_ext _ _)
  have hGc : IsLimit (G.mapCone c) :=
    { lift := fun s => hL.lift (lift s)
      fac := fun s ⟨j⟩ => hL.fac (lift s) (some j)
      uniq := fun s m hm => hL.hom_ext (fun j => by
        rw [hL.fac]
        cases j with
        | none => exact hT.hom_ext _ _
        | some j => exact hm ⟨j⟩) }
  haveI : PreservesLimit (Discrete.functor objs) G := preservesLimit_of_preserves_limit_cone hc hGc
  haveI : PreservesLimit (Discrete.functor (K.obj ∘ Discrete.mk)) G := this
  exact preservesLimit_of_iso_diagram G (Discrete.natIsoFunctor (F := K)).symm

/-- **A functor preserving the terminal object and `w`-small wide pullbacks preserves all
`w`-small limits.** -/
lemma preservesLimitsOfSize_of_preservesWidePullbacks : PreservesLimitsOfSize.{w, w} G := by
  haveI : HasLimitsOfSize.{w, w} C :=
    Adjunction.has_limits_of_equivalence (Over.equivalenceOfIsTerminal terminalIsTerminal).inverse
  haveI := preservesProducts_of_preservesWidePullbacks G
  haveI : PreservesLimitsOfShape WalkingCospan G :=
    preservesLimitsOfShape_of_equiv
      (WidePullbackShape.equivalenceOfEquiv _ (Equiv.ulift.{w} : ULift.{w} WalkingPair ≃ _)) G
  haveI : PreservesLimitsOfShape (Discrete WalkingPair) G :=
    preservesLimitsOfShape_of_equiv
      (Discrete.equivalence (Equiv.ulift.{w} : ULift.{w} WalkingPair ≃ _)) G
  haveI := preservesEqualizers_of_preservesPullbacks_and_binaryProducts G
  exact preservesLimits_of_preservesEqualizers_and_products G

end InfiniteGat
