/-
Copyright (c) 2026 Lean Contributor. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Contributor
-/
import CartexpAristotle.CompExp.CatWidePullbacks
import CartexpAristotle.ColaxSliceCartForget

/-!
# Wide pullbacks in `ColaxSliceCart`

This generalises the pullbacks of `CartexpAristotle.ColaxSliceCartLimits` to wide pullbacks
indexed by a type `J : Type w`.

Let `K` be a wide cospan in `ColaxSliceCart` with base `(Z, E)` and legs
`(H j, n j) : (X j, F j) ⟶ (Z, E)`. Its wide pullback has as underlying category the strict wide
pullback of the underlying categories in `Cat` (`CatWidePullback.Obj`), and the functor to `Fam`
sends `(b, (a j)ⱼ)` to the wide pushout of the cartesian maps `n j : E (H j (a j)) = E b ⟶ F j (a j)`:
its base is the quotient of `E b ⊕ Σ j, F j (a j)` gluing each index of `E b` to its images, and
its fibres are those of `E b` and of the `F j (a j)` (which agree on glued indices because the
`n j` are cartesian).

Since the underlying category is the wide pullback of `Cat`, the projection
`ColaxSliceCart.forget` preserves these wide pullbacks.

## References

* [Paper, App. A.4, Prop. `prop:colax-slice-limits`]: `CAT //_c Fam` has (small) limits, computed
  with the limit of the underlying categories and the colimit of the families.
-/

universe w

open CategoryTheory Limits

namespace ColaxSliceCart

namespace Wide

variable {J : Type w} (K : WidePullbackShape J ⥤ ColaxSliceCart.{w, w, w + 1})

/-- The base of the wide cospan. -/
abbrev Z : ColaxSliceCart.{w, w, w + 1} := K.obj none

/-- The components of the wide cospan. -/
abbrev X (j : J) : ColaxSliceCart.{w, w, w + 1} := K.obj (some j)

/-- The legs of the wide cospan. -/
abbrev f (j : J) : Hom (X K j) (Z K) := K.map (WidePullbackShape.Hom.term j)

/-- The objects of the wide pullback: those of the strict wide pullback of the underlying
categories. -/
abbrev WObj : Type (w + 1) := CatWidePullback.Obj.{w, w, w + 1} (K ⋙ forget)

variable {K}

lemma WObj.h' (p : WObj K) (j : J) : (f K j).functor.obj (p.a j) = p.b := p.h j

/-- The base types to glue. -/
abbrev S (p : WObj K) : Type w :=
  ((Z K).F.obj p.b).base ⊕ Σ j, ((X K j).F.obj (p.a j)).base

/-- The gluing relation: an index `i` of `E (H j (a j)) = E b` is glued to its image under
`n j`. -/
def wRel (p : WObj K) (s t : S p) : Prop :=
  ∃ (j : J) (i : ((Z K).F.obj ((f K j).functor.obj (p.a j))).base) (i' : ((Z K).F.obj p.b).base),
    HEq i i' ∧ s = Sum.inl i' ∧ t = Sum.inr ⟨j, ((f K j).nat.app (p.a j) : Fam.Hom _ _).base i⟩

lemma fiber_eq (p : WObj K) (j : J) (i : ((Z K).F.obj ((f K j).functor.obj (p.a j))).base)
    (i' : ((Z K).F.obj p.b).base) (hii' : HEq i i') :
    ((Z K).F.obj p.b).fiber i' =
      ((X K j).F.obj (p.a j)).fiber (((f K j).nat.app (p.a j) : Fam.Hom _ _).base i) :=
  (Fam.obj_fiber_congr (Z K).F (p.h' j) hii').symm.trans
    (((f K j).isPointwiseCartesian (p.a j)).fiber_eq i)

/-- The fibres over the base types to glue. -/
def sFiber (p : WObj K) : S p → Type w :=
  Sum.elim ((Z K).F.obj p.b).fiber (fun x => ((X K x.1).F.obj (p.a x.1)).fiber x.2)

/-- The fibres of the glued family. -/
def wFiber (p : WObj K) : Quot (wRel p) → Type w :=
  Quot.lift (sFiber p) (by
    rintro _ _ ⟨j, i, i', hii', rfl, rfl⟩
    exact fiber_eq p j i i' hii')

/-- The glued family over an object of the wide pullback. -/
def wFamObj (p : WObj K) : Fam.{w} := ⟨Quot (wRel p), wFiber p⟩

/-- The map between the base types to glue along a morphism. -/
def sMap {p q : WObj K} (φ : p ⟶ q) : S p → S q :=
  Sum.map ((Z K).F.map φ.base : Fam.Hom _ _).base
    (fun x => ⟨x.1, ((X K x.1).F.map (φ.comp x.1) : Fam.Hom _ _).base x.2⟩)

lemma wRel_map {p q : WObj K} (φ : p ⟶ q) (s t : S p) (hst : wRel p s t) :
    wRel q (sMap φ s) (sMap φ t) := by
  obtain ⟨j, i, i', hii', rfl, rfl⟩ := hst
  refine ⟨j, ((Z K).F.map ((f K j).functor.map (φ.comp j)) : Fam.Hom _ _).base i,
    ((Z K).F.map φ.base : Fam.Hom _ _).base i',
    Fam.map_base_heq (Z K).F (p.h' j) (q.h' j) (φ.w j) hii', rfl, ?_⟩
  exact congrArg (fun x => (Sum.inr ⟨j, x⟩ : S q)) (Fam.nat_base (f K j).nat (φ.comp j) i)

/-- The base map of the glued family along a morphism. -/
def wFamMapBase {p q : WObj K} (φ : p ⟶ q) : Quot (wRel p) → Quot (wRel q) :=
  Quot.lift (fun s => Quot.mk _ (sMap φ s)) (fun s t h => Quot.sound (wRel_map φ s t h))

lemma wFamMap_compat {p q : WObj K} (φ : p ⟶ q) (j : J)
    (i : ((Z K).F.obj ((f K j).functor.obj (p.a j))).base) (i' : ((Z K).F.obj p.b).base)
    (hii' : HEq i i') :
    HEq (((Z K).F.map φ.base : Fam.Hom _ _).fiber i')
      (((X K j).F.map (φ.comp j) : Fam.Hom _ _).fiber
        (((f K j).nat.app (p.a j) : Fam.Hom _ _).base i)) := by
  apply Function.hfunext (fiber_eq p j i i' hii')
  intro x y hxy
  obtain ⟨z, rfl⟩ : ∃ z, ((f K j).nat.app (p.a j) : Fam.Hom _ _).fiber i z = y :=
    ⟨cast (((f K j).isPointwiseCartesian (p.a j)).fiber_eq i).symm y, eq_of_heq
      ((((f K j).isPointwiseCartesian (p.a j)).fiber_heq i _).trans (cast_heq _ _))⟩
  have hxz : HEq x z :=
    hxy.trans (((f K j).isPointwiseCartesian (p.a j)).fiber_heq i z)
  refine HEq.trans ?_ (Fam.nat_fiber (f K j).nat (φ.comp j) i z).symm
  refine HEq.trans ?_ (((f K j).isPointwiseCartesian (q.a j)).fiber_heq _ _).symm
  exact Fam.map_fiber_heq (Z K).F (p.h' j).symm (q.h' j).symm (φ.w j).symm hii'.symm hxz

/-- The fibre maps of the glued family along a morphism. -/
def wFamMapFiber {p q : WObj K} (φ : p ⟶ q) :
    ∀ x, wFiber p x → wFiber q (wFamMapBase φ x) := fun x =>
  Quot.hrecOn (motive := fun x => wFiber p x → wFiber q (wFamMapBase φ x)) x
    (fun s => Sum.rec
      (motive := fun s => wFiber p (Quot.mk _ s) → wFiber q (wFamMapBase φ (Quot.mk _ s)))
      (fun a => ((Z K).F.map φ.base : Fam.Hom _ _).fiber a)
      (fun x => ((X K x.1).F.map (φ.comp x.1) : Fam.Hom _ _).fiber x.2) s)
    (by
      rintro _ _ ⟨j, i, i', hii', rfl, rfl⟩
      exact wFamMap_compat φ j i i' hii')

/-- The glued family along a morphism. -/
def wFamMap {p q : WObj K} (φ : p ⟶ q) : Fam.Hom (wFamObj p) (wFamObj q) :=
  ⟨wFamMapBase φ, wFamMapFiber φ⟩

variable (K) in
/-- The functor from the strict wide pullback to `Fam` sending `(b, (a j)ⱼ)` to the glued
family. -/
def wFam : WObj K ⥤ Fam.{w} where
  obj := wFamObj
  map φ := wFamMap φ
  map_id p := by
    refine Fam.Hom.ext' (funext fun x => ?_) (fun x => ?_)
    · induction x using Quot.ind with
      | mk s =>
        rcases s with a | ⟨j, b⟩
        · exact congrArg (fun t => Quot.mk _ (Sum.inl t))
            (Fam.Hom.congr_base ((Z K).F.map_id p.b) a)
        · exact congrArg (fun t => (Quot.mk (wRel p) (Sum.inr ⟨j, t⟩) : Quot (wRel p)))
            (Fam.Hom.congr_base ((X K j).F.map_id (p.a j)) b)
    · induction x using Quot.ind with
      | mk s =>
        rcases s with a | ⟨j, b⟩
        · exact fun y => Fam.Hom.congr_fiber ((Z K).F.map_id p.b) a y
        · exact fun y => Fam.Hom.congr_fiber ((X K j).F.map_id (p.a j)) b y
  map_comp {p q r} φ ψ := by
    refine Fam.Hom.ext' (funext fun x => ?_) (fun x => ?_)
    · induction x using Quot.ind with
      | mk s =>
        rcases s with a | ⟨j, b⟩
        · exact congrArg (fun t => Quot.mk _ (Sum.inl t))
            (Fam.Hom.congr_base ((Z K).F.map_comp φ.base ψ.base) a)
        · exact congrArg (fun t => (Quot.mk (wRel r) (Sum.inr ⟨j, t⟩) : Quot (wRel r)))
            (Fam.Hom.congr_base ((X K j).F.map_comp (φ.comp j) (ψ.comp j)) b)
    · induction x using Quot.ind with
      | mk s =>
        rcases s with a | ⟨j, b⟩
        · exact fun y => Fam.Hom.congr_fiber ((Z K).F.map_comp φ.base ψ.base) a y
        · exact fun y => Fam.Hom.congr_fiber ((X K j).F.map_comp (φ.comp j) (ψ.comp j)) b y

variable (K)

/-- The wide pullback object in `ColaxSliceCart`. -/
def wObj : ColaxSliceCart.{w, w, w + 1} := ⟨Cat.of (WObj K), wFam K⟩

/-- The projection to the base. -/
def wBase : Hom (wObj K) (Z K) where
  functor := (CatWidePullback.base (K ⋙ forget)).toFunctor
  nat :=
    { app := fun p =>
        (⟨fun a => Quot.mk _ (Sum.inl a), fun _ x => x⟩ :
          Fam.Hom ((Z K).F.obj p.b) (wFamObj p))
      naturality := fun _ _ _ => rfl }
  isPointwiseCartesian := fun _ _ => ⟨rfl, fun _ => rfl⟩

/-- The projection to a component. -/
def wProj (j : J) : Hom (wObj K) (X K j) where
  functor := (CatWidePullback.proj (K ⋙ forget) j).toFunctor
  nat :=
    { app := fun p =>
        (⟨fun a => Quot.mk _ (Sum.inr ⟨j, a⟩), fun _ x => x⟩ :
          Fam.Hom ((X K j).F.obj (p.a j)) (wFamObj p))
      naturality := fun _ _ _ => rfl }
  isPointwiseCartesian := fun _ _ => ⟨rfl, fun _ => rfl⟩

lemma wProj_comp (j : J) : Hom.comp (wProj K j) (f K j) = wBase K := by
  refine Hom.ext_of_functor_eq (Functor.hext (fun p => p.h' j) (fun _ _ φ => φ.w j))
    (fun p => ?_)
  apply Function.hfunext (Fam.obj_base_congr (Z K).F (p.h' j))
  intro i i' hii'
  exact heq_of_eq (Quot.sound ⟨j, i, i', hii', rfl, rfl⟩).symm

/-- The wide pullback cone in `ColaxSliceCart`. -/
def cone : Cone K := WidePullbackShape.mkCone (wBase K) (wProj K) (wProj_comp K)

variable {K}

section Lift

variable (s : Cone K)

/-- The functor part of the induced map into the wide pullback. -/
def liftFunctor : s.pt.cat ⥤ WObj K := (CatWidePullback.lift (forget.mapCone s)).toFunctor

lemma lift_functor_eq (j : J) :
    (s.π.app (some j) : Hom _ _).functor ⋙ (f K j).functor = (s.π.app none : Hom _ _).functor :=
  Hom.functor_eq_of_eq (s.w (WidePullbackShape.Hom.term j))

/-- The base map of the induced natural transformation. -/
def liftBase (q : s.pt.cat) : Quot (wRel ((liftFunctor s).obj q)) → (s.pt.F.obj q).base :=
  Quot.lift (Sum.elim ((s.π.app none : Hom _ _).nat.app q : Fam.Hom _ _).base
      (fun x => ((s.π.app (some x.1) : Hom _ _).nat.app q : Fam.Hom _ _).base x.2)) (by
    rintro _ _ ⟨j, i, i', hii', rfl, rfl⟩
    exact (heq_apply_of_heq
      (Fam.obj_base_congr (Z K).F (Functor.congr_obj (lift_functor_eq s j) q))
      (Hom.base_heq_of_eq (s.w (WidePullbackShape.Hom.term j)) q) hii').symm)

lemma lift_fiber_eq (q : s.pt.cat) (x : Quot (wRel ((liftFunctor s).obj q))) :
    wFiber ((liftFunctor s).obj q) x = (s.pt.F.obj q).fiber (liftBase s q x) := by
  induction x using Quot.ind with
  | mk t =>
    rcases t with a | ⟨j, b⟩
    · exact ((s.π.app none : Hom _ _).isPointwiseCartesian q).fiber_eq a
    · exact ((s.π.app (some j) : Hom _ _).isPointwiseCartesian q).fiber_eq b

/-- The components of the induced natural transformation. -/
def liftApp (q : s.pt.cat) : Fam.Hom (wFamObj ((liftFunctor s).obj q)) (s.pt.F.obj q) :=
  ⟨liftBase s q, fun x y => cast (lift_fiber_eq s q x) y⟩

lemma liftApp_isCartesian (q : s.pt.cat) :
    Fam.Hom.IsCartesian (X := wFamObj ((liftFunctor s).obj q)) (liftApp s q) :=
  fun x => ⟨lift_fiber_eq s q x, fun _ => rfl⟩

/-- The induced map into the wide pullback. -/
def lift : Hom s.pt (wObj K) where
  functor := liftFunctor s
  nat :=
    { app := liftApp s
      naturality := fun q q' φ => by
        refine Fam.Hom.ext' (funext fun x => ?_) (fun x => ?_)
        · induction x using Quot.ind with
          | mk t =>
            rcases t with a | ⟨j, b⟩
            · exact Fam.Hom.congr_base ((s.π.app none : Hom _ _).nat.naturality φ) a
            · exact Fam.Hom.congr_base ((s.π.app (some j) : Hom _ _).nat.naturality φ) b
        · induction x using Quot.ind with
          | mk t =>
            rcases t with a | ⟨j, b⟩
            · intro y
              let L := (s.π.app none : Hom _ _)
              refine (cast_heq _ _).trans ?_
              have hy : cast (lift_fiber_eq s q (Quot.mk _ (Sum.inl a))) y =
                  (L.nat.app q : Fam.Hom _ _).fiber a y :=
                eq_of_heq ((cast_heq _ _).trans ((L.isPointwiseCartesian q).fiber_heq a y).symm)
              refine HEq.trans ?_ (heq_of_eq (congrArg _ hy)).symm
              refine HEq.trans ?_ (Fam.nat_fiber L.nat φ a y).symm
              exact ((L.isPointwiseCartesian q').fiber_heq _ _).symm
            · intro y
              let L := (s.π.app (some j) : Hom _ _)
              refine (cast_heq _ _).trans ?_
              have hy : cast (lift_fiber_eq s q (Quot.mk _ (Sum.inr ⟨j, b⟩))) y =
                  (L.nat.app q : Fam.Hom _ _).fiber b y :=
                eq_of_heq ((cast_heq _ _).trans ((L.isPointwiseCartesian q).fiber_heq b y).symm)
              refine HEq.trans ?_ (heq_of_eq (congrArg _ hy)).symm
              refine HEq.trans ?_ (Fam.nat_fiber L.nat φ b y).symm
              exact ((L.isPointwiseCartesian q').fiber_heq _ _).symm }
  isPointwiseCartesian := liftApp_isCartesian s

lemma lift_base : Hom.comp (lift s) (wBase K) = s.π.app none :=
  Hom.ext_of_functor_eq rfl (fun _ => HEq.rfl)

lemma lift_proj (j : J) : Hom.comp (lift s) (wProj K j) = s.π.app (some j) :=
  Hom.ext_of_functor_eq rfl (fun _ => HEq.rfl)

lemma lift_uniq (m : Hom s.pt (wObj K)) (h : ∀ j, Hom.comp m ((cone K).π.app j) = s.π.app j) :
    m = lift s := by
  have hF : m.functor = liftFunctor s := by
    have := CatWidePullback.lift_uniq (forget.mapCone s) (forget.map m)
      (congrArg forget.map (h none)) (fun j => congrArg forget.map (h (some j)))
    exact congrArg Cat.Hom.toFunctor this
  rcases m with ⟨G, ν, hν⟩
  dsimp only at hF
  subst hF
  refine Hom.ext_of_functor_eq rfl (fun q => heq_of_eq (funext fun x => ?_))
  induction x using Quot.ind with
  | mk t =>
    rcases t with a | ⟨j, b⟩
    · exact congrFun (eq_of_heq (Hom.base_heq_of_eq (h none) q)) a
    · exact congrFun (eq_of_heq (Hom.base_heq_of_eq (h (some j)) q)) b

end Lift

variable (K)

/-- The wide pullback cone in `ColaxSliceCart` is a limit cone.

[Paper, App. A.4, Prop. `prop:colax-slice-limits`]: wide pullbacks. -/
def isLimit : IsLimit (cone K) where
  lift := lift
  fac s j := by
    cases j
    · exact lift_base s
    · exact lift_proj s _
  uniq s m h := lift_uniq s m h

/-- The image of the wide pullback cone under the projection to `Cat` is a limit cone. -/
def forgetIsLimit : IsLimit (forget.mapCone (cone K)) :=
  (CatWidePullback.isLimit.{w, w, w + 1} (K ⋙ forget)).ofIsoLimit
    (Cones.ext (Iso.refl _) (fun j => by cases j <;> exact (Category.id_comp _).symm))

end Wide

/-- `ColaxSliceCart.{w, w, w + 1}` has all `w`-small wide pullbacks. -/
instance hasWidePullbacks : HasWidePullbacks.{w} ColaxSliceCart.{w, w, w + 1} := fun _ =>
  ⟨fun K => HasLimit.mk ⟨Wide.cone K, Wide.isLimit K⟩⟩

/-- The projection `ColaxSliceCart ⥤ Cat` preserves `w`-small wide pullbacks. -/
instance forget_preservesWidePullbacks (J : Type w) :
    PreservesLimitsOfShape (WidePullbackShape J) forget.{w} where
  preservesLimit {K} := preservesLimit_of_preserves_limit_cone (Wide.isLimit K)
    (Wide.forgetIsLimit K)

end ColaxSliceCart
