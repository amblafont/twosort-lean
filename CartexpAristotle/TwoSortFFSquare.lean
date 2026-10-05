/-
Copyright (c) 2026 Lean Contributor. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Contributor
-/
import CartexpAristotle.TwoSortFFCollage

/-!
# Models of two-sortified theories: the square at `p` for the collage

We continue `CartexpAristotle.TwoSortFFCollage`. The collage functor `D G K` preserves pullbacks,
and we construct a pullback square from `D G K p` to the chosen arrow of `C₀`:

* at `X`, a sort `B : a ⟶ X` is sent to the family of terms `TmFam a` with the index `B`, and a
  model `e` of `X` is sent to its family with its index;
* at `Y`, a term `t : a ⟶ Y` is sent to `TmFam a` with the index `t ≫ p` and the element `t`.

## References

* [Paper, App. C.1, proof of Prop. `prop:model-faithful`]: the pullback square at `p` needed to
  apply [Paper, Thm. `thm:universal-property-natural-transformation`].
-/

open CategoryTheory Limits

universe w

namespace Lexp

namespace TwoSortFF

open SemanticTwoSortFunctor PointedForget SliceExp

noncomputable section

lemma fc_eqToHom_f {F F' : FormalCoproduct.{w} (Type w)} (h : F = F') (i : F.I) :
    (eqToHom h).f i = cast (congrArg FormalCoproduct.I h) i := by
  subst h; rfl

lemma fc_eqToHom_φ_heq {F F' : FormalCoproduct.{w} (Type w)} (h : F = F') (i : F.I)
    (x : F.obj i) : (eqToHom h).φ i x ≍ x := by
  subst h; rfl

variable {A : Lexp.{w + 1, w + 2}} [LocallySmall.{w} A.carrier] (G : A ⟶ C₀.{w})
  {a : A.carrier} (K : GL G a)

instance preservesPullbacks_D : PreservesLimitsOfShape WalkingCospan (D G K) := by
  have : PreservesLimitsOfShape WalkingCospan (D G K ⋙ Over.forget 𝔽.{w}) :=
    preservesPullbacks_of_isPullback _ fun _ _ _ _ _ _ _ _ h =>
      Collage.functor_isPullback _ h.w (homDiscFunctor_isPullback a h)
        ((h.map G.functor).map (Over.forget _))
  exact preservesLimitsOfShape_of_reflects_of_preserves (D G K) (Over.forget 𝔽.{w})

/-- A sort of `a` as a family with an index: `TmFam a` with the index `B`. -/
abbrev tmElt (B : a ⟶ A.cod) : (idx (Type w)).Elements := ⟨TmFam a, shX a B⟩

lemma psiF_eqToHom_f (B : a ⟶ A.cod) :
    (psiF G K ≫ eqToHom (ixX_eq G B K).symm).f (shX a B) = ((isoX G).obj ((Gm G B).obj K)).2 := by
  refine eq_of_heq ?_
  change (eqToHom (ixX_eq G B K).symm).f ((psiF G K).f (shX a B)) ≍ _
  rw [fc_eqToHom_f]
  refine (cast_heq _ _).trans ?_
  rw [psiF_f, show unX a (shX a B) = B from Equiv.symm_apply_apply _ _]
  exact ixX_heq G B K

/-- The interpretation in `K`, as a morphism of families with an index. -/
def thetaXApp (B : a ⟶ A.cod) : tmElt B ⟶ (isoX G).obj ((Gm G B).obj K) :=
  ⟨psiF G K ≫ eqToHom (ixX_eq G B K).symm, psiF_eqToHom_f G K B⟩

/-- The components at the sorts of the square at `X`. -/
def F₁X : Disc (a ⟶ A.cod) ⥤ (idx (Type w)).Elements := Disc.functor (fun B => tmElt B)

/-- The interpretation in `K`, as a natural transformation. -/
def thetaX : F₁X (a := a) ⟶ ((betaZ G K).app A.cod).toFunctor ⋙ isoX G where
  app B := thetaXApp G K B
  naturality B B' f := by
    have h := Disc.eq_of_hom f
    subst h
    rw [Disc.hom_ext f (𝟙 _)]
    simp

/-- The functor underlying the square at `X`. -/
def RX : Collage ((betaZ G K).app A.cod).toFunctor ⥤ (idx (Type w)).Elements :=
  Collage.lift F₁X (isoX G) (thetaX G K)

omit [LocallySmall.{w} A.carrier] in
lemma isoX_map_heq {x y : GL G A.cod} (f : x ⟶ y) :
    (CategoryOfElements.π (idx (Type w))).map ((isoX G).map f) ≍ (famF G A.cod).map f := by
  have := Functor.congr_hom (congrArg Cat.Hom.toFunctor (isoX_hom G)) f
  exact (heq_of_eq this).trans (CatPullback.conj_heq _ _ _)

lemma RX_w : (RX G K).toCatHom ≫ sW U.{w} = (ell G K A.cod).toCatHom := by
  refine Cat.Hom.ext (CategoryTheory.Functor.hext ?_ ?_)
  · rintro (σ | e)
    · rfl
    · exact isoX_fst G e
  · rintro (σ | e) (σ' | e') f
    · have h := Disc.eq_of_hom (S := a ⟶ A.cod) f
      subst h
      have : f = 𝟙 _ := Disc.hom_ext (S := a ⟶ A.cod) _ _
      subst this
      exact heq_of_eq ((CategoryTheory.Functor.map_id _ _).trans (CategoryTheory.Functor.map_id _ _).symm)
    · change (psiF G K ≫ eqToHom _) ≫
        (CategoryOfElements.π (idx (Type w))).map ((isoX G).map f) ≍
        (psiF G K ≫ eqToHom _) ≫ (famF G A.cod).map f
      rw [Category.assoc, Category.assoc]
      refine InitialModel.comp_heq_comp rfl rfl (isoX_fst G e') HEq.rfl ?_
      refine (eqToHom_comp_heq' _ _).trans ?_
      exact (isoX_map_heq G f).trans (eqToHom_comp_heq' _ _).symm
    · exact PEmpty.elim f
    · exact isoX_map_heq G f

/-- The component at `X` of the square. -/
def sqX : (D G K).obj A.cod ⟶ C₀.{w}.cod := Over.homMk (RX G K).toCatHom (RX_w G K)

omit [LocallySmall.{w} A.carrier] in
lemma eps_map_heq {x y : (idx (Type w)).Elements} (g : x ⟶ y) (z : (eps (Type w)).obj x) :
    (eps (Type w)).map g z ≍ g.1.φ x.2 z := by
  obtain ⟨X, i⟩ := x
  obtain ⟨Y, j⟩ := y
  obtain ⟨g, hg⟩ := g
  change X ⟶ Y at g
  obtain rfl : j = g.f i := hg.symm
  exact heq_of_eq (by simp [eps])

/-- The functor `D G K p` between the collages at `Y` and `X`. -/
abbrev Dp : Collage ((betaZ G K).app A.dom).toFunctor ⥤ Collage ((betaZ G K).app A.cod).toFunctor :=
  ((D G K).map A.arr).left.toFunctor

lemma tmSOf_tmS (t : a ⟶ A.dom) : (tmSOf a (tmS a t)).1 = t := by
  simp [tmSOf, tmS]

lemma thetaX_tmS (t : a ⟶ A.dom) :
    (eps (Type w)).map ((thetaX G K).app (t ≫ A.arr)) (tmS a t) =
      (gX G).map (eqToHom (Gm_comp_obj G t A.arr K).symm) (mptG G ((Gm G t).obj K)) := by
  refine eq_of_heq ?_
  refine HEq.trans ?_ (InitialModel.functor_map_eqToHom_heq _ _ _).symm
  refine (eps_map_heq _ _).trans ?_
  change (eqToHom (ixX_eq G (t ≫ A.arr) K).symm).φ _ ((psiF G K).φ (shX a (t ≫ A.arr)) (tmS a t)) ≍ _
  refine (fc_eqToHom_φ_heq _ _ _).trans ?_
  refine (psiF_φ_heq G K _).trans ?_
  rw [tmSOf_tmS]
  exact elY_heq G t K

/-- The distinguished elements over the collage at `Y`. -/
def secY : (x : Collage ((betaZ G K).app A.dom).toFunctor) →
    (RX G K ⋙ eps (Type w)).obj ((Dp G K).obj x)
  | .inl t => tmS a t
  | .inr e => mptG G e

lemma secY_map {x y : Collage ((betaZ G K).app A.dom).toFunctor} (f : x ⟶ y) :
    (RX G K ⋙ eps (Type w)).map ((Dp G K).map f) (secY G K x) = secY G K y := by
  rcases x with t | e <;> rcases y with t' | e'
  · obtain ⟨⟨rfl⟩⟩ := f
    exact congrFun ((eps (Type w)).map_id _) _
  · change (eps (Type w)).map ((thetaX G K).app (t ≫ A.arr) ≫
      (isoX G).map (eqToHom _ ≫ (Gm G A.arr).map f)) (tmS a t) = mptG G e'
    rw [Functor.map_comp, types_comp_apply, thetaX_tmS]
    change (gX G).map (eqToHom _ ≫ (Gm G A.arr).map f) ((gX G).map (eqToHom _) _) = _
    rw [← types_comp_apply ((gX G).map _) ((gX G).map _), ← Functor.map_comp, eqToHom_trans_assoc,
      eqToHom_refl, Category.id_comp]
    exact mptG_map G f
  · exact PEmpty.elim f
  · exact mptG_map G f

/-- The pointed sorts over the collage at `Y`. -/
abbrev Ptd : ((D G K).obj A.dom).left ⟶ Cat.of Pointed.{w} :=
  pointifyHom ((D G K).map A.arr).left ((RX G K).toCatHom ≫ sE U.{w}) (secY G K)
    (fun f => secY_map G K f)

/-- The functor underlying the square at `Y`. -/
def RY : ((D G K).obj A.dom).left ⟶ PB.{w} :=
  pullback.lift (Ptd G K) (((D G K).map A.arr).left ≫ (RX G K).toCatHom)
    (by rw [pointifyHom_comm, Category.assoc])

lemma RY_su' : RY G K ≫ su' U.{w} = ((D G K).map A.arr).left ≫ (RX G K).toCatHom :=
  pullback.lift_snd _ _ _

lemma RY_fst : RY G K ≫ pullback.fst U.{w} (sE U.{w}) = Ptd G K :=
  pullback.lift_fst _ _ _

lemma RY_w : RY G K ≫ (su' U.{w} ≫ sW U.{w}) = ((D G K).obj A.dom).hom := by
  rw [← Category.assoc, RY_su', Category.assoc]
  change ((D G K).map A.arr).left ≫ ((RX G K).toCatHom ≫ sW U.{w}) = _
  rw [RX_w]
  exact Over.w ((D G K).map A.arr)

/-- The component at `Y` of the square. -/
def sqY : (D G K).obj A.dom ⟶ C₀.{w}.dom := Over.homMk (RY G K) (RY_w G K)

/-- The square at `p` for the collage. -/
def sq : Arrow.mk ((D G K).map A.arr) ⟶ Arrow.mk C₀.{w}.arr :=
  Arrow.homMk (sqY G K) (sqX G K) (Over.OverMorphism.ext (RY_su' G K))

lemma crit : PointifyCrit ((D G K).map A.arr).left ((RX G K).toCatHom ≫ sE U.{w}) (secY G K) := by
  constructor
  · intro x z
    rcases x with B | e'
    · have hB : (tmSOf a z).1 ≫ A.arr = B := (tmSOf_arr a z).trans (Equiv.symm_apply_apply _ _)
      refine ⟨.inl (tmSOf a z).1, ⟨congrArg Sum.inl hB, tmS_tmSOf a z⟩, ?_⟩
      rintro (t | e) ⟨h₁, h₂⟩
      · exact congrArg Sum.inl (eq_of_tmS_heq' a z (congrArg _ (Sum.inl.inj h₁)) h₂)
      · cases h₁
    · obtain ⟨e, ⟨he₁, he₂⟩, hu⟩ := (critG G).obj e' z
      refine ⟨.inr e, ⟨congrArg Sum.inr he₁, he₂⟩, ?_⟩
      rintro (t | e'') ⟨h₁, h₂⟩
      · cases h₁
      · exact congrArg Sum.inr (hu e'' ⟨Sum.inr.inj h₁, h₂⟩)
  · intro x y h hcond
    rcases x with t | e <;> rcases y with t' | e'
    · have hB : t ≫ A.arr = t' ≫ A.arr := Disc.eq_of_hom h
      have key : (RX G K ⋙ eps (Type w)).map h (tmS a t) ≍ tmS a t :=
        InitialModel.functor_map_eqToHom_heq (eps (Type w))
          (congrArg (fun B => tmElt (a := a) B) (Disc.eq_of_hom h)) (tmS a t)
      have e : t = t' := eq_of_tmS_heq a hB (key.symm.trans (heq_of_eq hcond))
      exact ⟨Disc.homOfEq e, Disc.hom_ext _ _, fun _ _ => Disc.hom_ext _ _⟩
    · have c := Gm_comp_obj G t A.arr K
      change (eps (Type w)).map ((thetaX G K).app (t ≫ A.arr) ≫ (isoX G).map h) (tmS a t) =
        mptG G e' at hcond
      rw [Functor.map_comp, types_comp_apply, thetaX_tmS] at hcond
      have hcond' : (gX G).map (eqToHom c.symm ≫ h) (mptG G ((Gm G t).obj K)) = mptG G e' := by
        rw [Functor.map_comp, types_comp_apply]
        exact hcond
      obtain ⟨k, hk, hu⟩ := (critG G).hom _ _ _ hcond'
      refine ⟨(k : Collage.Hom ((betaZ G K).app A.dom).toFunctor (.inl t) (.inr e')), ?_,
        fun k' hk' => hu k' ?_⟩
      · change eqToHom _ ≫ (Gm G A.arr).map k = h
        rw [hk]; simp
      · change eqToHom _ ≫ (Gm G A.arr).map k' = h at hk'
        rw [← hk']; simp
    · exact PEmpty.elim h
    · exact (critG G).hom e e' h hcond

lemma isPullback_sq : IsPullback (sq G K).left ((D G K).map A.arr) C₀.{w}.arr (sq G K).right := by
  refine IsPullback.of_map (Over.forget _) (sq G K).w ?_
  change IsPullback (RY G K) ((D G K).map A.arr).left (su' U.{w}) (RX G K).toCatHom
  refine IsPullback.of_right ?_ (RY_su' G K) (shpb U.{w})
  rw [RY_fst]
  exact isPullback_pointify _ _ _ _ (crit G K)

end

end TwoSortFF

end Lexp
