/-
Copyright (c) 2026 Lean Contributor. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Contributor
-/
import CartexpAristotle.TwoSortFFReadout

/-!
# Two-sortification is fully faithful

We follow the appendix section "Two-sortification is fully faithful". Let `FinGat` be a
bi-initial object of `Lexp` whose hom-types are `w`-small, `T` the two-sortification
functor, and `p : Y ⟶ X` the chosen arrow.

* **Faithfulness at `X` and `Y`** (Corollary "two-sortification-faithful"): the model `M_Ω`
  (`MOmega`) of `T a` is sent by `T B` (resp. `T t`) to the family of terms of `a` with the index `B`
  (resp. the element `t`), so `B` (resp. `t`) can be read off from `T B` (resp. `T t`).
* **Fullness at `X` and `Y`** (Proposition "section-terms-two-sortification"): let `Z` be the
  initial model of `T a`, `i : Z ⟶ M_Ω` the initial morphism and `j : M_Ω ⟶ Z` the morphism
  whose family part is the interpretation of the sorts and terms of `a` in `Z`. Then `i ≫ j = 𝟙`,
  and reading off a morphism `h : T a ⟶ T X` (resp. `T a ⟶ T Y`) in `Z`, transporting it along `i`
  and back along `j`, shows that `h = T B` where `B` is read off from `h` in `M_Ω`.
* Faithfulness and fullness at `X` and `Y` extend to all objects
  (Proposition "faithful-at-XGAT-YGAT", `TwoSortificationFullyFaithful`).

## References

* [Paper, App. C.1, Cor. `cor:two-sortification-faithful`]: `twoSort_faithful_cod`,
  `twoSort_faithful_dom`, and `Lexp.twoSortification_faithful`.
* [Paper, App. C.2, Prop. `prop:section-terms-two-sortification`]: `twoSort_full_cod`,
  `twoSort_full_dom`.
* [Paper, App. C.2, final Corollary] (`T` is fully faithful): `Lexp.twoSortification_full`,
  `Lexp.twoSortificationFullyFaithful`.
* [Paper, App. C, Prop. `prop:faithful-at-XGAT-YGAT`]: `twoSortBij_all`.
-/

open CategoryTheory Limits

universe w

namespace Lexp

namespace TwoSortFF

open SemanticTwoSortFunctor PointedForget SliceExp InitialModel

noncomputable section

lemma fc_f_heq {X X' Y Y' : FormalCoproduct.{w} (Type w)} (hX : X = X') (hY : Y = Y')
    {g : X ⟶ Y} {g' : X' ⟶ Y'} (hg : g ≍ g') {x : X.I} {x' : X'.I} (hx : x ≍ x') :
    g.f x ≍ g'.f x' := by
  subst hX hY; cases hg; cases hx; rfl

lemma fc_φ_heq {X X' Y Y' : FormalCoproduct.{w} (Type w)} (hX : X = X') (hY : Y = Y')
    {g : X ⟶ Y} {g' : X' ⟶ Y'} (hg : g ≍ g') {x : X.I} {x' : X'.I} (hx : x ≍ x')
    {y : X.obj x} {y' : X'.obj x'} (hy : y ≍ y') : g.φ x y ≍ g'.φ x' y' := by
  subst hX hY; cases hg; cases hx; cases hy; rfl

lemma fc_obj_heq {F F' : FormalCoproduct.{w} (Type w)} (hF : F = F') {i : F.I} {i' : F'.I}
    (hi : i ≍ i') : F.obj i = F'.obj i' := by
  subst hF; cases hi; rfl

lemma heq_app {α α' β β' : Type w} (hα : α = α') (hβ : β = β') {f : α → β} {f' : α' → β'}
    (hf : f ≍ f') {x : α} {x' : α'} (hx : x ≍ x') : f x ≍ f' x' := by
  subst hα hβ; cases hf; cases hx; rfl

lemma functor_map_heq' {C D : Type*} [Category C] [Category D] (F : C ⥤ D) {x x' y y' : C}
    (hx : x = x') (hy : y = y') {f : x ⟶ y} {f' : x' ⟶ y'} (hf : f ≍ f') :
    F.map f ≍ F.map f' := by
  subst hx hy; cases hf; rfl

lemma elements_ext {F : FormalCoproduct.{w} (Type w) ⥤ Type w} {x y : F.Elements}
    (h₁ : x.1 = y.1) (h₂ : x.2 ≍ y.2) : x = y :=
  Sigma.ext h₁ h₂

variable {FinGat : Lexp.{w + 1, w + 2}} {hFinGat : TwoSortData FinGat} {a : FinGat.carrier}

lemma Rd_fst (K : GL (GT hFinGat) a)
    (h : (Tw hFinGat).functor.obj a ⟶ (Tw hFinGat).functor.obj FinGat.cod) :
    (Rd K h).1 = (famF (GT hFinGat) a).obj K :=
  (isoX_fst _ _).trans (famF_mapH_obj h K)

/-- Reading off `h : T a ⟶ T X` is natural in the model. -/
lemma Rd_map (h : (Tw hFinGat).functor.obj a ⟶ (Tw hFinGat).functor.obj FinGat.cod)
    {K K' : GL (GT hFinGat) a} (m : K ⟶ K') {x : ((famF (GT hFinGat) a).obj K).I}
    (hx : x ≍ (Rd K h).2) : ((famF (GT hFinGat) a).map m).f x ≍ (Rd K' h).2 := by
  let e := (isoX (GT hFinGat)).map ((GmH hFinGat h).map m)
  have h1 : e.1.f (Rd K h).2 = (Rd K' h).2 := e.2
  have hg : e.1 ≍ (famF (GT hFinGat) a).map m :=
    (isoX_map_heq _ _).trans (famF_mapH_heq h m)
  rw [← h1]
  exact fc_f_heq (Rd_fst K h).symm (Rd_fst K' h).symm hg.symm (hx.trans HEq.rfl)

lemma Gm_arr_GmH_obj (h : (Tw hFinGat).functor.obj a ⟶ (Tw hFinGat).functor.obj FinGat.dom)
    (K : GL (GT hFinGat) a) : (Gm (GT hFinGat) FinGat.arr).obj ((GmH hFinGat h).obj K) =
      (GmH hFinGat (h ≫ (Tw hFinGat).functor.map FinGat.arr)).obj K :=
  (Functor.congr_obj (congrArg (fun F => F.left.toFunctor)
    ((Φfun.{w + 1, w + 2} (Mf hFinGat)).map_comp h ((Tw hFinGat).functor.map FinGat.arr))) K).symm

lemma Gm_arr_GmH_map (h : (Tw hFinGat).functor.obj a ⟶ (Tw hFinGat).functor.obj FinGat.dom)
    {K K' : GL (GT hFinGat) a} (m : K ⟶ K') :
    (Gm (GT hFinGat) FinGat.arr).map ((GmH hFinGat h).map m) ≍
      (GmH hFinGat (h ≫ (Tw hFinGat).functor.map FinGat.arr)).map m := by
  have := Functor.congr_hom (congrArg (fun F => F.left.toFunctor)
    ((Φfun.{w + 1, w + 2} (Mf hFinGat)).map_comp h ((Tw hFinGat).functor.map FinGat.arr))) m
  exact ((heq_of_eq this).trans (CatPullback.conj_heq _ _ _)).symm

lemma Qd_X_eq (h : (Tw hFinGat).functor.obj a ⟶ (Tw hFinGat).functor.obj FinGat.dom)
    (K : GL (GT hFinGat) a) {F : FormalCoproduct.{w} (Type w)}
    (hF : (Rd K (h ≫ (Tw hFinGat).functor.map FinGat.arr)).1 = F) {i : F.I}
    (hi : (Rd K (h ≫ (Tw hFinGat).functor.map FinGat.arr)).2 ≍ i) : (Qd K h).X = F.obj i := by
  have e₁ : (Qd K h).X = (gX (GT hFinGat)).obj ((Gm (GT hFinGat) FinGat.arr).obj
      ((GmH hFinGat h).obj K)) := Functor.congr_obj (gw (GT hFinGat)) _
  rw [e₁, Gm_arr_GmH_obj]
  exact fc_obj_heq hF hi

/-- Reading off `h : T a ⟶ T Y` is natural in the model. -/
lemma Qd_map (h : (Tw hFinGat).functor.obj a ⟶ (Tw hFinGat).functor.obj FinGat.dom)
    {K K' : GL (GT hFinGat) a} (m : K ⟶ K') {x : ((famF (GT hFinGat) a).obj K).I}
    (hx : x ≍ (Rd K (h ≫ (Tw hFinGat).functor.map FinGat.arr)).2)
    {y : ((famF (GT hFinGat) a).obj K).obj x} (hy : y ≍ (Qd K h).point) :
    ((famF (GT hFinGat) a).map m).φ x y ≍ (Qd K' h).point := by
  set hp := h ≫ (Tw hFinGat).functor.map FinGat.arr
  let g := (gY (GT hFinGat)).map ((GmH hFinGat h).map m)
  rw [← g.map_point]
  let e' := (isoX (GT hFinGat)).map ((GmH hFinGat hp).map m)
  have hg : e'.1 ≍ (famF (GT hFinGat) a).map m :=
    (isoX_map_heq _ _).trans (famF_mapH_heq hp m)
  have hX : (Qd K h).X = (Rd K hp).1.obj (Rd K hp).2 := Qd_X_eq h K rfl HEq.rfl
  have hX' : (Qd K' h).X = (Rd K' hp).1.obj (Rd K' hp).2 := Qd_X_eq h K' rfl HEq.rfl
  -- the underlying function of `g`
  have G1 : g.toFun ≍ (gX (GT hFinGat)).map ((Gm (GT hFinGat) FinGat.arr).map
      ((GmH hFinGat h).map m)) := by
    have := Functor.congr_hom (gw (GT hFinGat)) ((GmH hFinGat h).map m)
    exact (heq_of_eq this).trans (CatPullback.conj_heq _ _ _)
  have G2 : (gX (GT hFinGat)).map ((Gm (GT hFinGat) FinGat.arr).map ((GmH hFinGat h).map m)) ≍
      (gX (GT hFinGat)).map ((GmH hFinGat hp).map m) :=
    functor_map_heq' _ (Gm_arr_GmH_obj h K) (Gm_arr_GmH_obj h K') (Gm_arr_GmH_map h m)
  have hz : (Qd K h).point ≍ (cast hX (Qd K h).point) := (cast_heq _ _).symm
  refine HEq.symm ((heq_app hX hX' (G1.trans G2) hz).trans ?_)
  refine (eps_map_heq e' _).trans ?_
  exact (fc_φ_heq (Rd_fst K hp) (Rd_fst K' hp) hg hx.symm
    ((cast_heq _ _).trans hy.symm))

variable [LocallySmall.{w} FinGat.carrier]

/-- **Faithfulness at `X`**: `B` is read off from `T B` in the model `M_Ω`.

[Paper, App. C.1, Cor. `cor:two-sortification-faithful`], at `X`. -/
theorem twoSort_faithful_cod {B₁ B₂ : a ⟶ FinGat.cod}
    (e : (Tw hFinGat).functor.map B₁ = (Tw hFinGat).functor.map B₂) : B₁ = B₂ := by
  have h1 := isoX_MOmega (GT hFinGat) (Zm a) hFinGat.univG B₁
  have h2 := isoX_MOmega (GT hFinGat) (Zm a) hFinGat.univG B₂
  have : tmElt (a := a) B₁ = tmElt B₂ := by
    rw [← h1, ← h2]
    change Rd _ ((Tw hFinGat).functor.map B₁) = Rd _ ((Tw hFinGat).functor.map B₂)
    rw [e]
  exact (equivShrink _).injective (eq_of_heq (Sigma.mk.inj this).2)

/-- **Fullness at `X`**: every `h : T a ⟶ T X` is `T B` for the sort `B` read off from `h` in
`M_Ω`.

[Paper, App. C.2, Prop. `prop:section-terms-two-sortification`], at `X`. -/
theorem twoSort_full_cod (h : (Tw hFinGat).functor.obj a ⟶ (Tw hFinGat).functor.obj FinGat.cod) :
    ∃ B : a ⟶ FinGat.cod, (Tw hFinGat).functor.map B = h := by
  let Z := Zm (hFinGat := hFinGat) a
  let N := MOmega (GT hFinGat) Z hFinGat.univG
  let i : Z ⟶ N := (isInitialZero (Mf hFinGat) hFinGat.univM).to N
  let j := jHom (GT hFinGat) Z hFinGat.univG
  have hij : i ≫ j = 𝟙 Z := (isInitialZero (Mf hFinGat) hFinGat.univM).hom_ext _ _
  have hfam : (famF (GT hFinGat) a).map i ≫ eqToHom (famF_MOmega (GT hFinGat) Z hFinGat.univG) ≫
      psiF (GT hFinGat) Z = 𝟙 _ := by
    rw [← famF_jHom, ← Functor.map_comp, hij, CategoryTheory.Functor.map_id]
  let x : ((famF (GT hFinGat) a).obj Z).I := cast (congrArg FormalCoproduct.I (Rd_fst Z h)) (Rd Z h).2
  have hx : x ≍ (Rd Z h).2 := cast_heq _ _
  have step1 : ((famF (GT hFinGat) a).map i).f x ≍ (Rd N h).2 := Rd_map h i hx
  let b : Shrink.{w} (a ⟶ FinGat.cod) :=
    cast (congrArg FormalCoproduct.I ((Rd_fst N h).trans (famF_MOmega (GT hFinGat) Z hFinGat.univG))) (Rd N h).2
  have step2 : (eqToHom (famF_MOmega (GT hFinGat) Z hFinGat.univG)).f (((famF (GT hFinGat) a).map i).f x) = b := by
    refine eq_of_heq ?_
    rw [fc_eqToHom_f]
    exact ((cast_heq _ _).trans step1).trans (cast_heq _ _).symm
  have key : x = (psiF (GT hFinGat) Z).f b := by
    have := congrArg (fun g => FormalCoproduct.Hom.f g x) hfam
    simp only at this
    rw [← step2]
    exact this.symm
  refine ⟨unX a b, (Rd_zero_injective ?_).symm⟩
  refine Sigma.ext ((Rd_fst Z h).trans (Rd_fst Z _).symm) ?_
  refine hx.symm.trans ?_
  rw [key]
  exact ixX_heq _ _ _

/-- **The base case `X`**: the two-sortification functor induces bijections
`(a ⟶ X) → (T a ⟶ T X)`. -/
theorem twoSortBij_cod : TwoSortBij (Tw hFinGat) FinGat.cod := fun _ =>
  ⟨fun _ _ e => twoSort_faithful_cod e, fun h => twoSort_full_cod h⟩

/-- **Faithfulness at `Y`**: `t` is read off from `T t` in the model `M_Ω`.

[Paper, App. C.1, Cor. `cor:two-sortification-faithful`], at `Y`. -/
theorem twoSort_faithful_dom {t₁ t₂ : a ⟶ FinGat.dom}
    (e : (Tw hFinGat).functor.map t₁ = (Tw hFinGat).functor.map t₂) : t₁ = t₂ := by
  have hB : t₁ ≫ FinGat.arr = t₂ ≫ FinGat.arr :=
    twoSort_faithful_cod (by rw [Functor.map_comp, Functor.map_comp, e])
  have h1 := gY_MOmega (GT hFinGat) (Zm a) hFinGat.univG t₁
  have h2 := gY_MOmega (GT hFinGat) (Zm a) hFinGat.univG t₂
  have : Qd (MOmega (GT hFinGat) (Zm a) hFinGat.univG) ((Tw hFinGat).functor.map t₁) =
      Qd (MOmega (GT hFinGat) (Zm a) hFinGat.univG) ((Tw hFinGat).functor.map t₂) := by rw [e]
  change (gY (GT hFinGat)).obj ((Gm (GT hFinGat) t₁).obj _) =
    (gY (GT hFinGat)).obj ((Gm (GT hFinGat) t₂).obj _) at this
  rw [h1, h2] at this
  exact eq_of_tmS_heq a hB (point_heq_of_eq this)

lemma psiF_φ_congr (K : GL (GT hFinGat) a) {i₁ i₂ : Shrink.{w} (a ⟶ FinGat.cod)} (hi : i₁ = i₂)
    {u : TmS a i₁} {v : TmS a i₂} (huv : u ≍ v) :
    (psiF (GT hFinGat) K).φ i₁ u ≍ (psiF (GT hFinGat) K).φ i₂ v := by
  subst hi; cases huv; rfl

/-- **Fullness at `Y`**: every `h : T a ⟶ T Y` is `T t` for the term `t` read off from `h` in
`M_Ω`.

[Paper, App. C.2, Prop. `prop:section-terms-two-sortification`], at `Y`. -/
theorem twoSort_full_dom (h : (Tw hFinGat).functor.obj a ⟶ (Tw hFinGat).functor.obj FinGat.dom) :
    ∃ t : a ⟶ FinGat.dom, (Tw hFinGat).functor.map t = h := by
  obtain ⟨B, hB⟩ := twoSort_full_cod (h ≫ (Tw hFinGat).functor.map FinGat.arr)
  let Z := Zm (hFinGat := hFinGat) a
  let N := MOmega (GT hFinGat) Z hFinGat.univG
  let i : Z ⟶ N := (isInitialZero (Mf hFinGat) hFinGat.univM).to N
  let j := jHom (GT hFinGat) Z hFinGat.univG
  have E := famF_MOmega (GT hFinGat) Z hFinGat.univG
  have hij : i ≫ j = 𝟙 Z := (isInitialZero (Mf hFinGat) hFinGat.univM).hom_ext _ _
  have hfam : (famF (GT hFinGat) a).map i ≫ eqToHom E ≫ psiF (GT hFinGat) Z = 𝟙 _ := by
    rw [← famF_jHom, ← Functor.map_comp, hij, CategoryTheory.Functor.map_id]
  let hp := h ≫ (Tw hFinGat).functor.map FinGat.arr
  let x : ((famF (GT hFinGat) a).obj Z).I :=
    cast (congrArg FormalCoproduct.I (Rd_fst Z hp)) (Rd Z hp).2
  have hx : x ≍ (Rd Z hp).2 := cast_heq _ _
  have hzX : (Qd Z h).X = ((famF (GT hFinGat) a).obj Z).obj x := Qd_X_eq h Z (Rd_fst Z hp) hx.symm
  let z : ((famF (GT hFinGat) a).obj Z).obj x := cast hzX (Qd Z h).point
  have hz : z ≍ (Qd Z h).point := cast_heq _ _
  have step1 : ((famF (GT hFinGat) a).map i).φ x z ≍ (Qd N h).point := Qd_map h i hx hz
  have step1f : ((famF (GT hFinGat) a).map i).f x ≍ (Rd N hp).2 := Rd_map hp i hx
  have hRN : Rd N hp = tmElt B := by
    change Rd N (h ≫ (Tw hFinGat).functor.map FinGat.arr) = tmElt B
    rw [← hB]
    exact isoX_MOmega (GT hFinGat) Z hFinGat.univG B
  have hi0 : (eqToHom E).f (((famF (GT hFinGat) a).map i).f x) = shX a B := by
    refine eq_of_heq ?_
    rw [fc_eqToHom_f]
    refine ((cast_heq _ _).trans step1f).trans ?_
    rw [hRN]
  have hsX : (Qd N h).X = TmS a (shX a B) :=
    Qd_X_eq h N (F := TmFam a) (by rw [hRN]) (by rw [hRN])
  let s : TmS a (shX a B) := cast hsX (Qd N h).point
  have hs : s ≍ (Qd N h).point := cast_heq _ _
  let t := (tmSOf a s).1
  have ht : t ≫ FinGat.arr = B := (tmSOf_arr a s).trans (Equiv.symm_apply_apply _ _)
  have hφ : (psiF (GT hFinGat) Z).φ ((eqToHom E).f (((famF (GT hFinGat) a).map i).f x))
      ((eqToHom E).φ _ (((famF (GT hFinGat) a).map i).φ x z)) ≍ z := by
    have h' : ∀ g : (famF (GT hFinGat) a).obj Z ⟶ (famF (GT hFinGat) a).obj Z, g = 𝟙 _ →
        g.φ x z ≍ z := by
      rintro g rfl; rfl
    exact h' _ hfam
  have hψ : (psiF (GT hFinGat) Z).φ ((eqToHom E).f (((famF (GT hFinGat) a).map i).f x))
      ((eqToHom E).φ _ (((famF (GT hFinGat) a).map i).φ x z)) ≍
        (psiF (GT hFinGat) Z).φ (shX a B) s :=
    psiF_φ_congr Z hi0 ((fc_eqToHom_φ_heq _ _ _).trans (step1.trans hs.symm))
  have hpt : (psiF (GT hFinGat) Z).φ (shX a B) s ≍ (Qd Z ((Tw hFinGat).functor.map t)).point := by
    refine (psiF_φ_heq _ _ s).trans ((elY_heq _ _ _).trans ?_)
    exact (point_heq_of_eq (Functor.congr_obj (gY_eq (GT hFinGat)) _)).symm
  refine ⟨t, (Qd_zero_injective ?_ ?_).symm⟩
  · rw [← Functor.map_comp, ht, hB]
  · exact ((hpt.symm.trans hψ.symm).trans (hφ.trans hz)).symm

/-- **The base case `Y`**: the two-sortification functor induces bijections
`(a ⟶ Y) → (T a ⟶ T Y)`. -/
theorem twoSortBij_dom : TwoSortBij (Tw hFinGat) FinGat.dom := fun _ =>
  ⟨fun _ _ e => twoSort_faithful_dom e, fun h => twoSort_full_dom h⟩

end

end TwoSortFF

section Main

open TwoSortFF

variable {FinGat : Lexp.{w + 1, w + 2}} [LocallySmall.{w} FinGat.carrier]
  (hFinGat : IsBiInitial FinGat)

/-- The data of `TwoSortFF.TwoSortData` for a bi-initial `FinGat`: the two-sortification
functor and the model functor. -/
noncomputable def twoSortData : TwoSortData FinGat where
  tw := twoSortification.{w + 1, w + 2} hFinGat
  mf := modelFunctor hFinGat
  univM := IsBiInitial.hasUniversalNatTrans.{w + 1, w + 2} hFinGat _
  univG := IsBiInitial.hasUniversalNatTrans.{w + 1, w + 2} hFinGat _

/-- The two-sortification functor induces bijections on all hom-sets: the induction of
Proposition "faithful-at-XGAT-YGAT" from the base cases `X` and `Y`.

[Paper, App. C, Prop. `prop:faithful-at-XGAT-YGAT`]. -/
theorem twoSortBij_all (b : FinGat.carrier) :
    TwoSortBij (twoSortification.{w + 1, w + 2} hFinGat) b :=
  hFinGat.induction
    { of_iso := fun i hb => twoSortBij_of_iso _ i hb
      terminal := twoSortBij_terminal _
      pullback := fun hpb h₁ h₂ hS => twoSortBij_pullback _ hpb h₁ h₂ hS
      exp := fun c hc => twoSortBij_exp _ c
        (TwoSortFF.twoSortBij_cod (hFinGat := twoSortData hFinGat)) hc
      dom := TwoSortFF.twoSortBij_dom (hFinGat := twoSortData hFinGat)
      cod := TwoSortFF.twoSortBij_cod (hFinGat := twoSortData hFinGat) } b

/-- **The two-sortification functor is full.**

[Paper, App. C.2, final Corollary]. -/
instance twoSortification_full : (twoSortification.{w + 1, w + 2} hFinGat).functor.Full :=
  ⟨fun {a b} f => (twoSortBij_all hFinGat b a).2 f⟩

/-- **The two-sortification functor is faithful.**

[Paper, App. C.1, Cor. `cor:two-sortification-faithful`]. -/
instance twoSortification_faithful : (twoSortification.{w + 1, w + 2} hFinGat).functor.Faithful :=
  ⟨fun {a b} _ _ h => (twoSortBij_all hFinGat b a).1 h⟩

/-- **The two-sortification functor is fully faithful.**

[Paper, App. C.2, final Corollary]: `T` is fully faithful. -/
noncomputable def twoSortificationFullyFaithful :
    (twoSortification.{w + 1, w + 2} hFinGat).functor.FullyFaithful :=
  Functor.FullyFaithful.ofFullyFaithful _

end Main

end Lexp
