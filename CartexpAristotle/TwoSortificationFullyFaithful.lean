/-
Copyright (c) 2026 Lean Contributor. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Contributor
-/
import CartexpAristotle.TwoSortification
import CartexpAristotle.BiInitialInduction

/-!
# Full faithfulness of the two-sortification functor

Let `FinGat` be a bi-initial object of `Lexp`, with chosen exponentiable arrow `p : Y ⟶ X`,
and let `T : FinGat ⥤ Φ FinGat = FinGat / P X` be the underlying functor of the two-sortification
functor. We show that `T` is fully faithful, by induction over the objects of `FinGat`
(`Lexp.IsBiInitial.induction`) applied to the property of an object `b`

  "for every object `a`, the map `(a ⟶ b) → (T a ⟶ T b)` induced by `T` is bijective".

This property is invariant under isomorphism, holds for the terminal object (since `T` preserves
it), is closed under pullbacks (since `T` preserves them) and under the chosen exponentials along
`p` (since `T` preserves them, using the transposition of the exponential adjunction). This is
Proposition "faithful-at-XGAT-YGAT" of the appendix.

The two base cases `b = Y` and `b = X`, and the resulting full faithfulness of `T`, are proved in
`CartexpAristotle.TwoSortFFMain` following the appendix.

## References

* [Paper, App. C, Prop. `prop:faithful-at-XGAT-YGAT`]: full faithfulness of a `Lexp`-functor
  out of `FinGat` reduces to full faithfulness at `X` and `Y` (`TwoSortBij`, closure lemmas
  `twoSortBij_of_iso`, `twoSortBij_terminal`, `twoSortBij_pullback`, `twoSortBij_exp`).
-/

open CategoryTheory Limits

universe v u

section FBF

variable {C : Type*} [Category C] {D : Type*} [Category D]

/-- A functor preserving pullbacks commutes with `FBF_on_mor`. -/
lemma map_FBF_on_mor (F : C ⥤ D) [PreservesLimitsOfShape WalkingCospan F] {X Y c : C}
    {u : Y ⟶ X} (d : Data u c) {e : C} {f : e ⟶ d.P} {h : e ⟶ X} (K : ChosenPullback u h)
    (eq : h = f ≫ d.pi) :
    F.map (FBF_on_mor d K eq) = FBF_on_mor (functor_on F d) (functPullback F K)
      (show F.map h = F.map f ≫ F.map d.pi by rw [eq, F.map_comp]) := by
  apply (functor_on F d).Pbk.hom_ext
  · erw [SliceExp.FBF_on_mor_fst, ← F.map_comp, SliceExp.FBF_on_mor_fst]
    rfl
  · erw [SliceExp.FBF_on_mor_snd, ← F.map_comp, SliceExp.FBF_on_mor_snd, F.map_comp]
    rfl

end FBF

namespace Lexp

variable {FinGat : Lexp.{v, max u v}} (hFinGat : IsBiInitial FinGat)

/-- The underlying functor `FinGat ⥤ FinGat / P X` of the two-sortification functor. -/
noncomputable abbrev twoSortFun := (twoSortification hFinGat).functor

/-- The property of an object `b` that, for every object `a`, the two-sortification functor
induces a bijection `(a ⟶ b) → (T a ⟶ T b)`.

[Paper, App. C, Prop. `prop:faithful-at-XGAT-YGAT`]: `T` is fully faithful at `b`. -/
def TwoSortBij (b : FinGat.carrier) : Prop :=
  ∀ a : FinGat.carrier, Function.Bijective (fun g : a ⟶ b => (twoSortFun hFinGat).map g)

lemma twoSortBij_of_iso {b b' : FinGat.carrier} (i : b ≅ b') (hb : TwoSortBij hFinGat b) :
    TwoSortBij hFinGat b' := by
  intro a
  constructor
  · intro g₁ g₂ hg
    have : g₁ ≫ i.inv = g₂ ≫ i.inv :=
      (hb a).1 (by simp only [CategoryTheory.Functor.map_comp]; exact congrArg (· ≫ _) hg)
    simpa using congrArg (· ≫ i.hom) this
  · intro h
    obtain ⟨g, hg⟩ := (hb a).2 (h ≫ (twoSortFun hFinGat).map i.inv)
    refine ⟨g ≫ i.hom, ?_⟩
    simp only [CategoryTheory.Functor.map_comp] at hg ⊢
    rw [hg, Category.assoc, ← CategoryTheory.Functor.map_comp, i.inv_hom_id,
      CategoryTheory.Functor.map_id, Category.comp_id]

lemma twoSortBij_terminal : TwoSortBij hFinGat (⊤_ FinGat.carrier) := by
  have hT : IsTerminal ((twoSortFun hFinGat).obj (⊤_ FinGat.carrier)) :=
    IsTerminal.isTerminalObj _ _ terminalIsTerminal
  intro a
  exact ⟨fun _ _ _ => terminal.hom_ext _ _,
    fun h => ⟨terminal.from a, hT.hom_ext _ _⟩⟩

lemma twoSortBij_pullback {W X₁ X₂ S : FinGat.carrier} {fst : W ⟶ X₁} {snd : W ⟶ X₂}
    {f : X₁ ⟶ S} {g : X₂ ⟶ S} (hpb : IsPullback fst snd f g) (h₁ : TwoSortBij hFinGat X₁)
    (h₂ : TwoSortBij hFinGat X₂) (hS : TwoSortBij hFinGat S) : TwoSortBij hFinGat W := by
  have hTpb := (twoSortFun hFinGat).map_isPullback hpb
  intro a
  constructor
  · intro k₁ k₂ hk
    simp only at hk
    apply hpb.hom_ext
    · exact (h₁ a).1 (by simp only [CategoryTheory.Functor.map_comp, hk])
    · exact (h₂ a).1 (by simp only [CategoryTheory.Functor.map_comp, hk])
  · intro h
    obtain ⟨k₁, hk₁⟩ := (h₁ a).2 (h ≫ (twoSortFun hFinGat).map fst)
    obtain ⟨k₂, hk₂⟩ := (h₂ a).2 (h ≫ (twoSortFun hFinGat).map snd)
    simp only at hk₁ hk₂
    have hw : k₁ ≫ f = k₂ ≫ g := (hS a).1 (by
      change (twoSortFun hFinGat).map (k₁ ≫ f) = (twoSortFun hFinGat).map (k₂ ≫ g)
      rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, hk₁, hk₂,
        Category.assoc, Category.assoc, ← CategoryTheory.Functor.map_comp,
        ← CategoryTheory.Functor.map_comp, hpb.w])
    refine ⟨hpb.lift k₁ k₂ hw, ?_⟩
    apply hTpb.hom_ext
    · simp only [← CategoryTheory.Functor.map_comp, IsPullback.lift_fst, hk₁]
    · simp only [← CategoryTheory.Functor.map_comp, IsPullback.lift_snd, hk₂]

lemma twoSortBij_exp (c : FinGat.carrier) (hX : TwoSortBij hFinGat FinGat.cod)
    (hc : TwoSortBij hFinGat c) :
    TwoSortBij hFinGat (IsExpArr.isExpArrowData (u := FinGat.arr) c).P := by
  intro a
  set d := IsExpArr.isExpArrowData (u := FinGat.arr) c
  haveI U' : Universal (functor_on (twoSortFun hFinGat) d) :=
    FunctorPreserves.functor_preserves d inferInstance
  constructor
  · intro m₁ m₂ hm
    simp only at hm
    have hx : m₁ ≫ d.pi = m₂ ≫ d.pi :=
      (hX a).1 (by simp only [CategoryTheory.Functor.map_comp, hm])
    let K := SliceExp.chosenOfIsPullback (IsPullback.of_hasPullback FinGat.arr (m₁ ≫ d.pi))
    apply Universal.uniq (data := d) K rfl hx
    apply (hc K.pullback).1
    simp only [CategoryTheory.Functor.map_comp, map_FBF_on_mor]
    congr 1
    exact SliceExp.FBF_on_mor_congr _ _ hm _ _
  · intro h
    obtain ⟨x, hx⟩ := (hX a).2 (h ≫ (twoSortFun hFinGat).map d.pi)
    simp only at hx
    let K := SliceExp.chosenOfIsPullback (IsPullback.of_hasPullback FinGat.arr x)
    have e : (twoSortFun hFinGat).map x = h ≫ (functor_on (twoSortFun hFinGat) d).pi := hx
    obtain ⟨g, hg⟩ := (hc K.pullback).2
      (FBF_on_mor (functor_on (twoSortFun hFinGat) d) (functPullback (twoSortFun hFinGat) K) e ≫
        (twoSortFun hFinGat).map d.epsilon)
    simp only at hg
    refine ⟨Universal.mor (data := d) (Kuf := K) g, ?_⟩
    have hs : x = Universal.mor (data := d) (Kuf := K) g ≫ d.pi :=
      Universal.isSlice (data := d) (Kuf := K) g
    have e' : (twoSortFun hFinGat).map x = (twoSortFun hFinGat).map
        (Universal.mor (data := d) (Kuf := K) g) ≫ (functor_on (twoSortFun hFinGat) d).pi := by
      change _ = _ ≫ (twoSortFun hFinGat).map d.pi
      rw [← CategoryTheory.Functor.map_comp, ← hs]
    apply Universal.uniq (data := functor_on (twoSortFun hFinGat) d)
      (functPullback (twoSortFun hFinGat) K) e' e
    change _ ≫ (twoSortFun hFinGat).map d.epsilon = _ ≫ (twoSortFun hFinGat).map d.epsilon
    rw [← map_FBF_on_mor (twoSortFun hFinGat) d K hs, ← CategoryTheory.Functor.map_comp,
      ← Universal.comm (data := d) (Kuf := K) g, hg]

end Lexp
