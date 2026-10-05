/-
Copyright (c) 2026 Lean Contributor. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Contributor
-/
import CartexpAristotle.CompExp.Basic
import CartexpAristotle.UniversalNatTrans

/-!
# Maps out of a bi-initial `CompExp`

This is the analogue for `CompExp` of `CartexpAristotle.UniversalNatTrans`.

Let `A` be a bi-initial object of `CompExp`. Given an object `C` of `CompExp`, a
pullback-preserving functor `F : A ⥤ C`, a morphism `G : A ⟶ C` of `CompExp` and a morphism
`f : F p ⟶ G p` of arrows which forms a pullback square, there is a unique natural transformation
`F ⟶ G` restricting to `f` (`CompExp.IsBiInitial.hasUniversalNatTrans`, stated with the property
`Lexp.HasUniversalNatTrans` of the underlying morphism of `Lexp`).

The proof is the same as for `Lexp`: the comma category `Comma F (𝟭 C)` is an object of `Lexp`
(`Lexp.commaOf`), and it has all the `w`-small wide pullbacks of `A` and `C` (computed
componentwise, whatever `F` is), so it is an object of `CompExp`; the projections and the section
associated to a natural transformation `α : F ⟶ G` preserve them (the latter because `G` does).
Note that, as in `Lexp`, `F` only needs to preserve pullbacks.

## References

* [Paper, §2.2, Thm. `thm:universal-property-natural-transformation`] and its proof in
  [Paper, App. A.3], adapted to `CompExp`.
-/

open CategoryTheory Limits

universe w v u

namespace CompExp

/-- An object `A` of `CompExp` is bi-initial if every hom-category `A ⟶ B` is equivalent to the
terminal category. -/
def IsBiInitial (A : CompExp.{w, v, u}) : Prop :=
  ∀ B : CompExp.{w, v, u}, Nonempty ((A ⟶ B) ≌ Discrete PUnit.{1})

namespace IsBiInitial

variable {A : CompExp.{w, v, u}} {B : CompExp.{w, v, u}}

/-- A bi-initial object has a morphism to every object. -/
lemma nonempty_hom (hA : IsBiInitial A) (B : CompExp.{w, v, u}) : Nonempty (A ⟶ B) :=
  ⟨(hA B).some.inverse.obj ⟨⟨⟩⟩⟩

/-- Any two parallel 2-cells out of a bi-initial object coincide. -/
lemma hom₂_ext (hA : IsBiInitial A) {F G : A ⟶ B} (α β : F ⟶ G) : α = β := by
  have := (hA B).some.faithful_functor
  exact (hA B).some.functor.map_injective (Subsingleton.elim _ _)

/-- Any two morphisms out of a bi-initial object are isomorphic. -/
lemma nonempty_iso (hA : IsBiInitial A) (F G : A ⟶ B) : Nonempty (F ≅ G) :=
  ⟨((hA B).some.unitIso.app F) ≪≫
    (hA B).some.inverse.mapIso (eqToIso (Subsingleton.elim _ _)) ≪≫
    ((hA B).some.unitIso.app G).symm⟩

end IsBiInitial

section Comma

variable {A C : CompExp.{w, v, max u v}} (F : A.carrier ⥤ C.carrier)
  [PreservesLimitsOfShape WalkingCospan F]
  (G : A ⟶ C) [IsExpArr (G.functor.map A.arr)] {y : F.obj A.dom ⟶ G.functor.obj A.dom}
  {x : F.obj A.cod ⟶ G.functor.obj A.cod}
  (hsq : IsPullback y (F.map A.arr) (G.functor.map A.arr) x)

/-- The comma category `Comma F (𝟭 C)` as an object of `CompExp`: its wide pullbacks are computed
componentwise. -/
noncomputable def commaOf : CompExp.{w, v, max u v} where
  toLexp := Lexp.commaOf F G.toLexpHom hsq
  hasWidePullbacks := fun J =>
    inferInstanceAs (HasLimitsOfShape (WidePullbackShape J) (Comma F (𝟭 C.carrier)))

/-- The first projection from the comma category. -/
noncomputable def commaFst : commaOf F G hsq ⟶ A where
  toHom := Lexp.commaFst F G.toLexpHom hsq
  preservesWidePullbacks J :=
    inferInstanceAs (PreservesLimitsOfShape (WidePullbackShape J) (Comma.fst F (𝟭 C.carrier)))

/-- The second projection from the comma category. -/
noncomputable def commaSnd : commaOf F G hsq ⟶ C where
  toHom := Lexp.commaSnd F G.toLexpHom hsq
  preservesWidePullbacks J :=
    inferInstanceAs (PreservesLimitsOfShape (WidePullbackShape J) (Comma.snd F (𝟭 C.carrier)))

/-- The morphism `A ⟶ commaOf F G hsq` associated to a natural transformation `α : F ⟶ G`
restricting to the pullback square `hsq`. It preserves wide pullbacks since `G` does. -/
noncomputable def commaSec (α : F ⟶ G.functor) (hα : α.app A.dom = y) (hαx : α.app A.cod = x) :
    A ⟶ commaOf F G hsq where
  toHom := Lexp.commaSec F G.toLexpHom hsq α hα hαx
  preservesWidePullbacks J :=
    inferInstanceAs (PreservesLimitsOfShape (WidePullbackShape J) (CommaLexp.toComma α))

variable {F G}

include hsq in
/-- A natural transformation `F ⟶ G` restricting to a given pullback square is unique. -/
lemma natTrans_unique (hA : IsBiInitial A) {α α' : F ⟶ G.functor}
    (hα : α.app A.dom = y) (hαx : α.app A.cod = x)
    (hα' : α'.app A.dom = y) (hαx' : α'.app A.cod = x) : α = α' := by
  let K := commaSec F G hsq α hα hαx
  let K' := commaSec F G hsq α' hα' hαx'
  let η : K ⟶ K' := (hA.nonempty_iso K K').some.hom
  have hL : ∀ Z, (η.nat.app Z).left = 𝟙 Z := by
    let c₁ : K ≫ commaFst F G hsq ⟶ K' ≫ commaFst F G hsq :=
      (⟨𝟙 (𝟭 A.carrier),
        by change 𝟙 A.dom ≫ (𝟙 A.dom ≫ 𝟙 A.dom) = 𝟙 A.dom ≫ 𝟙 A.dom; simp,
        by change 𝟙 A.cod ≫ (𝟙 A.cod ≫ 𝟙 A.cod) = 𝟙 A.cod ≫ 𝟙 A.cod; simp⟩ :
        Lexp.Hom₂ (K.toLexpHom ≫ (commaFst F G hsq).toLexpHom)
          (K'.toLexpHom ≫ (commaFst F G hsq).toLexpHom))
    have := hA.hom₂_ext
      (Lexp.Hom₂.whiskerRight η (commaFst F G hsq).toLexpHom :
        K ≫ commaFst F G hsq ⟶ K' ≫ commaFst F G hsq) c₁
    intro Z
    exact congrArg (fun t => Lexp.Hom₂.nat t |>.app Z) this
  have hR : ∀ Z, (η.nat.app Z).right = 𝟙 (G.functor.obj Z) := by
    let c₂ : K ≫ commaSnd F G hsq ⟶ K' ≫ commaSnd F G hsq :=
      (⟨𝟙 G.functor,
        by change 𝟙 _ ≫ (𝟙 _ ≫ G.iso.hom.left) = 𝟙 _ ≫ G.iso.hom.left; simp,
        by change 𝟙 _ ≫ (𝟙 _ ≫ G.iso.hom.right) = 𝟙 _ ≫ G.iso.hom.right; simp⟩ :
        Lexp.Hom₂ (K.toLexpHom ≫ (commaSnd F G hsq).toLexpHom)
          (K'.toLexpHom ≫ (commaSnd F G hsq).toLexpHom))
    have := hA.hom₂_ext
      (Lexp.Hom₂.whiskerRight η (commaSnd F G hsq).toLexpHom :
        K ≫ commaSnd F G hsq ⟶ K' ≫ commaSnd F G hsq) c₂
    intro Z
    exact congrArg (fun t => Lexp.Hom₂.nat t |>.app Z) this
  refine NatTrans.ext (funext fun Z => ?_)
  have w : F.map (η.nat.app Z).left ≫ α'.app Z = α.app Z ≫ (η.nat.app Z).right :=
    (η.nat.app Z).w
  rw [hL, hR] at w
  have w' : F.map (𝟙 Z) ≫ α'.app Z = α.app Z ≫ 𝟙 (G.functor.obj Z) := w
  rw [F.map_id, Category.id_comp, Category.comp_id] at w'
  exact w'.symm

include hsq in
/-- Existence of a natural transformation restricting to a given pullback square. -/
lemma natTrans_exists (hA : IsBiInitial A) :
    ∃ α : F ⟶ G.functor, α.app A.dom = y ∧ α.app A.cod = x := by
  obtain ⟨K⟩ := hA.nonempty_hom (commaOf F G hsq)
  obtain ⟨e₁⟩ := hA.nonempty_iso (K ≫ commaFst F G hsq) (𝟙 A)
  obtain ⟨e₂⟩ := hA.nonempty_iso (K ≫ commaSnd F G hsq) G
  let e₁' := Hom.isoToHom e₁
  let e₂' := Hom.isoToHom e₂
  let T : A.carrier ⥤ Comma F (𝟭 C.carrier) := K.functor
  let α : F ⟶ G.functor := CommaLexp.natTransOfSection T e₁'.inv.nat e₂'.hom.nat
  let k : T.obj A.dom ⟶ CommaLexp.commaDom F y := K.iso.hom.left
  let k' : T.obj A.cod ⟶ CommaLexp.commaCod F x := K.iso.hom.right
  let a : A.dom ⟶ (T.obj A.dom).left := e₁'.inv.nat.app A.dom
  let a' : A.cod ⟶ (T.obj A.cod).left := e₁'.inv.nat.app A.cod
  let b : (T.obj A.dom).right ⟶ G.functor.obj A.dom := e₂'.hom.nat.app A.dom
  let b' : (T.obj A.cod).right ⟶ G.functor.obj A.cod := e₂'.hom.nat.app A.cod
  have c1 : a ≫ k.left = 𝟙 A.dom := by
    have h : a ≫ (k.left ≫ 𝟙 A.dom) = 𝟙 A.dom := e₁'.inv.left_comm
    exact (congrArg (a ≫ ·) (Category.comp_id k.left)).symm.trans h
  have c1' : a' ≫ k'.left = 𝟙 A.cod := by
    have h : a' ≫ (k'.left ≫ 𝟙 A.cod) = 𝟙 A.cod := e₁'.inv.right_comm
    exact (congrArg (a' ≫ ·) (Category.comp_id k'.left)).symm.trans h
  have c2 : b = k.right := by
    have h : b ≫ G.iso.hom.left = k.right ≫ G.iso.hom.left := e₂'.hom.left_comm
    exact (cancel_mono _).1 h
  have c2' : b' = k'.right := by
    have h : b' ≫ G.iso.hom.right = k'.right ≫ G.iso.hom.right := e₂'.hom.right_comm
    exact (cancel_mono _).1 h
  refine ⟨α, ?_, ?_⟩
  · have hw : F.map k.left ≫ y = (T.obj A.dom).hom ≫ k.right := k.w
    change F.map a ≫ (T.obj A.dom).hom ≫ b = y
    rw [c2, ← hw, ← F.map_comp_assoc, c1, F.map_id, Category.id_comp]
  · have hw : F.map k'.left ≫ x = (T.obj A.cod).hom ≫ k'.right := k'.w
    change F.map a' ≫ (T.obj A.cod).hom ≫ b' = x
    rw [c2', ← hw, ← F.map_comp_assoc, c1', F.map_id, Category.id_comp]

end Comma

/-- **Main theorem.** Let `A` be a bi-initial object of `CompExp`, with chosen exponentiable arrow
`p = A.arr : Y ⟶ X`. Let `C` be an object of `CompExp`, `F : A ⥤ C` a functor preserving
pullbacks, `G : A ⟶ C` a morphism of `CompExp`, and `f : F p ⟶ G p` a morphism of arrows whose
underlying square is a pullback. Then there is a unique natural transformation `α : F ⟶ G` whose
components at `Y` and `X` are the components of `f`.

[Paper, §2.2, Thm. `thm:universal-property-natural-transformation`], for `CompExp`. -/
theorem IsBiInitial.existsUnique_natTrans_gen {A C : CompExp.{w, v, max u v}} (hA : IsBiInitial A)
    (F : A.carrier ⥤ C.carrier) [PreservesLimitsOfShape WalkingCospan F] (G : A ⟶ C)
    (f : Arrow.mk (F.map A.arr) ⟶ Arrow.mk (G.functor.map A.arr))
    (hf : IsPullback f.left (F.map A.arr) (G.functor.map A.arr) f.right) :
    ∃! α : F ⟶ G.functor, α.app A.dom = f.left ∧ α.app A.cod = f.right := by
  let _ : IsExpArr (G.functor.map A.arr) := IsExpArr.ofIso C.arr (G.functor.map A.arr) G.iso.symm
  obtain ⟨α, h₁, h₂⟩ := natTrans_exists (hsq := hf) hA
  exact ⟨α, ⟨h₁, h₂⟩, fun α' h' => natTrans_unique hf hA h'.1 h'.2 h₁ h₂⟩

/-- Every morphism out of a bi-initial object of `CompExp` has the universal property of natural
transformations (`Lexp.HasUniversalNatTrans`). -/
theorem IsBiInitial.hasUniversalNatTrans {A C : CompExp.{w, v, max u v}} (hA : IsBiInitial A)
    (G : A ⟶ C) : Lexp.HasUniversalNatTrans G.toLexpHom :=
  fun F _ f hf => hA.existsUnique_natTrans_gen F G f hf

end CompExp
