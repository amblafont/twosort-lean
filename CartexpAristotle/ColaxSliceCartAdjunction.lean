import CartexpAristotle.ColaxSliceCartToOver
import CartexpAristotle.ColaxSliceCartLimits
import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# `ColaxSliceCart.toOver` is a right adjoint

The slice `Over (Cat.of Fam)` embeds into `ColaxSliceCart` (`ColaxSliceCart.ofOver`): a category over `Fam`
is an object of `ColaxSliceCart`, and a functor commuting strictly with the projections to `Fam` is a
morphism of `ColaxSliceCart` whose natural transformation is an identity.

This embedding is left adjoint to `ColaxSliceCart.toOver` (`ColaxSliceCart.ofOverAdj`): a functor
`D ⥤ CartComma X` over `Fam` is the same as a functor `D ⥤ X.cat` together with a pointwise
cartesian natural transformation into the projection `D ⥤ Fam`.

## References

* [Paper, App. A.4, proof of Prop. `prop:semantic-twosort-functor`]: "the induced functor from
  `CAT //_c Fam` to `CAT/Fam` can be characterised as the right adjoint of the obvious embedding
  of `CAT/Fam` into `CAT //_c Fam`" (`ColaxSliceCart.ofOverAdj`).
-/

universe w

open CategoryTheory Limits

namespace ColaxSliceCart

lemma eqToHom_isPointwiseCartesian {C : Type*} [Category C] {F G : C ⥤ Fam.{w}} (h : F = G) :
    (eqToHom h).IsPointwiseCartesian := by
  subst h
  exact fun _ => Fam.Hom.isCartesian_id _

lemma eqToHom_app_base_heq {C : Type*} [Category C] {F G : C ⥤ Fam.{w}} (h : F = G) (c : C) :
    HEq ((eqToHom h).app c : Fam.Hom _ _).base (id : (F.obj c).base → (F.obj c).base) := by
  subst h
  rfl

/-- The embedding of the slice of categories over `Fam` into `ColaxSliceCart`. -/
def ofOver : Over (Cat.of Fam.{w}) ⥤ ColaxSliceCart.{w, w, w + 1} where
  obj d := ⟨d.left, d.hom.toFunctor⟩
  map {d d'} k :=
    { functor := k.left.toFunctor
      nat := eqToHom (congrArg Cat.Hom.toFunctor (Over.w k))
      isPointwiseCartesian := eqToHom_isPointwiseCartesian _ }
  map_id d := Hom.ext_of_functor_eq rfl (fun c =>
    (eqToHom_app_base_heq (congrArg Cat.Hom.toFunctor (Over.w (𝟙 d))) c))
  map_comp {d d' d''} k k' := Hom.ext_of_functor_eq rfl (fun c => by
    change HEq _ ((Hom.comp _ _).nat.app c : Fam.Hom _ _).base
    simp only [Hom.comp, NatTrans.comp_app, Functor.whiskerLeft_app, eqToHom_app, eqToHom_trans]
    rfl)

namespace CartComma

variable (X : ColaxSliceCart.{w, w, w + 1})

/-- The projection `(c, T, f) ↦ c` of the cartesian comma category to the underlying
category. -/
def objFunctor : CartComma X ⥤ X.cat where
  obj a := a.obj
  map f := (f : Hom _ _).left

variable {X}

lemma ext' {a b : CartComma X} (h₁ : a.obj = b.obj) (h₂ : a.tgt = b.tgt)
    (h₃ : HEq a.hom b.hom) : a = b := by
  rcases a with ⟨ao, at', ah, _⟩
  rcases b with ⟨bo, bt, bh, _⟩
  dsimp only at h₁ h₂ h₃
  subst h₁ h₂
  obtain rfl := eq_of_heq h₃
  rfl

lemma Hom.hext {a a' b b' : CartComma X} (ha : a = a') (hb : b = b') {f : Hom a b}
    {g : Hom a' b'} (h₁ : HEq f.left g.left) (h₂ : HEq f.right g.right) : HEq f g := by
  subst ha hb
  rcases f with ⟨fl, fr, _⟩
  rcases g with ⟨gl, gr, _⟩
  obtain rfl := eq_of_heq h₁
  obtain rfl := eq_of_heq h₂
  rfl

end CartComma

lemma heq_id_eqToHom {C : Type*} [Category C] {A B : C} (h : A = B) :
    HEq (𝟙 A) (eqToHom h) := by
  subst h; rfl

/-- The counit of the adjunction `ofOver ⊣ toOver`. -/
def ofOverCounit (X : ColaxSliceCart.{w, w, w + 1}) :
    (⟨Cat.of (CartComma X), CartComma.proj X⟩ : ColaxSliceCart.{w, w, w + 1}) ⟶ X where
  functor := CartComma.objFunctor X
  nat :=
    { app a := a.hom
      naturality _ _ f := (f : CartComma.Hom _ _).w }
  isPointwiseCartesian a := a.isCartesian

/-- The functor `D ⥤ CartComma (D, q)` sending `x` to the identity of `q x`. -/
def unitFunctor (d : Over (Cat.of Fam.{w})) :
    d.left ⥤ CartComma (⟨d.left, d.hom.toFunctor⟩ : ColaxSliceCart.{w, w, w + 1}) where
  obj x := ⟨x, d.hom.toFunctor.obj x, 𝟙 _, Fam.Hom.isCartesian_id _⟩
  map {x y} φ := ⟨φ, d.hom.toFunctor.map φ, by
    change d.hom.toFunctor.map φ ≫ 𝟙 _ = 𝟙 _ ≫ d.hom.toFunctor.map φ
    simp⟩

/-- The unit of the adjunction `ofOver ⊣ toOver`. -/
def ofOverUnit (d : Over (Cat.of Fam.{w})) : d ⟶ toOver.obj (ofOver.obj d) :=
  Over.homMk (unitFunctor d).toCatHom rfl

/-- The embedding `ofOver` is left adjoint to `toOver`.

[Paper, App. A.4, proof of Prop. `prop:semantic-twosort-functor`]. -/
def ofOverAdj : ofOver.{w} ⊣ toOver.{w} :=
  Adjunction.mkOfUnitCounit
    { unit :=
        { app := ofOverUnit
          naturality := fun d d' k => by
            have hk := congrArg Cat.Hom.toFunctor (Over.w k)
            have hobj : ∀ x, ((𝟭 _).map k ≫ ofOverUnit d').left.toFunctor.obj x =
                (ofOverUnit d ≫ (ofOver ⋙ toOver).map k).left.toFunctor.obj x := fun x => by
              refine CartComma.ext' rfl (Functor.congr_obj hk x) ?_
              change HEq (𝟙 _) ((eqToHom hk).app x ≫ 𝟙 _)
              rw [eqToHom_app, Category.comp_id]
              exact heq_id_eqToHom _
            exact Over.OverMorphism.ext (Cat.Hom.ext (Functor.hext hobj (fun x y φ =>
              CartComma.Hom.hext (hobj x) (hobj y) HEq.rfl (Functor.hcongr_hom hk φ)))) }
      counit :=
        { app := ofOverCounit
          naturality := fun X Y g => Hom.ext_of_functor_eq rfl (fun a => HEq.rfl) }
      left_triangle := by
        ext d
        exact Hom.ext_of_functor_eq rfl (fun c => HEq.rfl)
      right_triangle := by
        ext X
        rfl }

end ColaxSliceCart

namespace ColaxSliceCart

/-- `toOver` preserves all (small) limits, being a right adjoint. -/
instance toOver_preservesLimits : PreservesLimitsOfSize.{0, 0} toOver.{w} :=
  ofOverAdj.rightAdjoint_preservesLimits

end ColaxSliceCart
