import CartexpAristotle.SemanticTwoSortFunctor
import CartexpAristotle.CatPullbackCriterion

/-!
# The projection from the colax slice to `Cat` is a morphism of `Lexp`

* `ColaxSliceCart.forget : ColaxSliceCart ⥤ Cat` sends `(C, F)` to `C` and `(H, n)` to `H`.
* It preserves pullbacks (the pullback in `ColaxSliceCart` lies over the strict pullback of categories),
  the terminal object, and the exponentiable arrow `UFam` (the partial exponential of `UFam` lies
  over the partial exponential of `U` in `Cat`).
* `ColaxSliceCartForget.forgetHom : ColaxSliceCartLexp ⟶ CatLexp` is the resulting strict morphism of `Lexp`.
* `ColaxSliceCart.transportIso`: an object `(C, F)` is isomorphic to `(C', i⁻¹ ⋙ F)` for any isomorphism
  of categories `i : C ≅ C'`, by an isomorphism lying over `i` (the projection is an
  isofibration).

## References

* [Paper, §4.1, Thm. `thm:colax-exponentiable`], last sentence: the projection
  `CAT //_c Fam → CAT` is a `Lexp`-functor (`ColaxSliceCartForget.forgetHom`).
* [Paper, §4.1, proof of Cor. `cor:family-functor-gat`]: "the projection `CAT //_c Fam → CAT` is an
  isofibration" (`ColaxSliceCart.transportIso`).
-/

universe w

open CategoryTheory Limits ColaxSliceCart ColaxSliceCartExponentiable PointedForget SemanticTwoSortFunctor

namespace ColaxSliceCart

/-- The projection from the cartesian colax slice to `Cat`.

[Paper, §4.1, Thm. `thm:colax-exponentiable`]: the projection `CAT //_c Fam → CAT`. -/
def forget : ColaxSliceCart.{w, w, w + 1} ⥤ Cat.{w, w + 1} where
  obj X := X.cat
  map f := (f : Hom _ _).functor.toCatHom
  map_id _ := rfl
  map_comp _ _ := rfl

@[simp] lemma forget_map_toFunctor {X Y : ColaxSliceCart.{w, w, w + 1}} (f : X ⟶ Y) :
    (forget.map f).toFunctor = (f : Hom X Y).functor := rfl

section Pullbacks

variable {X Y Z : ColaxSliceCart.{w, w, w + 1}} (f : X ⟶ Z) (g : Y ⟶ Z)

lemma forget_crit : CatPullback.Crit (forget.map (pullbackCone f g).fst)
    (forget.map (pullbackCone f g).snd) (forget.map f) (forget.map g) where
  obj x₁ x₂ h := ⟨⟨x₁, x₂, h⟩, ⟨rfl, rfl⟩, fun _ hw => PbObj.ext hw.1 hw.2⟩
  hom _ _ h₁ h₂ h := ⟨⟨h₁, h₂, h⟩, ⟨rfl, rfl⟩, fun _ hk => PbHom.ext hk.1 hk.2⟩

lemma forget_isPullback : IsPullback (forget.map (pullbackCone f g).fst)
    (forget.map (pullbackCone f g).snd) (forget.map f) (forget.map g) :=
  CatPullback.isPullback_of_crit (forget_crit f g)
    (by rw [← forget.map_comp, ← forget.map_comp, (pullbackCone f g).condition])

instance : PreservesLimit (cospan f g) forget :=
  preservesLimit_of_preserves_limit_cone (pullbackConeIsLimit f g)
    ((isLimitMapConePullbackConeEquiv forget (pullbackCone f g).condition).symm
      (forget_isPullback f g).isLimit)

end Pullbacks

instance forget_preservesPullbacks : PreservesLimitsOfShape WalkingCospan forget.{w} :=
  ⟨fun {K} => preservesLimit_of_iso_diagram forget (diagramIsoCospan K).symm⟩

/-- The one-object category `Pt` is terminal in `Cat`. -/
def ptIsTerminal : IsTerminal (Cat.of Pt.{w + 1} : Cat.{w, w + 1}) :=
  IsTerminal.ofUniqueHom (fun C => ((Functor.const C).obj (Pt.star : Pt.{w + 1})).toCatHom)
    (fun C m => Cat.Hom.ext (CategoryTheory.Functor.ext (fun c => by cases m.toFunctor.obj c; rfl)
      (fun _ _ _ => rfl)))

instance forget_preservesTerminal :
    PreservesLimitsOfShape (Discrete PEmpty.{1}) forget.{w} :=
  have : PreservesLimit (Functor.empty.{0} ColaxSliceCart.{w, w, w + 1}) forget :=
    preservesTerminal_of_iso forget
      (forget.mapIso (terminalIsTerminal.uniqueUpToIso isTerminal) ≪≫
        ptIsTerminal.uniqueUpToIso terminalIsTerminal)
  preservesLimitsOfShape_pempty_of_preservesTerminal forget

lemma forget_expData (c : ColaxSliceCart.{w, w, w + 1}) :
    (functor_on forget (ColaxSliceCartExponentiable.expData c.F) : Data U c.cat) =
      PointedForget.expData c.cat := by
  simp only [functor_on, ColaxSliceCartExponentiable.expData, PointedForget.expData]
  congr 1
  simp only [functPullback, elChosen, pbChosen]
  congr 1
  exact Subsingleton.elim _ _

/-- The projection preserves the exponentiable arrow `UFam`. -/
noncomputable instance forget_preservesUFam : FunctorPreserves UFam.{w} forget.{w} :=
  functor_preserves_1_is_enough UFam forget (fun c => IsExpArr.isExpArrowData c)
    (fun c => IsExpArr.isExpArrow c)
    (fun c => (forget_expData c).symm ▸ (PointedForget.expUniversal (c := c.cat)))

/-! ### Transport along an isomorphism of categories -/

/-- The object `(C', i⁻¹ ⋙ F)` for `X = (C, F)` and `i : C ≅ C'`. -/
def transportObj (X : ColaxSliceCart.{w, w, w + 1}) {C' : Cat.{w, w + 1}} (i : X.cat ≅ C') :
    ColaxSliceCart.{w, w, w + 1} :=
  ⟨C', i.inv.toFunctor ⋙ X.F⟩

lemma transport_eq (X : ColaxSliceCart.{w, w, w + 1}) {C' : Cat.{w, w + 1}} (i : X.cat ≅ C') :
    i.hom.toFunctor ⋙ i.inv.toFunctor ⋙ X.F = X.F := by
  rw [← Functor.assoc]
  change (i.hom ≫ i.inv).toFunctor ⋙ X.F = X.F
  rw [i.hom_inv_id]
  rfl

lemma eqToHom_app_base_heq' {C : Type*} [Category C] {F G : C ⥤ Fam.{w}} (h : F = G) (c : C) :
    HEq ((eqToHom h).app c : Fam.Hom _ _).base (id : (G.obj c).base → (G.obj c).base) := by
  subst h
  rfl

/-- `X = (C, F)` is isomorphic to `(C', i⁻¹ ⋙ F)` over `i : C ≅ C'`.

[Paper, §4.1, proof of Cor. `cor:family-functor-gat`]: the projection is an isofibration. -/
def transportIso (X : ColaxSliceCart.{w, w, w + 1}) {C' : Cat.{w, w + 1}} (i : X.cat ≅ C') :
    X ≅ transportObj X i where
  hom :=
    { functor := i.hom.toFunctor
      nat := eqToHom (transport_eq X i)
      isPointwiseCartesian := eqToHom_isPointwiseCartesian _ }
  inv :=
    { functor := i.inv.toFunctor
      nat := 𝟙 _
      isPointwiseCartesian := fun _ => Fam.Hom.isCartesian_id _ }
  hom_inv_id := Hom.ext_of_functor_eq (congrArg Cat.Hom.toFunctor i.hom_inv_id) (fun c => by
    change HEq ((eqToHom (transport_eq X i)).app c ≫ 𝟙 _ : Fam.Hom _ _).base _
    rw [Category.comp_id]
    exact eqToHom_app_base_heq' _ c)
  inv_hom_id := Hom.ext_of_functor_eq (congrArg Cat.Hom.toFunctor i.inv_hom_id) (fun c => by
    change HEq ((eqToHom (transport_eq X i)).app (i.inv.toFunctor.obj c) ≫ 𝟙 _ : Fam.Hom _ _).base _
    rw [Category.comp_id]
    exact eqToHom_app_base_heq' _ _)

@[simp] lemma forget_map_transportIso_hom (X : ColaxSliceCart.{w, w, w + 1}) {C' : Cat.{w, w + 1}}
    (i : X.cat ≅ C') : forget.map (transportIso X i).hom = i.hom := rfl

@[simp] lemma forget_map_transportIso_inv (X : ColaxSliceCart.{w, w, w + 1}) {C' : Cat.{w, w + 1}}
    (i : X.cat ≅ C') : forget.map (transportIso X i).inv = i.inv := rfl

end ColaxSliceCart

namespace ColaxSliceCartForget

/-- **The projection from the cartesian colax slice to `Cat`** is a (strict) morphism of
`Lexp` from `ColaxSliceCartLexp` to `CatLexp`.

[Paper, §4.1, Thm. `thm:colax-exponentiable`]: the projection is a `Lexp`-functor. -/
noncomputable def forgetHom : ColaxSliceCartLexp.{w} ⟶ CatLexp.{w} where
  functor := ColaxSliceCart.forget
  preservesPullbacks := ColaxSliceCart.forget_preservesPullbacks
  preservesTerminal := ColaxSliceCart.forget_preservesTerminal
  preservesArr := ColaxSliceCart.forget_preservesUFam
  iso := Iso.refl _

@[simp] lemma forgetHom_functor :
    (forgetHom.{w} : Lexp.Hom ColaxSliceCartLexp CatLexp).functor = ColaxSliceCart.forget := rfl

@[simp] lemma forgetHom_iso_hom_left : forgetHom.{w}.iso.hom.left = 𝟙 _ := rfl

@[simp] lemma forgetHom_iso_hom_right : forgetHom.{w}.iso.hom.right = 𝟙 _ := rfl

end ColaxSliceCartForget
